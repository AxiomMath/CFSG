module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Glue3
public import CFSG.GH74.GLS.Stage1.Thm6.Adapters
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Transfer
public import CFSG.GH74.GLS.Bg.Local.Lemma1621
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Prop46b

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

theorem isElemAbelian_of_sq_one {G : Type} [Group G] {E : Subgroup G} (hE : ∀ a ∈ E, a * a = 1) :
    IsElementaryAbelian 2 ↥E :=
  { is_comm := ⟨fun a b => Subtype.ext (B.comm_of_forall_sq hE a.2 b.2)⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
      apply Subtype.ext
      simpa [pow_two] using hE x x.2 }

namespace Std4r1

variable {G : Type} [Group G] [Finite G] {z : G} {S K F : Subgroup G}

theorem hZ (h : Std4r1 G z S K F) : ∃ t ∈ S, t ≠ z ∧ IsConj z t := by
  obtain ⟨g, hgS, hgz⟩ := CFSG.GH74.GLS.Stage1.Thm6.Sec12.ig_15_3 G h.simple.1 h.simple.2.1 S
    h.S_top z h.z_mem_S h.z_sq h.z_ne (fun t ht => h.z_cent ht)
  refine ⟨g⁻¹ * z * g, hgS, hgz, isConj_iff.2 ⟨g⁻¹, ?_⟩⟩
  rw [inv_inv]

theorem hTransfer (h : Std4r1 G z S K F) : R1.HTransfer G S := by
  intro N hNS hnorm hne hcyc w hwS hw2 hwN
  have hw1 : w ≠ 1 := fun e => hwN (e ▸ N.one_mem)
  have hwo : orderOf w = 2 := R1.orderOf_two_of_sq_one hw2 hw1
  have hord : ∀ v ∈ S, v ∉ N → orderOf w ≤ orderOf v := by
    intro v hv hvN
    have hv1 : v ≠ 1 := fun e => hvN (e ▸ N.one_mem)
    have h1 : orderOf v ≠ 1 := fun e => hv1 (orderOf_eq_one_iff.1 e)
    have h2 := orderOf_pos v
    rw [hwo]; omega
  obtain ⟨b, hbS, hb⟩ := hcyc
  have hext : ∀ y ∈ S, (∃ g : G, g⁻¹ * w * g = y) →
      CFSG.GH74.GLS.Stage1.Thm6.Sec12.IsExtremal S y → y ∈ N ∨ w⁻¹ * y ∈ N := by
    intro y hyS hy _
    by_cases hyN : y ∈ N
    · exact Or.inl hyN
    · right
      obtain ⟨g, rfl⟩ := hy
      have hy2 : (g⁻¹ * w * g) * (g⁻¹ * w * g) = 1 := by
        calc (g⁻¹ * w * g) * (g⁻¹ * w * g) = g⁻¹ * (w * w) * g := by group
          _ = 1 := by rw [hw2]; group
      exact CFSG.GH74.GLS.Stage1.Thm6.Sec12b.uniq_inv_coset hnorm hbS hb hwS hyS hwN hyN
        (by rw [hw2]; exact N.one_mem) (by rw [hy2]; exact N.one_mem)
  obtain ⟨g, hg, -⟩ := CFSG.GH74.GLS.Stage1.Thm6.Sec12b.transfer_conj
    CFSG.GH74.GLS.Stage1.Thm6.Sec12.ig_15_15 h.simple.1 h.simple.2.1 h.S_top hNS hnorm hne
    ⟨b, hbS, hb⟩ hwS hwN hord hext
  exact ⟨g, hg⟩

theorem hThompson (h : Std4r1 G z S K F) : R1.HThompson G z S := by
  intro U hUS hU4 hUn u huU hu1 huz hconj
  have hsyl : ¬ 2 ∣ S.index := by
    have := h.S_top.2.2
    simpa [Subgroup.relIndex_top_right] using this
  have hHyp := CFSG.GH74.GLS.Bg.L1621.Hyp.of_cyclic h.S_pgroup h.Z_cyc hUS hUn hU4.2 hU4.1
    h.z_mem_S h.z_sq h.z_ne (fun g hg => (h.z_cent hg).symm) huU hu1 huz
  obtain ⟨a, b, ha, hb, haz, hau, hbu, hbz⟩ :=
    CFSG.GH74.GLS.Bg.L1621.exists_ab hHyp h.S_pgroup hsyl hconj
  refine ⟨b, hb, ?_⟩
  rw [hbz]
  intro e
  apply hu1
  calc u = u * z * z⁻¹ := by group
    _ = 1 := by rw [e]; group

end Std4r1

end CFSG.GH74.GLS.Stage1.Thm3.Sec6

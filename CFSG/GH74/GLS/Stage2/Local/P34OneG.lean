module

public import CFSG.GH74.GLS.Stage2.Local.P34OneY
public import CFSG.GH74.GLS.Stage2.Final.Thm6.SL2BoundBar
public import CFSG.GH74.GLS.Stage2.Local.Lemma23
public import CFSG.GH74.GLS.Stage2.Local.P34Bar
public import CFSG.GH74.GLS.Stage2.Local.P34OneX

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.Assembly.LowTwoRank
open CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound (bar_mem_S1_iff)

section G

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem one_z_mem_LC (hpair : Stage1Pair G z S q L₁ L₂) (hz : orderOf z = 2) : z ∈ LC z := by
  have hc := toBar_z_mem_center z
  have h1 : toBar z ⟨z, mem_Cen_self z⟩ ∈ generalizedFitting (CentralizerBar z) := by
    refine CFSG.centralizer_generalizedFitting_le (CentralizerBar z) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro f _
    exact Subgroup.mem_center_iff.mp hc f
  rw [hpair.fitting] at h1
  exact mem_LC_of_toBar_mem z (mem_Cen_self z) ⟨1, by simpa using hz⟩ h1

theorem one_toBar_z_ne_one (hz : orderOf z = 2) : toBar z ⟨z, mem_Cen_self z⟩ ≠ 1 := by
  intro h
  have hmem : (⟨z, mem_Cen_self z⟩ : ↥(Cen z)) ∈ pPrimeCore 2 ↥(Cen z) :=
    (QuotientGroup.eq_one_iff _).1 h
  have hodd := odd_orderOf_of_mem_pPrimeCore hmem
  rw [Subgroup.orderOf_mk, hz] at hodd
  exact absurd hodd (by decide)

theorem exists_inv_S1_out (ctx : Stage2Ctx G z k S) (hP : Stage1Pair G z S q L₁ L₂)
    {H : Subgroup G} (hCH : Cen z ≤ H) (hLle : barIn H (LC z) ≤ generalizedFitting (HBar H))
    (hq8 : q % 8 = 3 ∨ q % 8 = 5) (hpsp : IVK.IsPSp4 ↥(generalizedFitting (HBar H)) q)
    (hnS : ¬ barIn H S ≤ generalizedFitting (HBar H)) :
    ∃ y ∈ S1 S z, y * y = 1 ∧ y ∉ RC S z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : orderOf z = 2 := ctx.orderOf_z
  have hzH : z ∈ H := hCH (mem_Cen_self z)
  have hSH : S ≤ H := ctx.S_le_Cen.trans hCH
  have hJn : (generalizedFitting (HBar H)).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := HBar H)).2
  obtain ⟨F, iF, fF, hFq, ⟨e⟩⟩ := hpsp
  have hq8' : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5 := by rw [hFq]; exact hq8
  have h5 : 5 ≤ Nat.card F := by have := hP.gt3; rw [hFq]; omega
  obtain ⟨T, hT⟩ := barIn_sylow H ctx.sylow_top hSH
  have hzH' : orderOf (⟨z, hzH⟩ : ↥H) = 2 := by
    rw [← hz2]; exact (Subgroup.orderOf_coe (⟨z, hzH⟩ : ↥H)).symm
  have hz2' : orderOf (mkH H ⟨z, hzH⟩) = 2 := orderOf_mk_eq_two H hzH'
  have hzJ : mkH H ⟨z, hzH⟩ ∈ generalizedFitting (HBar H) :=
    hLle (Subgroup.mem_map.2 ⟨⟨z, hzH⟩, Subgroup.mem_subgroupOf.2 (one_z_mem_LC hP hz2), rfl⟩)
  have hzT : mkH H ⟨z, hzH⟩ ∈ (T : Subgroup (HBar H)) := by
    rw [hT]
    exact Subgroup.mem_map.2 ⟨⟨z, hzH⟩, Subgroup.mem_subgroupOf.2 ctx.z_mem, rfl⟩
  have hzc : ∀ t ∈ (T : Subgroup (HBar H)), t * mkH H ⟨z, hzH⟩ = mkH H ⟨z, hzH⟩ * t := by
    intro t ht
    rw [hT] at ht
    obtain ⟨s', hs', rfl⟩ := Subgroup.mem_map.1 ht
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (ctx.S_comm_z (Subgroup.mem_subgroupOf.1 hs'))
  have hTJ : ¬ (T : Subgroup (HBar H)) ≤ generalizedFitting (HBar H) := by rw [hT]; exact hnS
  have hCJ : ∀ x : HBar H, (∀ j ∈ generalizedFitting (HBar H), x * j = j * x) →
      x ∈ generalizedFitting (HBar H) := by
    intro x hx
    refine CFSG.centralizer_generalizedFitting_le (HBar H) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact (hx j hj).symm
  obtain ⟨E₁, E₂, u, hLU, hu2, huJ, huz, hn₁, hn₂⟩ := exists_outer_involution
    (J := generalizedFitting (HBar H)) hq8' h5 e hCJ T hzJ hz2' hzT hzc hTJ
  have hY : Subgroup.centralizer ({mkH H ⟨z, hzH⟩} : Set (HBar H)) = barIn H (Cen z) :=
    centralizer_mk_eq H hz2 hzH
  have huY : u ∈ barIn H (Cen z) := by
    rw [← hY]; exact Subgroup.mem_centralizer_singleton_iff.2 huz
  have hTY : (T : Subgroup (HBar H)) ≤ barIn H (Cen z) := by
    rw [hT]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono H ctx.S_le_Cen)
  have hρz : ∀ hz : mkH H ⟨z, hzH⟩ ∈ barIn H (Cen z),
      cenToBar H hCH ⟨mkH H ⟨z, hzH⟩, hz⟩ ≠ 1 := by
    intro hz
    have h1 := cenToBar_cenMk H hCH ⟨z, mem_Cen_self z⟩
    have h2 : (⟨cenMk H hCH ⟨z, mem_Cen_self z⟩, cenMk_mem H hCH ⟨z, mem_Cen_self z⟩⟩ :
        ↥(barIn H (Cen z))) = ⟨mkH H ⟨z, hzH⟩, hz⟩ := rfl
    rw [h2] at h1
    rw [h1]
    exact one_toBar_z_ne_one hz2
  obtain ⟨y, hyT, ⟨c, hyc⟩, hperm⟩ := exists_conj_normalizing hzJ hY (cenToBar H hCH)
    (cenToBar_surjective H hCH) hρz hP.comps hLU huY hu2 hn₁ hn₂ T hTY
  have hyJ : (y : HBar H) ∉ generalizedFitting (HBar H) := by
    intro hy
    apply huJ
    have h1 := hJn.conj_mem (y : HBar H) hy ((c : HBar H)⁻¹)
    have h2 : (c : HBar H)⁻¹ * (y : HBar H) * ((c : HBar H)⁻¹)⁻¹ = u := by
      rw [hyc]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rwa [h2] at h1
  have hysq : (y : HBar H) * (y : HBar H) = 1 := by
    rw [hyc]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (c : HBar H) * u * (c : HBar H)⁻¹ * ((c : HBar H) * u * (c : HBar H)⁻¹) =
        (c : HBar H) * (u * u) * (c : HBar H)⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have hyS : (y : HBar H) ∈ barIn H S := by rw [← hT]; exact hyT
  obtain ⟨s', hs', hsy⟩ := Subgroup.mem_map.1 hyS
  have hŷS : (s' : G) ∈ S := Subgroup.mem_subgroupOf.1 hs'
  have hŷC : (s' : G) ∈ Cen z := ctx.S_le_Cen hŷS
  have hbar : toBar z ⟨(s' : G), hŷC⟩ = cenToBar H hCH y := by
    have h1 := cenToBar_cenMk H hCH ⟨(s' : G), hŷC⟩
    have h2 : (⟨cenMk H hCH ⟨(s' : G), hŷC⟩, cenMk_mem H hCH ⟨(s' : G), hŷC⟩⟩ :
        ↥(barIn H (Cen z))) = y := Subtype.ext hsy
    rw [h2] at h1
    exact h1.symm
  refine ⟨(s' : G), ?_, ?_, ?_⟩
  · rw [bar_mem_S1_iff]
    refine ⟨hŷS, hŷC, fun K hK _ => ?_⟩
    rw [hbar]
    have h1 := congrArg (fun f => (f ⟨K, hK⟩).1) hperm
    have h2 : K.map (MulAut.conj (cenToBar H hCH y)).toMonoidHom = K := h1
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      rw [← h2]
      exact Subgroup.mem_map.2 ⟨a, ha, by simp⟩
    · intro ha
      rw [← h2] at ha
      obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.1 ha
      have : b = a := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hba
        simpa using hba
      rwa [← this]
  · have h1 : (mkH H s') * (mkH H s') = 1 := by rw [hsy]; exact hysq
    have h2 : s' * s' ∈ pPrimeCore 2 ↥H := (mkH_eq_one_iff H).1 (by rw [map_mul]; exact h1)
    have hodd := odd_orderOf_of_mem_core H h2
    have hS2 : IsPGroup 2 ↥S := ctx.sylow.isPGroup
    obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.1 hS2) ⟨(s' : G) * (s' : G), S.mul_mem hŷS hŷS⟩
    have hord : orderOf (s' * s') = 2 ^ a := by
      rw [← Subgroup.orderOf_coe (s' * s'), Subgroup.coe_mul]
      rw [← Subgroup.orderOf_coe (⟨(s' : G) * (s' : G), S.mul_mem hŷS hŷS⟩ : ↥S)] at ha
      exact ha
    rw [hord] at hodd
    have ha0 : a = 0 := by
      by_contra hne
      exact (Nat.not_even_iff_odd.2 hodd) (by
        exact (Nat.even_pow.2 ⟨even_two, hne⟩))
    rw [ha0, pow_zero, orderOf_eq_one_iff] at hord
    simpa using congrArg Subtype.val hord
  · intro hRC
    exact hyJ (hsy ▸ hLle (Subgroup.mem_map.2 ⟨s', Subgroup.mem_subgroupOf.2 hRC.2, rfl⟩))

end G

end CFSG.GH74.GLS.Stage2.Local.P34

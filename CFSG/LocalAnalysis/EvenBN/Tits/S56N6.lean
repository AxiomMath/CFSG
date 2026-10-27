module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56N4

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}


@[expose] def s56O (d : Data G) : Set G := {x | x ∈ d.s56U10 ∧ x ∉ d.s56U11}

theorem s56_card_O (d : Data G) : Nat.card ↥(d.s56O) = 4 := by
  have h : d.s56O = (d.s56U10 : Set G) \ (d.s56U11 : Set G) := rfl
  have hsub : (d.s56U11 : Set G) ⊆ (d.s56U10 : Set G) := s56_U11_le_U10 d
  have e10 : (d.s56U10 : Set G).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]; exact s56_card_U10 d
  have e11 : (d.s56U11 : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]; exact s56_card_U11 d
  have h1 : (d.s56O).ncard = 4 := by
    rw [h, Set.ncard_diff hsub (Set.toFinite _), e10, e11]
  rw [Nat.card_coe_set_eq]
  exact h1

theorem s56_P10_le_N (d : Data G) : d.s56P10 ≤ d.N := (s56_P10_le_P0 d).trans (s56_P0_le_N d)

theorem Hyp.s56_N_conj_O (h49 : d.Thm49Statement) (hd : d.Hyp) {n x : G} (hn : n ∈ d.N)
    (hx : x ∈ d.s56O) : n * x * n⁻¹ ∈ d.s56O := by
  refine ⟨hd.s56_N_conj_U10 h49 hn hx.1, fun h => hx.2 ?_⟩
  have := hd.s56_N_conj_U11 h49 (inv_mem hn) h
  simpa [mul_assoc] using this

@[expose] noncomputable def Hyp.s56Opermhom (h49 : d.Thm49Statement) (hd : d.Hyp) :
    ↥d.N →* Equiv.Perm ↥(d.s56O) where
  toFun n :=
    { toFun := fun x => ⟨n.1 * x.1 * n.1⁻¹, hd.s56_N_conj_O h49 n.2 x.2⟩
      invFun := fun x => ⟨n.1⁻¹ * x.1 * n.1⁻¹⁻¹, hd.s56_N_conj_O h49 (inv_mem n.2) x.2⟩
      left_inv := fun x => Subtype.ext (by group)
      right_inv := fun x => Subtype.ext (by group) }
  map_one' := by
    ext x
    show 1 * x.1 * 1⁻¹ = x.1
    group
  map_mul' := fun a b => by
    ext x
    show (a.1 * b.1) * x.1 * (a.1 * b.1)⁻¹ = a.1 * (b.1 * x.1 * b.1⁻¹) * a.1⁻¹
    group

theorem Hyp.s56Opermhom_apply (h49 : d.Thm49Statement) (hd : d.Hyp) (n : ↥d.N) (x : ↥(d.s56O)) :
    (((hd.s56Opermhom h49 n) x : ↥(d.s56O)) : G) = n.1 * x.1 * n.1⁻¹ := rfl

theorem Hyp.s56Opermhom_ker (h49 : d.Thm49Statement) (hd : d.Hyp) :
    (hd.s56Opermhom h49).ker = d.s56P10.subgroupOf d.N := by
  ext n
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  have hP10 : n.1 ∈ d.s56P10 ↔ n.1 ∈ d.N ⊓ centralizer (d.s56U10 : Set G) := by
    rw [← hd.s56_CN_U10_eq h49]
  constructor
  · intro h
    have hfix : ∀ x ∈ d.s56O, n.1 * x * n.1⁻¹ = x := fun x hx => by
      have := congrArg (fun σ : Equiv.Perm ↥(d.s56O) => ((σ ⟨x, hx⟩ : ↥(d.s56O)) : G)) h
      simpa [hd.s56Opermhom_apply] using this
    have h10 : n.1 * d.pv 10 = d.pv 10 * n.1 := by
      have := hfix _ ⟨s56_pv10_mem_U10 d, s56_pv10_not_mem_U11 d⟩
      calc n.1 * d.pv 10 = n.1 * d.pv 10 * n.1⁻¹ * n.1 := by group
        _ = d.pv 10 * n.1 := by rw [this]
    have hU : ∀ u ∈ d.s56U11, n.1 * u = u * n.1 := fun u hu => by
      have hO : d.pv 10 * u ∈ d.s56O := ⟨mul_mem (s56_pv10_mem_U10 d)
        (s56_U11_le_U10 d hu), fun h => s56_pv10_not_mem_U11 d (by
          have := mul_mem h (inv_mem hu)
          simpa using this)⟩
      have h2 := hfix _ hO
      have h3 : n.1 * (d.pv 10 * u) = (d.pv 10 * u) * n.1 := by
        calc n.1 * (d.pv 10 * u) = n.1 * (d.pv 10 * u) * n.1⁻¹ * n.1 := by group
          _ = (d.pv 10 * u) * n.1 := by rw [h2]
      calc n.1 * u = (d.pv 10)⁻¹ * (d.pv 10 * n.1) * u := by group
        _ = (d.pv 10)⁻¹ * (n.1 * d.pv 10) * u := by rw [h10]
        _ = (d.pv 10)⁻¹ * (n.1 * (d.pv 10 * u)) := by group
        _ = (d.pv 10)⁻¹ * ((d.pv 10 * u) * n.1) := by rw [h3]
        _ = u * n.1 := by group
    rw [hP10]
    refine mem_inf.2 ⟨n.2, mem_centralizer_iff.2 fun x hx => ?_⟩
    rcases s56_U10_cases hx with hx | ⟨u, hu, rfl⟩
    · exact (hU x hx).symm
    · calc d.pv 10 * u * n.1 = d.pv 10 * (u * n.1) := by group
        _ = d.pv 10 * (n.1 * u) := by rw [hU u hu]
        _ = (d.pv 10 * n.1) * u := by group
        _ = (n.1 * d.pv 10) * u := by rw [h10]
        _ = n.1 * (d.pv 10 * u) := by group
  · intro h
    rw [hP10] at h
    have hC := (mem_inf.1 h).2
    ext x
    show n.1 * x.1 * n.1⁻¹ = x.1
    have := mem_centralizer_iff.1 hC x.1 x.2.1
    calc n.1 * x.1 * n.1⁻¹ = (x.1 * n.1) * n.1⁻¹ := by rw [← this]
      _ = x.1 := by group

theorem Hyp.s56_N_quot_P10_equiv (h49 : d.Thm49Statement) (hd : d.Hyp) :
    ∃ _ : (d.s56P10.subgroupOf d.N).Normal,
      Nonempty (↥d.N ⧸ d.s56P10.subgroupOf d.N ≃* Equiv.Perm (Fin 4)) := by
  have hker := hd.s56Opermhom_ker h49
  haveI hNormal : (d.s56P10.subgroupOf d.N).Normal := hker ▸ (hd.s56Opermhom h49).normal_ker
  refine ⟨hNormal, ?_⟩
  have hcard := Subgroup.card_ker_mul_card_range (hd.s56Opermhom h49)
  rw [hker, Nat.card_congr (subgroupOfEquivOfLe (s56_P10_le_N d)).toEquiv] at hcard
  have hN := hd.s56_card_N h49
  have hperm : Nat.card (Equiv.Perm ↥(d.s56O)) = 24 := by
    rw [Nat.card_perm, s56_card_O]; norm_num [Nat.factorial]
  have hP10pos : 0 < Nat.card d.s56P10 := Nat.card_pos
  have hrange : Nat.card (hd.s56Opermhom h49).range = 24 := by
    have : Nat.card d.s56P10 * Nat.card (hd.s56Opermhom h49).range =
        Nat.card d.s56P10 * 24 := by
      rw [hcard, hN]; ring
    exact Nat.eq_of_mul_eq_mul_left hP10pos this
  have htop : (hd.s56Opermhom h49).range = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [hrange, hperm])
  have e1 : ↥d.N ⧸ d.s56P10.subgroupOf d.N ≃* Equiv.Perm ↥(d.s56O) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange (hd.s56Opermhom h49)).trans
        ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv))
  have e2 : ↥(d.s56O) ≃ Fin 4 := Finite.equivFinOfCardEq (s56_card_O d)
  exact ⟨e1.trans (Equiv.permCongrHom e2)⟩

end Data

end CFSG.LocalAnalysis.EvenBN.Tits

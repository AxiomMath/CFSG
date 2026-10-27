module

public import CFSG.CGT.Foote82.T66.CitedCaseI
public import CFSG.CGT.Foote82.T66.CitedCaseII
import CFSG.CGT.Foote82.T66.CaseIS6D8
import CFSG.LocalAnalysis.ComponentClassification.HSFLitDD
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFixedFactorSylowReduction
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.FittingNilpotence
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication

public section

namespace CFSG.CGT.Foote82

namespace G10Aux

open DihedralGroup CFSG.ComponentClassification
open scoped commutatorElement

local notation "DD" => DihedralGroup 4 × DihedralGroup 4

theorem comm_dih (a b : DihedralGroup 4) : ⁅a, b⁆ = 1 ∨ ⁅a, b⁆ = r 2 := by
  revert a b
  decide

theorem comm_mem_center (g h : DD) : ⁅g, h⁆ ∈ Subgroup.center DD := by
  rw [Subgroup.center_prod, Subgroup.mem_prod]
  have hmem : ∀ a b : DihedralGroup 4, ⁅a, b⁆ ∈ Subgroup.center (DihedralGroup 4) := by
    intro a b
    rcases comm_dih a b with e | e <;> rw [e]
    · exact one_mem _
    · exact CaseIS6D8.r_two_mem_center
  exact ⟨hmem g.1 h.1, hmem g.2 h.2⟩

theorem mem_center_iff_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (g : G) :
    e g ∈ Subgroup.center H ↔ g ∈ Subgroup.center G := by
  simp only [Subgroup.mem_center_iff]
  constructor
  · intro h k
    apply e.injective
    rw [map_mul, map_mul]
    exact h (e k)
  · intro h k
    obtain ⟨k, rfl⟩ := e.surjective k
    rw [← map_mul, ← map_mul, h k]

theorem card_center_equiv {G : Type*} [Group G] (e : G ≃* DD) :
    Nat.card (Subgroup.center G) = 4 := by
  rw [← CaseIS6D8.card_center_prod]
  exact Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun g => (mem_center_iff_equiv e g).symm)

theorem card_sq_aut (σ : DD ≃* DD) (y : DD) :
    Nat.card {g : DD // g ^ 2 = σ y} = Nat.card {g : DD // g ^ 2 = y} := by
  refine Nat.card_congr (Equiv.subtypeEquiv σ.symm.toEquiv fun g => ?_)
  show g ^ 2 = σ y ↔ σ.symm g ^ 2 = y
  rw [← map_pow, MulEquiv.symm_apply_eq]

theorem aut_center_swap (σ : DD ≃* DD) (hσ : ∃ c ∈ Subgroup.center DD, σ c ≠ c) :
    σ (r 2, 1) = (1, r 2) ∧ σ (1, r 2) = (r 2, 1) := by
  have hcent : ∀ y : DD, (∀ k : DD, y * k = k * y) → ∀ k : DD, σ y * k = k * σ y := by
    intro y hy k
    obtain ⟨k, rfl⟩ := σ.surjective k
    rw [← map_mul, ← map_mul, hy k]
  have hne : ∀ y : DD, y ≠ 1 → σ y ≠ 1 := fun y hy h =>
    hy (σ.injective (h.trans (map_one σ).symm))
  have hz1 : ∀ k : DD, ((r 2, 1) : DD) * k = k * (r 2, 1) := by decide
  have hzz := HSFLit.dd_r_two_r_two_central
  have hzzf : σ (r 2, r 2) = (r 2, r 2) := by
    have hc := card_sq_aut σ (r 2, r 2)
    rw [HSFLit.dd_card_sq_eq_both] at hc
    rcases HSFLit.dd_eq_of_central _ (hcent _ hzz) with h | h | h | h
    · exact absurd h (hne _ (by decide))
    · rw [h, HSFLit.dd_card_sq_eq_left] at hc
      exact absurd hc (by norm_num)
    · rw [h, HSFLit.dd_card_sq_eq_right] at hc
      exact absurd hc (by norm_num)
    · exact h
  have h1 : σ (r 2, 1) = (r 2, 1) ∨ σ (r 2, 1) = (1, r 2) := by
    have hc := card_sq_aut σ (r 2, 1)
    rw [HSFLit.dd_card_sq_eq_left] at hc
    rcases HSFLit.dd_eq_of_central _ (hcent _ hz1) with h | h | h | h
    · exact absurd h (hne _ (by decide))
    · exact Or.inl h
    · exact Or.inr h
    · rw [h, HSFLit.dd_card_sq_eq_both] at hc
      exact absurd hc (by norm_num)
  have e2 : ((1, r 2) : DD) = (r 2, 1) * (r 2, r 2) := by decide
  rcases h1 with h | h
  · exfalso
    obtain ⟨c, hc, hσc⟩ := hσ
    apply hσc
    have hσ2 : σ (1, r 2) = (1, r 2) := by
      rw [e2, map_mul, h, hzzf]
    rcases HSFLit.dd_eq_of_central c (fun k => (Subgroup.mem_center_iff.1 hc k).symm) with
      rfl | rfl | rfl | rfl
    · exact map_one σ
    · exact h
    · exact hσ2
    · exact hzzf
  · refine ⟨h, ?_⟩
    rw [e2, map_mul, h, hzzf]
    decide

theorem exists_comm_of_index_two (M : Subgroup DD) (hM : M.index = 2) :
    ∃ g ∈ M, ∃ h ∈ M, ⁅g, h⁆ = ((r 2, 1) : DD) ∨ ⁅g, h⁆ = ((1, r 2) : DD) := by
  have key : ∀ {x y : DD}, x ∉ M → y ∉ M → x * y ∈ M := fun hx hy =>
    (Subgroup.mul_mem_iff_of_index_two hM).2 (iff_of_false hx hy)
  have hA : ((r 1, 1) : DD) ∈ M ∧ ((sr 0, 1) : DD) ∈ M ∨
      ∃ v ∉ M, ∃ u ∈ M, ⁅v * ((1, r 1) : DD), u⁆ = ((r 2, 1) : DD) ∧
        ⁅v * ((1, sr 0) : DD), u⁆ = ((r 2, 1) : DD) := by
    by_cases ha : ((r 1, 1) : DD) ∈ M <;> by_cases hb : ((sr 0, 1) : DD) ∈ M
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr ⟨(sr 0, 1), hb, (r 1, 1), ha, by decide, by decide⟩
    · exact Or.inr ⟨(r 1, 1), ha, (sr 0, 1), hb, by decide, by decide⟩
    · exact Or.inr ⟨(r 1, 1), ha, (r 1, 1) * (sr 0, 1), key ha hb, by decide, by decide⟩
  have hB : ((1, r 1) : DD) ∈ M ∧ ((1, sr 0) : DD) ∈ M ∨
      ∃ w ∉ M, w = ((1, r 1) : DD) ∨ w = ((1, sr 0) : DD) := by
    by_cases hc : ((1, r 1) : DD) ∈ M
    · by_cases hd : ((1, sr 0) : DD) ∈ M
      · exact Or.inl ⟨hc, hd⟩
      · exact Or.inr ⟨_, hd, Or.inr rfl⟩
    · exact Or.inr ⟨_, hc, Or.inl rfl⟩
  rcases hB with ⟨hc, hd⟩ | ⟨w, hw, hw'⟩
  · exact ⟨_, hc, _, hd, Or.inr (by decide)⟩
  rcases hA with ⟨ha, hb⟩ | ⟨v, hv, u, hu, h1, h2⟩
  · exact ⟨_, ha, _, hb, Or.inl (by decide)⟩
  refine ⟨v * w, key hv hw, u, hu, Or.inl ?_⟩
  rcases hw' with rfl | rfl
  · exact h1
  · exact h2

variable {X : Type*} [Group X]

theorem commutator_le_center_map {H : Subgroup X} (e : ↥H ≃* DD) :
    ⁅H, H⁆ ≤ (Subgroup.center ↥H).map H.subtype := by
  rw [Subgroup.commutator_le]
  intro g hg k hk
  refine Subgroup.mem_map.2 ⟨⁅(⟨g, hg⟩ : ↥H), (⟨k, hk⟩ : ↥H)⁆, ?_, rfl⟩
  rw [← mem_center_iff_equiv e, map_commutatorElement]
  exact comm_mem_center _ _

theorem mem_center_map_cases {H : Subgroup X} (e : ↥H ≃* DD) {y : X}
    (hy : y ∈ (Subgroup.center ↥H).map H.subtype) :
    y = 1 ∨ y = (e.symm (r 2, 1) : X) ∨ y = (e.symm (1, r 2) : X) ∨
      y = (e.symm (r 2, 1) : X) * (e.symm (1, r 2) : X) := by
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hy
  obtain ⟨q, rfl⟩ := e.symm.surjective p
  rw [← mem_center_iff_equiv e, MulEquiv.apply_symm_apply] at hp
  rcases HSFLit.dd_eq_of_central q (fun k => (Subgroup.mem_center_iff.1 hp k).symm) with
    rfl | rfl | rfl | rfl
  · left
    simp
  · right; left; rfl
  · right; right; left; rfl
  · right; right; right
    rw [show ((r 2, r 2) : DD) = (r 2, 1) * (1, r 2) by decide, map_mul]
    rfl

theorem index_subgroupOf_eq_two {P Q : Subgroup X} (hP : P.index = 2) (hQ : Q.index = 2)
    (hne : P ≠ Q) : (Q.subgroupOf P).index = 2 := by
  haveI := Subgroup.normal_of_index_eq_two hQ
  have hdvd : Q.relIndex P ∣ 2 := hQ ▸ Subgroup.relIndex_dvd_index_of_normal Q P
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exfalso
    have hPQ : P ≤ Q := Subgroup.relIndex_eq_one.1 h
    have h2 := Subgroup.relIndex_mul_index hPQ
    rw [hP, hQ] at h2
    have h3 : P.relIndex Q = 1 := by omega
    exact hne (le_antisymm hPQ (Subgroup.relIndex_eq_one.1 h3))
  · exact h

theorem center_map_eq [Finite X] {P Q : Subgroup X} (hP : P.index = 2) (eP : ↥P ≃* DD)
    (hx : ∃ x : X, ∃ c ∈ Subgroup.center ↥P, x * (c : X) ≠ (c : X) * x)
    (hQ : Q.index = 2) (eQ : ↥Q ≃* DD) :
    (Subgroup.center ↥Q).map Q.subtype = (Subgroup.center ↥P).map P.subtype := by
  by_cases hPQ : P = Q
  · subst hPQ
    rfl
  obtain ⟨x, c, hc, hxc⟩ := hx
  haveI := Subgroup.normal_of_index_eq_two hP
  haveI := Subgroup.normal_of_index_eq_two hQ
  let σ : DD ≃* DD := (eP.symm.trans (MulAut.conjNormal x : MulAut ↥P)).trans eP
  have hσapp : ∀ w : DD, ((eP.symm (σ w) : ↥P) : X) = x * (eP.symm w : X) * x⁻¹ := by
    intro w
    simp [σ, MulAut.conjNormal_apply]
  have hσc : ∃ c' ∈ Subgroup.center DD, σ c' ≠ c' := by
    refine ⟨eP c, (mem_center_iff_equiv eP c).2 hc, fun h => hxc ?_⟩
    have h1 := congrArg (fun w => ((eP.symm w : ↥P) : X)) h
    rw [hσapp, MulEquiv.symm_apply_apply] at h1
    calc x * (c : X) = x * c * x⁻¹ * x := by group
      _ = c * x := by rw [h1]
  obtain ⟨hs1, hs2⟩ := aut_center_swap σ hσc
  have hx1 : x * (eP.symm (r 2, 1) : X) * x⁻¹ = (eP.symm (1, r 2) : X) := by
    rw [← hσapp, hs1]
  have hx2 : x * (eP.symm (1, r 2) : X) * x⁻¹ = (eP.symm (r 2, 1) : X) := by
    rw [← hσapp, hs2]
  have hM : ((Q.subgroupOf P).comap eP.symm.toMonoidHom).index = 2 := by
    rw [Subgroup.index_comap_of_surjective _ eP.symm.surjective]
    exact index_subgroupOf_eq_two hP hQ hPQ
  obtain ⟨g, hg, k, hk, hgk⟩ := exists_comm_of_index_two _ hM
  have hcomm : ((eP.symm ⁅g, k⁆ : ↥P) : X) ∈ ⁅Q, Q⁆ := by
    have e : ((eP.symm ⁅g, k⁆ : ↥P) : X) =
        ⁅((eP.symm g : ↥P) : X), ((eP.symm k : ↥P) : X)⁆ := by
      rw [map_commutatorElement]
      rfl
    rw [e]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.1 (Subgroup.mem_comap.1 hg))
      (Subgroup.mem_subgroupOf.1 (Subgroup.mem_comap.1 hk))
  have hN : (⁅Q, Q⁆ : Subgroup X).Normal := inferInstance
  have hboth : (eP.symm (r 2, 1) : X) ∈ ⁅Q, Q⁆ ∧ (eP.symm (1, r 2) : X) ∈ ⁅Q, Q⁆ := by
    rcases hgk with e | e <;> rw [e] at hcomm
    · refine ⟨hcomm, ?_⟩
      rw [← hx1]
      exact hN.conj_mem _ hcomm x
    · refine ⟨?_, hcomm⟩
      rw [← hx2]
      exact hN.conj_mem _ hcomm x
  have hle : (Subgroup.center ↥P).map P.subtype ≤ (Subgroup.center ↥Q).map Q.subtype := by
    intro y hy
    apply commutator_le_center_map eQ
    rcases mem_center_map_cases eP hy with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hboth.1
    · exact hboth.2
    · exact mul_mem hboth.1 hboth.2
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Subgroup.card_map_of_injective Q.subtype_injective,
    Subgroup.card_map_of_injective P.subtype_injective, card_center_equiv eP,
    card_center_equiv eQ]

end G10Aux

theorem caseIG10_holds : CaseIG10 := by
  rintro X _ _ P Q - hP ⟨eP⟩ hx hQ ⟨eQ⟩
  exact G10Aux.center_map_eq hP eP hx hQ eQ

theorem caseIIG10_holds : CaseIIG10 := by
  rintro X _ _ - P hP ⟨eP⟩ ⟨g, c, hc, -, hgc⟩ M hM ⟨eM⟩
  refine G10Aux.center_map_eq hP eP ⟨g, c, hc, fun h => hgc ?_⟩ hM eM
  rw [h, mul_inv_cancel_right]

end CFSG.CGT.Foote82

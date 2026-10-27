module

public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorBasic
public import CFSG.RankThree.Classical.SteinbergBYProjectiveInvolutionSign
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public noncomputable section

namespace CFSG.ComponentClassification.OddSelector

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancingLocal

theorem quaternion_central_mem_zpowers {y : QuaternionGroup 2} (hy : y ≠ 1) :
    QuaternionGroup.a 2 ∈ zpowers y := by
  rcases y with i | i
  · fin_cases i
    · exact absurd rfl hy
    · refine ⟨2, ?_⟩
      change QuaternionGroup.a 1 ^ (2 : ℤ) = _
      rw [zpow_two, QuaternionGroup.a_mul_a]
      rfl
    · exact mem_zpowers _
    · refine ⟨2, ?_⟩
      change QuaternionGroup.a 3 ^ (2 : ℤ) = _
      rw [zpow_two, QuaternionGroup.a_mul_a]
      rfl
  · refine ⟨2, ?_⟩
    change QuaternionGroup.xa i ^ (2 : ℤ) = _
    rw [zpow_two, ← sq, QuaternionGroup.xa_sq]
    rfl

theorem injective_of_quaternion {G : Type*} [Group G] (q : QuaternionGroup 2 →* G)
    (hq : q (QuaternionGroup.a 2) ≠ 1) : Function.Injective q := by
  rw [injective_iff_map_eq_one]
  intro y hy
  by_contra hy1
  obtain ⟨k, hk⟩ := quaternion_central_mem_zpowers hy1
  apply hq
  rw [← hk, map_zpow, hy, one_zpow]

open CFSG.RankThree.Classical.SteinbergBY in
theorem not_psl_two_odd_of_quaternion {X : Type} [Group X] (q : QuaternionGroup 2 →* X)
    (hq : Function.Injective q) {p f : ℕ} (hp2 : p ≠ 2) :
    ¬ StatedClassicalModel X .PSL 2 p f := by
  rintro ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨e⟩⟩
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hchar : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    exact hp2
  let ψ : X →* Equiv.Perm (CatalogueSchreierLinearTwo.Omega K) :=
    (CatalogueSchreierLinearTwo.coordinateG K).subtype.comp
      (e.trans ((projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
        (CatalogueSchreierLinearTwo.pslEquivCoordinateG K))).toMonoidHom
  have hψ : Function.Injective ψ :=
    (Subgroup.subtype_injective _).comp (MulEquiv.injective _)
  have hH : (ψ.comp q).range ≤ CatalogueSchreierLinearTwo.coordinateD K := by
    rintro _ ⟨y, rfl⟩
    exact CatalogueSchreierLinearTwo.coordinateG_le_D K (Subtype.prop _)
  obtain ⟨-, hno⟩ :=
    odd_linear_two_projective_involution_centralizers_exclude_quaternion hchar
  exact (hno 3 le_rfl _ hH).false (MonoidHom.ofInjective (f := ψ.comp q) (hψ.comp hq)).symm

variable {H : Type*} {L : Type} [Group H] [Group L]

theorem not_small_source_of_cover_quaternion [Group.IsPerfect H] (σ : H →* L)
    (hσ : σ.ker ≤ center H) (q : QuaternionGroup 2 →* H)
    (hq : q (QuaternionGroup.a 2) ∉ center H) {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2)
    (U : Subgroup H) (hU : l ^ 3 ∣ Nat.card U) (hUZ : U ⊓ center H = ⊥) :
    (∀ p f : ℕ, p ≠ 2 → ¬ StatedClassicalModel (L ⧸ center L) .PSL 2 p f) ∧
      IsEmpty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∧
      ¬ StatedClassicalModel (L ⧸ center L) .PSL 3 2 2 := by
  set τ : H →* L ⧸ center L := (QuotientGroup.mk' (center L)).comp σ with hτ
  have hτq : Function.Injective (τ.comp q) := by
    refine injective_of_quaternion _ fun h => hq ?_
    refine mem_center_of_map_mem_center σ hσ ?_
    rw [MonoidHom.comp_apply, hτ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at h
    exact h
  have hUi := injective_restrict_center σ hσ hUZ
  have hU' : l ^ 3 ∣ Nat.card (L ⧸ center L) := by
    refine hU.trans ?_
    rw [Nat.card_congr (MonoidHom.ofInjective hUi).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  exact ⟨fun _ _ hp2 => not_psl_two_odd_of_quaternion _ hτq hp2,
    isEmpty_alternating_seven_of_dvd hl hl2 hU', not_psl_three_four_of_dvd hl hl2 hU'⟩

end CFSG.ComponentClassification.OddSelector

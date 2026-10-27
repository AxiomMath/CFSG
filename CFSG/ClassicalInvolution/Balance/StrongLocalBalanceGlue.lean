module

public import CFSG.ClassicalInvolution.Balance.StrongLocalBalance

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance

open CFSG.Assembly.Dichotomy CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.LocalBalance

theorem commute_of_strongLocalTwoBalanceToral {t : StatedLieTag} {Q : ℕ → ℕ → ℕ → Prop}
    (hSB : StrongLocalTwoBalanceToralOn t Q) {n p e : ℕ} (hp : p.Prime) (hq : Q n p e)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ e)
    {X : Type} [Group X] [Finite X] (ψ : (modelUniv t n p e hp).K →* X)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t n p e hp).K) {F : Subgroup X}
    (hcard : Nat.card F = 4) (hF2 : ∀ f ∈ F, f * f = 1)
    (hfaith : ∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ ψ.range, f * x = x * f)
    (hFN : F ≤ Subgroup.normalizer (ψ.range : Set X)) (htoral : ToralAction ψ F) :
    (∀ d ∈ deltaCore F, d ∈ Subgroup.normalizer (ψ.range : Set X) →
      ∀ x ∈ ψ.range, d * x = x * d) ∧
    ∀ f ∈ F, f ≠ 1 → ∀ d ∈ involutionOddCore f, d ∈ Subgroup.normalizer (ψ.range : Set X) →
      ∀ g ∈ F, ∀ x ∈ ψ.range, d * g * x * (d * g)⁻¹ = g * d * x * (g * d)⁻¹ := by
  set N : Subgroup X := Subgroup.normalizer (ψ.range : Set X) with hN
  have hrN : ψ.range ≤ N := Subgroup.le_normalizer
  set ψ' : (modelUniv t n p e hp).K →* ↥N := ψ.codRestrict N fun k => hrN ⟨k, rfl⟩ with hψ'
  have hψ'y : ∀ y, ((ψ' y : ↥N) : X) = ψ y := fun y => rfl
  have hker' : ψ'.ker ≤ Subgroup.center (modelUniv t n p e hp).K := fun y hy =>
    hker (MonoidHom.mem_ker.mpr (congrArg Subtype.val (MonoidHom.mem_ker.mp hy)))
  have hrange : ψ'.range = ψ.range.subgroupOf N := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, Subtype.ext hx⟩
  have hnorm' : ψ'.range.Normal := by
    rw [hrange, Subgroup.normal_subgroupOf_iff_le_normalizer hrN]
  set F' : Subgroup ↥N := F.subgroupOf N with hF'
  have hF'4 : Nat.card F' = 4 := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFN).toEquiv
  have hF'2 : ∀ f ∈ F', f * f = 1 := fun f hf => Subtype.ext (hF2 f.1 hf)
  have hfaith' : ∀ f ∈ F', f ≠ 1 → ¬ ∀ x ∈ ψ'.range, f * x = x * f := by
    intro f hf hf1 hc
    refine hfaith f.1 hf (fun h => hf1 (Subtype.ext h)) fun x hx => ?_
    have hx' : (⟨x, hrN hx⟩ : ↥N) ∈ ψ'.range := by
      rw [hrange]
      exact hx
    exact congrArg Subtype.val (hc _ hx')
  have htoral' : ToralAction ψ' F' := by
    obtain ⟨P, hP, hact⟩ := htoral
    refine ⟨P, hP, fun f hf => ?_⟩
    obtain ⟨x, hxP, hxa⟩ := hact f.1 hf
    exact ⟨x, hxP, fun y => Subtype.ext (hxa y)⟩
  have hSC := hSB n p e hp hq hfund hadm hp2 h5 ↥N ψ' hker' hnorm' F' hF'4 hF'2 hfaith' htoral'
  have hxmem : ∀ x (hx : x ∈ ψ.range), (⟨x, hrN hx⟩ : ↥N) ∈ ψ'.range := fun x hx => by
    rw [hrange]
    exact hx
  refine ⟨fun d hd hdN x hx => ?_, fun f hf hf1 d hd hdN g hg x hx => ?_⟩
  · have hd' : (⟨d, hdN⟩ : ↥N) ∈ deltaCore F' := by
      rw [mem_deltaCore_iff]
      intro f' hf' hf'1
      have hf1 : (f' : X) ≠ 1 := fun h => hf'1 (Subtype.ext h)
      exact subgroupOf_involutionOddCore_le f' (Subgroup.mem_subgroupOf.mpr
        (mem_deltaCore_iff.mp hd (f' : X) hf' hf1))
    exact congrArg Subtype.val (hSC.1 _ hd' _ (hxmem x hx))
  · have hf' : (⟨f, hFN hf⟩ : ↥N) ∈ F' := hf
    have hf1' : (⟨f, hFN hf⟩ : ↥N) ≠ 1 := fun h => hf1 (congrArg Subtype.val h)
    have hd' : (⟨d, hdN⟩ : ↥N) ∈ involutionOddCore (⟨f, hFN hf⟩ : ↥N) :=
      subgroupOf_involutionOddCore_le (⟨f, hFN hf⟩ : ↥N) (Subgroup.mem_subgroupOf.mpr hd)
    have hg' : (⟨g, hFN hg⟩ : ↥N) ∈ F' := hg
    exact congrArg Subtype.val (hSC.2 _ hf' hf1' _ hd' _ hg' _ (hxmem x hx))

end CFSG.ClassicalInvolution.Balance.StrongBalance

module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510Pk
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510Inv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510CS

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure Sec510Stage1 (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G)
    (φ : (Fin 6 → ZMod 2) → G) (A : Subgroup G) (K₁ K₂ : Subgroup G) (a b : G) : Prop where
  pk : Sec510Pk G t L S z K₁ K₂
  ab : Sec510Ab t z a b φ A
  cs : S ⊓ centralizer (L : Set G) = zpowers t
  R_cases : sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂) = sec5p510_E t a b ∨
    (Nat.card ↥(sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)) = 16 ∧
      (sec5p510_E t a b).relIndex (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)) = 2)
  swap : (sec5p510_E t a b).relIndex (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)) = 2 →
    ∀ d ∈ sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂), d ∉ sec5p510_E t a b →
      d * a * d⁻¹ = b ∧ d * b * d⁻¹ = a
  T_cases : sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)) = sec5p510_E t a b ∨
    sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)) =
      sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)
  T_strong : ∀ x g : G, x ∈ sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)) →
    g ∈ centralizer ({z} : Set G) → g * x * g⁻¹ ∈ sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂) →
    g * x * g⁻¹ ∈ sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂))
  T_invol : ∀ x : G, x ∈ sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)) →
    x * x ∈ zpowers z → x ∉ zpowers z →
    ∃ y ∈ conjClassIn (centralizer ({z} : Set G)) t, x = y ∨ x = y * z

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r ρ : G}
  {B A : Subgroup G} {φ : (Fin 6 → ZMod 2) → G}

theorem sec5p510_stage1 (hy : Sec5B59Hyp) (h52a : Asc82Lemma52a) (hD : Asc82FactQCentOrd6)
    (hB : Asc82FactBCent6) (h4 : Asc82FactReflCentQ6) (hF0 : Asc82FactPockets6)
    (h : Sec510Ctx G t L S z r ρ B A φ) :
    ∃ (K₁ K₂ : Subgroup G) (a b : G), Sec510Stage1 G t L S z φ A K₁ K₂ a b := by
  obtain ⟨K₁, K₂, hk⟩ := sec5p510_exists_pk hy hF0 h.toSec5Ctx
  obtain ⟨a, b, hab⟩ := sec5p510_exists_ab h
  have hCS := sec5p510_CS hy h52a hB h
  refine ⟨K₁, K₂, a, b, hk, hab, hCS, sec5p510_R_cases hy hD h4 hCS h hk.q hab, ?_, ?_, ?_, ?_⟩
  · intro hrel d hdR hdE
    exact sec5p510_swap hy hD h4 hCS h hk.q hab hrel hdR hdE
  · exact sec5p510_T_cases hy hD h4 hCS h hk.q hab
  · intro x g hx hg hxR
    exact sec5p510_T_strong hy hD h4 hCS h hk.q hab hx hg hxR
  · intro x hxT hx2 hxz
    exact sec5p510_T_invol hy hD h4 hCS h hk.q hab hxT hx2 hxz

end CFSG.OddStandard.SmallF3.Omega

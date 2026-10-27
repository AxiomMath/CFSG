module

public import CFSG.ClassicalInvolution.Balance.Delta

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.SignalizerFunctorTheorem CFSG.Assembly.Dichotomy
open scoped commutatorElement

section Defs

variable {G : Type} [Group G]

@[expose] def uCore (F : Subgroup G) : Subgroup G :=
  ⨆ f ∈ F, ⨆ (_ : f ≠ 1), involutionOddCore f

@[expose] def alphaCore (F : Subgroup G) : Subgroup G :=
  normalClosureIn (uCore F) (⁅uCore F, F⁆ ⊔ deltaCore F)

end Defs

section Basic

variable {G : Type} [Group G] {F : Subgroup G}

theorem involutionOddCore_le_uCore {f : G} (hf : f ∈ F) (hf1 : f ≠ 1) :
    involutionOddCore f ≤ uCore F :=
  le_iSup₂_of_le f hf (le_iSup_of_le hf1 le_rfl)

theorem deltaCore_le_uCore {d : G} (hd : d ∈ F) (hd1 : d ≠ 1) : deltaCore F ≤ uCore F :=
  (deltaCore_le_involutionOddCore hd hd1).trans (involutionOddCore_le_uCore hd hd1)

theorem conj_mem_uCore {g : G} (hg : ∀ f ∈ F, g * f = f * g) {x : G} (hx : x ∈ uCore F) :
    g * x * g⁻¹ ∈ uCore F := by
  have hle : uCore F ≤ (uCore F).comap (MulAut.conj g).toMonoidHom := by
    refine iSup₂_le fun f hf => iSup_le fun hf1 => ?_
    intro y hy
    show g * y * g⁻¹ ∈ uCore F
    have hgC : g ∈ Subgroup.centralizer ({f} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hg f hf)
    exact involutionOddCore_le_uCore hf hf1 (conj_mem_oddCoreIn hgC hy)
  exact hle hx

theorem commutator_uCore_le (hF : ∀ f ∈ F, ∀ f' ∈ F, f * f' = f' * f) :
    ⁅uCore F, F⁆ ≤ uCore F := by
  rw [Subgroup.commutator_le]
  intro u hu f hf
  have h1 : f * u⁻¹ * f⁻¹ ∈ uCore F :=
    conj_mem_uCore (fun f' hf' => hF f hf f' hf') ((uCore F).inv_mem hu)
  have : ⁅u, f⁆ = u * (f * u⁻¹ * f⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [this]
  exact (uCore F).mul_mem hu h1

theorem deltaCore_le_alphaCore : deltaCore F ≤ alphaCore F :=
  le_sup_right.trans (le_normalClosureIn _ _)

theorem commutator_le_alphaCore : ⁅uCore F, F⁆ ≤ alphaCore F :=
  le_sup_left.trans (le_normalClosureIn _ _)

theorem conj_mem_alphaCore_of_mem_uCore {u : G} (hu : u ∈ uCore F) {x : G}
    (hx : x ∈ alphaCore F) : u * x * u⁻¹ ∈ alphaCore F :=
  conj_mem_normalClosureIn hu hx

theorem alphaCore_le_of_normalized {X : Subgroup G} (hS : ⁅uCore F, F⁆ ⊔ deltaCore F ≤ X)
    (hX : ∀ u ∈ uCore F, ∀ x ∈ X, u * x * u⁻¹ ∈ X) : alphaCore F ≤ X := by
  refine normalClosureIn_le fun g hg => ?_
  rintro _ ⟨y, hy, rfl⟩
  exact hX g hg y (hS hy)

theorem alphaCore_le_uCore (hF : ∀ f ∈ F, ∀ f' ∈ F, f * f' = f' * f) {d : G} (hd : d ∈ F)
    (hd1 : d ≠ 1) : alphaCore F ≤ uCore F := by
  refine alphaCore_le_of_normalized (sup_le (commutator_uCore_le hF) (deltaCore_le_uCore hd hd1))
    ?_
  intro u hu x hx
  exact (uCore F).mul_mem ((uCore F).mul_mem hu hx) ((uCore F).inv_mem hu)

theorem conj_mem_commutator_uCore {g : G} (hg : ∀ f ∈ F, g * f = f * g) {y : G}
    (hy : y ∈ ⁅uCore F, F⁆) : g * y * g⁻¹ ∈ ⁅uCore F, F⁆ := by
  have hle : ⁅uCore F, F⁆ ≤ (⁅uCore F, F⁆).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro u hu f hf
    show g * ⁅u, f⁆ * g⁻¹ ∈ ⁅uCore F, F⁆
    have hf' : g * f * g⁻¹ = f := by rw [hg f hf]; group
    have : g * ⁅u, f⁆ * g⁻¹ = ⁅g * u * g⁻¹, f⁆ := by
      calc g * ⁅u, f⁆ * g⁻¹ = ⁅g * u * g⁻¹, g * f * g⁻¹⁆ := by
            simp only [commutatorElement_def]
            group
        _ = ⁅g * u * g⁻¹, f⁆ := by rw [hf']
    rw [this]
    exact Subgroup.commutator_mem_commutator (conj_mem_uCore hg hu) hf
  exact hle hy

theorem conj_mem_alphaCore {g : G} (hg : ∀ f ∈ F, g * f = f * g) {x : G} (hx : x ∈ alphaCore F) :
    g * x * g⁻¹ ∈ alphaCore F := by
  have hS : ⁅uCore F, F⁆ ⊔ deltaCore F ≤
      (⁅uCore F, F⁆ ⊔ deltaCore F).comap (MulAut.conj g).toMonoidHom := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · exact (le_sup_left : ⁅uCore F, F⁆ ≤ ⁅uCore F, F⁆ ⊔ deltaCore F)
        (conj_mem_commutator_uCore hg hy)
    · exact (le_sup_right : deltaCore F ≤ ⁅uCore F, F⁆ ⊔ deltaCore F) (conj_mem_deltaCore hg hy)
  have hle : alphaCore F ≤ (alphaCore F).comap (MulAut.conj g).toMonoidHom := by
    refine normalClosureIn_le fun h hh => ?_
    rintro _ ⟨y, hy, rfl⟩
    show g * (h * y * h⁻¹) * g⁻¹ ∈ alphaCore F
    have hgy : g * y * g⁻¹ ∈ ⁅uCore F, F⁆ ⊔ deltaCore F := hS hy
    have e : g * (h * y * h⁻¹) * g⁻¹ = (g * h * g⁻¹) * (g * y * g⁻¹) * (g * h * g⁻¹)⁻¹ := by
      group
    rw [e]
    exact conj_mem_normalClosureIn (conj_mem_uCore hg hh) (le_normalClosureIn _ _ hgy)
  exact hle hx

end Basic

section Index

variable {G : Type} [Group G] [Finite G]

theorem mem_or_inv_mul_mem {A F : Subgroup G} (hFA : F ≤ A) (hcard : Nat.card A = 2 * Nat.card F)
    {y g : G} (hy : y ∈ A) (hyF : y ∉ F) (hg : g ∈ A) : g ∈ F ∨ y⁻¹ * g ∈ F := by
  have hpos : 0 < Nat.card F := Nat.card_pos
  have h2 : F.relIndex A = 2 := by
    have h := Subgroup.relIndex_mul_card (H := F) (K := A)
    rw [inf_eq_left.mpr hFA, hcard] at h
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h, mul_comm])
  obtain ⟨a, haA, ha⟩ := Subgroup.relIndex_eq_two_iff'.mp h2
  by_cases hgF : g ∈ F
  · exact Or.inl hgF
  · right
    have h1 := ha g hg
    have h3 := ha y hy
    have hag : a * g ∈ F := by
      rcases h1 with ⟨h, _⟩ | ⟨h, h'⟩
      · exact h
      · exact absurd h hgF
    have hay : a * y ∈ F := by
      rcases h3 with ⟨h, _⟩ | ⟨h, h'⟩
      · exact h
      · exact absurd h hyF
    have : y⁻¹ * g = (a * y)⁻¹ * (a * g) := by group
    rw [this]
    exact F.mul_mem (F.inv_mem hay) hag

omit [Finite G] in
theorem card_zpowers_of_involution {d : G} (hd : d * d = 1) (hd1 : d ≠ 1) :
    Nat.card (Subgroup.zpowers d) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two]; exact hd) hd1

omit [Finite G] in
theorem mem_zpowers_involution {d x : G} (hd : d * d = 1) (hx : x ∈ Subgroup.zpowers d) :
    x = 1 ∨ x = d := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hsq : d ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hd
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [← Int.emod_add_mul_ediv k 2, h, zpow_add, zpow_mul, hsq]
    simp
  · right
    rw [← Int.emod_add_mul_ediv k 2, h, zpow_add, zpow_mul, hsq]
    simp

end Index

end CFSG.ClassicalInvolution.Balance.Bootstrap

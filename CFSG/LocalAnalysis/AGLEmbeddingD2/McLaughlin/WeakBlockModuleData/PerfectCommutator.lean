module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutator_le_of_le_normalizer {L V : Subgroup G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) : ⁅V, L⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro v hv l hl
  have h1 : l * v⁻¹ * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hLV hl) v⁻¹).mp (V.inv_mem hv)
  have : ⁅v, l⁆ = v * (l * v⁻¹ * l⁻¹) := by simp [commutatorElement_def, mul_assoc]
  rw [this]
  exact V.mul_mem hv h1

theorem conj_mem_commutator {L X : Subgroup G} (hLX : L ≤ Subgroup.normalizer (X : Set G))
    {y : G} (hy : y ∈ ⁅X, L⁆) {ℓ : G} (hℓ : ℓ ∈ L) : ℓ * y * ℓ⁻¹ ∈ ⁅X, L⁆ := by
  have hmap := Subgroup.map_commutator X L (MulAut.conj ℓ).toMonoidHom
  have hX : X.map (MulAut.conj ℓ).toMonoidHom = X := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hLX hℓ) w).mp hw
    · intro hz
      refine ⟨ℓ⁻¹ * z * ℓ, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      have := (Subgroup.mem_normalizer_iff.mp (hLX (L.inv_mem hℓ)) z).mp hz
      simpa using this
  have hL : L.map (MulAut.conj ℓ).toMonoidHom = L := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have : ℓ * w * ℓ⁻¹ ∈ L := L.mul_mem (L.mul_mem hℓ hw) (L.inv_mem hℓ)
      simpa [MulAut.conj_apply] using this
    · intro hz
      refine ⟨ℓ⁻¹ * z * ℓ, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      exact L.mul_mem (L.mul_mem (L.inv_mem hℓ) hz) hℓ
  rw [hX, hL] at hmap
  rw [← hmap]
  exact Subgroup.mem_map.mpr ⟨y, hy, by simp [MulAut.conj_apply]⟩

theorem le_normalizer_of_forall_conj_mem {L Z : Subgroup G}
    (h : ∀ ℓ ∈ L, ∀ y ∈ Z, ℓ * y * ℓ⁻¹ ∈ Z) : L ≤ Subgroup.normalizer (Z : Set G) := by
  intro ℓ hℓ
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h ℓ hℓ x, fun hx => ?_⟩
  have := h ℓ⁻¹ (L.inv_mem hℓ) _ hx
  have e : ℓ⁻¹ * (ℓ * x * ℓ⁻¹) * ℓ⁻¹⁻¹ = x := by group
  rwa [e] at this

theorem commutator_le_commutator_commutator_of_perfect {L V : Subgroup G} (hL : ⁅L, L⁆ = L)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) :
    ⁅V, L⁆ ≤ ⁅⁅V, L⁆, L⁆ := by
  set X : Subgroup G := ⁅V, L⁆ with hXdef
  set Y : Subgroup G := ⁅X, L⁆ with hYdef
  have hXV : X ≤ V := commutator_le_of_le_normalizer hLV
  have hLX : L ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_of_forall_conj_mem fun ℓ hℓ y hy => conj_mem_commutator (X := V) hLV hy hℓ
  have hYX : Y ≤ X := commutator_le_of_le_normalizer hLX
  have hLY : L ≤ Subgroup.normalizer (Y : Set G) :=
    le_normalizer_of_forall_conj_mem fun ℓ hℓ y hy => conj_mem_commutator (X := X) hLX hy hℓ
  have hYconj : ∀ ℓ ∈ L, ∀ y ∈ Y, ℓ * y * ℓ⁻¹ ∈ Y := fun ℓ hℓ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hLY hℓ) y).mp hy
  let Λ : Subgroup G :=
    { carrier := {ℓ | ℓ ∈ L ∧ ∀ v ∈ V, ⁅ℓ, v⁆ ∈ Y}
      one_mem' := ⟨L.one_mem, fun v _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨haL, ha⟩ ⟨hbL, hb⟩
        refine ⟨L.mul_mem haL hbL, fun v hv => ?_⟩
        have e : ⁅a * b, v⁆ = a * ⁅b, v⁆ * a⁻¹ * ⁅a, v⁆ := by
          simp [commutatorElement_def]; group
        rw [e]
        exact Y.mul_mem (hYconj a haL _ (hb v hv)) (ha v hv)
      inv_mem' := by
        rintro a ⟨haL, ha⟩
        refine ⟨L.inv_mem haL, fun v hv => ?_⟩
        have e : ⁅a⁻¹, v⁆ = a⁻¹ * ⁅a, v⁆⁻¹ * a := by
          simp [commutatorElement_def]; group
        rw [e]
        have := hYconj a⁻¹ (L.inv_mem haL) _ (Y.inv_mem (ha v hv))
        simpa using this }
  have hΛ : ⁅L, L⁆ ≤ Λ := by
    rw [Subgroup.commutator_le]
    intro l₁ hl₁ l₂ hl₂
    refine ⟨(Subgroup.commutator_mem_commutator hl₁ hl₂ : ⁅l₁, l₂⁆ ∈ ⁅L, L⁆) |> fun h => ?_, ?_⟩
    · rw [hL] at h; exact h
    · intro v hv
      have hw := conj_commutatorElement_left_commutatorElement_mul l₁⁻¹ l₂ v
      simp only [inv_inv] at hw
      set T₁ := ⁅⁅l₁, l₂⁆, v⁆ with hT₁
      set T₂ := ⁅⁅v⁻¹, l₁⁻¹⁆, l₂⁆ with hT₂
      set T₃ := ⁅⁅l₂⁻¹, v⁆, l₁⁻¹⁆ with hT₃
      have hx₂ : ⁅v⁻¹, l₁⁻¹⁆ ∈ X := Subgroup.commutator_mem_commutator (V.inv_mem hv) (L.inv_mem hl₁)
      have hT₂Y : T₂ ∈ Y := Subgroup.commutator_mem_commutator hx₂ hl₂
      have hx₃ : ⁅l₂⁻¹, v⁆ ∈ X := by
        have : ⁅l₂⁻¹, v⁆ = ⁅v, l₂⁻¹⁆⁻¹ := (commutatorElement_inv v l₂⁻¹).symm
        rw [this]
        exact X.inv_mem (Subgroup.commutator_mem_commutator hv (L.inv_mem hl₂))
      have hT₃Y : T₃ ∈ Y := Subgroup.commutator_mem_commutator hx₃ (L.inv_mem hl₁)
      have hT₂V : T₂ ∈ V := hXV (hYX hT₂Y)
      have hc : v * T₂ * v⁻¹ = T₂ := by rw [hVc v hv T₂ hT₂V]; group
      have hb : l₂ * T₃ * l₂⁻¹ ∈ Y := hYconj l₂ hl₂ _ hT₃Y
      have hkey : l₁⁻¹ * T₁ * l₁ = (T₂ * (l₂ * T₃ * l₂⁻¹))⁻¹ := by
        have h1 : l₁⁻¹ * T₁ * l₁ * (v * T₂ * v⁻¹) * (l₂ * T₃ * l₂⁻¹) = 1 := by
          rw [← hw]; group
        rw [hc, mul_assoc] at h1
        exact eq_inv_of_mul_eq_one_left h1
      have hmem : l₁⁻¹ * T₁ * l₁ ∈ Y := by
        rw [hkey]; exact Y.inv_mem (Y.mul_mem hT₂Y hb)
      have := hYconj l₁ hl₁ _ hmem
      have e : l₁ * (l₁⁻¹ * T₁ * l₁) * l₁⁻¹ = T₁ := by group
      rwa [e] at this
  have hLΛ : ∀ ℓ ∈ L, ∀ v ∈ V, ⁅ℓ, v⁆ ∈ Y := fun ℓ hℓ v hv => by
    have : ℓ ∈ Λ := hΛ (by rw [hL]; exact hℓ)
    exact this.2 v hv
  rw [Subgroup.commutator_le]
  intro v hv l hl
  have e : ⁅v, l⁆ = ⁅l, v⁆⁻¹ := (commutatorElement_inv l v).symm
  rw [e]
  exact Y.inv_mem (hLΛ l hl v hv)

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

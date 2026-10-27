module

public import CFSG.GH74.GLS.C3.Layer1.P34Cfg

public section

namespace CFSG.GH74.GLS.C3.Layer1.P34

open Subgroup

variable {X : Type} [Group X]

theorem cyclic_aut_comm {A : Subgroup X} [IsCyclic ↥A] {u v : X}
    (hu : ∀ a ∈ A, u * a * u⁻¹ ∈ A) (hv : ∀ a ∈ A, v * a * v⁻¹ ∈ A) :
    ∀ a ∈ A, u * (v * a * v⁻¹) * u⁻¹ = v * (u * a * u⁻¹) * v⁻¹ := by
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := ↥A)
  obtain ⟨r, hr⟩ := mem_zpowers_iff.1 (hg₀ ⟨u * (g₀ : X) * u⁻¹, hu _ g₀.2⟩)
  obtain ⟨s, hs⟩ := mem_zpowers_iff.1 (hg₀ ⟨v * (g₀ : X) * v⁻¹, hv _ g₀.2⟩)
  have hr' : (g₀ : X) ^ r = u * (g₀ : X) * u⁻¹ := by
    have := congrArg Subtype.val hr
    simpa using this
  have hs' : (g₀ : X) ^ s = v * (g₀ : X) * v⁻¹ := by
    have := congrArg Subtype.val hs
    simpa using this
  intro a ha
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hg₀ ⟨a, ha⟩)
  have hak : a = (g₀ : X) ^ k := by
    have := congrArg Subtype.val hk
    simpa using this.symm
  rw [hak]
  have e1 : ∀ (w : X) (m : ℤ), w * (g₀ : X) ^ m * w⁻¹ = (w * (g₀ : X) * w⁻¹) ^ m :=
    fun w m => conj_zpow.symm
  calc u * (v * (g₀ : X) ^ k * v⁻¹) * u⁻¹
      = u * ((v * (g₀ : X) * v⁻¹) ^ k) * u⁻¹ := by rw [e1 v k]
    _ = u * (((g₀ : X) ^ s) ^ k) * u⁻¹ := by rw [← hs']
    _ = u * (g₀ : X) ^ (s * k) * u⁻¹ := by rw [← zpow_mul]
    _ = (u * (g₀ : X) * u⁻¹) ^ (s * k) := e1 u (s * k) |>.symm ▸ rfl
    _ = ((g₀ : X) ^ r) ^ (s * k) := by rw [← hr']
    _ = (g₀ : X) ^ (r * (s * k)) := by rw [← zpow_mul]
    _ = (g₀ : X) ^ (s * (r * k)) := by congr 1; ring
    _ = ((g₀ : X) ^ s) ^ (r * k) := by rw [← zpow_mul]
    _ = (v * (g₀ : X) * v⁻¹) ^ (r * k) := by rw [← hs']
    _ = v * (g₀ : X) ^ (r * k) * v⁻¹ := (e1 v (r * k)).symm
    _ = v * (((g₀ : X) ^ r) ^ k) * v⁻¹ := by rw [← zpow_mul]
    _ = v * ((u * (g₀ : X) * u⁻¹) ^ k) * v⁻¹ := by rw [← hr']
    _ = v * (u * (g₀ : X) ^ k * u⁻¹) * v⁻¹ := by rw [e1 u k]

theorem comm_cent_cyclic {A T : Subgroup X} [IsCyclic ↥A] (hA : ∀ t ∈ T, ∀ a ∈ A, t * a * t⁻¹ ∈ A)
    {a b : X} (ha : a ∈ T) (hb : b ∈ T) :
    ∀ c ∈ A, (a * b * a⁻¹ * b⁻¹) * c = c * (a * b * a⁻¹ * b⁻¹) := by
  intro c hc
  have hu : ∀ y ∈ A, a⁻¹ * y * a⁻¹⁻¹ ∈ A := fun y hy => hA a⁻¹ (T.inv_mem ha) y hy
  have hv : ∀ y ∈ A, b⁻¹ * y * b⁻¹⁻¹ ∈ A := fun y hy => hA b⁻¹ (T.inv_mem hb) y hy
  have hE := cyclic_aut_comm hu hv c hc
  have hE' : a⁻¹ * (b⁻¹ * c * b) * a = b⁻¹ * (a⁻¹ * c * a) * b := by simpa using hE
  have key : (a * b * a⁻¹ * b⁻¹) * c * (a * b * a⁻¹ * b⁻¹)⁻¹ = c := by
    calc (a * b * a⁻¹ * b⁻¹) * c * (a * b * a⁻¹ * b⁻¹)⁻¹
        = (a * b) * (a⁻¹ * (b⁻¹ * c * b) * a) * (a * b)⁻¹ := by group
      _ = (a * b) * (b⁻¹ * (a⁻¹ * c * a) * b) * (a * b)⁻¹ := by rw [hE']
      _ = c := by group
  calc (a * b * a⁻¹ * b⁻¹) * c
      = ((a * b * a⁻¹ * b⁻¹) * c * (a * b * a⁻¹ * b⁻¹)⁻¹) * (a * b * a⁻¹ * b⁻¹) := by group
    _ = c * (a * b * a⁻¹ * b⁻¹) := by rw [key]

theorem normalized_of_unique_cyclic {A P T : Subgroup X} [Finite X] (hAP : A ≤ P) (hAc : IsCyclic ↥A)
    (hAuniq : ∀ B : Subgroup X, B ≤ P → IsCyclic ↥B → Nat.card ↥B = Nat.card ↥A → B = A)
    (hP : ∀ t ∈ T, ∀ a ∈ P, t * a * t⁻¹ ∈ P) : ∀ t ∈ T, ∀ a ∈ A, t * a * t⁻¹ ∈ A := by
  intro t ht a ha
  set φ : X →* X := (MulAut.conj t).toMonoidHom with hφ
  have hinj : Function.Injective φ := (MulAut.conj t).injective
  have hB : A.map φ = A := by
    refine hAuniq _ ?_ ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hP t ht y (hAP hy)
    · have e := Subgroup.equivMapOfInjective A φ hinj
      exact isCyclic_of_surjective e.toMonoidHom e.surjective
    · exact Subgroup.card_map_of_injective hinj
  have : φ a ∈ A.map φ := ⟨a, ha, rfl⟩
  rw [hB] at this
  simpa [hφ] using this

end CFSG.GH74.GLS.C3.Layer1.P34

module

public import CFSG.LieType.CurtisTits.Recognition

public section

namespace CFSG.LieType.CurtisTits

open Subgroup

universe u v w

variable {K : Type u} [Group K] {ι : Type v} [Preorder ι] (L : ι → Subgroup K)

@[expose] def IsCompatible {G : Type w} [Group G] (φ : ∀ i, L i →* G) : Prop :=
  ∀ i j, i ≤ j → ∀ (x : L i) (y : L j), (x : K) = y → φ i x = φ j y

@[expose] def IsUniversalCompletion : Prop :=
  ∀ (G : Type w) [Group G] (φ : ∀ i, L i →* G), IsCompatible L φ →
    ∃! ψ : K →* G, ∀ i (x : L i), ψ x = φ i x

variable {L}

omit [Preorder ι] in
theorem hom_ext_of_iSup_eq_top (hgen : ⨆ i, L i = ⊤) {G : Type w} [Group G] {ψ₁ ψ₂ : K →* G}
    (h : ∀ i (x : L i), ψ₁ x = ψ₂ x) : ψ₁ = ψ₂ := by
  have hle : (⊤ : Subgroup K) ≤ MonoidHom.eqLocus ψ₁ ψ₂ := by
    rw [← hgen, iSup_le_iff]
    intro i x hx
    exact h i ⟨x, hx⟩
  ext x
  exact hle (Subgroup.mem_top x)

omit [Preorder ι] in
theorem range_eq_iSup_map_of_iSup_eq_top (hgen : ⨆ i, L i = ⊤) {G : Type w} [Group G]
    (ψ : K →* G) : ψ.range = ⨆ i, (L i).map ψ := by
  rw [MonoidHom.range_eq_map, ← hgen, Subgroup.map_iSup]

theorem recognition_of_isUniversalCompletion (hgen : ⨆ i, L i = ⊤) (hK : IsQuasisimple K)
    (hU : IsUniversalCompletion.{u, v, w} L) {G : Type w} [Group G] (φ : ∀ i, L i →* G)
    (hφ : IsCompatible L φ) (hGgen : ⨆ i, (φ i).range = ⊤) (hnt : ∃ i, ∃ x : L i, φ i x ≠ 1) :
    ∃ ψ : K →* G, (∀ i (x : L i), ψ x = φ i x) ∧ Function.Surjective ψ ∧ ψ.ker ≤ center K ∧
      IsQuasisimple G ∧ center G = (center K).map ψ ∧ Nonempty (K ⧸ ψ.ker ≃* G) := by
  obtain ⟨ψ, hψ, -⟩ := hU G φ hφ
  have hrange : ψ.range = ⊤ := by
    rw [range_eq_iSup_map_of_iSup_eq_top hgen, ← hGgen]
    congr 1
    ext i : 1
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, (hψ i ⟨x, hx⟩).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, hψ i x⟩
  have hsurj : Function.Surjective ψ := MonoidHom.range_eq_top.mp hrange
  have hnt' : ∃ k, ψ k ≠ 1 := by
    obtain ⟨i, x, hx⟩ := hnt
    exact ⟨x, by rw [hψ i x]; exact hx⟩
  have hker := ker_le_center_of_isQuasisimple hK hnt'
  exact ⟨ψ, hψ, hsurj, hker, isQuasisimple_of_surjective hK hsurj hnt',
    center_eq_map_center_of_isQuasisimple hK hsurj hker,
    ⟨QuotientGroup.quotientKerEquivOfSurjective ψ hsurj⟩⟩

theorem exists_surjective_ker_le_center_of_isUniversalCompletion (hgen : ⨆ i, L i = ⊤)
    (hK : IsQuasisimple K) (hU : IsUniversalCompletion.{u, v, w} L) (hnt : ∃ i, L i ≠ ⊥)
    {G : Type w} [Group G] (M : ι → Subgroup G) (hMgen : ⨆ i, M i = ⊤)
    (ψ : ∀ i, L i ≃* M i)
    (hψ : ∀ i j, i ≤ j → ∀ (x : L i) (y : L j), (x : K) = y → (ψ i x : G) = ψ j y) :
    ∃ θ : K →* G, (∀ i (x : L i), θ x = ψ i x) ∧ Function.Surjective θ ∧ θ.ker ≤ center K := by
  let φ : ∀ i, L i →* G := fun i => (M i).subtype.comp (ψ i).toMonoidHom
  have hφ : IsCompatible L φ := fun i j hij x y hxy => hψ i j hij x y hxy
  have hrange : ∀ i, (φ i).range = M i := by
    intro i
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact (ψ i x).2
    · intro hg
      exact ⟨(ψ i).symm ⟨g, hg⟩, by simp [φ]⟩
  have hGgen : ⨆ i, (φ i).range = ⊤ := by simpa only [hrange] using hMgen
  have hnt' : ∃ i, ∃ x : L i, φ i x ≠ 1 := by
    obtain ⟨i, hi⟩ := hnt
    obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hi
    refine ⟨i, x, ?_⟩
    intro h
    apply hx1
    have : (ψ i x : G) = 1 := h
    have h2 : ψ i x = 1 := Subtype.ext this
    exact (ψ i).injective (h2.trans (map_one _).symm)
  obtain ⟨θ, hθ, hsurj, hker, -⟩ :=
    recognition_of_isUniversalCompletion hgen hK hU φ hφ hGgen hnt'
  exact ⟨θ, hθ, hsurj, hker⟩

end CFSG.LieType.CurtisTits

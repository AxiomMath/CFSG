module

public import CFSG.Fischer.Classification.Uniqueness.Star

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer

variable {X Y : Type} [Group X] [Group Y] {E : Set X} {F : Set Y}

theorem starImage_mem_localImages {d : X} (f : LocalClass E d) :
    starImage E d f ∈ LocalImages E d := by
  rw [← range_starImage]
  exact ⟨f, rfl⟩

theorem Pair.exists_starEquiv_of_localQuotient (hE : Pair X E) (hF : Pair Y F) {d : X} {d' : Y}
    (hiE : Function.Injective (starImage E d)) (hiF : Function.Injective (starImage F d'))
    (α : LocalQuotient E d ≃* LocalQuotient F d') (hα : α '' LocalImages E d = LocalImages F d') :
    ∃ φ : LocalClass E d ≃ LocalClass F d', (∀ f, starImage F d' (φ f) = α (starImage E d f)) ∧
      (∀ f g : LocalClass E d, (f : X) * g = g * f ↔ (φ f : Y) * φ g = φ g * φ f) ∧
      ∀ (f g : LocalClass E d) (h : (f : X) * g * f ∈ LocalClass E d),
        (φ ⟨_, h⟩ : Y) = φ f * φ g * φ f := by
  have hex : ∀ f : LocalClass E d, ∃ g : LocalClass F d',
      starImage F d' g = α (starImage E d f) := by
    intro f
    have : α (starImage E d f) ∈ LocalImages F d' := by
      rw [← hα]
      exact ⟨_, starImage_mem_localImages f, rfl⟩
    rw [← range_starImage] at this
    exact this
  choose φ₀ hφ₀ using hex
  have hbij : Function.Bijective φ₀ := by
    refine ⟨fun f f' h => hiE (α.injective (by rw [← hφ₀, ← hφ₀, h])), fun g => ?_⟩
    have : starImage F d' g ∈ α '' LocalImages E d := by
      rw [hα]
      exact starImage_mem_localImages g
    obtain ⟨q, hq, hqg⟩ := this
    rw [← range_starImage] at hq
    obtain ⟨f, rfl⟩ := hq
    exact ⟨f, hiF (by rw [hφ₀, hqg])⟩
  let φ := Equiv.ofBijective φ₀ hbij
  have hφ : ∀ f, starImage F d' (φ f) = α (starImage E d f) := hφ₀
  refine ⟨φ, hφ, fun f g => ?_, fun f g h => ?_⟩
  · rw [← commute_iff_eq, ← commute_iff_eq, ← Pair.starImage_commute_iff hE,
      ← Pair.starImage_commute_iff hF, hφ, hφ]
    exact (commute_map_iff α.injective).symm
  · have h' := Pair.mul_mul_mem_localClass_of_mem hF (φ f).2 (φ g).2
    have : φ ⟨_, h⟩ = ⟨_, h'⟩ := hiF (by
      rw [hφ, starImage_conj f g h, map_mul, map_mul, starImage_conj (φ f) (φ g) h', hφ, hφ])
    exact congrArg Subtype.val this

theorem starMap_eq_of_image_eq {d : X} {d' : Y} (φ : LocalClass E d ≃ LocalClass F d')
    (α : LocalQuotient E d ≃* LocalQuotient F d')
    (hφ : ∀ f, starImage F d' (φ f) = α (starImage E d f))
    (hiF : Function.Injective (starImage F d')) {O : Set X} {O' : Set Y}
    (hO' : O' ⊆ LocalClass F d')
    (h : α '' (starImage E d '' {f | (f : X) ∈ O}) = starImage F d' '' {g | (g : Y) ∈ O'}) :
    starMap φ O = O' := by
  ext y
  constructor
  · rintro ⟨f, hf, rfl⟩
    have : starImage F d' (φ f) ∈ starImage F d' '' {g | (g : Y) ∈ O'} := by
      rw [← h, hφ]
      exact ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    obtain ⟨g, hg, hgf⟩ := this
    rw [← hiF hgf]
    exact hg
  · intro hy
    have : starImage F d' ⟨y, hO' hy⟩ ∈ α '' (starImage E d '' {f | (f : X) ∈ O}) := by
      rw [h]
      exact ⟨_, hy, rfl⟩
    obtain ⟨_, ⟨f, hf, rfl⟩, hfy⟩ := this
    refine ⟨f, hf, ?_⟩
    rw [hiF ((hφ f).trans hfy)]

end CFSG.Fischer.Classification

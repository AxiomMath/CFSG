module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44Frame
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Finite

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup

structure FrameModelG (G : Type) [Group G] (L E : Subgroup G) (t : G) (O : Fin 5 → Set G) :
    Prop where
  t_mem : t ∈ E
  t_ne_one : t ≠ 1
  card_N : Nat.card ↥(normalizer (E : Set G) ⊓ L) = 2 ^ 11 * 443520
  isOrbit : ∀ i, ∃ x ∈ E, O i = {y | ∃ n ∈ normalizer (E : Set G) ⊓ L, n * x * n⁻¹ = y}
  ncard : ∀ i, (O i).ncard = ![22, 22, 231, 231, 1540] i
  disjoint : ∀ i j, i ≠ j → Disjoint (O i) (O j)
  not_mem_one : ∀ i, (1 : G) ∉ O i
  not_mem_t : ∀ i, t ∉ O i
  cover : ∀ v ∈ E, v ≠ 1 → v = t ∨ ∃ i, v ∈ O i
  swap : O 1 = (fun u => t * u) '' O 0
  prod : ∀ u ∈ O 0, ∀ u' ∈ O 0, u ≠ u' → u * u' ∈ O 2
  gen : Subgroup.closure (insert t (O 0)) = E
  frameAut : ∀ α : E ≃* E, (∀ e : E, (e : G) = t → (α e : G) = t) →
    (∀ e : E, (e : G) ∈ O 0 → (α e : G) ∈ O 0) →
    ∃ n ∈ normalizer (E : Set G) ⊓ L, ∀ e : E, (α e : G) = n * e * n⁻¹

namespace FrameModel

variable {Λ G : Type} [Group Λ] [Group G]

theorem mem_normalizer_map_iff {E : Subgroup Λ} {ι : Λ →* G} (hι : Function.Injective ι)
    {n : Λ} : ι n ∈ normalizer ((E.map ι : Subgroup G) : Set G) ↔ n ∈ normalizer (E : Set Λ) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h x
    have := h (ι x)
    rw [← map_inv, ← map_mul, ← map_mul, Subgroup.mem_map_iff_mem hι,
      Subgroup.mem_map_iff_mem hι] at this
    exact this
  · intro h y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨n * x * n⁻¹, (h x).1 hx, ?_⟩
      simp
    · rintro ⟨x', hx', hy'⟩
      have hx : n⁻¹ * x' * n ∈ E := by
        have := (h (n⁻¹ * x' * n)).2
        rw [show n * (n⁻¹ * x' * n) * n⁻¹ = x' by group] at this
        exact this hx'
      refine ⟨n⁻¹ * x' * n, hx, ?_⟩
      have h2 : y = ι n⁻¹ * (ι x') * ι n := by
        rw [hy']
        simp [mul_assoc]
      rw [h2]
      simp

theorem toG {E : Subgroup Λ} {z : Λ} {O : Fin 5 → Set Λ} (F : FrameModel Λ E z O) (ι : Λ →* G)
    (hι : Function.Injective ι) :
    FrameModelG G ι.range (E.map ι) (ι z) (fun i => ι '' O i) where
  t_mem := Subgroup.mem_map_of_mem ι F.z_mem
  t_ne_one := fun h => F.z_ne_one (hι (by rw [h, map_one]))
  card_N := by
    have hN : normalizer ((E.map ι : Subgroup G) : Set G) ⊓ ι.range =
        (normalizer (E : Set Λ)).map ι := by
      ext g
      constructor
      · rintro ⟨hg, ⟨n, rfl⟩⟩
        exact ⟨n, (mem_normalizer_map_iff hι).1 hg, rfl⟩
      · rintro ⟨n, hn, rfl⟩
        exact ⟨(mem_normalizer_map_iff hι).2 hn, n, rfl⟩
    rw [hN, Subgroup.card_map_of_injective hι]
    exact F.card_N
  isOrbit := fun i => by
    obtain ⟨x, hx, hO⟩ := F.isOrbit i
    refine ⟨ι x, Subgroup.mem_map_of_mem ι hx, ?_⟩
    ext y
    constructor
    · rintro ⟨y₀, hy₀, rfl⟩
      rw [hO] at hy₀
      obtain ⟨n, hn, rfl⟩ := hy₀
      refine ⟨ι n, ⟨(mem_normalizer_map_iff hι).2 hn, n, rfl⟩, ?_⟩
      simp
    · rintro ⟨m, ⟨hm, n, rfl⟩, rfl⟩
      have hn := (mem_normalizer_map_iff hι).1 hm
      refine ⟨n * x * n⁻¹, ?_, by simp⟩
      rw [hO]
      exact ⟨n, hn, rfl⟩
  ncard := fun i => by rw [Set.ncard_image_of_injective _ hι]; exact F.ncard i
  disjoint := fun i j hij => (Set.disjoint_image_iff hι).2 (F.disjoint i j hij)
  not_mem_one := fun i h => by
    obtain ⟨y, hy, hy1⟩ := h
    have : y = 1 := hι (hy1.trans (map_one ι).symm)
    exact F.not_mem_one i (this ▸ hy)
  not_mem_t := fun i h => by
    obtain ⟨y, hy, hy1⟩ := h
    exact F.not_mem_z i ((hι hy1) ▸ hy)
  cover := by
    intro v hv hv1
    obtain ⟨e, he, rfl⟩ := hv
    have he1 : e ≠ 1 := fun h => hv1 (by rw [h, map_one])
    rcases F.cover e he he1 with h | ⟨i, hi⟩
    · exact Or.inl (by rw [h])
    · exact Or.inr ⟨i, e, hi, rfl⟩
  swap := by
    rw [F.swap, Set.image_image, Set.image_image]
    simp only [map_mul]
  prod := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩ hne
    exact ⟨u * u', F.prod u hu u' hu' (fun h => hne (by rw [h])), map_mul ι u u'⟩
  gen := by
    have : insert (ι z) (ι '' O 0) = ι '' insert z (O 0) := (Set.image_insert_eq).symm
    rw [this, ← MonoidHom.map_closure, F.gen]
  frameAut := by
    intro α hαt hα0
    set eqv : E ≃* E.map ι := Subgroup.equivMapOfInjective E ι hι with heqv
    set α' : E ≃* E := eqv.trans (α.trans eqv.symm) with hα'
    have hcoe : ∀ e : E, ((eqv e : E.map ι) : G) = ι e := fun e => rfl
    have key : ∀ e : E, ((α (eqv e) : E.map ι) : G) = ι (α' e : Λ) := by
      intro e
      have : eqv (α' e) = α (eqv e) := by simp [hα']
      rw [← this]
      rfl
    obtain ⟨n, hn, hnα⟩ := F.frameAut α' (by
      intro e he
      apply hι
      rw [← key e]
      exact hαt (eqv e) (by rw [hcoe, he])) (by
      intro e he
      have := hα0 (eqv e) ⟨e, he, (hcoe e).symm⟩
      obtain ⟨y, hy, hy2⟩ := this
      rw [key e] at hy2
      rwa [← hι hy2])
    refine ⟨ι n, ⟨(mem_normalizer_map_iff hι).2 hn, n, rfl⟩, fun e' => ?_⟩
    obtain ⟨e, rfl⟩ := eqv.surjective e'
    rw [key e, hnα e, hcoe e]
    simp

end FrameModel

end CFSG.EvenSporadicStandard.TwoFi22.DS81

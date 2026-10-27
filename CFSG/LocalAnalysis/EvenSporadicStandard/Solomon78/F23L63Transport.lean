module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.F23L63Perm

public section

namespace CFSG.EvenSporadicStandard.Solomon78.F23L63

open Subgroup CFSG.Sporadic.Fi23 CFSG.EvenSporadicStandard.TwoFi22
open CFSG.EvenSporadicStandard.TwoFi22.FrameJ
open CFSG.Blueprint.NativeSporadic (Carrier)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option linter.unusedSectionVars false

section Generic

variable {A B : Type} [Group A] [Group B] {φ : A →* B}

theorem mem_normalizer_map_iff (hφ : Function.Injective φ) {E : Subgroup A} {n : A} :
    φ n ∈ normalizer ((E.map φ : Subgroup B) : Set B) ↔ n ∈ normalizer (E : Set A) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    have := h (φ y)
    rwa [Subgroup.mem_map_iff_mem hφ, ← map_mul, ← map_inv, ← map_mul,
      Subgroup.mem_map_iff_mem hφ] at this
  · intro h g
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨n * y * n⁻¹, (h y).1 hy, by simp⟩
    · rintro ⟨z, hz, hzg⟩
      refine ⟨n⁻¹ * z * n, ?_, ?_⟩
      · have e : n * (n⁻¹ * z * n) * n⁻¹ = z := by group
        have := (h (n⁻¹ * z * n)).2 (by rw [e]; exact hz)
        exact this
      · rw [map_mul, map_mul, map_inv, hzg]
        group

theorem mem_centralizer_map_iff (hφ : Function.Injective φ) {E : Subgroup A} {n : A} :
    φ n ∈ centralizer ((E.map φ : Subgroup B) : Set B) ↔ n ∈ centralizer (E : Set A) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    have := h (φ y) ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul] at this
    exact hφ this
  · rintro h _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, h y hy]

theorem map_conjSub (φ : A →* B) (y : A) (E : Subgroup A) :
    (conjSub y E).map φ = conjSub (φ y) (E.map φ) := by
  ext x
  rw [mem_conjSub_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨y⁻¹ * z * y, mem_conjSub_iff.1 hz, ?_⟩
    simp
  · rintro ⟨b, hb, hbx⟩
    have e : y⁻¹ * (y * b * y⁻¹) * y = b := by group
    refine ⟨y * b * y⁻¹, mem_conjSub_iff.2 (by rw [e]; exact hb), ?_⟩
    rw [map_mul, map_mul, map_inv, hbx]
    group

theorem exists_mulEquiv_normalizer (hφ : Function.Injective φ) (E : Subgroup A) :
    ∃ e : ↥(normalizer (E : Set A)) ≃*
      ↥(normalizer ((E.map φ : Subgroup B) : Set B) ⊓ φ.range),
      ∀ n, ((e n : ↥(normalizer ((E.map φ : Subgroup B) : Set B) ⊓ φ.range)) : B) =
        φ (n : A) := by
  have hmemN : ∀ n ∈ normalizer (E : Set A),
      φ n ∈ normalizer ((E.map φ : Subgroup B) : Set B) ⊓ φ.range :=
    fun n hn => ⟨(mem_normalizer_map_iff hφ).2 hn, ⟨n, rfl⟩⟩
  let f : ↥(normalizer (E : Set A)) →*
      ↥(normalizer ((E.map φ : Subgroup B) : Set B) ⊓ φ.range) :=
    (φ.comp (normalizer (E : Set A)).subtype).codRestrict _ (fun n => hmemN n n.2)
  have hf : ∀ n, ((f n : ↥(normalizer ((E.map φ : Subgroup B) : Set B) ⊓ φ.range)) : B) =
      φ (n : A) := fun n => rfl
  have hfinj : Function.Injective f := fun n m h =>
    Subtype.ext (hφ (((hf n).symm.trans (congrArg Subtype.val h)).trans (hf m)))
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨n, hn⟩ := y.2.2
    have hnN : n ∈ normalizer (E : Set A) := (mem_normalizer_map_iff hφ).1 (hn ▸ y.2.1)
    exact ⟨⟨n, hnN⟩, Subtype.ext ((hf _).trans hn)⟩
  exact ⟨MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩, hf⟩

theorem map_subgroupOf_normalizer (hφ : Function.Injective φ) (E : Subgroup A)
    (e : ↥(normalizer (E : Set A)) ≃*
      ↥(normalizer ((E.map φ : Subgroup B) : Set B) ⊓ φ.range))
    (he : ∀ n, ((e n : ↥(normalizer ((E.map φ : Subgroup B) : Set B) ⊓ φ.range)) : B) =
      φ (n : A)) :
    (E.subgroupOf (normalizer (E : Set A))).map e.toMonoidHom =
      (E.map φ).subgroupOf (normalizer ((E.map φ : Subgroup B) : Set B) ⊓ φ.range) := by
  ext y
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨(n : A), Subgroup.mem_subgroupOf.1 hn, (he n).symm⟩
  · intro hy
    have h1 : φ ((e.symm y : normalizer (E : Set A)) : A) ∈ E.map φ := by
      rw [← he, e.apply_symm_apply]
      exact hy
    exact ⟨e.symm y, Subgroup.mem_subgroupOf.2 ((Subgroup.mem_map_iff_mem hφ).1 h1),
      e.apply_symm_apply y⟩

theorem exists_quotient_equiv_map (hφ : Function.Injective φ) (E : Subgroup A)
    [hN : (E.subgroupOf (normalizer (E : Set A))).Normal] {Q : Type} [Group Q]
    (eJ : normalizer (E : Set A) ⧸ E.subgroupOf (normalizer (E : Set A)) ≃* Q) :
    ∃ _hN' : ((E.map φ).subgroupOf
        (normalizer ((E.map φ : Subgroup B) : Set B) ⊓ φ.range)).Normal,
      Nonempty (↥(normalizer ((E.map φ : Subgroup B) : Set B) ⊓ φ.range) ⧸
        (E.map φ).subgroupOf (normalizer ((E.map φ : Subgroup B) : Set B) ⊓ φ.range) ≃* Q) := by
  obtain ⟨e, he⟩ := exists_mulEquiv_normalizer hφ E
  have hmap := map_subgroupOf_normalizer hφ E e he
  have hN' : ((E.map φ).subgroupOf
      (normalizer ((E.map φ : Subgroup B) : Set B) ⊓ φ.range)).Normal := by
    rw [← hmap]
    exact hN.map e.toMonoidHom e.surjective
  exact ⟨hN', ⟨(QuotientGroup.congr _ _ e hmap).symm.trans eJ⟩⟩

end Generic

section Embedding


theorem conj_of_embedding {G : Type} [Group G] {L : Subgroup G} (φ : J →* G)
    (hφ : Function.Injective φ) (hL : φ.range = L) {A A' : Subgroup G} (hA : A ≤ L)
    (hA' : A' ≤ L) (h1 : CFSG.Open.IsElemAbelian 2 A) (h2 : CFSG.Open.IsElemAbelian 2 A')
    (c1 : Nat.card A = 2 ^ 11) (c2 : Nat.card A' = 2 ^ 11) :
    ∃ y ∈ L, A' = A.map (MulAut.conj y).toMonoidHom := by
  subst hL
  have key : ∀ {B : Subgroup G}, B ≤ φ.range → CFSG.Open.IsElemAbelian 2 B →
      Nat.card B = 2 ^ 11 → IsE (B.comap φ) ∧ B = (B.comap φ).map φ := by
    intro B hB hel hcard
    have hBeq : B = (B.comap φ).map φ := (Subgroup.map_comap_eq_self hB).symm
    refine ⟨⟨fun b hb => hφ ?_, ?_⟩, hBeq⟩
    · rw [map_pow, map_one]
      exact hel.2 _ hb
    · rw [← Subgroup.card_map_of_injective hφ, ← hBeq]
      exact hcard
  obtain ⟨hE1, hB1⟩ := key hA h1 c1
  obtain ⟨hE2, hB2⟩ := key hA' h2 c2
  obtain ⟨g, hg⟩ := exists_conj_eq_frameE hE1
  obtain ⟨g', hg'⟩ := exists_conj_eq_frameE hE2
  refine ⟨φ (g' * g⁻¹), ⟨_, rfl⟩, ?_⟩
  have hA_eq : A = conjSub (φ g) ((frameE : Subgroup J).map φ) :=
    hB1.trans (by rw [hg, map_conjSub])
  have hA'_eq : A' = conjSub (φ g') ((frameE : Subgroup J).map φ) :=
    hB2.trans (by rw [hg', map_conjSub])
  show A' = conjSub (φ (g' * g⁻¹)) A
  have hmul : g' * g⁻¹ * g = g' := by group
  rw [hA'_eq, hA_eq, conjSub_conjSub, ← map_mul, hmul]

theorem frame_of_embedding {G : Type} [Group G] {L : Subgroup G} {u : G} (φ : J →* G)
    (hφ : Function.Injective φ) (hL : φ.range = L) (hu : φ d = u) :
    ∃ W : Subgroup G, W ≤ L ∧ u ∈ W ∧ CFSG.Open.IsElemAbelian 2 W ∧ Nat.card W = 2 ^ 11 ∧
      centralizer (W : Set G) ⊓ L = W ∧
      (∃ _hN : (W.subgroupOf (normalizer (W : Set G) ⊓ L)).Normal,
        Nonempty ((normalizer (W : Set G) ⊓ L : Subgroup G) ⧸
          W.subgroupOf (normalizer (W : Set G) ⊓ L) ≃* Carrier .M23)) ∧
      Set.ncard {x : G | x ∈ W ∧ ∃ l ∈ L, x = l * u * l⁻¹} = 23 ∧
      ∀ p : G, p ∈ W → (∃ l ∈ L, p = l * u * l⁻¹) →
        ∃ n ∈ normalizer (W : Set G) ⊓ L, n * u * n⁻¹ = p := by
  subst hL hu
  have hW_sq : ∀ x ∈ (frameE : Subgroup J).map φ, x ^ 2 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, frameE_sq y hy, map_one]
  have hW_comm : ∀ x ∈ (frameE : Subgroup J).map φ, ∀ y ∈ (frameE : Subgroup J).map φ,
      x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, frameE_comm a ha b hb]
  refine ⟨(frameE : Subgroup J).map φ, Subgroup.map_le_range _ _,
    Subgroup.mem_map_of_mem φ d_mem_frameE, ⟨⟨⟨fun a b => Subtype.ext (hW_comm a a.2 b b.2)⟩⟩,
      hW_sq⟩, by rw [Subgroup.card_map_of_injective hφ]; exact frameE_card, ?_, ?_, ?_, ?_⟩
  ·
    ext x
    constructor
    · rintro ⟨hx1, y, rfl⟩
      refine ⟨y, centralizer_frameE_le fun z hz => ?_, rfl⟩
      exact ((Subgroup.mem_centralizer_iff.1 ((mem_centralizer_map_iff hφ).1 hx1)) z hz).symm
    · intro hx
      exact ⟨Subgroup.mem_centralizer_iff.2 fun h hh => hW_comm h hh x hx,
        Subgroup.map_le_range _ _ hx⟩
  ·
    obtain ⟨hN, ⟨eJ⟩⟩ := frame_quotient_m23
    exact exists_quotient_equiv_map hφ (frameE : Subgroup J) eJ
  ·
    have hset : {x : G | x ∈ (frameE : Subgroup J).map φ ∧ ∃ l ∈ φ.range, x = l * φ d * l⁻¹} =
        φ '' {x : J | x ∈ (frameE : Subgroup J) ∧ x ∈ D23} := by
      ext x
      constructor
      · rintro ⟨⟨y, hy, rfl⟩, _, ⟨m, rfl⟩, hm⟩
        have hym : y = m * d * m⁻¹ := hφ (by rw [hm]; simp)
        exact ⟨y, ⟨hy, isConj_iff.2 ⟨m, hym.symm⟩⟩, rfl⟩
      · rintro ⟨y, ⟨hy, hyD⟩, rfl⟩
        obtain ⟨m, hm⟩ := isConj_iff.1 (hyD : IsConj d y)
        exact ⟨⟨y, hy, rfl⟩, φ m, ⟨m, rfl⟩, by rw [← hm]; simp⟩
    rw [hset, Set.ncard_image_of_injective _ hφ, ncard_frameE_D23]
  ·
    rintro p ⟨y, hy, rfl⟩ ⟨_, ⟨m, rfl⟩, hm⟩
    have hym : y = m * d * m⁻¹ := hφ (by rw [hm]; simp)
    obtain ⟨n, hn, hnd⟩ := exists_mem_normalizer_frameE d_mem_frameE (IsConj.refl d) hy
      (isConj_iff.2 ⟨m, hym.symm⟩)
    refine ⟨φ n, ?_, ?_⟩
    · exact ⟨(mem_normalizer_map_iff hφ).2 hn, ⟨n, rfl⟩⟩
    · rw [← map_inv, ← map_mul, ← map_mul, hnd]

end Embedding

end CFSG.EvenSporadicStandard.Solomon78.F23L63

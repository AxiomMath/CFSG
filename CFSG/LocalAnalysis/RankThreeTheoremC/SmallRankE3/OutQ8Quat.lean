module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.OutQ8Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zTYG

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.OutQ8

open Subgroup

section

section Bridge
variable {K : Type*} [Group K]

theorem q8_pow4 : ∀ q : QuaternionGroup 2, q ^ 4 = 1 := by decide

theorem q8_sq_two : ∀ q : QuaternionGroup 2, q ^ 2 = 1 → q = 1 ∨ q = QuaternionGroup.a 2 := by
  decide

theorem q8_comm : ∀ q q' : QuaternionGroup 2,
    q * q' * q⁻¹ * q'⁻¹ = 1 ∨ q * q' * q⁻¹ * q'⁻¹ = QuaternionGroup.a 2 := by
  decide

theorem q8_center : ∀ q : QuaternionGroup 2, (∀ q' : QuaternionGroup 2, q * q' = q' * q) →
    q = 1 ∨ q = QuaternionGroup.a 2 := by
  decide

theorem q8_fifth : (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 4 = 1 ∧
    (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 ≠ 1 ∧
    (QuaternionGroup.xa 0 : QuaternionGroup 2) ^ 2 = (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 ∧
    (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.a 1 * (QuaternionGroup.xa 0)⁻¹ =
      (QuaternionGroup.a 1)⁻¹ := by
  decide

theorem q8_gen : ∀ q : QuaternionGroup 2, ∃ k₁ < 2, ∃ k₂ < 4,
    q = (QuaternionGroup.xa 0) ^ k₁ * (QuaternionGroup.a 1) ^ k₂ := by
  decide

theorem emb_injective (A : Subgroup K) (e : ↥A ≃* QuaternionGroup 2) :
    Function.Injective (A.subtype.comp e.symm.toMonoidHom) := by
  intro x y h
  have h' : ((e.symm x : ↥A) : K) = ((e.symm y : ↥A) : K) := h
  exact e.symm.injective (Subtype.val_injective h')

theorem emb_mem (A : Subgroup K) (e : ↥A ≃* QuaternionGroup 2) :
    ∀ q : QuaternionGroup 2, (A.subtype.comp e.symm.toMonoidHom) q ∈ A :=
  fun q => (e.symm q).2

theorem emb_surj (A : Subgroup K) (e : ↥A ≃* QuaternionGroup 2) :
    ∀ a ∈ A, ∃ q : QuaternionGroup 2, (A.subtype.comp e.symm.toMonoidHom) q = a := by
  intro a ha
  refine ⟨e ⟨a, ha⟩, ?_⟩
  exact congrArg Subtype.val (e.symm_apply_apply ⟨a, ha⟩)

theorem card_of_equiv (A : Subgroup K) (e : ↥A ≃* QuaternionGroup 2) : Nat.card A = 8 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card] <;> norm_num

theorem qpair_of_inj {f : QuaternionGroup 2 →* K} (hf : Function.Injective f) :
    QPair (f (QuaternionGroup.a 1)) (f (QuaternionGroup.xa 0)) := by
  obtain ⟨g1, g2, g3, g4⟩ := q8_fifth
  unfold QPair
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← map_pow, g1, map_one]
  · intro h
    apply g2
    apply hf
    rw [map_pow, map_one]
    exact h
  · have h3 := congrArg f g3
    simp only [map_pow] at h3
    exact h3
  · have h4 := congrArg f g4
    simp only [map_mul, map_inv] at h4
    exact h4

theorem q8Like_of_hom (A : Subgroup K) (ι : QuaternionGroup 2 →* K)
    (hinj : Function.Injective ι) (hmem : ∀ q : QuaternionGroup 2, ι q ∈ A)
    (hsurj : ∀ a ∈ A, ∃ q : QuaternionGroup 2, ι q = a) (w : K) (hwA : w ∈ A)
    (hw1 : w ≠ 1) (hw2 : w ^ 2 = 1) (hcard : Nat.card A = 8) : Q8Like A w := by
  have hwι : ι (QuaternionGroup.a 2) = w := by
    obtain ⟨q₀, hq₀⟩ := hsurj w hwA
    have hq₀2 : q₀ ^ 2 = 1 := by
      apply hinj
      rw [map_pow, map_one, hq₀]
      exact hw2
    have hq₀1 : q₀ ≠ 1 := by
      intro h
      apply hw1
      rw [← hq₀, h, map_one]
    rw [← (q8_sq_two q₀ hq₀2).resolve_left hq₀1]
    exact hq₀
  have hc : ∀ x y : QuaternionGroup 2,
      ι x * ι y * (ι x)⁻¹ * (ι y)⁻¹ = ι (x * y * x⁻¹ * y⁻¹) := by
    intro x y
    simp only [map_mul, map_inv]
  have hi : ι (QuaternionGroup.a 1) ∈
      Subgroup.closure ({ι (QuaternionGroup.a 1), ι (QuaternionGroup.xa 0)} : Set K) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hj : ι (QuaternionGroup.xa 0) ∈
      Subgroup.closure ({ι (QuaternionGroup.a 1), ι (QuaternionGroup.xa 0)} : Set K) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  refine
    { ζ_mem := hwA
      ζ_ne := hw1
      ζ_sq := hw2
      card := hcard
      pow4 := ?_
      uniq := ?_
      comm := ?_
      center := ?_
      gen := ?_ }
  · intro a ha
    obtain ⟨q, rfl⟩ := hsurj a ha
    rw [← map_pow, q8_pow4 q, map_one]
  · intro a ha ha2
    obtain ⟨q, rfl⟩ := hsurj a ha
    have hq2 : q ^ 2 = 1 := by
      apply hinj
      rw [map_pow, map_one]
      exact ha2
    rcases q8_sq_two q hq2 with h | h
    · left
      rw [h, map_one]
    · right
      rw [h]
      exact hwι
  · intro a ha a' ha'
    obtain ⟨q, rfl⟩ := hsurj a ha
    obtain ⟨q', rfl⟩ := hsurj a' ha'
    rw [hc q q']
    rcases q8_comm q q' with h | h
    · left
      rw [h, map_one]
    · right
      rw [h]
      exact hwι
  · intro a ha hcomm
    obtain ⟨q, rfl⟩ := hsurj a ha
    have hq : ∀ q' : QuaternionGroup 2, q * q' = q' * q := by
      intro q'
      apply hinj
      rw [map_mul, map_mul]
      exact hcomm _ (hmem q')
    rcases q8_center q hq with h | h
    · left
      rw [h, map_one]
    · right
      rw [h]
      exact hwι
  · refine ⟨ι (QuaternionGroup.a 1), ι (QuaternionGroup.xa 0), hmem _, hmem _,
      qpair_of_inj hinj, ?_⟩
    apply le_antisymm
    · intro a ha
      obtain ⟨q, rfl⟩ := hsurj a ha
      obtain ⟨k₁, _, k₂, _, hq⟩ := q8_gen q
      rw [hq]
      simp only [map_mul, map_pow]
      exact mul_mem (pow_mem hj k₁) (pow_mem hi k₂)
    · rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact hmem _
      · exact hmem _

theorem exists_qpair_of_hom (R : Subgroup K) (ι : QuaternionGroup 2 →* K)
    (hinj : Function.Injective ι) (hmem : ∀ q : QuaternionGroup 2, ι q ∈ R) :
    ∃ u v : K, u ∈ R ∧ v ∈ R ∧ QPair u v :=
  ⟨ι (QuaternionGroup.a 1), ι (QuaternionGroup.xa 0), hmem _, hmem _, qpair_of_inj hinj⟩

theorem q8Like_of_equiv (A : Subgroup K) (e : ↥A ≃* QuaternionGroup 2) (w : K) (hwA : w ∈ A)
    (hw1 : w ≠ 1) (hw2 : w ^ 2 = 1) : Q8Like A w :=
  q8Like_of_hom A (A.subtype.comp e.symm.toMonoidHom) (emb_injective A e) (emb_mem A e)
    (emb_surj A e) w hwA hw1 hw2 (card_of_equiv A e)

theorem exists_qpair_of_equiv (R : Subgroup K) (e : ↥R ≃* QuaternionGroup 2) :
    ∃ u v : K, u ∈ R ∧ v ∈ R ∧ QPair u v :=
  exists_qpair_of_hom R (R.subtype.comp e.symm.toMonoidHom) (emb_injective R e) (emb_mem R e)

end Bridge

end

section

section QuatAux

variable {n : ℕ}

theorem qg_inv_a (i : ZMod (2 * n)) :
    (QuaternionGroup.a i : QuaternionGroup n)⁻¹ = QuaternionGroup.a (-i) := rfl

theorem qg_inv_xa (i : ZMod (2 * n)) :
    (QuaternionGroup.xa i : QuaternionGroup n)⁻¹ =
      QuaternionGroup.xa ((n : ZMod (2 * n)) + i) := rfl

theorem qg_mem_a_or_xa (x : QuaternionGroup n) :
    (∃ i : ZMod (2 * n), x = QuaternionGroup.a i) ∨
      ∃ i : ZMod (2 * n), x = QuaternionGroup.xa i := by
  cases x with
  | a i => exact Or.inl ⟨i, rfl⟩
  | xa i => exact Or.inr ⟨i, rfl⟩

theorem qg_zpow_a_one (k : ℤ) :
    (QuaternionGroup.a 1 : QuaternionGroup n) ^ k =
      QuaternionGroup.a (k : ZMod (2 * n)) := by
  rcases Int.eq_nat_or_neg k with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast, QuaternionGroup.a_one_pow, Int.cast_natCast]
  · rw [zpow_neg, zpow_natCast, QuaternionGroup.a_one_pow, qg_inv_a, Int.cast_neg,
      Int.cast_natCast]

end QuatAux

section Quat

variable {K : Type*} [Group K]

theorem quatLike_of_equiv (B : Subgroup K) (N : ℕ) [NeZero N]
    (e : ↥B ≃* QuaternionGroup N) (w : K) (hwB : w ∈ B) (hw1 : w ≠ 1) (hw2 : w ^ 2 = 1) :
    ∃ Y : Subgroup K, QuatLike B Y w := by
  obtain ⟨emb, hembinj, hembB, hembsurj⟩ :
      ∃ emb : QuaternionGroup N →* K, Function.Injective emb ∧
        (∀ x : QuaternionGroup N, emb x ∈ B) ∧
          ∀ g ∈ B, ∃ x : QuaternionGroup N, emb x = g := by
    refine ⟨B.subtype.comp e.symm.toMonoidHom, ?_, fun x => (e.symm x).2, ?_⟩
    · intro x y hxy
      apply e.symm.injective
      apply Subtype.ext
      exact hxy
    · intro g hg
      refine ⟨e ⟨g, hg⟩, ?_⟩
      exact congrArg Subtype.val (e.symm_apply_apply ⟨g, hg⟩)
  obtain ⟨x₀, hx₀⟩ := hembsurj w hwB
  have hx₀2 : x₀ ^ 2 = 1 := hembinj (by rw [map_pow, hx₀, hw2, map_one])
  have hx₀1 : x₀ ≠ 1 := by
    intro h
    apply hw1
    rw [← hx₀, h, map_one]
  have hwN : emb (QuaternionGroup.a (N : ZMod (2 * N))) = w := by
    rw [← hx₀, CFSG.LocalAnalysis.RankThreeTheoremC.k631_quat_involution x₀ hx₀2 hx₀1]
  obtain ⟨Y, hYdef⟩ : ∃ Y : Subgroup K,
      Y = Subgroup.zpowers (emb (QuaternionGroup.a 1 : QuaternionGroup N)) := ⟨_, rfl⟩
  have hYB : Y ≤ B := by
    rw [hYdef]
    exact Subgroup.zpowers_le.mpr (hembB _)
  have hc : ∀ x : QuaternionGroup N,
      emb x ∈ Y ↔ ∃ i : ZMod (2 * N), x = QuaternionGroup.a i := by
    intro x
    rw [hYdef]
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
      have h1 : emb ((QuaternionGroup.a 1 : QuaternionGroup N) ^ k) = emb x := by
        rw [map_zpow]
        exact hk
      have h2 : (QuaternionGroup.a 1 : QuaternionGroup N) ^ k = x := hembinj h1
      exact ⟨(k : ZMod (2 * N)), by rw [← h2, qg_zpow_a_one]⟩
    · rintro ⟨i, rfl⟩
      refine Subgroup.mem_zpowers_iff.mpr ⟨(i.val : ℤ), ?_⟩
      rw [← map_zpow emb (QuaternionGroup.a 1 : QuaternionGroup N) (i.val : ℤ), qg_zpow_a_one,
        Int.cast_natCast, ZMod.natCast_zmod_val]
  have hcaseY : ∀ x : QuaternionGroup N, emb x ∉ Y →
      ∃ i : ZMod (2 * N), x = QuaternionGroup.xa i := by
    intro x hx
    rcases qg_mem_a_or_xa x with h | h
    · exact absurd ((hc x).mpr h) hx
    · exact h
  have h2N : (N : ZMod (2 * N)) + (N : ZMod (2 * N)) = 0 := by
    rw [← Nat.cast_add, show N + N = 2 * N by ring]
    exact ZMod.natCast_self (2 * N)
  refine ⟨Y, hYB, ?_, ?_, hw1, hw2, ?_, ?_, ?_, ?_⟩
  · rw [hYdef]
    infer_instance
  · rw [← hwN]
    exact (hc _).mpr ⟨_, rfl⟩
  · intro b hb hb2
    obtain ⟨x, rfl⟩ := hembsurj b hb
    have hx2 : x ^ 2 = 1 := hembinj (by rw [map_pow, hb2, map_one])
    by_cases hx1 : x = 1
    · exact Or.inl (by rw [hx1, map_one])
    · refine Or.inr ?_
      rw [CFSG.LocalAnalysis.RankThreeTheoremC.k631_quat_involution x hx2 hx1, hwN]
  · intro g hg h hh hgY hhY
    obtain ⟨x, rfl⟩ := hembsurj g hg
    obtain ⟨z, rfl⟩ := hembsurj h hh
    obtain ⟨i, rfl⟩ := hcaseY x hgY
    obtain ⟨j, rfl⟩ := hcaseY z hhY
    rw [← map_inv emb, ← map_mul emb]
    exact (hc _).mpr ⟨(N : ZMod (2 * N)) + ((N : ZMod (2 * N)) + j) - i,
      by rw [qg_inv_xa, QuaternionGroup.xa_mul_xa]⟩
  · intro g hg hgY
    obtain ⟨x, rfl⟩ := hembsurj g hg
    obtain ⟨i, rfl⟩ := hcaseY x hgY
    rw [← map_pow emb, QuaternionGroup.xa_sq]
    exact hwN
  · intro g hg hgY y hy
    obtain ⟨x, rfl⟩ := hembsurj g hg
    obtain ⟨i, rfl⟩ := hcaseY x hgY
    obtain ⟨u, rfl⟩ := hembsurj y (hYB hy)
    obtain ⟨k, rfl⟩ := (hc u).mp hy
    have key : (QuaternionGroup.xa i : QuaternionGroup N) * QuaternionGroup.a k *
        (QuaternionGroup.xa i)⁻¹ = (QuaternionGroup.a k)⁻¹ := by
      rw [QuaternionGroup.xa_mul_a, qg_inv_xa, QuaternionGroup.xa_mul_xa, qg_inv_a]
      congr 1
      linear_combination h2N
    calc emb (QuaternionGroup.xa i) * emb (QuaternionGroup.a k) * (emb (QuaternionGroup.xa i))⁻¹
        = emb (QuaternionGroup.xa i * QuaternionGroup.a k * (QuaternionGroup.xa i)⁻¹) := by
          simp only [map_mul, map_inv]
      _ = emb ((QuaternionGroup.a k)⁻¹) := by rw [key]
      _ = (emb (QuaternionGroup.a k))⁻¹ := map_inv emb _

theorem isPGroup_two_of_equiv_quaternion (B : Subgroup K) (k : ℕ)
    (e : ↥B ≃* QuaternionGroup (2 ^ k)) : IsPGroup 2 B := by
  haveI : NeZero (2 ^ k) := ⟨pow_ne_zero _ two_ne_zero⟩
  have hcard : Nat.card B = 2 ^ (k + 2) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    ring
  exact IsPGroup.of_card hcard

end Quat

end

section

variable {K : Type*} [Group K]

theorem exists_involution_of_card_two {A B : Subgroup K}
    (h : Nat.card (A ⊓ B : Subgroup K) = 2) : ∃ w ∈ A ⊓ B, w ≠ 1 ∧ w ^ 2 = 1 := by
  haveI : Finite ↥(A ⊓ B) := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  haveI : Nontrivial ↥(A ⊓ B) := Finite.one_lt_card_iff_nontrivial.mp (by rw [h]; norm_num)
  obtain ⟨w, hw⟩ := exists_ne (1 : ↥(A ⊓ B))
  refine ⟨(w : K), w.2, ?_, ?_⟩
  · intro h1
    exact hw (Subtype.ext h1)
  · have h2 : w ^ Nat.card ↥(A ⊓ B) = 1 := pow_card_eq_one'
    rw [h] at h2
    have := congrArg Subtype.val h2
    simpa using this

end

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.OutQ8

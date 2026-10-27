module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84TS4Idx

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open scoped Count
open Certificates.T84P (Elt mulE oneE M0l Jl)
open Certificates.T84S4 (elt Ml mulT invT jT)

variable {Y : Type} [Group Y] {J : Subgroup Y} {rr : Y → Elt}
  (S : Certificates.T84S4.Facts) (C : Sec8T84TS4Coord J rr)

include S C

@[expose] noncomputable def sec8t84ts4_b {M : Subgroup Y} (hM : ∀ y, y ∈ M ↔ rr y ∈ Ml ()) :
    Fin 192 ≃ ↥M :=
  Equiv.ofBijective
    (fun i : Fin 192 =>
      (⟨sec8t84ts4_el S C i.val, (hM _).mpr (sec8t84ts4_rr_mem_Ml S C i.2)⟩ : ↥M))
    ⟨fun _ _ hij => Fin.ext (sec8t84ts4_el_inj S C (Fin.isLt _) (Fin.isLt _)
        (congrArg Subtype.val hij)),
      fun x => by
        obtain ⟨i, hi, hix⟩ := sec8t84ts4_exists_el S C ((hM _).mp x.2)
        exact ⟨⟨i, hi⟩, Subtype.ext hix⟩⟩

theorem sec8t84ts4_b_val {M : Subgroup Y} (hM : ∀ y, y ∈ M ↔ rr y ∈ Ml ()) (i : Fin 192) :
    ((sec8t84ts4_b S C hM i : ↥M) : Y) = sec8t84ts4_el S C i.val :=
  rfl

theorem sec8t84ts4_b_mul {M : Subgroup Y} (hM : ∀ y, y ∈ M ↔ rr y ∈ Ml ()) {i j : ℕ}
    (hi : i < 192) (hj : j < 192) :
    sec8t84ts4_b S C hM ⟨mulT i j, (sec8t84ts4_el_mul S C hi hj).1⟩ =
      sec8t84ts4_b S C hM ⟨i, hi⟩ * sec8t84ts4_b S C hM ⟨j, hj⟩ :=
  Subtype.ext (sec8t84ts4_el_mul S C hi hj).2

theorem sec8t84ts4_b_zero {M : Subgroup Y} (hM : ∀ y, y ∈ M ↔ rr y ∈ Ml ()) :
    sec8t84ts4_b S C hM ⟨0, by norm_num⟩ = 1 :=
  Subtype.ext (sec8t84ts4_el_zero S C)

private theorem sec8t84ts4_count_eq {M : Subgroup Y} (hM : ∀ y, y ∈ M ↔ rr y ∈ Ml ())
    (a : ↥M ≃* ↥M) (f : ℕ → ℕ)
    (hf : ∀ (n : ℕ) (h : n < 192),
      f n = ((sec8t84ts4_b S C hM).symm (a (sec8t84ts4_b S C hM ⟨n, h⟩))).val) :
    Nat.card {k : ℕ // k < 192 ∧ (jT k = true ∧ f k = k)} =
      Nat.card {x : ↥M // (x : Y) ∈ J ∧ a x = x} := by
  set b := sec8t84ts4_b S C hM with hb
  have hfix : ∀ (k : ℕ) (hk : k < 192), f k = k ↔ a (b ⟨k, hk⟩) = b ⟨k, hk⟩ := by
    intro k hk
    rw [hf k hk]
    constructor
    · intro h
      have h1 : b.symm (a (b ⟨k, hk⟩)) = ⟨k, hk⟩ := Fin.ext h
      exact b.symm_apply_eq.mp h1
    · intro h
      rw [h]
      simp
  let φ : {k : ℕ // k < 192 ∧ (jT k = true ∧ f k = k)} → {x : ↥M // (x : Y) ∈ J ∧ a x = x} :=
    fun k => ⟨b ⟨k.1, k.2.1⟩,
      (sec8t84ts4_el_J S C k.2.1).mpr k.2.2.1, (hfix k.1 k.2.1).mp k.2.2.2⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro k k' hkk
      have h1 : b ⟨k.1, k.2.1⟩ = b ⟨k'.1, k'.2.1⟩ := congrArg (fun z => z.1) hkk
      exact Subtype.ext (congrArg Fin.val (b.injective h1))
    · rintro ⟨x, hxJ, hxa⟩
      refine ⟨⟨(b.symm x).val, (b.symm x).isLt, ?_, ?_⟩, ?_⟩
      · rw [← sec8t84ts4_el_J S C (b.symm x).isLt]
        have h1 : (b ⟨(b.symm x).val, (b.symm x).isLt⟩ : ↥M) = x := b.apply_symm_apply x
        have h2 := congrArg Subtype.val h1
        rw [sec8t84ts4_b_val] at h2
        rw [h2]
        exact hxJ
      · rw [hfix _ (b.symm x).isLt]
        have h1 : (b ⟨(b.symm x).val, (b.symm x).isLt⟩ : ↥M) = x := b.apply_symm_apply x
        rw [h1]
        exact hxa
      · exact Subtype.ext (b.apply_symm_apply x)
  exact Nat.card_congr (Equiv.ofBijective φ hφ)

theorem sec8t84ts4_clause3 {M : Subgroup Y} (hM : ∀ y, y ∈ M ↔ rr y ∈ Ml ()) :
    ∀ a : ↥M ≃* ↥M, (∀ x, a (a x) = x) →
      Nat.card {x : ↥M // (x : Y) ∈ J ∧ a x = x} = 4 →
      (∀ x : ↥M, (x : Y) ∈ J → a x = x → x * x = 1) →
        ∃ y : ↥M, orderOf y = 3 ∧ a y = y := by
  intro a ha hcard hexp
  set b := sec8t84ts4_b S C hM with hb
  obtain ⟨B, hB⟩ : ∃ B : ℕ → ↥M, ∀ (n : ℕ) (h : n < 192), B n = b ⟨n, h⟩ :=
    ⟨fun n => if h : n < 192 then b ⟨n, h⟩ else 1, fun n h => dif_pos h⟩
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℕ, ∀ (n : ℕ) (h : n < 192),
      f n = (b.symm (a (b ⟨n, h⟩))).val :=
    ⟨fun n => if h : n < 192 then (b.symm (a (b ⟨n, h⟩))).val else 0, fun n h => dif_pos h⟩
  have hBinj : ∀ i, i < 192 → ∀ j, j < 192 → B i = B j → i = j := by
    intro i hi j hj h
    rw [hB i hi, hB j hj] at h
    exact congrArg Fin.val (b.injective h)
  have hBmul : ∀ i, i < 192 → ∀ j, j < 192 → mulT i j < 192 ∧ B (mulT i j) = B i * B j := by
    intro i hi j hj
    obtain ⟨hlt, -⟩ := sec8t84ts4_el_mul S C hi hj
    refine ⟨hlt, ?_⟩
    rw [hB _ hlt, hB i hi, hB j hj]
    exact sec8t84ts4_b_mul S C hM hi hj
  have hB0 : B 0 = 1 := by
    rw [hB 0 (by norm_num)]
    exact sec8t84ts4_b_zero S C hM
  have hfB : ∀ n, n < 192 → f n < 192 ∧ B (f n) = a (B n) := by
    intro n hn
    have hfn := hf n hn
    have hlt : f n < 192 := by
      rw [hfn]
      exact (b.symm _).isLt
    refine ⟨hlt, ?_⟩
    rw [hB n hn, hB (f n) hlt]
    have h1 : (⟨f n, hlt⟩ : Fin 192) = b.symm (a (b ⟨n, hn⟩)) := Fin.ext hfn
    rw [h1]
    exact b.apply_symm_apply _
  have hf1 : ∀ i < 192, f i < 192 := fun i hi => (hfB i hi).1
  have hf0 : f 0 = 0 := by
    have h0 : (0 : ℕ) < 192 := by norm_num
    obtain ⟨hlt, hBf⟩ := hfB 0 h0
    apply hBinj (f 0) hlt 0 h0
    rw [hBf, hB0, map_one]
  have hhom : ∀ i < 192, ∀ j < 192, f (mulT i j) = mulT (f i) (f j) := by
    intro i hi j hj
    obtain ⟨hlt, hBij⟩ := hBmul i hi j hj
    obtain ⟨hfi, hBfi⟩ := hfB i hi
    obtain ⟨hfj, hBfj⟩ := hfB j hj
    obtain ⟨hfij, hBfij⟩ := hfB (mulT i j) hlt
    obtain ⟨hlt2, hBm2⟩ := hBmul (f i) hfi (f j) hfj
    apply hBinj (f (mulT i j)) hfij (mulT (f i) (f j)) hlt2
    rw [hBfij, hBij, map_mul, ← hBfi, ← hBfj, hBm2]
  have hinvol : ∀ i < 192, f (f i) = i := by
    intro i hi
    obtain ⟨hfi, hBfi⟩ := hfB i hi
    obtain ⟨hffi, hBffi⟩ := hfB (f i) hfi
    apply hBinj (f (f i)) hffi i hi
    rw [hBffi, hBfi, ha]
  have hcardL : ((List.range 192).filter fun x => jT x && f x == x).length = 4 := by
    have hl : ((List.range 192).filter fun x => jT x && f x == x).length =
        Nat.count (fun k => jT k = true ∧ f k = k) 192 := by
      rw [Nat.count, List.countP_eq_length_filter]
      congr 1
    rw [hl, Nat.count_eq_card_fintype, ← Nat.card_eq_fintype_card,
      sec8t84ts4_count_eq S C hM a f hf]
    exact hcard
  have hexpf : ∀ i < 192, jT i = true → f i = i → mulT i i = 0 := by
    intro i hi hjT hfi
    have hxJ : ((B i : ↥M) : Y) ∈ J := by
      rw [hB i hi, sec8t84ts4_b_val]
      exact (sec8t84ts4_el_J S C hi).mpr hjT
    have hxa : a (B i) = B i := by
      rw [← (hfB i hi).2, hfi]
    have h1 := hexp (B i) hxJ hxa
    obtain ⟨hlt, hmul⟩ := hBmul i hi i hi
    apply hBinj (mulT i i) hlt 0 (by norm_num)
    rw [hmul, h1, hB0]
  obtain ⟨y, hy, hy0, hy3, hfy⟩ := S.autFix f hf1 hf0 hhom hinvol hcardL hexpf
  refine ⟨B y, ?_, ?_⟩
  · apply orderOf_eq_prime
    · obtain ⟨h1, e1⟩ := hBmul y hy y hy
      obtain ⟨h2, e2⟩ := hBmul (mulT y y) h1 y hy
      rw [hy3, hB0, e1] at e2
      rw [pow_three']
      exact e2.symm
    · intro h1
      rw [← hB0] at h1
      exact hy0 (hBinj y hy 0 (by norm_num) h1)
  · rw [← (hfB y hy).2, hfy]

end CFSG.OddStandard.SmallF3.Omega

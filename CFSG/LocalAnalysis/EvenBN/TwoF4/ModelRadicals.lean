module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.ModelCommutators
public import CFSG.LocalAnalysis.EvenBN.TwoF4.ModelTorusBraces
public import CFSG.LocalAnalysis.EvenBN.TwoF4.Model

public section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (torusPair)
open scoped commutatorElement

namespace Idx

@[expose] def isR1 : Idx → Bool
  | .i8 | .i9 | .i10 | .i11 | .i12 => true
  | _ => false

theorem isSz_eq_false_of_isR1 : ∀ k : Idx, k.isR1 = true → k.isSz = false := by decide

@[expose] def r1Col : Idx → Idx
  | .i8 => .i4
  | .i11 => .i6
  | .i12 => .i5
  | k => k

end Idx

section R1

variable (K : Type) [Field K] (a : ℕ)

@[expose] noncomputable def r1Elt
    (u : Idx → K) : ModGL F4.tag K :=
  rootElt K a .i8 (u .i8) * rootElt K a .i11 (u .i11) * rootElt K a .i12 (u .i12) *
    rootElt K a .i9 (u .i9) * rootElt K a .i10 (u .i10)

variable {K a} [Finite K] [CharP K F4.prime]

theorem rootElt_commute_of_isR1 (hK : Nat.card K = 2 ^ (2 * a + 1)) {k l : Idx}
    (hk : k.isR1 = true) (hl : l.isR1 = true) (u v : K) :
    rootElt K a k u * rootElt K a l v = rootElt K a l v * rootElt K a k u := by
  have hc : ∀ {x y : ModGL F4.tag K}, ⁅x, y⁆ = 1 → x * y = y * x := fun h =>
    commutatorElement_eq_one_iff_mul_comm.1 h
  have hd : ∀ {j : Idx}, j.isSz = false → ∀ u v : K,
      rootElt K a j u * rootElt K a j v = rootElt K a j v * rootElt K a j u := fun hj u v => by
    rw [← rootElt_add hK hj, ← rootElt_add hK hj, add_comm]
  match k, l, hk, hl with
  | .i8, .i8, _, _ => exact hd rfl u v
  | .i8, .i11, _, _ => exact hc (rootElt_comm_8_11 hK u v)
  | .i8, .i12, _, _ => exact hc (rootElt_comm_8_12 hK u v)
  | .i8, .i9, _, _ => exact hc (rootElt_comm_8_9 hK u v)
  | .i8, .i10, _, _ => exact hc (rootElt_comm_8_10 hK u v)
  | .i11, .i8, _, _ => exact (hc (rootElt_comm_8_11 hK v u)).symm
  | .i11, .i11, _, _ => exact hd rfl u v
  | .i11, .i12, _, _ => exact hc (rootElt_comm_11_12 hK u v)
  | .i11, .i9, _, _ => exact hc (rootElt_comm_11_9 hK u v)
  | .i11, .i10, _, _ => exact hc (rootElt_comm_11_10 hK u v)
  | .i12, .i8, _, _ => exact (hc (rootElt_comm_8_12 hK v u)).symm
  | .i12, .i11, _, _ => exact (hc (rootElt_comm_11_12 hK v u)).symm
  | .i12, .i12, _, _ => exact hd rfl u v
  | .i12, .i9, _, _ => exact hc (rootElt_comm_12_9 hK u v)
  | .i12, .i10, _, _ => exact hc (rootElt_comm_12_10 hK u v)
  | .i9, .i8, _, _ => exact (hc (rootElt_comm_8_9 hK v u)).symm
  | .i9, .i11, _, _ => exact (hc (rootElt_comm_11_9 hK v u)).symm
  | .i9, .i12, _, _ => exact (hc (rootElt_comm_12_9 hK v u)).symm
  | .i9, .i9, _, _ => exact hd rfl u v
  | .i9, .i10, _, _ => exact hc (rootElt_comm_9_10 hK u v)
  | .i10, .i8, _, _ => exact (hc (rootElt_comm_8_10 hK v u)).symm
  | .i10, .i11, _, _ => exact (hc (rootElt_comm_11_10 hK v u)).symm
  | .i10, .i12, _, _ => exact (hc (rootElt_comm_12_10 hK v u)).symm
  | .i10, .i9, _, _ => exact (hc (rootElt_comm_9_10 hK v u)).symm
  | .i10, .i10, _, _ => exact hd rfl u v
  | .i1, _, hk, _ => exact absurd hk (by decide)
  | .i2, _, hk, _ => exact absurd hk (by decide)
  | .i3, _, hk, _ => exact absurd hk (by decide)
  | .i4, _, hk, _ => exact absurd hk (by decide)
  | .i5, _, hk, _ => exact absurd hk (by decide)
  | .i6, _, hk, _ => exact absurd hk (by decide)
  | .i7, _, hk, _ => exact absurd hk (by decide)
  | _, .i1, _, hl => exact absurd hl (by decide)
  | _, .i2, _, hl => exact absurd hl (by decide)
  | _, .i3, _, hl => exact absurd hl (by decide)
  | _, .i4, _, hl => exact absurd hl (by decide)
  | _, .i5, _, hl => exact absurd hl (by decide)
  | _, .i6, _, hl => exact absurd hl (by decide)
  | _, .i7, _, hl => exact absurd hl (by decide)

omit [Finite K] [CharP K F4.prime]
  in
theorem R1_eq_rootJoin : R1 K a = rootJoin K a {.i8, .i9, .i10, .i11, .i12} := rfl

omit [Finite K] [CharP K F4.prime]
  in
theorem R1_eq_closure :
    R1 K a = closure (⋃ k ∈ ({.i8, .i9, .i10, .i11, .i12} : Finset Idx),
      Set.range (rootElt K a k)) := by
  rw [R1_eq_rootJoin, rootJoin, Subgroup.closure_iUnion]
  refine iSup_congr fun k => ?_
  rw [Subgroup.closure_iUnion]
  rfl

theorem commute_of_mem_R1 (hK : Nat.card K = 2 ^ (2 * a + 1)) {x y : ModGL F4.tag K}
    (hx : x ∈ R1 K a) (hy : y ∈ R1 K a) : x * y = y * x := by
  set S : Set (ModGL F4.tag K) := ⋃ k ∈ ({.i8, .i9, .i10, .i11, .i12} : Finset Idx),
    Set.range (rootElt K a k)
  have hS : ∀ s ∈ S, ∀ s' ∈ S, s * s' = s' * s := by
    intro s hs s' hs'
    simp only [S, Set.mem_iUnion, Set.mem_range] at hs hs'
    obtain ⟨k, hk, u, rfl⟩ := hs
    obtain ⟨l, hl, v, rfl⟩ := hs'
    exact rootElt_commute_of_isR1 hK (by revert hk; decide +revert) (by revert hl; decide +revert)
      u v
  have h1 : closure S ≤ centralizer S := (closure_le _).2 fun s hs =>
    mem_centralizer_iff.2 fun s' hs' => hS s' hs' s hs
  have h2 : closure S ≤ centralizer (closure S : Set (ModGL F4.tag K)) := (closure_le _).2
    fun s hs => mem_centralizer_iff.2 fun x hx => (mem_centralizer_iff.1 (h1 hx) s hs).symm
  rw [R1_eq_closure] at hx hy
  exact mem_centralizer_iff.1 (h2 hy) x hx

omit [Finite K] [CharP K F4.prime]
  in
theorem rootElt_mem_R1 {k : Idx} (hk : k.isR1 = true) (c : K) : rootElt K a k c ∈ R1 K a := by
  rw [R1_eq_rootJoin]
  have hkI : k ∈ ({.i8, .i9, .i10, .i11, .i12} : Finset Idx) := by
    cases k <;> simp_all [Idx.isR1]
  exact rootV_le_rootJoin hkI (rootElt_mem_rootV _ _)

omit [Finite K] [CharP K F4.prime]
  in
theorem r1Elt_mem (u : Idx → K) : r1Elt K a u ∈ R1 K a :=
  mul_mem (mul_mem (mul_mem (mul_mem (rootElt_mem_R1 rfl _) (rootElt_mem_R1 rfl _))
    (rootElt_mem_R1 rfl _)) (rootElt_mem_R1 rfl _)) (rootElt_mem_R1 rfl _)

theorem r1Elt_add (hK : Nat.card K = 2 ^ (2 * a + 1)) (u v : Idx → K) :
    r1Elt K a (u + v) = r1Elt K a u * r1Elt K a v := by
  have hc : ∀ {k l : Idx}, k.isR1 = true → l.isR1 = true → ∀ c d : K,
      Commute (rootElt K a k c) (rootElt K a l d) := fun hk hl c d =>
    rootElt_commute_of_isR1 hK hk hl c d
  have c8_11 := (hc (k := .i8) (l := .i11) rfl rfl (v .i8) (u .i11)).left_comm
  have c8_12 := (hc (k := .i8) (l := .i12) rfl rfl (v .i8) (u .i12)).left_comm
  have c8_9 := (hc (k := .i8) (l := .i9) rfl rfl (v .i8) (u .i9)).left_comm
  have c8_10 := (hc (k := .i8) (l := .i10) rfl rfl (v .i8) (u .i10)).left_comm
  have c11_12 := (hc (k := .i11) (l := .i12) rfl rfl (v .i11) (u .i12)).left_comm
  have c11_9 := (hc (k := .i11) (l := .i9) rfl rfl (v .i11) (u .i9)).left_comm
  have c11_10 := (hc (k := .i11) (l := .i10) rfl rfl (v .i11) (u .i10)).left_comm
  have c12_9 := (hc (k := .i12) (l := .i9) rfl rfl (v .i12) (u .i9)).left_comm
  have c12_10 := (hc (k := .i12) (l := .i10) rfl rfl (v .i12) (u .i10)).left_comm
  have c9_10 := (hc (k := .i9) (l := .i10) rfl rfl (v .i9) (u .i10)).left_comm
  simp only [r1Elt, Pi.add_apply, rootElt_add hK (i := .i8) rfl, rootElt_add hK (i := .i9) rfl,
    rootElt_add hK (i := .i10) rfl, rootElt_add hK (i := .i11) rfl,
    rootElt_add hK (i := .i12) rfl, mul_assoc]
  simp only [c8_11, c8_12, c8_9, c8_10, c11_12,
    c11_9, c11_10, c12_9, c12_10, c9_10]

omit [Finite K] [CharP K F4.prime]
  in
theorem r1Elt_zero : r1Elt K a 0 = 1 := by
  simp only [r1Elt, Pi.zero_apply, rootElt_zero, mul_one]

theorem r1Elt_mul_self (hK : Nat.card K = 2 ^ (2 * a + 1)) (u : Idx → K) :
    r1Elt K a u * r1Elt K a u = 1 := by
  rw [← r1Elt_add hK, show u + u = 0 from funext fun k => CharTwo.add_self_eq_zero (u k),
    r1Elt_zero]

omit [Finite K] [CharP K F4.prime]
  in
theorem rootElt_eq_r1Elt {k : Idx} (hk : k.isR1 = true) (c : K) :
    rootElt K a k c = r1Elt K a (Pi.single k c) := by
  cases k <;> simp only [Idx.isR1, Bool.false_eq_true] at hk <;>
    simp [r1Elt, rootElt_zero]

theorem r1Elt_eq_sylowVec (hK : Nat.card K = 2 ^ (2 * a + 1)) (u : Idx → K) :
    r1Elt K a u = sylowVec a K ![0, 0, 0, 0, u .i8, 0, u .i11, 0, u .i12, 0, u .i9, u .i10] := by
  rw [sylowVec_eq_prod_rootElt hK]
  simp [r1Elt, rootElt_zero, mul_assoc]

theorem r1Elt_eq_iff (hK : Nat.card K = 2 ^ (2 * a + 1)) {u v : Idx → K} :
    r1Elt K a u = r1Elt K a v ↔ ∀ k : Idx, k.isR1 = true → u k = v k := by
  constructor
  · intro h
    rw [r1Elt_eq_sylowVec hK, r1Elt_eq_sylowVec hK] at h
    have h' := (bijOn_sylowVec hK).2.1 (Set.mem_univ _) (Set.mem_univ _) h
    intro k hk
    cases k <;> simp only [Idx.isR1, Bool.false_eq_true] at hk
    · exact congrFun h' 4
    · exact congrFun h' 10
    · exact congrFun h' 11
    · exact congrFun h' 6
    · exact congrFun h' 8
  · intro h
    simp only [r1Elt, h .i8 rfl, h .i9 rfl, h .i10 rfl, h .i11 rfl, h .i12 rfl]

theorem exists_r1Elt_eq (hK : Nat.card K = 2 ^ (2 * a + 1)) {g : ModGL F4.tag K}
    (hg : g ∈ R1 K a) : ∃ u : Idx → K, g = r1Elt K a u := by
  have hg' : g ∈ (R1 K a : Set (ModGL F4.tag K)) := hg
  rw [(R1_spec hK).2.1] at hg'
  obtain ⟨x, hx, rfl⟩ := hg'
  refine ⟨fun k => match k with
    | .i8 => x 4 | .i11 => x 6 | .i12 => x 8 | .i9 => x 10 | .i10 => x 11 | _ => 0, ?_⟩
  rw [r1Elt_eq_sylowVec hK]
  congr 1
  funext n
  fin_cases n <;> simp_all

theorem torusPair_conj_r1Elt (hK : Nat.card K = 2 ^ (2 * a + 1)) (t : Kˣ × Kˣ) (u : Idx → K) :
    torusPair a t * r1Elt K a u * (torusPair a t)⁻¹ =
      r1Elt K a fun k => (rootChar K a k t : K) * u k := by
  rw [show torusPair a t * r1Elt K a u * (torusPair a t)⁻¹ =
    MulAut.conj (torusPair a t) (r1Elt K a u) from rfl]
  simp only [r1Elt, map_mul, MulAut.conj_apply, torusPair_conj_rootElt hK]

theorem rootElt_one_comm_eight (hK : Nat.card K = 2 ^ (2 * a + 1)) (c : K) :
    ⁅rootElt K a .i1 1, rootElt K a .i8 c⁆ =
      r1Elt K a (Pi.single .i9 c + Pi.single .i11 c + Pi.single .i12 (largeReeSigma a c)) := by
  rw [rootElt_comm_1_8 hK, r1Elt_add hK, r1Elt_add hK, ← rootElt_eq_r1Elt rfl,
    ← rootElt_eq_r1Elt rfl, ← rootElt_eq_r1Elt rfl]
  simp only [one_mul, largeReeSigma_one, mul_one]

theorem rootElt_one_comm_nine (hK : Nat.card K = 2 ^ (2 * a + 1)) (c : K) :
    ⁅rootElt K a .i1 1, rootElt K a .i9 c⁆ =
      r1Elt K a (Pi.single .i10 c + Pi.single .i11 c + Pi.single .i12 (largeReeSigma a c)) := by
  rw [rootElt_comm_1_9 hK, r1Elt_add hK, r1Elt_add hK, ← rootElt_eq_r1Elt rfl,
    ← rootElt_eq_r1Elt rfl, ← rootElt_eq_r1Elt rfl]
  simp only [one_mul, largeReeSigma_one, mul_one]

theorem rootElt_one_comm_ten (hK : Nat.card K = 2 ^ (2 * a + 1)) (c : K) :
    ⁅rootElt K a .i1 1, rootElt K a .i10 c⁆ = rootElt K a .i11 c := by
  rw [rootElt_comm_1_10 hK, one_mul]

omit [CharP K F4.prime]
  in
theorem exists_rootChar_eq_one_ne_one (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {k l : Idx}
    (hk : k.isR1 = true) (hl : l.isR1 = true) (hkl : k ≠ l) :
    ∃ t : Kˣ × Kˣ, rootChar K a l t = 1 ∧ rootChar K a k t ≠ 1 := by
  have hc : (Idx.r1Col l).isCenter = false := by revert hl; cases l <;> decide
  have hb : Idx.brace (Idx.r1Col l) k ≠ 0 := by
    revert hk hl hkl; cases k <;> cases l <;> decide
  obtain ⟨μ, hμ⟩ := exists_largeReeSigma_ne ha hK
  have hμ0 : μ ≠ 0 := fun h0 => hμ (by rw [h0, largeReeSigma_zero])
  have hμ1 : μ ≠ 1 := fun h1 => hμ (by rw [h1, largeReeSigma_one])
  obtain ⟨t, ht, htk⟩ := exists_rootChar_mul_eq hK hc hb one_ne_zero hμ0
  refine ⟨t, ?_, fun h1 => hμ1 (by rw [← htk, h1, Units.val_one, mul_one])⟩
  have hcen : ∀ {i : Idx}, i.isSz = true → rootChar K a i t = 1 → rootChar K a i.center t = 1 :=
    fun hi h1 => by rw [rootChar_center hK hi, h1, one_pow]
  cases l <;> simp only [Idx.isR1, Bool.false_eq_true] at hl
  · exact hcen (i := .i4) rfl ht
  · exact ht
  · exact ht
  · exact hcen (i := .i6) rfl ht
  · exact hcen (i := .i5) rfl ht

theorem exists_rootElt_mem_of_r1Elt_mem (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {M : Subgroup (ModGL F4.tag K)}
    (hM : ∀ t : Kˣ × Kˣ, ∀ x ∈ M, torusPair a t * x * (torusPair a t)⁻¹ ∈ M) {u : Idx → K}
    (hu : r1Elt K a u ∈ M) {k : Idx} (hk : k.isR1 = true) (huk : u k ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ rootElt K a k c ∈ M := by
  have step : ∀ v : Idx → K, r1Elt K a v ∈ M → v k ≠ 0 → ∀ l : Idx, l.isR1 = true → l ≠ k →
      ∃ w : Idx → K, r1Elt K a w ∈ M ∧ w k ≠ 0 ∧ w l = 0 ∧ ∀ j, v j = 0 → w j = 0 := by
    intro v hv hvk l hl hlk
    obtain ⟨t, htl, htk⟩ := exists_rootChar_eq_one_ne_one ha hK hk hl (Ne.symm hlk)
    have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
    refine ⟨fun j => ((rootChar K a j t : K) + 1) * v j, ?_, ?_, ?_, fun j hj => by simp [hj]⟩
    · have h1 := mul_mem (hM t _ hv) hv
      rw [torusPair_conj_r1Elt hK, ← r1Elt_add hK] at h1
      convert h1 using 2
      funext j
      simp only [Pi.add_apply]
      ring
    · refine mul_ne_zero (fun h0 => htk (Units.ext ?_)) hvk
      rw [Units.val_one]
      linear_combination h0 - h2
    · simp only [htl, Units.val_one, h2, zero_mul]
  have iter : ∀ L : List Idx, (∀ l ∈ L, l.isR1 = true) →
      ∃ w : Idx → K, r1Elt K a w ∈ M ∧ w k ≠ 0 ∧ ∀ l ∈ L, l ≠ k → w l = 0 := by
    intro L
    induction L with
    | nil => exact fun _ => ⟨u, hu, huk, by simp⟩
    | cons l L ih =>
      intro hL
      obtain ⟨w, hw, hwk, hwL⟩ := ih fun l' hl' => hL l' (List.mem_cons_of_mem _ hl')
      by_cases hlk : l = k
      · refine ⟨w, hw, hwk, fun l' hl' hl'k => ?_⟩
        rcases List.mem_cons.1 hl' with rfl | hl'
        · exact absurd hlk hl'k
        · exact hwL l' hl' hl'k
      · obtain ⟨w', hw', hw'k, hw'l, hw'0⟩ := step w hw hwk l (hL l (by simp)) hlk
        refine ⟨w', hw', hw'k, fun l' hl' hl'k => ?_⟩
        rcases List.mem_cons.1 hl' with rfl | hl'
        · exact hw'l
        · exact hw'0 _ (hwL l' hl' hl'k)
  obtain ⟨w, hw, hwk, hwL⟩ := iter [.i8, .i9, .i10, .i11, .i12] (by decide)
  refine ⟨w k, hwk, ?_⟩
  have e : r1Elt K a w = rootElt K a k (w k) := by
    rw [rootElt_eq_r1Elt hk, r1Elt_eq_iff hK]
    intro j hj
    by_cases hjk : j = k
    · subst hjk
      simp
    · rw [Pi.single_eq_of_ne hjk]
      exact hwL j (by revert hj; cases j <;> simp [Idx.isR1]) hjk
  rwa [← e]

theorem rootV_le_of_r1Elt_mem (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {M : Subgroup (ModGL F4.tag K)}
    (hM : ∀ t : Kˣ × Kˣ, ∀ x ∈ M, torusPair a t * x * (torusPair a t)⁻¹ ∈ M) {u : Idx → K}
    (hu : r1Elt K a u ∈ M) {k : Idx} (hk : k.isR1 = true) (huk : u k ≠ 0) :
    rootV K a k ≤ M := by
  obtain ⟨c, hc, hcM⟩ := exists_rootElt_mem_of_r1Elt_mem ha hK hM hu hk huk
  rw [rootV, closure_le]
  rintro _ ⟨d, rfl⟩
  by_cases hd : d = 0
  · rw [hd, rootElt_zero]
    exact one_mem _
  · have hb : Idx.brace .i3 k ≠ 0 := by revert hk; cases k <;> decide
    obtain ⟨t, -, htd⟩ := exists_rootChar_mul_eq hK (i := .i3) rfl hb hc hd
    have h1 := hM t _ hcM
    rwa [torusPair_conj_rootElt hK, htd] at h1

theorem rootV_le_of_rootElt_mem (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {M : Subgroup (ModGL F4.tag K)}
    (hM : ∀ t : Kˣ × Kˣ, ∀ x ∈ M, torusPair a t * x * (torusPair a t)⁻¹ ∈ M) {k : Idx}
    (hk : k.isR1 = true) {c : K} (hc : c ≠ 0) (hcM : rootElt K a k c ∈ M) : rootV K a k ≤ M :=
  rootV_le_of_r1Elt_mem ha hK hM (u := Pi.single k c) (by rwa [← rootElt_eq_r1Elt hk]) hk
    (by simpa using hc)

theorem le_rootV_twelve_of_invariant (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {M : Subgroup (ModGL F4.tag K)} (hMR : M ≤ R1 K a)
    (hH : ∀ t : Kˣ × Kˣ, ∀ x ∈ M, torusPair a t * x * (torusPair a t)⁻¹ ∈ M)
    (h1 : ∀ x ∈ M, rootElt K a .i1 1 * x * (rootElt K a .i1 1)⁻¹ ∈ M)
    (hr : ∀ x ∈ M, weylR K * x * (weylR K)⁻¹ ∈ M) (hne : M ≠ R1 K a) :
    M ≤ rootV K a .i12 := by
  have hc1 : ∀ x ∈ M, ⁅rootElt K a .i1 1, x⁆ ∈ M := fun x hx => mul_mem (h1 x hx) (inv_mem hx)
  have hmem : ∀ {k : Idx}, rootV K a k ≤ M → ∀ c, rootElt K a k c ∈ M :=
    fun hk c => hk (rootElt_mem_rootV _ _)
  have h89 : rootV K a .i8 ≤ M → rootV K a .i9 ≤ M := fun h8 => by
    have h := hc1 _ (hmem h8 1)
    rw [rootElt_one_comm_eight hK] at h
    exact rootV_le_of_r1Elt_mem ha hK hH h rfl (by simp)
  have h910 : rootV K a .i9 ≤ M → rootV K a .i10 ≤ M := fun h9 => by
    have h := hc1 _ (hmem h9 1)
    rw [rootElt_one_comm_nine hK] at h
    exact rootV_le_of_r1Elt_mem ha hK hH h rfl (by simp)
  have h1011 : rootV K a .i10 ≤ M → rootV K a .i11 ≤ M := fun h10 => by
    have h := hc1 _ (hmem h10 1)
    rw [rootElt_one_comm_ten hK] at h
    exact rootV_le_of_rootElt_mem ha hK hH rfl one_ne_zero h
  have h118 : rootV K a .i11 ≤ M → rootV K a .i8 ≤ M := fun h11 => by
    have h := hr _ (hmem h11 1)
    rw [weylR_conj_rootElt (by decide) (by decide)] at h
    exact rootV_le_of_rootElt_mem ha hK hH rfl one_ne_zero h
  by_contra hnot
  obtain ⟨x, hxM, hx12⟩ := IsConcreteLE.not_le_iff_exists.1 hnot
  obtain ⟨u, rfl⟩ := exists_r1Elt_eq hK (hMR hxM)
  have hu : u .i8 ≠ 0 ∨ u .i9 ≠ 0 ∨ u .i10 ≠ 0 ∨ u .i11 ≠ 0 := by
    by_contra! h0
    apply hx12
    have e : r1Elt K a u = rootElt K a .i12 (u .i12) := by
      rw [rootElt_eq_r1Elt rfl, r1Elt_eq_iff hK]
      intro j hj
      cases j <;> simp_all [Idx.isR1]
    rw [e]
    exact rootElt_mem_rootV _ _
  have h8 : rootV K a .i8 ≤ M := by
    rcases hu with h | h | h | h
    · exact rootV_le_of_r1Elt_mem ha hK hH hxM rfl h
    · exact h118 (h1011 (h910 (rootV_le_of_r1Elt_mem ha hK hH hxM rfl h)))
    · exact h118 (h1011 (rootV_le_of_r1Elt_mem ha hK hH hxM rfl h))
    · exact h118 (rootV_le_of_r1Elt_mem ha hK hH hxM rfl h)
  have h9 := h89 h8
  have h10 := h910 h9
  have h11 := h1011 h10
  have h12 : rootV K a .i12 ≤ M := by
    have h := hc1 _ (hmem h8 1)
    rw [rootElt_one_comm_eight hK, largeReeSigma_one, r1Elt_add hK, r1Elt_add hK,
      ← rootElt_eq_r1Elt (k := .i12) rfl, ← rootElt_eq_r1Elt (k := .i9) rfl,
      ← rootElt_eq_r1Elt (k := .i11) rfl] at h
    have h' := mul_mem (inv_mem (mul_mem (hmem h9 1) (hmem h11 1))) h
    rw [inv_mul_cancel_left] at h'
    exact rootV_le_of_rootElt_mem ha hK hH rfl one_ne_zero h'
  apply hne
  refine le_antisymm hMR ?_
  rw [R1, rootJoin]
  refine iSup₂_le fun k hk => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact h8
  · exact h9
  · exact h10
  · exact h11
  · exact h12

end R1

end CFSG.LocalAnalysis.EvenBN.TwoF4

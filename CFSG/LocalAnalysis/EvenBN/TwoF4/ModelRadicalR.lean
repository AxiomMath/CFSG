module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.ModelRadicals
public import CFSG.LocalAnalysis.EvenBN.TwoF4.SuzukiSylow

public section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (torusPair)
open scoped commutatorElement

section Generic

variable {X : Type*} [Group X]

theorem commutatorElement_mul_left_of_commute {a b r : X} (h : a * ⁅b, r⁆ = ⁅b, r⁆ * a) :
    ⁅a * b, r⁆ = ⁅b, r⁆ * ⁅a, r⁆ := by
  calc ⁅a * b, r⁆ = a * ⁅b, r⁆ * r * a⁻¹ * r⁻¹ := by simp only [commutatorElement_def]; group
    _ = ⁅b, r⁆ * a * r * a⁻¹ * r⁻¹ := by rw [h]
    _ = ⁅b, r⁆ * ⁅a, r⁆ := by simp only [commutatorElement_def]; group

theorem commutatorElement_mul_right_of_commute {a b c : X} (h : b * ⁅a, c⁆ = ⁅a, c⁆ * b) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  calc ⁅a, b * c⁆ = a * b * a⁻¹ * b⁻¹ * (b * ⁅a, c⁆) * b⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = a * b * a⁻¹ * b⁻¹ * (⁅a, c⁆ * b) * b⁻¹ := by rw [h]
    _ = ⁅a, b⁆ * ⁅a, c⁆ := by simp only [commutatorElement_def]; group

theorem commutator_closure_le {S S' : Set X} {N : Subgroup X}
    (hS : closure S ≤ normalizer (N : Set X)) (hS' : closure S' ≤ normalizer (N : Set X))
    (h : ∀ s ∈ S, ∀ s' ∈ S', ⁅s, s'⁆ ∈ N) : ⁅closure S, closure S'⁆ ≤ N := by
  have h1 : ∀ s' ∈ S', ∀ g ∈ closure S, ⁅g, s'⁆ ∈ N := by
    intro s' hs' g hg
    induction hg using closure_induction with
    | mem x hx => exact h x hx s' hs'
    | one => simp
    | mul x y hx hy ihx ihy =>
      have e : ⁅x * y, s'⁆ = x * ⁅y, s'⁆ * x⁻¹ * ⁅x, s'⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact mul_mem ((mem_normalizer_iff.1 (hS hx) _).1 ihy) ihx
    | inv x hx ihx =>
      have e : ⁅x⁻¹, s'⁆ = x⁻¹ * ⁅x, s'⁆⁻¹ * x⁻¹⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact (mem_normalizer_iff.1 (hS (inv_mem hx)) _).1 (inv_mem ihx)
  refine (commutator_le).2 fun g hg x hx => ?_
  induction hx using closure_induction with
  | mem x hx => exact h1 x hx g hg
  | one => simp
  | mul x y hx hy ihx ihy =>
    have e : ⁅g, x * y⁆ = ⁅g, x⁆ * (x * ⁅g, y⁆ * x⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact mul_mem ihx ((mem_normalizer_iff.1 (hS' hx) _).1 ihy)
  | inv x hx ihx =>
    have e : ⁅g, x⁻¹⁆ = x⁻¹ * ⁅g, x⁆⁻¹ * x⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (mem_normalizer_iff.1 (hS' (inv_mem hx)) _).1 (inv_mem ihx)

theorem commutatorElement_mem_swap {N : Subgroup X} {x y : X} (h : ⁅x, y⁆ ∈ N) : ⁅y, x⁆ ∈ N := by
  rw [← commutatorElement_inv]
  exact inv_mem h

theorem eq_one_of_add_of_const {K : Type*} [Field K] {μ : K} (hμ : μ ≠ 0) (hμ1 : μ + 1 ≠ 0)
    {f : K → X} (hadd : ∀ c d, f (c + d) = f c * f d)
    (hconst : ∀ c d : K, c ≠ 0 → d ≠ 0 → f c = f d) (c : K) : f c = 1 := by
  have h1 : f 1 = 1 := by
    have e := hadd μ 1
    rw [hconst (μ + 1) 1 hμ1 one_ne_zero, hconst μ 1 hμ one_ne_zero] at e
    exact left_eq_mul.1 e
  by_cases hc : c = 0
  · have e := hadd 0 0
    rw [add_zero] at e
    rw [hc]
    exact left_eq_mul.1 e
  · rw [hconst c 1 hc one_ne_zero, h1]

end Generic

variable {K : Type} [Field K] {a : ℕ} [Finite K] [CharP K F4.prime]

theorem rootElt_commute_twelve (hK : Nat.card K = 2 ^ (2 * a + 1)) (k : Idx) (s c : K) :
    rootElt K a k s * rootElt K a .i12 c = rootElt K a .i12 c * rootElt K a k s := by
  have hc : ∀ {x y : ModGL F4.tag K}, ⁅x, y⁆ = 1 → x * y = y * x := fun h =>
    commutatorElement_eq_one_iff_mul_comm.1 h
  match k with
  | .i1 => exact hc (rootElt_comm_1_12 hK s c)
  | .i2 => exact hc (rootElt_comm_2_12 hK s c)
  | .i3 => exact hc (rootElt_comm_3_12 hK s c)
  | .i4 => exact hc (rootElt_comm_4_12 hK s c)
  | .i5 => exact hc (rootElt_comm_5_12 hK s c)
  | .i6 => exact hc (rootElt_comm_6_12 hK s c)
  | .i7 => exact (hc (rootElt_comm_12_7 hK c s)).symm
  | .i8 => exact hc (rootElt_comm_8_12 hK s c)
  | .i9 => exact (hc (rootElt_comm_12_9 hK c s)).symm
  | .i10 => exact (hc (rootElt_comm_12_10 hK c s)).symm
  | .i11 => exact hc (rootElt_comm_11_12 hK s c)
  | .i12 => rw [← rootElt_add hK rfl, ← rootElt_add hK rfl, add_comm]

@[expose] def r1Pair (k : Idx) (s : K) (u : Idx → K) : K :=
  match k with
  | .i3 => s * u .i11
  | .i4 => s * u .i10
  | .i6 => s * u .i9
  | .i7 => s * u .i8
  | _ => 0

theorem comm_r1Elt_of (hK : Nat.card K = 2 ^ (2 * a + 1)) {x : ModGL F4.tag K} {e : Idx → K}
    (he : ∀ l : Idx, l.isR1 = true → ∀ c : K, ⁅x, rootElt K a l c⁆ = rootElt K a .i12 (e l * c))
    (u : Idx → K) :
    ⁅x, r1Elt K a u⁆ = rootElt K a .i12 (e .i8 * u .i8 + e .i11 * u .i11 + e .i12 * u .i12 +
      e .i9 * u .i9 + e .i10 * u .i10) := by
  have hz : ∀ {y : ModGL F4.tag K}, y ∈ R1 K a → ∀ c,
      y * rootElt K a .i12 c = rootElt K a .i12 c * y := fun hy c =>
    commute_of_mem_R1 hK hy (rootElt_mem_R1 rfl c)
  have m : ∀ {l : Idx}, l.isR1 = true → ∀ c, rootElt K a l c ∈ R1 K a := fun hl c =>
    rootElt_mem_R1 hl c
  simp only [r1Elt]
  rw [commutatorElement_mul_right_of_commute (by
      rw [he .i10 rfl]
      exact hz (mul_mem (mul_mem (mul_mem (m rfl _) (m rfl _)) (m rfl _)) (m rfl _)) _),
    commutatorElement_mul_right_of_commute (by
      rw [he .i9 rfl]
      exact hz (mul_mem (mul_mem (m rfl _) (m rfl _)) (m rfl _)) _),
    commutatorElement_mul_right_of_commute (by
      rw [he .i12 rfl]
      exact hz (mul_mem (m rfl _) (m rfl _)) _),
    commutatorElement_mul_right_of_commute (by
      rw [he .i11 rfl]
      exact hz (m rfl _) _),
    he .i8 rfl, he .i11 rfl, he .i12 rfl, he .i9 rfl, he .i10 rfl, ← rootElt_add hK rfl,
    ← rootElt_add hK rfl, ← rootElt_add hK rfl, ← rootElt_add hK rfl]

theorem rootElt_comm_r1Elt (hK : Nat.card K = 2 ^ (2 * a + 1)) {k : Idx} (hk1 : k ≠ .i1)
    (hk2 : k ≠ .i2) (s : K) (u : Idx → K) :
    ⁅rootElt K a k s, r1Elt K a u⁆ = rootElt K a .i12 (r1Pair k s u) := by
  have z : ∀ {x y : ModGL F4.tag K}, ⁅y, x⁆ = 1 → ⁅x, y⁆ = 1 := fun h => by
    rw [← commutatorElement_inv, h, inv_one]
  have hR1 : k.isR1 = true → ⁅rootElt K a k s, r1Elt K a u⁆ = rootElt K a .i12 (r1Pair k s u) :=
    fun hk => by
      rw [commutatorElement_eq_one_iff_mul_comm.2
        (commute_of_mem_R1 hK (rootElt_mem_R1 hk s) (r1Elt_mem u))]
      have : r1Pair k s u = 0 := by revert hk; cases k <;> simp [Idx.isR1, r1Pair]
      rw [this, rootElt_zero]
  match k, hk1, hk2 with
  | .i3, _, _ =>
    rw [comm_r1Elt_of hK (e := fun l => if l = .i11 then s else 0) (fun l hl c => ?_) u]
    · simp [r1Pair]
    · cases l <;> simp only [Idx.isR1, Bool.false_eq_true] at hl <;>
        simp [rootElt_comm_3_8 hK, rootElt_comm_3_11 hK, rootElt_comm_3_12 hK,
          rootElt_comm_3_9 hK, rootElt_comm_3_10 hK, rootElt_zero]
  | .i4, _, _ =>
    rw [comm_r1Elt_of hK (e := fun l => if l = .i10 then s else 0) (fun l hl c => ?_) u]
    · simp [r1Pair]
    · cases l <;> simp only [Idx.isR1, Bool.false_eq_true] at hl <;>
        simp [rootElt_comm_4_8 hK, rootElt_comm_4_11 hK, rootElt_comm_4_12 hK,
          rootElt_comm_4_9 hK, rootElt_comm_4_10 hK, rootElt_zero]
  | .i5, _, _ =>
    rw [comm_r1Elt_of hK (e := fun _ => 0) (fun l hl c => ?_) u]
    · simp [r1Pair]
    · cases l <;> simp only [Idx.isR1, Bool.false_eq_true] at hl <;>
        simp [z (rootElt_comm_8_5 hK _ _), z (rootElt_comm_11_5 hK _ _), rootElt_comm_5_12 hK,
          rootElt_comm_5_9 hK, rootElt_comm_5_10 hK, rootElt_zero]
  | .i6, _, _ =>
    rw [comm_r1Elt_of hK (e := fun l => if l = .i9 then s else 0) (fun l hl c => ?_) u]
    · simp [r1Pair]
    · cases l <;> simp only [Idx.isR1, Bool.false_eq_true] at hl <;>
        simp [z (rootElt_comm_8_6 hK _ _), rootElt_comm_6_11 hK, rootElt_comm_6_12 hK,
          rootElt_comm_6_9 hK, rootElt_comm_6_10 hK, rootElt_zero]
  | .i7, _, _ =>
    have h78 : ∀ c, ⁅rootElt K a .i7 s, rootElt K a .i8 c⁆ = rootElt K a .i12 (s * c) := fun c => by
      rw [← commutatorElement_inv, rootElt_comm_8_7 hK, mul_comm,
        inv_eq_of_mul_eq_one_right (rootElt_mul_self hK rfl _)]
    rw [comm_r1Elt_of hK (e := fun l => if l = .i8 then s else 0) (fun l hl c => ?_) u]
    · simp [r1Pair]
    · cases l <;> simp only [Idx.isR1, Bool.false_eq_true] at hl <;>
        simp [h78, z (rootElt_comm_11_7 hK _ _), z (rootElt_comm_12_7 hK _ _),
          rootElt_comm_7_9 hK, rootElt_comm_7_10 hK, rootElt_zero]
  | .i8, _, _ => exact hR1 rfl
  | .i9, _, _ => exact hR1 rfl
  | .i10, _, _ => exact hR1 rfl
  | .i11, _, _ => exact hR1 rfl
  | .i12, _, _ => exact hR1 rfl

theorem comm_list_prod_r1Elt (hK : Nat.card K = 2 ^ (2 * a + 1)) (u : Idx → K) :
    ∀ L : List (Idx × K), (∀ p ∈ L, p.1 ≠ .i1 ∧ p.1 ≠ .i2) →
      ⁅(L.map fun p => rootElt K a p.1 p.2).prod, r1Elt K a u⁆ =
        rootElt K a .i12 (L.map fun p => r1Pair p.1 p.2 u).sum
  | [], _ => by simp [rootElt_zero]
  | p :: L, hL => by
    have ih := comm_list_prod_r1Elt hK u L fun q hq => hL q (List.mem_cons_of_mem _ hq)
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    rw [commutatorElement_mul_left_of_commute (by rw [ih]; exact rootElt_commute_twelve hK _ _ _),
      ih, rootElt_comm_r1Elt hK (hL p (by simp)).1 (hL p (by simp)).2, ← rootElt_add hK rfl,
      add_comm]

theorem comm_sylowVec_r1Elt (hK : Nat.card K = 2 ^ (2 * a + 1)) {x : Fin 12 → K}
    (hx1 : x 1 = 0) (hx2 : x 2 = 0) (u : Idx → K) :
    ⁅sylowVec a K x, r1Elt K a u⁆ =
      rootElt K a .i12 (x 0 * u .i11 + x 3 * u .i10 + x 5 * u .i9 + x 9 * u .i8) := by
  have e : sylowVec a K x = ([(Idx.i3, x 0), (.i4, x 3), (.i8, x 4), (.i6, x 5), (.i11, x 6),
      (.i5, x 7), (.i12, x 8), (.i7, x 9), (.i9, x 10), (.i10, x 11)].map
        fun p => rootElt K a p.1 p.2).prod := by
    rw [sylowVec_eq_prod_rootElt hK, hx1, hx2, rootElt_zero, rootElt_zero]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rw [e, comm_list_prod_r1Elt hK u _ (by simp)]
  congr 1
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, r1Pair]
  ring

theorem exists_sylowVec_of_mem_radR (hK : Nat.card K = 2 ^ (2 * a + 1)) {g : ModGL F4.tag K}
    (hg : g ∈ radR K a) : ∃ x : Fin 12 → K, x 1 = 0 ∧ x 2 = 0 ∧ g = sylowVec a K x := by
  have hg' : g ∈ (radR K a : Set (ModGL F4.tag K)) := hg
  rw [(radR_spec hK).2.1] at hg'
  obtain ⟨x, hx, rfl⟩ := hg'
  exact ⟨x, hx 1 (by decide), hx 2 (by decide), rfl⟩

theorem commutator_radR_R1 (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ⁅radR K a, R1 K a⁆ = rootV K a .i12 := by
  refine le_antisymm ((commutator_le).2 fun g hg r hr => ?_) ?_
  · obtain ⟨x, hx1, hx2, rfl⟩ := exists_sylowVec_of_mem_radR hK hg
    obtain ⟨u, rfl⟩ := exists_r1Elt_eq hK hr
    rw [comm_sylowVec_r1Elt hK hx1 hx2]
    exact rootElt_mem_rootV _ _
  · rw [rootV, closure_le]
    rintro _ ⟨c, rfl⟩
    have e := rootElt_comm_3_11 hK c 1
    rw [mul_one] at e
    rw [← e]
    exact commutator_mem_commutator (rootV_le_rootJoin (by decide) (rootElt_mem_rootV _ _))
      (rootElt_mem_R1 rfl 1)

theorem R1_le_radR (hK : Nat.card K = 2 ^ (2 * a + 1)) : R1 K a ≤ radR K a :=
  (S1_le_S2_le_S3_le_S4_le_radS hK).2.2.2.2.1

theorem radR_inf_centralizer_R1 (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    radR K a ⊓ centralizer (R1 K a : Set (ModGL F4.tag K)) = rootV K a .i5 ⊔ R1 K a := by
  refine le_antisymm (fun g hg => ?_) (le_inf (sup_le (rootV_le_rootJoin (by decide))
    (R1_le_radR hK)) (sup_le ?_ fun r hr => mem_centralizer_iff.2 fun y hy =>
      commute_of_mem_R1 hK hy hr))
  · obtain ⟨hgR, hgC⟩ := mem_inf.1 hg
    obtain ⟨x, hx1, hx2, rfl⟩ := exists_sylowVec_of_mem_radR hK hgR
    have hcoef : ∀ u : Idx → K, r1Elt K a u ∈ R1 K a →
        x 0 * u .i11 + x 3 * u .i10 + x 5 * u .i9 + x 9 * u .i8 = 0 := fun u hu => by
      have h1 := commutatorElement_eq_one_iff_mul_comm.2
        (mem_centralizer_iff.1 hgC _ hu).symm
      rw [comm_sylowVec_r1Elt hK hx1 hx2, ← rootElt_zero (K := K) (a := a) .i12] at h1
      exact rootElt_injective hK _ h1
    have h0 : x 0 = 0 := by simpa using hcoef (Pi.single .i11 1) (r1Elt_mem _)
    have h3 : x 3 = 0 := by simpa using hcoef (Pi.single .i10 1) (r1Elt_mem _)
    have h5 : x 5 = 0 := by simpa using hcoef (Pi.single .i9 1) (r1Elt_mem _)
    have h9 : x 9 = 0 := by simpa using hcoef (Pi.single .i8 1) (r1Elt_mem _)
    rw [sylowVec_eq_prod_rootElt hK, h0, hx1, hx2, h3, h5, h9]
    simp only [rootElt_zero, one_mul, mul_one]
    have m : ∀ {l : Idx}, l.isR1 = true → ∀ c, rootElt K a l c ∈ rootV K a .i5 ⊔ R1 K a :=
      fun hl c => mem_sup_right (rootElt_mem_R1 hl c)
    exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (m rfl _) (m rfl _))
      (mem_sup_left (rootElt_mem_rootV _ _))) (m rfl _)) (m rfl _)) (m rfl _)
  · rw [rootV, closure_le]
    rintro _ ⟨c, rfl⟩
    refine mem_centralizer_iff.2 fun y hy => ?_
    obtain ⟨u, rfl⟩ := exists_r1Elt_eq hK hy
    have h := rootElt_comm_r1Elt hK (k := .i5) (by decide) (by decide) c u
    simp only [r1Pair, rootElt_zero] at h
    exact (commutatorElement_eq_one_iff_mul_comm.1 h).symm

theorem R1_inf_centralizer_radR_le (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    R1 K a ⊓ centralizer (radR K a : Set (ModGL F4.tag K)) ≤ rootV K a .i12 := by
  intro g hg
  obtain ⟨hgR, hgC⟩ := mem_inf.1 hg
  obtain ⟨u, rfl⟩ := exists_r1Elt_eq hK hgR
  have hcoef : ∀ k : Idx, k ∈ ({.i3, .i4, .i5, .i6, .i7, .i9, .i10} : Finset Idx) →
      r1Pair k 1 u = 0 := fun k hk => by
    have hk12 : k ≠ .i1 ∧ k ≠ .i2 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h1 := commutatorElement_eq_one_iff_mul_comm.2
      (mem_centralizer_iff.1 hgC _ (rootV_le_rootJoin hk (rootElt_mem_rootV k 1))).symm
    rw [← commutatorElement_inv, inv_eq_one, rootElt_comm_r1Elt hK hk12.1 hk12.2,
      ← rootElt_zero (K := K) (a := a) .i12] at h1
    exact rootElt_injective hK _ h1
  have h3 := hcoef .i3 (by decide)
  have h4 := hcoef .i4 (by decide)
  have h6 := hcoef .i6 (by decide)
  have h7 := hcoef .i7 (by decide)
  simp only [r1Pair, one_mul] at h3 h4 h6 h7
  have e : r1Elt K a u = rootElt K a .i12 (u .i12) := by
    rw [rootElt_eq_r1Elt rfl, r1Elt_eq_iff hK]
    intro j hj
    cases j <;> simp_all [Idx.isR1]
  rw [e]
  exact rootElt_mem_rootV _ _

omit [Finite K] [CharP K F4.prime]
  in
theorem radR_eq_closure :
    radR K a = closure (⋃ k ∈ ({.i3, .i4, .i5, .i6, .i7, .i9, .i10} : Finset Idx),
      Set.range (rootElt K a k)) := by
  rw [radR, rootJoin, Subgroup.closure_iUnion]
  refine iSup_congr fun k => ?_
  rw [Subgroup.closure_iUnion]
  rfl

theorem rootElt_comm_self_of_isSz (hK : Nat.card K = 2 ^ (2 * a + 1)) {k : Idx}
    (hk : k.isSz = true) (s t : K) :
    ⁅rootElt K a k s, rootElt K a k t⁆ = rootElt K a k.center
      (largeReeSigma a s * t + largeReeSigma a t * s) := by
  have hc : k.center.isCenter = true ∧ k.center.fourIdx = k.fourIdx := by
    cases k <;> simp_all [Idx.isSz, Idx.center, Idx.isCenter, Idx.fourIdx]
  rw [(rootElt_eq_coord k s).1 hk, (rootElt_eq_coord k t).1 hk, fourCoordG_commutator hK,
    (rootElt_eq_coord _ _).2.1 hc.1, hc.2]

theorem rootElt_comm_mem_R1 (hK : Nat.card K = 2 ^ (2 * a + 1)) {k l : Idx}
    (hk : k ∈ ({.i3, .i4, .i5, .i6, .i7, .i9, .i10} : Finset Idx))
    (hl : l ∈ ({.i3, .i4, .i5, .i6, .i7, .i9, .i10} : Finset Idx)) (s t : K) :
    ⁅rootElt K a k s, rootElt K a l t⁆ ∈ R1 K a := by
  have hN : radR K a ≤ normalizer (R1 K a : Set (ModGL F4.tag K)) :=
    (rootJoin_le_sylowP hK _).trans (R1_spec hK).2.2.2
  have hkR : rootElt K a k s ∈ radR K a := rootV_le_rootJoin hk (rootElt_mem_rootV _ _)
  have hlR : rootElt K a l t ∈ radR K a := rootV_le_rootJoin hl (rootElt_mem_rootV _ _)
  have m : ∀ {j : Idx}, j.isR1 = true → ∀ c, rootElt K a j c ∈ R1 K a := fun hj c =>
    rootElt_mem_R1 hj c
  have one : ∀ {x y : ModGL F4.tag K}, ⁅x, y⁆ = 1 → ⁅x, y⁆ ∈ R1 K a := fun h => h ▸ one_mem _
  have sw : ∀ {x y : ModGL F4.tag K}, ⁅x, y⁆ ∈ R1 K a → ⁅y, x⁆ ∈ R1 K a := fun h =>
    commutatorElement_mem_swap h
  have lin : ∀ {j : Idx}, j.isSz = false → ∀ c d,
      ⁅rootElt K a j c, rootElt K a j d⁆ ∈ R1 K a := fun hj c d => one
    (commutatorElement_eq_one_iff_mul_comm.2 (by
      rw [← rootElt_add hK hj, ← rootElt_add hK hj, add_comm]))
  have sz : ∀ {j : Idx}, j.isSz = true → j.center.isR1 = true → ∀ c d,
      ⁅rootElt K a j c, rootElt K a j d⁆ ∈ R1 K a := fun hj hc c d => by
    rw [rootElt_comm_self_of_isSz hK hj]
    exact m hc _
  have left : k.isR1 = true → ⁅rootElt K a k s, rootElt K a l t⁆ ∈ R1 K a := fun hk' => by
    have e : ⁅rootElt K a k s, rootElt K a l t⁆ = rootElt K a k s *
        (rootElt K a l t * (rootElt K a k s)⁻¹ * (rootElt K a l t)⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact mul_mem (m hk' s) ((mem_normalizer_iff.1 (hN hlR) _).1 (inv_mem (m hk' s)))
  have right : l.isR1 = true → ⁅rootElt K a k s, rootElt K a l t⁆ ∈ R1 K a := fun hl' => by
    rw [commutatorElement_def]
    exact mul_mem ((mem_normalizer_iff.1 (hN hkR) _).1 (m hl' t)) (inv_mem (m hl' t))
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk hl
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lin rfl s t
    · exact one (rootElt_comm_3_4 hK s t)
    · rw [rootElt_comm_3_5 hK]; exact m rfl _
    · rw [rootElt_comm_3_6 hK]; exact mul_mem (mul_mem (m rfl _) (m rfl _)) (m rfl _)
    · rw [rootElt_comm_3_7 hK]; exact mul_mem (m rfl _) (m rfl _)
    · exact right rfl
    · exact right rfl
  · rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sw (one (rootElt_comm_3_4 hK t s))
    · exact sz rfl rfl s t
    · rw [rootElt_comm_4_5 hK]; exact m rfl _
    · exact one (rootElt_comm_4_6 hK s t)
    · rw [rootElt_comm_4_7 hK]; exact mul_mem (mul_mem (m rfl _) (m rfl _)) (m rfl _)
    · exact right rfl
    · exact right rfl
  · rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sw (by rw [rootElt_comm_3_5 hK]; exact m rfl _)
    · exact sw (by rw [rootElt_comm_4_5 hK]; exact m rfl _)
    · exact sz rfl rfl s t
    · exact sw (by rw [rootElt_comm_6_5 hK]; exact m rfl _)
    · rw [rootElt_comm_5_7 hK]; exact m rfl _
    · exact right rfl
    · exact right rfl
  · rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sw (by
        rw [rootElt_comm_3_6 hK]; exact mul_mem (mul_mem (m rfl _) (m rfl _)) (m rfl _))
    · exact sw (one (rootElt_comm_4_6 hK t s))
    · rw [rootElt_comm_6_5 hK]; exact m rfl _
    · exact sz rfl rfl s t
    · exact one (rootElt_comm_6_7 hK s t)
    · exact right rfl
    · exact right rfl
  · rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sw (by rw [rootElt_comm_3_7 hK]; exact mul_mem (m rfl _) (m rfl _))
    · exact sw (by
        rw [rootElt_comm_4_7 hK]; exact mul_mem (mul_mem (m rfl _) (m rfl _)) (m rfl _))
    · exact sw (by rw [rootElt_comm_5_7 hK]; exact m rfl _)
    · exact sw (one (rootElt_comm_6_7 hK t s))
    · exact lin rfl s t
    · exact right rfl
    · exact right rfl
  · exact left rfl
  · exact left rfl

theorem commutator_radR_radR (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ⁅radR K a, radR K a⁆ = R1 K a := by
  have hN : radR K a ≤ normalizer (R1 K a : Set (ModGL F4.tag K)) :=
    (rootJoin_le_sylowP hK _).trans (R1_spec hK).2.2.2
  refine le_antisymm ?_ ?_
  · rw [radR_eq_closure]
    refine commutator_closure_le (by rw [← radR_eq_closure]; exact hN)
      (by rw [← radR_eq_closure]; exact hN) fun s hs s' hs' => ?_
    simp only [Set.mem_iUnion, Set.mem_range] at hs hs'
    obtain ⟨k, hk, c, rfl⟩ := hs
    obtain ⟨l, hl, d, rfl⟩ := hs'
    exact rootElt_comm_mem_R1 hK hk hl c d
  · have hR : ∀ {k : Idx}, k ∈ ({.i3, .i4, .i5, .i6, .i7, .i9, .i10} : Finset Idx) → ∀ c,
        rootElt K a k c ∈ radR K a := fun hk c => rootV_le_rootJoin hk (rootElt_mem_rootV _ _)
    have key : ∀ {k : Idx}, k.isR1 = true → rootV K a k ≤ ⁅radR K a, radR K a⁆ := by
      intro k hk
      rw [rootV, closure_le]
      rintro _ ⟨c, rfl⟩
      cases k <;> simp only [Idx.isR1, Bool.false_eq_true] at hk
      · have e := rootElt_comm_3_5 hK c 1
        rw [mul_one] at e
        rw [← e]
        exact commutator_mem_commutator (hR (by decide) c) (hR (by decide) 1)
      · have e := rootElt_comm_4_5 hK c 1
        rw [mul_one] at e
        rw [← e]
        exact commutator_mem_commutator (hR (by decide) c) (hR (by decide) 1)
      · have e := rootElt_comm_6_5 hK c 1
        rw [mul_one] at e
        rw [← e]
        exact commutator_mem_commutator (hR (by decide) c) (hR (by decide) 1)
      · have e := rootElt_comm_5_7 hK c 1
        rw [mul_one] at e
        rw [← e]
        exact commutator_mem_commutator (hR (by decide) c) (hR (by decide) 1)
      · have e := rootElt_comm_3_11 hK c 1
        rw [mul_one] at e
        rw [← e]
        exact commutator_mem_commutator (hR (by decide) c) (R1_le_radR hK (rootElt_mem_R1 rfl 1))
    rw [R1, rootJoin]
    refine iSup₂_le fun k hk => key ?_
    revert hk
    decide +revert

theorem sylowP_le_radR_sup (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    F4.reeFixedPosUnipotent K a ≤ radR K a ⊔ rootV K a .i1 := by
  have hR : ∀ {k : Idx}, k ∈ ({.i3, .i4, .i5, .i6, .i7, .i9, .i10} : Finset Idx) →
      rootV K a k ≤ radR K a ⊔ rootV K a .i1 := fun hk =>
    (rootV_le_rootJoin hk).trans le_sup_left
  rw [← rootJoin_univ hK]
  refine iSup₂_le fun i _ => ?_
  cases i
  · exact le_sup_right
  · exact (rootV_center_le hK .i1).1.trans le_sup_right
  · exact hR (by decide)
  · exact hR (by decide)
  · exact hR (by decide)
  · exact hR (by decide)
  · exact hR (by decide)
  · exact (rootV_center_le hK .i4).1.trans (hR (by decide))
  · exact hR (by decide)
  · exact hR (by decide)
  · exact (rootV_center_le hK .i6).1.trans (hR (by decide))
  · exact (rootV_center_le hK .i5).1.trans (hR (by decide))

theorem rootElt_eq_one_of_torusHi_invariant {X : Type*} [Group X] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {f : ModGL F4.tag K → X} {i k : Idx}
    (hi : i.isCenter = false) (hb : Idx.brace i k ≠ 0)
    (hmul : ∀ c d, f (rootElt K a k (c + d)) = f (rootElt K a k c) * f (rootElt K a k d))
    (hinv : ∀ t : Kˣ × Kˣ, torusPair a t ∈ torusHi K a i → ∀ c,
      f (rootElt K a k ((rootChar K a k t : K) * c)) = f (rootElt K a k c)) (c : K) :
    f (rootElt K a k c) = 1 := by
  obtain ⟨μ, hμ⟩ := exists_largeReeSigma_ne ha hK
  have hμ0 : μ ≠ 0 := fun h0 => hμ (by rw [h0, largeReeSigma_zero])
  have hμ1 : μ + 1 ≠ 0 := fun h1 => hμ (by
    rw [show μ = 1 by linear_combination h1 - CharTwo.add_self_eq_zero (1 : K), largeReeSigma_one])
  refine eq_one_of_add_of_const (f := fun c => f (rootElt K a k c)) hμ0 hμ1 hmul
    (fun c d hc hd => ?_) c
  obtain ⟨t, ht, htd⟩ := exists_torusHi_rootChar_mul_eq hK hi hb hc hd
  show f (rootElt K a k c) = f (rootElt K a k d)
  rw [← htd, hinv t ht]

theorem eq_one_of_torusHi_five_invariant_radR {X : Type*} [Group X] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {f : ModGL F4.tag K → X}
    (hf : ∀ x ∈ radR K a, ∀ y ∈ radR K a, f (x * y) = f x * f y)
    (hinv : ∀ t : Kˣ × Kˣ, torusPair a t ∈ torusHi K a .i5 → ∀ x ∈ radR K a,
      f (torusPair a t * x * (torusPair a t)⁻¹) = f x)
    (h5 : ∀ c, f (rootElt K a .i5 c) = 1) : ∀ x ∈ radR K a, f x = 1 := by
  have mem : ∀ {k : Idx}, k ∈ ({.i3, .i4, .i5, .i6, .i7, .i9, .i10} : Finset Idx) → ∀ c,
      rootElt K a k c ∈ radR K a := fun hk c => rootV_le_rootJoin hk (rootElt_mem_rootV _ _)
  have mem8 : ∀ c, rootElt K a .i8 c ∈ radR K a := fun c => R1_le_radR hK (rootElt_mem_R1 rfl c)
  have mem11 : ∀ c, rootElt K a .i11 c ∈ radR K a := fun c =>
    R1_le_radR hK (rootElt_mem_R1 rfl c)
  have hinv' : ∀ {k : Idx}, (∀ c, rootElt K a k c ∈ radR K a) →
      ∀ t : Kˣ × Kˣ, torusPair a t ∈ torusHi K a .i5 → ∀ c,
        f (rootElt K a k ((rootChar K a k t : K) * c)) = f (rootElt K a k c) := fun hk t ht c => by
    rw [← torusPair_conj_rootElt hK, hinv t ht _ (hk c)]
  have lin : ∀ {k : Idx}, k.isSz = false → Idx.brace .i5 k ≠ 0 → (∀ c, rootElt K a k c ∈ radR K a) →
      ∀ c, f (rootElt K a k c) = 1 := fun hks hb hk =>
    rootElt_eq_one_of_torusHi_invariant ha hK rfl hb
      (fun c d => by rw [rootElt_add hK hks, hf _ (hk c) _ (hk d)]) (hinv' hk)
  have sz : ∀ {k : Idx}, k.isSz = true → Idx.brace .i5 k ≠ 0 → (∀ c, rootElt K a k c ∈ radR K a) →
      (∀ c, rootElt K a k.center c ∈ radR K a) → (∀ c, f (rootElt K a k.center c) = 1) →
      ∀ c, f (rootElt K a k c) = 1 := fun {k} hks hb hk hkc hc =>
    rootElt_eq_one_of_torusHi_invariant ha hK rfl hb (fun c d => by
      have hcz : k.center.isCenter = true ∧ k.center.fourIdx = k.fourIdx := by
        cases k <;> simp_all [Idx.isSz, Idx.center, Idx.isCenter, Idx.fourIdx]
      have e : rootElt K a k c * rootElt K a k d =
          rootElt K a k (c + d) * rootElt K a k.center (largeReeSigma a c * d) := by
        rw [(rootElt_eq_coord k c).1 hks, (rootElt_eq_coord k d).1 hks,
          (rootElt_eq_coord k _).1 hks, (rootElt_eq_coord _ _).2.1 hcz.1, hcz.2,
          fourCoordG_mul_fourCoordG hK, ← fourCoordG_eq_mul hK, zero_add, zero_add]
      rw [← hf _ (hk c) _ (hk d), e, hf _ (hk _) _ (hkc _), hc, mul_one]) (hinv' hk)
  have f8 := lin (k := .i8) rfl (by decide) mem8
  have f11 := lin (k := .i11) rfl (by decide) mem11
  have gen : ∀ {k : Idx}, k ∈ ({.i3, .i4, .i5, .i6, .i7, .i9, .i10} : Finset Idx) → ∀ c,
      f (rootElt K a k c) = 1 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lin rfl (by decide) (mem (by decide))
    · exact sz rfl (by decide) (mem (by decide)) mem8 f8
    · exact h5
    · exact sz rfl (by decide) (mem (by decide)) mem11 f11
    · exact lin rfl (by decide) (mem (by decide))
    · exact lin rfl (by decide) (mem (by decide))
    · exact lin rfl (by decide) (mem (by decide))
  have f1 : f 1 = 1 := by
    have e := hf 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at e
    exact left_eq_mul.1 e
  intro x hx
  rw [radR_eq_closure] at hx
  induction hx using closure_induction with
  | mem y hy =>
    simp only [Set.mem_iUnion, Set.mem_range] at hy
    obtain ⟨k, hk, c, rfl⟩ := hy
    exact gen hk c
  | one => exact f1
  | mul y z hy hz ihy ihz =>
    rw [← radR_eq_closure] at hy hz
    rw [hf y hy z hz, ihy, ihz, mul_one]
  | inv y hy ihy =>
    rw [← radR_eq_closure] at hy
    have e := hf y⁻¹ (inv_mem hy) y hy
    rw [inv_mul_cancel, f1, ihy, mul_one] at e
    exact e.symm

theorem eq_one_of_torusHi_five_invariant_R1 {X : Type*} [Group X] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {f : ModGL F4.tag K → X}
    (hf : ∀ x ∈ R1 K a, ∀ y ∈ R1 K a, f (x * y) = f x * f y)
    (hinv : ∀ t : Kˣ × Kˣ, torusPair a t ∈ torusHi K a .i5 → ∀ x ∈ R1 K a,
      f (torusPair a t * x * (torusPair a t)⁻¹) = f x)
    (h12 : ∀ c, f (rootElt K a .i12 c) = 1) : ∀ x ∈ R1 K a, f x = 1 := by
  have gen : ∀ {k : Idx}, k.isR1 = true → ∀ c, f (rootElt K a k c) = 1 := by
    intro k hk
    have hks := Idx.isSz_eq_false_of_isR1 k hk
    by_cases h12' : k = .i12
    · subst h12'
      exact h12
    · refine rootElt_eq_one_of_torusHi_invariant (i := .i5) ha hK rfl
        (by revert hk h12'; cases k <;> decide)
        (fun c d => by rw [rootElt_add hK hks, hf _ (rootElt_mem_R1 hk c) _ (rootElt_mem_R1 hk d)])
        fun t ht c => by rw [← torusPair_conj_rootElt hK, hinv t ht _ (rootElt_mem_R1 hk c)]
  have f1 : f 1 = 1 := by
    have e := hf 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at e
    exact left_eq_mul.1 e
  intro x hx
  rw [R1_eq_closure] at hx
  induction hx using closure_induction with
  | mem y hy =>
    simp only [Set.mem_iUnion, Set.mem_range] at hy
    obtain ⟨k, hk, c, rfl⟩ := hy
    exact gen (by revert hk; decide +revert) c
  | one => exact f1
  | mul y z hy hz ihy ihz =>
    rw [← R1_eq_closure] at hy hz
    rw [hf y hy z hz, ihy, ihz, mul_one]
  | inv y hy ihy =>
    rw [← R1_eq_closure] at hy
    have e := hf y⁻¹ (inv_mem hy) y hy
    rw [inv_mul_cancel, f1, ihy, mul_one] at e
    exact e.symm

end CFSG.LocalAnalysis.EvenBN.TwoF4

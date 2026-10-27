module

public import CFSG.GF2Type.SmithTypeE.DMod.CliffordEx
public import CFSG.GF2Type.SmithTypeE.DMod.Planes
public import CFSG.Certificates.Kernel.SmithD6GramSound
import CFSG.Certificates.Kernel.SmithD6WtSound

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.DMod

open CFSG.SmithD6 CFSG.KD.SmithD6 Module

theorem getElem!_eq_getD_toList (B : Array ℕ) (m : ℕ) : B[m]! = B.toList.getD m 0 := by
  rcases B with ⟨l⟩
  simp [List.getD_eq_getElem?_getD]

theorem exC_lt_two_pow (s : ℕ) : exC s < 2 ^ 64 := by
  apply Nat.lt_pow_two_of_testBit
  intro T hT
  rw [testBit_exC]
  apply decide_eq_false
  rintro ⟨c, hc, -⟩
  have := (evF c).isLt
  omega

theorem decode64_ne_zero {s : ℕ} (hs : s < 2 ^ 64) (h0 : 0 < s) : decode64 s ≠ 0 := by
  intro h
  apply Nat.pos_iff_ne_zero.1 h0
  apply Nat.eq_of_testBit_eq
  intro T
  rw [Nat.zero_testBit]
  by_cases hT : T < 64
  · have h1 := congrFun h ⟨T, hT⟩
    cases hb : s.testBit T
    · rfl
    · simp [decode64_apply, bit, hb] at h1
  · exact Nat.testBit_lt_two_pow
      (lt_of_lt_of_le hs (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem testBit_xorComb_piv {B : Array ℕ} {p : ℕ → ℕ}
    (hp : ∀ j < 6, ∀ k < 6, B[k]!.testBit (p j) = (k == j)) (d : ℕ) {j : ℕ} (hj : j < 6) :
    (xorComb B d).testBit (p j) = d.testBit j := by
  have key : ∀ n ≤ 6, ((List.range n).foldl
      (fun acc m => if d.testBit m then acc ^^^ B[m]! else acc) 0).testBit (p j) =
      (decide (j < n) && d.testBit j) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have h0 := ih (by omega)
      have hb := hp j hj n (by omega)
      split_ifs with hd
      · rw [Nat.testBit_xor, h0, hb]
        rcases lt_trichotomy j n with h | rfl | h
        · simp [h, show j < n + 1 by omega, beq_false_of_ne (show n ≠ j by omega)]
        · simp [hd]
        · simp [show ¬ j < n by omega, show ¬ j < n + 1 by omega,
            beq_false_of_ne (show n ≠ j by omega)]
      · rw [h0]
        rcases lt_trichotomy j n with h | rfl | h
        · simp [h, show j < n + 1 by omega]
        · simp [hd]
        · simp [show ¬ j < n by omega, show ¬ j < n + 1 by omega]
  have := key 6 le_rfl
  unfold xorComb
  simpa [hj] using this

theorem six_le_finrank_planeSpan {B : Array ℕ} {p : ℕ → ℕ} (hB : ∀ m < 6, B[m]! < 4096)
    (hp : ∀ j < 6, ∀ k < 6, B[k]!.testBit (p j) = (k == j)) :
    6 ≤ finrank (ZMod 2) (planeSpan B) := by
  classical
  let f : Fin 64 → planeSpan B := fun d =>
    ⟨dec12 (xorComb B d.val), dec12_xorComb_mem_planeSpan B d.val⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : dec12 (xorComb B a.val) = dec12 (xorComb B b.val) := congrArg Subtype.val hab
    have h2 := eq_of_dec12_eq (xorComb_lt hB _) (xorComb_lt hB _) h1
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < 6
    · rw [← testBit_xorComb_piv hp a.val hj, ← testBit_xorComb_piv hp b.val hj, h2]
    · have h64 : (64 : ℕ) ≤ 2 ^ j := by
        have := Nat.pow_le_pow_right (n := 2) (by norm_num) (by omega : 6 ≤ j)
        simpa using this
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le a.isLt h64),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le b.isLt h64)]
  have hcard := Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card] at hcard
  have h6 : 2 ^ 6 ≤ 2 ^ finrank (ZMod 2) (planeSpan B) := by simpa using hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h6

theorem planeSpan_eq_annSub_of_planeL {s : ℕ} {B P : Array ℕ} (hs : s < 2 ^ 64)
    (h : planeL s B.toList P.toList = true) : planeSpan B = annSub (decode64 s) := by
  obtain ⟨hpos, hlB, -, hann, hpiv⟩ := planeL_sound h
  have hmem : ∀ m < 6, B[m]! ∈ B.toList := fun m hm => by
    rw [getElem!_eq_getD_toList, List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  have hB : ∀ m < 6, B[m]! < 4096 := fun m hm => (hann _ (hmem m hm)).1
  have hp : ∀ j < 6, ∀ k < 6, B[k]!.testBit (P.toList.getD j 0) = (k == j) := fun j hj k hk => by
    rw [getElem!_eq_getD_toList]
    exact hpiv j hj k hk
  have hle : planeSpan B ≤ annSub (decode64 s) := by
    unfold planeSpan
    rw [Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    change rhoL (dec12 B[m.val]!) (decode64 s) = 0
    rw [← decode64_rhoC, (hann _ (hmem m.val m.isLt)).2, decode64_zero]
  exact eq_annSub_of_le (decode64_ne_zero hs hpos) hle (six_le_finrank_planeSpan hB hp)

theorem evF_31 : (evF 31).val = 63 := by decide

theorem testBit_flipS_63 : ∀ i0 i : Fin 6, (flipS i0 63).val.testBit i.val = decide (i ≠ i0) := by
  decide

theorem disjoint_annSub_of_testBit {s : ℕ} (h : s.testBit 31 = true) :
    Disjoint (planeSpan fBasis) (annSub (exL (decode32 s))) := by
  rw [Submodule.disjoint_def]
  intro x hxF hxA
  have hx1 : x.1 = 0 := mem_planeSpan_fBasis_iff.1 hxF
  by_contra hne
  obtain ⟨i0, hi0⟩ : ∃ i, x.2 i ≠ 0 := by
    by_contra hall
    exact hne (Prod.ext hx1 (funext fun i => by_contra fun hi => hall ⟨i, hi⟩))
  have hi1 : x.2 i0 = 1 := by
    revert hi0
    generalize x.2 i0 = c
    revert c
    decide
  have h63 : exL (decode32 s) 63 = 1 := by
    have e : (63 : Fin 64) = evF 31 := Fin.ext evF_31.symm
    rw [e, exL_apply_evF, decode32_apply_bit]
    change bit (s.testBit 31) = 1
    rw [h]
    rfl
  have hrho := congrFun (mem_annSub.1 hxA) (flipS i0 63)
  simp only [rhoL_apply, hx1, Pi.zero_apply, zero_smul, Finset.sum_const_zero, zero_add,
    LinearMap.add_apply, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply,
    Pi.add_apply, Pi.smul_apply,
    contrL_apply] at hrho
  rw [Finset.sum_eq_single i0] at hrho
  · rw [testBit_flipS_63 i0 i0, flipS_flipS, hi1, h63] at hrho
    simp at hrho
  · intro i _ hi
    rw [testBit_flipS_63 i0 i, decide_eq_true hi]
    simp
  · simp

theorem not_disjoint_of_fComb {B : Array ℕ} (hB : B.size = 6) (h : FComb B.toList) :
    ¬ Disjoint (planeSpan fBasis) (planeSpan B) := by
  rcases B with ⟨bs⟩
  have hlen : bs.length = 6 := hB
  change FComb bs at h
  unfold FComb at h
  obtain ⟨x, h1, h2, h3, hx⟩ := h
  have hxW : dec12 x ∈ planeSpan ⟨bs⟩ := by
    refine hx (fun y => dec12 y ∈ planeSpan ⟨bs⟩) (by rw [dec12_zero]; exact zero_mem _) ?_
    intro y hy b hb
    rw [dec12_xor]
    refine add_mem hy ?_
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hb
    have e : (⟨bs⟩ : Array ℕ)[m]! = bs[m] := by
      rw [getElem!_eq_getD_toList, List.getD_eq_getElem _ _ hm]
    rw [← e]
    exact Submodule.subset_span ⟨⟨m, by omega⟩, rfl⟩
  have hxF : dec12 x ∈ planeSpan fBasis := by
    rw [mem_planeSpan_fBasis_iff, fst_dec12_eq_zero_iff]
    intro i hi
    have h4 := testBit_and_63 x i
    rw [h3, Nat.zero_testBit, decide_eq_true hi, Bool.true_and] at h4
    exact h4.symm
  intro hd
  have h0 := Submodule.disjoint_def.1 hd _ hxF hxW
  have := eq_of_dec12_eq h2 (by norm_num : (0 : ℕ) < 4096) (by rw [h0, dec12_zero])
  omega

theorem fB_one_left (v : ℕ) : fB 1 v = v.testBit 31 := by
  have key : ∀ n, 1 ≤ n → n ≤ 32 →
      (List.range n).foldl (fun b t => b ^^ ((1 : ℕ).testBit t && v.testBit (31 - t))) false =
        v.testBit 31 := by
    intro n h1 h2
    induction n with
    | zero => omega
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [ih hn (by omega)]
        have : (1 : ℕ).testBit n = false :=
          Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (by omega))
        simp [this]
  exact key 32 (by norm_num) le_rfl

end CFSG.GF2Type.SmithTypeE.DMod

end

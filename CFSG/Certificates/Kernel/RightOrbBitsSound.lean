module

public import Certificates.Data.Kernel.RightOrbBits
public import CFSG.Certificates.Kernel.ConjOrbSound
import CFSG.Certificates.Kernel.Spor.PackWord
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.KC.RightOrbBits

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.RankThree.Native CFSG.Monster.B.Fischer CFSG.KC.Bfs CFSG.KC.BfsPin CFSG.KC.ConjOrb
open CFSG.KLie.CT (fget)

@[expose] def decB (n c : Nat) : Array Nat := Array.ofFn (n := n) fun j => cond (Nat.testBit c j.1) 1 0

theorem bitK_eq (c j : Nat) : bitK c j = cond (Nat.testBit c j) 1 0 := by
  unfold bitK
  change (c >>> j) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (c / 2 ^ j) with h | h <;> simp [h]

theorem testBit_imgK (n w g c : Nat) : ∀ m j, Nat.testBit (Nat.rec (motive := fun _ => Nat) 0
    (fun j acc => Nat.lor acc (Nat.shiftLeft (bitK c (pg w (mask w) g j)) j)) m) j =
      (decide (j < m) && Nat.testBit c (pg w (mask w) g j))
  | 0, j => by simp
  | m + 1, j => by
    change Nat.testBit (_ ||| (bitK c (pg w (mask w) g m) <<< m)) j = _
    rw [Nat.testBit_or, testBit_imgK n w g c m j, bitK_eq, Nat.testBit_shiftLeft]
    by_cases hj : j < m
    · have h1 : ¬ m ≤ j := by omega
      simp [hj, h1, show j < m + 1 by omega]
    · by_cases hjm : j = m
      · subst hjm
        cases Nat.testBit c (pg w (mask w) g j) <;> simp
      · have h1 : ¬ j < m + 1 := by omega
        have h2 : m ≤ j := by omega
        have h3 : 0 < j - m := by omega
        simp only [hj, decide_false, Bool.false_and, Bool.false_or, h1, h2, decide_true,
          Bool.true_and]
        have h4 : Nat.testBit 1 (j - m) = false :=
          Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (by omega))
        cases Nat.testBit c (pg w (mask w) g m) <;> simp [h4]

theorem testBit_imgK' (n w g c j : Nat) :
    Nat.testBit (imgK n w g c) j = (decide (j < n) && Nat.testBit c (pg w (mask w) g j)) :=
  testBit_imgK n w g c n j

theorem testBit_ge {n c q : Nat} (hc : c < 2 ^ n) (hq : n ≤ q) : Nat.testBit c q = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) hq))

theorem decB_get {n c : Nat} (hc : c < 2 ^ n) (q : Nat) :
    (decB n c)[q]! = cond (Nat.testBit c q) 1 0 := by
  by_cases hq : q < n
  · unfold decB
    rw [getElem!_pos _ q (by simpa using hq), Array.getElem_ofFn]
  · unfold decB
    rw [getElem!_neg _ q (by simpa using hq), testBit_ge hc (by omega)]
    rfl

theorem decB_size (n c : Nat) : (decB n c).size = n := by simp [decB]

theorem comp_decB {n w g c : Nat} (hc : c < 2 ^ n) :
    compA n (decB n c) (unpack n w g) = decB n (imgK n w g c) := by
  apply Array.ext (by simp [compA, decB])
  intro i h1 h2
  have hi : i < n := by simpa [compA] using h1
  simp only [compA, decB, Array.getElem_ofFn]
  rw [← decB, decB_get hc, unpack_get' hi, testBit_imgK']
  simp [hi]

theorem decB_inj {n c₁ c₂ : Nat} (h₁ : c₁ < 2 ^ n) (h₂ : c₂ < 2 ^ n) (h : decB n c₁ = decB n c₂) :
    c₁ = c₂ := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · have e : (decB n c₁)[i]! = (decB n c₂)[i]! := by rw [h]
    rw [decB_get h₁, decB_get h₂] at e
    cases h1 : Nat.testBit c₁ i <;> cases h2 : Nat.testBit c₂ i <;> simp_all
  · rw [testBit_ge h₁ (by omega), testBit_ge h₂ (by omega)]

theorem keyA_decB_inj {n c₁ c₂ : Nat} (hn : 1 < n) (h₁ : c₁ < 2 ^ n) (h₂ : c₂ < 2 ^ n)
    (h : keyA n (List.range n) (decB n c₁) = keyA n (List.range n) (decB n c₂)) :
    decB n c₁ = decB n c₂ := by
  unfold keyA at h
  have hd : ∀ c, c < 2 ^ n → ∀ l ∈ (List.range n).map fun p => (decB n c)[p]!, l < n := by
    intro c hc l hl
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hl
    rw [decB_get hc]
    cases Nat.testBit c p <;> simp <;> omega
  have e := Nat.ofDigits_inj_of_len_eq hn (by simp) (hd c₁ h₁) (hd c₂ h₂) h
  apply Array.ext (by simp [decB_size])
  intro i hi _
  have hin : i < n := by simpa [decB_size] using hi
  have ei := congrArg (fun L => L.getD i 0) e
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hin,
    Option.map_some, Option.getD_some] at ei
  rw [← getElem!_pos (decB n c₁) i hi, ← getElem!_pos (decB n c₂) i (by simpa [decB_size] using hin)]
  exact ei

theorem closPtB_spec {n w ng N : Nat} {G T E : Nat → Nat} {i : Nat}
    (h : closPtB n w ng N G T E i = true) :
    T i < 2 ^ n ∧ ∀ k < ng, fget (E i) k 20 < N ∧ imgK n w (G k) (T i) = T (fget (E i) k 20) := by
  unfold closPtB at h
  rw [ConjOrb.strictB_eq, ConjOrb.strictB_eq, bAnd_iff] at h
  refine ⟨?_, fun k hk => ?_⟩
  · have := Nat.blt_eq.mp h.1
    have e : Nat.shiftLeft 1 n = 2 ^ n := by
      change 1 <<< n = 2 ^ n
      rw [Nat.shiftLeft_eq, Nat.one_mul]
    rwa [e] at this
  · have h2 := allN_spec h.2 k hk
    rw [ConjOrb.strictB_eq, bAnd_iff] at h2
    exact ⟨Nat.blt_eq.mp h2.1, Nat.eq_of_beq_eq_true h2.2⟩

theorem arrBfs_of_bits {n w ng ngc N r fuel : Nat} {G T E D S : Nat → Nat}
    {act : Nat → Array Nat → Array Nat} {valid : Array Nat → Bool} {root : Array Nat}
    (hn : 1 < n) (hng : ng ≤ ngc) (hact : ∀ k < ng, ∀ a, act k a = compA n a (unpack n w (G k)))
    (hcl : ∀ i < N, closPtB n w ngc N G T E i = true)
    (htr : ∀ i < N, treePt ng N r E D i = true) (hr : r < N)
    (hroot : root = decB n (T r)) (hv : ∀ i < N, valid (decB n (T i)) = true)
    (hK : distinctK N T S = true) (hf : N ≤ fuel) :
    arrCertOK act ng valid (keyA n (List.range n)) root
        (arrBfs act ng (keyA n (List.range n)) root fuel) = true ∧
      (∀ x, x ∈ (arrBfs act ng (keyA n (List.range n)) root fuel).pts ↔
        ∃ i < N, decB n (T i) = x) ∧
      (arrBfs act ng (keyA n (List.range n)) root fuel).pts.size = N := by
  classical
  have hcl1 : ∀ i < N, T i < 2 ^ n ∧ ∀ k < ng,
      fget (E i) k 20 < N ∧ imgK n w (G k) (T i) = T (fget (E i) k 20) :=
    fun i hi => ⟨(closPtB_spec (hcl i hi)).1, fun k hk => (closPtB_spec (hcl i hi)).2 k (by omega)⟩
  have hstep : ∀ i < N, ∀ k < ng, act k (decB n (T i)) = decB n (T (fget (E i) k 20)) := by
    intro i hi k hk
    obtain ⟨hc, hcl'⟩ := hcl1 i hi
    rw [hact k hk, comp_decB hc, (hcl' k hk).2]
  let U : Nat → Array Nat := fun i => decB n (T i)
  let Sf : Finset (Array Nat) := (Finset.range N).image U
  have hmemS : ∀ x, x ∈ Sf ↔ ∃ i < N, decB n (T i) = x := by
    intro x
    simp only [Sf, U, Finset.mem_image, Finset.mem_range]
  have hrootS : root ∈ Sf := (hmemS _).2 ⟨r, hr, hroot.symm⟩
  have hclosed : ∀ x ∈ Sf, ∀ k < ng, act k x ∈ Sf := by
    intro x hx k hk
    obtain ⟨i, hi, rfl⟩ := (hmemS x).1 hx
    rw [hstep i hi k hk]
    exact (hmemS _).2 ⟨_, ((hcl1 i hi).2 k hk).1, rfl⟩
  have hreach : ∀ d, ∀ i < N, tDep (D i) = d → Reach act ng root (decB n (T i)) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro i hi hd
      by_cases hir : i = r
      · rw [hir, ← hroot]
        exact Reach.root
      · obtain ⟨hp, hl, he, hdep⟩ := treePt_spec (htr i hi) hir
        have hpr := ih _ (by omega) _ hp rfl
        have e := hstep _ hp _ hl
        rw [he] at e
        rw [← e]
        exact Reach.step _ hl hpr
  have hR : ∀ x ∈ Sf, Reach act ng root x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := (hmemS x).1 hx
    exact hreach _ i hi rfl
  have hS : ∀ x, Reach act ng root x ↔ x ∈ Sf := reach_iff_of_closed hrootS hclosed hR
  have hvS : ∀ x ∈ Sf, valid x = true := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := (hmemS x).1 hx
    exact hv i hi
  have hkeyS : ∀ x ∈ Sf, ∀ y ∈ Sf, keyA n (List.range n) x = keyA n (List.range n) y → x = y := by
    intro x hx y hy e
    obtain ⟨i, hi, rfl⟩ := (hmemS x).1 hx
    obtain ⟨j, hj, rfl⟩ := (hmemS y).1 hy
    exact keyA_decB_inj hn (hcl1 i hi).1 (hcl1 j hj).1 e
  have hinj : ∀ i < N, ∀ j < N, decB n (T i) = decB n (T j) → i = j := by
    intro i hi j hj e
    exact distinctK_inj hK i hi j hj (decB_inj (hcl1 i hi).1 (hcl1 j hj).1 e)
  have hcard : Sf.card = N := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj e
    exact hinj i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) e
  obtain ⟨hcert, hmem, hsize, -⟩ := arrBfs_spec (act := act) (ngen := ng) (valid := valid)
    (key := keyA n (List.range n)) (root := root) (fuel := fuel) Sf hS hvS hkeyS
    (by rw [hcard]; exact hf)
  exact ⟨hcert, fun x => (hmem x).trans (hmemS x), hsize.trans hcard⟩

end CFSG.KC.RightOrbBits

end

module

public import CFSG.Monster.B.Co2.PermArr
public import Certificates.Data.CFSGNative.Schreier.Check
import Mathlib.Tactic.Group

public section

namespace CFSG.KC.Misc.ConjTree

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

section Words

variable {G : Type*} [Group G]

@[expose] def wv (g : ℕ → G) : List ℤ → G
  | [] => 1
  | l :: w => (if 0 < l then g (l.toNat - 1) else (g ((-l).toNat - 1))⁻¹) * wv g w

theorem wv_nil (g : ℕ → G) : wv g [] = 1 := rfl

theorem wv_cons (g : ℕ → G) (l : ℤ) (w : List ℤ) :
    wv g (l :: w) = (if 0 < l then g (l.toNat - 1) else (g ((-l).toNat - 1))⁻¹) * wv g w := rfl

theorem wv_append (g : ℕ → G) : ∀ a b : List ℤ, wv g (a ++ b) = wv g a * wv g b
  | [], b => by rw [List.nil_append, wv_nil, one_mul]
  | l :: a, b => by rw [List.cons_append, wv_cons, wv_cons, wv_append g a b, mul_assoc]

theorem wv_revneg (g : ℕ → G) : ∀ w : List ℤ, (∀ z ∈ w, z ≠ 0) →
    wv g (w.reverse.map fun l => -l) = (wv g w)⁻¹
  | [], _ => by simp [wv_nil]
  | l :: w, hw => by
    have hl : l ≠ 0 := hw l (by simp)
    rw [List.reverse_cons, List.map_append, wv_append, wv_revneg g w fun z hz =>
      hw z (List.mem_cons_of_mem l hz), wv_cons, List.map_cons, List.map_nil, wv_cons, wv_nil,
      mul_one, mul_inv_rev]
    by_cases h : 0 < l
    · have h' : ¬ 0 < -l := by omega
      rw [if_neg h', if_pos h, neg_neg]
    · have h' : 0 < -l := by omega
      rw [if_pos h', if_neg h, inv_inv]

theorem wv_conj (g : ℕ → G) (u : G) : ∀ w : List ℤ,
    u * wv g w * u⁻¹ = wv (fun h => u * g h * u⁻¹) w
  | [] => by rw [wv_nil, wv_nil, mul_one, mul_inv_cancel]
  | l :: w => by
    rw [wv_cons, wv_cons, ← wv_conj g u w]
    split_ifs <;> group

theorem wv_congr {f g : ℕ → G} {j : ℕ} (h : ∀ i < j, f i = g i) :
    ∀ w : List ℤ, lettersOK j w = true → wv f w = wv g w
  | [], _ => rfl
  | l :: w, hw => by
    simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hlj⟩, hw⟩ := hw
    have hw' : lettersOK j w = true := by simpa [lettersOK, List.all_eq_true] using hw
    rw [wv_cons, wv_cons, wv_congr h w hw']
    by_cases hp : 0 < l
    · rw [if_pos hp, if_pos hp, h _ (by omega)]
    · rw [if_neg hp, if_neg hp, h _ (by omega)]

end Words

theorem rep_wordA_wv {n j : ℕ} {S SI : Array (Array ℕ)} {g : ℕ → Equiv.Perm (Fin n)}
    (hS : ∀ h < j, Rep n S[h]! (g h)) (hSI : ∀ h < j, Rep n SI[h]! (g h)⁻¹) :
    ∀ w : List ℤ, lettersOK j w = true → Rep n (wordA n S SI w) (wv g w)
  | [], _ => by simpa [wordA, wv_nil] using (rep_idA (n := n))
  | l :: w, hw => by
    have hw0 := hw
    simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw0
    obtain ⟨⟨hl0, hlj⟩, hw0⟩ := hw0
    have hw' : lettersOK j w = true := by simpa [lettersOK, List.all_eq_true] using hw0
    rw [wordA, wv_cons]
    refine rep_compA ?_ (rep_wordA_wv hS hSI w hw')
    unfold letterA
    by_cases hp : 0 < l
    · rw [if_pos hp, if_pos hp]
      exact hS _ (by omega)
    · rw [if_neg hp, if_neg hp]
      exact hSI _ (by omega)

section Tree

variable {G : Type*} [Group G]

theorem conj_parent {N m d : ℕ} {k l : ℕ → G} {P : List (List ℤ)} {par : ℕ → ℕ}
    {T : ℕ → ℕ → ℕ} (hP0 : P.getD 0 [] = [])
    (hstep : ∀ i, 1 ≤ i → i < N → par i < N ∧ ∃ c < d,
      P.getD i [] = P.getD (par i) [] ++ [((c + 1 : ℕ) : ℤ)] ∧ T (par i) c = i)
    (hid : ∀ j < m, l 0 * k j * (l 0)⁻¹ = k j)
    (htr : ∀ i < N, ∀ c < d, ∀ j < m,
      l (T i c) * k j * (l (T i c))⁻¹ = l i * (l (c + 1) * k j * (l (c + 1))⁻¹) * (l i)⁻¹)
    (hnorm : ∀ c < d, ∀ j < m, ∃ W : List ℤ, lettersOK m W = true ∧
      l (c + 1) * k j * (l (c + 1))⁻¹ = wv k W) :
    ∀ i < N, (∀ z ∈ P.getD i [], 1 ≤ z ∧ z ≤ d) ∧ ∀ j < m,
      wv (fun h => l (h + 1)) (P.getD i []) * k j * (wv (fun h => l (h + 1)) (P.getD i []))⁻¹ =
        l i * k j * (l i)⁻¹ := by
  have key : ∀ s, ∀ i < N, (P.getD i []).length = s → (∀ z ∈ P.getD i [], 1 ≤ z ∧ z ≤ d) ∧
      ∀ j < m, wv (fun h => l (h + 1)) (P.getD i []) * k j *
        (wv (fun h => l (h + 1)) (P.getD i []))⁻¹ = l i * k j * (l i)⁻¹ := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro i hi hs
      by_cases i0 : i = 0
      · subst i0
        rw [hP0]
        refine ⟨fun z hz => by simp at hz, fun j hj => ?_⟩
        rw [wv_nil, one_mul, inv_one, mul_one, hid j hj]
      · obtain ⟨hp, c, hc, hPi, hT⟩ := hstep i (by omega) hi
        have hlen : (P.getD (par i) []).length < s := by
          rw [← hs, hPi, List.length_append, List.length_singleton]
          omega
        obtain ⟨ihz, ihc⟩ := ih _ hlen (par i) hp rfl
        rw [hPi]
        refine ⟨fun z hz => ?_, fun j hj => ?_⟩
        · rcases List.mem_append.1 hz with hz | hz
          · exact ihz z hz
          · rw [List.mem_singleton] at hz
            subst hz
            omega
        · have e1 : wv (fun h => l (h + 1)) [((c + 1 : ℕ) : ℤ)] = l (c + 1) := by
            rw [wv_cons, wv_nil, mul_one, if_pos (by omega)]
            beta_reduce
            congr 1
          obtain ⟨W, hW, hWe⟩ := hnorm c hc j hj
          have e2 : wv (fun h => l (h + 1)) (P.getD (par i) []) * wv k W *
              (wv (fun h => l (h + 1)) (P.getD (par i) []))⁻¹ =
              l (par i) * wv k W * (l (par i))⁻¹ := by
            rw [wv_conj, wv_conj]
            exact wv_congr (fun h hh => ihc h hh) W hW
          have e3 : l i * k j * (l i)⁻¹ =
              l (par i) * (l (c + 1) * k j * (l (c + 1))⁻¹) * (l (par i))⁻¹ := by
            rw [← htr (par i) hp c hc j hj, hT]
          rw [wv_append, e1, e3, hWe, ← e2, ← hWe]
          group
  exact fun i hi => key _ i hi rfl

end Tree

theorem rawChainOK_congrW {n : ℕ} {O S : Array (Array ℕ)} {base : Array ℕ}
    {W W' : Array (List ℤ)} {chunks : ℕ} (hs : W.size = W'.size)
    (he : ∀ j, O.size ≤ j → j < S.size → W[j]! = W'[j]!) :
    rawChainOK n O S base W chunks = rawChainOK n O S base W' chunks := by
  have h : ∀ j < S.size, (decide (j < O.size) || (lettersOK j W[j]! &&
      eqA n S[j]! (wordA n S (rawInvs n S) W[j]!))) = (decide (j < O.size) ||
      (lettersOK j W'[j]! && eqA n S[j]! (wordA n S (rawInvs n S) W'[j]!))) := by
    intro j hj
    by_cases hj' : j < O.size
    · simp [hj']
    · rw [he j (by omega) hj]
  have hc : allLt S.size (fun j => decide (j < O.size) || (lettersOK j W[j]! &&
      eqA n S[j]! (wordA n S (rawInvs n S) W[j]!))) = allLt S.size (fun j => decide (j < O.size) ||
      (lettersOK j W'[j]! && eqA n S[j]! (wordA n S (rawInvs n S) W'[j]!))) := by
    rw [Bool.eq_iff_iff, allLt_iff, allLt_iff]
    exact ⟨fun H j hj => (h j hj) ▸ H j hj, fun H j hj => (h j hj).symm ▸ H j hj⟩
  simp only [rawChainOK]
  rw [hs, hc]

end CFSG.KC.Misc.ConjTree

end

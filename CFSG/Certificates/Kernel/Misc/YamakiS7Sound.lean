module

public import Certificates.Data.Kernel.Misc.YamakiS7
public import CFSG.Certificates.Kernel.LocalQTPermSound
public import Certificates.Data.YamakiS7

public section

namespace CFSG.KC.YamakiS7

open Equiv CFSG.KD.YamakiS7 CFSG.KC.LQT.P CFSG.KC.Ord
  CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki CFSG.ClassicalInvolution.Q3.AE

theorem one_eq : ONE = code (1 : Perm (Fin 7)) := by
  rw [← code_one]
  rfl

theorem code_mu : code s7Mu = 1145148608 := by decide

theorem code_mu' : code s7Mu' = 1244793024 := by decide

theorem code_tau : code s7Tau = 5574329408 := by decide

theorem code_xi : code s7Xi = 5509254208 := by decide

theorem code_c1 : code s7c1 = 3427928096 := by decide

theorem code_c1_inv : code s7c1⁻¹ = 5506271264 := by decide

theorem code_c2 : code s7c2 = 3426912288 := by decide

theorem code_c2_inv : code s7c2⁻¹ = 5473765408 := by decide

theorem tri_sound : ∀ x y z : Fin 7,
    isLine (Nat.lor (Nat.lor (Nat.shiftLeft 1 x) (Nat.shiftLeft 1 y)) (Nat.shiftLeft 1 z)) = true →
      ({x, y, z} : Finset (Fin 7)) ∈ fanoLines := by
  decide

theorem triK_code (τ : Perm (Fin 7)) (a b c : Fin 7) :
    triK (code τ) a b c = Nat.lor (Nat.lor (Nat.shiftLeft 1 (τ a : ℕ)) (Nat.shiftLeft 1 (τ b : ℕ)))
      (Nat.shiftLeft 1 (τ c : ℕ)) := by
  rw [triK, img_code (by norm_num), img_code (by norm_num), img_code (by norm_num)]

theorem line_of (τ : Perm (Fin 7)) (a b c : Fin 7) (h : isLine (triK (code τ) a b c) = true) :
    ({a, b, c} : Finset (Fin 7)).map τ.toEmbedding ∈ fanoLines := by
  rw [triK_code] at h
  simpa [Finset.map_insert, Finset.map_singleton] using tri_sound _ _ _ h

theorem lines_of (τ : Perm (Fin 7)) (h : linesK (code τ) = true) :
    ∀ s ∈ fanoLines, s.map τ.toEmbedding ∈ fanoLines := by
  simp only [linesK, andB_iff] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  intro s hs
  simp only [fanoLines, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact line_of τ 0 1 3 h1
  · exact line_of τ 1 2 4 h2
  · exact line_of τ 2 3 5 h3
  · exact line_of τ 3 4 6 h4
  · exact line_of τ 4 5 0 h5
  · exact line_of τ 5 6 1 h6
  · exact line_of τ 6 0 2 h7

theorem inL32_of_l32K (τ : Perm (Fin 7)) (h : l32K (code τ) = true) : InL32 τ := by
  rw [l32K, andB_iff, code_inv (by norm_num)] at h
  exact fun s hs => ⟨lines_of τ h.1 s hs, lines_of τ⁻¹ h.2 s hs⟩

theorem letterK_code (σ : Perm (Fin 7)) (a : Fin 5) :
    letterK (code σ) a = code (s7Letters σ a) := by
  fin_cases a
  · change 1145148608 = code s7Mu
    rw [code_mu]
  · change 1244793024 = code s7Mu'
    rw [code_mu']
  · change 5574329408 = code s7Tau
    rw [code_tau]
  · change 5509254208 = code s7Xi
    rw [code_xi]
  · rfl

theorem evalK_code (σ : Perm (Fin 7)) :
    ∀ w : List (Fin 5), evalK (code σ) (w.map Fin.val) = code (evalWord (s7Letters σ) w)
  | [] => one_eq
  | a :: w => by
    change mul 7 (letterK (code σ) a) (evalK (code σ) (w.map Fin.val)) = _
    rw [letterK_code, evalK_code σ w, code_mul (by norm_num)]
    rfl

theorem isOrd5_of_ord5K (y : Perm (Fin 7)) (h : ord5K (code y) = true) : IsOrd5 y := by
  rw [ord5K, letB_eq, letB_eq, code_mul (by norm_num), code_mul (by norm_num),
    code_mul (by norm_num), one_eq, andB_iff, notB_iff, beq_code (by norm_num),
    beq_code (by norm_num)] at h
  have e : y ^ 5 = y * y * (y * y) * y := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  exact ⟨e.trans h.1, h.2⟩

theorem wordsK_iff (s : ℕ) :
    ∀ W : List (List ℕ), wordsK s W = true ↔ ∃ w ∈ W, ord5K (evalK s w) = true
  | [] => by simp [wordsK]
  | w :: W => by
    change orB (letB (evalK s w) ord5K) (wordsK s W) = true ↔ _
    rw [orB_iff, letB_eq, wordsK_iff s W]
    simp

theorem mem_wordsOfLength : ∀ (k : ℕ) (v : List (Fin 5)), v.length = k → v ∈ wordsOfLength k
  | 0, v, h => by simp [List.length_eq_zero_iff.mp h, wordsOfLength]
  | k + 1, v, h => by
    obtain ⟨u, a, rfl⟩ : ∃ u a, v = u ++ [a] := by
      rcases List.eq_nil_or_concat v with h0 | ⟨u, a, e⟩
      · simp [h0] at h
      · exact ⟨u, a, by rw [e, List.concat_eq_append]⟩
    have hu : u.length = k := by simpa using h
    simp only [wordsOfLength, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
    exact ⟨u, mem_wordsOfLength k u hu, a, rfl⟩

theorem mem_s7Words (v : List (Fin 5)) (h : v.length ≤ 5) : v ∈ s7Words () := by
  simp only [s7Words, List.mem_flatMap, List.mem_range]
  exact ⟨v.length, by omega, mem_wordsOfLength _ v rfl⟩

theorem s7KWords_ok : ∀ w ∈ s7KWords, (∀ a ∈ w, a < 5) ∧ w.length ≤ 5 := by
  decide

def toF5 (a : ℕ) : Fin 5 := ⟨a % 5, Nat.mod_lt _ (by norm_num)⟩

theorem lift_word {w : List ℕ} (h : ∀ a ∈ w, a < 5) : (w.map toF5).map Fin.val = w := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id w]
  refine List.map_congr_left fun a ha => ?_
  simp [toF5, Nat.mod_eq_of_lt (h a ha)]

theorem s7Ok_of_s7F (σ : Perm (Fin 7)) (h : s7F (code σ) = true) :
    s7Ok (s7Words ()) σ = true := by
  rw [s7F, s7FW, ← code_c1, ← code_c1_inv, ← code_c2, ← code_c2_inv, code_mul (by norm_num),
    code_mul (by norm_num), code_mul (by norm_num), code_mul (by norm_num), orB_iff, orB_iff,
    orB_iff, wordsK_iff] at h
  simp only [s7Ok, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true]
  rcases h with h0 | h1 | h2 | ⟨w, hw, h3⟩
  · refine Or.inl (Or.inl (Or.inl (Fin.ext ?_)))
    exact (img_code (by norm_num) σ 0).symm.trans (beq_iff.mp h0)
  · exact Or.inl (Or.inl (Or.inr (inL32_of_l32K _ h1)))
  · exact Or.inl (Or.inr (inL32_of_l32K _ h2))
  · right
    obtain ⟨hlt, hlen⟩ := s7KWords_ok w hw
    refine ⟨w.map toF5, mem_s7Words _ (by simpa using hlen), ?_⟩
    rw [← lift_word hlt, evalK_code] at h3
    exact isOrd5_of_ord5K _ h3

theorem s7Check_of_s7K (h : s7K = true) : s7Check () = true := by
  have hall := (allP_iff (n := 7) s7F).mp h
  simp only [s7Check, s7CheckW, List.all_eq_true]
  exact fun g _ => s7Ok_of_s7F g (hall g)

end CFSG.KC.YamakiS7

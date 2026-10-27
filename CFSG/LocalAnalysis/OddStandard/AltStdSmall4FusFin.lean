module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4FusDefs
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4FusFinData

public section

namespace CFSG.OddStandard.AltStdSmall4.Fus

open Equiv Subgroup FinCode FinData

namespace FinData

private theorem swap_mul_swap_mem {m : ℕ} {a b c d : Fin m} (h1 : a ≠ b) (h2 : c ≠ d) :
    swap a b * swap c d ∈ alternatingGroup (Fin m) := by
  rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap h1, Perm.sign_swap h2]
  rfl

private theorem le9 : (9 : ℕ) ≤ 16 := by norm_num

private theorem le11 : (11 : ℕ) ≤ 16 := by norm_num

private theorem e9_eq : enc (1 : Perm (Fin 9)) = e9 := by decide +kernel

private theorem w9_eq : enc (tr le89 1) = w9 := by decide +kernel

private theorem e11_eq : enc (1 : Perm (Fin 11)) = e11 := by decide +kernel

private theorem w11_eq : enc (tr le811 1) = w11 := by decide +kernel

private theorem bBar_eq : bBar = closure {x | x ∈ gensB} := by
  rw [bBar]
  congr 1
  ext x
  simp [gensB]

private theorem gcB_eq : gensB.map enc = gcB := by decide +kernel

private theorem sq_gensB : ∀ g ∈ gensB, g * g = 1 :=
  sq_eq_one_of_codes le9 gcB_eq e9_eq (by decide +kernel)

private theorem closedB_B : closedB 9 codesB gcB = true := by decide +kernel

private theorem wordsB_eq : wordsB.map (wordCode 9 e9 gcB) = codesB := by decide +kernel

private theorem oneB : e9 ∈ codesB := by decide +kernel

theorem mem_bBar_iff (σ : Perm (Fin 9)) : σ ∈ bBar ↔ enc σ ∈ codesB := by
  rw [bBar_eq]
  exact mem_closure_iff le9 gcB_eq e9_eq sq_gensB closedB_B wordsB_eq oneB σ

private theorem abelB : (codesB.all fun a => codesB.all fun b => cmul 9 a b == cmul 9 b a) =
    true := by
  decide +kernel

private theorem comm_of_mem_bBar {x y : Perm (Fin 9)} (hx : x ∈ bBar) (hy : y ∈ bBar) :
    x * y = y * x := by
  have h := abelB
  simp only [List.all_eq_true, beq_iff_eq] at h
  rw [commute_iff le9]
  exact h _ ((mem_bBar_iff x).1 hx) _ ((mem_bBar_iff y).1 hy)

private theorem rBar9_eq : rBar9 = closure {x | x ∈ gens9} := by
  rw [rBar9]
  congr 1
  ext x
  simp [gens9]

private theorem gc9_eq : gens9.map enc = gc9 := by decide +kernel

private theorem sq_gens9 : ∀ g ∈ gens9, g * g = 1 :=
  sq_eq_one_of_codes le9 gc9_eq e9_eq (by decide +kernel)

private theorem closed9 : closedB 9 codes9 gc9 = true := by decide +kernel

private theorem words9_eq : words9.map (wordCode 9 e9 gc9) = codes9 := by decide +kernel

private theorem one9 : e9 ∈ codes9 := by decide +kernel

private theorem nodup9 : nodupB codes9 = true := by decide +kernel

theorem mem_rBar9_iff (σ : Perm (Fin 9)) : σ ∈ rBar9 ↔ enc σ ∈ codes9 := by
  rw [rBar9_eq]
  exact mem_closure_iff le9 gc9_eq e9_eq sq_gens9 closed9 words9_eq one9 σ

private theorem card_rBar9 : Nat.card rBar9 = 2 ^ 6 := by
  rw [rBar9_eq, card_closure le9 gc9_eq e9_eq sq_gens9 closed9 words9_eq one9
    (nodup_of_nodupB nodup9)]
  decide +kernel

private theorem rBar9_le : rBar9 ≤ alternatingGroup (Fin 9) := by
  rw [rBar9, closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact swap_mul_swap_mem (by decide) (by decide)
  · exact mul_mem (swap_mul_swap_mem (by decide) (by decide))
      (swap_mul_swap_mem (by decide) (by decide))
  · exact mul_mem (swap_mul_swap_mem (by decide) (by decide))
      (swap_mul_swap_mem (by decide) (by decide))

private theorem tr_codes9 : ∀ v : Fin 8, enc (tr le89 v) ∈ codes9 := by decide +kernel

private theorem tr_mem9 (v : Fin 8) : tr le89 v ∈ rBar9 :=
  (mem_rBar9_iff _).2 (tr_codes9 v)

private theorem center9 : centerB 9 e9 w9 codes9 gc9 = true := by decide +kernel

private theorem a4567_mem9 : swap 4 5 * swap 6 7 ∈ rBar9 :=
  (mem_rBar9_iff _).2 (by decide +kernel)

private theorem comm_w9 : (swap 4 5 * swap 6 7 : Perm (Fin 9)) * tr le89 4 *
    (swap 4 5 * swap 6 7)⁻¹ * (tr le89 4)⁻¹ = tr le89 1 := by
  decide +kernel

private theorem inv9_ok : invB 9 e9 w9 codes9 inv9 = true := by decide +kernel

private theorem waC9_eq : wa9.map enc = waC9 := by decide +kernel

private theorem wbC9_eq : wb9.map enc = wbC9 := by decide +kernel

private theorem wa9_mem : ∀ t ∈ wa9, t ∈ alternatingGroup (Fin 9) ∧ t * t = 1 := by
  have hsq := sq_eq_one_of_codes le9 waC9_eq e9_eq (by decide +kernel)
  intro t ht
  refine ⟨?_, hsq t ht⟩
  simp only [wa9, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl <;> exact swap_mul_swap_mem (by decide) (by decide)

private theorem wb9_sq : ∀ g ∈ wb9, g * g = 1 :=
  sq_eq_one_of_codes le9 wbC9_eq e9_eq (by decide +kernel)

private theorem wb9_mem : ∀ g ∈ wb9, g ∈ alternatingGroup (Fin 9) ∧ g * g = 1 := by
  intro g hg
  refine ⟨?_, wb9_sq g hg⟩
  simp only [wb9, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> exact swap_mul_swap_mem (by decide) (by decide)

private theorem cc9_of_check : ∀ X : Subgroup (Perm (Fin 9)), ∀ O : List ℕ,
    (∀ x, x ∈ X ↔ enc x ∈ O) → cc9B O = true → cc9 X := by
  intro X O hXO hO y hyX hyB hy1 hyw
  simp only [cc9B, List.all_eq_true] at hO
  have h := hO (enc y) ((hXO y).1 hyX)
  have h1 : codesB.contains (enc y) = true := by
    rw [List.contains_eq_mem, decide_eq_true_eq]
    exact (mem_bBar_iff y).1 hyB
  have h2 : (enc y == e9) = false := by
    rw [beq_eq_false_iff_ne, ← e9_eq]
    exact fun h => hy1 (enc_injective le9 h)
  have h3 : (enc y == w9) = false := by
    rw [beq_eq_false_iff_ne, ← w9_eq]
    exact fun h => hyw (enc_injective le9 h)
  rw [h1, h2, h3] at h
  rw [card_support_eq le9]
  simpa using h

private theorem fx9 : fxB 9 e9 w9 inv9 waC9 wbC9 cc9B = true := by decide +kernel

private theorem rBarS9_eq : rBarS9 = closure {x | x ∈ gensS9} := by
  rw [rBarS9]
  congr 1
  ext x
  simp [gensS9]

private theorem gcS9_eq : gensS9.map enc = gcS9 := by decide +kernel

private theorem sq_gensS9 : ∀ g ∈ gensS9, g * g = 1 :=
  sq_eq_one_of_codes le9 gcS9_eq e9_eq (by decide +kernel)

private theorem closedS9 : closedB 9 codesS9 gcS9 = true := by decide +kernel

private theorem wordsS9_eq : wordsS9.map (wordCode 9 e9 gcS9) = codesS9 := by decide +kernel

private theorem oneS9 : e9 ∈ codesS9 := by decide +kernel

private theorem nodupS9 : nodupB codesS9 = true := by decide +kernel

theorem mem_rBarS9_iff (σ : Perm (Fin 9)) : σ ∈ rBarS9 ↔ enc σ ∈ codesS9 := by
  rw [rBarS9_eq]
  exact mem_closure_iff le9 gcS9_eq e9_eq sq_gensS9 closedS9 wordsS9_eq oneS9 σ

private theorem card_rBarS9 : Nat.card rBarS9 = 2 ^ 7 := by
  rw [rBarS9_eq, card_closure le9 gcS9_eq e9_eq sq_gensS9 closedS9 wordsS9_eq oneS9
    (nodup_of_nodupB nodupS9)]
  decide +kernel

private theorem tr_codesS9 : ∀ v : Fin 8, enc (tr le89 v) ∈ codesS9 := by decide +kernel

private theorem tr_memS9 (v : Fin 8) : tr le89 v ∈ rBarS9 :=
  (mem_rBarS9_iff _).2 (tr_codesS9 v)

private theorem centerS9 : centerB 9 e9 w9 codesS9 gcS9 = true := by decide +kernel

private theorem a4567_memS9 : swap 4 5 * swap 6 7 ∈ rBarS9 :=
  (mem_rBarS9_iff _).2 (by decide +kernel)

private theorem invS9_ok : invB 9 e9 w9 codesS9 invS9 = true := by decide +kernel

private theorem waCS9_eq : waS9.map enc = waCS9 := by decide +kernel

private theorem waS9_mem : ∀ t ∈ waS9, t ∈ (⊤ : Subgroup (Perm (Fin 9))) ∧ t * t = 1 :=
  fun t ht => ⟨mem_top t, sq_eq_one_of_codes le9 waCS9_eq e9_eq (by decide +kernel) t ht⟩

private theorem wbS9_mem : ∀ g ∈ wb9, g ∈ (⊤ : Subgroup (Perm (Fin 9))) ∧ g * g = 1 :=
  fun g hg => ⟨mem_top g, wb9_sq g hg⟩

private theorem fxS9 : fxB 9 e9 w9 invS9 waCS9 wbC9 (fun _ => false) = true := by decide +kernel

private theorem rBar11_eq : rBar11 = closure {x | x ∈ gens11} := by
  rw [rBar11]
  congr 1
  ext x
  simp [gens11]

private theorem gc11_eq : gens11.map enc = gc11 := by decide +kernel

private theorem sq_gens11 : ∀ g ∈ gens11, g * g = 1 :=
  sq_eq_one_of_codes le11 gc11_eq e11_eq (by decide +kernel)

private theorem closed11 : closedB 11 codes11 gc11 = true := by decide +kernel

private theorem words11_eq : words11.map (wordCode 11 e11 gc11) = codes11 := by decide +kernel

private theorem one11 : e11 ∈ codes11 := by decide +kernel

private theorem nodup11 : nodupB codes11 = true := by decide +kernel

theorem mem_rBar11_iff (σ : Perm (Fin 11)) : σ ∈ rBar11 ↔ enc σ ∈ codes11 := by
  rw [rBar11_eq]
  exact mem_closure_iff le11 gc11_eq e11_eq sq_gens11 closed11 words11_eq one11 σ

private theorem card_rBar11 : Nat.card rBar11 = 2 ^ 7 := by
  rw [rBar11_eq, card_closure le11 gc11_eq e11_eq sq_gens11 closed11 words11_eq one11
    (nodup_of_nodupB nodup11)]
  decide +kernel

private theorem rBar11_le : rBar11 ≤ alternatingGroup (Fin 11) := by
  rw [rBar11, closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact swap_mul_swap_mem (by decide) (by decide)
  · exact swap_mul_swap_mem (by decide) (by decide)
  · exact mul_mem (swap_mul_swap_mem (by decide) (by decide))
      (swap_mul_swap_mem (by decide) (by decide))

private theorem tr_codes11 : ∀ v : Fin 8, enc (tr le811 v) ∈ codes11 := by decide +kernel

private theorem tr_mem11 (v : Fin 8) : tr le811 v ∈ rBar11 :=
  (mem_rBar11_iff _).2 (tr_codes11 v)

private theorem center11 : centerB 11 e11 w11 codes11 gc11 = true := by decide +kernel

private theorem a4567_mem11 : swap 4 5 * swap 6 7 ∈ rBar11 :=
  (mem_rBar11_iff _).2 (by decide +kernel)

private theorem comm_w11 : (swap 4 5 * swap 6 7 : Perm (Fin 11)) * tr le811 4 *
    (swap 4 5 * swap 6 7)⁻¹ * (tr le811 4)⁻¹ = tr le811 1 := by
  decide +kernel

private theorem inv11_ok : invB 11 e11 w11 codes11 inv11 = true := by decide +kernel

private theorem waC11_eq : wa11.map enc = waC11 := by decide +kernel

private theorem wbC11_eq : wb11.map enc = wbC11 := by decide +kernel

private theorem wa11_mem : ∀ t ∈ wa11, t ∈ alternatingGroup (Fin 11) ∧ t * t = 1 := by
  have hsq := sq_eq_one_of_codes le11 waC11_eq e11_eq (by decide +kernel)
  intro t ht
  refine ⟨?_, hsq t ht⟩
  simp only [wa11, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact swap_mul_swap_mem (by decide) (by decide)

private theorem wb11_mem : ∀ g ∈ wb11, g ∈ alternatingGroup (Fin 11) ∧ g * g = 1 := by
  have hsq := sq_eq_one_of_codes le11 wbC11_eq e11_eq (by decide +kernel)
  intro g hg
  refine ⟨?_, hsq g hg⟩
  simp only [wb11, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> exact swap_mul_swap_mem (by decide) (by decide)

private theorem fx11 : fxB 11 e11 w11 inv11 waC11 wbC11 (fun _ => false) = true := by
  decide +kernel

private theorem exp4_9 : (codes9.all fun a => cmul 9 (cmul 9 a a) (cmul 9 a a) == e9) = true := by
  decide +kernel

private theorem inv_eq_of_mem_rBar9 {σ : Perm (Fin 9)} (hσ : σ ∈ rBar9) : σ⁻¹ = σ * (σ * σ) := by
  have h := exp4_9
  simp only [List.all_eq_true, beq_iff_eq] at h
  have h4 := h _ ((mem_rBar9_iff σ).1 hσ)
  rw [← enc_mul le9, ← enc_mul le9, ← e9_eq] at h4
  apply inv_eq_of_mul_eq_one_right
  rw [← enc_injective le9 h4]
  group

private theorem commB9 : (codes9.all fun a => codes9.all fun b => codesB.contains
    (cmul 9 (cmul 9 (cmul 9 a b) (cmul 9 a (cmul 9 a a))) (cmul 9 b (cmul 9 b b)))) = true := by
  decide +kernel

private theorem comm_mem_bBar {a b : Perm (Fin 9)} (ha : a ∈ rBar9) (hb : b ∈ rBar9) :
    a * b * a⁻¹ * b⁻¹ ∈ bBar := by
  have h := commB9
  simp only [List.all_eq_true, List.contains_eq_mem, decide_eq_true_eq] at h
  rw [inv_eq_of_mem_rBar9 ha, inv_eq_of_mem_rBar9 hb, mem_bBar_iff]
  simp only [enc_mul le9]
  exact h _ ((mem_rBar9_iff a).1 ha) _ ((mem_rBar9_iff b).1 hb)

private theorem centJ9 : (codes9.all fun r =>
    !(cmul 9 r 0x867452301 == cmul 9 0x867452301 r && cmul 9 r 0x867453210 ==
      cmul 9 0x867453210 r && cmul 9 r 0x854761032 == cmul 9 0x854761032 r) ||
    codesB.contains r) = true := by
  decide +kernel

private theorem mem_bBar_of_comm {r : Perm (Fin 9)} (hr : r ∈ rBar9)
    (h1 : r * tr le89 1 = tr le89 1 * r)
    (h2 : r * (swap 4 5 * swap 6 7) = swap 4 5 * swap 6 7 * r)
    (h3 : r * tr le89 2 = tr le89 2 * r) : r ∈ bBar := by
  have e1 : enc (tr le89 1) = 0x867452301 := by decide +kernel
  have e2 : enc (swap 4 5 * swap 6 7 : Perm (Fin 9)) = 0x867453210 := by decide +kernel
  have e3 : enc (tr le89 2) = 0x854761032 := by decide +kernel
  rw [commute_iff le9, e1] at h1
  rw [commute_iff le9, e2] at h2
  rw [commute_iff le9, e3] at h3
  have h := centJ9
  simp only [List.all_eq_true] at h
  have hr' := h _ ((mem_rBar9_iff r).1 hr)
  rw [h1, h2, h3] at hr'
  simp only [beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_or,
    List.contains_eq_mem, decide_eq_true_eq] at hr'
  exact (mem_bBar_iff r).2 hr'

private theorem a0145_mem9 : swap 0 1 * swap 4 5 ∈ rBar9 :=
  (mem_rBar9_iff _).2 (by decide +kernel)

private theorem a4657_mem9 : swap 4 6 * swap 5 7 ∈ rBar9 :=
  (mem_rBar9_iff _).2 (by decide +kernel)

private theorem a0213_mem9 : swap 0 2 * swap 1 3 ∈ rBar9 :=
  (mem_rBar9_iff _).2 (by decide +kernel)

private theorem comm_4567 : (swap 0 1 * swap 4 5 : Perm (Fin 9)) * (swap 4 6 * swap 5 7) *
    (swap 0 1 * swap 4 5)⁻¹ * (swap 4 6 * swap 5 7)⁻¹ = swap 4 5 * swap 6 7 := by
  decide +kernel

private theorem comm_f9 : (swap 0 2 * swap 1 3 : Perm (Fin 9)) * tr le89 4 *
    (swap 0 2 * swap 1 3)⁻¹ * (tr le89 4)⁻¹ = tr le89 2 := by
  decide +kernel

private theorem bBar_le_rBar9 : bBar ≤ rBar9 := by
  have h : (gcB.all fun c => codes9.contains c) = true := by decide +kernel
  simp only [List.all_eq_true, List.contains_eq_mem, decide_eq_true_eq] at h
  rw [bBar_eq, closure_le]
  intro x hx
  rw [SetLike.mem_coe, mem_rBar9_iff]
  exact h _ (gcB_eq ▸ List.mem_map_of_mem hx)

private theorem mBar_norm_bBar (b : Perm (Fin 9)) (hb : b ∈ bBar) : mBar * b * mBar⁻¹ ∈ bBar := by
  have hm : mBar⁻¹ = mBar := by decide +kernel
  have hme : enc mBar = 0x875643120 := by decide +kernel
  have h : (codesB.all fun c => codesB.contains (cmul 9 (cmul 9 0x875643120 c) 0x875643120)) =
      true := by
    decide +kernel
  simp only [List.all_eq_true, List.contains_eq_mem, decide_eq_true_eq] at h
  rw [hm, mem_bBar_iff, enc_mul le9, enc_mul le9, hme]
  exact h _ ((mem_bBar_iff b).1 hb)

end FinData

theorem fusR9 : FusR 9 le89 (alternatingGroup (Fin 9)) rBar9 6 cc9 where
  le := rBar9_le
  card := card_rBar9
  tr_mem := tr_mem9
  center := center_of_check le9 gc9_eq e9_eq w9_eq mem_rBar9_iff
    (fun g hg => by rw [rBar9_eq]; exact subset_closure hg) center9
  comm := ⟨_, a4567_mem9, _, tr_mem9 4, comm_w9⟩
  fx := fx_of_check (ccB := cc9B) le9 e9_eq w9_eq mem_rBar9_iff (mem_of_invB inv9_ok) waC9_eq
    wa9_mem wbC9_eq wb9_mem cc9_of_check fx9

theorem fusRS9 : FusR 9 le89 ⊤ rBarS9 7 fun _ => False where
  le := le_top
  card := card_rBarS9
  tr_mem := tr_memS9
  center := center_of_check le9 gcS9_eq e9_eq w9_eq mem_rBarS9_iff
    (fun g hg => by rw [rBarS9_eq]; exact subset_closure hg) centerS9
  comm := ⟨_, a4567_memS9, _, tr_memS9 4, comm_w9⟩
  fx := fx_of_check (ccB := fun _ => false) le9 e9_eq w9_eq mem_rBarS9_iff (mem_of_invB invS9_ok)
    waCS9_eq waS9_mem wbC9_eq wbS9_mem (fun _ _ _ h => by simp at h) fxS9

theorem fusR11 : FusR 11 le811 (alternatingGroup (Fin 11)) rBar11 7 fun _ => False where
  le := rBar11_le
  card := card_rBar11
  tr_mem := tr_mem11
  center := center_of_check le11 gc11_eq e11_eq w11_eq mem_rBar11_iff
    (fun g hg => by rw [rBar11_eq]; exact subset_closure hg) center11
  comm := ⟨_, a4567_mem11, _, tr_mem11 4, comm_w11⟩
  fx := fx_of_check (ccB := fun _ => false) le11 e11_eq w11_eq mem_rBar11_iff
    (mem_of_invB inv11_ok) waC11_eq wa11_mem wbC11_eq wb11_mem (fun _ _ _ h => by simp at h) fx11

theorem fusJ : FusJ where
  bBar_le := bBar_le_rBar9
  cent_iff := by
    intro r hr
    constructor
    · intro h
      refine mem_bBar_of_comm hr ?_ ?_ ?_
      · have h1 := h _ a4567_mem9 _ (tr_mem9 4)
        rwa [comm_w9] at h1
      · have h2 := h _ a0145_mem9 _ a4657_mem9
        rwa [comm_4567] at h2
      · have h3 := h _ a0213_mem9 _ (tr_mem9 4)
        rwa [comm_f9] at h3
    · intro hrB a ha b hb
      exact comm_of_mem_bBar hrB (comm_mem_bBar ha hb)
  mBar_mem := swap_mul_swap_mem (by decide) (by decide)
  mBar_conj := by decide +kernel
  mBar_norm := mBar_norm_bBar
  tr_two_mem := (mem_bBar_iff _).2 (by decide +kernel)

end CFSG.OddStandard.AltStdSmall4.Fus

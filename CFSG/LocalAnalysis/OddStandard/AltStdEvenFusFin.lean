module

public import CFSG.LocalAnalysis.OddStandard.AltStdEvenFusDefs
public import CFSG.LocalAnalysis.OddStandard.AltStdEvenFusFinData
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4FusDefs

public section

namespace CFSG.OddStandard.AltStdSmall4.Fus

open Equiv Subgroup FinCode FinData

namespace FinData

private theorem swap_mul_swap_mem {m : ℕ} {a b c d : Fin m} (h1 : a ≠ b) (h2 : c ≠ d) :
    swap a b * swap c d ∈ alternatingGroup (Fin m) := by
  rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap h1, Perm.sign_swap h2]
  rfl

private theorem le8 : (8 : ℕ) ≤ 16 := by norm_num

private theorem le10 : (10 : ℕ) ≤ 16 := by norm_num

private theorem e8_eq : enc (1 : Perm (Fin 8)) = e8 := by decide +kernel

private theorem w8_eq : enc (tr le88 1) = w8 := by decide +kernel

private theorem e10_eq : enc (1 : Perm (Fin 10)) = e10 := by decide +kernel

private theorem w10_eq : enc (tr le810 1) = w10 := by decide +kernel

private theorem bBar8_eq : bBar8 = closure {x | x ∈ gensB8} := by
  rw [bBar8]
  congr 1
  ext x
  simp [gensB8]

private theorem gcB8_eq : gensB8.map enc = gcB8 := by decide +kernel

private theorem sq_gensB8 : ∀ g ∈ gensB8, g * g = 1 :=
  sq_eq_one_of_codes le8 gcB8_eq e8_eq (by decide +kernel)

private theorem closed_B8 : closedB 8 codesB8 gcB8 = true := by decide +kernel

private theorem wordsB8_eq : wordsB8.map (wordCode 8 e8 gcB8) = codesB8 := by decide +kernel

private theorem one_B8 : e8 ∈ codesB8 := by decide +kernel

theorem mem_bBar8_iff (σ : Perm (Fin 8)) : σ ∈ bBar8 ↔ enc σ ∈ codesB8 := by
  rw [bBar8_eq]
  exact mem_closure_iff le8 gcB8_eq e8_eq sq_gensB8 closed_B8 wordsB8_eq one_B8 σ

private theorem abel_B8 : (codesB8.all fun a => codesB8.all fun b => cmul 8 a b == cmul 8 b a) =
    true := by
  decide +kernel

private theorem comm_of_mem_bBar8 {x y : Perm (Fin 8)} (hx : x ∈ bBar8) (hy : y ∈ bBar8) :
    x * y = y * x := by
  have h := abel_B8
  simp only [List.all_eq_true, beq_iff_eq] at h
  rw [commute_iff le8]
  exact h _ ((mem_bBar8_iff x).1 hx) _ ((mem_bBar8_iff y).1 hy)

private theorem rBar8_eq : rBar8 = closure {x | x ∈ gens8} := by
  rw [rBar8]
  congr 1
  ext x
  simp [gens8]

private theorem gc8_eq : gens8.map enc = gc8 := by decide +kernel

private theorem sq_gens8 : ∀ g ∈ gens8, g * g = 1 :=
  sq_eq_one_of_codes le8 gc8_eq e8_eq (by decide +kernel)

private theorem closed8 : closedB 8 codes8 gc8 = true := by decide +kernel

private theorem words8_eq : words8.map (wordCode 8 e8 gc8) = codes8 := by decide +kernel

private theorem one8 : e8 ∈ codes8 := by decide +kernel

private theorem nodup8 : nodupB codes8 = true := by decide +kernel

theorem mem_rBar8_iff (σ : Perm (Fin 8)) : σ ∈ rBar8 ↔ enc σ ∈ codes8 := by
  rw [rBar8_eq]
  exact mem_closure_iff le8 gc8_eq e8_eq sq_gens8 closed8 words8_eq one8 σ

private theorem card_rBar8 : Nat.card rBar8 = 2 ^ 6 := by
  rw [rBar8_eq, card_closure le8 gc8_eq e8_eq sq_gens8 closed8 words8_eq one8
    (nodup_of_nodupB nodup8)]
  decide +kernel

private theorem rBar8_le : rBar8 ≤ alternatingGroup (Fin 8) := by
  rw [rBar8, closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact swap_mul_swap_mem (by decide) (by decide)
  · exact mul_mem (swap_mul_swap_mem (by decide) (by decide))
      (swap_mul_swap_mem (by decide) (by decide))
  · exact mul_mem (swap_mul_swap_mem (by decide) (by decide))
      (swap_mul_swap_mem (by decide) (by decide))

private theorem tr_codes8 : ∀ v : Fin 8, enc (tr le88 v) ∈ codes8 := by decide +kernel

private theorem tr_mem8 (v : Fin 8) : tr le88 v ∈ rBar8 :=
  (mem_rBar8_iff _).2 (tr_codes8 v)

private theorem center8 : centerB 8 e8 w8 codes8 gc8 = true := by decide +kernel

private theorem a4567_mem8 : swap 4 5 * swap 6 7 ∈ rBar8 :=
  (mem_rBar8_iff _).2 (by decide +kernel)

private theorem comm_w8 : (swap 4 5 * swap 6 7 : Perm (Fin 8)) * tr le88 4 *
    (swap 4 5 * swap 6 7)⁻¹ * (tr le88 4)⁻¹ = tr le88 1 := by
  decide +kernel

private theorem inv8_ok : invB 8 e8 w8 codes8 inv8 = true := by decide +kernel

private theorem waC8_eq : wa8.map enc = waC8 := by decide +kernel

private theorem wbC8_eq : wb8.map enc = wbC8 := by decide +kernel

private theorem wa8_mem : ∀ t ∈ wa8, t ∈ alternatingGroup (Fin 8) ∧ t * t = 1 := by
  have hsq := sq_eq_one_of_codes le8 waC8_eq e8_eq (by decide +kernel)
  intro t ht
  refine ⟨?_, hsq t ht⟩
  simp only [wa8, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl <;> exact swap_mul_swap_mem (by decide) (by decide)

private theorem wb8_sq : ∀ g ∈ wb8, g * g = 1 :=
  sq_eq_one_of_codes le8 wbC8_eq e8_eq (by decide +kernel)

private theorem wb8_mem : ∀ g ∈ wb8, g ∈ alternatingGroup (Fin 8) ∧ g * g = 1 := by
  intro g hg
  refine ⟨?_, wb8_sq g hg⟩
  simp only [wb8, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> exact swap_mul_swap_mem (by decide) (by decide)

private theorem cc8_of_check : ∀ X : Subgroup (Perm (Fin 8)), ∀ O : List ℕ,
    (∀ x, x ∈ X ↔ enc x ∈ O) → cc8B O = true → cc8 X := by
  intro X O hXO hO y hyX hyB hy1 hyw
  simp only [cc8B, List.all_eq_true] at hO
  have h := hO (enc y) ((hXO y).1 hyX)
  have h1 : codesB8.contains (enc y) = true := by
    rw [List.contains_eq_mem, decide_eq_true_eq]
    exact (mem_bBar8_iff y).1 hyB
  have h2 : (enc y == e8) = false := by
    rw [beq_eq_false_iff_ne, ← e8_eq]
    exact fun h => hy1 (enc_injective le8 h)
  have h3 : (enc y == w8) = false := by
    rw [beq_eq_false_iff_ne, ← w8_eq]
    exact fun h => hyw (enc_injective le8 h)
  rw [h1, h2, h3] at h
  rw [card_support_eq le8]
  simpa using h

private theorem fx8 : fxB 8 e8 w8 inv8 waC8 wbC8 cc8B = true := by decide +kernel

private theorem rBarS8_eq : rBarS8 = closure {x | x ∈ gensS8} := by
  rw [rBarS8]
  congr 1
  ext x
  simp [gensS8]

private theorem gcS8_eq : gensS8.map enc = gcS8 := by decide +kernel

private theorem sq_gensS8 : ∀ g ∈ gensS8, g * g = 1 :=
  sq_eq_one_of_codes le8 gcS8_eq e8_eq (by decide +kernel)

private theorem closedS8 : closedB 8 codesS8 gcS8 = true := by decide +kernel

private theorem wordsS8_eq : wordsS8.map (wordCode 8 e8 gcS8) = codesS8 := by decide +kernel

private theorem oneS8 : e8 ∈ codesS8 := by decide +kernel

private theorem nodupS8 : nodupB codesS8 = true := by decide +kernel

theorem mem_rBarS8_iff (σ : Perm (Fin 8)) : σ ∈ rBarS8 ↔ enc σ ∈ codesS8 := by
  rw [rBarS8_eq]
  exact mem_closure_iff le8 gcS8_eq e8_eq sq_gensS8 closedS8 wordsS8_eq oneS8 σ

private theorem card_rBarS8 : Nat.card rBarS8 = 2 ^ 7 := by
  rw [rBarS8_eq, card_closure le8 gcS8_eq e8_eq sq_gensS8 closedS8 wordsS8_eq oneS8
    (nodup_of_nodupB nodupS8)]
  decide +kernel

private theorem tr_codesS8 : ∀ v : Fin 8, enc (tr le88 v) ∈ codesS8 := by decide +kernel

private theorem tr_memS8 (v : Fin 8) : tr le88 v ∈ rBarS8 :=
  (mem_rBarS8_iff _).2 (tr_codesS8 v)

private theorem centerS8 : centerB 8 e8 w8 codesS8 gcS8 = true := by decide +kernel

private theorem a4567_memS8 : swap 4 5 * swap 6 7 ∈ rBarS8 :=
  (mem_rBarS8_iff _).2 (by decide +kernel)

private theorem invS8_ok : invB 8 e8 w8 codesS8 invS8 = true := by decide +kernel

private theorem waCS8_eq : waS8.map enc = waCS8 := by decide +kernel

private theorem waS8_mem : ∀ t ∈ waS8, t ∈ (⊤ : Subgroup (Perm (Fin 8))) ∧ t * t = 1 :=
  fun t ht => ⟨mem_top t, sq_eq_one_of_codes le8 waCS8_eq e8_eq (by decide +kernel) t ht⟩

private theorem wbS8_mem : ∀ g ∈ wb8, g ∈ (⊤ : Subgroup (Perm (Fin 8))) ∧ g * g = 1 :=
  fun g hg => ⟨mem_top g, wb8_sq g hg⟩

private theorem fxS8 : fxB 8 e8 w8 invS8 waCS8 wbC8 (fun _ => false) = true := by decide +kernel

private theorem rBar10_eq : rBar10 = closure {x | x ∈ gens10} := by
  rw [rBar10]
  congr 1
  ext x
  simp [gens10]

private theorem gc10_eq : gens10.map enc = gc10 := by decide +kernel

private theorem sq_gens10 : ∀ g ∈ gens10, g * g = 1 :=
  sq_eq_one_of_codes le10 gc10_eq e10_eq (by decide +kernel)

private theorem closed10 : closedB 10 codes10 gc10 = true := by decide +kernel

private theorem words10_eq : words10.map (wordCode 10 e10 gc10) = codes10 := by decide +kernel

private theorem one10 : e10 ∈ codes10 := by decide +kernel

private theorem nodup10 : nodupB codes10 = true := by decide +kernel

theorem mem_rBar10_iff (σ : Perm (Fin 10)) : σ ∈ rBar10 ↔ enc σ ∈ codes10 := by
  rw [rBar10_eq]
  exact mem_closure_iff le10 gc10_eq e10_eq sq_gens10 closed10 words10_eq one10 σ

private theorem card_rBar10 : Nat.card rBar10 = 2 ^ 7 := by
  rw [rBar10_eq, card_closure le10 gc10_eq e10_eq sq_gens10 closed10 words10_eq one10
    (nodup_of_nodupB nodup10)]
  decide +kernel

private theorem rBar10_le : rBar10 ≤ alternatingGroup (Fin 10) := by
  rw [rBar10, closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact swap_mul_swap_mem (by decide) (by decide)
  · exact swap_mul_swap_mem (by decide) (by decide)
  · exact mul_mem (swap_mul_swap_mem (by decide) (by decide))
      (swap_mul_swap_mem (by decide) (by decide))

private theorem tr_codes10 : ∀ v : Fin 8, enc (tr le810 v) ∈ codes10 := by decide +kernel

private theorem tr_mem10 (v : Fin 8) : tr le810 v ∈ rBar10 :=
  (mem_rBar10_iff _).2 (tr_codes10 v)

private theorem center10 : centerB 10 e10 w10 codes10 gc10 = true := by decide +kernel

private theorem a4567_mem10 : swap 4 5 * swap 6 7 ∈ rBar10 :=
  (mem_rBar10_iff _).2 (by decide +kernel)

private theorem comm_w10 : (swap 4 5 * swap 6 7 : Perm (Fin 10)) * tr le810 4 *
    (swap 4 5 * swap 6 7)⁻¹ * (tr le810 4)⁻¹ = tr le810 1 := by
  decide +kernel

private theorem inv10_ok : invB 10 e10 w10 codes10 inv10 = true := by decide +kernel

private theorem waC10_eq : wa10.map enc = waC10 := by decide +kernel

private theorem wbC10_eq : wb10.map enc = wbC10 := by decide +kernel

private theorem wa10_mem : ∀ t ∈ wa10, t ∈ alternatingGroup (Fin 10) ∧ t * t = 1 := by
  have hsq := sq_eq_one_of_codes le10 waC10_eq e10_eq (by decide +kernel)
  intro t ht
  refine ⟨?_, hsq t ht⟩
  simp only [wa10, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact swap_mul_swap_mem (by decide) (by decide)

private theorem wb10_mem : ∀ g ∈ wb10, g ∈ alternatingGroup (Fin 10) ∧ g * g = 1 := by
  have hsq := sq_eq_one_of_codes le10 wbC10_eq e10_eq (by decide +kernel)
  intro g hg
  refine ⟨?_, hsq g hg⟩
  simp only [wb10, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> exact swap_mul_swap_mem (by decide) (by decide)

private theorem fx10 : fxB 10 e10 w10 inv10 waC10 wbC10 (fun _ => false) = true := by
  decide +kernel

private theorem exp4_8 : (codes8.all fun a => cmul 8 (cmul 8 a a) (cmul 8 a a) == e8) = true := by
  decide +kernel

private theorem inv_eq_of_mem_rBar8 {σ : Perm (Fin 8)} (hσ : σ ∈ rBar8) : σ⁻¹ = σ * (σ * σ) := by
  have h := exp4_8
  simp only [List.all_eq_true, beq_iff_eq] at h
  have h4 := h _ ((mem_rBar8_iff σ).1 hσ)
  rw [← enc_mul le8, ← enc_mul le8, ← e8_eq] at h4
  apply inv_eq_of_mul_eq_one_right
  rw [← enc_injective le8 h4]
  group

private theorem commB8 : (codes8.all fun a => codes8.all fun b => codesB8.contains
    (cmul 8 (cmul 8 (cmul 8 a b) (cmul 8 a (cmul 8 a a))) (cmul 8 b (cmul 8 b b)))) = true := by
  decide +kernel

private theorem comm_mem_bBar8 {a b : Perm (Fin 8)} (ha : a ∈ rBar8) (hb : b ∈ rBar8) :
    a * b * a⁻¹ * b⁻¹ ∈ bBar8 := by
  have h := commB8
  simp only [List.all_eq_true, List.contains_eq_mem, decide_eq_true_eq] at h
  rw [inv_eq_of_mem_rBar8 ha, inv_eq_of_mem_rBar8 hb, mem_bBar8_iff]
  simp only [enc_mul le8]
  exact h _ ((mem_rBar8_iff a).1 ha) _ ((mem_rBar8_iff b).1 hb)

private theorem centJ8 : (codes8.all fun r =>
    !(cmul 8 r 0x67452301 == cmul 8 0x67452301 r && cmul 8 r 0x67453210 ==
      cmul 8 0x67453210 r && cmul 8 r 0x54761032 == cmul 8 0x54761032 r) ||
    codesB8.contains r) = true := by
  decide +kernel

private theorem mem_bBar8_of_comm {r : Perm (Fin 8)} (hr : r ∈ rBar8)
    (h1 : r * tr le88 1 = tr le88 1 * r)
    (h2 : r * (swap 4 5 * swap 6 7) = swap 4 5 * swap 6 7 * r)
    (h3 : r * tr le88 2 = tr le88 2 * r) : r ∈ bBar8 := by
  have e1 : enc (tr le88 1) = 0x67452301 := by decide +kernel
  have e2 : enc (swap 4 5 * swap 6 7 : Perm (Fin 8)) = 0x67453210 := by decide +kernel
  have e3 : enc (tr le88 2) = 0x54761032 := by decide +kernel
  rw [commute_iff le8, e1] at h1
  rw [commute_iff le8, e2] at h2
  rw [commute_iff le8, e3] at h3
  have h := centJ8
  simp only [List.all_eq_true] at h
  have hr' := h _ ((mem_rBar8_iff r).1 hr)
  rw [h1, h2, h3] at hr'
  simp only [beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_or,
    List.contains_eq_mem, decide_eq_true_eq] at hr'
  exact (mem_bBar8_iff r).2 hr'

private theorem a0145_mem8 : swap 0 1 * swap 4 5 ∈ rBar8 :=
  (mem_rBar8_iff _).2 (by decide +kernel)

private theorem a4657_mem8 : swap 4 6 * swap 5 7 ∈ rBar8 :=
  (mem_rBar8_iff _).2 (by decide +kernel)

private theorem a0213_mem8 : swap 0 2 * swap 1 3 ∈ rBar8 :=
  (mem_rBar8_iff _).2 (by decide +kernel)

private theorem comm_4567 : (swap 0 1 * swap 4 5 : Perm (Fin 8)) * (swap 4 6 * swap 5 7) *
    (swap 0 1 * swap 4 5)⁻¹ * (swap 4 6 * swap 5 7)⁻¹ = swap 4 5 * swap 6 7 := by
  decide +kernel

private theorem comm_f8 : (swap 0 2 * swap 1 3 : Perm (Fin 8)) * tr le88 4 *
    (swap 0 2 * swap 1 3)⁻¹ * (tr le88 4)⁻¹ = tr le88 2 := by
  decide +kernel

private theorem bBar8_le_rBar8 : bBar8 ≤ rBar8 := by
  have h : (gcB8.all fun c => codes8.contains c) = true := by decide +kernel
  simp only [List.all_eq_true, List.contains_eq_mem, decide_eq_true_eq] at h
  rw [bBar8_eq, closure_le]
  intro x hx
  rw [SetLike.mem_coe, mem_rBar8_iff]
  exact h _ (gcB8_eq ▸ List.mem_map_of_mem hx)

private theorem mBar8_norm_bBar8 (b : Perm (Fin 8)) (hb : b ∈ bBar8) :
    mBar8 * b * mBar8⁻¹ ∈ bBar8 := by
  have hm : mBar8⁻¹ = mBar8 := by decide +kernel
  have hme : enc mBar8 = 0x75643120 := by decide +kernel
  have h : (codesB8.all fun c => codesB8.contains (cmul 8 (cmul 8 0x75643120 c) 0x75643120)) =
      true := by
    decide +kernel
  simp only [List.all_eq_true, List.contains_eq_mem, decide_eq_true_eq] at h
  rw [hm, mem_bBar8_iff, enc_mul le8, enc_mul le8, hme]
  exact h _ ((mem_bBar8_iff b).1 hb)

end FinData

theorem fusR8 : FusR 8 le88 (alternatingGroup (Fin 8)) rBar8 6 cc8 where
  le := rBar8_le
  card := card_rBar8
  tr_mem := tr_mem8
  center := center_of_check le8 gc8_eq e8_eq w8_eq mem_rBar8_iff
    (fun g hg => by rw [rBar8_eq]; exact subset_closure hg) center8
  comm := ⟨_, a4567_mem8, _, tr_mem8 4, comm_w8⟩
  fx := fx_of_check (ccB := cc8B) le8 e8_eq w8_eq mem_rBar8_iff (mem_of_invB inv8_ok) waC8_eq
    wa8_mem wbC8_eq wb8_mem cc8_of_check fx8

theorem fusRS8 : FusR 8 le88 ⊤ rBarS8 7 fun _ => False where
  le := le_top
  card := card_rBarS8
  tr_mem := tr_memS8
  center := center_of_check le8 gcS8_eq e8_eq w8_eq mem_rBarS8_iff
    (fun g hg => by rw [rBarS8_eq]; exact subset_closure hg) centerS8
  comm := ⟨_, a4567_memS8, _, tr_memS8 4, comm_w8⟩
  fx := fx_of_check (ccB := fun _ => false) le8 e8_eq w8_eq mem_rBarS8_iff (mem_of_invB invS8_ok)
    waCS8_eq waS8_mem wbC8_eq wbS8_mem (fun _ _ _ h => by simp at h) fxS8

theorem fusR10 : FusR 10 le810 (alternatingGroup (Fin 10)) rBar10 7 fun _ => False where
  le := rBar10_le
  card := card_rBar10
  tr_mem := tr_mem10
  center := center_of_check le10 gc10_eq e10_eq w10_eq mem_rBar10_iff
    (fun g hg => by rw [rBar10_eq]; exact subset_closure hg) center10
  comm := ⟨_, a4567_mem10, _, tr_mem10 4, comm_w10⟩
  fx := fx_of_check (ccB := fun _ => false) le10 e10_eq w10_eq mem_rBar10_iff
    (mem_of_invB inv10_ok) waC10_eq wa10_mem wbC10_eq wb10_mem (fun _ _ _ h => by simp at h) fx10

theorem fusJ8 : FusJ8 where
  bBar_le := bBar8_le_rBar8
  cent_iff := by
    intro r hr
    constructor
    · intro h
      refine mem_bBar8_of_comm hr ?_ ?_ ?_
      · have h1 := h _ a4567_mem8 _ (tr_mem8 4)
        rwa [comm_w8] at h1
      · have h2 := h _ a0145_mem8 _ a4657_mem8
        rwa [comm_4567] at h2
      · have h3 := h _ a0213_mem8 _ (tr_mem8 4)
        rwa [comm_f8] at h3
    · intro hrB a ha b hb
      exact comm_of_mem_bBar8 hrB (comm_mem_bBar8 ha hb)
  mBar_mem := swap_mul_swap_mem (by decide) (by decide)
  mBar_conj := by decide +kernel
  mBar_norm := mBar8_norm_bBar8
  tr_two_mem := (mem_bBar8_iff _).2 (by decide +kernel)

end CFSG.OddStandard.AltStdSmall4.Fus

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24Wreath
public import CFSG.GH74.Uniqueness.SU.SU5A8

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.GH74.Uniqueness.SU.SU5

private def e0 : Equiv.Perm (Fin 8) := Equiv.swap 1 4 * Equiv.swap 3 5

private def u0 : Equiv.Perm (Fin 8) := Equiv.swap 4 5 * Equiv.swap 6 7

private def w0 : Equiv.Perm (Fin 8) :=
  Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 6 * Equiv.swap 5 7

private theorem sign_e0 : Equiv.Perm.sign e0 = 1 := by
  rw [e0, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap', Equiv.Perm.sign_swap']
  decide

private theorem sign_u0 : Equiv.Perm.sign u0 = 1 := by
  rw [u0, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap', Equiv.Perm.sign_swap']
  decide

private theorem sign_w0 : Equiv.Perm.sign w0 = 1 := by
  rw [w0, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_swap', Equiv.Perm.sign_swap', Equiv.Perm.sign_swap', Equiv.Perm.sign_swap']
  decide

private theorem e0_mem : e0 ∈ alternatingGroup (Fin 8) :=
  Equiv.Perm.mem_alternatingGroup.mpr sign_e0

private theorem u0_mem : u0 ∈ alternatingGroup (Fin 8) :=
  Equiv.Perm.mem_alternatingGroup.mpr sign_u0

private theorem w0_mem : w0 ∈ alternatingGroup (Fin 8) :=
  Equiv.Perm.mem_alternatingGroup.mpr sign_w0

private def eA8 : alternatingGroup (Fin 8) := ⟨e0, e0_mem⟩

private def uA8 : alternatingGroup (Fin 8) := ⟨u0, u0_mem⟩

private def wA8 : alternatingGroup (Fin 8) := ⟨w0, w0_mem⟩

private def S8 : Subgroup (alternatingGroup (Fin 8)) :=
  Subgroup.closure ({eA8, uA8, wA8} : Set (alternatingGroup (Fin 8)))

private def gen : Fin 3 → alternatingGroup (Fin 8) :=
  fun k => if k = 0 then eA8 else if k = 1 then uA8 else wA8

private def evalWord : List (Fin 3) → alternatingGroup (Fin 8)
  | [] => 1
  | k :: ks => gen k * evalWord ks

private def words : List (List (Fin 3)) :=
  [[],
   [0],
   [1],
   [2],
   [0, 1],
   [0, 2],
   [1, 0],
   [1, 2],
   [2, 0],
   [0, 1, 0],
   [0, 1, 2],
   [0, 2, 0],
   [1, 0, 1],
   [1, 0, 2],
   [1, 2, 0],
   [2, 0, 1],
   [2, 0, 2],
   [0, 1, 0, 1],
   [0, 1, 0, 2],
   [0, 1, 2, 0],
   [0, 2, 0, 1],
   [0, 2, 0, 2],
   [1, 0, 1, 2],
   [1, 0, 2, 0],
   [1, 2, 0, 1],
   [1, 2, 0, 2],
   [2, 0, 1, 0],
   [2, 0, 1, 2],
   [0, 1, 0, 1, 2],
   [0, 1, 0, 2, 0],
   [0, 1, 2, 0, 1],
   [0, 1, 2, 0, 2],
   [0, 2, 0, 1, 0],
   [0, 2, 0, 1, 2],
   [1, 0, 1, 2, 0],
   [1, 0, 2, 0, 1],
   [1, 0, 2, 0, 2],
   [1, 2, 0, 1, 0],
   [1, 2, 0, 1, 2],
   [2, 0, 1, 0, 2],
   [2, 0, 1, 2, 0],
   [0, 1, 0, 1, 2, 0],
   [0, 1, 0, 2, 0, 1],
   [0, 1, 0, 2, 0, 2],
   [0, 1, 2, 0, 1, 0],
   [0, 1, 2, 0, 1, 2],
   [0, 2, 0, 1, 0, 2],
   [0, 2, 0, 1, 2, 0],
   [1, 0, 1, 2, 0, 1],
   [1, 0, 1, 2, 0, 2],
   [1, 0, 2, 0, 1, 0],
   [1, 0, 2, 0, 1, 2],
   [1, 2, 0, 1, 0, 2],
   [2, 0, 1, 0, 2, 0],
   [0, 1, 0, 1, 2, 0, 1],
   [0, 1, 0, 1, 2, 0, 2],
   [0, 1, 0, 2, 0, 1, 0],
   [0, 1, 0, 2, 0, 1, 2],
   [0, 1, 2, 0, 1, 0, 2],
   [0, 2, 0, 1, 0, 2, 0],
   [1, 0, 1, 2, 0, 1, 0],
   [1, 0, 2, 0, 1, 0, 2],
   [0, 1, 0, 1, 2, 0, 1, 0],
   [0, 1, 0, 2, 0, 1, 0, 2]]

private def elts : List (alternatingGroup (Fin 8)) := words.map evalWord

private theorem eA8_mem_S8 : eA8 ∈ S8 := Subgroup.subset_closure (by simp)

private theorem uA8_mem_S8 : uA8 ∈ S8 := Subgroup.subset_closure (by simp)

private theorem wA8_mem_S8 : wA8 ∈ S8 := Subgroup.subset_closure (by simp)

private theorem gen_mem (k : Fin 3) : gen k ∈ S8 := by
  by_cases h0 : k = 0
  · simp [gen, h0, eA8_mem_S8]
  · by_cases h1 : k = 1
    · simp [gen, h1, uA8_mem_S8]
    · simp [gen, h0, h1, wA8_mem_S8]

private theorem evalWord_mem (w : List (Fin 3)) : evalWord w ∈ S8 := by
  induction w with
  | nil => exact S8.one_mem
  | cons k ks ih =>
    change gen k * evalWord ks ∈ S8
    exact S8.mul_mem (gen_mem k) ih

set_option maxRecDepth 100000 in
private theorem elts_nodup : elts.Nodup := by decide +kernel

set_option maxRecDepth 100000 in
private theorem elts_length : elts.length = 64 := by decide +kernel

set_option maxRecDepth 100000 in
private theorem one_mem_elts : (1 : alternatingGroup (Fin 8)) ∈ elts := by decide +kernel

set_option maxRecDepth 100000 in
private theorem eA8_mem_elts : eA8 ∈ elts := by decide +kernel

set_option maxRecDepth 100000 in
private theorem uA8_mem_elts : uA8 ∈ elts := by decide +kernel

set_option maxRecDepth 100000 in
private theorem wA8_mem_elts : wA8 ∈ elts := by decide +kernel

set_option maxRecDepth 100000 in
private theorem elts_mul_gen_all :
    elts.all (fun g => decide (∀ k : Fin 3, g * gen k ∈ elts)) = true := by
  decide +kernel

private theorem elts_mul_gen (g : alternatingGroup (Fin 8)) (hg : g ∈ elts) (k : Fin 3) :
    g * gen k ∈ elts := by
  have h' : decide (∀ k : Fin 3, g * gen k ∈ elts) = true :=
    List.all_eq_true.mp elts_mul_gen_all g hg
  exact of_decide_eq_true h' k

set_option maxRecDepth 100000 in
private theorem elts_inv_all : elts.all (fun g => decide (g⁻¹ ∈ elts)) = true := by
  decide +kernel

private theorem elts_inv (g : alternatingGroup (Fin 8)) (hg : g ∈ elts) : g⁻¹ ∈ elts := by
  have h' : decide (g⁻¹ ∈ elts) = true := List.all_eq_true.mp elts_inv_all g hg
  exact of_decide_eq_true h'

private theorem elts_mul_evalWord (x : alternatingGroup (Fin 8)) (hx : x ∈ elts) :
    ∀ w : List (Fin 3), x * evalWord w ∈ elts := by
  intro w
  induction w generalizing x with
  | nil => show x * 1 ∈ elts; rw [mul_one]; exact hx
  | cons k ks ih =>
    rw [show evalWord (k :: ks) = gen k * evalWord ks from rfl, ← mul_assoc]
    exact ih (x * gen k) (elts_mul_gen x hx k)

private theorem hmem (g : alternatingGroup (Fin 8)) : g ∈ S8 ↔ g ∈ elts := by
  constructor
  · intro hg
    change g ∈ Subgroup.closure ({eA8, uA8, wA8} : Set (alternatingGroup (Fin 8))) at hg
    refine Subgroup.closure_induction (p := fun x _ => x ∈ elts) ?mem ?one ?mul ?inv hg
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact eA8_mem_elts
      · exact uA8_mem_elts
      · exact wA8_mem_elts
    · exact one_mem_elts
    · intro x y hx hy hpx hpy
      unfold elts at hpy
      obtain ⟨w, -, hw⟩ := List.mem_map.mp hpy
      rw [← hw]
      exact elts_mul_evalWord x hpx w
    · intro x hx hpx
      exact elts_inv x hpx
  · intro hg
    unfold elts at hg
    obtain ⟨w, -, hw⟩ := List.mem_map.mp hg
    rw [← hw]
    exact evalWord_mem w

private theorem card_S8 : Nat.card S8 = 64 := by
  have hcard : elts.toFinset.card = 64 := by
    rw [List.toFinset_card_of_nodup elts_nodup, elts_length]
  have hset : (S8 : Set (alternatingGroup (Fin 8))) = (elts.toFinset : Set _) := by
    ext g
    rw [Finset.mem_coe, List.mem_toFinset]
    exact hmem g
  have h1 : Nat.card S8 = (S8 : Set (alternatingGroup (Fin 8))).ncard :=
    Nat.card_coe_set_eq (S8 : Set (alternatingGroup (Fin 8)))
  rw [h1, hset, Set.ncard_coe_finset]
  exact hcard

private theorem card_A8_fact :
    (Nat.card (alternatingGroup (Fin 8))).factorization 2 = 6 := by
  have h1 : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  rw [h1, Nat.factorization_def _ Nat.prime_two]
  have h2 : (20160 : ℕ) = 2 ^ 6 * 315 := by norm_num
  rw [h2, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow]
  have h3 : padicValNat 2 315 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  omega

private theorem card_S8_sylow :
    Nat.card S8 = 2 ^ (Nat.card (alternatingGroup (Fin 8))).factorization 2 := by
  rw [card_S8, card_A8_fact]
  norm_num

private def Qw : Sylow 2 (alternatingGroup (Fin 8)) := Sylow.ofCard S8 card_S8_sylow

private def eQ : ↥(Qw : Subgroup (alternatingGroup (Fin 8))) :=
  ⟨eA8, Subgroup.subset_closure (by simp)⟩

private def uQ : ↥(Qw : Subgroup (alternatingGroup (Fin 8))) :=
  ⟨uA8, Subgroup.subset_closure (by simp)⟩

private def wQ : ↥(Qw : Subgroup (alternatingGroup (Fin 8))) :=
  ⟨wA8, Subgroup.subset_closure (by simp)⟩

set_option maxRecDepth 100000 in
private theorem e0_sq : e0 * e0 = 1 := by decide +kernel

set_option maxRecDepth 100000 in
private theorem u0_sq : u0 * u0 = 1 := by decide +kernel

set_option maxRecDepth 100000 in
private theorem w0_sq : w0 * w0 = 1 := by decide +kernel

set_option maxRecDepth 100000 in
private theorem uw_comm : u0 * w0 = w0 * u0 := by decide +kernel

private theorem conj_comm_perm :
    ∀ g ∈ ({1, u0, w0, u0 * w0} : Set (Equiv.Perm (Fin 8))),
      ∀ h ∈ ({1, u0, w0, u0 * w0} : Set (Equiv.Perm (Fin 8))),
        Commute (g * e0 * g⁻¹) (h * e0 * h⁻¹) := by
  intro g hg h hh
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg hh
  rcases hg with rfl | rfl | rfl | rfl
  all_goals rcases hh with rfl | rfl | rfl | rfl
  all_goals rw [commute_iff_eq]
  all_goals decide +kernel

theorem exists_sylow_wreathData : ∃ (Q : Sylow 2 (alternatingGroup (Fin 8)))
    (e u w : ↥(Q : Subgroup (alternatingGroup (Fin 8)))), WreathData ↥(Q : Subgroup
      (alternatingGroup (Fin 8))) e u w := by
  refine ⟨Qw, eQ, uQ, wQ, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact card_S8
  · have hk : ((↑) : ↥(Qw : Subgroup (alternatingGroup (Fin 8))) →
          alternatingGroup (Fin 8)) ⁻¹'
        ({eA8, uA8, wA8} : Set (alternatingGroup (Fin 8))) = {eQ, uQ, wQ} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro (h | h | h)
        · left; exact Subtype.ext h
        · right; left; exact Subtype.ext h
        · right; right; exact Subtype.ext h
      · rintro (rfl | rfl | rfl) <;> simp [eQ, uQ, wQ]
    rw [← hk]
    exact Subgroup.closure_closure_coe_preimage
      (k := ({eA8, uA8, wA8} : Set (alternatingGroup (Fin 8))))
  · apply Subtype.ext
    apply Subtype.ext
    simpa [eQ, eA8] using e0_sq
  · apply Subtype.ext
    apply Subtype.ext
    simpa [uQ, uA8] using u0_sq
  · apply Subtype.ext
    apply Subtype.ext
    simpa [wQ, wA8] using w0_sq
  · apply Subtype.ext
    apply Subtype.ext
    simpa [uQ, wQ, uA8, wA8] using uw_comm
  · intro g hg h hh
    have hg' : (↑(↑g) : Equiv.Perm (Fin 8)) ∈ ({1, u0, w0, u0 * w0} : Set _) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
      rcases hg with h | h | h | h
      · left; rw [h]; simp [uQ, wQ, uA8, wA8]
      · right; left; rw [h]; simp [uQ, wQ, uA8, wA8]
      · right; right; left; rw [h]; simp [uQ, wQ, uA8, wA8]
      · right; right; right; rw [h]; simp [uQ, wQ, uA8, wA8]
    have hh' : (↑(↑h) : Equiv.Perm (Fin 8)) ∈ ({1, u0, w0, u0 * w0} : Set _) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh ⊢
      rcases hh with h | h | h | h
      · left; rw [h]; simp [uQ, wQ, uA8, wA8]
      · right; left; rw [h]; simp [uQ, wQ, uA8, wA8]
      · right; right; left; rw [h]; simp [uQ, wQ, uA8, wA8]
      · right; right; right; rw [h]; simp [uQ, wQ, uA8, wA8]
    have hc := conj_comm_perm _ hg' _ hh'
    rw [commute_iff_eq] at hc ⊢
    apply Subtype.ext
    apply Subtype.ext
    exact hc

theorem isA8Type_of_wreathData {P : Type} [Group P] {e u w : P} (h : WreathData P e u w) :
    IsA8Type P := by
  obtain ⟨Q, e', u', w', hQ⟩ := exists_sylow_wreathData
  obtain ⟨φ, -, -, -⟩ := nonempty_mulEquiv_of_wreathData h hQ
  exact ⟨Q, ⟨φ⟩⟩

end CFSG.EvenSporadicStandard.HNRecog.Harada

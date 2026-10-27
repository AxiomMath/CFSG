module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.KappaDDefs
public import Certificates.Certificate561001

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.KappaD

open Matrix Subgroup CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open Certificates.TitsAschbacherParrott CFSG.LocalAnalysis.EvenBN.Tits.Model
open Certificates.KappaD (kappaDCheck actsOK closureOK slList slRows tMat wordOf wordOKb rowsOf
  rowArr bIdx)

namespace Cert

theorem getElem!_ofFn {α : Type*} [Inhabited α] {m : ℕ} (f : Fin m → α) (i : Fin m) :
    (Array.ofFn f)[(i : ℕ)]! = f i := by
  rw [getElem!_pos (Array.ofFn f) (i : ℕ) (by simp), Array.getElem_ofFn]

theorem rep_ofFn_foldr {n m : ℕ} (a : Fin m → Array ℕ) (g : Fin m → Equiv.Perm (Fin n))
    (h : ∀ j, Rep n (a j) (g j)) :
    Rep n ((List.ofFn a).foldr (compA n) (idA n)) (List.ofFn g).prod := by
  induction m with
  | zero => simpa using rep_idA
  | succ m ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.foldr_cons, List.prod_cons]
    exact rep_compA (h 0) (ih (fun j => a j.succ) (fun j => g j.succ) fun j => h j.succ)

section F

theorem pbasis_eq (j : Fin 5) : pbasis j = parrottV (bIdx j) := by
  fin_cases j <;> rfl

theorem pbasis_commute (i j : Fin 5) : pbasis i * pbasis j = pbasis j * pbasis i := by
  have key : ∀ i j : Fin 5, 1 ≤ bIdx i ∧ bIdx i ≤ 12 ∧ 1 ≤ bIdx j ∧ bIdx j ≤ 12 ∧
      listed (bIdx i) (bIdx j) = false ∧ listed (bIdx j) (bIdx i) = false := by decide
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := key i j
  rw [pbasis_eq, pbasis_eq]
  exact parrottV_commute h1 h2 h3 h4 h5 h6

theorem pbasis_sq (i : Fin 5) : pbasis i * pbasis i = 1 := by
  have key : ∀ i : Fin 5, 1 ≤ bIdx i ∧ bIdx i ≤ 12 ∧ bIdx i ∉ ({1, 4, 5, 6} : Finset ℕ) := by
    decide
  obtain ⟨h1, h2, h3⟩ := key i
  rw [pbasis_eq]
  exact parrott_squares.2.2.2.2 _ h1 h2 h3

theorem rep_pbasis (i : Fin 5) : Rep 1755 (vA (bIdx i)) (pbasis i) := by
  rw [pbasis_eq]
  have key : ∀ i : Fin 5, bIdx i < 13 := by decide
  exact rep_vA (key i)

theorem rep_rowArr (M : Mat5) (i : Fin 5) :
    Rep 1755 (rowArr M i) (List.ofFn fun k => pbasis k ^ (M i k).val).prod :=
  Cert.rep_ofFn_foldr _ _ fun k => rep_powA (rep_pbasis k) _

noncomputable def pw (n : Fin 5 → ZMod 2) : Equiv.Perm (Fin 1755) :=
  (List.ofFn fun j => pbasis j ^ (n j).val).prod

theorem pw_add (n n' : Fin 5 → ZMod 2) : pw (n + n') = pw n * pw n' :=
  ofFn_prod_pow_add pbasis pbasis_commute pbasis_sq n n'

theorem pw_zero : pw 0 = 1 := by
  simp [pw]

theorem pw_single_one (j : Fin 5) : pw (Pi.single j 1) = pbasis j := by
  have h1 : (1 : ZMod 2).val = 1 := rfl
  fin_cases j <;> simp [pw, List.ofFn_succ, Pi.single_apply, h1]

theorem conj_pw_single {π : Equiv.Perm (Fin 1755)} {M : Mat5}
    (h : ∀ i, π * pbasis i * π⁻¹ = pw (M i)) (j : Fin 5) (c : ZMod 2) :
    π * pw (Pi.single j c) * π⁻¹ = pw (Pi.single j c ᵥ* M) := by
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
  · simp [pw_zero]
  · rw [pw_single_one, Matrix.single_one_vecMul]
    exact h j

theorem conj_pw {π : Equiv.Perm (Fin 1755)} {M : Mat5}
    (h : ∀ i, π * pbasis i * π⁻¹ = pw (M i)) (n : Fin 5 → ZMod 2) :
    π * pw n * π⁻¹ = pw (n ᵥ* M) := by
  have hQ : ∀ a b : Fin 5 → ZMod 2, π * pw a * π⁻¹ = pw (a ᵥ* M) →
      π * pw b * π⁻¹ = pw (b ᵥ* M) → π * pw (a + b) * π⁻¹ = pw ((a + b) ᵥ* M) := by
    intro a b ha hb
    rw [pw_add, Matrix.add_vecMul, pw_add, ← ha, ← hb]
    group
  have hn : n = Pi.single (0 : Fin 5) (n 0) + Pi.single (1 : Fin 5) (n 1) +
      Pi.single (2 : Fin 5) (n 2) + Pi.single (3 : Fin 5) (n 3) + Pi.single (4 : Fin 5) (n 4) := by
    ext j
    fin_cases j <;> simp [Pi.single_apply]
  have key := hQ _ _ (hQ _ _ (hQ _ _ (hQ _ _ (conj_pw_single h 0 (n 0)) (conj_pw_single h 1 (n 1)))
    (conj_pw_single h 2 (n 2))) (conj_pw_single h 3 (n 3))) (conj_pw_single h 4 (n 4))
  rwa [← hn] at key

theorem acts_one : Acts 1 (1 : Mat5) := by
  intro i
  show 1 * pbasis i * 1⁻¹ = pw ((1 : Mat5) i)
  have h1 : (1 : Mat5) i = Pi.single i 1 := by
    ext j
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [h1, pw_single_one]
  simp

theorem acts_mul {π π' : Equiv.Perm (Fin 1755)} {M M' : Mat5} (h : Acts π M) (h' : Acts π' M') :
    Acts (π * π') (M' * M) := by
  intro i
  have e : π * π' * pbasis i * (π * π')⁻¹ = π * (π' * pbasis i * π'⁻¹) * π⁻¹ := by group
  show π * π' * pbasis i * (π * π')⁻¹ = pw ((M' * M) i)
  have hrow : (M' * M) i = M' i ᵥ* M := by
    ext k
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  rw [e, hrow, show π' * pbasis i * π'⁻¹ = pw (M' i) from h' i]
  exact conj_pw (fun i => h i) (M' i)

theorem acts_pow {π : Equiv.Perm (Fin 1755)} {M : Mat5} (h : Acts π M) :
    ∀ k : ℕ, Acts (π ^ k) (M ^ k)
  | 0 => by simpa using acts_one
  | k + 1 => by
    rw [pow_succ', pow_succ]
    exact acts_mul h (acts_pow h k)

theorem check_parts :
    (∀ j : Fin 4, ∀ i : Fin 5, actsOK j i = true) ∧
    closureOK (slList ()) (slRows ()) = true ∧
    (∀ e₁ e₂ e₃ d₁ : ZMod 2,
      wordOKb (slRows ()) tMat (wordOf e₁ e₂ e₃ d₁) e₁ e₂ e₃ 1 d₁ (e₃ + 1) 1 = true) := by
  have h := Certificates.certificate561001
  unfold kappaDCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
    true_implies] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, h3⟩

theorem acts_gen (j : Fin 4) :
    Acts (chainGen titsNArrs j) (tMat j) := by
  intro i
  have h := (check_parts.1 j i)
  unfold actsOK conjEqA at h
  have hg := chainGen_N_rep (i := (j : ℕ)) j.2
  have e := eq_of_eqA (rep_compA (rep_rowArr (tMat j) i) hg) (rep_compA hg (rep_pbasis i)) h
  rw [mul_inv_eq_iff_eq_mul]
  exact e.symm

theorem rowsOf_inj {M N : Mat5} (h : rowsOf M = rowsOf N) : M = N := by
  unfold rowsOf at h
  ext i j
  have h1 := List.map_inj_left.1 h i (List.mem_finRange i)
  exact List.map_inj_left.1 h1 j (List.mem_finRange j)

theorem mem_slList_iff {M : Mat5} : rowsOf M ∈ slRows () ↔ M ∈ slList () := by
  unfold slRows
  constructor
  · intro h
    obtain ⟨N, hN, hNM⟩ := List.mem_map.1 h
    rwa [rowsOf_inj hNM] at hN
  · exact List.mem_map_of_mem

theorem slList_facts :
    (1 : Mat5) ∈ slList () ∧ ∀ a ∈ slList (), ∀ j : Fin 4, a * tMat j ∈ slList () := by
  have h2 := check_parts.2.1
  unfold closureOK at h2
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
    true_implies] at h2
  exact ⟨mem_slList_iff.1 h2.1, fun a ha j => mem_slList_iff.1 (h2.2 a ha j)⟩

theorem closure_subset_slList :
    ∀ M ∈ Submonoid.closure (Set.range tMat), M ∈ slList () := by
  intro M hM
  induction hM using Submonoid.closure_induction_right with
  | one => exact slList_facts.1
  | mul_right x _ y hy ih =>
    obtain ⟨j, rfl⟩ := hy
    exact slList_facts.2 x ih j

theorem exists_acts_of_mem_titsN :
    ∀ π ∈ titsN, ∃ M ∈ (Submonoid.closure (Set.range tMat) : Set Mat5), Acts π M := by
  intro π hπ
  rw [titsN_eq_closure_chainGen] at hπ
  induction hπ using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact ⟨tMat j, Submonoid.subset_closure ⟨j, rfl⟩, acts_gen j⟩
  | one => exact ⟨1, Submonoid.one_mem _, acts_one⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨M, hM, hx⟩ := ihx
    obtain ⟨M', hM', hy⟩ := ihy
    exact ⟨M' * M, Submonoid.mul_mem _ hM' hM, acts_mul hx hy⟩
  | inv x _ ih =>
    obtain ⟨M, hM, hx⟩ := ih
    refine ⟨M ^ (orderOf x - 1), Submonoid.pow_mem _ hM _, ?_⟩
    have hpos : 0 < orderOf x := orderOf_pos x
    have hinv : x⁻¹ = x ^ (orderOf x - 1) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ' x (orderOf x - 1), Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
    rw [hinv]
    exact acts_pow hx _

end F

end Cert

theorem prodRevS_toMat (ls : List Mat6) :
    (Certificates.KappaD.prodRevS ls).toMat = prodRev ls := by
  have hofMat : ∀ M : Mat6, (Certificates.KappaD.Snap6.ofMat M).toMat = M := by
    intro M
    ext i j
    simp only [Certificates.KappaD.Snap6.toMat, Certificates.KappaD.Snap6.ofMat, Matrix.of_apply]
    rw [Cert.getElem!_ofFn, Cert.getElem!_ofFn]
  induction ls with
  | nil => exact hofMat 1
  | cons a l ih =>
    show (Certificates.KappaD.Snap6.ofMat ((Certificates.KappaD.prodRevS l).toMat * a)).toMat =
      prodRev l * a
    rw [hofMat, ih]

theorem letterMat_eq (e₁ e₂ e₃ e₄ d₁ d₂ d₃ : ZMod 2) (T : Fin 4 → Mat5) :
    Certificates.KappaD.letterMat e₁ e₂ e₃ e₄ d₁ d₂ d₃ T = letterMat e₁ e₂ e₃ e₄ d₁ d₂ d₃ T := by
  funext l
  cases l <;> rfl

section

theorem wordOK_of_check (e₁ e₂ e₃ d₁ : ZMod 2) :
    WordOK (Submonoid.closure (Set.range tMat) : Set Mat5) tMat (wordOf e₁ e₂ e₃ d₁)
      e₁ e₂ e₃ 1 d₁ (e₃ + 1) 1 := by
  have h := Cert.check_parts.2.2 e₁ e₂ e₃ d₁
  unfold wordOKb at h
  simp only [letterMat_eq, prodRevS_toMat, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    true_implies, beq_iff_eq, Bool.not_eq_true', decide_eq_false_iff_not] at h
  exact ⟨h.1, fun hmem => h.2 (Cert.mem_slList_iff.2 (Cert.closure_subset_slList _ hmem))⟩

theorem kappaD_model_facts :
    ∃ (τ : Fin 4 → Equiv.Perm (Fin 1755)) (T : Fin 4 → Mat5) (SL : Set Mat5)
      (words : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 → List Letter),
      (∀ j, τ j ∈ titsN) ∧ (∀ j, Acts (τ j) (T j)) ∧ (∀ π ∈ titsN, ∃ M ∈ SL, Acts π M) ∧
      (∀ e₁ e₂ e₃ d₁, WordOK SL T (words e₁ e₂ e₃ d₁) e₁ e₂ e₃ 1 d₁ (e₃ + 1) 1) :=
  ⟨fun j => chainGen titsNArrs j, tMat, (Submonoid.closure (Set.range tMat) : Set Mat5), wordOf,
    fun j => chainGen_N_mem j.2, Cert.acts_gen, Cert.exists_acts_of_mem_titsN, wordOK_of_check⟩

end

end CFSG.LocalAnalysis.EvenBN.Tits.N.KappaD

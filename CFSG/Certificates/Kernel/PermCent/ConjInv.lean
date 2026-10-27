module

public import CFSG.Certificates.Kernel.PermCent.KGrpC3Sound

public section

namespace CFSG.Certificates.Kernel.PkCV.ConjInv

open CFSG.GH74.E2 CFSG.ClassicalInvolution.Q3.TA3.Check CFSG.Certificates.Kernel.PkCV.KGrp

section Congr

variable {M : Type*}

theorem all_congr_mem {C D : List M} (h : ∀ x, x ∈ C ↔ x ∈ D) (p : M → Bool) :
    C.all p = D.all p := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  simp only [h]

theorem any_congr_mem {C D : List M} (h : ∀ x, x ∈ C ↔ x ∈ D) (p : M → Bool) :
    C.any p = D.any p := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  simp only [h]

theorem all_filter_congr_mem {C D : List M} (h : ∀ x, x ∈ C ↔ x ∈ D) (q p : M → Bool) :
    (C.filter q).all p = (D.filter q).all p :=
  all_congr_mem (fun x => by simp only [List.mem_filter, h]) p

variable [Group M] [DecidableEq M]

theorem noOddB_congr {C D : List M} (h : ∀ x, x ∈ C ↔ x ∈ D) (B : ℕ) :
    noOddB B C = noOddB B D := by
  unfold noOddB
  simp only [all_congr_mem h, any_congr_mem h]

theorem pairsB_congr {C D : List M} (h : ∀ x, x ∈ C ↔ x ∈ D) (t : M) :
    pairsB t C = pairsB t D := by
  unfold pairsB
  simp only [all_filter_congr_mem h, all_congr_mem h, any_congr_mem h]

theorem conj_mem_list (A : Subgroup M) {L : List M} (hL : ∀ x, x ∈ L ↔ x ∈ A) {g : M}
    (hg : g ∈ A) : (∀ x ∈ L, g * x * g⁻¹ ∈ L) ∧ ∀ x ∈ L, g⁻¹ * x * g ∈ L :=
  ⟨fun x hx => (hL _).2 (A.mul_mem (A.mul_mem hg ((hL x).1 hx)) (A.inv_mem hg)),
    fun x hx => (hL _).2 (A.mul_mem (A.mul_mem (A.inv_mem hg) ((hL x).1 hx)) hg)⟩

theorem mem_centB_conj {L : List M} {g : M} (h1 : ∀ x ∈ L, g * x * g⁻¹ ∈ L)
    (h2 : ∀ x ∈ L, g⁻¹ * x * g ∈ L) (t x : M) :
    x ∈ centB L ((MulAut.conj g).toMonoidHom t) ↔
      x ∈ (centB L t).map (MulAut.conj g).toMonoidHom := by
  simp only [centB, List.mem_filter, List.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hx, e⟩
    have e := of_decide_eq_true e
    refine ⟨g⁻¹ * x * g, ⟨h2 x hx, decide_eq_true ?_⟩, by group⟩
    calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * t * g⁻¹ * x) * g := by rw [e]
      _ = t * (g⁻¹ * x * g) := by group
  · rintro ⟨y, ⟨hy, e⟩, rfl⟩
    have e := of_decide_eq_true e
    refine ⟨h1 y hy, decide_eq_true ?_⟩
    calc g * y * g⁻¹ * (g * t * g⁻¹) = g * (y * t) * g⁻¹ := by group
      _ = g * (t * y) * g⁻¹ := by rw [e]
      _ = g * t * g⁻¹ * (g * y * g⁻¹) := by group

end Congr

section Good

variable {M : Type*} [Group M] [DecidableEq M]

@[expose] def goodAt (B : ℕ) (L : List M) (t : M) : Bool :=
  noOddB B (centB L t) && pairsB t (centB L t)

theorem goodAt_conj {L : List M} {g : M} (h1 : ∀ x ∈ L, g * x * g⁻¹ ∈ L)
    (h2 : ∀ x ∈ L, g⁻¹ * x * g ∈ L) (B : ℕ) (t : M) :
    goodAt B L (g * t * g⁻¹) = goodAt B L t := by
  have hf : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have e : g * t * g⁻¹ = (MulAut.conj g).toMonoidHom t := rfl
  rw [goodAt, goodAt, e, noOddB_congr (mem_centB_conj h1 h2 t), pairsB_congr
    (mem_centB_conj h1 h2 t), noOddB_map _ hf, pairsB_map _ hf]

theorem goodCheck_of_invol (A : Subgroup M) {L : List M} (hL : ∀ x, x ∈ L ↔ x ∈ A) (B : ℕ)
    (h : ∀ t ∈ A, t ^ 2 = 1 → t ≠ 1 → goodAt B L t = true) : goodCheck B L = true := by
  unfold goodCheck
  rw [List.all_eq_true]
  intro t ht
  by_cases hi : t * t = 1 ∧ t ≠ 1
  · have h' := h t ((hL t).1 ht) (by rw [sq]; exact hi.1) hi.2
    have hd : decide (t * t = 1 ∧ t ≠ 1) = true := decide_eq_true hi
    rw [goodAt] at h'
    simp only [hd, h', Bool.not_true, Bool.false_or]
  · have hd : decide (t * t = 1 ∧ t ≠ 1) = false := decide_eq_false hi
    simp only [hd, Bool.not_false, Bool.true_or]

end Good

section Q8C2

variable {n : ℕ}

@[expose] def q8c2At (L : List (Equiv.Perm (Fin n))) (c : Equiv.Perm (Fin n)) : Bool :=
  q8c2at c (centB L c)

theorem q8c2at_map (f : Equiv.Perm (Fin n) →* Equiv.Perm (Fin n)) (hf : Function.Injective f)
    (c : Equiv.Perm (Fin n)) (C : List (Equiv.Perm (Fin n))) :
    q8c2at (f c) (C.map f) = q8c2at c C := by
  unfold q8c2at
  simp only [List.all_map, Function.comp_def, ← map_pow, ← map_mul, ← map_inv,
    map_eq_one_iff f hf, ne_eq, hf.eq_iff]

theorem q8c2at_congr (c : Equiv.Perm (Fin n)) {C D : List (Equiv.Perm (Fin n))}
    (h : ∀ x, x ∈ C ↔ x ∈ D) : q8c2at c C = q8c2at c D := by
  unfold q8c2at
  simp only [all_congr_mem h]

theorem q8c2At_conj (A : Subgroup (Equiv.Perm (Fin n))) {L : List (Equiv.Perm (Fin n))}
    (hL : ∀ x, x ∈ L ↔ x ∈ A) {g : Equiv.Perm (Fin n)} (hg : g ∈ A) (c : Equiv.Perm (Fin n)) :
    q8c2At L (g * c * g⁻¹) = q8c2At L c := by
  have hf : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have e : g * c * g⁻¹ = (MulAut.conj g).toMonoidHom c := rfl
  obtain ⟨h1, h2⟩ := conj_mem_list A hL hg
  rw [q8c2At, q8c2At, e, q8c2at_congr _ (mem_centB_conj h1 h2 c), q8c2at_map _ hf]

theorem q8c2free_of_invol (A : Subgroup (Equiv.Perm (Fin n))) {L : List (Equiv.Perm (Fin n))}
    (hL : ∀ x, x ∈ L ↔ x ∈ A) (h : ∀ c ∈ A, c ^ 2 = 1 → c ≠ 1 → q8c2At L c = true) :
    q8c2free L = true := by
  unfold q8c2free
  rw [List.all_eq_true]
  intro c hc
  by_cases hi : c ^ 2 = 1 ∧ c ≠ 1
  · have h' := h c ((hL c).1 hc) hi.1 hi.2
    have hd : (decide (c ^ 2 = 1) && decide (c ≠ 1)) = true := by
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      exact hi
    rw [q8c2At, centB] at h'
    rw [hd, cond_true]
    exact h'
  · have hd : (decide (c ^ 2 = 1) && decide (c ≠ 1)) = false := by
      rw [← Bool.not_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      exact hi
    rw [hd, cond_false]

end Q8C2

end CFSG.Certificates.Kernel.PkCV.ConjInv

end

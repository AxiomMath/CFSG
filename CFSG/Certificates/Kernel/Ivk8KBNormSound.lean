module

public import Certificates.Data.Kernel.Ivk8KBNorm
public import CFSG.Certificates.Kernel.Ivk8NormSound

public section

namespace CFSG.KS.Ivk8KBNorm

open CFSG.Certificates.Kernel.PkEnum CFSG.KS.PK CFSG.KS.Ivk8Norm

variable {n : Nat}

theorem notInV_cons (x y : VP n) (ys : List (VP n)) :
    notInV x (y :: ys) = (difV x y && notInV x ys) := by
  change Bool.rec (motive := fun _ => Bool) false (notInV x ys) (difV x y) = _
  cases difV x y <;> rfl

theorem notInV_iff (x : VP n) (L : List (VP n)) : notInV x L = true ↔ pkp x ∉ L.map pkp := by
  induction L with
  | nil => simp only [List.map_nil, List.not_mem_nil, not_false_eq_true, iff_true]; rfl
  | cons y ys ih =>
    rw [notInV_cons, Bool.and_eq_true, ih, difV_eq_true_iff, List.map_cons, List.mem_cons,
      not_or]

theorem distinctV_cons (x : VP n) (xs : List (VP n)) :
    distinctV (x :: xs) = (notInV x xs && distinctV xs) := by
  change Bool.rec (motive := fun _ => Bool) false (distinctV xs) (notInV x xs) = _
  cases notInV x xs <;> rfl

theorem distinctV_nodup {L : List (VP n)} (h : distinctV L = true) : (L.map pkp).Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    rw [distinctV_cons, Bool.and_eq_true] at h
    rw [List.map_cons, List.nodup_cons]
    exact ⟨(notInV_iff x xs).1 h.1, ih h.2⟩

theorem conjsV_cons (d c : VP n) (cs : List (VP n)) :
    conjsV d (c :: cs) = conjV c d :: conjsV d cs := rfl

theorem conjsV_map (d : VP n) (cs : List (VP n)) :
    (conjsV d cs).map pkp = cs.map fun c => pkp c * pkp d * (pkp c)⁻¹ := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [conjsV_cons, List.map_cons, List.map_cons, ih, pkp_conjV]

theorem cubeNe_iff (w : VP n) : cubeNe w = true ↔ pkp w ^ 3 ≠ 1 := by
  rw [cubeNe, difV_eq_true_iff, pkp_mulV, pkp_mulV, pkp_oneV, pow_three]

theorem fixOK_cons (d : VP n) (E : List (VP n)) (z : VP n) (K : List (VP n)) :
    fixOK d E (z :: K) = (fixZ d E z && fixOK d E K) := by
  change Bool.rec (motive := fun _ => Bool) false (fixOK d E K) (fixZ d E z) = _
  cases fixZ d E z <;> rfl

theorem fixZ_spec {d : VP n} {E : List (VP n)} {z : VP n} (h : fixZ d E z = true)
    (h3 : pkp z ^ 3 = 1) (h1 : pkp z ≠ 1) (hE : pkp z ∉ E.map pkp) :
    (pkp z * (pkp d * pkp z * (pkp d)⁻¹)) ^ 3 ≠ 1 := by
  have c3 : cubeNe z = false := by
    cases hc : cubeNe z
    · rfl
    · exact absurd h3 ((cubeNe_iff z).1 hc)
  have c1 : difV z (oneV n) = true := by
    rw [difV_eq_true_iff, pkp_oneV]
    exact h1
  have cE : notInV z E = true := (notInV_iff z E).2 hE
  rw [fixZ, c3, c1, cE] at h
  have h2 := (cubeNe_iff _).1 h
  rwa [pkp_mulV, pkp_conjV] at h2

theorem fixOK_spec {d : VP n} {E K : List (VP n)} (h : fixOK d E K = true) :
    ∀ σ ∈ K.map pkp, σ ^ 3 = 1 → σ ≠ 1 → σ ∉ E.map pkp →
      (σ * (pkp d * σ * (pkp d)⁻¹)) ^ 3 ≠ 1 := by
  induction K with
  | nil => intro σ hσ; simp at hσ
  | cons z K ih =>
    rw [fixOK_cons, Bool.and_eq_true] at h
    intro σ hσ
    rw [List.map_cons, List.mem_cons] at hσ
    rcases hσ with rfl | hσ
    · exact fixZ_spec h.1
    · exact ih h.2 σ hσ

end CFSG.KS.Ivk8KBNorm

end

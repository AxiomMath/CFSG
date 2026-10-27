module

public import CFSG.GH74.KGroups.NativeChecks

public section

namespace CFSG.ComponentClassification.CatFactsSmall

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.KGroups.Native CFSG.Certificates
  CFSG.Sporadic.Schreier CFSG.GH74.KGroups CFSG.GH74.KGroups.NativeChecks

variable {n : ℕ}

theorem eqA_toA_iff (σ τ : Equiv.Perm (Fin n)) : eqA n (toA σ) (toA τ) = true ↔ σ = τ :=
  eqA_iff (rep_toA σ) (rep_toA τ)

theorem eqA_comm_iff (σ τ : Equiv.Perm (Fin n)) :
    eqA n (compA n (toA σ) (toA τ)) (compA n (toA τ) (toA σ)) = true ↔ σ * τ = τ * σ :=
  eqA_iff (rep_compA (rep_toA σ) (rep_toA τ)) (rep_compA (rep_toA τ) (rep_toA σ))

@[expose, noinline] def pairWitnessA (n : ℕ) (C : List (Array ℕ)) (m : ℕ) : Bool :=
  C.any fun x₁ => C.any fun x₂ => !(eqA n (powA n (compA n x₁ x₂) m) (idA n))

@[expose, noinline] def noNilpA (n : ℕ) (LA odd : List (Array ℕ)) (m : ℕ) : Bool :=
  LA.all fun s => !(eqA n (compA n s s) (idA n)) ||
    pairWitnessA n (odd.filter fun x => eqA n (compA n x s) (compA n s x)) m

theorem noNilpA_sound {LA odd : List (Equiv.Perm (Fin n))} {m : ℕ}
    (h : noNilpA n (LA.map toA) (odd.map toA) m = true) {s : Equiv.Perm (Fin n)} (hs : s ∈ LA)
    (hs2 : s * s = 1) :
    ∃ x₁ ∈ odd, ∃ x₂ ∈ odd, x₁ * s = s * x₁ ∧ x₂ * s = s * x₂ ∧ (x₁ * x₂) ^ m ≠ 1 := by
  have h1 := List.all_eq_true.1 h (toA s) (List.mem_map_of_mem hs)
  have hss : eqA n (compA n (toA s) (toA s)) (idA n) = true :=
    (eqA_iff (rep_compA (rep_toA s) (rep_toA s)) (rep_idA (n := n))).2 hs2
  rw [hss, Bool.not_true, Bool.false_or, pairWitnessA, List.any_eq_true] at h1
  obtain ⟨a₁, ha₁, h2⟩ := h1
  rw [List.any_eq_true] at h2
  obtain ⟨a₂, ha₂, h3⟩ := h2
  rw [List.mem_filter, List.mem_map] at ha₁ ha₂
  obtain ⟨⟨x₁, hx₁, rfl⟩, hc₁⟩ := ha₁
  obtain ⟨⟨x₂, hx₂, rfl⟩, hc₂⟩ := ha₂
  refine ⟨x₁, hx₁, x₂, hx₂, (eqA_comm_iff x₁ s).1 hc₁, (eqA_comm_iff x₂ s).1 hc₂, fun he => ?_⟩
  have h4 : eqA n (powA n (compA n (toA x₁) (toA x₂)) m) (idA n) = true :=
    (eqA_iff (rep_powA (rep_compA (rep_toA x₁) (rep_toA x₂)) m) (rep_idA (n := n))).2 he
  rw [h4] at h3
  exact absurd h3 (by decide)

@[expose, noinline] def admCheckA (LA : List (Equiv.Perm (Fin n))) (QP : RawSchreierDatum n)
    (L5 : List (Array ℕ)) (s₀ : Equiv.Perm (Fin n)) (cs : List (Equiv.Perm (Fin n))) : Bool :=
  LA.all fun s =>
    let a := toA s
    !(eqA n (compA n a a) (idA n)) ||
      (L5.all fun x => !(eqA n (compA n x a) (compA n a x))) || QP.sift s 0 ||
      cs.any fun k => decide (k * s₀ * k⁻¹ = s)

theorem exists_conj_of_admCheckA {LA : List (Equiv.Perm (Fin n))} {QP : RawSchreierDatum n}
    (hQP : ValidSchreier QP) {L5 : List (Equiv.Perm (Fin n))} {s₀ : Equiv.Perm (Fin n)}
    {cs : List (Equiv.Perm (Fin n))} (h : admCheckA LA QP (L5.map toA) s₀ cs = true)
    {s : Equiv.Perm (Fin n)} (hs : s ∈ LA) (hs2 : s * s = 1) (hsP : s ∉ QP.originalSubgroup)
    {x : Equiv.Perm (Fin n)} (hx : x ∈ L5) (hxs : x * s = s * x) :
    ∃ k ∈ cs, k * s₀ * k⁻¹ = s := by
  have h1 := List.all_eq_true.1 h s hs
  have hss : eqA n (compA n (toA s) (toA s)) (idA n) = true :=
    (eqA_iff (rep_compA (rep_toA s) (rep_toA s)) (rep_idA (n := n))).2 hs2
  have hL5 : (L5.map toA).all (fun y => !(eqA n (compA n y (toA s)) (compA n (toA s) y))) =
      false := by
    rw [List.all_eq_false]
    exact ⟨toA x, List.mem_map_of_mem hx, by simp [(eqA_comm_iff x s).2 hxs]⟩
  have hsift : QP.sift s 0 = false := by
    by_contra hne
    exact hsP ((mem_iff_sift QP hQP s).2 (by simpa using hne))
  simp only [hss, hL5, hsift, Bool.not_true, Bool.false_or, List.any_eq_true,
    decide_eq_true_eq] at h1
  exact h1

end CFSG.ComponentClassification.CatFactsSmall

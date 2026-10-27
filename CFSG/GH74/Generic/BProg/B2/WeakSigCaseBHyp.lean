module

public import CFSG.GH74.Generic.BProg.B2.WeakSigCaseBAux

public section

namespace CFSG.GH74.Generic.BProg.B2.WeakSigCaseB

open CFSG Subgroup CFSG.GH74.Generic.BProg.B2.WeakSigGen

section Hyp

variable {Y : Type} [Group Y]

theorem inv_eq_self_of_mul_self {s : Y} (hss : s * s = 1) : s⁻¹ = s :=
  inv_eq_of_mul_eq_one_right hss

theorem comm_conj_self [Finite Y] {L : Subgroup Y} (hL : IsComponent L) {s' c : Y}
    (hss : s' * s' = 1) (hs : s' ∉ normalizer (L : Set Y)) (hc : c ∈ L) :
    c * (s' * c * s'⁻¹) = (s' * c * s'⁻¹) * c := by
  have hne : L ≠ conjugate L s' := fun h => hs (conjugate_eq_self_iff.mp h.symm)
  have hinv := inv_eq_self_of_mul_self hss
  have hy : s' * c * s'⁻¹ ∈ conjugate L s' := by
    rw [mem_conjugate_iff, hinv]
    have : s' * (s' * c * s') * s' = c := by
      calc s' * (s' * c * s') * s' = (s' * s') * c * (s' * s') := by group
        _ = c := by rw [hss]; simp
    rw [this]; exact hc
  exact commute_of_ne hL (isComponent_conjugate hL s') hne c hc _ hy

theorem commute_xel [Finite Y] {L : Subgroup Y} (hL : IsComponent L) {s' c : Y}
    (hss : s' * s' = 1) (hs : s' ∉ normalizer (L : Set Y)) (hc : c ∈ L) :
    s' * (c * (s' * c * s'⁻¹)) = (c * (s' * c * s'⁻¹)) * s' := by
  have hcomm := comm_conj_self hL hss hs hc
  have hinv := inv_eq_self_of_mul_self hss
  rw [hinv] at hcomm ⊢
  calc s' * (c * (s' * c * s')) = s' * ((s' * c * s') * c) := by rw [hcomm]
    _ = (s' * s') * c * s' * c := by group
    _ = c * s' * c := by rw [hss]; simp
    _ = c * s' * c * (s' * s') := by rw [hss]; simp
    _ = c * (s' * c * s') * s' := by group

theorem x_mem_normalizer [Finite Y] {L D W E₀ : Subgroup Y} {s c : Y} (hL : IsComponent L)
    (hD : CFSG.IsElementaryAbelian 2 ↥D) (hss : s * s = 1) (hsD : s ∈ D)
    (hs : s ∉ normalizer (L : Set Y)) (hE₀ : E₀ ≤ D ⊓ normalizer (L : Set Y))
    (hrank : pRank 2 ↥D ≤ pRank 2 ↥E₀ + 2)
    (hC : ∀ E : Subgroup Y, E ≤ D → pRank 2 ↥D - 1 ≤ pRank 2 ↥E →
      centralizer (E : Set Y) ≤ normalizer (W : Set Y))
    (hc : c ∈ L) (hcE : c ∈ centralizer (E₀ : Set Y)) :
    c * (s * c * s⁻¹) ∈ normalizer (W : Set Y) := by
  have hE₀D : E₀ ≤ D := fun e he => (hE₀ he).1
  have hsE : s ∉ E₀ := fun h => hs (hE₀ h).2
  obtain ⟨hle, hr⟩ := sup_zpowers_rank hD hE₀D hsD hsE
  have hCW := hC (E₀ ⊔ Subgroup.zpowers s) hle (by omega)
  apply hCW
  set x : Y := c * (s * c * s⁻¹) with hx
  have hle' : E₀ ⊔ Subgroup.zpowers s ≤ Subgroup.centralizer ({x} : Set Y) := by
    refine sup_le (fun e he => ?_) ((Subgroup.zpowers_le).mpr ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have hab := (forall_of_isElementaryAbelian hD).1
      have hes : Commute e s := hab e (hE₀D he) s hsD
      have hec : Commute e c := mem_centralizer_iff.mp hcE e he
      exact (hec.mul_right ((hes.mul_right hec).mul_right hes.inv_right)).eq
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact commute_xel hL hss hs hc
  rw [mem_centralizer_iff]
  intro h hh
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle' hh)

end Hyp

end CFSG.GH74.Generic.BProg.B2.WeakSigCaseB

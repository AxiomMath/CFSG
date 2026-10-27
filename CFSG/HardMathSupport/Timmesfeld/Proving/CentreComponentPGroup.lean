module

public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreConj

public section

namespace CFSG.HardMathSupport.Timmesfeld.Proving

open CFSG.Open

variable {X : Type*} [Group X]

theorem GLAPPrimeCoreOf_le_of_normal_sub {p : ℕ} [Finite X] (hp : p.Prime) {H M : Subgroup X}
    (hHM : H ≤ M) (hn : (H.subgroupOf M).Normal) :
    GLAPPrimeCoreOf p H ≤ GLAPPrimeCoreOf p M := by
  refine le_GLAPPrimeCoreOf_of_normal ((GLAPPrimeCoreOf_le (p := p) H).trans hHM) ?_
    (coprime_card_GLAPPrimeCoreOf hp H)
  intro g hg x hx
  have hconj : ∀ m ∈ M, ∀ h ∈ H, m * h * m⁻¹ ∈ H := by
    intro m hm h hh
    have := hn.conj_mem ⟨h, hHM hh⟩ (Subgroup.mem_subgroupOf.2 hh) ⟨m, hm⟩
    simpa using Subgroup.mem_subgroupOf.1 this
  have hgN : g ∈ Subgroup.normalizer (H : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact hconj g hg h
    · intro hh
      simpa [mul_assoc] using hconj g⁻¹ (M.inv_mem hg) _ hh
  exact GLAPPrimeCoreOf_conj_mem_of_mem_normalizer hp hgN x hx

theorem GLAPPrimeCoreOf_le_of_isSubnormal_sub {p : ℕ} [Finite X] (hp : p.Prime)
    {L C : Subgroup X} (h : IsSubnormal L C) :
    GLAPPrimeCoreOf p L ≤ GLAPPrimeCoreOf p C := by
  induction h with
  | refl => exact le_rfl
  | step hHM hn _ ih => exact (GLAPPrimeCoreOf_le_of_normal_sub hp hHM hn).trans ih

theorem isPGroup_center_of_isComponentOf [Finite X] {p : ℕ} (hp : p.Prime) {L C : Subgroup X}
    (hL : IsComponentOf L C) (hO : GLAPPrimeCoreOf p C = ⊥) :
    IsPGroup p (Subgroup.center ↥L) := by
  rintro ⟨⟨z, hz⟩, hzL⟩
  have hzc : ∀ w ∈ L, w * z = z * w := fun w hw =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 hzL ⟨w, hw⟩)
  suffices h : ∃ k : ℕ, z ^ p ^ k = 1 by
    obtain ⟨k, hk⟩ := h
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  obtain ⟨e, n', hn', hnorder⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (isOfFinOrder_of_finite z).orderOf_pos.ne' p
      hp.one_lt.ne'
  have hyn : (z ^ p ^ e) ^ n' = 1 := by
    rw [← pow_mul, ← hnorder, pow_orderOf_eq_one]
  have hcop : Nat.Coprime p (orderOf (z ^ p ^ e)) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hyn)
      ((Nat.Prime.coprime_iff_not_dvd hp).2 hn')
  have hyL : z ^ p ^ e ∈ L := L.pow_mem hz _
  have hS : Subgroup.zpowers (z ^ p ^ e) ≤ GLAPPrimeCoreOf p L := by
    refine le_GLAPPrimeCoreOf_of_normal (Subgroup.zpowers_le.2 hyL) ?_ ?_
    · intro g hg x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      have hc : Commute g (z ^ p ^ e) :=
        ((show Commute g z from hzc g hg).pow_right _)
      have hck : g * (z ^ p ^ e) ^ k = (z ^ p ^ e) ^ k * g :=
        (hc.zpow_right k).eq
      rw [hck, mul_assoc, mul_inv_cancel, mul_one]
      exact Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩
    · rw [Nat.card_zpowers]
      exact hcop
  have hyC : z ^ p ^ e ∈ GLAPPrimeCoreOf p C :=
    (GLAPPrimeCoreOf_le_of_isSubnormal_sub hp hL.2.1) (hS (Subgroup.mem_zpowers _))
  rw [hO, Subgroup.mem_bot] at hyC
  exact ⟨e, hyC⟩

end CFSG.HardMathSupport.Timmesfeld.Proving

end

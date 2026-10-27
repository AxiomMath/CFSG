module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltHypIIShape
public import CFSG.Quasithin.SteinbergCBAlternatingAut

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoHypIIY
  CFSG.Quasithin.SteinbergCB

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem qWitness_of_not_le (h5 : 5 ≤ Fintype.card α) {E : Subgroup (Perm α)}
    (hE : IsElemAbelian 2 E) (h4 : 4 ≤ Nat.card E) (hEX : ¬ E ≤ alternatingGroup α) :
    QWitness (alternatingGroup α) E := by
  obtain ⟨t, htE, htX⟩ := IsConcreteLE.not_le_iff_exists.mp hEX
  have hsign : sign t ≠ 1 := fun h => htX (mem_alternatingGroup.mpr h)
  have hinv : ∀ x ∈ E, ∀ a, x (x a) = a := fun x hx a => by
    have h := hE.2 x hx
    rw [sq] at h
    rw [← Perm.mul_apply, h, Perm.one_apply]
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, ∀ a, x (y a) = y (x a) := fun x hx y hy a => by
    have h := congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    simp only [Subgroup.coe_mul] at h
    rw [← Perm.mul_apply, h, Perm.mul_apply]
  obtain ⟨s, hsE, hs1, hst⟩ : ∃ s ∈ E, s ≠ 1 ∧ s ≠ t := by
    by_contra h
    push Not at h
    have hle : E ≤ zpowers t := fun s hs => by
      by_cases h1 : s = 1
      · rw [h1]
        exact one_mem _
      · rw [h s hs h1]
        exact mem_zpowers t
    have hcard := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers] at hcard
    have := orderOf_le_of_pow_eq_one two_pos (hE.2 t htE)
    omega
  obtain ⟨p, hp2, hp⟩ := exists_twoOrbit_of_sign_ne_one (hinv t htE) (hinv s hsE)
    (hcomm t htE s hsE) hsign
  have huE : t * s ∈ E := E.mul_mem htE hsE
  rcases hp with hp1 | hp1
  · exact qWitness_of_twoOrbit h5 htE hsE (hinv t htE) (hinv s hsE) (hcomm t htE s hsE) hsign hs1
      hp1 hp2
  · have hu1 : t * s ≠ 1 := fun h => hst (by
      have h' : t * (t * s) = t * 1 := by rw [h]
      rwa [← mul_assoc, ← sq, hE.2 t htE, one_mul, mul_one] at h')
    exact qWitness_of_twoOrbit h5 htE huE (hinv t htE) (hinv _ huE) (hcomm t htE _ huE) hsign
      hu1 (by rw [Perm.mul_apply, hp1, hinv t htE]) hp2

theorem autModel_perm {n : ℕ} (hn : n = 5 ∨ 7 ≤ n) :
    AutModel (alternatingGroup (Fin n)) (Perm (Fin n)) (alternatingGroup (Fin n)) where
  normal := inferInstance
  centralizer_eq_bot := by
    rw [eq_bot_iff]
    intro σ hσ
    rw [mem_bot]
    refine CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup.eq_one_of_forall_commute_alternating
      (by simp only [Fintype.card_fin]; omega) fun g hg => ?_
    exact (mem_centralizer_iff.mp hσ g hg).symm
  nonempty_mulEquiv := ⟨MulEquiv.refl _⟩
  exists_conj := fun φ => by
    obtain ⟨σ, hσ⟩ := conjPerm_surjective hn φ
    exact ⟨σ, fun x => by rw [← hσ, conjPerm_apply]⟩

theorem hypII_of_alternating {n : ℕ} (hn : n = 5 ∨ 7 ≤ n) {A : Type*} [Group A]
    (hA : commutator A = ⊤) (e : A ⧸ center A ≃* alternatingGroup (Fin n)) : HypII A :=
  hypII_of_witness (autModel_perm hn) (fun _ hE h4 hEX => Or.inr
    (not_isTwoNilpotent_of_qWitness (qWitness_of_not_le (by simp only [Fintype.card_fin]; omega)
      hE h4 hEX))) hA e

end CFSG.ComponentClassification.RankTwoAlt

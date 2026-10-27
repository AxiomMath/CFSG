module

public import CFSG.CharacterTheory.Burnside.CharacterObstruction
public import CFSG.GH74.Uniqueness.SU.SU9Cnt

public section

namespace CFSG.GH74.Uniqueness.SU.SU9

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU5 CFSG.GH74.Uniqueness.SU.SU7
  CFSG CFSG.ShultStronglyClosedTI.InvolutionCounting

theorem sec19_false (h192 : Lemma192Stmt) (h194 : Lemma194Stmt)
    (h197 : Lemma197Stmt) : Sec19FalseStmt := by
  have h19AB := lemma19AB
  intro G _ _ S U M V x z h hH hcl
  obtain ⟨A, B, R, hAB⟩ := h19AB G S U M V x z h hH hcl
  have hc : Ctx19 S U M V x z A B R := ⟨hH, h, hcl, hAB⟩
  have hG : Nat.card G = 2 ^ 7 * 3 ^ 4 * 5 := h197 G S U M V x z A B R hc
  obtain ⟨-, hCz⟩ := Cnt.cent_z_facts h192 h194 hc
  have hcard := card_centralizer_mul_card_conjugatesOf z
  rw [hCz, hG] at hcard
  have hclass : Nat.card (ConjClasses.mk z).carrier = 3 ^ 3 := by
    have : (ConjClasses.mk z).carrier = conjugatesOf z := by
      ext y
      rw [ConjClasses.mem_carrier_iff_mk_eq]
      exact ⟨fun h' => (ConjClasses.mk_eq_mk_iff_isConj.1 h').symm, fun h' =>
        ConjClasses.mk_eq_mk_iff_isConj.2 h'.symm⟩
    rw [this]
    omega
  have : Fintype G := Fintype.ofFinite G
  have hsimple : IsSimpleGroup G := hH.simple
  have hnoncomm : ¬ ∀ y z' : G, y * z' = z' * y := by
    intro hall
    obtain ⟨p, q, hpq⟩ := hH.nonab
    exact hpq (hall p q)
  exact Burnside.CharacterObstruction.no_prime_pow_conjClass hnoncomm z (Cfg.z_ne_one hc) 3 3
    Nat.prime_three hclass

end CFSG.GH74.Uniqueness.SU.SU9

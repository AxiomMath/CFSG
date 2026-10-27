module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Trans
public import CFSG.ClassicalInvolution.Orders.Classical

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem aux_odd_card_oddCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := X)]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

private theorem aux_map_oddCore_le {G H : Type} [Group G] [Group H] [Finite G]
    (f : G →* H) (hf : Function.Surjective f) :
    (CFSG.oddCore G).map f ≤ CFSG.oddCore H := by
  have hn : ((CFSG.oddCore G).map f).Normal :=
    (inferInstance : (CFSG.oddCore G).Normal).map f hf
  have hodd : Odd (Nat.card ((CFSG.oddCore G).map f)) :=
    (aux_odd_card_oddCore G).of_dvd_nat
      (Subgroup.card_dvd_of_surjective (f.subgroupMap_surjective (CFSG.oddCore G)))
  exact le_sSup ⟨hn, hodd⟩

private theorem aux_prod_oddCore_le (A B : Type*) [Group A] [Group B] [Finite A] [Finite B] :
    (CFSG.oddCore A).prod (CFSG.oddCore B) ≤ CFSG.oddCore (A × B) := by
  have hn : ((CFSG.oddCore A).prod (CFSG.oddCore B)).Normal := inferInstance
  have hodd : Odd (Nat.card ((CFSG.oddCore A).prod (CFSG.oddCore B))) := by
    rw [Nat.card_congr (Subgroup.prodEquiv (CFSG.oddCore A) (CFSG.oddCore B)).toEquiv,
      Nat.card_prod]
    exact (aux_odd_card_oddCore A).mul (aux_odd_card_oddCore B)
  exact le_sSup ⟨hn, hodd⟩

theorem card_of_isTwoU43 {Q : Type} [Group Q] [Finite Q] (h : IsTwoU43 Q) :
    Nat.card Q = 6531840 := by
  unfold IsTwoU43 at h
  obtain ⟨hcenter, hmodel⟩ := h
  have hq : Nat.card (Q ⧸ center Q) = 3265920 := by
    rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Q ⧸ center Q)
      (show (3 : ℕ) ≠ 2 by norm_num)
      (hmodel.statedClassicalModel_of_ne_zero (by norm_num))).2.1 rfl]
    decide +kernel
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center Q), hq, hcenter]

theorem card_quotient_oddCore_eq_of_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') :
    Nat.card (Q ⧸ oddCore Q) = Nat.card (Q' ⧸ oddCore Q') := by
  obtain ⟨e'⟩ := nonempty_quotient_oddCore_mulEquiv e
  exact Nat.card_congr e'.toEquiv

theorem card_quotient_oddCore_conjugate (X : Subgroup G) (g : G) :
    Nat.card (CFSG.conjugate X g ⧸ oddCore (CFSG.conjugate X g)) =
      Nat.card (X ⧸ oddCore X) := by
  have hX : CFSG.conjugate X g = X.map (MulAut.conj g⁻¹).toMonoidHom := rfl
  rw [hX]
  exact (card_quotient_oddCore_eq_of_mulEquiv
    (Subgroup.equivMapOfInjective X (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective)).symm

theorem card_quotient_oddCore_sup_dvd [Finite G] {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Nat.card ((A ⊔ B : Subgroup G) ⧸ oddCore (A ⊔ B : Subgroup G)) ∣
      Nat.card (A ⧸ oddCore A) * Nat.card (B ⧸ oddCore B) := by
  let f : ↥A × ↥B →* ↥(A ⊔ B) :=
    { toFun := fun x => ⟨(x.1 : G) * (x.2 : G), mul_mem_sup x.1.2 x.2.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        change ((x.1 : G) * (y.1 : G)) * ((x.2 : G) * (y.2 : G)) =
          ((x.1 : G) * (x.2 : G)) * ((y.1 : G) * (y.2 : G))
        calc ((x.1 : G) * (y.1 : G)) * ((x.2 : G) * (y.2 : G))
            = (x.1 : G) * ((y.1 : G) * (x.2 : G)) * (y.2 : G) := by group
          _ = (x.1 : G) * ((x.2 : G) * (y.1 : G)) * (y.2 : G) := by
                rw [h y.1 y.1.2 x.2 x.2.2]
          _ = ((x.1 : G) * (x.2 : G)) * ((y.1 : G) * (y.2 : G)) := by group) }
  have hf : Function.Surjective f := by
    have htop : A.subgroupOf (A ⊔ B) ⊔ B.subgroupOf (A ⊔ B) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    apply MonoidHom.range_eq_top.mp
    rw [eq_top_iff, ← htop]
    apply sup_le
    · rintro a ha
      exact ⟨(⟨(a : G), ha⟩, 1), Subtype.ext (by simp [f])⟩
    · rintro b hb
      exact ⟨(1, ⟨(b : G), hb⟩), Subtype.ext (by simp [f])⟩
  let Φ : ↥A × ↥B →* (↥(A ⊔ B) ⧸ oddCore ↥(A ⊔ B)) :=
    (QuotientGroup.mk' (oddCore ↥(A ⊔ B))).comp f
  have hΦsurj : Function.Surjective Φ :=
    (QuotientGroup.mk'_surjective (oddCore ↥(A ⊔ B))).comp hf
  have hker : (oddCore ↥A).prod (oddCore ↥B) ≤ Φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxO : x ∈ oddCore (↥A × ↥B) := aux_prod_oddCore_le ↥A ↥B hx
    have hmap : f x ∈ (oddCore (↥A × ↥B)).map f := Subgroup.mem_map_of_mem f hxO
    have hle : (oddCore (↥A × ↥B)).map f ≤ oddCore ↥(A ⊔ B) := aux_map_oddCore_le f hf
    have hfx : f x ∈ oddCore ↥(A ⊔ B) := hle hmap
    change (QuotientGroup.mk' (oddCore ↥(A ⊔ B))) (f x) = 1
    exact (QuotientGroup.eq_one_iff (N := oddCore ↥(A ⊔ B)) (f x)).mpr hfx
  let Φ' : ((↥A × ↥B) ⧸ ((oddCore ↥A).prod (oddCore ↥B))) →*
      (↥(A ⊔ B) ⧸ oddCore ↥(A ⊔ B)) :=
    QuotientGroup.lift ((oddCore ↥A).prod (oddCore ↥B)) Φ hker
  have hΦ'surj : Function.Surjective Φ' :=
    QuotientGroup.lift_surjective_of_surjective ((oddCore ↥A).prod (oddCore ↥B)) Φ hΦsurj hker
  have hdvd : Nat.card (↥(A ⊔ B) ⧸ oddCore ↥(A ⊔ B)) ∣
      Nat.card ((↥A × ↥B) ⧸ ((oddCore ↥A).prod (oddCore ↥B))) :=
    Subgroup.card_dvd_of_surjective hΦ'surj
  rw [Nat.card_congr (QuotientGroup.prodMulEquiv (oddCore ↥A) (oddCore ↥B)).toEquiv,
    Nat.card_prod] at hdvd
  exact hdvd

end CFSG.OddStandard.SmallF3.Omega

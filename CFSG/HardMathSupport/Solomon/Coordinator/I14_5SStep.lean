module

public import CFSG.HardMathSupport.Solomon.Coordinator.I14_5SCop
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_5SCen

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Timmesfeld.Proving (GLAPPrimeCoreOf_conj_mem coprime_card_GLAPPrimeCoreOf)

theorem i145s_layer_le {A : Type*} [Group A] (D : Subgroup A) : GLAPLayer 3 D ≤ D :=
  sSup_le fun _ hL => hL.1

theorem i145s_bad_le_primeCore {A : Type*} [Group A] (D : Subgroup A) :
    ⁅GLAPLayer 3 D, GLAPPrimeCoreOf 3 D⁆ ≤ GLAPPrimeCoreOf 3 D := by
  rw [Subgroup.commutator_le]
  intro l hl w hw
  have h1 := GLAPPrimeCoreOf_conj_mem (p := 3) l (i145s_layer_le D hl) w hw
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hw)

theorem i145s_base {A : Type} [Group A] [Finite A] (hcore : GLAPPrimeCore 3 A = ⊥) :
    ⁅GLAPLayer 3 (Subgroup.centralizer ((⊥ : Subgroup A) : Set A)),
      GLAPPrimeCoreOf 3 (Subgroup.centralizer ((⊥ : Subgroup A) : Set A))⁆ = ⊥ := by
  have hC : Subgroup.centralizer ((⊥ : Subgroup A) : Set A) = ⊤ := by
    rw [Subgroup.centralizer_eq_top_iff_subset]
    intro g hg
    rw [SetLike.mem_coe, Subgroup.mem_bot] at hg
    rw [hg]
    exact Subgroup.one_mem _
  rw [hC]
  have hN : GLAPPrimeCoreOf 3 (⊤ : Subgroup A) = ⊥ := by
    have hnorm : (GLAPPrimeCoreOf 3 (⊤ : Subgroup A)).Normal :=
      ⟨fun n hn g => GLAPPrimeCoreOf_conj_mem (p := 3) g (Subgroup.mem_top g) n hn⟩
    have hle : GLAPPrimeCoreOf 3 (⊤ : Subgroup A) ≤ GLAPPrimeCore 3 A :=
      le_sSup ⟨hnorm, coprime_card_GLAPPrimeCoreOf Nat.prime_three ⊤⟩
    rw [hcore] at hle
    exact le_bot_iff.1 hle
  rw [hN]
  exact Subgroup.commutator_bot_right _

theorem i145s_exists_central_order_three {A : Type*} [Group A] [Finite A] (Q : Subgroup A)
    (hQ : IsPGroup 3 Q) (hne : Q ≠ ⊥) :
    ∃ x ∈ Q, (∀ q ∈ Q, q * x = x * q) ∧ orderOf x = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).2 hne
  have hcen : Nontrivial (Subgroup.center Q) := hQ.center_nontrivial
  have hC3 : IsPGroup 3 (Subgroup.center Q) := hQ.to_subgroup _
  obtain ⟨k, hk⟩ := hC3.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    have : Nat.card (Subgroup.center Q) = 1 := by simpa using hk
    have := (Nat.card_eq_one_iff_unique.1 this).1
    exact (not_subsingleton _ this).elim
  have hdvd : 3 ∣ Nat.card (Subgroup.center Q) := by
    rw [hk]
    exact dvd_pow_self 3 hk0
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center Q) 3 hdvd
  refine ⟨((g : Q) : A), (g : Q).2, fun q hq => ?_, ?_⟩
  · have := Subgroup.mem_center_iff.1 g.2 ⟨q, hq⟩
    exact congrArg Subtype.val this
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hg]

theorem i145s_central_step {A : Type} [Group A] [Finite A] (Z Q : Subgroup A) [Z.Normal]
    (hZ : Z ≤ Subgroup.center A) (hZ3 : Nat.card Z = 3)
    (hbad : ⁅GLAPLayer 3 (Subgroup.centralizer ((Q.map (QuotientGroup.mk' Z) : Subgroup (A ⧸ Z)) :
        Set (A ⧸ Z))), GLAPPrimeCoreOf 3 (Subgroup.centralizer
        ((Q.map (QuotientGroup.mk' Z) : Subgroup (A ⧸ Z)) : Set (A ⧸ Z)))⁆ = ⊥) :
    ⁅GLAPLayer 3 (Subgroup.centralizer (Q : Set A)),
      GLAPPrimeCoreOf 3 (Subgroup.centralizer (Q : Set A))⁆ = ⊥ := by
  have h1 := i145s_central_bad Z Q hZ hbad
  have h2 := i145s_bad_le_primeCore (Subgroup.centralizer (Q : Set A))
  have hd : Disjoint (GLAPPrimeCoreOf 3 (Subgroup.centralizer (Q : Set A))) Z := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hZ3]
    exact (coprime_card_GLAPPrimeCoreOf Nat.prime_three _).symm
  exact le_bot_iff.1 (hd h2 h1)

theorem i145s_cop_step {A : Type} [Group A] [Finite A] (H Q : Subgroup A) (hQ : IsPGroup 3 Q)
    (hQH : Q ≤ H) (hDH : Subgroup.centralizer (Q : Set A) ≤ H)
    (hbad : ⁅GLAPLayer 3 (Subgroup.centralizer
        (((Q.subgroupOf H).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥H)) :
          Subgroup (↥H ⧸ GLAPPrimeCore 3 ↥H)) : Set (↥H ⧸ GLAPPrimeCore 3 ↥H))),
      GLAPPrimeCoreOf 3 (Subgroup.centralizer
        (((Q.subgroupOf H).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥H)) :
          Subgroup (↥H ⧸ GLAPPrimeCore 3 ↥H)) : Set (↥H ⧸ GLAPPrimeCore 3 ↥H)))⁆ = ⊥) :
    ⁅GLAPLayer 3 (Subgroup.centralizer (Q : Set A)),
      GLAPPrimeCoreOf 3 (Subgroup.centralizer (Q : Set A))⁆ ≤ GLAPPrimeCoreOf 3 H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set U : Subgroup ↥H := GLAPPrimeCore 3 ↥H with hU
  set QH : Subgroup ↥H := Q.subgroupOf H with hQHdef
  set DH : Subgroup ↥H := Subgroup.centralizer (QH : Set ↥H) with hDHdef
  have hDHeq : DH.map H.subtype = Subgroup.centralizer (Q : Set A) := by
    ext g
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine Subgroup.mem_centralizer_iff.2 fun q hq => ?_
      have := Subgroup.mem_centralizer_iff.1 hy ⟨q, hQH hq⟩ (Subgroup.mem_subgroupOf.2 hq)
      exact congrArg Subtype.val this
    · intro hg
      refine ⟨⟨g, hDH hg⟩, Subgroup.mem_centralizer_iff.2 fun q' hq' => ?_, rfl⟩
      have := Subgroup.mem_centralizer_iff.1 hg (q' : A) (Subgroup.mem_subgroupOf.1 hq')
      exact Subtype.ext this
  have hker1 : Nat.Coprime 3 (Nat.card ↥(DH ⊓ H.subtype.ker)) := by
    rw [H.ker_subtype, inf_bot_eq]
    simp
  have hker2 : Nat.Coprime 3 (Nat.card ↥(DH ⊓ (QuotientGroup.mk' U).ker)) := by
    rw [QuotientGroup.ker_mk']
    exact (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥H)).coprime_dvd_right
      (Subgroup.card_dvd_of_le inf_le_right)
  have e1 := i145s_bad_map Nat.prime_three H.subtype DH hker1
  rw [hDHeq] at e1
  have e2 := i145s_bad_map Nat.prime_three (QuotientGroup.mk' U) DH hker2
  have hQH3 : IsPGroup 3 QH := hQ.comap_of_injective H.subtype H.subtype_injective
  have hcm := i145s_centralizer_map U (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥H)) hQH3
  have e2' : (⁅GLAPLayer 3 DH, GLAPPrimeCoreOf 3 DH⁆).map (QuotientGroup.mk' U) = ⊥ := by
    rw [← e2, hDHdef, hcm]
    exact hbad
  have e3 : ⁅GLAPLayer 3 DH, GLAPPrimeCoreOf 3 DH⁆ ≤ U := by
    have := (Subgroup.map_eq_bot_iff _).1 e2'
    rwa [QuotientGroup.ker_mk'] at this
  rw [e1]
  exact Subgroup.map_mono e3

end CFSG.HardMathSupport.Solomon.Coordinator

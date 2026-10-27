module

public import CFSG.HardMathSupport.Dickson.Bal207.FamF42Class
import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalNoNormal

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I2610

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Dickson.Bal207
  CFSG.HardMathSupport.Dickson.Bal207.FamF42 CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

private theorem card_of_f42CompType {Q : Type} [Group Q] (h : F42CompType Q) :
    Nat.card Q = 1451520 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (le_refl 1) (by rw [hF]; norm_num)
  have hZ := center_statedSp_eq_bot_of_charP_two (K := F) 3
  rw [Nat.card_congr e.toEquiv, hZ]
  rw [show Nat.card (StatedSp 3 F ⧸ (⊥ : Subgroup (StatedSp 3 F))) =
      Nat.card (StatedSp 3 F) from Nat.card_congr QuotientGroup.quotientBot.toEquiv]
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hF]
  decide


theorem eq_of_isComponentOf_fixSubgroup_conj {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {x : ↥(adjointGroup Tag.F4 K)} (hx : orderOf x = 3)
    {L₁ L₂ : Subgroup ↥(adjointGroup Tag.F4 K)}
    (h₁ : CFSG.Open.IsComponentOf L₁ (fixSubgroup (MulAut.conj x)))
    (h₂ : CFSG.Open.IsComponentOf L₂ (fixSubgroup (MulAut.conj x))) : L₁ = L₂ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  haveI : Finite ↥(adjointGroup Tag.F4 K) := by
    have : Finite (Module.End K (RootModule Tag.F4 K)) := Module.finite_of_finite K
    infer_instance
  by_contra hne
  have hcommute : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a := by
    rcases CFSG.Quasithin.F918V5G.isComponentOf_eq_or_commute h₁ h₂ with heq | hc
    · exact absurd heq hne
    · exact hc
  have hcomp := compShape_conj_F4_two hK x hx
  have hcard1q : Nat.card (↥L₁ ⧸ Subgroup.center ↥L₁) = 1451520 :=
    card_of_f42CompType (hcomp.type L₁ h₁)
  have hcard2q : Nat.card (↥L₂ ⧸ Subgroup.center ↥L₂) = 1451520 :=
    card_of_f42CompType (hcomp.type L₂ h₂)
  have hcard1 : Nat.card ↥L₁ = 1451520 * Nat.card (Subgroup.center ↥L₁) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L₁), hcard1q]
  have hcard2 : Nat.card ↥L₂ = 1451520 * Nat.card (Subgroup.center ↥L₂) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L₂), hcard2q]
  have hZinf : Nat.card ↥(L₁ ⊓ L₂) ∣ Nat.card ↥(Subgroup.center ↥L₁) := by
    have hsub : (L₁ ⊓ L₂).subgroupOf L₁ ≤ Subgroup.center ↥L₁ := by
      intro z hz
      rw [Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext (hcommute w.1 w.2 z.1 hz.2)
    have hdvd := Subgroup.card_dvd_of_le hsub
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at hdvd
  obtain ⟨k, hk⟩ := hZinf
  obtain ⟨hcardMul, -⟩ :=
    CFSG.GroupTheory.card_sup_mul_card_inf_of_commute L₁ L₂ hcommute
  have hbig : 1451520 * 1451520 ∣ Nat.card ↥(L₁ ⊔ L₂) := by
    refine ⟨k * Nat.card ↥(Subgroup.center ↥L₂), ?_⟩
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥(L₁ ⊓ L₂)))
    rw [hcardMul, hcard1, hcard2, hk]
    ring
  have h3 : 3 ^ 8 ∣ Nat.card ↥(L₁ ⊔ L₂) := by
    refine dvd_trans ?_ hbig
    decide
  have hdvdG : Nat.card ↥(L₁ ⊔ L₂) ∣ Nat.card ↥(adjointGroup Tag.F4 K) :=
    Subgroup.card_subgroup_dvd_card _
  have hG : Nat.card ↥(adjointGroup Tag.F4 K) = 3311126603366400 := by
    have h := CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4 (K := K)
    rw [hK] at h
    exact h.trans (by norm_num [CFSG.Open.ordF4])
  have h3G : 3 ^ 8 ∣ 3311126603366400 := by
    rw [← hG]
    exact dvd_trans h3 hdvdG
  exact (by decide : ¬ (3 ^ 8 ∣ 3311126603366400)) h3G

theorem exists_component_of_perfect_le {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {x : ↥(adjointGroup Tag.F4 K)} (hx : orderOf x = 3)
    {P : Subgroup ↥(adjointGroup Tag.F4 K)} (hPx : P ≤ fixSubgroup (MulAut.conj x))
    (hP : ⁅P, P⁆ = P) (hP1 : P ≠ ⊥) :
    ∃ L : Subgroup ↥(adjointGroup Tag.F4 K),
      CFSG.Open.IsComponentOf L (fixSubgroup (MulAut.conj x)) ∧ P ≤ L ∧
        F42CompType (↥L ⧸ Subgroup.center ↥L) ∧
        ∀ ω : MulAut ↥(adjointGroup Tag.F4 K), ω * MulAut.conj x = MulAut.conj x * ω →
          L.map ω.toMonoidHom = L := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  haveI : Finite ↥(adjointGroup Tag.F4 K) := by
    have : Finite (Module.End K (RootModule Tag.F4 K)) := Module.finite_of_finite K
    infer_instance
  set C : Subgroup ↥(adjointGroup Tag.F4 K) := fixSubgroup (MulAut.conj x) with hC
  have hcomp := compShape_conj_F4_two hK x hx
  have hPL : P ≤ GLALayer C := hcomp.layer P hPx hP
  have hex : ∃ L : Subgroup ↥(adjointGroup Tag.F4 K), CFSG.Open.IsComponentOf L C := by
    by_contra hno
    push Not at hno
    have hempty : {K : Subgroup ↥(adjointGroup Tag.F4 K) | CFSG.Open.IsComponentOf K C} = ∅ :=
      Set.eq_empty_of_forall_notMem hno
    have hbot : GLALayer C = ⊥ := by
      change sSup {K : Subgroup ↥(adjointGroup Tag.F4 K) | CFSG.Open.IsComponentOf K C} = ⊥
      rw [hempty, sSup_empty]
    exact hP1 (le_bot_iff.mp (hPL.trans (le_of_eq hbot)))
  obtain ⟨L, hL⟩ := hex
  have hLfix : CFSG.Open.IsComponentOf L (fixSubgroup (MulAut.conj x)) := by
    rw [← hC]
    exact hL
  have huniq : ∀ L' : Subgroup ↥(adjointGroup Tag.F4 K), CFSG.Open.IsComponentOf L' C → L' = L :=
    fun L' hL' => eq_of_isComponentOf_fixSubgroup_conj hK hx hL' hL
  have hlayer : GLALayer C = L := by
    apply le_antisymm
    · change sSup {K : Subgroup ↥(adjointGroup Tag.F4 K) | CFSG.Open.IsComponentOf K C} ≤ L
      exact sSup_le fun K hK' => by rw [huniq K hK']
    · change L ≤ sSup {K : Subgroup ↥(adjointGroup Tag.F4 K) | CFSG.Open.IsComponentOf K C}
      exact le_sSup hL
  refine ⟨L, hLfix, ?_, hcomp.type L hLfix, ?_⟩
  · rw [← hlayer]
    exact hPL
  · intro ω hω
    exact hcomp.norm ω hω L hLfix

end CFSG.LocalAnalysis.GLTheoremA.CatB.I2610

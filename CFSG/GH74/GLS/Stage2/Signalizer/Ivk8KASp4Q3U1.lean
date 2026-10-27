module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KASp4U1

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSp4
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

theorem kaQ3_two_ne_zero {F : Type} [Field F] [Finite F] (hK : Nat.card F = 3) : (2 : F) ≠ 0 := by
  intro h2
  have h3 := CFSG.LieType.HighestRoot.three_eq_zero hK
  have : (1 : F) = 0 := by linear_combination h3 - h2
  exact one_ne_zero this

theorem kaQ3_ringChar_ne_two {F : Type} [Field F] [Finite F] (hK : Nat.card F = 3) :
    ringChar F ≠ 2 := by
  intro h
  have h' : ((2 : ℕ) : F) = 0 := (ringChar.spec F 2).2 (by rw [h])
  exact kaQ3_two_ne_zero hK (by exact_mod_cast h')

theorem kaQ3_pPrimeCore_SL2 {F : Type} [Field F] [Finite F] (hK : Nat.card F = 3) :
    CFSG.pPrimeCore 2 (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  have h2 := kaQ3_two_ne_zero hK
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro N hN hcop
  by_cases hNZ : N ≤ center (Matrix.SpecialLinearGroup (Fin 2) F)
  · rw [eq_bot_iff]
    intro z hz
    rcases eq_one_or_neg_of_mem_center (hNZ hz) with h1 | h1
    · exact (Subgroup.mem_bot).mpr (Subtype.ext h1)
    · exfalso
      have hzn : z = negOneSL := Subtype.ext h1
      have hdvd := Subgroup.orderOf_dvd_natCard N hz
      rw [hzn, orderOf_negOneSL h2] at hdvd
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hcop hdvd
  · exfalso
    have := hN
    have h8 := CFSG.LieType.HighestRoot.eight_le_card_of_normal hK (MulEquiv.refl _) N hNZ
    have h24 := CFSG.LieType.HighestRoot.card_eq_24 hK
      (MulEquiv.refl (Matrix.SpecialLinearGroup (Fin 2) F))
    have hdvd : Nat.card N ∣ 24 := h24 ▸ Subgroup.card_subgroup_dvd_card N
    have hodd : Nat.card N % 2 = 1 := by
      rcases Nat.even_or_odd (Nat.card N) with he | ho
      · exfalso
        have : 2 ∣ Nat.card N := even_iff_two_dvd.mp he
        exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hcop this
      · exact Nat.odd_iff.mp ho
    have hle : Nat.card N ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card N = n at hdvd h8 hodd hle
    interval_cases n <;> omega

theorem kaQ3_pPrimeCore_E1 {F : Type} [Field F] [Finite F] (hK : Nat.card F = 3) :
    CFSG.pPrimeCore 2 (E1 F) = ⊥ := by
  rw [← CFSG.pPrimeCore_map_iso 2 (E1Equiv (kaQ3_two_ne_zero hK)), kaQ3_pPrimeCore_SL2 hK,
    Subgroup.map_bot]

theorem kaQ3_pPrimeCore_E2 {F : Type} [Field F] [Finite F] (hK : Nat.card F = 3) :
    CFSG.pPrimeCore 2 (E2 F) = ⊥ := by
  rw [← CFSG.pPrimeCore_map_iso 2 (E2Equiv (kaQ3_two_ne_zero hK)), kaQ3_pPrimeCore_SL2 hK,
    Subgroup.map_bot]

theorem kaQ3_X0_hRp {F : Type} [Field F] [Finite F] (hK : Nat.card F = 3)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Subgroup (StatedProj (StatedSp 2 F))}
    (hX : IsPGroup p ↥X) (hXle : X ≤ X0 F)
    (hnorm : ∀ r ∈ X0 F, r ∈ normalizer (X : Set (StatedProj (StatedSp 2 F)))) : X = ⊥ := by
  have h2 := kaQ3_two_ne_zero hK
  have hE1 : X ⊓ E1 F = ⊥ :=
    kaU1_inf_eq_bot_of_pPrimeCore hp hp2 hX (fun e he => hnorm e (E1_le_X0 h2 he))
      (kaQ3_pPrimeCore_E1 hK)
  have hE2 : X ⊓ E2 F = ⊥ :=
    kaU1_inf_eq_bot_of_pPrimeCore hp hp2 hX (fun e he => hnorm e (E2_le_X0 h2 he))
      (kaQ3_pPrimeCore_E2 hK)
  have hc2 : ∀ x ∈ X, ∀ e ∈ E2 F, x * e = e * x :=
    kaU1_commute_of_inf_bot hE2 (fun e he => hnorm e (E2_le_X0 h2 he))
      (fun x hx e he => conj_mem_E2 h2 (hXle hx) he)
  rw [eq_bot_iff]
  intro x hx
  have hxE1 : x ∈ E1 F := mem_E1_of_commute_E2 h2 (hXle hx) (fun y hy => hc2 x hx y hy)
  have hx1 : x ∈ X ⊓ E1 F := ⟨hx, hxE1⟩
  rwa [hE1] at hx1

theorem kaQ3_mem_closure_odd {F : Type} [Field F] [Finite F] (hK : Nat.card F = 3)
    (f : Matrix.SpecialLinearGroup (Fin 2) F →* StatedProj (StatedSp 2 F))
    (hf : ∀ g, f g ∈ X0 F) (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    f g ∈ Subgroup.closure {x : StatedProj (StatedSp 2 F) | x ∈ X0 F ∧ Odd (orderOf x)} := by
  have hg : g ∈ Subgroup.closure {y : Matrix.SpecialLinearGroup (Fin 2) F | orderOf y = 3} := by
    rw [CFSG.LieType.HighestRoot.closure_orderOf_three_eq_top hK]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    refine Subgroup.subset_closure ⟨hf y, ?_⟩
    have hd : orderOf (f y) ∣ orderOf y := orderOf_map_dvd f y
    rw [hy] at hd
    exact Odd.of_dvd_nat (by decide) hd
  | one =>
    rw [map_one]
    exact one_mem _
  | mul a b _ _ ha hb =>
    rw [map_mul]
    exact mul_mem ha hb
  | inv a _ ha =>
    rw [map_inv]
    exact inv_mem ha

theorem kaQ3_X0_gen {F : Type} [Field F] [Finite F] (hK : Nat.card F = 3) :
    Subgroup.closure {x : StatedProj (StatedSp 2 F) | x ∈ X0 F ∧ Odd (orderOf x)} = X0 F := by
  have h2 := kaQ3_two_ne_zero hK
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    exact fun x hx => hx.1
  · intro x hx
    obtain ⟨⟨g, h⟩, rfl⟩ := (mem_X0 h2).mp hx
    rw [show (g, h) = (g, 1) * (1, h) by simp, map_mul, map_mul]
    refine mul_mem ?_ ?_
    · exact kaQ3_mem_closure_odd hK ((proj 2 F).comp ((blkSL F).comp (MonoidHom.inl _ _)))
        (fun g => (mem_X0 h2).mpr ⟨(g, 1), rfl⟩) g
    · exact kaQ3_mem_closure_odd hK ((proj 2 F).comp ((blkSL F).comp (MonoidHom.inr _ _)))
        (fun g => (mem_X0 h2).mpr ⟨(1, g), rfl⟩) h

theorem kaSp4U1Three_thm : KASp4U1Three := by
  intro F _ _ hK
  have hodd : ringChar F ≠ 2 := kaQ3_ringChar_ne_two hK
  have hθα : ∀ g, MulAut.conj (u1 F) (proj 2 F g) = proj 2 F (MulAut.conj (T1 F) g) := by
    intro g
    have hu : u1 F = proj 2 F (T1 F) := rfl
    rw [hu, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
  refine ka_all_of_oddcore (ka_conj_inj_psp4 hodd) (X0 F) ?_ (kaQ3_X0_gen hK) ?_ ?_
    (ka_outCyc_psp4 hodd) (ka_outCentral_psp4 hodd _)
  · rw [fixSub_conj]
    exact X0_le_centralizer
  · intro c hc hco
    have h := ka_odd_mem_map_fixOf (MulAut.conj (T1 F)) (MulAut.conj (u1 F)) hθα
      (mem_fixSub.mp hc) hco
    rw [fixOf_conj] at h
    exact h
  · intro p hp hp2 X hX hXle hnorm
    exact kaQ3_X0_hRp hK hp hp2 hX hXle hnorm

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

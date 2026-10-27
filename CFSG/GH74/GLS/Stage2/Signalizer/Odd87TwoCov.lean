module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87KindIdx
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Open
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Mult
public import CFSG.GH74.GLS.Stage2.Local.P27.QIdArith
public import CFSG.LieType.Steinberg.CentralExt.PSLSmall

public section

open CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.GLS.Stage12
open scoped MatrixGroups
open Matrix

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem card_sz8 {Y : Type} [Group Y]
    (h : LieModel Y .twistedB2 0 2 3) : Nat.card Y = 29120 := by
  rcases h with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hS⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := hS
    have ha1 : a = 1 := by omega
    subst ha1
    have hK' : Nat.card K = 2 ^ (2 * 1 + 1) := hK
    rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK']
    norm_num

theorem card_l34 {Y : Type} [Group Y]
    (h : LieModel Y .PSL 3 2 2) : Nat.card Y = 20160 := by
  obtain ⟨e⟩ := CFSG.ComponentClassification.CatFactsSmall.nonempty_equiv_psl34_of_lieModel h
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.ComponentClassification.PSL3Four.card_S


theorem not_isL2_of_card (N : ℕ) (hN : ∀ r : ℕ, r ≤ 60 → r * (r ^ 2 - 1) / 2 ≠ N)
    (hN' : N < 60 * (60 ^ 2 - 1) / 2) {Y : Type} [Group Y] (hY : Nat.card Y = N) :
    ¬ IVK.IsL2 Y (fun r => Odd r ∧ 5 ≤ r) := by
  rintro ⟨F, _, _, ⟨hr, hr5⟩, ⟨e⟩⟩
  have h1 : IVK.IsL2 Y (fun r => r = Nat.card F) := ⟨F, inferInstance, inferInstance, rfl, ⟨e⟩⟩
  have h2 := CFSG.GH74.GLS.Stage2.Local.P27.QId.card_isL2 hr h1
  rw [hY] at h2
  by_cases hr60 : Nat.card F ≤ 60
  · exact hN _ hr60 h2.symm
  · push Not at hr60
    have : 60 * (60 ^ 2 - 1) / 2 ≤ Nat.card F * (Nat.card F ^ 2 - 1) / 2 := by
      apply Nat.div_le_div_right
      apply Nat.mul_le_mul hr60.le
      have : 60 ^ 2 ≤ Nat.card F ^ 2 := Nat.pow_le_pow_left hr60.le 2
      omega
    omega

theorem card_alt_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.factorial]

theorem not_kindFactorAll_aux (N : ℕ) (hN : ∀ r : ℕ, r ≤ 60 → r * (r ^ 2 - 1) / 2 ≠ N)
    (hN' : N < 60 * (60 ^ 2 - 1) / 2) (h7 : ¬ N ∣ 2520) (k : Kind) {Y : Type} [Group Y]
    (hY : Nat.card Y = N) (hmc : (k = Kind.mcl ∨ k = Kind.ly) → ¬ KindFactorAll k Y) :
    ¬ KindFactorAll k Y := by
  cases k with
  | g2 => exact not_isL2_of_card N hN hN' hY
  | psp4 => exact not_isL2_of_card N hN hN' hY
  | m12 => exact not_isL2_of_card N hN hN' hY
  | l4 ε =>
    rintro (hL | hS)
    · exact not_isL2_of_card N hN hN' hY hL
    · have := hS.card_dvd
      rw [hY, card_alt_seven] at this
      exact h7 this
  | mcl => exact hmc (Or.inl rfl)
  | ly => exact hmc (Or.inr rfl)

theorem not_kindFactorAll_sz8 (k : Kind) {Y : Type} [Group Y]
    (h : LieModel Y .twistedB2 0 2 3) : ¬ KindFactorAll k Y := by
  have hc := card_sz8 h
  refine not_kindFactorAll_aux 29120 (by decide) (by norm_num) (by decide) k hc ?_
  intro hk hKF
  have := KindFactorAll.card_dvd hKF hk
  rw [hc] at this
  revert this
  decide

theorem not_kindFactorAll_l34 (hMin : MinIndexL34) (k : Kind)
    {Y : Type} [Group Y] [Finite Y] (h : LieModel Y .PSL 3 2 2) : ¬ KindFactorAll k Y := by
  have hc := card_l34 h
  have : Nontrivial Y := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    rw [hc]
    norm_num
  refine not_kindFactorAll_aux 20160 (by decide) (by norm_num) (by decide) k hc ?_
  intro hk
  exact not_kindFactorAll_mclly_of_index hk (hMin Y h)

theorem center_eq_bot_psl2_even
    {L : Type} [Group L] [Finite L] (hL : CFSG.IsQuasisimple L)
    {f : ℕ} (hf : f = 3 ∨ f = 4) (hmodel : LieModel (L ⧸ center L) .PSL 2 2 f) :
    center L = ⊥ := by
  obtain ⟨-, -, F, iF, fF, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psl_data hmodel
  have : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = 2 ^ f := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hk5 : 5 ≤ Fintype.card F := by
    rw [hFc]; rcases hf with rfl | rfl <;> norm_num
  have hk9 : Fintype.card F ≠ 9 := by
    rw [hFc]; rcases hf with rfl | rfl <;> norm_num
  have eP : PSL(2, F) ≃* (L ⧸ center L) := (IVK.L2.equivPSL F).symm.trans e.symm
  obtain ⟨-, ⟨hM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_two_hopfMultiplier_of_mulEquiv
    hk5 hk9 eP
  have hgcd : Nat.gcd 2 (Fintype.card F - 1) = 1 := by
    rw [hFc]; rcases hf with rfl | rfl <;> norm_num
  rw [hgcd] at hM
  have hsub : Subsingleton (CFSG.Open.griessHopfMultiplier (L ⧸ center L)) := by
    refine ⟨fun a b => ?_⟩
    exact hM.injective (Subsingleton.elim _ _)
  exact center_eq_bot_of_hopf_subsingleton hL (MulEquiv.refl _) hsub

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87

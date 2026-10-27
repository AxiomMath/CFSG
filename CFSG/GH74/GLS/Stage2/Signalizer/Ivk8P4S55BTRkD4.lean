module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTRkG2Kind
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FD4
public import CFSG.CGT.T75P.A8ExclPGL
public import CFSG.ClassicalInvolution.AschTight.S19GD4Inv
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87D4Out

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
  CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank RkG2
open CFSG.ComponentClassification.FixedCommutingProduct renaming fixedSubgroup → fixedSubgroupFCP


namespace RkD4

theorem center_eq_bot_fd4 {Y : Type} [Group Y] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hLie : LieModel Y .trialityD4 0 p f) : center Y = ⊥ := by
  have htw : TwistedChevalleyModel Y .D4 (p ^ f) := by
    rcases hLie with ⟨ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact h.2
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  obtain ⟨M, _, _, σ, hM, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf htw
  obtain ⟨-, -, -, -, -, -, hZ, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf M hM σ hσ
  exact center_eq_bot_of_mulEquiv_target e hZ

theorem exists_ne_fd4 {Y : Type} [Group Y] [IsSimpleGroup Y] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hLie : LieModel Y .trialityD4 0 p f) :
    ∃ a b : Y, a * b ≠ b * a := by
  have : Nontrivial Y := IsSimpleGroup.toNontrivial
  by_contra h
  push Not at h
  obtain ⟨y, hy⟩ := exists_ne (1 : Y)
  have hyZ : y ∈ center Y := Subgroup.mem_center_iff.mpr fun g => h g y
  rw [center_eq_bot_fd4 hp hp2 hf hLie] at hyZ
  exact hy (Subgroup.mem_bot.mp hyZ)

section Rank

open CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
  CFSG.ClassicalInvolution.G2D4Models CFSG.ClassicalInvolution.Disconnected.AschTight.S19G

theorem card_le_eight_fd4 {Y : Type} [Group Y] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hL : LieModel Y .trialityD4 0 p f) (E : Subgroup Y)
    (hEsq : ∀ x ∈ E, x * x = 1) : Nat.card ↥E ≤ 8 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨φ⟩ := exists_equiv_concrete hp2 hL
  obtain ⟨hσ, hK, hC₀, hgF, -, hoddF⟩ := d4_model_data (p := p) hp2 hf
  have h2 : (2 : fixedField (sig0 p f)) ≠ 0 :=
    CFSG.ClassicalInvolution.Disconnected.AschTight.S19F.two_ne_zero_of_odd hoddF
  have hle := CFSG.CGT.T75P.a8x_card_le_eight_of_chart
    (CFSG.RankThree.PartOne.ringChar_ne_two_of_odd_card hoddF) (slLong _ hσ) (slLong_injective hσ)
    (tauL_mul_self hσ) (tauL_ne_one hσ hK)
    (fun x y hx hy hx1 hy1 =>
      CFSG.ClassicalInvolution.Balance.Bootstrap.trialityD4_involutions_conj hp2 hf hx hy hx1 hy1)
    (fun x hx => linAct_of_centralizes_long hσ hK h2 hC₀ hgF hx)
    (fun x hx hc => eq_one_or_eq_of_centralizing_slLong hσ hK hC₀ hgF hx hc)
    (E.map φ.toMonoidHom) (by
      rintro _ ⟨x, hx, rfl⟩
      show φ x * φ x = 1
      rw [← map_mul, hEsq x hx, map_one])
  rwa [← Nat.card_congr (E.equivMapOfInjective φ.toMonoidHom φ.injective).toEquiv] at hle

end Rank

theorem not_kindFactorAll_fd4 {k : Kind} (hk : IsClassicalKind k) {Y : Type} [Group Y]
    [Finite Y] [IsSimpleGroup Y] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hp2 : p ≠ 2)
    (hLie : LieModel Y .trialityD4 0 p f) : ¬ KindFactorAll k Y :=
  not_kindFactorAll_of_not_kindFactor hk
    (td4_bad_of_model (exists_ne_fd4 hp hp2 hf hLie) hp hp2 hf hLie)

theorem admRank3_fd4 {k : Kind} (hk : IsClassicalKind k) {Y : Type} [Group Y] [Finite Y]
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hp2 : p ≠ 2) (hLie : LieModel Y .trialityD4 0 p f) :
    AdmRank3 k Y := by
  refine admRank3_of_inner (conj_injective_of_center (center_eq_bot_fd4 hp hp2 hf hLie))
    (fun W hW => ?_) fun x hxx hnot => ?_
  · have := hW
    refine card_le_eight_fd4 hp hp2 hf hLie W fun x hx => ?_
    rw [← pow_two]
    exact elemPow_eq_one_of_isElementaryAbelian x hx
  · obtain ⟨e', he', hs, hnab, hm⟩ :=
      td4_outer_involution_fixed hp hp2 hf hLie x (by rw [sq]; exact hxx) hnot
    exact not_admAut_of_le (K := fixedSubgroupFCP x) (fun y hy => hy)
      (not_isSolvable_of_exists_ne hnab)
      (not_kindFactorAll_of_not_kindFactor hk (td4_bad_of_model hnab hp hp2 he' hm))

end RkD4

open RkD4 in
theorem rankCell_fd4 : RankCell FD4 := by
  intro k hk Y _ _ _ hY
  obtain ⟨p, f, hp, hf, hp2, hLie⟩ := hY
  exact ⟨not_kindFactorAll_fd4 hk hp hf hp2 hLie, admRank3_fd4 hk hp hf hp2 hLie⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

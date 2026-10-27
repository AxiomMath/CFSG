module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporShape
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.OrthOuterThreeAux.SympPrimeSubfieldOdd
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieSp4EFrame
public import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma49i

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4F

open CFSG.Open CFSG.Open.StatedAPI CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4E
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (congr_conj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  (spLinearAutGroup spSemilinearAutGroup fieldAut)
open scoped commutatorElement

abbrev F8 : Type := GaloisField 2 3

abbrev TF : Type := StatedProj (StatedSp 2 F8)

noncomputable abbrev innTF : Subgroup (MulAut TF) := CFSG.ComponentClassification.OuterAutomorphisms.inner TF

theorem card_F8 : Nat.card F8 = 8 := by
  rw [GaloisField.card 2 3 (by norm_num)]
  norm_num

theorem card_F8_pow : Nat.card F8 = 2 ^ 3 := GaloisField.card 2 3 (by norm_num)

noncomputable def eQ : TF ≃* ↥(StatedSp 2 F8) :=
  (QuotientGroup.quotientMulEquivOfEq (statedScalars_subgroupOf_statedSp_eq_bot (n := 2) (K := F8))).trans
    QuotientGroup.quotientBot

theorem isSimple_A6 : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem card_A6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.factorial]

theorem not_comm_A6 : ¬ IsMulCommutative ↥(alternatingGroup (Fin 6)) := by
  intro h
  have ha : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2) ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    norm_num
  have hb : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 3 4) ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    norm_num
  have key : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2) * (Equiv.swap 0 1 * Equiv.swap 3 4) ≠
      (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 3 4) * (Equiv.swap 0 1 * Equiv.swap 1 2) := by
    decide
  exact key (congrArg Subtype.val (h.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩))

theorem level_of_comp_H0 {T : Type} [Group T] [Finite T] (H₀ : Subgroup T)
    (hD : Nonempty (↥⁅H₀, H₀⁆ ≃* ↥(alternatingGroup (Fin 6)))) {J : Subgroup T}
    (hJ : GLAPComponent 3 H₀ J) : kLevel 3 (PSimple 3 J) ≤ 2 := by
  obtain ⟨f⟩ := hD
  have hD6le : ⁅H₀, H₀⁆ ≤ H₀ := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    rw [commutatorElement_def]
    exact H₀.mul_mem (H₀.mul_mem (H₀.mul_mem hg hh) (H₀.inv_mem hg)) (H₀.inv_mem hh)
  have hJD : J ≤ ⁅H₀, H₀⁆ := by
    calc J = ⁅J, J⁆ := (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ).symm
      _ ≤ ⁅H₀, H₀⁆ := Subgroup.commutator_mono hJ.1 hJ.1
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := isSimple_A6
  haveI : IsSimpleGroup ↥⁅H₀, H₀⁆ := f.isSimpleGroup
  have hsub : CFSG.Open.IsSubnormal (J ⊓ ⁅H₀, H₀⁆) ⁅H₀, H₀⁆ := hJ.2.1.inf_of_le hD6le
  rw [inf_eq_left.2 hJD] at hsub
  have hJeq : J = ⁅H₀, H₀⁆ :=
    (CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hsub inferInstance).resolve_left
      (CFSG.LocalAnalysis.GLTheoremA.glaPComponent_ne_bot' hJ)
  rw [hJeq]
  have hnc : ¬ IsMulCommutative ↥⁅H₀, H₀⁆ := not_comm_of_mulEquiv f not_comm_A6
  have h3 : 3 ∣ Nat.card ↥⁅H₀, H₀⁆ := by
    rw [Nat.card_congr f.toEquiv, card_A6]
    norm_num
  obtain ⟨eP⟩ := pSimple_equiv_of_simple' ⁅H₀, H₀⁆ hnc h3
  have hA6 : CFSG.HardMathSupport.Dickson.I271.IsA6At 3 (PSimple 3 ⁅H₀, H₀⁆) :=
    ⟨rfl, ⟨eP.trans f⟩⟩
  exact (CFSG.LocalAnalysis.GLTheoremA.KDSpor.kLevel_le_one_of_A6 hA6).trans (by norm_num)

theorem level_of_comp_conj {T : Type} [Group T] [Finite T] (H₀ : Subgroup T)
    (hD : Nonempty (↥⁅H₀, H₀⁆ ≃* ↥(alternatingGroup (Fin 6)))) (x : T) {J : Subgroup T}
    (hJ : GLAPComponent 3 (GLBConj x⁻¹ H₀) J) : kLevel 3 (PSimple 3 J) ≤ 2 := by
  have h1 := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hJ x
  rw [gLBConj_gLBConj_inv] at h1
  have h2 := level_of_comp_H0 H₀ hD h1
  obtain ⟨eP⟩ := pSimple_map_equiv' 3 (MulAut.conj x⁻¹) J
  rw [← CFSG.LocalAnalysis.GLTheoremA.kLevel_congr 3 eP]
  exact h2

theorem fix_conj_form {T : Type} [Group T] (x : T) (H₀ : Subgroup T) (φ : MulAut T)
    (hφ : ∀ z : T, z ∈ H₀ ↔ φ z = z) :
    fixSubgroup (MulAut.conj x * φ * MulAut.conj x⁻¹) = GLBConj x⁻¹ H₀ := by
  ext y
  rw [mem_fixSubgroup, mem_gLBConj, hφ]
  show x * φ (x⁻¹ * y * x⁻¹⁻¹) * x⁻¹ = y ↔ φ (x⁻¹ * y * x⁻¹⁻¹) = x⁻¹ * y * x⁻¹⁻¹
  set z := x⁻¹ * y * x⁻¹⁻¹ with hz
  have hy : y = x * z * x⁻¹ := by
    rw [hz]
    group
  rw [hy]
  simp only [mul_left_inj, mul_right_inj]

theorem fieldT_level (β : MulAut TF) (hβ3 : β ^ 3 = 1) (hβin : β ∉ innTF)
    {J : Subgroup TF} (hJ : GLAPComponent 3 (fixSubgroup β) J) :
    kLevel 3 (PSimple 3 J) ≤ 2 := by
  obtain ⟨-, -, -, -, -, -, -, hIdx, hRel, hfield⟩ :=
    CFSG.RankThree.Classical.SteinbergBY.symplectic_prime_semilinear_field_descent
      (ℓ := 2) (f := 3) (r := 2) Nat.prime_two (by norm_num) (by norm_num) card_F8_pow
  have hDinn : spLinearAutGroup 2 F8 ≤ innTF := by
    apply Subgroup.relIndex_eq_one.1
    have h1 : Nat.gcd 2 (2 ^ 3 - 1) = 1 := by norm_num
    rw [h1] at hRel
    exact Nat.dvd_one.1 hRel
  have hEn : (spSemilinearAutGroup 2 F8).Normal := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hIdx with h1 | h1
    · rw [Subgroup.index_eq_one] at h1
      rw [h1]
      infer_instance
    · exact Subgroup.normal_of_index_eq_two h1
  have hβE : β ∈ spSemilinearAutGroup 2 F8 := by
    have h3 : orderOf (QuotientGroup.mk' (spSemilinearAutGroup 2 F8) β) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hβ3, map_one])
    have h2 : orderOf (QuotientGroup.mk' (spSemilinearAutGroup 2 F8) β) ∣ 2 :=
      (orderOf_dvd_natCard _).trans hIdx
    have h1 : orderOf (QuotientGroup.mk' (spSemilinearAutGroup 2 F8) β) = 1 :=
      Nat.dvd_one.1 (by simpa using Nat.dvd_gcd h3 h2)
    exact (QuotientGroup.eq_one_iff β).1 (orderOf_eq_one_iff.1 h1)
  have hβD : β ∉ spLinearAutGroup 2 F8 := fun h => hβin (hDinn h)
  have hβ1 : β ≠ 1 := fun h => hβin (h ▸ (innTF).one_mem)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf β = 3 := orderOf_eq_prime hβ3 hβ1
  obtain ⟨-, σ, hσ, -, h, hhD, hβeq⟩ := hfield 3 Nat.prime_three β hβE hβD hord
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 (hDinn hhD)
  have hβform : β = MulAut.conj x * fieldAut 2 F8 σ * MulAut.conj x⁻¹ := by
    rw [hβeq, ← hx, map_inv]
  obtain ⟨-, -, -, -, -, hmem, -, -, hS6, -, -, -, -, -⟩ :=
    CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.symplectic_prime_subfield_fixed_group_and_full_centralizer_odd
      (K := F8) (ℓ := 2) (p := 3) (f := 3) (r := 2) Nat.prime_two Nat.prime_three (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) card_F8_pow σ hσ
  obtain ⟨-, hD6, -⟩ := hS6 ⟨rfl, by norm_num⟩
  have hfix : fixSubgroup β = GLBConj x⁻¹
      (CFSG.RankThree.CASymplecticSubfield.subfieldFixedGroup F8 2 σ) := by
    rw [hβform]
    exact fix_conj_form x _ _ hmem
  rw [hfix] at hJ
  exact level_of_comp_conj _ hD6 x hJ

end CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4F

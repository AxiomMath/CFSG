module

public import CFSG.GroupTheory.FixedPointsCentralQuotient
public import CFSG.GroupTheory.PCore.JointlyInjective
public import CFSG.Quasithin.Vol2.Ch11SecA02Card
public import CFSG.Quasithin.Background.GoldschmidtRankOneUnitary
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6Diag

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD1912

open CFSG.Open
open CFSG.Fischer
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
open CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.ClassicalGroups.UnitaryFlag

@[expose] def U6TwoOddCoreThree : Prop :=
  ∀ β : MulAut S6, β ^ 3 = 1 → pPrimeCore 3 (fixSubgroup β) = ⊥

theorem isPGroup_three_ker_mk : IsPGroup 3 (QuotientGroup.mk' ((StatedScalars (Fin 6) F4).subgroupOf
    (StatedSU 6 (2 ^ 1) F4))).ker := by
  let Z : Subgroup (StatedSU 6 (2 ^ 1) F4) :=
    (StatedScalars (Fin 6) F4).subgroupOf (StatedSU 6 (2 ^ 1) F4)
  have hπker : (QuotientGroup.mk' Z).ker = Z := QuotientGroup.ker_mk' Z
  have hdvd : Nat.card ↥Z ∣ 3 := by
    have h := CFSG.Quasithin.Vol2.Ch11.SecA.card_scalars_subgroupOf_dvd
      (K := F4) (H := StatedSU 6 (2 ^ 1) F4)
    simpa [Z, Nat.card_eq_fintype_card, F4.card] using h
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (p := 3) (m := 1) Nat.prime_three).1 hdvd
  exact IsPGroup.iff_card.2 ⟨k, hπker ▸ hk⟩

theorem u6TwoOddCoreThree_of_cenD
    (h : ∀ (B : GL (Fin 6) F4), B ∈ primeFormUnitary hF4 (idGram F4 6) →
      (∃ c : F4ˣ, B ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c) →
      pPrimeCore 3 (CenD B) = ⊥) : U6TwoOddCoreThree := by
  intro β hβ
  obtain ⟨B, hB, ⟨c, hBc⟩, hβuv⟩ := LevelLieU6.exists_unitary_of_pow_three β hβ
  let Z : Subgroup (StatedSU 6 (2 ^ 1) F4) :=
    (StatedScalars (Fin 6) F4).subgroupOf (StatedSU 6 (2 ^ 1) F4)
  let π : M6 →* S6 := QuotientGroup.mk' Z
  set α : MulAut M6 := conjM6 ⟨B, hB⟩ with hα
  have hαβ : ∀ k : M6, π (α k) = β (π k) := by
    intro k
    have h1 : β (QuotientGroup.mk k) = QuotientGroup.mk (conjM6 ⟨B, hB⟩ k) :=
      hβuv k (conjM6 ⟨B, hB⟩ k) (by rw [conjM6_apply])
    show QuotientGroup.mk (α k) = β (QuotientGroup.mk k)
    rw [show α k = conjM6 ⟨B, hB⟩ k from rfl, ← h1]
  have hker : π.ker ≤ Subgroup.center M6 := by
    have hπker : π.ker = Z := QuotientGroup.ker_mk' Z
    rw [hπker]
    exact CFSG.Quasithin.statedSU_scalars_le_center
  have hpker : IsPGroup 3 π.ker := isPGroup_three_ker_mk
  have hfixα : fixSubgroup α = CenD B := by
    rw [hα]
    exact fixSubgroup_conjM6 ⟨B, hB⟩
  refine pPrimeCore_eq_bot_of_fixSubgroup Nat.prime_three π
    (QuotientGroup.mk'_surjective Z) hker hpker α β hαβ ?_
  rw [hfixα]
  exact h B hB ⟨c, hBc⟩


@[expose] def U6TwoBlockCore : Prop :=
  ∀ {d : Fin 6 → F4} {D : GL (Fin 6) F4}
    (hD : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d) (c : F4),
    pPrimeCore 3 ↥((blkHom hD c).range) = ⊥

@[expose] def U6TwoNineCore : Prop :=
  ∀ (B : GL (Fin 6) F4) (c : F4ˣ), B ∈ primeFormUnitary hF4 (idGram F4 6) → c ≠ 1 →
    B ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c → pPrimeCore 3 (CenD B) = ⊥

theorem pPrimeCore_cenD_diag (hblocks : U6TwoBlockCore) {D : GL (Fin 6) F4} {d : Fin 6 → F4}
    (hD : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d) :
    pPrimeCore 3 (CenD D) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact CFSG.pPrimeCore_eq_bot_of_pi_range_eq_bot (fun c : F4 => blkHom hD c)
    (CFSG.LocalAnalysis.GLTheoremA.LevelLieU6.blkPi_injective hD)
    (fun c => hblocks hD c)

theorem pPrimeCore_cenD_of_cube_one (hblocks : U6TwoBlockCore)
    (B : primeFormUnitary hF4 (idGram F4 6)) (hB3 : B ^ 3 = 1) :
    pPrimeCore 3 (CenD (B : GL (Fin 6) F4)) = ⊥ := by
  obtain ⟨P, d, hd⟩ := exists_diag6 B hB3
  set D : GL (Fin 6) F4 := ((P⁻¹ * B * P : primeFormUnitary hF4 (idGram F4 6)) : GL (Fin 6) F4)
    with hDdef
  have hDmat : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d := hd
  have hcore : pPrimeCore 3 (CenD D) = ⊥ := pPrimeCore_cenD_diag hblocks hDmat
  have hmap : (CenD (B : GL (Fin 6) F4)).map (conjM6 P⁻¹).toMonoidHom = CenD D := by
    rw [map_CenD_conj]
    rfl
  have e : ↥(CenD (B : GL (Fin 6) F4)) ≃* ↥(CenD D) :=
    (Subgroup.equivMapOfInjective _ (conjM6 P⁻¹).toMonoidHom
      (MulEquiv.injective _)).trans (MulEquiv.subgroupCongr hmap)
  exact pPrimeCore_eq_bot_of_mulEquiv 3 e.symm hcore

theorem pPrimeCore_cenD (hblocks : U6TwoBlockCore) (hnine : U6TwoNineCore)
    (B : GL (Fin 6) F4) (hB : B ∈ primeFormUnitary hF4 (idGram F4 6))
    (hBc : ∃ c : F4ˣ, B ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c) :
    pPrimeCore 3 (CenD B) = ⊥ := by
  obtain ⟨c, hc⟩ := hBc
  by_cases hc1 : c = 1
  · subst hc1
    have hB3 : (⟨B, hB⟩ : primeFormUnitary hF4 (idGram F4 6)) ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, hc]
      simp
    exact pPrimeCore_cenD_of_cube_one hblocks ⟨B, hB⟩ hB3
  · exact hnine B c hB hc1 hc

theorem u6TwoOddCoreThree_of_cases (hblocks : U6TwoBlockCore) (hnine : U6TwoNineCore) :
    U6TwoOddCoreThree :=
  u6TwoOddCoreThree_of_cenD (pPrimeCore_cenD hblocks hnine)

end CFSG.LocalAnalysis.GLTheoremA.KD1912

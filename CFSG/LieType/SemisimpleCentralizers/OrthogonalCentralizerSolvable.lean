module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivOmega
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaFinal
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.PLengthLemmas
public import CFSG.GroupTheory.QuasisimplePSolvable
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalPComponentCore

public section

namespace CFSG.LieType.SemisimpleCentralizers

open CFSG.Assembly CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  QuadraticMap

theorem isSolvable_spinPlus_centralizer_of_hasNormalPComplement
    {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hn : 3 ≤ n)
    {G : Type*} [Group G] [Finite G]
    {ψ : spinGroup (quadPlus n K) →* G}
    (hker : ψ.ker ≤ Subgroup.center (spinGroup (quadPlus n K)))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K ^ 2 - 1)
    {E : Subgroup G} (hE : IsPGroup p E)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hdiag : ∀ e ∈ E, GGPsiInnerDiag (plusDatum n K hn) ψ e)
    (hNPC : CFSG.HasNormalPComplement p
      ↥(⁅ψ.range ⊓ Subgroup.centralizer (E : Set G),
         ψ.range ⊓ Subgroup.centralizer (E : Set G)⁆)) :
    Group.IsSolvable ↥(ψ.range ⊓ Subgroup.centralizer (E : Set G)) := by
  classical
  let H : Subgroup G := ψ.range ⊓ Subgroup.centralizer (E : Set G)
  have hNPC' : CFSG.HasNormalPComplement p ↥(⁅H, H⁆) := by
    simpa [H] using hNPC
  have hlayer := LayerFacts.ggLayer_spinPlus (K := K) ggOrthCentralizerCoreInput_holds hn hker hp
    hp2 hE hcomm hdiag
  have hno : ∀ X : Subgroup G, ¬ IsComponentOf X H := by
    intro X hX
    have hXq : CFSG.IsQuasisimple X :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native X).mp hX.2.2
    have hXperf : ⁅X, X⁆ = X := LayerFacts.ggCommutator_eq_of_isQuasisimple hXq
    have hXleD : X ≤ ⁅H, H⁆ := by
      rw [← hXperf]
      exact Subgroup.commutator_mono hX.1 hX.1
    have hNPCX : CFSG.HasNormalPComplement p ↥X :=
      CFSG.hasNormalPComplement_of_le p hXleD hNPC'
    have hpX : p ∣ Nat.card X :=
      LayerPDiv.dvd_card_of_isComponentOf_spinPlus_family hn hker hp hp2 hpK hE hdiag hX
    haveI : Group.IsPerfect ↥X := LayerFacts.ggIsPerfect_of_commutator_eq hXperf
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨N, hN, hcop, hpg⟩ := hNPCX
    haveI : N.Normal := hN
    have hNtop : N = ⊤ :=
      CFSG.ComponentClassification.LiteratureLocal.eq_top_of_isPGroup_quotient_of_perfect N hpg
    have hcardN : Nat.card ↥N = Nat.card ↥X := by rw [hNtop, Subgroup.card_top]
    have hcopX : Nat.Coprime p (Nat.card ↥X) := by rwa [← hcardN]
    exact (hp.coprime_iff_not_dvd).mp hcopX hpX
  have hlayerbot : LargeEvenLayer H = ⊥ := by
    have hset : {X : Subgroup G | IsComponentOf X H} = ∅ := by
      ext X
      simp [hno X]
    show LargeEvenLayer H = ⊥
    rw [show LargeEvenLayer H = sSup {X : Subgroup G | IsComponentOf X H} from rfl, hset,
      sSup_empty]
  have hpc : CFSG.Quasithin.perfectCore H = ⊥ := by
    have hle : CFSG.Quasithin.perfectCore H ≤ LargeEvenLayer H :=
      hlayer.2 (CFSG.Quasithin.perfectCore H)
        (by simpa [H] using CFSG.Quasithin.perfectCore_le H)
        (CFSG.Quasithin.perfectCore_perfect H)
    rw [hlayerbot, le_bot_iff] at hle
    exact hle
  exact (CFSG.Quasithin.isSolvable_iff_perfectCore_eq_bot H).mpr hpc

theorem isSolvable_spinMinus_centralizer_of_hasNormalPComplement
    {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hn : 4 ≤ n)
    {G : Type*} [Group G] [Finite G]
    {ψ : spinGroup (quadMinus n K b c) →* G}
    (hker : ψ.ker ≤ Subgroup.center (spinGroup (quadMinus n K b c)))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K ^ 2 - 1)
    {E : Subgroup G} (hE : IsPGroup p E)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hdiag : ∀ e ∈ E, GGPsiInnerDiag (CFSG.LieType.Universal.Spin.Twisted.minusDatum n hirr) ψ e)
    (hNPC : CFSG.HasNormalPComplement p
      ↥(⁅ψ.range ⊓ Subgroup.centralizer (E : Set G),
         ψ.range ⊓ Subgroup.centralizer (E : Set G)⁆)) :
    Group.IsSolvable ↥(ψ.range ⊓ Subgroup.centralizer (E : Set G)) := by
  classical
  let H : Subgroup G := ψ.range ⊓ Subgroup.centralizer (E : Set G)
  have hNPC' : CFSG.HasNormalPComplement p ↥(⁅H, H⁆) := by
    simpa [H] using hNPC
  have hlayer := LayerFacts.ggLayer_spinMinus (K := K) ggOrthCentralizerCoreInput_holds hirr hn
    hker hp hp2 hE hcomm hdiag
  have hno : ∀ X : Subgroup G, ¬ IsComponentOf X H := by
    intro X hX
    have hXq : CFSG.IsQuasisimple X :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native X).mp hX.2.2
    have hXperf : ⁅X, X⁆ = X := LayerFacts.ggCommutator_eq_of_isQuasisimple hXq
    have hXleD : X ≤ ⁅H, H⁆ := by
      rw [← hXperf]
      exact Subgroup.commutator_mono hX.1 hX.1
    have hNPCX : CFSG.HasNormalPComplement p ↥X :=
      CFSG.hasNormalPComplement_of_le p hXleD hNPC'
    have hpX : p ∣ Nat.card X :=
      LayerPDiv.dvd_card_of_isComponentOf_spinMinus_family hirr hn hker hp hp2 hpK hE hdiag hX
    haveI : Group.IsPerfect ↥X := LayerFacts.ggIsPerfect_of_commutator_eq hXperf
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨N, hN, hcop, hpg⟩ := hNPCX
    haveI : N.Normal := hN
    have hNtop : N = ⊤ :=
      CFSG.ComponentClassification.LiteratureLocal.eq_top_of_isPGroup_quotient_of_perfect N hpg
    have hcardN : Nat.card ↥N = Nat.card ↥X := by rw [hNtop, Subgroup.card_top]
    have hcopX : Nat.Coprime p (Nat.card ↥X) := by rwa [← hcardN]
    exact (hp.coprime_iff_not_dvd).mp hcopX hpX
  have hlayerbot : LargeEvenLayer H = ⊥ := by
    have hset : {X : Subgroup G | IsComponentOf X H} = ∅ := by
      ext X
      simp [hno X]
    show LargeEvenLayer H = ⊥
    rw [show LargeEvenLayer H = sSup {X : Subgroup G | IsComponentOf X H} from rfl, hset,
      sSup_empty]
  have hpc : CFSG.Quasithin.perfectCore H = ⊥ := by
    have hle : CFSG.Quasithin.perfectCore H ≤ LargeEvenLayer H :=
      hlayer.2 (CFSG.Quasithin.perfectCore H)
        (by simpa [H] using CFSG.Quasithin.perfectCore_le H)
        (CFSG.Quasithin.perfectCore_perfect H)
    rw [hlayerbot, le_bot_iff] at hle
    exact hle
  exact (CFSG.Quasithin.isSolvable_iff_perfectCore_eq_bot H).mpr hpc

end CFSG.LieType.SemisimpleCentralizers

module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivSL
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalPComponentCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.PLengthLemmas

public section

namespace CFSG.LieType.SemisimpleCentralizers

open CFSG.Assembly
open CFSG.StandardType

theorem isSolvable_centralizer_of_hasNormalPComplement
    {m : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {G : Type*} [Group G] [Finite G]
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F ^ 2 - 1)
    {E : Subgroup G} (hE : IsPGroup p E)
    (hEA : ∀ e ∈ E, ∃ A, (e, A) ∈ LinFusion.ggInducedPairs ψ)
    (hNPC : CFSG.HasNormalPComplement p
      ↥(⁅ψ.range ⊓ Subgroup.centralizer (E : Set G),
         ψ.range ⊓ Subgroup.centralizer (E : Set G)⁆)) :
    Group.IsSolvable ↥(ψ.range ⊓ Subgroup.centralizer (E : Set G)) := by
  classical
  let H : Subgroup G := ψ.range ⊓ Subgroup.centralizer (E : Set G)
  have hNPC' : CFSG.HasNormalPComplement p ↥(⁅H, H⁆) := by
    simpa [H] using hNPC
  have hlayer := LayerFacts.ggLayer_sl (m := m) (F := F) (G := G) hker hp hp2 hE hEA
  have hno : ∀ K : Subgroup G, ¬ IsComponentOf K H := by
    intro K hK
    have hKq : CFSG.IsQuasisimple K :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native K).mp hK.2.2
    have hKperf : ⁅K, K⁆ = K := LayerFacts.ggCommutator_eq_of_isQuasisimple hKq
    have hKleD : K ≤ ⁅H, H⁆ := by
      rw [← hKperf]
      exact Subgroup.commutator_mono hK.1 hK.1
    have hNPCK : CFSG.HasNormalPComplement p ↥K :=
      CFSG.hasNormalPComplement_of_le p hKleD hNPC'
    have hpK : p ∣ Nat.card K :=
      LayerPDiv.dvd_card_of_isComponentOf_sl hker hp hp2 hpF hE hEA hK
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Group.IsPerfect ↥K := LayerFacts.ggIsPerfect_of_commutator_eq hKperf
    obtain ⟨N, hN, hcop, hpg⟩ := hNPCK
    haveI : N.Normal := hN
    have hNtop : N = ⊤ :=
      CFSG.ComponentClassification.LiteratureLocal.eq_top_of_isPGroup_quotient_of_perfect N hpg
    have hcardN : Nat.card ↥N = Nat.card ↥K := by rw [hNtop, Subgroup.card_top]
    have hcopK : Nat.Coprime p (Nat.card ↥K) := by rwa [← hcardN]
    exact (hp.coprime_iff_not_dvd).mp hcopK hpK
  have hlayerbot : LargeEvenLayer H = ⊥ := by
    have hset : {K : Subgroup G | IsComponentOf K H} = ∅ := by
      ext K
      simp [hno K]
    show LargeEvenLayer H = ⊥
    rw [show LargeEvenLayer H = sSup {K : Subgroup G | IsComponentOf K H} from rfl, hset,
      sSup_empty]
  have hpc : CFSG.Quasithin.perfectCore H = ⊥ := by
    have hle : CFSG.Quasithin.perfectCore H ≤ LargeEvenLayer H :=
      hlayer.2 (CFSG.Quasithin.perfectCore H)
        (by simpa [H] using CFSG.Quasithin.perfectCore_le H)
        (CFSG.Quasithin.perfectCore_perfect H)
    rw [hlayerbot, le_bot_iff] at hle
    exact hle
  exact (CFSG.Quasithin.isSolvable_iff_perfectCore_eq_bot H).mpr hpc

theorem isSolvable_centralizer_of_hasNormalPComplement_commutator
    {m : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {G : Type*} [Group G] [Finite G]
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F ^ 2 - 1)
    {E : Subgroup G} (hE : IsPGroup p E)
    (hEA : ∀ e ∈ E, ∃ A, (e, A) ∈ LinFusion.ggInducedPairs ψ)
    (hNPC : CFSG.HasNormalPComplement p
      ↥(_root_.commutator ↥(ψ.range ⊓ Subgroup.centralizer (E : Set G)))) :
    Group.IsSolvable ↥(ψ.range ⊓ Subgroup.centralizer (E : Set G)) := by
  classical
  let H : Subgroup G := ψ.range ⊓ Subgroup.centralizer (E : Set G)
  have hNPC' : CFSG.HasNormalPComplement p ↥(_root_.commutator ↥H) := by
    simpa [H] using hNPC
  have hmap : CFSG.HasNormalPComplement p ↥((_root_.commutator ↥H).map H.subtype) :=
    CFSG.hasNormalPComplement_of_equiv p
      (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective) hNPC'
  have hNPCamb : CFSG.HasNormalPComplement p ↥(⁅H, H⁆) := by
    rw [← Subgroup.map_subtype_commutator H]
    exact hmap
  exact isSolvable_centralizer_of_hasNormalPComplement (m := m) (F := F) (G := G)
    hker hp hp2 hpF hE hEA (by simpa [H] using hNPCamb)

end CFSG.LieType.SemisimpleCentralizers

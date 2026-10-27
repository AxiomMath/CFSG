module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55D4Ord3Tor
public import CFSG.LocalAnalysis.OddStandard.GH71.S55D4Ord3Weyl2
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnSub
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der61a
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der69
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Field
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Prop67
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Statements
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt7
public import CFSG.LinearAlgebra.OddSolvableUnitary.HomologySaturation
public import CFSG.RankThree.Chevalley.SteinbergCDTrialityTwelveLocalCore
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2SplitInnerActor
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneOrthogonal
public import CFSG.RankThree.PartOne.KGD.D4T36Frame

public section

namespace CFSG.OddStandard.GH71.S55

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.RankThree.PartOne.KE


section Field

variable {M : Type} [Field M]

theorem monomial_conj_rootDiagUnit {x : ModGL TwistTag.D4.tag M}
    (hx : x ∈ monomialSubgroup TwistTag.D4.tag M) {w : WeylGroup TwistTag.D4.tag}
    (hxw : MapsRootLines x w) (b : Fin TwistTag.D4.tag.rank → Mˣ) :
    x * rootDiagUnit TwistTag.D4.tag b * x⁻¹ = rootDiagUnit TwistTag.D4.tag (weylTuple w b) := by
  obtain ⟨w', k, hk, hxk⟩ := monomialSubgroup_le_torusWeylCosets hx
  have hw : w' = w := (mapsRootLines_mul_canonicalRep hk w').unique (hxk ▸ hxw)
  subst hw
  rw [hxk]
  have h3 := canonicalRep_conj_rootDiagUnit (K := M) w' b
  have h4 := rootDiagUnit_mul_comm_of_mem_torusGroup (weylTuple w' b) hk
  calc k * canonicalRep (coxeterSystem TwistTag.D4.tag) M w' * rootDiagUnit TwistTag.D4.tag b *
        (k * canonicalRep (coxeterSystem TwistTag.D4.tag) M w')⁻¹ =
      k * (canonicalRep (coxeterSystem TwistTag.D4.tag) M w' * rootDiagUnit TwistTag.D4.tag b *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) M w')⁻¹) * k⁻¹ := by group
    _ = rootDiagUnit TwistTag.D4.tag (weylTuple w' b) := by rw [h3, ← h4, mul_inv_cancel_right]

theorem weylTuple_opposition_d4Sign (c : Fin TwistTag.D4.tag.rank → ℤ) :
    weylTuple trialityOppositionWeyl (d4Sign M c) = d4Sign M c := by
  funext i
  simp only [weylTuple]
  have hinv : trialityOppositionWeyl⁻¹ • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) =
      -Pi.single i 1 := by
    rw [inv_smul_eq_iff, trialityOppositionWeyl_smul, neg_neg]
  rw [hinv, rootChar_d4Sign]
  change _ = (-1 : Mˣ) ^ c i
  have h : (∑ j, c j * (-Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) j) = -c i := by
    simp [Pi.single_apply]
  rw [h]
  have h1 : (-1 : Mˣ) ^ (-c i - c i) = 1 :=
    (Int.even_iff.2 (show (-c i - c i) % 2 = 0 by omega)).neg_one_zpow
  rw [zpow_sub, mul_inv_eq_one] at h1
  exact h1

theorem diagramMap_conj_d4Sign (c : Fin TwistTag.D4.tag.rank → ℤ)
    (hρ : ∀ j, c (TwistTag.D4.perm.symm j) = c j) :
    (diagramMap TwistTag.D4 M)⁻¹ * rootDiagUnit TwistTag.D4.tag (d4Sign M c) *
      diagramMap TwistTag.D4 M = rootDiagUnit TwistTag.D4.tag (d4Sign M c) := by
  have h : diagramMap TwistTag.D4 M * rootDiagUnit TwistTag.D4.tag (d4Sign M c) =
      rootDiagUnit TwistTag.D4.tag (d4Sign M c) * diagramMap TwistTag.D4 M := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul]
    change (diagramMap TwistTag.D4 M : Module.End M (RootModule TwistTag.D4.tag M)) *
      rootDiag (d4Sign M c) = rootDiag (d4Sign M c) * _
    rw [diagramMap_mul_rootDiag]
    congr 2
    funext j
    simp [d4Sign, hρ]
  rw [mul_assoc, ← h, ← mul_assoc, inv_mul_cancel, one_mul]

end Field

section Frame

variable {p f : ℕ} [Fact p.Prime] {K : Type} [Field K] (σ : K ≃+* K) {L : Type}
  [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L p] {g₀ : ModGL TwistTag.D4.tag L}

theorem rootDiagUnit_d4Sign_mem_range (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (hg₀ : D4MinusFrame p f L g₀) (c : Fin TwistTag.D4.tag.rank → ℤ)
    (i : Fin TwistTag.D4.tag.rank) (hci : ∀ j, (TwistTag.D4.tag.cartan i j - c j) % 2 = 0)
    (hρ : ∀ j, c (TwistTag.D4.perm.symm j) = c j) :
    rootDiagUnit TwistTag.D4.tag (d4Sign L c) ∈ (d4MinusPsi σ L g₀).range := by
  obtain ⟨hg₀C, -, hg₀F⟩ := hg₀
  have hFr : ∀ c, iterateFrobenius L p f c = c ^ (p ^ f) := fun c => iterateFrobenius_def p f c
  rw [d4MinusPsi_mem_range_iff (Fact.out : p.Prime) hf hK hσ _ hFr hg₀C hg₀F]
  have ht : torusElt TwistTag.D4.tag L i (-1) = rootDiagUnit TwistTag.D4.tag (d4Sign L c) := by
    rw [torusElt_eq_rootDiagUnit]
    exact congrArg _ (d4Sign_congr hci)
  refine ⟨ht ▸ torusElt_mem_adjointGroup i (-1), ?_⟩
  have hF : twistHom TwistTag.D4 L (iterateFrobenius L p f)
      (rootDiagUnit TwistTag.D4.tag (d4Sign L c)) = rootDiagUnit TwistTag.D4.tag (d4Sign L c) := by
    rw [twistHom_rootDiagUnit_eq]
    congr 1
    funext j
    simp [d4Sign, hρ, map_zpow]
  rw [hF, monomial_conj_rootDiagUnit trialityOpposition_mem_monomialSubgroup
    mapsRootLines_trialityOpposition, weylTuple_opposition_d4Sign]

theorem diagramMap_conj_eq_of_mem_range (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (hg₀ : D4MinusFrame p f L g₀) {x : ModGL TwistTag.D4.tag L}
    (hx : x ∈ (d4MinusPsi σ L g₀).range) :
    (diagramMap TwistTag.D4 L)⁻¹ * x * diagramMap TwistTag.D4 L = trialityOpposition L *
      Units.map (entrywiseHom (iterateFrobenius L p f)) x * (trialityOpposition L)⁻¹ := by
  obtain ⟨hg₀C, -, hg₀F⟩ := hg₀
  have hFr : ∀ c, iterateFrobenius L p f c = c ^ (p ^ f) := fun c => iterateFrobenius_def p f c
  obtain ⟨-, hzx⟩ :=
    (d4MinusPsi_mem_range_iff (Fact.out : p.Prime) hf hK hσ _ hFr hg₀C hg₀F x).1 hx
  rw [twistHom_apply] at hzx
  have hPz := diagramMap_comm_trialityOpposition (L := L)
  conv_lhs => rw [← hzx]
  calc _ = ((diagramMap TwistTag.D4 L)⁻¹ * (trialityOpposition L * diagramMap TwistTag.D4 L)) *
        Units.map (entrywiseHom (iterateFrobenius L p f)) x *
        ((trialityOpposition L * diagramMap TwistTag.D4 L)⁻¹ * diagramMap TwistTag.D4 L) := by
          group
    _ = _ := by rw [← hPz]; group

theorem diagramMap_conj_monomial_of_mem_range [IsAlgClosed L] (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (p ^ f)) (hg₀ : D4MinusFrame p f L g₀)
    {x : ModGL TwistTag.D4.tag L} (hx : x ∈ (d4MinusPsi σ L g₀).range)
    (hxM : x ∈ monomialSubgroup TwistTag.D4.tag L) {w : WeylGroup TwistTag.D4.tag}
    (hxw : MapsRootLines x w) :
    (diagramMap TwistTag.D4 L)⁻¹ * x * diagramMap TwistTag.D4 L ∈
        monomialSubgroup TwistTag.D4.tag L ∧
      MapsRootLines ((diagramMap TwistTag.D4 L)⁻¹ * x * diagramMap TwistTag.D4 L) w := by
  rw [diagramMap_conj_eq_of_mem_range σ hf hK hσ hg₀ hx]
  obtain ⟨w', k, hk, hxk⟩ := monomialSubgroup_le_torusWeylCosets hxM
  have hw : w' = w := (mapsRootLines_mul_canonicalRep hk w').unique (hxk ▸ hxw)
  subst hw
  set δ : L ≃+* L := iterateFrobeniusEquiv L p f
  have hδ : δ.toRingHom = iterateFrobenius L p f := rfl
  have hFx : Units.map (entrywiseHom (iterateFrobenius L p f)) x =
      Units.map (entrywiseHom δ.toRingHom) k *
        canonicalRep (coxeterSystem TwistTag.D4.tag) L w' := by
    rw [hxk, map_mul, ← hδ, entrywise_canonicalRep]
  have hk' := entrywise_mem_torusGroup (σ := δ) hk
  have hzM := trialityOpposition_mem_monomialSubgroup (K := L)
  refine ⟨?_, ?_⟩
  · rw [hFx]
    exact mul_mem (mul_mem hzM (mul_mem (torusGroup_le_monomialSubgroup hk')
      (canonicalRep_mem_monomialSubgroup L w'))) (inv_mem hzM)
  · have h1 : MapsRootLines (Units.map (entrywiseHom (iterateFrobenius L p f)) x) w' := by
      rw [hFx]
      exact mapsRootLines_mul_canonicalRep hk' w'
    have h2 := ((mapsRootLines_trialityOpposition (K := L)).mul h1).mul
      (mapsRootLines_trialityOpposition (K := L)).inv
    rwa [d4Minus_oppositionWeyl_comm, mul_inv_cancel_right] at h2

end Frame

end CFSG.OddStandard.GH71.S55

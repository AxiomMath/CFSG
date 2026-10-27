module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.SmallQCommute
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.SmallQE8EightRank
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.SmallQE8EightEls

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration CFSG.LieType.Steinberg.Adjoint
open scoped Matrix

set_option linter.unusedSectionVars false


section E8


variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem rootChar_eq_one_E8_eight (S : LangSetup .E8 L p) (hq : S.D.q = 2) (hp : p = 17)
    {D₁ : Subgroup (ModGL .E8 L)} (hD₁E : D₁ ≤ S.E) (hD₁c : Nat.card D₁ = p ^ 2)
    {a : Fin Tag.E8.rank → Lˣ} (haT : rootDiagUnit Tag.E8 a ∈ torusGroup Tag.E8 L)
    (hcomm : ∀ x ∈ rigidTestSet S D₁, Commute (rootDiagUnit Tag.E8 a) x)
    {β : Fin Tag.E8.rank → ℤ} (hm : RankOneOrbit S.ρ β 4) : rootChar a β = 1 := by
  have h2L : (2 : L) = 0 := by
    have h := S.hqpow.2
    rw [hq] at h
    exact_mod_cast h
  haveI : CharP L 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2L
  have hQ4 : 4 ≤ S.D.q ^ 4 := by rw [hq]; norm_num
  have hpm : p ∣ S.D.q ^ (2 * 4) - 1 := by rw [hq, hp]; norm_num
  obtain ⟨θ, R, hbig, hθ, hθ1, hθθ, hR⟩ := exists_bigComponent_pair S
    (Or.inr (Or.inr (Or.inr rfl))) hm hQ4 (by omega) hpm h2L hD₁E hD₁c
  exact rootChar_eq_one_of_commute_pair hm.1 haT hθ hθ1 hθθ hR (hcomm _ (Or.inl hbig))


private theorem E8_artifact_length : ∀ r ∈ Tag.E8.artifactRoots, r.length = Tag.E8.rank := by
  decide +kernel

private theorem chk_e1 : RankOneChk Tag.E8.rank (cartanList Tag.E8) e8EightMat
    Tag.E8.artifactRoots [0, 1, 0, 0, 0, 0, 0, 0] 4 := by decide +kernel

private theorem chk_e3 : RankOneChk Tag.E8.rank (cartanList Tag.E8) e8EightMat
    Tag.E8.artifactRoots [0, 0, 0, 1, 0, 0, 0, 0] 4 := by decide +kernel

private theorem chk_e4 : RankOneChk Tag.E8.rank (cartanList Tag.E8) e8EightMat
    Tag.E8.artifactRoots [0, 0, 0, 0, 1, 0, 0, 0] 4 := by decide +kernel

private theorem chk_e6 : RankOneChk Tag.E8.rank (cartanList Tag.E8) e8EightMat
    Tag.E8.artifactRoots [0, 0, 0, 0, 0, 0, 1, 0] 4 := by decide +kernel

private theorem chk_b1 : RankOneChk Tag.E8.rank (cartanList Tag.E8) e8EightMat
    Tag.E8.artifactRoots [0, 0, 0, 0, 0, 0, 1, 1] 4 := by decide +kernel

private theorem chk_b2 : RankOneChk Tag.E8.rank (cartanList Tag.E8) e8EightMat
    Tag.E8.artifactRoots [0, 0, 0, 0, 0, 1, 1, 0] 4 := by decide +kernel

private theorem chk_b3 : RankOneChk Tag.E8.rank (cartanList Tag.E8) e8EightMat
    Tag.E8.artifactRoots [1, 0, 1, 0, 0, 0, 0, 0] 4 := by decide +kernel

private theorem chk_b4 : RankOneChk Tag.E8.rank (cartanList Tag.E8) e8EightMat
    Tag.E8.artifactRoots [0, 0, 1, 1, 1, 0, 0, 0] 4 := by decide +kernel

private theorem toVec_e1 : (toVec Tag.E8.rank [0, 1, 0, 0, 0, 0, 0, 0] : Fin Tag.E8.rank → ℤ) =
    Pi.single 1 1 := by decide +kernel

private theorem toVec_e3 : (toVec Tag.E8.rank [0, 0, 0, 1, 0, 0, 0, 0] : Fin Tag.E8.rank → ℤ) =
    Pi.single 3 1 := by decide +kernel

private theorem toVec_e4 : (toVec Tag.E8.rank [0, 0, 0, 0, 1, 0, 0, 0] : Fin Tag.E8.rank → ℤ) =
    Pi.single 4 1 := by decide +kernel

private theorem toVec_e6 : (toVec Tag.E8.rank [0, 0, 0, 0, 0, 0, 1, 0] : Fin Tag.E8.rank → ℤ) =
    Pi.single 6 1 := by decide +kernel

private theorem toVec_b1 : (toVec Tag.E8.rank [0, 0, 0, 0, 0, 0, 1, 1] : Fin Tag.E8.rank → ℤ) =
    Pi.single 6 1 + Pi.single 7 1 := by decide +kernel

private theorem toVec_b2 : (toVec Tag.E8.rank [0, 0, 0, 0, 0, 1, 1, 0] : Fin Tag.E8.rank → ℤ) =
    Pi.single 5 1 + Pi.single 6 1 := by decide +kernel

private theorem toVec_b3 : (toVec Tag.E8.rank [1, 0, 1, 0, 0, 0, 0, 0] : Fin Tag.E8.rank → ℤ) =
    Pi.single 0 1 + Pi.single 2 1 := by decide +kernel

private theorem toVec_b4 : (toVec Tag.E8.rank [0, 0, 1, 1, 1, 0, 0, 0] : Fin Tag.E8.rank → ℤ) =
    Pi.single 2 1 + Pi.single 3 1 + Pi.single 4 1 := by decide +kernel

theorem centralizerTrivial_E8_eight (S : LangSetup .E8 L p) (hρ : RhoIs S e8EightMat)
    (hq : S.D.q = 2) (hp : p = 17) {D₁ : Subgroup (ModGL .E8 L)} (hD₁E : D₁ ≤ S.E)
    (hD₁c : Nat.card D₁ = p ^ 2) : CentralizerTrivial S D₁ := by
  intro z hz hcomm
  have h2L : (2 : L) = 0 := by
    have h := S.hqpow.2
    rw [hq] at h
    exact_mod_cast h
  haveI : CharP L 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2L
  obtain ⟨ζ, hζ⟩ := SmallQ17.exists_zeta17 (L := L)
  have hzT : z ∈ torusGroup Tag.E8 L := SmallQ17.mem_torusGroup_of_commute_plane S hρ hq hp hζ
    hD₁E hD₁c hz fun x hx => hcomm x (Or.inr hx)
  obtain ⟨a, ha⟩ := torusGroup_le_range_rootDiagUnitHom hzT
  have hza : z = rootDiagUnit Tag.E8 a := ha.symm
  have haT : rootDiagUnit Tag.E8 a ∈ torusGroup Tag.E8 L := by rw [← hza]; exact hzT
  have hcomm' : ∀ x ∈ rigidTestSet S D₁, Commute (rootDiagUnit Tag.E8 a) x := by
    rw [← hza]
    exact hcomm
  have key : ∀ b : List ℤ, RankOneChk Tag.E8.rank (cartanList Tag.E8) e8EightMat
      Tag.E8.artifactRoots b 4 → rootChar a (toVec Tag.E8.rank b) = 1 := fun b hchk =>
    rootChar_eq_one_E8_eight S hq hp hD₁E hD₁c haT hcomm'
      (rankOneOrbit_of_check S (Or.inr (Or.inr (Or.inr rfl))) (toMat_cartanList _) hρ
        E8_artifact_length hchk)
  have r1 : a 1 = 1 := by
    have := key _ chk_e1
    rwa [toVec_e1, CTTorus.rootChar_single] at this
  have r3 : a 3 = 1 := by
    have := key _ chk_e3
    rwa [toVec_e3, CTTorus.rootChar_single] at this
  have r4 : a 4 = 1 := by
    have := key _ chk_e4
    rwa [toVec_e4, CTTorus.rootChar_single] at this
  have r6 : a 6 = 1 := by
    have := key _ chk_e6
    rwa [toVec_e6, CTTorus.rootChar_single] at this
  have r7 : a 7 = 1 := by
    have := key _ chk_b1
    rwa [toVec_b1, rootChar_add, CTTorus.rootChar_single, CTTorus.rootChar_single, r6,
      one_mul] at this
  have r5 : a 5 = 1 := by
    have := key _ chk_b2
    rwa [toVec_b2, rootChar_add, CTTorus.rootChar_single, CTTorus.rootChar_single, r6,
      mul_one] at this
  have r2 : a 2 = 1 := by
    have := key _ chk_b4
    rwa [toVec_b4, rootChar_add, rootChar_add, CTTorus.rootChar_single, CTTorus.rootChar_single,
      CTTorus.rootChar_single, r3, r4, mul_one, mul_one] at this
  have r0 : a 0 = 1 := by
    have := key _ chk_b3
    rwa [toVec_b3, rootChar_add, CTTorus.rootChar_single, CTTorus.rootChar_single, r2,
      mul_one] at this
  have hall : a = 1 := by
    funext i
    fin_cases i <;> first | exact r0 | exact r1 | exact r2 | exact r3 | exact r4 | exact r5 | exact r6 | exact r7
  rw [hza, hall, rootDiagUnit_one]

theorem smallQ_E8_eight : SmallQ_E8_eight := by
  intro L _ _ p S hp7 hAlg he hρ hq
  have hp : p = 17 := by
    have he' : orderOf (((2 : ℕ)) : ZMod p) = 8 := by rw [← hq]; exact he
    have h8 : ((2 : ℕ) : ZMod p) ^ 8 = 1 := by
      rw [← he']
      exact pow_orderOf_eq_one _
    have h255 : ((255 : ℕ) : ZMod p) = 0 := by
      push_cast at h8 ⊢
      linear_combination h8
    have hd : p ∣ 255 := (ZMod.natCast_eq_zero_iff 255 p).1 h255
    have h255' : (255 : ℕ) = 3 * 5 * 17 := by norm_num
    rw [h255'] at hd
    rcases (Nat.Prime.dvd_mul S.hp).1 hd with h15 | h17
    · rcases (Nat.Prime.dvd_mul S.hp).1 h15 with h3 | h5
      · have := Nat.le_of_dvd (by norm_num) h3
        omega
      · have := Nat.le_of_dvd (by norm_num) h5
        omega
    · exact (Nat.prime_dvd_prime_iff_eq S.hp (by norm_num)).1 h17
  exact setupRigid_E8 S (by omega) hAlg (fun D₁ _ _ => noFrobeniusInner_of_q_eq_two S hq D₁)
    (fun D₁ hD₁E hD₁c => centralizerTrivial_E8_eight S hρ hq hp hD₁E hD₁c)

end E8

end CFSG.HardMathSupport.Timmesfeld.LangTorus

end

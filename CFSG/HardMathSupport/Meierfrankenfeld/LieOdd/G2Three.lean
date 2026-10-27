module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.LiftOrbitMap
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.LnOrbit
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Hom
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.LocalAnalysis.ComponentInitial CFSG.Blueprint.Chevalley

theorem scalars_eq_bot_of_charP_three {K : Type} [Field K] [CharP K 3] :
    LinearFlag.scalars 3 K = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [eq_bot_iff]
  rintro A ⟨c, hc, hA⟩
  rw [Subgroup.mem_bot]
  have hc1 : (c : K) = 1 := by
    have h := congrArg (fun x : Kˣ => (x : K)) hc
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at h
    have hf := (frobenius_inj K 3)
    apply hf
    simp [frobenius_def, h]
  apply Subtype.ext
  rw [hA, hc1]
  simp


theorem exists_projectiveSL_three_to_adjointG2 {K : Type} [Field K] [Finite K] [CharP K 3] :
    ∃ ι : LinearFlag.projectiveSL (2 + 1) K →* CFSG.Blueprint.AdjointQuotient .G2 K,
      Function.Injective ι := by
  obtain ⟨φ, hφ, -⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm1.exists_a2Hom_injective (K := K)
  let f : Matrix.SpecialLinearGroup (Fin (2 + 1)) K →* CFSG.Blueprint.AdjointQuotient .G2 K :=
    (QuotientGroup.mk' (Subgroup.center ↥(adjointGroup .G2 K))).comp φ
  have hsc : LinearFlag.scalars (2 + 1) K = ⊥ := scalars_eq_bot_of_charP_three
  refine ⟨QuotientGroup.lift (LinearFlag.scalars (2 + 1) K) f (by rw [hsc]; exact bot_le), ?_⟩
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rw [MonoidHom.mem_ker, QuotientGroup.lift_mk] at hx
  have h1 : φ g ∈ Subgroup.center ↥(adjointGroup .G2 K) := (QuotientGroup.eq_one_iff _).1 hx
  rw [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot, Subgroup.mem_bot] at h1
  have h2 : g = 1 := hφ (by rw [h1, map_one])
  rw [h2, QuotientGroup.mk_one]
  exact Subgroup.one_mem _

theorem two_pow_le_card_of_adjointG2_three {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {K : Type} [Field K] [Finite K] [CharP K 3]
    {L : Subgroup (MulAut W)} (π : ↥L →* CFSG.Blueprint.AdjointQuotient .G2 K)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center ↥L)
    (hZ : ¬ 3 ∣ Nat.card π.ker) :
    2 ^ (((Nat.card K ^ 2 - 1) / (3 - 1)) * orderOf (2 : ZMod 3)) ≤ Nat.card W := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ι, hι⟩ := exists_projectiveSL_three_to_adjointG2 (K := K)
  let _ : Algebra (ZMod 3) K := ZMod.algebra K 3
  have hτ : (Algebra.trace (ZMod 3) K) ≠ 0 := by
    intro h
    obtain ⟨a, ha⟩ := Algebra.trace_surjective (ZMod 3) K 1
    rw [h] at ha
    exact zero_ne_one ha
  exact FFToolkit.two_pow_le_card_of_lift_orbit_map hW (p := 3) (by norm_num) π hπ hker hZ ι hι
    (U₀ := (uHom (K := K) (m := 2)).range) (T₀ := (tHom (K := K) (m := 2)).range)
    uHom_range_comm uHom_range_pow (uHom_range_ne_bot (by norm_num)) tHom_range_le_normalizer
    (fun D₀ hD hrel => orbit_bound (le_refl 2) hτ hD hrel)

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

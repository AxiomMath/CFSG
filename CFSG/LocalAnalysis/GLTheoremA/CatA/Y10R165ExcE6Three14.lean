module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Three11
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Three13

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.SeitzGeneration CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Steinberg.Isogeny
open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus adjEmb adjEmb_injective
  adjEmb_mem adjEmb_frobenius sigma_embedding_data subtorusImage mem_subtorusImage_iff
  twistedTorusOf mem_twistedTorusOf twistedFixedPoints mem_twistedFixedPoints subtorusSigma)
open CFSG.RankThree.PartOne.KE6
open CFSG.RankThree.Classical2 (torusRootKernel torusRootKernel_rootDiagUnit
  rootSpan_torusRootKernel_le_centralizer rootChar_neg')
open CFSG.HardMathSupport.Lang.TwE6Step3
open CFSG.RankThree.Lattice (e6T3W IsSeparated commute_of_isSeparated)
open scoped Matrix MatrixGroups Pointwise



theorem e6Three_dvd_concl (F : Type) [Field F] [Finite F] [CharP F 2]
    [Finite ↥(e6Data_valid.minGroup F)]
    (n p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (Ã : Subgroup ↥(e6Data_valid.minGroup F)) (hAe : IsElemAbelian p Ã)
    (D₁ : E6ThreeFrameData F n p q Ã)
    (D₂ : E6ThreeLayerData F n p q Ã D₁)
    (D₃ : E6ThreeCentreData F n p q Ã D₁ D₂) :
    Concl165Avoid ↥(e6Data_valid.minGroup F) p q Ã
      (Subgroup.center ↥(e6Data_valid.minGroup F)) := by
  have hxQmap : D₁.x ∈ Ã.map (e6Isogeny F) := by
    rw [← D₁.hQdef]; exact D₁.hxQ
  have hzQmap : D₁.z ∈ Ã.map (e6Isogeny F) := by
    rw [← D₁.hQdef]; exact D₁.hzQ
  obtain ⟨xt, hxtÃ, hxtπ⟩ := Subgroup.mem_map.mp hxQmap
  obtain ⟨zt, hztÃ, hztπ⟩ := Subgroup.mem_map.mp hzQmap
  obtain ⟨hxt1, hztxt, hJx, hJn', Ql, hQlJ, hQlz', hQln', hQlq, hpQl,
    hJ₁x, hJ₁perf, s₀, hs₀J₁, hsq₀, hsZ, h2ker⟩ :=
    Classical.choice (e6Three_concl_data F n p q Ã D₁ D₂ D₃ hxtÃ hztÃ hxtπ hztπ)
  have hconcl : Concl165Avoid ↥(e6Data_valid.minGroup F) p q Ã (e6Isogeny F).ker :=
    concl165Avoid_of_lifted_layers (e6Isogeny_surjective F) (le_of_eq D₁.hker) h2ker
      hp hq D₃.hqdiv' hAe hxtÃ hztÃ hxt1 hztxt hJx hJn' D₂.hJq D₂.hpJ hQlJ hQlz' hQln'
      hQlq hpQl D₂.eJ D₂.eJ₁ hJ₁x hJ₁perf hs₀J₁ hsq₀ hsZ D₂.hcommJ
  rw [D₁.hker] at hconcl
  exact hconcl

section Model

theorem e6Model165At_three_of_dvd (F : Type) [Field F] [Finite F] [CharP F 2]
    (n p q : ℕ) (hcard : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hrk : rk2Ord p n = 3)
    (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (hqdiv : q ∣ 2 ^ n - 1 ∨ n = 1 ∧ q = 3)
    (hqZ : q ∣ Nat.card (e6Isogeny F).ker) :
    letI : Finite ↥(e6Data_valid.minGroup F) :=
      CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup e6Data_valid F
    ∀ Ã : Subgroup ↥(e6Data_valid.minGroup F), IsElemAbelian p Ã →
      (∀ g ∈ Subgroup.centralizer (Ã : Set ↥(e6Data_valid.minGroup F)),
        orderOf g = p → g ∈ Ã) →
      CFSG.Open.pRank p (⊤ : Subgroup ↥(e6Data_valid.minGroup F)) ≤ CFSG.Open.pRank p Ã →
      3 ≤ CFSG.Open.pRank p Ã →
      Concl165Avoid ↥(e6Data_valid.minGroup F) p q Ã
        (Subgroup.center ↥(e6Data_valid.minGroup F)) := by
  letI : Finite ↥(e6Data_valid.minGroup F) :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup e6Data_valid F
  intro Ã hAe _hASC hmax hA3
  classical
  let D₁ := e6Three_frame_data F n p q hcard hn hp hp2 hrk hq Ã hAe hmax hA3
  let D₂ := e6Three_layer_data F n p q hcard hp hp2 hrk Ã D₁
  let D₃ := e6Three_centre_data F n p q hcard hn hq hqdiv Ã D₁ D₂
  exact e6Three_dvd_concl F n p q hp hq Ã hAe D₁ D₂ D₃

end Model

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Three

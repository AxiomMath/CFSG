module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6Six18
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6Six19
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6Model
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcDefs

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.TwistedE6
  CFSG.RankThree.E6 CFSG.RankThree.Lattice CFSG.HardMathSupport.Lang.TwE6Step3
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalGroups.UnitaryFlag
open scoped Matrix MatrixGroups Pointwise

theorem twE6Model165At_six : TwE6Model165At 6 := by
  intro k hField hFinite hChar n p q θ hk hθ hn hp hp2 hrk hq hq2 _hqp hqd
  letI : Field k := hField
  letI : Finite k := hFinite
  letI : CharP k 2 := hChar
  letI : Finite ↥(e6Data_valid.minGroup k) :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup e6Data_valid k
  intro Ã hÃ _hΩ _hmax h3
  classical
  obtain ⟨σ, hσθ, π, hπ, hπker⟩ :=
    exists_surjective_fixedGroup_twistedE6RootGroup (by omega) θ hk hθ
  have hσ : ∀ c, σ c = c ^ (2 ^ n) := fun c => by
    rw [show σ c = σ.toRingHom c from rfl, hσθ]
    exact hθ c
  haveI : Finite (ModGL TwistTag.E6.tag k) := finite_modGL
  haveI : Finite ↥(twistedE6RootGroup k σ) := Subtype.finite
  have hpker : ¬ p ∣ Nat.card π.ker := by
    rw [hπker]
    exact not_dvd_card_center_fixedGroup_of_rk2Ord_six θ hk hθ hp hrk
  obtain ⟨-, hAcard⟩ :=
    card_eq_pow_three_of_rk2Ord_six hk (by omega) hσ hp hp2 hrk hpker hÃ h3
  obtain ⟨x, hxA, y, hyA, hx1, hyx, J, J₁, hJx, hJn, hJq, hpJ, hJy, hJ₁x, hJ₁q, hcomm, ⟨eJ⟩,
      ⟨eJ₁⟩, ⟨F₀, hF₀le, hF₀el, hF₀card⟩, s₀, hs₀J₁, hs₀q, hs₀Z⟩ :=
    exists_twE6Six_layers hk hn hσ hp hp2 hrk hq hq2 hqd
      (CFSG.SectionRank.isElemAbelian_map hÃ π) hAcard
  obtain ⟨xt, hxt, rfl⟩ := Subgroup.mem_map.1 hxA
  obtain ⟨zt, hzt, rfl⟩ := Subgroup.mem_map.1 hyA
  rw [← hπker]
  exact concl165Avoid_of_unitary_layers hk hn hπ hπker.le hp hq hÃ hxt hzt
    (fun h => hx1 (by rw [h, map_one]))
    (fun h => hyx (by rw [← MonoidHom.map_zpowers]; exact Subgroup.mem_map_of_mem π h))
    hJx hJn hJq hpJ hJy hJ₁x hJ₁q hcomm eJ eJ₁ hF₀le hF₀el hF₀card hs₀J₁ hs₀q hs₀Z

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6

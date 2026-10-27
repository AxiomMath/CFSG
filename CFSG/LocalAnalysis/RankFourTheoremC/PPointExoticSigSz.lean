module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticDefs
public import Certificates.Certificate113
public import Certificates.Certificate43
public import Certificates.Certificate9530
import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticSigSzCore
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSz32Local
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

open CFSG.Open Subgroup

theorem signalizerAutAt_suzuki
    {p : ℕ} {d : TauCeti.ValidLieTypeIndex} (hp : p = 5) (hd : d.1 = .suzuki 2) :
    SignalizerAutAt p (.lie d) := by
  subst hp
  obtain ⟨x, hv⟩ := d
  simp only at hd
  subst hd
  intro K _ _ he B Y hB hBc hY hBY _
  have hiso : CFSG.RankThree.PartOne.Census3.IsoLie K (.suzuki 2) := ⟨hv, he⟩
  have hSz := CFSG.RankThree.PartOne.K159.SzAbs.szSylow_of_isoLie hiso
  have hmodel := CFSG.RankThree.PartOne.CTP.suzukiModel_of_isoLie 2 hiso
  have hOut : (Inn K).index ∣ 5 :=
    CFSG.RankThree.PartOne.K159F.card_outer_dvd_five hiso
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨eF⟩⟩ := hmodel
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hF
  have hsimple : IsSimpleGroup K := by
    have := (CFSG.LieType.Ree.suzuki_simple ha hF').2.2
    exact eF.isSimpleGroup
  obtain rfl : a = 2 := by omega
  let σ : F ≃+* CFSG.AGLEmbedding.KFactProofs.Sz32.F32 :=
    CFSG.AGLEmbedding.KFactProofs.Sz32.F32.ringEquiv F hF'
  let ε : K ≃* CFSG.Blueprint.suzukiGroup 2 CFSG.AGLEmbedding.KFactProofs.Sz32.F32 :=
    eF.trans (CFSG.AGLEmbedding.KFactProofs.Sz32Local.modelEquiv σ)
  have hC : ∀ T : Sylow 5 K, ∀ t ∈ (T : Subgroup K), t ≠ 1 → ∀ g : K, g * t = t * g →
      g ∈ (T : Subgroup K) := fun T =>
    CFSG.AGLEmbedding.KFactProofs.Sz32Local.centralizer_le_of_equiv ε T
  haveI : Finite (MulAut K) :=
    Finite.of_injective (fun f : MulAut K => (f : K → K)) DFunLike.coe_injective
  have hcinj : Function.Injective (MulAut.conj : K →* MulAut K) :=
    SzSignalizer.conj_injective hSz hsimple
  have hmemInner : ∀ w : MulAut K, w ∈ Inn K ↔ ∃ g : K, MulAut.conj g = w := fun w =>
    MonoidHom.mem_range
  have hYK : Y ≤ Inn K := by
    intro y hy
    have h1 : orderOf (QuotientGroup.mk' (Inn K) y) ∣ Nat.card Y :=
      (orderOf_map_dvd _ y).trans (Subgroup.orderOf_dvd_natCard Y hy)
    have h2 : orderOf (QuotientGroup.mk' (Inn K) y) ∣ 5 :=
      (_root_.orderOf_dvd_natCard _).trans hOut
    have h3 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hY.symm) h2
    exact (QuotientGroup.eq_one_iff y).1 (orderOf_eq_one_iff.1 h3)
  let φ : B →* MulAut K ⧸ Inn K := (QuotientGroup.mk' (Inn K)).comp B.subtype
  have hker : φ.ker ≠ ⊥ := by
    intro h
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 h
    have h1 := Nat.card_le_card_of_injective φ hinj
    rw [hBc] at h1
    have h5 : Nat.card (MulAut K ⧸ Inn K) ≤ 5 := Nat.le_of_dvd (by norm_num) hOut
    omega
  obtain ⟨b, hb⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hker
  have hb1 : ((b : B) : MulAut K) ≠ 1 := fun h => hb (Subtype.ext (Subtype.ext h))
  have hbK : ((b : B) : MulAut K) ∈ Inn K := (QuotientGroup.eq_one_iff _).1 b.2
  obtain ⟨z, hz⟩ := (hmemInner _).1 hbK
  have hz5 : z ^ 5 = 1 := by
    apply hcinj
    rw [map_pow, hz, map_one]
    exact hB.2 _ (b : B).2
  have hz1 : z ≠ 1 := by
    rintro rfl
    exact hb1 (by rw [← hz, map_one])
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hzord : orderOf z = 5 := orderOf_eq_prime hz5 hz1
  set Y' : Subgroup K := Y.comap (MulAut.conj : K →* MulAut K) with hY'
  have hmapY : Y'.map (MulAut.conj : K →* MulAut K) = Y := Subgroup.map_comap_eq_self hYK
  have hY'card : Nat.card Y' = Nat.card Y := by
    have := Subgroup.card_map_of_injective (f := (MulAut.conj : K →* MulAut K)) (K := Y') hcinj
    rw [hmapY] at this
    exact this.symm
  have hzY' : z ∈ normalizer (Y' : Set K) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have hbN := Subgroup.mem_normalizer_iff.1 (hBY (b : B).2) (MulAut.conj w)
    have hconj : MulAut.conj (z * w * z⁻¹) =
        ((b : B) : MulAut K) * MulAut.conj w * ((b : B) : MulAut K)⁻¹ := by
      rw [← hz, map_mul, map_mul, map_inv]
    show MulAut.conj w ∈ Y ↔ MulAut.conj (z * w * z⁻¹) ∈ Y
    rw [hconj]
    exact hbN
  have hY'bot : Y' = ⊥ :=
    SzSignalizer.eq_bot_of_normalizes hSz hsimple hC hzord
      (by rw [hY'card]; exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).1 hY) hzY'
  have hYbot : Y = ⊥ := by
    rw [← hmapY, hY'bot, Subgroup.map_bot]
  intro w _
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [hYbot] at hh
  have : h = 1 := Subgroup.mem_bot.1 hh
  rw [this]
  simp

end CFSG.LocalAnalysis.RankFourTheoremC

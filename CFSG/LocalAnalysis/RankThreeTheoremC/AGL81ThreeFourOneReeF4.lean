module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourOneDefs
import CFSG.HardMathSupport.Malle.LocalAction.ReeF4ElementCentralizer
import CFSG.HardMathSupport.Malle.LocalAction.ReeF4SocleFacts
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimGeneric
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoCriteria
import CFSG.RankThree.PartOne.K133.KillBasic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

open CFSG.LieType.Ree (ReeTag)

open CFSG.HardMathSupport.Malle.LocalAction
  (card_sup_of_commute_of_inf_eq_bot exists_centralizer_decomp exists_plane_of_sylow)

private theorem eq_bot_of_isPGroup_three_reeGamma {F : Type}
    [Field F] [Finite F] [CharP F ReeTag.F4.prime] (hF : Nat.card F = 2 ^ (2 * 2 + 1))
    [Finite (ReeTag.F4.reeGamma F 2)] (P : Sylow 5 (ReeTag.F4.reeGamma F 2))
    {V : Subgroup (ReeTag.F4.reeGamma F 2)} (hV : IsPGroup 3 V)
    (hPV : (P : Subgroup (ReeTag.F4.reeGamma F 2)) ≤
      Subgroup.normalizer (V : Set (ReeTag.F4.reeGamma F 2))) : V = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEP, hE, hEcard⟩ := exists_plane_of_sylow hF P
  refine Hyp111.eq_bot_of_plane Nat.prime_five (fun b hb => hE.2 b hb) hEcard
    (Hyp111.coprime_card_of_isPGroup Nat.prime_five Nat.prime_three (by norm_num) hV)
    (hEP.trans hPV) fun b hb hb1 => ?_
  obtain ⟨A, S, -, hA, -, hcomm, hinf, hsup, hS, -⟩ :=
    exists_centralizer_decomp hF P E hEP hE b hb hb1
  have hC : Nat.card (Subgroup.centralizer ({b} : Set (ReeTag.F4.reeGamma F 2))) =
      25 * 32537600 := by
    rw [← hsup, card_sup_of_commute_of_inf_eq_bot hcomm hinf, hA, hS]
  rcases (hV.to_le (inf_le_left (b := Subgroup.centralizer ({b} : Set _)))).card_eq_or_dvd
    with h1 | h3
  · exact Subgroup.card_eq_one.mp h1
  · have h := h3.trans ((Subgroup.card_dvd_of_le inf_le_right).trans (dvd_of_eq hC))
    omega


theorem signalizerThreeOn_reeF4 {d : TauCeti.ValidLieTypeIndex} (hd : d.1 = .reeF4 2)
    {K : Type} [Group K] [Finite K] (hK : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    SignalizerThreeOn 5 K := by
  intro T W hW hnorm
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨F, _, _, _, hF, ⟨eΓ⟩⟩ :=
    CFSG.HardMathSupport.Malle.LocalAction.exists_reeGamma_model hd hK
  obtain ⟨e⟩ := hK
  haveI : IsSimpleGroup (CFSG.AGLEmbedding.CatGroup d) :=
    CFSG.AGLEmbedding.isSimpleGroup_of_catGroup_reeF4 hd
  haveI : IsSimpleGroup K := e.isSimpleGroup
  have h25 : 5 ^ 2 ∣ Nat.card K := by
    rw [Nat.card_congr e.toEquiv, CFSG.AGLEmbedding.card_catGroup_reeF4 hd]
    norm_num [CFSG.Open.ordTwistedF4]
  have hZ : Subgroup.center K = ⊥ := CFSG.AGLEmbedding.center_bot_of_simple_nonab
    (CFSG.AGLEmbedding.nonabelian_of_simple_of_sq_dvd Nat.prime_five h25)
  have hOut : ¬ 3 ∣ Nat.card (Outer K) := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence eΓ).toEquiv]
    intro h3
    have := h3.trans (CFSG.AGLEmbedding.outer_reeGamma (a := 2) (K := F) (by norm_num) hF).2
    omega
  have hWI : W ≤ (MulAut.conj : K →* MulAut K).range :=
    CFSG.RankThree.PartOne.K133.le_inner_of_isPGroup_of_not_dvd_outer Nat.prime_three hOut hW
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
    intro g hg
    refine Subgroup.mem_center_iff.mpr fun x => ?_
    have h := congrArg (fun α : MulAut K => α x) (MonoidHom.mem_ker.mp hg)
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc x * g = g * x * g⁻¹ * g := by rw [h]
      _ = g * x := by group
  set W₀ : Subgroup K := W.comap (MulAut.conj : K →* MulAut K) with hW₀
  have hTV : ∀ t ∈ (T : Subgroup K),
      MulAut.conj t ∈ Subgroup.normalizer (W : Set (MulAut K)) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨fun hw => hnorm t ht w hw, fun hw => ?_⟩
    have := hnorm t⁻¹ (inv_mem ht) _ hw
    simpa [map_inv, mul_assoc] using this
  have hTW₀ : (T : Subgroup K) ≤ Subgroup.normalizer (W₀ : Set K) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro g
    simpa [hW₀] using Subgroup.mem_normalizer_iff.mp (hTV t ht) (MulAut.conj g)
  haveI : Finite (ReeTag.F4.reeGamma F 2) := Finite.of_equiv K eΓ.toEquiv
  have hsurj : Function.Surjective eΓ.toMonoidHom := eΓ.surjective
  have hV : W₀.map eΓ.toMonoidHom = ⊥ := by
    refine eq_bot_of_isPGroup_three_reeGamma hF (T.mapSurjective hsurj)
      ((hW.comap_of_injective _ hinj).map _) ?_
    rw [Sylow.coe_mapSurjective, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hTW₀
  have hW₀bot : W₀ = ⊥ := (Subgroup.map_eq_bot_iff_of_injective W₀ eΓ.injective).1 hV
  calc W = W₀.map (MulAut.conj : K →* MulAut K) := (Subgroup.map_comap_eq_self hWI).symm
    _ = ⊥ := by rw [hW₀bot, Subgroup.map_bot]

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

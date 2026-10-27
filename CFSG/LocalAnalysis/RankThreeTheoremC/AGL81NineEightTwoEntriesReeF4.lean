module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoEntries
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcAbs
import CFSG.HardMathSupport.Malle.LocalAction.ReeF4SocleFacts
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimGeneric
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcRee
import CFSG.RankThree.PartOne.K133.KillBasic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.AGLEmbedding CFSG.HardMathSupport.Malle.LocalAction
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)


theorem noSylowNormalizesTwo_of_mulEquiv {G H : Type*} [Group G] [Group H] {p : ℕ}
    (e : G ≃* H) (h : NoSylowNormalizesTwo p H) : NoSylowNormalizesTwo p G := by
  intro R E hR hR2 hE hdvd
  refine h (R.map e.toMonoidHom) (E.map e.toMonoidHom)
    (fun h0 => hR ((Subgroup.map_eq_bot_iff_of_injective R e.injective).1 h0)) (hR2.map _) ?_ ?_
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hE
  · rwa [Subgroup.card_map_of_injective e.injective, ← Nat.card_congr e.toEquiv]

theorem eq_bot_of_noSylowNormalizesTwo {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hZ : Subgroup.center G = ⊥) (hOut : ¬ 2 ∣ Nat.card (Outer G))
    (hN : NoSylowNormalizesTwo p G) (T : Sylow p G) {V : Subgroup (MulAut G)}
    (hV : IsPGroup 2 V)
    (hTV : ∀ t ∈ (T : Subgroup G), MulAut.conj t ∈ Subgroup.normalizer (V : Set (MulAut G))) :
    V = ⊥ := by
  have hVI : V ≤ (MulAut.conj : G →* MulAut G).range :=
    CFSG.RankThree.PartOne.K133.le_inner_of_isPGroup_of_not_dvd_outer Nat.prime_two hOut hV
  have hinj : Function.Injective (MulAut.conj : G →* MulAut G) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
    intro g hg
    refine Subgroup.mem_center_iff.mpr fun x => ?_
    have h := congrArg (fun α : MulAut G => α x) (MonoidHom.mem_ker.mp hg)
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc x * g = g * x * g⁻¹ * g := by rw [h]
      _ = g * x := by group
  set V₀ : Subgroup G := V.comap (MulAut.conj : G →* MulAut G) with hV₀
  have hTV₀ : (T : Subgroup G) ≤ Subgroup.normalizer (V₀ : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro g
    simpa [hV₀] using Subgroup.mem_normalizer_iff.mp (hTV t ht) (MulAut.conj g)
  have hV₀bot : V₀ = ⊥ := by
    by_contra hne
    exact hN V₀ T hne (hV.comap_of_injective _ hinj) hTV₀
      (dvd_of_eq (Sylow.card_eq_multiplicity T).symm)
  calc V = V₀.map (MulAut.conj : G →* MulAut G) := (Subgroup.map_comap_eq_self hVI).symm
    _ = ⊥ := by rw [hV₀bot, Subgroup.map_bot]

section ReeF4


theorem eq_bot_of_normalizes_reeF4 {d : TauCeti.ValidLieTypeIndex} (hd : d.1 = .reeF4 2)
    {K : Type} [Group K] [Finite K] (hK : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (T : Sylow 5 K) {V : Subgroup (MulAut K)} (hV : IsPGroup 2 V)
    (hTV : ∀ t ∈ (T : Subgroup K), MulAut.conj t ∈ Subgroup.normalizer (V : Set (MulAut K))) :
    V = ⊥ := by
  have he : orderOf (((2 ^ (2 * 2 + 1) : ℕ)) : ZMod 5) = 4 :=
    (orderOf_eq_iff (by norm_num)).2 ⟨by decide, by decide⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨F, _, _, _, hF, ⟨eΓ⟩⟩ := exists_reeGamma_model hd hK
  obtain ⟨e⟩ := hK
  haveI : IsSimpleGroup (CatGroup d) := isSimpleGroup_of_catGroup_reeF4 hd
  haveI : IsSimpleGroup K := e.isSimpleGroup
  have h25 : 5 ^ 2 ∣ Nat.card K := by
    rw [Nat.card_congr e.toEquiv, card_catGroup_reeF4 hd]
    norm_num [CFSG.Open.ordTwistedF4]
  have hOut : ¬ 2 ∣ Nat.card (Outer K) := by
    rw [Nat.card_congr (equivalence eΓ).toEquiv]
    intro h2
    have := h2.trans (outer_reeGamma (a := 2) (K := F) (by norm_num) hF).2
    omega
  exact eq_bot_of_noSylowNormalizesTwo
    (center_bot_of_simple_nonab (nonabelian_of_simple_of_sq_dvd Nat.prime_five h25)) hOut
    (noSylowNormalizesTwo_of_mulEquiv eΓ
      (noSylowNormalizesTwo_ree hF Nat.prime_five le_rfl (by norm_num) he (Or.inr rfl)))
    T hV hTV

theorem kFactNineThreeNoTwoAt_reeF4 {d : TauCeti.ValidLieTypeIndex} (hd : d.1 = .reeF4 2) :
    KFactNineThreeNoTwoAt 5 (.lie d) := by
  intro X _ _ K hK hiso _ T S hS hTS
  haveI := hK
  exact le_centralizer_of_aut (T := (T : Subgroup K).map K.subtype) (Subgroup.map_subtype_le _)
    (fun V hV hN => eq_bot_of_normalizes_reeF4 hd hiso T hV fun t ht => hN t ⟨t, ht, rfl⟩) hS
    hTS

end ReeF4

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

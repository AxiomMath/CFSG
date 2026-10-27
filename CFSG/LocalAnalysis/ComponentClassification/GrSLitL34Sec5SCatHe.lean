module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SRank
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23HeModelC
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedHe
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixCore
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsPFBase
public import CFSG.LinearAlgebra.LinearGroups.LinearTwoOddFourGroups
public import CFSG.LocalAnalysis.ComponentClassification.Foote47P3Gen
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitE8Generation
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGWBridge
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnitaryFix
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.Sporadic.HeldB.AllFixed
public import CFSG.Walter.J1

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.GSThmB.CF23L34

theorem two_le_pRank_center_of_component
    {L : Subgroup ↥(centralizerIn heP (heGenPerm 0))} (hL : IsComponent L) :
    2 ≤ pRank 2 ↥(center ↥L) := by
  have hJ := component_eq_hjJ hL
  have hzJ : hjZP ∈ hjJ := ⟨_, rfl⟩
  have htJ : heGenPerm 0 ∈ hjJ := ⟨_, hjLam_z₂⟩
  have hmem : ∀ {g : Equiv.Perm (Fin 8330)} (hg : g ∈ hjJ), (⟨g, hjJ_le hg⟩ :
      ↥(centralizerIn heP (heGenPerm 0))) ∈ L := fun hg => by
    rw [hJ, mem_subgroupOf]
    exact hg
  have hcenter : ∀ {g : Equiv.Perm (Fin 8330)} (hg : g ∈ hjJ),
      (∀ x : ↥L, (((x : ↥(centralizerIn heP (heGenPerm 0))) : Equiv.Perm (Fin 8330))) * g =
        g * ((x : ↥(centralizerIn heP (heGenPerm 0))) : Equiv.Perm (Fin 8330))) →
      (⟨⟨g, hjJ_le hg⟩, hmem hg⟩ : ↥L) ∈ center ↥L := fun hg hc => by
    rw [mem_center_iff]
    intro x
    exact Subtype.ext (Subtype.ext (hc x))
  have hLJ : ∀ y : ↥(centralizerIn heP (heGenPerm 0)), y ∈ L →
      (y : Equiv.Perm (Fin 8330)) ∈ hjJ := fun y hy => by
    rw [hJ, mem_subgroupOf] at hy
    exact hy
  have hxJ : ∀ x : ↥L, ((x : ↥(centralizerIn heP (heGenPerm 0))) : Equiv.Perm (Fin 8330)) ∈ hjJ :=
    fun x => hLJ x.1 x.2
  have hz := hcenter hzJ fun x => comm_hjZP (hxJ x)
  have ht := hcenter htJ fun x =>
    mem_centralizer_singleton_iff.mp (x : ↥(centralizerIn heP (heGenPerm 0))).2.2
  have hval : ∀ {g h : Equiv.Perm (Fin 8330)} (hg : g ∈ hjJ) (hh : h ∈ hjJ),
      ((⟨⟨g, hjJ_le hg⟩, hmem hg⟩ : ↥L) = ⟨⟨h, hjJ_le hh⟩, hmem hh⟩) ↔ g = h := fun _ _ =>
    ⟨fun e => congrArg (fun y : ↥L => ((y : ↥(centralizerIn heP (heGenPerm 0))) :
      Equiv.Perm (Fin 8330))) e, fun e => by subst e; rfl⟩
  have ht1 : heGenPerm 0 * heGenPerm 0 = 1 := by rw [← sq]; exact heGen0_sq
  refine HeEnd.two_le_pRank_of_pair hz ht ?_ ?_ ?_ ?_ ?_ ?_
  · exact Subtype.ext (Subtype.ext hjZP_mul_self)
  · exact Subtype.ext (Subtype.ext ht1)
  · intro h1
    exact hjZP_ne_one (congrArg (fun y : ↥L => ((y : ↥(centralizerIn heP (heGenPerm 0))) :
      Equiv.Perm (Fin 8330))) h1)
  · intro h1
    exact heA0_ne_one (congrArg (fun y : ↥L => ((y : ↥(centralizerIn heP (heGenPerm 0))) :
      Equiv.Perm (Fin 8330))) h1)
  · exact fun h1 => hjZP_ne_t ((hval hzJ htJ).mp h1)
  · exact Subtype.ext (Subtype.ext hjZP_comm_t)

theorem two_le_pRank_of_he
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (e : S ≃* NativeSporadic.He)
    {σ : MulAut S} {P : Subgroup S} (h : CatLeaf.ProperFixedComponent σ P)
    (htype : IsL34Type (P ⧸ Open.fusionZStar P)) : 2 ≤ pRank 2 ↥(Open.fusionZStar ↥P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ1 := h.ne_one
  obtain ⟨hσ, hPF, hP, -⟩ := h
  let θ : S ≃* heP := e.trans heEquivP
  have hσ2' : σ * σ = 1 := MulEquiv.ext fun t => hσ t
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hσ2') hσ1
  have hβ : orderOf (MulAut.congr θ σ) = 2 := by rw [orderOf_congr, hσ2]
  have hd : 20160 ∣ Nat.card (fixedSubgroup σ) :=
    (L34PF.dvd_card_of_isL34Type htype).trans (Subgroup.card_dvd_of_le hPF)
  suffices key : ∀ φ : fixedSubgroup σ ≃* centralizerIn heP (heGenPerm 0),
      2 ≤ pRank 2 ↥(Open.fusionZStar ↥P) by
    by_cases hinn : MulAut.congr θ σ ∈ (MulAut.conj : heP →* MulAut heP).range
    · obtain ⟨t, ht⟩ := hinn
      have ht2 : orderOf t = 2 := by
        rw [← orderOf_injective _ (conj_injective_of_center heP_center_eq_bot) t, ht, hβ]
      let f : fixedSubgroup σ ≃* centralizerIn heP (t : Equiv.Perm (Fin 8330)) :=
        ((fixedSubgroupCongr θ σ).trans
          (MulEquiv.subgroupCongr (by rw [← ht, fixedSubgroup_conj]))).trans
          (heCentralizerEquiv t)
      rcases involution_conj_cases t.2 (by rw [Subgroup.orderOf_coe]; exact ht2) with
        ⟨c, hc, hct⟩ | ⟨c, hc, hct⟩
      · exact key (f.trans ((MulEquiv.subgroupCongr (by rw [← hct]; rfl)).trans
          (infCentralizerConjEquiv hc (heGenPerm 0))))
      · exfalso
        let f' : fixedSubgroup σ ≃* centralizerIn heP heT1P :=
          f.trans ((MulEquiv.subgroupCongr (by rw [← hct]; rfl)).trans
            (infCentralizerConjEquiv hc heT1P))
        rw [Nat.card_congr f'.toEquiv, card_heP_cent1] at hd
        exact absurd hd (by decide)
    · exfalso
      obtain ⟨x, hx, hxP, hx2⟩ := exists_heConjR_eq ctbh_full_automorphism_permutation_model.1
        (MulAut.congr θ σ) hβ hinn
      obtain ⟨g, hg, hxg⟩ := exists_conj_heAutU x.2 hxP hx2
      let f' : fixedSubgroup σ ≃*
          (heP ⊓ Subgroup.centralizer {heAutU} : Subgroup (Equiv.Perm (Fin 8330))) :=
        ((fixedSubgroupCongr θ σ).trans (MulEquiv.subgroupCongr (by rw [hx]))).trans
          (fixedSubgroupEquivOfConj x hg heAutU hxg)
      rw [Nat.card_congr f'.toEquiv, card_heP_centralizer_heAutU] at hd
      exact absurd hd (by decide)
  intro φ
  set L := P.subgroupOf (fixedSubgroup σ) with hLdef
  have hL' : IsPComponent 2 (L.map φ.toMonoidHom) :=
    LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 φ hP
  have hO : pPrimeCore 2 ↥(centralizerIn heP (heGenPerm 0)) = ⊥ := by
    rw [HeldFix.pPrimeCore_two_eq_oddCore]
    exact heInner0_oddCore card_heP_cent0
  have hr : 2 ≤ pRank 2 ↥(Open.fusionZStar ↥(L.map φ.toMonoidHom)) := by
    rw [HeldFix.fusionZStar_eq_center_of_isPComponent hO hL']
    exact two_le_pRank_center_of_component (HeldFix.isComponent_of_isPComponent hO hL')
  let ε : ↥P ≃* ↥(L.map φ.toMonoidHom) :=
    (subgroupOfEquivOfLe hPF).symm.trans (L.equivMapOfInjective φ.toMonoidHom φ.injective)
  have hker : ¬ 2 ∣ Nat.card ε.toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr ε.injective, Subgroup.card_bot]
    norm_num
  obtain ⟨eO⟩ := GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective ε.toMonoidHom
    ε.surjective hker
  rw [pRank_fusionZStar_congr eO]
  exact hr

end CFSG.ComponentClassification.GrSLit.L34Sec5S

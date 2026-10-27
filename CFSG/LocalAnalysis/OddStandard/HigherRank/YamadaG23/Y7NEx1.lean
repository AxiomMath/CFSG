module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Ext26
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G]

private lemma pCoreOf_top_eq_pCore {G : Type*} [Group G] :
    pCoreOf 2 (⊤ : Subgroup G) = CFSG.pCore 2 G := by
  have hfun : Subgroup.topEquiv.toMonoidHom = (⊤ : Subgroup G).subtype := by
    ext x
    rfl
  unfold pCoreOf
  rw [← hfun]
  exact CFSG.pCore_map_iso 2 Subgroup.topEquiv

private lemma isMulCommutative_of_isE {F : Subgroup G} (hF : IsE 3 ↥F) :
    IsMulCommutative (F : Subgroup G) := by
  refine IsMulCommutative.of_comm fun a b => ?_
  have h := (isMulCommutative_iff.mp hF.1.1)
    (Subgroup.topEquiv.symm a) (Subgroup.topEquiv.symm b)
  simpa using congrArg Subgroup.topEquiv h

private lemma isE_mulEquiv_fin {F : Subgroup G} (hF : IsE 3 ↥F) :
    Nonempty (↥F ≃* (Fin 3 → Multiplicative (ZMod 2))) := by
  obtain ⟨hFe⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (W := ↥F) (p := 2)
    (fun a b => isMulCommutative_iff_of_setLike.mp hF.1.1 a (Subgroup.mem_top a) b
      (Subgroup.mem_top b))
    (fun a => hF.1.2 a (Subgroup.mem_top a)) hF.2
  exact ⟨hFe.trans (MulEquiv.funMultiplicative (Fin 3) (ZMod 2))⟩

theorem y7n_pcore_eq {N F : Subgroup G} (hFN : F ≤ N) (hF : IsE 3 ↥F)
    (hq : SecProp N F (fun Y _ _ _ => Nonempty (Y ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)))) :
    pCoreOf 2 (⊤ : Subgroup ↥N) = F.subgroupOf N := by
  obtain ⟨hn, ⟨e⟩⟩ := hq
  haveI := hn
  rw [pCoreOf_top_eq_pCore]
  refine le_antisymm ?_ ?_
  · intro x hx
    let π : ↥N →* (↥N ⧸ F.subgroupOf N) := QuotientGroup.mk' (F.subgroupOf N)
    haveI : (((CFSG.pCore 2 ↥N).map π).map e.toMonoidHom).Normal :=
      ((CFSG.pCore_normal (G := ↥N) (p := 2)).map π Quotient.mk''_surjective).map
        e.toMonoidHom e.surjective
    haveI : IsSimpleGroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :=
      CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (((CFSG.pCore 2 ↥N).map π).map e.toMonoidHom) with hbot | htop
    · have hbot' : (CFSG.pCore 2 ↥N).map π = ⊥ := by
        apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
        rw [hbot, Subgroup.map_bot]
      have hxmem : π x ∈ (CFSG.pCore 2 ↥N).map π := ⟨x, hx, rfl⟩
      rw [hbot'] at hxmem
      have hxker : x ∈ MonoidHom.ker π := MonoidHom.mem_ker.mpr (by simpa using hxmem)
      rwa [QuotientGroup.ker_mk'] at hxker
    · exfalso
      have hpGL : IsPGroup 2 (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) := by
        have hp' : IsPGroup 2 ((((CFSG.pCore 2 ↥N).map π).map e.toMonoidHom) :
            Subgroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) :=
          ((CFSG.pCore_isPGroup (G := ↥N) (p := 2)).map π).map e.toMonoidHom
        rw [htop] at hp'
        exact hp'.of_equiv (Subgroup.topEquiv :
          ↥(⊤ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) ≃*
            Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))
      obtain ⟨n, hncard⟩ := hpGL.exists_card_eq
      rw [CFSG.ComponentClassification.GHarris.card_GL32_gh] at hncard
      have h3dvd : (3 : ℕ) ∣ 2 ^ n := by rw [← hncard]; norm_num
      have h3 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3dvd
      norm_num at h3
  · have hp : IsPGroup 2 (F.subgroupOf N) := by
      apply IsPGroup.of_card
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFN).toEquiv, hF.2]
    rw [CFSG.pCore_eq_iSup]
    refine le_iSup_of_le (F.subgroupOf N) ?_
    refine le_iSup_of_le hn ?_
    exact le_iSup_of_le hp le_rfl

theorem y7n_isExt26_of_sub {N F : Subgroup G} (hFN : F ≤ N) (hF : IsE 3 ↥F)
    (hq : SecProp N F (fun Y _ _ _ => Nonempty (Y ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))))
    (hC : N ⊓ centralizer (F : Set G) = F) : Sec2.IsExt26 1 ↥N := by
  have h1 := y7n_pcore_eq hFN hF hq
  unfold Sec2.IsExt26
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨hFe⟩ := isE_mulEquiv_fin hF
    refine ⟨(MulEquiv.subgroupCongr h1).trans ((Subgroup.subgroupOfEquivOfLe hFN).trans ?_)⟩
    rw [pow_one]
    exact hFe
  · rw [h1]
    obtain ⟨hn, ⟨e⟩⟩ := hq
    haveI := hn
    unfold SecProp
    refine ⟨hn.subgroupOf (⊤ : Subgroup ↥N), ?_⟩
    have hsub : (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥N) ≃* ↥N).toMonoidHom =
        (⊤ : Subgroup ↥N).subtype := by
      ext x
      rfl
    have he : (((F.subgroupOf N).subgroupOf (⊤ : Subgroup ↥N)).map
        (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥N) ≃* ↥N).toMonoidHom) = F.subgroupOf N := by
      rw [hsub]
      exact Subgroup.map_comap_eq_self_of_surjective
        (f := (⊤ : Subgroup ↥N).subtype) Subgroup.topEquiv.surjective (F.subgroupOf N)
    exact ⟨(QuotientGroup.congr ((F.subgroupOf N).subgroupOf (⊤ : Subgroup ↥N))
      (F.subgroupOf N) (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥N) ≃* ↥N) he).trans e⟩
  · rw [h1]
    haveI := isMulCommutative_of_isE hF
    refine le_antisymm ?_ ?_
    · intro x hx
      have hxc : (x : G) ∈ centralizer (F : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro f hf
        have hy : (⟨f, hFN hf⟩ : ↥N) ∈ (F.subgroupOf N : Set ↥N) :=
          Subgroup.mem_subgroupOf.mpr hf
        exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hx) ⟨f, hFN hf⟩ hy)
      have hxF : (x : G) ∈ F := by
        have hmem : (x : G) ∈ N ⊓ centralizer (F : Set G) := ⟨x.2, hxc⟩
        rwa [hC] at hmem
      exact Subgroup.mem_subgroupOf.mpr hxF
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      apply Subtype.ext
      have hyF : (y : G) ∈ F := Subgroup.mem_subgroupOf.mp hy
      have hxF : (x : G) ∈ F := Subgroup.mem_subgroupOf.mp hx
      exact setLike_mul_comm hyF hxF

end CFSG.OddStandard.HigherRank.YamadaG23

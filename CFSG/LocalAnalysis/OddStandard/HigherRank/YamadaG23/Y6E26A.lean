module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Ext26
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G]

theorem y6e_isPres26_equiv {n : ℕ} {e : Bool} {P P' : Type} [Group P] [Group P']
    (φ : P ≃* P') {u v w r s : P} (h : Sec2.IsPres26 n e P u v w r s) :
    Sec2.IsPres26 n e P' (φ u) (φ v) (φ w) (φ r) (φ s) := by
  obtain ⟨hrel, hbij⟩ := h
  have hlift : FreeGroup.lift (![φ u, φ v, φ w, φ r, φ s] : Fin 5 → P') =
      φ.toMonoidHom.comp (FreeGroup.lift (![u, v, w, r, s] : Fin 5 → P)) := by
    apply FreeGroup.ext_hom
    intro i
    fin_cases i <;> simp
  have hrel' : ∀ x ∈ Sec2.rels26 n e,
      FreeGroup.lift (![φ u, φ v, φ w, φ r, φ s] : Fin 5 → P') x = 1 := by
    intro x hx
    rw [hlift, MonoidHom.comp_apply, hrel x hx, map_one]
  refine ⟨hrel', ?_⟩
  have hcomp : PresentedGroup.toGroup hrel' =
      φ.toMonoidHom.comp (PresentedGroup.toGroup hrel) := by
    apply PresentedGroup.ext
    intro i
    rw [PresentedGroup.toGroup.of, MonoidHom.comp_apply, PresentedGroup.toGroup.of]
    fin_cases i <;> rfl
  rw [hcomp]
  exact φ.bijective.comp hbij

private lemma pCoreOf_top_eq_pCore' {G : Type*} [Group G] :
    pCoreOf 2 (⊤ : Subgroup G) = CFSG.pCore 2 G := by
  have hfun : Subgroup.topEquiv.toMonoidHom = (⊤ : Subgroup G).subtype := by
    ext x
    rfl
  unfold pCoreOf
  rw [← hfun]
  exact CFSG.pCore_map_iso 2 Subgroup.topEquiv

theorem y6e_pcore_eq {N M : Subgroup G} (hMN : M ≤ N) (hM : IsPGroup 2 ↥M)
    (hq : SecProp N M (fun Y _ _ _ => Nonempty (Y ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)))) :
    pCoreOf 2 (⊤ : Subgroup ↥N) = M.subgroupOf N := by
  obtain ⟨hn, ⟨e⟩⟩ := hq
  haveI := hn
  rw [pCoreOf_top_eq_pCore']
  refine le_antisymm ?_ ?_
  · intro x hx
    let π : ↥N →* (↥N ⧸ M.subgroupOf N) := QuotientGroup.mk' (M.subgroupOf N)
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
  · have hp : IsPGroup 2 (M.subgroupOf N) := hM.of_equiv (Subgroup.subgroupOfEquivOfLe hMN).symm
    rw [CFSG.pCore_eq_iSup]
    refine le_iSup_of_le (M.subgroupOf N) ?_
    refine le_iSup_of_le hn ?_
    exact le_iSup_of_le hp le_rfl

theorem y6e_isExt26_of_sub {n : ℕ} {N M : Subgroup G} (hMN : M ≤ N) (hM : IsPGroup 2 ↥M)
    (e : ↥M ≃* (Fin 3 → Multiplicative (ZMod (2 ^ n))))
    (hq : SecProp N M (fun Y _ _ _ => Nonempty (Y ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))))
    (hC : N ⊓ centralizer (M : Set G) = M) : Sec2.IsExt26 n ↥N := by
  have h1 := y6e_pcore_eq hMN hM hq
  unfold Sec2.IsExt26
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨(MulEquiv.subgroupCongr h1).trans ((Subgroup.subgroupOfEquivOfLe hMN).trans e)⟩
  · rw [h1]
    obtain ⟨hn, ⟨e'⟩⟩ := hq
    haveI := hn
    unfold SecProp
    refine ⟨hn.subgroupOf (⊤ : Subgroup ↥N), ?_⟩
    have hsub : (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥N) ≃* ↥N).toMonoidHom =
        (⊤ : Subgroup ↥N).subtype := by
      ext x
      rfl
    have he : (((M.subgroupOf N).subgroupOf (⊤ : Subgroup ↥N)).map
        (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥N) ≃* ↥N).toMonoidHom) = M.subgroupOf N := by
      rw [hsub]
      exact Subgroup.map_comap_eq_self_of_surjective
        (f := (⊤ : Subgroup ↥N).subtype) Subgroup.topEquiv.surjective (M.subgroupOf N)
    exact ⟨(QuotientGroup.congr ((M.subgroupOf N).subgroupOf (⊤ : Subgroup ↥N))
      (M.subgroupOf N) (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥N) ≃* ↥N) he).trans e'⟩
  · rw [h1]
    have hMcomm : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a := by
      intro a ha b hb
      have h := e.injective (show e ⟨a * b, M.mul_mem ha hb⟩ = e ⟨b * a, M.mul_mem hb ha⟩ by
        rw [show (⟨a * b, M.mul_mem ha hb⟩ : ↥M) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl,
          show (⟨b * a, M.mul_mem hb ha⟩ : ↥M) = ⟨b, hb⟩ * ⟨a, ha⟩ from rfl, map_mul, map_mul,
          mul_comm])
      exact congrArg Subtype.val h
    refine le_antisymm ?_ ?_
    · intro x hx
      have hxc : (x : G) ∈ centralizer (M : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro f hf
        have hy : (⟨f, hMN hf⟩ : ↥N) ∈ (M.subgroupOf N : Set ↥N) :=
          Subgroup.mem_subgroupOf.mpr hf
        exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hx) ⟨f, hMN hf⟩ hy)
      have hxM : (x : G) ∈ M := by
        have hmem : (x : G) ∈ N ⊓ centralizer (M : Set G) := ⟨x.2, hxc⟩
        rwa [hC] at hmem
      exact Subgroup.mem_subgroupOf.mpr hxM
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      apply Subtype.ext
      have hyM : (y : G) ∈ M := Subgroup.mem_subgroupOf.mp hy
      have hxM : (x : G) ∈ M := Subgroup.mem_subgroupOf.mp hx
      exact hMcomm _ hyM _ hxM

end CFSG.OddStandard.HigherRank.YamadaG23

module

public import CFSG.LieType.Universal.Spin.Datum
public import CFSG.LieType.CurtisTits.Reduction
import CFSG.LieType.CurtisTits.Spin
import CFSG.LieType.CurtisTits.Conclusion
import CFSG.LieType.Universal.Spin.PlusCT.Weyl
import CFSG.LieType.Universal.Spin.Generation.Datum
import CFSG.LieType.Steinberg.Presentation
import CFSG.LocalAnalysis.SeitzReduction.F4PilotTwistLevi
import CFSG.ClassicalInvolution.RouteD.TypeDModel
public import CFSG.LieType.Universal.Spin.Roots
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.CharacterTheory.Semidihedral.OddFieldLift
import CFSG.ClassicalInvolution.Models.LinearFrames
import CFSG.ClassicalInvolution.Models.LinearPairs
import CFSG.ClassicalInvolution.Models.SymplecticPairs.Pairs
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LieType.Chevalley.C2E6StandardFixedData
import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
import CFSG.LieType.Steinberg.Classical.SpinFrame
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.SeitzReduction.F4PilotToralCentralizer
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.Open.QuasithinDefs
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
import CFSG.Walter.JRFacts

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.LieType.CurtisTits CFSG.LieType.Universal CFSG.LieType.Universal.Spin

noncomputable abbrev spinTenRankOne (F : Type) [Field F] (k : Fin 5) :
    Subgroup (spinGroup (quadPlus 5 F)) :=
  rankOne (plusDatum 5 F (by norm_num)).rootGroup k

private theorem levi_hom_ext {K G : Type} [Group K] [Group G] {I : Type} [DecidableEq I]
    (X : (I → ℤ) → Subgroup K) (J : Finset I) {ψ₁ ψ₂ : levi X J →* G}
    (h : ∀ k (hk : k ∈ J) (x : rankOne X k),
      ψ₁ (Subgroup.inclusion (rankOne_le_levi X hk) x) =
        ψ₂ (Subgroup.inclusion (rankOne_le_levi X hk) x)) : ψ₁ = ψ₂ := by
  ext ⟨x, hx⟩
  have hle : levi X J ≤ (MonoidHom.eqLocus ψ₁ ψ₂).map (levi X J).subtype := by
    refine iSup₂_le fun k hk y hy => ?_
    exact ⟨Subgroup.inclusion (rankOne_le_levi X hk) ⟨y, hy⟩, h k hk ⟨y, hy⟩,
      Subgroup.coe_inclusion (rankOne_le_levi X hk) ⟨y, hy⟩⟩
  obtain ⟨z, hz, hzx⟩ := hle hx
  have hzx' : z = ⟨x, hx⟩ := Subtype.ext hzx
  rw [← hzx']
  exact hz

private theorem cartanD_five_eq_zero (k l : Fin 5) (hk : k.val ≤ 1) (hl : 3 ≤ l.val) :
    cartanD 5 k l = 0 := by
  have hkl : k ≠ l := fun h => by rw [h] at hk; omega
  simp only [cartanD, Matrix.of_apply, if_neg hkl]
  rw [if_neg (by omega)]

private theorem five_nodes_cases (J : Finset (Fin 5)) (hJ : J.card ≤ 2) :
    (∀ k ∈ J, k.val ≤ 2) ∨ (∀ k ∈ J, 2 ≤ k.val) ∨
      ∃ k l : Fin 5, k.val ≤ 1 ∧ 3 ≤ l.val ∧ J = {k, l} := by
  by_cases h1 : ∀ k ∈ J, k.val ≤ 2
  · exact Or.inl h1
  by_cases h2 : ∀ k ∈ J, 2 ≤ k.val
  · exact Or.inr (Or.inl h2)
  push Not at h1 h2
  obtain ⟨l, hlJ, hl⟩ := h1
  obtain ⟨k, hkJ, hk⟩ := h2
  refine Or.inr (Or.inr ⟨k, l, by omega, by omega, ?_⟩)
  have hkl : k ≠ l := fun h => by rw [h] at hk; omega
  have hsub : ({k, l} : Finset (Fin 5)) ⊆ J := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    exacts [hkJ, hlJ]
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hkl]; exact hJ)).symm

private theorem mem_pair_of_eq {J : Finset (Fin 5)} {k l j : Fin 5} (hJ : J = {k, l})
    (hj : j ∈ J) : j = k ∨ j = l := by
  rw [hJ, Finset.mem_insert, Finset.mem_singleton] at hj
  exact hj

variable {F : Type} [Field F] {X G : Type} [Group X] [Group G]

theorem exists_hom_spinTen_of_rankOne (Θ : spinGroup (quadPlus 5 F) ≃* X)
    (ρ : ∀ k : Fin 5, spinTenRankOne F k →* G)
    (hext : ∀ J : Finset (Fin 5), J.card ≤ 2 →
      ∃ ψ : levi (plusRootGroup 5 F (by norm_num)) J →* G,
        ∀ k (hk : k ∈ J) (x : spinTenRankOne F k),
          ψ (Subgroup.inclusion (rankOne_le_levi _ hk) x) = ρ k x) :
    ∃ Ψ : X →* G, ∀ (k : Fin 5) (x : spinTenRankOne F k), Ψ (Θ x) = ρ k x := by
  classical
  have h35 : 3 ≤ 5 := by norm_num
  have hst := plusDatum_steinbergExtras (K := F) h35
  have hct := plusDatum_isCTGroupDatum (K := F) h35 (plusDatum_iSup_eq_top 5 F h35)
  have hU : IsUniversalCompletion.{0, 0, 0} (leviAmalgam (plusRootGroup 5 F h35)) :=
    (plusDatum 5 F h35).isUniversalCompletion_of_steinbergPresentation hct
      (CFSG.LieType.Steinberg.steinbergPresentation_of_extras hct hst)
  choose Ψ hΨ using fun J : {J : Finset (Fin 5) // J.card ≤ 2} => hext J.1 J.2
  have hcompat : IsCompatible (leviAmalgam (plusRootGroup 5 F h35)) Ψ := by
    intro I J hIJ x y hxy
    have hsub : I.1 ⊆ J.1 := hIJ
    have hle : levi (plusRootGroup 5 F h35) I.1 ≤ levi (plusRootGroup 5 F h35) J.1 :=
      levi_mono _ hsub
    have heq : (Ψ J).comp (Subgroup.inclusion hle) = Ψ I :=
      levi_hom_ext _ I.1 fun k hk x =>
        (hΨ J k (hsub hk) x).trans (hΨ I k hk x).symm
    have hx' : Subgroup.inclusion hle x = y :=
      Subtype.ext (by rw [Subgroup.coe_inclusion]; exact hxy)
    rw [← heq, MonoidHom.comp_apply, hx']
  obtain ⟨ψ, hψ, -⟩ := hU G Ψ hcompat
  refine ⟨ψ.comp Θ.symm.toMonoidHom, fun k x => ?_⟩
  have hk1 : ({k} : Finset (Fin 5)).card ≤ 2 := by simp
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  have h := hψ ⟨{k}, hk1⟩
    (Subgroup.inclusion (rankOne_le_levi (plusRootGroup 5 F h35) (Finset.mem_singleton_self k)) x)
  exact h.trans (hΨ ⟨{k}, hk1⟩ k (Finset.mem_singleton_self k) x)

theorem exists_levi_hom_pair_spinTen (ρ : ∀ k : Fin 5, spinTenRankOne F k →* G) {k l : Fin 5}
    (hkl : cartanD 5 k l = 0) (hρ : ∀ a b, Commute (ρ k a) (ρ l b)) :
    ∃ ψ : levi (plusRootGroup 5 F (by norm_num)) {k, l} →* G,
      ∀ j (hj : j ∈ ({k, l} : Finset (Fin 5))) (x : spinTenRankOne F j),
        ψ (Subgroup.inclusion (rankOne_le_levi _ hj) x) = ρ j x := by
  classical
  have h35 : 3 ≤ 5 := by norm_num
  have hst := plusDatum_steinbergExtras (K := F) h35
  have hct := plusDatum_isCTGroupDatum (K := F) h35 (plusDatum_iSup_eq_top 5 F h35)
  have hne : k ≠ l := by
    rintro rfl
    simp [cartanD] at hkl
  have hc : ∀ a ∈ spinTenRankOne F k, ∀ b ∈ spinTenRankOne F l, Commute a b :=
    fun a ha b hb => CFSG.ClassicalInvolution.RouteD.commutes_rankOne_plusDatum h35 hkl a ha b hb
  have hd : spinTenRankOne F k ⊓ spinTenRankOne F l = ⊥ :=
    CFSG.SeitzReduction.F4Pilot.rankOne_inf_rankOne_eq_bot (D := plusDatum 5 F h35) hct hst hne hc
  have hJle : levi (plusRootGroup 5 F h35) {k, l} ≤ spinTenRankOne F k ⊔ spinTenRankOne F l := by
    refine iSup₂_le fun j hj => ?_
    rcases mem_pair_of_eq rfl hj with rfl | rfl
    exacts [le_sup_left, le_sup_right]
  refine ⟨(CFSG.SeitzReduction.F4Pilot.supLift hc hd (ρ k) (ρ l) hρ).comp
    (Subgroup.inclusion hJle), fun j hj x => ?_⟩
  rw [MonoidHom.comp_apply]
  rcases mem_pair_of_eq rfl hj with rfl | rfl
  · have he : Subgroup.inclusion hJle (Subgroup.inclusion (rankOne_le_levi (plusRootGroup 5 F h35) hj) x) =
        ⟨x, Subgroup.mem_sup_left x.2⟩ := Subtype.ext rfl
    rw [he]
    exact CFSG.SeitzReduction.F4Pilot.supLift_apply_left hc hd hρ x
  · have he : Subgroup.inclusion hJle (Subgroup.inclusion (rankOne_le_levi (plusRootGroup 5 F h35) hj) x) =
        ⟨x, Subgroup.mem_sup_right x.2⟩ := Subtype.ext rfl
    rw [he]
    exact CFSG.SeitzReduction.F4Pilot.supLift_apply_right hc hd hρ x

theorem exists_hom_spinTen_of_two_charts (Θ : spinGroup (quadPlus 5 F) ≃* X) {P A : Subgroup X}
    (φ : P →* G) (α : A →* G)
    (hP : ∀ k : Fin 5, k.val ≤ 2 → (spinTenRankOne F k).map Θ.toMonoidHom ≤ P)
    (hA : ∀ k : Fin 5, 2 ≤ k.val → (spinTenRankOne F k).map Θ.toMonoidHom ≤ A)
    (hagree : ∀ x : spinTenRankOne F 2,
      φ ⟨Θ x, hP 2 le_rfl (Subgroup.mem_map_of_mem _ x.2)⟩ =
        α ⟨Θ x, hA 2 le_rfl (Subgroup.mem_map_of_mem _ x.2)⟩)
    (hcross : ∀ (k l : Fin 5) (hk : k.val ≤ 1) (hl : 3 ≤ l.val) (x : spinTenRankOne F k)
      (y : spinTenRankOne F l),
      Commute (φ ⟨Θ x, hP k (by omega) (Subgroup.mem_map_of_mem _ x.2)⟩)
        (α ⟨Θ y, hA l (by omega) (Subgroup.mem_map_of_mem _ y.2)⟩)) :
    ∃ Ψ : X →* G,
      (∀ (k : Fin 5) (hk : k.val ≤ 2) (x : spinTenRankOne F k),
        Ψ (Θ x) = φ ⟨Θ x, hP k hk (Subgroup.mem_map_of_mem _ x.2)⟩) ∧
      ∀ (k : Fin 5) (hk : 2 ≤ k.val) (x : spinTenRankOne F k),
        Ψ (Θ x) = α ⟨Θ x, hA k hk (Subgroup.mem_map_of_mem _ x.2)⟩ := by
  classical
  have h35 : 3 ≤ 5 := by norm_num
  let ρ : ∀ k : Fin 5, spinTenRankOne F k →* G := fun k =>
    if hk : k.val ≤ 2 then
      φ.comp ((Θ.toMonoidHom.comp (spinTenRankOne F k).subtype).codRestrict P
        fun x => hP k hk (Subgroup.mem_map_of_mem _ x.2))
    else
      α.comp ((Θ.toMonoidHom.comp (spinTenRankOne F k).subtype).codRestrict A
        fun x => hA k (by omega) (Subgroup.mem_map_of_mem _ x.2))
  have hρP : ∀ (k : Fin 5) (hk : k.val ≤ 2) (x : spinTenRankOne F k),
      ρ k x = φ ⟨Θ x, hP k hk (Subgroup.mem_map_of_mem _ x.2)⟩ := by
    intro k hk x
    simp only [ρ, dif_pos hk]
    rfl
  have hρA : ∀ (k : Fin 5) (hk : 2 ≤ k.val) (x : spinTenRankOne F k),
      ρ k x = α ⟨Θ x, hA k hk (Subgroup.mem_map_of_mem _ x.2)⟩ := by
    intro k hk x
    by_cases hk2 : k.val ≤ 2
    · have hk' : k = 2 := Fin.ext (by simp only [Fin.val_two]; omega)
      subst hk'
      rw [hρP 2 hk2 x]
      exact hagree x
    · simp only [ρ, dif_neg hk2]
      rfl
  obtain ⟨Ψ, hΨ⟩ := exists_hom_spinTen_of_rankOne Θ ρ fun J hJ => by
    rcases five_nodes_cases J hJ with hJ | hJ | ⟨k, l, hk, hl, rfl⟩
    · have hle : ∀ x ∈ levi (plusRootGroup 5 F h35) J, Θ x ∈ P := by
        have : levi (plusRootGroup 5 F h35) J ≤ P.comap Θ.toMonoidHom :=
          iSup₂_le fun k hk => Subgroup.map_le_iff_le_comap.mp (hP k (hJ k hk))
        exact fun x hx => this hx
      refine ⟨φ.comp ((Θ.toMonoidHom.comp (levi (plusRootGroup 5 F h35) J).subtype).codRestrict P
        fun x => hle x x.2), fun k hk x => ?_⟩
      rw [hρP k (hJ k hk) x, MonoidHom.comp_apply]
      exact congrArg φ (Subtype.ext rfl)
    · have hle : ∀ x ∈ levi (plusRootGroup 5 F h35) J, Θ x ∈ A := by
        have : levi (plusRootGroup 5 F h35) J ≤ A.comap Θ.toMonoidHom :=
          iSup₂_le fun k hk => Subgroup.map_le_iff_le_comap.mp (hA k (hJ k hk))
        exact fun x hx => this hx
      refine ⟨α.comp ((Θ.toMonoidHom.comp (levi (plusRootGroup 5 F h35) J).subtype).codRestrict A
        fun x => hle x x.2), fun k hk x => ?_⟩
      rw [hρA k (hJ k hk) x, MonoidHom.comp_apply]
      exact congrArg α (Subtype.ext rfl)
    · exact exists_levi_hom_pair_spinTen ρ (cartanD_five_eq_zero k l hk hl) fun a b => by
        rw [hρP k (by omega) a, hρA l (by omega) b]
        exact hcross k l hk hl a b
  exact ⟨Ψ, fun k hk x => (hΨ k x).trans (hρP k hk x),
    fun k hk x => (hΨ k x).trans (hρA k hk x)⟩

theorem iSup_spinTenRankOne_eq_top : ⨆ k : Fin 5, spinTenRankOne F k = ⊤ := by
  have h35 : 3 ≤ 5 := by norm_num
  have hct := plusDatum_isCTGroupDatum (K := F) h35 (plusDatum_iSup_eq_top 5 F h35)
  have htop := iSup_leviAmalgam_eq_top
    (CFSG.LieType.RootSystem.isCTRootSystem (plusDatum 5 F h35).isFiniteType
      (plusDatum 5 F h35).divisible) hct
  refine eq_top_iff.mpr (htop.symm.le.trans (iSup_le fun J => ?_))
  exact iSup₂_le fun k _ => le_iSup (fun k : Fin 5 => spinTenRankOne F k) k

theorem exists_hom_spinTen_of_two_charts_of_generation (Θ : spinGroup (quadPlus 5 F) ≃* X)
    {P A C : Subgroup X} (φ : P →* G) (α : A →* G)
    (hP : ∀ k : Fin 5, k.val ≤ 2 → (spinTenRankOne F k).map Θ.toMonoidHom ≤ P)
    (hA : ∀ k : Fin 5, 2 ≤ k.val → (spinTenRankOne F k).map Θ.toMonoidHom ≤ A)
    (hCP : C ≤ P) (hCA : C ≤ A) (h2C : (spinTenRankOne F 2).map Θ.toMonoidHom ≤ C)
    (hφα : ∀ (x : X) (hx : x ∈ C), φ ⟨x, hCP hx⟩ = α ⟨x, hCA hx⟩)
    (hcross : ∀ (k l : Fin 5) (hk : k.val ≤ 1) (hl : 3 ≤ l.val) (x : spinTenRankOne F k)
      (y : spinTenRankOne F l),
      Commute (φ ⟨Θ x, hP k (by omega) (Subgroup.mem_map_of_mem _ x.2)⟩)
        (α ⟨Θ y, hA l (by omega) (Subgroup.mem_map_of_mem _ y.2)⟩))
    (hAgen : A ≤ ⨆ (k : Fin 5) (_ : 2 ≤ k.val), (spinTenRankOne F k).map Θ.toMonoidHom)
    (hPgen : P ≤ (⨆ (k : Fin 5) (_ : k.val ≤ 2), (spinTenRankOne F k).map Θ.toMonoidHom) ⊔ C) :
    ∃ Ψ : X →* G, (∀ (x : X) (hx : x ∈ P), Ψ x = φ ⟨x, hx⟩) ∧
      (∀ (x : X) (hx : x ∈ A), Ψ x = α ⟨x, hx⟩) ∧ Ψ.range = φ.range ⊔ α.range := by
  obtain ⟨Ψ, hΨP, hΨA⟩ := exists_hom_spinTen_of_two_charts Θ φ α hP hA
    (fun x => hφα _ (h2C (Subgroup.mem_map_of_mem _ x.2))) hcross
  have hA' : ∀ (x : X) (hx : x ∈ A), Ψ x = α ⟨x, hx⟩ := by
    have hle : A ≤ (MonoidHom.eqLocus (Ψ.comp A.subtype) α).map A.subtype := by
      refine hAgen.trans (iSup₂_le fun k hk => ?_)
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨⟨Θ x, hA k hk (Subgroup.mem_map_of_mem _ hx)⟩, ?_, rfl⟩
      exact hΨA k hk ⟨x, hx⟩
    intro x hx
    obtain ⟨z, hz, hzx⟩ := hle hx
    have hz' : z = ⟨x, hx⟩ := Subtype.ext hzx
    subst hz'
    exact hz
  have hP' : ∀ (x : X) (hx : x ∈ P), Ψ x = φ ⟨x, hx⟩ := by
    have hle : P ≤ (MonoidHom.eqLocus (Ψ.comp P.subtype) φ).map P.subtype := by
      refine hPgen.trans (sup_le (iSup₂_le fun k hk => ?_) ?_)
      · rintro _ ⟨x, hx, rfl⟩
        refine ⟨⟨Θ x, hP k hk (Subgroup.mem_map_of_mem _ hx)⟩, ?_, rfl⟩
        exact hΨP k hk ⟨x, hx⟩
      · intro x hx
        refine ⟨⟨x, hCP hx⟩, ?_, rfl⟩
        exact (hA' x (hCA hx)).trans (hφα x hx).symm
    intro x hx
    obtain ⟨z, hz, hzx⟩ := hle hx
    have hz' : z = ⟨x, hx⟩ := Subtype.ext hzx
    subst hz'
    exact hz
  refine ⟨Ψ, hP', hA', le_antisymm ?_ (sup_le ?_ ?_)⟩
  ·
    have htop : (⊤ : Subgroup X) = ⨆ k : Fin 5, (spinTenRankOne F k).map Θ.toMonoidHom := by
      rw [← Subgroup.map_iSup, iSup_spinTenRankOne_eq_top, Subgroup.map_top_of_surjective _
        Θ.surjective]
    rw [MonoidHom.range_eq_map, htop, Subgroup.map_iSup]
    refine iSup_le fun k => ?_
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    by_cases hk : k.val ≤ 2
    · exact Subgroup.mem_sup_left ⟨⟨Θ x, hP k hk (Subgroup.mem_map_of_mem _ hx)⟩,
        (hΨP k hk ⟨x, hx⟩).symm⟩
    · exact Subgroup.mem_sup_right ⟨⟨Θ x, hA k (by omega) (Subgroup.mem_map_of_mem _ hx)⟩,
        (hΨA k (by omega) ⟨x, hx⟩).symm⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨x, hP' x x.2⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨x, hA' x x.2⟩

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

end

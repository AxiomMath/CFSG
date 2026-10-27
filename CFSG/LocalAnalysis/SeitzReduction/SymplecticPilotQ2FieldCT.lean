module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2FieldAlign

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic (equivStatedSp rootGroup rootDatum)
open CFSG.LieType.CurtisTits (rankOne levi IsCompatible)
open CFSG.Quasithin (perfectCore)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore statedSpMap)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG)

section Global

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ}

@[expose] noncomputable def nsGlobal (e : L ≃* StatedSp n K) : Subgroup G :=
  ⨆ k : Fin n, centralizerPerfectCore (modelToG e (nsTorusSp K k))

theorem nsGlobal_def (e : L ≃* StatedSp n K) :
    nsGlobal e = ⨆ k : Fin n, centralizerPerfectCore (modelToG e (nsTorusSp K k)) :=
  rfl

theorem mem_normalizer_nsGlobal (e : L ≃* StatedSp n K) {c : G}
    (hc : c ∈ centralizer (L : Set G)) : c ∈ normalizer (nsGlobal e : Set G) :=
  mem_normalizer_iSup_of_forall fun _ =>
    F4Pilot.normalizer_le_normalizer_centralizerPerfectCore _
      (UnitaryPilot.mem_normalizer_modelToG_of_mem_centralizer e hc _)

end Global

section Embed

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] {F : Type} [Field F]
  {n : ℕ}

theorem map_spBlock_compl_le_centralizerPerfectCore [Finite F] (hF : 4 ≤ Nat.card F)
    (e : L ≃* StatedSp n K) (ι : K →+* F) {ψ : StatedSp n F →* G}
    (hψ : ∀ x : StatedSp n K, ψ (spFieldMap n ι x) = ((e.symm x : L) : G)) (k : Fin n) :
    (spBlock F ({k}ᶜ : Finset (Fin n))).map ψ ≤
      centralizerPerfectCore (modelToG e (nsTorusSp K k)) := by
  refine CFSG.Quasithin.le_perfectCore_of_perfect ?_
    (by rw [← map_commutator, commutator_spBlock_eq hF])
  rw [nsTorusSp, centralizer_modelToG_zpowers]
  rintro _ ⟨y, hy, rfl⟩
  rw [mem_centralizer_singleton_iff, ← hψ, spFieldMap_nsElt, ← map_mul, ← map_mul]
  rw [SetLike.mem_coe, spBlock_compl_singleton] at hy
  exact congrArg ψ (mem_centralizer_singleton_iff.1 (mem_centralizer_nsElt_of_mem_complSp hy))

theorem range_le_nsGlobal_of_comp_spFieldMap [Finite F] (hF : 4 ≤ Nat.card F) (hn : 3 ≤ n)
    (e : L ≃* StatedSp n K) (ι : K →+* F) {ψ : StatedSp n F →* G}
    (hψ : ∀ x : StatedSp n K, ψ (spFieldMap n ι x) = ((e.symm x : L) : G)) :
    ψ.range ≤ nsGlobal e := by
  rw [MonoidHom.range_eq_map, ← iSup_spBlock_compl_singleton_eq_top hn, Subgroup.map_iSup]
  exact iSup_mono fun k => map_spBlock_compl_le_centralizerPerfectCore hF e ι hψ k

theorem le_range_of_comp_spFieldMap (e : L ≃* StatedSp n K) (ι : K →+* F)
    {ψ : StatedSp n F →* G}
    (hψ : ∀ x : StatedSp n K, ψ (spFieldMap n ι x) = ((e.symm x : L) : G)) : L ≤ ψ.range := by
  intro g hg
  refine ⟨spFieldMap n ι (e ⟨g, hg⟩), ?_⟩
  rw [hψ, e.symm_apply_apply]

theorem map_spBlock_compl_eq_of_nsFieldParam [Finite G] [Finite F] (hF : 4 ≤ Nat.card F)
    {e : L ≃* StatedSp n K} {ι : K →+* F} {ψ : StatedSp n F →* G} (hinj : Function.Injective ψ)
    (hψ : ∀ x : StatedSp n K, ψ (spFieldMap n ι x) = ((e.symm x : L) : G)) {t : G}
    {σ : F ≃+* F} {k : Fin n} (P : NsFieldParam e t ι σ k) :
    (spBlock F ({k}ᶜ : Finset (Fin n))).map ψ =
      centralizerPerfectCore (modelToG e (nsTorusSp K k)) := by
  refine Subgroup.eq_of_le_of_card_ge (map_spBlock_compl_le_centralizerPerfectCore hF e ι hψ k) ?_
  rw [← P.range_eq, Subgroup.card_map_of_injective hinj,
    ← Nat.card_congr (MonoidHom.ofInjective P.injective).toEquiv]

end Embed

section Recognition

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  {F : Type} [Field F] [Finite F] {n : ℕ} {e : L ≃* StatedSp n K} {t : G}
  {ι : K →+* F} {σ : F ≃+* F}

theorem exists_injective_nsFieldRow_of_agree (hF : 4 ≤ Nat.card F) (hn : 5 ≤ n)
    (P : ∀ k : Fin n, NsFieldParam e t ι σ k) (hagree : NsFieldParamAgree P) :
    ∃ ψ : StatedSp n F →* G, Function.Injective ψ ∧ ψ.range = nsGlobal e ∧
      (∀ x : StatedSp n K, ψ (spFieldMap n ι x) = ((e.symm x : L) : G)) ∧
      ∀ x : StatedSp n F, t * ψ x * t⁻¹ = ψ (fieldSp n F σ x) := by
  classical
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  choose kJ hkJ using fun J : {J : Finset (Fin n) // J.card ≤ 2} =>
    exists_notInSupp_of_card_le_two hn J.1 J.2
  have hKle : ∀ J, (rootDatum n F).leviAmalgam J ≤ spBlock F ({kJ J}ᶜ : Finset (Fin n)) :=
    fun J => (leviAmalgam_eq_iSup J).le.trans
      (iSup₂_le fun j hj => simpleRootSL2_le_spBlock_compl' (hkJ J j hj))
  set φ : ∀ J, (rootDatum n F).leviAmalgam J →* G :=
    fun J => (P (kJ J)).Φ.comp (Subgroup.inclusion (hKle J)) with hφ
  have hcomp : IsCompatible (rootDatum n F).leviAmalgam φ := by
    intro I J _ x y hxy
    change (P (kJ I)).Φ ⟨x, hKle I x.2⟩ = (P (kJ J)).Φ ⟨y, hKle J y.2⟩
    have hx' : (x : StatedSp n F) ∈ spBlock F ({kJ J}ᶜ : Finset (Fin n)) := hxy ▸ hKle J y.2
    rw [hagree (kJ I) (kJ J) x (hKle I x.2) hx']
    congr 1
    exact Subtype.ext hxy
  set G₀ : Subgroup G := ⨆ J, (φ J).range with hG₀
  have hle : ∀ J x, φ J x ∈ G₀ := fun J x => le_iSup (fun J => (φ J).range) J ⟨x, rfl⟩
  set φ' : ∀ J, (rootDatum n F).leviAmalgam J →* G₀ := fun J => (φ J).codRestrict G₀ (hle J)
    with hφ'
  have hcomp' : IsCompatible (rootDatum n F).leviAmalgam φ' := fun I J hIJ x y hxy =>
    Subtype.ext (hcomp I J hIJ x y hxy)
  have hgen' : ⨆ J, (φ' J).range = ⊤ := by
    apply Subgroup.map_injective G₀.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    refine (iSup_congr fun J => ?_).trans hG₀.symm
    rw [← MonoidHom.range_comp]
    rfl
  have hinjφ : ∀ J, Function.Injective (φ J) := fun J =>
    (P (kJ J)).injective.comp (Subgroup.inclusion_injective (hKle J))
  have hnt : ∃ J, ∃ x, φ' J x ≠ 1 := by
    obtain ⟨J, hJ⟩ := CFSG.LieType.CurtisTits.exists_leviAmalgam_ne_bot
      (CFSG.LieType.Universal.Symplectic.steinbergExtras n F) (show 0 < n by omega)
    obtain ⟨x, hx⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hJ
    refine ⟨J, x, fun h => hx ?_⟩
    have h1 : φ J x = φ J 1 := by
      rw [map_one]
      exact congrArg Subtype.val h
    exact hinjφ J h1
  obtain ⟨g, hg1, hFc⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := F)
  have hadm : StatedLieAdmissible .PSp n 2 g :=
    ⟨Nat.prime_two, hg1, by omega, fun h => by
      have := congrArg Prod.fst h
      simp only at this
      omega⟩
  obtain ⟨-, -, hrec, -⟩ :=
    CFSG.LieType.CurtisTits.curtisTitsConclusion_symplectic.{0} (F := F) hadm hFc
      (by omega : 3 ≤ n)
  obtain ⟨ψ₀, hψ₀, -, hker, -⟩ := hrec G₀ φ' hcomp' hgen' hnt
  have hinj₀ : Function.Injective ψ₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (center_statedSp_eq_bot n).le
  set ψ : StatedSp n F →* G := G₀.subtype.comp ψ₀ with hψdef
  have hψinj : Function.Injective ψ := G₀.subtype_injective.comp hinj₀
  have hψφ : ∀ J (x : (rootDatum n F).leviAmalgam J), ψ x = φ J x :=
    fun J x => congrArg Subtype.val (hψ₀ J x)
  have hJ1 : ∀ j : Fin n, ({j} : Finset (Fin n)).card ≤ 2 := fun j => by simp
  have hψJ : ∀ (j : Fin n) (y : StatedSp n F) (hy : y ∈ simpleRootSL2 F j),
      ψ y = (P (kJ ⟨{j}, hJ1 j⟩)).Φ ⟨y, simpleRootSL2_le_spBlock_compl'
        (hkJ ⟨{j}, hJ1 j⟩ j (Finset.mem_singleton_self j)) hy⟩ := by
    intro j y hy
    have hyK : y ∈ (rootDatum n F).leviAmalgam ⟨{j}, hJ1 j⟩ :=
      (leviAmalgam_eq_iSup ⟨{j}, hJ1 j⟩).ge
        (mem_iSup_of_mem j (mem_iSup_of_mem (Finset.mem_singleton_self j) hy))
    exact hψφ ⟨{j}, hJ1 j⟩ ⟨y, hyK⟩
  have hψι : ∀ x : StatedSp n K, ψ (spFieldMap n ι x) = ((e.symm x : L) : G) := by
    intro x
    have htop : (⊤ : Subgroup (StatedSp n K)) ≤
        MonoidHom.eqLocus (ψ.comp (spFieldMap n ι)) (L.subtype.comp e.symm.toMonoidHom) := by
      rw [← iSup_simpleRootSL2_eq_top (show 1 ≤ n by omega), iSup_le_iff]
      intro j y hy
      set k := kJ ⟨{j}, hJ1 j⟩ with hk
      have hkj := hkJ ⟨{j}, hJ1 j⟩ j (Finset.mem_singleton_self j)
      have hyF : spFieldMap n ι y ∈ simpleRootSL2 F j := by
        rw [spFieldMap_eq_statedSpMap]
        exact map_statedSpMap_simpleRootSL2_le ι j ⟨y, hy, rfl⟩
      change ψ (spFieldMap n ι y) = ((e.symm y : L) : G)
      rw [hψJ j _ hyF]
      exact (P k).N1 y (simpleRootSL2_le_spBlock_compl' hkj hy)
    exact htop (mem_top x)
  refine ⟨ψ, hψinj, ?_, hψι, ?_⟩
  ·
    refine le_antisymm (range_le_nsGlobal_of_comp_spFieldMap hF (by omega) e ι hψι)
      (iSup_le fun k => ?_)
    rw [← map_spBlock_compl_eq_of_nsFieldParam hF hψinj hψι (P k), MonoidHom.range_eq_map]
    exact map_mono le_top
  ·
    intro x
    have htop : (⊤ : Subgroup (StatedSp n F)) ≤
        MonoidHom.eqLocus ((MulAut.conj t).toMonoidHom.comp ψ)
          (ψ.comp (fieldSp n F σ).toMonoidHom) := by
      rw [← iSup_simpleRootSL2_eq_top (show 1 ≤ n by omega), iSup_le_iff]
      intro j y hy
      set k := kJ ⟨{j}, hJ1 j⟩ with hk
      have hyσ : fieldSp n F σ y ∈ simpleRootSL2 F j := fieldSp_mem_simpleRootSL2 σ hy
      change t * ψ y * t⁻¹ = ψ (fieldSp n F σ y)
      rw [hψJ j y hy, hψJ j _ hyσ, (P k).N3]
      congr 1
    exact htop (mem_top x)

theorem exists_injective_nsFieldRow (hF : 4 ≤ Nat.card F) (hn : 5 ≤ n) (hσ : orderOf σ = 2)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (hparam : ∀ k : Fin n, Nonempty (NsFieldParam e t ι σ k)) :
    ∃ ψ : StatedSp n F →* G, Function.Injective ψ ∧ ψ.range = nsGlobal e ∧
      (∀ x : StatedSp n K, ψ (spFieldMap n ι x) = ((e.symm x : L) : G)) ∧
      ∀ x : StatedSp n F, t * ψ x * t⁻¹ = ψ (fieldSp n F σ x) := by
  obtain ⟨Q, hQ⟩ := exists_nsFieldParamAgree hF (by omega) hσ hfix fun k => (hparam k).some
  exact exists_injective_nsFieldRow_of_agree hF hn Q hQ

end Recognition

end CFSG.SeitzReduction.SymplecticPilot

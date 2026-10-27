module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviBorelFactor
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ParabLeviComponents
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParK
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParS
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevAtomTransport
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevParabolicInputs

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.ABGLocalTools CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData Subgroup
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.AGLEmbedding.ParabHub
  CFSG.AGLEmbeddingD2.ParabLevi CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

section Defs

variable {K Y : Type} [Group K] [Group Y]

@[expose] def GomiLeviFactors (D : UniversalRootDatum K) : Prop :=
  ∀ C : Set (Fin D.rank), IsNodeConnected D C → 2 ≤ C.ncard → C ≠ Set.univ →
    GomiLeviFactor ↥(leviM D C)

@[expose] def GomiLeviFactorsMap (D : UniversalRootDatum K) (π : K →* Y) : Prop :=
  ∀ C : Set (Fin D.rank), IsNodeConnected D C → 2 ≤ C.ncard → C ≠ Set.univ →
    GomiLeviFactor ↥((leviM D C).map π)

@[expose] def borelLeviSet (D : UniversalRootDatum K) (π : K →* Y) (J : Set (Fin D.rank)) :
    Set (Subgroup Y) :=
  {A | ∃ i ∈ J, A = (leviM D (nodeComponent D J i)).map π}

end Defs

variable {K Y : Type} [Group K] [Finite K] [Group Y] [Finite Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {e : ℕ} {J : Set (Fin D.rank)}

omit [Finite K] in
private theorem leviM_mono' {J J' : Set (Fin D.rank)} (h : J ⊆ J') : leviM D J ≤ leviM D J' :=
  iSup₂_le fun _i hi => rankOne_le_leviM (h hi)

omit [Finite K] in
private theorem leviM_le_centralizer_of_rankOne' {J J' : Set (Fin D.rank)}
    (h : ∀ i ∈ J, ∀ j ∈ J', rankOne D.rootGroup i ≤
      Subgroup.centralizer (rankOne D.rootGroup j : Set K)) :
    leviM D J ≤ Subgroup.centralizer ((leviM D J' : Subgroup K) : Set K) := by
  refine iSup₂_le fun i hi x hx => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h2 : leviM D J' ≤ Subgroup.centralizer ({x} : Set K) := by
    refine iSup₂_le fun j hj y hy => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact ((Subgroup.mem_centralizer_iff.1 (h i hi j hj hx)) y hy).symm
  exact ((Subgroup.mem_centralizer_iff.1 (h2 hy)) x rfl).symm

omit [Finite K] in
private theorem rankOne_le_centralizer_leviM {i : Fin D.rank} {J' : Set (Fin D.rank)}
    (h : ∀ j ∈ J', rankOne D.rootGroup i ≤
      Subgroup.centralizer (rankOne D.rootGroup j : Set K)) :
    rankOne D.rootGroup i ≤ Subgroup.centralizer ((leviM D J' : Subgroup K) : Set K) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h2 : leviM D J' ≤ Subgroup.centralizer ({x} : Set K) := by
    refine iSup₂_le fun j hj y hy => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact ((Subgroup.mem_centralizer_iff.1 (h j hj hx)) y hy).symm
  exact ((Subgroup.mem_centralizer_iff.1 (h2 hy)) x rfl).symm

private theorem le_normalizer_sup_of_le {G : Type*} [Group G] {P R R' A : Subgroup G}
    (hR : P ≤ Subgroup.normalizer (R : Set G))
    (hX : P ≤ Subgroup.normalizer ((R' ⊔ A : Subgroup G) : Set G)) (hR' : R' ≤ R) :
    P ≤ Subgroup.normalizer ((R ⊔ A : Subgroup G) : Set G) := by
  refine le_normalizer_of_map_conj_le fun g hg => ?_
  have hRg : R.map (MulAut.conj g).toMonoidHom ≤ R := (mem_normalizer_iff_map_conj.1 (hR hg)).le
  have hXg : (R' ⊔ A).map (MulAut.conj g).toMonoidHom ≤ R' ⊔ A :=
    (mem_normalizer_iff_map_conj.1 (hX hg)).le
  rw [Subgroup.map_sup]
  exact sup_le (hRg.trans le_sup_left)
    ((Subgroup.map_mono le_sup_right).trans (hXg.trans (sup_le_sup_right hR' A)))

omit [Finite K] [Finite Y] in
theorem borelLeviSet_le {A : Subgroup Y} (hA : A ∈ borelLeviSet D π J) :
    A ≤ (parJ D H J).map π := by
  rcases hA with ⟨i, hi, rfl⟩
  exact Subgroup.map_mono ((leviM_mono' (nodeComponent_subset hi)).trans le_sup_right)

omit [Finite K] [Finite Y] in
theorem borelLeviSet_commute (h : BorelQuotient D n H π e) {A₁ A₂ : Subgroup Y}
    (h₁ : A₁ ∈ borelLeviSet D π J) (h₂ : A₂ ∈ borelLeviSet D π J) (hne : A₁ ≠ A₂) :
    ⁅A₁, A₂⁆ = ⊥ := by
  rcases h₁ with ⟨i, hi, rfl⟩
  rcases h₂ with ⟨j, hj, rfl⟩
  have hcomp : nodeComponent D J i ≠ nodeComponent D J j := fun hc => hne (by rw [hc])
  have hbot : ⁅leviM D (nodeComponent D J i), leviM D (nodeComponent D J j)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    refine leviM_le_centralizer_of_rankOne' fun k hk l hl => ?_
    have hcartan : D.cartan k l = 0 :=
      cartan_eq_zero_of_nodeComponent_ne hi hj hcomp hk hl
    have hkl : k ≠ l := by
      intro hkl
      apply hcomp
      rw [← nodeComponent_eq_of_mem hk, ← nodeComponent_eq_of_mem hl, hkl]
    have hcomm := CFSG.AGLEmbedding.ParabPrime.commutes_rankOne_of_cartan_eq_zero
      h.extras hkl hcartan
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcomm x hx y hy).symm
  rw [← Subgroup.map_commutator, hbot, Subgroup.map_bot]

theorem borelLeviSet_pElementSubgroup_eq (h : BorelQuotient D n H π e) {A : Subgroup Y}
    (hA : A ∈ borelLeviSet D π J) : pElementSubgroup 2 A = A := by
  rcases hA with ⟨i, hi, rfl⟩
  refine le_antisymm (pElementSubgroup_le _) ?_
  refine (Subgroup.map_mono ?_).trans (map_pElementSubgroup_le_pElementSubgroup_map π _)
  exact iSup₂_le fun k hk => rankOne_le_pElementSubgroup h (rankOne_le_leviM hk)

omit [Finite K] [Finite Y] in
theorem map_leviRad_le_pCoreOf (h : BorelQuotient D n H π e) (J : Set (Fin D.rank)) :
    (leviRad D J).map π ≤ pCoreOf 2 ((parJ D H J).map π) := by
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2) ?_ ?_ ?_
  · exact Subgroup.map_mono ((leviRad_le_posUnipotent).trans
      ((posUnipotent_le_borel).trans (borel_le_parJ J)))
  · exact (Subgroup.map_mono (le_normalizer_leviRad fun j hj =>
      parJ_le_normalizer_radical h.ct h.extras hj)).trans (Subgroup.le_normalizer_map π)
  · exact (isPGroup_leviRad h.extras h.pGroup).map π

omit [Finite K] [Finite Y] in
theorem map_posUnipotent_le (h : BorelQuotient D n H π e) (J : Set (Fin D.rank)) :
    (posUnipotent D).map π ≤ pCoreOf 2 ((parJ D H J).map π) ⊔ sSup (borelLeviSet D π J) := by
  refine (Subgroup.map_mono (posUnipotent_le_leviRad_sup_leviM (I := J) h.ct)).trans ?_
  rw [Subgroup.map_sup]
  refine sup_le ((map_leviRad_le_pCoreOf h J).trans le_sup_left) ?_
  have hlev : leviM D J = ⨆ i ∈ J, leviM D (nodeComponent D J i) :=
    leviM_eq_iSup_leviM_nodeComponent
  refine Subgroup.map_le_iff_le_comap.mpr ?_
  conv_lhs => rw [hlev]
  refine iSup₂_le fun i hi => ?_
  have hmem : (leviM D (nodeComponent D J i)).map π ∈ borelLeviSet D π J := ⟨i, hi, rfl⟩
  exact (Subgroup.le_comap_map π (leviM D (nodeComponent D J i))).trans
    (Subgroup.comap_mono ((le_sSup hmem).trans le_sup_right))

omit [Finite K] [Finite Y] in
theorem map_parJ_le_normalizer_pCoreOf_sup (h : BorelQuotient D n H π e) {A : Subgroup Y}
    (hA : A ∈ borelLeviSet D π J) :
    (parJ D H J).map π ≤
      normalizer ((pCoreOf 2 ((parJ D H J).map π) ⊔ A : Subgroup Y) : Set Y) := by
  rcases hA with ⟨i₀, hi₀, rfl⟩
  set C := nodeComponent D J i₀ with hC
  have hMJ_MC : leviM D J ≤ Subgroup.normalizer ((leviM D C : Subgroup K) : Set K) := by
    refine iSup₂_le fun i hi => ?_
    by_cases hiC : i ∈ C
    · exact (rankOne_le_leviM hiC).trans Subgroup.le_normalizer
    · have hcomp : nodeComponent D J i ≠ C := fun hc => hiC (hc ▸ mem_nodeComponent_self J i)
      refine (rankOne_le_centralizer_leviM (J' := C) fun k hk => ?_).trans
        (Subgroup.centralizer_le_normalizer ((leviM D C : Subgroup K) : Set K))
      have hcartan : D.cartan i k = 0 :=
        cartan_eq_zero_of_nodeComponent_ne hi hi₀ hcomp (mem_nodeComponent_self J i) hk
      have hkl : i ≠ k := fun hik => hiC (hik.symm ▸ hk)
      have hcomm := CFSG.AGLEmbedding.ParabPrime.commutes_rankOne_of_cartan_eq_zero
        h.extras hkl hcartan
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hcomm x hx y hy).symm
  have hMJ_rad : leviM D J ≤ Subgroup.normalizer (leviRad D J : Set K) :=
    iSup₂_le fun i hi => rankOne_le_normalizer_leviRad h.extras hi
  have hMJ : leviM D J ≤
      Subgroup.normalizer ((leviRad D J ⊔ leviM D C : Subgroup K) : Set K) :=
    le_normalizer_sup hMJ_rad hMJ_MC
  have hU : posUnipotent D ≤
      Subgroup.normalizer ((leviRad D J ⊔ leviM D C : Subgroup K) : Set K) :=
    (posUnipotent_le_leviRad_sup_leviM (I := J) h.ct).trans
      (sup_le (le_sup_left.trans Subgroup.le_normalizer) hMJ)
  have hT : (⨆ k, H k) ≤
      Subgroup.normalizer ((leviRad D J ⊔ leviM D C : Subgroup K) : Set K) :=
    le_normalizer_sup (le_sup_left.trans (borel_le_normalizer_leviRad h.ct h.extras))
      (torus_le_normalizer_leviM h.ct)
  have hparJ : parJ D H J ≤
      Subgroup.normalizer ((leviRad D J ⊔ leviM D C : Subgroup K) : Set K) :=
    sup_le (sup_le hT hU) hMJ
  have hPX : (parJ D H J).map π ≤
      Subgroup.normalizer (((leviRad D J).map π ⊔ (leviM D C).map π : Subgroup Y) : Set Y) := by
    have h1 := (Subgroup.map_mono hparJ).trans (Subgroup.le_normalizer_map π)
    rwa [Subgroup.map_sup] at h1
  refine le_normalizer_sup_of_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _) hPX ?_
  exact map_leviRad_le_pCoreOf h J

theorem borelLeviSet_atom (h : BorelQuotient D n H π e) (A : Subgroup Y)
    (hA : IsGomiAtom ⊤ ((posUnipotent D).map π) A) (hAP : A ≤ (parJ D H J).map π) :
    ∃ M ∈ borelLeviSet D π J,
      A ≤ ⊤ ⊓ normalizer (((posUnipotent D).map π : Subgroup Y) : Set Y) ⊔ M ∧
        ∀ M' ∈ borelLeviSet D π J,
          A ≤ ⊤ ⊓ normalizer (((posUnipotent D).map π : Subgroup Y) : Set Y) ⊔ M' → M' = M := by
  obtain ⟨k, hk⟩ := exists_eq_map_parJ h
    ((isGomiAtom_iff_isMinOverBorel ⊤ ((posUnipotent D).map π) A).1 hA)
  have hkJ : k ∈ J := by
    rw [hk] at hAP
    have h1 : rankOne D.rootGroup k ≤ ((parJ D H J).map π).comap π :=
      Subgroup.map_le_iff_le_comap.1
        ((Subgroup.map_mono (rankOne_le_parJ (J := {k}) rfl)).trans hAP)
    rw [comap_map_of_ker_le (ker_le_parJ h J)] at h1
    exact mem_of_rankOne_le_parJ h.ct h.extras h1
  set C := nodeComponent D J k with hC
  refine ⟨(leviM D C).map π, ⟨k, hkJ, by rw [hC]⟩, ?_, ?_⟩
  · rw [hk, top_inf_eq]
    have hAK : parJ D H {k} ≤ Subgroup.normalizer (posUnipotent D : Set K) ⊔ leviM D C := by
      refine sup_le ((borel_le_normalizer_posUnipotent h.ct).trans le_sup_left) ?_
      refine iSup₂_le fun j hj => ?_
      rw [Set.mem_singleton_iff] at hj
      rw [hj]
      exact (rankOne_le_leviM (mem_nodeComponent_self J k)).trans le_sup_right
    refine (Subgroup.map_mono hAK).trans ?_
    rw [Subgroup.map_sup]
    exact sup_le ((Subgroup.le_normalizer_map π).trans le_sup_left) le_sup_right
  · intro M' hM' hle
    rcases hM' with ⟨i', hi', rfl⟩
    rw [top_inf_eq] at hle
    have hleC : (parJ D H {k}).map π ≤ (parJ D H (nodeComponent D J i')).map π := by
      rw [hk] at hle
      refine hle.trans ?_
      rw [h.normalizer_map_posUnipotent, ← Subgroup.map_sup]
      exact le_rfl
    have hPk_le : parJ D H {k} ≤ parJ D H (nodeComponent D J i') := by
      have h2 := Subgroup.map_le_iff_le_comap.1 hleC
      rwa [Subgroup.comap_map_eq, sup_eq_left.mpr (ker_le_parJ h _)] at h2
    have hkC' : k ∈ nodeComponent D J i' :=
      mem_of_rankOne_le_parJ h.ct h.extras ((rankOne_le_parJ (J := {k}) rfl).trans hPk_le)
    have hceq : nodeComponent D J i' = C :=
      (nodeComponent_eq_of_mem hkC').symm.trans hC.symm
    rw [hceq]

end CFSG.GroupTheory

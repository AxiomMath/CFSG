module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeFieldMain

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic (rootDatum)
open CFSG.LieType.CurtisTits (IsCompatible)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)

theorem exists_notInSupp_four (J : Finset (Fin 4)) (hJ : J.card ≤ 2) (h02 : J ≠ {0, 2}) :
    ∃ k : Fin 4, ∀ j ∈ J, NotInSupp k j := by
  have key : ∀ J : Finset (Fin 4), J.card ≤ 2 → J ≠ {0, 2} →
      ∃ k : Fin 4, ∀ j ∈ J, k ≠ j ∧ (j.val + 1 < 4 → k.val ≠ j.val + 1) := by
    decide
  exact key J hJ h02

theorem subset_zero_or_two_of_subset {I : Finset (Fin 4)} (hI : I ⊆ {0, 2}) (hne : I ≠ {0, 2}) :
    I ⊆ {0} ∨ I ⊆ {2} := by
  by_cases h2 : (2 : Fin 4) ∈ I
  · right
    intro j hj
    rcases Finset.mem_insert.1 (hI hj) with rfl | h
    · exfalso
      exact hne (Finset.Subset.antisymm hI (by
        intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact hj
        · rw [Finset.mem_singleton.1 hx]
          exact h2))
    · exact h
  · left
    intro j hj
    rcases Finset.mem_insert.1 (hI hj) with rfl | h
    · exact Finset.mem_singleton_self _
    · rw [Finset.mem_singleton.1 h] at hj
      exact absurd hj h2

section Four

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  {F : Type} [Field F] [Finite F] {e : L ≃* StatedSp 4 K} {t : G} {ι : K →+* F} {σ : F ≃+* F}

omit [Finite F] in
theorem commute_simpleRootSL2_zero_two :
    ∀ a ∈ simpleRootSL2 F (0 : Fin 4), ∀ b ∈ simpleRootSL2 F (2 : Fin 4), Commute a b := by
  intro a ha b hb
  refine commute_of_mem_spBlock_of_disjoint (I := {0, 1}) (J := {2, 3}) (by decide)
    (simpleRootSL2_le_spBlock (by decide) (fun _ => by simp) ha)
    (simpleRootSL2_le_spBlock (by decide) (fun _ => by simp) hb)

omit [Finite F] in
theorem simpleRootSL2_zero_inf_two :
    simpleRootSL2 F (0 : Fin 4) ⊓ simpleRootSL2 F (2 : Fin 4) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨ha, hb⟩
  have h1 := simpleRootSL2_le_spBlock (F := F) (N := ({0, 1} : Finset (Fin 4))) (by decide)
    (fun _ => by simp) ha
  have h2 := simpleRootSL2_le_spBlock (F := F) (N := ({2, 3} : Finset (Fin 4))) (by decide)
    (fun _ => by simp) hb
  exact mem_bot.2 (eq_one_of_isSupp_of_isSupp_compl h1
    (suppGroup_mono (planeCoords_subset_compl_of_disjoint (by decide)) h2))

omit [Finite F] in
theorem leviAmalgam_zero_two (J : {J : Finset (Fin 4) // J.card ≤ 2}) (hJ : J.1 = {0, 2}) :
    (rootDatum 4 F).leviAmalgam J =
      simpleRootSL2 F (0 : Fin 4) ⊔ simpleRootSL2 F (2 : Fin 4) := by
  rw [leviAmalgam_eq_iSup, hJ, Finset.iSup_insert, Finset.iSup_singleton]

end Four

section Main4

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  {F : Type} [Field F] [Finite F]

theorem exists_injective_fieldRow_four_of_agree (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 4 K)
    {t : G} {ι : K →+* F} {σ : F ≃+* F} (P : ∀ k : Fin 4, FieldNeighbourParam e t ι σ k)
    (hagree : FieldParamAgree P)
    (hcomm : ∀ a ∈ pieceCore e ({0} : Finset (Fin 4)),
      ∀ b ∈ pieceCore e ({2} : Finset (Fin 4)), Commute a b) :
    ∃ ψ : StatedSp 4 F →* G, Function.Injective ψ ∧ ψ.range = spGlobal e ∧
      (∀ x : StatedSp 4 K, ψ (spFieldMap 4 ι x) = ((e.symm x : L) : G)) ∧
      ∀ x : StatedSp 4 F, t * ψ x * t⁻¹ = ψ (fieldSp 4 F σ x) := by
  classical
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  choose kJ hkJ using fun (J : {J : Finset (Fin 4) // J.card ≤ 2}) (h : J.1 ≠ {0, 2}) =>
    exists_notInSupp_four J.1 J.2 h
  have hJ1 : ∀ j : Fin 4, ({j} : Finset (Fin 4)).card ≤ 2 := fun j => by simp
  have hJ1ne : ∀ j : Fin 4, ({j} : Finset (Fin 4)) ≠ {0, 2} := fun j h => by
    have := congrArg Finset.card h
    simp at this
  have hkpS : ∀ j : Fin 4, NotInSupp (kJ ⟨{j}, hJ1 j⟩ (hJ1ne j)) j := fun j =>
    hkJ ⟨{j}, hJ1 j⟩ (hJ1ne j) j (Finset.mem_singleton_self j)
  have hKle : ∀ (J : {J : Finset (Fin 4) // J.card ≤ 2}) (h : J.1 ≠ {0, 2}),
      (rootDatum 4 F).leviAmalgam J ≤ spBlock F ({kJ J h}ᶜ : Finset (Fin 4)) :=
    fun J h => (leviAmalgam_eq_iSup J).le.trans
      (iSup₂_le fun j hj => simpleRootSL2_le_spBlock_compl' (hkJ J h j hj))
  have hA := simpleRootSL2_le_spBlock_compl' (F := F) (hkpS 0)
  have hB := simpleRootSL2_le_spBlock_compl' (F := F) (hkpS 2)
  obtain ⟨fA, hfA⟩ : ∃ f : simpleRootSL2 F (0 : Fin 4) →* G,
      ∀ a, f a = (P (kJ ⟨{0}, hJ1 0⟩ (hJ1ne 0))).Φ ⟨a, hA a.2⟩ :=
    ⟨(P (kJ ⟨{0}, hJ1 0⟩ (hJ1ne 0))).Φ.comp (Subgroup.inclusion hA), fun a => rfl⟩
  obtain ⟨gB, hgB⟩ : ∃ g : simpleRootSL2 F (2 : Fin 4) →* G,
      ∀ b, g b = (P (kJ ⟨{2}, hJ1 2⟩ (hJ1ne 2))).Φ ⟨b, hB b.2⟩ :=
    ⟨(P (kJ ⟨{2}, hJ1 2⟩ (hJ1ne 2))).Φ.comp (Subgroup.inclusion hB), fun b => rfl⟩
  have hfM : ∀ a, fA a ∈ pieceCore e ({0} : Finset (Fin 4)) := by
    intro a
    rw [hfA, (P _).pieceCore_singleton_eq_map hK (hkpS 0).1 (hkpS 0).2]
    exact ⟨⟨a, hA a.2⟩, mem_subgroupOf.2 a.2, rfl⟩
  have hgM : ∀ b, gB b ∈ pieceCore e ({2} : Finset (Fin 4)) := by
    intro b
    rw [hgB, (P _).pieceCore_singleton_eq_map hK (hkpS 2).1 (hkpS 2).2]
    exact ⟨⟨b, hB b.2⟩, mem_subgroupOf.2 b.2, rfl⟩
  have hfg : ∀ a b, Commute (fA a) (gB b) := fun a b => hcomm _ (hfM a) _ (hgM b)
  obtain ⟨ρ, hρA, hρB⟩ : ∃ ρ : ↥(simpleRootSL2 F (0 : Fin 4) ⊔ simpleRootSL2 F (2 : Fin 4)) →* G,
      (∀ a : simpleRootSL2 F (0 : Fin 4), ρ ⟨a, mem_sup_left a.2⟩ = fA a) ∧
      ∀ b : simpleRootSL2 F (2 : Fin 4), ρ ⟨b, mem_sup_right b.2⟩ = gB b :=
    ⟨F4Pilot.supLift commute_simpleRootSL2_zero_two simpleRootSL2_zero_inf_two fA gB hfg,
      F4Pilot.supLift_apply_left _ _ hfg, F4Pilot.supLift_apply_right _ _ hfg⟩
  obtain ⟨φ, hφne, hφ02⟩ : ∃ φ : ∀ J : {J : Finset (Fin 4) // J.card ≤ 2},
      (rootDatum 4 F).leviAmalgam J →* G,
      (∀ (J : {J : Finset (Fin 4) // J.card ≤ 2}) (h : J.1 ≠ {0, 2}) x,
        φ J x = (P (kJ J h)).Φ ⟨x, hKle J h x.2⟩) ∧
      ∀ (J : {J : Finset (Fin 4) // J.card ≤ 2}) (h : J.1 = {0, 2}) x,
        φ J x = ρ ⟨x, (leviAmalgam_zero_two J h).le x.2⟩ := by
    refine ⟨fun J => if h : J.1 = {0, 2} then
        ρ.comp (Subgroup.inclusion (leviAmalgam_zero_two J h).le)
      else (P (kJ J h)).Φ.comp (Subgroup.inclusion (hKle J h)), fun J h x => ?_, fun J h x => ?_⟩
    · simp only [dite_eq_right h]
      rfl
    · simp only [dite_eq_left h]
      rfl
  have hcomp : IsCompatible (rootDatum 4 F).leviAmalgam φ := by
    intro (I : {J : Finset (Fin 4) // J.card ≤ 2}) (J : {J : Finset (Fin 4) // J.card ≤ 2}) hIJ x y
      hxy
    have hIJ' : I.1 ⊆ J.1 := hIJ
    by_cases hJ : J.1 = {0, 2}
    · by_cases hI : I.1 = {0, 2}
      · have hIJeq : I = J := Subtype.ext (hI.trans hJ.symm)
        subst hIJeq
        exact congrArg (φ I) (Subtype.ext hxy)
      · rw [hφne I hI, hφ02 J hJ]
        rcases subset_zero_or_two_of_subset (hJ ▸ hIJ') hI with h0 | h2
        · have hxA : (x : StatedSp 4 F) ∈ simpleRootSL2 F (0 : Fin 4) :=
            (leviAmalgam_eq_iSup I).le.trans (iSup₂_le fun j hj => by
              rw [Finset.mem_singleton.1 (h0 hj)]) x.2
          have hyA : (y : StatedSp 4 F) ∈ simpleRootSL2 F (0 : Fin 4) := hxy ▸ hxA
          have h1 := hρA ⟨y, hyA⟩
          rw [hfA] at h1
          refine Eq.trans ?_ h1.symm
          rw [hagree (kJ I hI) _ x (hKle I hI x.2) (hxy ▸ hA hyA)]
          congr 1
          exact Subtype.ext hxy
        · have hxB : (x : StatedSp 4 F) ∈ simpleRootSL2 F (2 : Fin 4) :=
            (leviAmalgam_eq_iSup I).le.trans (iSup₂_le fun j hj => by
              rw [Finset.mem_singleton.1 (h2 hj)]) x.2
          have hyB : (y : StatedSp 4 F) ∈ simpleRootSL2 F (2 : Fin 4) := hxy ▸ hxB
          have h1 := hρB ⟨y, hyB⟩
          rw [hgB] at h1
          refine Eq.trans ?_ h1.symm
          rw [hagree (kJ I hI) _ x (hKle I hI x.2) (hxy ▸ hB hyB)]
          congr 1
          exact Subtype.ext hxy
    · have hI : I.1 ≠ {0, 2} := fun hI => hJ (Finset.eq_of_subset_of_card_le (hI ▸ hIJ')
        (J.2.trans (by decide))).symm
      rw [hφne I hI, hφne J hJ]
      have hx' : (x : StatedSp 4 F) ∈ spBlock F ({kJ J hJ}ᶜ : Finset (Fin 4)) :=
        hxy ▸ hKle J hJ y.2
      rw [hagree (kJ I hI) (kJ J hJ) x (hKle I hI x.2) hx']
      congr 1
      exact Subtype.ext hxy
  set G₀ : Subgroup G := ⨆ J, (φ J).range with hG₀
  have hle : ∀ J x, φ J x ∈ G₀ := fun J x => le_iSup (fun J => (φ J).range) J ⟨x, rfl⟩
  set φ' : ∀ J, (rootDatum 4 F).leviAmalgam J →* G₀ := fun J => (φ J).codRestrict G₀ (hle J)
    with hφ'
  have hcomp' : IsCompatible (rootDatum 4 F).leviAmalgam φ' := fun I J hIJ x y hxy =>
    Subtype.ext (hcomp I J hIJ x y hxy)
  have hgen' : ⨆ J, (φ' J).range = ⊤ := by
    apply Subgroup.map_injective G₀.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    refine (iSup_congr fun J => ?_).trans hG₀.symm
    rw [← MonoidHom.range_comp]
    rfl
  have hφJ : ∀ (j : Fin 4) (y : StatedSp 4 F) (hy : y ∈ simpleRootSL2 F j),
      φ ⟨{j}, hJ1 j⟩ ⟨y, (leviAmalgam_eq_iSup ⟨{j}, hJ1 j⟩).ge
        (mem_iSup_of_mem j (mem_iSup_of_mem (Finset.mem_singleton_self j) hy))⟩ =
      (P (kJ ⟨{j}, hJ1 j⟩ (hJ1ne j))).Φ ⟨y, simpleRootSL2_le_spBlock_compl' (hkpS j) hy⟩ :=
    fun j y hy => hφne _ (hJ1ne j) _
  have hnt : ∃ J, ∃ x, φ' J x ≠ 1 := by
    have hF4 : 4 ≤ Nat.card F := hK.trans (Nat.card_le_card_of_injective ι ι.injective)
    have hq := isQuasisimple_simpleRootSL2' hF4 (0 : Fin 4)
    have : Nontrivial (simpleRootSL2 F (0 : Fin 4) ⧸ center (simpleRootSL2 F (0 : Fin 4))) :=
      hq.2.1.toNontrivial
    have : Nontrivial (simpleRootSL2 F (0 : Fin 4)) :=
      (QuotientGroup.mk'_surjective (center (simpleRootSL2 F (0 : Fin 4)))).nontrivial
    obtain ⟨y, hy⟩ := exists_ne (1 : simpleRootSL2 F (0 : Fin 4))
    refine ⟨(⟨{0}, hJ1 0⟩ : {J : Finset (Fin 4) // J.card ≤ 2}), ⟨y, (leviAmalgam_eq_iSup ⟨{0}, hJ1 0⟩).ge
      (mem_iSup_of_mem 0 (mem_iSup_of_mem (Finset.mem_singleton_self 0) y.2))⟩, fun h => hy ?_⟩
    have h1 := congrArg Subtype.val h
    have h2 : (P (kJ ⟨{0}, hJ1 0⟩ (hJ1ne 0))).Φ ⟨y, simpleRootSL2_le_spBlock_compl' (hkpS 0) y.2⟩ =
        (P (kJ ⟨{0}, hJ1 0⟩ (hJ1ne 0))).Φ 1 :=
      ((hφJ 0 y y.2).symm.trans h1).trans (map_one _).symm
    exact Subtype.ext (congrArg Subtype.val ((P _).injective h2) :)
  obtain ⟨g, hg1, hFc⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := F)
  have hadm : StatedLieAdmissible .PSp 4 2 g :=
    ⟨Nat.prime_two, hg1, by omega, fun h => by
      have := congrArg Prod.fst h
      simp only at this
      omega⟩
  obtain ⟨-, -, hrec, -⟩ :=
    CFSG.LieType.CurtisTits.curtisTitsConclusion_symplectic.{0} (F := F) hadm hFc
      (by omega : 3 ≤ 4)
  obtain ⟨ψ₀, hψ₀, -, hker, -⟩ := hrec G₀ φ' hcomp' hgen' hnt
  have hinj₀ : Function.Injective ψ₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (center_statedSp_eq_bot 4).le
  set ψ : StatedSp 4 F →* G := G₀.subtype.comp ψ₀ with hψdef
  have hψφ : ∀ J (x : (rootDatum 4 F).leviAmalgam J), ψ x = φ J x :=
    fun J x => congrArg Subtype.val (hψ₀ J x)
  have hψJ : ∀ (j : Fin 4) (y : StatedSp 4 F) (hy : y ∈ simpleRootSL2 F j),
      ψ y = (P (kJ ⟨{j}, hJ1 j⟩ (hJ1ne j))).Φ ⟨y, simpleRootSL2_le_spBlock_compl' (hkpS j) hy⟩ :=
    fun j y hy => (hψφ ⟨{j}, hJ1 j⟩ _).trans (hφJ j y hy)
  refine ⟨ψ, G₀.subtype_injective.comp hinj₀, ?_, ?_, ?_⟩
  ·
    rw [MonoidHom.range_eq_map, ← iSup_simpleRootSL2_eq_top (show 1 ≤ 4 by omega),
      Subgroup.map_iSup, spGlobal]
    refine iSup_congr fun j => ?_
    rw [(P (kJ ⟨{j}, hJ1 j⟩ (hJ1ne j))).pieceCore_singleton_eq_map hK (hkpS j).1 (hkpS j).2]
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, simpleRootSL2_le_spBlock_compl' (hkpS j) hy⟩, mem_subgroupOf.2 hy,
        (hψJ j y hy).symm⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, mem_subgroupOf.1 hy, hψJ j y (mem_subgroupOf.1 hy)⟩
  ·
    intro x
    have htop : (⊤ : Subgroup (StatedSp 4 K)) ≤
        MonoidHom.eqLocus (ψ.comp (spFieldMap 4 ι)) (L.subtype.comp e.symm.toMonoidHom) := by
      rw [← iSup_simpleRootSL2_eq_top (show 1 ≤ 4 by omega), iSup_le_iff]
      intro j y hy
      have hyF : spFieldMap 4 ι y ∈ simpleRootSL2 F j := by
        rw [spFieldMap_eq_statedSpMap]
        exact map_statedSpMap_simpleRootSL2_le ι j ⟨y, hy, rfl⟩
      change ψ (spFieldMap 4 ι y) = ((e.symm y : L) : G)
      rw [hψJ j _ hyF]
      exact (P _).N1 y (simpleRootSL2_le_spBlock_compl' (hkpS j) hy)
    exact htop (mem_top x)
  ·
    intro x
    have htop : (⊤ : Subgroup (StatedSp 4 F)) ≤
        MonoidHom.eqLocus ((MulAut.conj t).toMonoidHom.comp ψ)
          (ψ.comp (fieldSp 4 F σ).toMonoidHom) := by
      rw [← iSup_simpleRootSL2_eq_top (show 1 ≤ 4 by omega), iSup_le_iff]
      intro j y hy
      have hyσ : fieldSp 4 F σ y ∈ simpleRootSL2 F j := fieldSp_mem_simpleRootSL2 σ hy
      change t * ψ y * t⁻¹ = ψ (fieldSp 4 F σ y)
      rw [hψJ j y hy, hψJ j _ hyσ, (P _).N3]
      congr 1
    exact htop (mem_top x)

theorem exists_injective_fieldRow_four (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 4 K) {t : G}
    {ι : K →+* F} {σ : F ≃+* F} (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (hparam : ∀ k : Fin 4, Nonempty (FieldNeighbourParam e t ι σ k))
    (hcomm : ∀ a ∈ pieceCore e ({0} : Finset (Fin 4)),
      ∀ b ∈ pieceCore e ({2} : Finset (Fin 4)), Commute a b) :
    ∃ ψ : StatedSp 4 F →* G, Function.Injective ψ ∧ ψ.range = spGlobal e ∧
      (∀ x : StatedSp 4 K, ψ (spFieldMap 4 ι x) = ((e.symm x : L) : G)) ∧
      ∀ x : StatedSp 4 F, t * ψ x * t⁻¹ = ψ (fieldSp 4 F σ x) := by
  obtain ⟨Q, hQ⟩ := exists_fieldParamAgree hK le_rfl hσ hfix fun k => (hparam k).some
  exact exists_injective_fieldRow_four_of_agree hK e Q hQ hcomm

end Main4

end CFSG.SeitzReduction.SymplecticPilot

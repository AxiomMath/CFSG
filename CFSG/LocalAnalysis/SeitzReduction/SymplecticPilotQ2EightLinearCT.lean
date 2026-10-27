module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTFourCT

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open scoped MatrixGroups

section Recognition

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {ε : ℕ}
  {hK : Nat.card K = 2} {e : L ≃* StatedSp 4 K}

theorem exists_injective_nsLinRow_four_of_agree [CharP K 2] (hε : ε ≤ 1)
    (P : ∀ k : Fin 4, NsLinParam hK ε e k) (hagree : NsLinParamAgree P)
    (hcomm : ∀ x ∈ blockSpecialLinear ({ctF 4 ε 0, ctE 4 ε 1} : Finset (Fin (2 * 4 + ε))),
      ∀ y ∈ blockSpecialLinear ({ctF 4 ε 2, ctE 4 ε 3} : Finset (Fin (2 * 4 + ε))),
      ∀ (hx : x ∈ q2Block ε K {2}) (hy : y ∈ q2Block ε K {0}),
        Commute ((P 2).Φ ⟨x, hx⟩) ((P 0).Φ ⟨y, hy⟩)) :
    ∃ ψ : SpecialLinearGroup (Fin (2 * 4 + ε)) K →* G, Function.Injective ψ ∧
      ψ.range = nsGlobal e ∧ LieModel (nsGlobal e) .PSL (2 * 4 + ε) 2 1 := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; omega)
  obtain ⟨m, hm⟩ : ∃ m, m + 1 = 2 * 4 + ε := ⟨2 * 4 + ε - 1, by omega⟩
  have hm7 : 7 ≤ m := by omega
  set j₁ : Fin m := ⟨1, by omega⟩ with hj₁
  set j₅ : Fin m := ⟨5, by omega⟩ with hj₅
  have hj15 : j₁ ≠ j₅ := fun h => by simp [hj₁, hj₅, Fin.ext_iff] at h
  set J₀ : Finset (Fin m) := {j₁, j₅} with hJ₀def
  have hJ₀card : J₀.card = 2 := by rw [hJ₀def, Finset.card_pair hj15]
  have hgood : ∀ J : {J : Finset (Fin m) // J.card ≤ 2}, J.1 ≠ J₀ →
      ∀ a ∈ J.1, ∀ b ∈ J.1, ¬(a.val = 1 ∧ b.val = 5) := by
    intro J hJ a ha b hb ⟨h1, h5⟩
    apply hJ
    have ha' : a = j₁ := Fin.ext h1
    have hb' : b = j₅ := Fin.ext h5
    rw [ha'] at ha
    rw [hb'] at hb
    symm
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact ha
      · rw [Finset.mem_singleton.1 hx]
        exact hb
    · rw [Finset.card_pair hj15]
      exact J.2
  choose kJ hkJ using fun (J : {J : Finset (Fin m) // J.card ≤ 2}) (h : J.1 ≠ J₀) =>
    exists_plane_notMem_four hm hε J.1 J.2 (hgood J h)
  have hKle : ∀ (J : {J : Finset (Fin m) // J.card ≤ 2}) (h : J.1 ≠ J₀)
      (x : SpecialLinearGroup (Fin (m + 1)) K),
      x ∈ (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam J →
        q2CastSL hm x ∈ q2Block ε K {kJ J h} := by
    intro J h x hxJ
    have hx : x ∈ CFSG.LieType.Universal.SpecialLinear.levi m K J.1 := by
      rw [← CFSG.LieType.Universal.SpecialLinear.levi_rootGroup]
      exact hxJ
    exact map_levi_le_q2Block hm (hkJ J h) ⟨x, hx, rfl⟩
  have hmono : ∀ {I I' : Finset (Fin m)}, I ⊆ I' →
      CFSG.LieType.CurtisTits.levi (CFSG.LieType.Universal.SpecialLinear.rootGroup m K) I ≤
        CFSG.LieType.CurtisTits.levi (CFSG.LieType.Universal.SpecialLinear.rootGroup m K) I' :=
    fun h => biSup_mono fun j hj => h hj
  have hJ1card : ({j₁} : Finset (Fin m)).card ≤ 2 := by simp
  have hJ5card : ({j₅} : Finset (Fin m)).card ≤ 2 := by simp
  set J₁ : {J : Finset (Fin m) // J.card ≤ 2} := ⟨{j₁}, hJ1card⟩ with hJ₁
  set J₅ : {J : Finset (Fin m) // J.card ≤ 2} := ⟨{j₅}, hJ5card⟩ with hJ₅
  have hJ₁ne : J₁.1 ≠ J₀ := fun h => by
    have := congrArg Finset.card h
    rw [Finset.card_singleton, hJ₀def, Finset.card_pair hj15] at this
    omega
  have hJ₅ne : J₅.1 ≠ J₀ := fun h => by
    have := congrArg Finset.card h
    rw [Finset.card_singleton, hJ₀def, Finset.card_pair hj15] at this
    omega
  set A := (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam J₁ with hA
  set B := (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam J₅ with hB
  have hI₁ : ({finCongr hm j₁.castSucc, finCongr hm j₁.succ} : Finset (Fin (2 * 4 + ε))) =
      {ctF 4 ε 0, ctE 4 ε 1} := by
    rw [show finCongr hm j₁.castSucc = ctF 4 ε 0 from Fin.ext (by simp [hj₁]),
      show finCongr hm j₁.succ = ctE 4 ε 1 from Fin.ext (by simp [hj₁])]
  have hI₅ : ({finCongr hm j₅.castSucc, finCongr hm j₅.succ} : Finset (Fin (2 * 4 + ε))) =
      {ctF 4 ε 2, ctE 4 ε 3} := by
    rw [show finCongr hm j₅.castSucc = ctF 4 ε 2 from Fin.ext (by simp [hj₅]),
      show finCongr hm j₅.succ = ctE 4 ε 3 from Fin.ext (by simp [hj₅])]
  have hAblk : ∀ a ∈ A, q2CastSL hm a ∈
      blockSpecialLinear ({ctF 4 ε 0, ctE 4 ε 1} : Finset (Fin (2 * 4 + ε))) := by
    intro a ha
    have ha' : a ∈ CFSG.LieType.Universal.SpecialLinear.levi m K {j₁} := by
      rw [← CFSG.LieType.Universal.SpecialLinear.levi_rootGroup]
      exact ha
    rw [← hI₁]
    exact map_levi_singleton_le hm j₁ ⟨a, ha', rfl⟩
  have hBblk : ∀ b ∈ B, q2CastSL hm b ∈
      blockSpecialLinear ({ctF 4 ε 2, ctE 4 ε 3} : Finset (Fin (2 * 4 + ε))) := by
    intro b hb
    have hb' : b ∈ CFSG.LieType.Universal.SpecialLinear.levi m K {j₅} := by
      rw [← CFSG.LieType.Universal.SpecialLinear.levi_rootGroup]
      exact hb
    rw [← hI₅]
    exact map_levi_singleton_le hm j₅ ⟨b, hb', rfl⟩
  have hdisjI : Disjoint ({ctF 4 ε 0, ctE 4 ε 1} : Finset (Fin (2 * 4 + ε)))
      {ctF 4 ε 2, ctE 4 ε 3} := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with h | h <;>
      · have := congrArg Fin.val h
        simp at this
  have hcommAB : ∀ a ∈ A, ∀ b ∈ B, Commute a b := by
    intro a ha b hb
    have h1 := LinearPilot.commute_blockSpecialLinear_of_disjoint hdisjI (hAblk a ha) (hBblk b hb)
    have h2 : q2CastSL hm (a * b) = q2CastSL hm (b * a) := by
      rw [map_mul, map_mul]
      exact h1.eq
    exact (q2CastSL hm).injective h2
  have hdisjAB : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxA, hxB⟩
    have h1 := blockSpecialLinear_inf_le _ _ ⟨hAblk x hxA, hBblk x hxB⟩
    rw [Finset.disjoint_iff_inter_eq_empty.1 hdisjI, LinearPilot.blockSpecialLinear_empty] at h1
    rw [Subgroup.mem_bot]
    exact (q2CastSL hm).injective (by rw [map_one]; exact Subgroup.mem_bot.1 h1)
  have hlevi₀ : ∀ J : {J : Finset (Fin m) // J.card ≤ 2}, J.1 = J₀ →
      (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam J = A ⊔ B := by
    intro J hJ
    change CFSG.LieType.CurtisTits.levi _ J.1 = _
    rw [hJ, hJ₀def]
    exact F4Pilot.levi_pair (CFSG.LieType.Universal.SpecialLinear.rootGroup m K) j₁ j₅
  have hsub2 : ({ctF 4 ε 0, ctE 4 ε 1} : Finset (Fin (2 * 4 + ε))) ⊆
      (planeCoordsQ2 ε ({2} : Finset (Fin 4)))ᶜ := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rw [Finset.mem_compl]
    rcases ha with rfl | rfl
    · exact q2Coord_inl_notMem (by decide) _ rfl
    · exact q2Coord_inl_notMem (by decide) _ rfl
  have hsub0 : ({ctF 4 ε 2, ctE 4 ε 3} : Finset (Fin (2 * 4 + ε))) ⊆
      (planeCoordsQ2 ε ({0} : Finset (Fin 4)))ᶜ := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rw [Finset.mem_compl]
    rcases ha with rfl | rfl
    · exact q2Coord_inl_notMem (by decide) _ rfl
    · exact q2Coord_inl_notMem (by decide) _ rfl
  set fA : A →* G := (P (kJ J₁ hJ₁ne)).Φ.comp
    (((q2CastSL hm).toMonoidHom.comp A.subtype).codRestrict _ fun a => hKle J₁ hJ₁ne a a.2)
    with hfA
  set gB : B →* G := (P (kJ J₅ hJ₅ne)).Φ.comp
    (((q2CastSL hm).toMonoidHom.comp B.subtype).codRestrict _ fun b => hKle J₅ hJ₅ne b b.2)
    with hgB
  have hfA2 : ∀ a : A, fA a = (P 2).Φ ⟨q2CastSL hm a,
      LinearPilot.blockSpecialLinear_mono hsub2 (hAblk a a.2)⟩ :=
    fun a => hagree _ _ _ (hKle J₁ hJ₁ne a a.2) _
  have hgB0 : ∀ b : B, gB b = (P 0).Φ ⟨q2CastSL hm b,
      LinearPilot.blockSpecialLinear_mono hsub0 (hBblk b b.2)⟩ :=
    fun b => hagree _ _ _ (hKle J₅ hJ₅ne b b.2) _
  have hfg : ∀ a b, Commute (fA a) (gB b) := by
    intro a b
    rw [hfA2, hgB0]
    exact hcomm _ (hAblk a a.2) _ (hBblk b b.2) _ _
  set ρ : ↥(A ⊔ B) →* G := F4Pilot.supLift hcommAB hdisjAB fA gB hfg with hρ
  have hρA : ∀ a : A, ρ ⟨a, mem_sup_left a.2⟩ = fA a := F4Pilot.supLift_apply_left _ _ hfg
  have hρB : ∀ b : B, ρ ⟨b, mem_sup_right b.2⟩ = gB b := F4Pilot.supLift_apply_right _ _ hfg
  obtain ⟨φ, hφne, hφ0⟩ : ∃ φ : ∀ J : {J : Finset (Fin m) // J.card ≤ 2},
      (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam J →* G,
      (∀ (J : {J : Finset (Fin m) // J.card ≤ 2}) (h : J.1 ≠ J₀) x,
        φ J x = (P (kJ J h)).Φ ⟨q2CastSL hm x, hKle J h x x.2⟩) ∧
      ∀ (J : {J : Finset (Fin m) // J.card ≤ 2}) (h : J.1 = J₀) x,
        φ J x = ρ ⟨x, (hlevi₀ J h).le x.2⟩ := by
    refine ⟨fun J => if h : J.1 = J₀ then ρ.comp (Subgroup.inclusion (hlevi₀ J h).le)
      else (P (kJ J h)).Φ.comp (((q2CastSL hm).toMonoidHom.comp (Subgroup.subtype _)).codRestrict
        _ fun x => hKle J h x x.2), fun J h x => ?_, fun J h x => ?_⟩
    · simp only [dite_eq_right h]
      rfl
    · simp only [dite_eq_left h]
      rfl
  have hcomp : CFSG.LieType.CurtisTits.IsCompatible
      (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam φ := by
    intro I J hIJ x y hxy
    have hIJ' : I.1 ⊆ J.1 := hIJ
    by_cases hJ : J.1 = J₀
    · by_cases hI : I.1 = J₀
      · have hIJeq : I = J := Subtype.ext (hI.trans hJ.symm)
        subst hIJeq
        exact congrArg (φ I) (Subtype.ext hxy)
      · rw [hφne I hI, hφ0 J hJ]
        rcases subset_singleton_or_of_subset_pair (a := j₁) (b := j₅)
          (show I.1 ⊆ J₀ from hJ ▸ hIJ') hI with h1 | h5
        · have hyA : (y : SpecialLinearGroup (Fin (m + 1)) K) ∈ A :=
            hxy ▸ hmono h1 x.2
          have h2 := hρA ⟨y, hyA⟩
          refine Eq.trans ?_ h2.symm
          change _ = (P (kJ J₁ hJ₁ne)).Φ ⟨q2CastSL hm y, hKle J₁ hJ₁ne y hyA⟩
          rw [hagree (kJ I hI) (kJ J₁ hJ₁ne) _ (hKle I hI x x.2)
            (hxy ▸ hKle J₁ hJ₁ne y hyA)]
          congr 2
          rw [hxy]
        · have hyB : (y : SpecialLinearGroup (Fin (m + 1)) K) ∈ B :=
            hxy ▸ hmono h5 x.2
          have h2 := hρB ⟨y, hyB⟩
          refine Eq.trans ?_ h2.symm
          change _ = (P (kJ J₅ hJ₅ne)).Φ ⟨q2CastSL hm y, hKle J₅ hJ₅ne y hyB⟩
          rw [hagree (kJ I hI) (kJ J₅ hJ₅ne) _ (hKle I hI x x.2)
            (hxy ▸ hKle J₅ hJ₅ne y hyB)]
          congr 2
          rw [hxy]
    · have hI : I.1 ≠ J₀ := fun hI => hJ (Finset.eq_of_subset_of_card_le (hI ▸ hIJ')
        (J.2.trans hJ₀card.ge)).symm
      rw [hφne I hI, hφne J hJ]
      have hx' : q2CastSL hm (x : SpecialLinearGroup (Fin (m + 1)) K) ∈ q2Block ε K {kJ J hJ} :=
        hxy ▸ hKle J hJ y y.2
      rw [hagree (kJ I hI) (kJ J hJ) _ (hKle I hI x x.2) hx']
      congr 2
      rw [hxy]
  set G₀ : Subgroup G := ⨆ J, (φ J).range with hG₀
  have hle : ∀ J x, φ J x ∈ G₀ := fun J x => le_iSup (fun J => (φ J).range) J ⟨x, rfl⟩
  set φ' : ∀ J, (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam J →* G₀ :=
    fun J => (φ J).codRestrict G₀ (hle J) with hφ'
  have hcomp' : CFSG.LieType.CurtisTits.IsCompatible
      (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam φ' :=
    fun I J hIJ x y hxy => Subtype.ext (hcomp I J hIJ x y hxy)
  have hgen' : ⨆ J, (φ' J).range = ⊤ := by
    apply Subgroup.map_injective G₀.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    refine (iSup_congr fun J => ?_).trans hG₀.symm
    rw [← MonoidHom.range_comp]
    rfl
  have hnt : ∃ J, ∃ x, φ' J x ≠ 1 := by
    set j₀ : Fin m := ⟨0, by omega⟩ with hj₀
    set J₀' : {J : Finset (Fin m) // J.card ≤ 2} := ⟨{j₀}, by simp⟩ with hJ₀'
    have hJ₀'ne : J₀'.1 ≠ J₀ := fun h => by
      have := congrArg Finset.card h
      rw [Finset.card_singleton, hJ₀card] at this
      omega
    have hne : j₀.castSucc ≠ j₀.succ := (show j₀.castSucc < j₀.succ from Fin.castSucc_lt_succ).ne
    have hx₀ : SpecialLinearGroup.transvection hne (1 : K) ∈
        (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam J₀' := by
      have h1 : SpecialLinearGroup.transvection hne (1 : K) ∈
          CFSG.LieType.CurtisTits.levi (CFSG.LieType.Universal.SpecialLinear.rootGroup m K)
            ({j₀} : Finset (Fin m)) := by
        rw [CFSG.LieType.Universal.SpecialLinear.levi_rootGroup]
        have hlevi : CFSG.LieType.Universal.SpecialLinear.fundamentalRootSubgroup m K j₀ true ≤
            CFSG.LieType.Universal.SpecialLinear.levi m K {j₀} :=
          le_iSup_of_le j₀ (le_iSup_of_le (Finset.mem_singleton_self j₀)
            (le_iSup (fun s => CFSG.LieType.Universal.SpecialLinear.fundamentalRootSubgroup m K j₀
              s) true))
        exact hlevi (CFSG.LieType.Universal.SpecialLinear.transvection_mem_rootSubgroup _ 1)
      exact h1
    refine ⟨J₀', ⟨_, hx₀⟩, fun h => ?_⟩
    have h1 : φ J₀' ⟨_, hx₀⟩ = φ J₀' 1 := by
      rw [map_one]
      exact congrArg Subtype.val h
    rw [hφne J₀' hJ₀'ne, hφne J₀' hJ₀'ne] at h1
    have h2 := congrArg Subtype.val ((P (kJ J₀' hJ₀'ne)).injective h1)
    have h3 := (q2CastSL hm).injective h2
    have h4 := congrArg (fun z : SpecialLinearGroup (Fin (m + 1)) K =>
      (z : Matrix (Fin (m + 1)) (Fin (m + 1)) K) j₀.castSucc j₀.succ) h3
    simp [SpecialLinearGroup.transvection_coe, Matrix.one_apply_ne hne] at h4
  have hadm : StatedLieAdmissible .PSL (m + 1) 2 1 :=
    ⟨Nat.prime_two, le_rfl, by omega, fun h => by simp at h; omega, fun h => by simp at h⟩
  obtain ⟨-, -, hrec, -⟩ :=
    CFSG.LieType.CurtisTits.curtisTitsConclusion_specialLinear.{0} (F := K) hadm
      (by rw [hK, pow_one]) (by omega : 3 ≤ m)
  obtain ⟨ψ₀, hψ₀, hsurj, hker, -, hZ, -, hLM⟩ := hrec G₀ φ' hcomp' hgen' hnt
  have hinj₀ : Function.Injective ψ₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro z hz
    exact LinearPilot.eq_one_of_mem_center_specialLinearGroup_of_card_two hK (hker hz)
  have hZbot : Subgroup.center G₀ = ⊥ := by
    rw [hZ, eq_bot_iff]
    rintro _ ⟨z, hz, rfl⟩
    rw [LinearPilot.eq_one_of_mem_center_specialLinearGroup_of_card_two hK hz, map_one]
    exact one_mem _
  set ψ : SpecialLinearGroup (Fin (2 * 4 + ε)) K →* G :=
    (G₀.subtype.comp ψ₀).comp (q2CastSL hm).symm.toMonoidHom with hψdef
  have hψinj : Function.Injective ψ :=
    (G₀.subtype_injective.comp hinj₀).comp (q2CastSL hm).symm.injective
  have hψrange : ψ.range = G₀ := by
    rw [hψdef, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulEquiv.surjective _),
      ← MonoidHom.range_eq_map, MonoidHom.range_comp, MonoidHom.range_eq_top.2 hsurj,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hψφ : ∀ J (x : (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam J),
      ψ (q2CastSL hm x) = φ J x := by
    intro J x
    change ((ψ₀ ((q2CastSL hm).symm (q2CastSL hm x)) : G₀) : G) = _
    rw [MulEquiv.symm_apply_apply]
    exact congrArg Subtype.val (hψ₀ J x)
  have hΦle : ∀ k : Fin 4, (P k).Φ.range ≤ nsGlobal e := fun k => by
    rw [(P k).range_eq, nsGlobal_def]
    exact le_iSup (fun i : Fin 4 => centralizerPerfectCore (modelToG e (nsTorusSp K i))) k
  have hG₀le : G₀ ≤ nsGlobal e := by
    refine iSup_le fun J => ?_
    by_cases hJ : J.1 = J₀
    · rintro _ ⟨x, rfl⟩
      rw [hφ0 J hJ]
      have h1 : ρ ⟨x, (hlevi₀ J hJ).le x.2⟩ ∈ ρ.range := ⟨_, rfl⟩
      rw [hρ, F4Pilot.range_supLift] at h1
      have hle2 : fA.range ⊔ gB.range ≤ nsGlobal e := by
        refine sup_le ?_ ?_
        · rintro _ ⟨a, rfl⟩
          exact hΦle _ ⟨_, rfl⟩
        · rintro _ ⟨b, rfl⟩
          exact hΦle _ ⟨_, rfl⟩
      exact hle2 h1
    · rintro _ ⟨x, rfl⟩
      rw [hφne J hJ]
      exact hΦle _ ⟨_, rfl⟩
  have hpiece : ∀ k : Fin 4, centralizerPerfectCore (modelToG e (nsTorusSp K k)) ≤ G₀ := by
    intro k
    obtain ⟨j, hj⟩ : ∃ j : Fin m, j.val = 2 * k.val := ⟨⟨2 * k.val, by have := k.2; omega⟩, rfl⟩
    have hJ1 : ({j} : Finset (Fin m)).card ≤ 2 := by simp
    set J : {J : Finset (Fin m) // J.card ≤ 2} := ⟨{j}, hJ1⟩ with hJ
    have hJne : J.1 ≠ J₀ := fun h => by
      have := congrArg Finset.card h
      rw [Finset.card_singleton, hJ₀card] at this
      omega
    have hc : q2Embed ε hK (nsElt k) ∈ (CFSG.LieType.Universal.SpecialLinear.levi m K {j}).map
        (q2CastSL hm).toMonoidHom := by
      refine blockSpecialLinear_plane_le_map_levi hm k j hj ?_
      rw [show nsElt (K := K) k = longBlock K 4 k zThreeSL from rfl, q2Embed_longBlock hK,
        ← LinearPilot.range_pairEmbed (q2PlaneNe k)]
      exact ⟨_, rfl⟩
    obtain ⟨x₀, hx₀, hx₀c⟩ := hc
    have hx₀' : x₀ ∈ (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam J := by
      have h1 : x₀ ∈ CFSG.LieType.CurtisTits.levi
          (CFSG.LieType.Universal.SpecialLinear.rootGroup m K) ({j} : Finset (Fin m)) := by
        rw [CFSG.LieType.Universal.SpecialLinear.levi_rootGroup]
        exact hx₀
      exact h1
    have hkk : kJ J hJne ≠ k := by
      intro hkk
      have h1 := (hkJ J hJne j (Finset.mem_singleton_self j)).1
      rw [hkk] at h1
      apply h1
      rw [mem_planeCoordsQ2_iff]
      refine ⟨by have := k.2; simp only [finCongr_apply, Fin.val_cast, Fin.val_castSucc]; omega,
        ?_⟩
      rw [Finset.mem_singleton]
      exact Fin.ext (by simp only [finCongr_apply, Fin.val_cast, Fin.val_castSucc]; omega)
    have hnk : nsElt (K := K) k ∈ spBlock K ({kJ J hJne} : Finset (Fin 4))ᶜ := by
      have := nsElt_mem_spBlock_compl (K := K) hkk
      simpa using this
    have hψc : ψ (q2Embed ε hK (nsElt k)) = ((e.symm (nsElt k) : L) : G) := by
      have h1 := hψφ J ⟨x₀, hx₀'⟩
      change ψ (q2CastSL hm x₀) = _ at h1
      rw [MulEquiv.coe_toMonoidHom] at hx₀c
      rw [← hx₀c, h1, hφne J hJne]
      have h2 := (P (kJ J hJne)).N1 _ hnk
      rw [← h2]
      congr 2
    have hblock : (q2Block ε K {k}).map ψ ≤
        centralizerPerfectCore (modelToG e (nsTorusSp K k)) := by
      refine CFSG.Quasithin.le_perfectCore_of_perfect ?_ ?_
      · rw [nsTorusSp, centralizer_modelToG_zpowers]
        rintro _ ⟨z, hz, rfl⟩
        rw [mem_centralizer_singleton_iff, ← hψc, ← map_mul, ← map_mul]
        congr 1
        have hcb : q2Embed ε hK (nsElt k) ∈ blockSpecialLinear (planeCoordsQ2 ε {k}) := by
          rw [planeCoordsQ2_singleton, show nsElt (K := K) k = longBlock K 4 k zThreeSL from rfl,
            q2Embed_longBlock hK, ← LinearPilot.range_pairEmbed (q2PlaneNe k)]
          exact ⟨_, rfl⟩
        exact (LinearPilot.commute_blockSpecialLinear_of_disjoint disjoint_compl_right hcb
          hz).eq.symm
      · have hcard : 3 ≤ ((planeCoordsQ2 ε ({k} : Finset (Fin 4)))ᶜ).card := by
          rw [Finset.card_compl, card_planeCoordsQ2, Finset.card_singleton, Fintype.card_fin]
          omega
        rw [← map_commutator, commutator_q2Block_eq hcard]
    have hcardE : Nat.card ((q2Block ε K {k}).map ψ) ≥
        Nat.card (centralizerPerfectCore (modelToG e (nsTorusSp K k))) := by
      rw [Subgroup.card_map_of_injective hψinj, ← (P k).range_eq,
        ← Nat.card_congr (MonoidHom.ofInjective (P k).injective).toEquiv]
    have heq := Subgroup.eq_of_le_of_card_ge hblock hcardE
    rw [← heq, ← hψrange]
    rintro _ ⟨z, -, rfl⟩
    exact ⟨z, rfl⟩
  have hG₀eq : G₀ = nsGlobal e := le_antisymm hG₀le (by
    rw [nsGlobal_def]
    exact iSup_le hpiece)
  refine ⟨ψ, hψinj, hψrange.trans hG₀eq, ?_⟩
  have e1 : G₀ ⧸ Subgroup.center G₀ ≃* nsGlobal e :=
    ((QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot).trans
      (MulEquiv.subgroupCongr hG₀eq)
  rw [← hm]
  exact LieType.CurtisTits.lieModel_of_mulEquiv e1 hLM

end Recognition

end CFSG.SeitzReduction.SymplecticPilot

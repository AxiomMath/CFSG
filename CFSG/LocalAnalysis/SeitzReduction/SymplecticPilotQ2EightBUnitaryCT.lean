module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2UnitaryCTMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUAlignFourCT

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.LieType.CurtisTits (rankOne levi)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Recognition

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]
  [CharP K 2] {ε : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {hε : ε ≤ 1}
  {ι : K →+* F} {hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c} {e : L ≃* StatedSp 4 K}

@[expose] def NsUniProductCommute (hF : Nat.card F = (2 ^ 1) ^ 2)
    (P : ∀ k : Fin 4, NsUniParam ε hε (unitaryInvolution F 2 1) ι hι e k) : Prop :=
  ∀ (x : SU (unitaryInvolution F 2 1) (2 * 4 + ε))
    (_ : x ∈ rankOne (rootGroup (unitaryInvolution F 2 1) (unitaryInvolution_involutive hF)
      (2 * 4 + ε)) ⟨0, by omega⟩)
    (hx2 : x ∈ ctuBlock (unitaryInvolution F 2 1) ε ({2} : Finset (Fin 4)))
    (y : SU (unitaryInvolution F 2 1) (2 * 4 + ε))
    (_ : y ∈ rankOne (rootGroup (unitaryInvolution F 2 1) (unitaryInvolution_involutive hF)
      (2 * 4 + ε)) ⟨2, by omega⟩)
    (hy0 : y ∈ ctuBlock (unitaryInvolution F 2 1) ε ({0} : Finset (Fin 4))),
    Commute ((P 2).Φ ⟨x, hx2⟩) ((P 0).Φ ⟨y, hy0⟩)

set_option maxHeartbeats 400000 in
theorem exists_ct_nsUniRow_four_of_agree (hF : Nat.card F = (2 ^ 1) ^ 2)
    (P : ∀ k : Fin 4, NsUniParam ε hε (unitaryInvolution F 2 1) ι hι e k)
    (hagree : NsUniParamAgree P) (hcomm : NsUniProductCommute hF P) :
    ∃ ψ : SU (unitaryInvolution F 2 1) (2 * 4 + ε) →* G, ψ.range = nsGlobal e ∧
      ψ.ker ≤ center (SU (unitaryInvolution F 2 1) (2 * 4 + ε)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn3 : 3 ≤ 2 * 4 + ε := by omega
  have hnq : (2 * 4 + ε, 2 ^ 1) ≠ (3, 2) := fun h => by
    have := (Prod.mk.inj h).1
    omega
  set σ := unitaryInvolution F 2 1 with hσdef
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hF
  set D := rootDatum hF (2 * 4 + ε) with hD
  have hrank : D.rank = (2 * 4 + ε) / 2 := rfl
  have h0 : 0 + 1 < (2 * 4 + ε) / 2 := by omega
  have h2 : 2 + 1 < (2 * 4 + ε) / 2 := by omega
  set j₀ : Fin D.rank := ⟨0, by omega⟩ with hj₀
  set j₂ : Fin D.rank := ⟨2, by omega⟩ with hj₂
  have hj02 : j₀ ≠ j₂ := fun h => by simp [hj₀, hj₂, Fin.ext_iff] at h
  set J₀ : Finset (Fin D.rank) := {j₀, j₂} with hJ₀def
  have hgood : ∀ J : {J : Finset (Fin D.rank) // J.card ≤ 2}, J.1 ≠ J₀ →
      ∀ a ∈ J.1, ∀ b ∈ J.1, ¬(a.val = 0 ∧ b.val = 2) := by
    intro J hJ a ha b hb ⟨ha0, hb2⟩
    apply hJ
    have ha' : a = j₀ := Fin.ext ha0
    have hb' : b = j₂ := Fin.ext hb2
    rw [ha'] at ha
    rw [hb'] at hb
    symm
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact ha
      · rw [Finset.mem_singleton.1 hx]
        exact hb
    · rw [hJ₀def, Finset.card_pair hj02]
      exact J.2
  choose kJ hkJ using fun (J : {J : Finset (Fin D.rank) // J.card ≤ 2}) (h : J.1 ≠ J₀) =>
    exists_plane_off_ctu_four (m := D.rank) (by omega) J.1 J.2 (hgood J h)
  have hKle : ∀ (J : {J : Finset (Fin D.rank) // J.card ≤ 2}) (h : J.1 ≠ J₀),
      D.leviAmalgam J ≤ ctuBlock σ ε ({kJ J h} : Finset (Fin 4)) :=
    fun J h => levi_le_ctuBlock hε (hkJ J h)
  set J₁ : {J : Finset (Fin D.rank) // J.card ≤ 2} := ⟨{j₀}, by simp⟩ with hJ₁
  set J₃ : {J : Finset (Fin D.rank) // J.card ≤ 2} := ⟨{j₂}, by simp⟩ with hJ₃
  have hJ₁ne : J₁.1 ≠ J₀ := fun h => by
    have := congrArg Finset.card h
    rw [Finset.card_singleton, hJ₀def, Finset.card_pair hj02] at this
    omega
  have hJ₃ne : J₃.1 ≠ J₀ := fun h => by
    have := congrArg Finset.card h
    rw [Finset.card_singleton, hJ₀def, Finset.card_pair hj02] at this
    omega
  set A := D.leviAmalgam J₁ with hA
  set B := D.leviAmalgam J₃ with hB
  have hArank : A ≤ rankOne D.rootGroup j₀ := iSup₂_le fun j hj => by
    rw [Finset.mem_singleton.1 hj]
  have hBrank : B ≤ rankOne D.rootGroup j₂ := iSup₂_le fun j hj => by
    rw [Finset.mem_singleton.1 hj]
  have hcommAB : ∀ a ∈ A, ∀ b ∈ B, Commute a b := fun a ha b hb =>
    commute_rankOne_zero_two (by omega) h0 h2 (hArank ha) (hBrank hb)
  have hdisjAB : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [← rankOne_zero_inf_two (σ := σ) (hσ := hσ) (by omega) h0 h2]
    exact ⟨hArank hx.1, hBrank hx.2⟩
  have hlevi₀ : ∀ J : {J : Finset (Fin D.rank) // J.card ≤ 2}, J.1 = J₀ →
      D.leviAmalgam J = A ⊔ B := by
    intro J hJ
    change levi _ J.1 = _
    rw [hJ, hJ₀def]
    exact F4Pilot.levi_pair D.rootGroup j₀ j₂
  have h20 : (2 : Fin 4).val ≠ j₀.val := by simp [hj₀]
  have h21 : (2 : Fin 4).val ≠ j₀.val + 1 := by simp [hj₀]
  have h02 : (0 : Fin 4).val ≠ j₂.val := by simp [hj₂]
  have h03 : (0 : Fin 4).val ≠ j₂.val + 1 := by simp [hj₂]
  set fA : A →* G := (P (kJ J₁ hJ₁ne)).Φ.comp (Subgroup.inclusion (hKle J₁ hJ₁ne)) with hfA
  set gB : B →* G := (P (kJ J₃ hJ₃ne)).Φ.comp (Subgroup.inclusion (hKle J₃ hJ₃ne)) with hgB
  have hfA2 : ∀ a : A, fA a = (P 2).Φ ⟨a, rankOne_le_ctuBlock hε j₀ h20 h21 (hArank a.2)⟩ :=
    fun a => hagree _ _ _ (hKle J₁ hJ₁ne a.2) _
  have hgB0 : ∀ b : B, gB b = (P 0).Φ ⟨b, rankOne_le_ctuBlock hε j₂ h02 h03 (hBrank b.2)⟩ :=
    fun b => hagree _ _ _ (hKle J₃ hJ₃ne b.2) _
  have hfg : ∀ a b, Commute (fA a) (gB b) := fun a b => by
    rw [hfA2, hgB0]
    exact hcomm a (hArank a.2) _ b (hBrank b.2) _
  set ρ : ↥(A ⊔ B) →* G := F4Pilot.supLift hcommAB hdisjAB fA gB hfg with hρ
  have hρA : ∀ a : A, ρ ⟨a, mem_sup_left a.2⟩ = fA a := F4Pilot.supLift_apply_left _ _ hfg
  have hρB : ∀ b : B, ρ ⟨b, mem_sup_right b.2⟩ = gB b := F4Pilot.supLift_apply_right _ _ hfg
  obtain ⟨φ, hφne, hφ0⟩ : ∃ φ : ∀ J : {J : Finset (Fin D.rank) // J.card ≤ 2},
      D.leviAmalgam J →* G,
      (∀ (J : {J : Finset (Fin D.rank) // J.card ≤ 2}) (h : J.1 ≠ J₀) x,
        φ J x = (P (kJ J h)).Φ ⟨x, hKle J h x.2⟩) ∧
      ∀ (J : {J : Finset (Fin D.rank) // J.card ≤ 2}) (h : J.1 = J₀) x,
        φ J x = ρ ⟨x, (hlevi₀ J h).le x.2⟩ := by
    refine ⟨fun J => if h : J.1 = J₀ then ρ.comp (Subgroup.inclusion (hlevi₀ J h).le)
      else (P (kJ J h)).Φ.comp (Subgroup.inclusion (hKle J h)), fun J h x => ?_, fun J h x => ?_⟩
    · simp only [h, ↓reduceDIte]
      rfl
    · simp only [h, ↓reduceDIte]
      rfl
  have hcomp : CFSG.LieType.CurtisTits.IsCompatible D.leviAmalgam φ := by
    intro I J hIJ x y hxy
    have hIJ' : I.1 ⊆ J.1 := hIJ
    by_cases hJ : J.1 = J₀
    · by_cases hI : I.1 = J₀
      · have hIJeq : I = J := Subtype.ext (hI.trans hJ.symm)
        subst hIJeq
        exact congrArg (φ I) (Subtype.ext hxy)
      · rw [hφne I hI, hφ0 J hJ]
        have hIJ₀ : I.1 ⊆ J₀ := by
          rw [← hJ]
          exact hIJ'
        rcases subset_singleton_or_of_subset_pair_ctua hIJ₀ hI with hI1 | hI2
        · have hyA : (y : SU σ (2 * 4 + ε)) ∈ A := by
            rw [← hxy]
            exact CFSG.LieType.CurtisTits.levi_mono _ hI1 x.2
          change _ = ρ ⟨((⟨y, hyA⟩ : A) : SU σ (2 * 4 + ε)), mem_sup_left hyA⟩
          rw [hρA, hfA]
          have hy' : (x : SU σ (2 * 4 + ε)) ∈ ctuBlock σ ε ({kJ J₁ hJ₁ne} : Finset (Fin 4)) := by
            rw [hxy]
            exact hKle J₁ hJ₁ne hyA
          rw [hagree (kJ I hI) (kJ J₁ hJ₁ne) _ (hKle I hI x.2) hy']
          exact congrArg _ (Subtype.ext hxy)
        · have hyB : (y : SU σ (2 * 4 + ε)) ∈ B := by
            rw [← hxy]
            exact CFSG.LieType.CurtisTits.levi_mono _ hI2 x.2
          change _ = ρ ⟨((⟨y, hyB⟩ : B) : SU σ (2 * 4 + ε)), mem_sup_right hyB⟩
          rw [hρB, hgB]
          have hy' : (x : SU σ (2 * 4 + ε)) ∈ ctuBlock σ ε ({kJ J₃ hJ₃ne} : Finset (Fin 4)) := by
            rw [hxy]
            exact hKle J₃ hJ₃ne hyB
          rw [hagree (kJ I hI) (kJ J₃ hJ₃ne) _ (hKle I hI x.2) hy']
          exact congrArg _ (Subtype.ext hxy)
    · have hI : I.1 ≠ J₀ := fun hI => by
        have hJ₀J : J₀ ⊆ J.1 := by
          rw [← hI]
          exact hIJ'
        exact hJ (Finset.eq_of_subset_of_card_le hJ₀J
          (by rw [hJ₀def, Finset.card_pair hj02]; exact J.2)).symm
      rw [hφne I hI, hφne J hJ]
      have hy' : (x : SU σ (2 * 4 + ε)) ∈ ctuBlock σ ε ({kJ J hJ} : Finset (Fin 4)) := by
        rw [hxy]
        exact hKle J hJ y.2
      rw [hagree (kJ I hI) (kJ J hJ) _ (hKle I hI x.2) hy']
      exact congrArg _ (Subtype.ext hxy)
  set G₀ : Subgroup G := ⨆ J, (φ J).range with hG₀
  have hle : ∀ J x, φ J x ∈ G₀ := fun J x => le_iSup (fun J => (φ J).range) J ⟨x, rfl⟩
  set φ' : ∀ J, D.leviAmalgam J →* G₀ := fun J => (φ J).codRestrict G₀ (hle J) with hφ'
  have hcomp' : CFSG.LieType.CurtisTits.IsCompatible D.leviAmalgam φ' :=
    fun I J hIJ x y hxy => Subtype.ext (hcomp I J hIJ x y hxy)
  have hgen' : ⨆ J, (φ' J).range = ⊤ := by
    apply Subgroup.map_injective G₀.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    refine (iSup_congr fun J => ?_).trans hG₀.symm
    rw [← MonoidHom.range_comp]
    rfl
  have hrank : ∀ (j : Fin D.rank) (y : StatedSp 4 K)
      (hy : ctuEmbed ε hε σ ι hι y ∈ rankOne D.rootGroup j),
      ∃ (J : {J : Finset (Fin D.rank) // J.card ≤ 2}) (hJ : ctuEmbed ε hε σ ι hι y ∈
        D.leviAmalgam J), φ J ⟨_, hJ⟩ = ((e.symm y : L) : G) := by
    intro j y hy
    set J : {J : Finset (Fin D.rank) // J.card ≤ 2} := ⟨{j}, by simp⟩ with hJ
    have hJne : J.1 ≠ J₀ := fun h => by
      have := congrArg Finset.card h
      rw [Finset.card_singleton, hJ₀def, Finset.card_pair hj02] at this
      omega
    have hxJ : ctuEmbed ε hε σ ι hι y ∈ D.leviAmalgam J :=
      CFSG.LieType.CurtisTits.rankOne_le_levi _ (Finset.mem_singleton_self j) hy
    refine ⟨J, hxJ, ?_⟩
    rw [hφne J hJne]
    exact (P (kJ J hJne)).N1' (ctuEmbed_mem_ctuBlock_iff.1 (hKle J hJne hxJ)) _ rfl
  have hjl : (4 - 1 : ℕ) < D.rank := by change 4 - 1 < (2 * 4 + ε) / 2; omega
  have hnt : ∃ J, ∃ x, φ' J x ≠ 1 := by
    have hlast : ¬((⟨4 - 1, hjl⟩ : Fin D.rank).val + 1 < (2 * 4 + ε) / 2) := by
      change ¬(4 - 1 + 1 < (2 * 4 + ε) / 2)
      omega
    obtain ⟨J, hJ, hφJ⟩ := hrank ⟨4 - 1, hjl⟩ _
      (ctuEmbed_nsElt_mem_rankOne (hε := hε) (ι := ι) (hι := hι) hσ hlast)
    refine ⟨J, ⟨_, hJ⟩, fun h => ?_⟩
    have h1 : φ J ⟨_, hJ⟩ = 1 := congrArg Subtype.val h
    rw [hφJ] at h1
    have h2 : e.symm (nsElt (K := K) ⟨(⟨4 - 1, hjl⟩ : Fin D.rank).val, by omega⟩) = 1 :=
      Subtype.ext h1
    rw [MulEquiv.map_eq_one_iff] at h2
    exact nsElt_ne_one _ h2
  have hadm : StatedLieAdmissible .PSU (2 * 4 + ε) 2 1 := ⟨Nat.prime_two, le_rfl, hn3, hnq⟩
  obtain ⟨-, -, hrec, -⟩ :=
    CFSG.LieType.CurtisTits.curtisTitsConclusion_unitary.{0} (F := F) (p := 2) (f := 1)
      (n := 2 * 4 + ε) hadm hF
  obtain ⟨ψ₀, hψ₀, hsurj, hker, -, -, -, -⟩ := hrec G₀ φ' hcomp' hgen' hnt
  set ψ : SU σ (2 * 4 + ε) →* G := G₀.subtype.comp ψ₀ with hψdef
  have hψrange : ψ.range = G₀ := by
    rw [hψdef, MonoidHom.range_comp, MonoidHom.range_eq_top.2 hsurj, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hψφ : ∀ J (x : D.leviAmalgam J), ψ x = φ J x := fun J x =>
    congrArg Subtype.val (hψ₀ J x)
  have hψker : ψ.ker ≤ center (SU σ (2 * 4 + ε)) := by
    intro z hz
    apply hker
    rw [MonoidHom.mem_ker] at hz ⊢
    exact G₀.subtype_injective (by rw [map_one]; exact hz)
  have hG₀le : G₀ ≤ nsGlobal e := by
    refine iSup_le fun J => ?_
    rintro _ ⟨x, rfl⟩
    rw [nsGlobal_def]
    by_cases hJ : J.1 = J₀
    · rw [hφ0 J hJ]
      have hρle : ρ.range ≤ ⨆ i : Fin 4, centralizerPerfectCore (modelToG e (nsTorusSp K i)) := by
        rw [hρ, F4Pilot.range_supLift]
        refine sup_le ?_ ?_
        · rintro _ ⟨a, rfl⟩
          have h1 : fA a ∈ (P 2).Φ.range := ⟨_, (hfA2 a).symm⟩
          rw [(P 2).range_eq] at h1
          exact le_iSup (fun i : Fin 4 => centralizerPerfectCore (modelToG e (nsTorusSp K i))) 2
            h1
        · rintro _ ⟨b, rfl⟩
          have h1 : gB b ∈ (P 0).Φ.range := ⟨_, (hgB0 b).symm⟩
          rw [(P 0).range_eq] at h1
          exact le_iSup (fun i : Fin 4 => centralizerPerfectCore (modelToG e (nsTorusSp K i))) 0
            h1
      exact hρle ⟨_, rfl⟩
    · rw [hφne J hJ]
      have h1 : (P (kJ J hJ)).Φ ⟨x, hKle J hJ x.2⟩ ∈ (P (kJ J hJ)).Φ.range := ⟨_, rfl⟩
      rw [(P (kJ J hJ)).range_eq] at h1
      exact le_iSup (fun i : Fin 4 => centralizerPerfectCore (modelToG e (nsTorusSp K i))) _ h1
  have hrankψ : ∀ (j : Fin D.rank) (y : StatedSp 4 K)
      (hy : ctuEmbed ε hε σ ι hι y ∈ rankOne D.rootGroup j),
      ψ (ctuEmbed ε hε σ ι hι y) = ((e.symm y : L) : G) := by
    intro j y hy
    obtain ⟨J, hJ, hφJ⟩ := hrank j y hy
    rw [← hφJ]
    exact hψφ J ⟨_, hJ⟩
  have hns : ∀ k : Fin 4, ψ (ctuEmbed ε hε σ ι hι (nsElt k)) = ((e.symm (nsElt k) : L) : G) := by
    refine eq_nsElt_of_eq_last_of_eq_swap (ψ.comp (ctuEmbed ε hε σ ι hι))
      (L.subtype.comp e.symm.toMonoidHom) (fun k hk => ?_) (fun j hj => ?_)
    · have hkr : k.val < D.rank := by change k.val < (2 * 4 + ε) / 2; omega
      have hlast : ¬((⟨k.val, hkr⟩ : Fin D.rank).val + 1 < (2 * 4 + ε) / 2) := by
        change ¬(k.val + 1 < (2 * 4 + ε) / 2)
        omega
      have hmem : ctuEmbed ε hε σ ι hι (nsElt k) ∈ rankOne D.rootGroup ⟨k.val, hkr⟩ :=
        ctuEmbed_nsElt_mem_rankOne (hε := hε) (ι := ι) (hι := hι) hσ hlast
      exact hrankψ _ _ hmem
    · have hjr : j.val < D.rank := by change j.val < (2 * 4 + ε) / 2; omega
      have hjs : (⟨j.val, hjr⟩ : Fin D.rank).val + 1 < (2 * 4 + ε) / 2 := by
        change j.val + 1 < (2 * 4 + ε) / 2
        omega
      have hmem : ctuEmbed ε hε σ ι hι (permSp K (Equiv.swap j ⟨j.val + 1, hj⟩)) ∈
          rankOne D.rootGroup ⟨j.val, hjr⟩ :=
        ctuEmbed_permSp_swap_mem_rankOne (hε := hε) (ι := ι) (hι := hι) hσ hjs
      exact hrankψ _ _ hmem
  have hEk : ∀ k : Fin 4, centralizerPerfectCore (modelToG e (nsTorusSp K k)) ≤ G₀ := by
    intro k
    set B' := ctuBlock σ ε ({k} : Finset (Fin 4)) with hB'
    set A' := perfectCore B' with hA'def
    have hAB : A' ≤ B' := CFSG.Quasithin.perfectCore_le B'
    have hk' : k ∈ ({k} : Finset (Fin 4)) := Finset.mem_singleton_self k
    have hnsk : nsElt (K := K) k ∈ spBlock K ({k} : Finset (Fin 4)) := by
      rw [spBlock_singleton]
      exact nsTorusSp_le_longRootSp2 k (mem_zpowers _)
    have hA1 : A'.map ψ ≤ centralizerPerfectCore (modelToG e (nsTorusSp K k)) := by
      refine CFSG.Quasithin.le_perfectCore_of_perfect ?_ ?_
      · rw [nsTorusSp, centralizer_modelToG_zpowers]
        rintro _ ⟨a, ha, rfl⟩
        rw [mem_centralizer_singleton_iff, ← hns k, ← map_mul, ← map_mul]
        congr 1
        exact commute_ctuBlock_ctuEmbed (hAB ha) hnsk
      · rw [← map_commutator, CFSG.Quasithin.perfectCore_perfect]
    have hcardE : Nat.card (centralizerPerfectCore (modelToG e (nsTorusSp K k))) ≤
        Nat.card (A'.map ψ) := by
      have hinj : Function.Injective (ψ.comp A'.subtype) := by
        intro x y hxy
        exact Subtype.ext (injOn_ctuBlock_of_ker_le_center hF hn3 hnq hψker hk' (hAB x.2)
          (hAB y.2) hxy)
      have h1 : Nat.card (A'.map ψ) = Nat.card A' := by
        have h2 : A'.map ψ = (ψ.comp A'.subtype).range := by
          rw [MonoidHom.range_comp, range_subtype]
        rw [h2]
        exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
      have hEperf : perfectCore (centralizerPerfectCore (modelToG e (nsTorusSp K k))) =
          centralizerPerfectCore (modelToG e (nsTorusSp K k)) :=
        CFSG.Quasithin.perfectCore_eq_self_of_perfect
          (F4Pilot.commutator_centralizerPerfectCore _)
      have h3 : centralizerPerfectCore (modelToG e (nsTorusSp K k)) =
          (perfectCore (⊤ : Subgroup B')).map (P k).Φ := by
        rw [CFSG.Quasithin.map_perfectCore, ← MonoidHom.range_eq_map, (P k).range_eq, hEperf]
      have h4 : (perfectCore (⊤ : Subgroup B')).map B'.subtype = A' := by
        rw [CFSG.Quasithin.map_perfectCore, ← MonoidHom.range_eq_map, range_subtype]
      rw [h1, h3, ← h4, Subgroup.card_map_of_injective B'.subtype_injective]
      exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)
    have heq := Subgroup.eq_of_le_of_card_ge hA1 hcardE
    rw [← heq, ← hψrange]
    rintro _ ⟨a, -, rfl⟩
    exact ⟨a, rfl⟩
  have hG₀eq : G₀ = nsGlobal e := le_antisymm hG₀le (by
    rw [nsGlobal_def]
    exact iSup_le hEk)
  exact ⟨ψ, hψrange.trans hG₀eq, hψker⟩

theorem nsUnitaryCover_four_of_nsUniParamAgree (hF : Nat.card F = (2 ^ 1) ^ 2)
    (P : ∀ k : Fin 4, NsUniParam ε hε (unitaryInvolution F 2 1) ι hι e k)
    (hagree : NsUniParamAgree P) (hcomm : NsUniProductCommute hF P) :
    NsUnitaryCover e (2 * 4 + ε) := by
  obtain ⟨ψ, hψr, hψk⟩ := exists_ct_nsUniRow_four_of_agree hF P hagree hcomm
  exact nsUnitaryCover_of_SU hF ψ hψr hψk

end Recognition

end CFSG.SeitzReduction.SymplecticPilot

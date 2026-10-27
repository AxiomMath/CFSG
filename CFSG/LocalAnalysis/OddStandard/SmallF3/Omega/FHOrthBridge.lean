module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFD4OG
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205HU33Pf
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GFacts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1Simp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FHCent3Gen
public import CFSG.Blueprint.OddStandardExact
public import CFSG.Blueprint.RecognitionDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf42U3Model
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205HU33

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG CFSG.Blueprint CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance CFSG.Assembly.LowTwoRank

private lemma fh_conj_comm {G : Type} [Group G] {a u z : G}
    (hu : u * a = a * u) (hz : z * a = a * z) :
    (u * z * u⁻¹) * a = a * (u * z * u⁻¹) := by
  have hu' : u⁻¹ * a = a * u⁻¹ := by
    calc u⁻¹ * a = (u⁻¹ * a * u) * u⁻¹ := by group
      _ = a * u⁻¹ := by
        have h : u⁻¹ * a * u = a := by
          calc u⁻¹ * a * u = u⁻¹ * (a * u) := by group
            _ = u⁻¹ * (u * a) := by rw [hu.symm]
            _ = a := by group
        rw [h]
  calc (u * z * u⁻¹) * a = u * z * (u⁻¹ * a) := by group
    _ = u * z * (a * u⁻¹) := by rw [hu']
    _ = u * (z * a) * u⁻¹ := by group
    _ = u * (a * z) * u⁻¹ := by rw [hz]
    _ = u * a * z * u⁻¹ := by group
    _ = a * u * z * u⁻¹ := by rw [hu]
    _ = a * (u * z * u⁻¹) := by group

theorem fh_f1_of_autOddFree {A : Type} [Group A] [Finite A] (H : Subgroup A) [H.Normal]
    (hC : centralizer (H : Set A) = ⊥) (hX : Q3NM.AutOddFree ↥H) {a : A} (ha : orderOf a = 2) :
    CFSG.inSubgroup (CFSG.pCore 3) (H ⊓ centralizer ({a} : Set A)) = ⊥ := by
  set C : Subgroup A := centralizer ({a} : Set A) with hCdef
  set K : Subgroup A := H ⊓ C with hKdef
  have hOa : oddCoreIn C = ⊥ := by
    set ρ : A →* MulAut ↥H := MulAut.conjNormal with hρdef
    have hρinj : Function.Injective ρ := by
      rw [injective_iff_map_eq_one]
      intro g hg
      have hmem : g ∈ Subgroup.centralizer (H : Set A) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have h1 := congrArg (fun φ : MulAut ↥H => (φ ⟨y, hy⟩ : A)) hg
        rw [hρdef] at h1
        have h2 : g * y * g⁻¹ = y := by simpa using h1
        have hgy : g * y = y * g := by
          calc g * y = (g * y * g⁻¹) * g := by group
            _ = y * g := by rw [h2]
        exact hgy.symm
      rw [hC, Subgroup.mem_bot] at hmem
      exact hmem
    set 𝒳 : Subgroup (MulAut ↥H) := ρ.range with h𝒳
    have hinn : Q3NM.innSubgroup ↥H ≤ 𝒳 := by
      rintro α ⟨h, rfl⟩
      exact ⟨(h : A), by
        rw [hρdef]
        ext x
        simp [MulAut.conjNormal_apply, MulAut.conj_apply]⟩
    let e : A ≃* ↥𝒳 := MonoidHom.ofInjective hρinj
    have hf : orderOf (e a) = 2 := by rw [MulEquiv.orderOf_eq]; exact ha
    have hbot : oddCoreIn (Subgroup.centralizer ({(e a)} : Set ↥𝒳)) = ⊥ := by
      have h := hX 𝒳 hinn (e a) hf
      rwa [involutionOddCore_eq_oddCoreIn] at h
    have h := oddCoreIn_centralizer_eq_bot_of_mulEquiv e a hbot
    simpa only [hCdef] using h
  set N0 : Subgroup A := CFSG.inSubgroup (CFSG.pCore 3) K with hN0
  have hN0C : N0 ≤ C := (Subgroup.map_subtype_le _).trans inf_le_right
  have hN03 : IsPGroup 3 N0 := IsPGroup.map CFSG.pCore_isPGroup K.subtype
  have hoddN0 : Odd (Nat.card N0) := by
    obtain ⟨n, hn⟩ := hN03.exists_card_eq
    rw [hn]
    exact (by decide : Odd (3 : ℕ)).pow
  have hnorm : C ≤ Subgroup.normalizer (N0 : Set A) := by
    intro x hx
    have hxa : x * a = a * x := Subgroup.mem_centralizer_singleton_iff.1 hx
    have hxinv : x⁻¹ * a = a * x⁻¹ := by
      calc x⁻¹ * a = (x⁻¹ * a * x) * x⁻¹ := by group
        _ = a * x⁻¹ := by
          have h : x⁻¹ * a * x = a := by
            calc x⁻¹ * a * x = x⁻¹ * (a * x) := by group
              _ = x⁻¹ * (x * a) := by rw [hxa.symm]
              _ = a := by group
          rw [h]
    have hHmap : H.map (MulAut.conj x).toMonoidHom = H := by
      simpa using (Subgroup.normal_iff_map_conj_eq.mp (inferInstance : H.Normal)) x
    have hCmap : C.map (MulAut.conj x).toMonoidHom = C := by
      change (Subgroup.centralizer ({a} : Set A)).map (MulAut.conj x).toMonoidHom =
        Subgroup.centralizer ({a} : Set A)
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        change x * y * x⁻¹ ∈ Subgroup.centralizer ({a} : Set A)
        exact Subgroup.mem_centralizer_singleton_iff.2
          (fh_conj_comm hxa (Subgroup.mem_centralizer_singleton_iff.1 hy))
      · intro hz
        refine ⟨x⁻¹ * z * x, ?_, ?_⟩
        · exact Subgroup.mem_centralizer_singleton_iff.2
            (by simpa using
              fh_conj_comm hxinv (Subgroup.mem_centralizer_singleton_iff.1 hz))
        · change x * (x⁻¹ * z * x) * x⁻¹ = z
          group
    have hKmap : K.map (MulAut.conj x).toMonoidHom = K := by
      rw [hKdef, Subgroup.map_inf_eq H C (MulAut.conj x).toMonoidHom
        (MulAut.conj x).injective, hHmap, hCmap]
    have hxN : x ∈ Subgroup.normalizer (K : Set A) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.2 hKmap
    let φ : MulAut ↥K := K.normalizerMonoidHom ⟨x, hxN⟩
    have hchar : (CFSG.pCore 3 ↥K).map φ.toMonoidHom = CFSG.pCore 3 ↥K :=
      Subgroup.characteristic_iff_map_eq.1
        (inferInstance : (CFSG.pCore 3 ↥K).Characteristic) φ
    have hcomp : (MulAut.conj x).toMonoidHom.comp K.subtype =
        K.subtype.comp φ.toMonoidHom := by
      ext y
      exact Subgroup.normalizerMonoidHom_apply_apply_coe K ⟨x, hxN⟩ y
    have hN0map : N0.map (MulAut.conj x).toMonoidHom = N0 := by
      show ((CFSG.pCore 3 ↥K).map K.subtype).map (MulAut.conj x).toMonoidHom =
        (CFSG.pCore 3 ↥K).map K.subtype
      rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hchar]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 hN0map
  have hle : N0 ≤ oddCoreIn C := le_oddCoreIn_of_normalizes hN0C hnorm hoddN0
  rw [hOa] at hle
  exact le_bot_iff.mp hle

section Certified


theorem fh_autOddFree_of_smallF3Omega {Y : Type} [Group Y] [Finite Y]
    (h : SmallF3OmegaQuotient Y) : Q3NM.AutOddFree Y := by
  obtain ⟨hsimple, hZ⟩ := l34g_simple_of_simpleFStar (Or.inl h)
  haveI : IsSimpleGroup Y := hsimple
  let e : Y ⧸ Subgroup.center Y ≃* Y :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hCent : CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.CentOmega3 Y := by
    change LieModel (Y ⧸ Subgroup.center Y) .PSp 2 3 1 ∨
      LieModel (Y ⧸ Subgroup.center Y) .PSL 4 3 1 ∨
      LieModel (Y ⧸ Subgroup.center Y) .PSU 4 3 1 ∨
      (∃ k, 3 ≤ k ∧ LieModel (Y ⧸ Subgroup.center Y) .POmegaOdd k 3 1) ∨
      (∃ k, 4 ≤ k ∧ LieModel (Y ⧸ Subgroup.center Y) .POmegaPlus k 3 1) ∨
      (∃ k, 4 ≤ k ∧ LieModel (Y ⧸ Subgroup.center Y) .POmegaMinus k 3 1)
    rcases h with h | h | h | h | h | h
    · exact Or.inl (LieModel.of_mulEquiv e.symm h)
    · exact Or.inr (Or.inl (LieModel.of_mulEquiv e.symm h))
    · exact Or.inr (Or.inr (Or.inl (LieModel.of_mulEquiv e.symm h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨3, le_rfl, LieModel.of_mulEquiv e.symm h⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨4, le_rfl, LieModel.of_mulEquiv e.symm h⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨4, le_rfl, LieModel.of_mulEquiv e.symm h⟩))))
  exact Q3NM.AutOddFree.of_mulEquiv e (TL4.omegaAutOddFreeR_proved Y hCent)

theorem fh_autOddFree_psu3 {Y : Type} [Group Y] [Finite Y] (h : LieModel Y .PSU 3 3 1) :
    Q3NM.AutOddFree Y := by
  have hsimple : IsSimpleGroup Y :=
    (l34g_simple_of_simpleFStar (Or.inr (Or.inr (Or.inr (Or.inr h))))).1
  haveI : IsSimpleGroup Y := hsimple
  refine TL4.autOddFree_of_outer (t := .PSU) (n := 3) (by decide) (by decide) trivial
    (by decide) h ?_
  intro σ hσ hin
  exact CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.frameOuterFixedOddFree_PSU3
    Y hsimple h σ hσ hin

private theorem fh_odd3Inner_model {t : StatedLieTag} {n : ℕ}
    (hD4 : ¬ (t = .POmegaPlus ∧ n = 4)) (hT : t ≠ .trialityD4) (hFT : IsFundTag t)
    (hcl : t ∈ classicalTags) {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hS : LieModel S t n 3 1) : FHOdd3Inner S := by
  have hadm : StatedLieAdmissible t n 3 1 := (Upgrade.statedClassicalModel_of_lieModel hcl hS).1
  obtain ⟨ψ, hψ, hker⟩ :=
    Upgrade.lieModelCentralCover t n 3 1 Nat.prime_three (by norm_num) hFT hadm S hS
  obtain ⟨hSq, -, -, -, -⟩ := Q3NM.centralQuotientData Nat.prime_three hFT hadm S ψ hψ hker
  have hZ := TL4.center_eq_bot_of_isQuasisimple hSq
  intro σ hσ
  have hodd : Odd (orderOf σ) := Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hσ)
  obtain ⟨s, hs⟩ := TL4.oddAut_inner_of_cover hD4 hT hFT hadm ψ hψ hker hZ σ hodd
  exact ⟨s, hs.symm⟩

theorem fh_odd3Inner_of_tl4 {Y : Type} [Group Y] [Finite Y]
    (h : LieModel Y .PSp 2 3 1 ∨ LieModel Y .PSL 4 3 1 ∨ LieModel Y .PSU 4 3 1 ∨
      LieModel Y .POmegaOdd 3 3 1 ∨ LieModel Y .POmegaMinus 4 3 1 ∨ LieModel Y .PSL 3 3 1 ∨
      LieModel Y .PSU 3 3 1) : FHOdd3Inner Y := by
  rcases h with h | h | h | h | h | h | h
  · haveI := (l34g_simple_of_simpleFStar (Or.inl (Or.inl h))).1
    exact fh_odd3Inner_model (t := .PSp) (n := 2) (by decide) (by decide) trivial (by decide) h
  · haveI := (l34g_simple_of_simpleFStar (Or.inl (Or.inr (Or.inl h)))).1
    exact fh_odd3Inner_model (t := .PSL) (n := 4) (by decide) (by decide) trivial (by decide) h
  · haveI := (l34g_simple_of_simpleFStar (Or.inl (Or.inr (Or.inr (Or.inl h))))).1
    exact fh_odd3Inner_model (t := .PSU) (n := 4) (by decide) (by decide) trivial (by decide) h
  · haveI := (l34g_simple_of_simpleFStar (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h)))))).1
    exact fh_odd3Inner_model (t := .POmegaOdd) (n := 3) (by decide) (by decide) trivial
      (by decide) h
  · haveI := (l34g_simple_of_simpleFStar
      (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))).1
    exact fh_odd3Inner_model (t := .POmegaMinus) (n := 4) (by decide) (by decide) trivial
      (by decide) h
  · haveI := (l34g_simple_of_simpleFStar (Or.inr (Or.inr (Or.inr (Or.inl h))))).1
    exact fh_odd3Inner_model (t := .PSL) (n := 3) (by decide) (by decide) trivial (by decide) h
  · haveI := (l34g_simple_of_simpleFStar (Or.inr (Or.inr (Or.inr (Or.inr h))))).1
    exact fh_odd3Inner_model (t := .PSU) (n := 3) (by decide) (by decide) trivial (by decide) h

end Certified

end CFSG.OddStandard.SmallF3.Omega

module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166LayerDataTwD5

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal

theorem inW_apply_of_mem_rootLevi {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {P₁ P₂ : HypPair Q} (h₁₂ : P₁.Orth P₂)
    {g : V ≃ₗ[K] V} (hg : g ∈ rootLevi Q P₁ P₂) {x : V} (hx : InW P₁ P₂ x) :
    InW P₁ P₂ (g x) := by
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := hg.1.1
  have hc0 : g * eichler Q P₁.e P₂.e = eichler Q P₁.e P₂.e * g :=
    mem_centralizer_singleton_iff.mp hg.1.2
  have hc1 : g * eichler Q P₁.f P₂.f = eichler Q P₁.f P₂.f * g :=
    mem_centralizer_singleton_iff.mp hg.2
  obtain ⟨he1, he2⟩ := apply_e_eq_coeff h₁₂ hc0
  obtain ⟨hf1, hf2⟩ := apply_e_eq_coeff (orth_flipPair_flipPair h₁₂) hc1
  simp only [flipPair_e, flipPair_f] at hf1 hf2
  have hd0 := det_coeff_eq_one h₁₂ hgO hc0
  have hd1 := det_coeff_eq_one (orth_flipPair_flipPair h₁₂) hgO hc1
  simp only [flipPair_e, flipPair_f] at hd1
  set a : K := polar Q (g P₁.e) P₁.f with ha
  set c : K := polar Q (g P₁.e) P₂.f with hc
  set b : K := polar Q (g P₂.e) P₁.f with hb
  set d : K := polar Q (g P₂.e) P₂.f with hd
  set a' : K := polar Q (g P₁.f) P₁.e with ha'
  set c' : K := polar Q (g P₁.f) P₂.e with hc'
  set b' : K := polar Q (g P₂.f) P₁.e with hb'
  set d' : K := polar Q (g P₂.f) P₂.e with hd'
  have he1' : g P₁.e = a • P₁.e + c • P₂.e := by rw [ha, hc]; exact he1
  have he2' : g P₂.e = b • P₁.e + d • P₂.e := by rw [hb, hd]; exact he2
  have hf1' : g P₁.f = a' • P₁.f + c' • P₂.f := by rw [ha', hc']; exact hf1
  have hf2' : g P₂.f = b' • P₁.f + d' • P₂.f := by rw [hb', hd']; exact hf2
  have hd0' : a * d - b * c = 1 := by rw [ha, hb, hc, hd]; exact hd0
  have hd1' : a' * d' - b' * c' = 1 := by rw [ha', hb', hc', hd']; exact hd1
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hcoef : d * a + c * b = 1 := by
    linear_combination hd0' + (b * c) * h2
  have hcoef' : d * c + c * d = 0 := by linear_combination (d * c) * h2
  have hcoef2 : d' * a' + c' * b' = 1 := by
    linear_combination hd1' + (b' * c') * h2
  have hcoef2' : d' * c' + c' * d' = 0 := by linear_combination (d' * c') * h2
  have he1inv : P₁.e = d • (g P₁.e) + c • (g P₂.e) := by
    rw [he1', he2', smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
    rw [show (d * a) • P₁.e + (d * c) • P₂.e + ((c * b) • P₁.e + (c * d) • P₂.e) =
        (d * a + c * b) • P₁.e + (d * c + c * d) • P₂.e by
      rw [add_smul, add_smul]; abel]
    rw [hcoef, hcoef', one_smul, zero_smul, add_zero]
  have he2inv : P₂.e = b • (g P₁.e) + a • (g P₂.e) := by
    have hcoefba : b * a + a * b = 0 := by linear_combination (b * a) * h2
    have hcoefda : b * c + a * d = 1 := by
      linear_combination hd0' + (b * c) * h2
    rw [he1', he2', smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
    rw [show (b * a) • P₁.e + (b * c) • P₂.e + ((a * b) • P₁.e + (a * d) • P₂.e) =
        (b * a + a * b) • P₁.e + (b * c + a * d) • P₂.e by
      rw [add_smul, add_smul]; abel]
    rw [hcoefba, hcoefda, zero_smul, one_smul, zero_add]
  have hf1inv : P₁.f = d' • (g P₁.f) + c' • (g P₂.f) := by
    rw [hf1', hf2', smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
    rw [show (d' * a') • P₁.f + (d' * c') • P₂.f + ((c' * b') • P₁.f + (c' * d') • P₂.f) =
        (d' * a' + c' * b') • P₁.f + (d' * c' + c' * d') • P₂.f by
      rw [add_smul, add_smul]; abel]
    rw [hcoef2, hcoef2', one_smul, zero_smul, add_zero]
  have hf2inv : P₂.f = b' • (g P₁.f) + a' • (g P₂.f) := by
    have hcoefba : b' * a' + a' * b' = 0 := by linear_combination (b' * a') * h2
    have hcoefda : b' * c' + a' * d' = 1 := by
      linear_combination hd1' + (b' * c') * h2
    rw [hf1', hf2', smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
    rw [show (b' * a') • P₁.f + (b' * c') • P₂.f + ((a' * b') • P₁.f + (a' * d') • P₂.f) =
        (b' * a' + a' * b') • P₁.f + (b' * c' + a' * d') • P₂.f by
      rw [add_smul, add_smul]; abel]
    rw [hcoefba, hcoefda, zero_smul, one_smul, zero_add]
  have h1 : polar Q (g x) (g P₁.e) = 0 := by
    rw [polar_map_of_mem hgO, polar_comm]; exact hx.1
  have h2' : polar Q (g x) (g P₂.e) = 0 := by
    rw [polar_map_of_mem hgO, polar_comm]; exact hx.2.2.1
  have h3 : polar Q (g x) (g P₁.f) = 0 := by
    rw [polar_map_of_mem hgO, polar_comm]; exact hx.2.1
  have h4 : polar Q (g x) (g P₂.f) = 0 := by
    rw [polar_map_of_mem hgO, polar_comm]; exact hx.2.2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [polar_comm, he1inv, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, h1, h2',
      mul_zero, mul_zero, add_zero]
  · rw [polar_comm, hf1inv, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, h3, h4,
      mul_zero, mul_zero, add_zero]
  · rw [polar_comm, he2inv, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, h1, h2',
      mul_zero, mul_zero, add_zero]
  · rw [polar_comm, hf2inv, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, h3, h4,
      mul_zero, mul_zero, add_zero]

end CFSG.SeitzReduction.OmegaPilot

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.OmegaMinusLD

open CFSG.SeitzReduction.OmegaPilot
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.Open
open QuadraticMap Subgroup ClassicalGroups.Orthogonal
open scoped Classical

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n q : ℕ} {b c : F}

private theorem inW_single_anisoLeft :
    InW (cPair F b c 0) (cPair F b c 1) (Pi.single ldAL (1 : F)) := by
  rw [inW_cPair_single_iff]
  have d0 := pairDisjoint_aniso (n := 5) (by norm_num) (0 : Fin 4)
  have d1 := pairDisjoint_aniso (n := 5) (by norm_num) (1 : Fin 4)
  exact ⟨d0.right_ne_left.symm, d0.left_ne_left.symm,
    d1.right_ne_left.symm, d1.left_ne_left.symm⟩

private theorem map_single_anisoLeft (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    Qc F b c (Pi.single ldAL (1 : F)) = 1 := by
  show Qc F b c (Pi.single (anisoCoordLeft (n := 5) (by norm_num)) (1 : F)) = 1
  exact (isAnisoCoord_coordinateQuadMinus (K := F) (n := 5) (by norm_num) hirr).map_left

private theorem apply_eq_self_of_eichler_conj
    {B : (Fin (2 * 5) → F) ≃ₗ[F] (Fin (2 * 5) → F)} {e e' f f' v : Fin (2 * 5) → F}
    (hO : B ∈ TauCeti.QuadraticMap.orthogonalGroup (Qc F b c))
    (hQe : Qc F b c e = 0) (hef : polar (Qc F b c) e f = 1)
    (hf'e : polar (Qc F b c) f' e = 0) (he'f : polar (Qc F b c) e' f = 0)
    (he'f' : polar (Qc F b c) e' f' = 1)
    (hev : polar (Qc F b c) e v = 0) (hfv : polar (Qc F b c) f v = 0)
    (hf'v : polar (Qc F b c) f' v = 0) (hQv : Qc F b c v = 1)
    (hconv : eichler (Qc F b c) (B e) (B v) = eichler (Qc F b c) e v)
    (hBvf : polar (Qc F b c) f (B v) = 0) (hBvf' : polar (Qc F b c) f' (B v) = 0)
    (hdec : B e = polar (Qc F b c) (B e) f • e + polar (Qc F b c) (B e) f' • e') :
    B e = e := by
  have hBQ : Qc F b c (B e) = 0 := by rw [map_of_mem hO, hQe]
  have hBpol : polar (Qc F b c) (B e) (B v) = 0 := by rw [polar_map_of_mem hO, hev]
  have hBQv : Qc F b c (B v) = 1 := by rw [map_of_mem hO, hQv]
  have hfe : polar (Qc F b c) f e = 1 := by rw [polar_comm]; exact hef
  have heq : polar (Qc F b c) f (B e) • (B v) -
      polar (Qc F b c) f (B e) • (B e) = v - e := by
    have h := congrArg (fun L => L f) hconv
    rw [eichler_apply hBQ hBpol, eichler_apply hQe hev] at h
    simp only [hBvf, hfv, hBQv, hQv, hfe, mul_one, one_mul, zero_add, one_smul] at h
    have h' : f + (polar (Qc F b c) f (B e) • (B v) -
        polar (Qc F b c) f (B e) • (B e)) = f + (v - e) := by
      calc f + (polar (Qc F b c) f (B e) • (B v) - polar (Qc F b c) f (B e) • (B e))
          = f + polar (Qc F b c) f (B e) • (B v) - polar (Qc F b c) f (B e) • (B e) := by abel
        _ = f + v - e := h
        _ = f + (v - e) := by abel
    exact add_left_cancel h'
  set a : F := polar (Qc F b c) f (B e) with ha
  have hBea : polar (Qc F b c) (B e) f = a := by rw [polar_comm]
  have hdec' : B e = a • e + polar (Qc F b c) (B e) f' • e' := by rw [← hBea]; exact hdec
  have hBvfs : polar (Qc F b c) (B v) f = 0 := by rw [polar_comm]; exact hBvf
  have hBvfs' : polar (Qc F b c) (B v) f' = 0 := by rw [polar_comm]; exact hBvf'
  have hvs : polar (Qc F b c) v f = 0 := by rw [polar_comm]; exact hfv
  have hvs' : polar (Qc F b c) v f' = 0 := by rw [polar_comm]; exact hf'v
  have hef' : polar (Qc F b c) e f' = 0 := by rw [polar_comm]; exact hf'e
  have haa : a * a = 1 := by
    have h := congrArg (fun z => polar (Qc F b c) z f) heq
    simp only [polar_sub_left, polar_smul_left_eq] at h
    rw [hBvfs, hBea, hvs, hef] at h
    linear_combination -h
  have hac : a * polar (Qc F b c) (B e) f' = 0 := by
    have h := congrArg (fun z => polar (Qc F b c) z f') heq
    simp only [polar_sub_left, polar_smul_left_eq] at h
    rw [hBvfs', hvs', hef'] at h
    linear_combination -h
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, mul_zero] at haa
    exact zero_ne_one haa
  have hc0 : polar (Qc F b c) (B e) f' = 0 := by
    rcases mul_eq_zero.mp hac with h | h
    · exact absurd h ha0
    · exact h
  have ha1 : a = 1 := eq_one_of_mul_self_eq_one haa
  rw [hdec', hc0, ha1, zero_smul, one_smul, add_zero]

private theorem apply_eq_self_of_eichler_conj_of_fix
    {B : (Fin (2 * 5) → F) ≃ₗ[F] (Fin (2 * 5) → F)} {e f w : Fin (2 * 5) → F}
    (hO : B ∈ TauCeti.QuadraticMap.orthogonalGroup (Qc F b c))
    (hQe : Qc F b c e = 0) (hef : polar (Qc F b c) e f = 1)
    (heW : polar (Qc F b c) e w = 0) (hfw : polar (Qc F b c) f w = 0)
    (hBe : B e = e)
    (hconv : eichler (Qc F b c) (B e) (B w) = eichler (Qc F b c) e w)
    (hBfw : polar (Qc F b c) f (B w) = 0) :
    B w = w := by
  have hBQ : Qc F b c (B e) = 0 := by rw [map_of_mem hO, hQe]
  have hBpol : polar (Qc F b c) (B e) (B w) = 0 := by rw [polar_map_of_mem hO, heW]
  have hfe : polar (Qc F b c) f e = 1 := by rw [polar_comm]; exact hef
  have hQ : Qc F b c (B w) = Qc F b c w := map_of_mem hO w
  have h := congrArg (fun L => L f) hconv
  rw [eichler_apply hBQ hBpol, eichler_apply hQe heW] at h
  rw [hBe, hfe, hfw, hBfw] at h
  simp only [one_mul, zero_add, mul_one, one_smul] at h
  rw [hQ] at h
  have h2 : f + B w = f + w := by
    have h3 := congrArg (fun z => z + Qc F b c w • e) h
    simpa only [sub_add_cancel] using h3
  exact add_left_cancel h2

private theorem apply_f_eq_self_of_fix
    {B : (Fin (2 * 5) → F) ≃ₗ[F] (Fin (2 * 5) → F)} {e e' f f' : Fin (2 * 5) → F}
    (hO : B ∈ TauCeti.QuadraticMap.orthogonalGroup (Qc F b c))
    (he : B e = e) (he' : B e' = e')
    (hdec : B f = polar (Qc F b c) (B f) e • f + polar (Qc F b c) (B f) e' • f')
    (hef : polar (Qc F b c) f e = 1) (he'f : polar (Qc F b c) f e' = 0) :
    B f = f := by
  have h1 : polar (Qc F b c) (B f) e = 1 := by
    rw [← he, polar_map_of_mem hO]; exact hef
  have h2 : polar (Qc F b c) (B f) e' = 0 := by
    rw [← he', polar_map_of_mem hO]; exact he'f
  rw [hdec, h1, h2, one_smul, zero_smul, add_zero]

private theorem projLift_commutes_of_mem_rootRadical
    (hQ' : ∃ v, Qc F b c v ≠ 0) {b₀ : matrixProjectiveDerived (Qc F b c)}
    (hbC : b₀ ∈ Subgroup.centralizer
      (rootRadicalBar (Qc F b c) (cPair F b c 0) (cPair F b c 1) :
        Set (matrixProjectiveDerived (Qc F b c))))
    {E : orthDerived (Qc F b c)}
    (hE : E ∈ (rootRadical (Qc F b c) (cPair F b c 0) (cPair F b c 1)).subgroupOf
      (orthDerived (Qc F b c))) :
    (E : (Fin (2 * 5) → F) ≃ₗ[F] (Fin (2 * 5) → F)) * projLift hQ' b₀ =
      projLift hQ' b₀ * E := by
  have hbar : projHom (Qc F b c) E ∈
      rootRadicalBar (Qc F b c) (cPair F b c 0) (cPair F b c 1) := ⟨E, hE, rfl⟩
  have hcomm : projHom (Qc F b c) E * b₀ = b₀ * projHom (Qc F b c) E :=
    Subgroup.mem_centralizer_iff.mp hbC _ hbar
  have := congrArg (projLiftHom hQ') hcomm
  simpa only [map_mul, projLiftHom_apply, projLift_projHom] using this

theorem bJ_inf_centralizer_rootRadicalBar (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (X : LayerQGenerators (F := F) (b := b) (c := c) (q := q)) :
    bJ X ⊓ Subgroup.centralizer
      (rootRadicalBar (Qc F b c) (cPair F b c 0) (cPair F b c 1) :
        Set (matrixProjectiveDerived (Qc F b c))) = ⊥ := by
  classical
  have hQ' : ∃ v, Qc F b c v ≠ 0 :=
    (isHypCoord_coordinateQuadMinus (K := F) (n := 5) (by norm_num) (b := b) (c := c)
      (0 : Fin 4)).exists_ne_zero
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadMinus 5 F b c (by norm_num) hirr
  have h01 : (cPair F b c 0).Orth (cPair F b c 1) := cPair_orth F b c 0 1 (by decide)
  refine le_antisymm ?_ bot_le
  rintro b₀ ⟨hbJ, hbC⟩
  rw [Subgroup.mem_bot]
  set B := projLift hQ' b₀ with hB
  have hBroot : B ∈ rootLevi (Qc F b c) (cPair F b c 0) (cPair F b c 1) :=
    projLift_mem_of_mem_map hQ' (bJ_le_rootLeviBar hirr X hbJ)
  have hBO : B ∈ TauCeti.QuadraticMap.orthogonalGroup (Qc F b c) := hBroot.1.1
  have hcommR : ∀ {E : orthDerived (Qc F b c)},
      E ∈ (rootRadical (Qc F b c) (cPair F b c 0) (cPair F b c 1)).subgroupOf
        (orthDerived (Qc F b c)) → (E : (Fin (2 * 5) → F) ≃ₗ[F] (Fin (2 * 5) → F)) * B =
        B * E := by
    intro E hE
    exact projLift_commutes_of_mem_rootRadical hQ' hbC hE
  have hconv_of (u w : Fin (2 * 5) → F)
      (hroot : eichler (Qc F b c) u w ∈
        rootRadical (Qc F b c) (cPair F b c 0) (cPair F b c 1)) :
      eichler (Qc F b c) (B u) (B w) = eichler (Qc F b c) u w := by
    have horth : eichler (Qc F b c) u w ∈ orthDerived (Qc F b c) :=
      eichler_mem_orthDerived hQ hT u w
    have hcommE : (⟨eichler (Qc F b c) u w, horth⟩ :
        orthDerived (Qc F b c)) * B =
        B * (⟨eichler (Qc F b c) u w, horth⟩ : orthDerived (Qc F b c)) :=
      hcommR (mem_subgroupOf.mpr hroot)
    have hconjB : B * eichler (Qc F b c) u w * B⁻¹ = eichler (Qc F b c) u w := by
      rw [← hcommE]
      rw [mul_inv_cancel_right]
    have hconj := eichler_conj hBO u w
    rw [hconjB] at hconj
    exact hconj.symm
  have hconv0 : ∀ w, InW (cPair F b c 0) (cPair F b c 1) w →
      eichler (Qc F b c) (B (cPair F b c 0).e) (B w) =
        eichler (Qc F b c) (cPair F b c 0).e w := by
    intro w hw
    exact hconv_of _ _ (eichler_mem_rootRadical_left h01 hw.1 hw.2.2.1)
  have hconv1 : ∀ w, InW (cPair F b c 0) (cPair F b c 1) w →
      eichler (Qc F b c) (B (cPair F b c 1).e) (B w) =
        eichler (Qc F b c) (cPair F b c 1).e w := by
    intro w hw
    exact hconv_of _ _ (eichler_mem_rootRadical_right h01 hw.1 hw.2.2.1)
  have hBW : ∀ w, InW (cPair F b c 0) (cPair F b c 1) w →
      InW (cPair F b c 0) (cPair F b c 1) (B w) :=
    fun w hw => inW_apply_of_mem_rootLevi h01 hBroot hw
  have hc0 : B * eichler (Qc F b c) (cPair F b c 0).e (cPair F b c 1).e =
      eichler (Qc F b c) (cPair F b c 0).e (cPair F b c 1).e * B :=
    mem_centralizer_singleton_iff.mp hBroot.1.2
  have hc1 : B * eichler (Qc F b c) (cPair F b c 0).f (cPair F b c 1).f =
      eichler (Qc F b c) (cPair F b c 0).f (cPair F b c 1).f * B :=
    mem_centralizer_singleton_iff.mp hBroot.2
  have he₁ := (apply_e_eq_coeff h01 hc0).1
  have he₂ := (apply_e_eq_coeff h01 hc0).2
  have hf₁ := (apply_e_eq_coeff (orth_flipPair_flipPair h01) hc1).1
  have hf₂ := (apply_e_eq_coeff (orth_flipPair_flipPair h01) hc1).2
  simp only [flipPair_e, flipPair_f] at hf₁ hf₂
  have hBe0 : B (cPair F b c 0).e = (cPair F b c 0).e :=
    apply_eq_self_of_eichler_conj hBO (cPair F b c 0).Q_e (cPair F b c 0).polar_ef
      (by rw [polar_comm]; exact h01.ef) (by rw [polar_comm]; exact h01.fe)
      (cPair F b c 1).polar_ef (inW_single_anisoLeft.1) (inW_single_anisoLeft.2.1)
      (inW_single_anisoLeft.2.2.2) (map_single_anisoLeft hirr)
      (hconv0 _ inW_single_anisoLeft) (hBW _ inW_single_anisoLeft).2.1
      (hBW _ inW_single_anisoLeft).2.2.2 he₁
  have hBe1 : B (cPair F b c 1).e = (cPair F b c 1).e :=
    apply_eq_self_of_eichler_conj hBO (cPair F b c 1).Q_e (cPair F b c 1).polar_ef
      h01.fe h01.ef
      (cPair F b c 0).polar_ef (inW_single_anisoLeft.2.2.1) (inW_single_anisoLeft.2.2.2)
      (inW_single_anisoLeft.2.1) (map_single_anisoLeft hirr)
      (hconv1 _ inW_single_anisoLeft) (hBW _ inW_single_anisoLeft).2.2.2
      (hBW _ inW_single_anisoLeft).2.1 (by rw [add_comm]; exact he₂)
  have hWfix : ∀ w, InW (cPair F b c 0) (cPair F b c 1) w → B w = w := by
    intro w hw
    exact apply_eq_self_of_eichler_conj_of_fix hBO (cPair F b c 0).Q_e
      (cPair F b c 0).polar_ef hw.1 hw.2.1 hBe0 (hconv0 w hw) (hBW w hw).2.1
  have hBf0 : B (cPair F b c 0).f = (cPair F b c 0).f :=
    apply_f_eq_self_of_fix hBO hBe0 hBe1 hf₁ (cPair F b c 0).polar_fe h01.fe
  have hBf1 : B (cPair F b c 1).f = (cPair F b c 1).f :=
    apply_f_eq_self_of_fix hBO hBe1 hBe0 (by rw [add_comm]; exact hf₂)
      (cPair F b c 1).polar_fe (by rw [polar_comm]; exact h01.ef)
  have hsE0 : (Pi.single (ldE 0) (1 : F) : Fin (2 * 5) → F) = (cPair F b c 0).e := by
    simp [cPair, ldE]
  have hsF0 : (Pi.single (ldF 0) (1 : F) : Fin (2 * 5) → F) = (cPair F b c 0).f := by
    simp [cPair, ldF]
  have hsE1 : (Pi.single (ldE 1) (1 : F) : Fin (2 * 5) → F) = (cPair F b c 1).e := by
    simp [cPair, ldE]
  have hsF1 : (Pi.single (ldF 1) (1 : F) : Fin (2 * 5) → F) = (cPair F b c 1).f := by
    simp [cPair, ldF]
  have hBfix : ∀ i : Fin (2 * 5), B (Pi.single i (1 : F)) = Pi.single i (1 : F) := by
    intro i
    rcases eq_or_ne i (ldE 0) with rfl | h1
    · rw [hsE0]; exact hBe0
    rcases eq_or_ne i (ldF 0) with rfl | h2
    · rw [hsF0]; exact hBf0
    rcases eq_or_ne i (ldE 1) with rfl | h3
    · rw [hsE1]; exact hBe1
    rcases eq_or_ne i (ldF 1) with rfl | h4
    · rw [hsF1]; exact hBf1
    · exact hWfix _ (by rw [inW_cPair_single_iff]; exact ⟨h2, h1, h4, h3⟩)
  have hB1 : B = 1 := linearEquiv_eq_one_of_fix_single hBfix
  have hlift1 : projLiftHom hQ' b₀ = 1 := by
    rw [projLiftHom_apply, ← hB]
    exact hB1
  exact projLiftHom_injective hQ' (by rw [hlift1, map_one])

end CFSG.LocalAnalysis.GLTheoremA.Y10F.OmegaMinusLD

end

module

public import CFSG.ClassicalInvolution.RouteD.TWT8VMinus
public import CFSG.ClassicalInvolution.RouteD.TWEB6Scalar
public import CFSG.ClassicalInvolution.RouteD.GapsFrBGen
public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusOrth
public import CFSG.ClassicalInvolution.RouteD.GapsOrthSpin
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutMinusNormalized
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.RouteD.TWEB6Fixed
public import CFSG.ClassicalInvolution.RouteD.TWEB6YBridge

public section

namespace CFSG.ClassicalInvolution.RouteD.TWT8

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TWE.B6
  CFSG.ClassicalInvolution.RouteD CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.ModelFacts.OrthAut
open CFSG.ClassicalInvolution.Generic (Commutes fundamentalSubgroups)
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Lift

variable {p f : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (GaloisField p f) V]
  [FiniteDimensional (GaloisField p f) V] {Q : QuadraticForm (GaloisField p f) V}

theorem bridgeSpin_of_omega (hodd : Odd (Nat.card (GaloisField p f)))
    {𝓕 : Set (Subgroup (spinGroup Q))}
    (cq : CentralQuot (spinAction Q) 𝓕 (fundSet Q) (scalars (GaloisField p f) V))
    {T₁ T₂ : Subgroup (spinGroup Q)} (h₁ : T₁ ∈ 𝓕) (h₂ : T₂ ∈ 𝓕)
    (hb : BridgeOmega Q (T₁.map (spinAction Q)) (T₂.map (spinAction Q))) :
    T₁ ≠ T₂ ∧ ¬ Commutes T₁ T₂ ∧ ∀ r, InvOf T₂ r → ∀ y ∈ T₁, r * y * r⁻¹ ∈ T₁ := by
  obtain ⟨-, -, hne, hnc, hnorm⟩ := hb
  refine ⟨fun h => hne (by rw [h]), fun h => hnc ((cq.commutes_iff h₁).mpr h), ?_⟩
  intro r hr y hy
  have hinv : InvOf (T₂.map (spinAction Q)) (spinAction Q r) := cq.invOf h₂ hr
  obtain ⟨i₂, hi₂⟩ := cq.map_mem T₂ h₂
  have hπr : spinAction Q r = i₂ := IsFundamental.eq_of_orderOf_eq_two hodd hi₂ hinv.1 hinv.2
  have hmem := hnorm i₂ hi₂
  rw [Subgroup.mem_normalizer_iff] at hmem
  have hmap : (T₁.map (MulAut.conj r).toMonoidHom).map (spinAction Q) = T₁.map (spinAction Q) := by
    ext s
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨_, ⟨y', hy', rfl⟩, rfl⟩
      obtain ⟨y'', hy'', hy''e⟩ := (hmem (spinAction Q y')).mp ⟨y', hy', rfl⟩
      refine ⟨y'', hy'', ?_⟩
      rw [hy''e]
      show _ = spinAction Q (r * y' * r⁻¹)
      rw [map_mul, map_mul, map_inv, hπr]
    · rintro ⟨y', hy', rfl⟩
      obtain ⟨y'', hy'', hy''e⟩ := (hmem (i₂⁻¹ * spinAction Q y' * i₂)).mpr (by
        have : i₂ * (i₂⁻¹ * spinAction Q y' * i₂) * i₂⁻¹ = spinAction Q y' := by group
        rw [this]
        exact ⟨y', hy', rfl⟩)
      refine ⟨(MulAut.conj r).toMonoidHom y'', ⟨y'', hy'', rfl⟩, ?_⟩
      show spinAction Q (r * y'' * r⁻¹) = spinAction Q y'
      rw [map_mul, map_mul, map_inv, hπr, hy''e]
      group
  have hperf : ⁅T₁.map (MulAut.conj r).toMonoidHom, T₁.map (MulAut.conj r).toMonoidHom⁆ =
      T₁.map (MulAut.conj r).toMonoidHom := by
    rw [← Subgroup.map_commutator, cq.perf T₁ h₁]
  have heq := CFSG.ClassicalInvolution.ModelFacts.eq_of_map_eq_of_isPerfect (spinAction Q)
    cq.ker_le hperf (cq.perf T₁ h₁) hmap
  rw [← heq]
  exact ⟨y, hy, rfl⟩

end Lift

section Frames

variable {p f : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (GaloisField p f) V]
  [FiniteDimensional (GaloisField p f) V] {Q : QuadraticForm (GaloisField p f) V} {m : ℕ}

theorem spinAction_mem_O (x : spinGroup Q) :
    spinAction Q x ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ x v

theorem exists_bridge_spin_of_frames (hodd : Odd (Nat.card (GaloisField p f))) (F₀ : HypFrame Q m)
    {𝓕 : Set (Subgroup (spinGroup Q))}
    (cq : CentralQuot (spinAction Q) 𝓕 (fundSet Q) (scalars (GaloisField p f) V))
    (h0 : 0 < m) (h1 : 1 < m) (h2 : 2 < m) {x₀ : spinGroup Q} {R₀ R₁ : Subgroup (spinGroup Q)}
    (hR₀ : R₀ = (rootSL2 F₀ 0 1 h0 h1 (by omega) true false).map (MulAut.conj x₀).toMonoidHom)
    (hR₁ : R₁ = (rootSL2 F₀ 1 2 h1 h2 (by omega) true false).map (MulAut.conj x₀).toMonoidHom)
    {F₁ F₂ : OFrame Q} (hbr : BridgeOmega Q F₁.La.range F₂.La.range)
    {W : Submodule (GaloisField p f) V} (hW₁ : F₁.span ≤ W) (hW₂ : F₂.span ≤ W)
    (hWo : ∀ a : Fin m, a.val < 3 → ∀ x ∈ hypPlane (imgPair F₀ a (spinAction_mem_O x₀)),
      ∀ y ∈ W, polar Q x y = 0) :
    ∃ T₁ ∈ 𝓕, ∃ T₂ ∈ 𝓕, Commutes T₁ R₀ ∧ Commutes T₁ R₁ ∧ Commutes T₂ R₀ ∧ Commutes T₂ R₁ ∧
      T₁ ≠ T₂ ∧ ¬ Commutes T₁ T₂ ∧ ∀ r, InvOf T₂ r → ∀ y ∈ T₁, r * y * r⁻¹ ∈ T₁ := by
  classical
  have hg := spinAction_mem_O (Q := Q) x₀
  let a0 : Fin m := ⟨0, h0⟩
  let a1 : Fin m := ⟨1, h1⟩
  let a2 : Fin m := ⟨2, h2⟩
  have o01 : (imgPair F₀ a0 hg).Orth (swapPair (imgPair F₀ a1 hg)) :=
    orth_swapPair (imgPair_orth F₀ hg (by simp [a0, a1, Fin.ext_iff]))
  have o12 : (imgPair F₀ a1 hg).Orth (swapPair (imgPair F₀ a2 hg)) :=
    orth_swapPair (imgPair_orth F₀ hg (by simp [a1, a2, Fin.ext_iff]))
  have hC₀ : (mkFrame (imgPair F₀ a0 hg) (swapPair (imgPair F₀ a1 hg)) o01).La.range =
      R₀.map (spinAction Q) := by
    rw [hR₀]
    exact La_range_eq_of_pairs F₀ h0 h1 (by omega) true false x₀ o01 ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
  have hC₁ : (mkFrame (imgPair F₀ a1 hg) (swapPair (imgPair F₀ a2 hg)) o12).La.range =
      R₁.map (spinAction Q) := by
    rw [hR₁]
    exact La_range_eq_of_pairs F₀ h1 h2 (by omega) true false x₀ o12 ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
  have hco : ∀ (F : OFrame Q), F.span ≤ W → ∀ (a b : Fin m)
      (hab : (imgPair F₀ a hg).Orth (swapPair (imgPair F₀ b hg))), a.val < 3 → b.val < 3 →
      Commutes F.La.range
        (mkFrame (imgPair F₀ a hg) (swapPair (imgPair F₀ b hg)) hab).La.range := by
    intro F hF a b hab ha hb
    have hspan : (mkFrame (imgPair F₀ a hg) (swapPair (imgPair F₀ b hg)) hab).span =
        hypPlane (imgPair F₀ a hg) ⊔ hypPlane (imgPair F₀ b hg) := by
      rw [frame_span_eq]
      show hypPlane (imgPair F₀ a hg) ⊔ hypPlane (swapPair (imgPair F₀ b hg)) = _
      rw [hypPlane_swapPair]
    refine commutes_of_span_orth F _ fun x hx y hy => ?_
    rw [hspan] at hy
    have hxW := hF hx
    exact polar_zero_of_mem_sup (A := W)
      (fun x' hx' y' hy' => by rw [polar_comm]; exact hWo a ha y' hy' x' hx')
      (fun x' hx' y' hy' => by rw [polar_comm]; exact hWo b hb y' hy' x' hx') x hxW y hy
  obtain ⟨T₁, hT₁, hT₁e⟩ := cq.surj _ hbr.1
  obtain ⟨T₂, hT₂, hT₂e⟩ := cq.surj _ hbr.2.1
  refine ⟨T₁, hT₁, T₂, hT₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (cq.commutes_iff hT₁).mp ?_
    rw [hT₁e, ← hC₀]
    exact hco F₁ hW₁ a0 a1 o01 (by simp [a0]) (by simp [a1])
  · refine (cq.commutes_iff hT₁).mp ?_
    rw [hT₁e, ← hC₁]
    exact hco F₁ hW₁ a1 a2 o12 (by simp [a1]) (by simp [a2])
  · refine (cq.commutes_iff hT₂).mp ?_
    rw [hT₂e, ← hC₀]
    exact hco F₂ hW₂ a0 a1 o01 (by simp [a0]) (by simp [a1])
  · refine (cq.commutes_iff hT₂).mp ?_
    rw [hT₂e, ← hC₁]
    exact hco F₂ hW₂ a1 a2 o12 (by simp [a1]) (by simp [a2])
  · exact (bridgeSpin_of_omega hodd cq hT₁ hT₂ (by rw [hT₁e, hT₂e]; exact hbr)).1
  · exact (bridgeSpin_of_omega hodd cq hT₁ hT₂ (by rw [hT₁e, hT₂e]; exact hbr)).2.1
  · exact (bridgeSpin_of_omega hodd cq hT₁ hT₂ (by rw [hT₁e, hT₂e]; exact hbr)).2.2

end Frames

@[expose] def planeImg {F : Type} [Field F] (n : ℕ) (g : Vm n F ≃ₗ[F] Vm n F) :
    Submodule F (Vm n F) := (planeSub n F).map (g : Vm n F →ₗ[F] Vm n F)

section Minus

variable {F : Type} [Field F] [Finite F] {n : ℕ} {b c : F}

theorem finrank_planeSub : Module.finrank F (planeSub n F) = 2 := by
  let L : (Fin 2 → F) →ₗ[F] Vm n F :=
    { toFun := planeVec n
      map_add' := planeVec_add n
      map_smul' := fun r w => planeVec_smul n r w }
  have hinj : Function.Injective L := planeVec_injective n
  have hrange : LinearMap.range L = planeSub n F := by
    ext x
    simp only [LinearMap.mem_range, mem_planeSub]
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w, rfl⟩
    · rintro ⟨w, rfl⟩
      exact ⟨w, rfl⟩
  rw [← hrange, LinearMap.finrank_range_of_inj hinj]
  simp

theorem planeImg_aniso (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {g : Vm n F ≃ₗ[F] Vm n F}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n F b c)) :
    Module.finrank F (planeImg n g) = 2 ∧
      ¬ HasSingularVector (quadMinus n F b c) (planeImg n g) := by
  refine ⟨by rw [planeImg, LinearEquiv.finrank_map_eq, finrank_planeSub], ?_⟩
  rintro ⟨y, hy, hy0, hQy⟩
  obtain ⟨_, ⟨w, rfl⟩, rfl⟩ := hy
  have hw : w ≠ 0 := by
    rintro rfl
    apply hy0
    simp [planeVec_zero]
  have := map_of_mem hg (planeVec n w)
  change (quadMinus n F b c) (g (planeVec n w)) = 0 at hQy
  rw [this, quadMinus_planeVec'] at hQy
  exact planeNorm_ne_zero hirr hw hQy

theorem polar_imgPair_planeImg {g : Vm n F ≃ₗ[F] Vm n F}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n F b c)) (j : Fin (n - 1)) :
    ∀ x ∈ hypPlane (imgPair (minusFrame n b c).toHypFrame j hg), ∀ y ∈ planeImg n g,
      polar (quadMinus n F b c) x y = 0 := by
  intro x hx y hy
  obtain ⟨a, a', rfl⟩ := (mem_hypPlane_iff _).mp hx
  obtain ⟨_, ⟨w, rfl⟩, rfl⟩ := hy
  change polar (quadMinus n F b c) (a • g ((minusFrame n b c).toHypFrame.vec j true) +
    a' • g ((minusFrame n b c).toHypFrame.vec j false)) (g (planeVec n w)) = 0
  rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, polar_map_of_mem hg,
    polar_map_of_mem hg]
  have h1 : polar (quadMinus n F b c) ((minusFrame n b c).toHypFrame.vec j true)
      (planeVec n w) = 0 := polar_minusVec_planeVec n b c j true w
  have h2 : polar (quadMinus n F b c) ((minusFrame n b c).toHypFrame.vec j false)
      (planeVec n w) = 0 := polar_minusVec_planeVec n b c j false w
  rw [h1, h2]
  ring

end Minus

section Models

variable {p f : ℕ} [Fact p.Prime]


theorem exists_bridge_spin_plus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {R₀ R₁ : Subgroup (spinGroup (quadPlus 6 (GaloisField p f)))}
    (h₀ : R₀ ∈ fundamentalSubgroups .POmegaPlus (plusDatum 6 (GaloisField p f) (by norm_num)))
    (h₁ : R₁ ∈ fundamentalSubgroups .POmegaPlus (plusDatum 6 (GaloisField p f) (by norm_num)))
    (hadj : ModelAdj (Subgroup.center _) R₀ R₁)
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField p f) W R₀ R₁) :
    ∃ T₁ ∈ fundamentalSubgroups .POmegaPlus (plusDatum 6 (GaloisField p f) (by norm_num)),
      ∃ T₂ ∈ fundamentalSubgroups .POmegaPlus (plusDatum 6 (GaloisField p f) (by norm_num)),
        Commutes T₁ R₀ ∧ Commutes T₁ R₁ ∧ Commutes T₂ R₀ ∧ Commutes T₂ R₁ ∧ T₁ ≠ T₂ ∧
        ¬ Commutes T₁ T₂ ∧ ∀ r, InvOf T₂ r → ∀ y ∈ T₁, r * y * r⁻¹ ∈ T₁ := by
  classical
  obtain ⟨hf0, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have : Invertible (2 : GaloisField p f) := invertibleOfNonzero h2
  have cq := centralQuot_plus (m := 6) hp2 (by norm_num) (by norm_num) hq
  have hQ : (quadPlus 6 (GaloisField p f)).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadPlus 6 _)
  have hdim : 9 ≤ Module.finrank (GaloisField p f) (Fin 6 ⊕ Fin 6 → GaloisField p f) := by
    rw [finrank_plus]
    norm_num
  set F₀ : HypFrame (quadPlus 6 (GaloisField p f)) 6 :=
    plusFrame 6 (GaloisField p f) (by norm_num : 3 ≤ 6) with hF₀
  obtain ⟨x₀, hx0, hx1⟩ := exists_spin_pair_gen hp2 hq hQ (m := 6) (by norm_num) F₀ hdim cq h₀ h₁
    hadj hlin
  have hg := spinAction_mem_O (Q := quadPlus 6 (GaloisField p f)) x₀
  have hc : ∀ a b : Fin 6, a ≠ b → (imgPair F₀ a hg).Orth (imgPair F₀ b hg) :=
    fun a b hab => imgPair_orth F₀ hg hab
  obtain ⟨hbr, hs₁, hs₂⟩ := bridgeOmega_of_pairs hodd (imgPair F₀ 3 hg) (imgPair F₀ 4 hg)
    (imgPair F₀ 5 hg) (hc 3 4 (by decide)) (hc 3 5 (by decide)) (hc 4 5 (by decide))
  refine exists_bridge_spin_of_frames hodd F₀ cq (by norm_num) (by norm_num) (by norm_num) hx0 hx1
    hbr (W := hypPlane (imgPair F₀ 3 hg) ⊔ hypPlane (imgPair F₀ 4 hg) ⊔ hypPlane (imgPair F₀ 5 hg))
    ?_ ?_ ?_
  · rw [hs₁]
    exact le_sup_left
  · rw [hs₂]
    exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
  · intro a ha x hx y hy
    have h3 : a ≠ 3 := fun h => by simp [h] at ha
    have h4 : a ≠ 4 := fun h => by simp [h] at ha
    have h5 : a ≠ 5 := fun h => by simp [h] at ha
    exact polar_zero_of_mem_sup (A := hypPlane (imgPair F₀ a hg))
      (polar_zero_of_mem_sup (polar_hypPlane_of_orth (hc a 3 h3))
        (polar_hypPlane_of_orth (hc a 4 h4))) (polar_hypPlane_of_orth (hc a 5 h5)) x hx y hy

theorem exists_bridge_spin_minus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {R₀ R₁ : Subgroup (spinGroup (quadMinus 6 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2))}
    (h₀ : R₀ ∈ fundamentalSubgroups .POmegaMinus (minusDatum 6 (minusCoeffs_irr p f)))
    (h₁ : R₁ ∈ fundamentalSubgroups .POmegaMinus (minusDatum 6 (minusCoeffs_irr p f)))
    (hadj : ModelAdj (Subgroup.center _) R₀ R₁)
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField p f) W R₀ R₁) :
    ∃ T₁ ∈ fundamentalSubgroups .POmegaMinus (minusDatum 6 (minusCoeffs_irr p f)),
      ∃ T₂ ∈ fundamentalSubgroups .POmegaMinus (minusDatum 6 (minusCoeffs_irr p f)),
        Commutes T₁ R₀ ∧ Commutes T₁ R₁ ∧ Commutes T₂ R₀ ∧ Commutes T₂ R₁ ∧ T₁ ≠ T₂ ∧
        ¬ Commutes T₁ T₂ ∧ ∀ r, InvOf T₂ r → ∀ y ∈ T₁, r * y * r⁻¹ ∈ T₁ := by
  classical
  obtain ⟨hf0, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hf1 : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr hf0
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have : Invertible (2 : GaloisField p f) := invertibleOfNonzero h2
  have hirr := minusCoeffs_irr p f
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .POmegaMinus 6 p f :=
    ⟨Fact.out, hf1, by show 4 ≤ 6; omega⟩
  have cq := Exotic.centralQuot_minus hp2 hq hadm
  have hQ : (quadMinus 6 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_quadMinus_of_finite 6 (GaloisField p f) hirr)
  have hdim : 9 ≤ Module.finrank (GaloisField p f)
      (Fin (6 - 1) ⊕ Fin (6 - 1) ⊕ Fin 2 → GaloisField p f) := by
    rw [finrank_minus p f 6 (by omega)]
    omega
  set F₀ : HypFrame (quadMinus 6 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2)
      (6 - 1) := (minusFrame 6 (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame with hF₀
  obtain ⟨x₀, hx0, hx1⟩ := exists_spin_pair_gen hp2 hq hQ (m := 6 - 1) (by norm_num) F₀ hdim cq h₀
    h₁ hadj hlin
  have hg := spinAction_mem_O (Q := quadMinus 6 (GaloisField p f) (minusCoeffs p f).1
    (minusCoeffs p f).2) x₀
  have hc : ∀ a b : Fin (6 - 1), a ≠ b → (imgPair F₀ a hg).Orth (imgPair F₀ b hg) :=
    fun a b hab => imgPair_orth F₀ hg hab
  have hK' : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
    rw [GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]
  obtain ⟨inst⟩ := Aniso.nonempty_algebra hK hK'
  have E := QuadExt.of_card hK hK' hodd
  obtain ⟨hZ2, hZs⟩ := planeImg_aniso hirr hg
  obtain ⟨F₁, F₂, hbr, hs₁, hs₂⟩ := exists_bridge_minus hodd E (imgPair F₀ ⟨3, by norm_num⟩ hg)
    (imgPair F₀ ⟨4, by norm_num⟩ hg) (hc _ _ (by simp [Fin.ext_iff])) hZ2 hZs
    (polar_imgPair_planeImg hg ⟨3, by norm_num⟩) (polar_imgPair_planeImg hg ⟨4, by norm_num⟩)
  refine exists_bridge_spin_of_frames hodd F₀ cq (by norm_num) (by norm_num) (by norm_num) hx0 hx1
    hbr (W := hypPlane (imgPair F₀ ⟨3, by norm_num⟩ hg) ⊔
      hypPlane (imgPair F₀ ⟨4, by norm_num⟩ hg) ⊔
      planeImg 6 (spinAction (quadMinus 6 (GaloisField p f) (minusCoeffs p f).1
        (minusCoeffs p f).2) x₀)) hs₁ hs₂ ?_
  intro a ha x hx y hy
  have h3 : a ≠ ⟨3, by norm_num⟩ := fun h => by simp [h] at ha
  have h4 : a ≠ ⟨4, by norm_num⟩ := fun h => by simp [h] at ha
  exact polar_zero_of_mem_sup (A := hypPlane (imgPair F₀ a hg))
    (polar_zero_of_mem_sup (polar_hypPlane_of_orth (hc a _ h3))
      (polar_hypPlane_of_orth (hc a _ h4))) (polar_imgPair_planeImg hg a) x hx y hy

end Models

end CFSG.ClassicalInvolution.RouteD.TWT8

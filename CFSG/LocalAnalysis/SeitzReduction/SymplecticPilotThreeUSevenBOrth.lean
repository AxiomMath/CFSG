module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeUSevenBGen
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeUSevenBLevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeUSevenMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeOrthPlane
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeUSixCore
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2UnitaryCTModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeShortRows
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallJ

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.LieType.CurtisTits (rankOne)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore centralizerPerfectCore_le_centralizer)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG)
open CFSG.Quasithin (perfectCore)
open scoped MatrixGroups

section Transport

variable {K F : Type} [Field K] [Field F] [CharP K 2] {σ : F ≃+* F} {ι' : K →+* F}

theorem usb_coord_e1 : (ctuCoord 2 1 (Sum.inl (Sum.inl 1)) : Fin (2 * 2 + 1)) = 1 := Fin.ext rfl

theorem usb_coord_v : (ctuCoord 2 1 (Sum.inr 0) : Fin (2 * 2 + 1)) = 2 := Fin.ext rfl

theorem usb_coord_f1 : (ctuCoord 2 1 (Sum.inl (Sum.inr 1)) : Fin (2 * 2 + 1)) = 3 := Fin.ext rfl

theorem usb_ctuBlockIdx (a : Fin (2 * 1 + 1)) :
    (ctuBlockIdx 1 1 (0 : Fin (1 + 1)) a : ℕ) = a.val + 1 := by
  obtain ⟨w, rfl⟩ := (ctuCoord 1 1).surjective a
  rw [ctuBlockIdx_ctuCoord]
  rcases w with (p | p) | i
  · rw [Fin.fin_one_eq_zero p]
    rfl
  · rw [Fin.fin_one_eq_zero p]
    rfl
  · rw [Fin.fin_one_eq_zero i]
    rfl

variable (hσ : ∀ c, σ (σ c) = c)

theorem ctuBlockEquiv_uOddHeis [CharP F 2] {ω : F} (hω : σ ω = ω + 1) :
    ctuBlockEquiv σ le_rfl (0 : Fin (1 + 1)) ⟨uOddHeis hσ hω, uOddHeis_mem_ctuBlock hσ hω⟩ =
      ug3Heis hσ (ug3_valid_y hω) := by
  apply mat_injective
  rw [mat_ctuBlockEquiv]
  ext a b
  rw [submatrix_apply]
  have ha := usb_ctuBlockIdx a
  have hb := usb_ctuBlockIdx b
  change heisenbergMatrix σ (1 : Fin (2 * 2 + 1)) 2 1 ω _ _ = heisenbergMatrix σ (0 : Fin 3) 1 1 ω a b
  simp only [heisenbergMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.single_apply, Fin.ext_iff, ha, hb, Fin.val_rev]
  fin_cases a <;> fin_cases b <;> simp

theorem ctuEmbed_complSp_longBlock_mem (hι' : ∀ c, σ (ι' c) = ι' c) (s : SL(2, K)) :
    ctuEmbed 1 le_rfl σ ι' hι' ((complSpEquiv (0 : Fin (1 + 1)) (longBlock K 1 0 s) :
      complSp K 0) : StatedSp (1 + 1) K) ∈ ctuBlock σ 1 ({0} : Finset (Fin (1 + 1))) := by
  rw [ctuEmbed_mem_ctuBlock_iff, spBlock_compl_singleton]
  exact (complSpEquiv (0 : Fin (1 + 1)) (longBlock K 1 0 s)).2

theorem ctuBlockEquiv_ctuEmbed_complSp_longBlock (hι' : ∀ c, σ (ι' c) = ι' c)
    (s : SL(2, K)) :
    ctuBlockEquiv σ le_rfl (0 : Fin (1 + 1)) ⟨_, ctuEmbed_complSp_longBlock_mem hι' s⟩ =
      ug3Sl σ ι' hι' s :=
  ctuBlockEquiv_ctuEmbed le_rfl hι' 0 (longBlock K 1 0 s) _

omit [CharP K 2] in
theorem coe_complSpEquiv_complSpEquiv_longBlock (s : SL(2, K)) :
    ((complSpEquiv (0 : Fin 3) ((complSpEquiv (0 : Fin 2) (longBlock K 1 0 s) : complSp K 0) :
      StatedSp 2 K) : complSp K 0) : StatedSp 3 K) = longBlock K 3 2 s := by
  rw [coe_complSpEquiv_apply, coe_complSpEquiv_apply, spEmbed_longBlock, spEmbed_longBlock]
  rfl

omit [CharP K 2] in
theorem coe_complSpEquiv_siegDiag_one :
    ((complSpEquiv (0 : Fin 3) (siegDiag K 1 1) : complSp K 0) : StatedSp 3 K) =
      siegDiag K 2 1 := by
  rw [siegDiag_eq_longBlock, siegDiag_eq_longBlock, coe_complSpEquiv_apply, spEmbed_longBlock]
  rfl

theorem uOddHeis_inv_sq_eq_ctuEmbed [CharP F 2] {ω : F} (hω : σ ω = ω + 1)
    (hι' : ∀ c, σ (ι' c) = ι' c) :
    (uOddHeis hσ hω)⁻¹ * (uOddHeis hσ hω)⁻¹ = ctuEmbed 1 le_rfl σ ι' hι' (siegDiag K 1 1) := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_uOddHeis_inv_sq, siegDiag_eq_longBlock, upperUnit_eq_sl2Upper,
    coe_ctuEmbed_longBlock_sl2Upper, map_one, usb_coord_e1]
  ext a b
  simp only [heisenbergMatrix, longRootMatrix, Matrix.add_apply, Matrix.sub_apply,
    Matrix.one_apply, Matrix.single_apply, map_zero]
  fin_cases a <;> fin_cases b <;> simp [Fin.ext_iff, Fin.rev]

end Transport

section Orth

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite K] in
theorem pieceCore_two_eq_map_ctuBlock_of_uodd (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K)
    {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
    (hf : 2 ≤ f) {ι : K →+* F} {hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c}
    (Φ : SU (unitaryInvolution F 2 f) (2 * 2 + 1) →* G) (hrange : Φ.range = neighbourCore e 0)
    (hker : Φ.ker ≤ center (SU (unitaryInvolution F 2 f) (2 * 2 + 1)))
    (hN1 : ∀ x : StatedSp 2 K, Φ (ctuEmbed 1 le_rfl (unitaryInvolution F 2 f) ι hι x) =
      ((e.symm ((complSpEquiv 0 x : complSp K 0) : StatedSp 3 K) : L) : G)) :
    pieceCore e ({2} : Finset (Fin 3)) =
      (ctuBlock (unitaryInvolution F 2 f) 1 ({0} : Finset (Fin 2))).map Φ := by
  have hY : ((rootTorusSp K 0).map (ctuEmbed 1 le_rfl (unitaryInvolution F 2 f) ι hι)).map Φ =
      modelToG e ((rootTorusSp K 0).map (complSpHom (K := K) 0)) := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      change Φ (ctuEmbed 1 le_rfl (unitaryInvolution F 2 f) ι hι x) ∈ _
      rw [hN1]
      exact symm_mem_modelToG e ⟨x, hx, rfl⟩
    · intro hy
      obtain ⟨_, ⟨x, hx, rfl⟩, hxy⟩ := (UnitaryPilot.mem_modelToG e).1 hy
      refine ⟨_, ⟨x, hx, rfl⟩, ?_⟩
      change Φ (ctuEmbed 1 le_rfl (unitaryInvolution F 2 f) ι hι x) = y
      rw [hN1, ← hxy]
      rfl
  rw [pieceCore_eq_map_perfectCore_centralizer e hK (k := 0) (by decide) leviTorusSp_two_le_sup
    map_rootTorusSp_zero_le_leviTorusSp_two Φ hrange hker _ hY,
    perfectCore_centralizer_ctuEmbed_rootTorus_eq hF le_rfl hι hK (l := (0 : Fin 2))
      (by decide) (fun h3 => by
        have h4 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
        omega)]

theorem usb_unitaryInvolution_ne_one {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) : unitaryInvolution F 2 f ≠ 1 := by
  obtain ⟨a, ha⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_ne hF
  intro h1
  exact ha (by rw [h1]; rfl)

theorem pieceCore_two_le_centralizer_simpleRootSL2_zero_uodd (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp 3 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hF : Nat.card F = (2 ^ f) ^ 2) {ι : K →+* F}
    {hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c}
    (Φ : SU (unitaryInvolution F 2 f) (2 * 2 + 1) →* G) (hrange : Φ.range = neighbourCore e 0)
    (hker : Φ.ker ≤ center (SU (unitaryInvolution F 2 f) (2 * 2 + 1)))
    (hN1 : ∀ x : StatedSp 2 K, Φ (ctuEmbed 1 le_rfl (unitaryInvolution F 2 f) ι hι x) =
      ((e.symm ((complSpEquiv 0 x : complSp K 0) : StatedSp 3 K) : L) : G))
    (hN3 : ∀ y, t * Φ y * t⁻¹ = Φ (ctuaBarAut (unitaryInvolution F 2 f)
      (unitaryInvolution_involutive hF) (2 * 2 + 1) y)) :
    pieceCore e ({2} : Finset (Fin 3)) ≤
      centralizer (modelToG e (simpleRootSL2 K (0 : Fin 3)) : Set G) := by
  classical
  have hK : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have hσ := unitaryInvolution_involutive hF
  have hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer L) :=
    isSolvable_outer_of_isCyclic (isCyclic_outer_of_mulEquiv_statedSp (by norm_num) e)
  set J := modelToG e (longRootSp2 K 3 (2 : Fin 3)) with hJdef
  set J0 := modelToG e (simpleRootSL2 K (0 : Fin 3)) with hJ0def
  have hJ0J : J0 ≤ centralizer (J : Set G) :=
    modelToG_simpleRootSL2_zero_le_centralizer_longRootSp2_two e
  have hJJ0 : J ≤ centralizer (J0 : Set G) := le_centralizer_iff.1 hJ0J
  have hM2 := pieceCore_two_eq_map_ctuBlock_of_uodd hK e hF hf Φ hrange hker hN1
  have hσσ : unitaryInvolution F 2 f * unitaryInvolution F 2 f = 1 :=
    RingEquiv.ext fun c => hσ c
  obtain ⟨ω, hω⟩ := LinearPilot.exists_trace_one_of_involution
    (usb_unitaryInvolution_ne_one hF) hσσ
  have hyB := uOddHeis_mem_ctuBlock hσ hω
  set y := uOddHeis hσ hω with hydef
  set z : G := ((e.symm (siegDiag K 2 1) : L) : G) with hzdef
  have hz : Φ (y⁻¹ * y⁻¹) = z := by
    rw [hydef, uOddHeis_inv_sq_eq_ctuEmbed hσ hω hι, hN1, coe_complSpEquiv_siegDiag_one]
  set g : G := (Φ y)⁻¹ with hgdef
  have hgz : g * z = z * g := by
    rw [hgdef, ← hz, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    group
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hg : g⁻¹ * t * g = t * z := by
    have h3 : t * Φ y * t⁻¹ = (Φ y)⁻¹ := by rw [hN3, ctuaBarAut_uOddHeis, map_inv]
    rw [hgdef, inv_inv, ← hz, map_mul, map_inv]
    calc Φ y * t * (Φ y)⁻¹ = Φ y * t * (t * Φ y * t⁻¹) := by rw [h3]
      _ = Φ y * (t * t) * Φ y * t⁻¹ := by group
      _ = (t * t) * Φ y * (t⁻¹ * t) * Φ y * t⁻¹ := by rw [htt, inv_mul_cancel]; group
      _ = t * (t * Φ y * t⁻¹) * (t * Φ y * t⁻¹) := by group
      _ = t * ((Φ y)⁻¹ * (Φ y)⁻¹) := by rw [h3, mul_assoc]
  have hgM : g ∈ pieceCore e ({2} : Finset (Fin 3)) := by
    rw [hM2, hgdef, ← map_inv]
    exact ⟨_, inv_mem hyB, rfl⟩
  have hT02 : modelToG e (leviTorusSp K ({0, 2} : Finset (Fin 3))) ≤
      modelToG e (leviTorusSp K ({2} : Finset (Fin 3))) :=
    UnitaryPilot.modelToG_mono e (leviTorusSp_anti (by decide))
  have hgY : g ∈ centralizer (modelToG e (leviTorusSp K ({0, 2} : Finset (Fin 3))) : Set G) :=
    centralizer_le hT02 (centralizerPerfectCore_le_centralizer _ hgM)
  have hJY : J ≤ centralizer (modelToG e (leviTorusSp K ({0, 2} : Finset (Fin 3))) : Set G) := by
    rw [hJdef, ← simpleRootSL2_of_not_lt (by decide)]
    exact UnitaryPilot.modelToG_le_centralizer e
      (simpleRootSL2_le_centralizer_leviTorusSp (by decide))
  have hJ0Y : J0 ≤ centralizer (modelToG e (leviTorusSp K ({0, 2} : Finset (Fin 3))) : Set G) :=
    UnitaryPilot.modelToG_le_centralizer e (simpleRootSL2_le_centralizer_leviTorusSp (by decide))
  set φ' : StatedSp 3 K →* G :=
    (MulAut.conj g⁻¹).toMonoidHom.comp (L.subtype.comp e.symm.toMonoidHom) with hφ'def
  have hφ' : Function.Injective φ' :=
    (MulAut.conj g⁻¹).injective.comp (L.subtype_injective.comp e.symm.injective)
  have hφ'r : φ'.range = CFSG.conjugate L g := by
    rw [hφ'def, MonoidHom.range_comp, EPilot.range_subtype_comp_mulEquiv_symm]
    rfl
  have hφ'z : φ' (siegDiag K 2 1) = z := by
    change g⁻¹ * z * g⁻¹⁻¹ = z
    rw [((show Commute g z from hgz).inv_left).eq, mul_inv_cancel_right]
  set j : SL(2, K) →* G := φ'.comp (longBlock K 3 (2 : Fin 3)) with hjdef
  have := LinearPilot.isSimpleGroup_specialLinearGroup_two (K := K) hK
  have := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK
  have hj : ∀ A, j A = g⁻¹ * ((e.symm (longBlock K 3 2 A) : L) : G) * g := by
    intro A
    change g⁻¹ * _ * g⁻¹⁻¹ = _
    rw [inv_inv]
    rfl
  have hjJ : ∀ A, ((e.symm (longBlock K 3 2 A) : L) : G) ∈ J := fun A =>
    symm_mem_modelToG e ⟨A, rfl⟩
  have hSt : j.range ≤ centralizer ({g⁻¹ * t * g} : Set G) := by
    rintro _ ⟨A, rfl⟩
    rw [mem_centralizer_singleton_iff, hj]
    have hyt : ((e.symm (longBlock K 3 2 A) : L) : G) * t =
        t * ((e.symm (longBlock K 3 2 A) : L) : G) :=
      mem_centralizer_iff.1 htC _ (e.symm _).2
    calc g⁻¹ * ((e.symm (longBlock K 3 2 A) : L) : G) * g * (g⁻¹ * t * g) =
        g⁻¹ * (((e.symm (longBlock K 3 2 A) : L) : G) * t) * g := by group
      _ = g⁻¹ * (t * ((e.symm (longBlock K 3 2 A) : L) : G)) * g := by rw [hyt]
      _ = g⁻¹ * t * g * (g⁻¹ * ((e.symm (longBlock K 3 2 A) : L) : G) * g) := by group
  have hSY : j.range ≤
      centralizer (modelToG e (leviTorusSp K ({0, 2} : Finset (Fin 3))) : Set G) := by
    rintro _ ⟨A, rfl⟩
    rw [mem_centralizer_iff]
    intro w hw
    rw [hj]
    have h1 : w * g = g * w := mem_centralizer_iff.1 hgY w hw
    have h1' : w * g⁻¹ = g⁻¹ * w := (show Commute w g from h1).inv_right.eq
    have h2 : w * ((e.symm (longBlock K 3 2 A) : L) : G) =
        ((e.symm (longBlock K 3 2 A) : L) : G) * w :=
      mem_centralizer_iff.1 (hJY (hjJ A)) w hw
    calc w * (g⁻¹ * ((e.symm (longBlock K 3 2 A) : L) : G) * g) =
        g⁻¹ * (w * ((e.symm (longBlock K 3 2 A) : L) : G)) * g := by
          rw [← mul_assoc, ← mul_assoc, h1']
          group
      _ = g⁻¹ * ((e.symm (longBlock K 3 2 A) : L) : G) * (w * g) := by rw [h2]; group
      _ = g⁻¹ * ((e.symm (longBlock K 3 2 A) : L) : G) * g * w := by rw [h1]; group
  have hzS : z ∈ j.range := by
    refine ⟨LinearPilot.upperUnit 1, ?_⟩
    rw [hj, ← siegDiag_eq_longBlock, ← hzdef, mul_assoc, ← hgz, inv_mul_cancel_left]
  have hBperf : ⁅J0, J0⁆ = J0 := by
    rw [hJ0def, UnitaryPilot.modelToG_def, ← map_commutator, ← map_commutator,
      commutator_simpleRootSL2_eq_of_four_le hK 0]
  have hBL : J0 ≤ L := by
    rw [hJ0def, UnitaryPilot.modelToG_def]
    exact map_subtype_le _
  have hBz : J0 ≤ centralizer ({z} : Set G) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    have hzJ : z ∈ J := symm_mem_modelToG e (siegDiag_mem_longRootSp2 2 1)
    exact (mem_centralizer_iff.1 (hJ0J hx) z hzJ).symm
  have hcore := le_centralizer_of_conj_eq_mul_three_two hset.standardSetting hOut hK e htC ht hg
    hφ' hφ'r hφ'z (LinearPilot.commutator_range_eq_self_of_isPerfect j)
    (LinearPilot.eq_bot_or_eq_top_of_normal_range j) hSt hSY hzS hBperf hBL hBz hJ0Y
  set H₀ : Subgroup (SU (unitaryInvolution F 2 f) (2 * 2 + 1)) :=
    (centralizer (J0 : Set G)).comap Φ with hH₀
  set E := ctuBlockEquiv (unitaryInvolution F 2 f) le_rfl (0 : Fin (1 + 1)) with hE
  set H₃ : Subgroup (SU (unitaryInvolution F 2 f) 3) :=
    (H₀.subgroupOf (ctuBlock (unitaryInvolution F 2 f) 1 ({0} : Finset (Fin (1 + 1))))).map
      E.toMonoidHom with hH₃
  have hfix := ctuf_fix_iff hKc hF (by omega) hι
  have hK2 : ∃ r : K, r ≠ 0 ∧ r ≠ 1 := by
    obtain ⟨κ, hκ⟩ := exists_units_mul_self_ne_one_of_four_le hK
    exact ⟨κ, κ.ne_zero, fun h => hκ (by rw [show κ = 1 from Units.ext h, one_mul])⟩
  have hA : ∀ s : SL(2, K), ug3Sl _ ι hι s ∈ H₃ := by
    intro s
    refine ⟨⟨_, ctuEmbed_complSp_longBlock_mem hι s⟩, ?_,
      ctuBlockEquiv_ctuEmbed_complSp_longBlock hι s⟩
    change Φ (ctuEmbed 1 le_rfl _ ι hι ((complSpEquiv (0 : Fin 2) (longBlock K 1 0 s) :
      complSp K 0) : StatedSp 2 K)) ∈ centralizer (J0 : Set G)
    rw [hN1, coe_complSpEquiv_complSpEquiv_longBlock]
    exact hJJ0 (hjJ s)
  have hyE : E ⟨y, hyB⟩ = ug3Heis hσ (ug3_valid_y hω) := ctuBlockEquiv_uOddHeis hσ hω
  have hAy : ∀ s : SL(2, K), ug3Heis hσ (ug3_valid_y hω) * ug3Sl _ ι hι s *
      (ug3Heis hσ (ug3_valid_y hω))⁻¹ ∈ H₃ := by
    intro s
    rw [← hyE, ← ctuBlockEquiv_ctuEmbed_complSp_longBlock hι s, ← map_inv, ← map_mul,
      ← map_mul]
    refine ⟨_, ?_, rfl⟩
    change Φ (y * ctuEmbed 1 le_rfl _ ι hι ((complSpEquiv (0 : Fin 2) (longBlock K 1 0 s) :
      complSp K 0) : StatedSp 2 K) * y⁻¹) ∈ centralizer (J0 : Set G)
    rw [map_mul, map_mul, map_inv, hN1, coe_complSpEquiv_complSpEquiv_longBlock]
    have e1 : Φ y * ((e.symm (longBlock K 3 2 s) : L) : G) * (Φ y)⁻¹ = j s := by
      rw [hj, hgdef, inv_inv]
    rw [e1]
    exact hcore ⟨s, rfl⟩
  have htop : H₃ = ⊤ := ug3_eq_top hF ι hι hfix hK2 hω hA hAy
  rw [hM2]
  rintro _ ⟨x, hx, rfl⟩
  have hmem : E ⟨x, hx⟩ ∈ H₃ := htop ▸ Subgroup.mem_top _
  obtain ⟨x', hx', hxx⟩ := hmem
  have hx'' : x' = ⟨x, hx⟩ := E.injective hxx
  subst hx''
  exact hx'

end Orth

section Rank

variable {F : Type} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c)

theorem usb_h0 : (⟨0, by norm_num⟩ : Fin ((2 * 2 + 1) / 2)).val + 1 < (2 * 2 + 1) / 2 := by
  norm_num

@[expose] noncomputable def usbU (c : F) : SU σ (2 * 2 + 1) :=
  rootHom σ hσ (lowIdx_ne_succ usb_h0) (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _)
    (Multiplicative.ofAdd c)

@[expose] noncomputable def usbL (c : F) : SU σ (2 * 2 + 1) :=
  rootHom σ hσ (lowIdx_ne_succ usb_h0).symm (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _)
    (Multiplicative.ofAdd c)

theorem usbU_mem_rootGroup (c : F) : usbU hσ c ∈ rootGroup σ hσ (2 * 2 + 1) (Pi.single
    (⟨0, by norm_num⟩ : Fin ((2 * 2 + 1) / 2)) 1) :=
  rootHom_mem hσ (lowIdx_ne_succ usb_h0) (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _)
    (lowIdx_ne_rev _ _) (toStd_short usb_h0).symm _

theorem usbL_mem_rootGroup (c : F) : usbL hσ c ∈ rootGroup σ hσ (2 * 2 + 1) (-Pi.single
    (⟨0, by norm_num⟩ : Fin ((2 * 2 + 1) / 2)) 1) :=
  rootHom_mem hσ (lowIdx_ne_succ usb_h0).symm (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _)
    (lowIdx_ne_rev _ _) (toStd_short_neg usb_h0).symm _

theorem usbU_mem (c : F) : usbU hσ c ∈ rankOne (rootGroup σ hσ (2 * 2 + 1))
    (⟨0, by norm_num⟩ : Fin ((2 * 2 + 1) / 2)) :=
  Subgroup.mem_sup_left (usbU_mem_rootGroup hσ c)

theorem usbL_mem (c : F) : usbL hσ c ∈ rankOne (rootGroup σ hσ (2 * 2 + 1))
    (⟨0, by norm_num⟩ : Fin ((2 * 2 + 1) / 2)) :=
  Subgroup.mem_sup_right (usbL_mem_rootGroup hσ c)

@[expose] noncomputable def usbT (c : F) : SU σ (2 * 2 + 1) :=
  CFSG.LieType.Universal.Unitary.shortTorus σ hσ (lowIdx_ne_succ usb_h0) (lowIdx_ne_rev _ _)
    (lowIdx_ne_rev _ _) c

theorem usbT_mem (c : F) : usbT hσ c ∈ rankOne (rootGroup σ hσ (2 * 2 + 1))
    (⟨0, by norm_num⟩ : Fin ((2 * 2 + 1) / 2)) := by
  rw [usbT, CFSG.LieType.Universal.Unitary.shortTorus_def,
    CFSG.LieType.Universal.Unitary.shortWeyl_def, CFSG.LieType.Universal.Unitary.shortWeyl_def]
  exact mul_mem (mul_mem (mul_mem (usbU_mem hσ _) (usbL_mem hσ _)) (usbU_mem hσ _))
    (mul_mem (mul_mem (usbU_mem hσ _) (usbL_mem hσ _)) (usbU_mem hσ _))

theorem coe_usbT {c : F} (hc : c ≠ 0) :
    ((usbT hσ c : GL (Fin (2 * 2 + 1)) F) : Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) F) =
      diagonal (shortTorusFun σ (lowIdx (n := 2 * 2 + 1) ⟨0, by norm_num⟩)
        (lowIdx (n := 2 * 2 + 1) ⟨0 + 1, usb_h0⟩) c) :=
  CFSG.LieType.Universal.Unitary.coe_shortTorus σ hσ _ _ _ (lowIdx_ne_rev _ _) hc

variable {hσ}

theorem rankOneShortEquiv_usbU (c : F) :
    CFSG.LieType.Steinberg.rankOneShortEquiv (hσ := hσ) usb_h0 ⟨usbU hσ c, usbU_mem hσ c⟩ =
      LinearPilot.upperUnit c := by
  apply Subtype.ext
  change SUExtras.toBlock (lowIdx _) (lowIdx _) (mat σ (2 * 2 + 1) (usbU hσ c)) = _
  rw [toBlock_of_mem_pos usb_h0 (usbU_mem_rootGroup hσ c), LinearPilot.coe_upperUnit, mat_apply,
    usbU, coe_rootHom, toAdd_ofAdd, rootMatrix_apply_pq (lowIdx_ne_succ usb_h0) (lowIdx_ne_rev _ _)]

theorem rankOneShortEquiv_usbL (c : F) :
    CFSG.LieType.Steinberg.rankOneShortEquiv (hσ := hσ) usb_h0 ⟨usbL hσ c, usbL_mem hσ c⟩ =
      LinearPilot.lowerUnit c := by
  apply Subtype.ext
  change SUExtras.toBlock (lowIdx _) (lowIdx _) (mat σ (2 * 2 + 1) (usbL hσ c)) = _
  rw [toBlock_of_mem_neg usb_h0 (usbL_mem_rootGroup hσ c), LinearPilot.coe_lowerUnit, mat_apply,
    usbL, coe_rootHom, toAdd_ofAdd,
    rootMatrix_apply_pq (lowIdx_ne_succ usb_h0).symm (lowIdx_ne_rev _ _)]

theorem rankOneShortEquiv_usbT (c : Fˣ) :
    CFSG.LieType.Steinberg.rankOneShortEquiv (hσ := hσ) usb_h0 ⟨usbT hσ c, usbT_mem hσ c⟩ =
      LinearPilot.diagUnit c := by
  apply Subtype.ext
  change SUExtras.toBlock (lowIdx _) (lowIdx _) (mat σ (2 * 2 + 1) (usbT hσ c)) = _
  rw [mat_apply, coe_usbT hσ c.ne_zero, LinearPilot.coe_diagUnit]
  have hne : (lowIdx (n := 2 * 2 + 1) (0 : Fin ((2 * 2 + 1) / 2))) ≠ lowIdx 1 := fun h => by
    simp [lowIdx] at h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SUExtras.toBlock, shortTorusFun, diagonal_apply_ne _ hne, Ne.symm hne]

end Rank

section Diff

open CFSG.LieType.Universal.Symplectic.SpExtras (elt mat_elt E)

variable {N ε : ℕ} {K F : Type} [Field K] [Field F] [CharP K 2] {hε : ε ≤ 1} {σ : F ≃+* F}
  {ι : K →+* F} {hι : ∀ c, σ (ι c) = ι c}

theorem usb_coe_ctuEmbed_elt_difference {p p' : Fin N} (hpp : p ≠ p') (c : K) :
    (((ctuEmbed ε hε σ ι hι (elt (.difference p p' hpp) c) : SU σ (2 * N + ε)) :
      GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) =
        1 + single (ctuCoord N ε (Sum.inl (Sum.inl p))) (ctuCoord N ε (Sum.inl (Sum.inl p')))
          (ι c) - single (ctuCoord N ε (Sum.inl (Sum.inr p'))) (ctuCoord N ε (Sum.inl (Sum.inr p)))
            (ι c) := by
  ext a b
  obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective a
  obtain ⟨w', rfl⟩ := (ctuCoord N ε).surjective b
  rw [ctuEmbed_apply_ctuCoord, mat_elt, Matrix.sub_apply, Matrix.add_apply, single_apply,
    single_apply, one_apply]
  simp only [(ctuCoord N ε).injective.eq_iff]
  rcases w with u | i <;> rcases w' with v | j
  · rw [fromBlocks_apply₁₁, map_apply, Matrix.add_apply, Matrix.smul_apply, one_apply]
    simp only [E, Matrix.sub_apply, single_apply, Sum.inl.injEq, smul_eq_mul]
    split_ifs <;> simp_all [sub_eq_add_neg]
  · rw [fromBlocks_apply₁₂, Matrix.zero_apply]
    simp
  · rw [fromBlocks_apply₂₁, Matrix.zero_apply]
    simp
  · rw [fromBlocks_apply₂₂, one_apply]
    simp

theorem usb_ctuEmbed_elt_difference_eq_rootHom (hσ : ∀ c, σ (σ c) = c) {p p' : Fin N}
    (hpp : p ≠ p') {i j : Fin (2 * N + ε)} (hi : ctuCoord N ε (Sum.inl (Sum.inl p)) = i)
    (hj : ctuCoord N ε (Sum.inl (Sum.inl p')) = j) (hij : i ≠ j) (hii : i ≠ Fin.rev i)
    (hjj : j ≠ Fin.rev j) (c : K) :
    ctuEmbed ε hε σ ι hι (elt (.difference p p' hpp) c) =
      rootHom σ hσ hij hii hjj (Multiplicative.ofAdd (ι c)) := by
  subst hi hj
  apply Subtype.ext
  apply Units.ext
  rw [usb_coe_ctuEmbed_elt_difference, coe_rootHom, toAdd_ofAdd, rootMatrix, hι, ctuCoord_rev hε,
    ctuCoord_rev hε, ctuPar_inl, ctuPar_inl, par_inl, par_inl]

end Diff

section Pair

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite K] in
theorem pieceCore_zero_le_centralizer_of_uodd (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K)
    {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
    (hf : 2 ≤ f) {ι : K →+* F} {hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c}
    (Φ : SU (unitaryInvolution F 2 f) (2 * 2 + 1) →* G) (hrange : Φ.range = neighbourCore e 2)
    (hker : Φ.ker ≤ center (SU (unitaryInvolution F 2 f) (2 * 2 + 1)))
    (hN1 : ∀ x : StatedSp 2 K, Φ (ctuEmbed 1 le_rfl (unitaryInvolution F 2 f) ι hι x) =
      ((e.symm ((complSpEquiv 2 x : complSp K 2) : StatedSp 3 K) : L) : G))
    (hJ0 : modelToG e (simpleRootSL2 K (0 : Fin 3)) ≤
      centralizer (pieceCore e ({2} : Finset (Fin 3)) : Set G)) :
    pieceCore e ({0} : Finset (Fin 3)) ≤
      centralizer (pieceCore e ({2} : Finset (Fin 3)) : Set G) := by
  have hσ := unitaryInvolution_involutive hF
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hK2 : ∃ r : K, r ≠ 0 ∧ r ≠ 1 := by
    obtain ⟨κ, hκ⟩ := exists_units_mul_self_ne_one_of_four_le hK
    exact ⟨κ, κ.ne_zero, fun h => hκ (by rw [show κ = 1 from Units.ext h, one_mul])⟩
  set L₀ := rankOne (rootGroup (unitaryInvolution F 2 f) hσ (2 * 2 + 1))
    (⟨0, by norm_num⟩ : Fin ((2 * 2 + 1) / 2)) with hL₀
  have hY : ((siegelTorus K 2).map (ctuEmbed 1 le_rfl (unitaryInvolution F 2 f) ι hι)).map Φ =
      modelToG e ((siegelTorus K 2).map (complSpHom (K := K) 2)) := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      change Φ (ctuEmbed 1 le_rfl (unitaryInvolution F 2 f) ι hι x) ∈ _
      rw [hN1]
      exact symm_mem_modelToG e ⟨x, hx, rfl⟩
    · intro hy
      obtain ⟨_, ⟨x, hx, rfl⟩, hxy⟩ := (UnitaryPilot.mem_modelToG e).1 hy
      refine ⟨_, ⟨x, hx, rfl⟩, ?_⟩
      change Φ (ctuEmbed 1 le_rfl (unitaryInvolution F 2 f) ι hι x) = y
      rw [hN1, ← hxy]
      rfl
  have hM0 : pieceCore e ({0} : Finset (Fin 3)) = L₀.map Φ := by
    rw [pieceCore_eq_map_perfectCore_centralizer e hK (k := 2) (by decide) leviTorusSp_zero_le_sup
      map_siegelTorus_two_le_leviTorusSp_zero Φ hrange hker _ hY,
      perfectCore_centralizer_ctuEmbed_siegelTorus_eq hF hf hK2]
  set M := pieceCore e ({2} : Finset (Fin 3)) with hMdef
  set H₀ : Subgroup (SU (unitaryInvolution F 2 f) (2 * 2 + 1)) :=
    (centralizer (M : Set G)).comap Φ with hH₀
  have hdiag : ∀ d : SU (unitaryInvolution F 2 f) (2 * 2 + 1),
      (∀ i j, i ≠ j → ((d : GL (Fin (2 * 2 + 1)) F) : Matrix (Fin (2 * 2 + 1))
        (Fin (2 * 2 + 1)) F) i j = 0) → ∀ x ∈ H₀, d * x * d⁻¹ ∈ H₀ := by
    intro d hd x hx
    have hdY : Φ d ∈ centralizer (modelToG e (leviTorusSp K ({2} : Finset (Fin 3))) : Set G) := by
      rw [mem_centralizer_iff]
      intro w hw
      obtain ⟨_, ⟨u, hu, rfl⟩, rfl⟩ := (UnitaryPilot.mem_modelToG e).1 hw
      have hu2 : u 2 = 1 := (hu 2 (Finset.mem_singleton_self 2)).2 (by decide)
      have hw' : ((e.symm (diagSp K 3 u) : L) : G) =
          Φ (ctuEmbed 1 le_rfl (unitaryInvolution F 2 f) ι hι (diagSp K 2 ![u 0, u 1])) := by
        rw [hN1, coe_complSpEquiv_two_diagSp]
        congr 3
        funext i
        fin_cases i <;> simp [hu2]
      change ((e.symm (diagSp K 3 u) : L) : G) * Φ d = Φ d * ((e.symm (diagSp K 3 u) : L) : G)
      rw [hw', ← map_mul, ← map_mul]
      congr 1
      apply mat_injective
      rw [map_mul, map_mul, mat_ctuEmbed_diagSp]
      have hdd : mat _ (2 * 2 + 1) d = diagonal fun i => mat _ (2 * 2 + 1) d i i := by
        ext i j
        by_cases hij : i = j
        · subst hij
          simp
        · rw [mat_apply, hd i j hij, diagonal_apply_ne _ hij]
      rw [hdd, diagonal_mul_diagonal, diagonal_mul_diagonal]
      congr 1
      funext i
      ring
    have hdN : Φ d ∈ normalizer (M : Set G) :=
      LinearPilot.mem_normalizer_centralizerPerfectCore (centralizer_le_normalizer _ hdY)
    change Φ (d * x * d⁻¹) ∈ centralizer (M : Set G)
    rw [map_mul, map_mul, map_inv, mem_centralizer_iff]
    intro m hm
    have hm' : (Φ d)⁻¹ * m * (Φ d)⁻¹⁻¹ ∈ M := (mem_normalizer_iff.1 (inv_mem hdN) m).1 hm
    have hc := mem_centralizer_iff.1 hx _ hm'
    rw [inv_inv] at hc
    calc m * (Φ d * Φ x * (Φ d)⁻¹) = Φ d * ((Φ d)⁻¹ * m * Φ d * Φ x) * (Φ d)⁻¹ := by group
      _ = Φ d * (Φ x * ((Φ d)⁻¹ * m * Φ d)) * (Φ d)⁻¹ := by rw [hc]
      _ = Φ d * Φ x * (Φ d)⁻¹ * m := by group
  have hJ : ∀ A : SL(2, K), ctuEmbed 1 le_rfl (unitaryInvolution F 2 f) ι hι
      (shortBlock K (show (0 : Fin 2) ≠ 1 by decide) A) ∈ H₀ := by
    intro A
    change Φ (ctuEmbed 1 le_rfl (unitaryInvolution F 2 f) ι hι
      (shortBlock K (show (0 : Fin 2) ≠ 1 by decide) A)) ∈ centralizer (M : Set G)
    rw [hN1, coe_complSpEquiv_apply]
    have h1 := congrArg (fun φ : SL(2, K) →* StatedSp 3 K => φ A)
      (spEmbed_comp_shortBlock_of_injective (K := K)
        (Fin.succAbove_right_injective (p := (2 : Fin 3)))
        (show (0 : Fin 2) ≠ 1 by decide))
    simp only [MonoidHom.comp_apply] at h1
    rw [h1]
    refine hJ0 (symm_mem_modelToG e ⟨A, ?_⟩)
    rw [simpleRootHom_of_lt (by decide)]
    rfl
  have hU : ∀ c : K, usbU hσ (ι c) ∈ H₀ := by
    intro c
    have e1 := usb_ctuEmbed_elt_difference_eq_rootHom (ε := 1) (hε := le_rfl) (ι := ι) (hι := hι) hσ
      (show (0 : Fin 2) ≠ 1 by decide) (i := lowIdx (n := 2 * 2 + 1) ⟨0, by norm_num⟩)
      (j := lowIdx (n := 2 * 2 + 1) ⟨0 + 1, usb_h0⟩) (Fin.ext rfl) (Fin.ext rfl)
      (lowIdx_ne_succ usb_h0) (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _) c
    have e2 : usbU hσ (ι c) = ctuEmbed 1 le_rfl (unitaryInvolution F 2 f) ι hι
        (shortBlock K (show (0 : Fin 2) ≠ 1 by decide) (sl2Upper c)) := by
      rw [shortBlock_sl2Upper, e1]
      rfl
    rw [e2]
    exact hJ _
  have hL : ∀ c : K, usbL hσ (ι c) ∈ H₀ := by
    intro c
    have e1 := usb_ctuEmbed_elt_difference_eq_rootHom (ε := 1) (hε := le_rfl) (ι := ι) (hι := hι) hσ
      (show (1 : Fin 2) ≠ 0 by decide) (i := lowIdx (n := 2 * 2 + 1) ⟨0 + 1, usb_h0⟩)
      (j := lowIdx (n := 2 * 2 + 1) ⟨0, by norm_num⟩) (Fin.ext rfl) (Fin.ext rfl)
      (lowIdx_ne_succ usb_h0).symm (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _) c
    have e2 : usbL hσ (ι c) = ctuEmbed 1 le_rfl (unitaryInvolution F 2 f) ι hι
        (shortBlock K (show (0 : Fin 2) ≠ 1 by decide) (sl2Lower c)) := by
      rw [shortBlock_sl2Lower, e1]
      rfl
    rw [e2]
    exact hJ _
  set eR := CFSG.LieType.Steinberg.rankOneShortEquiv (hσ := hσ) (n := 2 * 2 + 1)
    (k := ⟨0, by norm_num⟩) usb_h0 with heR
  set Hs : Subgroup SL(2, F) := (H₀.subgroupOf L₀).comap eR.symm.toMonoidHom with hHs
  have hmemHs : ∀ g : L₀, eR g ∈ Hs ↔ (g : SU (unitaryInvolution F 2 f) (2 * 2 + 1)) ∈ H₀ := by
    intro g
    change eR.symm (eR g) ∈ H₀.subgroupOf L₀ ↔ _
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hUs : LinearPilot.upperUnit 1 ∈ Hs := by
    rw [← rankOneShortEquiv_usbU (hσ := hσ) (1 : F), hmemHs]
    have h := hU 1
    rwa [map_one] at h
  have hLs : LinearPilot.lowerUnit 1 ∈ Hs := by
    rw [← rankOneShortEquiv_usbL (hσ := hσ) (1 : F), hmemHs]
    have h := hL 1
    rwa [map_one] at h
  have hWs : LinearPilot.weylUnit ∈ Hs := by
    have hw : (LinearPilot.weylUnit : SL(2, F)) =
        LinearPilot.upperUnit 1 * LinearPilot.lowerUnit 1 * LinearPilot.upperUnit 1 := by
      ext i j
      simp only [Matrix.SpecialLinearGroup.coe_mul, LinearPilot.coe_upperUnit,
        LinearPilot.coe_lowerUnit, LinearPilot.coe_weylUnit, Matrix.mul_fin_two]
      fin_cases i <;> fin_cases j <;> simp <;> grind
    rw [hw]
    exact mul_mem (mul_mem hUs hLs) hUs
  have hTs : ∀ (α : Fˣ), ∀ x ∈ Hs, LinearPilot.diagUnit α * x * (LinearPilot.diagUnit α)⁻¹ ∈ Hs := by
    intro α x hx
    obtain ⟨g, rfl⟩ := eR.surjective x
    rw [← rankOneShortEquiv_usbT (hσ := hσ) α, ← map_inv, ← map_mul, ← map_mul, hmemHs]
    rw [hmemHs] at hx
    exact hdiag (usbT hσ α) (fun i j hij => by
      rw [coe_usbT hσ α.ne_zero, diagonal_apply_ne _ hij]) _ hx
  have htop := LinearPilot.eq_top_of_upperUnit_one_mem_of_conj_mem hUs hWs hTs
  rw [hM0]
  rintro _ ⟨g, hg, rfl⟩
  have h1 : eR ⟨g, hg⟩ ∈ Hs := htop ▸ Subgroup.mem_top _
  exact (hmemHs ⟨g, hg⟩).1 h1

end Pair

theorem spThreeUnitaryOddOrthInput_holds :
    SpThreeUnitaryOddOrthInput := by
  intro G _ _ L hset f K _ _ _ hKc hf e t ht hKt hroot hstd
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hK : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  obtain ⟨F₀, _, _, _, hF₀, ι₀, hι₀, Φ₀, hr₀, hk₀, hN1₀, hN3₀⟩ :=
    spThreeUOddNormalized_of_standard hset hKc hf e htC ht 0 (hroot 0) hstd
  obtain ⟨F₂, _, _, _, hF₂, ι₂, hι₂, Φ₂, hr₂, hk₂, hN1₂, -⟩ :=
    spThreeUOddNormalized_of_standard hset hKc hf e htC ht 2 (hroot 2) hstd
  have h1 := pieceCore_two_le_centralizer_simpleRootSL2_zero_uodd hset hKc hf e htC ht hF₀ Φ₀ hr₀
    hk₀ (fun x => hN1₀ x) hN3₀
  have h2 := pieceCore_zero_le_centralizer_of_uodd hK e hF₂ hf Φ₂ hr₂ hk₂ (fun x => hN1₂ x)
    (le_centralizer_iff.1 h1)
  intro a ha b hb
  exact (mem_centralizer_iff.1 (h2 ha) b hb).symm

end CFSG.SeitzReduction.SymplecticPilot

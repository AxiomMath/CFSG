module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighD4OddSplit
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriA2Tau

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighD4Odd

open Matrix CFSG.RankThree.PartTwo
open scoped MatrixGroups commutatorElement

section Minus

set_option linter.unusedSectionVars false

open CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2
  CFSG.LieType.Steinberg.TwistedD4 CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
  CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit
  CFSG.RankThree.PartOne.CTP CFSG.HardMathSupport.Lang.D4Three

variable {L : Type} [Field L]

noncomputable abbrev xb (a : ℕ) (u : L) : ↥(adjointGroup Tag.D4 L) :=
  CFSG.LieType.Steinberg.Adjoint.xPar (rootOperatorFamily Tag.D4) (d4Root a) u

noncomputable abbrev zB (L : Type) [Field L] : ↥(adjointGroup Tag.D4 L) := zA L

theorem zB_conj_xb {i j : ℕ} {u v : L} (h : zA L * xa i u * (zA L)⁻¹ = xa j v) :
    zB L * xb i u * (zB L)⁻¹ = xb j v :=
  h

theorem bcAd_xb (σ : L →+* L) {k : ℕ} (hk : k < 24) (u : L) : bcAd σ (xb k u) = xb k (σ u) :=
  bcAd_xPar σ (isRoot_d4Root hk) u

theorem diag_conj_xb {t : ↥(adjointGroup Tag.D4 L)} {b : Fin Tag.D4.rank → Lˣ}
    (ht : (t : ModGL Tag.D4 L) = rootDiagUnit Tag.D4 b) {k : ℕ} (hk : k < 24) (u : L) :
    t * xb k u * t⁻¹ = xb k (((rootChar (τ := d4) b (d4Root k) : Lˣ) : L) * u) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ht]
  exact rootDiagUnit_conj_xPar_d4 b (isRoot_d4Root hk) u

theorem rootChar_xxzx (x z : Lˣ) (v : Fin d4.rank → ℤ) :
    rootChar (τ := d4) ![x, x, z, x] v = x ^ (v 0 + v 1 + v 3) * z ^ v 2 := by
  show ∏ i : Fin 4, (![x, x, z, x] : Fin 4 → Lˣ) i ^ v i =
    x ^ (v (0 : Fin 4) + v (1 : Fin 4) + v (3 : Fin 4)) * z ^ v (2 : Fin 4)
  rw [Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  rw [mul_right_comm _ (z ^ _), ← _root_.zpow_add, ← _root_.zpow_add]

theorem d4Graph_zB : d4Graph L 1 (zB L) = zB L := by
  have hz : ((zB L : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L) =
      CFSG.RankThree.Chevalley.trialityOpposition L := coe_zA
  apply Subtype.ext
  rw [coe_d4Graph, pow_one, hz]
  show diagramMap TwistTag.D4 L * CFSG.RankThree.Chevalley.trialityOpposition L *
    (diagramMap TwistTag.D4 L)⁻¹ = CFSG.RankThree.Chevalley.trialityOpposition L
  rw [diagramMap_comm_trialityOpposition, mul_inv_cancel_right]

theorem wN_smul (i : Fin Tag.D4.rank) :
    (wN : WeylGroup Tag.D4) • (Pi.single i 1 : Fin Tag.D4.rank → ℤ) = -Pi.single i 1 := by
  simp only [wN, mul_smul, simple_smul]
  revert i
  decide

theorem wN_eq : (wN : WeylGroup Tag.D4) = CFSG.RankThree.Chevalley.trialityOppositionWeyl :=
  ext_single (τ := TwistTag.D4.tag) fun i =>
    (wN_smul i).trans (CFSG.RankThree.Chevalley.trialityOppositionWeyl_smul _).symm

theorem isMono_zB : IsMono ((zB L : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L) wN := by
  have h1 : ((zB L : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L) =
      CFSG.RankThree.Chevalley.trialityOpposition L := coe_zA
  rw [h1, wN_eq]
  exact ⟨CFSG.RankThree.Chevalley.trialityOpposition_mem_monomialSubgroup,
    CFSG.RankThree.Chevalley.mapsRootLines_trialityOpposition⟩

theorem exists_gTw_nSL_mul_zB_inv (c : Lˣ) : ∃ x z : Lˣ,
    ((gTw (nSL c) * (zB L)⁻¹ : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L) =
      rootDiagUnit Tag.D4 ![x, x, z, x] := by
  have h := (isMono_gTw_nSL (L := L) c).mul (isMono_zB (L := L)).inv
  rw [mul_inv_cancel] at h
  have hT : ((gTw (nSL c) * (zB L)⁻¹ : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L) ∈
      torusGroup Tag.D4 L :=
    IsMono.mem_torusGroup (by rw [Subgroup.coe_mul, Subgroup.coe_inv]; exact h)
  obtain ⟨e, he⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  have hγ := d4Graph_one_torusSub he
  rw [map_mul, map_inv, d4Graph_gTw, d4Graph_zB, he] at hγ
  have hfix : tupAct permM e = e := (rootDiagUnit_injective_D4 hγ).symm
  have he' := eq_tupXZ_of_tupAct_permM hfix
  have h1 : e ⟨1, by decide⟩ = e ⟨0, by decide⟩ := by
    have h := congrFun he' ⟨1, by decide⟩
    rwa [tupXZ_apply, vX_vals.2.1, vZ_vals.2.1, _root_.zpow_one, _root_.zpow_zero,
      mul_one] at h
  have h3 : e ⟨3, by decide⟩ = e ⟨0, by decide⟩ := by
    have h := congrFun he' ⟨3, by decide⟩
    rwa [tupXZ_apply, vX_vals.2.2.2, vZ_vals.2.2.2, _root_.zpow_one, _root_.zpow_zero,
      mul_one] at h
  exact ⟨e ⟨0, by decide⟩, e ⟨2, by decide⟩, he.trans (congrArg _ (tuple_ext4 rfl h1 rfl h3))⟩

theorem zB_conj_rootDiagUnit (b : Fin Tag.D4.rank → Lˣ) :
    ((zB L : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L) * rootDiagUnit Tag.D4 b *
        ((zB L : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L)⁻¹ = rootDiagUnit Tag.D4 b⁻¹ := by
  have hz : ((zB L : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L) =
      CFSG.RankThree.Chevalley.trialityOpposition L := coe_zA
  rw [hz]
  exact CFSG.RankThree.Chevalley.conj_rootDiagUnit_of_smul_eq_neg
    CFSG.RankThree.Chevalley.trialityOpposition_mem_monomialSubgroup
    CFSG.RankThree.Chevalley.weylQuotientHom_trialityOpposition_smul b

theorem zB_mul_zB : zB L * zB L = 1 := by
  apply Subtype.ext
  have h2 := CFSG.RankThree.Chevalley.trialityOpposition_sq (K := L)
  rw [← coe_zA, pow_two] at h2
  exact h2

theorem bcAd_zB (σ : L →+* L) : bcAd σ (zB L) = zB L := by
  apply Subtype.ext
  have h := CFSG.RankThree.Chevalley.baseChangeGL_trialityOpposition (K := L) σ
  rw [← coe_zA] at h
  exact h

theorem frob_xxzx {σ : L →+* L} {c : Lˣ} (hc : Units.map σ.toMonoidHom c = -c) {x z : Lˣ}
    (h : ((gTw (nSL c) * (zB L)⁻¹ : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L) =
      rootDiagUnit Tag.D4 ![x, x, z, x]) :
    Units.map σ.toMonoidHom x = x ∧ Units.map σ.toMonoidHom z = z := by
  set b : Fin Tag.D4.rank → Lˣ := ![x, x, z, x] with hb
  have hσn := bcAd_gTw_nSL σ hc
  have hσw := bcAd_zB (L := L) σ
  have hw2 := zB_mul_zB (L := L)
  have hw' : (zB L)⁻¹ = zB L := inv_eq_of_mul_eq_one_left hw2
  have hwt : zB L * (gTw (nSL c) * (zB L)⁻¹) * (zB L)⁻¹ = (gTw (nSL c) * (zB L)⁻¹)⁻¹ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, h, Subgroup.coe_inv, h,
      zB_conj_rootDiagUnit, rootDiagUnit_inv]
  have key : bcAd σ (gTw (nSL c) * (zB L)⁻¹) = gTw (nSL c) * (zB L)⁻¹ := by
    rw [map_mul, map_inv, hσn, hσw]
    calc (gTw (nSL c))⁻¹ * (zB L)⁻¹ =
        (zB L)⁻¹ * (gTw (nSL c) * (zB L)⁻¹)⁻¹ * (zB L)⁻¹ := by group
      _ = (zB L)⁻¹ * (zB L * (gTw (nSL c) * (zB L)⁻¹) * (zB L)⁻¹) * (zB L)⁻¹ := by rw [hwt]
      _ = gTw (nSL c) * (zB L)⁻¹ * ((zB L)⁻¹ * (zB L)⁻¹) := by group
      _ = gTw (nSL c) * (zB L)⁻¹ := by rw [hw', hw2, mul_one]
  have e1 := coe_bcAd_of_eq_rootDiagUnit σ h
  rw [key, h] at e1
  have e2 := rootDiagUnit_injective_D4 e1
  have e3 : Units.map σ.toMonoidHom (b ⟨0, by decide⟩) = b ⟨0, by decide⟩ := (congrFun e2 _).symm
  have e4 : Units.map σ.toMonoidHom (b ⟨2, by decide⟩) = b ⟨2, by decide⟩ := (congrFun e2 _).symm
  exact ⟨e3, e4⟩

theorem conj_tz_triple {t : ↥(adjointGroup Tag.D4 L)} {b : Fin Tag.D4.rank → Lˣ}
    (ht : (t : ModGL Tag.D4 L) = rootDiagUnit Tag.D4 b) {i j k i' j' k' : ℕ}
    (hi' : i' < 24) (hj' : j' < 24) (hk' : k' < 24) {u v w u' v' w' : L}
    (hzi : zA L * xa i u * (zA L)⁻¹ = xa i' u') (hzj : zA L * xa j v * (zA L)⁻¹ = xa j' v')
    (hzk : zA L * xa k w * (zA L)⁻¹ = xa k' w') :
    t * zB L * (xb i u * xb j v * xb k w) * (t * zB L)⁻¹ =
      xb i' (((rootChar (τ := d4) b (d4Root i') : Lˣ) : L) * u') *
        xb j' (((rootChar (τ := d4) b (d4Root j') : Lˣ) : L) * v') *
          xb k' (((rootChar (τ := d4) b (d4Root k') : Lˣ) : L) * w') := by
  have e : t * zB L * (xb i u * xb j v * xb k w) * (t * zB L)⁻¹ =
      t * (zB L * xb i u * (zB L)⁻¹) * t⁻¹ * (t * (zB L * xb j v * (zB L)⁻¹) * t⁻¹) *
        (t * (zB L * xb k w * (zB L)⁻¹) * t⁻¹) := by group
  rw [e, zB_conj_xb hzi, zB_conj_xb hzj, zB_conj_xb hzk, diag_conj_xb ht hi', diag_conj_xb ht hj',
    diag_conj_xb ht hk']

theorem xb_triple_congr {i j k : ℕ} {a a' b b' c c' : L} (ha : a = a') (hb : b = b')
    (hc : c = c') : xb i a * xb j b * xb k c = xb i a' * xb j b' * xb k c' := by
  subst ha hb hc
  rfl

theorem rootChar_xxzx_val {x z : Lˣ} {b : Fin Tag.D4.rank → Lˣ} (hb : b = ![x, x, z, x])
    {k : ℕ} {m n : ℤ} (hmn : d4Root k 0 + d4Root k 1 + d4Root k 3 = m ∧ d4Root k 2 = n) :
    ((rootChar (τ := d4) b (d4Root k) : Lˣ) : L) = (x : L) ^ m * (z : L) ^ n := by
  subst hb
  rw [rootChar_xxzx, hmn.1, hmn.2, Units.val_mul, Units.val_zpow_eq_zpow_val,
    Units.val_zpow_eq_zpow_val]

theorem frob_frameHom {σ : L →+* L} {ω c x z : Lˣ}
    (hσω : σ (ω : L) = (ω : L) ^ 2) (hσω2 : σ ((ω : L) ^ 2) = ω)
    (h : ((gTw (nSL c) * (zB L)⁻¹ : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L) =
      rootDiagUnit Tag.D4 ![x, x, z, x])
    (Ψ : GL (Fin 3) L →* ↥(adjointGroup Tag.D4 L))
    (h01 : ∀ c', Ψ (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 3) ≠ 1 by decide) c')) =
        xb 0 c' * xb 1 ((ω : L) ^ 2 * c') * xb 3 ((ω : L) * c'))
    (h12 : ∀ c', Ψ (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 3) ≠ 2 by decide) c')) =
        xb 5 c' * xb 7 ((ω : L) * c') * xb 9 (-((ω : L) ^ 2 * c')))
    (h02 : ∀ c', Ψ (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 3) ≠ 2 by decide) c')) = xb 15 (-c') * xb 13 (-c') * xb 12 (-c'))
    (h10 : ∀ c', Ψ (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 3) ≠ 0 by decide) c')) =
        xb 4 c' * xb 6 ((ω : L) * c') * xb 10 ((ω : L) ^ 2 * c'))
    (h21 : ∀ c', Ψ (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection
      (show (2 : Fin 3) ≠ 1 by decide) c')) =
        xb 11 c' * xb 14 ((ω : L) ^ 2 * c') * xb 16 (-((ω : L) * c')))
    (h20 : ∀ c', Ψ (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection
      (show (2 : Fin 3) ≠ 0 by decide) c')) = xb 20 (-c') * xb 18 (-c') * xb 17 (-c'))
    (hD : ∀ a : Lˣ, (Ψ (diagA a) : ModGL Tag.D4 L) = rootDiagUnit Tag.D4 ![a, a, a⁻¹, a])
    (g : GL (Fin 3) L) :
    gTw (nSL c) * bcAd σ (Ψ g) * (gTw (nSL c))⁻¹ = Ψ (thetaD σ ![x, 1, -(x * z)⁻¹] g) := by
  set b : Fin Tag.D4.rank → Lˣ := ![x, x, z, x] with hb
  set t := gTw (nSL c) * (zB L)⁻¹ with ht
  have hn : gTw (nSL c) = t * zB L := by rw [ht, inv_mul_cancel_right]
  set D : Fin 3 → Lˣ := ![x, 1, -(x * z)⁻¹] with hDdef
  have hD0 : ((D 0 : Lˣ) : L) = x := rfl
  have hD1 : ((D 1 : Lˣ) : L) = 1 := rfl
  have hD2 : ((D 2 : Lˣ) : L) = -((x : L)⁻¹ * (z : L)⁻¹) := by
    show (((-(x * z)⁻¹ : Lˣ)) : L) = _
    rw [Units.val_neg, Units.val_inv_eq_inv_val, Units.val_mul, mul_inv]
  have hD0i : (((D 0)⁻¹ : Lˣ) : L) = (x : L)⁻¹ := Units.val_inv_eq_inv_val _
  have hD1i : (((D 1)⁻¹ : Lˣ) : L) = 1 := by
    show (((1 : Lˣ)⁻¹ : Lˣ) : L) = 1
    rw [inv_one, Units.val_one]
  have hD2i : (((D 2)⁻¹ : Lˣ) : L) = -((x : L) * z) := by
    show (((-(x * z)⁻¹ : Lˣ)⁻¹ : Lˣ) : L) = _
    rw [inv_neg, inv_inv, Units.val_neg, Units.val_mul]
  let F₁ : GL (Fin 3) L →* ↥(adjointGroup Tag.D4 L) :=
    (MulAut.conj (gTw (nSL c))).toMonoidHom.comp ((bcAd σ).comp Ψ)
  let F₂ : GL (Fin 3) L →* ↥(adjointGroup Tag.D4 L) := Ψ.comp (thetaD σ D)
  have hF : F₁ = F₂ := by
    refine gl_hom_ext₆ (fun c' => ?_) (fun c' => ?_) (fun c' => ?_) (fun c' => ?_)
      (fun c' => ?_) (fun c' => ?_) (fun a => ?_)
    · show gTw (nSL c) * bcAd σ (Ψ _) * (gTw (nSL c))⁻¹ = Ψ (thetaD σ D _)
      rw [thetaD_transvection, h01, h10, map_mul, map_mul, bcAd_xb σ (by norm_num),
        bcAd_xb σ (by norm_num), bcAd_xb σ (by norm_num), hn,
        conj_tz_triple h (by norm_num) (by norm_num) (by norm_num) (zc_0 _) (zc_1 _) (zc_3 _)]
      refine xb_triple_congr ?_ ?_ ?_
      · rw [rootChar_xxzx_val hb (show d4Root 4 0 + d4Root 4 1 + d4Root 4 3 = -1 ∧
          d4Root 4 2 = 0 by decide), hD1, hD0i]
        simp only [_root_.zpow_neg_one, _root_.zpow_zero]
        ring
      · rw [rootChar_xxzx_val hb (show d4Root 6 0 + d4Root 6 1 + d4Root 6 3 = -1 ∧
          d4Root 6 2 = 0 by decide), hD1, hD0i, map_mul, hσω2]
        simp only [_root_.zpow_neg_one, _root_.zpow_zero]
        ring
      · rw [rootChar_xxzx_val hb (show d4Root 10 0 + d4Root 10 1 + d4Root 10 3 = -1 ∧
          d4Root 10 2 = 0 by decide), hD1, hD0i, map_mul, hσω]
        simp only [_root_.zpow_neg_one, _root_.zpow_zero]
        ring
    · show gTw (nSL c) * bcAd σ (Ψ _) * (gTw (nSL c))⁻¹ = Ψ (thetaD σ D _)
      rw [thetaD_transvection, h12, h21, map_mul, map_mul, bcAd_xb σ (by norm_num),
        bcAd_xb σ (by norm_num), bcAd_xb σ (by norm_num), hn,
        conj_tz_triple h (by norm_num) (by norm_num) (by norm_num) (zc_5 _) (zc_7 _) (zc_9 _)]
      refine xb_triple_congr ?_ ?_ ?_
      · rw [rootChar_xxzx_val hb (show d4Root 11 0 + d4Root 11 1 + d4Root 11 3 = -1 ∧
          d4Root 11 2 = -1 by decide), hD2, hD1i]
        simp only [_root_.zpow_neg_one]
        ring
      · rw [rootChar_xxzx_val hb (show d4Root 14 0 + d4Root 14 1 + d4Root 14 3 = -1 ∧
          d4Root 14 2 = -1 by decide), hD2, hD1i, map_mul, hσω]
        simp only [_root_.zpow_neg_one]
        ring
      · rw [rootChar_xxzx_val hb (show d4Root 16 0 + d4Root 16 1 + d4Root 16 3 = -1 ∧
          d4Root 16 2 = -1 by decide), hD2, hD1i, map_neg, map_mul, hσω2]
        simp only [_root_.zpow_neg_one]
        ring
    · show gTw (nSL c) * bcAd σ (Ψ _) * (gTw (nSL c))⁻¹ = Ψ (thetaD σ D _)
      rw [thetaD_transvection, h02, h20, map_mul, map_mul, bcAd_xb σ (by norm_num),
        bcAd_xb σ (by norm_num), bcAd_xb σ (by norm_num), hn,
        conj_tz_triple h (by norm_num) (by norm_num) (by norm_num) (zc_15 _) (zc_13 _) (zc_12 _)]
      refine xb_triple_congr ?_ ?_ ?_
      · rw [rootChar_xxzx_val hb (show d4Root 20 0 + d4Root 20 1 + d4Root 20 3 = -2 ∧
          d4Root 20 2 = -1 by decide), hD2, hD0i, map_neg]
        simp only [_root_.zpow_neg_one, _root_.zpow_neg, zpow_ofNat]
        ring
      · rw [rootChar_xxzx_val hb (show d4Root 18 0 + d4Root 18 1 + d4Root 18 3 = -2 ∧
          d4Root 18 2 = -1 by decide), hD2, hD0i, map_neg]
        simp only [_root_.zpow_neg_one, _root_.zpow_neg, zpow_ofNat]
        ring
      · rw [rootChar_xxzx_val hb (show d4Root 17 0 + d4Root 17 1 + d4Root 17 3 = -2 ∧
          d4Root 17 2 = -1 by decide), hD2, hD0i, map_neg]
        simp only [_root_.zpow_neg_one, _root_.zpow_neg, zpow_ofNat]
        ring
    · show gTw (nSL c) * bcAd σ (Ψ _) * (gTw (nSL c))⁻¹ = Ψ (thetaD σ D _)
      rw [thetaD_transvection, h10, h01, map_mul, map_mul, bcAd_xb σ (by norm_num),
        bcAd_xb σ (by norm_num), bcAd_xb σ (by norm_num), hn,
        conj_tz_triple h (by norm_num) (by norm_num) (by norm_num) (zc_4 _) (zc_6 _) (zc_10 _)]
      refine xb_triple_congr ?_ ?_ ?_
      · rw [rootChar_xxzx_val hb (show d4Root 0 0 + d4Root 0 1 + d4Root 0 3 = 1 ∧
          d4Root 0 2 = 0 by decide), hD0, hD1i]
        simp only [_root_.zpow_one, _root_.zpow_zero]
        ring
      · rw [rootChar_xxzx_val hb (show d4Root 1 0 + d4Root 1 1 + d4Root 1 3 = 1 ∧
          d4Root 1 2 = 0 by decide), hD0, hD1i, map_mul, hσω]
        simp only [_root_.zpow_one, _root_.zpow_zero]
        ring
      · rw [rootChar_xxzx_val hb (show d4Root 3 0 + d4Root 3 1 + d4Root 3 3 = 1 ∧
          d4Root 3 2 = 0 by decide), hD0, hD1i, map_mul, hσω2]
        simp only [_root_.zpow_one, _root_.zpow_zero]
        ring
    · show gTw (nSL c) * bcAd σ (Ψ _) * (gTw (nSL c))⁻¹ = Ψ (thetaD σ D _)
      rw [thetaD_transvection, h21, h12, map_mul, map_mul, bcAd_xb σ (by norm_num),
        bcAd_xb σ (by norm_num), bcAd_xb σ (by norm_num), hn,
        conj_tz_triple h (by norm_num) (by norm_num) (by norm_num) (zc_11 _) (zc_14 _) (zc_16 _)]
      refine xb_triple_congr ?_ ?_ ?_
      · rw [rootChar_xxzx_val hb (show d4Root 5 0 + d4Root 5 1 + d4Root 5 3 = 1 ∧
          d4Root 5 2 = 1 by decide), hD1, hD2i]
        simp only [_root_.zpow_one]
        ring
      · rw [rootChar_xxzx_val hb (show d4Root 7 0 + d4Root 7 1 + d4Root 7 3 = 1 ∧
          d4Root 7 2 = 1 by decide), hD1, hD2i, map_mul, hσω2]
        simp only [_root_.zpow_one]
        ring
      · rw [rootChar_xxzx_val hb (show d4Root 9 0 + d4Root 9 1 + d4Root 9 3 = 1 ∧
          d4Root 9 2 = 1 by decide), hD1, hD2i, map_neg, map_mul, hσω]
        simp only [_root_.zpow_one]
        ring
    · show gTw (nSL c) * bcAd σ (Ψ _) * (gTw (nSL c))⁻¹ = Ψ (thetaD σ D _)
      rw [thetaD_transvection, h20, h02, map_mul, map_mul, bcAd_xb σ (by norm_num),
        bcAd_xb σ (by norm_num), bcAd_xb σ (by norm_num), hn,
        conj_tz_triple h (by norm_num) (by norm_num) (by norm_num) (zc_20 _) (zc_18 _) (zc_17 _)]
      refine xb_triple_congr ?_ ?_ ?_
      · rw [rootChar_xxzx_val hb (show d4Root 15 0 + d4Root 15 1 + d4Root 15 3 = 2 ∧
          d4Root 15 2 = 1 by decide), hD0, hD2i, map_neg]
        simp only [_root_.zpow_one, zpow_ofNat]
        ring
      · rw [rootChar_xxzx_val hb (show d4Root 13 0 + d4Root 13 1 + d4Root 13 3 = 2 ∧
          d4Root 13 2 = 1 by decide), hD0, hD2i, map_neg]
        simp only [_root_.zpow_one, zpow_ofNat]
        ring
      · rw [rootChar_xxzx_val hb (show d4Root 12 0 + d4Root 12 1 + d4Root 12 3 = 2 ∧
          d4Root 12 2 = 1 by decide), hD0, hD2i, map_neg]
        simp only [_root_.zpow_one, zpow_ofNat]
        ring
    · show gTw (nSL c) * bcAd σ (Ψ _) * (gTw (nSL c))⁻¹ = Ψ (thetaD σ D _)
      rw [thetaD_diagA]
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hn, Subgroup.coe_mul,
        coe_bcAd_of_eq_rootDiagUnit σ (hD a), hD]
      have e1 : ((t : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L) *
          ((zB L : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L) *
          rootDiagUnit Tag.D4 (fun j => Units.map σ.toMonoidHom ((![a, a, a⁻¹, a] :
            Fin Tag.D4.rank → Lˣ) j)) *
          (((t : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L) *
            ((zB L : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L))⁻¹ =
          (t : ModGL Tag.D4 L) * (((zB L : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L) *
            rootDiagUnit Tag.D4 (fun j => Units.map σ.toMonoidHom ((![a, a, a⁻¹, a] :
              Fin Tag.D4.rank → Lˣ) j)) *
            ((zB L : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L)⁻¹) *
          ((t : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L)⁻¹ := by group
      rw [e1, zB_conj_rootDiagUnit, h, rootDiagUnit_commute, mul_inv_cancel_right]
      congr 1
      refine tuple_ext4 ?_ ?_ ?_ ?_ <;> exact Units.ext rfl
  exact DFunLike.congr_fun hF g

theorem twFrob_ιTw {K : Type} [Field K] [Finite K] {K₂ : Type} [Field K₂] [Algebra K K₂]
    (σ : K₂ →+* K₂) (hσ : ∀ x, σ x = x ^ Nat.card K) {Q : SL2 K₂} {c : K₂ˣ}
    (hQc : Matrix.SpecialLinearGroup.map σ Q = Q * nSL c) (h : ↥(adjointGroup Tag.D4 K)) :
    gTw (nSL c) * bcAd σ (ιTw K Q h) * (gTw (nSL c))⁻¹ = ιTw K Q h := by
  have : Fintype K := Fintype.ofFinite K
  have hσg : bcAd σ (gTw Q) = gTw Q * gTw (nSL c) := by rw [bcAd_gTw, hQc, gTw_mul]
  have hσf : σ.comp (algebraMap K K₂) = algebraMap K K₂ := RingHom.ext fun a => by
    rw [RingHom.comp_apply, hσ, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hσh : bcAd σ (bcAd (algebraMap K K₂) h) = bcAd (algebraMap K K₂) h := by
    apply Subtype.ext
    rw [coe_bcAd, coe_bcAd, baseChangeGL_baseChangeGL, hσf]
  rw [ιTw_apply, map_mul, map_mul, map_inv, hσg, hσh]
  group

theorem exists_diag_mul_of_twFrob_fixed {K : Type} [Field K] [Finite K] {K₂ : Type} [Field K₂]
    [Finite K₂] [Algebra K K₂] (σ : K₂ →+* K₂) (hσ : ∀ x, σ x = x ^ Nat.card K) {Q : SL2 K₂}
    {c : K₂ˣ} (hQc : Matrix.SpecialLinearGroup.map σ Q = Q * nSL c)
    {h : ↥(adjointGroup Tag.D4 K₂)} (hfix : gTw (nSL c) * bcAd σ h * (gTw (nSL c))⁻¹ = h) :
    ∃ (a : Fin Tag.D4.rank → Kˣ) (j : ModGL Tag.D4 K), j ∈ adjointGroup Tag.D4 K ∧
      (h : ModGL Tag.D4 K₂) = (((gTw Q)⁻¹ : ↥(adjointGroup Tag.D4 K₂)) : ModGL Tag.D4 K₂) *
        baseChangeGL (algebraMap K K₂) (rootDiagUnit Tag.D4 a * j) *
          ((gTw Q : ↥(adjointGroup Tag.D4 K₂)) : ModGL Tag.D4 K₂) := by
  have hσg : bcAd σ (gTw Q) = gTw Q * gTw (nSL c) := by rw [bcAd_gTw, hQc, gTw_mul]
  have hrF : bcAd σ (gTw Q * h * (gTw Q)⁻¹) = gTw Q * h * (gTw Q)⁻¹ := by
    rw [map_mul, map_mul, map_inv, hσg, _root_.mul_inv_rev]
    conv_rhs => rw [← hfix]
    group
  have hrF' : Units.map (entrywiseHom σ) ((gTw Q * h * (gTw Q)⁻¹ : ↥(adjointGroup Tag.D4 K₂)) :
      ModGL Tag.D4 K₂) = ((gTw Q * h * (gTw Q)⁻¹ : ↥(adjointGroup Tag.D4 K₂)) :
        ModGL Tag.D4 K₂) := by
    have e := congrArg Subtype.val hrF
    rw [coe_bcAd] at e
    exact (A2Nonsplit.units_map_entrywiseHom_eq_baseChangeGL σ _).trans e
  obtain ⟨a, u, ⟨u₀, hu₀, rfl⟩, hru⟩ := exists_rootDiagUnit_mul_of_frobenius_fixed Tag.D4 σ hσ
    (gTw Q * h * (gTw Q)⁻¹).2 hrF'
  refine ⟨a, u₀, hu₀, ?_⟩
  rw [map_mul, ← hru, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem diag_mul_sq_mem {K : Type} [Field K] (a : Fin Tag.D4.rank → Kˣ) {j : ModGL Tag.D4 K}
    (hj : j ∈ adjointGroup Tag.D4 K) :
    rootDiagUnit Tag.D4 a * j * (rootDiagUnit Tag.D4 a * j) ∈ adjointGroup Tag.D4 K := by
  have hsq : rootDiagUnit Tag.D4 a * rootDiagUnit Tag.D4 a ∈ adjointGroup Tag.D4 K := by
    rw [← rootDiagUnit_mul]
    convert CFSG.HardMathSupport.Lang.D4Three.rootDiagUnit_sq_mem_adjointGroup_D4 (K := K) a
      using 2
    congr 1
    funext i
    rw [Pi.mul_apply, pow_two]
  have hconj : (rootDiagUnit Tag.D4 a)⁻¹ * j * rootDiagUnit Tag.D4 a ∈ adjointGroup Tag.D4 K := by
    have h := conj_rootDiagUnit_mem_adjointGroup (τ := Tag.D4) a⁻¹ hj
    rwa [← rootDiagUnit_inv, inv_inv] at h
  have e : rootDiagUnit Tag.D4 a * j * (rootDiagUnit Tag.D4 a * j) =
      (rootDiagUnit Tag.D4 a * rootDiagUnit Tag.D4 a) *
        ((rootDiagUnit Tag.D4 a)⁻¹ * j * rootDiagUnit Tag.D4 a) * j := by group
  rw [e]
  exact mul_mem (mul_mem hsq hconj) hj

theorem diag_mul_commutator_mem {K : Type} [Field K] (a b : Fin Tag.D4.rank → Kˣ)
    {j j' : ModGL Tag.D4 K} (hj : j ∈ adjointGroup Tag.D4 K) (hj' : j' ∈ adjointGroup Tag.D4 K) :
    rootDiagUnit Tag.D4 a * j * (rootDiagUnit Tag.D4 b * j') * (rootDiagUnit Tag.D4 a * j)⁻¹ *
      (rootDiagUnit Tag.D4 b * j')⁻¹ ∈ adjointGroup Tag.D4 K := by
  have hc : rootDiagUnit Tag.D4 b * rootDiagUnit Tag.D4 a * (rootDiagUnit Tag.D4 b)⁻¹ =
      rootDiagUnit Tag.D4 a := by rw [rootDiagUnit_commute, mul_inv_cancel_right]
  have hX : (rootDiagUnit Tag.D4 b)⁻¹ * j * rootDiagUnit Tag.D4 b * j' * j⁻¹ ∈
      adjointGroup Tag.D4 K := by
    have h := conj_rootDiagUnit_mem_adjointGroup (τ := Tag.D4) b⁻¹ hj
    rw [← rootDiagUnit_inv, inv_inv] at h
    exact mul_mem (mul_mem h hj') (inv_mem hj)
  have hY := conj_rootDiagUnit_mem_adjointGroup (τ := Tag.D4) a hX
  have hZ := conj_rootDiagUnit_mem_adjointGroup (τ := Tag.D4) b (mul_mem hY (inv_mem hj'))
  have e : rootDiagUnit Tag.D4 a * j * (rootDiagUnit Tag.D4 b * j') *
      (rootDiagUnit Tag.D4 a * j)⁻¹ * (rootDiagUnit Tag.D4 b * j')⁻¹ =
      rootDiagUnit Tag.D4 b * (rootDiagUnit Tag.D4 a * ((rootDiagUnit Tag.D4 b)⁻¹ * j *
        rootDiagUnit Tag.D4 b * j' * j⁻¹) * (rootDiagUnit Tag.D4 a)⁻¹ * j'⁻¹) *
          (rootDiagUnit Tag.D4 b)⁻¹ := by
    calc rootDiagUnit Tag.D4 a * j * (rootDiagUnit Tag.D4 b * j') *
          (rootDiagUnit Tag.D4 a * j)⁻¹ * (rootDiagUnit Tag.D4 b * j')⁻¹ =
        rootDiagUnit Tag.D4 a * j * rootDiagUnit Tag.D4 b * j' * j⁻¹ *
          (rootDiagUnit Tag.D4 a)⁻¹ * j'⁻¹ * (rootDiagUnit Tag.D4 b)⁻¹ := by group
      _ = (rootDiagUnit Tag.D4 b * rootDiagUnit Tag.D4 a * (rootDiagUnit Tag.D4 b)⁻¹) * j *
          rootDiagUnit Tag.D4 b * j' * j⁻¹ * (rootDiagUnit Tag.D4 a)⁻¹ * j'⁻¹ *
            (rootDiagUnit Tag.D4 b)⁻¹ := by rw [hc]
      _ = _ := by group
  rw [e]
  exact hZ

end Minus

section MinusAssembly

set_option linter.unusedSectionVars false

open CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2
  CFSG.LieType.Steinberg.TwistedD4 CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
  CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit
  CFSG.RankThree.PartOne.CTP CFSG.HardMathSupport.Lang.D4Three
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh3
  CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator

theorem isPGLPiThree_fixedSubgroup_gammaP_orderThreeSL_of_ext {K : Type} [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (hp2 : p ≠ 2)
    (hq : p ^ f % 3 = 2) {K₂ : Type} [Field K₂] [Finite K₂] [Algebra K K₂]
    (hcard : Nat.card K₂ = Nat.card K ^ 2) (σ : K₂ →+* K₂) (hσ : ∀ x, σ x = x ^ Nat.card K) :
    IsPGLPiThree ↥(fixedSubgroup (gammaP K (orderThreeSL K))) (p ^ f) := by
  classical
  have hp : p.Prime := Fact.out
  have hq' : Nat.card K % 3 = 2 := by rw [hK]; exact hq
  obtain ⟨Q, ω, c₀, hQ, hω, hσωu, hQc, hc₀⟩ := exists_twist_data hq' hcard hσ
  have hω3 : ω ^ 3 = 1 := hω ▸ pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hω
    exact absurd hω (by norm_num)
  have hK₂ : Nat.card K₂ = p ^ (2 * f) := by rw [hcard, hK, ← pow_mul, mul_comm]
  have hK₂' : Nat.card K₂ = (p ^ f) ^ 2 := by rw [hcard, hK]
  have hq₂ : p ^ (2 * f) % 3 = 1 := by
    rw [mul_comm, pow_mul, Nat.pow_mod, hq]
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have hq2 : 2 < p ^ f := by
    have h3 : 3 ≤ p := by
      have := hp.two_le
      omega
    calc 2 < p := by omega
      _ ≤ p ^ f := Nat.le_self_pow (by omega) p
  have hσ' : ∀ c, σ c = c ^ p ^ f := fun c => by rw [hσ, hK]
  have hσ2 : ∀ c, σ (σ c) = c := frob_frob hcard hσ
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K₂ := ⟨hp, hf, hK₂⟩
  have hPi : Sec4.PiField false p f K₂ := ⟨hp, hf, hK₂'⟩
  have hnorm : ∀ w : K₂ˣ, Units.map σ.toMonoidHom w = w →
      ∃ ν : K₂ˣ, ν * Units.map σ.toMonoidHom ν = w := fun w hw =>
    exists_mul_frob_eq hK₂' hq1 hσ' hw
  obtain ⟨Ψ₂, hΨs, hΨk, hP1, hP2, hP3, hM1, hM2, hM3, hD⟩ :=
    exists_gammaP_HSL_frameHom (K := K₂) (p := p) (f := 2 * f) (by omega) hK₂ hp2 hq₂ hω3 hω1
  let Ψ' : GL (Fin 3) K₂ →* ↥(adjointGroup Tag.D4 K₂) :=
    (fixedSubgroup (gammaP K₂ (HSL ω))).subtype.comp Ψ₂
  obtain ⟨x, z, hxz⟩ := exists_gTw_nSL_mul_zB_inv c₀
  obtain ⟨hσx, hσz⟩ := frob_xxzx hc₀ hxz
  have hω3' : (ω : K₂) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  have hσω : σ (ω : K₂) = (ω : K₂) ^ 2 := by
    have h1 : σ (ω : K₂) = ((ω⁻¹ : K₂ˣ) : K₂) := congrArg Units.val hσωu
    rw [h1, Units.val_inv_eq_inv_val]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hω3')
  have hσω2 : σ ((ω : K₂) ^ 2) = ω := by
    rw [map_pow, hσω]
    linear_combination (ω : K₂) * hω3'
  have hF := frob_frameHom hσω hσω2 hxz Ψ' (fun c => Subtype.ext (hP1 c))
    (fun c => Subtype.ext (hP2 c)) (fun c => Subtype.ext (hP3 c)) (fun c => Subtype.ext (hM1 c))
    (fun c => Subtype.ext (hM2 c)) (fun c => Subtype.ext (hM3 c)) (fun a => hD a)
  obtain ⟨D, hDdef⟩ : ∃ D : Fin 3 → K₂ˣ, D = ![x, 1, -(x * z)⁻¹] := ⟨_, rfl⟩
  rw [← hDdef] at hF
  have hDfix : ∀ i, Units.map σ.toMonoidHom (D i) = D i := by
    intro i
    rw [hDdef]
    fin_cases i
    · exact hσx
    · exact map_one _
    · apply Units.ext
      show σ (((-(x * z)⁻¹ : K₂ˣ)) : K₂) = _
      rw [Units.val_neg, Units.val_inv_eq_inv_val, Units.val_mul, map_neg, map_inv₀, map_mul,
        show σ (x : K₂) = x from congrArg Units.val hσx,
        show σ (z : K₂) = z from congrArg Units.val hσz]
      show _ = (((-(x * z)⁻¹ : K₂ˣ)) : K₂)
      rw [Units.val_neg, Units.val_inv_eq_inv_val, Units.val_mul]
  choose X hX using fun i => hnorm (D i)⁻¹ (by rw [map_inv, hDfix i])
  have hker' : ∀ a b : GL (Fin 3) K₂, Ψ' a = Ψ' b ↔
      a * b⁻¹ ∈ Subgroup.center (GL (Fin 3) K₂) := by
    intro a b
    rw [← Matrix.ProjGenLinGroup.ker_mk, ← hΨk, MonoidHom.mem_ker, map_mul, map_inv,
      mul_inv_eq_one]
    exact ⟨fun h1 => Subtype.ext h1, fun h1 => congrArg Subtype.val h1⟩
  have hkey : ∀ g, gTw (nSL c₀) * bcAd σ (Ψ' g) * (gTw (nSL c₀))⁻¹ = Ψ' g ↔
      Matrix.ProjGenLinGroup.mk (diagU X * g * (diagU X)⁻¹) ∈
        CFSG.PGLModel.projImage (Sec4.glPi false 3 (p ^ f) K₂) := by
    intro g
    rw [hF g, hker', thetaD_mul_inv_mem_center_iff hU hσ' hσ2 hnorm hX]
  let Ftw : ↥(adjointGroup Tag.D4 K₂) →* ↥(adjointGroup Tag.D4 K₂) :=
    (MulAut.conj (gTw (nSL c₀))).toMonoidHom.comp (bcAd σ)
  let N : Subgroup ↥(adjointGroup Tag.D4 K₂) :=
    fixedSubgroup (gammaP K₂ (HSL ω)) ⊓ MonoidHom.eqLocus Ftw (MonoidHom.id _)
  have hNF : ∀ y ∈ N, gTw (nSL c₀) * bcAd σ y * (gTw (nSL c₀))⁻¹ = y := fun y hy => hy.2
  let eΨ : Matrix.ProjGenLinGroup (Fin 3) K₂ ≃* ↥(fixedSubgroup (gammaP K₂ (HSL ω))) :=
    (QuotientGroup.quotientMulEquivOfEq (hΨk.trans Matrix.ProjGenLinGroup.ker_mk)).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective Ψ₂ hΨs)
  have heΨ : ∀ g, eΨ (Matrix.ProjGenLinGroup.mk g) = Ψ₂ g := fun g => rfl
  let φ : ↥N →* Matrix.ProjGenLinGroup (Fin 3) K₂ :=
    (MulAut.conj (Matrix.ProjGenLinGroup.mk (diagU X))).toMonoidHom.comp
      (eΨ.symm.toMonoidHom.comp (Subgroup.inclusion inf_le_left))
  have hφinj : Function.Injective φ :=
    (MulAut.conj _).injective.comp (eΨ.symm.injective.comp (Subgroup.inclusion_injective _))
  have hφrange : φ.range = CFSG.PGLModel.projImage (Sec4.glPi false 3 (p ^ f) K₂) := by
    ext v
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨g, hg⟩ := Matrix.ProjGenLinGroup.mk_surjective
        (eΨ.symm (Subgroup.inclusion inf_le_left y))
      have h1 : Ψ₂ g = Subgroup.inclusion inf_le_left y := by
        rw [← heΨ, hg, MulEquiv.apply_symm_apply]
      have h2 : Ψ' g = (y : ↥(adjointGroup Tag.D4 K₂)) := congrArg Subtype.val h1
      have h3 := (hkey g).1 (by rw [h2]; exact hNF y y.2)
      show (MulAut.conj (Matrix.ProjGenLinGroup.mk (diagU X)))
        (eΨ.symm (Subgroup.inclusion inf_le_left y)) ∈ _
      rw [← hg, MulAut.conj_apply,
        ← map_inv (Matrix.ProjGenLinGroup.mk : GL (Fin 3) K₂ →* _), ← map_mul, ← map_mul]
      exact h3
    · rintro ⟨h, hh, rfl⟩
      have hg : diagU X * ((diagU X)⁻¹ * h * diagU X) * (diagU X)⁻¹ = h := by group
      have h3 := (hkey ((diagU X)⁻¹ * h * diagU X)).2 (by rw [hg]; exact ⟨h, hh, rfl⟩)
      refine ⟨⟨Ψ' ((diagU X)⁻¹ * h * diagU X), (Ψ₂ _).2, h3⟩, ?_⟩
      show (MulAut.conj (Matrix.ProjGenLinGroup.mk (diagU X)))
        (eΨ.symm (Ψ₂ ((diagU X)⁻¹ * h * diagU X))) = _
      rw [← heΨ, MulEquiv.symm_apply_apply, MulAut.conj_apply,
        ← map_inv (Matrix.ProjGenLinGroup.mk : GL (Fin 3) K₂ →* _), ← map_mul, ← map_mul, hg]
  let eN : ↥N ≃* ↥(CFSG.PGLModel.projImage (Sec4.glPi false 3 (p ^ f) K₂)) :=
    (MonoidHom.ofInjective hφinj).trans (MulEquiv.subgroupCongr hφrange)
  have hιN : ∀ c : ↥(fixedSubgroup (gammaP K (orderThreeSL K))), ιTw K Q c ∈ N := by
    intro c
    refine ⟨?_, twFrob_ιTw σ hσ hQc c⟩
    show gammaP K₂ (HSL ω) (ιTw K Q c) = ιTw K Q c
    rw [← ιTw_gammaP hQ]
    exact congrArg (ιTw K Q) c.2
  let ιN : ↥(fixedSubgroup (gammaP K (orderThreeSL K))) →* ↥N :=
    ((ιTw K Q).comp (fixedSubgroup (gammaP K (orderThreeSL K))).subtype).codRestrict N hιN
  have hιinj : Function.Injective ιN := fun a b hab =>
    Subtype.ext (ιTw_injective Q (congrArg Subtype.val hab))
  have hcoeι : ∀ (w : ModGL Tag.D4 K) (hw : w ∈ adjointGroup Tag.D4 K),
      ((ιTw K Q ⟨w, hw⟩ : ↥(adjointGroup Tag.D4 K₂)) : ModGL Tag.D4 K₂) =
        (((gTw Q)⁻¹ : ↥(adjointGroup Tag.D4 K₂)) : ModGL Tag.D4 K₂) *
          baseChangeGL (algebraMap K K₂) w *
            ((gTw Q : ↥(adjointGroup Tag.D4 K₂)) : ModGL Tag.D4 K₂) := by
    intro w hw
    rw [ιTw_apply, Subgroup.coe_mul, Subgroup.coe_mul, coe_bcAd]
  have hsq : ∀ y ∈ N, y * y ∈ (ιTw K Q).range := by
    intro y hy
    obtain ⟨a, j, hj, hyj⟩ := exists_diag_mul_of_twFrob_fixed σ hσ hQc (hNF y hy)
    refine ⟨⟨_, diag_mul_sq_mem a hj⟩, Subtype.ext ?_⟩
    rw [hcoeι, Subgroup.coe_mul, hyj]
    simp only [map_mul, Subgroup.coe_inv]
    group
  have hcomm : ∀ y ∈ N, ∀ y' ∈ N, ⁅y, y'⁆ ∈ (ιTw K Q).range := by
    intro y hy y' hy'
    obtain ⟨a, j, hj, hyj⟩ := exists_diag_mul_of_twFrob_fixed σ hσ hQc (hNF y hy)
    obtain ⟨b, j', hj', hyj'⟩ := exists_diag_mul_of_twFrob_fixed σ hσ hQc (hNF y' hy')
    refine ⟨⟨_, diag_mul_commutator_mem a b hj hj'⟩, Subtype.ext ?_⟩
    rw [hcoeι, commutatorElement_def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hyj, hyj']
    simp only [map_mul, map_inv, Subgroup.coe_inv]
    group
  have hcommN : commutator ↥N ≤ (ιTw K Q).range.comap N.subtype := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    exact hcomm a a.2 b b.2
  have hcube : ∀ y : ↥N, y ^ 3 ∈ commutator ↥N := by
    intro y
    have h1 : eN y ^ 3 ∈
        commutator ↥(CFSG.PGLModel.projImage (Sec4.glPi false 3 (p ^ f) K₂)) := by
      rw [Sec13.commutator_projImage_glPi hPi hq2, Subgroup.mem_subgroupOf, Subgroup.coe_pow]
      obtain ⟨u, hu, hu'⟩ := (eN y).2
      rw [← hu']
      exact mk_pow_three_mem_projImage_slPi hU hσ' hu
    have h2 : (commutator ↥(CFSG.PGLModel.projImage (Sec4.glPi false 3 (p ^ f) K₂))).map
        eN.symm.toMonoidHom = commutator ↥N := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ eN.symm.surjective]
    rw [← h2]
    refine ⟨_, h1, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, map_pow, MulEquiv.symm_apply_apply]
  have hιsurj : Function.Surjective ιN := by
    intro y
    have hy3 : (y : ↥(adjointGroup Tag.D4 K₂)) ^ 3 ∈ (ιTw K Q).range := by
      have h1 := hcommN (hcube y)
      rw [Subgroup.mem_comap] at h1
      simpa using h1
    have hy2 := hsq y y.2
    have hy : (y : ↥(adjointGroup Tag.D4 K₂)) ∈ (ιTw K Q).range := by
      have e : (y : ↥(adjointGroup Tag.D4 K₂)) = (y : ↥(adjointGroup Tag.D4 K₂)) ^ 3 *
          ((y : ↥(adjointGroup Tag.D4 K₂)) * (y : ↥(adjointGroup Tag.D4 K₂)))⁻¹ := by group
      rw [e]
      exact mul_mem hy3 (inv_mem hy2)
    obtain ⟨h, hh⟩ := hy
    have hhC : h ∈ fixedSubgroup (gammaP K (orderThreeSL K)) := by
      show gammaP K (orderThreeSL K) h = h
      apply ιTw_injective Q
      rw [ιTw_gammaP hQ, hh]
      exact y.2.1
    exact ⟨⟨h, hhC⟩, Subtype.ext hh⟩
  exact ⟨false, p, f, K₂, inferInstance, hPi, rfl, hq,
    ⟨(MulEquiv.ofBijective ιN ⟨hιinj, hιsurj⟩).trans eN⟩⟩

theorem d4GraphA2FixIsoMinusB0_holds : D4GraphA2FixIsoMinusB0 := by
  intro K _ _ hK2 _ _ hq
  have := Fintype.ofFinite K
  obtain ⟨f, hp, hcard⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hp⟩
  have hK : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hcard
  rw [hK]
  exact isPGLPiThree_fixedSubgroup_gammaP_orderThreeSL_of_ext f.pos hK hK2
    (by rw [← hK]; exact hq) (FiniteField.natCard_extension K (ringChar K) 2)
    (FiniteField.Extension.frob K (ringChar K) 2).toRingEquiv.toRingHom
    (fun y => FiniteField.Extension.frob_apply K (ringChar K) 2)

theorem d4GraphA2FixIsoOdd_holds : D4GraphA2FixIsoOdd :=
  d4GraphA2FixIsoOdd_of_minusB0 d4GraphA2FixIsoMinusB0_holds

end MinusAssembly

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighD4Odd

end

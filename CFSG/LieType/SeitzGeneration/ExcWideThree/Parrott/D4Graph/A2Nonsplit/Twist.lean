module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit.BaseChange
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit.TwistDiag
public import CFSG.LieType.Chevalley.WeylNormalizerQuotient

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator CFSG.HardMathSupport.Seitz.Proving

section Matrices

variable {L L' : Type} [Field L] [Field L']

theorem mapSL_HSL (f : L →+* L') (t : Lˣ) :
    Matrix.SpecialLinearGroup.map f (HSL t) = HSL (Units.map f.toMonoidHom t) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [HSL]

theorem mapSL_nSL (f : L →+* L') (c : Lˣ) :
    Matrix.SpecialLinearGroup.map f (nSL c) = nSL (Units.map f.toMonoidHom c) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nSL, RingHom.mapMatrix_apply]

theorem mapSL_orderThreeSL (f : L →+* L') :
    Matrix.SpecialLinearGroup.map f (orderThreeSL L) = orderThreeSL L' := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, orderThreeSL_val, orderThreeSL_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [RingHom.mapMatrix_apply]

theorem nSL_inv (c : Lˣ) : (nSL c)⁻¹ = nSL (-c) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nSL, Matrix.adjugate_fin_two]

theorem exists_eq_nSL {n : SL2 L} {t : Lˣ} (ht : (t : L) ^ 2 ≠ 1)
    (h : HSL t * n = n * HSL t⁻¹) : ∃ c : Lˣ, n = nSL c := by
  have ht0 : (t : L) ≠ 0 := t.ne_zero
  have hti : ((t⁻¹ : Lˣ) : L) = (t : L)⁻¹ := Units.val_inv_eq_inv_val t
  have hne : (t : L) - (t : L)⁻¹ ≠ 0 := by
    intro h0
    apply ht
    have : (t : L) = (t : L)⁻¹ := sub_eq_zero.1 h0
    calc (t : L) ^ 2 = (t : L) * (t : L)⁻¹ := by rw [pow_two, ← this]
      _ = 1 := mul_inv_cancel₀ ht0
  have hm := congrArg (fun A : SL2 L => (A : Matrix (Fin 2) (Fin 2) L)) h
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hm
  have e00 := congrFun (congrFun hm 0) 0
  have e11 := congrFun (congrFun hm 1) 1
  simp only [HSL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    inv_inv, hti] at e00 e11
  have h00 : (n : Matrix (Fin 2) (Fin 2) L) 0 0 = 0 := by
    have : ((t : L) - (t : L)⁻¹) * (n : Matrix (Fin 2) (Fin 2) L) 0 0 = 0 := by
      linear_combination e00
    exact (mul_eq_zero.1 this).resolve_left hne
  have h11 : (n : Matrix (Fin 2) (Fin 2) L) 1 1 = 0 := by
    have : ((t : L) - (t : L)⁻¹) * (n : Matrix (Fin 2) (Fin 2) L) 1 1 = 0 := by
      linear_combination -e11
    exact (mul_eq_zero.1 this).resolve_left hne
  have hdet := n.2
  rw [Matrix.det_fin_two, h00, h11, zero_mul, zero_sub] at hdet
  have h01 : (n : Matrix (Fin 2) (Fin 2) L) 0 1 ≠ 0 := by
    intro h0
    rw [h0, zero_mul, neg_zero] at hdet
    exact zero_ne_one hdet
  refine ⟨Units.mk0 _ h01, ?_⟩
  apply Subtype.ext
  ext i j
  have h10 : (n : Matrix (Fin 2) (Fin 2) L) 1 0 = -((n : Matrix (Fin 2) (Fin 2) L) 0 1)⁻¹ := by
    field_simp
    linear_combination -hdet
  fin_cases i <;> fin_cases j <;> simp [nSL, h00, h11, h10]

end Matrices


section Conj

variable {L L' : Type} [Field L] [Field L']

@[expose] noncomputable def gTw (A : SL2 L) : ↥(adjointGroup Tag.D4 L) :=
  sl2At L ⟨2, by decide⟩ A * frameDiag A

theorem gTw_mul (A B : SL2 L) : gTw (A * B) = gTw A * gTw B := by
  have hc := (frameDiag_commute_sl2Two (K := L) A B).eq
  simp only [gTw, map_mul, frameDiag_mul, mul_assoc]
  rw [← mul_assoc (sl2At L ⟨2, by decide⟩ B), ← hc, mul_assoc]

theorem gTw_one : gTw (1 : SL2 L) = 1 := by
  have h := gTw_mul (1 : SL2 L) 1
  rw [mul_one] at h
  exact left_eq_mul.1 h |>.symm ▸ rfl

theorem gTw_inv (A : SL2 L) : gTw A⁻¹ = (gTw A)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← gTw_mul, inv_mul_cancel, gTw_one])

theorem d4Graph_gTw (A : SL2 L) : d4Graph L 1 (gTw A) = gTw A := by
  rw [gTw, map_mul, d4Graph_one_sl2Two, d4Graph_frameDiag]

theorem bcAd_gTw (f : L →+* L') (A : SL2 L) :
    bcAd f (gTw A) = gTw (Matrix.SpecialLinearGroup.map f A) := by
  rw [gTw, gTw, map_mul, bcAd_sl2At, bcAd_frameDiag]

theorem gTw_conj_sl2Two (Q B : SL2 L) :
    (gTw Q)⁻¹ * sl2At L ⟨2, by decide⟩ B * gTw Q = sl2At L ⟨2, by decide⟩ (Q⁻¹ * B * Q) := by
  have hc := (frameDiag_commute_sl2Two (K := L) Q (Q⁻¹ * B * Q)).eq
  rw [gTw, mul_inv_rev]
  calc (frameDiag Q)⁻¹ * (sl2At L ⟨2, by decide⟩ Q)⁻¹ * sl2At L ⟨2, by decide⟩ B *
        (sl2At L ⟨2, by decide⟩ Q * frameDiag Q) =
      (frameDiag Q)⁻¹ * ((sl2At L ⟨2, by decide⟩ Q)⁻¹ * sl2At L ⟨2, by decide⟩ B *
        sl2At L ⟨2, by decide⟩ Q) * frameDiag Q := by group
    _ = (frameDiag Q)⁻¹ * (frameDiag Q * sl2At L ⟨2, by decide⟩ (Q⁻¹ * B * Q)) := by
      rw [← map_inv, ← map_mul, ← map_mul, mul_assoc, hc]
    _ = _ := inv_mul_cancel_left _ _

end Conj

section Acts

variable {L : Type} [Field L]

@[expose] def ActsBy (m : ModGL Tag.D4 L) (M : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ) :
    Prop :=
  ∀ b : Fin Tag.D4.rank → Lˣ, m * rootDiagUnit Tag.D4 b * m⁻¹ = rootDiagUnit Tag.D4 (tupAct M b)

theorem ActsBy.mul {m m' : ModGL Tag.D4 L} {M M' : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ}
    (h : ActsBy m M) (h' : ActsBy m' M') : ActsBy (m * m') (M * M') := by
  intro b
  rw [mul_inv_rev, show m * m' * rootDiagUnit Tag.D4 b * (m'⁻¹ * m⁻¹) =
    m * (m' * rootDiagUnit Tag.D4 b * m'⁻¹) * m⁻¹ by group, h', h, tupAct_tupAct]

theorem ActsBy.inv {m : ModGL Tag.D4 L} {M N : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ}
    (h : ActsBy m M) (hMN : M * N = 1) : ActsBy m⁻¹ N := by
  intro b
  have e := h (tupAct N b)
  rw [tupAct_tupAct, hMN, tupAct_one] at e
  rw [inv_inv, ← e]
  group

theorem actsBy_weylElt (i : Fin Tag.D4.rank) : ActsBy (weylElt Tag.D4 L i 1) (reflM i) :=
  fun b => weylElt_conj_rootDiagUnit_tupAct i b

theorem actsBy_torusElt (i : Fin Tag.D4.rank) (t : Lˣ) : ActsBy (torusElt Tag.D4 L i t) 1 := by
  intro b
  rw [torusElt_eq_rootDiagUnit, rootDiagUnit_commute, mul_inv_cancel_right, tupAct_one]

theorem tupAct_neg_one (b : Fin Tag.D4.rank → Lˣ) : tupAct (-1) b = b⁻¹ := by
  funext j
  simp only [tupAct, Pi.inv_apply]
  rw [Finset.prod_eq_single j (fun k _ hkj => by
      rw [Matrix.neg_apply, Matrix.one_apply_ne (Ne.symm hkj), neg_zero, zpow_zero])
    (fun h => absurd (Finset.mem_univ j) h), Matrix.neg_apply, Matrix.one_apply_eq, zpow_neg_one]

theorem coe_nW (i : Fin Tag.D4.rank) :
    ((nW i : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L) = weylElt Tag.D4 L i 1 :=
  coe_weylElement_one i

theorem coe_sl2At_nSL (i : Fin Tag.D4.rank) (c : Lˣ) :
    ((sl2At L i (nSL c) : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L) =
      torusElt Tag.D4 L i c * weylElt Tag.D4 L i 1 := by
  rw [coe_sl2At, nSL_eq_HSL_mul, map_mul, simpleRootSL2_HSL, simpleRootSL2_WSL]

theorem actsBy_nW_mul_nW (a b : Fin Tag.D4.rank) :
    ActsBy ((nW a * nW b : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L) (reflM a * reflM b) := by
  rw [Subgroup.coe_mul, coe_nW, coe_nW]
  exact (actsBy_weylElt a).mul (actsBy_weylElt b)

theorem ActsBy.conj_nW (a b : Fin Tag.D4.rank) {x : ↥(adjointGroup Tag.D4 L)}
    {M : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ} (hx : ActsBy (x : ModGL Tag.D4 L) M)
    (hab : reflM a * reflM b * (reflM b * reflM a) = 1) :
    ActsBy ((nW a * nW b * x * (nW a * nW b)⁻¹ : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L)
      (reflM a * reflM b * M * (reflM b * reflM a)) := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  exact ((actsBy_nW_mul_nW a b).mul hx).mul ((actsBy_nW_mul_nW a b).inv hab)

theorem coe_conj_torusElement {m : ↥(adjointGroup Tag.D4 L)}
    {M : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ} (hm : ActsBy (m : ModGL Tag.D4 L) M)
    (i : Fin Tag.D4.rank) (t : Lˣ) :
    ((m * torusElement Tag.D4 L i t * m⁻¹ : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L) =
      rootDiagUnit Tag.D4 (tupAct M (fun j => t ^ Tag.D4.cartan i j)) := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_torusElement, hm]

theorem actsBy_gTw_nSL (c : Lˣ) :
    ActsBy ((gTw (nSL c) : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L) (-1) := by
  have h2 : ActsBy ((sl2At L ⟨2, by decide⟩ (nSL c) : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L)
      (1 * reflM ⟨2, by decide⟩) := by
    rw [coe_sl2At_nSL]
    exact (actsBy_torusElt _ _).mul (actsBy_weylElt _)
  have h1 := h2.conj_nW ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
  have h3 := h2.conj_nW ⟨1, by decide⟩ ⟨3, by decide⟩ (by decide)
  have h4 := h2.conj_nW ⟨3, by decide⟩ ⟨0, by decide⟩ (by decide)
  rw [← frameK₁_apply] at h1
  rw [← frameK₃_eq] at h3
  rw [← frameK₂_eq] at h4
  have h := h2.mul ((h1.mul h3).mul h4)
  rw [gTw, frameDiag, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul]
  have e : (1 * reflM (⟨2, by decide⟩ : Fin Tag.D4.rank)) *
      ((reflM ⟨0, by decide⟩ * reflM ⟨1, by decide⟩ * (1 * reflM ⟨2, by decide⟩) *
          (reflM ⟨1, by decide⟩ * reflM ⟨0, by decide⟩)) *
        (reflM ⟨1, by decide⟩ * reflM ⟨3, by decide⟩ * (1 * reflM ⟨2, by decide⟩) *
          (reflM ⟨3, by decide⟩ * reflM ⟨1, by decide⟩)) *
        (reflM ⟨3, by decide⟩ * reflM ⟨0, by decide⟩ * (1 * reflM ⟨2, by decide⟩) *
          (reflM ⟨0, by decide⟩ * reflM ⟨3, by decide⟩))) = -1 := by decide
  rw [← e]
  simpa only [Subgroup.coe_mul, mul_assoc] using h

theorem gTw_nSL_conj_diag (c : Lˣ) {t : ↥(adjointGroup Tag.D4 L)} {b : Fin Tag.D4.rank → Lˣ}
    (ht : (t : ModGL Tag.D4 L) = rootDiagUnit Tag.D4 b) :
    gTw (nSL c) * t * (gTw (nSL c))⁻¹ = t⁻¹ := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, ht,
    actsBy_gTw_nSL c b, tupAct_neg_one, rootDiagUnit_inv]

theorem gTw_nSL_inv_conj_diag (c : Lˣ) {t : ↥(adjointGroup Tag.D4 L)}
    {b : Fin Tag.D4.rank → Lˣ} (ht : (t : ModGL Tag.D4 L) = rootDiagUnit Tag.D4 b) :
    (gTw (nSL c))⁻¹ * t * gTw (nSL c) = t⁻¹ := by
  have h := gTw_nSL_conj_diag c (t := t⁻¹) (b := b⁻¹) (by rw [Subgroup.coe_inv, ht,
    rootDiagUnit_inv])
  rw [inv_inv] at h
  calc (gTw (nSL c))⁻¹ * t * gTw (nSL c) =
      (gTw (nSL c))⁻¹ * (gTw (nSL c) * t⁻¹ * (gTw (nSL c))⁻¹) * gTw (nSL c) := by rw [h]
    _ = t⁻¹ := by group

end Acts

section Mono

variable {L : Type} [Field L]

@[expose] def IsMono (m : ModGL Tag.D4 L) (w : WeylGroup Tag.D4) : Prop :=
  m ∈ monomialSubgroup Tag.D4 L ∧ MapsRootLines m w

theorem IsMono.mul {m m' : ModGL Tag.D4 L} {w w' : WeylGroup Tag.D4} (h : IsMono m w)
    (h' : IsMono m' w') : IsMono (m * m') (w * w') :=
  ⟨mul_mem h.1 h'.1, h.2.mul h'.2⟩

theorem IsMono.inv {m : ModGL Tag.D4 L} {w : WeylGroup Tag.D4} (h : IsMono m w) :
    IsMono m⁻¹ w⁻¹ :=
  ⟨inv_mem h.1, h.2.inv⟩

theorem IsMono.pow {m : ModGL Tag.D4 L} {w : WeylGroup Tag.D4} (h : IsMono m w) (n : ℕ) :
    IsMono (m ^ n) (w ^ n) := by
  induction n with
  | zero => exact ⟨one_mem _, by simpa using mapsRootLines_one⟩
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul h

theorem isMono_torusElt (i : Fin Tag.D4.rank) (t : Lˣ) : IsMono (torusElt Tag.D4 L i t) 1 :=
  ⟨torusElt_mem_monomialSubgroup i t, mapsRootLines_of_mem_torusGroup (torusElt_mem_torusGroup i t)⟩

theorem isMono_weylElt (i : Fin Tag.D4.rank) :
    IsMono (weylElt Tag.D4 L i 1) (simple Tag.D4 i) :=
  ⟨weylElt_mem_monomialSubgroup i, mapsRootLines_weylElt i⟩

theorem IsMono.mem_torusGroup {m : ModGL Tag.D4 L} (h : IsMono m 1) :
    m ∈ torusGroup Tag.D4 L := by
  obtain ⟨w, k, hk, hmk⟩ := monomialSubgroup_le_torusWeylCosets h.1
  have hmaps : MapsRootLines m w := by
    rw [hmk]
    simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep w)
  have hw : w = 1 := hmaps.unique h.2
  rw [hmk, hw, canonicalRep_one, mul_one]
  exact hk

theorem isMono_nW (i : Fin Tag.D4.rank) :
    IsMono ((nW i : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L) (simple Tag.D4 i) := by
  rw [coe_nW]
  exact isMono_weylElt i

theorem IsMono.conj_nW (a b : Fin Tag.D4.rank) {x : ↥(adjointGroup Tag.D4 L)}
    {w : WeylGroup Tag.D4} (hx : IsMono (x : ModGL Tag.D4 L) w) :
    IsMono ((nW a * nW b * x * (nW a * nW b)⁻¹ : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L)
      (simple Tag.D4 a * simple Tag.D4 b * w * (simple Tag.D4 b * simple Tag.D4 a)) := by
  have h := (((isMono_nW (L := L) a).mul (isMono_nW b)).mul hx).mul
    ((isMono_nW (L := L) a).mul (isMono_nW b)).inv
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev,
    (coxeterSystem Tag.D4).inv_simple] using h

@[expose] def wN : WeylGroup Tag.D4 :=
  simple Tag.D4 ⟨2, by decide⟩ *
    ((simple Tag.D4 ⟨0, by decide⟩ * simple Tag.D4 ⟨1, by decide⟩ * simple Tag.D4 ⟨2, by decide⟩ *
        (simple Tag.D4 ⟨1, by decide⟩ * simple Tag.D4 ⟨0, by decide⟩)) *
      (simple Tag.D4 ⟨1, by decide⟩ * simple Tag.D4 ⟨3, by decide⟩ *
        simple Tag.D4 ⟨2, by decide⟩ *
          (simple Tag.D4 ⟨3, by decide⟩ * simple Tag.D4 ⟨1, by decide⟩)) *
      (simple Tag.D4 ⟨3, by decide⟩ * simple Tag.D4 ⟨0, by decide⟩ *
        simple Tag.D4 ⟨2, by decide⟩ *
          (simple Tag.D4 ⟨0, by decide⟩ * simple Tag.D4 ⟨3, by decide⟩)))

@[expose] def wG : WeylGroup Tag.D4 :=
  simple Tag.D4 ⟨2, by decide⟩ *
    (simple Tag.D4 ⟨0, by decide⟩ * simple Tag.D4 ⟨1, by decide⟩ * simple Tag.D4 ⟨3, by decide⟩)

theorem isMono_gTw_nSL (c : Lˣ) :
    IsMono ((gTw (nSL c) : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L) wN := by
  have h2 : IsMono ((sl2At L ⟨2, by decide⟩ (nSL c) : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L)
      (simple Tag.D4 ⟨2, by decide⟩) := by
    rw [coe_sl2At_nSL, ← one_mul (simple Tag.D4 _)]
    exact (isMono_torusElt _ _).mul (isMono_weylElt _)
  have h1 := h2.conj_nW ⟨0, by decide⟩ ⟨1, by decide⟩
  have h3 := h2.conj_nW ⟨1, by decide⟩ ⟨3, by decide⟩
  have h4 := h2.conj_nW ⟨3, by decide⟩ ⟨0, by decide⟩
  rw [← frameK₁_apply] at h1
  rw [← frameK₃_eq] at h3
  rw [← frameK₂_eq] at h4
  have h := h2.mul ((h1.mul h3).mul h4)
  rw [gTw, frameDiag]
  unfold wN
  simpa only [Subgroup.coe_mul] using h

theorem isMono_weylG2 : IsMono ((weylG2 : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L) wG := by
  have h := (isMono_nW (L := L) ⟨2, by decide⟩).mul (((isMono_nW (L := L) ⟨0, by decide⟩).mul
    (isMono_nW ⟨1, by decide⟩)).mul (isMono_nW ⟨3, by decide⟩))
  simp only [nW] at h
  unfold weylG2 wG
  simpa only [Subgroup.coe_mul] using h

theorem wN_mul_wG_pow : wN * wG ^ 4 = wG ^ 4 * wN := by
  apply ext_single
  intro i
  simp only [wN, wG, pow_succ, pow_zero, one_mul, mul_smul, simple_smul]
  revert i
  decide

end Mono

section Twist

variable {K K₂ : Type} [Field K] [Field K₂] [Algebra K K₂]

variable (K) in
@[expose] noncomputable def ιTw (Q : SL2 K₂) :
    ↥(adjointGroup Tag.D4 K) →* ↥(adjointGroup Tag.D4 K₂) :=
  (MulAut.conj (gTw Q)⁻¹).toMonoidHom.comp (bcAd (algebraMap K K₂))

theorem ιTw_apply (Q : SL2 K₂) (h : ↥(adjointGroup Tag.D4 K)) :
    ιTw K Q h = (gTw Q)⁻¹ * bcAd (algebraMap K K₂) h * gTw Q := by
  simp [ιTw, MulAut.conj_apply]

theorem ιTw_injective (Q : SL2 K₂) : Function.Injective (ιTw K Q) := by
  intro x y hxy
  rw [ιTw_apply, ιTw_apply] at hxy
  exact bcAd_injective _ (by simpa using hxy)

theorem ιTw_gammaP {Q : SL2 K₂} {ω : K₂ˣ} (hQ : Q⁻¹ * orderThreeSL K₂ * Q = HSL ω)
    (h : ↥(adjointGroup Tag.D4 K)) :
    ιTw K Q (gammaP K (orderThreeSL K) h) = gammaP K₂ (HSL ω) (ιTw K Q h) := by
  have hg : d4Graph K₂ 1 (gTw Q) = gTw Q := d4Graph_gTw Q
  have hs := gTw_conj_sl2Two Q (orderThreeSL K₂)
  rw [hQ] at hs
  rw [ιTw_apply, ιTw_apply, bcAd_gammaP, mapSL_orderThreeSL, gammaP, gammaP, MulAut.mul_apply,
    MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, ← hs, map_mul, map_mul, hg, map_inv,
    hg]
  group

theorem frameD_exponents (j : Fin Tag.D4.rank) :
    (reflM ⟨3, by decide⟩ * reflM ⟨0, by decide⟩).mulVec (Tag.D4.cartan ⟨2, by decide⟩) j -
      (reflM ⟨1, by decide⟩ * reflM ⟨3, by decide⟩).mulVec (Tag.D4.cartan ⟨2, by decide⟩) j =
        vD j := by
  revert j
  decide

theorem ιTw_frameD {Q : SL2 K₂} {ω : K₂ˣ} (hQ : Q⁻¹ * orderThreeSL K₂ * Q = HSL ω) :
    ιTw K Q (frameD K (orderThreeSL K)) =
      torusElement Tag.D4 K₂ ⟨0, by decide⟩ ω * torusElement Tag.D4 K₂ ⟨1, by decide⟩ ω⁻¹ := by
  rw [ιTw_apply, bcAd_frameD, mapSL_orderThreeSL]
  have hc2 := (frameK_commute_sl2Two (K := K₂) (orderThreeSL K₂) Q).2.2
  have hc3 := (frameK_commute_sl2Two (K := K₂) (orderThreeSL K₂) Q).2.1
  have hcd : Commute (frameD K₂ (orderThreeSL K₂)) (sl2At K₂ ⟨2, by decide⟩ Q) :=
    hc2.mul_left hc3.inv_left
  have e1 : (gTw Q)⁻¹ * frameD K₂ (orderThreeSL K₂) * gTw Q =
      frameDiag Q⁻¹ * frameD K₂ (orderThreeSL K₂) * (frameDiag Q⁻¹)⁻¹ := by
    rw [gTw, mul_inv_rev, frameDiag_inv, inv_inv,
      show (frameDiag Q)⁻¹ * (sl2At K₂ ⟨2, by decide⟩ Q)⁻¹ * frameD K₂ (orderThreeSL K₂) *
          (sl2At K₂ ⟨2, by decide⟩ Q * frameDiag Q) =
        (frameDiag Q)⁻¹ * ((sl2At K₂ ⟨2, by decide⟩ Q)⁻¹ * (frameD K₂ (orderThreeSL K₂) *
          sl2At K₂ ⟨2, by decide⟩ Q)) * frameDiag Q by group, hcd.eq, inv_mul_cancel_left]
  have e2 : frameDiag Q⁻¹ * frameD K₂ (orderThreeSL K₂) * (frameDiag Q⁻¹)⁻¹ =
      frameK₂ K₂ (HSL ω) * (frameK₃ K₂ (HSL ω))⁻¹ := by
    rw [frameD, show frameDiag Q⁻¹ * (frameK₂ K₂ (orderThreeSL K₂) *
          (frameK₃ K₂ (orderThreeSL K₂))⁻¹) * (frameDiag Q⁻¹)⁻¹ =
        (frameDiag Q⁻¹ * frameK₂ K₂ (orderThreeSL K₂) * (frameDiag Q⁻¹)⁻¹) *
          (frameDiag Q⁻¹ * frameK₃ K₂ (orderThreeSL K₂) * (frameDiag Q⁻¹)⁻¹)⁻¹ by group,
      frameDiag_conj_frameK₂, frameDiag_conj_frameK₃, inv_inv, hQ]
  rw [e1, e2, frameK₂_eq, frameK₃_eq, sl2At_HSL]
  apply Subtype.ext
  rw [coe_dTorus, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_conj_torusElement (actsBy_nW_mul_nW _ _), coe_conj_torusElement (actsBy_nW_mul_nW _ _),
    rootDiagUnit_inv, ← rootDiagUnit_mul, tupAct_zpow, tupAct_zpow]
  congr 1
  funext j
  simp only [Pi.mul_apply, Pi.inv_apply, ← zpow_neg, ← zpow_add]
  congr 1
  have := frameD_exponents j
  linarith

end Twist

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit

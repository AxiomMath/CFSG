module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoB2OrderThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bAut
public import CFSG.Quasithin.Background.SmithB42Sp4Nat

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open
open CFSG.Quasithin.B42Sp4 (spM)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (gsp conjSp fieldSp
  statedSp_le_gsp coe_conjSp)
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

@[expose] noncomputable def stspKerCard {F : Type} [Field F] (γ : StatedSp 2 F) : ℕ :=
  kerCardCyclo3 (spM γ)

private theorem kerCardCyclo3_conj_unit {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (P : (Matrix ι ι F)ˣ) (M : Matrix ι ι F) :
    kerCardCyclo3 ((P : Matrix ι ι F) * M * (P⁻¹ : Matrix ι ι F)) = kerCardCyclo3 M := by
  let Q : Matrix ι ι F := (P : Matrix ι ι F) * M * (P⁻¹ : Matrix ι ι F)
  have hQ : Q = (P : Matrix ι ι F) * M * (P⁻¹ : Matrix ι ι F) := rfl
  have hQv : ∀ w : ι → F, Q.mulVec w =
      (P : Matrix ι ι F).mulVec (M.mulVec ((P⁻¹ : Matrix ι ι F).mulVec w)) := by
    intro w
    rw [hQ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hPP' : ∀ w : ι → F,
      (P⁻¹ : Matrix ι ι F).mulVec ((P : Matrix ι ι F).mulVec w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, ← Matrix.coe_units_inv, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mulVec]
  have hPP : ∀ w : ι → F,
      (P : Matrix ι ι F).mulVec ((P⁻¹ : Matrix ι ι F).mulVec w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, ← Matrix.coe_units_inv, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mulVec]
  have hQ2v : ∀ w : ι → F, Q.mulVec (Q.mulVec w) =
      (P : Matrix ι ι F).mulVec (M.mulVec (M.mulVec ((P⁻¹ : Matrix ι ι F).mulVec w))) := by
    intro w
    rw [hQv (Q.mulVec w), hQv w, hPP' (M.mulVec ((P⁻¹ : Matrix ι ι F).mulVec w))]
  have htriple : ∀ v : ι → F,
      Q.mulVec (Q.mulVec v) + Q.mulVec v + v =
      (P : Matrix ι ι F).mulVec (M.mulVec (M.mulVec ((P⁻¹ : Matrix ι ι F).mulVec v)) +
        M.mulVec ((P⁻¹ : Matrix ι ι F).mulVec v) +
          (P⁻¹ : Matrix ι ι F).mulVec v) := by
    intro v
    rw [hQ2v v, hQv v]
    conv_lhs => enter [2]; rw [← hPP v]
    rw [← Matrix.mulVec_add, ← Matrix.mulVec_add]
  have hP0 : ∀ x : ι → F, (P : Matrix ι ι F).mulVec x = 0 → x = 0 := by
    intro x hx
    have h := congrArg (fun y => (P⁻¹ : Matrix ι ι F).mulVec y) hx
    rw [Matrix.mulVec_zero, Matrix.mulVec_mulVec, ← Matrix.coe_units_inv, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h
    exact h
  change kerCardCyclo3 Q = kerCardCyclo3 M
  rw [kerCardCyclo3, kerCardCyclo3]
  refine Nat.card_congr
    { toFun := fun v => ⟨(P⁻¹ : Matrix ι ι F).mulVec v.1, ?_⟩
      invFun := fun w => ⟨(P : Matrix ι ι F).mulVec w.1, ?_⟩
      left_inv := fun v => Subtype.ext (hPP v.1)
      right_inv := fun w => Subtype.ext (hPP' w.1) }
  · exact hP0 _ (by rw [← htriple v.1, v.2])
  · have h := htriple ((P : Matrix ι ι F).mulVec w.1)
    rw [hPP' w.1, w.2, Matrix.mulVec_zero] at h
    exact h

private theorem kerCardCyclo3_submatrix {F ι κ : Type} [Field F]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (σ : ι ≃ κ) (M : Matrix κ κ F) :
    kerCardCyclo3 (M.submatrix σ σ) = kerCardCyclo3 M := by
  let T : (κ → F) ≃+ (ι → F) :=
    { toFun := fun w => w ∘ ⇑σ
      invFun := fun v => v ∘ ⇑σ.symm
      left_inv := fun w => by funext k; simp
      right_inv := fun v => by funext i; simp
      map_add' := fun a b => by funext i; rfl }
  have h1 : ∀ u : κ → F, (M.submatrix σ σ).mulVec (T u) = T (M.mulVec u) := by
    intro u
    change (M.submatrix ⇑σ ⇑σ).mulVec (u ∘ ⇑σ) = T (M.mulVec u)
    rw [Matrix.submatrix_mulVec_equiv M (u ∘ ⇑σ) ⇑σ σ]
    have hcomp : (u ∘ ⇑σ) ∘ ⇑σ.symm = u := by funext a; simp
    rw [hcomp]
    rfl
  have hT : ∀ w : κ → F,
      (M.submatrix σ σ).mulVec ((M.submatrix σ σ).mulVec (T w)) +
        (M.submatrix σ σ).mulVec (T w) + T w =
      T (M.mulVec (M.mulVec w) + M.mulVec w + w) := by
    intro w
    rw [h1 w, h1 (M.mulVec w)]
    funext i
    simp
  rw [kerCardCyclo3, kerCardCyclo3]
  refine Nat.card_congr
    { toFun := fun v => ⟨T.symm v.1, ?_⟩
      invFun := fun w => ⟨T w.1, ?_⟩
      left_inv := fun v => Subtype.ext (T.apply_symm_apply v.1)
      right_inv := fun w => Subtype.ext (T.symm_apply_apply w.1) }
  · have h := hT (T.symm v.1)
    rw [T.apply_symm_apply, v.2] at h
    exact T.injective (by rw [map_zero]; exact h.symm)
  · rw [hT w.1, w.2, map_zero]

private theorem stspKerCard_antiSpEquiv {F : Type} [Field F] [CharP F 2] (g : antiSp F) :
    stspKerCard (antiSpEquiv F g) = kerCardCyclo3 (glMat (g : GL (Fin 4) F)) := by
  rw [stspKerCard]
  change kerCardCyclo3 (spMat (antiSpEquiv F g)) =
    kerCardCyclo3 (glMat (g : GL (Fin 4) F))
  rw [spMat_antiSpEquiv]
  exact kerCardCyclo3_submatrix antiIdx (glMat (g : GL (Fin 4) F))

private theorem mulAut_conj_map {G : Type} [Group G] (σ : MulAut G) (g x : G) :
    σ (MulAut.conj g x) = MulAut.conj (σ g) (σ x) := by
  simp only [MulAut.conj_apply, map_mul, map_inv]

private theorem mulAut_conj_mul {G : Type} [Group G] (g h : G) :
    MulAut.conj (g * h) = MulAut.conj g * MulAut.conj h := by
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem kerCardCyclo3_glMat_conj {F : Type} [Field F] [CharP F 2]
    (g y : antiSp F) :
    kerCardCyclo3 (glMat (MulAut.conj g y : GL (Fin 4) F)) =
      kerCardCyclo3 (glMat (y : GL (Fin 4) F)) := by
  have hmat : (glMat (MulAut.conj g y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        (glMat (y : GL (Fin 4) F)) *
        (((g : GL (Fin 4) F)⁻¹) : Matrix (Fin 4) (Fin 4) F) := by
    rw [MulAut.conj_apply, ← Matrix.coe_units_inv]
    rfl
  rw [hmat]
  exact kerCardCyclo3_conj_unit (P := (g : GL (Fin 4) F))
    (M := glMat (y : GL (Fin 4) F))

theorem two_pow_finrank_ker_aeval_cyclo3_eq {F : Type} [Field F] {M : Type} [AddCommGroup M]
    [Module (ZMod 2) M] [Finite M] (φ : M ≃+ (Fin 2 ⊕ Fin 2 → F)) (T : Module.End (ZMod 2) M)
    (γ : StatedSp 2 F) (hφ : ∀ x, φ (T x) = (spM γ).mulVec (φ x)) :
    2 ^ Module.finrank (ZMod 2)
        (LinearMap.ker (Polynomial.aeval T
          (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial (ZMod 2)))) = stspKerCard γ := by
  have haeval :
      Polynomial.aeval T (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial (ZMod 2)) =
        T ^ 2 + T + 1 := by
    rw [map_add, map_add, map_pow, Polynomial.aeval_X, map_one]
  have hiff : ∀ x : M,
      (((T ^ 2 + T + 1 : Module.End (ZMod 2) M)) x = 0) ↔
      (spM γ).mulVec ((spM γ).mulVec (φ x)) + (spM γ).mulVec (φ x) + φ x = 0 := by
    intro x
    have hx : ((T ^ 2 + T + 1 : Module.End (ZMod 2) M)) x = T (T x) + T x + x := by
      simp only [pow_two, LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply]
    have key : φ (T (T x) + T x + x) =
        (spM γ).mulVec ((spM γ).mulVec (φ x)) + (spM γ).mulVec (φ x) + φ x := by
      rw [map_add, map_add, hφ (T x), hφ x]
    rw [hx]
    constructor
    · intro h
      rw [← key, h, map_zero]
    · intro h
      apply φ.injective
      rw [map_zero, key, h]
  let e : ↥(LinearMap.ker ((T ^ 2 + T + 1 : Module.End (ZMod 2) M))) ≃
      {v : Fin 2 ⊕ Fin 2 → F //
        (spM γ).mulVec ((spM γ).mulVec v) + (spM γ).mulVec v + v = 0} :=
    { toFun := fun x => ⟨φ x.1, (hiff x.1).mp (LinearMap.mem_ker.mp x.2)⟩
      invFun := fun v => ⟨φ.symm v.1,
        LinearMap.mem_ker.mpr ((hiff (φ.symm v.1)).mpr (by simpa using v.2))⟩
      left_inv := fun x => Subtype.ext (φ.symm_apply_apply x.1)
      right_inv := fun v => Subtype.ext (φ.apply_symm_apply v.1) }
  have hcard : Nat.card ↥(LinearMap.ker ((T ^ 2 + T + 1 : Module.End (ZMod 2) M))) =
      stspKerCard γ := by
    rw [stspKerCard, kerCardCyclo3]
    exact Nat.card_congr e
  rw [haeval, ← hcard]
  exact FiniteField.pow_finrank_eq_natCard 2 ↥(LinearMap.ker ((T ^ 2 + T + 1 :
    Module.End (ZMod 2) M)))

theorem exists_order_three_conjSp_mul_fieldSp {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) :
    ∃ x₀ : StatedSp 2 F, x₀ ^ 3 = 1 ∧ ∀ α β : MulAut (StatedSp 2 F),
      stspKerCard (α (β x₀)) = stspKerCard (α x₀) →
        ∃ (A : gsp 2 F) (σ : F ≃+* F), β = conjSp 2 F A * fieldSp 2 F σ := by
  classical
  obtain ⟨x₀', hx₀'3, hx₀'ρ2, hx₀'card, hx₀'ρcard⟩ :=
    exists_order_three_kerCardCyclo3 (F := F)
  obtain ⟨Fr, hFr, -, -⟩ :=
    CFSG.QuasithinUnique.Setup.X7b.exists_frobenius_data (K := F) hn hF
  set e : antiSp F ≃* StatedSp 2 F := antiSpEquiv F with hedef
  set ρ : MulAut (antiSp F) := minorAut F with hρdef
  have hρ2 : (ρ ^ 2) x₀' = x₀' := by
    rw [pow_two, MulAut.mul_apply, hρdef]
    exact hx₀'ρ2
  have hρ2frob : ∀ z : antiSp F, (ρ ^ 2) z = frobHom F z := by
    intro z
    rw [pow_two, MulAut.mul_apply, hρdef]
    exact minorHom_minorHom z
  have hρper : ∀ m : ℕ, (ρ ^ (m + 2)) x₀' = (ρ ^ m) x₀' := by
    intro m
    rw [pow_add, MulAut.mul_apply, hρ2]
  have hρeven : ∀ m : ℕ, Even m → (ρ ^ m) x₀' = x₀' := by
    intro m hm
    obtain ⟨t, ht⟩ := hm
    rw [← two_mul t] at ht
    subst m
    induction t with
    | zero => simp
    | succ t ih =>
      rw [show 2 * (t + 1) = 2 * t + 2 from by ring, hρper]
      exact ih
  have hρodd : ∀ m : ℕ, Odd m → (ρ ^ m) x₀' = ρ x₀' := by
    intro m hm
    obtain ⟨t, ht⟩ := hm
    subst m
    induction t with
    | zero => simp
    | succ t ih =>
      rw [show 2 * (t + 1) + 1 = (2 * t + 1) + 2 from by ring, hρper]
      exact ih
  have hfrob_iter : ∀ k (z : antiSp F),
      e ((ρ ^ (2 * k)) z) = fieldSp 2 F (Fr ^ k) (e z) := by
    intro k
    induction k with
    | zero => intro z; simp
    | succ k ih =>
      intro z
      rw [show 2 * (k + 1) = 2 * k + 2 from by ring, pow_add, MulAut.mul_apply, hρ2frob,
        ih (frobHom F z), hedef, antiSpEquiv_frobHom hFr z, pow_succ, map_mul,
        MulAut.mul_apply]
  have hcard_even : ∀ k,
      kerCardCyclo3 (glMat ((ρ ^ (2 * k)) x₀' : GL (Fin 4) F)) = Nat.card F ^ 2 := by
    intro k
    rw [hρeven (2 * k) ⟨k, by ring⟩, hx₀'card]
  have hcard_odd : ∀ k,
      kerCardCyclo3 (glMat ((ρ ^ (2 * k + 1)) x₀' : GL (Fin 4) F)) = Nat.card F ^ 4 := by
    intro k
    rw [hρodd (2 * k + 1) ⟨k, by ring⟩, hρdef]
    exact hx₀'ρcard
  have htwo : 2 ≤ Nat.card F := by
    rw [hF]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  refine ⟨e x₀', ?_, ?_⟩
  · rw [← map_pow, hx₀'3, map_one]
  · intro α β hαβ
    set α' : MulAut (antiSp F) := (MulAut.congr e).symm α with hα'def
    set β' : MulAut (antiSp F) := (MulAut.congr e).symm β with hβ'def
    have hα'e : ∀ y : antiSp F, α (e y) = e (α' y) := by
      intro y
      have h : (MulAut.congr e) α' = α := MulEquiv.apply_symm_apply (MulAut.congr e) α
      rw [← h]
      simp [MulAut.congr_apply]
    have hβ'e : ∀ y : antiSp F, β (e y) = e (β' y) := by
      intro y
      have h : (MulAut.congr e) β' = β := MulEquiv.apply_symm_apply (MulAut.congr e) β
      rw [← h]
      simp [MulAut.congr_apply]
    have hker : kerCardCyclo3 (glMat (α' (β' x₀') : GL (Fin 4) F)) =
        kerCardCyclo3 (glMat (α' x₀' : GL (Fin 4) F)) := by
      have h1 : α (β (e x₀')) = e (α' (β' x₀')) := by
        rw [hβ'e x₀', hα'e (β' x₀')]
      have h2 : α (e x₀') = e (α' x₀') := hα'e x₀'
      rw [h1, h2, hedef, stspKerCard_antiSpEquiv, stspKerCard_antiSpEquiv] at hαβ
      exact hαβ
    obtain ⟨g₁, i, -, hα'eq⟩ :=
      CFSG.QuasithinUnique.Setup.X7b.aut_eq_conj_mul_pow (K := F) hn hF α'
    obtain ⟨g₂, j, -, hβ'eq⟩ :=
      CFSG.QuasithinUnique.Setup.X7b.aut_eq_conj_mul_pow (K := F) hn hF β'
    rw [← hρdef] at hα'eq hβ'eq
    have hα'x : α' x₀' = MulAut.conj g₁ ((ρ ^ i) x₀') := by
      rw [hα'eq, MulAut.mul_apply]
    have hαβ'x : α' (β' x₀') =
        MulAut.conj (g₁ * (ρ ^ i) g₂) ((ρ ^ (i + j)) x₀') := by
      rw [hα'eq, hβ'eq, MulAut.mul_apply, MulAut.mul_apply, mulAut_conj_map,
        mulAut_conj_mul, ← MulAut.mul_apply]
      congr 1
      rw [← MulAut.mul_apply, ← pow_add]
    rw [hαβ'x, hα'x, kerCardCyclo3_glMat_conj, kerCardCyclo3_glMat_conj] at hker
    have hevenj : Even j := by
      rcases Nat.even_or_odd j with hj | hj
      · exact hj
      · exfalso
        obtain ⟨t, ht⟩ := hj
        rcases Nat.even_or_odd i with hi | hi
        · obtain ⟨s, hs⟩ := hi
          have hsi : i = 2 * s := by rw [hs]; ring
          have hL : kerCardCyclo3 (glMat ((ρ ^ (i + j)) x₀' : GL (Fin 4) F)) =
              Nat.card F ^ 4 := by
            have hij : i + j = 2 * (s + t) + 1 := by rw [hsi, ht]; ring
            rw [hij, hcard_odd]
          have hR : kerCardCyclo3 (glMat ((ρ ^ i) x₀' : GL (Fin 4) F)) =
              Nat.card F ^ 2 := by
            rw [hsi, hcard_even]
          rw [hL, hR] at hker
          exact (ne_of_lt (Nat.pow_lt_pow_right (by omega) (by norm_num))) hker.symm
        · obtain ⟨s, hs⟩ := hi
          have hsi : i = 2 * s + 1 := by rw [hs]
          have hL : kerCardCyclo3 (glMat ((ρ ^ (i + j)) x₀' : GL (Fin 4) F)) =
              Nat.card F ^ 2 := by
            have hij : i + j = 2 * (s + t + 1) := by rw [hsi, ht]; ring
            rw [hij, hcard_even]
          have hR : kerCardCyclo3 (glMat ((ρ ^ i) x₀' : GL (Fin 4) F)) =
              Nat.card F ^ 4 := by
            rw [hsi, hcard_odd]
          rw [hL, hR] at hker
          exact (ne_of_lt (Nat.pow_lt_pow_right (by omega) (by norm_num))) hker
    obtain ⟨k, hk⟩ := hevenj
    have hk2 : j = 2 * k := by rw [hk]; ring
    let A : gsp 2 F := ⟨(e g₂ : GL (Fin 2 ⊕ Fin 2) F), statedSp_le_gsp (e g₂).2⟩
    refine ⟨A, Fr ^ k, ?_⟩
    refine MulEquiv.ext fun y => ?_
    calc β y = e (β' (e.symm y)) := by
          simpa using hβ'e (e.symm y)
      _ = e (g₂ * (ρ ^ j) (e.symm y) * g₂⁻¹) := by
          rw [hβ'eq, MulAut.mul_apply, MulAut.conj_apply]
      _ = e (g₂ * (ρ ^ (2 * k)) (e.symm y) * g₂⁻¹) := by rw [hk2]
      _ = e g₂ * e ((ρ ^ (2 * k)) (e.symm y)) * (e g₂)⁻¹ := by
          rw [map_mul, map_mul, map_inv]
      _ = e g₂ * (fieldSp 2 F (Fr ^ k) (e (e.symm y))) * (e g₂)⁻¹ := by
          rw [hfrob_iter k (e.symm y)]
      _ = e g₂ * (fieldSp 2 F (Fr ^ k) y) * (e g₂)⁻¹ := by
          rw [MulEquiv.apply_symm_apply]
      _ = (conjSp 2 F A * fieldSp 2 F (Fr ^ k)) y := by
          rw [MulAut.mul_apply]
          apply Subtype.ext
          rw [coe_conjSp]
          rfl


end CFSG.LocalAnalysis.RankThreeUC.S15

end

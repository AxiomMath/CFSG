module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDDischarge
public import CFSG.ClassicalInvolution.WeakCT.SU4SpinMinusFinal
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutMain
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Models.TwistedPairs
open CFSG.ClassicalInvolution.WeakCT
  (torusHom diagConj2 coe_diagConj2 coe_torusHom torusHom_injective)
open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.LieType.Universal (minusCoeffs minusCoeffs_irr)
open CFSG.ClassicalInvolution.Phan (Su)
open scoped MatrixGroups

namespace T7Z

section SL2

variable {E : Type} [Field E]

@[expose] def wE : SL(2, E) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two_of]⟩

theorem coe_wE : ((wE : SL(2, E)) : Matrix (Fin 2) (Fin 2) E) = !![0, 1; -1, 0] := rfl

theorem coe_wE_inv : (((wE : SL(2, E))⁻¹ : SL(2, E)) : Matrix (Fin 2) (Fin 2) E) =
    !![0, -1; 1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, coe_wE, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem wE_mul_self : (wE : SL(2, E)) * wE = torusHom E (-1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_wE, coe_torusHom, Matrix.mul_apply, Fin.sum_univ_two]

theorem torusHom_neg_one_eq : (torusHom E (-1) : SL(2, E)) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_torusHom]

theorem diagConj2_neg_one_wE : diagConj2 (-1 : Eˣ) 1 (wE : SL(2, E)) =
    torusHom E (-1) * wE := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_diagConj2, coe_wE, coe_torusHom, Matrix.mul_apply, Matrix.diagonal_apply,
      Fin.sum_univ_two]

theorem diagConj2_comp (a b a' b' : Eˣ) (X : SL(2, E)) :
    diagConj2 a b (diagConj2 a' b' X) = diagConj2 (a * a') (b * b') X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_diagConj2, Matrix.mul_apply, Matrix.diagonal_apply] <;>
    field_simp

theorem diagConj2_self' (a : Eˣ) (X : SL(2, E)) : diagConj2 a a X = X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_diagConj2, Matrix.mul_apply, Matrix.diagonal_apply] <;>
    field_simp

theorem wE_mul_diagConj2 (a b : Eˣ) (X : SL(2, E)) :
    wE * diagConj2 a b X * wE⁻¹ = diagConj2 b a (wE * X * wE⁻¹) := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_diagConj2, coe_wE, coe_wE_inv]
  rw [Matrix.eta_fin_two (X : Matrix (Fin 2) (Fin 2) E)]
  simp only [Matrix.diagonal_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.mul_fin_two]
  fin_cases i <;> fin_cases j <;> simp

theorem diagConj2_swap_wE (μ : Eˣ) (B : SL(2, E)) :
    diagConj2 μ 1 (wE * diagConj2 μ 1 (wE⁻¹ * B * wE) * wE⁻¹) = B := by
  rw [wE_mul_diagConj2]
  have : wE * (wE⁻¹ * B * wE) * wE⁻¹ = B := by group
  rw [this, diagConj2_comp, show μ * 1 = μ from mul_one μ, show 1 * μ = μ from one_mul μ,
    diagConj2_self']

end SL2

section Spin

variable {F : Type} [Field F] [Finite F] {b c : F} [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)]


omit [Finite F] [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] in
theorem spinNu_neg_one : spinNu b c (-1 : (ShortField b c)ˣ) = 1 := by
  apply Units.ext
  rw [spinNu, Units.val_inv_eq_inv_val, Units.coe_map]
  simp

omit [Finite F] [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] in
theorem spinMu_neg_one : spinMu b c (-1 : Fˣ) = (-1 : (ShortField b c)ˣ) := by
  apply Units.ext
  rw [spinMu, Units.coe_map]
  simp

theorem spin_core (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (h2 : (2 : F) ≠ 0)
    (hg6 : RouteD.SpinMinus6Generated hirr) {ω : F} (hω : ω * ω = -1) :
    ∃ (x a n c₀ : spinGroup (quadMinus 3 F b c)),
      x ∈ (spinMinusModel hirr).lb.range ∧ a ∈ (spinMinusModel hirr).lb.range ∧
      n ∈ (spinMinusModel hirr).sb.range ∧
      c₀ ∈ Subgroup.center (spinGroup (quadMinus 3 F b c)) ∧ c₀ ≠ 1 ∧ x * x = 1 ∧ x ≠ 1 ∧
      a * a = x ∧ x * n * x⁻¹ = c₀ * n ∧ n * x * n⁻¹ = c₀ * x ∧
      ∀ B : SL(2, ShortField b c), (a * (n * a * n⁻¹)) * (spinMinusModel hirr).sb B *
        (a * (n * a * n⁻¹))⁻¹ = (spinMinusModel hirr).sb B := by
  classical
  set P := spinMinusModel hirr with hP
  have hω0 : ω ≠ 0 := fun h => by
    rw [h, mul_zero] at hω
    exact one_ne_zero (neg_eq_zero.mp hω.symm)
  let u : Fˣ := Units.mk0 ω hω0
  have hu2 : u * u = -1 := Units.ext (by simp [u, hω])
  have hlb : Function.Injective P.lb := RouteD.injective_minusLongBlock hirr h2
  have hsb : Function.Injective P.sb := shortBlock_injective hirr h2 3 finOne
  have h2E : (2 : ShortField b c) ≠ 0 := fun h => by
    have h' : algebraMap F (ShortField b c) (2 : F) = (2 : ShortField b c) := map_ofNat _ 2
    exact h2 ((algebraMap F (ShortField b c)).injective (by rw [h', h, map_zero]))
  have hm1F : (-1 : Fˣ) ≠ 1 := fun h => h2 (by
    have := congrArg (fun v : Fˣ => (v : F)) h
    simp at this
    linear_combination -this)
  have hm1E : (-1 : (ShortField b c)ˣ) ≠ 1 := fun h => h2E (by
    have := congrArg (fun v : (ShortField b c)ˣ => (v : ShortField b c)) h
    simp at this
    linear_combination -this)
  set x : spinGroup (quadMinus 3 F b c) := P.lb (torusHom F (-1)) with hx
  set a : spinGroup (quadMinus 3 F b c) := P.lb (torusHom F u) with ha
  set n : spinGroup (quadMinus 3 F b c) := P.sb wE with hn
  set c₀ : spinGroup (quadMinus 3 F b c) := P.sb (torusHom (ShortField b c) (-1)) with hc₀
  have haa : a * a = x := by
    rw [ha, hx, ← map_mul, ← map_mul, hu2]
  have hx2 : x * x = 1 := by
    rw [hx, ← map_mul, ← map_mul, show (-1 : Fˣ) * -1 = 1 by simp, map_one, map_one]
  have hx1 : x ≠ 1 := fun h => hm1F (torusHom_injective (K := F) (hlb (by
    rw [← hx, h, map_one, map_one])))
  have hc₀1 : c₀ ≠ 1 := fun h => hm1E (torusHom_injective (K := ShortField b c) (hsb (by
    rw [← hc₀, h, map_one, map_one])))
  have hc₀2 : c₀ * c₀ = 1 := by
    rw [hc₀, ← map_mul, ← map_mul, show (-1 : (ShortField b c)ˣ) * -1 = 1 by simp, map_one,
      map_one]
  have hnn : n * n = c₀ := by
    rw [hn, hc₀, ← map_mul, wE_mul_self]
  have hcen : c₀ ∈ Subgroup.center (spinGroup (quadMinus 3 F b c)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hle : P.lb.range ⊔ P.sb.range ≤ Subgroup.centralizer ({c₀} : Set _) := by
      refine sup_le ?_ ?_
      · rintro _ ⟨A, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h := P.conj_sl (-1) A
        have hν : P.nu (-1) = 1 := spinNu_neg_one
        rw [hν, diagConj2_self'] at h
        have h' : c₀ * P.lb A * c₀⁻¹ = P.lb A := h
        exact (mul_inv_eq_iff_eq_mul.mp h').symm
      · rintro _ ⟨B, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff, hc₀, torusHom_neg_one_eq, ← map_mul,
          ← map_mul]
        congr 1
        exact Subgroup.mem_center_iff.mp ((CFSG.ClassicalInvolution.mem_center_sl2_iff
          (-1 : SL(2, ShortField b c))).mpr (Or.inr rfl)) B
    have hy : y ∈ P.lb.range ⊔ P.sb.range := by rw [hg6]; trivial
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  have hc₀c : ∀ g, g * c₀ = c₀ * g := fun g => Subgroup.mem_center_iff.mp hcen g
  have hxn : x * n * x⁻¹ = c₀ * n := by
    have h := P.conj_ls (-1) wE
    have hμ : P.mu (-1) = -1 := spinMu_neg_one
    rw [hμ, diagConj2_neg_one_wE, map_mul] at h
    exact h
  have hnx : n * x * n⁻¹ = c₀ * x := by
    have h1 : x * n = c₀ * n * x := by
      have := hxn
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    have hninv : n⁻¹ = n * c₀ := by
      apply inv_eq_of_mul_eq_one_right
      calc n * (n * c₀) = (n * n) * c₀ := by group
        _ = c₀ * c₀ := by rw [hnn]
        _ = 1 := hc₀2
    rw [hninv]
    calc n * x * (n * c₀) = n * (x * n) * c₀ := by group
      _ = n * (c₀ * n * x) * c₀ := by rw [h1]
      _ = n * c₀ * (n * x) * c₀ := by group
      _ = c₀ * n * (n * x) * c₀ := by rw [← hc₀c n]
      _ = c₀ * (n * n) * x * c₀ := by group
      _ = c₀ * c₀ * x * c₀ := by rw [hnn]
      _ = x * c₀ := by rw [hc₀2, one_mul]
      _ = c₀ * x := hc₀c x
  have hkey : ∀ B : SL(2, ShortField b c), (a * (n * a * n⁻¹)) * P.sb B *
      (a * (n * a * n⁻¹))⁻¹ = P.sb B := by
    intro B
    have ha_act : ∀ B' : SL(2, ShortField b c), a * P.sb B' * a⁻¹ =
        P.sb (diagConj2 (P.mu u) 1 B') := fun B' => P.conj_ls u B'
    have hn_act : n⁻¹ * P.sb B * n = P.sb (wE⁻¹ * B * wE) := by
      rw [hn, ← map_inv, ← map_mul, ← map_mul]
    have hn_act' : ∀ B' : SL(2, ShortField b c), n * P.sb B' * n⁻¹ = P.sb (wE * B' * wE⁻¹) := by
      intro B'
      rw [hn, ← map_inv, ← map_mul, ← map_mul]
    calc (a * (n * a * n⁻¹)) * P.sb B * (a * (n * a * n⁻¹))⁻¹
        = a * (n * (a * (n⁻¹ * P.sb B * n) * a⁻¹) * n⁻¹) * a⁻¹ := by group
      _ = a * (n * (a * P.sb (wE⁻¹ * B * wE) * a⁻¹) * n⁻¹) * a⁻¹ := by rw [hn_act]
      _ = a * (n * P.sb (diagConj2 (P.mu u) 1 (wE⁻¹ * B * wE)) * n⁻¹) * a⁻¹ := by
        rw [ha_act]
      _ = a * P.sb (wE * diagConj2 (P.mu u) 1 (wE⁻¹ * B * wE) * wE⁻¹) * a⁻¹ := by
        rw [hn_act']
      _ = P.sb (diagConj2 (P.mu u) 1 (wE * diagConj2 (P.mu u) 1 (wE⁻¹ * B * wE) * wE⁻¹)) := by
        rw [ha_act]
      _ = P.sb B := by rw [diagConj2_swap_wE]
  exact ⟨x, a, n, c₀, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, hcen, hc₀1, hx2, hx1, haa, hxn, hnx, hkey⟩

end Spin


section Adapted

variable {p f : ℕ} [Fact p.Prime]
  [Fact (∀ r : GaloisField p f, r ^ 2 ≠ -(minusCoeffs p f).2 + (minusCoeffs p f).1 * r)]


theorem spin_adapted (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {ω : GaloisField p f} (hω : ω * ω = -1) :
    ∃ e : spinGroup (quadMinus 3 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2) ≃*
        Su (GaloisField p (2 * f)) p f 4,
      ∃ (Rs' : Subgroup (Su (GaloisField p (2 * f)) p f 4))
        (x x' a b : Su (GaloisField p (2 * f)) p f 4),
        (spinMinusModel (minusCoeffs_irr p f)).lb.range.map e.toMonoidHom ∈
          longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) (by norm_num : 2 ≤ 4) ∧
        Rs' ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f)
          (by norm_num : 2 ≤ 4) ∧
        (spinMinusModel (minusCoeffs_irr p f)).lb.range.map e.toMonoidHom ≠ Rs' ∧
        x ∈ (spinMinusModel (minusCoeffs_irr p f)).lb.range.map e.toMonoidHom ∧ x * x = 1 ∧
        x ≠ 1 ∧ x' ∈ Rs' ∧ x' * x' = 1 ∧ x' ≠ 1 ∧
        x' * x⁻¹ ∈ Subgroup.center (Su (GaloisField p (2 * f)) p f 4) ∧
        a ∈ (spinMinusModel (minusCoeffs_irr p f)).lb.range.map e.toMonoidHom ∧ a * a = x ∧
        b ∈ Rs' ∧ b * b = x' ∧
        (spinMinusModel (minusCoeffs_irr p f)).sb.range.map e.toMonoidHom ≤
          Subgroup.centralizer ({a * b} : Set (Su (GaloisField p (2 * f)) p f 4)) ∧
        (spinMinusModel (minusCoeffs_irr p f)).lb.range.map e.toMonoidHom ⊔
          (spinMinusModel (minusCoeffs_irr p f)).sb.range.map e.toMonoidHom = ⊤ := by
  classical
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have : NeZero (2 * f) := ⟨by omega⟩
  have hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 :=
    ModelFacts.UnitaryAut.card_galoisField_two_mul_eq hq
  have h2 : (2 : GaloisField p f) ≠ 0 := ModelFacts.two_ne_zero_galoisField f hp2
  obtain ⟨e, he⟩ := WeakCT.SU4.su4SpinMinus_galois hp2 hq
  have hg6 : RouteD.SpinMinus6Generated (minusCoeffs_irr p f) :=
    RouteD.spinMinus6Generated_galois hp2
  obtain ⟨x, a, n, c₀, hxlb, halb, hnsb, hcen, hc₀1, hx2, hx1, haa, hxn, hnx, hkey⟩ :=
    spin_core (minusCoeffs_irr p f) h2 hg6 hω
  set Rs : Subgroup (Su (GaloisField p (2 * f)) p f 4) :=
    (spinMinusModel (minusCoeffs_irr p f)).lb.range.map e.toMonoidHom with hRs
  have hRsL : Rs ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f)
      (by norm_num : 2 ≤ 4) := he
  set N := e n with hN
  set X := e x with hX
  set A := e a with hA
  set C₀ := e c₀ with hC₀
  set Rs' : Subgroup (Su (GaloisField p (2 * f)) p f 4) := Rs.map (MulAut.conj N).toMonoidHom
    with hRs'
  have hRs'L : Rs' ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f)
      (by norm_num : 2 ≤ 4) := by
    obtain ⟨i, hi⟩ := hRsL
    exact ⟨_, hi.conj N⟩
  have hXRs : X ∈ Rs := Subgroup.mem_map.mpr ⟨x, hxlb, rfl⟩
  have hARs : A ∈ Rs := Subgroup.mem_map.mpr ⟨a, halb, rfl⟩
  have hX2 : X * X = 1 := by rw [hX, ← map_mul, hx2, map_one]
  have hX1 : X ≠ 1 := fun h => hx1 (e.injective (by rw [← hX, h, map_one]))
  have hAA : A * A = X := by rw [hA, hX, ← map_mul, haa]
  have hx'eq : N * X * N⁻¹ = C₀ * X := by
    rw [hN, hX, hC₀, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hnx]
  have hx'Rs' : N * X * N⁻¹ ∈ Rs' := Subgroup.mem_map.mpr ⟨X, hXRs, by simp [MulAut.conj_apply]⟩
  have hbRs' : N * A * N⁻¹ ∈ Rs' := Subgroup.mem_map.mpr ⟨A, hARs, by simp [MulAut.conj_apply]⟩
  have hx'2 : (N * X * N⁻¹) * (N * X * N⁻¹) = 1 := by
    calc (N * X * N⁻¹) * (N * X * N⁻¹) = N * (X * X) * N⁻¹ := by group
      _ = 1 := by rw [hX2]; group
  have hx'1 : N * X * N⁻¹ ≠ 1 := fun h => hX1 (by
    have : N * X * N⁻¹ = N * 1 * N⁻¹ := by rw [h]; group
    exact mul_left_cancel (mul_right_cancel this))
  have hC₀c : C₀ ∈ Subgroup.center (Su (GaloisField p (2 * f)) p f 4) :=
    (MulEquivClass.apply_mem_center_iff e).2 hcen
  have hx'c : (N * X * N⁻¹) * X⁻¹ ∈ Subgroup.center (Su (GaloisField p (2 * f)) p f 4) := by
    rw [hx'eq, mul_inv_cancel_right]
    exact hC₀c
  have hbb : (N * A * N⁻¹) * (N * A * N⁻¹) = N * X * N⁻¹ := by
    calc (N * A * N⁻¹) * (N * A * N⁻¹) = N * (A * A) * N⁻¹ := by group
      _ = N * X * N⁻¹ := by rw [hAA]
  have hne : Rs ≠ Rs' := by
    intro h
    obtain ⟨i, hi⟩ := hRsL
    have hord : ∀ t : Su (GaloisField p (2 * f)) p f 4, t * t = 1 → t ≠ 1 → orderOf t = 2 :=
      fun t ht2 ht1 => orderOf_eq_prime (by rwa [pow_two]) ht1
    have h1 : X = i := hi.eq_of_orderOf_eq_two hK hp2 hXRs (hord X hX2 hX1)
    have h2' : N * X * N⁻¹ = i := hi.eq_of_orderOf_eq_two hK hp2 (h ▸ hx'Rs')
      (hord _ hx'2 hx'1)
    apply hc₀1
    apply e.injective
    have : C₀ * X = X := by rw [← hx'eq, h2', h1]
    rw [map_one, ← hC₀]
    exact mul_right_cancel (this.trans (one_mul X).symm)
  refine ⟨e, Rs', X, N * X * N⁻¹, A, N * A * N⁻¹, hRsL, hRs'L, hne, hXRs, hX2, hX1, hx'Rs',
    hx'2, hx'1, hx'c, hARs, hAA, hbRs', hbb, ?_, ?_⟩
  · rintro _ ⟨s, ⟨B, rfl⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := congrArg e.toMonoidHom (hkey B)
    simp only [map_mul, map_inv, MulEquiv.coe_toMonoidHom] at h
    have h' : (A * (N * A * N⁻¹)) * e ((spinMinusModel (minusCoeffs_irr p f)).sb B) *
        (A * (N * A * N⁻¹))⁻¹ = e ((spinMinusModel (minusCoeffs_irr p f)).sb B) := h
    exact (mul_inv_eq_iff_eq_mul.mp h').symm
  · rw [← Subgroup.map_sup, hg6, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr e.surjective

end Adapted

end T7Z

end CFSG.ClassicalInvolution.Asc77

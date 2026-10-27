module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3GraphAut
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3Abs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3CharVec
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3Cross
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Sl2Triv
public import CFSG.GH74.KGroups.L3EpsInvLin

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.GLS.Stage4.Hex CFSG.ComponentClassification CFSG.ComponentClassification.Burgoyne.PSL
  CFSG.GH74.KGroups.L3Eps
open scoped MatrixGroups commutatorElement

variable {F : Type} [Field F]

structure FL3GraphOrth (R : GL (Fin 3) F) (Ω : Subgroup SL(3, F)) : Prop where
  isometry : Ω ≤ isometrySL 3 R
  perfect : Group.IsPerfect Ω
  irred : ∀ W : Submodule F (Fin 3 → F),
    (∀ g ∈ Ω, ∀ v ∈ W, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤
  comm : ∀ T : Matrix (Fin 3) (Fin 3) F,
    (∀ g ∈ Ω, T * (g : Matrix (Fin 3) (Fin 3) F) = (g : Matrix (Fin 3) (Fin 3) F) * T) →
      ∃ c : F, T = c • (1 : Matrix (Fin 3) (Fin 3) F)
  traces : ∀ σ : F ≃+* F, (∀ g ∈ Ω, σ (Matrix.trace (g : Matrix (Fin 3) (Fin 3) F)) =
    Matrix.trace (g : Matrix (Fin 3) (Fin 3) F)) → σ = 1
  sl2 : ∃ ι : SL(2, F) →* SL(3, F), ι.range = Ω


theorem fl3g_proj_eq_one_of_commute [Finite F] {Ω : Subgroup SL(3, F)} (hperf : Group.IsPerfect Ω)
    (hcomm : ∀ T : Matrix (Fin 3) (Fin 3) F,
      (∀ g ∈ Ω, T * (g : Matrix (Fin 3) (Fin 3) F) = (g : Matrix (Fin 3) (Fin 3) F) * T) →
        ∃ c : F, T = c • (1 : Matrix (Fin 3) (Fin 3) F))
    {y : SL(3, F)} (hy : ∀ g ∈ Ω, proj 3 F y * proj 3 F g = proj 3 F g * proj 3 F y) :
    proj 3 F y = 1 := by
  set A : GL (Fin 3) F := SpecialLinearGroup.toGL y with hA
  have hfix : ∀ g ∈ Ω, proj 3 F (semiSL A 1 g) = proj 3 F g := by
    intro g hg
    rw [← beta_proj, map_one, mul_one, hA, LinearFlag.conjAut_toGL, MulAut.conj_apply]
    rw [hy g hg]; group
  have hf1 := semiSL_fix_of_perfect A 1 hperf hfix
  have hAcomm : ∀ g ∈ Ω, (y : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F) =
      (g : Matrix (Fin 3) (Fin 3) F) * y := by
    intro g hg
    have h1 := congrArg (fun x : SL(3, F) => (x : Matrix (Fin 3) (Fin 3) F)) (hf1 g hg)
    simp only [coe_semiSL] at h1
    have h2 : (g : Matrix (Fin 3) (Fin 3) F).map ⇑(1 : F ≃+* F) = (g : Matrix (Fin 3) (Fin 3) F) := by
      ext i j; rfl
    rw [h2] at h1
    have h3 : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hAy : (A : Matrix (Fin 3) (Fin 3) F) = (y : Matrix (Fin 3) (Fin 3) F) := rfl
    rw [← hAy]
    calc (A : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F)
        = (A : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F) *
            ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) := by
          rw [Matrix.mul_assoc _ _ (A : Matrix (Fin 3) (Fin 3) F), h3, Matrix.mul_one]
      _ = (g : Matrix (Fin 3) (Fin 3) F) * A := by rw [h1]
  obtain ⟨c, hc⟩ := hcomm _ hAcomm
  rw [proj_eq_one_iff]
  have hdet : (y : Matrix (Fin 3) (Fin 3) F).det = 1 := y.2
  rw [hc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hdet
    exact zero_ne_one hdet
  refine ⟨Units.mk0 c hc0, ?_, ?_⟩
  · apply Units.ext
    simpa using hdet
  · rw [hc, smul_one_eq_diagonal]
    rfl


section Setup

variable {A : Type} [Group A] {K : Subgroup A} [K.Normal] (e : ↥K ≃* projectiveSL 3 F)

omit [K.Normal] in
theorem phi_fixes_of_isometry {Asym : GL (Fin 3) F} {φ : MulAut ↥K}
    (hφ : ∀ k, e (φ k) = (conjAut 3 F Asym * dualAut 3 F) (e k))
    {Ω : Subgroup SL(3, F)} (hΩ : Ω ≤ isometrySL 3 Asym⁻¹) {k : ↥K}
    (hk : k ∈ subgroupOfEquiv e (Ω.map (proj 3 F))) : φ k = k := by
  rw [mem_subgroupOfEquiv] at hk
  obtain ⟨g, hg, hgk⟩ := Subgroup.mem_map.1 hk
  apply e.injective
  rw [hφ, ← hgk, conjAut_mul_dualAut_proj, (graphLift_eq_iff Asym g).2 (hΩ hg)]


omit [K.Normal] in
theorem fl3g_X0_bot_of_char [Finite F] {r : ℕ} [Fact r.Prime] [CharP F r]
    {Ω : Subgroup SL(3, F)}
    (hirr : ∀ W : Submodule F (Fin 3 → F),
      (∀ g ∈ Ω, ∀ v ∈ W, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤)
    {X : Subgroup A} (hX : IsPGroup r ↥X)
    (hnorm : ∀ k ∈ subgroupOfEquiv e (Ω.map (proj 3 F)),
      (k : A) ∈ normalizer ((X ⊓ K : Subgroup A) : Set A)) :
    X ⊓ K = ⊥ := by
  classical
  set X0 : Subgroup A := X ⊓ K with hX0
  set Yk : Subgroup ↥K := X0.subgroupOf K with hYk
  have hYkp : IsPGroup r ↥Yk := by
    let f : ↥Yk →* ↥X := ((K.subtype.comp Yk.subtype).codRestrict X
      (fun y => (Subgroup.mem_subgroupOf.1 y.2).1))
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ↥X => (z : A)) hab
    exact hX.of_injective f hf
  set YP : Subgroup (projectiveSL 3 F) := Yk.map e.toMonoidHom with hYP
  have hYPp : IsPGroup r ↥YP := hYkp.map e.toMonoidHom
  obtain ⟨Yh, hYh, hmap, hnormY⟩ := exists_lift_isPGroup_proj r YP hYPp
  obtain ⟨v, hv0, hv⟩ := exists_fixed_vector_sl3 r Yh hYh
  have hnormΩ : ∀ g ∈ Ω, g ∈ normalizer (Yh : Set SL(3, F)) := by
    intro g hg
    apply hnormY
    have hk : e.symm (proj 3 F g) ∈ subgroupOfEquiv e (Ω.map (proj 3 F)) := by
      rw [mem_subgroupOfEquiv, MulEquiv.apply_symm_apply]
      exact Subgroup.mem_map_of_mem _ hg
    have hn := hnorm _ hk
    have hnK : e.symm (proj 3 F g) ∈ normalizer ((Yk : Subgroup ↥K) : Set ↥K) := by
      rw [Subgroup.mem_normalizer_iff] at hn ⊢
      intro y
      have := hn (y : A)
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact this
    have h1 : proj 3 F g ∈ (normalizer ((Yk : Subgroup ↥K) : Set ↥K)).map e.toMonoidHom :=
      ⟨e.symm (proj 3 F g), hnK, by simp⟩
    rw [Subgroup.map_equiv_normalizer_eq] at h1
    exact h1
  let W : Submodule F (Fin 3 → F) :=
    { carrier := {w | ∀ y ∈ Yh, (y : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w}
      add_mem' := fun {a b} ha hb y hy => by simp [Matrix.mulVec_add, ha y hy, hb y hy]
      zero_mem' := fun y hy => by simp
      smul_mem' := fun c a ha y hy => by simp [Matrix.mulVec_smul, ha y hy] }
  have hWinv : ∀ g ∈ Ω, ∀ w ∈ W, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ W := by
    intro g hg w hw y hy
    have hg1 := hnormΩ g hg
    have hg2 : g⁻¹ ∈ normalizer (Yh : Set SL(3, F)) := Subgroup.inv_mem _ hg1
    have hy' : g⁻¹ * y * g ∈ Yh := by
      have := (Subgroup.mem_normalizer_iff.1 hg2 y).1 hy
      simpa using this
    have h2 : g * (g⁻¹ * y * g) = y * g := by group
    calc (y : Matrix (Fin 3) (Fin 3) F) *ᵥ ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ w)
        = ((y * g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ w := by
          rw [Matrix.mulVec_mulVec, Matrix.SpecialLinearGroup.coe_mul]
      _ = ((g * (g⁻¹ * y * g) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ w := by rw [h2]
      _ = (g : Matrix (Fin 3) (Fin 3) F) *ᵥ (((g⁻¹ * y * g : SL(3, F)) :
            Matrix (Fin 3) (Fin 3) F) *ᵥ w) := by
          rw [Matrix.mulVec_mulVec, Matrix.SpecialLinearGroup.coe_mul]
      _ = (g : Matrix (Fin 3) (Fin 3) F) *ᵥ w := by rw [hw _ hy']
  rcases hirr W hWinv with hW | hW
  · exfalso
    have hvW : v ∈ W := fun y hy => hv y hy
    rw [hW] at hvW
    exact hv0 ((Submodule.mem_bot F).1 hvW)
  · have hYh1 : ∀ y ∈ Yh, y = 1 := by
      intro y hy
      have hall : ∀ w : Fin 3 → F, (y : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w := by
        intro w
        have : w ∈ W := by rw [hW]; trivial
        exact this y hy
      apply Subtype.ext
      ext i j
      have := congrFun (hall (Pi.single j 1)) i
      simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this
    have hYhbot : Yh = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hYh1
    have hYPbot : YP = ⊥ := by rw [← hmap, hYhbot, Subgroup.map_bot]
    have hYkbot : Yk = ⊥ := by
      have : Yk.map e.toMonoidHom = ⊥ := hYPbot
      rw [Subgroup.map_eq_bot_iff_of_injective _ e.injective] at this
      exact this
    refine (Subgroup.eq_bot_iff_forall _).2 fun a ha => ?_
    have haK : a ∈ K := ha.2
    have : (⟨a, haK⟩ : ↥K) ∈ Yk := Subgroup.mem_subgroupOf.2 ha
    rw [hYkbot, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this


omit [K.Normal] in
theorem fl3g_X0_bot_of_cross [Finite A] [Finite F] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) (hpF : ¬ p ∣ Nat.card F) {R : GL (Fin 3) F}
    {Ω : Subgroup SL(3, F)} (hΩ : FL3GraphOrth R Ω) {X : Subgroup A} (hX : IsPGroup p ↥X)
    (hnorm : ∀ k ∈ subgroupOfEquiv e (Ω.map (proj 3 F)),
      (k : A) ∈ normalizer ((X ⊓ K : Subgroup A) : Set A)) :
    X ⊓ K = ⊥ := by
  classical
  obtain ⟨ι₀, hι₀⟩ := hΩ.sl2
  let ι : SL2 F →* A := K.subtype.comp ((e.symm : projectiveSL 3 F →* ↥K).comp ((proj 3 F).comp ι₀))
  have hmemΩ : ∀ g, e.symm (proj 3 F (ι₀ g)) ∈ subgroupOfEquiv e (Ω.map (proj 3 F)) := by
    intro g
    rw [mem_subgroupOfEquiv, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_map_of_mem _ (hι₀ ▸ ⟨g, rfl⟩)
  have hnormι : ∀ g, ι g ∈ normalizer (((X ⊓ K : Subgroup A) : Subgroup A) : Set A) := fun g =>
    hnorm _ (hmemΩ g)
  have hX0 : IsPGroup p ↥(X ⊓ K) := hX.to_le inf_le_left
  rcases sl2_centralizes_or_large hp2 hodd h5 hpF ι hX0 hnormι with hcen | hlarge
  · refine (Subgroup.eq_bot_iff_forall _).2 fun a ha => ?_
    have haK : a ∈ K := ha.2
    obtain ⟨y, hy⟩ := proj_surjective 3 F (e ⟨a, haK⟩)
    have hyc : ∀ g ∈ Ω, proj 3 F y * proj 3 F g = proj 3 F g * proj 3 F y := by
      intro g hg
      obtain ⟨g', rfl⟩ : g ∈ ι₀.range := hι₀ ▸ hg
      have h1 := hcen g' a ha
      have h2 : (e.symm (proj 3 F (ι₀ g')) : ↥K) * ⟨a, haK⟩ = ⟨a, haK⟩ * e.symm (proj 3 F (ι₀ g')) :=
        Subtype.ext h1
      have h3 := congrArg e h2
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, ← hy] at h3
      exact h3.symm
    have := fl3g_proj_eq_one_of_commute hΩ.perfect hΩ.comm hyc
    rw [hy] at this
    have h4 : (⟨a, haK⟩ : ↥K) = 1 := e.injective (by rw [this, map_one])
    exact congrArg Subtype.val h4
  · exfalso
    have hdvd : Nat.card ↥(X ⊓ K) ∣ Nat.card ↥K := Subgroup.card_dvd_of_le inf_le_right
    have hle : padicValNat p (Nat.card ↥(X ⊓ K)) ≤ padicValNat p (Nat.card ↥K) :=
      (padicValNat_dvd_iff_le Nat.card_pos.ne').1
        ((pow_padicValNat_dvd (p := p) (n := Nat.card ↥(X ⊓ K))).trans hdvd)
    have hK : Nat.card ↥K = psl3Order (Nat.card F) := by
      rw [Nat.card_congr e.toEquiv]
      exact card_projectiveSL_three
    have := padicValNat_psl3Order_lt hodd h5 hp2 hpF
    rw [hK] at hle
    omega


theorem fl3g_conjAutEquiv_pow {K X : Type*} [Group K] [Group X] (e : K ≃* X) (σ : MulAut K) (n : ℕ) :
    conjAutEquiv e σ ^ n = conjAutEquiv e (σ ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, conjAutEquiv_one]
  | succ n ih => rw [pow_succ, pow_succ, ih, conjAutEquiv_mul]

theorem fl3g_false_of_X0_bot [Finite F] {Asym : GL (Fin 3) F} {φ : MulAut ↥K}
    (hφ : ∀ k, e (φ k) = (conjAut 3 F Asym * dualAut 3 F) (e k))
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {X : Subgroup A} (hX : IsPGroup p ↥X) (hX1 : X ≠ ⊥)
    (hfaith : X ⊓ centralizer (K : Set A) = ⊥)
    (hJ : ∀ j : ↥K, φ j = j → (j : A) ∈ normalizer (X : Set A)) {Ω : Subgroup SL(3, F)}
    (hiso : Ω ≤ isometrySL 3 Asym⁻¹)
    (hlift : ∀ (A : GL (Fin 3) F) (σ : F ≃+* F),
      (∀ g ∈ Ω, proj 3 F (semiSL A σ g) = proj 3 F g) → ∀ g ∈ Ω, semiSL A σ g = g)
    (hcommΩ : ∀ T : Matrix (Fin 3) (Fin 3) F,
      (∀ g ∈ Ω, T * (g : Matrix (Fin 3) (Fin 3) F) = (g : Matrix (Fin 3) (Fin 3) F) * T) →
        ∃ c : F, T = c • (1 : Matrix (Fin 3) (Fin 3) F))
    (htr : ∀ σ : F ≃+* F, (∀ g ∈ Ω, σ (Matrix.trace (g : Matrix (Fin 3) (Fin 3) F)) =
      Matrix.trace (g : Matrix (Fin 3) (Fin 3) F)) → σ = 1)
    (hX0 : X ⊓ K = ⊥) : False := by
  classical
  apply hX1
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  have hcomm : ∀ j ∈ subgroupOfEquiv e (Ω.map (proj 3 F)), (x : A) * j * (x : A)⁻¹ = j := by
    intro j hj
    have hjn := hJ j (phi_fixes_of_isometry e hφ hiso hj)
    have hc1 : (j : A) * x * (j : A)⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 hjn x).1 hx
    have hcX : ⁅(j : A), x⁆ ∈ X := by
      rw [commutatorElement_def]
      have := Subgroup.mul_mem X hc1 (Subgroup.inv_mem X hx)
      simpa [mul_assoc] using this
    have hcK : ⁅(j : A), x⁆ ∈ K := by
      rw [commutatorElement_def]
      have h1 : (x : A) * (j : A)⁻¹ * (x : A)⁻¹ ∈ K := by
        have := (inferInstance : K.Normal).conj_mem ((j : A)⁻¹) (K.inv_mem j.2) x
        simpa [mul_assoc] using this
      have := K.mul_mem j.2 h1
      simpa [mul_assoc] using this
    have h1 : ⁅(j : A), x⁆ = 1 := by
      have : ⁅(j : A), x⁆ ∈ X ⊓ K := ⟨hcX, hcK⟩
      rw [hX0, Subgroup.mem_bot] at this
      exact this
    have h2 : (j : A) * x = x * j := commutatorElement_eq_one_iff_mul_comm.1 h1
    rw [mul_inv_eq_iff_eq_mul]
    exact h2.symm
  set β : MulAut (projectiveSL 3 F) := conjAutEquiv e (MulAut.conjNormal (H := K) x) with hβ
  have hfix : ∀ g ∈ Ω, β (proj 3 F g) = proj 3 F g := by
    intro g hg
    have hk : e.symm (proj 3 F g) ∈ subgroupOfEquiv e (Ω.map (proj 3 F)) := by
      rw [mem_subgroupOfEquiv, MulEquiv.apply_symm_apply]
      exact Subgroup.mem_map_of_mem _ hg
    have h1 : MulAut.conjNormal (H := K) x (e.symm (proj 3 F g)) = e.symm (proj 3 F g) :=
      Subtype.ext (by rw [MulAut.conjNormal_apply]; exact hcomm _ hk)
    have h2 := conjAutEquiv_apply e (MulAut.conjNormal (H := K) x) (e.symm (proj 3 F g))
    rw [MulEquiv.apply_symm_apply, h1, MulEquiv.apply_symm_apply] at h2
    exact h2
  obtain ⟨a, ha⟩ := hX ⟨x, hx⟩
  have hxa : x ^ (p ^ a) = 1 := congrArg Subtype.val ha
  have hβpow : β ^ (p ^ a) = 1 := by
    rw [hβ, fl3g_conjAutEquiv_pow, ← map_pow, hxa, map_one, conjAutEquiv_one]
  have hodd : Odd (p ^ a) := (Fact.out : p.Prime).odd_of_ne_two hp2 |>.pow
  have hβ1 : β = 1 := aut_fixing_trivial' hlift hcommΩ htr hodd hβpow hfix
  have hcn : MulAut.conjNormal (H := K) x = 1 := (conjAutEquiv_eq_one_iff e _).1 hβ1
  have hxc : x ∈ centralizer (K : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have := congrArg (fun τ : MulAut ↥K => (τ ⟨k, hk⟩ : A)) hcn
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
    calc k * x = (x * k * x⁻¹) * x := by rw [this]
      _ = x * k := by group
  have : x ∈ X ⊓ centralizer (K : Set A) := ⟨hx, hxc⟩
  rw [hfaith, Subgroup.mem_bot] at this
  exact this

end Setup

theorem fl3g_charP_of_dvd_card [Finite F] {p : ℕ} [Fact p.Prime] (h : p ∣ Nat.card F) : CharP F p := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hr, hcard⟩ := FiniteField.card F (ringChar F)
  have hp : p ∣ ringChar F ^ (n : ℕ) := by
    rw [← hcard, ← Nat.card_eq_fintype_card]
    exact h
  have hpr : p ∣ ringChar F := (Fact.out : p.Prime).dvd_of_dvd_pow hp
  have : p = ringChar F := (Nat.prime_dvd_prime_iff_eq (Fact.out) hr).1 hpr
  rw [this]
  exact ringChar.charP F

section Main

variable {A : Type} [Group A] {K : Subgroup A} [K.Normal] (e : ↥K ≃* projectiveSL 3 F)

theorem fl3_graph_false_ge5 [Finite A] [Finite F] (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    {φ : MulAut ↥K} {Asym : GL (Fin 3) F}
    (hφ : ∀ k, e (φ k) = (conjAut 3 F Asym * dualAut 3 F) (e k))
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {X : Subgroup A} (hX : IsPGroup p ↥X) (hX1 : X ≠ ⊥)
    (hfaith : X ⊓ centralizer (K : Set A) = ⊥)
    (hJ : ∀ j : ↥K, φ j = j → (j : A) ∈ normalizer (X : Set A)) {Ω : Subgroup SL(3, F)}
    (hΩ : FL3GraphOrth Asym⁻¹ Ω) : False := by
  have hnorm : ∀ k ∈ subgroupOfEquiv e (Ω.map (proj 3 F)),
      (k : A) ∈ normalizer ((X ⊓ K : Subgroup A) : Set A) := fun k hk =>
    mem_normalizer_inf_of_normal (hJ k (phi_fixes_of_isometry e hφ hΩ.isometry hk))
  have hX0 : X ⊓ K = ⊥ := by
    by_cases hpF : p ∣ Nat.card F
    · have : CharP F p := fl3g_charP_of_dvd_card hpF
      exact fl3g_X0_bot_of_char e hΩ.irred hX hnorm
    · exact fl3g_X0_bot_of_cross e hp2 hodd h5 hpF hΩ hX hnorm
  exact fl3g_false_of_X0_bot e hφ hp2 hX hX1 hfaith hJ hΩ.isometry
    (fun A σ h => semiSL_fix_of_perfect A σ hΩ.perfect h) hΩ.comm hΩ.traces hX0

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87

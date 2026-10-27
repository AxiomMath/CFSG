module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoCore
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsBalanceCop

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

set_option linter.unusedSectionVars false

section Generic

private theorem twE6Two_map_centralizer_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (x : G) :
    (Subgroup.centralizer ({x} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e x} : Set H) := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg e h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using this
  · intro h
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact h

theorem gLAPPrimeCoreOf_centralizer_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (x : G)
    (h : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({e x} : Set H)) = ⊥) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set G)) = ⊥ := by
  rw [← twE6Two_map_centralizer_equiv,
    gLAPPrimeCoreOf_map_of_injective 3 e.toMonoidHom e.injective] at h
  exact eq_bot_of_map_eq_bot e.injective h

theorem innerOneBalanceThree_of_toral_aut {K : Type*} [Group K] [Finite K]
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) (T : Set K)
    (hfus : ∀ s : K, s ^ 3 = 1 → s ≠ 1 → ∃ φ : MulAut K, φ s ∈ T)
    (hin : ∀ t ∈ T, GLAPPrimeCoreOf 3 (Subgroup.centralizer {t}) = ⊥)
    (hrig : ∀ t ∈ T, ∀ α : MulAut K, Nat.Coprime 3 (orderOf α) →
      (∀ y ∈ Subgroup.centralizer {t}, α y = y) → α ∈ innerAut K) :
    InnerOneBalanceThree K := by
  refine innerOneBalanceThree_of_toral_coprime hinj {t | ∃ φ : MulAut K, φ t ∈ T} ?_ ?_ ?_
  · intro s hs3 hs1
    obtain ⟨φ, hφ⟩ := hfus s hs3 hs1
    exact ⟨1, by simpa using ⟨φ, hφ⟩⟩
  · rintro t ⟨φ, hφ⟩
    exact gLAPPrimeCoreOf_centralizer_equiv φ t (hin _ hφ)
  · rintro t ⟨φ, hφ⟩ α hα3 hfix
    have hC : ∀ y ∈ Subgroup.centralizer ({φ t} : Set K),
        φ⁻¹ y ∈ Subgroup.centralizer ({t} : Set K) := by
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      apply φ.injective
      simpa only [map_mul, MulAut.mul_apply, MulAut.apply_inv_self] using hy
    have hfix' : ∀ y ∈ Subgroup.centralizer ({φ t} : Set K), (φ * α * φ⁻¹) y = y := by
      intro y hy
      simp only [MulAut.mul_apply]
      rw [hfix _ (hC y hy)]
      simp
    have hord : orderOf (φ * α * φ⁻¹) = orderOf α := by
      have : IsConj α (φ * α * φ⁻¹) := isConj_iff.2 ⟨φ, rfl⟩
      exact this.orderOf_eq.symm
    obtain ⟨g, hg⟩ := hrig _ hφ (φ * α * φ⁻¹) (by rw [hord]; exact hα3) hfix'
    refine ⟨φ⁻¹ g, ?_⟩
    have h1 : φ⁻¹ * MulAut.conj g * φ = MulAut.conj (φ⁻¹ g) := by
      ext z
      simp [MulAut.conj_apply]
    have h2 : α = φ⁻¹ * (φ * α * φ⁻¹) * φ := by group
    rw [h2, ← hg, h1]

theorem twE6Two_conj_mem_commutator {G : Type*} [Group G] {M : Subgroup G} {m : G} (hm : m ∈ M)
    {x : G} (hx : x ∈ ⁅M, M⁆) : m * x * m⁻¹ ∈ ⁅M, M⁆ := by
  rw [Subgroup.commutator_def] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨g₁, h₁, g₂, h₂, rfl⟩ := hx
    have : m * ⁅g₁, g₂⁆ * m⁻¹ = ⁅m * g₁ * m⁻¹, m * g₂ * m⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [this]
    exact Subgroup.commutator_mem_commutator (mul_mem (mul_mem hm h₁) (inv_mem hm))
      (mul_mem (mul_mem hm h₂) (inv_mem hm))
  | one => simp
  | mul x y _ _ hx hy =>
    have : m * (x * y) * m⁻¹ = (m * x * m⁻¹) * (m * y * m⁻¹) := by group
    rw [this]
    exact mul_mem hx hy
  | inv x _ hx =>
    have : m * x⁻¹ * m⁻¹ = (m * x * m⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem hx

@[expose] noncomputable def conjCommutator {G : Type*} [Group G] (M : Subgroup G) {m : G}
    (hm : m ∈ M) : ↥⁅M, M⁆ ≃* ↥⁅M, M⁆ where
  toFun x := ⟨m * x * m⁻¹, twE6Two_conj_mem_commutator hm x.2⟩
  invFun x := ⟨m⁻¹ * x * m, by
    have := twE6Two_conj_mem_commutator (inv_mem hm) x.2
    simpa using this⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem coe_conjCommutator {G : Type*} [Group G] (M : Subgroup G) {m : G} (hm : m ∈ M)
    (x : ↥⁅M, M⁆) : ((conjCommutator M hm x : ↥⁅M, M⁆) : G) = m * x * m⁻¹ := rfl

end Generic

section Assembly


theorem innerOneBalanceThree_twE6_two
    (hfus : TwE6TwoFusion) (hrig : TwE6TwoRigid) :
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = 4 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ 2) →
      InnerOneBalanceThree (twistedE6RootGroup K σ) := by
  intro K _ _ hK σ hσ
  have hchar : CharP K 2 := charP_two_of_card_four hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨g0, hg0C, hg0⟩ := exists_twE6Two_lang K
  have hcL : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hAC : IsAlgClosed (AlgebraicClosure K) := inferInstance
  obtain ⟨ω₀, hω₀⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [card_units_four hK])
  set ω : (AlgebraicClosure K)ˣ := Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom ω₀
    with hωdef
  have hω : orderOf ω = 3 := by
    rw [hωdef, orderOf_injective (Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom)
      (Units.map_injective (algebraMap K (AlgebraicClosure K)).injective), hω₀]
  have hω3 : ω ^ 3 = 1 := pow_three_of_orderOf hω
  set e := twE6TwoEquiv hK σ hσ hg0C hg0 with he
  have hFin : Finite ↥⁅twE6TwoModel (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆ :=
    Finite.of_equiv _ e.toEquiv
  have hcoe : ∀ t : twistedE6RootGroup K σ,
      ((e t : ↥⁅twE6TwoModel (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆) :
        ModGL Tag.E6 (AlgebraicClosure K)) = g0⁻¹ *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (t : ModGL TwistTag.E6.tag K) * g0 :=
    fun t => coe_twE6TwoEquiv hK σ hσ hg0C hg0 t
  refine innerOneBalanceThree_of_toral_aut
    (mulAut_conj_injective_of_center_eq_bot (exceptional_fixed_center_trivial TwistTag.E6 K σ))
    {t | ∃ y : Fin 5 → ZMod 3, y ≠ 0 ∧ e t = dTwE6Two hω3 y} ?_ ?_ ?_
  · intro s hs3 hs1
    set s' := (e s : ↥⁅twE6TwoModel (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆)
      with hs'
    have hs'3 : (s' : ModGL Tag.E6 (AlgebraicClosure K)) ^ 3 = 1 := by
      have : s' ^ 3 = 1 := by rw [hs', ← map_pow, hs3, map_one]
      have := congrArg Subtype.val this
      simpa using this
    obtain ⟨m, hm, y, hmy⟩ := hfus K hK σ hσ g0 hg0C hg0 ω hω s' s'.2 hs'3
    have hy : y ≠ 0 := by
      rintro rfl
      apply hs1
      have h1 : m * (s' : ModGL Tag.E6 (AlgebraicClosure K)) * m⁻¹ = 1 := by
        rw [hmy, subLin_zero, dV_zero]
      have h2 : (s' : ModGL Tag.E6 (AlgebraicClosure K)) = 1 := by
        calc (s' : ModGL Tag.E6 (AlgebraicClosure K)) = m⁻¹ * (m * s' * m⁻¹) * m := by group
          _ = 1 := by rw [h1]; group
      apply e.injective
      apply Subtype.ext
      rw [← hs']
      simpa using h2
    refine ⟨e.trans ((conjCommutator _ hm).trans e.symm), y, hy, ?_⟩
    simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [coe_conjCommutator, coe_dTwE6Two]
    exact hmy
  · rintro t ⟨y, hy, hty⟩
    refine gLAPPrimeCoreOf_centralizer_equiv e t ?_
    rw [hty]
    exact gLAPPrimeCoreOf_centralizer_dS_twE6Two hω hy
  · rintro t ⟨y, hy, hty⟩ α hα3 hfix
    refine hrig K hK σ hσ (iterateFrobenius (AlgebraicClosure K) 2 1)
      (fun c => iterateFrobenius_two_one c) g0 hg0C hg0 ω hω y hy t ?_ α hα3 hfix
    have h1 := hcoe t
    rw [hty, coe_dTwE6Two] at h1
    have h2 : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (t : ModGL TwistTag.E6.tag K) * g0 =
        dV (τ := TwistTag.E6.tag) ω (subLin (τ := TwistTag.E6.tag) e6InnerVec y) := h1.symm
    calc baseChangeGL (algebraMap K (AlgebraicClosure K)) (t : ModGL TwistTag.E6.tag K)
        = g0 * (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (t : ModGL TwistTag.E6.tag K) * g0) * g0⁻¹ := by group
      _ = g0 * dV (τ := TwistTag.E6.tag) ω (subLin (τ := TwistTag.E6.tag) e6InnerVec y) * g0⁻¹ := by
        rw [h2]

end Assembly

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

end

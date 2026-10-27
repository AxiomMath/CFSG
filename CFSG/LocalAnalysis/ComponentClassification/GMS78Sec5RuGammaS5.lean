module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuGammaS5Data

public section

namespace CFSG.ComponentClassification.GMS78.RuGamma

open CFSG.Quasithin.RuType CFSG.Quasithin.RuType.Sigma Matrix

abbrev GL4 : Type := V4 ≃ₗ[ZMod 2] V4

instance : Finite GL4 := Finite.of_injective (fun g : GL4 => (g : V4 → V4)) DFunLike.coe_injective

theorem v4_add_self (v : V4) : v + v = 0 := by
  have key : ∀ a : ZMod 2, a + a = 0 := by decide
  funext i
  exact key (v i)

theorem v4_eq_of_add_eq_zero {v w : V4} (h : v + w = 0) : v = w := by
  rw [← add_zero v, ← v4_add_self w, ← add_assoc, h, zero_add]

theorem single_zero_ne_zero : (Pi.single 0 1 : V4) ≠ 0 := by decide

theorem ncard_ne_zero_v4 : {v : V4 | v ≠ 0}.ncard = 15 := by
  rw [show {v : V4 | v ≠ 0} = ((Finset.univ.filter fun v : V4 => v ≠ 0 : Finset V4) : Set V4) by
    ext v; simp, Set.ncard_coe_finset]
  decide

theorem m4_ext {M N : M4} (h : ∀ j : Fin 4, M *ᵥ Pi.single j 1 = N *ᵥ Pi.single j 1) :
    M = N := by
  ext i j
  have := congrFun (h j) i
  simpa [Matrix.mulVec_single_one] using this

theorem linearMap_ext_v4 {f g : V4 →ₗ[ZMod 2] V4}
    (h : ∀ j : Fin 4, f (Pi.single j 1) = g (Pi.single j 1)) : f = g :=
  (Pi.basisFun (ZMod 2) (Fin 4)).ext fun j => by rw [Pi.basisFun_apply]; exact h j

abbrev comb (w : Fin 4 → V4) : V4 →ₗ[ZMod 2] V4 := Fintype.linearCombination (ZMod 2) w

theorem comb_single (w : Fin 4 → V4) (j : Fin 4) : comb w (Pi.single j 1) = w j := by
  rw [Fintype.linearCombination_apply_single, one_smul]

theorem comb_apply (w : Fin 4 → V4) (c : V4) :
    comb w c = c 0 • w 0 + c 1 • w 1 + c 2 • w 2 + c 3 • w 3 := by
  rw [Fintype.linearCombination_apply, Fin.sum_univ_four]

@[expose] def ActsAs (w : Fin 4 → V4) (M : M4) (g : GL4) : Prop :=
  ∀ c : V4, comb w (M *ᵥ c) = g (comb w c)

namespace ActsAs

variable {w : Fin 4 → V4}

theorem mul {M N : M4} {g h : GL4} (hM : ActsAs w M g) (hN : ActsAs w N h) :
    ActsAs w (M * N) (g * h) := fun c => by
  rw [← Matrix.mulVec_mulVec, hM, hN, LinearEquiv.mul_apply]

theorem one (w : Fin 4 → V4) : ActsAs w 1 1 := fun c => by
  rw [Matrix.one_mulVec]
  rfl

theorem pow {M : M4} {g : GL4} (hM : ActsAs w M g) : ∀ n : ℕ, ActsAs w (M ^ n) (g ^ n)
  | 0 => by rw [pow_zero, pow_zero]; exact one w
  | n + 1 => by rw [pow_succ, pow_succ]; exact (hM.pow n).mul hM

theorem word {M : Fin 3 → M4} {g : Fin 3 → GL4} (h : ∀ i, ActsAs w (M i) (g i)) :
    ∀ W : List (Fin 3), ActsAs w (evalW M W) (evalW g W)
  | [] => one w
  | i :: W => (h i).mul (word h W)

theorem of_single {M : M4} {g : GL4}
    (h : ∀ j : Fin 4, comb w (M *ᵥ Pi.single j 1) = g (w j)) : ActsAs w M g := by
  have key : (comb w).comp (Matrix.mulVecLin M) = (g : V4 →ₗ[ZMod 2] V4).comp (comb w) :=
    linearMap_ext_v4 fun j => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, Matrix.mulVecLin_apply, h j,
        LinearEquiv.coe_coe, comb_single]
  intro c
  exact LinearMap.congr_fun key c

theorem matrix_eq (hw : Function.Injective (comb w)) {M N : M4} {g : GL4} (hM : ActsAs w M g)
    (hN : ActsAs w N g) : M = N :=
  m4_ext fun j => hw (by rw [hM, hN])

theorem elem_eq (hw : Function.Surjective (comb w)) {M : M4} {g h : GL4} (hg : ActsAs w M g)
    (hh : ActsAs w M h) : g = h := by
  ext v
  obtain ⟨c, rfl⟩ := hw v
  rw [← hg, ← hh]

theorem fix {M : M4} {g : GL4} (hM : ActsAs w M g) {c : V4} (hc : M *ᵥ c = c) :
    g (comb w c) = comb w c := by
  rw [← hM, hc]

end ActsAs

theorem exists_actsAs {w : Fin 4 → V4} (hw : Function.Bijective (comb w)) (g : GL4) :
    ∃ M : M4, ActsAs w M g := by
  let β := LinearEquiv.ofBijective (comb w) hw
  refine ⟨Matrix.of fun i j => β.symm (g (w j)) i, ActsAs.of_single fun j => ?_⟩
  have hcol : (Matrix.of fun i j => β.symm (g (w j)) i) *ᵥ Pi.single j 1 = β.symm (g (w j)) := by
    funext i
    simp
  rw [hcol]
  exact β.apply_symm_apply _

theorem pow_succ_apply (b : GL4) (k : ℕ) (v : V4) : (b ^ (k + 1)) v = b ((b ^ k) v) := by
  rw [pow_succ', LinearEquiv.mul_apply]

theorem pow_two_apply (b : GL4) (v : V4) : (b ^ 2) v = b (b v) := by
  rw [sq, LinearEquiv.mul_apply]

theorem pow_four_apply {b : GL4} (hb5 : b ^ 5 = 1) (hfix : ∀ v : V4, b v = v → v = 0)
    (v : V4) : (b ^ 4) v = v + b v + (b ^ 2) v + (b ^ 3) v := by
  have h5 : b ((b ^ 4) v) = v := by rw [← pow_succ_apply, hb5]; rfl
  have e2 : b (b v) = (b ^ 2) v := by rw [sq, LinearEquiv.mul_apply]
  have e3 : b ((b ^ 2) v) = (b ^ 3) v := (pow_succ_apply b 2 v).symm
  have e4 : b ((b ^ 3) v) = (b ^ 4) v := (pow_succ_apply b 3 v).symm
  have hy := hfix (v + b v + (b ^ 2) v + (b ^ 3) v + (b ^ 4) v) (by
    rw [map_add, map_add, map_add, map_add, h5, e2, e3, e4]
    abel)
  exact (v4_eq_of_add_eq_zero hy).symm

@[expose] def cyc (b : GL4) (w : V4) : Fin 4 → V4 := fun j => (b ^ (j : ℕ)) w

theorem cyc_zero (b : GL4) (w : V4) : cyc b w 0 = w := by
  simp [cyc]

theorem actsAs_c5 {b : GL4} (hb5 : b ^ 5 = 1) (hfix : ∀ v : V4, b v = v → v = 0) (w : V4) :
    ActsAs (cyc b w) c5 b := by
  obtain ⟨h0, h1, h2, h3⟩ := c5_mulVec_single
  refine ActsAs.of_single fun j => ?_
  fin_cases j
  · simp [h0, cyc]
  · simp [h1, cyc, pow_two_apply]
  · simp [h2, cyc, ← pow_succ_apply]
  · simp only [Fin.reduceFinMk, Fin.isValue, h3, comb_apply]
    simp [cyc, ← pow_succ_apply, pow_four_apply hb5 hfix]

theorem comb_cyc_bijective {b : GL4} (hb5 : b ^ 5 = 1) (hfix : ∀ v : V4, b v = v → v = 0)
    {w : V4} (hw : w ≠ 0) : Function.Bijective (comb (cyc b w)) := by
  refine Finite.injective_iff_bijective.1 ((injective_iff_map_eq_zero _).2 fun c hc => ?_)
  by_contra hc0
  have hrep := actsAs_c5 hb5 hfix w
  have h1 : comb (cyc b w) (c5 *ᵥ c) = 0 := by rw [hrep, hc, map_zero]
  have h2 : comb (cyc b w) (c5 *ᵥ (c5 *ᵥ c)) = 0 := by rw [hrep, h1, map_zero]
  have h3 : comb (cyc b w) (c5 *ᵥ (c5 *ᵥ (c5 *ᵥ c))) = 0 := by rw [hrep, h2, map_zero]
  obtain ⟨a, ha⟩ := c5_irred c hc0
  apply hw
  have := congrArg (comb (cyc b w)) ha
  rw [comb_single, cyc_zero, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul,
    hc, h1, h2, h3] at this
  simpa using this.symm

theorem eq_one_of_commute_of_fix {b : GL4} (hb5 : b ^ 5 = 1) (hfix : ∀ v : V4, b v = v → v = 0)
    {w : V4} (hw : w ≠ 0) {r : GL4} (hrb : Commute r b) (hrw : r w = w) : r = 1 := by
  have hrep : ActsAs (cyc b w) 1 r := ActsAs.of_single fun j => by
    rw [Matrix.one_mulVec, comb_single]
    change (b ^ (j : ℕ)) w = r ((b ^ (j : ℕ)) w)
    rw [← LinearEquiv.mul_apply, (hrb.pow_right _).eq, LinearEquiv.mul_apply, hrw]
  exact ActsAs.elem_eq (comb_cyc_bijective hb5 hfix hw).2 hrep (ActsAs.one _)

theorem sq_add_apply (r : GL4) (v : V4) : r (r v + v) + (r v + v) = (r * r) v + v := by
  rw [map_add, LinearEquiv.mul_apply, add_assoc, ← add_assoc (r v) (r v) v, v4_add_self, zero_add]

theorem exists_fix_of_pow_four {r : GL4} (hr : r ^ 4 = 1) : ∃ w : V4, w ≠ 0 ∧ r w = w := by
  have hr' : r * r * (r * r) = 1 := by rw [← hr]; simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  set v₀ : V4 := Pi.single 0 1 with hv₀
  set v₁ := r v₀ + v₀
  set v₂ := r v₁ + v₁
  set v₃ := r v₂ + v₂
  have h4 : r v₃ + v₃ = 0 := by
    have e2 : v₂ = (r * r) v₀ + v₀ := sq_add_apply r v₀
    rw [sq_add_apply r v₂, e2, sq_add_apply (r * r) v₀, hr']
    exact v4_add_self v₀
  by_cases h1 : v₁ = 0
  · exact ⟨v₀, single_zero_ne_zero, v4_eq_of_add_eq_zero h1⟩
  by_cases h2 : v₂ = 0
  · exact ⟨v₁, h1, v4_eq_of_add_eq_zero h2⟩
  by_cases h3 : v₃ = 0
  · exact ⟨v₂, h2, v4_eq_of_add_eq_zero h3⟩
  · exact ⟨v₃, h3, v4_eq_of_add_eq_zero h4⟩

theorem actsAs_fr {b τ : GL4} (hb5 : b ^ 5 = 1) (hfix : ∀ v : V4, b v = v → v = 0) {w : V4}
    (hτb : τ * b * τ⁻¹ = b ^ 2) (hτw : τ w = w) : ActsAs (cyc b w) fr τ := by
  have hc := actsAs_c5 hb5 hfix w
  have hτw' : τ⁻¹ w = w := by
    nth_rewrite 1 [← hτw]
    rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  refine ActsAs.of_single fun j => ?_
  rw [fr_mulVec_single, hc.pow (2 * (j : ℕ)) (Pi.single 0 1), comb_single, cyc_zero]
  have h1 : τ * b ^ (j : ℕ) * τ⁻¹ = b ^ (2 * (j : ℕ)) := by rw [← conj_pow, hτb, ← pow_mul]
  rw [← h1, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hτw']
  rfl

theorem exists_cand {b τ t : GL4} (hb5 : b ^ 5 = 1) (hfix : ∀ v : V4, b v = v → v = 0) {w : V4}
    (hw : w ≠ 0) (hτb : τ * b * τ⁻¹ = b ^ 2) (hτw : τ w = w) (htw : t w = w)
    (htτ : t * τ = τ * t ∨ t * τ = τ ^ 3 * t) (htn : ∀ j : ℕ, t ≠ τ ^ j) :
    ∃ u : V4, ∃ e ∈ ([1, 3] : List ℕ), ActsAs (cyc b w) (candMat u e) t ∧
      candMat u e * fr = fr ^ e * candMat u e ∧ ∀ j : Fin 4, candMat u e ≠ fr ^ (j : ℕ) := by
  have hβ := comb_cyc_bijective hb5 hfix hw
  have hfr := actsAs_fr hb5 hfix hτb hτw
  obtain ⟨T, hT⟩ := exists_actsAs hβ t
  obtain ⟨e, he, hTe⟩ : ∃ e ∈ ([1, 3] : List ℕ), t * τ = τ ^ e * t := by
    rcases htτ with h | h
    · exact ⟨1, by simp, by rw [pow_one]; exact h⟩
    · exact ⟨3, by simp, h⟩
  have hTfr : T * fr = fr ^ e * T :=
    ActsAs.matrix_eq hβ.1 (hT.mul hfr) (by rw [hTe]; exact (hfr.pow e).mul hT)
  have hT0 : T *ᵥ Pi.single 0 1 = Pi.single 0 1 :=
    hβ.1 (by rw [hT, comb_single, cyc_zero, htw])
  have hT3 : T * fr ^ 3 = fr ^ (3 * e) * T := by
    have h := (SemiconjBy.pow_right hTfr 3 : SemiconjBy T (fr ^ 3) ((fr ^ e) ^ 3))
    rw [← pow_mul, mul_comm e 3] at h
    exact h
  obtain ⟨u, hu⟩ : ∃ u, T *ᵥ Pi.single 1 1 = u := ⟨_, rfl⟩
  obtain ⟨c0, c1, c2, c3⟩ := candMat_mulVec_single u e
  have hTu : T = candMat u e := by
    refine m4_ext fun j => ?_
    fin_cases j
    · exact hT0.trans c0.symm
    · exact hu.trans c1.symm
    · change T *ᵥ Pi.single 2 1 = candMat u e *ᵥ Pi.single 2 1
      rw [c2, ← fr_mulVec_single_one, Matrix.mulVec_mulVec, hTfr, ← Matrix.mulVec_mulVec, hu]
    · change T *ᵥ Pi.single 3 1 = candMat u e *ᵥ Pi.single 3 1
      rw [c3, ← fr_pow_three_mulVec, Matrix.mulVec_mulVec, hT3, ← Matrix.mulVec_mulVec, hu]
  subst hTu
  refine ⟨u, e, he, hT, hTfr, fun j hj => htn j ?_⟩
  exact ActsAs.elem_eq hβ.2 hT (by rw [hj]; exact hfr.pow j)

@[expose] noncomputable def kapEquiv : V4 ≃+ (Fin 2 → F4) :=
  AddEquiv.ofBijective (AddMonoidHom.mk' kap kap_add) ⟨kap_injective, kap_surjective⟩

@[expose] def sigSub (κ : V4 → Fin 2 → F4) : Subgroup GL4 where
  carrier := {g | ∃ x : SigmaL2F4, ∀ v, κ (g v) = sigmaAct x (κ v)}
  mul_mem' := by
    rintro g h ⟨x, hx⟩ ⟨y, hy⟩
    exact ⟨x * y, fun v => by rw [LinearEquiv.mul_apply, hx, hy, sigmaAct_mul]⟩
  one_mem' := ⟨1, fun v => by rw [sigmaAct_one]; rfl⟩
  inv_mem' := by
    rintro g ⟨x, hx⟩
    refine ⟨x⁻¹, fun v => ?_⟩
    have h := hx (g⁻¹ v)
    rw [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] at h
    rw [LinearEquiv.coe_inv, h, ← sigmaAct_mul, inv_mul_cancel, sigmaAct_one]

theorem mem_sigSub {κ : V4 → Fin 2 → F4} {g : GL4} :
    g ∈ sigSub κ ↔ ∃ x : SigmaL2F4, ∀ v, κ (g v) = sigmaAct x (κ v) := Iff.rfl

theorem mem_sigSub_of_actsAs {w : Fin 4 → V4} {κ : V4 → Fin 2 → F4}
    (hκ : ∀ c, κ (comb w c) = kap c) (hw : Function.Surjective (comb w)) {M : M4} {g : GL4}
    (hM : ActsAs w M g) {x : SigmaL2F4} (hx : ∀ c, kap (M *ᵥ c) = sigmaAct x (kap c)) :
    g ∈ sigSub κ := by
  refine ⟨x, fun v => ?_⟩
  obtain ⟨c, rfl⟩ := hw v
  rw [← hM, hκ, hκ, hx]

theorem evalW_mem {K : Subgroup GL4} {g : Fin 3 → GL4} (hg : ∀ i, g i ∈ K) :
    ∀ W : List (Fin 3), evalW g W ∈ K
  | [] => K.one_mem
  | i :: W => K.mul_mem (hg i) (evalW_mem hg W)

theorem vec3_forall {α : Type*} {P : α → Prop} {a b c : α} (ha : P a) (hb : P b) (hc : P c) :
    ∀ i, P (![a, b, c] i) := by
  intro i
  fin_cases i
  exacts [ha, hb, hc]

theorem actsAs_vec3 {w : Fin 4 → V4} {M₀ M₁ M₂ : M4} {g₀ g₁ g₂ : GL4} (h₀ : ActsAs w M₀ g₀)
    (h₁ : ActsAs w M₁ g₁) (h₂ : ActsAs w M₂ g₂) :
    ∀ i, ActsAs w (![M₀, M₁, M₂] i) (![g₀, g₁, g₂] i) := by
  intro i
  fin_cases i
  exacts [h₀, h₁, h₂]

theorem le_of_stab_of_orbit {Γ K : Subgroup GL4} {w : V4} (hw : w ≠ 0)
    (hS : ∀ s ∈ Γ, s w = w → s ∈ K) (hO : ∀ v : V4, v ≠ 0 → ∃ k ∈ K, k ∈ Γ ∧ k w = v) :
    Γ ≤ K := by
  intro g hg
  obtain ⟨k, hkK, hkΓ, hkw⟩ := hO (g w) ((LinearEquiv.map_ne_zero_iff g).2 hw)
  have h1 : k⁻¹ * g ∈ K := hS _ (Γ.mul_mem (Γ.inv_mem hkΓ) hg) (by
    rw [LinearEquiv.mul_apply, ← hkw, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply])
  have h2 := K.mul_mem hkK h1
  rwa [mul_inv_cancel_left] at h2

theorem index_normalizer_modEq_five {G : Type*} [Group G] [Finite G] {P : Subgroup G}
    (hP : Nat.card P = 5) (hidx : ¬ 5 ∣ P.index) :
    (Subgroup.normalizer (P : Set G)).index ≡ 1 [MOD 5] := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hpg : IsPGroup 5 P := IsPGroup.of_card (n := 1) (by rw [hP, pow_one])
  have h1 := card_sylow_modEq_one 5 G
  have hS : ((hpg.toSylow hidx : Subgroup G) : Set G) = P := by rw [IsPGroup.toSylow_coe]
  rw [Sylow.card_eq_index_normalizer (hpg.toSylow hidx),
    show ((hpg.toSylow hidx : Sylow 5 G) : Set G) = P from hS] at h1
  exact h1

section Gamma

variable {Γ : Subgroup GL4}

theorem orbit_eq (htr : ∀ v w : V4, v ≠ 0 → w ≠ 0 → ∃ g ∈ Γ, g v = w) {w : V4} (hw : w ≠ 0) :
    MulAction.orbit Γ w = {v | v ≠ 0} := by
  ext v
  simp only [MulAction.mem_orbit_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨g, rfl⟩
    rw [Subgroup.smul_def, LinearEquiv.smul_def]
    exact (LinearEquiv.map_ne_zero_iff _).2 hw
  · intro hv
    obtain ⟨g, hg, rfl⟩ := htr w v hw hv
    exact ⟨⟨g, hg⟩, rfl⟩

theorem mem_stabilizer_iff_apply {g : Γ} {w : V4} :
    g ∈ MulAction.stabilizer Γ w ↔ (g : GL4) w = w := by
  rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, LinearEquiv.smul_def]

theorem card_stabilizer (hcard : Nat.card Γ = 120)
    (htr : ∀ v w : V4, v ≠ 0 → w ≠ 0 → ∃ g ∈ Γ, g v = w) {w : V4} (hw : w ≠ 0) :
    Nat.card (MulAction.stabilizer Γ w) = 8 := by
  have h1 := MulAction.index_stabilizer Γ w
  rw [orbit_eq htr hw, ncard_ne_zero_v4] at h1
  have h2 := (MulAction.stabilizer Γ w).card_mul_index
  rw [h1, hcard] at h2
  omega

theorem orderOf_dvd_eight (hcard : Nat.card Γ = 120)
    (htr : ∀ v w : V4, v ≠ 0 → w ≠ 0 → ∃ g ∈ Γ, g v = w) {w : V4} (hw : w ≠ 0) {g : Γ}
    (hg : (g : GL4) w = w) : orderOf g ∣ 8 := by
  have hmem : g ∈ MulAction.stabilizer Γ w := mem_stabilizer_iff_apply.2 hg
  rw [← card_stabilizer hcard htr hw, ← Subgroup.orderOf_mk g hmem]
  exact orderOf_dvd_natCard _

theorem pow_five_coe {b : Γ} (hb : orderOf b = 5) : (b : GL4) ^ 5 = 1 := by
  have h := pow_orderOf_eq_one b
  rw [hb] at h
  rw [← Subgroup.coe_pow, h, Subgroup.coe_one]

theorem fix_free (hcard : Nat.card Γ = 120)
    (htr : ∀ v w : V4, v ≠ 0 → w ≠ 0 → ∃ g ∈ Γ, g v = w) {b : Γ} (hb : orderOf b = 5) :
    ∀ v : V4, (b : GL4) v = v → v = 0 := by
  intro v hv
  by_contra hv0
  have := orderOf_dvd_eight hcard htr hv0 hv
  rw [hb] at this
  norm_num at this

theorem eq_one_of_commute (hcard : Nat.card Γ = 120)
    (htr : ∀ v w : V4, v ≠ 0 → w ≠ 0 → ∃ g ∈ Γ, g v = w) {b : Γ} (hb : orderOf b = 5)
    {w : V4} (hw : w ≠ 0) {r : Γ} (hrb : r * b = b * r) (hrw : (r : GL4) w = w) : r = 1 := by
  have hc : Commute (r : GL4) b := by
    change (r : GL4) * b = b * r
    rw [← Subgroup.coe_mul, hrb, Subgroup.coe_mul]
  exact Subtype.ext (eq_one_of_commute_of_fix (pow_five_coe hb) (fix_free hcard htr hb) hw hc hrw)

theorem card_le_four_of_le_normalizer {b : Γ} (hb : orderOf b = 5) {K : Subgroup Γ}
    (hKN : K ≤ Subgroup.normalizer (Subgroup.zpowers b : Set Γ))
    (hK : ∀ k ∈ K, k * b = b * k → k = 1) :
    Nat.card K ≤ 4 ∧ (Nat.card K = 4 → ∃ k ∈ K, k * b * k⁻¹ = b ^ 2) := by
  classical
  let T : Finset Γ := {b, b ^ 2, b ^ 3, b ^ 4}
  have hT : ∀ k ∈ K, k * b * k⁻¹ ∈ T := by
    intro k hk
    have h1 : k * b * k⁻¹ ∈ Subgroup.zpowers b :=
      (Subgroup.mem_normalizer_iff.1 (hKN hk) b).1 (Subgroup.mem_zpowers b)
    rw [mem_zpowers_iff_mem_range_orderOf, hb] at h1
    obtain ⟨i, hi, he⟩ := Finset.mem_image.1 h1
    have hne : k * b * k⁻¹ ≠ 1 := by
      intro h
      have hb1 : b = 1 := by
        calc b = k⁻¹ * (k * b * k⁻¹) * k := by group
          _ = 1 := by rw [h]; group
      rw [hb1, orderOf_one] at hb
      norm_num at hb
    simp only [Finset.mem_range] at hi
    simp only [T, Finset.mem_insert, Finset.mem_singleton]
    interval_cases i
    · exact absurd (he.symm.trans (pow_zero b)) hne
    · exact Or.inl (by rw [← he, pow_one])
    · exact Or.inr (Or.inl he.symm)
    · exact Or.inr (Or.inr (Or.inl he.symm))
    · exact Or.inr (Or.inr (Or.inr he.symm))
  let f : K → T := fun k => ⟨k * b * (k : Γ)⁻¹, hT k k.2⟩
  have hf : Function.Injective f := by
    intro k k' h
    have h' : (k : Γ) * b * (k : Γ)⁻¹ = k' * b * (k' : Γ)⁻¹ := congrArg Subtype.val h
    have hc : ((k : Γ)⁻¹ * k') * b = b * ((k : Γ)⁻¹ * k') := by
      calc (k : Γ)⁻¹ * k' * b = (k : Γ)⁻¹ * ((k' : Γ) * b * (k' : Γ)⁻¹) * k' := by group
        _ = (k : Γ)⁻¹ * ((k : Γ) * b * (k : Γ)⁻¹) * k' := by rw [h']
        _ = b * ((k : Γ)⁻¹ * k') := by group
    exact Subtype.ext (inv_mul_eq_one.1 (hK _ (K.mul_mem (K.inv_mem k.2) k'.2) hc))
  have hTc : Nat.card T ≤ 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact Finset.card_le_four
  refine ⟨(Nat.card_le_card_of_injective f hf).trans hTc, fun h4 => ?_⟩
  obtain ⟨k, hk⟩ := (hf.bijective_of_nat_card_le (hTc.trans h4.ge)).2 ⟨b ^ 2, by simp [T]⟩
  exact ⟨k, k.2, congrArg Subtype.val hk⟩

theorem exists_tau (hcard : Nat.card Γ = 120)
    (htr : ∀ v w : V4, v ≠ 0 → w ≠ 0 → ∃ g ∈ Γ, g v = w) {b : Γ} (hb : orderOf b = 5) :
    ∃ τ : Γ, τ * b * τ⁻¹ = b ^ 2 ∧ orderOf τ = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := Subgroup.zpowers b
  set N := Subgroup.normalizer (P : Set Γ)
  have hP5 : Nat.card P = 5 := by rw [Nat.card_zpowers, hb]
  have hPidx : P.index = 24 := by
    have := P.card_mul_index
    rw [hP5, hcard] at this
    omega
  have hmod : N.index % 5 = 1 := index_normalizer_modEq_five hP5 (by rw [hPidx]; norm_num)
  have hNc := N.card_mul_index
  rw [hcard] at hNc
  have h5N : 5 ∣ Nat.card N := hP5 ▸ Subgroup.card_dvd_of_le Subgroup.le_normalizer
  have hN1 : N.index ≠ 1 := by
    intro h1
    have hNtop : N = ⊤ := Subgroup.index_eq_one.1 h1
    have hS := card_stabilizer hcard htr single_zero_ne_zero
    have := (card_le_four_of_le_normalizer hb (K := MulAction.stabilizer Γ (Pi.single 0 1))
      (le_top.trans hNtop.ge)
      (fun k hk hkb => eq_one_of_commute hcard htr hb single_zero_ne_zero hkb
        (mem_stabilizer_iff_apply.1 hk))).1
    omega
  have hN20 : Nat.card N = 20 := by
    obtain ⟨m, hm⟩ := h5N
    have h24 : 5 * (m * N.index) = 5 * 24 := by rw [← mul_assoc, ← hm, hNc]
    have hdvd : N.index ∣ 24 :=
      ⟨m, by rw [mul_comm]; exact (Nat.eq_of_mul_eq_mul_left (by norm_num) h24).symm⟩
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : N.index <;> omega
  obtain ⟨Q', hQ'⟩ := Sylow.exists_subgroup_card_pow_prime (G := N) 2 (n := 2)
    (by rw [hN20]; norm_num)
  set Q := Q'.map N.subtype
  have hQc : Nat.card Q = 4 := by
    rw [Subgroup.card_map_of_injective N.subtype_injective, hQ']
    norm_num
  have hQN : Q ≤ N := Subgroup.map_subtype_le Q'
  have hQ4 : ∀ q ∈ Q, q ^ 4 = 1 := fun q hq => by
    have := orderOf_dvd_natCard (⟨q, hq⟩ : Q)
    rw [hQc, Subgroup.orderOf_mk] at this
    exact orderOf_dvd_iff_pow_eq_one.1 this
  obtain ⟨τ, hτQ, hτb⟩ := (card_le_four_of_le_normalizer hb hQN (fun q hq hqb => by
    obtain ⟨w, hw, hqw⟩ := exists_fix_of_pow_four (r := (q : GL4))
      (by rw [← Subgroup.coe_pow, hQ4 q hq, Subgroup.coe_one])
    exact eq_one_of_commute hcard htr hb hw hqb hqw)).2 hQc
  refine ⟨τ, hτb, ?_⟩
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h
    have hb4 : b = b ^ 4 := by
      calc b = τ ^ 2 * b * (τ ^ 2)⁻¹ := by rw [h, inv_one, mul_one, one_mul]
        _ = τ * (τ * b * τ⁻¹) * τ⁻¹ := by rw [sq, _root_.mul_inv_rev]; simp only [mul_assoc]
        _ = τ * b ^ 2 * τ⁻¹ := by rw [hτb]
        _ = (τ * b * τ⁻¹) ^ 2 := conj_pow.symm
        _ = b ^ 4 := by rw [hτb, ← pow_mul]
    have h3 : b ^ 3 = 1 := by
      calc b ^ 3 = b⁻¹ * b ^ 4 := by group
        _ = 1 := by rw [← hb4]; group
    have := orderOf_dvd_of_pow_eq_one h3
    rw [hb] at this
    norm_num at this
  have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := τ) (by simpa using hτ2)
    (by simpa using hQ4 τ hτQ)
  simpa using this

theorem exists_t (hcard : Nat.card Γ = 120)
    (htr : ∀ v w : V4, v ≠ 0 → w ≠ 0 → ∃ g ∈ Γ, g v = w) {τ : Γ} (hτ : orderOf τ = 4) {w : V4}
    (hw : w ≠ 0) (hτw : (τ : GL4) w = w) :
    ∃ t : Γ, (t : GL4) w = w ∧ t ∉ Subgroup.zpowers τ ∧ (t * τ = τ * t ∨ t * τ = τ ^ 3 * t) ∧
      ∀ s : Γ, (s : GL4) w = w → s ∈ Subgroup.zpowers τ ∨ s * t ∈ Subgroup.zpowers τ := by
  classical
  set S := MulAction.stabilizer Γ w
  have hSc : Nat.card S = 8 := card_stabilizer hcard htr hw
  have hτS : τ ∈ S := mem_stabilizer_iff_apply.2 hτw
  set τS : S := ⟨τ, hτS⟩
  set Z := Subgroup.zpowers τS
  have hτS4 : orderOf τS = 4 := by rw [Subgroup.orderOf_mk, hτ]
  have hZc : Nat.card Z = 4 := by rw [Nat.card_zpowers, hτS4]
  have hZ2 : Z.index = 2 := by
    have := Z.card_mul_index
    rw [hZc, hSc] at this
    omega
  have hmemZ : ∀ s : S, s ∈ Z ↔ (s : Γ) ∈ Subgroup.zpowers τ := by
    intro s
    simp only [Z, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [← hk, Subgroup.coe_zpow]⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow, ← hk])⟩
  obtain ⟨t, htZ⟩ : ∃ t : S, t ∉ Z := by
    by_contra h
    push Not at h
    have hZtop : Z = ⊤ := eq_top_iff.2 fun s _ => h s
    rw [hZtop, Subgroup.index_top] at hZ2
    norm_num at hZ2
  have hconj : t * τS * t⁻¹ ∈ Z :=
    (Subgroup.normal_of_index_eq_two hZ2).conj_mem τS (Subgroup.mem_zpowers τS) t
  rw [mem_zpowers_iff_mem_range_orderOf, hτS4] at hconj
  obtain ⟨i, hi, he⟩ := Finset.mem_image.1 hconj
  simp only [Finset.mem_range] at hi
  have hcomm : t * τS = τS * t ∨ t * τS = τS ^ 3 * t := by
    interval_cases i
    · exfalso
      have h1 : τS = 1 := by
        calc τS = t⁻¹ * (t * τS * t⁻¹) * t := by group
          _ = 1 := by rw [← he]; group
      rw [h1, orderOf_one] at hτS4
      norm_num at hτS4
    · left
      calc t * τS = (t * τS * t⁻¹) * t := by group
        _ = τS * t := by rw [← he, pow_one]
    · exfalso
      have h2 : τS ^ 2 = 1 := by
        have h4 : τS ^ 4 = 1 := by
          have := pow_orderOf_eq_one τS
          rwa [hτS4] at this
        calc τS ^ 2 = t⁻¹ * (t * τS * t⁻¹) ^ 2 * t := by rw [conj_pow]; group
          _ = t⁻¹ * τS ^ 4 * t := by rw [← he, ← pow_mul]
          _ = 1 := by rw [h4]; group
      have := orderOf_dvd_of_pow_eq_one h2
      rw [hτS4] at this
      norm_num at this
    · right
      calc t * τS = (t * τS * t⁻¹) * t := by group
        _ = τS ^ 3 * t := by rw [← he]
  refine ⟨t, t.2, fun h => htZ ((hmemZ t).2 h), ?_, fun s hs => ?_⟩
  · rcases hcomm with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  · by_cases hsZ : (⟨s, hs⟩ : S) ∈ Z
    · exact Or.inl ((hmemZ _).1 hsZ)
    · right
      have : (⟨s, hs⟩ : S) * t ∈ Z :=
        (Subgroup.mul_mem_iff_of_index_two hZ2).2 (iff_of_false hsZ htZ)
      exact (hmemZ _).1 this

theorem false_of_bad (hcard : Nat.card Γ = 120)
    (htr : ∀ v w : V4, v ≠ 0 → w ≠ 0 → ∃ g ∈ Γ, g v = w) {w : Fin 4 → V4}
    (hw : Function.Bijective (comb w)) {g : Fin 3 → GL4} (hgΓ : ∀ i, g i ∈ Γ) {M : Fin 3 → M4}
    (hg : ∀ i, ActsAs w (M i) (g i)) {W : List (Fin 3)} (hW : Order3Fix (evalW M W)) : False := by
  obtain ⟨h3, h1, v, hv0, hv⟩ := hW
  have hk := ActsAs.word hg W
  set k : Γ := ⟨evalW g W, evalW_mem hgΓ W⟩
  have hk3 : k ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact ActsAs.elem_eq hw.2 (hk.pow 3) (by rw [h3]; exact ActsAs.one w))
  have hk1 : k ≠ 1 := fun h => h1 (ActsAs.matrix_eq hw.1 hk (by
    have h' : evalW g W = 1 := congrArg Subtype.val h
    rw [h']
    exact ActsAs.one w))
  have hne : comb w v ≠ 0 := fun h => hv0 (hw.1 (h.trans (map_zero _).symm))
  have h8 := orderOf_dvd_eight hcard htr hne (g := k) (hk.fix hv)
  have h3' : orderOf k = 3 := ((Nat.dvd_prime Nat.prime_three).1
    (orderOf_dvd_of_pow_eq_one hk3)).resolve_left fun h => hk1 (orderOf_eq_one_iff.1 h)
  rw [h3'] at h8
  norm_num at h8

end Gamma

theorem exists_coords {Γ : Subgroup GL4} (hcard : Nat.card Γ = 120)
    (htr : ∀ v w : V4, v ≠ 0 → w ≠ 0 → ∃ g ∈ Γ, g v = w) :
    ∃ κ : V4 ≃+ (Fin 2 → F4), Γ ≤ sigSub κ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := Γ) 5 (by rw [hcard]; norm_num)
  obtain ⟨τ, hτb, hτ⟩ := exists_tau hcard htr hb
  have hτ4 : (τ : GL4) ^ 4 = 1 := by
    have h := pow_orderOf_eq_one τ
    rw [hτ] at h
    rw [← Subgroup.coe_pow, h, Subgroup.coe_one]
  obtain ⟨w, hw, hτw⟩ := exists_fix_of_pow_four hτ4
  obtain ⟨t, htw, htn, htτ, hstab⟩ := exists_t hcard htr hτ hw hτw
  have hb5 := pow_five_coe hb
  have hfix := fix_free hcard htr hb
  have hτb' : (τ : GL4) * b * (τ : GL4)⁻¹ = (b : GL4) ^ 2 := by
    rw [← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hτb, Subgroup.coe_pow]
  have htτ' : (t : GL4) * τ = τ * t ∨ (t : GL4) * τ = (τ : GL4) ^ 3 * t := by
    rcases htτ with h | h
    · exact Or.inl (by rw [← Subgroup.coe_mul, h, Subgroup.coe_mul])
    · exact Or.inr (by rw [← Subgroup.coe_mul, h, Subgroup.coe_mul, Subgroup.coe_pow])
  have htn' : ∀ j : ℕ, (t : GL4) ≠ (τ : GL4) ^ j := by
    intro j h
    apply htn
    have h' : t = τ ^ j := Subtype.ext (by rw [Subgroup.coe_pow]; exact h)
    rw [h']
    exact Subgroup.npow_mem_zpowers τ j
  obtain ⟨u, e, he, hT, hTfr, hTn⟩ := exists_cand hb5 hfix hw hτb' hτw htw htτ' htn'
  have hβ := comb_cyc_bijective hb5 hfix hw
  have hc5 := actsAs_c5 hb5 hfix w
  have hfr := actsAs_fr hb5 hfix hτb' hτw
  have hgΓ : ∀ i, ![(b : GL4), τ, t] i ∈ Γ := vec3_forall b.2 τ.2 t.2
  rcases cand_classify u e he hTfr hTn with hgood | hbad
  · obtain ⟨⟨u', e', x, Ws⟩, hmem, heq⟩ := List.mem_map.1 hgood
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    let β := LinearEquiv.ofBijective (comb (cyc b w)) hβ
    refine ⟨β.symm.toAddEquiv.trans kapEquiv, ?_⟩
    have hκ : ∀ c, (β.symm.toAddEquiv.trans kapEquiv) (comb (cyc b w) c) = kap c := fun c => by
      change kap (β.symm (β c)) = kap c
      rw [β.symm_apply_apply]
    have hτK := mem_sigSub_of_actsAs hκ hβ.2 hfr fr_cert
    have hgc : ∀ c, kap (candMat u' e' *ᵥ c) = sigmaAct x (kap c) :=
      good_cert (u', e', x, Ws) hmem
    have htK := mem_sigSub_of_actsAs hκ hβ.2 hT hgc
    have hgK : ∀ i, ![(b : GL4), τ, t] i ∈ sigSub (β.symm.toAddEquiv.trans kapEquiv) :=
      vec3_forall (mem_sigSub_of_actsAs hκ hβ.2 hc5 c5_cert) hτK htK
    refine le_of_stab_of_orbit hw (fun s hs hsw => ?_) (fun v hv => ?_)
    · have hz : ∀ s' : Γ, s' ∈ Subgroup.zpowers τ →
          (s' : GL4) ∈ sigSub (β.symm.toAddEquiv.trans kapEquiv) := by
        intro s' hs'
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs'
        rw [Subgroup.coe_zpow]
        exact Subgroup.zpow_mem _ hτK k
      rcases hstab ⟨s, hs⟩ hsw with h | h
      · exact hz ⟨s, hs⟩ h
      · have h' := Subgroup.mul_mem _ (hz (⟨s, hs⟩ * t) h) (Subgroup.inv_mem _ htK)
        rw [Subgroup.coe_mul, mul_inv_cancel_right] at h'
        exact h'
    · obtain ⟨c, rfl⟩ := hβ.2 v
      have hc : c ≠ 0 := by
        rintro rfl
        exact hv (map_zero _)
      obtain ⟨W, -, hWc⟩ : ∃ W ∈ Ws, evalV ![c5, fr, candMat u' e'] W (Pi.single 0 1) = c :=
        good_orbit (u', e', x, Ws) hmem c hc
      refine ⟨evalW ![(b : GL4), τ, t] W, evalW_mem hgK W, evalW_mem hgΓ W, ?_⟩
      have hW := ActsAs.word (actsAs_vec3 hc5 hfr hT) W
      have h0 : comb (cyc (b : GL4) w) (Pi.single 0 1) = w := by rw [comb_single, cyc_zero]
      conv_lhs => rw [← h0]
      rw [← hW, ← evalV_eq, hWc]
  · obtain ⟨⟨u', e', W⟩, hmem, heq⟩ := List.mem_map.1 hbad
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have hbc : Order3Fix (evalW ![c5, fr, candMat u' e'] W) := bad_cert (u', e', W) hmem
    exact (false_of_bad hcard htr hβ hgΓ (actsAs_vec3 hc5 hfr hT) hbc).elim

section Group

open CFSG.Open

variable {G : Type*} [Group G]

theorem nonempty_mulEquiv_v4 {W : Type*} [Group W] [Finite W] (hcomm : ∀ a b : W, a * b = b * a)
    (hpow : ∀ a : W, a ^ 2 = 1) (hcard : Nat.card W = 2 ^ 4) :
    Nonempty (W ≃* Multiplicative V4) := by
  let _ : CommGroup W := { (inferInstance : Group W) with mul_comm := hcomm }
  let _ : Module (ZMod 2) (Additive W) := AddCommGroup.zmodModule (n := 2) fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow, hpow, ofMul_one]
  have hF : Module.Finite (ZMod 2) (Additive W) := Module.Finite.of_finite
  have hFr : Module.Free (ZMod 2) (Additive W) := Module.Free.of_divisionRing _ _
  have h := @Module.natCard_eq_pow_finrank (ZMod 2) (Additive W) _ _ _ hF
  have hfin : Module.finrank (ZMod 2) (Additive W) = Module.finrank (ZMod 2) V4 := by
    rw [Nat.card_zmod] at h
    rw [Module.finrank_fin_fun]
    exact Nat.pow_right_injective le_rfl (h.symm.trans hcard)
  exact ⟨AddEquiv.toMultiplicativeRight
    (@LinearEquiv.ofFinrankEq (ZMod 2) (Additive W) V4 _ _ _ hFr _ _ _ _ hF _ hfin).toAddEquiv⟩

theorem exists_coordMap {X Z : Subgroup G} (hX : IsElemAbelian 2 X) (hXc : Nat.card X = 32)
    (hZX : Z ≤ X) (hZc : Nat.card Z = 2) :
    ∃ π : X →* Multiplicative V4, Function.Surjective π ∧ π.ker = Z.subgroupOf X := by
  have hfin : Finite X := Nat.finite_of_card_ne_zero (by rw [hXc]; norm_num)
  have hcomm : ∀ a b : X, a * b = b * a := fun a b => @mul_comm' X _ hX.1 a b
  have hN : (Z.subgroupOf X).Normal := ⟨fun n hn g => by rwa [hcomm g n, mul_inv_cancel_right]⟩
  have hZ' : Nat.card (Z.subgroupOf X) = 2 := by
    rw [← hZc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZX).toEquiv
  have hQc : Nat.card (X ⧸ Z.subgroupOf X) = 2 ^ 4 := by
    have h := (Z.subgroupOf X).card_mul_index
    rw [hZ', hXc] at h
    change (Z.subgroupOf X).index = 2 ^ 4
    omega
  have hQcomm : ∀ a b : X ⧸ Z.subgroupOf X, a * b = b * a := by
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm]
  have hQpow : ∀ a : X ⧸ Z.subgroupOf X, a ^ 2 = 1 := by
    intro a
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    have hx : x ^ 2 = 1 := Subtype.ext (by simpa using hX.2 x x.2)
    rw [← QuotientGroup.mk_pow, hx, QuotientGroup.mk_one]
  obtain ⟨e⟩ := nonempty_mulEquiv_v4 hQcomm hQpow hQc
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' _),
    e.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  ext x
  simp

theorem exists_rho {H X Z : Subgroup G} {π : X →* Multiplicative V4} (hπs : Function.Surjective π)
    (hπk : π.ker = Z.subgroupOf X) (hZcen : ∀ h ∈ H, ∀ z ∈ Z, h * z * h⁻¹ = z)
    (hXn : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) :
    ∃ ρ : H →* GL4, ∀ (h : H) (x x' : X), (x' : G) = h * x * (h : G)⁻¹ →
      π x' = Multiplicative.ofAdd (ρ h (Multiplicative.toAdd (π x))) := by
  have hπ1 : ∀ x : X, π x = 1 ↔ (x : G) ∈ Z := fun x => by
    rw [← MonoidHom.mem_ker, hπk, Subgroup.mem_subgroupOf]
  let cX : H → X → X := fun h x => ⟨h * x * (h : G)⁻¹, hXn h h.2 x x.2⟩
  have hcX : ∀ (h : H) (x y : X), π x = π y → π (cX h x) = π (cX h y) := by
    intro h x y hxy
    have hz : (x : G) * (y : G)⁻¹ ∈ Z := by
      have h1 : π (x * y⁻¹) = 1 := by
        rw [map_mul, map_inv, hxy]
        exact mul_inv_cancel _
      simpa using (hπ1 _).1 h1
    have h2 : π (cX h x * (cX h y)⁻¹) = 1 := by
      refine (hπ1 _).2 ?_
      have h3 : ((cX h x * (cX h y)⁻¹ : X) : G) = h * ((x : G) * (y : G)⁻¹) * (h : G)⁻¹ := by
        simp only [cX, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [h3, hZcen h h.2 _ hz]
      exact hz
    rw [map_mul, map_inv] at h2
    exact mul_inv_eq_one.1 h2
  let sec : V4 → X := fun v => Function.surjInv hπs (Multiplicative.ofAdd v)
  have hsec : ∀ v, π (sec v) = Multiplicative.ofAdd v := fun v => Function.surjInv_eq hπs _
  let act : H → V4 → V4 := fun h v => Multiplicative.toAdd (π (cX h (sec v)))
  have hact : ∀ (h : H) (x : X),
      π (cX h x) = Multiplicative.ofAdd (act h (Multiplicative.toAdd (π x))) := fun h x =>
    hcX h x (sec (Multiplicative.toAdd (π x))) (by rw [hsec, ofAdd_toAdd])
  have hadd : ∀ (h : H) (v w : V4), act h (v + w) = act h v + act h w := by
    intro h v w
    have h1 := hact h (sec v * sec w)
    rw [map_mul, hsec, hsec, ← ofAdd_add, toAdd_ofAdd] at h1
    have h2 : cX h (sec v * sec w) = cX h (sec v) * cX h (sec w) :=
      Subtype.ext (by simp only [cX, Subgroup.coe_mul]; group)
    rw [h2, map_mul] at h1
    calc act h (v + w) = Multiplicative.toAdd (Multiplicative.ofAdd (act h (v + w))) := rfl
      _ = act h v + act h w := by rw [← h1, toAdd_mul]
  have hmul : ∀ (h h' : H) (v : V4), act (h * h') v = act h (act h' v) := by
    intro h h' v
    have h2 : cX (h * h') (sec v) = cX h (cX h' (sec v)) :=
      Subtype.ext (by simp only [cX, Subgroup.coe_mul]; group)
    change Multiplicative.toAdd (π (cX (h * h') (sec v))) = act h (act h' v)
    rw [h2, hact]
    rfl
  have hone : ∀ v, act 1 v = v := by
    intro v
    have h2 : cX 1 (sec v) = sec v :=
      Subtype.ext (by simp only [cX, Subgroup.coe_one, one_mul, inv_one, mul_one])
    change Multiplicative.toAdd (π (cX 1 (sec v))) = v
    rw [h2, hsec, toAdd_ofAdd]
  have hzero : ∀ h : H, act h 0 = 0 := fun h => by
    have h1 := hadd h 0 0
    rw [add_zero] at h1
    exact add_eq_left.1 h1.symm
  have hsmul : ∀ (h : H) (c : ZMod 2) (v : V4), act h (c • v) = c • act h v := by
    intro h c v
    rcases zmod2_cases c with rfl | rfl
    · rw [zero_smul, zero_smul, hzero]
    · rw [one_smul, one_smul]
  let ρ : H →* GL4 :=
    { toFun := fun h =>
        { toFun := act h
          map_add' := hadd h
          map_smul' := hsmul h
          invFun := act h⁻¹
          left_inv := fun v => by rw [← hmul, inv_mul_cancel, hone]
          right_inv := fun v => by rw [← hmul, mul_inv_cancel, hone] }
      map_one' := LinearEquiv.ext hone
      map_mul' := fun h h' => LinearEquiv.ext (hmul h h') }
  refine ⟨ρ, fun h x x' hx' => ?_⟩
  have h1 : x' = cX h x := Subtype.ext hx'
  rw [h1, hact]
  rfl

theorem dempwolff218 {H J X Z : Subgroup G} (hX : IsElemAbelian 2 X) (hXc : Nat.card X = 32)
    (hZX : Z ≤ X) (hZc : Nat.card Z = 2) (hZcen : ∀ h ∈ H, ∀ z ∈ Z, h * z * h⁻¹ = z)
    (hXn : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X)
    (hJ : ∀ h, h ∈ J ↔ h ∈ H ∧ ∀ x ∈ X, h * x * h⁻¹ * x⁻¹ ∈ Z) (hidx : J.relIndex H = 120)
    (htr : ∀ x ∈ X, x ∉ Z → ∀ x' ∈ X, x' ∉ Z → ∃ h ∈ H, h * x * h⁻¹ * x'⁻¹ ∈ Z) :
    (∃ σ : H →* Equiv.Perm (Fin 5), Function.Surjective σ ∧ σ.ker = J.subgroupOf H) ∧
    ∃ (φ : H →* SigmaL2F4) (ψ : X →* Multiplicative (Fin 2 → F4)),
      Function.Surjective φ ∧ φ.ker = J.subgroupOf H ∧
      Function.Surjective ψ ∧ ψ.ker = Z.subgroupOf X ∧
      ∀ (h : H) (u u' : X), (u' : G) = h * u * (h : G)⁻¹ →
        ψ u' = Multiplicative.ofAdd (sigmaAct (φ h) (Multiplicative.toAdd (ψ u))) := by
  obtain ⟨π, hπs, hπk⟩ := exists_coordMap hX hXc hZX hZc
  obtain ⟨ρ, hρ⟩ := exists_rho hπs hπk hZcen hXn
  have hπ1 : ∀ x : X, π x = 1 ↔ (x : G) ∈ Z := fun x => by
    rw [← MonoidHom.mem_ker, hπk, Subgroup.mem_subgroupOf]
  have hπeq : ∀ x y : X, π x = π y ↔ (x : G) * (y : G)⁻¹ ∈ Z := fun x y => by
    have h1 : π x = π y ↔ π (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv]
      exact mul_inv_eq_one.symm
    rw [h1, hπ1, Subgroup.coe_mul, Subgroup.coe_inv]
  have hρπ : ∀ (h : H) (x : X), ρ h (Multiplicative.toAdd (π x)) =
      Multiplicative.toAdd (π ⟨h * x * (h : G)⁻¹, hXn h h.2 x x.2⟩) := fun h x => by
    rw [hρ h x ⟨_, hXn h h.2 x x.2⟩ rfl, toAdd_ofAdd]
  have hsurjV : ∀ v : V4, ∃ x : X, Multiplicative.toAdd (π x) = v := fun v => by
    obtain ⟨x, hx⟩ := hπs (Multiplicative.ofAdd v)
    exact ⟨x, by rw [hx, toAdd_ofAdd]⟩
  have hker : ρ.ker = J.subgroupOf H := by
    ext h
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hJ]
    constructor
    · intro h1
      refine ⟨h.2, fun x hx => ?_⟩
      have h2 := hρπ h ⟨x, hx⟩
      rw [h1] at h2
      exact (hπeq _ _).1 (congrArg Multiplicative.ofAdd h2).symm
    · rintro ⟨-, h1⟩
      ext v
      obtain ⟨x, rfl⟩ := hsurjV v
      rw [hρπ, (hπeq _ x).2 (h1 x x.2)]
      rfl
  have hcard : Nat.card ρ.range = 120 := by
    rw [← Subgroup.index_ker, hker]
    exact hidx
  have htrV : ∀ v w : V4, v ≠ 0 → w ≠ 0 → ∃ g ∈ ρ.range, g v = w := by
    intro v w hv hw
    obtain ⟨x, rfl⟩ := hsurjV v
    obtain ⟨x', rfl⟩ := hsurjV w
    have hxZ : (x : G) ∉ Z := fun h => hv (by rw [(hπ1 x).2 h]; rfl)
    have hx'Z : (x' : G) ∉ Z := fun h => hw (by rw [(hπ1 x').2 h]; rfl)
    obtain ⟨h, hh, hZ⟩ := htr x x.2 hxZ x' x'.2 hx'Z
    refine ⟨ρ ⟨h, hh⟩, ⟨⟨h, hh⟩, rfl⟩, ?_⟩
    rw [hρπ, (hπeq _ x').2 hZ]
  obtain ⟨κ, hκ⟩ := exists_coords hcard htrV
  have hex : ∀ h : H, ∃ x : SigmaL2F4, ∀ v, κ (ρ h v) = sigmaAct x (κ v) :=
    fun h => mem_sigSub.1 (hκ ⟨h, rfl⟩)
  have huniq : ∀ (g : GL4) (x y : SigmaL2F4), (∀ v, κ (g v) = sigmaAct x (κ v)) →
      (∀ v, κ (g v) = sigmaAct y (κ v)) → x = y := by
    intro g x y hx hy
    have h1 : x⁻¹ * y = 1 := eq_one_of_sigmaAct_eq fun u => by
      obtain ⟨v, rfl⟩ := κ.surjective u
      rw [sigmaAct_mul, ← hy, hx, ← sigmaAct_mul, inv_mul_cancel, sigmaAct_one]
    exact inv_mul_eq_one.1 h1
  choose φ0 hφ0 using hex
  let φ : H →* SigmaL2F4 :=
    { toFun := φ0
      map_one' := huniq (ρ 1) _ _ (hφ0 1) fun v => by rw [map_one, sigmaAct_one]; rfl
      map_mul' := fun h h' => huniq (ρ (h * h')) _ _ (hφ0 _) fun v => by
        rw [map_mul, LinearEquiv.mul_apply, hφ0, hφ0, sigmaAct_mul] }
  have hφ : ∀ (h : H) (v : V4), κ (ρ h v) = sigmaAct (φ h) (κ v) := hφ0
  have hφker : φ.ker = J.subgroupOf H := by
    rw [← hker]
    ext h
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro h1
      refine LinearEquiv.ext fun v => κ.injective ?_
      rw [hφ, h1, sigmaAct_one]
      rfl
    · intro h1
      exact huniq (ρ h) _ _ (hφ h) fun v => by rw [h1, sigmaAct_one]; rfl
  have hφs : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top]
    apply Subgroup.eq_top_of_card_eq
    rw [← Subgroup.index_ker, hφker, card_Sigma']
    exact hidx
  let ψ : X →* Multiplicative (Fin 2 → F4) := (AddEquiv.toMultiplicative κ).toMonoidHom.comp π
  have hψ : ∀ x, ψ x = Multiplicative.ofAdd (κ (Multiplicative.toAdd (π x))) := fun x => rfl
  refine ⟨⟨linePerm.comp φ, linePerm_bijective.2.comp hφs, ?_⟩, φ, ψ, hφs, hφker,
    (AddEquiv.toMultiplicative κ).surjective.comp hπs, ?_, fun h u u' hu => ?_⟩
  · rw [← hφker]
    ext h
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply,
      map_eq_one_iff _ linePerm_bijective.1]
  · rw [← hπk]
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ (AddEquiv.toMultiplicative κ).injective]
  · rw [hψ, hψ, hρ h u u' hu, toAdd_ofAdd, hφ, toAdd_ofAdd]

end Group

end CFSG.ComponentClassification.GMS78.RuGamma

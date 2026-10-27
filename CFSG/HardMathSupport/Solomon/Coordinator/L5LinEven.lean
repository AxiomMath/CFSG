module

public import CFSG.HardMathSupport.Solomon.Coordinator.L5Root
public import CFSG.HardMathSupport.Solomon.Coordinator.L5Assembly

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.HardMathSupport.Timmesfeld.LocalTwo.Torus CFSG.HardMathSupport.Solomon.Proving
open CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL (mem_semilinearAutGroup_of_odd)

section Matrix

variable {K : Type*} [Field K] {n : ℕ}

theorem diag_conj_transvection (v : Fin n → Kˣ) {i j : Fin n} (hij : i ≠ j) (c : K) :
    diagonal (fun k => (v k : K)) * transvection i j c * diagonal (fun k => (((v k)⁻¹ : Kˣ) : K)) =
      transvection i j ((v i : K) * c * (((v j)⁻¹ : Kˣ) : K)) := by
  ext a b
  rw [mul_diagonal, diagonal_mul]
  simp only [transvection, Matrix.add_apply, one_apply, single_apply]
  by_cases hab : a = b
  · subst hab
    have hai : ¬(i = a ∧ j = a) := fun h => hij (h.1.trans h.2.symm)
    simp only [ite_true, hai, ite_false, add_zero, mul_one]
    exact Units.mul_inv (v a)
  · by_cases h : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := h
      simp [hab]
    · simp [hab, h]

end Matrix

variable {F : Type} [Field F] [Finite F]

@[expose] def rootSL (c : F) : SpecialLinearGroup (Fin 5) F :=
  ⟨transvection 0 4 c, det_transvection_of_ne _ _ (by decide) c⟩

omit [Finite F] in
theorem rootSL_add (c d : F) : rootSL c * rootSL d = rootSL (c + d) :=
  Subtype.ext (transvection_mul_transvection_same _ _ (by decide) c d)

@[expose] def rootHom : Multiplicative F →* SpecialLinearGroup (Fin 5) F where
  toFun c := rootSL (Multiplicative.toAdd c)
  map_one' := Subtype.ext (by simp [rootSL])
  map_mul' a b := (rootSL_add _ _).symm

@[expose] noncomputable def rootGroup (V : Subgroup (Multiplicative F)) :
    Subgroup (projectiveSL 5 F) :=
  V.map ((proj 5 F).comp rootHom)

omit [Finite F] in
theorem isMulCommutative_rootGroup (V : Subgroup (Multiplicative F)) :
    IsMulCommutative (rootGroup V) := by
  refine ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨_, ⟨x, -, rfl⟩⟩ := a
  obtain ⟨_, ⟨y, -, rfl⟩⟩ := b
  apply Subtype.ext
  show (proj 5 F).comp rootHom x * (proj 5 F).comp rootHom y =
    (proj 5 F).comp rootHom y * (proj 5 F).comp rootHom x
  rw [← map_mul, ← map_mul, mul_comm]

omit [Finite F] in
theorem isPGroup_rootGroup [CharP F 2] (V : Subgroup (Multiplicative F)) :
    IsPGroup 2 (rootGroup V) := by
  refine IsPGroup.map (fun x => ⟨1, Subtype.ext ?_⟩) _
  show (x : Multiplicative F) ^ 2 ^ 1 = 1
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, pow_one, two_smul, CharTwo.add_self_eq_zero]

omit [Finite F] in
theorem rootGroup_ne_bot {V : Subgroup (Multiplicative F)} (hV : Multiplicative.ofAdd (1 : F) ∈ V) :
    rootGroup V ≠ ⊥ := by
  intro h
  have h1 : proj 5 F (rootSL 1) ∈ rootGroup V := ⟨_, hV, rfl⟩
  rw [h, Subgroup.mem_bot] at h1
  obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 h1)
  have := congrArg (fun M : Matrix (Fin 5) (Fin 5) F => M 0 4) hc
  simp [rootSL, transvection, scalar_apply, diagonal_apply_ne] at this

omit [Finite F] in
theorem starX_conj_rootSL {ζ : Fˣ} {k : Fin 3} {x : SpecialLinearGroup (Fin 5) F}
    (hx : SpecialLinearGroup.toGL x = starX ζ (0 : Fin 5) ![1, 2, 3] k) (c : F) :
    x * rootSL c * x⁻¹ = rootSL ((ζ : F) * c) := by
  have hxm : (x : Matrix (Fin 5) (Fin 5) F) = diagonal fun m => (tvec ζ 0 (![1, 2, 3] k) m : F) := by
    have := congrArg (fun g : GL (Fin 5) F => (g : Matrix (Fin 5) (Fin 5) F)) hx
    simpa [starX, diagHom_apply, coe_diagGL] using this
  have hxi : ((x⁻¹ : SpecialLinearGroup (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) =
      diagonal fun m => (((tvec ζ 0 (![1, 2, 3] k) m)⁻¹ : Fˣ) : F) := by
    have h1 : ((x⁻¹ : SpecialLinearGroup (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) =
        ((SpecialLinearGroup.toGL x)⁻¹ : GL (Fin 5) F) := by
      rw [← map_inv]; rfl
    rw [h1, hx, starX, ← map_inv, diagHom_apply, coe_diagGL]
    rfl
  have key : (diagonal fun m => (tvec ζ (0 : Fin 5) (![1, 2, 3] k) m : F)) *
      transvection (0 : Fin 5) 4 c *
      (diagonal fun m => (((tvec ζ (0 : Fin 5) (![1, 2, 3] k) m)⁻¹ : Fˣ) : F)) =
        transvection (0 : Fin 5) 4 ((ζ : F) * c) := by
    rw [diag_conj_transvection _ (by decide) c]
    congr 1
    fin_cases k <;> simp [tvec]
  ext a b
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hxm, hxi]
  exact congrFun (congrFun key a) b

omit [Finite F] in
theorem tvec_inv (ζ : Fˣ) (i j : Fin 5) : (tvec ζ i j)⁻¹ = tvec ζ⁻¹ i j := by
  funext m
  simp only [Pi.inv_apply, tvec, Function.update_apply, Pi.one_apply]
  split_ifs <;> simp

omit [Finite F] in
theorem starX_inv (ζ : Fˣ) (k : Fin 3) :
    (starX ζ (0 : Fin 5) ![1, 2, 3] k : GL (Fin 5) F)⁻¹ = starX ζ⁻¹ (0 : Fin 5) ![1, 2, 3] k := by
  rw [starX, starX, ← map_inv, tvec_inv]

@[expose] def IsZetaStable (ζ : Fˣ) (V : Subgroup (Multiplicative F)) : Prop :=
  ∀ c : F, Multiplicative.ofAdd c ∈ V →
    Multiplicative.ofAdd ((ζ : F) * c) ∈ V ∧ Multiplicative.ofAdd (((ζ⁻¹ : Fˣ) : F) * c) ∈ V

omit [Finite F] in
theorem proj_starX_mem_normalizer {ζ : Fˣ} {k : Fin 3} {x : SpecialLinearGroup (Fin 5) F}
    (hx : SpecialLinearGroup.toGL x = starX ζ (0 : Fin 5) ![1, 2, 3] k)
    {V : Subgroup (Multiplicative F)} (hV : IsZetaStable ζ V) :
    proj 5 F x ∈ Subgroup.normalizer (rootGroup V : Set (projectiveSL 5 F)) := by
  have hx' : SpecialLinearGroup.toGL x⁻¹ = starX ζ⁻¹ (0 : Fin 5) ![1, 2, 3] k := by
    rw [map_inv, hx, starX_inv]
  have hconj : ∀ c : F, Multiplicative.ofAdd c ∈ V →
      proj 5 F x * proj 5 F (rootSL c) * (proj 5 F x)⁻¹ ∈ rootGroup V := by
    intro c hc
    rw [← map_inv, ← map_mul, ← map_mul, starX_conj_rootSL hx c]
    exact ⟨_, (hV c hc).1, rfl⟩
  have hconj' : ∀ c : F, Multiplicative.ofAdd c ∈ V →
      (proj 5 F x)⁻¹ * proj 5 F (rootSL c) * proj 5 F x ∈ rootGroup V := by
    intro c hc
    have := starX_conj_rootSL hx' c
    rw [inv_inv] at this
    rw [← map_inv, ← map_mul, ← map_mul, this]
    exact ⟨_, (hV c hc).2, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact hconj (Multiplicative.toAdd c) hc
  · intro hy
    obtain ⟨c, hc, hcy⟩ := hy
    have := hconj' (Multiplicative.toAdd c) hc
    change (proj 5 F x)⁻¹ * ((proj 5 F).comp rootHom c) * proj 5 F x ∈ _ at this
    rw [hcy] at this
    convert this using 1
    group

section Five

variable {Lb : Type*} [Group Lb] [Finite Lb] {Γ : Lb →* projectiveSL 5 F}

theorem hasTorusFixed_three_projectiveSL_five_even [CharP F 2] (hΓ : Function.Surjective Γ)
    (hker : Γ.ker = Subgroup.center Lb) (hodd : Odd (Nat.card (Subgroup.center Lb)))
    (h5 : 5 ∣ Nat.card F - 1) : HasTorusFixed 5 3 Lb 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_five_of_dvd h5
  have hd : ∀ k : Fin 3, (0 : Fin 5) ≠ ![1, 2, 3] k := by decide
  obtain ⟨D, hcard, hX, -⟩ := exists_torusData_star hζ SpecialLinearGroup.toGL
    SpecialLinearGroup.toGL_injective (proj 5 F) proj_ker_scalar 0 4 ![1, 2, 3] (by decide) hd
    (by decide) (by decide) (fun k => mem_range_toGL_of_det (det_starX ζ hd k))
    (fun k => mem_range_toGL_of_det (det_starSw hd k))
  refine hasTorusFixed_one_of_root Nat.prime_five hΓ hker hodd D hcard (rootGroup ⊤)
    (isMulCommutative_rootGroup ⊤) (isPGroup_rootGroup ⊤) (rootGroup_ne_bot trivial)
    (fun k => ?_)
  obtain ⟨x, hx, hxk⟩ := hX k
  rw [hxk]
  exact proj_starX_mem_normalizer hx (fun _ _ => ⟨trivial, trivial⟩)

@[expose] def fixedAdd (σ : F ≃+* F) : Subgroup (Multiplicative F) where
  carrier := {c | σ (Multiplicative.toAdd c) = Multiplicative.toAdd c}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, toAdd_mul] at ha hb ⊢
    rw [map_add, ha, hb]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, toAdd_inv] at ha ⊢
    rw [map_neg, ha]

theorem hasTorusFixed_three_projectiveSL_five_even_fix [CharP F 2] (hΓ : Function.Surjective Γ)
    (hker : Γ.ker = Subgroup.center Lb) (hodd : Odd (Nat.card (Subgroup.center Lb)))
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card F = 2 ^ f) (h5 : 5 ∣ Nat.card F - 1) {β : MulAut Lb}
    {b : MulAut (projectiveSL 5 F)} (hβ : ∀ x, Γ (β x) = b (Γ x))
    (hbD : b ∉ linearAutGroup 5 F) (hb5 : b ^ 5 = 1) : HasTorusFixed 5 3 Lb β := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨A, σ, ζ, hbh, hζ, hζσ, -⟩ :=
    exists_descent_projectiveSL_five Nat.prime_two hf hK h5 hbD hb5
  obtain ⟨D, hcard, hX, -⟩ := exists_fixTorus_projectiveSL_five hΓ hker hodd hβ hbh hζ hζσ
  set Ubar := (rootGroup (fixedAdd σ)).map (conjAut 5 F A).toMonoidHom with hUbar
  have hVζ : IsZetaStable ζ (fixedAdd σ) := by
    intro c hc
    have hc' : σ c = c := hc
    have hζσ' : σ ((ζ⁻¹ : Fˣ) : F) = (ζ⁻¹ : Fˣ) := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, hζσ]
    refine ⟨?_, ?_⟩
    · show σ ((ζ : F) * c) = (ζ : F) * c
      rw [map_mul, hζσ, hc']
    · show σ (((ζ⁻¹ : Fˣ) : F) * c) = ((ζ⁻¹ : Fˣ) : F) * c
      rw [map_mul, hζσ', hc']
  refine hasTorusFixed_of_fixData_root Nat.prime_five hΓ hker hodd hβ D hcard Ubar ?_ ?_ ?_ ?_ ?_
  · have h1 := isMulCommutative_rootGroup (fixedAdd σ)
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
    obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
    apply Subtype.ext
    show (conjAut 5 F A) x * (conjAut 5 F A) y = (conjAut 5 F A) y * (conjAut 5 F A) x
    rw [← map_mul, ← map_mul]
    exact congrArg _ (congrArg Subtype.val (h1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  · exact (isPGroup_rootGroup (fixedAdd σ)).map _
  · intro h
    apply rootGroup_ne_bot (V := fixedAdd σ) (show σ (1 : F) = 1 from map_one σ)
    exact (Subgroup.map_eq_bot_iff_of_injective _ (conjAut 5 F A).injective).1 h
  · rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    show b (conjAut 5 F A (proj 5 F (rootSL (Multiplicative.toAdd c)))) = _
    refine conj_fieldAut_fix hbh (sl_map_eq_self _ ?_)
    ext i j
    simp only [rootSL, Matrix.map_apply, transvection, Matrix.add_apply, one_apply,
      single_apply]
    have hc' : σ (Multiplicative.toAdd c) = Multiplicative.toAdd c := hc
    split_ifs <;> simp [hc']
  · intro k
    obtain ⟨x, hx, hxk⟩ := hX k
    rw [hxk]
    have h1 := proj_starX_mem_normalizer hx hVζ
    rw [Subgroup.mem_normalizer_iff] at h1 ⊢
    intro y
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨_, (h1 u).1 hu, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]
    · rintro ⟨u, hu, hyu⟩
      have hy : y = (conjAut 5 F A) ((proj 5 F x)⁻¹ * u * proj 5 F x) := by
        simp only [MulEquiv.coe_toMonoidHom] at hyu
        rw [map_mul, map_mul, map_inv, hyu]
        group
      rw [hy]
      refine ⟨_, ?_, rfl⟩
      have h2 := (h1 ((proj 5 F x)⁻¹ * u * proj 5 F x)).2
      exact h2 (by
        rw [show proj 5 F x * ((proj 5 F x)⁻¹ * u * proj 5 F x) * (proj 5 F x)⁻¹ = u by group]
        exact hu)

end Five

section Assembly

variable {G : Type} [Group G] [Finite G]

theorem isCompLocallyBalanced_five_projectiveSL_even {X B : Subgroup G} (hBX : B ≤ X)
    (hB : IsElemAbelian 5 B) (hrank : GLATwoLocalRank 5 ↥X ≤ CFSG.Open.pRank 5 B)
    {L : Subgroup G} (hL : GLAPComponent 5 X L) [CharP F 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card F = 2 ^ f) (h5 : 5 ∣ Nat.card F - 1)
    (e : barOf 5 L ⧸ Subgroup.center (barOf 5 L) ≃* projectiveSL 5 F) :
    IsCompLocallyBalanced 5 2 B L := by
  have hp : Nat.Prime 5 := Nat.prime_five
  have hperf : commutator (barOf 5 L) = ⊤ :=
    (CFSG.HardMathSupport.Timmesfeld.Coordinator.isQuasisimple_barOf hp hL).1
  have hodd := CFSG.HardMathSupport.Timmesfeld.Balance.Alt.odd_card_center_barOf hp
    (by norm_num) L
  set Γ := centerQuotHom e with hΓ
  set ψ := centerQuotAut e with hψ
  have hΓs := centerQuotHom_surjective e
  have hΓk := ker_centerQuotHom e
  refine isCompLocallyBalanced_five_of_data hBX hB hrank hL ((linearAutGroup 5 F).comap ψ) ?_
    ((heisUpper_projectiveSL hp (by norm_num) h5).of_injective ψ (centerQuotAut_injective e hperf)
      (innerAut_le_map_centerQuotAut e))
    (hasCentTorus_two_projectiveSL_five hΓs hΓk hodd h5)
    (hasTorusFixed_three_projectiveSL_five_even hΓs hΓk hodd h5)
    (fun β hβR hβ5 => hasTorusFixed_three_projectiveSL_five_even_fix hΓs hΓk hodd hf hK h5
      (b := ψ β) (fun x => centerQuotAut_apply e β x) hβR (by rw [← map_pow, hβ5, map_one]))
  rintro _ ⟨x, rfl⟩
  rw [Subgroup.mem_comap, centerQuotAut_conj]
  obtain ⟨g, hg⟩ := proj_surjective 5 F (Γ x)
  rw [← hg, ← conjAut_toGL]
  exact conjAut_mem_linearAutGroup _

end Assembly

end CFSG.HardMathSupport.Solomon.Coordinator

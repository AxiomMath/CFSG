module

public import CFSG.GF2Type.SmithTypeE.DMod.RhoTD6
public import CFSG.GF2Type.SmithTypeE.DMod.PlaneTrans
public import Certificates.Certificate38751

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open CFSG.SmithD6 CFSG.GF2Type.SmithTypeE.DMod

section Fixing

variable {σ : V12 ≃ₗ[ZMod 2] V12}

theorem B12_pair (a b a' b' : Fin 6 → ZMod 2) :
    B12 (a, b) (a', b') = ∑ i, (a i * b' i + a' i * b i) := rfl

theorem q12_pair (a b : Fin 6 → ZMod 2) : q12 (a, b) = ∑ i, a i * b i := rfl

@[expose] def FixesF (σ : V12 ≃ₗ[ZMod 2] V12) : Prop := ∀ b, σ (0, b) = (0, b)

theorem fix_fst (hσ : ∀ x, q12 (σ x) = q12 x) (hF : FixesF σ) (a : Fin 6 → ZMod 2) :
    (σ (a, 0)).1 = a := by
  funext j
  have h := B12_of_isometry hσ (a, 0) (0, Pi.single j 1)
  rw [hF] at h
  simp only [B12, Pi.zero_apply, Pi.single_apply, mul_ite, mul_one, mul_zero, zero_mul,
    add_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  exact h

theorem fix_apply (hσ : ∀ x, q12 (σ x) = q12 x) (hF : FixesF σ) (a b : Fin 6 → ZMod 2) :
    σ (a, b) = (a, b + (σ (a, 0)).2) := by
  have h : ((a, b) : V12) = (a, 0) + (0, b) := by
    ext <;> simp
  rw [h, map_add, hF]
  refine Prod.ext ?_ ?_
  · simp [fix_fst hσ hF]
  · simp [add_comm]

@[expose] noncomputable def Mlin (σ : V12 ≃ₗ[ZMod 2] V12) :
    (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2) :=
  (LinearMap.snd (ZMod 2) (Fin 6 → ZMod 2) (Fin 6 → ZMod 2)) ∘ₗ σ.toLinearMap ∘ₗ
    (LinearMap.inl (ZMod 2) (Fin 6 → ZMod 2) (Fin 6 → ZMod 2))

theorem Mlin_apply (σ : V12 ≃ₗ[ZMod 2] V12) (a : Fin 6 → ZMod 2) : Mlin σ a = (σ (a, 0)).2 := rfl

theorem fix_sq (hσ : ∀ x, q12 (σ x) = q12 x) (hF : FixesF σ) (x : V12) : σ (σ x) = x := by
  obtain ⟨a, b⟩ := x
  rw [fix_apply hσ hF, fix_apply hσ hF]
  refine Prod.ext rfl ?_
  show b + (σ (a, 0)).2 + (σ (a, 0)).2 = b
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem Mlin_alt (hσ : ∀ x, q12 (σ x) = q12 x) (hF : FixesF σ) (a : Fin 6 → ZMod 2) :
    ∑ i, a i * Mlin σ a i = 0 := by
  have h := hσ (a, 0)
  rw [q12_apply, q12_apply] at h
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h
  have h1 : (σ (a, 0)).1 = a := fix_fst hσ hF a
  rw [h1] at h
  exact h

theorem Mlin_symm (hσ : ∀ x, q12 (σ x) = q12 x) (hF : FixesF σ) (a a' : Fin 6 → ZMod 2) :
    ∑ i, a i * Mlin σ a' i = ∑ i, a' i * Mlin σ a i := by
  have h := B12_of_isometry hσ (a, 0) (a', 0)
  simp only [B12, Pi.zero_apply, mul_zero, zero_mul, add_zero, Finset.sum_const_zero] at h
  rw [fix_fst hσ hF, fix_fst hσ hF] at h
  have h2 : ∑ i, (a i * Mlin σ a' i + a' i * Mlin σ a i) = 0 := h
  rw [Finset.sum_add_distrib] at h2
  exact (CharTwo.add_eq_zero.mp h2)

@[expose] noncomputable def ent (σ : V12 ≃ₗ[ZMod 2] V12) (i j : Fin 6) : ZMod 2 :=
  Mlin σ (Pi.single j 1) i

theorem ent_comm (hσ : ∀ x, q12 (σ x) = q12 x) (hF : FixesF σ) (i j : Fin 6) :
    ent σ i j = ent σ j i := by
  have h := Mlin_symm hσ hF (Pi.single j 1) (Pi.single i 1)
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at h
  exact h.symm

theorem ent_diag (hσ : ∀ x, q12 (σ x) = q12 x) (hF : FixesF σ) (i : Fin 6) : ent σ i i = 0 := by
  have h := Mlin_alt hσ hF (Pi.single i 1)
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at h
  exact h

theorem fix_ext {σ τ : V12 ≃ₗ[ZMod 2] V12} (hσ : ∀ x, q12 (σ x) = q12 x) (hF : FixesF σ)
    (hτ : ∀ x, q12 (τ x) = q12 x) (hG : FixesF τ)
    (h : ∀ i j : Fin 6, i < j → ent σ i j = ent τ i j) : σ = τ := by
  have hent : ∀ i j : Fin 6, ent σ i j = ent τ i j := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · exact h i j hij
    · rw [ent_diag hσ hF, ent_diag hτ hG]
    · rw [ent_comm hσ hF, ent_comm hτ hG]
      exact h j i hij
  have hM : Mlin σ = Mlin τ := by
    refine LinearMap.pi_ext fun j c => ?_
    funext i
    have hc : c = 0 ∨ c = 1 := by
      revert c
      decide
    rcases hc with rfl | rfl
    · simp
    · exact hent i j
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨a, b⟩ := x
  rw [fix_apply hσ hF, fix_apply hτ hG]
  have := congrFun (congrArg DFunLike.coe hM) a
  rw [Mlin_apply, Mlin_apply] at this
  rw [this]

end Fixing

section K0

noncomputable abbrev Stab0 : Subgroup TD6 := MulAction.stabilizer TD6 (0 : Fin 75735)

theorem mem_Stab0 {g : TD6} :
    g ∈ Stab0 ↔ Submodule.map (omegaTD6.symm g).1.toLinearMap (planeSub 0) = planeSub 0 := by
  rw [MulAction.mem_stabilizer_iff, plane_smul_def, planeActOmega_eq_iff]
  rfl

theorem mem_F_iff {x : V12} : x ∈ planeSub 0 ↔ x.1 = 0 := by
  unfold planeSub
  rw [pbArr_zero, mem_planeSpan_fBasis_iff]

@[expose] noncomputable def K0 : Subgroup TD6 where
  carrier := {g | ∀ x ∈ planeSub 0, (omegaTD6.symm g).1 x = x}
  mul_mem' {g h} hg hh x hx := by
    have : (omegaTD6.symm (g * h)).1 x = (omegaTD6.symm g).1 ((omegaTD6.symm h).1 x) := by
      rw [map_mul]
      rfl
    rw [this, hh x hx, hg x hx]
  one_mem' x _ := by
    rw [map_one]
    rfl
  inv_mem' {g} hg x hx := by
    have h1 := hg x hx
    have : (omegaTD6.symm g⁻¹).1 x = (omegaTD6.symm g).1.symm x := by
      rw [map_inv]
      rfl
    rw [this]
    exact (LinearEquiv.symm_apply_eq _).2 h1.symm

theorem mem_K0 {g : TD6} : g ∈ K0 ↔ ∀ x ∈ planeSub 0, (omegaTD6.symm g).1 x = x := Iff.rfl

theorem iso_symm (g : TD6) : ∀ x, q12 ((omegaTD6.symm g).1 x) = q12 x :=
  mem_isoGrp.mp (omegaPlus_le_iso (omegaTD6.symm g).2)

theorem fixesF_of_mem_K0 {g : TD6} (hg : g ∈ K0) : FixesF (omegaTD6.symm g).1 := fun b =>
  hg (0, b) (mem_F_iff.mpr rfl)

theorem K0_le_stab : K0 ≤ Stab0 := by
  intro g hg
  rw [mem_Stab0]
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    show (omegaTD6.symm g).1 x ∈ planeSub 0
    rw [hg x hx]
    exact hx
  · intro x hx
    exact ⟨x, hx, hg x hx⟩

theorem K0_normal {g k : TD6} (hg : g ∈ Stab0) (hk : k ∈ K0) : g * k * g⁻¹ ∈ K0 := by
  intro x hx
  have hm := mem_Stab0.mp hg
  have hinv : (omegaTD6.symm g).1.symm x ∈ planeSub 0 := by
    have : x ∈ Submodule.map (omegaTD6.symm g).1.toLinearMap (planeSub 0) := by
      rw [hm]
      exact hx
    obtain ⟨y, hy, hyx⟩ := this
    have : (omegaTD6.symm g).1.symm x = y := by
      rw [LinearEquiv.symm_apply_eq]
      exact hyx.symm
    rw [this]
    exact hy
  have e : (omegaTD6.symm (g * k * g⁻¹)).1 x =
      (omegaTD6.symm g).1 ((omegaTD6.symm k).1 ((omegaTD6.symm g).1.symm x)) := by
    rw [map_mul, map_mul, map_inv]
    rfl
  rw [e, hk _ hinv]
  exact LinearEquiv.apply_symm_apply _ x

theorem K0_sq {g : TD6} (hg : g ∈ K0) : g * g = 1 := by
  apply (omegaTD6.symm).injective
  rw [map_mul, map_one]
  apply Subtype.ext
  refine LinearEquiv.ext fun x => ?_
  exact fix_sq (iso_symm g) (fixesF_of_mem_K0 hg) x

theorem isPGroup_K0 : IsPGroup 2 K0 := by
  intro g
  refine ⟨1, ?_⟩
  have h := K0_sq g.2
  apply Subtype.ext
  show (g : TD6) ^ 2 ^ 1 = 1
  rw [pow_one, pow_two]
  exact h

theorem card_K0_le : Nat.card K0 ≤ 2 ^ 15 := by
  let f : K0 → ({p : Fin 6 × Fin 6 // p.1 < p.2} → ZMod 2) := fun g p =>
    ent (omegaTD6.symm g.1).1 p.1.1 p.1.2
  have hf : Function.Injective f := by
    intro g h hgh
    have hfix : ∀ g : K0, FixesF (omegaTD6.symm g.1).1 := fun g => fixesF_of_mem_K0 g.2
    have hext := fix_ext (iso_symm g.1) (hfix g) (iso_symm h.1) (hfix h) (fun i j hij =>
      congrFun hgh ⟨(i, j), hij⟩)
    apply Subtype.ext
    apply omegaTD6.symm.injective
    exact Subtype.ext hext
  have h1 := Nat.card_le_card_of_injective f hf
  have h2 : Nat.card ({p : Fin 6 × Fin 6 // p.1 < p.2} → ZMod 2) = 2 ^ 15 := by
    rw [Nat.card_fun, Nat.card_zmod]
    have : Nat.card {p : Fin 6 × Fin 6 // p.1 < p.2} = 15 := by
      rw [Nat.card_eq_fintype_card]
      decide
    rw [this]
  rw [h2] at h1
  exact h1

theorem B12_F {x y : V12} (hx : x.1 = 0) (hy : y.1 = 0) : B12 x y = 0 := by
  simp [B12, hx, hy]

theorem tvP_mem_K0 {p : Fin 365211} (hp : ∀ x ∈ lineSet p.val, x ∈ planeSub 0) :
    (⟨tvP p, tvP_mem p⟩ : TD6) ∈ K0 := by
  have hsym : omegaTD6.symm ⟨tvP p, tvP_mem p⟩ =
      ⟨siegelK p.val, siegelK_mem_omega p.2⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext (omegaTD6_siegelK p).symm
  intro x hx
  rw [hsym]
  have hts := tsPair_linePair p.2
  have hu : (dec12 (linePair p.val).1) ∈ planeSub 0 := hp _ (by simp [lineSet, lineOfPair])
  have hw : (dec12 (linePair p.val).2) ∈ planeSub 0 := hp _ (by simp [lineSet, lineOfPair])
  show siegelEquiv (dec12 (linePair p.val).1) (dec12 (linePair p.val).2) x = x
  rw [siegelEquiv_apply hts, B12_F (mem_F_iff.mp hx) (mem_F_iff.mp hw),
    B12_F (mem_F_iff.mp hx) (mem_F_iff.mp hu)]
  simp

theorem exists_transvection (y φ : Fin 6 → ZMod 2) (hy : y ≠ 0) (hφy : ∑ i, φ i * y i = 0) :
    ∃ g : TD6, g ∈ Stab0 ∧ ∀ b : Fin 6 → ZMod 2,
      (omegaTD6.symm g).1 (0, b) = (0, b + (∑ i, φ i * b i) • y) := by
  have hts : TsPair (((0 : Fin 6 → ZMod 2), y) : V12) ((φ, (0 : Fin 6 → ZMod 2)) : V12) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [q12_pair]
      simp
    · rw [q12_pair]
      simp
    · rw [B12_pair]
      simpa using hφy
  have hne : (((0 : Fin 6 → ZMod 2), y) : V12) ≠ 0 := fun h => hy (congrArg Prod.snd h)
  have hSom := siegelEquiv_mem_omega hts hne
  have hform : ∀ b : Fin 6 → ZMod 2,
      siegelEquiv (((0 : Fin 6 → ZMod 2), y) : V12) ((φ, (0 : Fin 6 → ZMod 2)) : V12) (0, b) =
        (0, b + (∑ i, φ i * b i) • y) := by
    intro b
    rw [siegelEquiv_apply hts]
    have h1 : B12 (((0 : Fin 6 → ZMod 2), b) : V12) ((φ, (0 : Fin 6 → ZMod 2)) : V12) =
        ∑ i, φ i * b i := by
      rw [B12_pair]
      simp
    have h2 : B12 (((0 : Fin 6 → ZMod 2), b) : V12) (((0 : Fin 6 → ZMod 2), y) : V12) = 0 := by
      rw [B12_pair]
      simp
    rw [h1, h2]
    refine Prod.ext ?_ ?_ <;> simp
  refine ⟨omegaTD6 ⟨_, hSom⟩, ?_, fun b => ?_⟩
  · rw [mem_Stab0, MulEquiv.symm_apply_apply]
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hx0 : x = (0, x.2) := Prod.ext (mem_F_iff.mp hx) rfl
      show siegelEquiv _ _ x ∈ planeSub 0
      rw [hx0, hform]
      exact mem_F_iff.mpr rfl
    · intro x hx
      have hx0 : x = (0, x.2) := Prod.ext (mem_F_iff.mp hx) rfl
      refine ⟨siegelEquiv (((0 : Fin 6 → ZMod 2), y) : V12) ((φ, (0 : Fin 6 → ZMod 2)) : V12) x,
        ?_, ?_⟩
      · rw [hx0, hform]
        exact mem_F_iff.mpr rfl
      · show siegelEquiv _ _ (siegelEquiv _ _ x) = x
        exact (LinearEquiv.ext_iff.mp (siegelEquiv_mul_self hts)) x
  · rw [MulEquiv.symm_apply_apply]
    exact hform b

theorem exists_phi (β η : Fin 6 → ZMod 2) (hβ : β ≠ 0) (hη : η ≠ 0) :
    ∃ φ : Fin 6 → ZMod 2, ∑ i, φ i * β i = 1 ∧ ∑ i, φ i * η i = 1 := by
  have hone : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hβ
  obtain ⟨l, hl⟩ := Function.ne_iff.mp hη
  have hk1 : β k = 1 := hone _ hk
  have hl1 : η l = 1 := hone _ hl
  by_cases hηk : η k = 1
  · refine ⟨Pi.single k 1, ?_, ?_⟩
    · simp [Pi.single_apply, hk1]
    · simp [Pi.single_apply, hηk]
  · have hηk0 : η k = 0 := by
      have : η k = 0 ∨ η k = 1 := by revert hηk; generalize η k = c; revert c; decide
      exact this.resolve_right hηk
    have hlk : l ≠ k := fun h => by rw [h] at hl1; rw [hl1] at hηk0; exact absurd hηk0 (by decide)
    by_cases hβl : β l = 1
    · refine ⟨Pi.single l 1, ?_, ?_⟩
      · simp [Pi.single_apply, hβl]
      · simp [Pi.single_apply, hl1]
    · have hβl0 : β l = 0 := by
        have : β l = 0 ∨ β l = 1 := by revert hβl; generalize β l = c; revert c; decide
        exact this.resolve_right hβl
      refine ⟨Pi.single k 1 + Pi.single l 1, ?_, ?_⟩
      · simp [add_mul, Finset.sum_add_distrib, Pi.single_apply, hk1, hβl0]
      · simp [add_mul, Finset.sum_add_distrib, Pi.single_apply, hηk0, hl1]

@[expose] noncomputable def permF (g : TD6) (hg : g ∈ Stab0) : Equiv.Perm ↥(planeSub 0) :=
  (LinearEquiv.ofSubmodules (omegaTD6.symm g).1 (planeSub 0) (planeSub 0)
    (mem_Stab0.mp hg)).toEquiv

@[expose] noncomputable def actN (N : Subgroup TD6) (hN : N ≤ Stab0) :
    ↥N →* Equiv.Perm ↥(planeSub 0) where
  toFun n := permF n.1 (hN n.2)
  map_one' := by
    refine Equiv.ext fun x => Subtype.ext ?_
    show (omegaTD6.symm (1 : TD6)).1 x = x
    rw [map_one]
    rfl
  map_mul' n m := by
    refine Equiv.ext fun x => Subtype.ext ?_
    show (omegaTD6.symm (n.1 * m.1)).1 x = (omegaTD6.symm n.1).1 ((omegaTD6.symm m.1).1 x)
    rw [map_mul]
    rfl

theorem actN_apply (N : Subgroup TD6) (hN : N ≤ Stab0) (n : ↥N) (x : ↥(planeSub 0)) :
    ((actN N hN n x : ↥(planeSub 0)) : V12) = (omegaTD6.symm n.1).1 x := rfl

theorem card_F : Nat.card ↥(planeSub 0) = 2 ^ 6 := by
  let e : ↥(planeSub 0) ≃ (Fin 6 → ZMod 2) :=
    { toFun := fun x => x.1.2
      invFun := fun b => ⟨(0, b), mem_F_iff.mpr rfl⟩
      left_inv := fun x => Subtype.ext (Prod.ext (mem_F_iff.mp x.2).symm rfl)
      right_inv := fun b => rfl }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem exists_fixed_vec {N : Subgroup TD6} (hN : N ≤ Stab0) (hp : IsPGroup 2 N) :
    ∃ x ∈ planeSub 0, x ≠ 0 ∧ ∀ n ∈ N, (omegaTD6.symm n).1 x = x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : MulAction ↥N ↥(planeSub 0) := MulAction.compHom _ (actN N hN)
  have h0 : (0 : ↥(planeSub 0)) ∈ MulAction.fixedPoints ↥N ↥(planeSub 0) := by
    intro n
    show actN N hN n 0 = 0
    exact Subtype.ext (by rw [actN_apply]; exact map_zero _)
  haveI : Finite ↥(planeSub 0) := Nat.finite_of_card_ne_zero (by rw [card_F]; norm_num)
  obtain ⟨b, hb, hb0⟩ := hp.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    ↥(planeSub 0) (by rw [card_F]; norm_num) h0
  refine ⟨b.1, b.2, fun h => hb0 (Subtype.ext h.symm), fun n hn => ?_⟩
  have := hb ⟨n, hn⟩
  exact congrArg Subtype.val this

theorem le_K0_of_normal {N : Subgroup TD6} (hN : N ≤ Stab0)
    (hnorm : ∀ g ∈ Stab0, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (hp : IsPGroup 2 N) : N ≤ K0 := by
  obtain ⟨β, hβF, hβ0, hβfix⟩ := exists_fixed_vec hN hp
  intro n hn x hx
  have hβ : β = (0, β.2) := Prod.ext (mem_F_iff.mp hβF) rfl
  have hxe : x = (0, x.2) := Prod.ext (mem_F_iff.mp hx) rfl
  by_cases hx0 : x = 0
  · rw [hx0, map_zero]
  by_cases hxβ : x = β
  · rw [hxβ]
    exact hβfix n hn
  have hβb : β.2 ≠ 0 := fun h => hβ0 (by rw [hβ, h]; rfl)
  have hxb : x.2 ≠ 0 := fun h => hx0 (by rw [hxe, h]; rfl)
  obtain ⟨φ, hφβ, hφx⟩ := exists_phi β.2 x.2 hβb hxb
  have hc : β.2 + x.2 ≠ 0 := by
    intro h
    apply hxβ
    have : x.2 = β.2 := by
      have h' : x.2 = - β.2 := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
      rw [h', CharTwo.neg_eq]
    rw [hxe, hβ, this]
  have hφc : ∑ i, φ i * (β.2 + x.2) i = 0 := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hφβ, hφx]
    exact CharTwo.add_self_eq_zero _
  obtain ⟨g, hg, hgb⟩ := exists_transvection _ φ hc hφc
  have hgβ : (omegaTD6.symm g).1 β = x := by
    rw [hβ, hgb, hxe]
    refine Prod.ext rfl ?_
    show β.2 + (∑ i, φ i * β.2 i) • (β.2 + x.2) = x.2
    rw [hφβ, one_smul, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hn' : g⁻¹ * n * g ∈ N := by
    have := hnorm g⁻¹ (Subgroup.inv_mem _ hg) n hn
    rwa [inv_inv] at this
  have e : n * g = g * (g⁻¹ * n * g) := by group
  have h1 : (omegaTD6.symm n).1 ((omegaTD6.symm g).1 β) =
      (omegaTD6.symm g).1 ((omegaTD6.symm (g⁻¹ * n * g)).1 β) := by
    have := congrArg (fun t : TD6 => (omegaTD6.symm t).1 β) e
    simpa [map_mul] using this
  rw [← hgβ, h1, hβfix _ hn']

end K0

section Cv

theorem fModel_comm' (v w : V) : fModel v w = fModel w v := by
  rw [fModel_apply, fModel_apply, fVal, fVal,
    ← Equiv.sum_comp Fin.revPerm (fun t => v t * w (Fin.rev t))]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp [Fin.revPerm_apply, mul_comm]

theorem bit_smul' (b : Bool) (v : V) : bit b • v = if b then v else 0 := by
  cases b <;> simp [bit]

theorem decode32_foldl_xor' (p : ℕ → Bool) (f : ℕ → ℕ) (n : ℕ) :
    decode32 ((List.range n).foldl (fun acc t => if p t then acc ^^^ f t else acc) 0) =
      ∑ t ∈ Finset.range n, bit (p t) • decode32 (f t) := by
  induction n with
  | zero => simp [decode32_zero]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, Finset.sum_range_succ, ← ih]
    simp only [List.foldl_cons, List.foldl_nil, bit_smul']
    split_ifs
    · rw [decode32_xor]
    · rw [add_zero]

theorem getElem!_map_of_lt'' {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) {a : Array α}
    {k : ℕ} (hk : k < a.size) : (a.map f)[k]! = f a[k]! := by
  rw [getElem!_pos (a.map f) k (by rwa [Array.size_map]), Array.getElem_map,
    getElem!_pos a k hk]

theorem getElem!_mem'' {α : Type} [Inhabited α] {a : Array α} {k : ℕ} (hk : k < a.size) :
    a[k]! ∈ a := by
  rw [getElem!_pos a k hk]
  exact Array.getElem_mem hk

theorem idCvCheck_holds : id7ChkCv = true := Certificates.certificate38751

theorem cv_parts : id7CvGens.size = 31 ∧ id7CvDual.size = 31 ∧
    (∀ g ∈ id7CvGens, id7CvGenOK g = true) ∧
    ∀ m < 32, (2 ^ m ^^^ id7CvProj (2 ^ m) = 0 ∨ 2 ^ m ^^^ id7CvProj (2 ^ m) = wt 0) := by
  have h := idCvCheck_holds
  simp only [id7ChkCv, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Array.all_eq_true', decide_eq_true_eq, Bool.or_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem cvVecs_get {t : ℕ} (ht : t < 31) : id7CvVecs[t]! = id7CvVec id7CvGens[t]! := by
  rw [id7CvVecs, getElem!_map_of_lt'' _ (by rw [(cv_parts).1]; exact ht)]

theorem dec12_mem_F {c : ℕ} (hc : c &&& 63 = 0) : dec12 c ∈ planeSub 0 := by
  rw [mem_F_iff, fst_dec12_eq_zero_iff]
  intro i hi
  have h := testBit_and_63 c i
  rw [hc, Nat.zero_testBit] at h
  simpa [hi] using h.symm

theorem cvVecs_spec {t : ℕ} (ht : t < 31) :
    ∃ p : Fin 365211, (∀ x ∈ lineSet p.val, x ∈ planeSub 0) ∧ ∃ m : ℕ, m < 32 ∧
      id7CvVecs[t]! = applyCols (tvCols p.val) (2 ^ m) ^^^ 2 ^ m := by
  obtain ⟨h1, -, h3, -⟩ := cv_parts
  have ht' : t < id7CvGens.size := by rw [h1]; exact ht
  have hg := h3 _ (getElem!_mem'' ht')
  set g := id7CvGens[t]! with hgdef
  simp only [id7CvGenOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hg
  obtain ⟨⟨⟨⟨⟨hu4096, hw4096⟩, hu63⟩, hw63⟩, hp⟩, hm⟩ := hg
  refine ⟨⟨lineIdx g.1 g.2.1, hp⟩, ?_, g.2.2, hm, ?_⟩
  · have hpair := linePair_lineIdx hu4096 hw4096 hp
    intro x hx
    rw [lineSet_eq, hpair] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact dec12_mem_F hu63
    · exact dec12_mem_F hw63
    · rw [dec12_xor]
      exact Submodule.add_mem _ (dec12_mem_F hu63) (dec12_mem_F hw63)
  · rw [cvVecs_get ht, id7CvVec]

theorem fModel_cv_eq_zero {v : V} (hv : ∀ g ∈ K0, rhoMod g v = v) {t : ℕ} (ht : t < 31) :
    fModel (decode32 id7CvVecs[t]!) v = 0 := by
  obtain ⟨p, hline, m, hm, he⟩ := cvVecs_spec ht
  have hp : (⟨tvP p, tvP_mem p⟩ : TD6) ∈ K0 := tvP_mem_K0 hline
  have hfix : tvEquiv p.val v = v := by
    have := hv _ hp
    rwa [rhoMod_tvP] at this
  rw [he, decode32_xor, ← tvEquiv_decode p.2, map_add, LinearMap.add_apply]
  have h1 : fModel (tvEquiv p.val (decode32 (2 ^ m))) v = fModel (decode32 (2 ^ m)) v := by
    calc fModel (tvEquiv p.val (decode32 (2 ^ m))) v =
        fModel (tvEquiv p.val (decode32 (2 ^ m))) (tvEquiv p.val v) := by rw [hfix]
      _ = fModel (decode32 (2 ^ m)) v := fModel_tvEquiv p.2 _ _
  rw [h1]
  exact CharTwo.add_self_eq_zero _

theorem fixed_of_K0 {v : V} (hv : ∀ g ∈ K0, rhoMod g v = v) : v = 0 ∨ v = wtV 0 := by
  have hw : ∀ t < 31, fModel v (decode32 id7CvVecs[t]!) = 0 := fun t ht => by
    rw [fModel_comm']
    exact fModel_cv_eq_zero hv ht
  have hproj : ∀ m : Fin 32, decode32 (id7CvProj (2 ^ m.val)) =
      ∑ t : Fin 31, fModel (Pi.single m 1) (decode32 id7CvVecs[t.val]!) •
        decode32 id7CvDual[t.val]! := by
    intro m
    rw [id7CvProj, decode32_foldl_xor', ← Fin.sum_univ_eq_sum_range
      (fun t => bit (fB (2 ^ m.val) id7CvVecs[t]!) • decode32 id7CvDual[t]!) 31]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← decode32_two_pow, fModel_decode]
  have hres : ∀ m : Fin 32, Pi.single m (1 : ZMod 2) + ∑ t : Fin 31,
      fModel (Pi.single m 1) (decode32 id7CvVecs[t.val]!) • decode32 id7CvDual[t.val]! ∈
        Submodule.span (ZMod 2) {wtV 0} := by
    intro m
    have e : decode32 (2 ^ m.val ^^^ id7CvProj (2 ^ m.val)) =
        Pi.single m (1 : ZMod 2) + ∑ t : Fin 31,
          fModel (Pi.single m 1) (decode32 id7CvVecs[t.val]!) • decode32 id7CvDual[t.val]! := by
      rw [decode32_xor, hproj, decode32_two_pow]
    rw [← e]
    rcases (cv_parts).2.2.2 m.val m.2 with h | h
    · rw [h, decode32_zero]
      exact Submodule.zero_mem _
    · rw [h]
      exact Submodule.mem_span_singleton_self _
  have hsum : v = ∑ m : Fin 32, v m • (Pi.single m (1 : ZMod 2) : V) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  have h0 : ∑ m : Fin 32, v m • ∑ t : Fin 31,
      fModel (Pi.single m 1) (decode32 id7CvVecs[t.val]!) • decode32 id7CvDual[t.val]! = 0 := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [← Finset.sum_smul]
    have e : ∑ m : Fin 32, v m * fModel (Pi.single m 1) (decode32 id7CvVecs[t.val]!) =
        fModel v (decode32 id7CvVecs[t.val]!) := by
      conv_rhs => rw [hsum]
      simp [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [e, hw t t.2, zero_smul]
  have hv' : v = ∑ m : Fin 32, v m • (Pi.single m (1 : ZMod 2) + ∑ t : Fin 31,
      fModel (Pi.single m 1) (decode32 id7CvVecs[t.val]!) • decode32 id7CvDual[t.val]!) := by
    simp only [smul_add, Finset.sum_add_distrib]
    rw [h0, add_zero]
    exact hsum
  have hmem : v ∈ Submodule.span (ZMod 2) {wtV 0} := by
    rw [hv']
    exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (hres m)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
  rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl
  · left
    rw [← ha, zero_smul]
  · right
    rw [← ha, one_smul]

end Cv

section Syl

theorem le_of_normal_isPGroup_of_max {X : Type*} [Group X] {H N P : Subgroup X} (hNH : N ≤ H)
    (hPH : P ≤ H) (hnorm : ∀ g ∈ H, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (hN : IsPGroup 2 N)
    (hP : IsPGroup 2 P) (hmax : ∀ Q : Subgroup X, P ≤ Q → IsPGroup 2 Q → Q = P) : N ≤ P := by
  have hnormP : P ≤ Subgroup.normalizer (N : Set X) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact hnorm g (hPH hg) n hn
    · intro hn
      have := hnorm g⁻¹ (H.inv_mem (hPH hg)) _ hn
      rwa [show g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n by group] at this
  have hsup : IsPGroup 2 (N ⊔ P : Subgroup X) := hN.to_sup_of_normal_left' hP hnormP
  have := hmax _ le_sup_right hsup
  rw [← this]
  exact le_sup_left

theorem isMax_map {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {P : Subgroup X}
    (hmax : ∀ Q : Subgroup X, P ≤ Q → IsPGroup 2 Q → Q = P) :
    ∀ Q : Subgroup Y, P.map e.toMonoidHom ≤ Q → IsPGroup 2 Q → Q = P.map e.toMonoidHom := by
  intro Q hPQ hQ
  have h1 : P ≤ Q.comap e.toMonoidHom := fun x hx => hPQ ⟨x, hx, rfl⟩
  have h2 : IsPGroup 2 (Q.comap e.toMonoidHom) := hQ.comap_of_injective _ e.injective
  have h3 := hmax _ h1 h2
  rw [← h3, Subgroup.map_comap_eq_self_of_surjective e.surjective]

theorem K0_le_of_max {P : Subgroup TD6} (hPS : P ≤ Stab0) (hP : IsPGroup 2 P)
    (hmax : ∀ Q : Subgroup TD6, P ≤ Q → IsPGroup 2 Q → Q = P) : K0 ≤ P :=
  le_of_normal_isPGroup_of_max K0_le_stab hPS (fun _ hg _ hn => K0_normal hg hn) isPGroup_K0 hP hmax

theorem fixed_vec_of_maximal {P : Subgroup TD6} (hP : IsPGroup 2 P)
    (hmax : ∀ Q : Subgroup TD6, P ≤ Q → IsPGroup 2 Q → Q = P) {v : V}
    (hv : ∀ g ∈ P, rhoMod g v = v) : v = 0 ∨ ∃ i : Fin 75735, v = wtV i.val := by
  obtain ⟨i, hi⟩ := exists_fixed_plane P hP
  obtain ⟨g₀, hg₀⟩ := exists_smul_planes_eq i 0
  have hg₀' : g₀⁻¹ • (0 : Fin 75735) = i := by
    rw [inv_smul_eq_iff]
    exact hg₀.symm
  have hP'p : IsPGroup 2 (P.map (MulAut.conj g₀).toMonoidHom) := hP.map _
  have hP'max := isMax_map (MulAut.conj g₀) hmax
  have hP'S : P.map (MulAut.conj g₀).toMonoidHom ≤ Stab0 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    show (g₀ * y * g₀⁻¹) • (0 : Fin 75735) = 0
    rw [mul_smul, mul_smul, hg₀', hi y hy, hg₀]
  have hK := K0_le_of_max hP'S hP'p hP'max
  have hv' : ∀ k ∈ K0, rhoMod k (rhoMod g₀ v) = rhoMod g₀ v := by
    intro k hk
    obtain ⟨y, hy, rfl⟩ := hK hk
    show rhoMod (g₀ * y * g₀⁻¹) (rhoMod g₀ v) = rhoMod g₀ v
    rw [map_mul, map_mul, map_inv]
    show rhoMod g₀ (rhoMod y ((rhoMod g₀)⁻¹ (rhoMod g₀ v))) = rhoMod g₀ v
    rw [show (rhoMod g₀)⁻¹ (rhoMod g₀ v) = v from (rhoMod g₀).symm_apply_apply v, hv y hy]
  rcases fixed_of_K0 hv' with h | h
  · left
    exact (rhoMod g₀).injective (by rw [h, map_zero])
  · right
    refine ⟨i, ?_⟩
    have := congrArg (rhoMod g₀⁻¹) h
    rw [map_inv] at this
    rw [show (rhoMod g₀)⁻¹ (rhoMod g₀ v) = v from (rhoMod g₀).symm_apply_apply v] at this
    rw [this, ← map_inv]
    exact (rhoMod_wtV g₀⁻¹ 0).trans (congrArg (fun j : Fin 75735 => wtV j.val) hg₀')

theorem fModel_nondeg : fModel.Nondegenerate :=
  ⟨fun _ h => fModel_nondegenerate h,
    fun _ h => fModel_nondegenerate fun u => by rw [fModel_comm']; exact h u⟩

theorem fixed_of_stab0 {v : V} (hv : ∀ g ∈ Stab0, rhoMod g v = v) : v = 0 ∨ v = wtV 0 :=
  fixed_of_K0 fun g hg => hv g (K0_le_stab hg)

theorem eq_fModel_or_zero (B' : LinearMap.BilinForm (ZMod 2) V)
    (hB : ∀ (g : TD6) (v w : V), B' (rhoMod g v) (rhoMod g w) = B' v w) :
    B' = fModel ∨ B' = 0 := by
  set A := B'.symmCompOfNondegenerate fModel fModel_nondeg with hA
  have hAB : ∀ v w, fModel (A v) w = B' v w := fun v w =>
    LinearMap.BilinForm.symmCompOfNondegenerate_left_apply B' fModel_nondeg w v
  have hcomm : ∀ (g : TD6) (v : V), A (rhoMod g v) = rhoMod g (A v) := by
    intro g v
    have h0 : ∀ w', fModel (A (rhoMod g v) + rhoMod g (A v)) w' = 0 := by
      intro w'
      obtain ⟨w, rfl⟩ : ∃ w, rhoMod g w = w' := ⟨(rhoMod g).symm w', (rhoMod g).apply_symm_apply w'⟩
      rw [map_add, LinearMap.add_apply, hAB, hB, ← hAB, ← fModel_rhoMod g (A v) w]
      exact CharTwo.add_self_eq_zero _
    have := fModel_nondegenerate h0
    exact (CharTwo.add_eq_zero.mp this)
  have hfix : ∀ g ∈ Stab0, rhoMod g (A (wtV 0)) = A (wtV 0) := by
    intro g hg
    rw [← hcomm]
    have h1 : rhoMod g (wtV 0) = wtV 0 := by
      have := rhoMod_wtV g 0
      rw [MulAction.mem_stabilizer_iff.mp hg] at this
      exact this
    exact congrArg A h1
  have hAw : ∀ (c : ZMod 2), A (wtV 0) = c • wtV 0 →
      ∀ i : Fin 75735, A (wtV i.val) = c • wtV i.val := by
    intro c hc i
    obtain ⟨g, hg⟩ := exists_smul_zero_eq i
    have h1 : rhoMod g (wtV 0) = wtV i.val := by
      have := rhoMod_wtV g 0
      rw [hg] at this
      exact this
    rw [← h1, hcomm, hc, map_smul]
  have hAext : ∀ (c : ZMod 2), A (wtV 0) = c • wtV 0 →
      (A : V →ₗ[ZMod 2] V) = c • (LinearMap.id : V →ₗ[ZMod 2] V) := fun c hc =>
    LinearMap.ext_on_range span_wtV fun i => by
      rw [hAw c hc i]
      rfl
  rcases fixed_of_stab0 (hfix) with h | h
  · right
    have hA0 : (A : V →ₗ[ZMod 2] V) = (0 : ZMod 2) • (LinearMap.id : V →ₗ[ZMod 2] V) :=
      hAext 0 (by rw [h, zero_smul])
    refine LinearMap.ext fun v => LinearMap.ext fun w => ?_
    rw [← hAB, hA0]
    simp
  · left
    have hA1 : (A : V →ₗ[ZMod 2] V) = (1 : ZMod 2) • (LinearMap.id : V →ₗ[ZMod 2] V) :=
      hAext 1 (by rw [h, one_smul])
    refine LinearMap.ext fun v => LinearMap.ext fun w => ?_
    rw [← hAB, hA1]
    simp

end Syl

end CFSG.GF2Type.SmithTypeE.E7

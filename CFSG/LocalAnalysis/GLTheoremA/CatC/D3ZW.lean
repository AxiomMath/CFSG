module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3FTriality
public import CFSG.LieType.Chevalley.OrdinaryEFieldGraphQuotient
public import CFSG.LieType.Chevalley.LangFiniteRootCentralizer
public import CFSG.HardMathSupport.Lang.D4Three.NormalForm

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.D4Three


section Formula

variable {K : Type} [Field K]

theorem units_map_entrywiseHom_d4P (σ : K →+* K) :
    Units.map (entrywiseHom σ) (d4P K) = d4P K :=
  Units.ext (entrywise_diagramMap (t := TwistTag.D4) σ)

theorem coe_normal_form_apply (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K)
    (ε : ℕ) (x : adjointGroup Tag.D4 K) :
    ((MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) x : ModGL Tag.D4 K) =
      ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ ε) *
        Units.map (entrywiseHom σ.toRingHom) (x : ModGL Tag.D4 K) *
        ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ ε)⁻¹ := by
  have hP : ∀ n : ℕ, Units.map (entrywiseHom σ.toRingHom) (d4P K ^ n) = d4P K ^ n := fun n => by
    rw [map_pow, units_map_entrywiseHom_d4P]
  simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_exactNormalAut, coe_d4Graph, map_mul, map_inv, hP]
  change (g : ModGL Tag.D4 K) * (rootDiagUnit Tag.D4 a * (1 : ModGL Tag.D4 K) *
    (d4P K ^ ε * Units.map (entrywiseHom σ.toRingHom) (x : ModGL Tag.D4 K) * (d4P K ^ ε)⁻¹) *
      (1 : ModGL Tag.D4 K)⁻¹ * (rootDiagUnit Tag.D4 a)⁻¹) * (g : ModGL Tag.D4 K)⁻¹ = _
  group

end Formula

section Poly

variable {K : Type} [Field K]

theorem injective_zero_one_neg_one {K : Type} [Field K] (hK2 : (2 : K) ≠ 0) :
    Function.Injective (![0, 1, -1] : Fin 3 → K) := by
  have h01 : (0 : K) ≠ 1 := zero_ne_one
  have h0m : (0 : K) ≠ -1 := fun h => one_ne_zero (neg_eq_zero.1 h.symm)
  have h1m : (1 : K) ≠ -1 := by
    intro h
    apply hK2
    have h' : (1 : K) + 1 = 0 := by
      have := congrArg (· + (1 : K)) h
      simpa using this
    simpa [one_add_one_eq_two] using h'
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> tauto

theorem commute_xOp_of_pm_one (hK2 : (2 : K) ≠ 0) (i : Fin Tag.D4.rank)
    (h : Module.End K (RootModule Tag.D4 K))
    (h1 : h * xOp Tag.D4 K i 1 = xOp Tag.D4 K i 1 * h)
    (h2 : h * xOp Tag.D4 K i (-1) = xOp Tag.D4 K i (-1) * h) (c : K) :
    h * xOp Tag.D4 K i c = xOp Tag.D4 K i c * h := by
  have hf := injective_zero_one_neg_one hK2
  refine commute_of_polynomial_entries (τ := Tag.D4) (F := xOp Tag.D4 K i) (D := 2) (fun a b => ?_) h
    ![0, 1, -1] hf ?_ ?_ c
  · obtain ⟨p, q, hp, hq, hpq⟩ := exists_entry_polynomial K Tag.D4 i a b
    exact ⟨p, by simpa [entryDegreeBound] using hp, fun c => (hpq c).1⟩
  · simp [entryDegreeBound]
  · intro j
    fin_cases j
    · simp [xOp_zero]
    · simpa using h1
    · simpa using h2

theorem commute_yOp_of_pm_one (hK2 : (2 : K) ≠ 0) (i : Fin Tag.D4.rank)
    (h : Module.End K (RootModule Tag.D4 K))
    (h1 : h * yOp Tag.D4 K i 1 = yOp Tag.D4 K i 1 * h)
    (h2 : h * yOp Tag.D4 K i (-1) = yOp Tag.D4 K i (-1) * h) (c : K) :
    h * yOp Tag.D4 K i c = yOp Tag.D4 K i c * h := by
  have hf := injective_zero_one_neg_one hK2
  refine commute_of_polynomial_entries (τ := Tag.D4) (F := yOp Tag.D4 K i) (D := 2) (fun a b => ?_) h
    ![0, 1, -1] hf ?_ ?_ c
  · obtain ⟨p, q, hp, hq, hpq⟩ := exists_entry_polynomial K Tag.D4 i a b
    exact ⟨q, by simpa [entryDegreeBound] using hq, fun c => (hpq c).2⟩
  · simp [entryDegreeBound]
  · intro j
    fin_cases j
    · simp [yOp_zero]
    · simpa using h1
    · simpa using h2

end Poly

section Centralizer

variable {K : Type} [Field K]

theorem commute_adjointGroup_of_pm_one (hK2 : (2 : K) ≠ 0) (h : ModGL Tag.D4 K)
    (hx : ∀ (i : Fin Tag.D4.rank) (c : K), (c = 1 ∨ c = -1) →
      h * xUnit Tag.D4 K i c = xUnit Tag.D4 K i c * h)
    (hy : ∀ (i : Fin Tag.D4.rank) (c : K), (c = 1 ∨ c = -1) →
      h * yUnit Tag.D4 K i c = yUnit Tag.D4 K i c * h)
    (x : ModGL Tag.D4 K) (hxC : x ∈ adjointGroup Tag.D4 K) : h * x = x * h := by
  have hle : adjointGroup Tag.D4 K ≤ Subgroup.centralizer ({h} : Set (ModGL Tag.D4 K)) := by
    rw [adjointGroup, Subgroup.closure_le]
    rintro g ⟨i, c, hg | hg⟩
    · have hg' : g = xUnit Tag.D4 K i c := Units.ext (by rw [hg, coe_xUnit])
      subst hg'
      have e1 := congrArg Units.val (hx i 1 (Or.inl rfl))
      have e2 := congrArg Units.val (hx i (-1) (Or.inr rfl))
      simp only [Units.val_mul, coe_xUnit] at e1 e2
      have := commute_xOp_of_pm_one hK2 i (h : Module.End K (RootModule Tag.D4 K)) e1 e2 c
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact Units.ext (by simp only [Units.val_mul, coe_xUnit]; exact this.symm)
    · have hg' : g = yUnit Tag.D4 K i c := Units.ext (by rw [hg, coe_yUnit])
      subst hg'
      have e1 := congrArg Units.val (hy i 1 (Or.inl rfl))
      have e2 := congrArg Units.val (hy i (-1) (Or.inr rfl))
      simp only [Units.val_mul, coe_yUnit] at e1 e2
      have := commute_yOp_of_pm_one hK2 i (h : Module.End K (RootModule Tag.D4 K)) e1 e2 c
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact Units.ext (by simp only [Units.val_mul, coe_yUnit]; exact this.symm)
  have := Subgroup.mem_centralizer_singleton_iff.1 (hle hxC)
  exact this.symm

end Centralizer

section Main

theorem ringEquiv_eq_one_of_cube_fixes_subfield {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (k : Subfield K)
    (hkk : Nat.card k ^ 2 = Nat.card K) (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1)
    (hσk : ∀ c ∈ k, σ c = c) : σ = 1 := by
  by_contra hne
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hne
  obtain ⟨φ, -, -, -, -, hfix⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hp hf hK
  obtain ⟨hdvd, S, hS, hcardS⟩ := hfix (Subgroup.zpowers σ)
  have hA : Nat.card (Subgroup.zpowers σ) = 3 := by rw [Nat.card_zpowers, hord]
  rw [hA] at hdvd hcardS
  obtain ⟨g, hg⟩ := hdvd
  have hg1 : 1 ≤ g := by omega
  have hfg : f / 3 = g := by omega
  rw [hfg] at hcardS
  have hkS : ∀ c : k, (c : K) ∈ S := by
    intro c
    have : (c : K) ∈ (S : Set K) := by
      rw [hS]
      intro τ hτ
      have hst : σ ∈ MulAction.stabilizer (K ≃+* K) (c : K) := hσk c c.2
      exact Subgroup.zpowers_le.2 hst hτ
    exact this
  have hle : Nat.card k ≤ Nat.card S := by
    refine Nat.card_le_card_of_injective (fun c => ⟨c.1, hkS c⟩) ?_
    intro a b hab
    exact Subtype.ext (Subtype.mk.inj hab)
  have hle2 : Nat.card k ^ 2 ≤ (p ^ g) ^ 2 := by
    rw [← hcardS]; exact Nat.pow_le_pow_left hle 2
  have hlt : (p ^ g) ^ 2 < p ^ f := by
    rw [← pow_mul, hg]
    exact Nat.pow_lt_pow_right hp.one_lt (by omega)
  rw [hkk, hK] at hle2
  omega

theorem claimW {K : Type} [Field K] [Finite K] [CharP K 3] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 3 ^ f) (k : Subfield K) (hkk : Nat.card k ^ 2 = Nat.card K)
    (w : MulAut (adjointGroup Tag.D4 K)) (hw3 : w ^ 3 = 1)
    (hwx : ∀ (i : Fin Tag.D4.rank) (c : K), c ∈ k → w (adjX Tag.D4 K i c) = adjX Tag.D4 K i c)
    (hwy : ∀ (i : Fin Tag.D4.rank) (c : K), c ∈ k → w (adjY Tag.D4 K i c) = adjY Tag.D4 K i c) :
    w = 1 := by
  obtain ⟨g, a, σ, ε, hε, hσ3, hw⟩ := CFSG.HardMathSupport.Lang.D4Three.exists_cube_normal_form_sigma w hw3
  have hK2 : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K 3] at h'
    omega
  set h : ModGL Tag.D4 K := (g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ ε with hh
  have hform : ∀ x : adjointGroup Tag.D4 K, (w x : ModGL Tag.D4 K) =
      h * Units.map (entrywiseHom σ.toRingHom) (x : ModGL Tag.D4 K) * h⁻¹ := by
    intro x
    rw [hw]
    exact coe_normal_form_apply g a σ ε x
  have hσ1 : ∀ c : K, (c = 1 ∨ c = -1) → σ c = c := by
    rintro c (rfl | rfl) <;> simp
  have hmemk : ∀ c : K, (c = 1 ∨ c = -1) → c ∈ k := by
    rintro c (rfl | rfl)
    · exact k.one_mem
    · exact k.neg_mem k.one_mem
  have hxc : ∀ (i : Fin Tag.D4.rank) (c : K), (c = 1 ∨ c = -1) →
      h * xUnit Tag.D4 K i c = xUnit Tag.D4 K i c * h := by
    intro i c hc
    have e := congrArg (fun y : adjointGroup Tag.D4 K => (y : ModGL Tag.D4 K)) (hwx i c (hmemk c hc))
    rw [hform] at e
    change h * Units.map (entrywiseHom σ.toRingHom) (xUnit Tag.D4 K i c) * h⁻¹ = xUnit Tag.D4 K i c
      at e
    rw [units_map_entrywiseHom_xUnit] at e
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hσ1 c hc] at e
    calc h * xUnit Tag.D4 K i c = (h * xUnit Tag.D4 K i c * h⁻¹) * h := by group
      _ = xUnit Tag.D4 K i c * h := by rw [e]
  have hyc : ∀ (i : Fin Tag.D4.rank) (c : K), (c = 1 ∨ c = -1) →
      h * yUnit Tag.D4 K i c = yUnit Tag.D4 K i c * h := by
    intro i c hc
    have e := congrArg (fun y : adjointGroup Tag.D4 K => (y : ModGL Tag.D4 K)) (hwy i c (hmemk c hc))
    rw [hform] at e
    change h * Units.map (entrywiseHom σ.toRingHom) (yUnit Tag.D4 K i c) * h⁻¹ = yUnit Tag.D4 K i c
      at e
    rw [units_map_entrywiseHom_yUnit] at e
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hσ1 c hc] at e
    calc h * yUnit Tag.D4 K i c = (h * yUnit Tag.D4 K i c * h⁻¹) * h := by group
      _ = yUnit Tag.D4 K i c * h := by rw [e]
  have hcomm : ∀ x : ModGL Tag.D4 K, x ∈ adjointGroup Tag.D4 K → h * x = x * h :=
    commute_adjointGroup_of_pm_one hK2 h hxc hyc
  have hσk : ∀ c ∈ k, σ c = c := by
    intro c hc
    have e := congrArg (fun y : adjointGroup Tag.D4 K => (y : ModGL Tag.D4 K)) (hwx 0 c hc)
    rw [hform] at e
    change h * Units.map (entrywiseHom σ.toRingHom) (xUnit Tag.D4 K 0 c) * h⁻¹ = xUnit Tag.D4 K 0 c
      at e
    rw [units_map_entrywiseHom_xUnit] at e
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at e
    have h2 := hcomm (xUnit Tag.D4 K 0 (σ c)) (xUnit_mem_adjointGroup _ _)
    have e3 : xUnit Tag.D4 K 0 (σ c) = xUnit Tag.D4 K 0 c := by
      rw [← e, h2]; group
    have := adjX_injective (τ := Tag.D4) (K := K) 0 (Subtype.ext e3)
    exact this
  have hσ : σ = 1 :=
    ringEquiv_eq_one_of_cube_fixes_subfield Nat.prime_three hf hK k hkk σ hσ3 hσk
  subst hσ
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [hform]
  have hx := hcomm (x : ModGL Tag.D4 K) x.2
  change h * Units.map (entrywiseHom (RingEquiv.refl K).toRingHom) (x : ModGL Tag.D4 K) * h⁻¹ = _
  have : Units.map (entrywiseHom (RingEquiv.refl K).toRingHom) (x : ModGL Tag.D4 K) = x :=
    Units.ext (entrywise_id _)
  rw [this, hx]
  group
  rfl

end Main

end CFSG.LocalAnalysis.GLTheoremA

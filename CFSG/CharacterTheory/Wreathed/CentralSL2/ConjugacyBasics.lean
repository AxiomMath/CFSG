module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.NonsplitTorusWeyl

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization

section General

variable {K : Type*} [Group K]

theorem card_isConj_mul_card_centralizer [Finite K] (g : K) :
    Nat.card {h : K // IsConj g h} * Nat.card (Subgroup.centralizer {g} : Subgroup K) =
      Nat.card K := by
  let f : K → {h : K // IsConj g h} := fun k => ⟨k * g * k⁻¹, isConj_iff.mpr ⟨k, rfl⟩⟩
  have hfib : ∀ h : {h : K // IsConj g h},
      Nat.card {k // f k = h} = Nat.card (Subgroup.centralizer {g} : Subgroup K) := by
    intro h
    obtain ⟨k₀, hk₀⟩ := isConj_iff.mp h.2
    refine Nat.card_congr
      { toFun := fun k => ⟨k₀⁻¹ * k, ?_⟩
        invFun := fun c => ⟨k₀ * c, ?_⟩
        left_inv := fun k => Subtype.ext (mul_inv_cancel_left _ _)
        right_inv := fun c => Subtype.ext (inv_mul_cancel_left _ _) }
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have hk := congrArg Subtype.val k.2
      change (k : K) * g * (k : K)⁻¹ = h.1 at hk
      rw [← hk₀] at hk
      calc k₀⁻¹ * k * g = k₀⁻¹ * ((k : K) * g * (k : K)⁻¹) * k := by group
        _ = g * (k₀⁻¹ * k) := by rw [hk]; group
    · apply Subtype.ext
      change k₀ * (c : K) * g * (k₀ * c)⁻¹ = h.1
      have hc := Subgroup.mem_centralizer_singleton_iff.mp c.2
      rw [← hk₀]
      calc k₀ * (c : K) * g * (k₀ * c)⁻¹ = k₀ * ((c : K) * g) * (c : K)⁻¹ * k₀⁻¹ := by group
        _ = k₀ * g * k₀⁻¹ := by rw [hc]; group
  have : Fintype {h : K // IsConj g h} := Fintype.ofFinite _
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  simp only [hfib]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

variable {Ω : Type*} [MulAction K Ω]

theorem card_fixed_conj (k g : K) :
    Nat.card {p : Ω // (k * g * k⁻¹) • p = p} = Nat.card {p : Ω // g • p = p} := by
  refine Nat.card_congr
    { toFun := fun p => ⟨k⁻¹ • p.1, ?_⟩
      invFun := fun p => ⟨k • p.1, ?_⟩
      left_inv := fun p => Subtype.ext (smul_inv_smul _ _)
      right_inv := fun p => Subtype.ext (inv_smul_smul _ _) }
  · have hp := p.2
    rw [mul_smul, mul_smul] at hp
    exact eq_inv_smul_iff.mpr hp
  · rw [mul_smul, mul_smul, inv_smul_smul, p.2]

theorem card_fixed_of_isConj {g h : K} (hgh : IsConj g h) :
    Nat.card {p : Ω // h • p = p} = Nat.card {p : Ω // g • p = p} := by
  obtain ⟨k, rfl⟩ := isConj_iff.mp hgh
  exact card_fixed_conj k g

theorem two_mul_ncard_image_of_pairs {α β : Type*} [Finite α] (f : α → β) (w : α → α)
    (S : Set α) (hS : ∀ P ∈ S, w P ∈ S ∧ w P ≠ P)
    (hf : ∀ P ∈ S, ∀ Q ∈ S, f P = f Q ↔ Q = P ∨ Q = w P) :
    2 * Set.ncard (f '' S) = Set.ncard S := by
  have : Fintype α := Fintype.ofFinite α
  set s := S.toFinset with hs
  have hfibre : ∀ x ∈ s.image f, (s.filter (fun P => f P = x)).card = 2 := by
    intro x hx
    obtain ⟨P₀, hP₀, rfl⟩ := Finset.mem_image.mp hx
    have hP₀S : P₀ ∈ S := by simpa [hs] using hP₀
    have hfil : s.filter (fun P => f P = f P₀) = {P₀, w P₀} := by
      ext Q
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, hs,
        Set.mem_toFinset]
      constructor
      · rintro ⟨hQ, hfQ⟩
        exact (hf P₀ hP₀S Q hQ).mp hfQ.symm
      · rintro (rfl | rfl)
        · exact ⟨hP₀S, rfl⟩
        · exact ⟨(hS P₀ hP₀S).1, ((hf P₀ hP₀S _ (hS P₀ hP₀S).1).mpr (Or.inr rfl)).symm⟩
    rw [hfil, Finset.card_pair (hS P₀ hP₀S).2.symm]
  have h2 : s.card = 2 * (s.image f).card := by
    rw [Finset.card_eq_sum_card_image f s, Finset.sum_congr rfl hfibre, Finset.sum_const,
      smul_eq_mul, mul_comm]
  have hSs : S = ↑s := by simp [hs]
  rw [hSs, ← Finset.coe_image, Set.ncard_coe_finset, Set.ncard_coe_finset, h2]

end General

section Model

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}

omit [Fintype F] in
theorem smul_eq_coordinateGLAction {g : CentralExtension F b m hm heven}
    {M : GL (Fin 2) F} (hM : projectiveMap F b m hm heven g = ProjGenLinGroup.mk M)
    (p : Omega F) : g • p = coordinateGLAction F M p := by
  rw [centralExtension_smul_def, ← coordinatePGLAction_projectiveMap, hM]
  rfl

omit [Fintype F] in
theorem projectiveMap_eq_one_iff (hb : ¬ IsSquare b) (g : CentralExtension F b m hm heven) :
    projectiveMap F b m hm heven g = 1 ↔
      g ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) := by
  rw [← MonoidHom.mem_ker, projectiveMap_ker F b m hm heven hb]

theorem card_fixed_le_two (hb : ¬ IsSquare b) {g : CentralExtension F b m hm heven}
    (hg : g ∉ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) :
    Nat.card {p : Omega F // g • p = p} = 0 ∨ Nat.card {p : Omega F // g • p = p} = 1 ∨
      Nat.card {p : Omega F // g • p = p} = 2 := by
  have h2 := two_ne_zero_of_not_isSquare hb
  obtain ⟨M, hM⟩ := ProjGenLinGroup.mk_surjective (projectiveMap F b m hm heven g)
  have hnonscalar : ¬ ∃ c : Fˣ, M = GeneralLinearGroup.scalar (Fin 2) c := by
    rintro ⟨c, rfl⟩
    apply hg
    rw [← projectiveMap_eq_one_iff hb, ← hM, ProjGenLinGroup.mk_scalar]
  have hfix : Nat.card {p : Omega F // g • p = p} =
      Nat.card {p : Omega F // coordinateGLAction F M p = p} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun p => by
      rw [smul_eq_coordinateGLAction hM.symm])
  rw [hfix, card_fixed_coordinateGLAction h2 M hnonscalar, sqrtCount_eq h2]
  split_ifs <;> simp

theorem card_fixed_of_mem_zpowers {g : CentralExtension F b m hm heven}
    (hg : g ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) :
    Nat.card {p : Omega F // g • p = p} = Nat.card F + 1 := by
  have h : ∀ p : Omega F, g • p = p := zpowers_cyclicGenerator_sq_smul F b m hm heven hg
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv h), card_omega]

omit [Fintype F] in
theorem card_fixed_eq_one_iff_single {g : CentralExtension F b m hm heven} (p₀ : Omega F)
    (h : ∀ p : Omega F, g • p = p ↔ p = p₀) : Nat.card {p : Omega F // g • p = p} = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun x y => Subtype.ext (((h _).mp x.2).trans ((h _).mp y.2).symm)⟩,
    ⟨⟨p₀, (h p₀).mpr rfl⟩⟩⟩

omit [Fintype F] in
theorem card_fixed_unipotent {α : CentralExtension F b m hm heven}
    (hα : α ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) {t : F} (ht : t ≠ 0) :
    Nat.card {p : Omega F // (α * unipotentElement F b m hm heven t) • p = p} = 1 := by
  apply card_fixed_eq_one_iff_single none
  intro p
  rw [mul_smul, zpowers_cyclicGenerator_sq_smul F b m hm heven hα]
  cases p with
  | none => simp [unipotentElement_smul_none]
  | some y =>
    simp only [reduceCtorEq, iff_false]
    exact unipotentElement_smul_some_ne F b m hm heven ht y

omit [Fintype F] in
theorem card_fixed_splitTorus (hb : ¬ IsSquare b) {g : CentralExtension F b m hm heven}
    (hg : g ∈ splitTorus F b m hm heven)
    (hgA : g ∉ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) :
    Nat.card {p : Omega F // g • p = p} = 2 := by
  obtain ⟨h1, h2⟩ := (mem_splitTorus_iff F b m hm heven g).mp hg
  have hset : ∀ p : Omega F, g • p = p ↔ p = none ∨ p = some 0 := by
    intro p
    constructor
    · intro hp
      cases p with
      | none => exact Or.inl rfl
      | some y =>
        by_cases hy : y = 0
        · exact Or.inr (by rw [hy])
        · exact absurd hp (splitTorus_smul_some_ne F b m hm heven hb hg hgA hy)
    · rintro (rfl | rfl)
      · exact h1
      · exact h2
  have e : {p : Omega F // g • p = p} ≃ Fin 2 :=
    { toFun := fun p => if p.1 = none then 0 else 1
      invFun := fun i => if i = 0 then ⟨none, h1⟩ else ⟨some 0, h2⟩
      left_inv := fun p => by
        rcases (hset p.1).mp p.2 with hp | hp
        · apply Subtype.ext
          simp [hp]
        · apply Subtype.ext
          simp [hp]
      right_inv := fun i => by
        fin_cases i <;> simp }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]

omit [Fintype F] in
theorem center_eq_zpowers (hb : ¬ IsSquare b) :
    Subgroup.center (CentralExtension F b m hm heven) =
      Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) := by
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_center_iff] at hg
    have hU1 := hg (unipotentElement F b m hm heven 1)
    have hw := hg (weylElement F b m hm heven)
    have hinf : g • (none : Omega F) = none := by
      have hfix : unipotentElement F b m hm heven 1 • (g • (none : Omega F)) =
          g • (none : Omega F) := by
        rw [← mul_smul, hU1, mul_smul, unipotentElement_smul_none]
      cases h : g • (none : Omega F) with
      | none => rfl
      | some y =>
        rw [h] at hfix
        exact absurd hfix (unipotentElement_smul_some_ne F b m hm heven one_ne_zero y)
    have hzero : g • (some 0 : Omega F) = some 0 := by
      rw [← weylElement_smul_none F b m hm heven, ← mul_smul, ← hw, mul_smul, hinf]
    have hT : g ∈ splitTorus F b m hm heven :=
      (mem_splitTorus_iff F b m hm heven g).mpr ⟨hinf, hzero⟩
    obtain ⟨α, -, hα⟩ := splitTorus_smul_some F b m hm heven hT
    have hα1 : α = 1 := by
      have h := congrArg (fun k : CentralExtension F b m hm heven => k • (some 0 : Omega F))
        (show g * unipotentElement F b m hm heven 1 * g⁻¹ =
          unipotentElement F b m hm heven 1 by rw [← hU1, mul_inv_cancel_right])
      simp only [mul_smul] at h
      rw [show g⁻¹ • (some 0 : Omega F) = some 0 by rw [inv_smul_eq_iff, hzero],
        unipotentElement_smul_some, zero_add, hα, mul_one] at h
      exact Option.some.inj h
    rw [← fixes_all_iff F b m hm heven hb]
    intro p
    cases p with
    | none => exact hinf
    | some y => rw [hα, hα1, one_mul]
  · rw [Subgroup.zpowers_le]
    exact cyclicGenerator_sq_mem_center F b m hm heven

end Model

end CFSG.Wreathed.CentralSL2

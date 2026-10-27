module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesOuterSym

public section

namespace CFSG.QuasithinUnique.Setup.SL2Modules

section Perm

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

@[expose] def permUHom : Equiv.Perm Ω →* (Module.End (ZMod 2) ↥(evenWeight Ω))ˣ where
  toFun := permU
  map_one' := permU_one
  map_mul' := permU_mul

theorem exists_common_fixed_point (h5 : Fintype.card Ω = 5) {a b : Ω} (hab : a ≠ b)
    (B : Subgroup (Equiv.Perm Ω)) (hB2 : ∀ σ ∈ B, σ * σ = 1) (hsw : Equiv.swap a b ∈ B) :
    ∃ ω, ω ≠ a ∧ ω ≠ b ∧ ∀ σ ∈ B, σ ω = ω := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 B := fun σ => ⟨1, by
    apply Subtype.ext
    have h := hB2 σ.1 σ.2
    simpa [pow_two] using h⟩
  have hmod := hp.card_modEq_card_fixedPoints Ω
  rw [Nat.card_eq_fintype_card, h5] at hmod
  by_contra hno
  push Not at hno
  have hcard0 : Nat.card (MulAction.fixedPoints B Ω) = 0 := by
    rw [Nat.card_eq_zero]
    left
    refine ⟨fun ⟨x, hx⟩ => ?_⟩
    have hfix := hx ⟨Equiv.swap a b, hsw⟩
    have hfix' : Equiv.swap a b x = x := hfix
    have hxa : x ≠ a := by
      intro h
      rw [h, Equiv.swap_apply_left] at hfix'
      exact hab hfix'.symm
    have hxb : x ≠ b := by
      intro h
      rw [h, Equiv.swap_apply_right] at hfix'
      exact hab hfix'
    obtain ⟨σ, hσ, hne⟩ := hno x hxa hxb
    exact hne (hx ⟨σ, hσ⟩)
  rw [hcard0] at hmod
  exact absurd hmod (by decide)

@[expose] def pairVec (x ω : Ω) : ↥(evenWeight Ω) := ⟨delta x + delta ω, delta_add_delta_mem x ω⟩

omit [Fintype Ω] in
theorem permAct_pairVec_aux (τ : Equiv.Perm Ω) (x ω : Ω) :
    permAct τ (delta x + delta ω) = delta (τ x) + delta (τ ω) := by
  rw [permAct_add, permAct_delta, permAct_delta]

theorem permU_pairVec (τ : Equiv.Perm Ω) (x ω : Ω) :
    (permU τ).val (pairVec x ω) = pairVec (τ x) (τ ω) :=
  Subtype.ext (permAct_pairVec_aux τ x ω)

omit [Fintype Ω] in
theorem perm_commute_swap {a b : Ω} (hab : a ≠ b) (τ : Equiv.Perm Ω)
    (h : τ * Equiv.swap a b = Equiv.swap a b * τ) :
    (τ a = a ∧ τ b = b) ∨ (τ a = b ∧ τ b = a) := by
  have h1 : τ b = Equiv.swap a b (τ a) := by
    have := congrArg (fun σ : Equiv.Perm Ω => σ a) h
    simpa using this
  by_cases ha : τ a = a
  · left
    refine ⟨ha, ?_⟩
    rw [h1, ha, Equiv.swap_apply_left]
  · by_cases hb : τ a = b
    · right
      refine ⟨hb, ?_⟩
      rw [h1, hb, Equiv.swap_apply_right]
    · exfalso
      rw [Equiv.swap_apply_of_ne_of_ne ha hb] at h1
      exact hab (τ.injective h1.symm)

theorem pairVec_apply (x ω i : Ω) :
    ((pairVec x ω : ↥(evenWeight Ω)) : Ω → ZMod 2) i =
      (if i = x then 1 else 0) + (if i = ω then 1 else 0) := by
  simp [pairVec, delta, Pi.single_apply]

theorem swap_add_one_apply {a b : Ω} (hab : a ≠ b) (x : ↥(evenWeight Ω)) :
    ((permU (Equiv.swap a b)).val + 1) x =
      ((x : Ω → ZMod 2) a + (x : Ω → ZMod 2) b) • pairVec a b := by
  apply Subtype.ext
  funext i
  have hperm : (((permU (Equiv.swap a b)).val x : ↥(evenWeight Ω)) : Ω → ZMod 2) i =
      (x : Ω → ZMod 2) (Equiv.swap a b i) := by
    show (x : Ω → ZMod 2) ((Equiv.swap a b).symm i) = _
    rw [Equiv.symm_swap]
  show (((permU (Equiv.swap a b)).val x : ↥(evenWeight Ω)) : Ω → ZMod 2) i + (x : Ω → ZMod 2) i = _
  rw [hperm, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, pairVec_apply]
  by_cases hia : i = a
  · subst hia
    rw [Equiv.swap_apply_left, ite_eq_left rfl, ite_eq_right hab]
    generalize (x : Ω → ZMod 2) i = p
    generalize (x : Ω → ZMod 2) b = q
    revert p q
    decide
  · by_cases hib : i = b
    · subst hib
      rw [Equiv.swap_apply_right, ite_eq_right hia, ite_eq_left rfl]
      generalize (x : Ω → ZMod 2) a = p
      generalize (x : Ω → ZMod 2) i = q
      revert p q
      decide
    · rw [Equiv.swap_apply_of_ne_of_ne hia hib, ite_eq_right hia, ite_eq_right hib, add_zero,
        mul_zero]
      generalize (x : Ω → ZMod 2) i = p
      revert p
      decide

theorem finrank_span_pairVec {a b : Ω} (hab : a ≠ b) :
    Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) {pairVec a b}) = 1 := by
  let _ : AddCommGroup (ZMod 2) := zmod2AddCommGroup
  apply finrank_span_singleton
  intro h
  have h1 := congrArg (fun v : ↥(evenWeight Ω) => (v : Ω → ZMod 2) a) h
  simp [pairVec_apply, hab] at h1

theorem swap_add_one_pairVec {a b ω : Ω} (hab : a ≠ b) (hωa : ω ≠ a) (hωb : ω ≠ b) :
    ((permU (Equiv.swap a b)).val + 1) (pairVec a ω) = pairVec a b ∧
      ((permU (Equiv.swap a b)).val + 1) (pairVec b ω) = pairVec a b := by
  constructor
  · rw [swap_add_one_apply hab]
    simp [pairVec_apply, hab.symm, hωa.symm, hωb.symm]
  · rw [swap_add_one_apply hab]
    simp [pairVec_apply, hab, hωa.symm, hωb.symm]

theorem deleted_five_transposition_plane (h5 : Fintype.card Ω = 5) {a b : Ω} (hab : a ≠ b)
    (E : Subgroup (Module.End (ZMod 2) ↥(evenWeight Ω))ˣ) [CFSG.IsElementaryAbelian 2 E]
    (hEN : ∀ e ∈ E, ∀ σ ∈ alternatingGroup Ω,
      ∃ σ' ∈ alternatingGroup Ω, e * permU σ * e⁻¹ = permU σ')
    (ht : permU (Equiv.swap a b) ∈ E) :
    (∃ ω : Ω, ω ≠ a ∧ ω ≠ b ∧ ∀ e ∈ E, ∀ τ : Equiv.Perm Ω, e = permU τ → τ ω = ω) ∧
    ∀ ω : Ω, ω ≠ a → ω ≠ b → (∀ e ∈ E, ∀ τ : Equiv.Perm Ω, e = permU τ → τ ω = ω) →
      (∀ e ∈ E, ∀ w ∈ Submodule.span (ZMod 2) {pairVec a ω, pairVec b ω},
        e.val w ∈ Submodule.span (ZMod 2) {pairVec a ω, pairVec b ω}) ∧
      (∀ e ∈ E,
        (∀ w ∈ Submodule.span (ZMod 2) {pairVec a ω, pairVec b ω}, e.val w = w) ∨
        (∀ w ∈ Submodule.span (ZMod 2) {pairVec a ω, pairVec b ω},
          e.val w = (permU (Equiv.swap a b)).val w)) ∧
      (∃ w ∈ Submodule.span (ZMod 2) {pairVec a ω, pairVec b ω},
        (permU (Equiv.swap a b)).val w ≠ w) ∧
      Module.finrank (ZMod 2) ↥(Submodule.map ((permU (Equiv.swap a b)).val + 1)
        (Submodule.span (ZMod 2) {pairVec a ω, pairVec b ω})) = 1 ∧
      Module.finrank (ZMod 2) ↥(LinearMap.range ((permU (Equiv.swap a b)).val + 1)) = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let B : Subgroup (Equiv.Perm Ω) := E.comap permUHom
  have hBmem : ∀ σ, σ ∈ B ↔ permU σ ∈ E := fun σ => Iff.rfl
  have hB2 : ∀ σ ∈ B, σ * σ = 1 := by
    intro σ hσ
    have h1 : (permU σ) ^ 2 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (permU σ) hσ
    apply permU_injective h5
    rw [permU_mul, permU_one, ← pow_two]
    exact h1
  have hsw : Equiv.swap a b ∈ B := ht
  have hcomm : ∀ e ∈ E, ∀ τ : Equiv.Perm Ω, e = permU τ →
      τ * Equiv.swap a b = Equiv.swap a b * τ := by
    intro e he τ hτ
    have h1 : e * permU (Equiv.swap a b) = permU (Equiv.swap a b) * e := by
      have := (inferInstance : IsMulCommutative ↥E).is_comm.comm ⟨e, he⟩ ⟨_, ht⟩
      exact congrArg Subtype.val this
    rw [hτ, ← permU_mul, ← permU_mul] at h1
    exact permU_injective h5 h1
  refine ⟨?_, ?_⟩
  · obtain ⟨ω, hωa, hωb, hωfix⟩ := exists_common_fixed_point h5 hab B hB2 hsw
    refine ⟨ω, hωa, hωb, fun e he τ hτ => hωfix τ ?_⟩
    rw [hBmem, ← hτ]
    exact he
  · intro ω hωa hωb hfix
    set Wp := Submodule.span (ZMod 2) {pairVec a ω, pairVec b ω} with hWp
    have hga : pairVec a ω ∈ Wp := Submodule.subset_span (by simp)
    have hgb : pairVec b ω ∈ Wp := Submodule.subset_span (by simp)
    have hgen : ∀ e ∈ E, ∃ τ, e = permU τ := fun e he => by
      obtain ⟨τ, hτ, -⟩ := deleted_five_normalizer h5 e (hEN e he)
      exact ⟨τ, hτ⟩
    have hact : ∀ e ∈ E, ∀ τ : Equiv.Perm Ω, e = permU τ →
        ((τ a = a ∧ τ b = b) ∨ (τ a = b ∧ τ b = a)) ∧
        e.val (pairVec a ω) = pairVec (τ a) ω ∧ e.val (pairVec b ω) = pairVec (τ b) ω := by
      intro e he τ hτ
      refine ⟨perm_commute_swap hab τ (hcomm e he τ hτ), ?_, ?_⟩
      · rw [hτ, permU_pairVec, hfix e he τ hτ]
      · rw [hτ, permU_pairVec, hfix e he τ hτ]
    have hinv : ∀ e ∈ E, ∀ w ∈ Wp, e.val w ∈ Wp := by
      intro e he w hw
      obtain ⟨τ, hτ⟩ := hgen e he
      obtain ⟨hc, ha, hb⟩ := hact e he τ hτ
      have hle : Wp ≤ Wp.comap e.val := by
        rw [hWp, Submodule.span_le]
        intro v hv
        rcases hv with rfl | rfl
        · show e.val (pairVec a ω) ∈ Wp
          rw [ha]
          rcases hc with ⟨h1, -⟩ | ⟨h1, -⟩
          · rw [h1]; exact hga
          · rw [h1]; exact hgb
        · show e.val (pairVec b ω) ∈ Wp
          rw [hb]
          rcases hc with ⟨-, h1⟩ | ⟨-, h1⟩
          · rw [h1]; exact hgb
          · rw [h1]; exact hga
      exact hle hw
    have htω : Equiv.swap a b ω = ω := Equiv.swap_apply_of_ne_of_ne hωa hωb
    have hta : (permU (Equiv.swap a b)).val (pairVec a ω) = pairVec b ω := by
      rw [permU_pairVec, htω, Equiv.swap_apply_left]
    have htb : (permU (Equiv.swap a b)).val (pairVec b ω) = pairVec a ω := by
      rw [permU_pairVec, htω, Equiv.swap_apply_right]
    have hact2 : ∀ e ∈ E, (∀ w ∈ Wp, e.val w = w) ∨
        (∀ w ∈ Wp, e.val w = (permU (Equiv.swap a b)).val w) := by
      intro e he
      obtain ⟨τ, hτ⟩ := hgen e he
      obtain ⟨hc, ha, hb⟩ := hact e he τ hτ
      rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        have heq : Set.EqOn e.val (1 : Module.End (ZMod 2) ↥(evenWeight Ω))
            {pairVec a ω, pairVec b ω} := by
          intro v hv
          rcases hv with rfl | rfl
          · rw [ha, h1]; rfl
          · rw [hb, h2]; rfl
        intro w hw
        exact LinearMap.eqOn_span' heq hw
      · right
        have heq : Set.EqOn e.val (permU (Equiv.swap a b)).val {pairVec a ω, pairVec b ω} := by
          intro v hv
          rcases hv with rfl | rfl
          · rw [ha, h1, hta]
          · rw [hb, h2, htb]
        intro w hw
        exact LinearMap.eqOn_span' heq hw
    have hnt : ∃ w ∈ Wp, (permU (Equiv.swap a b)).val w ≠ w := by
      refine ⟨pairVec a ω, hga, ?_⟩
      rw [hta]
      intro h
      have h1 := congrArg (fun v : ↥(evenWeight Ω) => (v : Ω → ZMod 2) a) h
      simp [pairVec_apply, hab, hωa.symm] at h1
    have hmap : Submodule.map ((permU (Equiv.swap a b)).val + 1) Wp =
        Submodule.span (ZMod 2) {pairVec a b} := by
      rw [hWp, Submodule.map_span, Set.image_pair, (swap_add_one_pairVec hab hωa hωb).1,
        (swap_add_one_pairVec hab hωa hωb).2, Set.pair_eq_singleton]
    have hrange : LinearMap.range ((permU (Equiv.swap a b)).val + 1) =
        Submodule.span (ZMod 2) {pairVec a b} := by
      apply le_antisymm
      · rintro _ ⟨x, rfl⟩
        rw [swap_add_one_apply hab]
        exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact ⟨pairVec a ω, (swap_add_one_pairVec hab hωa hωb).1⟩
    refine ⟨hinv, hact2, hnt, ?_, ?_⟩
    · rw [hmap]
      exact finrank_span_pairVec hab
    · rw [hrange]
      exact finrank_span_pairVec hab

end Perm

end CFSG.QuasithinUnique.Setup.SL2Modules

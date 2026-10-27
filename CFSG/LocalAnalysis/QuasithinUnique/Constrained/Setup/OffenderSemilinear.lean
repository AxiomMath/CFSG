module

public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderChar
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderModule

public section

namespace CFSG.QuasithinUnique.Setup.Offender

open Module TensorProduct

universe u v

section Semilinear

variable {F : Type*} [Field F] {W : Type*} [AddCommGroup W] [Module F W]

@[expose] def IsSemilinearWith (a : Equiv.Perm W) (σ : F ≃+* F) : Prop :=
  ∀ (c : F) (w : W), a (c • w) = σ c • a w

theorem IsSemilinearWith.map_zero {a : Equiv.Perm W} {σ : F ≃+* F} (h : IsSemilinearWith a σ) :
    a 0 = 0 := by
  have := h 0 0
  simpa using this

theorem IsSemilinearWith.unique [Nontrivial W] {a : Equiv.Perm W} {σ σ' : F ≃+* F}
    (h : IsSemilinearWith a σ) (h' : IsSemilinearWith a σ') : σ = σ' := by
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  have haw : a w ≠ 0 := fun h0 => hw (a.injective (by rw [h0, h.map_zero]))
  refine RingEquiv.ext fun c => ?_
  have := (h c w).symm.trans (h' c w)
  exact smul_left_injective F haw this

theorem IsSemilinearWith.one_perm : IsSemilinearWith (1 : Equiv.Perm W) (1 : F ≃+* F) :=
  fun _ _ => rfl

theorem IsSemilinearWith.mul {a b : Equiv.Perm W} {σ τ : F ≃+* F}
    (ha : IsSemilinearWith a σ) (hb : IsSemilinearWith b τ) :
    IsSemilinearWith (a * b) (σ * τ) := by
  intro c w
  show a (b (c • w)) = σ (τ c) • a (b w)
  rw [hb, ha]

theorem sq_eq_one_of_semilinear [Nontrivial W] {b : Equiv.Perm W} (hb2 : b * b = 1)
    {σ : F ≃+* F} (hσ : IsSemilinearWith b σ) : σ * σ = 1 := by
  have h := hσ.mul hσ
  rw [hb2] at h
  exact h.unique IsSemilinearWith.one_perm

end Semilinear

section FiniteField

variable {F : Type*} [Field F]

theorem neg_eq_self_of_char_two (x : F) [CharP F 2] : -x = x := by
  have h : (2 : F) = 0 := CharP.cast_eq_zero F 2
  calc -x = -x + (2 : F) * x := by rw [h, zero_mul, add_zero]
    _ = x := by ring

theorem add_self_eq_zero_of_char_two (x : F) [CharP F 2] : x + x = 0 := by
  rw [← two_mul, show (2 : F) = 0 from CharP.cast_eq_zero F 2, zero_mul]

theorem mem_fixedSubfield_zpowers_iff (σ : F ≃+* F) (x : F) :
    x ∈ FixedPoints.subfield (Subgroup.zpowers σ) F ↔ σ x = x := by
  constructor
  · intro hx
    exact hx ⟨σ, Subgroup.mem_zpowers σ⟩
  · intro hx g
    have hσmem : σ ∈ MulAction.stabilizer (F ≃+* F) x := by
      rw [MulAction.mem_stabilizer_iff]; exact hx
    have := Subgroup.zpowers_le.2 hσmem g.2
    exact (MulAction.mem_stabilizer_iff.1 this)

theorem card_eq_sq_of_involution [Finite F] (σ : F ≃+* F) (hσ1 : σ ≠ 1) (hσ2 : σ * σ = 1) :
    ∃ n : ℕ, Nat.card F = n ^ 2 ∧ 2 ≤ n ∧ Nat.card {c : F // σ c = c} = n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hσ2) hσ1
  have hcard := CFSG.GorensteinWalter.nat_card_eq_fixedSubfield_card_pow_orderOf F σ
  rw [hord] at hcard
  refine ⟨Nat.card (FixedPoints.subfield (Subgroup.zpowers σ) F), hcard, Finite.one_lt_card, ?_⟩
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => (mem_fixedSubfield_zpowers_iff σ x).symm)

theorem exists_trace_eq_one [Finite F] [CharP F 2] (σ : F ≃+* F) (hσ1 : σ ≠ 1)
    (hσ2 : σ * σ = 1) : ∃ x : F, σ x + x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hσ2) hσ1
  have hcard := CFSG.GorensteinWalter.nat_card_eq_fixedSubfield_card_pow_orderOf F σ
  rw [hord] at hcard
  set F0 := FixedPoints.subfield (Subgroup.zpowers σ) F with hF0
  let T : F →+ F := (σ : F →+ F) + AddMonoidHom.id F
  have hT : ∀ x, T x = σ x + x := fun x => rfl
  have hker : ∀ x, x ∈ T.ker ↔ x ∈ F0 := by
    intro x
    rw [AddMonoidHom.mem_ker, hT, hF0, mem_fixedSubfield_zpowers_iff]
    constructor
    · intro h
      have := eq_neg_of_add_eq_zero_left h
      rw [this, neg_eq_self_of_char_two]
    · intro h
      rw [h]; exact add_self_eq_zero_of_char_two x
  have hrange : ∀ y ∈ T.range, y ∈ F0 := by
    rintro _ ⟨x, rfl⟩
    rw [hF0, mem_fixedSubfield_zpowers_iff, hT]
    have : σ (σ x) = x := by
      have := congrArg (fun τ : F ≃+* F => τ x) hσ2
      simpa using this
    rw [map_add, this, add_comm]
  have hkerc : Nat.card T.ker = Nat.card F0 :=
    Nat.card_congr (Equiv.subtypeEquivRight hker)
  have hkr := AddSubgroup.card_ker_mul_card_range T
  have hpos : 0 < Nat.card F0 := Nat.card_pos
  have hrc : Nat.card T.range = Nat.card F0 := by
    rw [hkerc, hcard] at hkr
    have : Nat.card F0 * Nat.card T.range = Nat.card F0 * Nat.card F0 := by rw [hkr]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have hle : T.range ≤ F0.toAddSubgroup := fun y hy => hrange y hy
  have heq : T.range = F0.toAddSubgroup :=
    AddSubgroup.eq_of_le_of_card_ge hle (by rw [hrc]; exact le_rfl)
  have h1 : (1 : F) ∈ T.range := by
    rw [heq]; exact F0.one_mem
  obtain ⟨x, hx⟩ := h1
  exact ⟨x, hx⟩

theorem aut_involution_unique [Finite F] [CharP F 2] (τ₁ τ₂ : F ≃+* F)
    (h₁ : τ₁ * τ₁ = 1) (h₂ : τ₂ * τ₂ = 1) (n₁ : τ₁ ≠ 1) (n₂ : τ₂ ≠ 1) : τ₁ = τ₂ := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F 2
  have hF : Nat.card F = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  obtain ⟨φ, -, -, hzp, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      hp n.pos hF
  have hcyc : IsCyclic (F ≃+* F) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨φ, hzp⟩
  have : Finite (F ≃+* F) := Finite.of_injective (fun e : F ≃+* F => (e : F → F))
    (fun _ _ h => RingEquiv.ext (congrFun h))
  have : Fintype (F ≃+* F) := Fintype.ofFinite _
  have hle := IsCyclic.card_pow_eq_one_le (α := F ≃+* F) (n := 2) (by norm_num)
  by_contra hne
  have hsub : ({1, τ₁, τ₂} : Finset (F ≃+* F)) ⊆
      Finset.univ.filter (fun a : F ≃+* F => a ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · simp
    · rw [pow_two]; exact h₁
    · rw [pow_two]; exact h₂
  have hcard : ({1, τ₁, τ₂} : Finset (F ≃+* F)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hne
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨n₁.symm, n₂.symm⟩
  have := Finset.card_le_card hsub
  omega

end FiniteField

section Involution

variable {F : Type*} [Field F] {W : Type*} [AddCommGroup W] [Module F W] [CharP F 2]

theorem semilinear_involution_fixed_image
    {a : Equiv.Perm W} {σ : F ≃+* F} (hsem : IsSemilinearWith a σ)
    (htr : ∃ x : F, σ x + x = 1) (w : W) (hw : a w = w) : ∃ x : W, a x - x = w := by
  obtain ⟨l, hl⟩ := htr
  refine ⟨l • w, ?_⟩
  rw [hsem, hw, sub_eq_add_neg, ← neg_smul, neg_eq_self_of_char_two, ← add_smul, hl, one_smul]

theorem eq_one_of_fixes_image {a b : Equiv.Perm W} {σ : F ≃+* F} (hsem : IsSemilinearWith a σ)
    (hb : IsSemilinearWith b (1 : F ≃+* F))
    (hadd_a : ∀ x y, a (x + y) = a x + a y) (hadd_b : ∀ x y, b (x + y) = b x + b y)
    (ha2 : ∀ w, a (a w) = w) (hσ1 : σ ≠ 1) (hσ2 : σ * σ = 1) (htr : ∃ x, σ x + x = 1)
    (hfix : ∀ x, b (a x - x) = a x - x) : b = 1 := by
  obtain ⟨c, hc⟩ : ∃ c : F, σ c ≠ c := by
    by_contra h
    exact hσ1 (RingEquiv.ext (fun x => by_contra fun hx => h ⟨x, hx⟩))
  have hσσ : ∀ x : F, σ (σ x) = x := fun x => by
    have := congrArg (fun τ : F ≃+* F => τ x) hσ2
    simpa using this
  have hbs : ∀ (r : F) (x : W), b (r • x) = r • b x := fun r x => hb r x
  have hne : σ c + c ≠ 0 := by
    intro h
    apply hc
    have := eq_neg_of_add_eq_zero_left h
    rw [this, neg_eq_self_of_char_two]
  have hfixb : ∀ x, a x = x → b x = x := by
    intro x hx
    obtain ⟨y, hy⟩ := semilinear_involution_fixed_image hsem htr x hx
    rw [← hy]; exact hfix y
  refine Equiv.ext fun v => ?_
  show b v = v
  set w := v + a v with hw
  set u := σ c • v + c • a v with hu
  have haw : a w = w := by
    rw [hw, hadd_a, ha2, add_comm]
  have hau : a u = u := by
    rw [hu, hadd_a, hsem, hsem, ha2, hσσ, add_comm]
  have hbw : b w = w := hfixb w haw
  have hbu : b u = u := hfixb u hau
  have key : (σ c + c) • v = u + c • w := by
    rw [hu, hw, smul_add, add_smul]
    have h2 := char_two_add_self F (c • a v)
    calc σ c • v + c • v = σ c • v + c • v + (c • a v + c • a v) := by rw [h2, add_zero]
      _ = σ c • v + c • a v + (c • v + c • a v) := by abel
  have hv : v = (σ c + c)⁻¹ • (u + c • w) := by
    rw [← key, inv_smul_smul₀ hne]
  conv_lhs => rw [hv]
  rw [hbs, hadd_b, hbs, hbu, hbw]
  exact hv.symm

theorem card_eq_sq_fixed (a : Equiv.Perm W) (hadd : ∀ x y : W, a (x + y) = a x + a y)
    (ha2 : ∀ w, a (a w) = w) (hneg : ∀ w : W, -w = w)
    (himg : ∀ w, a w = w → ∃ x, a x - x = w) :
    Nat.card W = Nat.card {w : W // a w = w} ^ 2 := by
  let a' : W →+ W := AddMonoidHom.mk' (⇑a) hadd
  let D : W →+ W := AddMonoidHom.mk' (fun w => a w - w) (fun x y => by
    rw [hadd]; abel)
  have hker : ∀ w, w ∈ D.ker ↔ a w = w := fun w => by
    rw [AddMonoidHom.mem_ker]
    show a w - w = 0 ↔ _
    exact sub_eq_zero
  have hrange : ∀ w, w ∈ D.range ↔ a w = w := by
    intro w
    constructor
    · rintro ⟨x, rfl⟩
      show a (a x - x) = a x - x
      have h1 : a (a x - x) = a (a x) - a x := map_sub a' (a x) x
      rw [h1, ha2, ← neg_sub (a x) x, hneg]
    · intro hw
      obtain ⟨x, hx⟩ := himg w hw
      exact ⟨x, hx⟩
  have h1 : Nat.card D.ker = Nat.card {w : W // a w = w} :=
    Nat.card_congr (Equiv.subtypeEquivRight hker)
  have h2 : Nat.card D.range = Nat.card {w : W // a w = w} :=
    Nat.card_congr (Equiv.subtypeEquivRight hrange)
  have := AddSubgroup.card_ker_mul_card_range D
  rw [h1, h2] at this
  rw [← this, pow_two]

theorem sub_of_inj [Finite F] [Nontrivial W] (B : Subgroup (Equiv.Perm W))
    (hsq : ∀ b ∈ B, b * b = 1) (hsemi : ∀ b ∈ B, ∃ σ : F ≃+* F, IsSemilinearWith b σ)
    (hinj : ∀ b ∈ B, IsSemilinearWith b (1 : F ≃+* F) → b = 1)
    {a₀ : Equiv.Perm W} (ha₀ : a₀ ∈ B) {σ₀ : F ≃+* F} (hσ₀ : IsSemilinearWith a₀ σ₀)
    (hσ₀1 : σ₀ ≠ 1) : ∀ b ∈ B, b = 1 ∨ b = a₀ := by
  have hσ₀2 : σ₀ * σ₀ = 1 := sq_eq_one_of_semilinear (hsq a₀ ha₀) hσ₀
  intro b hb
  obtain ⟨σ, hσ⟩ := hsemi b hb
  have hσ2 := sq_eq_one_of_semilinear (hsq b hb) hσ
  by_cases hσ1 : σ = 1
  · left
    subst hσ1
    exact hinj b hb hσ
  · right
    have hσσ : σ = σ₀ := aut_involution_unique σ σ₀ hσ2 hσ₀2 hσ1 hσ₀1
    subst hσσ
    have hba : IsSemilinearWith (b * a₀) (1 : F ≃+* F) := by
      have := hσ.mul hσ₀
      rwa [hσ₀2] at this
    have hba1 : b * a₀ = 1 := hinj (b * a₀) (B.mul_mem hb ha₀) hba
    have : b = a₀⁻¹ := mul_eq_one_iff_eq_inv.1 hba1
    rw [this]
    exact inv_eq_of_mul_eq_one_right (hsq a₀ ha₀)

theorem involution_offender_card [Finite F] [Finite W] [Nontrivial W] {a₀ : Equiv.Perm W}
    (hadd : ∀ x y : W, a₀ (x + y) = a₀ x + a₀ y) (ha₂ : ∀ w, a₀ (a₀ w) = w)
    {σ₀ : F ≃+* F} (hσ₀ : IsSemilinearWith a₀ σ₀) (hσ₀1 : σ₀ ≠ 1) (hσ₀2 : σ₀ * σ₀ = 1)
    (hoff : Nat.card W ≤ 2 * Nat.card {w : W // a₀ w = w}) :
    Nat.card F = 4 ∧ Nat.card W = 4 ∧ Nat.card {w : W // a₀ w = w} = 2 := by
  have htr : ∃ x : F, σ₀ x + x = 1 := exists_trace_eq_one σ₀ hσ₀1 hσ₀2
  have hneg : ∀ w : W, -w = w := fun w => neg_eq_self_of_char_two_module F w
  have himg : ∀ w, a₀ w = w → ∃ x, a₀ x - x = w := fun w hw =>
    semilinear_involution_fixed_image hσ₀ htr w hw
  have hsq := card_eq_sq_fixed a₀ hadd ha₂ hneg himg
  have hnz : Nonempty {w : W // a₀ w = w} := ⟨⟨0, hσ₀.map_zero⟩⟩
  set c := Nat.card {w : W // a₀ w = w} with hc
  have hcpos : 0 < c := Nat.card_pos
  have hc2 : c ≤ 2 := by nlinarith [hsq, hoff]
  have hW4 : Nat.card W ≤ 4 := by rw [hsq]; nlinarith
  obtain ⟨n, hFn, hn2, -⟩ := card_eq_sq_of_involution σ₀ hσ₀1 hσ₀2
  have hF4 : 4 ≤ Nat.card F := by rw [hFn]; nlinarith
  have hFW : Nat.card F ≤ Nat.card W := by
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    exact Nat.card_le_card_of_injective (fun c : F => c • w) (smul_left_injective F hw)
  have hF : Nat.card F = 4 := by omega
  have hW : Nat.card W = 4 := by omega
  refine ⟨hF, hW, ?_⟩
  rw [hW] at hsq
  nlinarith

end Involution

section Collapse

variable {F : Type*} [Field F] [Finite F] [CharP F 2] {W : Type*} [AddCommGroup W] [Module F W]
  [Finite W] [Nontrivial W]

theorem quadratic_semilinear_offender_field_collapse
    (A : Subgroup (Equiv.Perm W)) (hadd : ∀ a ∈ A, ∀ x y : W, a (x + y) = a x + a y)
    [CFSG.IsElementaryAbelian 2 A]
    (hsemi : ∀ a ∈ A, ∃ σ : F ≃+* F, IsSemilinearWith a σ)
    (hquad : ∀ a ∈ A, ∀ b ∈ A, ∀ w, b (a w - w) = a w - w)
    (hoff : Nat.card W ≤ Nat.card A * Nat.card {w : W // ∀ a ∈ A, a w = w})
    (hnt : ∃ a ∈ A, ∃ σ : F ≃+* F, IsSemilinearWith a σ ∧ σ ≠ 1) :
    Nat.card A = 2 ∧ Nat.card F = 4 ∧ Module.finrank F W = 1 ∧ Nat.card W = 4 := by
  obtain ⟨a₀, ha₀, σ₀, hσ₀, hσ₀1⟩ := hnt
  have hA2 : ∀ a ∈ A, a * a = 1 := fun a ha => by
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) a ha
    rwa [pow_two] at this
  have ha₀2 : ∀ w, a₀ (a₀ w) = w := fun w => by
    have := congrArg (fun e : Equiv.Perm W => e w) (hA2 a₀ ha₀)
    simpa using this
  have hσ₀2 : σ₀ * σ₀ = 1 := sq_eq_one_of_semilinear (hA2 a₀ ha₀) hσ₀
  have htr : ∃ x : F, σ₀ x + x = 1 := exists_trace_eq_one σ₀ hσ₀1 hσ₀2
  have hadd0 := hadd a₀ ha₀
  have hinj : ∀ b ∈ A, IsSemilinearWith b (1 : F ≃+* F) → b = 1 := fun b hb hb1 =>
    eq_one_of_fixes_image hσ₀ hb1 hadd0 (hadd b hb) ha₀2 hσ₀1 hσ₀2 htr
      (fun x => hquad a₀ ha₀ b hb x)
  have hsub := sub_of_inj A hA2 hsemi hinj ha₀ hσ₀ hσ₀1
  have ha₀1 : a₀ ≠ 1 := by
    intro h
    rw [h] at hσ₀
    exact hσ₀1 (hσ₀.unique IsSemilinearWith.one_perm)
  have hcardA : Nat.card A = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨⟨1, A.one_mem⟩, ⟨a₀, ha₀⟩, ?_, ?_⟩
    · intro h; exact ha₀1 (congrArg Subtype.val h).symm
    · ext ⟨b, hb⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      rcases hsub b hb with rfl | rfl
      · left; rfl
      · right; rfl
  have hfixA : Nat.card {w : W // ∀ a ∈ A, a w = w} = Nat.card {w : W // a₀ w = w} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
    constructor
    · intro h; exact h a₀ ha₀
    · intro h a ha
      rcases hsub a ha with rfl | rfl
      · rfl
      · exact h
  rw [hcardA, hfixA] at hoff
  obtain ⟨hF4, hW4, -⟩ := involution_offender_card hadd0 ha₀2 hσ₀ hσ₀1 hσ₀2 hoff
  have hFinW : Module.Finite F W := Module.Finite.of_finite
  have hWF : Nat.card W = Nat.card F ^ Module.finrank F W := Module.natCard_eq_pow_finrank
  have hd : 0 < Module.finrank F W := Module.finrank_pos
  have hd1 : Module.finrank F W = 1 := by
    rw [hF4, hW4] at hWF
    by_contra h
    have h2 : 2 ≤ Module.finrank F W := by omega
    have h3 : 4 ^ 2 ≤ 4 ^ Module.finrank F W := Nat.pow_le_pow_right (by omega) h2
    omega
  exact ⟨hcardA, hF4, hd1, hW4⟩

omit [Finite F] [CharP F 2] in
theorem linearEquiv_comm_of_finrank_one (hd : Module.finrank F W = 1) (f g : W ≃ₗ[F] W) :
    f * g = g * f := by
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.1 hd
  obtain ⟨a, ha⟩ := hv (f v)
  obtain ⟨b, hb⟩ := hv (g v)
  have hfv : f v = a • v := ha.symm
  have hgv : g v = b • v := hb.symm
  ext w
  obtain ⟨c, rfl⟩ := hv w
  show f (g (c • v)) = g (f (c • v))
  simp only [map_smul, hfv, hgv, smul_smul]
  rw [mul_right_comm c b a]

theorem no_field_action_of_perfect
    (A : Subgroup (Equiv.Perm W)) (hadd : ∀ a ∈ A, ∀ x y : W, a (x + y) = a x + a y)
    [CFSG.IsElementaryAbelian 2 A]
    (hsemi : ∀ a ∈ A, ∃ σ : F ≃+* F, IsSemilinearWith a σ)
    (hquad : ∀ a ∈ A, ∀ b ∈ A, ∀ w, b (a w - w) = a w - w)
    (hoff : Nat.card W ≤ Nat.card A * Nat.card {w : W // ∀ a ∈ A, a w = w})
    (H : Subgroup (W ≃ₗ[F] W)) (hHne : H ≠ ⊥) (hHperf : Group.IsPerfect H) :
    ∀ a ∈ A, (∀ σ : F ≃+* F, IsSemilinearWith a σ → σ = 1) ∧
      IsSemilinearWith a (1 : F ≃+* F) := by
  have key : ∀ a ∈ A, ∀ σ : F ≃+* F, IsSemilinearWith a σ → σ = 1 := by
    intro a ha σ hσ
    by_contra hσ1
    obtain ⟨-, -, hd1, -⟩ := quadratic_semilinear_offender_field_collapse A hadd hsemi hquad hoff
      ⟨a, ha, σ, hσ, hσ1⟩
    have hcomm : ∀ x y : H, x * y = y * x := fun x y =>
      Subtype.ext (linearEquiv_comm_of_finrank_one hd1 x y)
    have h1 : commutator H ≤ ⊥ := by
      rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      exact Subgroup.mem_bot.2 (commutatorElement_eq_one_iff_mul_comm.2 (hcomm x y))
    have h2 : commutator H = ⊤ := hHperf.commutator_eq_top
    apply hHne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx' : (⟨x, hx⟩ : H) ∈ commutator H := by rw [h2]; exact Subgroup.mem_top _
    have := Subgroup.mem_bot.1 (h1 hx')
    exact congrArg Subtype.val this
  intro a ha
  refine ⟨key a ha, ?_⟩
  obtain ⟨σ, hσ⟩ := hsemi a ha
  have := key a ha σ hσ
  rwa [this] at hσ

end Collapse

section ThreeActor

variable {k : Type*} [Field k] {W : Type u} [AddCommGroup W] [Module k W]

@[expose] def glToPerm : (W ≃ₗ[k] W) →* Equiv.Perm W where
  toFun g := g.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

theorem glToPerm_apply (g : W ≃ₗ[k] W) (w : W) : glToPerm g w = g w := rfl

theorem glToPerm_injective : Function.Injective (glToPerm (k := k) (W := W)) :=
  fun _ _ h => LinearEquiv.ext fun w => congrArg (fun e : Equiv.Perm W => e w) h

theorem natCard_linearEquiv_two [Finite k] (hk : Nat.card k = 2)
    (hd : Module.finrank k W = 2) : Nat.card (W ≃ₗ[k] W) = 6 := by
  have : Fintype k := Fintype.ofFinite k
  have hq : Fintype.card k = 2 := by rw [← Nat.card_eq_fintype_card]; exact hk
  have hfd : Module.Finite k W := Module.finite_of_finrank_pos (by omega)
  let b := Module.finBasisOfFinrankEq k W hd
  have h1 : Nat.card (W ≃ₗ[k] W) = Nat.card (Matrix.GeneralLinearGroup (Fin 2) k) :=
    (Nat.card_congr ((Matrix.GeneralLinearGroup.toLin' b).toEquiv.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv k W).toEquiv)).symm
  rw [h1, Matrix.card_GL_field, hq]
  simp [Fin.prod_univ_two]

theorem irreducible_odd_abelian_offender_forces_binary_natural_three_actor
    [CharP k 2] [Nontrivial W] [Finite W]
    (H : Subgroup (W ≃ₗ[k] W)) (hirr : IsIrrAct H) (hHne : H ≠ ⊥)
    (hHab : ∀ x y : H, x * y = y * x) (hHodd : Odd (Nat.card H))
    (B : Subgroup (W ≃ₗ[k] W)) (hBN : B ≤ Subgroup.normalizer (H : Set (W ≃ₗ[k] W)))
    (hBne : B ≠ ⊥) [CFSG.IsElementaryAbelian 2 B]
    (hoff : Nat.card W ≤ Nat.card B * Nat.card (fixGL B)) :
    Nat.card k = 2 ∧ Module.finrank k W = 2 ∧ Nat.card H = 3 ∧ Nat.card B = 2 ∧
      H ⊔ B = ⊤ ∧ Nat.card B * Nat.card (fixGL B) = Nat.card W := by
  classical
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : W)
  have : Finite k := Finite.of_injective (fun c : k => c • w₀) (smul_left_injective k hw₀)
  have : Finite (W ≃ₗ[k] W) :=
    Finite.of_injective (fun f : W ≃ₗ[k] W => (f : W → W)) DFunLike.coe_injective
  obtain ⟨F, _, _, _, _, _, hcomm, -, -, hnorm⟩ :=
    finite_irreducible_endomorphism_field_core H hirr
  have : CharP F 2 := charP_of_injective_algebraMap (algebraMap k F).injective 2
  have hscal : ∀ h ∈ H, ∃ c : F, ∀ w, h w = c • w := by
    intro h hh
    refine (hcomm (h : Module.End k W)).1 (fun h' hh' w => ?_)
    have := congrArg (fun x : H => (x : W ≃ₗ[k] W) w) (hHab ⟨h, hh⟩ ⟨h', hh'⟩)
    exact this
  have hfin1 : Module.finrank F W = 1 := by
    have hU : ∀ h ∈ H, ∀ u ∈ (Submodule.span F {w₀}).restrictScalars k,
        h u ∈ (Submodule.span F {w₀}).restrictScalars k := by
      intro h hh u hu
      rw [Submodule.restrictScalars_mem] at hu ⊢
      obtain ⟨c, hc⟩ := hscal h hh
      rw [hc u]
      exact Submodule.smul_mem _ c hu
    have hline : ∀ w : W, w ∈ Submodule.span F {w₀} := by
      rcases hirr _ hU with h | h
      · exfalso
        have hmem : w₀ ∈ (Submodule.span F {w₀}).restrictScalars k := by
          rw [Submodule.restrictScalars_mem]; exact Submodule.mem_span_singleton_self w₀
        rw [h] at hmem
        exact hw₀ ((Submodule.mem_bot k).1 hmem)
      · intro w
        have hmem : w ∈ (Submodule.span F {w₀}).restrictScalars k := by
          rw [h]; exact Submodule.mem_top
        rwa [Submodule.restrictScalars_mem] at hmem
    exact (finrank_eq_one_iff_of_nonzero' w₀ hw₀).2
      (fun w => Submodule.mem_span_singleton.1 (hline w))
  have hsemiB : ∀ b ∈ B, ∃ σ : F ≃+* F, IsSemilinearWith (glToPerm b) σ := by
    intro b hb
    obtain ⟨σ, hσ⟩ := hnorm b (hBN hb)
    exact ⟨σ.toRingEquiv, fun c w => hσ c w⟩
  have hB2 : ∀ b ∈ B, b * b = 1 := fun b hb => by
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := B) b hb
    rwa [pow_two] at this
  have hb2 : ∀ b ∈ B, ∀ w, b (b w) = w := fun b hb w =>
    congrArg (fun x : W ≃ₗ[k] W => x w) (hB2 b hb)
  have hlinB : ∀ b ∈ B, IsSemilinearWith (glToPerm b) (1 : F ≃+* F) → b = 1 := by
    intro b hb hlin
    obtain ⟨d, hd⟩ := (finrank_eq_one_iff_of_nonzero' w₀ hw₀).1 hfin1 (b w₀)
    have hbs : ∀ w, b w = d • w := by
      intro w
      obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' w₀ hw₀).1 hfin1 w
      have h1 : b (c • w₀) = c • b w₀ := hlin c w₀
      rw [h1, ← hd, smul_smul, smul_smul, mul_comm]
    have hdd : d * d = 1 := by
      have h1 := hb2 b hb w₀
      rw [hbs, hbs, smul_smul] at h1
      have h2 : (d * d - 1) • w₀ = 0 := by rw [sub_smul, h1, one_smul, sub_self]
      exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right hw₀)
    have hd1 : d = 1 := by
      have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
      have h3 : (d - 1) * (d - 1) = 0 := by
        have h4 : (d - 1) * (d - 1) = d * d - 2 * d + 1 := by ring
        rw [h4, hdd, show (1 : F) - 2 * d + 1 = 2 - 2 * d by ring, h2]
        ring
      exact sub_eq_zero.1 (mul_self_eq_zero.1 h3)
    refine LinearEquiv.ext fun w => ?_
    have : b w = w := by rw [hbs w, hd1, one_smul]
    exact this
  let B' : Subgroup (Equiv.Perm W) := B.map glToPerm
  have hB'mem : ∀ a ∈ B', ∃ b ∈ B, glToPerm b = a := fun a ha => Subgroup.mem_map.1 ha
  have hsqB' : ∀ a ∈ B', a * a = 1 := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := hB'mem a ha
    rw [← map_mul, hB2 b hb, map_one]
  have hsemiB' : ∀ a ∈ B', ∃ σ : F ≃+* F, IsSemilinearWith a σ := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := hB'mem a ha
    exact hsemiB b hb
  have hinj : ∀ a ∈ B', IsSemilinearWith a (1 : F ≃+* F) → a = 1 := by
    intro a ha h1
    obtain ⟨b, hb, rfl⟩ := hB'mem a ha
    rw [hlinB b hb h1, map_one]
  obtain ⟨⟨b₀, hb₀⟩, hb₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hBne
  have hb₀ne : b₀ ≠ 1 := fun h => hb₀1 (Subtype.ext h)
  have ha₀B : glToPerm b₀ ∈ B' := Subgroup.mem_map.2 ⟨b₀, hb₀, rfl⟩
  obtain ⟨σ₀, hσ₀⟩ := hsemiB' _ ha₀B
  have hσ₀1 : σ₀ ≠ 1 := by
    intro h
    rw [h] at hσ₀
    have h1 : glToPerm b₀ = 1 := hinj _ ha₀B hσ₀
    exact hb₀ne (glToPerm_injective (by rw [h1, map_one]))
  have hσ₀2 : σ₀ * σ₀ = 1 := sq_eq_one_of_semilinear (hsqB' _ ha₀B) hσ₀
  have hsub := sub_of_inj B' hsqB' hsemiB' hinj ha₀B hσ₀ hσ₀1
  have hBsub : ∀ b ∈ B, b = 1 ∨ b = b₀ := by
    intro b hb
    rcases hsub (glToPerm b) (Subgroup.mem_map.2 ⟨b, hb, rfl⟩) with h | h
    · left; exact glToPerm_injective (by rw [h, map_one])
    · right; exact glToPerm_injective h
  have hBcard : Nat.card B = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨⟨1, B.one_mem⟩, ⟨b₀, hb₀⟩, ?_, ?_⟩
    · intro h; exact hb₀ne (congrArg Subtype.val h).symm
    · ext ⟨b, hb⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      rcases hBsub b hb with rfl | rfl
      · left; rfl
      · right; rfl
  have hfixeq : Nat.card (fixGL B) = Nat.card {w : W // glToPerm b₀ w = w} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
    rw [mem_fixGL]
    constructor
    · intro h; exact h b₀ hb₀
    · intro h x hx
      rcases hBsub x hx with rfl | rfl
      · rfl
      · exact h
  have hoff' : Nat.card W ≤ 2 * Nat.card {w : W // glToPerm b₀ w = w} := by
    have := hoff
    rw [hBcard, hfixeq] at this
    exact this
  obtain ⟨hF4, hW4, hfix2⟩ := involution_offender_card (a₀ := glToPerm b₀)
    (fun x y => map_add b₀ x y) (fun w => hb2 b₀ hb₀ w) hσ₀ hσ₀1 hσ₀2 hoff'
  obtain ⟨n, hFn, hn2, hnfix⟩ := card_eq_sq_of_involution σ₀ hσ₀1 hσ₀2
  have hn : n = 2 := by
    rw [hF4] at hFn
    have h1 : n ≤ 2 := by
      by_contra h
      have h' : 3 ≤ n := by omega
      nlinarith
    omega
  have hkF : ∀ c : k, σ₀ (algebraMap k F c) = algebraMap k F c := by
    intro c
    have hb₀w : b₀ w₀ ≠ 0 := fun h => hw₀ (b₀.injective (by rw [h, map_zero]))
    have h1 : b₀ (c • w₀) = c • b₀ w₀ := map_smul b₀ c w₀
    have h2 : b₀ ((algebraMap k F c) • w₀) = σ₀ (algebraMap k F c) • b₀ w₀ := hσ₀ _ _
    rw [algebraMap_smul F] at h2
    have h3 : (algebraMap k F c) • b₀ w₀ = σ₀ (algebraMap k F c) • b₀ w₀ := by
      rw [algebraMap_smul F, ← h1]; exact h2
    exact (smul_left_injective F hb₀w h3).symm
  have hkcard : Nat.card k ≤ Nat.card {c : F // σ₀ c = c} :=
    Nat.card_le_card_of_injective
      (fun c : k => (⟨algebraMap k F c, hkF c⟩ : {c : F // σ₀ c = c}))
      (fun c c' h => (algebraMap k F).injective (congrArg Subtype.val h))
  have hk2 : Nat.card k = 2 := by
    have h2 : Nat.card {c : F // σ₀ c = c} = 2 := by rw [hnfix, hn]
    have h1 : 1 < Nat.card k := Finite.one_lt_card
    omega
  have hd2 : Module.finrank k W = 2 := by
    have hfk : Module.Finite k W := Module.Finite.of_finite
    have hWk : Nat.card W = Nat.card k ^ Module.finrank k W := Module.natCard_eq_pow_finrank
    rw [hW4, hk2] at hWk
    have h1 : (2 : ℕ) ^ 2 = 2 ^ Module.finrank k W := by rw [← hWk]; norm_num
    exact (Nat.pow_right_injective (le_refl 2) h1).symm
  have hGL : Nat.card (W ≃ₗ[k] W) = 6 := natCard_linearEquiv_two hk2 hd2
  have hH3 : Nat.card H = 3 := by
    have hdvd : Nat.card H ∣ 6 := by
      rw [← hGL]; exact Subgroup.card_subgroup_dvd_card H
    have hne1 : Nat.card H ≠ 1 := fun h => hHne (Subgroup.card_eq_one.1 h)
    have hpos : 0 < Nat.card H := Nat.card_pos
    obtain ⟨m, hm⟩ := hHodd
    have hle : Nat.card H ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card H = nH at *
    interval_cases nH <;> omega
  have hHB : H ⊔ B = ⊤ := by
    have h3 : 3 ∣ Nat.card (H ⊔ B : Subgroup (W ≃ₗ[k] W)) := by
      rw [← hH3]; exact Subgroup.card_dvd_of_le le_sup_left
    have h2 : 2 ∣ Nat.card (H ⊔ B : Subgroup (W ≃ₗ[k] W)) := by
      rw [← hBcard]; exact Subgroup.card_dvd_of_le le_sup_right
    have h6 : Nat.card (H ⊔ B : Subgroup (W ≃ₗ[k] W)) ∣ 6 := by
      rw [← hGL]; exact Subgroup.card_subgroup_dvd_card _
    have hle : Nat.card (H ⊔ B : Subgroup (W ≃ₗ[k] W)) ≤ 6 := Nat.le_of_dvd (by norm_num) h6
    have hpos : 0 < Nat.card (H ⊔ B : Subgroup (W ≃ₗ[k] W)) := Nat.card_pos
    have heq : Nat.card (H ⊔ B : Subgroup (W ≃ₗ[k] W)) = 6 := by omega
    exact Subgroup.eq_top_of_card_eq _ (by rw [heq, hGL])
  have hfixB2 : Nat.card (fixGL B) = 2 := by rw [hfixeq]; exact hfix2
  refine ⟨hk2, hd2, hH3, hBcard, hHB, ?_⟩
  rw [hBcard, hfixB2, hW4]

end ThreeActor

end CFSG.QuasithinUnique.Setup.Offender

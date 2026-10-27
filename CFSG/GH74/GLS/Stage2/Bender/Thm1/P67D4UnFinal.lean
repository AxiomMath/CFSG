module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnLay
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnAsm
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnHeis2
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnSL2

public section

open scoped Pointwise

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Steinberg Multiplicative

theorem un_norm_solution {p f : ℕ} [Fact p.Prime] (hf : 0 < f) {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = (p ^ f) ^ 4) (ε : k ≃+* k) (hε : ∀ a, ε a = a ^ (p ^ f))
    (κ : kˣ)
    (hN : (κ : k) * ε (((κ⁻¹ : kˣ) : k) * ε ((κ : k) * ε (((κ⁻¹ : kˣ) : k) * ε 1))) = 1) :
    ∃ t : kˣ, (t : k) * (((κ⁻¹ : kˣ) : k) * ε t) = 1 := by
  have hq2 : 2 ≤ p ^ f :=
    le_trans (Fact.out : p.Prime).two_le (Nat.le_self_pow hf.ne' p)
  generalize hq : p ^ f = q at hq2 hk hε hN
  have hE : κ * (κ⁻¹ * (κ * κ⁻¹ ^ q) ^ q) ^ q = 1 := by
    apply Units.ext
    simpa [hε, mul_pow] using hN
  have h2 : κ ^ ((1 : ℤ) - q + q ^ 2 - q ^ 3) = 1 := by
    rw [← hE]
    group
  have h3 : κ ^ ((q - 1) * (q ^ 2 + 1)) = 1 := by
    have h4 : κ ^ (((q - 1) * (q ^ 2 + 1) : ℕ) : ℤ) = κ ^ (-((1 : ℤ) - q + q ^ 2 - q ^ 3)) := by
      congr 1
      push_cast [Nat.cast_sub (by omega : 1 ≤ q)]
      ring
    rw [zpow_natCast] at h4
    rw [h4, zpow_neg, h2, inv_one]
  have hG : Nat.card kˣ = (q + 1) * ((q - 1) * (q ^ 2 + 1)) := by
    rw [Nat.card_units, hk]
    obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    have h5 : (m + 1) ^ 4 = (m + 1 + 1) * (m * ((m + 1) ^ 2 + 1)) + 1 := by ring
    simp only [Nat.add_sub_cancel]
    omega
  have hs : 0 < (q - 1) * (q ^ 2 + 1) := Nat.mul_pos (by omega) (by positivity)
  have hcard := card_pow_eq_of_isCyclic (G := kˣ) (d := q + 1) (s := (q - 1) * (q ^ 2 + 1))
    (by omega) hs hG (g := κ) h3
  have hpos : 0 < Nat.card {x : kˣ // x ^ (q + 1) = κ} := by
    rw [hcard]
    omega
  obtain ⟨⟨t, ht⟩⟩ := Finite.card_pos_iff.1 hpos
  refine ⟨t, ?_⟩
  have h6 : t * (κ⁻¹ * t ^ q) = 1 := by
    calc t * (κ⁻¹ * t ^ q) = κ⁻¹ * (t * t ^ q) := mul_left_comm _ _ _
      _ = κ⁻¹ * t ^ (q + 1) := by rw [pow_succ']
      _ = 1 := by rw [ht, inv_mul_cancel]
  have h7 := congrArg Units.val h6
  simpa [hε] using h7

theorem un_norm_eq {G : Type*} [Group G] {k : Type*} [Field k]
    (ρ : Matrix.SpecialLinearGroup (Fin 2) k →* G) (hρinj : Function.Injective ρ) (τ : G ≃* G)
    (hτ4 : ∀ y, τ (τ (τ (τ y))) = y) (ε : k ≃+* k) (κ : kˣ)
    (hu : ∀ a, τ (ρ (sl2Upper a)) = ρ (sl2Lower ((κ : k) * ε a)))
    (hl : ∀ a, τ (ρ (sl2Lower a)) = ρ (sl2Upper (((κ⁻¹ : kˣ) : k) * ε a))) :
    (κ : k) * ε (((κ⁻¹ : kˣ) : k) * ε ((κ : k) * ε (((κ⁻¹ : kˣ) : k) * ε 1))) = 1 := by
  have h := hτ4 (ρ (sl2Lower 1))
  rw [hl, hu, hl, hu] at h
  have h' := hρinj h
  have := congrArg
    (fun M : Matrix.SpecialLinearGroup (Fin 2) k => (M : Matrix (Fin 2) (Fin 2) k) 1 0) h'
  simpa [coe_sl2Lower] using this

theorem un_theta_apply {G : Type*} [Group G] (τ : G ≃* G) (x y : G) :
    τ.trans (MulAut.conj (x⁻¹ * τ x)) y = x⁻¹ * τ (x * y * x⁻¹) * x := by
  rw [MulEquiv.trans_apply, MulAut.conj_apply]
  simp only [map_mul, map_inv]
  group

theorem un_theta_four {G : Type*} [Group G] (τ : G ≃* G) (hτ4 : ∀ y, τ (τ (τ (τ y))) = y)
    (x y : G) :
    (τ.trans (MulAut.conj (x⁻¹ * τ x))) ((τ.trans (MulAut.conj (x⁻¹ * τ x)))
      ((τ.trans (MulAut.conj (x⁻¹ * τ x))) ((τ.trans (MulAut.conj (x⁻¹ * τ x))) y))) = y := by
  have hc : ∀ z : G, x * (x⁻¹ * z * x) * x⁻¹ = z := fun z => by group
  simp only [un_theta_apply, hc, hτ4]
  group

theorem un_adapted_mem_B {X : Type*} [Group X] (D : RankTwoSystem X 3) {k : Type*} [Field k]
    (ρ : Matrix.SpecialLinearGroup (Fin 2) k →* X) (τ : X ≃* X) (ε : k ≃+* k) (κ : kˣ)
    (hl : ∀ a, τ (ρ (sl2Lower a)) = ρ (sl2Upper (((κ⁻¹ : kˣ) : k) * ε a)))
    (hρ2 : ∀ a, ρ (sl2Upper a) ∈ D.root 2)
    (hρN : ∃ m₀ : D.N, (m₀ : X) = ρ unSL2W ∧ (m₀ : D.Weyl) = D.w₀)
    (hρH : ∀ u : kˣ, ρ (unSL2Diag u) ∈ D.B ⊓ D.N)
    (t : kˣ) (ht : (t : k) * (((κ⁻¹ : kˣ) : k) * ε t) = 1) :
    ((ρ (sl2Lower (t : k)))⁻¹ * τ (ρ (sl2Lower (t : k)))) *
      ((D.lift D.w₀ : D.N) : X) ∈ D.B := by
  obtain ⟨m₀, hm₀X, hm₀W⟩ := hρN
  rw [un_adapted_elt ρ τ ε ((κ⁻¹ : kˣ) : k) hl t.ne_zero ht]
  have hmk : Units.mk0 (t : k) t.ne_zero = t := Units.ext rfl
  have e : ρ unSL2W * ρ (unSL2Diag t) = ρ (unSL2Diag t⁻¹) * ρ unSL2W := by
    rw [← map_mul, ← map_mul, un_sl2W_diag]
  have hg : ∀ a : X, a * ρ unSL2W * ρ (unSL2Diag t) = a * ρ (unSL2Diag t⁻¹) * (m₀ : X) := by
    intro a
    rw [mul_assoc a, e, ← mul_assoc, hm₀X]
  rw [hmk, hg]
  exact RankTwoSystem.exists_adapted_mid hm₀W (hρ2 _) (hρH _)

theorem un_theta_x2 {X : Type*} [Group X] {k : Type*} [Field k]
    (ρ : Matrix.SpecialLinearGroup (Fin 2) k →* X) (τ : X ≃* X) (ε : k ≃+* k) (κ : kˣ)
    (hu : ∀ a, τ (ρ (sl2Upper a)) = ρ (sl2Lower ((κ : k) * ε a)))
    (hl : ∀ a, τ (ρ (sl2Lower a)) = ρ (sl2Upper (((κ⁻¹ : kˣ) : k) * ε a)))
    (t : kˣ) (ht : (t : k) * (((κ⁻¹ : kˣ) : k) * ε t) = 1) :
    ∃ l₂ : kˣ, ∀ b : k,
      τ.trans (MulAut.conj ((ρ (sl2Lower (t : k)))⁻¹ * τ (ρ (sl2Lower (t : k)))))
        (ρ (sl2Upper b)) = ρ (sl2Upper ((l₂ : k) * ε b)) := by
  have hεt : ε (t : k) ≠ 0 := (map_ne_zero ε).2 t.ne_zero
  have hne : (-((κ : k) * (((κ⁻¹ : kˣ) : k) * ε t) ^ 2)) ≠ 0 :=
    neg_ne_zero.2 (mul_ne_zero κ.ne_zero (pow_ne_zero 2 (mul_ne_zero (κ⁻¹).ne_zero hεt)))
  refine ⟨Units.mk0 _ hne, fun b => ?_⟩
  rw [un_theta_apply, un_theta_upper ρ τ ε (κ : k) ((κ⁻¹ : kˣ) : k) hu hl ht b]
  congr 2
  rw [Units.val_mk0]
  ring

section Layers

variable {X : Type*} [Group X] (D : RankTwoSystem X 3)

private theorem un_intList : intList 1 ((3 : ℕ) : ℤ) = [1, 2, 3] := by decide

theorem un_decomp {u : X} (hu : u ∈ D.U) :
    ∃ y ∈ D.root 1, ∃ b ∈ D.root 2, ∃ z ∈ D.root 3, u = y * b * z := by
  have hu' : u ∈ chainProd D.root (intList 1 ((3 : ℕ) : ℤ)) := by
    rw [← D.roots.carrier_eq]
    exact hu
  rw [un_intList, chainProd_cons, chainProd_cons, chainProd_singleton] at hu'
  obtain ⟨y, hy, w, hw, rfl⟩ := Set.mem_mul.1 hu'
  obtain ⟨b, hb, z, hz, rfl⟩ := Set.mem_mul.1 hw
  exact ⟨y, hy, b, hb, z, hz, (mul_assoc y b z).symm⟩

theorem un_unique {y y' b b' z z' : X} (hy : y ∈ D.root 1) (hy' : y' ∈ D.root 1)
    (hb : b ∈ D.root 2) (hb' : b' ∈ D.root 2) (hz : z ∈ D.root 3) (hz' : z' ∈ D.root 3)
    (h : y * b * z = y' * b' * z') : y = y' ∧ b = b' ∧ z = z' := by
  have key := D.roots.unique (fun j => if j = 1 then y else if j = 2 then b else z)
    (fun j => if j = 1 then y' else if j = 2 then b' else z') ?_ ?_ ?_
  · refine ⟨?_, ?_, ?_⟩
    · simpa using key 1 (by rw [un_intList]; decide)
    · simpa using key 2 (by rw [un_intList]; decide)
    · simpa using key 3 (by rw [un_intList]; decide)
  · intro j hj
    rw [un_intList] at hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> simp [hy, hb, hz]
  · intro j hj
    rw [un_intList] at hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> simp [hy', hb', hz']
  · rw [un_intList]
    simpa [mul_assoc] using h

theorem un_theta_sq_x1 [Finite X] {k : Type*} [Field k] (τ e : X ≃* X)
    (hτ : D.IsOpposition τ) (hτe : ∀ y, τ (τ y) = e y) (he : ∀ b ∈ D.B, e b ∈ D.B)
    (ε : k ≃+* k) (x₁ : Multiplicative k →* X) (hx₁ : ∀ a, x₁ a ∈ D.root 1)
    (hx₁torus : ∀ h ∈ D.B ⊓ D.N, ∃ χ : kˣ,
      ∀ a : k, h * x₁ (ofAdd a) * h⁻¹ = x₁ (ofAdd ((χ : k) * a)))
    (hx₁e : ∀ a : k, e (x₁ (ofAdd a)) = x₁ (ofAdd (ε (ε a))))
    (hab₁ : ∀ a ∈ D.root 1, ∀ b ∈ D.root 1, a * b = b * a)
    (hab₃ : ∀ a ∈ D.root 3, ∀ b ∈ D.root 3, a * b = b * a) {g : X}
    (hg : g * ((D.lift D.w₀ : D.N) : X) ∈ D.B) :
    ∃ ν : kˣ, ∀ a : k, ∃ b ∈ D.root 2,
      τ.trans (MulAut.conj g) (τ.trans (MulAut.conj g) (x₁ (ofAdd a))) =
        b * x₁ (ofAdd ((ν : k) * ε (ε a))) := by
  obtain ⟨b₂, hb₂, hsq⟩ := hτ.theta_sq hτe he hg
  have hb₂' : b₂ ∈ ((D.B ⊓ D.N : Subgroup X) : Set X) * (D.U : Set X) := D.isSplit.2 ▸ hb₂
  obtain ⟨h, hh, u, hu, rfl⟩ := Set.mem_mul.1 hb₂'
  obtain ⟨χ, hχ⟩ := hx₁torus h hh
  refine ⟨χ, fun a => ?_⟩
  have hxU : x₁ (ofAdd (ε (ε a))) ∈ D.U :=
    D.root_le_U (by norm_num) (by norm_num) (hx₁ _)
  have hc := D.commutator_mem_root₂ hab₁ hab₃ hu hxU
  refine ⟨h * (u * x₁ (ofAdd (ε (ε a))) * u⁻¹ * (x₁ (ofAdd (ε (ε a))))⁻¹) * h⁻¹,
    D.roots.invariant 2 ⟨by norm_num, by norm_num⟩ h hh _ hc, ?_⟩
  rw [hsq, hx₁e, ← hχ (ε (ε a))]
  group

theorem un_heis_fixed {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 0 < f) [Finite X]
    {k : Type} [Field k] [Finite k] [CharP k p] (hk : Nat.card k = (p ^ f) ^ 4)
    (ε : k ≃+* k) (hε : ∀ a, ε a = a ^ (p ^ f)) (x₁ x₂ : Multiplicative k →* X)
    (hx₁inj : Function.Injective x₁) (hx₂inj : Function.Injective x₂)
    (hx₁ : ∀ a, x₁ a ∈ D.root 1) (hx₂ : ∀ a, x₂ a ∈ D.root 2)
    (hx₁s : ∀ y ∈ D.root 1, ∃ a, y = x₁ a) (hx₂s : ∀ y ∈ D.root 2, ∃ a, y = x₂ a)
    (hab₁ : ∀ a ∈ D.root 1, ∀ b ∈ D.root 1, a * b = b * a)
    (hab₃ : ∀ a ∈ D.root 3, ∀ b ∈ D.root 3, a * b = b * a)
    (θ : X ≃* X) (hθU : ∀ u ∈ D.U, θ u ∈ D.U) (hθ4 : ∀ y, θ (θ (θ (θ y))) = y) (l₂ ν : kˣ)
    (hθ₂ : ∀ b : k, θ (x₂ (ofAdd b)) = x₂ (ofAdd ((l₂ : k) * ε b)))
    (hθ₁ : ∀ y ∈ D.root 1, ∃ b ∈ D.root 2, ∃ z ∈ D.root 3, θ y = b * z)
    (hθ₃ : ∀ z ∈ D.root 3, ∃ b ∈ D.root 2, ∃ y ∈ D.root 1, θ z = b * y)
    (hθ₁₁ : ∀ a : k, ∃ b ∈ D.root 2,
      θ (θ (x₁ (ofAdd a))) = b * x₁ (ofAdd ((ν : k) * ε (ε a)))) :
    Nat.card ↥(D.U ⊓ foldFix θ) = (p ^ f) ^ 3 ∧
      ∃ y ∈ D.root 1, y ≠ 1 ∧ ∃ b ∈ D.root 2, ∃ z ∈ D.root 3, z ≠ 1 ∧
        θ (y * b * z) = y * b * z := by
  have hU1 : D.root 1 ≤ D.U := D.root_le_U (by norm_num) (by norm_num)
  have hU2 : D.root 2 ≤ D.U := D.root_le_U (by norm_num) (by norm_num)
  have hU3 : D.root 3 ≤ D.U := D.root_le_U (by norm_num) (by norm_num)
  let θU : ↥D.U ≃* ↥D.U :=
    { toFun := fun u => ⟨θ (u : X), hθU u u.2⟩
      invFun := fun u => ⟨θ (θ (θ (u : X))), hθU _ (hθU _ (hθU _ u.2))⟩
      left_inv := fun u => Subtype.ext (hθ4 (u : X))
      right_inv := fun u => Subtype.ext (hθ4 (u : X))
      map_mul' := fun u v => Subtype.ext (map_mul θ (u : X) (v : X)) }
  have hθU4 : (θU : MulAut ↥D.U) ^ 4 = 1 := by
    ext u
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply]
    exact hθ4 (u : X)
  let y₁ : Multiplicative k →* ↥D.U := x₁.codRestrict D.U fun a => hU1 (hx₁ a)
  let y₂ : Multiplicative k →* ↥D.U := x₂.codRestrict D.U fun a => hU2 (hx₂ a)
  have hdec : ∀ u : ↥D.U, ∃! t : ↥D.U × ↥D.U × ↥D.U,
      t.1 ∈ (D.root 1).subgroupOf D.U ∧ t.2.1 ∈ (D.root 2).subgroupOf D.U ∧
        t.2.2 ∈ (D.root 3).subgroupOf D.U ∧ u = t.1 * t.2.1 * t.2.2 := by
    intro u
    obtain ⟨y, hy, b, hb, z, hz, hu⟩ := un_decomp D u.2
    refine ⟨(⟨y, hU1 hy⟩, ⟨b, hU2 hb⟩, ⟨z, hU3 hz⟩),
      ⟨Subgroup.mem_subgroupOf.2 hy, Subgroup.mem_subgroupOf.2 hb, Subgroup.mem_subgroupOf.2 hz,
        Subtype.ext hu⟩, ?_⟩
    rintro ⟨y', b', z'⟩ ⟨hy', hb', hz', hu'⟩
    obtain ⟨h1, h2, h3⟩ := un_unique D (Subgroup.mem_subgroupOf.1 hy')
      hy (Subgroup.mem_subgroupOf.1 hb') hb (Subgroup.mem_subgroupOf.1 hz') hz
      (by rw [← hu]; exact (congrArg Subtype.val hu').symm)
    exact Prod.ext (Subtype.ext h1) (Prod.ext (Subtype.ext h2) (Subtype.ext h3))
  obtain ⟨hcard, -, y, hy, hy1, b, hb, z, hz, hz1, hfix⟩ := card_fixed_heis' hp2 hf hk ε hε
    ((D.root 1).subgroupOf D.U) ((D.root 2).subgroupOf D.U) ((D.root 3).subgroupOf D.U) y₁ y₂
    (fun a b h => hx₁inj (congrArg Subtype.val h)) (fun a b h => hx₂inj (congrArg Subtype.val h))
    (fun a => Subgroup.mem_subgroupOf.2 (hx₁ _)) (fun a => Subgroup.mem_subgroupOf.2 (hx₂ _))
    (fun y hy => by
      obtain ⟨a, ha⟩ := hx₁s y (Subgroup.mem_subgroupOf.1 hy)
      exact ⟨toAdd a, Subtype.ext ha⟩)
    (fun y hy => by
      obtain ⟨a, ha⟩ := hx₂s y (Subgroup.mem_subgroupOf.1 hy)
      exact ⟨toAdd a, Subtype.ext ha⟩)
    hdec
    (fun u y hy => Subgroup.mem_subgroupOf.2 (D.conj_root₂_mem u.2 (Subgroup.mem_subgroupOf.1 hy)))
    (fun u v => Subgroup.mem_subgroupOf.2 (D.commutator_mem_root₂ hab₁ hab₃ u.2 v.2))
    θU hθU4 l₂ ν (fun b => Subtype.ext (hθ₂ b))
    (fun y hy => by
      obtain ⟨b, hb, z, hz, h⟩ := hθ₁ y (Subgroup.mem_subgroupOf.1 hy)
      exact ⟨⟨b, hU2 hb⟩, Subgroup.mem_subgroupOf.2 hb, ⟨z, hU3 hz⟩,
        Subgroup.mem_subgroupOf.2 hz, Subtype.ext h⟩)
    (fun z hz => by
      obtain ⟨b, hb, y, hy, h⟩ := hθ₃ z (Subgroup.mem_subgroupOf.1 hz)
      exact ⟨⟨b, hU2 hb⟩, Subgroup.mem_subgroupOf.2 hb, ⟨y, hU1 hy⟩,
        Subgroup.mem_subgroupOf.2 hy, Subtype.ext h⟩)
    (fun a => by
      obtain ⟨b, hb, h⟩ := hθ₁₁ a
      exact ⟨⟨b, hU2 hb⟩, Subgroup.mem_subgroupOf.2 hb, Subtype.ext h⟩)
  refine ⟨?_, (y : X), Subgroup.mem_subgroupOf.1 hy, fun h => hy1 (Subtype.ext h), (b : X),
    Subgroup.mem_subgroupOf.1 hb, (z : X), Subgroup.mem_subgroupOf.1 hz,
    fun h => hz1 (Subtype.ext h), congrArg Subtype.val (mem_foldFix.1 hfix)⟩
  rw [← hcard]
  exact Nat.card_congr
    { toFun := fun w => ⟨⟨(w : X), (Subgroup.mem_inf.1 w.2).1⟩,
        Subtype.ext (mem_foldFix.1 (Subgroup.mem_inf.1 w.2).2)⟩
      invFun := fun v => ⟨(v.1 : X),
        Subgroup.mem_inf.2 ⟨v.1.2, mem_foldFix.2 (congrArg Subtype.val v.2)⟩⟩
      left_inv := fun w => rfl
      right_inv := fun v => rfl }

theorem un_hKC (hab₁ : ∀ a ∈ D.root 1, ∀ b ∈ D.root 1, a * b = b * a)
    (hab₃ : ∀ a ∈ D.root 3, ∀ b ∈ D.root 3, a * b = b * a)
    (hTor : ∀ h ∈ D.B ⊓ D.N, ∀ y ∈ D.root 1, y ≠ 1 → ∀ z ∈ D.root 3, z ≠ 1 →
      h * y = y * h → h * z = z * h → h = 1) (θ : X ≃* X)
    (hfix : ∃ y ∈ D.root 1, y ≠ 1 ∧ ∃ b ∈ D.root 2, ∃ z ∈ D.root 3, z ≠ 1 ∧
      θ (y * b * z) = y * b * z) :
    ∀ k₀ ∈ D.B, θ k₀ = k₀ → (∀ u ∈ D.U, θ u = u → k₀ * u = u * k₀) → k₀ ∈ D.U := by
  have hU1 : D.root 1 ≤ D.U := D.root_le_U (by norm_num) (by norm_num)
  have hU2 : D.root 2 ≤ D.U := D.root_le_U (by norm_num) (by norm_num)
  have hU3 : D.root 3 ≤ D.U := D.root_le_U (by norm_num) (by norm_num)
  obtain ⟨y, hy, hy1, b, hb, z, hz, hz1, hfx⟩ := hfix
  intro k₀ hk₀ _ hcomm
  have hk' : k₀ ∈ ((D.B ⊓ D.N : Subgroup X) : Set X) * (D.U : Set X) := D.isSplit.2 ▸ hk₀
  obtain ⟨h, hh, u, hu, rfl⟩ := Set.mem_mul.1 hk'
  have hv : y * b * z ∈ D.U := D.U.mul_mem (D.U.mul_mem (hU1 hy) (hU2 hb)) (hU3 hz)
  have hk : (h * u) * (y * b * z) * (h * u)⁻¹ = y * b * z :=
    mul_inv_eq_iff_eq_mul.2 (hcomm _ hv hfx)
  obtain ⟨h1, h2⟩ := commute_outer_of_commute_fixed' D.U (D.root 1) (D.root 2) (D.root 3)
    hU1 hU2 hU3 (fun y y' b b' z z' hy hy' hb hb' hz hz' e => un_unique D hy hy' hb hb' hz hz' e)
    (fun u hu y hy => D.conj_root₂_mem hu hy)
    (fun u hu v hv => D.commutator_mem_root₂ hab₁ hab₃ hu hv) h u hu
    (fun y hy => D.roots.invariant 1 ⟨by norm_num, by norm_num⟩ h hh y hy)
    (fun y hy => D.roots.invariant 2 ⟨by norm_num, by norm_num⟩ h hh y hy)
    (fun y hy => D.roots.invariant 3 ⟨by norm_num, by norm_num⟩ h hh y hy) hy hb hz hk
  have hh1 : h = 1 := hTor h hh y hy hy1 z hz hz1 (mul_inv_eq_iff_eq_mul.1 h1)
    (mul_inv_eq_iff_eq_mul.1 h2)
  rw [hh1, one_mul]
  exact hu

end Layers

theorem un_lower_mem_dc {X : Type*} [Group X] (D : RankTwoSystem X 3) {k : Type*} [Field k]
    (ρ : Matrix.SpecialLinearGroup (Fin 2) k →* X) (hρ2 : ∀ a, ρ (sl2Upper a) ∈ D.root 2)
    (hρN : ∃ m₀ : D.N, (m₀ : X) = ρ unSL2W ∧ (m₀ : D.Weyl) = D.w₀)
    (hρH : ∀ u : kˣ, ρ (unSL2Diag u) ∈ D.B ⊓ D.N) {s : k} (hs : s ≠ 0) :
    ρ (sl2Lower s) ∈ dc D.B D.N D.w₀ := by
  obtain ⟨m₀, hm₀X, hm₀W⟩ := hρN
  rw [mem_dc_of_lift hm₀W]
  have hB2 : ∀ a, ρ (sl2Upper a) ∈ D.B := fun a =>
    D.root_le_B (by norm_num) (by norm_num) (hρ2 a)
  refine ⟨ρ (sl2Upper s⁻¹), hB2 _, ρ (unSL2Diag (-(Units.mk0 s hs))) * ρ (sl2Upper s⁻¹),
    D.B.mul_mem (hρH _).1 (hB2 _), ?_⟩
  rw [un_sl2Lower_eq hs, hm₀X]
  simp only [map_mul, mul_assoc]

theorem un_c0_mem_dc {X : Type*} [Group X] (D : RankTwoSystem X 3) {k : Type*} [Field k]
    (ρ : Matrix.SpecialLinearGroup (Fin 2) k →* X) (hρ2 : ∀ a, ρ (sl2Upper a) ∈ D.root 2)
    (hρm2 : ∀ a, ρ (sl2Lower a) ∈ D.root (-2))
    (hρN : ∃ m₀ : D.N, (m₀ : X) = ρ unSL2W ∧ (m₀ : D.Weyl) = D.w₀)
    (hρH : ∀ u : kˣ, ρ (unSL2Diag u) ∈ D.B ⊓ D.N) (h2 : (2 : k) ≠ 0) {c : X}
    (hcH : c ∈ D.B ⊓ D.N) (hcinv : ∀ y ∈ D.root (-2), c * y * c⁻¹ = y⁻¹) (t : kˣ) :
    (ρ (sl2Lower (t : k)))⁻¹ * c * ρ (sl2Lower (t : k)) ∈ dc D.B D.N D.w₀ := by
  have hx : c * ρ (sl2Lower (t : k)) = (ρ (sl2Lower (t : k)))⁻¹ * c :=
    mul_inv_eq_iff_eq_mul.1 (hcinv _ (hρm2 _))
  have e : (ρ (sl2Lower (t : k)))⁻¹ * c * ρ (sl2Lower (t : k)) =
      c * ρ (sl2Lower ((t : k) + t)) * 1 := by
    rw [un_sl2Lower_add, map_mul, mul_one, ← mul_assoc, hx]
  have ht2 : (t : k) + t ≠ 0 := by
    rw [← two_mul]
    exact mul_ne_zero h2 t.ne_zero
  rw [e]
  exact mul_mem_dc (un_lower_mem_dc D ρ hρ2 hρN hρH ht2) hcH.1 D.B.one_mem

theorem un_noAbel_of_equiv {F F' : Type*} [Group F] [Group F'] (e : F ≃* F')
    (h : ∀ A : Subgroup F, A.Normal → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → A = ⊥) :
    ∀ A : Subgroup F', A.Normal → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → A = ⊥ := by
  intro A hA hab
  have hA' : (A.comap e.toMonoidHom).Normal := hA.comap e.toMonoidHom
  have h0 := h (A.comap e.toMonoidHom) hA' fun a ha b hb =>
    e.injective (by simpa using hab _ ha _ hb)
  rw [eq_bot_iff]
  intro z hz
  have hz' : e.symm z ∈ A.comap e.toMonoidHom := by simpa using hz
  rw [h0, Subgroup.mem_bot] at hz'
  rw [Subgroup.mem_bot]
  simpa using congrArg e hz'

def unFixEquiv {X : Type*} [Group X] (τ θ : X ≃* X) (x : X)
    (hθ : ∀ y, θ y = x⁻¹ * τ (x * y * x⁻¹) * x) : ↥(foldFix θ) ≃* ↥(foldFix τ) where
  toFun y := ⟨x * (y : X) * x⁻¹, by
    have h := mem_foldFix.1 y.2
    rw [hθ] at h
    rw [mem_foldFix]
    calc τ (x * (y : X) * x⁻¹) = x * (x⁻¹ * τ (x * (y : X) * x⁻¹) * x) * x⁻¹ := by group
      _ = x * (y : X) * x⁻¹ := by rw [h]⟩
  invFun z := ⟨x⁻¹ * (z : X) * x, by
    rw [mem_foldFix, hθ]
    have h := mem_foldFix.1 z.2
    have e : x * (x⁻¹ * (z : X) * x) * x⁻¹ = (z : X) := by group
    rw [e, h]⟩
  left_inv y := Subtype.ext (by
    show x⁻¹ * (x * (y : X) * x⁻¹) * x = (y : X)
    group)
  right_inv z := Subtype.ext (by
    show x * (x⁻¹ * (z : X) * x) * x⁻¹ = (z : X)
    group)
  map_mul' y y' := Subtype.ext (by
    show x * ((y : X) * (y' : X)) * x⁻¹ = x * (y : X) * x⁻¹ * (x * (y' : X) * x⁻¹)
    group)

@[expose] def unSL2UpperHom (k : Type*) [Field k] :
    Multiplicative k →* Matrix.SpecialLinearGroup (Fin 2) k :=
  MonoidHom.mk' (fun a => sl2Upper (toAdd a)) fun a b => by
    rw [toAdd_mul]
    exact un_sl2Upper_add _ _

theorem un_sl2Upper_injective {k : Type*} [Field k] :
    Function.Injective (sl2Upper : k → Matrix.SpecialLinearGroup (Fin 2) k) := fun a b h => by
  have := congrArg
    (fun M : Matrix.SpecialLinearGroup (Fin 2) k => (M : Matrix (Fin 2) (Fin 2) k) 0 1) h
  simpa [coe_sl2Upper] using this

theorem un_two_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {k : Type*} [Field k] [CharP k p] :
    (2 : k) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : k) = 0 := by exact_mod_cast h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1
    ((CharP.cast_eq_zero_iff k p 2).1 h'))

theorem un_final {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p % 3 = 2) (hf : 0 < f)
    {X : Type*} [Group X] [Finite X] (D : RankTwoSystem X 3) (hUp : IsPGroup p D.U)
    (τ e : X ≃* X) (hτ : D.IsOpposition τ) (hτe : ∀ y, τ (τ y) = e y)
    (he : ∀ b ∈ D.B, e b ∈ D.B) (hτ4 : ∀ y, τ (τ (τ (τ y))) = y)
    {k : Type} [Field k] [Finite k] [CharP k p] (hk : Nat.card k = (p ^ f) ^ 4)
    (ε : k ≃+* k) (hε : ∀ a, ε a = a ^ (p ^ f))
    (ρ : Matrix.SpecialLinearGroup (Fin 2) k →* X) (hρinj : Function.Injective ρ) (κ : kˣ)
    (hu : ∀ a, τ (ρ (sl2Upper a)) = ρ (sl2Lower ((κ : k) * ε a)))
    (hl : ∀ a, τ (ρ (sl2Lower a)) = ρ (sl2Upper (((κ⁻¹ : kˣ) : k) * ε a)))
    (hρ2 : ∀ a, ρ (sl2Upper a) ∈ D.root 2) (hρ2' : ∀ y ∈ D.root 2, ∃ a, y = ρ (sl2Upper a))
    (hρm2 : ∀ a, ρ (sl2Lower a) ∈ D.root (-2))
    (hρN : ∃ m₀ : D.N, (m₀ : X) = ρ unSL2W ∧ (m₀ : D.Weyl) = D.w₀)
    (hρH : ∀ u : kˣ, ρ (unSL2Diag u) ∈ D.B ⊓ D.N)
    (x₁ : Multiplicative k →* X) (hx₁inj : Function.Injective x₁)
    (hx₁ : ∀ a, x₁ a ∈ D.root 1) (hx₁s : ∀ y ∈ D.root 1, ∃ a, y = x₁ a)
    (hx₁torus : ∀ h ∈ D.B ⊓ D.N, ∃ χ : kˣ,
      ∀ a : k, h * x₁ (ofAdd a) * h⁻¹ = x₁ (ofAdd ((χ : k) * a)))
    (hx₁e : ∀ a : k, e (x₁ (ofAdd a)) = x₁ (ofAdd (ε (ε a))))
    (hab₁ : ∀ a ∈ D.root 1, ∀ b ∈ D.root 1, a * b = b * a)
    (hab₃ : ∀ a ∈ D.root 3, ∀ b ∈ D.root 3, a * b = b * a)
    (hTor : ∀ h ∈ D.B ⊓ D.N, ∀ y ∈ D.root 1, y ≠ 1 → ∀ z ∈ D.root 3, z ≠ 1 →
      h * y = y * h → h * z = z * h → h = 1)
    (hĉ : ∃ c ∈ D.B ⊓ D.N, τ c = c ∧ c * c = 1 ∧ ∀ y ∈ D.root (-2), c * y * c⁻¹ = y⁻¹) :
    (∀ A : Subgroup ↥(foldFix τ), A.Normal → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → A = ⊥) ∧
      ∃ U₀ : Subgroup X, U₀ ≤ foldFix τ ∧ IsPGroup p U₀ ∧ (p ^ f) ^ 3 ≤ Nat.card U₀ := by
  obtain ⟨t, ht⟩ := un_norm_solution hf hk ε hε κ (un_norm_eq ρ hρinj τ hτ4 ε κ hu hl)
  have hg : (ρ (sl2Lower (t : k)))⁻¹ * τ (ρ (sl2Lower (t : k))) *
      ((D.lift D.w₀ : D.N) : X) ∈ D.B := un_adapted_mem_B D ρ τ ε κ hl hρ2 hρN hρH t ht
  have hθpol := hτ.isPolarity hg
  have hθapp := un_theta_apply τ (ρ (sl2Lower (t : k)))
  have hθ4 := un_theta_four τ hτ4 (ρ (sl2Lower (t : k)))
  obtain ⟨l₂, hθ₂⟩ := un_theta_x2 ρ τ ε κ hu hl t ht
  obtain ⟨ν, hθ₁₁⟩ := un_theta_sq_x1 D τ e hτ hτe he ε x₁ hx₁ hx₁torus hx₁e hab₁ hab₃ hg
  have hθ₁ := fun y (hy : y ∈ D.root 1) => hτ.theta_root₁ hg hy
  have hθ₃ := fun z (hz : z ∈ D.root 3) => hτ.theta_root₃ hg hz
  have hU1 : D.root 1 ≤ D.U := D.root_le_U (by norm_num) (by norm_num)
  have hU2 : D.root 2 ≤ D.U := D.root_le_U (by norm_num) (by norm_num)
  have hU3 : D.root 3 ≤ D.U := D.root_le_U (by norm_num) (by norm_num)
  set x : X := ρ (sl2Lower (t : k))
  set θ : X ≃* X := τ.trans (MulAut.conj (x⁻¹ * τ x))
  have hx₂inj : Function.Injective (ρ.comp (unSL2UpperHom k)) := fun a b h =>
    Multiplicative.toAdd.injective
      (@un_sl2Upper_injective k _ (toAdd a) (toAdd b) (hρinj h))
  obtain ⟨hcard, hfix⟩ := un_heis_fixed D hp2 hf hk ε hε x₁ (ρ.comp (unSL2UpperHom k)) hx₁inj
    hx₂inj hx₁ (fun a => hρ2 _) hx₁s
    (fun y hy => by
      obtain ⟨a, ha⟩ := hρ2' y hy
      exact ⟨ofAdd a, ha⟩) hab₁ hab₃ θ hθpol.mem_U hθ4 l₂ ν hθ₂ hθ₁ hθ₃ hθ₁₁
  have hKC := un_hKC D hab₁ hab₃ hTor θ hfix
  have hnt : ∃ u ∈ D.U, u ≠ 1 ∧ θ u = u := by
    obtain ⟨y, hy, hy1, b, hb, z, hz, hz1, hfx⟩ := hfix
    refine ⟨y * b * z, D.U.mul_mem (D.U.mul_mem (hU1 hy) (hU2 hb)) (hU3 hz), fun h1 => hy1 ?_,
      hfx⟩
    exact (un_unique D hy (D.root 1).one_mem hb (D.root 2).one_mem hz (D.root 3).one_mem
      (by rw [h1]; simp)).1
  obtain ⟨c, hcH, hcτ, -, hcinv⟩ := hĉ
  have hc₀ := un_c0_mem_dc D ρ hρ2 hρm2 hρN hρH (un_two_ne_zero hp2) hcH hcinv t
  have hc₀f : θ (x⁻¹ * c * x) = x⁻¹ * c * x := by
    rw [hθapp]
    have e : x * (x⁻¹ * c * x) * x⁻¹ = c := by group
    rw [e, hcτ]
  have hNA : ∀ A : Subgroup ↥(foldFix θ), A.Normal → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      A = ⊥ := fun A hA hab => by
    have := hA
    exact D.noAbel_foldFix_of_polarity Fact.out hp2 hp3 hUp hθpol hc₀ hc₀f hnt hKC A hab
  refine ⟨un_noAbel_of_equiv (unFixEquiv τ θ x hθapp) hNA, ?_⟩
  have hcard₀ : Nat.card ↥((D.U ⊓ foldFix θ).map (MulAut.conj x).toMonoidHom) =
      (p ^ f) ^ 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
    exact hcard
  refine ⟨(D.U ⊓ foldFix θ).map (MulAut.conj x).toMonoidHom, ?_, ?_, hcard₀.ge⟩
  · rintro _ ⟨u, hu, rfl⟩
    have h := mem_foldFix.1 (Subgroup.mem_inf.1 hu).2
    rw [hθapp] at h
    rw [mem_foldFix]
    show τ (x * u * x⁻¹) = x * u * x⁻¹
    calc τ (x * u * x⁻¹) = x * (x⁻¹ * τ (x * u * x⁻¹) * x) * x⁻¹ := by group
      _ = x * u * x⁻¹ := by rw [h]
  · exact IsPGroup.of_card (n := f * 3) (by rw [hcard₀, pow_mul])

end CFSG.GH74.GLS.Stage2.Bender.Thm1

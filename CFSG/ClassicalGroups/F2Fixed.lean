module

public import CFSG.Timmesfeld.Orders.Bang
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.ClassicalGroups.F2Fixed

section Fixed

variable {G : Type*} [Group G] (M : Type*) [AddCommGroup M] [DistribMulAction G M]

@[expose] def fixedSub (S : Set G) : AddSubgroup M where
  carrier := {m | ∀ g ∈ S, g • m = m}
  zero_mem' := fun g _ => smul_zero g
  add_mem' := fun {a b} ha hb g hg => by rw [smul_add, ha g hg, hb g hg]
  neg_mem' := fun {a} ha g hg => by rw [smul_neg, ha g hg]

variable {M}

theorem mem_fixedSub {S : Set G} {m : M} : m ∈ fixedSub M S ↔ ∀ g ∈ S, g • m = m := Iff.rfl

theorem fixedSub_anti {S T : Set G} (h : S ⊆ T) : fixedSub M T ≤ fixedSub M S :=
  fun _ hm g hg => hm g (h hg)

theorem fixedSub_closure (S : Set G) :
    fixedSub M (Subgroup.closure S : Set G) = fixedSub M S := by
  refine le_antisymm (fixedSub_anti Subgroup.subset_closure) fun m hm g hg => ?_
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hm x hx
  | one => exact one_smul G m
  | mul x y _ _ hx hy => rw [mul_smul, hy, hx]
  | inv x _ hx => rw [inv_smul_eq_iff]; exact hx.symm

theorem smul_mem_fixedSub_conj {S : Set G} (g : G) {m : M} (hm : m ∈ fixedSub M S) :
    g • m ∈ fixedSub M ((fun s => g * s * g⁻¹) '' S) := by
  rintro _ ⟨s, hs, rfl⟩
  rw [mul_smul, mul_smul, inv_smul_smul, hm s hs]

theorem card_fixedSub_conj (S : Set G) (g : G) :
    Nat.card (fixedSub M ((fun s => g * s * g⁻¹) '' S)) = Nat.card (fixedSub M S) := by
  refine Nat.card_congr (Equiv.symm
    { toFun := fun m => ⟨g • (m : M), smul_mem_fixedSub_conj g m.2⟩
      invFun := fun m => ⟨g⁻¹ • (m : M), ?_⟩
      left_inv := fun m => by ext; simp
      right_inv := fun m => by ext; simp })
  intro s hs
  have := m.2 (g * s * g⁻¹) ⟨s, hs, rfl⟩
  calc s • g⁻¹ • (m : M) = g⁻¹ • (g * s * g⁻¹) • (m : M) := by
        simp only [mul_smul, smul_inv_smul, inv_smul_smul]
    _ = g⁻¹ • (m : M) := by rw [this]

end Fixed

section Decomp

variable {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [DistribMulAction G M]

theorem fixedSub_singleton_eq {L₁ L₂ : Subgroup G} {x : G} (hx : x ∈ L₂)
    (hgen : Subgroup.closure ((L₁ : Set G) ∪ {x}) = ⊤)
    (hdec : IsCompl (fixedSub M (L₁ : Set G)) (fixedSub M (L₂ : Set G))) :
    fixedSub M {x} = fixedSub M (L₂ : Set G) := by
  refine le_antisymm ?_ (fixedSub_anti (Set.singleton_subset_iff.mpr hx))
  intro m hm
  have hm' : m ∈ fixedSub M (L₁ : Set G) ⊔ fixedSub M (L₂ : Set G) := by
    rw [hdec.sup_eq_top]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.mp hm'
  have hbx : b ∈ fixedSub M {x} := fixedSub_anti (Set.singleton_subset_iff.mpr hx) hb
  have hax : a ∈ fixedSub M {x} := by
    have := (fixedSub M {x}).sub_mem hm hbx
    simpa using this
  have hall : a ∈ fixedSub M ((Subgroup.closure ((L₁ : Set G) ∪ {x}) : Subgroup G) : Set G) := by
    rw [fixedSub_closure]
    intro g hg
    rcases hg with hg | hg
    · exact ha g hg
    · rw [Set.mem_singleton_iff.mp hg]; exact hax x rfl
  rw [hgen] at hall
  have ha2 : a ∈ fixedSub M (L₂ : Set G) := fun g hg => hall g (by trivial)
  have : a ∈ fixedSub M (L₁ : Set G) ⊓ fixedSub M (L₂ : Set G) := ⟨ha, ha2⟩
  rw [hdec.inf_eq_bot, AddSubgroup.mem_bot] at this
  rw [this, zero_add]
  exact hb

theorem card_eq_mul_of_isCompl [Finite M] {A B : AddSubgroup M} (h : IsCompl A B) :
    Nat.card M = Nat.card A * Nat.card B := by
  let φ : A × B →+ M := AddMonoidHom.coprod A.subtype B.subtype
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨a, b⟩ hab
    have hab' : (a : M) + b = 0 := hab
    have hb : (b : M) ∈ A := by
      have : (b : M) = -(a : M) := eq_neg_of_add_eq_zero_right hab'
      rw [this]; exact A.neg_mem a.2
    have : (b : M) ∈ A ⊓ B := ⟨hb, b.2⟩
    rw [h.inf_eq_bot, AddSubgroup.mem_bot] at this
    have ha : (a : M) = 0 := by rw [this] at hab'; simpa using hab'
    exact Prod.ext (Subtype.ext ha) (Subtype.ext this)
  have hsurj : Function.Surjective φ := by
    intro m
    have : m ∈ A ⊔ B := by rw [h.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.mp this
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩)).symm

@[expose] def comm (M : Type*) [AddCommGroup M] [DistribMulAction G M] (x : G) : M →+ M :=
  DistribSMul.toAddMonoidHom M x - AddMonoidHom.id M

theorem comm_apply (x : G) (m : M) : comm M x m = x • m - m := rfl

theorem ker_comm (x : G) : (comm M x).ker = fixedSub M {x} := by
  ext m
  simp only [AddMonoidHom.mem_ker, comm_apply, sub_eq_zero]
  exact ⟨fun h g hg => by rw [Set.mem_singleton_iff.mp hg]; exact h, fun h => h x rfl⟩

theorem sub_eq_add_of_exp2 (h2 : ∀ m : M, m + m = 0) (a b : M) : a - b = a + b := by
  rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_right (h2 b)]

theorem range_comm_le (h2 : ∀ m : M, m + m = 0) {x : G} (hx : x * x = 1) :
    (comm M x).range ≤ fixedSub M {x} := by
  rintro _ ⟨m, rfl⟩ g hg
  rw [Set.mem_singleton_iff.mp hg, comm_apply, sub_eq_add_of_exp2 h2, smul_add, ← mul_smul, hx,
    one_smul, add_comm]

theorem card_eq_card_fixedSub_mul_card_range [Finite M] (x : G) :
    Nat.card M = Nat.card (fixedSub M {x}) * Nat.card (comm M x).range := by
  rw [← ker_comm]
  exact (AddSubgroup.card_ker_mul_card_range (comm M x)).symm

theorem card_eq_sq [Finite M] {L₁ L₂ : Subgroup G}
    (hdec : IsCompl (fixedSub M (L₁ : Set G)) (fixedSub M (L₂ : Set G)))
    (hcard : Nat.card (fixedSub M (L₁ : Set G)) = Nat.card (fixedSub M (L₂ : Set G))) :
    Nat.card M = Nat.card (fixedSub M (L₂ : Set G)) ^ 2 := by
  rw [card_eq_mul_of_isCompl hdec, hcard, sq]

theorem range_comm_eq_fixedSub [Finite M] (h2 : ∀ m : M, m + m = 0) {x : G} (hx : x * x = 1)
    (hcard : Nat.card M = Nat.card (fixedSub M {x}) ^ 2) :
    (comm M x).range = fixedSub M {x} := by
  have h1 := card_eq_card_fixedSub_mul_card_range (M := M) x
  have hpos : 0 < Nat.card (fixedSub M {x}) := Nat.card_pos
  have h3 : Nat.card (comm M x).range = Nat.card (fixedSub M {x}) := by
    rw [hcard, sq] at h1
    exact (Nat.eq_of_mul_eq_mul_left hpos h1).symm
  exact AddSubgroup.eq_of_le_of_card_ge (range_comm_le h2 hx) h3.ge

theorem pair_facts [Finite M] (h2 : ∀ m : M, m + m = 0) {L₁ L₂ : Subgroup G} {x : G}
    (hx : x ∈ L₂) (hx2 : x * x = 1) (hgen : Subgroup.closure ((L₁ : Set G) ∪ {x}) = ⊤)
    (hdec : IsCompl (fixedSub M (L₁ : Set G)) (fixedSub M (L₂ : Set G)))
    (hcard : Nat.card (fixedSub M (L₁ : Set G)) = Nat.card (fixedSub M (L₂ : Set G))) :
    fixedSub M {x} = fixedSub M (L₂ : Set G) ∧ (comm M x).range = fixedSub M (L₂ : Set G) ∧
      Nat.card M = Nat.card (fixedSub M (L₂ : Set G)) ^ 2 := by
  have hfix := fixedSub_singleton_eq hx hgen hdec
  have hsq := card_eq_sq hdec hcard
  refine ⟨hfix, ?_, hsq⟩
  rw [← hfix]
  exact range_comm_eq_fixedSub h2 hx2 (by rw [hfix]; exact hsq)

theorem fixedSub_mul_eq_bot (h2 : ∀ m : M, m + m = 0) {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (h : fixedSub M {x} ⊓ fixedSub M {y} = ⊥) : fixedSub M {x * y} = ⊥ := by
  rw [eq_bot_iff]
  intro m hm
  have hxy : x • y • m = m := by rw [← mul_smul]; exact hm _ rfl
  have hxx : ∀ n : M, x • x • n = n := fun n => by rw [← mul_smul, hx, one_smul]
  have hyy : ∀ n : M, y • y • n = n := fun n => by rw [← mul_smul, hy, one_smul]
  have hym : y • m = x • m := by
    have := congrArg (fun n => x • n) hxy
    simp only [hxx] at this
    exact this
  have hyx : y • x • m = m := by
    rw [← hym, hyy]
  have hn : m + x • m ∈ fixedSub M {x} ⊓ fixedSub M {y} := by
    refine ⟨fun g hg => ?_, fun g hg => ?_⟩
    · rw [Set.mem_singleton_iff.mp hg, smul_add, hxx, add_comm]
    · rw [Set.mem_singleton_iff.mp hg, smul_add, hym, hyx, add_comm]
  rw [h, AddSubgroup.mem_bot] at hn
  have hxm : x • m = m := by
    have : x • m = -m := eq_neg_of_add_eq_zero_right hn
    rw [this, neg_eq_of_add_eq_zero_right (h2 m)]
  have : m ∈ fixedSub M {x} ⊓ fixedSub M {y} := by
    refine ⟨fun g hg => ?_, fun g hg => ?_⟩
    · rw [Set.mem_singleton_iff.mp hg]; exact hxm
    · rw [Set.mem_singleton_iff.mp hg, hym, hxm]
  rw [h] at this
  exact this

theorem dvd_card_sub_one_of_fixedSub_eq_bot [Finite M] {w : G} {r : ℕ} (hr : r.Prime)
    (hw : w ^ r = 1) (h : fixedSub M {w} = ⊥) : r ∣ Nat.card M - 1 := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hP : IsPGroup r (Subgroup.zpowers w) := by
    intro g
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw, one_zpow]
  have hmod := hP.card_modEq_card_fixedPoints M
  have hfp : Nat.card (MulAction.fixedPoints (Subgroup.zpowers w) M) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨0, fun g => smul_zero _⟩⟩⟩
    have key : ∀ c : MulAction.fixedPoints (Subgroup.zpowers w) M, (c : M) = 0 := by
      intro c
      have h1 : (c : M) ∈ fixedSub M {w} := by
        intro g hg
        rw [Set.mem_singleton_iff.mp hg]
        exact c.2 ⟨w, Subgroup.mem_zpowers w⟩
      rw [h] at h1
      exact h1
    exact Subtype.ext ((key a).trans (key b).symm)
  rw [hfp] at hmod
  exact (Nat.modEq_iff_dvd' Nat.card_pos).mp hmod.symm

theorem exists_card_eq_two_pow [Finite M] (h2 : ∀ m : M, m + m = 0) :
    ∃ N : ℕ, Nat.card M = 2 ^ N := by
  have hP : IsPGroup 2 (Multiplicative M) := by
    intro g
    refine ⟨1, ?_⟩
    have := h2 (Multiplicative.toAdd g)
    apply Multiplicative.toAdd.injective
    simpa [pow_one, toAdd_pow, two_nsmul, toAdd_one] using this
  obtain ⟨N, hN⟩ := hP.exists_card_eq
  exact ⟨N, by rw [← hN]; exact (Nat.card_congr Multiplicative.ofAdd).symm⟩

end Decomp

section Arith

theorem dvd_of_forall_prime_dvd {k N : ℕ} (hk : 1 ≤ k)
    (h : ∀ r : ℕ, r.Prime → r ∣ 2 ^ k - 1 → r ∣ 2 ^ N - 1) : k ∣ N := by
  open CFSG.Timmesfeld in
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · have : k = 1 := by omega
    rw [this]; exact one_dvd N
  by_cases h6 : k = 6
  · subst h6
    have h3 : IsPrimitivePrimeDivisor 3 2 := by
      refine ⟨Nat.prime_three, by norm_num, fun j hj hj2 => ?_⟩
      interval_cases j; norm_num
    have h7 : IsPrimitivePrimeDivisor 7 3 := by
      refine ⟨by norm_num, by norm_num, fun j hj hj3 => ?_⟩
      interval_cases j <;> norm_num
    have e3 := (h3.dvd_sub_one_iff (by norm_num) N).mp (h 3 Nat.prime_three (by norm_num))
    have e7 := (h7.dvd_sub_one_iff (by norm_num) N).mp (h 7 (by norm_num) (by norm_num))
    exact (show Nat.Coprime 2 3 by norm_num).mul_dvd_of_dvd_of_dvd e3 e7
  · obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor hk2 h6
    exact (hr.dvd_sub_one_iff (by omega) N).mp (h r hr.prime hr.dvd)

end Arith

section Projection

variable {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [DistribMulAction G M]

theorem eq_inf_sup_inf_of_comm [Finite M] {a c : G}
    (hdec : IsCompl (fixedSub M {a}) (fixedSub M {c}))
    (hra : (comm M a).range = fixedSub M {a}) (hrc : (comm M c).range = fixedSub M {c})
    {A : AddSubgroup M} (hAa : ∀ m ∈ A, a • m ∈ A) (hAc : ∀ m ∈ A, c • m ∈ A) :
    A = (A ⊓ fixedSub M {a}) ⊔ (A ⊓ fixedSub M {c}) := by
  set V₁ := fixedSub M {a} with hV₁
  set V₂ := fixedSub M {c} with hV₂
  set E : M →+ M := (comm M a).comp (comm M c) with hE
  have hfa : ∀ m ∈ V₁, comm M a m = 0 := fun m hm => by
    rw [comm_apply, hm a rfl, sub_self]
  have hfc : ∀ m ∈ V₂, comm M c m = 0 := fun m hm => by
    rw [comm_apply, hm c rfl, sub_self]
  have hE2 : ∀ m ∈ V₂, E m = 0 := fun m hm => by
    simp only [hE, AddMonoidHom.comp_apply, hfc m hm, map_zero]
  have hE1 : ∀ m ∈ V₁, E m ∈ V₁ := fun m _ => by
    simp only [hE, AddMonoidHom.comp_apply]
    rw [← hra]; exact ⟨_, rfl⟩
  have hEinj : ∀ m ∈ V₁, E m = 0 → m = 0 := by
    intro m hm hEm
    have h1 : comm M c m ∈ V₁ := by
      rw [hV₁, ← ker_comm, AddMonoidHom.mem_ker]
      simpa [hE] using hEm
    have h2' : comm M c m ∈ V₂ := by rw [← hrc]; exact ⟨_, rfl⟩
    have h3 : comm M c m ∈ V₁ ⊓ V₂ := ⟨h1, h2'⟩
    rw [hdec.inf_eq_bot, AddSubgroup.mem_bot] at h3
    have h4 : m ∈ V₂ := by
      rw [hV₂, ← ker_comm]; exact h3
    have h5 : m ∈ V₁ ⊓ V₂ := ⟨hm, h4⟩
    rw [hdec.inf_eq_bot, AddSubgroup.mem_bot] at h5
    exact h5
  let f : V₁ → V₁ := fun v => ⟨E v, hE1 v v.2⟩
  have hfinj : Function.Injective f := by
    intro v w hvw
    have : E (v - w) = 0 := by
      rw [map_sub, sub_eq_zero]; exact congrArg Subtype.val hvw
    exact sub_eq_zero.mp (Subtype.ext (hEinj _ (V₁.sub_mem v.2 w.2) this))
  let σ : Equiv.Perm V₁ := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj)
  obtain ⟨k, hk0, hk⟩ := isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_finite σ)
  have hiter : ∀ n : ℕ, ∀ v : V₁, (((σ ^ n) v : V₁) : M) = E^[n] (v : M) := by
    intro n
    induction n with
    | zero => intro v; rfl
    | succ n ih =>
      intro v
      rw [pow_succ, Equiv.Perm.mul_apply, ih, Function.iterate_succ_apply]
      rfl
  have hEk1 : ∀ v ∈ V₁, E^[k] v = v := by
    intro v hv
    have := hiter k ⟨v, hv⟩
    rw [hk] at this
    exact this.symm
  have hEk2 : ∀ v ∈ V₂, E^[k] v = 0 := by
    intro v hv
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Function.iterate_succ_apply, hE2 v hv]
    exact Function.iterate_fixed (map_zero E) j
  have hEA : ∀ n : ℕ, ∀ m ∈ A, E^[n] m ∈ A := by
    intro n
    induction n with
    | zero => intro m hm; exact hm
    | succ n ih =>
      intro m hm
      rw [Function.iterate_succ_apply]
      refine ih _ ?_
      have h1 : comm M c m ∈ A := by
        rw [comm_apply]; exact A.sub_mem (hAc m hm) hm
      have h2 : comm M a (comm M c m) ∈ A := by
        rw [comm_apply]; exact A.sub_mem (hAa _ h1) h1
      exact h2
  refine le_antisymm (fun m hm => ?_) (sup_le inf_le_left inf_le_left)
  have hm' : m ∈ V₁ ⊔ V₂ := by rw [hdec.sup_eq_top]; trivial
  obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := AddSubgroup.mem_sup.mp hm'
  have hEadd : ∀ n : ℕ, ∀ a b : M, E^[n] (a + b) = E^[n] a + E^[n] b := by
    intro n
    induction n with
    | zero => intro a b; rfl
    | succ n ih =>
      intro a b
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
        map_add, ih]
  have hsplit : E^[k] (v₁ + v₂) = v₁ := by
    rw [hEadd, hEk1 v₁ hv₁, hEk2 v₂ hv₂, add_zero]
  have hv₁A : v₁ ∈ A := by rw [← hsplit]; exact hEA k _ hm
  have hv₂A : v₂ ∈ A := by
    have := A.sub_mem hm hv₁A
    simpa using this
  exact AddSubgroup.mem_sup.mpr ⟨v₁, ⟨hv₁A, hv₁⟩, v₂, ⟨hv₂A, hv₂⟩, rfl⟩

end Projection

section StepLemma

variable {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [DistribMulAction G M]

theorem isCompl_fixedSub_conj {S T : Set G} (g : G)
    (h : IsCompl (fixedSub M S) (fixedSub M T)) :
    IsCompl (fixedSub M ((fun s => g * s * g⁻¹) '' S))
      (fixedSub M ((fun s => g * s * g⁻¹) '' T)) := by
  have hmem : ∀ (S : Set G) (m : M), m ∈ fixedSub M ((fun s => g * s * g⁻¹) '' S) ↔
      g⁻¹ • m ∈ fixedSub M S := by
    intro S m
    constructor
    · intro hm s hs
      have := hm (g * s * g⁻¹) ⟨s, hs, rfl⟩
      calc s • g⁻¹ • m = g⁻¹ • (g * s * g⁻¹) • m := by
            simp only [mul_smul, smul_inv_smul, inv_smul_smul]
        _ = g⁻¹ • m := by rw [this]
    · intro hm _ ⟨s, hs, hsx⟩
      subst hsx
      have := hm s hs
      calc (g * s * g⁻¹) • m = g • s • g⁻¹ • m := by simp only [mul_smul]
        _ = g • g⁻¹ • m := by rw [this]
        _ = m := smul_inv_smul g m
  constructor
  · rw [disjoint_iff, eq_bot_iff]
    intro m ⟨h1, h2⟩
    have : g⁻¹ • m ∈ fixedSub M S ⊓ fixedSub M T := ⟨(hmem S m).mp h1, (hmem T m).mp h2⟩
    rw [h.inf_eq_bot, AddSubgroup.mem_bot] at this
    rw [AddSubgroup.mem_bot]
    have h3 : g • g⁻¹ • m = g • (0 : M) := by rw [this]
    rwa [smul_inv_smul, smul_zero] at h3
  · rw [codisjoint_iff, eq_top_iff]
    intro m _
    have hm : g⁻¹ • m ∈ fixedSub M S ⊔ fixedSub M T := by rw [h.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, hab⟩ := AddSubgroup.mem_sup.mp hm
    refine AddSubgroup.mem_sup.mpr ⟨g • a, (hmem S _).mpr ?_, g • b, (hmem T _).mpr ?_, ?_⟩
    · rwa [inv_smul_smul]
    · rwa [inv_smul_smul]
    · rw [← smul_add, hab, smul_inv_smul]

theorem step_decomp [Finite M] (h2 : ∀ m : M, m + m = 0) {P₁ P₂ : Subgroup G} {a c : G}
    (ha : a ∈ P₁) (hc : c ∈ P₂) (ha2 : a * a = 1) (hc2 : c * c = 1)
    (hgen₁ : Subgroup.closure ((P₂ : Set G) ∪ {a}) = ⊤)
    (hgen₂ : Subgroup.closure ((P₁ : Set G) ∪ {c}) = ⊤)
    (hdec : IsCompl (fixedSub M (P₁ : Set G)) (fixedSub M (P₂ : Set G)))
    (hcard : Nat.card (fixedSub M (P₁ : Set G)) = Nat.card (fixedSub M (P₂ : Set G)))
    {E₁ E₂ : Set G} (hE₁ : a ∈ E₁) (hE₁' : E₁ ⊆ P₁) (hE₂ : c ∈ E₂) (hE₂' : E₂ ⊆ P₂)
    {W : AddSubgroup M} (hWa : ∀ w ∈ W, a • w ∈ W) (hWc : ∀ w ∈ W, c • w ∈ W) :
    W = (W ⊓ fixedSub M E₁) ⊔ (W ⊓ fixedSub M E₂) ∧
      (W ⊓ fixedSub M E₁) ⊓ (W ⊓ fixedSub M E₂) = ⊥ := by
  obtain ⟨hfa, hra, -⟩ := pair_facts h2 (L₁ := P₂) (L₂ := P₁) ha ha2 hgen₁ hdec.symm hcard.symm
  obtain ⟨hfc, hrc, -⟩ := pair_facts h2 (L₁ := P₁) (L₂ := P₂) hc hc2 hgen₂ hdec hcard
  have hE₁fix : fixedSub M E₁ = fixedSub M {a} := by
    refine le_antisymm (fixedSub_anti (Set.singleton_subset_iff.mpr hE₁)) ?_
    rw [hfa]; exact fixedSub_anti hE₁'
  have hE₂fix : fixedSub M E₂ = fixedSub M {c} := by
    refine le_antisymm (fixedSub_anti (Set.singleton_subset_iff.mpr hE₂)) ?_
    rw [hfc]; exact fixedSub_anti hE₂'
  have hdec' : IsCompl (fixedSub M {a}) (fixedSub M {c}) := by rw [hfa, hfc]; exact hdec
  rw [hE₁fix, hE₂fix]
  refine ⟨eq_inf_sup_inf_of_comm hdec' (hra.trans hfa.symm) (hrc.trans hfc.symm) hWa hWc, ?_⟩
  rw [eq_bot_iff]
  intro m hm
  have : m ∈ fixedSub M {a} ⊓ fixedSub M {c} := ⟨hm.1.2, hm.2.2⟩
  rw [hdec'.inf_eq_bot] at this
  exact this

end StepLemma

section Restrict

variable {H G : Type*} [Group H] [Group G] {M : Type*} [AddCommGroup M] [DistribMulAction G M]

@[expose, instance_reducible] def restrictAction (π : H →* G) (A : AddSubgroup M)
    (hA : ∀ h : H, ∀ a ∈ A, π h • a ∈ A) :
    DistribMulAction H A where
  smul h a := ⟨π h • (a : M), hA h a a.2⟩
  one_smul a := Subtype.ext (by show π 1 • (a : M) = a; simp)
  mul_smul h h' a := Subtype.ext (by
    show π (h * h') • (a : M) = π h • π h' • (a : M)
    simp [mul_smul])
  smul_zero h := Subtype.ext (by show π h • (0 : M) = 0; simp)
  smul_add h a b := Subtype.ext (by
    show π h • ((a : M) + (b : M)) = π h • (a : M) + π h • (b : M)
    simp [smul_add])

theorem map_subtype_fixedSub_restrict (π : H →* G) (A : AddSubgroup M)
    (hA : ∀ h : H, ∀ a ∈ A, π h • a ∈ A) (S : Set H) :
    (@fixedSub H _ A _ (restrictAction π A hA) S).map A.subtype =
      A ⊓ fixedSub M (π '' S) := by
  ext m
  simp only [AddSubgroup.mem_map, AddSubgroup.coe_subtype, AddSubgroup.mem_inf]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a.2, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have := ha s hs
    exact congrArg Subtype.val this
  · rintro ⟨hmA, hm⟩
    refine ⟨⟨m, hmA⟩, fun s hs => Subtype.ext (hm _ ⟨s, hs, rfl⟩), rfl⟩

theorem isCompl_fixedSub_restrict (π : H →* G) (W : AddSubgroup M)
    (hW : ∀ h : H, ∀ a ∈ W, π h • a ∈ W) (S₁ S₂ : Set H)
    (hsup : W = (W ⊓ fixedSub M (π '' S₁)) ⊔ (W ⊓ fixedSub M (π '' S₂)))
    (hinf : (W ⊓ fixedSub M (π '' S₁)) ⊓ (W ⊓ fixedSub M (π '' S₂)) = ⊥) :
    IsCompl (@fixedSub H _ W _ (restrictAction π W hW) S₁)
      (@fixedSub H _ W _ (restrictAction π W hW) S₂) := by
  have h1 := map_subtype_fixedSub_restrict π W hW S₁
  have h2 := map_subtype_fixedSub_restrict π W hW S₂
  have hinj : Function.Injective W.subtype := W.subtype_injective
  constructor
  · rw [disjoint_iff]
    apply AddSubgroup.map_injective hinj
    rw [AddSubgroup.map_inf _ _ _ hinj, h1, h2, AddSubgroup.map_bot]
    exact hinf
  · rw [codisjoint_iff]
    apply AddSubgroup.map_injective hinj
    rw [AddSubgroup.map_sup, h1, h2, AddSubgroup.map_top, AddSubgroup.range_subtype]
    exact hsup.symm

end Restrict

section Closure

theorem closure_subgroupOf_insert_eq_top {G : Type*} [Group G] (H L : Subgroup G) (hL : L ≤ H)
    (x : G) (hx : x ∈ H) (h : L ⊔ Subgroup.zpowers x = H) :
    Subgroup.closure ((L.subgroupOf H : Set H) ∪ {⟨x, hx⟩}) = ⊤ := by
  set S : Set H := (L.subgroupOf H : Set H) ∪ {⟨x, hx⟩} with hS
  have key : ∀ y ∈ Subgroup.closure ((L : Set G) ∪ {x}), ∃ hy : y ∈ H, (⟨y, hy⟩ : H) ∈
      Subgroup.closure S := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem z hz =>
      rcases hz with hz | hz
      · exact ⟨hL hz, Subgroup.subset_closure (Or.inl hz)⟩
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        exact ⟨hx, Subgroup.subset_closure (Or.inr rfl)⟩
    | one => exact ⟨H.one_mem, Subgroup.one_mem _⟩
    | mul y z _ _ hy hz =>
      obtain ⟨hy1, hy2⟩ := hy
      obtain ⟨hz1, hz2⟩ := hz
      exact ⟨H.mul_mem hy1 hz1, mul_mem hy2 hz2⟩
    | inv y _ hy =>
      obtain ⟨hy1, hy2⟩ := hy
      exact ⟨H.inv_mem hy1, inv_mem hy2⟩
  refine eq_top_iff.mpr fun g _ => ?_
  have hclos : Subgroup.closure ((L : Set G) ∪ {x}) = L ⊔ Subgroup.zpowers x := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, ← Subgroup.zpowers_eq_closure]
  have hg : (g : G) ∈ Subgroup.closure ((L : Set G) ∪ {x}) := by
    rw [hclos, h]; exact g.2
  obtain ⟨hg1, hg2⟩ := key g hg
  exact hg2

end Closure

end CFSG.ClassicalGroups.F2Fixed

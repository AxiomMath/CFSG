module

public import CFSG.GroupTheory.FrattiniQuotient

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.OrderReductions.FrattiniAutomorphisms
open scoped commutatorElement

theorem apply_commutator_eq_of_isCyclic {G Q : Type*} [Group G] [Group Q] [IsCyclic Q]
    (F : G → Q →* Q) (hF1 : ∀ q, F 1 q = q) (hFmul : ∀ g h q, F (g * h) q = F g (F h q))
    (g h : G) (q : Q) : F ⁅g, h⁆ q = q := by
  have hcomm : ∀ a b q, F a (F b q) = F b (F a q) := fun a b q => by
    obtain ⟨m, hm⟩ := MonoidHom.map_cyclic (F a)
    obtain ⟨m', hm'⟩ := MonoidHom.map_cyclic (F b)
    rw [hm (F b q), hm' q, hm' (F a q), hm q, ← zpow_mul, ← zpow_mul, mul_comm m' m]
  rw [commutatorElement_def, hFmul, hFmul, hFmul, hcomm h g⁻¹, ← hFmul g g⁻¹,
    ← hFmul h h⁻¹, mul_inv_cancel, mul_inv_cancel, hF1, hF1]

theorem apply_eq_of_isCyclic_of_sq {Q : Type*} [Group Q] [IsCyclic Q] (hQ : ∀ q : Q, q ^ 2 = 1)
    (f f' : Q →* Q) (hff' : ∀ q, f' (f q) = q) (q : Q) : f q = q := by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic f
  have hpow : ∀ (x : Q) (n : ℤ), x ^ n = x ^ (n % 2) := fun x n =>
    zpow_eq_zpow_emod' n (hQ x)
  rcases Int.emod_two_eq_zero_or_one m with h | h
  · have h1 : ∀ x, f x = 1 := fun x => by rw [hm, hpow, h, zpow_zero]
    have := hff' q
    rw [h1, map_one] at this
    rw [h1, ← this]
  · rw [hm, hpow, h, zpow_one]

section Factors

variable {A : Type*} [CommGroup A]

@[expose] def quotMap (M : Subgroup A) (hM : ∀ τ : MulAut A, ∀ w ∈ M, τ w ∈ M) (τ : MulAut A) :
    A ⧸ M →* A ⧸ M :=
  QuotientGroup.map M M τ.toMonoidHom fun w hw => hM τ w hw

@[expose] def subquotMap (M N : Subgroup A) (hM : ∀ τ : MulAut A, ∀ w ∈ M, τ w ∈ M)
    (hN : ∀ τ : MulAut A, ∀ w ∈ N, τ w ∈ N) (τ : MulAut A) :
    ↥M ⧸ N.subgroupOf M →* ↥M ⧸ N.subgroupOf M :=
  QuotientGroup.map (N.subgroupOf M) (N.subgroupOf M)
    ((τ.toMonoidHom.comp M.subtype).codRestrict M fun x => hM τ x x.2)
    fun x hx => hN τ (x : A) hx

variable {M N : Subgroup A} (hM : ∀ τ : MulAut A, ∀ w ∈ M, τ w ∈ M)
  (hN : ∀ τ : MulAut A, ∀ w ∈ N, τ w ∈ N)

include hM in
theorem quotMap_one (q : A ⧸ M) : quotMap M hM 1 q = q := by
  induction q using QuotientGroup.induction_on
  rfl

include hM in
theorem quotMap_mul (τ σ : MulAut A) (q : A ⧸ M) :
    quotMap M hM (τ * σ) q = quotMap M hM τ (quotMap M hM σ q) := by
  induction q using QuotientGroup.induction_on
  rfl

include hM hN in
theorem subquotMap_one (q : ↥M ⧸ N.subgroupOf M) : subquotMap M N hM hN 1 q = q := by
  induction q using QuotientGroup.induction_on
  rfl

include hM hN in
theorem subquotMap_mul (τ σ : MulAut A) (q : ↥M ⧸ N.subgroupOf M) :
    subquotMap M N hM hN (τ * σ) q = subquotMap M N hM hN τ (subquotMap M N hM hN σ q) := by
  induction q using QuotientGroup.induction_on
  rfl

include hM in
theorem apply_mul_inv_mem_of_quotMap {τ : MulAut A} (h : ∀ q, quotMap M hM τ q = q) (x : A) :
    τ x * x⁻¹ ∈ M := by
  have h1 : ((τ x : A) : A ⧸ M) = (x : A ⧸ M) := h x
  rw [QuotientGroup.eq] at h1
  have h2 := inv_mem h1
  rwa [mul_inv_rev, inv_inv, mul_comm] at h2

include hM hN in
theorem apply_mul_inv_mem_of_subquotMap {τ : MulAut A}
    (h : ∀ q, subquotMap M N hM hN τ q = q) {w : A} (hw : w ∈ M) : τ w * w⁻¹ ∈ N := by
  have h1 : (((⟨τ w, hM τ w hw⟩ : M)) : ↥M ⧸ N.subgroupOf M) = ((⟨w, hw⟩ : M) : _) :=
    h (QuotientGroup.mk ⟨w, hw⟩)
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
  have h2 := inv_mem h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
  rwa [mul_inv_rev, inv_inv, mul_comm] at h2

@[expose] def stabSubgroup (H N : Subgroup A) (hH : ∀ τ : MulAut A, ∀ w ∈ H, τ w ∈ H) :
    Subgroup (MulAut A) where
  carrier := {τ | ∀ w ∈ H, τ w * w⁻¹ ∈ N}
  one_mem' := fun w _ => by
    change w * w⁻¹ ∈ N
    rw [mul_inv_cancel]
    exact one_mem N
  mul_mem' := fun {τ σ} hτ hσ w hw => by
    have h := mul_mem (hτ (σ w) (hH σ w hw)) (hσ w hw)
    rwa [mul_assoc, inv_mul_cancel_left] at h
  inv_mem' := fun {τ} hτ w hw => by
    have hv := hτ (τ⁻¹ w) (hH τ⁻¹ w hw)
    have hw' : τ (τ⁻¹ w) = w := τ.apply_symm_apply w
    rw [hw'] at hv
    have h := inv_mem hv
    rwa [mul_inv_rev, inv_inv] at h

end Factors

section Commutators

variable {A : Type*} [CommGroup A]

theorem commutator_apply_mul_inv_mem_of_cyclic {M N : Subgroup A}
    (hM : ∀ τ : MulAut A, ∀ w ∈ M, τ w ∈ M) (hN : ∀ τ : MulAut A, ∀ w ∈ N, τ w ∈ N)
    [IsCyclic (A ⧸ M)] [IsCyclic (↥M ⧸ N.subgroupOf M)] (τ₁ τ₂ : MulAut A) :
    (∀ x, ⁅τ₁, τ₂⁆ x * x⁻¹ ∈ M) ∧ ∀ w ∈ M, ⁅τ₁, τ₂⁆ w * w⁻¹ ∈ N :=
  ⟨apply_mul_inv_mem_of_quotMap hM (apply_commutator_eq_of_isCyclic (quotMap M hM)
      (quotMap_one hM) (quotMap_mul hM) τ₁ τ₂),
    fun _ hw => apply_mul_inv_mem_of_subquotMap hM hN (apply_commutator_eq_of_isCyclic
      (subquotMap M N hM hN) (subquotMap_one hM hN) (subquotMap_mul hM hN) τ₁ τ₂) hw⟩

theorem mul_eq_mul_inv_mul {p q a b u : A} :
    p * a * (q * b)⁻¹ = (p * (b * u⁻¹)⁻¹) * (q * (a * u⁻¹)⁻¹)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem commutator_apply_mul_inv_mem_of_unipotent {M N : Subgroup A} {τ₁ τ₂ : MulAut A}
    (h₁M : ∀ x, τ₁ x * x⁻¹ ∈ M) (h₂M : ∀ x, τ₂ x * x⁻¹ ∈ M)
    (h₁N : ∀ w ∈ M, τ₁ w * w⁻¹ ∈ N) (h₂N : ∀ w ∈ M, τ₂ w * w⁻¹ ∈ N) (x : A) :
    ⁅τ₁, τ₂⁆ x * x⁻¹ ∈ N := by
  set u := τ₁⁻¹ (τ₂⁻¹ x) with hu
  have hx : x = τ₂ (τ₁ u) := by
    rw [hu]
    change x = τ₂ (τ₁ (τ₁.symm (τ₂.symm x)))
    rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  have hκ : ⁅τ₁, τ₂⁆ x = τ₁ (τ₂ u) := by
    rw [commutatorElement_def]
    rfl
  have e₁ : τ₁ (τ₂ u) = τ₁ (τ₂ u * u⁻¹) * τ₁ u := by rw [← map_mul, inv_mul_cancel_right]
  have e₂ : τ₂ (τ₁ u) = τ₂ (τ₁ u * u⁻¹) * τ₂ u := by rw [← map_mul, inv_mul_cancel_right]
  rw [hκ, hx, e₁, e₂, mul_eq_mul_inv_mul (u := u)]
  exact mul_mem (h₁N _ (h₂M u)) (inv_mem (h₂N _ (h₁M u)))

theorem derivedSeries_two_apply_mul_inv_mem {M N : Subgroup A}
    (hM : ∀ τ : MulAut A, ∀ w ∈ M, τ w ∈ M) (hN : ∀ τ : MulAut A, ∀ w ∈ N, τ w ∈ N)
    [IsCyclic (A ⧸ M)] [IsCyclic (↥M ⧸ N.subgroupOf M)] {τ : MulAut A}
    (hτ : τ ∈ derivedSeries (MulAut A) 2) (x : A) : τ x * x⁻¹ ∈ N := by
  have htop : ∀ σ : MulAut A, ∀ w ∈ (⊤ : Subgroup A), σ w ∈ (⊤ : Subgroup A) :=
    fun _ _ _ => Subgroup.mem_top _
  set U := stabSubgroup ⊤ M htop ⊓ stabSubgroup M N hM
  have hU : derivedSeries (MulAut A) 1 ≤ U := by
    rw [derivedSeries_one, _root_.commutator_def, Subgroup.commutator_le]
    intro τ₁ _ τ₂ _
    obtain ⟨h1, h2⟩ := commutator_apply_mul_inv_mem_of_cyclic hM hN τ₁ τ₂
    exact Subgroup.mem_inf.2 ⟨fun w _ => h1 w, h2⟩
  have hW : derivedSeries (MulAut A) 2 ≤ stabSubgroup ⊤ N htop := by
    rw [derivedSeries_succ]
    refine (Subgroup.commutator_mono hU hU).trans (Subgroup.commutator_le.2 ?_)
    intro τ₁ hτ₁ τ₂ hτ₂ w _
    obtain ⟨h₁M, h₁N⟩ := Subgroup.mem_inf.1 hτ₁
    obtain ⟨h₂M, h₂N⟩ := Subgroup.mem_inf.1 hτ₂
    exact commutator_apply_mul_inv_mem_of_unipotent (fun x => h₁M x (Subgroup.mem_top x))
      (fun x => h₂M x (Subgroup.mem_top x)) h₁N h₂N w
  exact hW hτ x (Subgroup.mem_top x)

theorem sq_apply_mul_inv_mem {M N : Subgroup A}
    (hM : ∀ τ : MulAut A, ∀ w ∈ M, τ w ∈ M) (hN : ∀ τ : MulAut A, ∀ w ∈ N, τ w ∈ N)
    [IsCyclic (A ⧸ M)] [IsCyclic (↥M ⧸ N.subgroupOf M)] (hM2 : ∀ w ∈ M, w ^ 2 = 1)
    (hQ1 : ∀ q : A ⧸ M, q ^ 2 = 1) (hQ2 : ∀ q : ↥M ⧸ N.subgroupOf M, q ^ 2 = 1)
    (τ : MulAut A) (x : A) : (τ * τ) x * x⁻¹ ∈ N := by
  have h1 : ∀ y, τ y * y⁻¹ ∈ M := apply_mul_inv_mem_of_quotMap hM fun q =>
    apply_eq_of_isCyclic_of_sq hQ1 (quotMap M hM τ) (quotMap M hM τ⁻¹)
      (fun q => by rw [← quotMap_mul hM, inv_mul_cancel, quotMap_one hM]) q
  have h2 : ∀ w ∈ M, τ w * w⁻¹ ∈ N := fun _ hw => apply_mul_inv_mem_of_subquotMap hM hN
    (fun q => apply_eq_of_isCyclic_of_sq hQ2 (subquotMap M N hM hN τ)
      (subquotMap M N hM hN τ⁻¹)
      (fun q => by rw [← subquotMap_mul hM hN, inv_mul_cancel, subquotMap_one hM hN]) q) hw
  set n := τ x * x⁻¹ with hn
  have hnM : n ∈ M := h1 x
  have e : (τ * τ) x * x⁻¹ = (τ n * n⁻¹) * n ^ 2 := by
    have hτx : τ x = n * x := by rw [hn, inv_mul_cancel_right]
    change τ (τ x) * x⁻¹ = _
    rw [hτx, map_mul]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, hn]
    abel
  rw [e, hM2 n hnM, mul_one]
  exact h2 n hnM

end Commutators

section Structure

variable {p : ℕ} [hp : Fact p.Prime] {A : Type*} [CommGroup A]

theorem ofAdd_eq_pow_val {n : ℕ} [NeZero n] (x : ZMod n) :
    Multiplicative.ofAdd x = Multiplicative.ofAdd (1 : ZMod n) ^ x.val := by
  rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val]

theorem ofAdd_pow_card {n : ℕ} (x : ZMod n) : Multiplicative.ofAdd x ^ n = 1 := by
  rw [← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]

omit hp in
theorem pow_ker_range_le :
    (powMonoidHom p : A →* A).range ≤ (powMonoidHom p : A →* A).ker ↔
      ∀ x : A, x ^ (p * p) = 1 := by
  constructor
  · intro h x
    have := h ⟨x, rfl⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply, powMonoidHom_apply, ← pow_mul] at this
    exact this
  · rintro h _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply, powMonoidHom_apply, ← pow_mul]
    exact h x

omit hp in
theorem mem_ker_powMonoidHom_of_mulEquiv (τ : MulAut A) {w : A}
    (hw : w ∈ (powMonoidHom p : A →* A).ker) : τ w ∈ (powMonoidHom p : A →* A).ker := by
  rw [MonoidHom.mem_ker, powMonoidHom_apply] at hw ⊢
  rw [← map_pow, hw, map_one]

omit hp in
theorem mem_range_powMonoidHom_of_mulEquiv (τ : MulAut A) {w : A}
    (hw : w ∈ (powMonoidHom p : A →* A).range) : τ w ∈ (powMonoidHom p : A →* A).range := by
  obtain ⟨y, rfl⟩ := hw
  exact ⟨τ y, by rw [powMonoidHom_apply, powMonoidHom_apply, map_pow]⟩

variable (e : A ≃* Multiplicative (ZMod (p ^ 2)) × Multiplicative (ZMod p))
include e

theorem eq_mul_of_mulEquiv_prod (a : A) :
    a = e.symm (Multiplicative.ofAdd 1, 1) ^ (Multiplicative.toAdd (e a).1).val *
      e.symm (1, Multiplicative.ofAdd 1) ^ (Multiplicative.toAdd (e a).2).val := by
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.out.ne_zero⟩
  have : NeZero p := ⟨hp.out.ne_zero⟩
  apply e.injective
  rw [map_mul, map_pow, map_pow, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_mul, Prod.pow_fst, one_pow, mul_one]
    rw [← ofAdd_eq_pow_val, ofAdd_toAdd]
  · simp only [Prod.snd_mul, Prod.pow_snd, one_pow, one_mul]
    rw [← ofAdd_eq_pow_val, ofAdd_toAdd]

theorem pow_mul_self_eq_one_of_mulEquiv_prod (x : A) : x ^ (p * p) = 1 := by
  apply e.injective
  rw [map_pow, map_one]
  refine Prod.ext ?_ ?_
  · rw [Prod.pow_fst, Prod.fst_one, ← sq, ← ofAdd_toAdd (e x).1, ofAdd_pow_card]
  · rw [Prod.pow_snd, Prod.snd_one, pow_mul, ← ofAdd_toAdd (e x).2, ofAdd_pow_card, one_pow]

theorem symm_one_ofAdd_mem_ker :
    e.symm (1, Multiplicative.ofAdd 1) ∈ (powMonoidHom p : A →* A).ker := by
  rw [MonoidHom.mem_ker, powMonoidHom_apply, ← map_pow, Prod.pow_mk, one_pow, ofAdd_pow_card,
    Prod.mk_one_one, map_one]

theorem isCyclic_quotient_ker_powMonoidHom :
    IsCyclic (A ⧸ (powMonoidHom p : A →* A).ker) := by
  refine ⟨⟨(e.symm (Multiplicative.ofAdd 1, 1) : A ⧸ (powMonoidHom p : A →* A).ker), ?_⟩⟩
  intro q
  induction q using QuotientGroup.induction_on with
  | H a =>
    have hae := eq_mul_of_mulEquiv_prod e a
    generalize Multiplicative.toAdd (e a).1 = c at hae
    generalize Multiplicative.toAdd (e a).2 = d at hae
    refine ⟨c.val, ?_⟩
    have h2 : ((e.symm (1, Multiplicative.ofAdd 1) : A) :
        A ⧸ (powMonoidHom p : A →* A).ker) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (symm_one_ofAdd_mem_ker e)
    beta_reduce
    rw [zpow_natCast, hae, QuotientGroup.mk_mul, QuotientGroup.mk_pow, QuotientGroup.mk_pow, h2,
      one_pow, mul_one]

theorem isCyclic_ker_quotient_range_powMonoidHom :
    IsCyclic (↥(powMonoidHom p : A →* A).ker ⧸
      (powMonoidHom p : A →* A).range.subgroupOf (powMonoidHom p : A →* A).ker) := by
  have hp0 := hp.out.pos
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.out.ne_zero⟩
  refine ⟨⟨((⟨_, symm_one_ofAdd_mem_ker e⟩ : (powMonoidHom p : A →* A).ker) : _), ?_⟩⟩
  intro q
  induction q using QuotientGroup.induction_on with
  | H w =>
    have hw : (w : A) ^ p = 1 := w.2
    have hwe := eq_mul_of_mulEquiv_prod e (w : A)
    have h1 : p • Multiplicative.toAdd (e w).1 = 0 := by
      have := congrArg (fun z => Multiplicative.toAdd (e z).1) hw
      simp only [map_pow, Prod.pow_fst, map_one, Prod.fst_one, toAdd_pow, toAdd_one] at this
      exact this
    generalize Multiplicative.toAdd (e w).1 = c at hwe h1
    generalize Multiplicative.toAdd (e w).2 = d at hwe
    have hdvd : p ∣ c.val := by
      have h1' : ((p * c.val : ℕ) : ZMod (p ^ 2)) = 0 := by
        rw [Nat.cast_mul, ZMod.natCast_zmod_val, ← nsmul_eq_mul]
        exact h1
      rw [ZMod.natCast_eq_zero_iff] at h1'
      generalize c.val = k at h1' ⊢
      rw [sq] at h1'
      exact Nat.dvd_of_mul_dvd_mul_left hp0 h1'
    obtain ⟨m, hm⟩ := hdvd
    refine ⟨d.val, ?_⟩
    beta_reduce
    rw [zpow_natCast, ← QuotientGroup.mk_pow, QuotientGroup.eq, Subgroup.mem_subgroupOf,
      Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, hwe, mul_comm (_ ^ c.val),
      inv_mul_cancel_left, hm]
    exact ⟨e.symm (Multiplicative.ofAdd 1, 1) ^ m, by rw [powMonoidHom_apply, ← pow_mul,
      mul_comm]⟩

end Structure

theorem tits_unequal_cyclic_abelianization_automorphisms {p : ℕ} [hp : Fact p.Prime] {S : Type*}
    [Group S] [Finite S] (hS : IsPGroup p S)
    (e : Abelianization S ≃* Multiplicative (ZMod (p ^ 2)) × Multiplicative (ZMod p)) :
    IsPGroup p (derivedSeries (MulAut S) 2) ∧ Group.IsSolvable (MulAut S) ∧
      (p = 2 → IsPGroup 2 (MulAut S)) := by
  classical
  have hM : ∀ τ : MulAut (Abelianization S), ∀ w ∈ (powMonoidHom p).ker, τ w ∈
      (powMonoidHom p : Abelianization S →* Abelianization S).ker :=
    fun τ _ hw => mem_ker_powMonoidHom_of_mulEquiv τ hw
  have hN : ∀ τ : MulAut (Abelianization S), ∀ w ∈ (powMonoidHom p).range, τ w ∈
      (powMonoidHom p : Abelianization S →* Abelianization S).range :=
    fun τ _ hw => mem_range_powMonoidHom_of_mulEquiv τ hw
  have := isCyclic_quotient_ker_powMonoidHom e
  have := isCyclic_ker_quotient_range_powMonoidHom e
  have hNM := (pow_ker_range_le (p := p) (A := Abelianization S)).2
    (pow_mul_self_eq_one_of_mulEquiv_prod e)
  obtain ⟨-, hcomm, hpow, -, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hS
  have hS'Φ : commutator S ≤ frattini S := by
    have := Abelianization.commutator_subset_ker (QuotientGroup.mk' (frattini S))
    rwa [QuotientGroup.ker_mk'] at this
  have hpΦ : ∀ t : S, t ^ p ∈ frattini S := fun t => by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hpow _
  have : (commutator S).Characteristic := by
    rw [commutator_def]
    infer_instance
  let ψ : MulAut S →* MulAut (Abelianization S) := quotientAutomorphism (commutator S)
  have hψ : ∀ (σ : MulAut S) (s : S),
      ψ σ (Abelianization.of s) = Abelianization.of (σ s) :=
    fun σ s => quotientEquivalence_apply (commutator S) σ s
  have hker : ∀ σ : MulAut S, (∀ x, ψ σ x * x⁻¹ ∈
      (powMonoidHom p : Abelianization S →* Abelianization S).range) →
      σ ∈ (quotientAutomorphism (frattini S)).ker := by
    intro σ hσ
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H s =>
      change quotientEquivalence (frattini S) σ (QuotientGroup.mk' _ s) = QuotientGroup.mk' _ s
      rw [quotientEquivalence_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]
      obtain ⟨y, hy⟩ := hσ (Abelianization.of s)
      obtain ⟨t, ht⟩ : ∃ t : S, Abelianization.of t = y := QuotientGroup.mk_surjective y
      rw [← ht, hψ, powMonoidHom_apply, ← map_pow, ← map_inv, ← map_mul] at hy
      have h1 : (t ^ p)⁻¹ * (σ s * s⁻¹) ∈ commutator S := QuotientGroup.eq.1 hy
      have h2 := mul_mem (hpΦ t) (hS'Φ h1)
      rwa [mul_inv_cancel_left] at h2
  have hD : derivedSeries (MulAut S) 2 ≤ (quotientAutomorphism (frattini S)).ker :=
    fun σ hσ => hker σ fun x => derivedSeries_two_apply_mul_inv_mem hM hN
      (map_derivedSeries_le_derivedSeries ψ 2 ⟨σ, hσ, rfl⟩) x
  have hker2 := (CFSG.GroupTheory.frattini_automorphism_kernel hS).2
  have hpg : IsPGroup p (derivedSeries (MulAut S) 2) := hker2.to_le hD
  have : Finite (MulAut S) := Finite.of_injective (fun σ : MulAut S => (σ : S → S))
    fun σ τ h => MulEquiv.ext (congrFun h)
  have hsolv : Group.IsSolvable (MulAut S) := by
    have : Group.IsNilpotent (derivedSeries (MulAut S) 2) := hpg.isNilpotent
    have hQ : Group.IsSolvable (MulAut S ⧸ derivedSeries (MulAut S) 2) := by
      refine (Group.isSolvable_def _).2 ⟨2, ?_⟩
      rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective (derivedSeries (MulAut S) 2)) 2,
        Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact Group.isSolvable_of_ker_le_range (derivedSeries (MulAut S) 2).subtype
      (QuotientGroup.mk' (derivedSeries (MulAut S) 2))
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  refine ⟨hpg, hsolv, ?_⟩
  rintro rfl
  intro σ
  have hsq : σ * σ ∈ (quotientAutomorphism (frattini S)).ker := hker (σ * σ) fun x => by
    rw [map_mul]
    refine sq_apply_mul_inv_mem hM hN (fun w hw => hw) (fun q => ?_) (fun q => ?_) (ψ σ) x
    · induction q using QuotientGroup.induction_on with
      | H a =>
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
        exact hNM ⟨a, rfl⟩
    · induction q using QuotientGroup.induction_on with
      | H w =>
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
          Subgroup.coe_pow]
        exact ⟨(w : Abelianization S), rfl⟩
  obtain ⟨k, hk⟩ := hker2 ⟨σ * σ, hsq⟩
  refine ⟨k + 1, ?_⟩
  have h := congrArg Subtype.val hk
  simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h
  rw [pow_succ', pow_mul, sq]
  exact h

end CFSG.LieType.Ree

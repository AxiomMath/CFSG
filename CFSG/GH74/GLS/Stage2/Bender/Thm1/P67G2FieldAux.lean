module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67CoreTools

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem five_le_of_ne_three {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) : 5 ≤ p := by
  have h2 := hp.two_le
  have h4 : p ≠ 4 := by
    rintro rfl
    exact absurd hp (by decide)
  omega


theorem dvd_of_forall_pow_prime_pow_eq {p d j : ℕ} (hp : p.Prime) (L : Type) [Field L] [Finite L]
    (hL : Nat.card L = p ^ d) (h : ∀ x : L, x ^ p ^ j = x) : d ∣ j := by
  classical
  have := Fintype.ofFinite L
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · subst h0
      have h0' : Nat.card L = 1 := by rw [hL]; rfl
      have h1 : 1 < Nat.card L := Finite.one_lt_card
      omega
    · exact h0
  have hq : ∀ x : L, x ^ p ^ d = x := fun x => by
    rw [← hL, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  have hnm : ∀ m : ℕ, ∀ x : L, x ^ p ^ (d * m) = x := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [Nat.mul_succ, pow_add, pow_mul, ih, hq]
  set r := j % d with hr
  have hrx : ∀ x : L, x ^ p ^ r = x := by
    intro x
    have hk : j = d * (j / d) + r := (Nat.div_add_mod j d).symm
    have h1 := h x
    rw [hk, pow_add, pow_mul, hnm] at h1
    exact h1
  by_contra hdvd
  have hr0 : 0 < r := Nat.pos_of_ne_zero fun h0 => hdvd (Nat.dvd_of_mod_eq_zero h0)
  have hrn : r < d := Nat.mod_lt _ hd
  have h3r : 2 ≤ p ^ r := (Nat.le_self_pow (by omega) p).trans' hp.two_le
  set P : Polynomial L := Polynomial.X ^ p ^ r - Polynomial.X with hP
  have hdeg : P.natDegree = p ^ r := by
    rw [hP, Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;>
      simp only [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
    omega
  have hP0 : P = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
      (f := fun x : L => x) (fun _ _ h => h) (fun x => ?_) ?_
    · simp [hP, hrx x]
    · rw [hdeg, ← Nat.card_eq_fintype_card, hL]
      exact Nat.pow_lt_pow_right hp.one_lt hrn
  have hc : P.coeff (p ^ r) = 1 := by
    simp only [hP, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X,
      show (1 : ℕ) ≠ p ^ r by omega, ↓reduceIte, sub_zero]
  rw [hP0, Polynomial.coeff_zero] at hc
  exact zero_ne_one hc

theorem eq_bot_of_normal_abelian_of_isQuasisimple {Q : Type*} [Group Q]
    (hQ : CFSG.IsQuasisimple Q) (hZ : Subgroup.center Q = ⊥) (N : Subgroup Q) [N.Normal]
    (hN : ∀ x y : N, x * y = y * x) : N = ⊥ := by
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hQ N with h | h
  · rwa [hZ, le_bot_iff] at h
  · exfalso
    obtain ⟨-, -, a, b, hab⟩ := hQ
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    have ha : a' ∈ N := h ▸ Subgroup.mem_top a'
    have hb : b' ∈ N := h ▸ Subgroup.mem_top b'
    apply hab
    have h1 : a' * b' = b' * a' := congrArg Subtype.val (hN ⟨a', ha⟩ ⟨b', hb⟩)
    change ((a' * b' : Q) : Q ⧸ Subgroup.center Q) = ((b' * a' : Q) : Q ⧸ Subgroup.center Q)
    rw [h1]

theorem noAbelNormal_of_equiv {F F' : Type*} [Group F] [Group F'] (e : F ≃* F')
    (h' : ∀ N : Subgroup F', N.Normal → (∀ x y : N, x * y = y * x) → N = ⊥) :
    ∀ N : Subgroup F, N.Normal → (∀ x y : N, x * y = y * x) → N = ⊥ := by
  intro N hN hc
  have := h' (N.map e.toMonoidHom) (hN.map _ e.surjective) (by
    rintro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hc ⟨x, hx⟩ ⟨y, hy⟩))
  exact (Subgroup.map_eq_bot_iff_of_injective N e.injective).1 this

variable {K : Type} [Field K] [Finite K]

theorem fixSub_conj_equiv {Y : Type} [Group Y] (φ δ : MulAut Y) :
    Nonempty (↥(fixSub φ) ≃* ↥(fixSub (δ * φ * δ⁻¹))) := by
  have h : (fixSub φ).map δ.toMonoidHom = fixSub (δ * φ * δ⁻¹) := by
    have := fixSub_congr δ φ
    rw [this]
    rfl
  exact ⟨(Subgroup.equivMapOfInjective _ δ.toMonoidHom δ.injective).trans
    (MulEquiv.subgroupCongr h)⟩

omit [Finite K] in
theorem card_fixSubfield {p f r : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    {τ : K ≃+* K} (hτ : orderOf τ = r) : Nat.card (fixSubfield τ) = p ^ (f / r) := by
  obtain ⟨-, -, -, -, -, hsub⟩ := finite_field_automorphism_fixed_field_cardinality hp hf hK
  obtain ⟨-, S, hS, hSc⟩ := hsub (Subgroup.zpowers τ)
  have hcard : Nat.card (Subgroup.zpowers τ) = r := by rw [Nat.card_zpowers, hτ]
  have hSeq : S = fixSubfield τ := by
    ext a
    have h1 : a ∈ S ↔ ∀ τ' ∈ Subgroup.zpowers τ, τ' a = a := by
      have := congrArg (fun T : Set K => a ∈ T) hS
      simpa using this
    rw [h1, mem_fixSubfield]
    constructor
    · intro h
      exact h τ (Subgroup.mem_zpowers τ)
    · intro h τ' hτ'
      obtain ⟨k, rfl⟩ := hτ'
      have hinv : τ⁻¹ a = a := by
        have := congrArg (fun y => τ⁻¹ y) h
        simpa using this.symm
      induction k using Int.induction_on with
      | zero => simp
      | succ n ih =>
        have ih' : (τ ^ (n : ℤ)) a = a := ih
        show (τ ^ ((n : ℤ) + 1)) a = a
        rw [zpow_add_one, RingAut.mul_apply, h, ih']
      | pred n ih =>
        have ih' : (τ ^ (-(n : ℤ))) a = a := ih
        show (τ ^ (-(n : ℤ) - 1)) a = a
        rw [zpow_sub_one, RingAut.mul_apply, hinv, ih']
  rw [← hSeq, hSc, hcard]


end CFSG.GH74.GLS.Stage2.Bender.Thm1

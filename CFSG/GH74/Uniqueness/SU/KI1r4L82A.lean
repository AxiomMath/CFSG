module

public import CFSG.GH74.Uniqueness.SU.KI1r3PowB
public import CFSG.Goldschmidt.Steps.Sec89b

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4.L82

open Subgroup CFSG.GH74.Uniqueness.SU.K.R3.Pow CFSG.OrderReductions.FrattiniAutomorphisms
open scoped commutatorElement

@[expose] def fixSub {M : Type*} [Group M] (τ : MulAut M) : Subgroup M where
  carrier := {m | τ m = m}
  mul_mem' := fun {a b} (ha : τ a = a) (hb : τ b = b) => by
    show τ (a * b) = a * b
    rw [map_mul, ha, hb]
  one_mem' := map_one τ
  inv_mem' := fun {a} (ha : τ a = a) => by
    show τ a⁻¹ = a⁻¹
    rw [map_inv, ha]

theorem mem_fixSub {M : Type*} [Group M] {τ : MulAut M} {m : M} : m ∈ fixSub τ ↔ τ m = m :=
  Iff.rfl

theorem card_fix_sq_elem {V : Type} [Group V] [Finite V] (hcomm : ∀ a b : V, a * b = b * a)
    (hsq : ∀ a : V, a * a = 1) (σ τ : MulAut V) (hτ : τ ^ 2 = 1)
    (hστ : τ * σ * τ⁻¹ = σ⁻¹) (hfix : ∀ v, σ v = v → v = 1) :
    Nat.card (fixSub τ) ^ 2 = Nat.card V := by
  have hττ : ∀ v, τ (τ v) = v := fun v => by
    have h2 : (τ * τ) v = v := by rw [← pow_two, hτ]; rfl
    exact h2
  let f : V →* V := MonoidHom.mk' (fun v => v * τ v) (by
    intro a b
    simp only [map_mul]
    calc a * b * (τ a * τ b) = a * (b * τ a) * τ b := by group
      _ = a * (τ a * b) * τ b := by rw [hcomm b (τ a)]
      _ = a * τ a * (b * τ b) := by group)
  have hker : f.ker = fixSub τ := by
    ext v
    rw [MonoidHom.mem_ker, mem_fixSub]
    show v * τ v = 1 ↔ τ v = v
    constructor
    · intro h
      have h1 : τ v = v⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [h1]
      exact inv_eq_of_mul_eq_one_right (hsq v)
    · intro h
      rw [h]; exact hsq v
  have hrange : f.range = fixSub τ := by
    ext v
    rw [MonoidHom.mem_range, mem_fixSub]
    constructor
    · rintro ⟨w, rfl⟩
      show τ (w * τ w) = w * τ w
      rw [map_mul, hττ, hcomm]
    · intro hv
      obtain ⟨w, hw⟩ := exists_eq_mul_map_of_fixed hcomm hsq σ τ hτ hστ hfix v hv
      exact ⟨w, hw.symm⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have h2 : Nat.card (V ⧸ f.ker) = Nat.card f.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  rw [h2, hker, hrange] at h1
  rw [h1, sq]

variable {M : Type} [Group M] [Finite M]

theorem exists_fixed_mul (hM : IsPGroup 2 M) {σ τ : MulAut M} {k : ℕ} (h : DihAct σ τ k)
    (N : Subgroup M) [N.Characteristic] (r : M) (hr : r⁻¹ * τ r ∈ N) :
    ∃ d ∈ N, τ (r * d) = r * d := by
  have hΦ := coboundary_aux (Nat.card N) N rfl (hM.to_subgroup N) _ _ k (h.restrict N)
  have hyτ : (⟨r⁻¹ * τ r, hr⟩ : N) *
      MulAut.characteristic N τ ⟨r⁻¹ * τ r, hr⟩ = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, MulAut.characteristic_apply_apply_coe, map_mul, map_inv,
      h.tau_tau, OneMemClass.coe_one]
    group
  obtain ⟨d, hd⟩ := hΦ _ hyτ
  have hd' : r⁻¹ * τ r = (d : M) * (τ (d : M))⁻¹ := by
    have := congrArg Subtype.val hd
    simpa using this
  refine ⟨d, d.2, ?_⟩
  rw [map_mul]
  calc τ r * τ d = r * (r⁻¹ * τ r) * (τ d) := by group
    _ = r * ((d : M) * (τ (d : M))⁻¹) * τ d := by rw [hd']
    _ = r * d := by group

@[expose] def resΦ (τ : MulAut M) : ↥(fixSub τ) →* M ⧸ frattini M :=
  (QuotientGroup.mk' (frattini M)).comp (fixSub τ).subtype

theorem range_resΦ (hM : IsPGroup 2 M) {σ τ : MulAut M} {k : ℕ} (h : DihAct σ τ k) :
    (resΦ τ).range = fixSub (bar τ) := by
  ext v
  rw [MonoidHom.mem_range, mem_fixSub]
  constructor
  · rintro ⟨⟨c, hc⟩, rfl⟩
    show bar τ (c : M ⧸ frattini M) = c
    rw [bar_mk]
    have : τ c = c := hc
    rw [this]
  · intro hv
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective v
    rw [bar_mk] at hv
    have hr : r⁻¹ * τ r ∈ frattini M := QuotientGroup.eq.mp hv.symm
    obtain ⟨d, hd, hτd⟩ := exists_fixed_mul hM h (frattini M) r hr
    refine ⟨⟨r * d, hτd⟩, ?_⟩
    show ((r * d : M) : M ⧸ frattini M) = r
    rw [QuotientGroup.mk_mul]
    have : ((d : M) : M ⧸ frattini M) = 1 := (QuotientGroup.eq_one_iff d).mpr hd
    rw [this, mul_one]

theorem card_fixSub_sq : ∀ (n : ℕ) (M : Type) [Group M] [Finite M], Nat.card M = n →
    IsPGroup 2 M → ∀ (σ τ : MulAut M) (k : ℕ), DihAct σ τ k →
      Nat.card (fixSub τ) ^ 2 = Nat.card M := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M _ _ hn hM σ τ k h
    by_cases hsub : Subsingleton M
    · have h1 : Nat.card M = 1 := Nat.card_of_subsingleton 1
      have h2 : Nat.card (fixSub τ) = 1 := Nat.card_of_subsingleton 1
      rw [h1, h2]
      norm_num
    · have hnt : Nontrivial M := not_subsingleton_iff_nontrivial.mp hsub
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hne : frattini M ≠ ⊤ := by
        intro htop
        have := frattini_nongenerating (G := M) (K := ⊥) (by rw [htop]; simp)
        exact bot_ne_top this
      have hlt : Nat.card (frattini M) < n := by
        rw [← hn]
        have h1 := Subgroup.one_lt_index_of_ne_top hne
        have h2 := (frattini M).card_mul_index
        have h3 : 0 < Nat.card (frattini M) := Nat.card_pos
        nlinarith
      have hΦ := ih _ hlt (frattini M) rfl (hM.to_subgroup _) _ _ k (h.restrict (frattini M))
      obtain ⟨hcomm, hsq⟩ := quot_comm_sq hM
      have hrange : (resΦ τ).range = fixSub (bar τ) := range_resΦ hM h
      set res := resΦ τ with hres
      have hker : Nat.card res.ker =
          Nat.card (fixSub (MulAut.characteristic (frattini M) τ)) := by
        refine Nat.card_congr ?_
        have key : ∀ c : res.ker, (c.1.1 : M) ∈ frattini M := fun c => by
          have := c.2
          rw [MonoidHom.mem_ker] at this
          exact (QuotientGroup.eq_one_iff _).mp this
        have key2 : ∀ d : fixSub (MulAut.characteristic (frattini M) τ),
            τ ((d.1 : frattini M) : M) = ((d.1 : frattini M) : M) := fun d => by
          have := congrArg Subtype.val d.2
          simpa using this
        refine
          { toFun := fun c => ⟨⟨(c.1.1 : M), key c⟩, ?_⟩
            invFun := fun d => ⟨⟨((d.1 : frattini M) : M), key2 d⟩, ?_⟩
            left_inv := fun c => rfl
            right_inv := fun d => rfl }
        · apply Subtype.ext
          have h1 : τ (c.1.1 : M) = c.1.1 := c.1.2
          simpa using h1
        · rw [MonoidHom.mem_ker]
          exact (QuotientGroup.eq_one_iff _).mpr d.1.2
      have hrange_card : Nat.card res.range = Nat.card (fixSub (bar τ)) := by rw [hrange]
      have hbar2 : (bar τ) ^ 2 = 1 := by rw [← map_pow, h.sq, map_one]
      have hbarinv : bar τ * bar σ * (bar τ)⁻¹ = (bar σ)⁻¹ := by
        have := congrArg (quotientAutomorphism (frattini M)) h.inv
        simpa [map_mul, map_inv] using this
      have hV := card_fix_sq_elem hcomm hsq (bar σ) (bar τ) hbar2 hbarinv (bar_fix hM h)
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup res.ker
      have h2 : Nat.card (↥(fixSub τ) ⧸ res.ker) = Nat.card res.range :=
        Nat.card_congr (QuotientGroup.quotientKerEquivRange res).toEquiv
      rw [h2, hker] at h1
      have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini M)
      calc Nat.card (fixSub τ) ^ 2
          = (Nat.card res.range *
              Nat.card (fixSub (MulAut.characteristic (frattini M) τ))) ^ 2 := by
            rw [← h1]
        _ = Nat.card (fixSub (bar τ)) ^ 2 *
            Nat.card (fixSub (MulAut.characteristic (frattini M) τ)) ^ 2 := by
            rw [hrange_card, mul_pow]
        _ = Nat.card (M ⧸ frattini M) * Nat.card (frattini M) := by rw [hV, hΦ]
        _ = Nat.card M := h3.symm

section ClassTwo

variable {σ τ : MulAut M}

omit [Finite M] in
theorem dihAct_cube (h : DihAct σ τ 1) (q : M) : σ (σ (σ q)) = q := by
  have h1 : σ ^ 3 = 1 := by simpa using h.pow
  have h3 : (σ ^ 3) q = q := by rw [h1]; rfl
  exact h3

theorem prod_sigma (h : DihAct σ τ 1) (q : M) : q * σ q * σ (σ q) = 1 := by
  have hFPF : MonoidHom.FixedPointFree (fun q : M => σ q) := fun q hq => h.fix q hq
  have hphi_period : (fun q : M => σ q)^[3] = id := by
    ext q
    simpa [Function.iterate_succ_apply] using dihAct_cube h q
  have hnorm := MonoidHom.FixedPointFree.prod_pow_eq_one hFPF hphi_period q
  simpa [Function.iterate_succ_apply, mul_assoc] using hnorm

theorem commutator_central (h : DihAct σ τ 1) (a b g : M) : Commute ⁅a, b⁆ g := by
  have := CFSG.Goldschmidt.Sec89.commute_kappa_of_fixedPointFree σ h.fix (dihAct_cube h) a⁻¹ b⁻¹ g
  simpa [commutatorElement_def] using this

theorem commute_sigma (h : DihAct σ τ 1) (q : M) : Commute q (σ q) := by
  have hq := prod_sigma h q
  have hqq := prod_sigma h (q * σ q)
  simp only [map_mul] at hqq
  rw [dihAct_cube h] at hqq
  have hc : σ (σ q) = (q * σ q)⁻¹ := eq_inv_of_mul_eq_one_right hq
  rw [hc] at hqq
  group at hqq
  rw [commute_iff_eq]
  have hconj : q * σ q * q⁻¹ = σ q := by
    apply mul_inv_eq_one.mp
    simpa [mul_assoc] using hqq
  exact mul_inv_eq_iff_eq_mul.mp hconj

end ClassTwo

end CFSG.GH74.Uniqueness.SU.K.R4.L82

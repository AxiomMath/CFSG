module

public import CFSG.GH74.Uniqueness.SU.KI1r3PowA
public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core

public section

namespace CFSG.GH74.Uniqueness.SU.K.R3.Pow

open CFSG.OrderReductions.FrattiniAutomorphisms CFSG.OrderReductions.FixedPointLifting

structure DihAct {M : Type*} [Group M] (σ τ : MulAut M) (k : ℕ) : Prop where
  pow : σ ^ 3 ^ k = 1
  sq : τ ^ 2 = 1
  inv : τ * σ * τ⁻¹ = σ⁻¹
  fix : ∀ x, σ x = x → x = 1

namespace DihAct

variable {M : Type*} [Group M] {σ τ : MulAut M} {k : ℕ}

theorem tau_tau (h : DihAct σ τ k) (a : M) : τ (τ a) = a := by
  have h2 : (τ * τ) a = a := by rw [← pow_two, h.sq]; rfl
  exact h2

theorem restrict (h : DihAct σ τ k) (H : Subgroup M) [H.Characteristic] :
    DihAct (MulAut.characteristic H σ) (MulAut.characteristic H τ) k where
  pow := by rw [← map_pow, h.pow, map_one]
  sq := by rw [← map_pow, h.sq, map_one]
  inv := by
    have := congrArg (MulAut.characteristic H) h.inv
    simpa [map_mul, map_inv] using this
  fix x hx := by
    apply Subtype.ext
    have hx' : σ (x : M) = x := by
      have := congrArg Subtype.val hx
      simpa using this
    exact h.fix _ hx'

end DihAct

section Quot

variable {M : Type} [Group M] [Finite M]

noncomputable abbrev bar (σ : MulAut M) : MulAut (M ⧸ frattini M) :=
  quotientAutomorphism (frattini M) σ

omit [Finite M] in
theorem bar_mk (σ : MulAut M) (a : M) :
    bar σ (a : M ⧸ frattini M) = ((σ a : M) : M ⧸ frattini M) :=
  quotientAutomorphism_apply (frattini M) σ a

theorem quot_comm_sq (hM : IsPGroup 2 M) :
    (∀ a b : M ⧸ frattini M, a * b = b * a) ∧ ∀ a : M ⧸ frattini M, a * a = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hc, hp, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hM
  exact ⟨fun a b => mul_comm' a b, fun a => by rw [← pow_two]; exact hp a⟩

theorem bar_fix (hM : IsPGroup 2 M) {σ τ : MulAut M} {k : ℕ} (h : DihAct σ τ k) :
    ∀ v : M ⧸ frattini M, bar σ v = v → v = 1 := by
  intro v hv
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf σ ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one h.pow
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hord
  have hact : IsPGroup 3 (Subgroup.zpowers σ) :=
    IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hΦcard : ¬ 3 ∣ Nat.card (QuotientGroup.mk' (frattini M)).ker := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp (hM.to_subgroup (frattini M))
    rw [hn]
    intro h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  obtain ⟨r, hrv, hr⟩ := exists_fixed_lift_of_coprime_kernel 3 hact (Subgroup.zpowers σ).subtype
    ((quotientAutomorphism (frattini M)).comp (Subgroup.zpowers σ).subtype)
    (QuotientGroup.mk' (frattini M)) (QuotientGroup.mk'_surjective _) hΦcard
    (fun a x => (quotientAutomorphism_apply (frattini M) a.1 x).symm) v (by
      intro a
      have hstab : bar σ ∈ MulAction.stabilizer (MulAut (M ⧸ frattini M)) v := hv
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
      have hz := Subgroup.zpow_mem _ hstab i
      show (quotientAutomorphism (frattini M) a.1) v = v
      rw [← hi, map_zpow]
      exact hz)
  have : r = 1 := h.fix r (hr ⟨σ, Subgroup.mem_zpowers σ⟩)
  rw [← hrv, this, map_one]

end Quot

section Lift

variable {M : Type} [Group M] [Finite M]

theorem exists_coboundary_of_frattini (hM : IsPGroup 2 M) {σ τ : MulAut M} {k : ℕ}
    (h : DihAct σ τ k)
    (hΦ : ∀ y : frattini M, y * MulAut.characteristic (frattini M) τ y = 1 →
      ∃ d : frattini M, y = d * (MulAut.characteristic (frattini M) τ d)⁻¹)
    (x : M) (hx : x * τ x = 1) : ∃ c : M, x = c * (τ c)⁻¹ := by
  obtain ⟨hcomm, hsq⟩ := quot_comm_sq hM
  have hbτ2 : (bar τ) ^ 2 = 1 := by rw [← map_pow, h.sq, map_one]
  have hbinv : bar τ * bar σ * (bar τ)⁻¹ = (bar σ)⁻¹ := by
    have := congrArg (quotientAutomorphism (frattini M)) h.inv
    simpa [map_mul, map_inv] using this
  have hτx : τ x = x⁻¹ := eq_inv_of_mul_eq_one_right hx
  have hfixed : bar τ (x : M ⧸ frattini M) = x := by
    rw [bar_mk, hτx, QuotientGroup.mk_inv]
    exact inv_eq_of_mul_eq_one_right (hsq _)
  obtain ⟨w, hw⟩ := exists_eq_mul_map_of_fixed hcomm hsq (bar σ) (bar τ) hbτ2 hbinv
    (bar_fix hM h) _ hfixed
  obtain ⟨c₀, rfl⟩ := QuotientGroup.mk_surjective w
  rw [bar_mk] at hw
  have hyΦ : c₀⁻¹ * x * τ c₀ ∈ frattini M := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, hw]
    calc (c₀ : M ⧸ frattini M)⁻¹ * (↑c₀ * ↑(τ c₀)) * ↑(τ c₀)
        = ((τ c₀ : M) : M ⧸ frattini M) * ((τ c₀ : M) : M ⧸ frattini M) := by group
      _ = 1 := hsq _
  have hyτ : (⟨c₀⁻¹ * x * τ c₀, hyΦ⟩ : frattini M) *
      MulAut.characteristic (frattini M) τ ⟨c₀⁻¹ * x * τ c₀, hyΦ⟩ = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, MulAut.characteristic_apply_apply_coe, map_mul, map_inv,
      h.tau_tau, OneMemClass.coe_one]
    calc c₀⁻¹ * x * τ c₀ * ((τ c₀)⁻¹ * τ x * c₀) = c₀⁻¹ * (x * τ x) * c₀ := by group
      _ = 1 := by rw [hx]; group
  obtain ⟨d, hd⟩ := hΦ ⟨c₀⁻¹ * x * τ c₀, hyΦ⟩ hyτ
  have hd' : c₀⁻¹ * x * τ c₀ = (d : M) * (τ (d : M))⁻¹ := by
    have := congrArg Subtype.val hd
    simpa using this
  refine ⟨c₀ * d, ?_⟩
  rw [map_mul, mul_inv_rev]
  calc x = c₀ * (c₀⁻¹ * x * τ c₀) * (τ c₀)⁻¹ := by group
    _ = c₀ * ((d : M) * (τ (d : M))⁻¹) * (τ c₀)⁻¹ := by rw [hd']
    _ = c₀ * d * ((τ (d : M))⁻¹ * (τ c₀)⁻¹) := by group

omit [Finite M] in
theorem exists_fixed_of_bar_fixed {σ τ : MulAut M} {k : ℕ} (h : DihAct σ τ k)
    (hΦ : ∀ y : frattini M, y * MulAut.characteristic (frattini M) τ y = 1 →
      ∃ d : frattini M, y = d * (MulAut.characteristic (frattini M) τ d)⁻¹)
    (r : M) (hr : bar τ (r : M ⧸ frattini M) = r) : ∃ d ∈ frattini M, τ (r * d) = r * d := by
  rw [bar_mk] at hr
  have hyΦ : r⁻¹ * τ r ∈ frattini M := QuotientGroup.eq.mp hr.symm
  have hyτ : (⟨r⁻¹ * τ r, hyΦ⟩ : frattini M) *
      MulAut.characteristic (frattini M) τ ⟨r⁻¹ * τ r, hyΦ⟩ = 1 := by
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

end Lift

theorem coboundary_aux : ∀ (n : ℕ) (M : Type) [Group M] [Finite M], Nat.card M = n →
    IsPGroup 2 M → ∀ (σ τ : MulAut M) (k : ℕ), DihAct σ τ k → ∀ x : M, x * τ x = 1 →
      ∃ c : M, x = c * (τ c)⁻¹ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M _ _ hn hM σ τ k h x hx
    by_cases hsub : Subsingleton M
    · exact ⟨1, Subsingleton.elim _ _⟩
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
      exact exists_coboundary_of_frattini hM h hΦ x hx

theorem pow_three_eq_one_aut {M : Type} [Group M] [Finite M] (hM : IsPGroup 2 M) {σ τ : MulAut M}
    {k : ℕ} (h : DihAct σ τ k) {P : Type} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hP4 : Nat.card (P ⧸ frattini P) ≤ 4) (ι : P →* M)
    (hι : ∀ r : M, τ r = r → r ∈ ι.range) : σ ^ 3 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcomm, hsq⟩ := quot_comm_sq hM
  have hΦ := coboundary_aux _ (frattini M) rfl (hM.to_subgroup _) _ _ k (h.restrict (frattini M))
  let f : P →* M ⧸ frattini M := (QuotientGroup.mk' (frattini M)).comp ι
  have hcover : ∀ v : M ⧸ frattini M, bar τ v = v → v ∈ f.range := by
    intro v hv
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective v
    obtain ⟨d, hd, hτd⟩ := exists_fixed_of_bar_fixed h hΦ r hv
    obtain ⟨p, hp⟩ := hι _ hτd
    refine ⟨p, ?_⟩
    show QuotientGroup.mk' (frattini M) (ι p) = (r : M ⧸ frattini M)
    rw [hp]
    exact QuotientGroup.eq.mpr (by simpa [mul_assoc] using inv_mem hd)
  have hker : frattini P ≤ f.ker := by
    have : Fact (IsPGroup 2 P) := ⟨hP⟩
    rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 2), Subgroup.closure_le]
    rintro x (hx | ⟨a, rfl⟩)
    · have hcomm_le : commutator P ≤ f.ker := by
        rw [commutator_def, Subgroup.commutator_le]
        intro a _ b _
        rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
        exact hcomm (f a) (f b)
      exact hcomm_le hx
    · simp only [SetLike.mem_coe, MonoidHom.mem_ker, map_pow]
      rw [pow_two]; exact hsq _
  have hrange : Nat.card f.range ≤ 4 := by
    have h1 : Nat.card f.range = f.ker.index := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]; rfl
    have h2 : f.ker.index ∣ (frattini P).index := Subgroup.index_dvd_of_le hker
    have h3 : (frattini P).index = Nat.card (P ⧸ frattini P) := rfl
    have h4 : 0 < (frattini P).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    rw [h1]; exact (Nat.le_of_dvd h4 h2).trans (h3 ▸ hP4)
  have hfix4 : Nat.card {v : M ⧸ frattini M // bar τ v = v} ≤ 4 := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun v => (⟨v.1, hcover v.1 v.2⟩ : f.range)) ?_) hrange
    intro a b hab
    exact Subtype.ext (congrArg (fun x : f.range => (x : M ⧸ frattini M)) hab)
  have hbτ2 : (bar τ) ^ 2 = 1 := by rw [← map_pow, h.sq, map_one]
  have hbinv : bar τ * bar σ * (bar τ)⁻¹ = (bar σ)⁻¹ := by
    have := congrArg (quotientAutomorphism (frattini M)) h.inv
    simpa [map_mul, map_inv] using this
  have hdvd : orderOf (bar σ) ∣ 3 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, h.pow, map_one])
  have hodd : Odd (orderOf (bar σ)) := Odd.of_dvd_nat (Odd.pow (by decide : Odd 3)) hdvd
  have hcase := orderOf_eq_of_card_fixed_le_four hcomm hsq (bar σ) (bar τ) hbτ2 hbinv
    (bar_fix hM h) hodd hfix4
  have hbar3 : (bar σ) ^ 3 = 1 := by
    rcases hcase with h1 | h3 | h5
    · rw [h1, one_pow]
    · rw [← h3]; exact pow_orderOf_eq_one _
    · exfalso
      rw [h5] at hdvd
      have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) hdvd
      omega
  have hker3 : σ ^ 3 ∈ (quotientAutomorphism (frattini M)).ker := by
    rw [MonoidHom.mem_ker, map_pow]; exact hbar3
  obtain ⟨n, hn⟩ := frattini_automorphism_kernel_isPGroup 2 hM ⟨σ ^ 3, hker3⟩
  have hn' : (σ ^ 3) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have h3k : (σ ^ 3) ^ 3 ^ k = 1 := by rw [← pow_mul, mul_comm, pow_mul, h.pow, one_pow]
  have hcop : Nat.Coprime (2 ^ n) (3 ^ k) := Nat.Coprime.pow _ _ (by norm_num)
  have := pow_gcd_eq_one.mpr ⟨hn', h3k⟩
  rwa [hcop.gcd_eq_one, pow_one] at this

end CFSG.GH74.Uniqueness.SU.K.R3.Pow

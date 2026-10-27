module

public import CFSG.GH74.GLS.IVK.L2.Fixed14a
public import CFSG.GH74.GLS.IVK.L2.FieldProj

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GorensteinWalter

theorem le_of_pow_dvd_mul_sq_sub_one {p m j : ℕ} (hp : p.Prime) (hm : 1 ≤ m)
    (h : p ^ j ∣ p ^ m * ((p ^ m) ^ 2 - 1)) : j ≤ m := by
  have hcop : Nat.Coprime (p ^ j) ((p ^ m) ^ 2 - 1) := by
    apply Nat.Coprime.pow_left
    rw [hp.coprime_iff_not_dvd]
    intro hdvd
    have h1 : p ∣ (p ^ m) ^ 2 := dvd_pow (dvd_pow_self p (by omega)) (by norm_num)
    have h2 : p ∣ (p ^ m) ^ 2 - ((p ^ m) ^ 2 - 1) := Nat.dvd_sub h1 hdvd
    have h3 : (p ^ m) ^ 2 - ((p ^ m) ^ 2 - 1) = 1 := by
      have : 1 ≤ (p ^ m) ^ 2 := Nat.one_le_pow 2 (p ^ m) (pow_pos hp.pos m)
      omega
    rw [h3] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
  have := hcop.dvd_of_dvd_mul_right h
  exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp this

theorem card_fixedField_eq_aux {q₀ q p n : ℕ} (hp : p.Prime) (h : q₀ ^ p = q) (hq : q = p ^ n) :
    ∃ m, q₀ = p ^ m ∧ m * p = n := by
  have hdvd : q₀ ∣ p ^ n := by
    rw [← hq, ← h]; exact dvd_pow_self _ hp.ne_zero
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  refine ⟨m, hm, ?_⟩
  rw [hm, ← pow_mul, hq] at h
  exact Nat.pow_right_injective hp.two_le h

theorem exists_elemAbelian_range {G : Type*} [Group G] (p : ℕ) {M : Type*} [CommGroup M] [Finite M]
    (hM : ∀ x : M, x ^ p = 1) (Φ : M →* G) (hΦ : Function.Injective Φ) (f : G) (hf : orderOf f = p)
    (hcomm : ∀ x : M, Φ x * f = f * Φ x) (hdisj : ∀ x : M, ∀ k : ℤ, Φ x = f ^ k → Φ x = 1)
    (C : Subgroup G) (hfC : f ∈ C) (hΦC : ∀ x : M, Φ x ∈ C) :
    ∃ A : Subgroup G, IsElementaryAbelian p ↥A ∧ Nat.card ↥A = Nat.card M * p ∧ A ≤ C := by
  classical
  have hfcomm : ∀ (x : M) (k : ℤ), Φ x * f ^ k = f ^ k * Φ x := by
    intro x k
    exact ((Commute.zpow_right (hcomm x) k))
  have hcomm' : ∀ (x : M) (y : Subgroup.zpowers f), Commute (Φ x) (y : G) := by
    rintro x ⟨y, hy⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact hfcomm x k
  let Ψ : M × Subgroup.zpowers f →* G :=
    Φ.noncommCoprod (Subgroup.zpowers f).subtype hcomm'
  have hDcomm : ∀ d₁ d₂ : M × Subgroup.zpowers f, d₁ * d₂ = d₂ * d₁ := by
    rintro ⟨x₁, ⟨y₁, hy₁⟩⟩ ⟨x₂, ⟨y₂, hy₂⟩⟩
    obtain ⟨k₁, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy₁
    obtain ⟨k₂, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy₂
    refine Prod.ext (mul_comm x₁ x₂) (Subtype.ext ?_)
    show f ^ k₁ * f ^ k₂ = f ^ k₂ * f ^ k₁
    rw [← zpow_add, ← zpow_add, add_comm]
  have hDpow : ∀ d : M × Subgroup.zpowers f, d ^ p = 1 := by
    rintro ⟨x, ⟨y, hy⟩⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine Prod.ext (hM x) (Subtype.ext ?_)
    show (f ^ k) ^ p = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hf, pow_orderOf_eq_one,
      one_zpow]
  have hΨinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, ⟨y, hy⟩⟩ h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have h1 : Φ x * f ^ k = 1 := h
    have h2 : Φ x = f ^ (-k) := by
      rw [zpow_neg, eq_inv_iff_mul_eq_one]; exact h1
    have h3 := hdisj x (-k) h2
    have h4 : x = 1 := hΦ (by rw [h3, map_one])
    have h5 : f ^ k = 1 := by rw [h4, map_one, one_mul] at h1; exact h1
    subst h4
    refine Prod.ext rfl (Subtype.ext ?_)
    exact h5
  refine ⟨Ψ.range, ?_, ?_, ?_⟩
  · refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
    · rintro ⟨a, d₁, rfl⟩ ⟨b, d₂, rfl⟩
      apply Subtype.ext
      show Ψ d₁ * Ψ d₂ = Ψ d₂ * Ψ d₁
      rw [← map_mul, ← map_mul, hDcomm]
    · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      rintro ⟨a, d, rfl⟩
      apply Subtype.ext
      show Ψ d ^ p = 1
      rw [← map_pow, hDpow, map_one]
  · rw [Nat.card_congr (MonoidHom.ofInjective hΨinj).toEquiv.symm, Nat.card_prod,
      Nat.card_zpowers, hf]
  · rintro _ ⟨⟨x, ⟨y, hy⟩⟩, rfl⟩
    have hyC : y ∈ C := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact C.zpow_mem hfC k
    exact C.mul_mem (hΦC x) hyC

section Unipotent

@[expose] noncomputable def uPGL (F₀ : Type) [Field F₀] : Multiplicative F₀ →* PGL2 F₀ :=
  (Matrix.ProjGenLinGroup.mk : GL (Fin 2) F₀ →* PGL2 F₀).comp (uHom F₀)

theorem uPGL_injective (F₀ : Type) [Field F₀] : Function.Injective (uPGL F₀) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  have hc : uHom F₀ t ∈ Subgroup.center (GL (Fin 2) F₀) := Matrix.ProjGenLinGroup.mk_eq_one.mp ht
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc
  obtain ⟨u, hu⟩ := hc
  have h01 := congrArg (fun g : GL (Fin 2) F₀ => (g : Matrix (Fin 2) (Fin 2) F₀) 0 1) hu
  simp [uHom, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h01
  exact h01.symm

end Unipotent

section Rank

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K] (e : K ≃* L2 F)
  (σ : F ≃+* F)

include e σ in
theorem card_le_of_pow_eq_one {p m : ℕ} (hp : p.Prime) (hq₀ : Nat.card (fixedField σ) = p ^ m)
    (hm : 1 ≤ m) (A : Subgroup (MulAut K))
    (hAC : A ≤ centralizer ({fieldAutHom e σ} : Set (MulAut K)))
    (hpow : ∀ x ∈ A, x ^ p = 1) : Nat.card A ≤ p ^ (m + 1) := by
  have : Fact p.Prime := ⟨hp⟩
  set ψ : ↥A →* (F ≃+* F) := (fieldProj e).comp A.subtype with hψ
  have hpowA : ∀ a : ↥A, a ^ p = 1 := fun a => Subtype.ext (by simpa using hpow a a.2)
  have hrange : Nat.card ψ.range ≤ p := by
    have := ringAut_isCyclic F
    have : IsCyclic ψ.range := Subgroup.isCyclic _
    have h1 : Monoid.exponent ψ.range ∣ p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      rintro ⟨_, a, rfl⟩
      apply Subtype.ext
      show ψ a ^ p = 1
      rw [← map_pow, hpowA a, map_one]
    rw [IsCyclic.exponent_eq_card] at h1
    exact Nat.le_of_dvd hp.pos h1
  have hker : Nat.card ψ.ker ≤ p ^ m := by
    set X : Subgroup (MulAut K) := ψ.ker.map A.subtype with hX
    have hXA : X ≤ A := by
      rintro _ ⟨a, _, rfl⟩
      exact a.2
    have hXle : X ≤ centralizer ({fieldAutHom e σ} : Set (MulAut K)) ⊓ innDiagSub e := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨hAC a.2, (mem_innDiagSub_iff e _).mpr (MonoidHom.mem_ker.mp ha)⟩
    have hXcard : Nat.card X = Nat.card ψ.ker :=
      Subgroup.card_map_of_injective A.subtype_injective
    have hdvd : Nat.card X ∣ p ^ m * ((p ^ m) ^ 2 - 1) := by
      have h1 := Subgroup.card_dvd_of_le hXle
      rw [card_centralizer_fieldAut e σ, hq₀] at h1
      exact h1
    have hXp : IsPGroup p X := by
      intro x
      refine ⟨1, ?_⟩
      apply Subtype.ext
      simpa using hpow x (hXA x.2)
    obtain ⟨j, hj⟩ := (IsPGroup.iff_card).mp hXp
    rw [hj] at hdvd
    have := le_of_pow_dvd_mul_sq_sub_one hp hm hdvd
    rw [← hXcard, hj]
    exact Nat.pow_le_pow_right hp.pos this
  have := Subgroup.card_ker_mul_card_range ψ
  calc Nat.card A = Nat.card ψ.ker * Nat.card ψ.range := this.symm
    _ ≤ p ^ m * p := Nat.mul_le_mul hker hrange
    _ = p ^ (m + 1) := by ring

end Rank

theorem ivk_1_4f : IVK_1_4f := by
  intro F _ _ hF K _ _ e p n hp hFn W _ σ hσ
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by
    have hp2 : p ≠ 2 := by
      rintro rfl
      have hn : n ≠ 0 := by
        rintro rfl
        have := hF.2
        rw [hFn] at this
        simp at this
      have : Even (Nat.card F) := by
        rw [hFn]; exact (Nat.even_pow.mpr ⟨even_two, hn⟩)
      exact (Nat.not_even_iff_odd.mpr hF.1) this
    have := hp.two_le
    omega
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨m, hm, hmp⟩ := card_fixedField_eq_aux hp (by rw [← hσ]; exact fixedField_card_pow σ) hFn
  have hm1 : 1 ≤ m := by
    have := one_lt_card_fixedField σ
    rw [hm] at this
    by_contra h0
    have : m = 0 := by omega
    subst this
    simp at *
  have hfo : orderOf (fieldAutHom e σ) = p := by
    rw [orderOf_injective (fieldAutHom e) (fieldAutHom_injective e) σ, hσ]
  have hnp : n / p = m := by rw [← hmp]; exact Nat.mul_div_cancel _ hp.pos
  have h3m : 3 * m ≤ m * p := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  ·
    by_contra hcon
    push Not at hcon
    have hle : (W : Subgroup K) ≤ fixedSubgroup K (fieldAutHom e σ) := fun x hx => hcon x hx
    have hq : Odd (Nat.card F) := hF.1
    have hKcard := ivk_1_2b F hF K e
    have hK2 : 2 ∣ Nat.card F ^ 2 - 1 := by
      have : Odd (Nat.card F ^ 2) := hq.pow
      have := Nat.odd_iff.mp this
      omega
    have hpnK : p ^ n ∣ Nat.card K := by
      rw [hKcard, Nat.mul_div_assoc _ hK2, hFn]
      exact dvd_mul_right _ _
    have hK0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
    have hWcard : p ^ n ∣ Nat.card (W : Subgroup K) := by
      rw [Sylow.card_eq_multiplicity W]
      exact pow_dvd_pow p ((hp.pow_dvd_iff_le_factorization hK0).mp hpnK)
    have hodd : Odd (orderOf σ) := by rw [hσ]; exact hpodd
    have hCcard := card_fixedSubgroup_of_odd e σ hodd hq
    have hq₀odd : Odd (Nat.card (fixedField σ)) := odd_card_fixedField σ hq
    have h2 : 2 ∣ Nat.card (fixedField σ) * (Nat.card (fixedField σ) ^ 2 - 1) := by
      have : Odd (Nat.card (fixedField σ) ^ 2) := hq₀odd.pow
      have := Nat.odd_iff.mp this
      exact Dvd.dvd.mul_left (by omega) _
    have hdvd : Nat.card (W : Subgroup K) ∣
        Nat.card (fixedField σ) * (Nat.card (fixedField σ) ^ 2 - 1) :=
      (Subgroup.card_dvd_of_le hle).trans
        (by rw [hCcard]; exact Nat.div_dvd_of_dvd h2)
    have := le_of_pow_dvd_mul_sq_sub_one hp hm1 (by
      rw [hm] at hdvd
      exact hWcard.trans hdvd)
    omega
  ·
    set C := centralizer ({fieldAutHom e σ} : Set (MulAut K)) with hC
    have hub : ∀ r ∈ {r : ℕ | ∃ A : Subgroup ↥C, IsElementaryAbelian p ↥A ∧ Nat.card ↥A = p ^ r},
        r ≤ m + 1 := by
      rintro r ⟨A, hA, hr⟩
      set A' : Subgroup (MulAut K) := A.map C.subtype with hA'
      have hAC : A' ≤ C := by
        rintro _ ⟨a, _, rfl⟩
        exact a.2
      have hpow : ∀ x ∈ A', x ^ p = 1 := by
        rintro _ ⟨a, ha, rfl⟩
        have := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p ↥A)
          ⟨a, ha⟩
        have h2 : a ^ p = 1 := congrArg Subtype.val this
        have h3 := congrArg Subtype.val h2
        simpa using h3
      have hcard : Nat.card A' = Nat.card A := Subgroup.card_map_of_injective C.subtype_injective
      have := card_le_of_pow_eq_one e σ hp hm hm1 A' hAC hpow
      rw [hcard, hr] at this
      exact (Nat.pow_le_pow_iff_right hp.one_lt).mp this
    have hmem : m + 1 ∈ {r : ℕ | ∃ A : Subgroup ↥C, IsElementaryAbelian p ↥A ∧
        Nat.card ↥A = p ^ r} := by
      have hFp : CharP F p := by
        have := Fintype.ofFinite F
        rw [Nat.card_eq_fintype_card] at hFn
        exact charP_of_card_eq_prime_pow hFn
      have hF0p : CharP ↥(fixedField σ) p := inferInstance
      let Φ : Multiplicative ↥(fixedField σ) →* MulAut K :=
        (innDiagHom e).comp ((pgl2Incl σ).comp (uPGL ↥(fixedField σ)))
      have hΦinj : Function.Injective Φ :=
        (innDiagHom_injective e).comp ((pgl2Incl_injective σ).comp (uPGL_injective _))
      have hΦcent : ∀ x, Φ x * fieldAutHom e σ = fieldAutHom e σ * Φ x := by
        intro x
        have h1 : pgl2Incl σ (uPGL _ x) ∈ (pgl2Incl σ).range := ⟨_, rfl⟩
        have h2 := (mem_centralizer_innDiagHom_iff e σ (pgl2Incl σ (uPGL _ x))).mpr
          ((mem_range_pgl2Incl_iff σ _).mp h1)
        exact Subgroup.mem_centralizer_singleton_iff.mp h2
      have hΦC : ∀ x, Φ x ∈ C := fun x => Subgroup.mem_centralizer_singleton_iff.mpr (hΦcent x)
      have hM : ∀ x : Multiplicative ↥(fixedField σ), x ^ p = 1 := by
        intro x
        have h : Multiplicative.toAdd (x ^ p) = 0 := by
          rw [toAdd_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
        exact toAdd_eq_zero.mp h
      have hdisj : ∀ (x : Multiplicative ↥(fixedField σ)) (k : ℤ),
          Φ x = fieldAutHom e σ ^ k → Φ x = 1 := by
        intro x k hk
        have h1 : Φ x ∈ innDiagSub e ⊓ fieldAutSub e :=
          ⟨(mem_innDiagSub_iff e _).mpr (fieldProj_innDiagHom e _),
            by rw [hk]; exact (fieldAutSub e).zpow_mem ⟨σ, rfl⟩ k⟩
        rw [innDiagSub_inf_fieldAutSub e] at h1
        exact h1
      have hfC : fieldAutHom e σ ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
      obtain ⟨A₀, hA₀, hcard₀, hle⟩ := exists_elemAbelian_range p hM Φ hΦinj (fieldAutHom e σ) hfo
        hΦcent hdisj C hfC hΦC
      refine ⟨A₀.subgroupOf C, ?_, ?_⟩
      · exact IsElementaryAbelian.subgroupOf hle
      · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcard₀,
          Nat.card_congr (Multiplicative.toAdd : Multiplicative ↥(fixedField σ) ≃ _), hm, pow_succ]
    show sSup {r : ℕ | ∃ A : Subgroup ↥C, IsElementaryAbelian p ↥A ∧ Nat.card ↥A = p ^ r} =
      1 + n / p
    rw [hnp]
    apply le_antisymm
    · exact csSup_le ⟨m + 1, hmem⟩ (fun r hr => by have := hub r hr; omega)
    · have := le_csSup ⟨m + 1, hub⟩ hmem
      omega
  ·
    rw [hnp]
    omega

end CFSG.GH74.GLS.IVK

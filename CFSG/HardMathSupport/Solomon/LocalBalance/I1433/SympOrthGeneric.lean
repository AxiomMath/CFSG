module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.SimpleCfg
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.SympOrthLinear
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem congr_conj_apply_so {S G : Type*} [Group S] [Group G] (e : S ≃* G) (s : S) :
    MulAut.congr e (MulAut.conj s) = MulAut.conj (e s) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem inner_of_mem_commutator_of_equiv {S T : Type} [Group S] [Group T] (e : S ≃* T)
    (h : ∀ β ∈ commutator (MulAut T), β ^ 3 = 1 → ∃ t : T, MulAut.conj t = β)
    {β : MulAut S} (hβ : β ∈ commutator (MulAut S)) (hβ3 : β ^ 3 = 1) :
    ∃ s : S, MulAut.conj s = β := by
  have hmem : MulAut.congr e β ∈ commutator (MulAut T) := by
    have h1 : (commutator (MulAut S)).map (MulAut.congr e).toMonoidHom ≤ commutator (MulAut T) := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    exact h1 ⟨β, hβ, rfl⟩
  obtain ⟨t, ht⟩ := h _ hmem (by rw [← map_pow, hβ3, map_one])
  refine ⟨e.symm t, ?_⟩
  apply (MulAut.congr e).injective
  rw [congr_conj_apply_so, MulEquiv.apply_symm_apply, ht]

theorem injective_conj_of_center_eq_bot {S : Type*} [Group S] (hS : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hc : a ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun φ : MulAut S => φ g) ha
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * a = a * g * a⁻¹ * a := by rw [this]
      _ = a * g := by group
  rw [hS, Subgroup.mem_bot] at hc
  exact hc

theorem I1433SCfg.exists_heisenberg {S : Type} [Group S] [Finite S] (hS : Subgroup.center S = ⊥)
    {Q : Subgroup (MulAut S)} {x : S} {J : Subgroup S} {q : ℕ} (c : I1433SCfg Q x J q)
    (hinn : ∀ β ∈ Q, ∃ t : S, MulAut.conj t = β) :
    ∃ a b : S, ⁅a, b⁆ = x ∧ a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ ⁅a, x⁆ = 1 ∧ ⁅b, x⁆ = 1 ∧
      ∀ L : Subgroup S, GLAPComponent 3 (Subgroup.centralizer ({x} : Set S)) L →
        ∀ l ∈ L, ⁅a, l⁆ = 1 ∧ ⁅b, l⁆ = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinj := injective_conj_of_center_eq_bot hS
  have hx3 : x ^ 3 = 1 := by rw [← c.order]; exact pow_orderOf_eq_one x
  obtain ⟨α, hα, β, hβ, hne⟩ := c.nonabelian
  have hnaQ : ¬ ∀ a b : ↥Q, a * b = b * a := fun h =>
    hne (congrArg Subtype.val (h ⟨α, hα⟩ ⟨β, hβ⟩))
  have hZ3 : Nat.card (Subgroup.center ↥Q) = 3 := card_center_eq_three c.card hnaQ
  have hquot : Nat.card (↥Q ⧸ Subgroup.center ↥Q) = 3 ^ 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥Q)
    rw [c.card, hZ3] at h
    omega
  have hcomm := IsPGroup.commutative_of_card_eq_prime_sq (p := 3) hquot
  set γ : ↥Q := ⁅(⟨α, hα⟩ : ↥Q), ⟨β, hβ⟩⁆ with hγ
  have hγc : γ ∈ Subgroup.center ↥Q := by
    have h1 : (QuotientGroup.mk' (Subgroup.center ↥Q)) γ = 1 := by
      rw [hγ, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (hcomm _ _)
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hγne : γ ≠ 1 := by
    intro h
    apply hne
    have := commutatorElement_eq_one_iff_mul_comm.mp (hγ ▸ h)
    exact congrArg Subtype.val this
  have hγmem : (γ : MulAut S) ∈ Subgroup.zpowers (MulAut.conj x) := by
    rw [← c.center]
    exact ⟨γ, hγc, rfl⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hγmem
  have hord : orderOf x = 3 := c.order
  have hk' : (MulAut.conj x) ^ k = MulAut.conj (x ^ k) := by rw [map_zpow]
  have hxk : x ^ k = x ∨ x ^ k = x⁻¹ := by
    have hmod : x ^ (k % (3 : ℤ)) = x ^ k := by
      have := zpow_mod_orderOf x k
      rwa [hord] at this
    have h3 : k % (3 : ℤ) = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases h3 with h | h | h
    · exfalso
      rw [h, zpow_zero] at hmod
      apply hγne
      apply Subtype.ext
      show (γ : MulAut S) = 1
      rw [← hk, hk', ← hmod, map_one]
    · left; rw [← hmod, h, zpow_one]
    · right
      rw [← hmod, h]
      have : x ^ (2 : ℤ) = x⁻¹ := by
        have : x ^ (2 : ℤ) * x = 1 := by
          rw [← zpow_add_one]
          exact_mod_cast hx3
        exact eq_inv_of_mul_eq_one_left this
      exact this
  obtain ⟨α', hα', β', hβ', hαβ⟩ : ∃ α' ∈ Q, ∃ β' ∈ Q, ⁅α', β'⁆ = MulAut.conj x := by
    rcases hxk with h | h
    · refine ⟨α, hα, β, hβ, ?_⟩
      have : (γ : MulAut S) = MulAut.conj x := by rw [← hk, hk', h]
      rw [← this]; rfl
    · refine ⟨β, hβ, α, hα, ?_⟩
      have : (γ : MulAut S) = MulAut.conj x⁻¹ := by rw [← hk, hk', h]
      have h2 : ⁅β, α⁆ = ((γ : MulAut S))⁻¹ := by
        rw [← commutatorElement_inv]; rfl
      rw [h2, this, map_inv, inv_inv]
  obtain ⟨a, rfl⟩ := hinn α' hα'
  obtain ⟨b, rfl⟩ := hinn β' hβ'
  have hab : ⁅a, b⁆ = x := by
    apply hinj
    rw [map_commutatorElement]
    exact hαβ
  have hcube : ∀ g : S, MulAut.conj g ∈ Q → g ^ 3 = 1 := by
    intro g hg
    have h1 := c.exponent _ hg
    have h2 : g ^ 3 ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg (fun φ : MulAut S => φ y) (show MulAut.conj (g ^ 3) = 1 by
        rw [map_pow]; exact h1)
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * g ^ 3 = g ^ 3 * y * (g ^ 3)⁻¹ * g ^ 3 := by rw [this]
        _ = g ^ 3 * y := by group
    rw [hS, Subgroup.mem_bot] at h2
    exact h2
  have hxQ : MulAut.conj x ∈ Q := by
    have : MulAut.conj x ∈ (Subgroup.center ↥Q).map Q.subtype := by
      rw [c.center]; exact Subgroup.mem_zpowers _
    obtain ⟨z, -, hz⟩ := this
    rw [← hz]; exact z.2
  have hcentral : ∀ g : S, MulAut.conj g ∈ Q → ⁅g, x⁆ = 1 := by
    intro g hg
    have : MulAut.conj x ∈ (Subgroup.center ↥Q).map Q.subtype := by
      rw [c.center]; exact Subgroup.mem_zpowers _
    obtain ⟨z, hz, hzx⟩ := this
    have h1 : (⟨MulAut.conj g, hg⟩ : ↥Q) * z = z * ⟨MulAut.conj g, hg⟩ :=
      Subgroup.mem_center_iff.mp hz _
    have h2 : MulAut.conj g * MulAut.conj x = MulAut.conj x * MulAut.conj g := by
      have := congrArg Subtype.val h1
      simp only [Subgroup.coe_mul] at this
      rw [← hzx]; exact this
    apply hinj
    rw [map_commutatorElement, map_one]
    exact commutatorElement_eq_one_iff_mul_comm.mpr h2
  refine ⟨a, b, hab, hcube a hα', hcube b hβ', hcentral a hα', hcentral b hβ', ?_⟩
  intro L hL l hl
  have key : ∀ g : S, MulAut.conj g ∈ Q → ⁅g, l⁆ = 1 := by
    intro g hg
    have h1 := c.centralizes L hL _ hg l hl
    rw [MulAut.conj_apply] at h1
    rw [commutatorElement_def]
    calc g * l * g⁻¹ * l⁻¹ = (g * l * g⁻¹) * l⁻¹ := by group
      _ = 1 := by rw [h1]; group
  exact ⟨key a hα', key b hβ'⟩

theorem commutator_eq_one_of_perfect {G : Type*} [Group G] {Z : Subgroup G}
    (hZ : Z ≤ Subgroup.center G) {P : Subgroup G} (hP : ⁅P, P⁆ = P) {A : G}
    (hA : ∀ g ∈ P, ⁅A, g⁆ ∈ Z) : ∀ g ∈ P, ⁅A, g⁆ = 1 := by
  have hcomm : ∀ z ∈ Z, ∀ y : G, y * z = z * y := fun z hz y =>
    Subgroup.mem_center_iff.mp (hZ hz) y
  have hconj : ∀ g : G, A * g * A⁻¹ = ⁅A, g⁆ * g := fun g => by
    rw [commutatorElement_def]; group
  have hprod : ∀ g ∈ P, ∀ h ∈ P, ⁅A, g * h⁆ = ⁅A, g⁆ * ⁅A, h⁆ := by
    intro g hg h hh
    have e : ⁅A, g * h⁆ = (A * g * A⁻¹) * (A * h * A⁻¹ * h⁻¹) * g⁻¹ := by
      rw [commutatorElement_def]; group
    have e2 : A * h * A⁻¹ * h⁻¹ = ⁅A, h⁆ := by rw [commutatorElement_def]
    rw [e, e2, hconj g]
    have h1 := hcomm _ (hA h hh) g⁻¹
    calc ⁅A, g⁆ * g * ⁅A, h⁆ * g⁻¹ = ⁅A, g⁆ * (g * (⁅A, h⁆ * g⁻¹)) := by group
      _ = ⁅A, g⁆ * (g * (g⁻¹ * ⁅A, h⁆)) := by rw [← h1]
      _ = ⁅A, g⁆ * ⁅A, h⁆ := by group
  have hinv : ∀ g ∈ P, ⁅A, g⁻¹⁆ = (⁅A, g⁆)⁻¹ := by
    intro g hg
    have := hprod g hg g⁻¹ (P.inv_mem hg)
    have h1 : ⁅A, g * g⁻¹⁆ = 1 := by rw [mul_inv_cancel]; simp
    rw [h1] at this
    exact eq_inv_of_mul_eq_one_right this.symm
  have hcomP : ∀ g ∈ P, ∀ h ∈ P, ⁅A, ⁅g, h⁆⁆ = 1 := by
    intro g hg h hh
    have e : ⁅g, h⁆ = g * h * g⁻¹ * h⁻¹ := commutatorElement_def g h
    have hm : ∀ u ∈ P, ∀ v ∈ P, ⁅A, u * v⁆ = ⁅A, u⁆ * ⁅A, v⁆ := hprod
    have h1 := hm (g * h * g⁻¹) (P.mul_mem (P.mul_mem hg hh) (P.inv_mem hg)) h⁻¹ (P.inv_mem hh)
    have h2 := hm (g * h) (P.mul_mem hg hh) g⁻¹ (P.inv_mem hg)
    have h3 := hm g hg h hh
    rw [e, h1, h2, h3, hinv g hg, hinv h hh]
    have hzg := hcomm _ (hA g hg)
    have hzh := hcomm _ (hA h hh)
    set zg := ⁅A, g⁆ with hzgdef
    set zh := ⁅A, h⁆ with hzhdef
    have : zg * zh * zg⁻¹ * zh⁻¹ = 1 := by
      have hzz : zh * zg = zg * zh := hzg zh
      calc zg * zh * zg⁻¹ * zh⁻¹ = zg * zh * (zg⁻¹ * zh⁻¹) := by group
        _ = zg * zh * (zh * zg)⁻¹ := by rw [mul_inv_rev]
        _ = zg * zh * (zg * zh)⁻¹ := by rw [hzz]
        _ = 1 := mul_inv_cancel _
    exact this
  intro g hg
  have hle : ⁅P, P⁆ ≤ Subgroup.centralizer ({A} : Set G) := by
    rw [Subgroup.commutator_le]
    intro u hu v hv
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact commutatorElement_eq_one_iff_mul_comm.mp (hcomP u hu v hv)
  have hgP : g ∈ ⁅P, P⁆ := by rw [hP]; exact hg
  have hg' : g ∈ Subgroup.centralizer ({A} : Set G) := hle hgP
  rw [Subgroup.mem_centralizer_iff] at hg'
  exact commutatorElement_eq_one_iff_mul_comm.mpr (hg' A (Set.mem_singleton A))

theorem commutator_cube_eq_one {G : Type*} [Group G] {A B : G} (hA3 : A ^ 3 = 1)
    (hzA : Commute ⁅A, B⁆ A) (_hzB : Commute ⁅A, B⁆ B) : ⁅A, B⁆ ^ 3 = 1 := by
  set z : G := ⁅A, B⁆ with hz
  have hAB : MulAut.conj A B = z * B := by
    rw [MulAut.conj_apply, hz, commutatorElement_def]; group
  have hAz : MulAut.conj A z = z := by
    rw [MulAut.conj_apply]
    have : A * z = z * A := hzA.symm.eq
    rw [this]; group
  have hpow : ∀ n : ℕ, (MulAut.conj A ^ n) B = z ^ n * B := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hAz, hAB, pow_succ, mul_assoc]
  have h3 := hpow 3
  rw [← map_pow, hA3, map_one] at h3
  have : z ^ 3 * B = 1 * B := by rw [← h3]; simp
  exact mul_right_cancel this

@[expose] def selfCentralizer {G : Type*} [Group G] (X : G) :
    Subgroup.centralizer ({X} : Set G) :=
  ⟨X, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

@[expose] def HasLowRankBlock {G S : Type} [Group G] [Group S] (π : G →* S) (X : G)
    (J : Subgroup S) : Prop :=
  ∃ (E : Type) (_ : Field E) (U : Type) (_ : AddCommGroup U) (_ : Module E U)
    (_ : FiniteDimensional E U)
    (ρ : Subgroup.centralizer ({X} : Set G) →* LinearMap.GeneralLinearGroup E U) (ω : E)
    (P : Subgroup G) (hP : P ≤ Subgroup.centralizer ({X} : Set G)) (g : G) (hg : g ∈ P),
    ω ≠ 1 ∧ ω ^ 3 = 1 ∧ (∀ u, (ρ (selfCentralizer X) : Module.End E U) u = ω • u) ∧
      ⁅P, P⁆ = P ∧ P.map π ≤ J ∧
      0 < Module.finrank E (LinearMap.range ((ρ ⟨g, hP hg⟩ : Module.End E U) - 1)) ∧
      Module.finrank E (LinearMap.range ((ρ ⟨g, hP hg⟩ : Module.End E U) - 1)) < 3

theorem hasLowRankBlock_of_factor {G S : Type} [Group G] [Group S] (π : G →* S) (X : G)
    (J : Subgroup S) (E : Type) [Field E] (U : Type) [AddCommGroup U] [Module E U]
    [FiniteDimensional E U]
    (ρ : Subgroup.centralizer ({X} : Set G) →* LinearMap.GeneralLinearGroup E U) (ω : E)
    (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    (hρX : ∀ u, (ρ (selfCentralizer X) : Module.End E U) u = ω • u)
    (F : Subgroup G) (hFC : F ≤ Subgroup.centralizer ({X} : Set G))
    (hJ : J = (⁅F, F⁆).map π) (hperf : ⁅⁅F, F⁆, ⁅F, F⁆⁆ = ⁅F, F⁆)
    (hnonab : ∃ g₁ ∈ ⁅F, F⁆, ∃ g₂ ∈ ⁅F, F⁆, g₁ * g₂ ≠ g₂ * g₁)
    (Fimg : Subgroup (LinearMap.GeneralLinearGroup E U))
    (hFimg : ∀ g (hg : g ∈ F), ρ ⟨g, hFC hg⟩ ∈ Fimg)
    (hsurj : ∀ u ∈ Fimg, ∃ g, ∃ hg : g ∈ F, ρ ⟨g, hFC hg⟩ = u)
    (hinj : ∀ g₁ (h₁ : g₁ ∈ F) g₂ (h₂ : g₂ ∈ F), ρ ⟨g₁, hFC h₁⟩ = ρ ⟨g₂, hFC h₂⟩ → g₁ = g₂)
    (hlow : ∀ N : Subgroup (LinearMap.GeneralLinearGroup E U), N ≤ Fimg →
      (∀ f ∈ Fimg, ∀ n ∈ N, f * n * f⁻¹ ∈ N) → (∃ n₁ ∈ N, ∃ n₂ ∈ N, n₁ * n₂ ≠ n₂ * n₁) →
      ∃ n ∈ N, 0 < Module.finrank E (LinearMap.range ((n : Module.End E U) - 1)) ∧
        Module.finrank E (LinearMap.range ((n : Module.End E U) - 1)) < 3) :
    HasLowRankBlock π X J := by
  have hPF : ⁅F, F⁆ ≤ F := Subgroup.commutator_le_self F
  have hPC : ⁅F, F⁆ ≤ Subgroup.centralizer ({X} : Set G) := hPF.trans hFC
  let N : Subgroup (LinearMap.GeneralLinearGroup E U) :=
    ((⁅F, F⁆).subgroupOf (Subgroup.centralizer ({X} : Set G))).map ρ
  have hmemN : ∀ g (hg : g ∈ ⁅F, F⁆), ρ ⟨g, hPC hg⟩ ∈ N := fun g hg =>
    ⟨⟨g, hPC hg⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  have hNle : N ≤ Fimg := by
    rintro _ ⟨⟨g, hgC⟩, hg, rfl⟩
    exact hFimg g (hPF (Subgroup.mem_subgroupOf.mp hg))
  have hNnormal : ∀ f ∈ Fimg, ∀ n ∈ N, f * n * f⁻¹ ∈ N := by
    intro f hf n hn
    obtain ⟨h, hh, rfl⟩ := hsurj f hf
    obtain ⟨⟨g, hgC⟩, hg, rfl⟩ := hn
    have hgP : g ∈ ⁅F, F⁆ := Subgroup.mem_subgroupOf.mp hg
    have hhgh : h * g * h⁻¹ ∈ ⁅F, F⁆ := by
      have h1 : ⁅h, g⁆ ∈ ⁅F, F⁆ := Subgroup.commutator_mem_commutator hh (hPF hgP)
      have h2 : h * g * h⁻¹ = ⁅h, g⁆ * g := by rw [commutatorElement_def]; group
      rw [h2]; exact Subgroup.mul_mem _ h1 hgP
    have := hmemN (h * g * h⁻¹) hhgh
    convert this using 1
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
  have hNna : ∃ n₁ ∈ N, ∃ n₂ ∈ N, n₁ * n₂ ≠ n₂ * n₁ := by
    obtain ⟨g₁, hg₁, g₂, hg₂, hne⟩ := hnonab
    refine ⟨_, hmemN g₁ hg₁, _, hmemN g₂ hg₂, fun h => hne ?_⟩
    rw [← map_mul, ← map_mul] at h
    have := hinj (g₁ * g₂) (F.mul_mem (hPF hg₁) (hPF hg₂)) (g₂ * g₁)
      (F.mul_mem (hPF hg₂) (hPF hg₁)) h
    exact this
  obtain ⟨n, ⟨⟨g, hgC⟩, hg, rfl⟩, hr0, hr3⟩ := hlow N hNle hNnormal hNna
  have hgP : g ∈ ⁅F, F⁆ := Subgroup.mem_subgroupOf.mp hg
  exact ⟨E, inferInstance, U, inferInstance, inferInstance, inferInstance, ρ, ω, ⁅F, F⁆, hPC, g,
    hgP, hω1, hω3, hρX, hperf, hJ.symm ▸ le_rfl, hr0, hr3⟩

theorem hasLowRankBlock_of_perfect {G S : Type} [Group G] [Group S] (π : G →* S) (X : G)
    (J : Subgroup S) (E : Type) [Field E] (U : Type) [AddCommGroup U] [Module E U]
    [FiniteDimensional E U]
    (ρ : Subgroup.centralizer ({X} : Set G) →* LinearMap.GeneralLinearGroup E U) (ω : E)
    (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    (hρX : ∀ u, (ρ (selfCentralizer X) : Module.End E U) u = ω • u)
    (P : Subgroup G) (hPC : P ≤ Subgroup.centralizer ({X} : Set G)) (hJ : P.map π ≤ J)
    (hperf : ⁅P, P⁆ = P)
    (hnonab : ∃ g₁ g₂ : G, ∃ (h₁ : g₁ ∈ P) (h₂ : g₂ ∈ P),
      ρ ⟨g₁, hPC h₁⟩ * ρ ⟨g₂, hPC h₂⟩ ≠ ρ ⟨g₂, hPC h₂⟩ * ρ ⟨g₁, hPC h₁⟩)
    (Fimg : Subgroup (LinearMap.GeneralLinearGroup E U))
    (hPimg : ∀ g (hg : g ∈ P), ρ ⟨g, hPC hg⟩ ∈ Fimg)
    (hnormal : ∀ f ∈ Fimg, ∀ g (hg : g ∈ P), ∃ g' : G, ∃ hg' : g' ∈ P,
      ρ ⟨g', hPC hg'⟩ = f * ρ ⟨g, hPC hg⟩ * f⁻¹)
    (hlow : ∀ N : Subgroup (LinearMap.GeneralLinearGroup E U), N ≤ Fimg →
      (∀ f ∈ Fimg, ∀ n ∈ N, f * n * f⁻¹ ∈ N) → (∃ n₁ ∈ N, ∃ n₂ ∈ N, n₁ * n₂ ≠ n₂ * n₁) →
      ∃ n ∈ N, 0 < Module.finrank E (LinearMap.range ((n : Module.End E U) - 1)) ∧
        Module.finrank E (LinearMap.range ((n : Module.End E U) - 1)) < 3) :
    HasLowRankBlock π X J := by
  let N : Subgroup (LinearMap.GeneralLinearGroup E U) :=
    (P.subgroupOf (Subgroup.centralizer ({X} : Set G))).map ρ
  have hmemN : ∀ g (hg : g ∈ P), ρ ⟨g, hPC hg⟩ ∈ N := fun g hg =>
    ⟨⟨g, hPC hg⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  have hNle : N ≤ Fimg := by
    rintro _ ⟨⟨g, hgC⟩, hg, rfl⟩
    exact hPimg g (Subgroup.mem_subgroupOf.mp hg)
  have hNnormal : ∀ f ∈ Fimg, ∀ n ∈ N, f * n * f⁻¹ ∈ N := by
    intro f hf n hn
    obtain ⟨⟨g, hgC⟩, hg, rfl⟩ := hn
    obtain ⟨g', hg', h'⟩ := hnormal f hf g (Subgroup.mem_subgroupOf.mp hg)
    rw [← h']
    exact hmemN g' hg'
  have hNna : ∃ n₁ ∈ N, ∃ n₂ ∈ N, n₁ * n₂ ≠ n₂ * n₁ := by
    obtain ⟨g₁, g₂, h₁, h₂, hne⟩ := hnonab
    exact ⟨_, hmemN g₁ h₁, _, hmemN g₂ h₂, hne⟩
  obtain ⟨n, ⟨⟨g, hgC⟩, hg, rfl⟩, hr0, hr3⟩ := hlow N hNle hNnormal hNna
  have hgP : g ∈ P := Subgroup.mem_subgroupOf.mp hg
  exact ⟨E, inferInstance, U, inferInstance, inferInstance, inferInstance, ρ, ω, P, hPC, g,
    hgP, hω1, hω3, hρX, hperf, hJ, hr0, hr3⟩

theorem fixSubgroup_conj_eq_centralizer_so {X : Type*} [Group X] (x : X) :
    fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set X) := by
  ext g
  rw [mem_fixSubgroup, MulAut.conj_apply, mul_inv_eq_iff_eq_mul,
    Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem I1433SCfg.false_of_lowRank {S G : Type} [Group S] [Finite S] [Group G] (π : G →* S)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center G)
    (hker2 : ∀ z ∈ π.ker, z ^ 2 = 1) (hS : Subgroup.center S = ⊥)
    (hlayer : ∀ y : S, y ^ 3 = 1 → PerfectInLayer (MulAut.conj y))
    (hblock : ∀ X : G, X ^ 3 = 1 → π X ≠ 1 → ∀ J : Subgroup S,
      IsComponentOf J (Subgroup.centralizer ({π X} : Set S)) → π X ∈ J → HasLowRankBlock π X J)
    {Q : Subgroup (MulAut S)} {x : S} {J : Subgroup S} {q : ℕ} (c : I1433SCfg Q x J q)
    (hinn : ∀ β ∈ Q, ∃ t : S, MulAut.conj t = β) : False := by
  have hx3 : x ^ 3 = 1 := by rw [← c.order]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h
    have := c.order
    rw [h, orderOf_one] at this
    omega
  obtain ⟨a, b, hab, ha3, hb3, hax, hbx, hL⟩ := c.exists_heisenberg hS hinn
  have lift3 : ∀ s : S, s ^ 3 = 1 → ∃ g : G, π g = s ∧ g ^ 3 = 1 := by
    intro s hs
    obtain ⟨g₀, rfl⟩ := hπ s
    have h1 : g₀ ^ 3 ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow]; exact hs
    refine ⟨g₀ ^ 4, ?_, ?_⟩
    · rw [map_pow, show (4 : ℕ) = 1 + 3 from rfl, pow_add, pow_one, hs, mul_one]
    · have h2 := hker2 _ h1
      calc (g₀ ^ 4) ^ 3 = (g₀ ^ 3) ^ 4 := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ = ((g₀ ^ 3) ^ 2) ^ 2 := by group
        _ = 1 := by rw [h2, one_pow]
  obtain ⟨X, hπX, hX3⟩ := lift3 x hx3
  obtain ⟨A, hπA, hA3⟩ := lift3 a ha3
  obtain ⟨B, hπB, hB3⟩ := lift3 b hb3
  have hfix := fixSubgroup_conj_eq_centralizer_so x
  have hcomp3 : GLAPComponent 3 (fixSubgroup (MulAut.conj x)) J := by rw [hfix]; exact c.comp
  have hJperf : ⁅J, J⁆ = J := glaPComponent_perfect c.comp
  have hJle : J ≤ GLALayer (fixSubgroup (MulAut.conj x)) :=
    hlayer x hx3 J (by rw [hfix]; exact c.comp.1) hJperf
  have hJcomp : IsComponentOf J (Subgroup.centralizer ({x} : Set S)) := by
    rw [← hfix]; exact (glaPComponent_isComponent_of_le_layer hcomp3 hJle).1
  obtain ⟨E, _, U, _, _, _, ρ, ω, P, hP, g, hg, hω1, hω3, hρX, hperf, hPJ, hr0, hr3⟩ :=
    hblock X hX3 (by rw [hπX]; exact hx1) J (by rw [hπX]; exact hJcomp)
      (by rw [hπX]; exact c.mem)
  have hcommX : ∀ T : G, ⁅π T, x⁆ = 1 → ⁅T, X⁆ = 1 := by
    intro T hT
    set z : G := ⁅T, X⁆ with hz
    have hzker : z ∈ π.ker := by
      rw [MonoidHom.mem_ker, hz, map_commutatorElement, hπX]; exact hT
    have hzc : ∀ y : G, y * z = z * y := fun y => Subgroup.mem_center_iff.mp (hker hzker) y
    have h1 : T * X * T⁻¹ = z * X := by rw [hz, commutatorElement_def]; group
    have h2 : (T * X * T⁻¹) ^ 3 = 1 := by rw [conj_pow, hX3]; group
    have hzX : Commute z X := (hzc X).symm
    rw [h1, hzX.mul_pow, hX3, mul_one] at h2
    have h3 : z ^ 2 = 1 := hker2 z hzker
    calc z = z ^ 3 * (z ^ 2)⁻¹ := by group
      _ = 1 := by rw [h2, h3]; group
  have hAX : ⁅A, X⁆ = 1 := hcommX A (by rw [hπA]; exact hax)
  have hBX : ⁅B, X⁆ = 1 := hcommX B (by rw [hπB]; exact hbx)
  have hAC : A ∈ Subgroup.centralizer ({X} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (commutatorElement_eq_one_iff_mul_comm.mp hAX)
  have hBC : B ∈ Subgroup.centralizer ({X} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (commutatorElement_eq_one_iff_mul_comm.mp hBX)
  have hgC : g ∈ Subgroup.centralizer ({X} : Set G) := hP hg
  have hcentP : ∀ T : G, π T = a ∨ π T = b → ∀ g' ∈ P, ⁅T, g'⁆ = 1 := by
    intro T hT
    apply commutator_eq_one_of_perfect hker hperf
    intro g' hg'
    rw [MonoidHom.mem_ker, map_commutatorElement]
    have hj : π g' ∈ J := hPJ ⟨g', hg', rfl⟩
    rcases hT with h | h
    · rw [h]; exact (hL J c.comp (π g') hj).1
    · rw [h]; exact (hL J c.comp (π g') hj).2
  have hAP := hcentP A (Or.inl hπA) g hg
  have hBP := hcentP B (Or.inr hπB) g hg
  obtain ⟨c', hc'⟩ : ∃ c' : G, c' = ⁅A, B⁆ * X⁻¹ := ⟨_, rfl⟩
  have hc'ker : c' ∈ π.ker := by
    rw [MonoidHom.mem_ker, hc', map_mul, map_inv, map_commutatorElement, hπA, hπB, hπX, hab]
    exact mul_inv_cancel x
  have hc'central : ∀ y : G, y * c' = c' * y := fun y =>
    Subgroup.mem_center_iff.mp (hker hc'ker) y
  have hABz : ⁅A, B⁆ = c' * X := by rw [hc']; group
  have hAX' : A * X = X * A := commutatorElement_eq_one_iff_mul_comm.mp hAX
  have hBX' : B * X = X * B := commutatorElement_eq_one_iff_mul_comm.mp hBX
  have hzA : Commute ⁅A, B⁆ A := by
    show ⁅A, B⁆ * A = A * ⁅A, B⁆
    rw [hABz]
    calc c' * X * A = c' * (X * A) := by rw [mul_assoc]
      _ = c' * (A * X) := by rw [hAX']
      _ = (c' * A) * X := by rw [mul_assoc]
      _ = (A * c') * X := by rw [hc'central A]
      _ = A * (c' * X) := by rw [mul_assoc]
  have hzB : Commute ⁅A, B⁆ B := by
    show ⁅A, B⁆ * B = B * ⁅A, B⁆
    rw [hABz]
    calc c' * X * B = c' * (X * B) := by rw [mul_assoc]
      _ = c' * (B * X) := by rw [hBX']
      _ = (c' * B) * X := by rw [mul_assoc]
      _ = (B * c') * X := by rw [hc'central B]
      _ = B * (c' * X) := by rw [mul_assoc]
  have hcube : ⁅A, B⁆ ^ 3 = 1 := commutator_cube_eq_one hA3 hzA hzB
  have hc'1 : c' = 1 := by
    have h1 : (c' * X) ^ 3 = 1 := by rw [← hABz]; exact hcube
    have hcX : Commute c' X := (hc'central X).symm
    rw [hcX.mul_pow, hX3, mul_one] at h1
    have h2 : c' ^ 2 = 1 := hker2 c' hc'ker
    calc c' = c' ^ 3 * (c' ^ 2)⁻¹ := by group
      _ = 1 := by rw [h1, h2]; group
  have hABX : ⁅A, B⁆ = X := by rw [hABz, hc'1, one_mul]
  set A' := ρ ⟨A, hAC⟩ with hA'
  set B' := ρ ⟨B, hBC⟩ with hB'
  set g' := ρ ⟨g, hgC⟩ with hg'
  have hcomm_ρ : A' * B' * A'⁻¹ * B'⁻¹ = ρ (selfCentralizer X) := by
    have h1 : (⟨A, hAC⟩ : Subgroup.centralizer ({X} : Set G)) * ⟨B, hBC⟩ * ⟨A, hAC⟩⁻¹ *
        ⟨B, hBC⟩⁻¹ = selfCentralizer X := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, selfCentralizer]
      rw [← hABX, commutatorElement_def]
    rw [← h1, map_mul, map_mul, map_mul, map_inv, map_inv]
  have hgA : g' * A' = A' * g' := by
    rw [hA', hg', ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show g * A = A * g
    exact (commutatorElement_eq_one_iff_mul_comm.mp hAP).symm
  have hgB : g' * B' = B' * g' := by
    rw [hB', hg', ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show g * B = B * g
    exact (commutatorElement_eq_one_iff_mul_comm.mp hBP).symm
  have hAB' : A' * B' = ρ (selfCentralizer X) * (B' * A') := by
    calc A' * B' = (A' * B' * A'⁻¹ * B'⁻¹) * (B' * A') := by group
      _ = ρ (selfCentralizer X) * (B' * A') := by rw [hcomm_ρ]
  refine false_of_commute_lowRank (LinearMap.GeneralLinearGroup.generalLinearEquiv E U A')
    (LinearMap.GeneralLinearGroup.generalLinearEquiv E U B') ω hω3 hω1 ?_
    ((g' : Module.End E U) - 1) ?_ ?_ hr0 hr3
  · intro u
    have h1 := congrArg (fun w : LinearMap.GeneralLinearGroup E U => (w : Module.End E U) u) hAB'
    simp only [Units.val_mul, Module.End.mul_apply] at h1
    rw [hρX] at h1
    simpa [LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv] using h1
  · intro u
    have h1 := congrArg (fun w : LinearMap.GeneralLinearGroup E U => (w : Module.End E U) u) hgA
    simp only [Units.val_mul, Module.End.mul_apply] at h1
    simp [LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv, h1]
  · intro u
    have h1 := congrArg (fun w : LinearMap.GeneralLinearGroup E U => (w : Module.End E U) u) hgB
    simp only [Units.val_mul, Module.End.mul_apply] at h1
    simp [LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv, h1]

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

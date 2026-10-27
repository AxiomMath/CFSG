module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67CoreTools
public import CFSG.RankThree.PartOne.KC.EvenUnitaryFiveFieldActor

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement


section Aux

theorem un_commutator_eq_self_of_simple {G : Type*} [Group G] (H : Subgroup G)
    (hs : IsSimpleGroup ↥H) (hn : ¬ ∀ x y : ↥H, x * y = y * x) : ⁅H, H⁆ = H := by
  have hmap : (⊤ : Subgroup ↥H).map H.subtype = H := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hmc := Subgroup.map_commutator (H₁ := (⊤ : Subgroup ↥H)) (H₂ := ⊤) H.subtype
  rw [hmap] at hmc
  rcases hs.eq_bot_or_eq_top_of_normal (commutator ↥H) with h | h
  · exfalso
    apply hn
    intro x y
    have hxy : x * y * x⁻¹ * y⁻¹ ∈ commutator ↥H :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    rw [h, Subgroup.mem_bot] at hxy
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hxy)
  · rw [← hmc]
    have : (⁅(⊤ : Subgroup ↥H), ⊤⁆ : Subgroup ↥H) = ⊤ := h
    rw [this, hmap]

theorem un_eq_one_of_mem_zpowers_coprime {G : Type*} [Group G] {b a : G} {r c : ℕ}
    (hbr : b ^ r = 1) (hcop : Nat.Coprime c r) (ha : a ∈ Subgroup.zpowers b)
    (hac : a ^ c = 1) : a = 1 := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have har : (b ^ m) ^ r = 1 := by
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hbr,
      _root_.one_zpow]
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hac)
    (orderOf_dvd_of_pow_eq_one har))

theorem un_center_eq_bot_of_simple {T : Type} [Group T] (hs : IsSimpleGroup T)
    (hn : ∃ a b : T, a * b ≠ b * a) : Subgroup.center T = ⊥ := by
  obtain ⟨a₀, b₀, hab₀⟩ := hn
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
  · exact h
  · exfalso
    apply hab₀
    have ha : a₀ ∈ Subgroup.center T := h ▸ Subgroup.mem_top a₀
    exact (Subgroup.mem_center_iff.mp ha b₀).symm

end Aux

section Core

variable {T : Type} [Group T]

theorem un_false_of_simple_fixed {r : ℕ} {V Z : Subgroup (MulAut T)}
    (hcen : Subgroup.center T = ⊥) (h2 : N2Cfg T r V Z) (h3 : N3Deriv T V Z) {b : MulAut T}
    (hbr : b ^ r = 1) (hb1 : b ≠ 1) (hbV : b ∈ V) (H : Subgroup T) (hHs : IsSimpleGroup ↥H)
    (hHn : ¬ ∀ x y : ↥H, x * y = y * x) (hHfix : H ≤ fixSub b)
    (hconjH : ∀ y ∈ fixSub b, ∀ c ∈ H, y * c * y⁻¹ ∈ H)
    (hfixH : ∀ a : MulAut T, (∀ y ∈ H, a y = y) → a ∈ Subgroup.zpowers b) : False := by
  classical
  obtain ⟨hr, -, -, -, hZab, -, hZcop, hZbot, hcomm⟩ := h2
  have hinj := mulAut_conj_injective_of_center_bot hcen
  have hHperf : ⁅H, H⁆ = H := un_commutator_eq_self_of_simple H hHs hHn
  have hHder : H ≤ ⁅fixSub b, fixSub b⁆ := hHperf ▸ Subgroup.commutator_mono hHfix hHfix
  have hnorm : ∀ c ∈ H, MulAut.conj c ∈ normalizer (Z : Set (MulAut T)) :=
    fun c hc => h3 b hbV hb1 c (hHder hc)
  set D : Subgroup T := Z.comap (MulAut.conj : T →* MulAut T) with hDdef
  have hDmem : ∀ u, u ∈ D ↔ MulAut.conj u ∈ Z := fun u => Iff.rfl
  have hDab : ∀ u ∈ D, ∀ v ∈ D, u * v = v * u := by
    intro u hu v hv
    apply hinj
    rw [map_mul, map_mul]
    exact hZab _ hu _ hv
  have hDfix : ∀ u ∈ D, b u = u := by
    intro u hu
    have h1 := hcomm b hbV _ hu
    apply hinj
    rw [← mulAut_conj_conj, h1]
    group
  have hDnorm : ∀ c ∈ H, ∀ u ∈ D, c * u * c⁻¹ ∈ D := by
    intro c hc u hu
    have := (Subgroup.mem_normalizer_iff.mp (hnorm c hc) (MulAut.conj u)).mp hu
    rw [hDmem, map_mul, map_mul, map_inv]
    exact this
  have hDH : ∀ x ∈ D, x ∈ H → x = 1 := by
    let A : Subgroup ↥H := (D ⊓ H).subgroupOf H
    have hAn : A.Normal := ⟨fun a ha g => by
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      refine ⟨?_, (g * a * g⁻¹).2⟩
      have := hDnorm g g.2 a ha.1
      simpa using this⟩
    rcases hHs.eq_bot_or_eq_top_of_normal A with h | h
    · intro x hx hxH
      have : (⟨x, hxH⟩ : ↥H) ∈ A := Subgroup.mem_subgroupOf.mpr ⟨hx, hxH⟩
      rw [h, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    · exfalso
      apply hHn
      intro x y
      have hx : (x : T) ∈ D := by
        have : x ∈ A := h ▸ Subgroup.mem_top x
        exact (Subgroup.mem_subgroupOf.mp this).1
      have hy : (y : T) ∈ D := by
        have : y ∈ A := h ▸ Subgroup.mem_top y
        exact (Subgroup.mem_subgroupOf.mp this).1
      exact Subtype.ext (hDab _ hx _ hy)
  have hDcommH : ∀ c ∈ H, ∀ u ∈ D, c * u = u * c := by
    intro c hc u hu
    have hw : c * u * c⁻¹ * u⁻¹ ∈ D := D.mul_mem (hDnorm c hc u hu) (D.inv_mem hu)
    have hwH : c * u * c⁻¹ * u⁻¹ ∈ H := by
      have h1 := hconjH u (mem_fixSub.mpr (hDfix u hu)) c⁻¹ (H.inv_mem hc)
      have : c * u * c⁻¹ * u⁻¹ = c * (u * c⁻¹ * u⁻¹) := by group
      rw [this]
      exact H.mul_mem hc h1
    have := hDH _ hw hwH
    calc c * u = (c * u * c⁻¹ * u⁻¹) * (u * c) := by group
      _ = u * c := by rw [this, one_mul]
  have hZcard : ∀ a ∈ Z, a ^ Nat.card ↥Z = 1 := by
    intro a ha
    have h' : (⟨a, ha⟩ : ↥Z) ^ Nat.card ↥Z = 1 := pow_card_eq_one'
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using congrArg Subtype.val h'
  have hD1 : ∀ u ∈ D, u = 1 := by
    intro u hu
    have hfix : ∀ y ∈ H, MulAut.conj u y = y := by
      intro y hy
      rw [MulAut.conj_apply]
      have := hDcommH y hy u hu
      calc u * y * u⁻¹ = (y * u) * u⁻¹ := by rw [this]
        _ = y := by group
    have hconj1 : MulAut.conj u = 1 :=
      un_eq_one_of_mem_zpowers_coprime hbr hZcop (hfixH _ hfix) (hZcard _ hu)
    exact hinj (by rw [hconj1, map_one])
  have hZfix : ∀ z ∈ Z, ∀ c ∈ H, z c = c := by
    intro z hz c hc
    have h1 := (Subgroup.mem_normalizer_iff.mp (hnorm c hc) z).mp hz
    have h4 : MulAut.conj c * z * (MulAut.conj c)⁻¹ * z⁻¹ ∈ Z := Z.mul_mem h1 (Z.inv_mem hz)
    have h5 : MulAut.conj c * z * (MulAut.conj c)⁻¹ * z⁻¹ = MulAut.conj (c * z c⁻¹) := by
      have : z * (MulAut.conj c)⁻¹ * z⁻¹ = MulAut.conj (z c⁻¹) := by
        have := mulAut_conj_conj z c⁻¹
        simpa [map_inv] using this
      calc MulAut.conj c * z * (MulAut.conj c)⁻¹ * z⁻¹
          = MulAut.conj c * (z * (MulAut.conj c)⁻¹ * z⁻¹) := by group
        _ = MulAut.conj (c * z c⁻¹) := by rw [this, map_mul]
    rw [h5] at h4
    have h6 := hD1 _ h4
    have : z c⁻¹ = c⁻¹ := by
      have := congrArg (fun t => c⁻¹ * t) h6
      simpa using this
    have := congrArg (fun t => t⁻¹) this
    simpa using this
  apply hZbot
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  exact un_eq_one_of_mem_zpowers_coprime hbr hZcop (hfixH z (hZfix z hz)) (hZcard z hz)

end Core

section Unitary

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.Classical CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KCEvenUnitaryFive

variable {p f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem false_of_u_fieldAut_mem (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ p ^ f = 2)) (hp2 : p ≠ 2) {r : ℕ}
    {V Z : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))}
    (h2 : N2Cfg (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) r V Z)
    (h3 : N3Deriv (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) V Z)
    {σ : K ≃+* K} (hσ : orderOf σ = r)
    (hb : primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ ∈ V) : False := by
  classical
  have : Finite K := h.finite
  have hr : r.Prime := h2.1
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact absurd h2.2.1 (by decide)
  set b := primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ with hbdef
  have hbr : b ^ r = 1 := by rw [hbdef, ← map_pow, ← hσ, pow_orderOf_eq_one, map_one]
  have hb1 : b ≠ 1 := by
    intro h1
    have := primeFormFieldHom_injective h n hn hq (h1.trans (map_one _).symm)
    rw [this, orderOf_one] at hσ
    exact hr.one_lt.ne hσ
  have hTs := isSimpleGroup_primeFormP_one h hn hq
  have hTn := not_commute_primeFormP_one h hn hq
  have hcen : Subgroup.center (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      ⊥ := by
    refine un_center_eq_bot_of_simple hTs ?_
    by_contra hcon
    push Not at hcon
    exact hTn fun x y => hcon x y
  set h₀ := fixSubfield_unitaryFieldData h hr hr2 hσ with hh₀
  have hbar := fixSubfield_unitaryFieldData_bar h hr hr2 hσ
  have hq₀ : ¬(n = 3 ∧ p ^ (f / r) = 2) := by
    rintro ⟨-, h4⟩
    have : p ∣ p ^ (f / r) := dvd_pow_self p (by
      have := (dvd_and_card_fixSubfield_unitary h hr hr2 hσ).1
      have := h₀.one_le
      omega)
    rw [h4] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 this)
  set H : Subgroup (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    (subfieldPSU h h₀ hbar n).range with hH
  have hinj := subfieldPSU_injective h h₀ hbar n (by omega)
  let eJ : primeFormP h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ)) ≃* H := MonoidHom.ofInjective hinj
  have hs0 := isSimpleGroup_primeFormP_one h₀ hn hq₀
  have hnc := not_commute_primeFormP_one h₀ hn hq₀
  have hHs : IsSimpleGroup ↥H := eJ.symm.isSimpleGroup
  have hHn : ¬ ∀ x y : ↥H, x * y = y * x := fun hc => hnc fun x y => by
    have h1 := congrArg eJ.symm (hc (eJ x) (eJ y))
    rwa [map_mul, map_mul, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at h1
  have hHfix : H ≤ fixSub b := fun y hy => mem_fixSub.2 (range_subfieldPSU_le h n h₀ hbar hy)
  have hconjH : ∀ y ∈ fixSub b, ∀ c ∈ H, y * c * y⁻¹ ∈ H := by
    intro y hy c hc
    have hy' : b y = y := mem_fixSub.1 hy
    have hcomm : (MulAut.conj y : MulAut (primeFormP h ((1 : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K))) * b = b * MulAut.conj y := by
      have h1 := mulAut_conj_conj b y
      rw [hy'] at h1
      calc MulAut.conj y * b = (b * MulAut.conj y * b⁻¹) * b := by rw [h1]
        _ = b * MulAut.conj y := by group
    have h1 := map_mem_range_of_commute h hbar n hn hq₀ hcomm hc
    have e : (MulAut.conj y : MulAut (primeFormP h ((1 : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K))) c = y * c * y⁻¹ := MulAut.conj_apply y c
    rw [e] at h1
    exact h1
  have hfixH : ∀ a : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)),
      (∀ y ∈ H, a y = y) → a ∈ Subgroup.zpowers b := by
    intro a ha
    obtain ⟨hfixing, hmap, -⟩ := fixingSubgroup_range_subfieldPSU h n h₀ hbar hn hq hq₀
    have : a ∈ fixingSubgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K))) (H : Set (primeFormP h ((1 : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K))) :=
      (mem_fixingSubgroup_iff _).2 fun y hy => by rw [MulAut.smul_def]; exact ha y hy
    rw [hH, hfixing, hmap] at this
    exact this
  exact un_false_of_simple_fixed hcen h2 h3 hbr hb1 hb H hHs hHn hHfix hconjH hfixH

theorem un_congr_eq {Y : Type} [Group Y] (φ α : MulAut Y) :
    MulAut.congr φ α = φ * α * φ⁻¹ := by
  ext y
  simp [MulAut.congr_apply]

theorem false_of_u_noninner (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ p ^ f = 2)) (hp2 : p ≠ 2) {r : ℕ}
    (hrp : r ≠ p)
    {V Z : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))}
    (h2 : N2Cfg (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) r V Z)
    (h3 : N3Deriv (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) V Z)
    (hVD : ¬ V ≤ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) : False := by
  classical
  have : Finite K := h.finite
  obtain ⟨b, hbV, hbD⟩ := IsConcreteLE.not_le_iff_exists.mp hVD
  obtain ⟨hr, hrodd, hVe, -⟩ := id h2
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact absurd hrodd (by decide)
  have : Fact r.Prime := ⟨hr⟩
  have hbr : b ^ r = 1 := elemPow_eq_one_of_isElementaryAbelian b hbV
  have hb1 : b ≠ 1 := fun h1 => hbD (h1 ▸ one_mem _)
  have hord : orderOf b = r := orderOf_eq_prime hbr hb1
  set σ := primeFormFieldFactor h (isPrimeFormGram_one (n := n)) hn hq b with hσdef
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply hbD
    rw [← ker_primeFormFieldFactor h (isPrimeFormGram_one (n := n)) hn hq]
    exact h1
  have hσr : σ ^ r = 1 := by rw [hσdef, ← map_pow, hbr, map_one]
  have hσord : orderOf σ = r := orderOf_eq_prime hσr hσ1
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn hq hr hr2 hrp b hord
      σ rfl hσord
  have h2' := h2.map_mulEquiv (MulAut.congr (primeFormConjHom h ((1 : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K) M)⁻¹)
  have h3' := h3.map_mulEquiv (primeFormConjHom h ((1 : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K) M)⁻¹
  refine false_of_u_fieldAut_mem h hn hq hp2 h2' h3' hσord ⟨b, hbV, ?_⟩
  show MulAut.congr (primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M)⁻¹ b =
    primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ
  rw [un_congr_eq, inv_inv, ← hM]

end Unitary

end CFSG.GH74.GLS.Stage2.Bender.Thm1

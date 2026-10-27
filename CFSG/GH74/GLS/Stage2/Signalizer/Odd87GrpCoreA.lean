module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpDefs
public import Mathlib.GroupTheory.Nilpotent
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup
open scoped commutatorElement

namespace CoreA

section Normalizers

variable {A : Type} [Group A]

theorem eq_one_of_mem_of_mem {p : ℕ} {W X : Subgroup A} (hp : p.Prime) (hodd : p ≠ 2)
    (hW : IsPGroup 2 ↥W) (hX : IsPGroup p ↥X) {g : A} (hgW : g ∈ W) (hgX : g ∈ X) : g = 1 := by
  obtain ⟨k, hk⟩ := hW ⟨g, hgW⟩
  obtain ⟨m, hm⟩ := hX ⟨g, hgX⟩
  have hk' : g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hm' : g ^ p ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hcop : Nat.Coprime (2 ^ k) (p ^ m) :=
    Nat.Coprime.pow k m ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hodd))
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_iff_pow_eq_one.2 hk')
    (orderOf_dvd_iff_pow_eq_one.2 hm'))

theorem mem_centralizer_of_mem_normalizer {p : ℕ} {W X : Subgroup A} {z : A}
    (h : Setup412 p W X z) {c : A} (hc : c ∈ W) (hcn : c ∈ normalizer (X : Set A)) :
    c ∈ centralizer (X : Set A) := by
  rw [mem_centralizer_iff]
  intro x hx
  have h1 : c * x * c⁻¹ * x⁻¹ ∈ X :=
    X.mul_mem ((mem_normalizer_iff.mp hcn x).mp hx) (X.inv_mem hx)
  have h2 : c * x * c⁻¹ * x⁻¹ ∈ W := by
    have : c * (x * c⁻¹ * x⁻¹) ∈ W :=
      W.mul_mem hc ((mem_normalizer_iff.mp (h.XW hx) c⁻¹).mp (W.inv_mem hc))
    simpa [mul_assoc] using this
  have h3 : ⁅c, x⁆ = 1 := by
    simpa [commutatorElement_def] using eq_one_of_mem_of_mem h.prime h.odd h.W2 h.Xp h2 h1
  exact (commutatorElement_eq_one_iff_mul_comm.1 h3).symm

theorem mem_centralizer_of_commute {p : ℕ} {W X : Subgroup A} {z : A}
    (h : Setup412 p W X z) {c : A} (hc : c ∈ W) (hcz : c * z = z * c) :
    c ∈ centralizer (X : Set A) :=
  mem_centralizer_of_mem_normalizer h hc (h.Cz c hc hcz)

theorem mem_normalizer_commutator {H K : Subgroup A} {g : A} (hH : g ∈ normalizer (H : Set A))
    (hK : g ∈ normalizer (K : Set A)) : g ∈ normalizer ((⁅H, K⁆ : Subgroup A) : Set A) := by
  have key : ∀ g : A, g ∈ normalizer (H : Set A) → g ∈ normalizer (K : Set A) →
      ∀ c ∈ (⁅H, K⁆ : Subgroup A), g * c * g⁻¹ ∈ (⁅H, K⁆ : Subgroup A) := by
    intro g hH hK
    have hle : (⁅H, K⁆ : Subgroup A) ≤
        (⁅H, K⁆ : Subgroup A).comap (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro h hh k hk
      show g * ⁅h, k⁆ * g⁻¹ ∈ (⁅H, K⁆ : Subgroup A)
      have e : g * ⁅h, k⁆ * g⁻¹ = ⁅g * h * g⁻¹, g * k * g⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.commutator_mem_commutator ((mem_normalizer_iff.mp hH h).mp hh)
        ((mem_normalizer_iff.mp hK k).mp hk)
    intro c hc
    exact hle hc
  rw [mem_normalizer_iff]
  intro c
  refine ⟨key g hH hK c, fun hc => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hH) (Subgroup.inv_mem _ hK) _ hc
  simpa [mul_assoc] using this

theorem mem_normalizer_center {W : Subgroup A} {g : A} (hg : g ∈ normalizer (W : Set A)) :
    g ∈ normalizer ((W ⊓ centralizer (W : Set A) : Subgroup A) : Set A) := by
  have key : ∀ g : A, g ∈ normalizer (W : Set A) →
      ∀ c ∈ (W ⊓ centralizer (W : Set A) : Subgroup A), g * c * g⁻¹ ∈
        (W ⊓ centralizer (W : Set A) : Subgroup A) := by
    intro g hg c hc
    obtain ⟨hcW, hcC⟩ := Subgroup.mem_inf.1 hc
    refine Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.mp hg c).mp hcW, ?_⟩
    rw [mem_centralizer_iff]
    intro w hw
    have hw' : g⁻¹ * w * g ∈ W := by
      have := (mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) w).mp hw
      simpa using this
    have hcomm : (g⁻¹ * w * g) * c = c * (g⁻¹ * w * g) := mem_centralizer_iff.mp hcC _ hw'
    calc w * (g * c * g⁻¹) = g * ((g⁻¹ * w * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * w * g)) * g⁻¹ := by rw [hcomm]
      _ = g * c * g⁻¹ * w := by group
  rw [mem_normalizer_iff]
  intro c
  refine ⟨key g hg c, fun hc => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hc
  simpa [mul_assoc] using this

theorem mem_normalizer_lowerCentralSeries {W : Subgroup A} {g : A}
    (hg : g ∈ normalizer (W : Set A)) (n : ℕ) :
    g ∈ normalizer ((W.lowerCentralSeries n : Subgroup A) : Set A) := by
  have hmap : ∀ g : A, g ∈ normalizer (W : Set A) → W.map (MulAut.conj g).toMonoidHom ≤ W := by
    intro g hg
    rintro _ ⟨w, hw, rfl⟩
    exact (mem_normalizer_iff.mp hg w).mp hw
  have key : ∀ g : A, g ∈ normalizer (W : Set A) →
      ∀ y ∈ W.lowerCentralSeries n, g * y * g⁻¹ ∈ W.lowerCentralSeries n := by
    intro g hg y hy
    have h1 : (W.lowerCentralSeries n).map (MulAut.conj g).toMonoidHom ≤ W.lowerCentralSeries n := by
      rw [Subgroup.map_lowerCentralSeries]
      exact Subgroup.lowerCentralSeries_mono n (hmap g hg)
    exact h1 ⟨y, hy, rfl⟩
  rw [mem_normalizer_iff]
  intro c
  refine ⟨key g hg c, fun hc => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hc
  simpa [mul_assoc] using this

end Normalizers

section CoprimeAction

variable {A : Type} [Group A] [Finite A]

theorem odd_natCard {p : ℕ} {W X : Subgroup A} {z : A} (h : Setup412 p W X z) :
    Odd (Nat.card ↥X) := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨n, hn⟩ := h.Xp.exists_card_eq
  rw [hn]
  exact (h.prime.odd_of_ne_two h.odd).pow

theorem coprime_natCard {p : ℕ} {W X : Subgroup A} {z : A} (h : Setup412 p W X z) :
    Nat.Coprime (Nat.card ↥X) (Nat.card ↥W) := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨n, hn⟩ := h.Xp.exists_card_eq
  obtain ⟨m, hm⟩ := h.W2.exists_card_eq
  rw [hn, hm]
  exact Nat.Coprime.pow n m ((Nat.coprime_primes h.prime Nat.prime_two).2 h.odd)

theorem exists_ne_one_commute {B : Subgroup A} {z : A} (hB2 : IsPGroup 2 ↥B) (hB : B ≠ ⊥)
    (hz : z ∈ normalizer (B : Set A)) (hz2 : z * z = 1) :
    ∃ b ∈ B, b ≠ 1 ∧ z * b = b * z := by
  classical
  have hti : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hmem : ∀ x : ↥B, z * (x : A) * z⁻¹ ∈ B := fun x => (mem_normalizer_iff.mp hz x).mp x.2
  let σ : Function.End ↥B := fun x => ⟨z * x * z⁻¹, hmem x⟩
  have hσ : σ ^ 2 ^ 1 = 1 := by
    funext x
    apply Subtype.ext
    show z * (z * (x : A) * z⁻¹) * z⁻¹ = x
    rw [hti]
    calc z * (z * (x : A) * z) * z = (z * z) * (x : A) * (z * z) := by group
      _ = x := by rw [hz2]; group
  have : Fintype ↥B := Fintype.ofFinite _
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := ↥B) (f := σ) (p := 2) (n := 1) hσ
    (hp := ⟨Nat.prime_two⟩)
  obtain ⟨k, hk⟩ := hB2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hB
    have : Nat.card ↥B = 1 := by simpa using hk
    exact (Subgroup.card_eq_one).1 this
  have hcardB : Fintype.card ↥B = 2 ^ k := by rw [← hk, Nat.card_eq_fintype_card]
  by_contra hcon
  have hcon' : ∀ b ∈ B, b ≠ 1 → z * b ≠ b * z := fun b hb h1 h2 => hcon ⟨b, hb, h1, h2⟩
  have hone : Fintype.card ↑(Function.fixedPoints σ) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨1, ?_⟩, fun y => ?_⟩
    · apply Subtype.ext
      show z * (1 : A) * z⁻¹ = 1
      simp
    · refine Subtype.ext (Subtype.ext ?_)
      show ((y : ↥B) : A) = 1
      by_contra hy
      have hyfix : σ y.1 = y.1 := y.2
      have := congrArg Subtype.val hyfix
      have hcomm : z * ((y : ↥B) : A) = ((y : ↥B) : A) * z := by
        have h' : z * ((y : ↥B) : A) * z⁻¹ = ((y : ↥B) : A) := this
        calc z * ((y : ↥B) : A) = (z * ((y : ↥B) : A) * z⁻¹) * z := by group
          _ = ((y : ↥B) : A) * z := by rw [h']
      exact hcon' ((y : ↥B) : A) (y : ↥B).2 hy hcomm
  rw [hone, hcardB] at hmod
  have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 hk0
  have h3 : 2 ^ k % 2 = 1 % 2 := hmod
  have h4 : 2 ^ k % 2 = 0 := Nat.mod_eq_zero_of_dvd h2
  omega

theorem commutator_inf_centralizer_le_commutator {V X : Subgroup A} (hV : IsPGroup 2 ↥V)
    (hXV : X ≤ normalizer (V : Set A)) (hX : Odd (Nat.card ↥X)) :
    ⁅V, X⁆ ⊓ centralizer (X : Set A) ≤ ⁅V, V⁆ := by
  classical
  have : Fintype ↥X := Fintype.ofFinite _
  let act : ↥X → ↥V → ↥V := fun x v =>
    ⟨(x : A) * v * (x : A)⁻¹, (mem_normalizer_iff.mp (hXV x.2) v).mp v.2⟩
  have act_coe : ∀ x v, ((act x v : ↥V) : A) = (x : A) * v * (x : A)⁻¹ := fun _ _ => rfl
  have act_mul : ∀ x v w, act x (v * w) = act x v * act x w := by
    intro x v w
    apply Subtype.ext
    simp only [act_coe, Subgroup.coe_mul]
    group
  have act_one : ∀ x, act x 1 = 1 := by
    intro x
    apply Subtype.ext
    simp [act_coe]
  have act_act : ∀ x y v, act x (act y v) = act (x * y) v := by
    intro x y v
    apply Subtype.ext
    simp only [act_coe, Subgroup.coe_mul, mul_inv_rev]
    group
  let N : ↥V →* Abelianization ↥V :=
    { toFun := fun v => ∏ x : ↥X, Abelianization.of (act x v)
      map_one' := by simp [act_one]
      map_mul' := by
        intro v w
        simp only [act_mul, map_mul]
        exact Finset.prod_mul_distrib }
  have hN_act : ∀ y v, N (act y v) = N v := by
    intro y v
    show ∏ x : ↥X, Abelianization.of (act x (act y v)) = ∏ x : ↥X, Abelianization.of (act x v)
    exact Fintype.prod_equiv (Equiv.mulRight y) _ _ (fun x => by simp [act_act])
  have hker : ⁅V, X⁆ ≤ (N.ker).map V.subtype := by
    rw [Subgroup.commutator_le]
    intro w hw y hy
    refine Subgroup.mem_map.2 ⟨(⟨w, hw⟩ : ↥V) * act ⟨y, hy⟩ (⟨w, hw⟩ : ↥V)⁻¹, ?_, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, hN_act, map_inv, mul_inv_cancel]
    · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, act_coe, Subgroup.coe_inv,
        commutatorElement_def]
      group
  intro c ⟨hcK, hcC⟩
  obtain ⟨v, hv, hvc⟩ := Subgroup.mem_map.1 (hker hcK)
  have hfix : ∀ x : ↥X, act x v = v := by
    intro x
    apply Subtype.ext
    rw [act_coe]
    have hxc : (x : A) * c = c * (x : A) := mem_centralizer_iff.mp hcC x x.2
    have hvc' : ((v : ↥V) : A) = c := hvc
    rw [hvc', hxc]
    group
  have hNv : N v = (Abelianization.of v) ^ Nat.card ↥X := by
    show ∏ x : ↥X, Abelianization.of (act x v) = _
    simp only [hfix]
    rw [Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]
  have hNv1 : N v = 1 := hv
  rw [hNv] at hNv1
  obtain ⟨k, hk⟩ := hV v
  have hk' : (Abelianization.of v) ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
  have hcop : Nat.Coprime (2 ^ k) (Nat.card ↥X) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hX)
  have hord : orderOf (Abelianization.of v) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_iff_pow_eq_one.2 hk')
      (orderOf_dvd_iff_pow_eq_one.2 hNv1)
  have hv1 : Abelianization.of v = 1 := orderOf_eq_one_iff.1 hord
  have hvker : v ∈ (Abelianization.of (G := ↥V)).ker := hv1
  rw [Abelianization.ker_of, _root_.commutator_def] at hvker
  have : ((v : ↥V) : A) ∈ Subgroup.map V.subtype ⁅(⊤ : Subgroup ↥V), (⊤ : Subgroup ↥V)⁆ :=
    ⟨v, hvker, rfl⟩
  rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.subtype_range] at this
  rw [← hvc]
  exact this

theorem abelian_centralized {p : ℕ} {W X : Subgroup A} {z : A} (h : Setup412 p W X z)
    {U : Subgroup A} (hUW : U ≤ W) (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hXU : X ≤ normalizer (U : Set A)) (hzU : z ∈ normalizer (U : Set A)) :
    ∀ x ∈ X, ∀ u ∈ U, x * u = u * x := by
  have hU2 : IsPGroup 2 ↥U := h.W2.to_le hUW
  have hnorm := commutator_inf_centralizer_le_commutator hU2 hXU (odd_natCard h)
  have hUU : (⁅U, U⁆ : Subgroup A) = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro u hu
    rw [mem_centralizer_iff]
    intro v hv
    exact hUab v hv u hu
  have hBU : (⁅U, X⁆ : Subgroup A) ≤ U := (Subgroup.le_normalizer_iff_commutator_le_left).mp hXU
  have hB : (⁅U, X⁆ : Subgroup A) = ⊥ := by
    by_contra hne
    have hzB : z ∈ normalizer ((⁅U, X⁆ : Subgroup A) : Set A) :=
      mem_normalizer_commutator hzU h.zX
    obtain ⟨b, hbB, hb1, hbz⟩ := exists_ne_one_commute (h.W2.to_le (hBU.trans hUW)) hne hzB h.z2
    have hbX : b ∈ centralizer (X : Set A) :=
      mem_centralizer_of_commute h (hUW (hBU hbB)) hbz.symm
    have : b ∈ (⁅U, U⁆ : Subgroup A) := hnorm ⟨hbB, hbX⟩
    rw [hUU] at this
    exact hb1 (Subgroup.mem_bot.1 this)
  intro x hx u hu
  have : ⁅u, x⁆ ∈ (⁅U, X⁆ : Subgroup A) := Subgroup.commutator_mem_commutator hu hx
  rw [hB, Subgroup.mem_bot] at this
  have := commutatorElement_eq_one_iff_mul_comm.1 this
  exact this.symm

theorem abelian_le_centralizer {p : ℕ} {W X : Subgroup A} {z : A} (h : Setup412 p W X z)
    (hW : ⁅W, X⁆ = W) {U : Subgroup A} (hUW : U ≤ W)
    (hUn : ∀ w ∈ W, ∀ u ∈ U, w * u * w⁻¹ ∈ U) (hXU : X ≤ normalizer (U : Set A))
    (hzU : z ∈ normalizer (U : Set A)) (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) :
    U ≤ centralizer (W : Set A) := by
  have hXc := abelian_centralized h hUW hUab hXU hzU
  have hle : (⁅W, X⁆ : Subgroup A) ≤ centralizer (U : Set A) := by
    rw [Subgroup.commutator_le]
    intro w hw x hx
    rw [mem_centralizer_iff]
    intro u hu
    have hu' : w⁻¹ * u * w ∈ U := by
      have := hUn w⁻¹ (W.inv_mem hw) u hu
      simpa using this
    have hxu : x * u = u * x := hXc x hx u hu
    have hxu' : x * (w⁻¹ * u * w) = (w⁻¹ * u * w) * x := hXc x hx _ hu'
    have hxu'' : u * x⁻¹ = x⁻¹ * u := by
      calc u * x⁻¹ = x⁻¹ * (x * u) * x⁻¹ := by group
        _ = x⁻¹ * (u * x) * x⁻¹ := by rw [hxu]
        _ = x⁻¹ * u := by group
    calc u * ⁅w, x⁆ = u * (w * x * w⁻¹ * x⁻¹) := by rw [commutatorElement_def]
      _ = w * ((w⁻¹ * u * w) * x) * w⁻¹ * x⁻¹ := by group
      _ = w * (x * (w⁻¹ * u * w)) * w⁻¹ * x⁻¹ := by rw [← hxu']
      _ = w * x * w⁻¹ * (u * x⁻¹) := by group
      _ = w * x * w⁻¹ * (x⁻¹ * u) := by rw [hxu'']
      _ = ⁅w, x⁆ * u := by rw [commutatorElement_def]; group
  intro u hu
  rw [mem_centralizer_iff]
  intro w hw
  have hw' : w ∈ (⁅W, X⁆ : Subgroup A) := by rw [hW]; exact hw
  exact (mem_centralizer_iff.mp (hle hw') u hu).symm

theorem lowerCentralSeries_two_eq_bot {p : ℕ} {W X : Subgroup A} {z : A} (h : Setup412 p W X z)
    (hW : ⁅W, X⁆ = W) : W.lowerCentralSeries 2 = ⊥ := by
  have hnil : Group.IsNilpotent ↥W := h.W2.isNilpotent
  obtain ⟨N, hN⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries W).1 hnil
  have step : ∀ j : ℕ, 1 ≤ j → W.lowerCentralSeries (j + 2) = ⊥ →
      W.lowerCentralSeries (j + 1) = ⊥ := by
    intro j hj hj2
    have hY1 : W.lowerCentralSeries j ≤ ⁅W, W⁆ := by
      have := Subgroup.lowerCentralSeries_antitone W hj
      simpa using this
    have hY2 : (⁅⁅W.lowerCentralSeries j, W⁆, W⁆ : Subgroup A) = ⊥ := hj2
    have h3 : (⁅⁅W, W⁆, W.lowerCentralSeries j⁆ : Subgroup A) = ⊥ := by
      refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ hY2
      rw [Subgroup.commutator_comm W (W.lowerCentralSeries j)]
      exact hY2
    have hab : ∀ a ∈ W.lowerCentralSeries j, ∀ b ∈ W.lowerCentralSeries j, a * b = b * a := by
      intro a ha b hb
      have h4 : ⁅a, b⁆ ∈ (⁅⁅W, W⁆, W.lowerCentralSeries j⁆ : Subgroup A) :=
        Subgroup.commutator_mem_commutator (hY1 ha) hb
      rw [h3, Subgroup.mem_bot] at h4
      exact (commutatorElement_eq_one_iff_mul_comm.1 h4)
    have hcent := abelian_le_centralizer h hW (U := W.lowerCentralSeries j)
      (Subgroup.lowerCentralSeries_le_self W j)
      (fun w hw u hu => (mem_normalizer_iff.mp
        (Subgroup.self_le_normalizer_lowerCentralSeries W j hw) u).mp hu)
      (fun x hx => mem_normalizer_lowerCentralSeries (h.XW hx) j)
      (mem_normalizer_lowerCentralSeries h.zW j) hab
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hcent
  have key : ∀ k : ℕ, W.lowerCentralSeries (2 + k) = ⊥ → W.lowerCentralSeries 2 = ⊥ := by
    intro k
    induction k with
    | zero => exact id
    | succ k ih =>
      intro hk
      apply ih
      have := step (1 + k) (by omega) (by simpa [add_assoc, add_comm, add_left_comm] using hk)
      simpa [add_assoc, add_comm, add_left_comm] using this
  apply key N
  rw [eq_bot_iff, ← hN]
  exact Subgroup.lowerCentralSeries_antitone W (Nat.le_add_left N 2)

theorem le_commutator_sup_inf_centralizer {P X : Subgroup A}
    (hXP : X ≤ normalizer (P : Set A)) (hsolv : Group.IsSolvable ↥P)
    (hcop : Nat.Coprime (Nat.card X) (Nat.card P)) :
    P ≤ ⁅P, X⁆ ⊔ (P ⊓ centralizer (X : Set A)) := by
  have : Subgroup.Normalizes X P := ⟨hXP⟩
  have hsup := CFSG.fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
    (A := ↥X) (G := ↥P) hsolv hcop
  have hcommMap : (CFSG.commutatorAction (A := ↥X) (G := ↥P)).map P.subtype = ⁅P, X⁆ :=
    CFSG.commutatorAction_subgroup_conj_map_eq_commutator P X hXP
  have hfixEq : CFSG.fixedPointSubgroup ↥X ↥P =
      (P ⊓ centralizer (X : Set A)).subgroupOf P := by
    simpa [CFSG.subgroupCentralizerIn] using
      CFSG.fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn P X hXP
  intro x hx
  have htop : (⟨x, hx⟩ : ↥P) ∈ CFSG.fixedPointSubgroup ↥X ↥P ⊔
      CFSG.commutatorAction (A := ↥X) (G := ↥P) := by
    rw [hsup]
    exact Subgroup.mem_top _
  have hmap := Subgroup.mem_map_of_mem P.subtype htop
  rw [Subgroup.map_sup, hcommMap, hfixEq, Subgroup.map_subgroupOf_eq_of_le inf_le_left] at hmap
  rw [sup_comm]
  exact hmap

omit [Finite A] in
theorem commutator_commutator_eq_of_coprime {P X : Subgroup A}
    (hXP : X ≤ normalizer (P : Set A)) (hcop : Nat.Coprime (Nat.card X) (Nat.card P)) :
    ⁅⁅P, X⁆, X⁆ = ⁅P, X⁆ := by
  classical
  have : Subgroup.Normalizes X P := ⟨hXP⟩
  have h2 : CFSG.commutatorAction₂ (A := ↥X) (G := ↥P) =
      CFSG.commutatorAction (A := ↥X) (G := ↥P) :=
    CFSG.commutatorAction₂_eq_commutatorAction_of_coprime (G := ↥P) (A := ↥X) hcop
  have hmap : (CFSG.commutatorAction (A := ↥X) (G := ↥P)).map P.subtype = ⁅P, X⁆ :=
    CFSG.commutatorAction_subgroup_conj_map_eq_commutator P X hXP
  have hmap2 : (CFSG.commutatorAction₂ (A := ↥X) (G := ↥P)).map P.subtype ≤ ⁅⁅P, X⁆, X⁆ := by
    let C : Subgroup ↥P := CFSG.commutatorAction (A := ↥X) (G := ↥P)
    let S : Set ↥P := {x : ↥P | ∃ a : ↥X, ∃ h : ↥P, h ∈ C ∧ x = h⁻¹ * (a • h)}
    calc (CFSG.commutatorAction₂ (A := ↥X) (G := ↥P)).map P.subtype =
          (Subgroup.closure S).map P.subtype := rfl
      _ = Subgroup.closure (P.subtype '' S) := by
        simpa using (MonoidHom.map_closure (f := P.subtype) S)
      _ ≤ ⁅⁅P, X⁆, X⁆ := by
        refine (Subgroup.closure_le (K := ⁅⁅P, X⁆, X⁆)).2 ?_
        rintro _ ⟨y, hy, rfl⟩
        rcases hy with ⟨a, h, hhC, rfl⟩
        have hhcomm : (h : A) ∈ ⁅P, X⁆ := by
          rw [← hmap]
          exact Subgroup.mem_map_of_mem P.subtype hhC
        have hcomm : ⁅(h : A)⁻¹, (a : A)⁆ ∈ ⁅⁅P, X⁆, X⁆ :=
          Subgroup.commutator_mem_commutator ((⁅P, X⁆ : Subgroup A).inv_mem hhcomm) a.2
        simpa [commutatorElement_def, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
          hXP, mul_assoc] using hcomm
  refine le_antisymm ?_ fun x hx => ?_
  · exact (Subgroup.le_normalizer_iff_commutator_le_left).mp
      (Subgroup.normalizer_commutator_ge_right P X)
  · rw [← hmap, ← h2] at hx
    exact hmap2 hx

theorem center_le_centralizer {p : ℕ} {W X : Subgroup A} {z : A} (h : Setup412 p W X z) :
    W ⊓ centralizer (W : Set A) ≤ centralizer (X : Set A) := by
  have hUab : ∀ a ∈ (W ⊓ centralizer (W : Set A) : Subgroup A),
      ∀ b ∈ (W ⊓ centralizer (W : Set A) : Subgroup A), a * b = b * a := by
    intro a ha b hb
    exact mem_centralizer_iff.mp (Subgroup.mem_inf.1 hb).2 a (Subgroup.mem_inf.1 ha).1
  have hc := abelian_centralized h (inf_le_left : (W ⊓ centralizer (W : Set A) : Subgroup A) ≤ W)
    hUab (fun x hx => mem_normalizer_center (h.XW hx)) (mem_normalizer_center h.zW)
  intro u hu
  rw [mem_centralizer_iff]
  intro x hx
  exact hc x hx u hu

theorem inf_centralizer_le_commutator {p : ℕ} {W X : Subgroup A} {z : A} (h : Setup412 p W X z)
    (hW : ⁅W, X⁆ = W) : W ⊓ centralizer (X : Set A) ≤ ⁅W, W⁆ := by
  have := commutator_inf_centralizer_le_commutator h.W2 h.XW (odd_natCard h)
  rwa [hW] at this

end CoprimeAction

end CoreA

variable {A : Type} [Group A] [Finite A]

theorem part1_of_setup {p : ℕ} {W X : Subgroup A} {z : A} (h : Setup412 p W X z)
    (hW : ⁅W, X⁆ = W) (hne : W ≠ ⊥) : Part1 p W X z where
  setup := h
  comm_eq := hW
  ne_bot := hne
  nonab := by
    intro hab
    have hc := CoreA.abelian_centralized h (le_refl W) hab h.XW h.zW
    apply hne
    rw [← hW, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro w hw
    rw [mem_centralizer_iff]
    intro x hx
    exact hc x hx w hw
  abel_central := fun U hUW hUn hXU hzU hUab => CoreA.abelian_le_centralizer h hW hUW hUn hXU hzU hUab
  class_two := by
    intro a ha b hb c hc
    have h1 : ⁅a, b⁆ ∈ (⁅W, W⁆ : Subgroup A) := Subgroup.commutator_mem_commutator ha hb
    have h2 : ⁅⁅a, b⁆, c⁆ ∈ (⁅⁅W, W⁆, W⁆ : Subgroup A) :=
      Subgroup.commutator_mem_commutator h1 hc
    have h3 : (⁅⁅W, W⁆, W⁆ : Subgroup A) = ⊥ := CoreA.lowerCentralSeries_two_eq_bot h hW
    rw [h3] at h2
    exact Subgroup.mem_bot.1 h2
  X_cent_Z := CoreA.center_le_centralizer h
  CX_le_derived := CoreA.inf_centralizer_le_commutator h hW

theorem reduce412 {p : ℕ} {W X : Subgroup A} {z : A} (h : Setup412 p W X z) :
    ⁅W, X⁆ ≤ W ∧ X ≤ normalizer ((⁅W, X⁆ : Subgroup A) : Set A) ∧
      z ∈ normalizer ((⁅W, X⁆ : Subgroup A) : Set A) ∧ ⁅(⁅W, X⁆ : Subgroup A), X⁆ = ⁅W, X⁆ ∧
      X ⊓ centralizer (W : Set A) = X ⊓ centralizer ((⁅W, X⁆ : Subgroup A) : Set A) ∧
      Setup412 p ⁅W, X⁆ X z := by
  have hle : ⁅W, X⁆ ≤ W := (Subgroup.le_normalizer_iff_commutator_le_left).mp h.XW
  have hXn : X ≤ normalizer ((⁅W, X⁆ : Subgroup A) : Set A) :=
    Subgroup.normalizer_commutator_ge_right W X
  have hzn : z ∈ normalizer ((⁅W, X⁆ : Subgroup A) : Set A) :=
    CoreA.mem_normalizer_commutator h.zW h.zX
  have hcop := CoreA.coprime_natCard h
  have hsolv : Group.IsSolvable ↥W := by
    have := h.W2.isNilpotent
    infer_instance
  have hcent : X ⊓ centralizer (W : Set A) = X ⊓ centralizer ((⁅W, X⁆ : Subgroup A) : Set A) := by
    refine le_antisymm (inf_le_inf_left X (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hle)))
      ?_
    intro x hx
    obtain ⟨hxX, hxC⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_inf.2 ⟨hxX, ?_⟩
    have hfac := CoreA.le_commutator_sup_inf_centralizer h.XW hsolv hcop
    have h1 : (⁅W, X⁆ : Subgroup A) ≤ centralizer ({x} : Set A) := by
      intro c hc
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.mp hxC c hc
    have h2 : W ⊓ centralizer (X : Set A) ≤ centralizer ({x} : Set A) := by
      intro c hc
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mem_centralizer_iff.mp (Subgroup.mem_inf.1 hc).2 x hxX).symm
    have hW' : W ≤ centralizer ({x} : Set A) := hfac.trans (sup_le h1 h2)
    rw [mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_singleton_iff.mp (hW' hw)
  refine ⟨hle, hXn, hzn, CoreA.commutator_commutator_eq_of_coprime h.XW hcop, hcent, ?_⟩
  exact
    { prime := h.prime
      odd := h.odd
      W2 := h.W2.to_le hle
      Xp := h.Xp
      XW := hXn
      zW := hzn
      z2 := h.z2
      zX := h.zX
      comm := h.comm
      Cz := fun c hc hcz => h.Cz c (hle hc) hcz }

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87

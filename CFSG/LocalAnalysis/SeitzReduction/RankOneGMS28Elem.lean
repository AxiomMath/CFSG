module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneGMS28Trans
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherGoldschmidtFour

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.SteinbergBV CFSG.LocalAnalysis.SteinbergBX
open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

namespace GMS28

variable {D : Type} [Group D]

section Counting

theorem card_le_two_mul_of_mul_mem [Finite D] {E H : Subgroup D}
    (h : ∀ x₁ ∈ E, ∀ x₂ ∈ E, x₁ ∉ H → x₂ ∉ H → x₁ * x₂ ∈ H) :
    Nat.card E ≤ 2 * Nat.card H := by
  classical
  by_cases hEH : E ≤ H
  · have := card_le_of_le hEH
    omega
  obtain ⟨x₁, hx₁E, hx₁H⟩ := IsConcreteLE.not_le_iff_exists.mp hEH
  let Φ : E → Bool × H := fun x =>
    if hx : (x : D) ∈ H then (true, ⟨x, hx⟩) else (false, ⟨x₁ * x, h x₁ hx₁E x x.2 hx₁H hx⟩)
  have hΦ : Function.Injective Φ := by
    intro x x' hxx'
    by_cases hx : (x : D) ∈ H <;> by_cases hx' : (x' : D) ∈ H <;>
      simp only [Φ, hx, hx', dite_true, dite_false, Prod.mk.injEq] at hxx'
    · have h2 := congrArg Subtype.val hxx'.2
      exact Subtype.ext h2
    · exact absurd hxx'.1 (by decide)
    · exact absurd hxx'.1 (by decide)
    · have h2 := congrArg Subtype.val hxx'.2
      exact Subtype.ext (mul_left_cancel h2)
  have h1 := Nat.card_le_card_of_injective Φ hΦ
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h1

theorem card_le_card_inf_centralizer_mul [Finite D] {V : Subgroup D}
    (hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) {w : D} (hwV : w ∈ normalizer (V : Set D)) :
    Nat.card V ≤ Nat.card (V ⊓ centralizer ({w} : Set D) : Subgroup D) *
      Nat.card (⁅V, zpowers w⁆ : Subgroup D) := by
  classical
  have hc : ∀ v ∈ V, w * v * w⁻¹ ∈ V := fun v hv => (mem_normalizer_iff.mp hwV v).mp hv
  let φ : V →* V :=
    { toFun := fun v => ⟨v * (w * v * w⁻¹)⁻¹, mul_mem v.2 (inv_mem (hc v v.2))⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        have ha := inv_mem (hc x x.2)
        have hb := inv_mem (hc y y.2)
        have h1 : (w * ((x : D) * y) * w⁻¹)⁻¹ = (w * y * w⁻¹)⁻¹ * (w * x * w⁻¹)⁻¹ := by group
        show (x : D) * y * (w * ((x : D) * y) * w⁻¹)⁻¹ =
          (x : D) * (w * x * w⁻¹)⁻¹ * ((y : D) * (w * y * w⁻¹)⁻¹)
        rw [h1]
        set a := (w * (x : D) * w⁻¹)⁻¹
        set b := (w * (y : D) * w⁻¹)⁻¹
        have hab : b * a = a * b := hcomm b hb a ha
        have hya : (y : D) * a = a * y := hcomm _ y.2 a ha
        calc (x : D) * y * (b * a) = x * y * (a * b) := by rw [hab]
          _ = x * (y * a) * b := by simp only [mul_assoc]
          _ = x * (a * y) * b := by rw [hya]
          _ = x * a * (y * b) := by simp only [mul_assoc]) }
  have hφ : ∀ v : V, (φ v : D) = v * (w * v * w⁻¹)⁻¹ := fun _ => rfl
  have hker : ∀ v : V, φ v = 1 → (v : D) ∈ centralizer ({w} : Set D) := by
    intro v hv
    have h1 : (v : D) * (w * v * w⁻¹)⁻¹ = 1 := by rw [← hφ, hv, coe_one]
    rw [mul_inv_eq_one] at h1
    rw [mem_centralizer_singleton_iff]
    calc (v : D) * w = w * v * w⁻¹ * w := by rw [← h1]
      _ = w * v := by group
  have hrange : ∀ v : V, (φ v : D) ∈ (⁅V, zpowers w⁆ : Subgroup D) := by
    intro v
    rw [hφ, show (v : D) * (w * v * w⁻¹)⁻¹ = ⁅(v : D), w⁆ by rw [commutatorElement_def]; group]
    exact commutator_mem_commutator v.2 (mem_zpowers w)
  have h1 := card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at h1
  have h2 : Nat.card φ.ker ≤ Nat.card (V ⊓ centralizer ({w} : Set D) : Subgroup D) := by
    refine Nat.card_le_card_of_injective (fun v => ⟨v.1.1, v.1.2, hker v.1 v.2⟩) ?_
    intro v v' hvv
    have h := congrArg Subtype.val hvv
    exact Subtype.ext (Subtype.ext h)
  have h3 : Nat.card φ.range ≤ Nat.card (⁅V, zpowers w⁆ : Subgroup D) := by
    refine Nat.card_le_card_of_injective (fun u => ⟨u.1.1, ?_⟩) ?_
    · obtain ⟨v, hv⟩ := u.2
      rw [← hv]
      exact hrange v
    · intro u u' huu
      have h := congrArg Subtype.val huu
      exact Subtype.ext (Subtype.ext h)
  calc Nat.card V = Nat.card φ.range * Nat.card φ.ker := h1
    _ ≤ Nat.card (⁅V, zpowers w⁆ : Subgroup D) *
        Nat.card (V ⊓ centralizer ({w} : Set D) : Subgroup D) := Nat.mul_le_mul h3 h2
    _ = _ := mul_comm _ _

theorem exists_mem_normalizer_of_not_isSylowOf [Finite D] {S : Subgroup D} (hS : IsPGroup 2 S)
    (hSD : ¬ IsSylowOf 2 S ⊤) :
    ∃ T : Sylow 2 D, S ≤ T ∧ ∃ z ∈ (T : Subgroup D), z ∈ normalizer (S : Set D) ∧ z ∉ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hST⟩ := hS.exists_le_sylow
  have hne : S ≠ (T : Subgroup D) := by
    intro hST'
    apply hSD
    rw [isSylowOf_iff]
    refine ⟨le_top, hS, ?_⟩
    rw [hST', relIndex_top_right]
    exact Sylow.not_dvd_index T
  set I := S.subgroupOf (T : Subgroup D) with hI
  have hIlt : I < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hne (le_antisymm hST fun x hx => ?_)
    have : (⟨x, hx⟩ : (T : Subgroup D)) ∈ I := by
      rw [htop]
      trivial
    exact mem_subgroupOf.mp this
  have : Group.IsNilpotent (T : Subgroup D) := T.isPGroup'.isNilpotent
  have hlt := Group.normalizerCondition_of_isNilpotent (G := (T : Subgroup D)) I hIlt
  obtain ⟨x, hxN, hxI⟩ := IsConcreteLE.exists_of_lt hlt
  have hxN' : (x : D) ∈ normalizer (S : Set D) := by
    have : x ∈ (normalizer (S : Set D)).subgroupOf (T : Subgroup D) := by
      rw [subgroupOf_normalizer_eq hST]
      exact hxN
    exact mem_subgroupOf.mp this
  exact ⟨T, hST, x, x.2, hxN', fun hx => hxI (mem_subgroupOf.mpr hx)⟩

end Counting

structure IsTorus (U R V₁ : Subgroup D) (t y d : D) : Prop where
  mem_normalizer_U : y ∈ normalizer (U : Set D)
  trans : ∀ a ∈ U, ∀ b ∈ U, a ≠ 1 → b ≠ 1 → ∃ k : ℕ, y ^ k * a * (y ^ k)⁻¹ = b
  mem_normalizer : d ∈ normalizer (V₁ : Set D)
  mem_normalizer_V : d ∈ normalizer ((U ⊔ R : Subgroup D) : Set D)
  commute : d * t = t * d
  odd : Odd (orderOf d)
  conj_eq : ∀ v ∈ U ⊔ R, d * v * d⁻¹ = y * v * y⁻¹

variable {J R X U P V₁ : Subgroup D} {n : ℕ} {t y d : D}

theorem IsV₁.exists_isTorus [Finite D] (hV₁ : IsV₁ U R P V₁) (hS : Setup J R X U P n t)
    (htr : ∀ u ∈ U, ∃ x ∈ V₁, x * t * x⁻¹ = u * t) :
    ∃ y ∈ X ⊓ normalizer (U : Set D), Odd (orderOf y) ∧
      (∀ g ∈ X ⊓ normalizer (U : Set D), ∃ k : ℕ,
        ∀ v ∈ U ⊔ R, g * v * g⁻¹ = y ^ k * v * (y ^ k)⁻¹) ∧
      ∃ d : D, IsTorus U R V₁ t y d := by
  obtain ⟨y, hyX, hyodd, hytr, hygen, d, hdV₁, hdV, hdt, hdodd, hdy⟩ := hV₁.exists_torus hS htr
  exact ⟨y, hyX, hyodd, hygen, d, ⟨(mem_inf.mp hyX).2, hytr, hdV₁, hdV, hdt, hdodd, hdy⟩⟩

namespace IsV₁

theorem comm_eq_one_iff_mem [Finite D] (hV₁ : IsV₁ U R P V₁) (hS : Setup J R X U P n t) {x : D}
    (hx : x ∈ V₁) : x * t * x⁻¹ * t = 1 ↔ x ∈ U ⊔ R := by
  rw [hS.comm_eq_one_iff]
  exact ⟨hV₁.mem_V_of_commute hS hx, fun hxV => hS.commute_V hxV hS.t_mem_V⟩

theorem comm_inv [Finite D] (hV₁ : IsV₁ U R P V₁) (hS : Setup J R X U P n t) {x : D}
    (hx : x ∈ V₁) : x⁻¹ * t * x⁻¹⁻¹ * t = x * t * x⁻¹ * t := by
  have h1 := hS.comm_mul (hV₁.le_tr hx) (hV₁.le_tr (inv_mem hx))
  rw [mul_inv_cancel, one_mul, inv_one, mul_one, hS.mul_self_t] at h1
  have hc := hS.comm_mem (hV₁.le_tr hx)
  have h2 := hS.mul_self_U hc
  calc x⁻¹ * t * x⁻¹⁻¹ * t = (x * t * x⁻¹ * t) * ((x * t * x⁻¹ * t) * (x⁻¹ * t * x⁻¹⁻¹ * t)) := by
        rw [← mul_assoc, h2, one_mul]
    _ = x * t * x⁻¹ * t := by rw [← h1, mul_one]

end IsV₁

namespace IsTorus

theorem comm_conj [Finite D] (hT : IsTorus U R V₁ t y d) (hV₁ : IsV₁ U R P V₁)
    (hS : Setup J R X U P n t) {x : D} (hx : x ∈ V₁) :
    (d * x * d⁻¹) * t * (d * x * d⁻¹)⁻¹ * t = y * (x * t * x⁻¹ * t) * y⁻¹ := by
  have hdt : d⁻¹ * t * d = t := by
    calc d⁻¹ * t * d = d⁻¹ * (t * d) := by group
      _ = t := by rw [← hT.commute]; group
  have e1 : (d * x * d⁻¹) * t * (d * x * d⁻¹)⁻¹ * t =
      d * (x * (d⁻¹ * t * d) * x⁻¹ * (d⁻¹ * t * d)) * d⁻¹ := by group
  rw [e1, hdt, hT.conj_eq _ (mem_sup_left (hS.comm_mem (hV₁.le_tr hx)))]

theorem comm_conj_pow [Finite D] (hT : IsTorus U R V₁ t y d) (hV₁ : IsV₁ U R P V₁)
    (hS : Setup J R X U P n t) (k : ℕ) {x : D} (hx : x ∈ V₁) :
    (d ^ k * x * (d ^ k)⁻¹) * t * (d ^ k * x * (d ^ k)⁻¹)⁻¹ * t =
      y ^ k * (x * t * x⁻¹ * t) * (y ^ k)⁻¹ := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have hdx : d * x * d⁻¹ ∈ V₁ := (mem_normalizer_iff.mp hT.mem_normalizer x).mp hx
    have e1 : d ^ (k + 1) * x * (d ^ (k + 1))⁻¹ = d ^ k * (d * x * d⁻¹) * (d ^ k)⁻¹ := by
      rw [pow_succ]
      group
    rw [e1, ih hdx, hT.comm_conj hV₁ hS hx]
    group

theorem exists_pow_conj [Finite D] (hT : IsTorus U R V₁ t y d) (hV₁ : IsV₁ U R P V₁)
    (hS : Setup J R X U P n t) {x x₀ : D} (hx : x ∈ V₁) (hxV : x ∉ U ⊔ R) (hx₀ : x₀ ∈ V₁)
    (hx₀V : x₀ ∉ U ⊔ R) : ∃ k : ℕ, x⁻¹ * (d ^ k * x₀ * (d ^ k)⁻¹) ∈ U ⊔ R := by
  have hc := hS.comm_mem (hV₁.le_tr hx)
  have hc₀ := hS.comm_mem (hV₁.le_tr hx₀)
  have hc1 : x * t * x⁻¹ * t ≠ 1 := fun h1 => hxV ((hV₁.comm_eq_one_iff_mem hS hx).mp h1)
  have hc₀1 : x₀ * t * x₀⁻¹ * t ≠ 1 := fun h1 => hx₀V ((hV₁.comm_eq_one_iff_mem hS hx₀).mp h1)
  obtain ⟨k, hk⟩ := hT.trans _ hc₀ _ hc hc₀1 hc1
  refine ⟨k, ?_⟩
  set z := d ^ k * x₀ * (d ^ k)⁻¹ with hz
  have hzV₁ : z ∈ V₁ := (mem_normalizer_iff.mp (pow_mem hT.mem_normalizer k) x₀).mp hx₀
  have hzc : z * t * z⁻¹ * t = x * t * x⁻¹ * t := by
    rw [hz, hT.comm_conj_pow hV₁ hS k hx₀, hk]
  have hmem : x⁻¹ * z ∈ V₁ := mul_mem (inv_mem hx) hzV₁
  rw [← hV₁.comm_eq_one_iff_mem hS hmem, hS.comm_mul (hV₁.le_tr (inv_mem hx)) (hV₁.le_tr hzV₁),
    hzc, hV₁.comm_inv hS hx]
  exact hS.mul_self_U hc

end IsTorus

namespace IsV₁

theorem inf_P (hV₁ : IsV₁ U R P V₁) (hS : Setup J R X U P n t) : V₁ ⊓ P = U ⊔ R := by
  refine le_antisymm (fun x hx => ?_) (le_inf hV₁.le hS.V_le_P)
  rw [← hS.inf_centralizer_U]
  exact mem_inf.mpr ⟨(mem_inf.mp hx).2, (mem_inf.mp (hV₁.le_tr (mem_inf.mp hx).1)).2⟩

theorem exists_mul_eq (hV₁ : IsV₁ U R P V₁) {w : D} (hw : w ∈ V₁ ⊔ P) :
    ∃ p ∈ P, ∃ x ∈ V₁, p * x = w := by
  rw [sup_comm] at hw
  exact exists_mul_of_mem_sup hV₁.le_normalizer hw

theorem card_sq_le [Finite D] (hV₁ : IsV₁ U R P V₁) (hS : Setup J R X U P n t) {w : D}
    (hw : w ∈ V₁ ⊔ P) (hwV₁ : w ∉ V₁) :
    Nat.card (U ⊓ centralizer ({w} : Set D) : Subgroup D) ^ 2 ≤ 2 ^ n := by
  obtain ⟨p, hp, x, hx, rfl⟩ := hV₁.exists_mul_eq hw
  have hpV : p ∉ U ⊔ R := fun hpV => hwV₁ (mul_mem (hV₁.le hpV) hx)
  have heq : U ⊓ centralizer ({p * x} : Set D) = U ⊓ centralizer ({p} : Set D) := by
    ext u
    simp only [mem_inf, mem_centralizer_singleton_iff]
    refine and_congr_right fun hu => ?_
    have hxu : u * x = x * u := hV₁.commute_U hx hu
    constructor
    · intro h1
      have : p * u * x = u * p * x := by
        calc p * u * x = p * (u * x) := by group
          _ = p * (x * u) := by rw [hxu]
          _ = p * x * u := by group
          _ = u * (p * x) := h1.symm
          _ = u * p * x := by group
      exact (mul_right_cancel this).symm
    · intro h1
      calc u * (p * x) = u * p * x := by group
        _ = p * u * x := by rw [h1]
        _ = p * (u * x) := by group
        _ = p * (x * u) := by rw [hxu]
        _ = p * x * u := by group
  rw [heq]
  obtain ⟨K, _, _, _, hKcard, e, -, -, φ, hequiv, -, hker⟩ :=
    (SteinbergBT.gms_normal_root_singer_action_and_weak_closure hS.data).1
  have hφp : φ ⟨p, hp⟩ ≠ 1 := fun h1 => hpV (by
    have hmem : (⟨p, hp⟩ : P) ∈ φ.ker := h1
    rw [hker] at hmem
    exact hmem)
  obtain ⟨-, -, -, -, -, -, ⟨-, -, -, -, hPNU, -⟩⟩ := hS.data
  exact SteinbergBT.card_inf_centralizer_sq_le hKcard e φ hequiv hPNU ⟨p, hp⟩ hφp

theorem mul_mem_of_mul_self [Finite D] (hV₁ : IsV₁ U R P V₁) (hS : Setup J R X U P n t)
    {x₁ x₂ : D} (h₁ : x₁ ∈ V₁ ⊔ P) (h₂ : x₂ ∈ V₁ ⊔ P) (h₁₁ : x₁ * x₁ = 1) (h₂₂ : x₂ * x₂ = 1)
    (h₁V : x₁ ∉ V₁) (h₂V : x₂ ∉ V₁) : x₁ * x₂ ∈ V₁ := by
  classical
  obtain ⟨p₁, hp₁, v₁, hv₁, rfl⟩ := hV₁.exists_mul_eq h₁
  obtain ⟨p₂, hp₂, v₂, hv₂, rfl⟩ := hV₁.exists_mul_eq h₂
  have hp₁V₁ : p₁ ∉ V₁ := fun h => h₁V (mul_mem h hv₁)
  have hp₂V₁ : p₂ ∉ V₁ := fun h => h₂V (mul_mem h hv₂)
  have hsq : ∀ p ∈ P, ∀ v ∈ V₁, p * v * (p * v) = 1 → p * p ∈ U ⊔ R := by
    intro p hp v hv hpv
    have hpv' : p⁻¹ * v⁻¹ * p ∈ V₁ := by
      have := (mem_normalizer_iff.mp (inv_mem (hV₁.le_normalizer hp)) v⁻¹).mp (inv_mem hv)
      rwa [inv_inv] at this
    have e : p * p = v⁻¹ * (p⁻¹ * v⁻¹ * p) := by
      have h1 : p * v * p = v⁻¹ := by
        calc p * v * p = p * v * p * v * v⁻¹ := by group
          _ = v⁻¹ := by rw [show p * v * p * v = p * v * (p * v) by group, hpv, one_mul]
      calc p * p = p * v * p * (p⁻¹ * v⁻¹ * p) := by group
        _ = v⁻¹ * (p⁻¹ * v⁻¹ * p) := by rw [h1]
    rw [← hV₁.inf_P hS]
    refine mem_inf.mpr ⟨?_, mul_mem hp hp⟩
    rw [e]
    exact mul_mem (inv_mem hv) hpv'
  have hs₁ := hsq p₁ hp₁ v₁ hv₁ h₁₁
  have hs₂ := hsq p₂ hp₂ v₂ hv₂ h₂₂
  obtain ⟨K, _, _, _, hKcard, e, -, -, φ, -, -, hker⟩ :=
    (SteinbergBT.gms_normal_root_singer_action_and_weak_closure hS.data).1
  obtain ⟨-, -, -, -, -, -, ⟨-, -, -, -, -, -, -, hVn⟩⟩ := hS.data
  obtain ⟨hcyc, -⟩ := SteinbergBT.isCyclic_quotient_of_ker_eq hKcard φ hker
  set Q := P ⧸ (U ⊔ R).subgroupOf P
  let _ : Fintype Q := Fintype.ofFinite Q
  have hmk : ∀ p : P, (QuotientGroup.mk p : Q) = 1 ↔ (p : D) ∈ U ⊔ R := fun p => by
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
  set q₁ : Q := QuotientGroup.mk ⟨p₁, hp₁⟩
  set q₂ : Q := QuotientGroup.mk ⟨p₂, hp₂⟩
  have hq₁ : q₁ ≠ 1 := fun h => hp₁V₁ (hV₁.le ((hmk _).mp h))
  have hq₂ : q₂ ≠ 1 := fun h => hp₂V₁ (hV₁.le ((hmk _).mp h))
  have hq₁2 : q₁ ^ 2 = 1 := by
    rw [sq, ← QuotientGroup.mk_mul, hmk]
    exact hs₁
  have hq₂2 : q₂ ^ 2 = 1 := by
    rw [sq, ← QuotientGroup.mk_mul, hmk]
    exact hs₂
  have hq : q₁ = q₂ := by
    by_contra hne
    have hle := IsCyclic.card_pow_eq_one_le (α := Q) (n := 2) (by norm_num)
    have hsub : ({1, q₁, q₂} : Finset Q) ⊆ Finset.univ.filter (fun a : Q => a ^ 2 = 1) := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases ha with rfl | rfl | rfl
      · exact one_pow 2
      · exact hq₁2
      · exact hq₂2
    have h3 : ({1, q₁, q₂} : Finset Q).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair hne]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hq₁, Ne.symm hq₂⟩
    have := Finset.card_le_card hsub
    omega
  have hp₁₂ : p₁ * p₂ ∈ U ⊔ R := by
    have h1 : (QuotientGroup.mk (⟨p₁, hp₁⟩ * ⟨p₂, hp₂⟩⁻¹) : Q) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      change q₁ * q₂⁻¹ = 1
      rw [hq, mul_inv_cancel]
    have h2 := (hmk _).mp h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
    have := mul_mem h2 hs₂
    rwa [show p₁ * p₂⁻¹ * (p₂ * p₂) = p₁ * p₂ by group] at this
  have hp₂v₁ : p₂⁻¹ * v₁ * p₂ ∈ V₁ := by
    have := (mem_normalizer_iff.mp (inv_mem (hV₁.le_normalizer hp₂)) v₁).mp hv₁
    rwa [inv_inv] at this
  have e : p₁ * v₁ * (p₂ * v₂) = (p₁ * p₂) * (p₂⁻¹ * v₁ * p₂) * v₂ := by group
  rw [e]
  exact mul_mem (mul_mem (hV₁.le hp₁₂) hp₂v₁) hv₂

theorem card_le_two_mul [Finite D] (hV₁ : IsV₁ U R P V₁) (hS : Setup J R X U P n t)
    {E : Subgroup D} (hE : E ≤ V₁ ⊔ P) (hE2 : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 2 * Nat.card (E ⊓ V₁ : Subgroup D) := by
  refine card_le_two_mul_of_mul_mem fun x₁ hx₁ x₂ hx₂ h₁ h₂ =>
    mem_inf.mpr ⟨mul_mem hx₁ hx₂, ?_⟩
  have h₁V : x₁ ∉ V₁ := fun h => h₁ (mem_inf.mpr ⟨hx₁, h⟩)
  have h₂V : x₂ ∉ V₁ := fun h => h₂ (mem_inf.mpr ⟨hx₂, h⟩)
  exact hV₁.mul_mem_of_mul_self hS (hE hx₁) (hE hx₂) (hE2 _ hx₁) (hE2 _ hx₂) h₁V h₂V

theorem two_mul_card_lt [Finite D] (hV₁ : IsV₁ U R P V₁) (hS : Setup J R X U P n t) {w : D}
    (hw : w ∈ V₁ ⊔ P) (hwV₁ : w ∉ V₁) {F : Subgroup D} (hFV : F ≤ U ⊔ R)
    (hFC : F ≤ centralizer ({w} : Set D)) : 2 * Nat.card F < Nat.card (U ⊔ R : Subgroup D) := by
  obtain ⟨hn3, -, -, -, ⟨-, -, -, hUcard⟩, -⟩ := hS.data
  have hVcard : Nat.card (U ⊔ R : Subgroup D) = 2 ^ n * 2 := by
    rw [SteinbergBT.card_sup_of_centralizes (gms_R_le_centralizer_U hS.data) hS.inf_eq_bot,
      hUcard, hS.card]
  have hFU : Nat.card F ≤ 2 * Nat.card (F ⊓ U : Subgroup D) := by
    refine card_le_two_mul_of_mul_mem fun x₁ hx₁ x₂ hx₂ h₁ h₂ => mem_inf.mpr ⟨mul_mem hx₁ hx₂, ?_⟩
    have h₁U : x₁ ∉ U := fun h => h₁ (mem_inf.mpr ⟨hx₁, h⟩)
    have h₂U : x₂ ∉ U := fun h => h₂ (mem_inf.mpr ⟨hx₂, h⟩)
    have ha := (hS.mem_or_mul_mem (hFV hx₁)).resolve_left h₁U
    have hb := (hS.mem_or_mul_mem (hFV hx₂)).resolve_left h₂U
    have e : x₁ * x₂ = (x₁ * t) * (x₂ * t) := by
      rw [hS.commute_V (hFV hx₂) hS.t_mem_V, show x₁ * t * (t * x₂) = x₁ * (t * t) * x₂ by group,
        hS.mul_self_t, mul_one]
    rw [e]
    exact mul_mem ha hb
  have hFUC : Nat.card (F ⊓ U : Subgroup D) ≤ Nat.card (U ⊓ centralizer ({w} : Set D) : Subgroup D) :=
    card_le_of_le (le_inf inf_le_right (inf_le_left.trans hFC))
  have hsq := hV₁.card_sq_le hS hw hwV₁
  have h8 : 8 ≤ 2 ^ n :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  rw [hVcard]
  by_contra hle
  push Not at hle
  set a := Nat.card (F ⊓ U : Subgroup D)
  set c := Nat.card (U ⊓ centralizer ({w} : Set D) : Subgroup D)
  set q := 2 ^ n
  have h1 : q ≤ 2 * c := by nlinarith
  have h2 : q * q ≤ 4 * (c * c) := by nlinarith
  have h3 : c * c ≤ q := by rw [← sq]; exact hsq
  nlinarith

theorem rightConjugate_eq [Finite D] (hV₁ : IsV₁ U R P V₁) (hS : Setup J R X U P n t)
    (hinv : ∀ x ∈ V₁, x * x = 1 → x ∈ U ⊔ R) {g : D}
    (hg : rightConjugate (U ⊔ R) g ≤ V₁ ⊔ P) : rightConjugate (U ⊔ R) g = U ⊔ R := by
  set E := rightConjugate (U ⊔ R) g with hEdef
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hS.commute_V ha hb]
  have hE2 : ∀ x ∈ E, x * x = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← sq, gms_sq_V hS.data a ha, map_one]
  have hER : E ⊓ V₁ ≤ U ⊔ R := fun x hx => hinv x (mem_inf.mp hx).2 (hE2 x (mem_inf.mp hx).1)
  have hEcard : Nat.card E = Nat.card (U ⊔ R : Subgroup D) := by
    rw [hEdef, rightConjugate_card]
  by_cases hEle : E ≤ V₁
  · have hEV : E ≤ U ⊔ R := fun x hx => hER (mem_inf.mpr ⟨hx, hEle hx⟩)
    exact Subgroup.eq_of_le_of_card_ge hEV hEcard.symm.le
  · exfalso
    obtain ⟨x, hxE, hxV₁⟩ := IsConcreteLE.not_le_iff_exists.mp hEle
    have hcard := hV₁.card_le_two_mul hS hg hE2
    have hFC : E ⊓ V₁ ≤ centralizer ({x} : Set D) := fun z hz =>
      mem_centralizer_singleton_iff.mpr (hcomm z (mem_inf.mp hz).1 x hxE)
    have hlt := hV₁.two_mul_card_lt hS (hg hxE) hxV₁ hER hFC
    omega

theorem isSylowOf_top [Finite D] (hV₁ : IsV₁ U R P V₁) (hS : Setup J R X U P n t)
    (htr : ∀ u ∈ U, ∃ x ∈ V₁, x * t * x⁻¹ = u * t)
    (hinv : ∀ x ∈ V₁, x * x = 1 → x ∈ U ⊔ R) : IsSylowOf 2 (V₁ ⊔ P) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS₀ := hV₁.isSylowOf_sup hS htr
  have hVS₀ : U ⊔ R ≤ V₁ ⊔ P := hV₁.le.trans le_sup_left
  by_contra hns
  obtain ⟨S, hS₀S, z, hzS, hzN, hzS₀⟩ := exists_mem_normalizer_of_not_isSylowOf hS₀.isPGroup hns
  have hle : rightConjugate (U ⊔ R) z⁻¹ ≤ V₁ ⊔ P := by
    intro x hx
    rw [mem_rightConjugate_iff, inv_inv] at hx
    have h1 := (mem_normalizer_iff.mp hzN _).mp (hVS₀ hx)
    simpa [mul_assoc] using h1
  have hzV : z ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) := by
    have h1 := (rightConjugate_eq_self_iff _ _).mp (hV₁.rightConjugate_eq hS hinv hle)
    simpa using inv_mem h1
  have hp : IsPGroup 2 (V₁ ⊔ P ⊔ zpowers z : Subgroup D) :=
    S.isPGroup'.to_le (sup_le hS₀S (zpowers_le.mpr hzS))
  have heq := hS₀.eq_of_le le_sup_left (sup_le hS₀.le (zpowers_le.mpr hzV)) hp
  exact hzS₀ (heq ▸ mem_sup_right (mem_zpowers z))

theorem exists_sq_mem [Finite D] (hV₁ : IsV₁ U R P V₁) (hS : Setup J R X U P n t)
    (htr : ∀ u ∈ U, ∃ x ∈ V₁, x * t * x⁻¹ = u * t)
    (hsc : ∀ T : Sylow 2 D, U ⊔ R ≤ T →
      ¬ IsStronglyClosedIn (T : Subgroup D) ((U ⊔ R : Subgroup D) : Set D)) :
    ∃ x₀ ∈ V₁, x₀ ∉ U ⊔ R ∧ x₀ * x₀ ∈ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hex
  push Not at hex
  have hinv : ∀ x ∈ V₁, x * x = 1 → x ∈ U ⊔ R := by
    intro x hx hxx
    by_contra hxV
    exact hex x hx hxV (by rw [hxx]; exact one_mem U)
  have hsyl := hV₁.isSylowOf_top hS htr hinv
  obtain ⟨-, hS₀p, hS₀idx⟩ := isSylowOf_iff.mp hsyl
  rw [relIndex_top_right] at hS₀idx
  let S : Sylow 2 D := hS₀p.toSylow hS₀idx
  have hSc : (S : Subgroup D) = V₁ ⊔ P := IsPGroup.toSylow_coe hS₀p hS₀idx
  have hVS : U ⊔ R ≤ S := hSc ▸ hV₁.le.trans le_sup_left
  have hVel : CFSG.Open.IsElemAbelian 2 (U ⊔ R) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 _).1 (gms_isElementaryAbelian_V hS.data)
  have hwc : ∀ g : D, rightConjugate (U ⊔ R) g ≤ S → rightConjugate (U ⊔ R) g = U ⊔ R :=
    fun g hg => hV₁.rightConjugate_eq hS hinv (hSc ▸ hg)
  have hnsc : ∃ v ∈ U ⊔ R, ∃ g : D, g⁻¹ * v * g ∈ (S : Subgroup D) ∧ g⁻¹ * v * g ∉ U ⊔ R := by
    by_contra hall
    push Not at hall
    exact hsc S hVS ⟨fun v hv => hVS hv, fun v hv g hg => hall v hv g hg⟩
  obtain ⟨U', hU'V, h, hU'S, hU'nV, hbound⟩ :=
    CFSG.ComponentClassification.GoldschmidtFour.goldschmidt_theorem_four_holds D S (U ⊔ R) hVS
      hVel hwc hnsc
  set W := rightConjugate U' h with hWdef
  have hWS : W ≤ V₁ ⊔ P := hSc ▸ hU'S
  have hW2 : ∀ x ∈ W, x * x = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← sq, gms_sq_V hS.data a (hU'V ha), map_one]
  have hWV₁ : W ⊓ V₁ ≤ U ⊔ R := fun x hx => hinv x (mem_inf.mp hx).2 (hW2 x (mem_inf.mp hx).1)
  have hWnV₁ : ¬ W ≤ V₁ := fun h1 => hU'nV fun x hx => hWV₁ (mem_inf.mpr ⟨hx, h1 hx⟩)
  obtain ⟨w, hwW, hwV₁⟩ := IsConcreteLE.not_le_iff_exists.mp hWnV₁
  have hcard := hV₁.card_le_two_mul hS hWS hW2
  have hinf : (U ⊔ R) ⊓ W = W ⊓ V₁ :=
    le_antisymm (le_inf inf_le_right (inf_le_left.trans hV₁.le)) (le_inf hWV₁ inf_le_left)
  have hidx := relIndex_mul_card (U ⊔ R) W
  rw [hinf] at hidx
  have hpos : 0 < Nat.card (W ⊓ V₁ : Subgroup D) := Nat.card_pos
  have hidx2 : (U ⊔ R).relIndex W ≤ 2 := by nlinarith
  have hb := hbound w hwW
  have hwN : w ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) :=
    (hV₁.isSylowOf_sup hS htr).le (hWS hwW)
  have hc := card_le_card_inf_centralizer_mul (fun a ha b hb => hS.commute_V ha hb) hwN
  have hlt := hV₁.two_mul_card_lt hS (hWS hwW) hwV₁
    (inf_le_left : (U ⊔ R) ⊓ centralizer ({w} : Set D) ≤ U ⊔ R) inf_le_right
  have : Nat.card (U ⊔ R : Subgroup D) ≤
      Nat.card ((U ⊔ R) ⊓ centralizer ({w} : Set D) : Subgroup D) * 2 :=
    hc.trans (Nat.mul_le_mul_left _ (hb.trans hidx2))
  omega

theorem sq_mem [Finite D] (hV₁ : IsV₁ U R P V₁) (hS : Setup J R X U P n t)
    (htr : ∀ u ∈ U, ∃ x ∈ V₁, x * t * x⁻¹ = u * t) (hT : IsTorus U R V₁ t y d)
    (hsc : ∀ T : Sylow 2 D, U ⊔ R ≤ T →
      ¬ IsStronglyClosedIn (T : Subgroup D) ((U ⊔ R : Subgroup D) : Set D)) :
    ∀ x ∈ V₁, x * x ∈ U := by
  obtain ⟨x₀, hx₀, hx₀V, hx₀U⟩ := hV₁.exists_sq_mem hS htr hsc
  have hdU : d ∈ normalizer (U : Set D) := hS.normalizer_V_le hT.mem_normalizer_V
  intro x hx
  by_cases hxV : x ∈ U ⊔ R
  · rw [show x * x = 1 by rw [← sq]; exact gms_sq_V hS.data x hxV]
    exact one_mem U
  obtain ⟨k, hk⟩ := hT.exists_pow_conj hV₁ hS hx hxV hx₀ hx₀V
  set z := d ^ k * x₀ * (d ^ k)⁻¹ with hz
  have hzV₁ : z ∈ V₁ := (mem_normalizer_iff.mp (pow_mem hT.mem_normalizer k) x₀).mp hx₀
  have hzU : z * z ∈ U := by
    have := (mem_normalizer_iff.mp (pow_mem hdU k) _).mp hx₀U
    rw [hz]
    rwa [show d ^ k * (x₀ * x₀) * (d ^ k)⁻¹ = d ^ k * x₀ * (d ^ k)⁻¹ * (d ^ k * x₀ * (d ^ k)⁻¹) by
      group] at this
  set v := z⁻¹ * x with hv
  have hvV : v ∈ U ⊔ R := by
    have := inv_mem hk
    rwa [show (x⁻¹ * z)⁻¹ = z⁻¹ * x by group] at this
  have hxe : x = z * v := by rw [hv]; group
  have hzv : z⁻¹ * v * z * v ∈ U := by
    have hzN : z⁻¹ ∈ normalizer (U : Set D) := inv_mem (hS.normalizer_V_le (hV₁.le_normalizer_V hzV₁))
    have hzVN : z⁻¹ ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) := inv_mem (hV₁.le_normalizer_V hzV₁)
    have hw : z⁻¹ * v * z ∈ U ⊔ R := by
      have := (mem_normalizer_iff.mp hzVN v).mp hvV
      rwa [inv_inv] at this
    by_cases hvU : v ∈ U
    · have := (mem_normalizer_iff.mp hzN v).mp hvU
      rw [inv_inv] at this
      exact mul_mem this hvU
    · have hwU : z⁻¹ * v * z ∉ U := fun h1 => hvU (by
        have := (mem_normalizer_iff.mp (inv_mem hzN) _).mp h1
        rwa [inv_inv, show z * (z⁻¹ * v * z) * z⁻¹ = v by group] at this)
      have ha := (hS.mem_or_mul_mem hw).resolve_left hwU
      have hb := (hS.mem_or_mul_mem hvV).resolve_left hvU
      have e : z⁻¹ * v * z * v = (z⁻¹ * v * z * t) * (v * t) := by
        rw [hS.commute_V hvV hS.t_mem_V,
          show z⁻¹ * v * z * t * (t * v) = z⁻¹ * v * z * (t * t) * v by group, hS.mul_self_t,
          mul_one]
      rw [e]
      exact mul_mem ha hb
  rw [hxe]
  have e : z * v * (z * v) = (z * z) * (z⁻¹ * v * z * v) := by group
  rw [e]
  exact mul_mem hzU hzv

end IsV₁

end GMS28

end CFSG.SeitzReduction.RankOne

module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.QuasithinUnique.A5.C25

open scoped commutatorElement

section Abstract

variable {K : Type*} [Group K]

theorem comm_central_mem_center (hperf : Group.IsPerfect K) {k : K}
    (h : ∀ g : K, ⁅k, g⁆ ∈ Subgroup.center K) : k ∈ Subgroup.center K := by
  rw [Subgroup.mem_center_iff]
  let δ : K →* Subgroup.center K :=
    { toFun := fun g => ⟨⁅k, g⁆, h g⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        have hb : ∀ x, x * ⁅k, b⁆ = ⁅k, b⁆ * x := fun x => Subgroup.mem_center_iff.1 (h b) x
        show ⁅k, a * b⁆ = ⁅k, a⁆ * ⁅k, b⁆
        calc ⁅k, a * b⁆ = ⁅k, a⁆ * (a * ⁅k, b⁆ * a⁻¹) := by
              simp only [commutatorElement_def]; group
          _ = ⁅k, a⁆ * ⁅k, b⁆ := by rw [hb a]; group }
  have hδ : ∀ g, δ g = 1 := by
    intro g
    have hg : g ∈ commutator K := by
      rw [Group.isPerfect_def.1 hperf]; exact Subgroup.mem_top g
    rw [commutator_eq_closure] at hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, b, rfl⟩ := hx
      have : δ ⁅a, b⁆ = ⁅δ a, δ b⁆ := map_commutatorElement δ a b
      rw [this]
      exact commutatorElement_eq_one_iff_mul_comm.2
        (Subtype.ext (Subgroup.mem_center_iff.1 (δ b).2 (δ a)))
    | one => exact map_one δ
    | mul x y _ _ hx hy => rw [map_mul, hx, hy, one_mul]
    | inv x _ hx => rw [map_inv, hx, inv_one]
  intro g
  have h1 : ⁅k, g⁆ = 1 := congrArg Subtype.val (hδ g)
  have h2 : k * g = g * k := commutatorElement_eq_one_iff_mul_comm.1 h1
  exact h2.symm

theorem quasisimple_of_ker_central (R : Subgroup K) [R.Normal]
    (hRc : R ≤ Subgroup.center K) (hperf : Group.IsPerfect K)
    (hsimple : IsSimpleGroup ((K ⧸ R) ⧸ Subgroup.center (K ⧸ R)))
    (hnab : ∃ a b : (K ⧸ R) ⧸ Subgroup.center (K ⧸ R), a * b ≠ b * a) :
    IsSimpleGroup (K ⧸ Subgroup.center K) ∧
      ∃ a b : K ⧸ Subgroup.center K, a * b ≠ b * a := by
  let π : K →* K ⧸ R := QuotientGroup.mk' R
  let φ : K →* (K ⧸ R) ⧸ Subgroup.center (K ⧸ R) :=
    (QuotientGroup.mk' (Subgroup.center (K ⧸ R))).comp π
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective R
  have hφ : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective (Subgroup.center (K ⧸ R))).comp hπ
  have hker : φ.ker = Subgroup.center K := by
    apply le_antisymm
    · intro k hk
      have h1 : π k ∈ Subgroup.center (K ⧸ R) :=
        (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hk)
      apply comm_central_mem_center hperf
      intro g
      have hmem : ⁅k, g⁆ ∈ R := by
        rw [← QuotientGroup.eq_one_iff]
        have : ((⁅k, g⁆ : K) : K ⧸ R) = ⁅(k : K ⧸ R), (g : K ⧸ R)⁆ :=
          map_commutatorElement π k g
        rw [this]
        exact commutatorElement_eq_one_iff_mul_comm.2
          (Subgroup.mem_center_iff.1 h1 (g : K ⧸ R)).symm
      exact hRc hmem
    · intro z hz
      rw [MonoidHom.mem_ker]
      have hzc : π z ∈ Subgroup.center (K ⧸ R) := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨g, rfl⟩ := hπ y
        have := congrArg π (Subgroup.mem_center_iff.1 hz g)
        simpa [map_mul] using this
      exact (QuotientGroup.eq_one_iff _).2 hzc
  let e : K ⧸ Subgroup.center K ≃* (K ⧸ R) ⧸ Subgroup.center (K ⧸ R) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  refine ⟨e.isSimpleGroup_congr.mpr hsimple, ?_⟩
  obtain ⟨a, b, hab⟩ := hnab
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

theorem exists_central_odd [Finite K] (R : Subgroup K) [R.Normal] (hR : IsPGroup 2 R)
    (hRmax : ∀ N : Subgroup K, N.Normal → IsPGroup 2 N → N ≤ R)
    (hperf : Group.IsPerfect K)
    (hbar : ∀ D : Subgroup (K ⧸ R), D.Normal → D = ⊤ ∨ D ≤ Subgroup.center (K ⧸ R))
    (hnc : ¬ Subgroup.centralizer (R : Set K) ≤ R)
    (hnR : Subgroup.centralizer (R : Set K) ≠ ⊤) :
    ∃ y : K, y ∈ Subgroup.center K ∧ (orderOf y).Prime ∧ orderOf y ≠ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup K := Subgroup.centralizer (R : Set K) with hC
  have hCn : C.Normal := by
    refine ⟨fun c hc g => ?_⟩
    rw [hC, Subgroup.mem_centralizer_iff] at hc ⊢
    intro r hr
    have h1 : g⁻¹ * r * g ∈ R := (inferInstance : R.Normal).conj_mem r hr g⁻¹ |> fun h => by
      simpa using h
    have h2 := hc (g⁻¹ * r * g) h1
    calc r * (g * c * g⁻¹) = g * ((g⁻¹ * r * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * r * g)) * g⁻¹ := by rw [h2]
      _ = g * c * g⁻¹ * r := by group
  obtain ⟨y₀, hy₀C, hy₀p, hy₀2⟩ : ∃ y ∈ C, (orderOf y).Prime ∧ orderOf y ≠ 2 := by
    by_contra hno
    push Not at hno
    apply hnc
    apply hRmax C hCn
    rw [IsPGroup.iff_card]
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (p := 2) Nat.card_pos.ne' ?_⟩
    intro d hd hdd
    have : Fact d.Prime := ⟨hd⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' d hdd
    have h1 := hno (x : K) x.2 (by rw [Subgroup.orderOf_coe, hx]; exact hd)
    rw [Subgroup.orderOf_coe, hx] at h1
    exact h1
  let π : K →* K ⧸ R := QuotientGroup.mk' R
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective R
  set D : Subgroup (K ⧸ R) := C.map π with hD
  have hDn : D.Normal := Subgroup.Normal.map hCn π hπ
  have hDtop : D ≠ ⊤ := by
    intro hDt
    have hsup : C ⊔ R = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : π x ∈ D := hDt ▸ Subgroup.mem_top _
      obtain ⟨c, hc, hcx⟩ := hx
      have hr : c⁻¹ * x ∈ R := QuotientGroup.eq.1 hcx
      have : x = c * (c⁻¹ * x) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hr)
    let f : R →* K ⧸ C := (QuotientGroup.mk' C).comp R.subtype
    have hf : Function.Surjective f := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective C q
      have hx : x ∈ C ⊔ R := hsup ▸ Subgroup.mem_top x
      obtain ⟨c, hc, r, hr, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx
      refine ⟨⟨r, hr⟩, ?_⟩
      have h1 : (QuotientGroup.mk' C) c = 1 := (QuotientGroup.eq_one_iff c).2 hc
      show (QuotientGroup.mk' C) r = (QuotientGroup.mk' C) (c * r)
      rw [map_mul, h1, one_mul]
    have hp : IsPGroup 2 (K ⧸ C) := hR.of_surjective f hf
    have : Group.IsNilpotent (K ⧸ C) := hp.isNilpotent
    have hperfQ : Group.IsPerfect (K ⧸ C) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective C)
    have hsub : Subsingleton (K ⧸ C) := by
      by_contra hns
      rw [not_subsingleton_iff_nontrivial] at hns
      exact Group.IsPerfect.not_isSolvable (K ⧸ C) inferInstance
    apply hnR
    rw [eq_top_iff]
    intro x _
    exact (QuotientGroup.eq_one_iff x).1 (Subsingleton.elim _ _)
  have hDc : D ≤ Subgroup.center (K ⧸ R) := (hbar D hDn).resolve_left hDtop
  refine ⟨y₀, ?_, hy₀p, hy₀2⟩
  rw [Subgroup.mem_center_iff]
  intro k
  have hπy : π y₀ ∈ Subgroup.center (K ⧸ R) := hDc ⟨y₀, hy₀C, rfl⟩
  have hc := Subgroup.mem_center_iff.1 hπy (π k)
  have hrR : y₀⁻¹ * (k * y₀ * k⁻¹) ∈ R := by
    rw [← QuotientGroup.eq_one_iff]
    show π (y₀⁻¹ * (k * y₀ * k⁻¹)) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    calc (π y₀)⁻¹ * (π k * π y₀ * (π k)⁻¹) = (π y₀)⁻¹ * ((π y₀ * π k) * (π k)⁻¹) := by rw [hc]
      _ = 1 := by group
  set r := y₀⁻¹ * (k * y₀ * k⁻¹) with hrdef
  have hk : k * y₀ * k⁻¹ = y₀ * r := by rw [hrdef]; group
  have hcomm : Commute y₀ r := (Subgroup.mem_centralizer_iff.1 hy₀C r hrR).symm
  have hpow : (k * y₀ * k⁻¹) ^ (orderOf y₀) = 1 := by
    rw [conj_pow, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
  rw [hk, hcomm.mul_pow, pow_orderOf_eq_one, one_mul] at hpow
  obtain ⟨m, hm⟩ := hR ⟨r, hrR⟩
  have hm' : r ^ 2 ^ m = 1 := congrArg Subtype.val hm
  have hdvd1 : orderOf r ∣ orderOf y₀ := orderOf_dvd_of_pow_eq_one hpow
  have hdvd2 : orderOf r ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm'
  have hcop : Nat.Coprime (orderOf y₀) (2 ^ m) :=
    Nat.Coprime.pow_right m ((Nat.coprime_primes hy₀p Nat.prime_two).2 hy₀2)
  have h1 : orderOf r = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
  have hr1 : r = 1 := orderOf_eq_one_iff.1 h1
  rw [hr1, mul_one] at hk
  calc k * y₀ = (k * y₀ * k⁻¹) * k := by group
    _ = y₀ * k := by rw [hk]

theorem quasisimple_or_central_odd [Finite K] (R : Subgroup K) [R.Normal] (hR : IsPGroup 2 R)
    (hRmax : ∀ N : Subgroup K, N.Normal → IsPGroup 2 N → N ≤ R)
    (hperf : Group.IsPerfect K)
    (hbar : ∀ D : Subgroup (K ⧸ R), D.Normal → D = ⊤ ∨ D ≤ Subgroup.center (K ⧸ R))
    (hsimple : IsSimpleGroup ((K ⧸ R) ⧸ Subgroup.center (K ⧸ R)))
    (hnab : ∃ a b : (K ⧸ R) ⧸ Subgroup.center (K ⧸ R), a * b ≠ b * a)
    (hnc : ¬ Subgroup.centralizer (R : Set K) ≤ R) :
    (IsSimpleGroup (K ⧸ Subgroup.center K) ∧
      ∃ a b : K ⧸ Subgroup.center K, a * b ≠ b * a) ∨
      ∃ y : K, y ∈ Subgroup.center K ∧ (orderOf y).Prime ∧ orderOf y ≠ 2 := by
  by_cases hRK : Subgroup.centralizer (R : Set K) = ⊤
  · left
    refine quasisimple_of_ker_central R ?_ hperf hsimple hnab
    intro r hr
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ Subgroup.centralizer (R : Set K) := hRK ▸ Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_iff.1 this r hr).symm
  · right
    exact exists_central_odd R hR hRmax hperf hbar hnc hRK

end Abstract

end CFSG.QuasithinUnique.A5.C25

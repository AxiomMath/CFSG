module

public import CFSG.Quasithin.Background.A1cTransfer
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
public import Mathlib.GroupTheory.Focal
public import Mathlib.GroupTheory.Nilpotent
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

namespace CFSG.GH74.Uniqueness.Hering

open Subgroup MulAction
open scoped commutatorElement

section PPart

variable {G : Type*} [Group G]

@[expose] def pPart (K : Subgroup G) (hKab : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) (p : ℕ) :
    Subgroup G where
  carrier := {k | k ∈ K ∧ ∃ n : ℕ, k ^ p ^ n = 1}
  mul_mem' := by
    rintro a b ⟨ha, n, hn⟩ ⟨hb, n', hn'⟩
    refine ⟨K.mul_mem ha hb, n + n', ?_⟩
    rw [(Commute.mul_pow (hKab a ha b hb) _), pow_add, pow_mul, hn, one_pow, mul_comm (p ^ n),
      pow_mul, hn', one_pow, one_mul]
  one_mem' := ⟨K.one_mem, 0, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, n, hn⟩
    exact ⟨K.inv_mem ha, n, by rw [inv_pow, hn, inv_one]⟩

variable {K : Subgroup G} {hKab : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a} {p : ℕ}

theorem mem_pPart {k : G} : k ∈ pPart K hKab p ↔ k ∈ K ∧ ∃ n : ℕ, k ^ p ^ n = 1 := Iff.rfl

theorem pPart_le : pPart K hKab p ≤ K := fun _ h => h.1

theorem conj_mem_pPart {h k : G} (hK : h * k * h⁻¹ ∈ K) (hk : k ∈ pPart K hKab p) :
    h * k * h⁻¹ ∈ pPart K hKab p := by
  obtain ⟨-, n, hn⟩ := hk
  exact ⟨hK, n, by rw [conj_pow, hn, mul_one, mul_inv_cancel]⟩

theorem exists_ne_one_mem_pPart [Finite G] [hp : Fact p.Prime] (hpK : p ∣ Nat.card K) :
    ∃ k ∈ pPart K hKab p, k ≠ 1 := by
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := K) p hpK
  refine ⟨k, ⟨k.2, 1, ?_⟩, ?_⟩
  · rw [pow_one, ← hk, ← Subgroup.orderOf_coe]
    exact pow_orderOf_eq_one (k : G)
  · intro h1
    have : k = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hk
    exact hp.out.one_lt.ne hk

end PPart

section CaseA

variable {G Ω : Type*} [Group G] [MulAction G Ω] {ω : Ω} {K : Subgroup G}

theorem mem_stabilizer_of_conj (hKfix : ∀ k ∈ K, k ≠ 1 → ∀ x : Ω, k • x = x → x = ω)
    {z : G} (hz : z ∈ K) (hz1 : z ≠ 1) {d : G} (hd : d⁻¹ * z * d ∈ stabilizer G ω) :
    d ∈ stabilizer G ω := by
  rw [mem_stabilizer_iff] at hd ⊢
  apply hKfix z hz hz1
  have := congrArg (d • ·) hd
  simp only [mul_smul, smul_inv_smul] at this
  exact this

variable [Finite G]

theorem exists_stabilizer_conj {p : ℕ} [Fact p.Prime]
    (hKfix : ∀ k ∈ K, k ≠ 1 → ∀ x : Ω, k • x = x → x = ω)
    (R : Sylow p G) (hRH : (R : Subgroup G) ≤ stabilizer G ω) {z : G} (hz : z ∈ K)
    (hz1 : z ≠ 1) (hzR : z ∈ (R : Subgroup G)) (hzc : ∀ r ∈ (R : Subgroup G), z * r = r * z)
    {x y g : G} (hx : x ∈ (R : Subgroup G)) (hy : y ∈ (R : Subgroup G))
    (hg : g * x * g⁻¹ = y) : ∃ h ∈ stabilizer G ω, h * x * h⁻¹ = y := by
  set C := centralizer ({y} : Set G) with hC
  have hzC : z ∈ C := by
    rw [mem_centralizer_singleton_iff]
    exact hzc y hy
  have hgzC : g * z * g⁻¹ ∈ C := by
    rw [mem_centralizer_singleton_iff, ← hg]
    have := hzc x hx
    calc g * z * g⁻¹ * (g * x * g⁻¹) = g * (z * x) * g⁻¹ := by group
      _ = g * (x * z) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * (g * z * g⁻¹) := by group
  have hzp : IsPGroup p (zpowers z) :=
    R.isPGroup'.to_le ((zpowers_le (H := (R : Subgroup G))).mpr hzR)
  have hgzp : IsPGroup p (zpowers (g * z * g⁻¹)) := by
    have : zpowers (g * z * g⁻¹) = (zpowers z).map (MulAut.conj g).toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      rfl
    rw [this]
    exact hzp.map _
  obtain ⟨c, hcC, d, h1, h2⟩ := Quasithin.exists_conj_le_sylow_of_isPGroup R
    ((zpowers_le (H := C)).mpr hzC) ((zpowers_le (H := C)).mpr hgzC) hzp hgzp
  have hd : d ∈ stabilizer G ω := by
    apply mem_stabilizer_of_conj hKfix hz hz1
    apply hRH
    apply h1
    rw [Quasithin.mem_conjSubgroup_iff]
    have : d * (d⁻¹ * z * d) * d⁻¹ = z := by group
    rw [this]
    exact mem_zpowers z
  have hcd : g⁻¹ * (c * d) ∈ stabilizer G ω := by
    apply mem_stabilizer_of_conj hKfix hz hz1
    apply hRH
    apply h2
    rw [Quasithin.mem_conjSubgroup_iff]
    have : c * d * ((g⁻¹ * (c * d))⁻¹ * z * (g⁻¹ * (c * d))) * (c * d)⁻¹ = g * z * g⁻¹ := by
      group
    rw [this]
    exact mem_zpowers _
  refine ⟨c⁻¹ * g, ?_, ?_⟩
  · have : c⁻¹ * g = d * (g⁻¹ * (c * d))⁻¹ := by group
    rw [this]
    exact (stabilizer G ω).mul_mem hd ((stabilizer G ω).inv_mem hcd)
  · have hcy : c * y = y * c := by
      rw [mem_centralizer_singleton_iff] at hcC
      exact hcC
    calc c⁻¹ * g * x * (c⁻¹ * g)⁻¹ = c⁻¹ * (g * x * g⁻¹) * c := by group
      _ = c⁻¹ * (c * y) := by rw [hg, mul_assoc, hcy]
      _ = y := by group

omit [MulAction G Ω] in
theorem sylow_inf_commutator_le {p : ℕ} [Fact p.Prime] (R : Sylow p G) {H : Subgroup G}
    (hRH : (R : Subgroup G) ≤ H) (hHK : ⁅H, H⁆ ≤ K)
    (hfus : ∀ x ∈ (R : Subgroup G), ∀ y ∈ (R : Subgroup G), ∀ g : G, g * x * g⁻¹ = y →
      ∃ h ∈ H, h * x * h⁻¹ = y) :
    commutator G ⊓ (R : Subgroup G) ≤ K := by
  rw [Subgroup.commutator_inf_eq_focalSubgroup R, Subgroup.focalSubgroup_def, Subgroup.closure_le]
  rintro g ⟨hgR, x, hxR, u, rfl⟩
  have hy : u * x⁻¹ * u⁻¹ ∈ (R : Subgroup G) := by
    have h1 : x⁻¹ * ⁅x, u⁆ ∈ (R : Subgroup G) :=
      (R : Subgroup G).mul_mem ((R : Subgroup G).inv_mem hxR) hgR
    have e : u * x⁻¹ * u⁻¹ = x⁻¹ * ⁅x, u⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact h1
  obtain ⟨h, hhH, hh⟩ := hfus x⁻¹ ((R : Subgroup G).inv_mem hxR) _ hy u rfl
  have e : ⁅x, u⁆ = ⁅x, h⁆ := by
    have h1 : ⁅x, u⁆ = x * (u * x⁻¹ * u⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [h1, ← hh]
    simp only [commutatorElement_def]
    group
  rw [SetLike.mem_coe, e]
  exact hHK (Subgroup.commutator_mem_commutator (hRH hxR) hhH)

omit [MulAction G Ω] in
theorem exists_sylow_central {H : Subgroup G} (hKH : K ≤ H)
    (hKn : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) (hKab : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a)
    {p : ℕ} [Fact p.Prime] (hpK : p ∣ Nat.card K) (hpidx : ¬ p ∣ H.index) {γ : G}
    (hγH : γ ∈ H) (hγp : γ ^ p = 1) :
    ∃ R : Sylow p G, (R : Subgroup G) ≤ H ∧ γ ∈ (R : Subgroup G) ∧
      pPart K hKab p ≤ R ∧ ∃ z ∈ pPart K hKab p, z ≠ 1 ∧ z ∈ (R : Subgroup G) ∧
        ∀ r ∈ (R : Subgroup G), z * r = r * z := by
  classical
  set S := pPart K hKab p with hS
  have hSH : S ≤ H := fun k hk => hKH (pPart_le hk)
  have hSn : (S.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hSH]
    intro k h hk hh
    exact conj_mem_pPart (hKn h hh k (pPart_le hk)) hk
  have hSp : IsPGroup p (S.subgroupOf H) := by
    rintro ⟨⟨k, hkH⟩, hk⟩
    obtain ⟨-, n, hn⟩ := (mem_subgroupOf.mp hk : k ∈ S)
    exact ⟨n, Subtype.ext (Subtype.ext (by simpa using hn))⟩
  have hγp' : IsPGroup p (zpowers (⟨γ, hγH⟩ : H)) := by
    have h1 : (⟨γ, hγH⟩ : H) ^ p = 1 := Subtype.ext (by simpa using hγp)
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp (orderOf_dvd_of_pow_eq_one h1) with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  obtain ⟨Q, hQ⟩ := hγp'.exists_le_sylow
  have hSQ : S.subgroupOf H ≤ Q := hSp.le_sylow_of_normal Q
  set R₀ : Subgroup G := (Q : Subgroup H).map H.subtype with hR₀
  have hR₀p : IsPGroup p R₀ := Q.isPGroup'.map H.subtype
  have hR₀i : ¬ p ∣ R₀.index := by
    rw [hR₀, Subgroup.index_map_subtype]
    intro hdvd
    rcases (Fact.out : p.Prime).dvd_mul.mp hdvd with h | h
    · exact Q.not_dvd_index h
    · exact hpidx h
  set R := hR₀p.toSylow hR₀i with hR
  have hRc : (R : Subgroup G) = R₀ := IsPGroup.toSylow_coe hR₀p hR₀i
  have hRH : (R : Subgroup G) ≤ H := by
    rw [hRc, hR₀]
    exact Subgroup.map_subtype_le _
  have hSR : S ≤ R := by
    intro k hk
    rw [hRc]
    exact ⟨⟨k, hSH hk⟩, hSQ (mem_subgroupOf.mpr hk), rfl⟩
  refine ⟨R, hRH, ?_, hSR, ?_⟩
  · rw [hRc]
    exact ⟨⟨γ, hγH⟩, hQ (mem_zpowers _), rfl⟩
  have hRp : IsPGroup p (R : Subgroup G) := R.isPGroup'
  have : Group.IsNilpotent (R : Subgroup G) := hRp.isNilpotent
  have hNn : (S.subgroupOf R).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hSR]
    intro k h hk hh
    exact conj_mem_pPart (hKn h (hRH hh) k (pPart_le hk)) hk
  obtain ⟨k₀, hk₀S, hk₀1⟩ := exists_ne_one_mem_pPart (hKab := hKab) hpK
  have hNne : S.subgroupOf R ≠ ⊥ := by
    intro hbot
    apply hk₀1
    have hmem : (⟨k₀, hSR hk₀S⟩ : (R : Subgroup G)) ∈ S.subgroupOf R :=
      mem_subgroupOf.mpr hk₀S
    rw [hbot, mem_bot] at hmem
    exact congrArg Subtype.val hmem
  obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hNne)
  have hwS : ((w : (R : Subgroup G)) : G) ∈ S := mem_subgroupOf.mp (w.2.1)
  have hwZ : (w : (R : Subgroup G)) ∈ center (R : Subgroup G) := w.2.2
  refine ⟨((w : (R : Subgroup G)) : G), hwS, ?_, (w : (R : Subgroup G)).2, ?_⟩
  · intro h1
    apply hw1
    exact Subtype.ext (Subtype.ext h1)
  · intro r hr
    have := (Subgroup.mem_center_iff.mp hwZ) ⟨r, hr⟩
    exact (congrArg Subtype.val this).symm

theorem caseA_false (ω : Ω) (K : Subgroup G) (hKH : K ≤ stabilizer G ω)
    (hKn : ∀ h ∈ stabilizer G ω, ∀ k ∈ K, h * k * h⁻¹ ∈ K)
    (hKab : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a)
    (hKfix : ∀ k ∈ K, k ≠ 1 → ∀ x : Ω, k • x = x → x = ω)
    (hHK : ⁅stabilizer G ω, stabilizer G ω⁆ ≤ K)
    {p : ℕ} [hp : Fact p.Prime] (hpK : p ∣ Nat.card K) (hpidx : ¬ p ∣ (stabilizer G ω).index)
    {γ : G} (hγH : γ ∈ stabilizer G ω) (hγK : γ ∉ K) (hγp : γ ^ p = 1)
    (hcl : normalClosure (K : Set G) = ⊤) : False := by
  obtain ⟨R, hRH, hγR, hSR, z, hzS, hz1, hzR, hzc⟩ :=
    exists_sylow_central hKH hKn hKab hpK hpidx hγH hγp
  have hfoc : commutator G ⊓ (R : Subgroup G) ≤ K :=
    sylow_inf_commutator_le R hRH hHK (fun x hx y hy g hg =>
      exists_stabilizer_conj hKfix R hRH (pPart_le hzS) hz1 hzR hzc hx hy hg)
  set π := (Abelianization.of : G →* Abelianization G) with hπ
  have hM : normalClosure (K : Set G) ≤ (K.map π).comap π := by
    have : (K.map π).Normal := Subgroup.normal_of_isMulCommutative _
    exact normalClosure_le_normal (le_comap_map π K)
  have hγM : γ ∈ (K.map π).comap π := hM (hcl ▸ mem_top γ)
  obtain ⟨k, hkK, hkγ⟩ := hγM
  obtain ⟨a, n', hn', hcard⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (Nat.card_pos (α := K)).ne' p hp.out.ne_one
  have hcop : n'.Coprime p := Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hn')
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.out.one_lt
  set k' := k ^ (n' * u) with hk'
  have hk'K : k' ∈ K := K.pow_mem hkK _
  have hk'S : k' ∈ pPart K hKab p := by
    refine ⟨hk'K, a, ?_⟩
    have hkord : k ^ Nat.card K = 1 := by
      obtain ⟨c, hc⟩ := Subgroup.orderOf_dvd_natCard K hkK
      rw [hc, pow_mul, pow_orderOf_eq_one, one_pow]
    rw [hk', ← pow_mul, show n' * u * p ^ a = Nat.card K * u by rw [hcard]; ring, pow_mul,
      hkord, one_pow]
  have hπγ : π γ ^ p = 1 := by rw [← map_pow, hγp, map_one]
  have hπk' : π k' = π γ := by
    have hmod : n' * u ≡ 1 [MOD p] := by
      rw [Nat.ModEq, hu, Nat.one_mod_eq_one.mpr hp.out.ne_one]
    rw [hk', map_pow, hkγ, pow_eq_pow_of_modEq hmod hπγ, pow_one]
  have hcomm : γ⁻¹ * k' ∈ commutator G := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker, map_mul, map_inv, hπk', inv_mul_cancel]
  have hR' : γ⁻¹ * k' ∈ (R : Subgroup G) :=
    (R : Subgroup G).mul_mem ((R : Subgroup G).inv_mem hγR) (hSR hk'S)
  have hK : γ⁻¹ * k' ∈ K := hfoc ⟨hcomm, hR'⟩
  apply hγK
  have : γ = k' * (γ⁻¹ * k')⁻¹ := by group
  rw [this]
  exact K.mul_mem hk'K (K.inv_mem hK)

end CaseA

end CFSG.GH74.Uniqueness.Hering

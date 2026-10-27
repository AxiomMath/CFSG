module

public import CFSG.Holt.H78.Sec4Toolkit
public import CFSG.Holt.H78.Conjugacy
public import CFSG.Holt.H78.Sec4SEAut

public section


namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Open CFSG.GH74.Uniqueness.Bender
open scoped Pointwise

section Bundle

variable (G : Type) [Group G] (Ω : Type) [MulAction G Ω]

structure Prop46CaseB (α β γ : Ω) (v : G) (P : Subgroup (typeLSection G Ω v)) : Prop where
  isTypeL : IsTypeL G Ω α v
  ne : α ≠ β
  normal : P.Normal
  minimal : ∀ R ≤ P, R.Normal → R = ⊥ ∨ R = P
  le_oddCore : P ≤ CFSG.pPrimeCore 2 (typeLSection G Ω v)
  mem_orbit : ∃ p ∈ P, ∃ a : fixSet Ω (Subgroup.zpowers v), (a : Ω) = α ∧ ((p • a : _) : Ω) = β
  mem_holtDelta : γ ∈ holtDelta G Ω α β
  fixed_iff : ∀ δ ∈ holtDelta G Ω α β, v • δ = δ ↔ δ = γ
  isNaturalSE : IsNaturalSE (twoPointJ G Ω α β)
  odd_card : Odd (Nat.card (twoPointKernel G Ω α β))

@[expose] def caseBRad (α β : Ω) (γ : holtDelta G Ω α β) : Subgroup G :=
  ((rootCenter (seRadical (twoPointJ G Ω α β) γ)).comap (twoPointHom G Ω α β)).map
    (stabilizer G ({α, β} : Set Ω)).subtype ⊓ (stabilizer G α ⊓ stabilizer G β)

end Bundle

section Basic


variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω] {α β γ : Ω} {v : G}
  {P : Subgroup (typeLSection G Ω v)}

theorem mem_caseBRad {γ : holtDelta G Ω α β} {g : G} :
    g ∈ caseBRad G Ω α β γ ↔ ∃ hg : g ∈ stabilizer G ({α, β} : Set Ω), g • α = α ∧ g • β = β ∧
      twoPointHom G Ω α β ⟨g, hg⟩ ∈ rootCenter (seRadical (twoPointJ G Ω α β) γ) := by
  simp only [caseBRad, Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_comap, mem_stabilizer_iff]
  constructor
  · rintro ⟨⟨⟨g, hg⟩, hZ, rfl⟩, hα, hβ⟩
    exact ⟨hg, hα, hβ, hZ⟩
  · rintro ⟨hg, hα, hβ, hZ⟩
    exact ⟨⟨⟨g, hg⟩, hZ, rfl⟩, hα, hβ⟩

namespace Prop46CaseB

variable (hC : Prop46CaseB G Ω α β γ v P)
include hC

theorem smul_α : v • α = α := hC.isTypeL.smul_eq

theorem orderOf_v : orderOf v = 2 := hC.isTypeL.orderOf_eq_two

theorem v_mul_v : v * v = 1 := by
  rw [← sq, ← hC.orderOf_v, pow_orderOf_eq_one]

theorem smul_β : v • β = β := by
  obtain ⟨p, -, a, -, hβ⟩ := hC.mem_orbit
  rw [← hβ]
  exact (p • a).2 v (Subgroup.mem_zpowers v)

theorem smul_γ : v • γ = γ := (hC.fixed_iff γ hC.mem_holtDelta).mpr rfl

theorem α_mem : α ∈ fixSet Ω (Subgroup.zpowers v) := by
  rw [fixSet_zpowers, mem_fixedBy]; exact hC.smul_α

theorem β_mem : β ∈ fixSet Ω (Subgroup.zpowers v) := by
  rw [fixSet_zpowers, mem_fixedBy]; exact hC.smul_β

theorem γ_mem : γ ∈ fixSet Ω (Subgroup.zpowers v) := by
  rw [fixSet_zpowers, mem_fixedBy]; exact hC.smul_γ

theorem v_mem_pair : v ∈ stabilizer G ({α, β} : Set Ω) :=
  stabilizer_inf_le_stabilizer_pair α β (Subgroup.mem_inf.mpr
    ⟨mem_stabilizer_iff.mpr hC.smul_α, mem_stabilizer_iff.mpr hC.smul_β⟩)

end Prop46CaseB

theorem twoPointHom_eq_of_forall {g : G} (hg : g ∈ stabilizer G ({α, β} : Set Ω))
    {π : Equiv.Perm (holtDelta G Ω α β)} (hπ : ∀ δ : holtDelta G Ω α β, (π δ : Ω) = g • (δ : Ω)) :
    twoPointHom G Ω α β ⟨g, hg⟩ = π :=
  Equiv.ext fun δ => Subtype.ext (by rw [coe_twoPointHom_apply, hπ])

theorem mem_twoPointKernel_of_twoPointHom_eq_one {g : G} (hg : g ∈ stabilizer G ({α, β} : Set Ω))
    (hgα : g • α = α) (hgβ : g • β = β) (h1 : twoPointHom G Ω α β ⟨g, hg⟩ = 1) :
    g ∈ twoPointKernel G Ω α β :=
  mem_twoPointKernel.mpr ⟨hgα, hgβ, fun δ hδ => by
    have := congrArg (fun π : Equiv.Perm (holtDelta G Ω α β) => ((π ⟨δ, hδ⟩ : _) : Ω)) h1
    simpa [coe_twoPointHom_apply] using this⟩

theorem smul_mem_holtDelta_of_mem_pair {g : G} (hg : g ∈ stabilizer G ({α, β} : Set Ω))
    {δ : Ω} (hδ : δ ∈ holtDelta G Ω α β) : g • δ ∈ holtDelta G Ω α β := by
  rw [← mem_stabilizer_iff.mp (stabilizer_pair_le α β hg)]
  exact Set.smul_mem_smul_set hδ

end Basic

section Odd


variable {G : Type*} [Group G]

theorem exists_mem_conj_eq_of_mul_mem_of_odd {K : Subgroup G} (hK : Odd (Nat.card K)) {t u : G}
    (ht : t * t = 1) (hu : u * u = 1) (htu : t * u ∈ K) : ∃ k ∈ K, k * t * k⁻¹ = u := by
  have hodd : Odd (orderOf (t * u)) := hK.of_dvd_nat (K.orderOf_dvd_natCard htu)
  obtain ⟨k, hk, hkt⟩ := exists_mem_zpowers_conj_eq_of_odd ht hu hodd
  exact ⟨k, (Subgroup.zpowers_le.mpr htu) hk, hkt⟩

theorem eq_one_of_mul_self_eq_one_of_odd {K : Subgroup G} (hK : Odd (Nat.card K)) {g : G}
    (hg : g ∈ K) (hg2 : g * g = 1) : g = 1 := by
  have hodd : Odd (orderOf g) := hK.of_dvd_nat (K.orderOf_dvd_natCard hg)
  have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, hg2])
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.coprime_two_right.mpr hodd) hdvd)

theorem mem_centralizer_zpowers_iff_commute {g v : G} :
    g ∈ Subgroup.centralizer (Subgroup.zpowers v : Set G) ↔ Commute g v := by
  refine ⟨fun h => (Subgroup.mem_centralizer_iff.mp h v (Subgroup.mem_zpowers v)).symm,
    fun h => Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact ((h.symm.zpow_left k).eq)

theorem smul_smul_eq_inv_smul_of_normal {Y : Type*} [MulAction G Y] {P : Subgroup G}
    (hPn : P.Normal) (hPc : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p) {e : Y} {r : G} (hr : r * r = 1)
    (hre : r • e = e) (hfix : ∀ p ∈ P, r • (p • e) = p • e → p • e = e) {p : G} (hp : p ∈ P) :
    r • (p • e) = p⁻¹ • e := by
  have hrp : r * p * r⁻¹ ∈ P := hPn.conj_mem p hp r
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr
  have hq : p * (r * p * r⁻¹) ∈ P := mul_mem hp hrp
  have hrq : r * (p * (r * p * r⁻¹)) * r⁻¹ = p * (r * p * r⁻¹) := by
    calc r * (p * (r * p * r⁻¹)) * r⁻¹ = (r * p * r⁻¹) * (r * r * p * (r⁻¹ * r⁻¹)) := by group
      _ = (r * p * r⁻¹) * p := by rw [hr, hrinv, hr, one_mul, mul_one]
      _ = p * (r * p * r⁻¹) := hPc _ hrp _ hp
  have hfq : r • ((p * (r * p * r⁻¹)) • e) = (p * (r * p * r⁻¹)) • e := by
    calc r • ((p * (r * p * r⁻¹)) • e) = (r * (p * (r * p * r⁻¹)) * r⁻¹) • (r • e) := by
          rw [← mul_smul, ← mul_smul, inv_mul_cancel_right]
      _ = (p * (r * p * r⁻¹)) • e := by rw [hrq, hre]
  have hqe := hfix _ hq hfq
  rw [mul_smul] at hqe
  have h2 : (r * p * r⁻¹) • e = p⁻¹ • e := by rw [eq_inv_smul_iff, hqe]
  calc r • (p • e) = (r * p * r⁻¹) • (r • e) := by
        rw [← mul_smul, ← mul_smul, inv_mul_cancel_right]
    _ = p⁻¹ • e := by rw [hre, h2]

end Odd

section Radical

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  {α β γ : Ω} {v : G} {P : Subgroup (typeLSection G Ω v)}

namespace Prop46CaseB

variable (hC : Prop46CaseB G Ω α β γ v P)
include hC

omit [Finite G] [Fintype Ω] [DecidableEq Ω] in
theorem three_le_card : 3 ≤ Nat.card (holtDelta G Ω α β) := by
  obtain ⟨q, e, h⟩ := hC.isNaturalSE
  obtain ⟨hq, -, he, -⟩ := h.params
  rw [h.card_eq]
  have : q ≤ q ^ e := Nat.le_self_pow (by omega) q
  omega

omit [Finite G] [DecidableEq Ω] in
theorem exists_ne_γ : ∃ δ : holtDelta G Ω α β, δ ≠ ⟨γ, hC.mem_holtDelta⟩ := by
  have : Nontrivial (holtDelta G Ω α β) :=
    Finite.one_lt_card_iff_nontrivial.mp (by have := hC.three_le_card; omega)
  exact exists_ne _

theorem twoPointHom_mem_rootCenter (hS : Sec4Setting G Ω) {g : G}
    (hg : g ∈ stabilizer G ({α, β} : Set Ω)) (hg2 : g * g = 1)
    (hfix : ∀ δ ∈ holtDelta G Ω α β, g • δ = δ ↔ δ = γ) :
    twoPointHom G Ω α β ⟨g, hg⟩ ∈
      rootCenter (seRadical (twoPointJ G Ω α β) ⟨γ, hC.mem_holtDelta⟩) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := twoPointHom G Ω α β ⟨g, hg⟩ with hπ
  have hπS : π ∈ twoPointSection G Ω α β := twoPointHom_mem_twoPointSection _
  have hπ2 : π * π = 1 := by
    rw [hπ, ← map_mul, show (⟨g, hg⟩ * ⟨g, hg⟩ : stabilizer G ({α, β} : Set Ω)) = 1 from
      Subtype.ext hg2, map_one]
  have hfixπ : ∀ δ : holtDelta G Ω α β, π δ = δ ↔ δ = ⟨γ, hC.mem_holtDelta⟩ := fun δ => by
    rw [Subtype.ext_iff, Subtype.ext_iff, hπ, coe_twoPointHom_apply]
    exact hfix δ δ.2
  obtain ⟨δ, hδ⟩ := hC.exists_ne_γ
  have hπ1 : π ≠ 1 := fun h => hδ ((hfixπ δ).mp (by rw [h]; rfl))
  have hJ : (⟨π, hπS⟩ : twoPointSection G Ω α β) ∈
      longInv (twoPointSection G Ω α β) (holtDelta G Ω α β) := by
    refine ⟨orderOf_eq_prime ?_ ?_, ⟨⟨γ, hC.mem_holtDelta⟩, ?_, fun δ' hδ' => ?_⟩⟩
    · exact Subtype.ext (by rw [sq]; exact hπ2)
    · exact fun h => hπ1 (congrArg Subtype.val h)
    · exact (hfixπ _).mpr rfl
    · exact (hfixπ δ').mp hδ'
  have hN : π ∈ twoPointJ G Ω α β := by
    rw [hS.twoPointJ_eq_map_jHull]
    exact ⟨_, mem_jHull_of_mem_longInv hJ, rfl⟩
  exact hC.isNaturalSE.mem_rootCenter_seRadical hN ((hfixπ _).mpr rfl) hπ2

omit [Finite G] [DecidableEq Ω] in
theorem exists_eq_of_mem_twoPointJ {d : Equiv.Perm (holtDelta G Ω α β)}
    (hd : d ∈ twoPointJ G Ω α β) :
    ∃ g : G, g • α = α ∧ g • β = β ∧ ∀ δ : holtDelta G Ω α β, (d δ : Ω) = g • (δ : Ω) := by
  classical
  have : Group.IsPerfect (twoPointJ G Ω α β) :=
    IsHoltFactor.isPerfect (Or.inr hC.isNaturalSE)
  rw [← Subgroup.commutator_eq_self (H := twoPointJ G Ω α β)] at hd
  obtain ⟨g, -, hgα, hgβ, hπ⟩ := mem_twoPointJFix.mp (commutator_twoPointJ_le α β hd)
  exact ⟨g, hgα, hgβ, hπ⟩

omit [Finite G] [DecidableEq Ω] in
theorem exists_eq_of_mem_twoPointJ_of_fix {d : Equiv.Perm (holtDelta G Ω α β)}
    (hd : d ∈ twoPointJ G Ω α β) (hdγ : d ⟨γ, hC.mem_holtDelta⟩ = ⟨γ, hC.mem_holtDelta⟩) :
    ∃ g : G, g • α = α ∧ g • β = β ∧ g • γ = γ ∧
      ∀ δ : holtDelta G Ω α β, (d δ : Ω) = g • (δ : Ω) := by
  obtain ⟨g, hgα, hgβ, hπ⟩ := hC.exists_eq_of_mem_twoPointJ hd
  refine ⟨g, hgα, hgβ, ?_, hπ⟩
  have := hπ ⟨γ, hC.mem_holtDelta⟩
  rw [hdγ] at this
  exact this.symm

theorem twoPointHom_v_mem (hS : Sec4Setting G Ω) :
    twoPointHom G Ω α β ⟨v, hC.v_mem_pair⟩ ∈
      rootCenter (seRadical (twoPointJ G Ω α β) ⟨γ, hC.mem_holtDelta⟩) :=
  hC.twoPointHom_mem_rootCenter hS hC.v_mem_pair hC.v_mul_v hC.fixed_iff

theorem v_mem_caseBRad (hS : Sec4Setting G Ω) :
    v ∈ caseBRad G Ω α β ⟨γ, hC.mem_holtDelta⟩ :=
  mem_caseBRad.mpr ⟨hC.v_mem_pair, hC.smul_α, hC.smul_β, hC.twoPointHom_v_mem hS⟩

omit [Finite G] [Fintype Ω] [DecidableEq Ω] in
theorem eq_one_of_twoPointHom_eq_one {y : G} (hy : y ∈ stabilizer G ({α, β} : Set Ω))
    (hyα : y • α = α) (hyβ : y • β = β) (hy2 : y * y = 1)
    (h1 : twoPointHom G Ω α β ⟨y, hy⟩ = 1) : y = 1 :=
  eq_one_of_mul_self_eq_one_of_odd hC.odd_card
    (mem_twoPointKernel_of_twoPointHom_eq_one hy hyα hyβ h1) hy2

theorem isConj_of_mem_caseBRad (hS : Sec4Setting G Ω) {y : G}
    (hy : y ∈ caseBRad G Ω α β ⟨γ, hC.mem_holtDelta⟩) (hy2 : y * y = 1) (hy1 : y ≠ 1) :
    IsConj v y := by
  obtain ⟨hyP, hyα, hyβ, hyZ⟩ := mem_caseBRad.mp hy
  have hvZ := hC.twoPointHom_v_mem hS
  have hyh1 : twoPointHom G Ω α β ⟨y, hyP⟩ ≠ 1 := fun h =>
    hy1 (hC.eq_one_of_twoPointHom_eq_one hyP hyα hyβ hy2 h)
  have hv1 : v ≠ 1 := fun h => by have := hC.orderOf_v; rw [h, orderOf_one] at this; omega
  have hvh1 : twoPointHom G Ω α β ⟨v, hC.v_mem_pair⟩ ≠ 1 := fun h =>
    hv1 (hC.eq_one_of_twoPointHom_eq_one hC.v_mem_pair hC.smul_α hC.smul_β hC.v_mul_v h)
  obtain ⟨δ, hδ⟩ := hC.exists_ne_γ
  obtain ⟨d, hdN, hdγ, -, hdc⟩ := hC.isNaturalSE.exists_conj_eq (Ne.symm hδ) hyZ hyh1 hvZ hvh1
  obtain ⟨h, hhα, hhβ, -, hhd⟩ := hC.exists_eq_of_mem_twoPointJ_of_fix hdN hdγ
  have hhP : h ∈ stabilizer G ({α, β} : Set Ω) := stabilizer_inf_le_stabilizer_pair α β
    (Subgroup.mem_inf.mpr ⟨mem_stabilizer_iff.mpr hhα, mem_stabilizer_iff.mpr hhβ⟩)
  have hhh : twoPointHom G Ω α β ⟨h, hhP⟩ = d := twoPointHom_eq_of_forall hhP hhd
  set y' := h * y * h⁻¹ with hy'
  have hy'P : y' ∈ stabilizer G ({α, β} : Set Ω) := mul_mem (mul_mem hhP hyP) (inv_mem hhP)
  have hhy : twoPointHom G Ω α β ⟨y', hy'P⟩ = twoPointHom G Ω α β ⟨v, hC.v_mem_pair⟩ := by
    rw [← hdc, ← hhh, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hhα' : h⁻¹ • α = α := by rw [inv_smul_eq_iff, hhα]
  have hhβ' : h⁻¹ • β = β := by rw [inv_smul_eq_iff, hhβ]
  have hvy'P : v * y' ∈ stabilizer G ({α, β} : Set Ω) := mul_mem hC.v_mem_pair hy'P
  have hK : v * y' ∈ twoPointKernel G Ω α β := by
    refine mem_twoPointKernel_of_twoPointHom_eq_one hvy'P ?_ ?_ ?_
    · rw [hy', mul_smul, mul_smul, mul_smul, hhα', hyα, hhα, hC.smul_α]
    · rw [hy', mul_smul, mul_smul, mul_smul, hhβ', hyβ, hhβ, hC.smul_β]
    · have : (⟨v * y', hvy'P⟩ : stabilizer G ({α, β} : Set Ω)) = ⟨v, hC.v_mem_pair⟩ * ⟨y', hy'P⟩ :=
        rfl
      rw [this, map_mul, hhy, ← map_mul,
        show (⟨v, hC.v_mem_pair⟩ * ⟨v, hC.v_mem_pair⟩ : stabilizer G ({α, β} : Set Ω)) = 1 from
          Subtype.ext hC.v_mul_v, map_one]
  have hy'2 : y' * y' = 1 := by
    rw [hy', show h * y * h⁻¹ * (h * y * h⁻¹) = h * (y * y) * h⁻¹ by group, hy2, mul_one,
      mul_inv_cancel]
  obtain ⟨k, -, hk⟩ := exists_mem_conj_eq_of_mul_mem_of_odd hC.odd_card hC.v_mul_v hy'2 hK
  refine isConj_iff.mpr ⟨h⁻¹ * k, ?_⟩
  rw [show h⁻¹ * k * v * (h⁻¹ * k)⁻¹ = h⁻¹ * (k * v * k⁻¹) * h by group, hk, hy']
  group

omit [Finite G] [Fintype Ω] [DecidableEq Ω] in
theorem mul_self_eq_one_of_isConj {s : G} (hs : IsConj v s) : s * s = 1 := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hs
  rw [show c * v * c⁻¹ * (c * v * c⁻¹) = c * (v * v) * c⁻¹ by group, hC.v_mul_v, mul_one,
    mul_inv_cancel]

theorem mem_caseBRad_of_fixedBy_eq (hS : Sec4Setting G Ω) {s : G} (hs : IsConj v s)
    (hfix : fixedBy Ω s = fixedBy Ω v) : s ∈ caseBRad G Ω α β ⟨γ, hC.mem_holtDelta⟩ := by
  have hsα : s • α = α := by
    have : α ∈ fixedBy Ω s := hfix ▸ hC.smul_α
    exact this
  have hsβ : s • β = β := by
    have : β ∈ fixedBy Ω s := hfix ▸ hC.smul_β
    exact this
  have hsP : s ∈ stabilizer G ({α, β} : Set Ω) := stabilizer_inf_le_stabilizer_pair α β
    (Subgroup.mem_inf.mpr ⟨mem_stabilizer_iff.mpr hsα, mem_stabilizer_iff.mpr hsβ⟩)
  refine mem_caseBRad.mpr ⟨hsP, hsα, hsβ, hC.twoPointHom_mem_rootCenter hS hsP
    (hC.mul_self_eq_one_of_isConj hs) fun δ hδ => ?_⟩
  rw [← hC.fixed_iff δ hδ]
  change δ ∈ fixedBy Ω s ↔ δ ∈ fixedBy Ω v
  rw [hfix]

theorem isConj_mul (hS : Sec4Setting G Ω) {s s' : G} (hs : IsConj v s) (hs' : IsConj v s')
    (hc : Commute s s') (hne : s ≠ s') (hfix : fixedBy Ω s = fixedBy Ω s') :
    IsConj v (s * s') := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hs
  set s₁ := g⁻¹ * s' * g with hs₁
  have hs₁c : IsConj v s₁ := hs'.trans (isConj_iff.mpr ⟨g⁻¹, by rw [hs₁, inv_inv]⟩)
  have hfix₁ : fixedBy Ω s₁ = fixedBy Ω v := by
    have h1 : fixedBy Ω s₁ = g⁻¹ • fixedBy Ω s' := by
      rw [smul_fixedBy, inv_inv, hs₁]
    rw [h1, ← hfix, ← smul_fixedBy, inv_smul_smul]
  have hv₁ := hC.mem_caseBRad_of_fixedBy_eq hS hs₁c hfix₁
  have hvv := hC.v_mem_caseBRad hS
  have hcomm : v * s₁ = s₁ * v := by
    have := hc.eq
    rw [hs₁]
    calc v * (g⁻¹ * s' * g) = g⁻¹ * ((g * v * g⁻¹) * s') * g := by group
      _ = g⁻¹ * (s' * (g * v * g⁻¹)) * g := by rw [this]
      _ = g⁻¹ * s' * g * v := by group
  have h2 : v * s₁ * (v * s₁) = 1 := by
    rw [show v * s₁ * (v * s₁) = v * v * (s₁ * s₁) by
      rw [mul_assoc, ← mul_assoc s₁, ← hcomm]; group, hC.v_mul_v,
      hC.mul_self_eq_one_of_isConj hs₁c, one_mul]
  have h1 : v * s₁ ≠ 1 := fun h => hne (by
    rw [mul_eq_one_iff_eq_inv, inv_eq_of_mul_eq_one_right (hC.mul_self_eq_one_of_isConj hs₁c)]
      at h
    rw [h, hs₁]; group)
  have := hC.isConj_of_mem_caseBRad hS (mul_mem hvv hv₁) h2 h1
  refine this.trans (isConj_iff.mpr ⟨g, ?_⟩)
  rw [hs₁]; group

theorem exists_commute_eq_of_mem_rootCenter (hS : Sec4Setting G Ω)
    {z : Equiv.Perm (holtDelta G Ω α β)}
    (hz : z ∈ rootCenter (seRadical (twoPointJ G Ω α β) ⟨γ, hC.mem_holtDelta⟩)) :
    ∃ g : G, Commute g v ∧ g • α = α ∧ g • β = β ∧
      ∀ δ : holtDelta G Ω α β, (z δ : Ω) = g • (δ : Ω) := by
  have hzR := hz.1
  obtain ⟨h, hhα, hhβ, -, hhz⟩ := hC.exists_eq_of_mem_twoPointJ_of_fix (seRadical_le hzR)
    (apply_eq_of_mem_seRadical hzR)
  have hhP : h ∈ stabilizer G ({α, β} : Set Ω) := stabilizer_inf_le_stabilizer_pair α β
    (Subgroup.mem_inf.mpr ⟨mem_stabilizer_iff.mpr hhα, mem_stabilizer_iff.mpr hhβ⟩)
  have hhh : twoPointHom G Ω α β ⟨h, hhP⟩ = z := twoPointHom_eq_of_forall hhP hhz
  set y' := h * v * h⁻¹ with hy'
  have hy'P : y' ∈ stabilizer G ({α, β} : Set Ω) :=
    mul_mem (mul_mem hhP hC.v_mem_pair) (inv_mem hhP)
  have hvZ := hC.twoPointHom_v_mem hS
  have hzv : z * twoPointHom G Ω α β ⟨v, hC.v_mem_pair⟩ * z⁻¹ =
      twoPointHom G Ω α β ⟨v, hC.v_mem_pair⟩ := by
    rw [(Subgroup.mem_centralizer_iff.mp hz.2 _ hvZ.1).symm, mul_inv_cancel_right]
  have hhy : twoPointHom G Ω α β ⟨y', hy'P⟩ = twoPointHom G Ω α β ⟨v, hC.v_mem_pair⟩ := by
    rw [← hzv, ← hhh, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hhα' : h⁻¹ • α = α := by rw [inv_smul_eq_iff, hhα]
  have hhβ' : h⁻¹ • β = β := by rw [inv_smul_eq_iff, hhβ]
  have hvy'P : v * y' ∈ stabilizer G ({α, β} : Set Ω) := mul_mem hC.v_mem_pair hy'P
  have hK : v * y' ∈ twoPointKernel G Ω α β := by
    refine mem_twoPointKernel_of_twoPointHom_eq_one hvy'P ?_ ?_ ?_
    · rw [hy', mul_smul, mul_smul, mul_smul, hhα', hC.smul_α, hhα, hC.smul_α]
    · rw [hy', mul_smul, mul_smul, mul_smul, hhβ', hC.smul_β, hhβ, hC.smul_β]
    · have : (⟨v * y', hvy'P⟩ : stabilizer G ({α, β} : Set Ω)) = ⟨v, hC.v_mem_pair⟩ * ⟨y', hy'P⟩ :=
        rfl
      rw [this, map_mul, hhy, ← map_mul,
        show (⟨v, hC.v_mem_pair⟩ * ⟨v, hC.v_mem_pair⟩ : stabilizer G ({α, β} : Set Ω)) = 1 from
          Subtype.ext hC.v_mul_v, map_one]
  have hy'2 : y' * y' = 1 := by
    rw [hy', show h * v * h⁻¹ * (h * v * h⁻¹) = h * (v * v) * h⁻¹ by group, hC.v_mul_v, mul_one,
      mul_inv_cancel]
  obtain ⟨k, hkK, hk⟩ := exists_mem_conj_eq_of_mul_mem_of_odd hC.odd_card hC.v_mul_v hy'2 hK
  obtain ⟨hkα, hkβ, hkΔ⟩ := mem_twoPointKernel.mp hkK
  refine ⟨k⁻¹ * h, ?_, ?_, ?_, fun δ => ?_⟩
  · change k⁻¹ * h * v = v * (k⁻¹ * h)
    have : h * v = k * v * k⁻¹ * h := by rw [hk, hy', inv_mul_cancel_right]
    rw [mul_assoc, this]; group
  · rw [mul_smul, hhα, inv_smul_eq_iff, hkα]
  · rw [mul_smul, hhβ, inv_smul_eq_iff, hkβ]
  · have hδ' : h • (δ : Ω) ∈ holtDelta G Ω α β := by rw [← hhz]; exact (z δ).2
    rw [mul_smul, hhz, eq_inv_smul_iff, hkΔ _ hδ']

omit [Finite G] [Fintype Ω] [DecidableEq Ω] in
theorem smul_β_of_smul_α {e : G} (he : e ∈ stabilizer G ({α, β} : Set Ω)) (heα : e • α = β) :
    e • β = α := by
  rcases smul_pair_of_mem_stabilizer_pair he with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact absurd (h1.symm.trans heα) hC.ne
  · exact h2

theorem exists_odd_pow_mem_longInv (hS : Sec4Setting G Ω) {e : G}
    (he : e ∈ stabilizer G ({α, β} : Set Ω)) (heα : e • α = β)
    (heZ : twoPointHom G Ω α β ⟨e, he⟩ ∈
      rootCenter (seRadical (twoPointJ G Ω α β) ⟨γ, hC.mem_holtDelta⟩))
    (he1 : twoPointHom G Ω α β ⟨e, he⟩ ≠ 1) :
    ∃ n : ℕ, Odd n ∧ e ^ n ∈ longInvSwap G Ω α β := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have heβ := hC.smul_β_of_smul_α he heα
  have hê2 := hC.isNaturalSE.mul_self_eq_one_of_mem_rootCenter heZ
  have hee : e * e ∈ stabilizer G ({α, β} : Set Ω) := mul_mem he he
  have hK : e * e ∈ twoPointKernel G Ω α β := by
    refine mem_twoPointKernel_of_twoPointHom_eq_one hee ?_ ?_ ?_
    · rw [mul_smul, heα, heβ]
    · rw [mul_smul, heβ, heα]
    · rw [show (⟨e * e, hee⟩ : stabilizer G ({α, β} : Set Ω)) = ⟨e, he⟩ * ⟨e, he⟩ from rfl,
        map_mul, hê2]
  have ho : Odd (orderOf (e * e)) :=
    hC.odd_card.of_dvd_nat ((twoPointKernel G Ω α β).orderOf_dvd_natCard hK)
  obtain ⟨m, hm⟩ := ho
  set o := orderOf (e * e) with hodef
  have hpow : ∀ k : ℕ, (e * e) ^ k • α = α := fun k => by
    induction k with
    | zero => rw [pow_zero, one_smul]
    | succ k ih => rw [pow_succ, mul_smul, mul_smul, heα, heβ, ih]
  have heo : e ^ o = e * (e * e) ^ m := by
    rw [hm, pow_succ', ← sq, ← pow_mul]
  have heoα : e ^ o • α = β := by rw [heo, mul_smul, hpow, heα]
  have heo2 : e ^ o * e ^ o = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, sq, pow_orderOf_eq_one]
  have heoP : e ^ o ∈ stabilizer G ({α, β} : Set Ω) := pow_mem he o
  have hord : orderOf (e ^ o) = 2 := orderOf_eq_prime (by rw [sq, heo2]) fun h => hC.ne (by
    rw [h, one_smul] at heoα; exact heoα)
  refine ⟨o, ⟨m, hm⟩, (hS.mem_longInv_iff_of_odd_twoPointKernel hC.ne hC.odd_card
    hC.three_le_card hord heoα).mpr ?_, heoα⟩
  have himg : twoPointHom G Ω α β ⟨e ^ o, heoP⟩ = twoPointHom G Ω α β ⟨e, he⟩ := by
    rw [show (⟨e ^ o, heoP⟩ : stabilizer G ({α, β} : Set Ω)) = ⟨e, he⟩ ^ o from rfl, map_pow,
      hm, pow_succ', pow_mul, sq, hê2, one_pow, mul_one]
  have hêN : twoPointHom G Ω α β ⟨e, he⟩ ∈ twoPointJ G Ω α β := seRadical_le heZ.1
  have hord' : orderOf (⟨_, hêN⟩ : twoPointJ G Ω α β) = 2 :=
    orderOf_eq_prime (Subtype.ext (by rw [sq]; exact hê2))
      fun h => he1 (congrArg Subtype.val h)
  obtain ⟨δ₀, hδ₀, huniq⟩ := hC.isNaturalSE.existsUnique_fixed hord'
  refine ⟨δ₀, ⟨δ₀.2, ?_⟩, fun δ ⟨hδ, hδf⟩ => ?_⟩
  · have h0 : ((twoPointHom G Ω α β ⟨e, he⟩ δ₀ : holtDelta G Ω α β) : Ω) = δ₀ :=
      congrArg Subtype.val hδ₀
    rw [← himg, coe_twoPointHom_apply] at h0
    exact h0
  · have h1 : (⟨_, hêN⟩ : twoPointJ G Ω α β) • (⟨δ, hδ⟩ : holtDelta G Ω α β) = ⟨δ, hδ⟩ := by
      refine Subtype.ext ?_
      change ((twoPointHom G Ω α β ⟨e, he⟩ ⟨δ, hδ⟩ : holtDelta G Ω α β) : Ω) = δ
      rw [← himg, coe_twoPointHom_apply]
      exact hδf
    exact congrArg Subtype.val (huniq _ h1)

theorem exists_commute_commute_eq_of_mem_rootCenter (hS : Sec4Setting G Ω) {y : G}
    (hyv : Commute y v) (hy2 : y * y = 1) (hyY : y ∈ caseBRad G Ω α β ⟨γ, hC.mem_holtDelta⟩)
    {z : Equiv.Perm (holtDelta G Ω α β)}
    (hz : z ∈ rootCenter (seRadical (twoPointJ G Ω α β) ⟨γ, hC.mem_holtDelta⟩)) :
    ∃ g : G, Commute g v ∧ Commute g y ∧ g • α = α ∧ g • β = β ∧
      ∀ δ : holtDelta G Ω α β, (z δ : Ω) = g • (δ : Ω) := by
  obtain ⟨h, hhv, hhα, hhβ, hhz⟩ := hC.exists_commute_eq_of_mem_rootCenter hS hz
  obtain ⟨hyP, hyα, hyβ, hyZ⟩ := mem_caseBRad.mp hyY
  have hhP : h ∈ stabilizer G ({α, β} : Set Ω) := stabilizer_inf_le_stabilizer_pair α β
    (Subgroup.mem_inf.mpr ⟨mem_stabilizer_iff.mpr hhα, mem_stabilizer_iff.mpr hhβ⟩)
  have hhh : twoPointHom G Ω α β ⟨h, hhP⟩ = z := twoPointHom_eq_of_forall hhP hhz
  set y' := h * y * h⁻¹ with hy'
  have hy'2 : y' * y' = 1 := by
    rw [hy', show h * y * h⁻¹ * (h * y * h⁻¹) = h * (y * y) * h⁻¹ by group, hy2, mul_one,
      mul_inv_cancel]
  have hyy'P : y * y' ∈ stabilizer G ({α, β} : Set Ω) :=
    mul_mem hyP (mul_mem (mul_mem hhP hyP) (inv_mem hhP))
  have hhα' : h⁻¹ • α = α := by rw [inv_smul_eq_iff, hhα]
  have hhβ' : h⁻¹ • β = β := by rw [inv_smul_eq_iff, hhβ]
  have hK₀ : y * y' ∈ twoPointKernel G Ω α β := by
    refine mem_twoPointKernel_of_twoPointHom_eq_one hyy'P ?_ ?_ ?_
    · rw [hy', mul_smul, mul_smul, mul_smul, hhα', hyα, hhα, hyα]
    · rw [hy', mul_smul, mul_smul, mul_smul, hhβ', hyβ, hhβ, hyβ]
    · have : (⟨y * y', hyy'P⟩ : stabilizer G ({α, β} : Set Ω)) =
          ⟨y, hyP⟩ * (⟨h, hhP⟩ * ⟨y, hyP⟩ * ⟨h, hhP⟩⁻¹) := rfl
      rw [this, map_mul, map_mul, map_mul, map_inv, hhh,
        (Subgroup.mem_centralizer_iff.mp hz.2 _ hyZ.1).symm, mul_inv_cancel_right,
        hC.isNaturalSE.mul_self_eq_one_of_mem_rootCenter hyZ]
  have hy'v : Commute y' v := (hhv.mul_left hyv).mul_left hhv.inv_left
  have hCv : y * y' ∈ Subgroup.centralizer (Subgroup.zpowers v : Set G) :=
    mem_centralizer_zpowers_iff_commute.mpr (hyv.mul_left hy'v)
  have hodd : Odd (Nat.card ↥(twoPointKernel G Ω α β ⊓
      Subgroup.centralizer (Subgroup.zpowers v : Set G))) :=
    hC.odd_card.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  obtain ⟨k, hk, hky⟩ := exists_mem_conj_eq_of_mul_mem_of_odd hodd hy2 hy'2
    (Subgroup.mem_inf.mpr ⟨hK₀, hCv⟩)
  obtain ⟨hkK, hkv⟩ := Subgroup.mem_inf.mp hk
  obtain ⟨hkα, hkβ, hkΔ⟩ := mem_twoPointKernel.mp hkK
  have hkv' : Commute k v := mem_centralizer_zpowers_iff_commute.mp hkv
  refine ⟨k⁻¹ * h, hkv'.inv_left.mul_left hhv, ?_, ?_, ?_, fun δ => ?_⟩
  · change k⁻¹ * h * y = y * (k⁻¹ * h)
    have : h * y = k * y * k⁻¹ * h := by rw [hky, hy', inv_mul_cancel_right]
    rw [mul_assoc, this]; group
  · rw [mul_smul, hhα, inv_smul_eq_iff, hkα]
  · rw [mul_smul, hhβ, inv_smul_eq_iff, hkβ]
  · have hδ' : h • (δ : Ω) ∈ holtDelta G Ω α β := by rw [← hhz]; exact (z δ).2
    rw [mul_smul, hhz, eq_inv_smul_iff, hkΔ _ hδ']

theorem exists_x_commute (hS : Sec4Setting G Ω) {y : G} (hyv : Commute y v) (hy2 : y * y = 1)
    (hyY : y ∈ caseBRad G Ω α β ⟨γ, hC.mem_holtDelta⟩) :
    ∃ x : G, Commute x v ∧ Commute x y ∧ x * x = 1 ∧ x • α = β ∧
      (∀ δ ∈ holtDelta G Ω α β, x • δ = δ) ∧ ∀ ω : Ω, x • ω = ω → v • ω = ω → ω = γ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hyP, hyα, hyβ, hyZ⟩ := mem_caseBRad.mp hyY
  have hyγ : y • γ = γ := congrArg Subtype.val (apply_eq_of_mem_seRadical hyZ.1)
  set V := Subgroup.zpowers v ⊔ Subgroup.zpowers y with hV
  have hV2 : IsPGroup 2 V :=
    (isPGroup_zpowers_of_orderOf_eq_two hC.orderOf_v).to_sup_of_normal_right'
    (isPGroup_zpowers_of_pow_eq_one (k := 1) (by rw [pow_one, sq, hy2]))
    (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _
      (mem_centralizer_zpowers_iff_commute.mpr hyv.symm)))
  have hVαβ : V ≤ stabilizer G α ⊓ stabilizer G β := sup_le
    (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr
      ⟨mem_stabilizer_iff.mpr hC.smul_α, mem_stabilizer_iff.mpr hC.smul_β⟩))
    (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr
      ⟨mem_stabilizer_iff.mpr hyα, mem_stabilizer_iff.mpr hyβ⟩))
  have hVγ : V ≤ stabilizer G γ := sup_le
    (Subgroup.zpowers_le.mpr (mem_stabilizer_iff.mpr hC.smul_γ))
    (Subgroup.zpowers_le.mpr (mem_stabilizer_iff.mpr hyγ))
  obtain ⟨u, hu, huγ, huV⟩ := hS.exists_mem_longInvSwap_centralizer_of_mem_holtDelta hC.ne
    hC.mem_holtDelta hV2 hVαβ hVγ
  have huv : u ∈ Subgroup.centralizer (Subgroup.zpowers v : Set G) :=
    Subgroup.centralizer_le (fun w hw => (le_sup_left : Subgroup.zpowers v ≤ V) hw) huV
  have huy : Commute u y := (Subgroup.mem_centralizer_iff.mp huV y
    ((le_sup_right : Subgroup.zpowers y ≤ V) (Subgroup.mem_zpowers y))).symm
  have huv' : Commute u v := mem_centralizer_zpowers_iff_commute.mp huv
  have huP : u ∈ stabilizer G ({α, β} : Set Ω) :=
    closure_longInvSwap_le_stabilizer_pair α β (Subgroup.subset_closure hu)
  have hu2 : u * u = 1 := mul_self_eq_one_of_mem_longInv hu.1
  have huβ : u • β = α := smul_eq_of_mem_longInvSwap hu
  have hufix : ∀ δ ∈ holtDelta G Ω α β, u • δ = δ ↔ δ = γ := fun δ _ => by
    refine ⟨fun h => ?_, fun h => h ▸ huγ⟩
    obtain ⟨ω, -, hω⟩ := hu.1.2
    exact (hω δ h).trans (hω γ huγ).symm
  obtain ⟨g, hgv, hgy, hgα, hgβ, hgz⟩ := hC.exists_commute_commute_eq_of_mem_rootCenter hS hyv hy2
    hyY (hC.twoPointHom_mem_rootCenter hS huP hu2 hufix)
  have huv' : Commute u v := mem_centralizer_zpowers_iff_commute.mp huv
  set x₀ := g⁻¹ * u with hx₀
  have hx₀α : x₀ • α = β := by rw [hx₀, mul_smul, hu.2, inv_smul_eq_iff, hgβ]
  have hx₀β : x₀ • β = α := by rw [hx₀, mul_smul, huβ, inv_smul_eq_iff, hgα]
  have hx₀Δ : ∀ δ ∈ holtDelta G Ω α β, x₀ • δ = δ := fun δ hδ => by
    have := hgz ⟨δ, hδ⟩
    rw [coe_twoPointHom_apply] at this
    rw [hx₀, mul_smul, this, inv_smul_smul]
  have hx₀v : Commute x₀ v := (hgv.inv_left).mul_left huv'
  have hx₀y : Commute x₀ y := (hgy.inv_left).mul_left huy
  have hK : x₀ * x₀ ∈ twoPointKernel G Ω α β := mem_twoPointKernel.mpr
    ⟨by rw [mul_smul, hx₀α, hx₀β], by rw [mul_smul, hx₀β, hx₀α],
      fun δ hδ => by rw [mul_smul, hx₀Δ δ hδ, hx₀Δ δ hδ]⟩
  obtain ⟨m, hm⟩ : Odd (orderOf (x₀ * x₀)) :=
    hC.odd_card.of_dvd_nat ((twoPointKernel G Ω α β).orderOf_dvd_natCard hK)
  have hpowα : ∀ k : ℕ, (x₀ * x₀) ^ k • α = α := fun k => by
    induction k with
    | zero => rw [pow_zero, one_smul]
    | succ k ih => rw [pow_succ, mul_smul, mul_smul, hx₀α, hx₀β, ih]
  have hpowΔ : ∀ k : ℕ, ∀ δ ∈ holtDelta G Ω α β, (x₀ * x₀) ^ k • δ = δ := fun k δ hδ => by
    induction k with
    | zero => rw [pow_zero, one_smul]
    | succ k ih => rw [pow_succ, mul_smul, mul_smul, hx₀Δ δ hδ, hx₀Δ δ hδ, ih]
  set x := x₀ * (x₀ * x₀) ^ m with hxdef
  have hxv : Commute x v := hx₀v.mul_left ((hx₀v.mul_left hx₀v).pow_left m)
  have hxy : Commute x y := hx₀y.mul_left ((hx₀y.mul_left hx₀y).pow_left m)
  have hx2 : x * x = 1 := by
    have h1 : x = x₀ ^ orderOf (x₀ * x₀) := by rw [hxdef, hm, pow_succ', pow_mul, sq]
    rw [h1, ← pow_add, ← two_mul, pow_mul, sq, pow_orderOf_eq_one]
  have hxα : x • α = β := by rw [hxdef, mul_smul, hpowα, hx₀α]
  have hxΔ : ∀ δ ∈ holtDelta G Ω α β, x • δ = δ := fun δ hδ => by
    rw [hxdef, mul_smul, hpowΔ m δ hδ, hx₀Δ δ hδ]
  refine ⟨x, hxv, hxy, hx2, hxα, hxΔ, fun ω hxω hvω => ?_⟩
  have hy2 : x * v * (x * v) = 1 := by
    rw [show x * v * (x * v) = x * x * (v * v) by rw [mul_assoc, ← mul_assoc v, ← hxv.eq]; group,
      hx2, hC.v_mul_v, one_mul]
  have hyα : (x * v) • α = β := by rw [mul_smul, hC.smul_α, hxα]
  have hord : orderOf (x * v) = 2 := orderOf_eq_prime (by rw [sq, hy2]) fun h => hC.ne (by
    rw [h, one_smul] at hyα; exact hyα)
  have hyJ : x * v ∈ longInv G Ω := by
    refine (hS.mem_longInv_iff_of_odd_twoPointKernel hC.ne hC.odd_card hC.three_le_card hord
      hyα).mpr ⟨γ, ⟨hC.mem_holtDelta, ?_⟩, fun δ ⟨hδ, hδf⟩ => ?_⟩
    · rw [mul_smul, hC.smul_γ, hxΔ γ hC.mem_holtDelta]
    · have hvδ : v • δ ∈ holtDelta G Ω α β := smul_mem_holtDelta_of_mem_pair hC.v_mem_pair hδ
      rw [mul_smul, hxΔ _ hvδ] at hδf
      exact (hC.fixed_iff δ hδ).mp hδf
  obtain ⟨ω₀, -, huniq⟩ := hyJ.2
  have hγf : (x * v) • γ = γ := by rw [mul_smul, hC.smul_γ, hxΔ γ hC.mem_holtDelta]
  have hωf : (x * v) • ω = ω := by rw [mul_smul, hvω, hxω]
  exact (huniq ω hωf).trans (huniq γ hγf).symm

theorem exists_x (hS : Sec4Setting G Ω) :
    ∃ x : G, Commute x v ∧ x * x = 1 ∧ x • α = β ∧ (∀ δ ∈ holtDelta G Ω α β, x • δ = δ) ∧
      ∀ ω : Ω, x • ω = ω → v • ω = ω → ω = γ := by
  obtain ⟨x, hxv, -, hx2, hxα, hxΔ, hxf⟩ :=
    hC.exists_x_commute hS (Commute.refl v) hC.v_mul_v (hC.v_mem_caseBRad hS)
  exact ⟨x, hxv, hx2, hxα, hxΔ, hxf⟩

theorem smul_γ_and_mem_rootCenter_of_mem_longInvSwap (hS : Sec4Setting G Ω) {s : G}
    (hs : s ∈ longInvSwap G Ω α β) (hsv : Commute s v) :
    s • γ = γ ∧ ∃ hsP : s ∈ stabilizer G ({α, β} : Set Ω), twoPointHom G Ω α β ⟨s, hsP⟩ ∈
      rootCenter (seRadical (twoPointJ G Ω α β) ⟨γ, hC.mem_holtDelta⟩) := by
  have hsP : s ∈ stabilizer G ({α, β} : Set Ω) :=
    closure_longInvSwap_le_stabilizer_pair α β (Subgroup.subset_closure hs)
  have hsγ : s • γ = γ := by
    refine (hC.fixed_iff _ (smul_mem_holtDelta_of_mem_pair hsP hC.mem_holtDelta)).mp ?_
    rw [← mul_smul, ← hsv.eq, mul_smul, hC.smul_γ]
  refine ⟨hsγ, hsP, hC.twoPointHom_mem_rootCenter hS hsP (mul_self_eq_one_of_mem_longInv hs.1)
    fun δ _ => ⟨fun h => ?_, fun h => h ▸ hsγ⟩⟩
  obtain ⟨ω, -, hω⟩ := hs.1.2
  exact (hω δ h).trans (hω γ hsγ).symm

theorem exists_mem_caseBRad_mul_self_eq_one (hS : Sec4Setting G Ω)
    {z : Equiv.Perm (holtDelta G Ω α β)}
    (hz : z ∈ rootCenter (seRadical (twoPointJ G Ω α β) ⟨γ, hC.mem_holtDelta⟩)) :
    ∃ y : G, ∃ hyP : y ∈ stabilizer G ({α, β} : Set Ω), y ∈ caseBRad G Ω α β ⟨γ, hC.mem_holtDelta⟩ ∧
      Commute y v ∧ y * y = 1 ∧ twoPointHom G Ω α β ⟨y, hyP⟩ = z := by
  obtain ⟨g, hgv, hgα, hgβ, hgz⟩ := hC.exists_commute_eq_of_mem_rootCenter hS hz
  have hgP : g ∈ stabilizer G ({α, β} : Set Ω) := stabilizer_inf_le_stabilizer_pair α β
    (Subgroup.mem_inf.mpr ⟨mem_stabilizer_iff.mpr hgα, mem_stabilizer_iff.mpr hgβ⟩)
  have hĝ : twoPointHom G Ω α β ⟨g, hgP⟩ = z := twoPointHom_eq_of_forall hgP hgz
  have hz2 := hC.isNaturalSE.mul_self_eq_one_of_mem_rootCenter hz
  have hggP : g * g ∈ stabilizer G ({α, β} : Set Ω) := mul_mem hgP hgP
  have hK : g * g ∈ twoPointKernel G Ω α β := by
    refine mem_twoPointKernel_of_twoPointHom_eq_one hggP (by rw [mul_smul, hgα, hgα])
      (by rw [mul_smul, hgβ, hgβ]) ?_
    rw [show (⟨g * g, hggP⟩ : stabilizer G ({α, β} : Set Ω)) = ⟨g, hgP⟩ * ⟨g, hgP⟩ from rfl,
      map_mul, hĝ, hz2]
  obtain ⟨m, hm⟩ : Odd (orderOf (g * g)) :=
    hC.odd_card.of_dvd_nat ((twoPointKernel G Ω α β).orderOf_dvd_natCard hK)
  have hyP : g ^ orderOf (g * g) ∈ stabilizer G ({α, β} : Set Ω) := pow_mem hgP _
  have himg : twoPointHom G Ω α β ⟨g ^ orderOf (g * g), hyP⟩ = z := by
    rw [show (⟨g ^ orderOf (g * g), hyP⟩ : stabilizer G ({α, β} : Set Ω)) =
      ⟨g, hgP⟩ ^ orderOf (g * g) from rfl, map_pow, hĝ, hm, pow_succ', pow_mul, sq, hz2, one_pow,
      mul_one]
  have hpowα : ∀ k : ℕ, g ^ k • α = α := fun k => by
    induction k with
    | zero => rw [pow_zero, one_smul]
    | succ k ih => rw [pow_succ, mul_smul, hgα, ih]
  have hpowβ : ∀ k : ℕ, g ^ k • β = β := fun k => by
    induction k with
    | zero => rw [pow_zero, one_smul]
    | succ k ih => rw [pow_succ, mul_smul, hgβ, ih]
  refine ⟨g ^ orderOf (g * g), hyP, mem_caseBRad.mpr ⟨hyP, hpowα _, hpowβ _, himg ▸ hz⟩,
    hgv.pow_left _, ?_, himg⟩
  rw [← pow_add, ← two_mul, pow_mul, sq, pow_orderOf_eq_one]

end Prop46CaseB

end Radical

end CFSG.Holt.H78

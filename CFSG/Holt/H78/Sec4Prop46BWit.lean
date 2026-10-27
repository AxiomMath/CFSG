module

public import CFSG.Holt.H78.Sec4Prop46B
public import CFSG.Holt.H78.AltModelSylow
public import CFSG.Holt.H78.OddCoreMinimal
public import CFSG.Holt.H78.Prelim
public import CFSG.Holt.H78.OddCore

public section


namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Open CFSG.GH74.Uniqueness.Bender
open scoped Pointwise

section Realize


namespace HoltData

variable {K : Type*} [Group K] [Finite K] {X : Type*} [MulAction K X] (D : HoltData K X)

theorem exists_mem_longInvAt_rho_conj {j : K} (hj : j ∈ longInv K X) {i₀ : D.ι}
    {g : Equiv.Perm (D.Ψc i₀)} (hg : g ∈ D.M i₀) {e : X}
    (he : ∀ i, i ≠ i₀ → D.ρ i ⟨j, mem_jHull_of_mem_longInv hj⟩ (D.coord e i) = D.coord e i)
    (he₀ : (g * D.ρ i₀ ⟨j, mem_jHull_of_mem_longInv hj⟩ * g⁻¹) (D.coord e i₀) = D.coord e i₀) :
    ∃ j' : jHull K X, (j' : K) ∈ longInvAt K X e ∧
      D.ρ i₀ j' = g * D.ρ i₀ ⟨j, mem_jHull_of_mem_longInv hj⟩ * g⁻¹ ∧
      ∀ i, i ≠ i₀ → D.ρ i j' = D.ρ i ⟨j, mem_jHull_of_mem_longInv hj⟩ := by
  obtain ⟨h, hhL, hhg⟩ := D.mem_M.mp hg
  have hρh : ∀ i, i ≠ i₀ → D.ρ i h = 1 := fun i hi =>
    D.le_ker i₀ i (Ne.symm hi) (show h ∈ (D.L i₀).subgroupOf (jHull K X) from hhL)
  set jH : jHull K X := ⟨j, mem_jHull_of_mem_longInv hj⟩
  set j₁ : jHull K X := h * jH * h⁻¹ with hj₁
  have hj₁J : (j₁ : K) ∈ longInv K X := conj_mem_longInv hj (h : K)
  have hρ₁ : ∀ i, D.ρ i j₁ = D.ρ i h * D.ρ i jH * (D.ρ i h)⁻¹ := fun i => by
    rw [hj₁, map_mul, map_mul, map_inv]
  have hcoord : D.coord ((j₁ : K) • e) = D.coord e := funext fun i => by
    rw [D.coord_smul j₁ e i, hρ₁]
    by_cases hi : i = i₀
    · subst hi; rw [hhg]; exact he₀
    · rw [hρh i hi, one_mul, inv_one, mul_one]; exact he i hi
  obtain ⟨f, hf⟩ := exists_mem_longInvAt hj₁J
  have hef : D.coord e = D.coord f := (D.coord_smul_eq_iff hf e).mp hcoord
  obtain ⟨o, ho⟩ := mem_orbit_iff.mp ((D.coord_eq_iff f e).mp hef.symm)
  set oH : jHull K X := ⟨(o : K), jOddCore_le_jHull o.2⟩
  refine ⟨oH * j₁ * oH⁻¹, ?_, ?_, fun i hi => ?_⟩
  · have := conj_mem_longInvAt hf (o : K)
    rwa [show (o : K) • f = e from ho] at this
  · rw [map_mul, map_mul, map_inv, D.rho_eq_one_of_mem_jOddCore (h := oH) o.2, one_mul, inv_one,
      mul_one, hρ₁, hhg]
  · rw [map_mul, map_mul, map_inv, D.rho_eq_one_of_mem_jOddCore (h := oH) o.2, one_mul, inv_one,
      mul_one, hρ₁, hρh i hi, one_mul, inv_one, mul_one]

end HoltData

end Realize

section Section


variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω] {v : G}

abbrev typeLHom (v : G) :
    Subgroup.centralizer (Subgroup.zpowers v : Set G) →* typeLSection G Ω v :=
  (MulAction.toPermHom (Subgroup.centralizer (Subgroup.zpowers v : Set G))
    (fixSet Ω (Subgroup.zpowers v))).rangeRestrict

abbrev typeLElt {g : G} (hg : Commute g v) : typeLSection G Ω v :=
  typeLHom (Ω := Ω) v ⟨g, mem_centralizer_zpowers_iff_commute.mpr hg⟩

@[simp] theorem coe_typeLElt_apply {g : G} (hg : Commute g v)
    (ω : fixSet Ω (Subgroup.zpowers v)) :
    (((typeLElt (Ω := Ω) hg : typeLSection G Ω v) :
      Equiv.Perm (fixSet Ω (Subgroup.zpowers v))) ω : Ω) = g • (ω : Ω) := rfl

theorem typeLElt_mul {g h : G} (hg : Commute g v) (hh : Commute h v) :
    typeLElt (Ω := Ω) hg * typeLElt hh = typeLElt (hg.mul_left hh) :=
  (map_mul (typeLHom (Ω := Ω) v) _ _).symm

theorem typeLElt_pow {g : G} (hg : Commute g v) (n : ℕ) :
    typeLElt (Ω := Ω) hg ^ n = typeLElt (hg.pow_left n) := by
  rw [← map_pow]
  congr 1

theorem ncard_fixedBy_of_isConj {s : G} (hs : IsConj v s) :
    (fixedBy Ω s).ncard = (fixedBy Ω v).ncard := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hs
  rw [← smul_fixedBy, Set.ncard_smul_set]

end Section

section Setup

variable {G : Type} [Group G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  {α β γ : Ω} {v : G} {P : Subgroup (typeLSection G Ω v)}

namespace Prop46CaseB

variable (hC : Prop46CaseB G Ω α β γ v P)
include hC

omit [DecidableEq Ω] in
theorem odd_card_P : Odd (Nat.card P) := by
  have h := Subgroup.card_dvd_of_le hC.le_oddCore
  have hc : Nat.Coprime 2 (Nat.card (CFSG.pPrimeCore 2 (typeLSection G Ω v))) :=
    CFSG.pPrimeCore_coprime_card
  exact Nat.odd_iff.mpr (by
    have := Nat.Coprime.coprime_dvd_right h hc
    exact Nat.two_dvd_ne_zero.mp fun h2 => by
      have := Nat.Coprime.eq_one_of_dvd this h2; omega)

omit [DecidableEq Ω] in
theorem P_comm : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p :=
  commute_of_minimal_normal_of_odd hC.normal hC.minimal hC.odd_card_P

omit [DecidableEq Ω] in
theorem smul_smul_eq_inv_smul {r : typeLSection G Ω v} (hr : r * r = 1)
    {e : fixSet Ω (Subgroup.zpowers v)} (hre : r • e = e) (huniq : ∀ ω, r • ω = ω → ω = e)
    {p : typeLSection G Ω v} (hp : p ∈ P) : r • (p • e) = p⁻¹ • e :=
  smul_smul_eq_inv_smul_of_normal hC.normal hC.P_comm hr hre (fun _ _ h => huniq _ h) hp

omit [Fintype Ω] [DecidableEq Ω] in
theorem exists_mem_P_smul_α_eq_β :
    ∃ p ∈ P, p • (⟨α, hC.α_mem⟩ : fixSet Ω (Subgroup.zpowers v)) = ⟨β, hC.β_mem⟩ := by
  obtain ⟨p, hp, a, ha, hpa⟩ := hC.mem_orbit
  obtain rfl : a = ⟨α, hC.α_mem⟩ := Subtype.ext ha
  exact ⟨p, hp, Subtype.ext hpa⟩

omit [DecidableEq Ω] in
theorem exists_mem_P_smul_α_eq_γ {x : G} (hxv : Commute x v) (hx2 : x * x = 1)
    (hxα : x • α = β) (hxfix : ∀ ω : Ω, x • ω = ω → v • ω = ω → ω = γ) :
    ∃ p ∈ P, p • (⟨α, hC.α_mem⟩ : fixSet Ω (Subgroup.zpowers v)) = ⟨γ, hC.γ_mem⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨p₀, hp₀, hp₀a⟩ := hC.exists_mem_P_smul_α_eq_β
  set a : fixSet Ω (Subgroup.zpowers v) := ⟨α, hC.α_mem⟩
  set xb : typeLSection G Ω v := typeLElt (Ω := Ω) hxv with hxb
  have hxb2 : xb * xb = 1 := by
    rw [hxb, typeLElt_mul]
    exact Subtype.ext (Equiv.ext fun ω => Subtype.ext (by
      change (x * x) • (ω : Ω) = ω; rw [hx2, one_smul]))
  have hxba : xb • a = ⟨β, hC.β_mem⟩ := Subtype.ext hxα
  set O : Set (fixSet Ω (Subgroup.zpowers v)) := orbit P a
  have hsub : ∀ y ∈ O, xb • y ∈ O := by
    rintro _ ⟨q, rfl⟩
    refine ⟨⟨xb * q * xb⁻¹ * p₀, mul_mem (hC.normal.conj_mem _ q.2 xb) hp₀⟩, ?_⟩
    change (xb * q * xb⁻¹ * p₀) • a = xb • ((q : typeLSection G Ω v) • a)
    rw [mul_smul, hp₀a, ← hxba, ← mul_smul, ← mul_smul, inv_mul_cancel_right, mul_smul]
  have hstab : Subgroup.zpowers xb ≤ stabilizer (typeLSection G Ω v) O := by
    rw [Subgroup.zpowers_le, mem_stabilizer_iff]
    refine Set.Subset.antisymm ?_ fun y hy => ?_
    · rintro _ ⟨y, hy, rfl⟩; exact hsub y hy
    · refine ⟨xb • y, hsub y hy, ?_⟩
      show xb • (xb • y) = y
      rw [← mul_smul, hxb2, one_smul]
  have hodd : Odd (Nat.card O) := by
    rw [Nat.card_coe_set_eq, ← index_stabilizer]
    exact Odd.of_dvd_nat hC.odd_card_P (Subgroup.index_dvd_card _)
  have : Finite O := Set.toFinite O
  obtain ⟨ω, ⟨q, hq⟩, hωfix⟩ := exists_mem_fixSet_of_le_stabilizer
    (isPGroup_zpowers_of_orderOf_eq_two (orderOf_eq_prime (by rw [sq]; exact hxb2) fun h => by
      have h' := hxba
      rw [h, one_smul] at h'
      exact hC.ne (congrArg Subtype.val h'))) hodd hstab
  have hxω : x • (ω : Ω) = ω := congrArg Subtype.val (hωfix xb (Subgroup.mem_zpowers xb))
  have hωγ := hxfix ω hxω (ω.2 v (Subgroup.mem_zpowers v))
  have hωc : ω = ⟨γ, hC.γ_mem⟩ := Subtype.ext hωγ
  exact ⟨q, q.2, hq.trans hωc⟩

end Prop46CaseB

end Setup

section GAP9

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β γ : Ω} {v : G} {P : Subgroup (typeLSection G Ω v)}

namespace Prop46CaseB

variable (hC : Prop46CaseB G Ω α β γ v P)
include hC

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem typeLElt_x_mem {x : G} (hxv : Commute x v) (hx2 : x * x = 1)
    (hxα : x • α = β) (hxΔ : ∀ δ ∈ holtDelta G Ω α β, x • δ = δ)
    (hxfix : ∀ ω : Ω, x • ω = ω → v • ω = ω → ω = γ) :
    typeLElt (Ω := Ω) hxv ∈ longInvAt (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))
      ⟨γ, hC.γ_mem⟩ ∧
    typeLElt (Ω := Ω) hxv • (⟨α, hC.α_mem⟩ : fixSet Ω (Subgroup.zpowers v)) = ⟨β, hC.β_mem⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxγ : x • γ = γ := hxΔ γ hC.mem_holtDelta
  have hxa : typeLElt (Ω := Ω) hxv • (⟨α, hC.α_mem⟩ : fixSet Ω (Subgroup.zpowers v)) =
      ⟨β, hC.β_mem⟩ := Subtype.ext hxα
  refine ⟨⟨⟨orderOf_eq_prime ?_ fun h => ?_, ⟨⟨γ, hC.γ_mem⟩, Subtype.ext hxγ,
    fun ω hω => Subtype.ext (hxfix ω (congrArg Subtype.val hω) (ω.2 v (Subgroup.mem_zpowers v)))⟩⟩,
    Subtype.ext hxγ⟩, hxa⟩
  · rw [sq, typeLElt_mul]
    exact Subtype.ext (Equiv.ext fun ω => Subtype.ext (by
      change (x * x) • (ω : Ω) = ω; rw [hx2, one_smul]))
  · have h' := hxa
    rw [h, one_smul] at h'
    exact hC.ne (congrArg Subtype.val h')

theorem false_of_isNaturalSE (hS : Sec4Setting G Ω)
    (D : HoltData (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))) (i₀ : D.ι)
    (hSE : IsNaturalSE (D.M i₀)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 (Subgroup.zpowers v) := isPGroup_zpowers_of_orderOf_eq_two hC.orderOf_v
  have h3 : 3 ≤ Nat.card (fixSet Ω (Subgroup.zpowers v)) :=
    three_le_card_fixSet_of_isTypeL hS.star hC.isTypeL
  have hK : IsStarGroup (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) :=
    hS.star_typeLSection hC.isTypeL
  obtain ⟨x, hxv, hx2, hxα, hxΔ, hxuniq⟩ := hC.exists_x hS
  obtain ⟨hxJ, hxa⟩ := hC.typeLElt_x_mem hxv hx2 hxα hxΔ hxuniq
  obtain ⟨p₀, hp₀, hp₀a⟩ := hC.exists_mem_P_smul_α_eq_β
  obtain ⟨p₁, hp₁, hp₁a⟩ := hC.exists_mem_P_smul_α_eq_γ hxv hx2 hxα hxuniq
  set a : fixSet Ω (Subgroup.zpowers v) := ⟨α, hC.α_mem⟩ with ha
  set b : fixSet Ω (Subgroup.zpowers v) := ⟨β, hC.β_mem⟩ with hb
  set c : fixSet Ω (Subgroup.zpowers v) := ⟨γ, hC.γ_mem⟩ with hc
  have hcoord : ∀ {p}, p ∈ P → D.coord (p • a) = D.coord a := fun {p} hp => by
    have h1 : p • a ∈ orbit (CFSG.pPrimeCore 2 (typeLSection G Ω v)) a :=
      ⟨⟨p, hC.le_oddCore hp⟩, rfl⟩
    rw [← orbit_jOddCore_eq hK] at h1
    exact ((D.coord_eq_iff a _).mpr h1).symm
  have hbB : D.coord b = D.coord a := by rw [← hp₀a]; exact hcoord hp₀
  have hcB : D.coord c = D.coord a := by rw [← hp₁a]; exact hcoord hp₁
  set B₁ := D.coord a i₀ with hB₁
  have hJsw : ∀ j : typeLSection G Ω v, ∀ hj : j ∈ longInv _ (fixSet Ω (Subgroup.zpowers v)),
      j • a = b → D.ρ i₀ ⟨j, mem_jHull_of_mem_longInv hj⟩ ∈ rootCenter (seRadical (D.M i₀) B₁) ∧
        D.ρ i₀ ⟨j, mem_jHull_of_mem_longInv hj⟩ ≠ 1 := by
    intro j hj hja
    have hL := D.rho_mem_longInv hj i₀
    have hM : D.ρ i₀ ⟨j, mem_jHull_of_mem_longInv hj⟩ ∈ D.M i₀ := by
      rw [← D.range_rho_of_not_isOuterFactor hSE.not_isOuterFactor]; exact ⟨_, rfl⟩
    have hfixB : D.ρ i₀ ⟨j, mem_jHull_of_mem_longInv hj⟩ B₁ = B₁ := by
      have := D.coord_smul ⟨j, mem_jHull_of_mem_longInv hj⟩ a i₀
      rw [show ((⟨j, mem_jHull_of_mem_longInv hj⟩ : jHull _ _) : typeLSection G Ω v) • a = b
        from hja, hbB] at this
      exact this.symm
    refine ⟨hSE.mem_rootCenter_seRadical hM hfixB ?_, fun h1 => ?_⟩
    · rw [← map_mul, show (⟨j, mem_jHull_of_mem_longInv hj⟩ * ⟨j, mem_jHull_of_mem_longInv hj⟩ :
        jHull _ _) = 1 from Subtype.ext (mul_self_eq_one_of_mem_longInv hj), map_one]
    · have := hL.1; rw [h1, orderOf_one] at this; omega
  set xb := typeLElt (Ω := Ω) hxv with hxb
  have hxbH : xb ∈ jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) :=
    mem_jHull_of_mem_longInv hxJ.1
  set a₀ := D.ρ i₀ ⟨xb, hxbH⟩ with ha₀
  obtain ⟨ha₀Z, ha₀1⟩ := hJsw xb hxJ.1 hxa
  have ha₀2 : a₀ * a₀ = 1 := hSE.mul_self_eq_one_of_mem_rootCenter ha₀Z
  have hord : ∀ y : D.M i₀, (y : Equiv.Perm (D.Ψc i₀)) * y = 1 → (y : Equiv.Perm (D.Ψc i₀)) ≠ 1 →
      orderOf y = 2 := fun y h2 h1 =>
    orderOf_eq_prime (by rw [sq]; exact Subtype.ext h2) fun h => h1 (congrArg Subtype.val h)
  have huniq : ∀ r : typeLSection G Ω v, r ∈ longInvAt _ (fixSet Ω (Subgroup.zpowers v)) c →
      ∀ ω, r • ω = ω → ω = c := fun r hr ω hω => by
    obtain ⟨ω₀, -, h⟩ := hr.1.2
    exact (h ω hω).trans (h c hr.2).symm
  have hainv : a = p₁⁻¹ • c := by rw [eq_inv_smul_iff]; exact hp₁a
  have hreal : ∀ m ∈ rootCenter (seRadical (D.M i₀) B₁), m ≠ 1 →
      ∃ j : typeLSection G Ω v, ∃ hj : j ∈ longInv _ (fixSet Ω (Subgroup.zpowers v)),
        j • a = b ∧ D.ρ i₀ ⟨j, mem_jHull_of_mem_longInv hj⟩ = m := by
    intro m hmZ hm1
    have hmM : m ∈ D.M i₀ := seRadical_le hmZ.1
    have ha₀M : a₀ ∈ D.M i₀ := seRadical_le ha₀Z.1
    obtain ⟨g, hg⟩ := isConj_iff.mp (hSE.isConj (x := ⟨a₀, ha₀M⟩) (y := ⟨m, hmM⟩)
      (hord _ ha₀2 ha₀1) (hord _ (hSE.mul_self_eq_one_of_mem_rootCenter hmZ) hm1))
    have hgm : (g : Equiv.Perm (D.Ψc i₀)) * a₀ * (g : Equiv.Perm (D.Ψc i₀))⁻¹ = m :=
      congrArg Subtype.val hg
    have he : ∀ i, i ≠ i₀ → D.ρ i ⟨xb, hxbH⟩ (D.coord c i) = D.coord c i := fun i _ => by
      rw [← D.coord_smul]
      exact congrArg (fun ω => D.coord ω i) hxJ.2
    have he₀ : ((g : Equiv.Perm (D.Ψc i₀)) * a₀ * (g : Equiv.Perm (D.Ψc i₀))⁻¹) (D.coord c i₀) =
        D.coord c i₀ := by
      rw [hgm, hcB]; exact apply_eq_of_mem_seRadical hmZ.1
    obtain ⟨j', hj'c, hj'ρ, -⟩ := D.exists_mem_longInvAt_rho_conj hxJ.1 g.2 he he₀
    refine ⟨j', hj'c.1, ?_, by rw [← hgm]; exact hj'ρ⟩
    have h1 := hC.smul_smul_eq_inv_smul (mul_self_eq_one_of_mem_longInv hj'c.1) hj'c.2
      (huniq _ hj'c) (inv_mem hp₁)
    have h2 := hC.smul_smul_eq_inv_smul (mul_self_eq_one_of_mem_longInv hxJ.1) hxJ.2
      (huniq _ hxJ) (inv_mem hp₁)
    rw [hainv, h1, ← h2, ← hainv, hxa]
  obtain ⟨m, hmZ, hm1, hma₀⟩ : ∃ m ∈ rootCenter (seRadical (D.M i₀) B₁), m ≠ 1 ∧ m ≠ a₀ := by
    obtain ⟨n, i, e, hA⟩ := isNaturalSE_iff.mp hSE
    have hcard := hA.card_rootCenter_seRadical B₁
    have h4 := hA.four_le_q
    by_contra hcon
    push Not at hcon
    have hsub : (rootCenter (seRadical (D.M i₀) B₁) : Set (Equiv.Perm (D.Ψc i₀))) ⊆ {1, a₀} :=
      fun y hy => by
        by_cases h1 : y = 1
        · exact Or.inl h1
        · exact Or.inr (hcon y hy h1)
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hcard] at hle
    have h2 : ({1, a₀} : Set (Equiv.Perm (D.Ψc i₀))).ncard ≤ 2 :=
      (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    omega
  have hm2 : m * m = 1 := hSE.mul_self_eq_one_of_mem_rootCenter hmZ
  have hm'1 : m * a₀ ≠ 1 := fun h => hma₀ (by
    rw [mul_eq_one_iff_eq_inv, inv_eq_of_mul_eq_one_right ha₀2] at h; exact h)
  obtain ⟨j, hj, hja, hjm⟩ := hreal m hmZ hm1
  obtain ⟨j', hj', hj'a, hj'm⟩ := hreal (m * a₀) (mul_mem hmZ ha₀Z) hm'1
  obtain ⟨s, hs, hsv, hsj⟩ := (hS.mem_longInvSwap_centralizerImage_iff hV2 h3 j).mp ⟨hj, hja⟩
  obtain ⟨s', hs', hs'v, hs'j⟩ :=
    (hS.mem_longInvSwap_centralizerImage_iff hV2 h3 j').mp ⟨hj', hj'a⟩
  have hsv' : Commute s v := mem_centralizer_zpowers_iff_commute.mp hsv
  have hs'v' : Commute s' v := mem_centralizer_zpowers_iff_commute.mp hs'v
  have hjs : j = typeLElt (Ω := Ω) hsv' := Subtype.ext (Equiv.ext fun ω => Subtype.ext (hsj ω))
  have hj's : j' = typeLElt (Ω := Ω) hs'v' :=
    Subtype.ext (Equiv.ext fun ω => Subtype.ext (hs'j ω))
  obtain ⟨-, hsP, hsZ⟩ := hC.smul_γ_and_mem_rootCenter_of_mem_longInvSwap hS hs hsv'
  obtain ⟨-, hs'P, hs'Z⟩ := hC.smul_γ_and_mem_rootCenter_of_mem_longInvSwap hS hs' hs'v'
  have hssP : s * s' ∈ stabilizer G ({α, β} : Set Ω) := mul_mem hsP hs'P
  have hssα : (s * s') • α = α := by rw [mul_smul, hs'.2, smul_eq_of_mem_longInvSwap hs]
  have hssβ : (s * s') • β = β := by rw [mul_smul, smul_eq_of_mem_longInvSwap hs', hs.2]
  have hjj : D.ρ i₀ (⟨j, mem_jHull_of_mem_longInv hj⟩ * ⟨j', mem_jHull_of_mem_longInv hj'⟩) =
      a₀ := by
    rw [map_mul, hjm, hj'm, ← mul_assoc, hm2, one_mul]
  by_cases hz : twoPointHom G Ω α β ⟨s * s', hssP⟩ = 1
  ·
    have hK0 := mem_twoPointKernel_of_twoPointHom_eq_one hssP hssα hssβ hz
    have hodd : Odd (orderOf (s * s')) :=
      hC.odd_card.of_dvd_nat ((twoPointKernel G Ω α β).orderOf_dvd_natCard hK0)
    have hdvd : orderOf a₀ ∣ orderOf (s * s') := by
      rw [← hjj]
      refine (orderOf_map_dvd _ _).trans ?_
      rw [← Subgroup.orderOf_coe]
      change orderOf (j * j') ∣ _
      rw [hjs, hj's, typeLElt_mul]
      exact (orderOf_map_dvd _ _).trans (by rw [Subgroup.orderOf_mk])
    have ha₀ord : orderOf a₀ = 2 := orderOf_eq_prime (by rw [sq, ha₀2]) ha₀1
    rw [ha₀ord] at hdvd
    exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr hdvd)
  ·
    have hxord : orderOf x = 2 := orderOf_eq_prime (by rw [sq, hx2]) fun h => hC.ne (by
      rw [h, one_smul] at hxα; exact hxα)
    have hxP : x ∈ stabilizer G ({α, β} : Set Ω) := mem_stabilizer_pair_of_orderOf_eq_two hxord hxα
    have heP : x * (s * s') ∈ stabilizer G ({α, β} : Set Ω) := mul_mem hxP hssP
    have heα : (x * (s * s')) • α = β := by rw [mul_smul, hssα, hxα]
    have hx1 : twoPointHom G Ω α β ⟨x, hxP⟩ = 1 := Equiv.ext fun δ => Subtype.ext (hxΔ δ δ.2)
    have heΔ : twoPointHom G Ω α β ⟨x * (s * s'), heP⟩ =
        twoPointHom G Ω α β ⟨s * s', hssP⟩ := by
      rw [show (⟨x * (s * s'), heP⟩ : stabilizer G ({α, β} : Set Ω)) = ⟨x, hxP⟩ * ⟨s * s', hssP⟩
        from rfl, map_mul, hx1, one_mul]
    have hssZ : twoPointHom G Ω α β ⟨s * s', hssP⟩ ∈
        rootCenter (seRadical (twoPointJ G Ω α β) ⟨γ, hC.mem_holtDelta⟩) := by
      rw [show (⟨s * s', hssP⟩ : stabilizer G ({α, β} : Set Ω)) = ⟨s, hsP⟩ * ⟨s', hs'P⟩ from rfl,
        map_mul]
      exact mul_mem hsZ hs'Z
    obtain ⟨n, -, hen⟩ := hC.exists_odd_pow_mem_longInv hS heP heα (heΔ ▸ hssZ) (heΔ ▸ hz)
    have hev : Commute (x * (s * s')) v := hxv.mul_left (hsv'.mul_left hs'v')
    have henv : Commute ((x * (s * s')) ^ n) v := hev.pow_left n
    have henJ : typeLElt (Ω := Ω) henv ∈
        longInv (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) :=
      (hS.mem_longInv_centralizerImage_iff hV2 h3 _).mpr
        ⟨_, hen.1, mem_centralizer_zpowers_iff_commute.mpr henv, fun ω => rfl⟩
    have hena : typeLElt (Ω := Ω) henv • a = b := Subtype.ext hen.2
    apply (hJsw _ henJ hena).2
    have hē : typeLElt (Ω := Ω) hev = xb * (j * j') := by
      rw [hxb, hjs, hj's, typeLElt_mul, typeLElt_mul]
    have hēH : typeLElt (Ω := Ω) hev ∈
        jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) := by
      rw [hē]
      exact mul_mem hxbH (mul_mem (mem_jHull_of_mem_longInv hj) (mem_jHull_of_mem_longInv hj'))
    have h1 : (⟨typeLElt (Ω := Ω) henv, mem_jHull_of_mem_longInv henJ⟩ : jHull _ _) =
        ⟨typeLElt (Ω := Ω) hev, hēH⟩ ^ n :=
      Subtype.ext (by rw [SubgroupClass.coe_pow, typeLElt_pow hev n])
    have h2 : D.ρ i₀ ⟨typeLElt (Ω := Ω) hev, hēH⟩ = 1 := by
      have : (⟨typeLElt (Ω := Ω) hev, hēH⟩ : jHull _ _) = ⟨xb, hxbH⟩ *
          (⟨j, mem_jHull_of_mem_longInv hj⟩ * ⟨j', mem_jHull_of_mem_longInv hj'⟩) :=
        Subtype.ext hē
      rw [this, map_mul, map_mul, hjm, hj'm, ← mul_assoc m, hm2, one_mul, ha₀2]
    rw [h1, map_pow, h2, one_pow]

end Prop46CaseB

end GAP9

section Solvable

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {Δ : Type} [Finite Δ] {L : Subgroup (Equiv.Perm Δ)}

theorem IsNaturalSE.isSolvable_normalizer_inf_stabilizer (hL : IsNaturalSE L) (b : Δ) :
    Group.IsSolvable ↥(Subgroup.normalizer (L : Set (Equiv.Perm Δ)) ⊓
      stabilizer (Equiv.Perm Δ) b) := by
  obtain ⟨n, i, e, hA⟩ := isNaturalSE_iff.mp hL
  have : Finite L := inferInstance
  have hLb : Group.IsSolvable ↥(stabilizer ↥L b) := by
    obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer b
    obtain ⟨t, hc⟩ := hA.benderType.exists_benderCore Q
    rw [hA.stabilizer_eq_borel hQ]
    exact hc.isSolvable_borel
  have hout : Group.IsSolvable (Outer ↥L) := BenderType.isSolvable_outer hA.benderType
  set X := Subgroup.normalizer (L : Set (Equiv.Perm Δ)) ⊓ stabilizer (Equiv.Perm Δ) b
  let φ : (L.subgroupOf X) →* stabilizer (↥L) b :=
    { toFun := fun x => ⟨⟨((x : X) : Equiv.Perm Δ), x.2⟩,
        mem_stabilizer_iff.mpr (mem_stabilizer_iff.mp (Subgroup.mem_inf.mp (x : X).2).2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := fun x y hxy => by
    have := congrArg (fun z : stabilizer (↥L) b => ((z : ↥L) : Equiv.Perm Δ)) hxy
    exact Subtype.ext (Subtype.ext this)
  have : Group.IsSolvable (L.subgroupOf X) := Group.isSolvable_of_isSolvable_injective hφ
  refine Group.isSolvable_of_ker_le_range (L.subgroupOf X).subtype
    ((normalizerOuterHom L).comp (Subgroup.inclusion inf_le_left)) fun x hx => ?_
  have h1 := (hL.normalizerOuterHom_eq_one_iff _).mp hx
  exact ⟨⟨x, h1⟩, rfl⟩

end Solvable

section TwoPointJ


variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω] {α β : Ω}

theorem conj_mem_closure_longInvSwap {g : G} (hg : g ∈ stabilizer G ({α, β} : Set Ω)) {k : G}
    (hk : k ∈ Subgroup.closure (longInvSwap G Ω α β)) :
    g * k * g⁻¹ ∈ Subgroup.closure (longInvSwap G Ω α β) := by
  induction hk using Subgroup.closure_induction with
  | mem t ht =>
    refine Subgroup.subset_closure ?_
    have h := conj_mem_longInvSwap ht g
    rcases smul_pair_of_mem_stabilizer_pair hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rwa [h1, h2] at h
    · rwa [h1, h2, ← longInvSwap_comm] at h
  | one => simp
  | mul x y _ _ hx hy =>
    rw [show g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) by group]
    exact mul_mem hx hy
  | inv x _ hx =>
    rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
    exact inv_mem hx

theorem conj_mem_twoPointJ {g : G} (hg : g ∈ stabilizer G ({α, β} : Set Ω))
    {n : Equiv.Perm (holtDelta G Ω α β)} (hn : n ∈ twoPointJ G Ω α β) :
    twoPointHom G Ω α β ⟨g, hg⟩ * n * (twoPointHom G Ω α β ⟨g, hg⟩)⁻¹ ∈ twoPointJ G Ω α β := by
  obtain ⟨k, hk, hkn⟩ := mem_twoPointJ.mp hn
  refine mem_twoPointJ.mpr ⟨g * k * g⁻¹, conj_mem_closure_longInvSwap hg hk, fun δ => ?_⟩
  rw [← map_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, coe_twoPointHom_apply, hkn,
    coe_twoPointHom_apply]
  simp only [mul_smul]
  rfl

end TwoPointJ

section Alternating

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β γ : Ω} {v : G} {P : Subgroup (typeLSection G Ω v)}

namespace Prop46CaseB

variable (hC : Prop46CaseB G Ω α β γ v P)
include hC

omit [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem isSolvable_centralizer_inf :
    Group.IsSolvable ↥(Subgroup.centralizer (Subgroup.zpowers v : Set G) ⊓
      (stabilizer G α ⊓ stabilizer G β)) := by
  set W := Subgroup.centralizer (Subgroup.zpowers v : Set G) ⊓ (stabilizer G α ⊓ stabilizer G β)
  have hWP : W ≤ stabilizer G ({α, β} : Set Ω) :=
    inf_le_right.trans (stabilizer_inf_le_stabilizer_pair α β)
  set f : W →* Equiv.Perm (holtDelta G Ω α β) :=
    (twoPointHom G Ω α β).comp (Subgroup.inclusion hWP)
  set X := Subgroup.normalizer (twoPointJ G Ω α β : Set (Equiv.Perm (holtDelta G Ω α β))) ⊓
    stabilizer (Equiv.Perm (holtDelta G Ω α β)) (⟨γ, hC.mem_holtDelta⟩ : holtDelta G Ω α β)
  have hX : Group.IsSolvable X := hC.isNaturalSE.isSolvable_normalizer_inf_stabilizer _
  have hrange : ∀ w : W, f w ∈ X := fun w => by
    obtain ⟨hwv, hwα, hwβ⟩ : w.1 ∈ Subgroup.centralizer (Subgroup.zpowers v : Set G) ∧
        w.1 ∈ stabilizer G α ∧ w.1 ∈ stabilizer G β := ⟨w.2.1, w.2.2.1, w.2.2.2⟩
    have hwγ : (w : G) • γ = γ := by
      refine (hC.fixed_iff _ (smul_mem_holtDelta_of_mem_pair (hWP w.2) hC.mem_holtDelta)).mp ?_
      rw [← mul_smul, ← (mem_centralizer_zpowers_iff_commute.mp hwv).eq, mul_smul, hC.smul_γ]
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_normalizer_iff.mpr fun n => ⟨fun hn => ?_,
      fun hn => ?_⟩, mem_stabilizer_iff.mpr (Subtype.ext hwγ)⟩
    · exact conj_mem_twoPointJ (hWP w.2) hn
    · have := conj_mem_twoPointJ (inv_mem (hWP w.2)) hn
      rwa [show (⟨(w : G)⁻¹, inv_mem (hWP w.2)⟩ : stabilizer G ({α, β} : Set Ω)) =
        (⟨w, hWP w.2⟩ : stabilizer G ({α, β} : Set Ω))⁻¹ from rfl, map_inv, inv_inv,
        show f w = twoPointHom G Ω α β ⟨w, hWP w.2⟩ from rfl, ← mul_assoc, ← mul_assoc,
        inv_mul_cancel, one_mul, mul_assoc, inv_mul_cancel, mul_one] at this
  set g : W →* X := f.codRestrict X hrange
  have : Group.IsSolvable (twoPointKernel G Ω α β) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hC.odd_card
  have hker : Group.IsSolvable g.ker := by
    let ψ : g.ker →* twoPointKernel G Ω α β :=
      { toFun := fun x => ⟨((x : W) : G), by
          have hx : f x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
          exact mem_twoPointKernel_of_twoPointHom_eq_one (hWP (x : W).2) (x : W).2.2.1
            (x : W).2.2.2 hx⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine Group.isSolvable_of_isSolvable_injective (f := ψ) fun x y hxy => ?_
    have h := congrArg (fun z : twoPointKernel G Ω α β => (z : G)) hxy
    exact Subtype.ext (Subtype.ext h)
  exact Group.isSolvable_of_ker_le_range g.ker.subtype g fun x hx => ⟨⟨x, hx⟩, rfl⟩

theorem false_of_alternating (hS : Sec4Setting G Ω)
    (D : HoltData (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))) (i₀ : D.ι)
    (hA : D.M i₀ = alternatingGroup (D.Ψc i₀) ∧ 7 ≤ Fintype.card (D.Ψc i₀)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 (Subgroup.zpowers v) := isPGroup_zpowers_of_orderOf_eq_two hC.orderOf_v
  have h3 : 3 ≤ Nat.card (fixSet Ω (Subgroup.zpowers v)) :=
    three_le_card_fixSet_of_isTypeL hS.star hC.isTypeL
  obtain ⟨p₀, hp₀, hp₀a⟩ := hC.exists_mem_P_smul_α_eq_β
  obtain ⟨t, ht, u, -, -, htu, htuv, -⟩ := hC.isTypeL
  have htv : Commute t v := htuv ▸ (Commute.refl t).mul_right htu
  set a : fixSet Ω (Subgroup.zpowers v) := ⟨α, hC.α_mem⟩ with ha
  set b : fixSet Ω (Subgroup.zpowers v) := ⟨β, hC.β_mem⟩ with hb
  set H₁ := jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))
  have htJ : typeLElt (Ω := Ω) htv ∈
      longInvAt (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) a :=
    (hS.mem_longInvAt_centralizerImage_iff hV2 h3 _).mpr
      ⟨t, ht, mem_centralizer_zpowers_iff_commute.mpr htv, fun ω => rfl⟩
  set B₁ := D.coord a i₀
  have hreal : ∀ π ∈ longInvAt (Equiv.Perm (D.Ψc i₀)) (D.Ψc i₀) B₁, ∃ j : typeLSection G Ω v,
      ∃ hj : j ∈ longInvAt _ (fixSet Ω (Subgroup.zpowers v)) a,
        D.ρ i₀ ⟨j, mem_jHull_of_mem_longInv hj.1⟩ = π := by
    intro π hπ
    have hρt := D.rho_mem_longInvAt htJ
    obtain ⟨g, hgA, hg⟩ := exists_mem_alternatingGroup_conj_eq (hρt i₀).1 hπ.1
    have hgM : g ∈ D.M i₀ := hA.1 ▸ hgA
    obtain ⟨j', hj'a, hj'ρ, -⟩ := D.exists_mem_longInvAt_rho_conj htJ.1 hgM
      (fun i _ => (hρt i).2) (by rw [hg]; exact hπ.2)
    exact ⟨j', hj'a, by rw [← hg]; exact hj'ρ⟩
  set W := Subgroup.centralizer (Subgroup.zpowers v : Set G) ⊓ (stabilizer G α ⊓ stabilizer G β)
  have : Group.IsSolvable W := hC.isSolvable_centralizer_inf
  have hWC : W ≤ Subgroup.centralizer (Subgroup.zpowers v : Set G) := inf_le_left
  set Wimg : Subgroup (typeLSection G Ω v) := (W.subgroupOf _).map (typeLHom (Ω := Ω) v)
  have : Group.IsSolvable Wimg := by
    have : Group.IsSolvable (W.subgroupOf (Subgroup.centralizer (Subgroup.zpowers v : Set G))) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hWC).toMonoidHom) (MulEquiv.injective _)
    exact Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective _ _)
  set R : Subgroup (Equiv.Perm (D.Ψc i₀)) := (Wimg.subgroupOf H₁).map (D.ρ i₀)
  have hR : Group.IsSolvable R := by
    let ι : (Wimg.subgroupOf H₁) →* Wimg :=
      { toFun := fun x => ⟨((x : H₁) : typeLSection G Ω v), x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have : Group.IsSolvable (Wimg.subgroupOf H₁) :=
      Group.isSolvable_of_isSolvable_injective (f := ι) fun x y h =>
        Subtype.ext (Subtype.ext (congrArg (fun z : Wimg => (z : typeLSection G Ω v)) h))
    exact Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective _ _)
  have huniq : ∀ r ∈ longInvAt (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) a,
      ∀ ω, r • ω = ω → ω = a := fun r hr ω hω => by
    obtain ⟨ω₀, -, h⟩ := hr.1.2
    exact (h ω hω).trans (h a hr.2).symm
  have hprod : ∀ j₁ ∈ longInvAt (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) a,
      ∀ j₂ ∈ longInvAt (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) a,
      ∀ (h₁ : j₁ ∈ H₁) (h₂ : j₂ ∈ H₁), D.ρ i₀ ⟨j₁, h₁⟩ * D.ρ i₀ ⟨j₂, h₂⟩ ∈ R := by
    intro j₁ hj₁ j₂ hj₂ h₁ h₂
    obtain ⟨s₁, hs₁, hs₁v, hs₁j⟩ := (hS.mem_longInvAt_centralizerImage_iff hV2 h3 j₁).mp hj₁
    obtain ⟨s₂, hs₂, hs₂v, hs₂j⟩ := (hS.mem_longInvAt_centralizerImage_iff hV2 h3 j₂).mp hj₂
    have hb₁ := hC.smul_smul_eq_inv_smul (mul_self_eq_one_of_mem_longInv hj₁.1) hj₁.2
      (huniq _ hj₁) (inv_mem hp₀)
    have hb₂ := hC.smul_smul_eq_inv_smul (mul_self_eq_one_of_mem_longInv hj₂.1) hj₂.2
      (huniq _ hj₂) hp₀
    have hjjb : (j₁ * j₂) • b = b := by rw [mul_smul, ← hp₀a, hb₂, hb₁, inv_inv]
    have hssβ : (s₁ * s₂) • β = β := by
      have h := congrArg Subtype.val hjjb
      change ((j₁ : Equiv.Perm (fixSet Ω (Subgroup.zpowers v)))
        ((j₂ : Equiv.Perm (fixSet Ω (Subgroup.zpowers v))) b) : Ω) = β at h
      rw [hs₁j, hs₂j] at h
      rwa [mul_smul]
    have hssv : Commute (s₁ * s₂) v :=
      (mem_centralizer_zpowers_iff_commute.mp hs₁v).mul_left
        (mem_centralizer_zpowers_iff_commute.mp hs₂v)
    have hssW : s₁ * s₂ ∈ W := Subgroup.mem_inf.mpr ⟨mem_centralizer_zpowers_iff_commute.mpr hssv,
      Subgroup.mem_inf.mpr ⟨mem_stabilizer_iff.mpr (by rw [mul_smul, hs₂.2, hs₁.2]),
        mem_stabilizer_iff.mpr hssβ⟩⟩
    have hjj : j₁ * j₂ =
        typeLHom (Ω := Ω) v ⟨s₁ * s₂, mem_centralizer_zpowers_iff_commute.mpr hssv⟩ :=
      Subtype.ext (Equiv.ext fun ω => Subtype.ext (by
        change ((j₁ : Equiv.Perm (fixSet Ω (Subgroup.zpowers v)))
          ((j₂ : Equiv.Perm (fixSet Ω (Subgroup.zpowers v))) ω) : Ω) = (s₁ * s₂) • (ω : Ω)
        rw [hs₁j, hs₂j, mul_smul]))
    refine ⟨⟨j₁, h₁⟩ * ⟨j₂, h₂⟩, ⟨⟨s₁ * s₂, mem_centralizer_zpowers_iff_commute.mpr hssv⟩, hssW,
      hjj.symm⟩, map_mul _ _ _⟩
  have hclos : alternatingGroup (D.Ψc i₀) ⊓ stabilizer (Equiv.Perm (D.Ψc i₀)) B₁ ≤ R := by
    rw [← closure_mul_longInvAt_perm_eq (D.odd_card_Ψc i₀) hA.2 B₁, Subgroup.closure_le]
    rintro _ ⟨π₁, hπ₁, π₂, hπ₂, rfl⟩
    obtain ⟨j₁, hj₁, hρ₁⟩ := hreal π₁ hπ₁
    obtain ⟨j₂, hj₂, hρ₂⟩ := hreal π₂ hπ₂
    rw [← hρ₁, ← hρ₂]
    exact hprod j₁ hj₁ j₂ hj₂ _ _
  have : Group.IsSolvable
      ↥(alternatingGroup (D.Ψc i₀) ⊓ stabilizer (Equiv.Perm (D.Ψc i₀)) B₁) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hclos)
  have h6 : 6 ≤ Fintype.card (D.Ψc i₀) := by have := hA.2; omega
  have := isSimpleGroup_alternatingGroup_inf_stabilizer h6 B₁
  have := isPerfect_alternatingGroup_inf_stabilizer h6 B₁
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥(alternatingGroup (D.Ψc i₀) ⊓
    stabilizer (Equiv.Perm (D.Ψc i₀)) B₁))).ne Group.IsPerfect.commutator_eq_top

theorem isPretransitive_pPrimeCore (hS : Sec4Setting G Ω) :
    IsPretransitive (CFSG.pPrimeCore 2 (typeLSection G Ω v)) (fixSet Ω (Subgroup.zpowers v)) := by
  by_contra hQ
  obtain ⟨D⟩ := hS.holtData_typeLSection hC.isTypeL
  have hK := hS.star_typeLSection hC.isTypeL
  obtain ⟨i₀⟩ : Nonempty D.ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hQ (hK.isPretransitive_jOddCore_iff.mp (D.isEmpty_ι_iff.mp h))
  rcases D.factor i₀ with hA | hSE
  · exact hC.false_of_alternating hS D i₀ hA
  · exact hC.false_of_isNaturalSE hS D i₀ hSE

theorem fixedBy_eq_of_commute (hS : Sec4Setting G Ω) {u₁ u₂ : G} (hu₁v : Commute u₁ v)
    (hu₂v : Commute u₂ v) (hc : Commute u₁ u₂) (hu₁ : IsConj v u₁) (hu₂2 : u₂ * u₂ = 1)
    (h12 : fixedBy Ω u₁ = fixedBy Ω u₂) (h13 : fixedBy Ω u₁ = fixedBy Ω (u₁ * u₂)) :
    fixedBy Ω u₁ = fixedBy Ω v := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hC.isPretransitive_pPrimeCore hS
  have hu₁2 := hC.mul_self_eq_one_of_isConj hu₁
  set Φ := fixSet Ω (Subgroup.zpowers v) with hΦ
  have hΦv : (Φ : Set Ω) = fixedBy Ω v := fixSet_zpowers v
  have hcard := ncard_fixedBy_of_isConj (Ω := Ω) hu₁
  suffices hsub : ∀ ω : Φ, u₁ • (ω : Ω) = ω by
    refine (Set.eq_of_subset_of_ncard_le (fun ω hω => ?_) hcard.le (Set.toFinite _)).symm
    rw [← hΦv] at hω
    exact hsub ⟨ω, hω⟩
  have hfix : ∀ (g : G) (hg : Commute g v) (ω : Φ),
      typeLElt (Ω := Ω) hg • ω = ω ↔ g • (ω : Ω) = ω := fun g hg ω =>
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have h2 : ∀ (g : G) (hg : Commute g v), g * g = 1 → typeLElt (Ω := Ω) hg * typeLElt hg = 1 :=
    fun g hg hg2 => by
      rw [typeLElt_mul]
      exact Subtype.ext (Equiv.ext fun ω => Subtype.ext (by
        change (g * g) • (ω : Ω) = ω; rw [hg2, one_smul]))
  by_cases h1 : typeLElt (Ω := Ω) hu₁v = 1
  · exact fun ω => by have := (hfix u₁ hu₁v ω).mp (by rw [h1, one_smul]); exact this
  by_cases h2' : typeLElt (Ω := Ω) hu₂v = 1
  · intro ω
    have h := (hfix u₂ hu₂v ω).mp (by rw [h2', one_smul])
    have : (ω : Ω) ∈ fixedBy Ω u₂ := h
    rw [← h12] at this
    exact this
  by_cases h3 : typeLElt (Ω := Ω) hu₁v = typeLElt (Ω := Ω) hu₂v
  · intro ω
    have h12' : typeLElt (Ω := Ω) hu₁v * typeLElt (Ω := Ω) hu₂v = 1 := by
      rw [← h3]; exact h2 u₁ hu₁v hu₁2
    rw [typeLElt_mul] at h12'
    have h := (hfix _ _ ω).mp (by rw [h12', one_smul])
    have : (ω : Ω) ∈ fixedBy Ω (u₁ * u₂) := h
    rw [← h13] at this
    exact this
  have hord : ∀ (g : G) (hg : Commute g v), g * g = 1 → typeLElt (Ω := Ω) hg ≠ 1 →
      orderOf (typeLElt (Ω := Ω) hg) = 2 := fun g hg hg2 hne =>
    orderOf_eq_prime (by rw [sq]; exact h2 g hg hg2) hne
  have hcomm : Commute (typeLElt (Ω := Ω) hu₁v) (typeLElt (Ω := Ω) hu₂v) := by
    rw [Commute, SemiconjBy, typeLElt_mul, typeLElt_mul]
    exact Subtype.ext (Equiv.ext fun ω => Subtype.ext (by
      change (u₁ * u₂) • (ω : Ω) = (u₂ * u₁) • (ω : Ω); rw [hc.eq]))
  have hBW := card_fixedBy_mul_card_fixedBy_mul_card_fixedBy (Ω := Φ) (hord u₁ hu₁v hu₁2 h1)
    (hord u₂ hu₂v hu₂2 h2') hcomm h3
  set I := fixedBy Φ (typeLElt (Ω := Ω) hu₁v) with hI
  have hI2 : fixedBy Φ (typeLElt (Ω := Ω) hu₂v) = I := Set.ext fun ω => by
    rw [hI, mem_fixedBy, mem_fixedBy, hfix, hfix]
    change (ω : Ω) ∈ fixedBy Ω u₂ ↔ (ω : Ω) ∈ fixedBy Ω u₁
    rw [h12]
  have hI3 : fixedBy Φ (typeLElt (Ω := Ω) hu₁v * typeLElt (Ω := Ω) hu₂v) = I :=
    Set.ext fun ω => by
    rw [hI, typeLElt_mul, mem_fixedBy, mem_fixedBy, hfix, hfix]
    change (ω : Ω) ∈ fixedBy Ω (u₁ * u₂) ↔ (ω : Ω) ∈ fixedBy Ω u₁
    rw [h13]
  rw [hI2, hI3, Set.inter_self] at hBW
  have : Nonempty Φ := ⟨⟨α, hC.α_mem⟩⟩
  obtain ⟨ω₀, hω₀, -⟩ := exists_common_fixed_of_commute Φ (hord u₁ hu₁v hu₁2 h1)
    (hord u₂ hu₂v hu₂2 h2') hcomm h3
  have hIpos : 0 < I.ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨ω₀, hω₀⟩
  have hIeq : I.ncard = Nat.card Φ := by
    have h : I.ncard * I.ncard * I.ncard = Nat.card Φ * I.ncard * I.ncard := by
      rw [hBW]; ring
    exact Nat.eq_of_mul_eq_mul_right hIpos (Nat.eq_of_mul_eq_mul_right hIpos h)
  have hIu : I = Set.univ := Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
    (by rw [Set.ncard_univ, hIeq]) (Set.toFinite _)
  intro ω
  have : ω ∈ I := hIu ▸ Set.mem_univ ω
  exact (hfix u₁ hu₁v ω).mp this

theorem smul_eq_of_mem_caseBRad (hS : Sec4Setting G Ω) {y : G} (hyv : Commute y v)
    (hy2 : y * y = 1) (hyY : y ∈ caseBRad G Ω α β ⟨γ, hC.mem_holtDelta⟩) {ω : Ω}
    (hω : v • ω = ω) : y • ω = ω := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hC.isPretransitive_pPrimeCore hS
  set Φ := fixSet Ω (Subgroup.zpowers v) with hΦ
  have hωΦ : ω ∈ Φ := by rw [hΦ, fixSet_zpowers]; exact hω
  obtain ⟨hyP, hyα, hyβ, hyZ⟩ := mem_caseBRad.mp hyY
  have hyγ : y • γ = γ := congrArg Subtype.val (apply_eq_of_mem_seRadical hyZ.1)
  obtain ⟨x, hxv, hxy, hx2, hxα, hxΔ, hxuniq⟩ := hC.exists_x_commute hS hyv hy2 hyY
  have hfix : ∀ (g : G) (hg : Commute g v) (ω : Φ),
      typeLElt (Ω := Ω) hg • ω = ω ↔ g • (ω : Ω) = ω := fun g hg ω =>
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have h2 : ∀ (g : G) (hg : Commute g v), g * g = 1 → typeLElt (Ω := Ω) hg * typeLElt hg = 1 :=
    fun g hg hg2 => by
      rw [typeLElt_mul]
      exact Subtype.ext (Equiv.ext fun ω => Subtype.ext (by
        change (g * g) • (ω : Ω) = ω; rw [hg2, one_smul]))
  by_cases hy1 : typeLElt (Ω := Ω) hyv = 1
  · exact (hfix y hyv ⟨ω, hωΦ⟩).mp (by rw [hy1, one_smul])
  have hxP : x ∈ stabilizer G ({α, β} : Set Ω) := mem_stabilizer_pair_of_orderOf_eq_two
    (orderOf_eq_prime (by rw [sq, hx2]) fun h => hC.ne (by rw [h, one_smul] at hxα; exact hxα))
    hxα
  have hxyP : x * y ∈ stabilizer G ({α, β} : Set Ω) := mul_mem hxP hyP
  have hx1 : twoPointHom G Ω α β ⟨x, hxP⟩ = 1 := Equiv.ext fun δ => Subtype.ext (hxΔ δ δ.2)
  have hxyΔ : twoPointHom G Ω α β ⟨x * y, hxyP⟩ = twoPointHom G Ω α β ⟨y, hyP⟩ := by
    rw [show (⟨x * y, hxyP⟩ : stabilizer G ({α, β} : Set Ω)) = ⟨x, hxP⟩ * ⟨y, hyP⟩ from rfl,
      map_mul, hx1, one_mul]
  have hŷ1 : twoPointHom G Ω α β ⟨y, hyP⟩ ≠ 1 := fun h => hy1 (by
    have hy1' := hC.eq_one_of_twoPointHom_eq_one hyP hyα hyβ hy2 h
    exact Subtype.ext (Equiv.ext fun ω => Subtype.ext (by
      change y • (ω : Ω) = ω; rw [hy1', one_smul])))
  obtain ⟨n, ⟨k, hk⟩, hxyn⟩ := hC.exists_odd_pow_mem_longInv hS hxyP
    (by rw [mul_smul, hyα, hxα]) (hxyΔ ▸ hyZ) (hxyΔ ▸ hŷ1)
  have hxy2 : x * y * (x * y) = 1 := by
    rw [show x * y * (x * y) = x * x * (y * y) by rw [mul_assoc, ← mul_assoc y, ← hxy.eq]; group,
      hx2, hy2, one_mul]
  have hxyJ : x * y ∈ longInv G Ω := by
    have : (x * y) ^ n = x * y := by
      rw [hk, pow_succ, pow_mul, sq, hxy2, one_pow, one_mul]
    rw [← this]; exact hxyn.1
  have hord : ∀ (g : G) (hg : Commute g v), g * g = 1 → typeLElt (Ω := Ω) hg ≠ 1 →
      orderOf (typeLElt (Ω := Ω) hg) = 2 := fun g hg hg2 hne =>
    orderOf_eq_prime (by rw [sq]; exact h2 g hg hg2) hne
  have hxa : typeLElt (Ω := Ω) hxv • (⟨α, hC.α_mem⟩ : Φ) = ⟨β, hC.β_mem⟩ := Subtype.ext hxα
  have hx1' : typeLElt (Ω := Ω) hxv ≠ 1 := fun h => hC.ne (by
    have := hxa; rw [h, one_smul] at this; exact congrArg Subtype.val this)
  have hne : typeLElt (Ω := Ω) hxv ≠ typeLElt (Ω := Ω) hyv := fun h => hC.ne (by
    have := hxa; rw [h] at this
    have h' := congrArg Subtype.val this
    change y • α = β at h'
    rw [hyα] at h'; exact h')
  have hcomm : Commute (typeLElt (Ω := Ω) hxv) (typeLElt (Ω := Ω) hyv) := by
    rw [Commute, SemiconjBy, typeLElt_mul, typeLElt_mul]
    exact Subtype.ext (Equiv.ext fun ω => Subtype.ext (by
      change (x * y) • (ω : Ω) = (y * x) • (ω : Ω); rw [hxy.eq]))
  have hBW := card_fixedBy_mul_card_fixedBy_mul_card_fixedBy (Ω := Φ) (hord x hxv hx2 hx1')
    (hord y hyv hy2 hy1) hcomm hne
  have hc : ∀ ω' : Φ, typeLElt (Ω := Ω) hxv • ω' = ω' ↔ ω' = ⟨γ, hC.γ_mem⟩ := fun ω' =>
    ⟨fun h => Subtype.ext (hxuniq _ ((hfix x hxv ω').mp h) (ω'.2 v (Subgroup.mem_zpowers v))),
      fun h => h ▸ Subtype.ext (hxΔ γ hC.mem_holtDelta)⟩
  have hcxy : ∀ ω' : Φ, (typeLElt (Ω := Ω) hxv * typeLElt (Ω := Ω) hyv) • ω' = ω' ↔
      ω' = ⟨γ, hC.γ_mem⟩ := fun ω' => by
    rw [typeLElt_mul, hfix]
    obtain ⟨ω₀, -, hu⟩ := hxyJ.2
    have hγf : (x * y) • γ = γ := by rw [mul_smul, hyγ, hxΔ γ hC.mem_holtDelta]
    exact ⟨fun h => Subtype.ext ((hu _ h).trans (hu γ hγf).symm), fun h => h ▸ hγf⟩
  have hFx : fixedBy Φ (typeLElt (Ω := Ω) hxv) = {⟨γ, hC.γ_mem⟩} := Set.ext fun ω' => hc ω'
  have hFxy : fixedBy Φ (typeLElt (Ω := Ω) hxv * typeLElt (Ω := Ω) hyv) = {⟨γ, hC.γ_mem⟩} :=
    Set.ext fun ω' => hcxy ω'
  have hγy : (⟨γ, hC.γ_mem⟩ : Φ) ∈ fixedBy Φ (typeLElt (Ω := Ω) hyv) :=
    (hfix y hyv _).mpr hyγ
  have hint : fixedBy Φ (typeLElt (Ω := Ω) hxv) ∩ fixedBy Φ (typeLElt (Ω := Ω) hyv) =
      {⟨γ, hC.γ_mem⟩} := by
    rw [hFx, Set.singleton_inter_of_mem hγy]
  rw [hint, hFx, hFxy, Set.ncard_singleton] at hBW
  have hall : fixedBy Φ (typeLElt (Ω := Ω) hyv) = Set.univ :=
    Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (by rw [Set.ncard_univ]; omega)
      (Set.toFinite _)
  have hmem : (⟨ω, hωΦ⟩ : Φ) ∈ fixedBy Φ (typeLElt (Ω := Ω) hyv) := by
    rw [hall]; exact Set.mem_univ _
  exact (hfix y hyv ⟨ω, hωΦ⟩).mp hmem

end Prop46CaseB

end Alternating

end CFSG.Holt.H78

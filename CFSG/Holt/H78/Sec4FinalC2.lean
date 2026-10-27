module

public import CFSG.Holt.H78.Sec4FinalC

public section


namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open
open CFSG.GH74.Uniqueness.Bender (rootCenter)
open scoped Pointwise

namespace FinalC

section OddCore

variable {G : Type} [Group G] [Finite G]

theorem odd_orderOf_of_mem_oddCoreOf {B : Subgroup G} {g : G} (hg : g ∈ oddCoreOf B) :
    Odd (orderOf g) := by
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := B))
  rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
  exact hc.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hb)

theorem eq_one_of_mem_oddCoreOf {B : Subgroup G} {g : G} (hg : g ∈ oddCoreOf B) {k : ℕ}
    (hk : g ^ 2 ^ k = 1) : g = 1 := by
  have h1 := orderOf_dvd_of_pow_eq_one hk
  have h2 := (Nat.coprime_two_right.mpr (odd_orderOf_of_mem_oddCoreOf hg)).pow_right k
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h2 h1)

omit [Finite G] in
theorem conj_mem_oddCoreOf_of_mem {B : Subgroup G} {b q : G} (hb : b ∈ B)
    (hq : q ∈ oddCoreOf B) : b * q * b⁻¹ ∈ oddCoreOf B := by
  obtain ⟨q₀, hq₀, rfl⟩ := Subgroup.mem_map.mp hq
  have := (CFSG.pPrimeCore_normal (p := 2) (G := B)).conj_mem q₀ hq₀ ⟨b, hb⟩
  exact ⟨_, this, rfl⟩

theorem le_oddCoreOf_of_odd {B N : Subgroup G} (hNB : N ≤ B)
    (hnorm : ∀ b ∈ B, ∀ n ∈ N, b * n * b⁻¹ ∈ N) (hodd : ∀ n ∈ N, Odd (orderOf n)) :
    N ≤ oddCoreOf B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : (N.subgroupOf B).Normal := ⟨fun n hn b => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm b b.2 n hn⟩
  have hcop : Nat.Coprime 2 (Nat.card (N.subgroupOf B)) := by
    rw [Nat.coprime_two_left]
    by_contra h
    rw [Nat.not_odd_iff_even] at h
    obtain ⟨n, hn⟩ := exists_prime_orderOf_dvd_card' (G := N.subgroupOf B) 2
      (even_iff_two_dvd.mp h)
    have h1 := hodd ((n : B) : G) (Subgroup.mem_subgroupOf.mp n.2)
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hn] at h1
    exact Nat.not_odd_iff_even.mpr even_two h1
  intro n hn
  have hle : N.subgroupOf B ≤ CFSG.pPrimeCore 2 B :=
    le_sSup (show N.subgroupOf B ∈ {K : Subgroup B | K.Normal ∧ Nat.Coprime 2 (Nat.card K)} from
      ⟨hK, hcop⟩)
  exact ⟨⟨n, hNB hn⟩, hle (Subgroup.mem_subgroupOf.mpr hn), rfl⟩

theorem conj_mem_oddCoreOf_of_normalizes {B : Subgroup G} {g : G}
    (hg : ∀ b, b ∈ B ↔ g * b * g⁻¹ ∈ B) {q : G} (hq : q ∈ oddCoreOf B) :
    g * q * g⁻¹ ∈ oddCoreOf B := by
  have hle : (oddCoreOf B).map (MulAut.conj g).toMonoidHom ≤ oddCoreOf B := by
    refine le_oddCoreOf_of_odd ?_ ?_ ?_
    · rintro _ ⟨q', hq', rfl⟩
      exact (hg q').mp (Subgroup.map_subtype_le _ hq')
    · rintro b hb _ ⟨q', hq', rfl⟩
      have hb' : g⁻¹ * b * g ∈ B := (hg _).mpr (by simpa [mul_assoc] using hb)
      refine ⟨(g⁻¹ * b * g) * q' * (g⁻¹ * b * g)⁻¹, conj_mem_oddCoreOf_of_mem hb' hq', ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · rintro _ ⟨q', hq', rfl⟩
      rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
      exact odd_orderOf_of_mem_oddCoreOf hq'
  exact hle ⟨q, hq, rfl⟩

end OddCore

section Involutions

variable {G : Type} [Group G]

theorem exists_conj_eq_of_odd_orderOf_mul {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hodd : Odd (orderOf (a * b))) : ∃ k : G, k * a * k⁻¹ = b := by
  obtain ⟨m, hm⟩ := hodd
  set c := a * b with hc_def
  have hc : c ^ (2 * m + 1) = 1 := hm ▸ pow_orderOf_eq_one c
  have h1 : a * c ^ (m + 1) * a⁻¹ = (c ^ (m + 1))⁻¹ := conj_pow_mul_eq_inv ha hb (m + 1)
  have h2 : a * c ^ (m + 1) = (c ^ (m + 1))⁻¹ * a := by
    calc a * c ^ (m + 1) = (a * c ^ (m + 1) * a⁻¹) * a := by group
      _ = (c ^ (m + 1))⁻¹ * a := by rw [h1]
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  refine ⟨(c ^ (m + 1))⁻¹, ?_⟩
  calc (c ^ (m + 1))⁻¹ * a * (c ^ (m + 1))⁻¹⁻¹ = (c ^ (m + 1))⁻¹ * (a * c ^ (m + 1)) := by
        group
    _ = (c ^ (m + 1) * c ^ (m + 1))⁻¹ * a := by rw [h2, mul_inv_rev, mul_assoc]
    _ = c⁻¹ * a := by
        rw [← pow_add, show m + 1 + (m + 1) = 2 * m + 1 + 1 by ring, pow_succ, hc, one_mul]
    _ = b := by rw [hc_def, mul_inv_rev, inv_mul_cancel_right, hbinv]

theorem commute_of_forall_mul_self_eq_one {V : Subgroup G} (hV : ∀ u ∈ V, u * u = 1) {a b : G}
    (ha : a ∈ V) (hb : b ∈ V) : Commute a b := by
  have hab := hV _ (mul_mem ha hb)
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hV a ha)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hV b hb)
  show a * b = b * a
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
    _ = b * a := by rw [mul_inv_rev, ha', hb']

end Involutions

end FinalC

namespace FinConfig

section Splitting

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

structure Splitting (hS : Sec4Setting G Ω) where
  Mc : Subgroup G
  Mc_le : Mc ≤ Subgroup.centralizer (C.Y : Set G)
  centralizer_inf_oddCore_le : Subgroup.centralizer (C.Y : Set G) ⊓
    oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) ≤ Mc
  piM_mem : ∀ g (hg : g ∈ Mc), C.piM hS ⟨g, C.centralizer_Y_le hS (Mc_le hg)⟩ ∈ C.Dv.M C.i
  exists_piM : ∀ m ∈ C.Dv.M C.i, ∃ g, ∃ hg : g ∈ Mc,
    C.piM hS ⟨g, C.centralizer_Y_le hS (Mc_le hg)⟩ = m
  mem_oddCore : ∀ g ∈ Mc, g ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) →
    g ∈ oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)))
  exists_mul_mem : ∀ g (hg : g ∈ Subgroup.centralizer (C.Y : Set G)),
    C.piM hS ⟨g, C.centralizer_Y_le hS hg⟩ ∈ C.Dv.M C.i → ∃ z ∈ C.Z, g * z ∈ Mc
  conj_mem : ∀ g ∈ Subgroup.centralizer (C.Y : Set G), ∀ c ∈ Mc, g * c * g⁻¹ ∈ Mc
  conj_mem_of_normalizes : ∀ h : G, (∀ y ∈ C.Y, h * y * h⁻¹ ∈ C.Y) → ∀ c ∈ Mc,
    h * c * h⁻¹ ∈ Mc
  x_mem : C.x ∈ Mc
  U : Subgroup G
  V : Subgroup G
  U_le : U ≤ Mc
  V_le : V ≤ U
  U_le_stabilizer : U ≤ stabilizer G (C.γ : Ω)
  sylow : fusionIsSylowIn 2 U (Mc ⊓ stabilizer G (C.γ : Ω))
  x_mem_V : C.x ∈ V
  mem_V_iff : ∀ u ∈ U, u ∈ V ↔ u * u = 1
  piM_eq_one : ∀ u (hu : u ∈ U),
    C.piM hS ⟨u, C.centralizer_Y_le hS (Mc_le (U_le hu))⟩ = 1 → u = 1
  exists_piM_U : ∀ m ∈ seRadical (C.Dv.M C.i) (C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i), ∃ u,
    ∃ hu : u ∈ U, C.piM hS ⟨u, C.centralizer_Y_le hS (Mc_le (U_le hu))⟩ = m
  piM_U_mem : ∀ u (hu : u ∈ U), C.piM hS ⟨u, C.centralizer_Y_le hS (Mc_le (U_le hu))⟩ ∈
    seRadical (C.Dv.M C.i) (C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i)
  exists_lift : ∀ m ∈ C.Dv.M C.i,
    m (C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i) = C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i →
      ∃ h, ∃ hh : h ∈ Mc, h ∈ stabilizer G (C.γ : Ω) ∧ (∀ u ∈ U, h * u * h⁻¹ ∈ U) ∧
        C.piM hS ⟨h, C.centralizer_Y_le hS (Mc_le hh)⟩ = m
  exists_conj_x : ∀ r ∈ V, r ≠ 1 → ∃ h ∈ Mc ⊓ stabilizer G (C.γ : Ω), h * C.x * h⁻¹ = r
  mul_mem_longInv : ∀ r ∈ V, ∀ z ∈ C.Z, r ≠ 1 → z ≠ 1 → r * z ∈ longInv G Ω
  exists_conj_x_mul : ∀ c ∈ Mc,
    ∀ q ∈ oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))),
      orderOf (c * q) = 2 → ∃ h : G, h * C.x * h⁻¹ = c * q

theorem Splitting.nonempty (hS : Sec4Setting G Ω)
    (hF67 : ∃ Mc : Subgroup G, ∃ hMcY : Mc ≤ Subgroup.centralizer (C.Y : Set G),
      Subgroup.centralizer (C.Y : Set G) ⊓
          oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) ≤ Mc ∧
      (∀ g (hg : g ∈ Mc), C.piM hS ⟨g, C.centralizer_Y_le hS (hMcY hg)⟩ ∈ C.Dv.M C.i) ∧
      (∀ m ∈ C.Dv.M C.i, ∃ g, ∃ hg : g ∈ Mc,
        C.piM hS ⟨g, C.centralizer_Y_le hS (hMcY hg)⟩ = m) ∧
      (∀ g ∈ Mc, g ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) →
        g ∈ oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)))) ∧
      (∀ g (hg : g ∈ Subgroup.centralizer (C.Y : Set G)),
        C.piM hS ⟨g, C.centralizer_Y_le hS hg⟩ ∈ C.Dv.M C.i → ∃ z ∈ C.Z, g * z ∈ Mc) ∧
      (∀ g ∈ Subgroup.centralizer (C.Y : Set G), ∀ c ∈ Mc, g * c * g⁻¹ ∈ Mc) ∧
      (∀ h : G, (∀ y ∈ C.Y, h * y * h⁻¹ ∈ C.Y) → ∀ c ∈ Mc, h * c * h⁻¹ ∈ Mc) ∧
    C.x ∈ Mc ∧
    ∃ U V : Subgroup G, ∃ hUMc : U ≤ Mc,
      V ≤ U ∧ U ≤ stabilizer G (C.γ : Ω) ∧
      fusionIsSylowIn 2 U (Mc ⊓ stabilizer G (C.γ : Ω)) ∧ C.x ∈ V ∧
      (∀ u ∈ U, u ∈ V ↔ u * u = 1) ∧
      (∀ u (hu : u ∈ U), C.piM hS ⟨u, C.centralizer_Y_le hS (hMcY (hUMc hu))⟩ = 1 → u = 1) ∧
      (∀ m ∈ seRadical (C.Dv.M C.i) (C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i), ∃ u, ∃ hu : u ∈ U,
        C.piM hS ⟨u, C.centralizer_Y_le hS (hMcY (hUMc hu))⟩ = m) ∧
      (∀ u (hu : u ∈ U), C.piM hS ⟨u, C.centralizer_Y_le hS (hMcY (hUMc hu))⟩ ∈
        seRadical (C.Dv.M C.i) (C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i)) ∧
      (∀ m ∈ C.Dv.M C.i, m (C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i) = C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i →
        ∃ h, ∃ hh : h ∈ Mc, h ∈ stabilizer G (C.γ : Ω) ∧ (∀ u ∈ U, h * u * h⁻¹ ∈ U) ∧
          C.piM hS ⟨h, C.centralizer_Y_le hS (hMcY hh)⟩ = m) ∧
      (∀ r ∈ V, r ≠ 1 → ∃ h ∈ Mc ⊓ stabilizer G (C.γ : Ω), h * C.x * h⁻¹ = r) ∧
      (∀ r ∈ V, ∀ z ∈ C.Z, r ≠ 1 → z ≠ 1 → r * z ∈ longInv G Ω) ∧
      (∀ c ∈ Mc, ∀ q ∈ oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))),
        orderOf (c * q) = 2 → ∃ h : G, h * C.x * h⁻¹ = c * q)) :
    Nonempty (C.Splitting hS) := by
  obtain ⟨Mc, hMcY, h1, h2, h3, h4, h5, h6, h7, hx, U, V, hUMc, h8, h9, h10, h11, h12, h13,
    h14, h15, h16, h17, h18, h19⟩ := hF67
  exact ⟨⟨Mc, hMcY, h1, h2, h3, h4, h5, h6, h7, hx, U, V, hUMc, h8, h9, h10, h11, h12, h13,
    h14, h15, h16, h17, h18, h19⟩⟩

end Splitting

end FinConfig

namespace FinConfig

section NormalizesP

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω] {v : G}

theorem conj_mem_fixingSubgroup_iff {c : G}
    (hc : c ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) (b : G) :
    b ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) ↔
      c * b * c⁻¹ ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) := by
  have hΦ : ∀ {d : G}, d ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) →
      ∀ ω ∈ fixSet Ω (Subgroup.zpowers v), d • ω ∈ fixSet Ω (Subgroup.zpowers v) :=
    fun {d} hd ω hω => by
      rw [← smul_fixSet_zpowers_of_mem_centralizer hd]
      exact Set.smul_mem_smul_set hω
  simp only [mem_fixingSubgroup_iff]
  constructor
  · intro h ω hω
    rw [mul_smul, mul_smul, h _ (hΦ (inv_mem hc) ω hω), smul_inv_smul]
  · intro h ω hω
    have h1 := h (c • ω) (hΦ hc ω hω)
    rwa [mul_smul, mul_smul, inv_smul_smul, smul_left_cancel_iff] at h1

end NormalizesP

section Lemma41

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

omit [FaithfulSMul G Ω] in
theorem mem_oddCoreOf_of_psi_eq_one (hS : Sec4Setting G Ω) {g : G}
    (hgP : g ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)))
    (hψ : C.psi ⟨g, stabilizer_inf_le_stabilizer_pair α β
      (C.fixingSubgroup_le_stabilizer_inf hgP)⟩ = 1) :
    g ∈ oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) := by
  set P := fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))
  have hP : ∀ {b : G}, b ∈ P → b ∈ stabilizer G ({α, β} : Set Ω) := fun hb =>
    stabilizer_inf_le_stabilizer_pair α β (C.fixingSubgroup_le_stabilizer_inf hb)
  have hK : P ⊓ C.psiPre ⊥ ≤ oddCoreOf P := by
    refine FinalC.le_oddCoreOf_of_odd inf_le_left (fun b hb n hn => ?_) fun n hn => ?_
    · obtain ⟨hnP, hnK⟩ := Subgroup.mem_inf.mp hn
      obtain ⟨hnp, hnψ⟩ := C.mem_psiPre.mp hnK
      refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hb hnP) (inv_mem hb),
        C.mem_psiPre.mpr ⟨mul_mem (mul_mem (hP hb) hnp) (inv_mem (hP hb)), ?_⟩⟩
      rw [C.psi_mul (mul_mem (hP hb) hnp) (inv_mem (hP hb)), C.psi_mul (hP hb) hnp,
        C.psi_inv (hP hb), Subgroup.mem_bot.mp hnψ, mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    · obtain ⟨hnP, hnK⟩ := Subgroup.mem_inf.mp hn
      obtain ⟨hnp, hnψ⟩ := C.mem_psiPre.mp hnK
      exact C.odd_orderOf_of_psi_eq_one hS (C.fixingSubgroup_le_stabilizer_inf hnP)
        (Subgroup.mem_bot.mp hnψ) fun δ _ hδΦ => (mem_fixingSubgroup_iff G).mp hnP δ hδΦ
  exact hK (Subgroup.mem_inf.mpr ⟨hgP, C.mem_psiPre.mpr ⟨_, Subgroup.mem_bot.mpr hψ⟩⟩)

theorem x_conj_mul_inv_mem_oddCoreOf (hS : Sec4Setting G Ω) {d : G}
    (hd : d ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) :
    C.x⁻¹ * d * C.x * d⁻¹ ∈ oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) := by
  have hxc := C.x_mem_centralizer hS
  have hd' : C.x⁻¹ * d * C.x ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) := by
    have h := (conj_mem_fixingSubgroup_iff (inv_mem hxc) d).mp hd
    rwa [inv_inv] at h
  have hmem : C.x⁻¹ * d * C.x * d⁻¹ ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) :=
    mul_mem hd' (inv_mem hd)
  refine C.mem_oddCoreOf_of_psi_eq_one hS hmem ?_
  have hxp := C.x_mem_stabilizer_pair hS
  have hdp := stabilizer_inf_le_stabilizer_pair α β (C.fixingSubgroup_le_stabilizer_inf hd)
  rw [C.psi_mul (mul_mem (mul_mem (inv_mem hxp) hdp) hxp) (inv_mem hdp),
    C.psi_mul (mul_mem (inv_mem hxp) hdp) hxp, C.psi_mul (inv_mem hxp) hdp, C.psi_inv hxp,
    C.psi_inv hdp, C.psi_x hS, inv_one, one_mul, mul_one, mul_inv_cancel]

end Lemma41

end FinConfig

namespace FinConfig

section Sylow

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

theorem eq_γ_of_mem_fixSet_of_x_smul (hS : Sec4Setting G Ω) {δ : Ω}
    (hδ : δ ∈ fixSet Ω (Subgroup.zpowers v)) (hxδ : C.x • δ = δ) : δ = C.γ := by
  obtain ⟨hM, h2, -, hγ⟩ := C.piM_x hS
  obtain ⟨c, -, hu⟩ := (C.isNaturalSE_Dv C.i).existsUnique_fixed
    (x := ⟨_, hM⟩) (by rw [Subgroup.orderOf_mk]; exact h2)
  have h1 := (C.smul_eq_iff_piM_apply_eq hS ⟨C.x, C.x_mem_centralizer hS⟩ ⟨δ, hδ⟩).mp hxδ
  have h3 := (hu _ h1).trans (hu _ hγ).symm
  have h4 := (C.smul_eq_iff_piM_apply hS 1 ⟨δ, hδ⟩ ⟨C.γ, C.γ_mem⟩).mpr
    (by rw [map_one, Equiv.Perm.one_apply]; exact h3)
  rwa [OneMemClass.coe_one, one_smul] at h4

theorem Y_le_centralizer_v (hS : Sec4Setting G Ω) :
    C.Y ≤ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) := fun _ hy =>
  mem_centralizer_zpowers (C.commute_of_mem_Z hS (C.v_mem_Z hS) hy)

theorem isPGroup_U_sup_Y (hS : Sec4Setting G Ω) (D : C.Splitting hS) :
    IsPGroup 2 ↥(D.U ⊔ C.Y) :=
  D.sylow.2.1.to_sup_of_normal_right' (C.sylow.2.1.to_le C.Y_le_S)
    ((D.U_le.trans D.Mc_le).trans (Subgroup.centralizer_le_normalizer _))

theorem U_sup_Y_le (hS : Sec4Setting G Ω) (D : C.Splitting hS) :
    D.U ⊔ C.Y ≤ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) :=
  sup_le ((D.U_le.trans D.Mc_le).trans (C.centralizer_Y_le hS)) (C.Y_le_centralizer_v hS)

theorem le_stabilizer_γ (hS : Sec4Setting G Ω) (D : C.Splitting hS) {T : Subgroup G}
    (hT : fusionIsSylowIn 2 T
      (Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)))
    (hUT : D.U ⊔ C.Y ≤ T) : T ≤ stabilizer G (C.γ : Ω) := by
  have hTΦ : T ≤ stabilizer G (fixSet Ω (Subgroup.zpowers v)) := fun t ht =>
    mem_stabilizer_iff.mpr (smul_fixSet_zpowers_of_mem_centralizer (hT.1 ht))
  obtain ⟨δ, hδΦ, hδT⟩ := exists_mem_fixSet_of_le_stabilizer hT.2.1
    (hS.star.odd_card_fixSet C.isPGroup_zpowers) hTΦ
  have hxT : C.x ∈ T := hUT (Subgroup.mem_sup_left (D.V_le D.x_mem_V))
  have hδγ := C.eq_γ_of_mem_fixSet_of_x_smul hS hδΦ (hδT _ hxT)
  intro t ht
  exact mem_stabilizer_iff.mpr (hδγ ▸ hδT t ht)

theorem Z_le_inf (hS : Sec4Setting G Ω) (D : C.Splitting hS) {T : Subgroup G}
    (hUT : D.U ⊔ C.Y ≤ T) : C.Z ≤ T ⊓ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) :=
  le_inf (C.Z_le_Y.trans (le_sup_right.trans hUT)) (C.Z_le_fixingSubgroup hS)

theorem commute_of_mem_V (hS : Sec4Setting G Ω) (D : C.Splitting hS) {T : Subgroup G}
    (hT : fusionIsSylowIn 2 T
      (Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)))
    (hUT : D.U ⊔ C.Y ≤ T) {r : G} (hr : r ∈ D.V) {y : G}
    (hy : y ∈ T ⊓ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) : r * y = y * r := by
  rcases eq_or_ne r 1 with rfl | hr1
  · rw [one_mul, mul_one]
  obtain ⟨h, hh, rfl⟩ := D.exists_conj_x r hr hr1
  have hhC := (D.Mc_le.trans (C.centralizer_Y_le hS)) (Subgroup.mem_inf.mp hh).1
  set P := fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))
  set X' := (T ⊓ P).map (MulAut.conj h⁻¹).toMonoidHom
  have hX'2 : IsPGroup 2 X' := (hT.2.1.to_inf_left).map _
  have hrT : h * C.x * h⁻¹ ∈ T := hUT (Subgroup.mem_sup_left (D.V_le hr))
  have hrC := hT.1 hrT
  have hX'P : X' ≤ P := by
    rintro _ ⟨y', hy', rfl⟩
    have h1 := (conj_mem_fixingSubgroup_iff (inv_mem hhC) y').mp (Subgroup.mem_inf.mp hy').2
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h1
  have hnorm : ∀ g ∈ X', C.x * g * C.x⁻¹ ∈ X' := by
    rintro _ ⟨y', hy', rfl⟩
    refine ⟨(h * C.x * h⁻¹) * y' * (h * C.x * h⁻¹)⁻¹, Subgroup.mem_inf.mpr
      ⟨mul_mem (mul_mem hrT (Subgroup.mem_inf.mp hy').1) (inv_mem hrT),
        (conj_mem_fixingSubgroup_iff hrC y').mp (Subgroup.mem_inf.mp hy').2⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hyX' : h⁻¹ * y * h ∈ X' :=
    ⟨y, hy, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
  have hc := C.commute_x_of_le_fixingSubgroup hS hX'2 hX'P hnorm hyX'
  calc h * C.x * h⁻¹ * y = h * (C.x * (h⁻¹ * y * h)) * h⁻¹ := by group
    _ = h * ((h⁻¹ * y * h) * C.x) * h⁻¹ := by rw [hc]
    _ = y * (h * C.x * h⁻¹) := by group

end Sylow

end FinConfig

namespace FinConfig

section Dichotomy

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
include C in
theorem fixingSubgroup_le_pair :
    fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) ≤ stabilizer G ({α, β} : Set Ω) :=
  fun _ hg => stabilizer_inf_le_stabilizer_pair α β (C.fixingSubgroup_le_stabilizer_inf hg)

theorem exists_mem_Z_inv_mul_mem_oddCoreOf (hS : Sec4Setting G Ω) {p : G}
    (hpP : p ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) (hp2 : p * p = 1)
    (hN : C.psi ⟨p, C.fixingSubgroup_le_pair hpP⟩ ∈ C.N) :
    ∃ z ∈ C.Z, z⁻¹ * p ∈ oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) := by
  have hpp := C.fixingSubgroup_le_pair hpP
  have hψ2 : C.psi ⟨p, hpp⟩ * C.psi ⟨p, hpp⟩ = 1 := by
    rw [← C.psi_mul hpp hpp, show (⟨p * p, mul_mem hpp hpp⟩ : stabilizer G ({α, β} : Set Ω)) = 1
      from Subtype.ext hp2, map_one]
  have hpγ : p • (C.γ : Ω) = C.γ := (mem_fixingSubgroup_iff G).mp hpP _ C.γ_mem
  obtain ⟨z, hz, hzψ⟩ := C.exists_mem_Z_of_mem_Zhat hS
    (C.isNaturalSE_N.mem_rootCenter_seRadical hN (C.psi_apply_bγ hpγ) hψ2)
  have hzP := C.Z_le_fixingSubgroup hS hz
  have hzp := C.fixingSubgroup_le_pair hzP
  refine ⟨z, hz, C.mem_oddCoreOf_of_psi_eq_one hS (mul_mem (inv_mem hzP) hpP) ?_⟩
  rw [C.psi_mul (inv_mem hzp) hpp, C.psi_inv hzp, hzψ, inv_mul_cancel]

theorem isConj_x_mul_of_isConj_x_mul (hS : Sec4Setting G Ω) {p₁ p₂ : G}
    (hp₁P : p₁ ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)))
    (hp₂P : p₂ ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)))
    (hp₁2 : p₁ * p₁ = 1) (hp₂2 : p₂ * p₂ = 1)
    (hp₁N : C.psi ⟨p₁, C.fixingSubgroup_le_pair hp₁P⟩ ∉ C.N)
    (hp₂N : C.psi ⟨p₂, C.fixingSubgroup_le_pair hp₂P⟩ ∉ C.N)
    (hc₁ : C.x * p₁ = p₁ * C.x) (hc₂ : C.x * p₂ = p₂ * C.x) (h : IsConj v (C.x * p₁)) :
    IsConj v (C.x * p₂) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) with hP_def
  have hPp : ∀ {g : G}, g ∈ P → g ∈ stabilizer G ({α, β} : Set Ω) := fun hg =>
    C.fixingSubgroup_le_pair hg
  have hsq : ∀ {g : G}, g * g = 1 → g ^ 2 ^ 1 = 1 := fun {g} hg => by rw [pow_one, sq, hg]
  obtain ⟨T₁, hT₁p, hT₁⟩ := exists_fusionIsSylowIn_ge
    (isPGroup_zpowers_of_pow_eq_one (hsq hp₁2)) (Subgroup.zpowers_le.mpr hp₁P)
  obtain ⟨T₂, hT₂p, hT₂⟩ := exists_fusionIsSylowIn_ge
    (isPGroup_zpowers_of_pow_eq_one (hsq hp₂2)) (Subgroup.zpowers_le.mpr hp₂P)
  obtain ⟨c, hcP, hc⟩ := exists_mem_conj_of_fusionIsSylowIn hT₁ hT₂
  have hcp₁T : c * p₁ * c⁻¹ ∈ T₂ := (hc _).mpr (by
    rw [show c⁻¹ * (c * p₁ * c⁻¹) * c = p₁ by group]
    exact hT₁p (Subgroup.mem_zpowers p₁))
  have hp₂T : p₂ ∈ T₂ := hT₂p (Subgroup.mem_zpowers p₂)
  have hcp₁P : c * p₁ * c⁻¹ ∈ P := mul_mem (mul_mem hcP hp₁P) (inv_mem hcP)
  set S₂ : Subgroup (Equiv.Perm C.Psi) :=
    (T₂.subgroupOf (stabilizer G ({α, β} : Set Ω))).map C.psi
  have hS₂2 : IsPGroup 2 S₂ :=
    (hT₂.2.1.comap_of_injective _ (Subgroup.subtype_injective _)).map _
  have hS₂N : S₂ ≤ Subgroup.normalizer (C.N : Set (Equiv.Perm C.Psi)) := by
    rintro _ ⟨g, -, rfl⟩
    exact C.psi_mem_normalizer g
  have hS₂b : ∀ t ∈ S₂, t C.bγ = C.bγ := by
    rintro _ ⟨g, hg, rfl⟩
    exact C.psi_apply_bγ ((mem_fixingSubgroup_iff G).mp (hT₂.1 (Subgroup.mem_subgroupOf.mp hg))
      _ C.γ_mem)
  have hmem : ∀ {y : G} (hy : y ∈ T₂), C.psi ⟨y, hPp (hT₂.1 hy)⟩ ∈ S₂ := fun {y} hy =>
    ⟨⟨y, hPp (hT₂.1 hy)⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  have hψ2 : ∀ {g : G} (hg : g ∈ stabilizer G ({α, β} : Set Ω)), g * g = 1 →
      C.psi ⟨g, hg⟩ * C.psi ⟨g, hg⟩ = 1 := fun hg hg2 => by
    rw [← C.psi_mul hg hg, show (⟨_, mul_mem hg hg⟩ : stabilizer G ({α, β} : Set Ω)) = 1
      from Subtype.ext hg2, map_one]
  have hcp₁2 : c * p₁ * c⁻¹ * (c * p₁ * c⁻¹) = 1 := by
    rw [show c * p₁ * c⁻¹ * (c * p₁ * c⁻¹) = c * (p₁ * p₁) * c⁻¹ by group, hp₁2, mul_one,
      mul_inv_cancel]
  have hψc : C.psi ⟨c * p₁ * c⁻¹, hPp hcp₁P⟩ =
      C.psi ⟨c, hPp hcP⟩ * C.psi ⟨p₁, hPp hp₁P⟩ * (C.psi ⟨c, hPp hcP⟩)⁻¹ := by
    rw [C.psi_mul (mul_mem (hPp hcP) (hPp hp₁P)) (inv_mem (hPp hcP)), C.psi_mul (hPp hcP)
      (hPp hp₁P), C.psi_inv (hPp hcP)]
  have hcp₁N : C.psi ⟨c * p₁ * c⁻¹, hPp hcp₁P⟩ ∉ C.N := fun hN => hp₁N (by
    have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem (C.psi_mem_normalizer ⟨c, hPp hcP⟩))
      _).mp hN
    rwa [hψc, inv_inv, show (C.psi ⟨c, hPp hcP⟩)⁻¹ * (C.psi ⟨c, hPp hcP⟩ *
      C.psi ⟨p₁, hPp hp₁P⟩ * (C.psi ⟨c, hPp hcP⟩)⁻¹) * C.psi ⟨c, hPp hcP⟩ =
      C.psi ⟨p₁, hPp hp₁P⟩ by group] at h1)
  obtain ⟨ρ, hρ, hρe⟩ := C.isNaturalSE_N.exists_conj_eq_of_isPGroup hS₂2 hS₂N hS₂b
    (hmem hcp₁T) (hmem hp₂T) (hψ2 _ hcp₁2) (hψ2 _ hp₂2) hcp₁N hp₂N
  obtain ⟨y₀, hy₀, hy₀ρ⟩ := C.exists_mem_Y_of_mem_Rhat hS hρ
  have hy₀P := C.Y_le_fixingSubgroup hS hy₀
  set d := y₀ * c with hd_def
  have hdP : d ∈ P := mul_mem hy₀P hcP
  have hdp₁P : d * p₁ * d⁻¹ ∈ P := mul_mem (mul_mem hdP hp₁P) (inv_mem hdP)
  have hψd : C.psi ⟨d * p₁ * d⁻¹, hPp hdp₁P⟩ = C.psi ⟨p₂, hPp hp₂P⟩ := by
    have e1 : d * p₁ * d⁻¹ = y₀ * (c * p₁ * c⁻¹) * y₀⁻¹ := by rw [hd_def]; group
    have hy₀p := hPp hy₀P
    rw [show (⟨d * p₁ * d⁻¹, hPp hdp₁P⟩ : stabilizer G ({α, β} : Set Ω)) =
      ⟨y₀ * (c * p₁ * c⁻¹) * y₀⁻¹, e1 ▸ hPp hdp₁P⟩ from Subtype.ext e1,
      C.psi_mul (mul_mem hy₀p (hPp hcp₁P)) (inv_mem hy₀p), C.psi_mul hy₀p (hPp hcp₁P),
      C.psi_inv hy₀p, hρe]
    exact congrArg (fun r => r * C.psi ⟨c * p₁ * c⁻¹, hPp hcp₁P⟩ * r⁻¹) hy₀ρ
  have heQ : p₂⁻¹ * (d * p₁ * d⁻¹) ∈ oddCoreOf P :=
    C.mem_oddCoreOf_of_psi_eq_one hS (mul_mem (inv_mem hp₂P) hdp₁P) (by
      rw [C.psi_mul (inv_mem (hPp hp₂P)) (hPp hdp₁P), C.psi_inv (hPp hp₂P), hψd,
        inv_mul_cancel])
  have hfQ := C.x_conj_mul_inv_mem_oddCoreOf hS hdP
  have hfQ' : p₂⁻¹ * (C.x⁻¹ * d * C.x * d⁻¹) * p₂ ∈ oddCoreOf P := by
    have h1 := FinalC.conj_mem_oddCoreOf_of_mem (inv_mem hp₂P) hfQ
    rwa [inv_inv] at h1
  have hx2 := C.x_mul_self hS
  have ha : C.x * p₂ * (C.x * p₂) = 1 := by
    calc C.x * p₂ * (C.x * p₂) = C.x * (p₂ * C.x) * p₂ := by group
      _ = C.x * (C.x * p₂) * p₂ := by rw [hc₂]
      _ = (C.x * C.x) * (p₂ * p₂) := by group
      _ = 1 := by rw [hx2, hp₂2, mul_one]
  have hb : d * (C.x * p₁) * d⁻¹ * (d * (C.x * p₁) * d⁻¹) = 1 := by
    calc d * (C.x * p₁) * d⁻¹ * (d * (C.x * p₁) * d⁻¹) =
        d * (C.x * (p₁ * C.x) * p₁) * d⁻¹ := by group
      _ = d * (C.x * (C.x * p₁) * p₁) * d⁻¹ := by rw [hc₁]
      _ = d * ((C.x * C.x) * (p₁ * p₁)) * d⁻¹ := by group
      _ = 1 := by rw [hx2, hp₁2, mul_one, mul_one, mul_inv_cancel]
  have hainv : (C.x * p₂)⁻¹ = C.x * p₂ := inv_eq_of_mul_eq_one_right ha
  have hab : C.x * p₂ * (d * (C.x * p₁) * d⁻¹) ∈ oddCoreOf P := by
    rw [← hainv, show (C.x * p₂)⁻¹ * (d * (C.x * p₁) * d⁻¹) =
      p₂⁻¹ * (C.x⁻¹ * d * C.x * d⁻¹) * p₂ * (p₂⁻¹ * (d * p₁ * d⁻¹)) by group]
    exact mul_mem hfQ' heQ
  obtain ⟨k, hk⟩ := FinalC.exists_conj_eq_of_odd_orderOf_mul ha hb
    (FinalC.odd_orderOf_of_mem_oddCoreOf hab)
  have h1 : IsConj v (d * (C.x * p₁) * d⁻¹) := h.trans (isConj_iff.mpr ⟨d, rfl⟩)
  rw [← hk] at h1
  exact h1.trans (isConj_iff.mpr ⟨k⁻¹, by group⟩)

theorem psi_conj_not_mem_N (hS : Sec4Setting G Ω) (D : C.Splitting hS) {T : Subgroup G}
    (hT : fusionIsSylowIn 2 T
      (Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)))
    (hUT : D.U ⊔ C.Y ≤ T) {h : G} (hh : h ∈ D.Mc) {p₀ : G}
    (hp₀ : p₀ ∈ T ⊓ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) (hp₀2 : p₀ * p₀ = 1)
    (hp₀Z : p₀ ∉ C.Z) (hp₁P : h⁻¹ * p₀ * h ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) :
    C.psi ⟨h⁻¹ * p₀ * h, C.fixingSubgroup_le_pair hp₁P⟩ ∉ C.N := by
  intro hN
  have hhC := (D.Mc_le.trans (C.centralizer_Y_le hS)) hh
  have hp₁2 : h⁻¹ * p₀ * h * (h⁻¹ * p₀ * h) = 1 := by
    rw [show h⁻¹ * p₀ * h * (h⁻¹ * p₀ * h) = h⁻¹ * (p₀ * p₀) * h by group, hp₀2, mul_one,
      inv_mul_cancel]
  obtain ⟨z, hz, hzQ⟩ := C.exists_mem_Z_inv_mul_mem_oddCoreOf hS hp₁P hp₁2 hN
  have hq := FinalC.conj_mem_oddCoreOf_of_normalizes (conj_mem_fixingSubgroup_iff hhC) hzQ
  have hzh : z * h = h * z :=
    Subgroup.mem_centralizer_iff.mp (D.Mc_le hh) z (C.Z_le_Y hz)
  have he : h * (z⁻¹ * (h⁻¹ * p₀ * h)) * h⁻¹ = z⁻¹ * p₀ := by
    have hzh' : h * z⁻¹ = z⁻¹ * h := by
      calc h * z⁻¹ = z⁻¹ * (z * h) * z⁻¹ := by group
        _ = z⁻¹ * (h * z) * z⁻¹ := by rw [hzh]
        _ = z⁻¹ * h := by group
    calc h * (z⁻¹ * (h⁻¹ * p₀ * h)) * h⁻¹ = (h * z⁻¹) * h⁻¹ * p₀ := by group
      _ = z⁻¹ * p₀ := by rw [hzh']; group
  rw [he] at hq
  have hzT := (C.Z_le_inf hS D hUT hz)
  obtain ⟨k, hk⟩ := hT.2.1 ⟨z⁻¹ * p₀, mul_mem (inv_mem (Subgroup.mem_inf.mp hzT).1)
    (Subgroup.mem_inf.mp hp₀).1⟩
  have hk' : (z⁻¹ * p₀) ^ 2 ^ k = 1 := by
    simpa only [Subgroup.coe_pow, Subgroup.coe_mk, OneMemClass.coe_one] using
      congrArg Subtype.val hk
  have h1 := FinalC.eq_one_of_mem_oddCoreOf hq hk'
  rw [inv_mul_eq_one] at h1
  exact hp₀Z (h1 ▸ hz)

theorem isConj_mul_of_isConj_mul (hS : Sec4Setting G Ω) (D : C.Splitting hS) {T : Subgroup G}
    (hT : fusionIsSylowIn 2 T
      (Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)))
    (hUT : D.U ⊔ C.Y ≤ T) {r₀ p₀ r p : G} (hr₀ : r₀ ∈ D.V) (hr₀1 : r₀ ≠ 1)
    (hp₀ : p₀ ∈ T ⊓ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) (hp₀2 : p₀ * p₀ = 1)
    (hp₀Z : p₀ ∉ C.Z) (hr : r ∈ D.V) (hr1 : r ≠ 1)
    (hp : p ∈ T ⊓ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) (hp2 : p * p = 1)
    (hpZ : p ∉ C.Z) (h : IsConj v (r₀ * p₀)) : IsConj v (r * p) := by
  have hc₀ := C.commute_of_mem_V hS D hT hUT hr₀ hp₀
  have hc := C.commute_of_mem_V hS D hT hUT hr hp
  obtain ⟨h₀, hh₀, rfl⟩ := D.exists_conj_x r₀ hr₀ hr₀1
  obtain ⟨h₁, hh₁, rfl⟩ := D.exists_conj_x r hr hr1
  have hh₀M := (Subgroup.mem_inf.mp hh₀).1
  have hh₁M := (Subgroup.mem_inf.mp hh₁).1
  have hh₀C := (D.Mc_le.trans (C.centralizer_Y_le hS)) hh₀M
  have hh₁C := (D.Mc_le.trans (C.centralizer_Y_le hS)) hh₁M
  have hp₁P : h₀⁻¹ * p₀ * h₀ ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) := by
    have h1 := (conj_mem_fixingSubgroup_iff (inv_mem hh₀C) p₀).mp (Subgroup.mem_inf.mp hp₀).2
    rwa [inv_inv] at h1
  have hp₂P : h₁⁻¹ * p * h₁ ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) := by
    have h1 := (conj_mem_fixingSubgroup_iff (inv_mem hh₁C) p).mp (Subgroup.mem_inf.mp hp).2
    rwa [inv_inv] at h1
  have hsq : ∀ {g q : G}, q * q = 1 → g⁻¹ * q * g * (g⁻¹ * q * g) = 1 := fun {g q} hq => by
    rw [show g⁻¹ * q * g * (g⁻¹ * q * g) = g⁻¹ * (q * q) * g by group, hq, mul_one,
      inv_mul_cancel]
  have hcomm : ∀ {g q : G}, g * C.x * g⁻¹ * q = q * (g * C.x * g⁻¹) →
      C.x * (g⁻¹ * q * g) = g⁻¹ * q * g * C.x := fun {g q} hgq => by
    calc C.x * (g⁻¹ * q * g) = g⁻¹ * ((g * C.x * g⁻¹) * q) * g := by group
      _ = g⁻¹ * (q * (g * C.x * g⁻¹)) * g := by rw [hgq]
      _ = g⁻¹ * q * g * C.x := by group
  have key := C.isConj_x_mul_of_isConj_x_mul hS hp₁P hp₂P (hsq hp₀2) (hsq hp2)
    (C.psi_conj_not_mem_N hS D hT hUT hh₀M hp₀ hp₀2 hp₀Z hp₁P)
    (C.psi_conj_not_mem_N hS D hT hUT hh₁M hp hp2 hpZ hp₂P) (hcomm hc₀) (hcomm hc)
    (h.trans (isConj_iff.mpr ⟨h₀⁻¹, by group⟩))
  exact key.trans (isConj_iff.mpr ⟨h₁, by group⟩)

end Dichotomy

end FinConfig

namespace FinConfig

section Shape

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
include C in
theorem exists_mem_fixSet_ne_γ : ∃ δ ∈ fixSet Ω (Subgroup.zpowers v), δ ≠ (C.γ : Ω) := by
  by_cases h : α = C.γ
  · exact ⟨β, C.mem_fixSet, fun hβ => C.ne (h.trans hβ.symm)⟩
  · exact ⟨α, C.isTypeL.mem_fixSet, h⟩

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
include C in
theorem not_mem_longInv_of_isConj {s : G} (hs : IsConj v s) : s ∉ longInv G Ω := fun hJ => by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hs
  obtain ⟨-, -, -, -, -, -, -, hvJ⟩ := C.isTypeL
  exact hvJ ((conj_mem_longInv_iff g).mp hJ)

theorem isConj_shape (hS : Sec4Setting G Ω) (D : C.Splitting hS) {T : Subgroup G}
    (hT : fusionIsSylowIn 2 T
      (Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)))
    (hUT : D.U ⊔ C.Y ≤ T) {s : G} (hs : IsConj v s) (hsT : s ∈ T) :
    s ∈ C.Z ∨ s ∈ D.V ∨ ∃ r ∈ D.V, r ≠ 1 ∧
      ∃ p ∈ T ⊓ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)), p * p = 1 ∧ p ∉ C.Z ∧
        s = r * p := by
  have hsC := hT.1 hsT
  have hsγ : s • (C.γ : Ω) = C.γ := C.le_stabilizer_γ hS D hT hUT hsT
  have hvs : Commute v s := Subgroup.mem_centralizer_iff.mp hsC v (Subgroup.mem_zpowers v)
  have hs2 := mul_self_eq_one_of_isConj C.v_mul_self hs
  have hmemF : ∀ {δ : Ω}, s • δ = δ → δ ∈ fixSet Ω (Subgroup.zpowers s) := fun h => by
    rw [fixSet_zpowers, mem_fixedBy]
    exact h
  by_cases hcase : ∃ δ ∈ fixSet Ω (Subgroup.zpowers v), δ ≠ C.γ ∧ s • δ = δ
  · left
    obtain ⟨δ, hδΦ, hδγ, hδs⟩ := hcase
    have hF := C.fixSet_eq_of_isConj_of_commute hS hs hvs (Ne.symm hδγ) (hmemF hsγ) C.γ_mem
      (hmemF hδs) hδΦ
    have hsP : s ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) :=
      (mem_fixingSubgroup_iff G).mpr fun ω hω => by
        rw [← hF, fixSet_zpowers, mem_fixedBy] at hω
        exact hω
    exact C.mem_Z_of_isConj_of_mem hS hT.2.1.to_inf_left inf_le_right (C.Z_le_inf hS D hUT) hs
      (Subgroup.mem_inf.mpr ⟨hsT, hsP⟩)
  right
  push Not at hcase
  set sC : Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) := ⟨s, hsC⟩
  set γi := C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i
  have hms2 : C.piM hS sC * C.piM hS sC = 1 := by
    rw [← map_mul, show sC * sC = 1 from Subtype.ext hs2, map_one]
  have hmsγ : C.piM hS sC γi = γi :=
    (C.smul_eq_iff_piM_apply_eq hS sC ⟨_, C.γ_mem⟩).mp hsγ
  have hfix : ∃! c, C.piM hS sC c = c := by
    refine ⟨γi, hmsγ, fun c hc => ?_⟩
    obtain ⟨ω, rfl⟩ := C.Dv.exists_coord_apply_eq C.i c
    have hω := (C.smul_eq_iff_piM_apply_eq hS sC ω).mpr hc
    by_contra hne
    exact hcase ω ω.2 (fun h => hne (by rw [show ω = ⟨C.γ, C.γ_mem⟩ from Subtype.ext h])) hω
  have hmsM := (C.isNaturalSE_Dv C.i).mem_of_existsUnique_fixed
    (C.piM_mem_normalizer hS sC) hms2 hfix
  have hmsR : C.piM hS sC ∈ seRadical (C.Dv.M C.i) γi :=
    mem_seRadical_of_pow_eq_one hmsM hmsγ (k := 1) (by rw [pow_one, sq, hms2])
  obtain ⟨u, hu, hum⟩ := D.exists_piM_U _ hmsR
  have huC := C.centralizer_Y_le hS (D.Mc_le (D.U_le hu))
  have hu2 : u * u = 1 := D.piM_eq_one (u * u) (mul_mem hu hu) (by
    rw [show (⟨u * u, C.centralizer_Y_le hS (D.Mc_le (D.U_le (mul_mem hu hu)))⟩ :
      Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) = ⟨u, huC⟩ * ⟨u, huC⟩
      from rfl, map_mul, hum, hms2])
  have huV : u ∈ D.V := (D.mem_V_iff u hu).mpr hu2
  have hu1 : u ≠ 1 := by
    rintro rfl
    have h1 : C.piM hS sC = 1 := by
      rw [← hum]
      exact map_one (C.piM hS)
    obtain ⟨δ, hδΦ, hδγ⟩ := C.exists_mem_fixSet_ne_γ
    exact hcase δ hδΦ hδγ ((C.piM_eq_one_iff hS sC).mp h1 δ hδΦ)
  set p := u * s with hp_def
  have hpC : p ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) :=
    mul_mem huC hsC
  have hpP : p ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) := by
    have h1 : C.piM hS ⟨p, hpC⟩ = 1 := by
      rw [show (⟨p, hpC⟩ : Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) =
        ⟨u, huC⟩ * sC from rfl, map_mul, hum, hms2]
    exact (mem_fixingSubgroup_iff G).mpr ((C.piM_eq_one_iff hS _).mp h1)
  have hpT : p ∈ T := mul_mem (hUT (Subgroup.mem_sup_left hu)) hsT
  have hup : u * p = p * u := C.commute_of_mem_V hS D hT hUT huV (Subgroup.mem_inf.mpr ⟨hpT, hpP⟩)
  have hsp : s = u * p := by rw [hp_def, ← mul_assoc, hu2, one_mul]
  have hus : u * s = s * u := by
    have h1 : s = u * s * u := by
      have := hup
      rw [hp_def, ← mul_assoc, hu2, one_mul] at this
      exact this
    calc u * s = u * s * u * u := by rw [mul_assoc (u * s) u u, hu2, mul_one]
      _ = s * u := by rw [← h1]
  have hp2 : p * p = 1 := by
    calc p * p = u * (s * u) * s := by rw [hp_def]; group
      _ = u * (u * s) * s := by rw [hus]
      _ = (u * u) * (s * s) := by group
      _ = 1 := by rw [hu2, hs2, mul_one]
  by_cases hp1 : p = 1
  · left
    rw [hsp, hp1, mul_one]
    exact huV
  · right
    refine ⟨u, huV, hu1, p, Subgroup.mem_inf.mpr ⟨hpT, hpP⟩, hp2, fun hpZ => ?_, hsp⟩
    have hJ := D.mul_mem_longInv u huV p hpZ hu1 hp1
    rw [← hsp] at hJ
    exact C.not_mem_longInv_of_isConj hs hJ

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
include C in
theorem v_mul_ne_one {s : G} (hs : s ≠ v) : v * s ≠ 1 := fun h => hs (by
  calc s = v * (v * s) := by rw [← mul_assoc, C.v_mul_self, one_mul]
    _ = v := by rw [h, mul_one])

theorem exists_mem_V_ne (hS : Sec4Setting G Ω) (D : C.Splitting hS) :
    ∃ x' ∈ D.V, x' ≠ 1 ∧ x' ≠ C.x := by
  by_contra h
  push Not at h
  have hM := C.isNaturalSE_Dv C.i
  obtain ⟨n, i, e, hA⟩ := hM.exists_isBenderAction
  set γi := C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i
  set R := rootCenter (seRadical (C.Dv.M C.i) γi)
  have hxC := C.centralizer_Y_le hS (D.Mc_le (D.U_le (D.V_le D.x_mem_V)))
  have hsub : (R : Set (Equiv.Perm (C.Dv.Ψc C.i))) ⊆ {1, C.piM hS ⟨C.x, hxC⟩} := by
    intro m hm
    obtain ⟨u, hu, hum⟩ := D.exists_piM_U m (CFSG.GH74.Uniqueness.Bender.rootCenter_le _ hm)
    have huC := C.centralizer_Y_le hS (D.Mc_le (D.U_le hu))
    have hu2 : u * u = 1 := D.piM_eq_one (u * u) (mul_mem hu hu) (by
      rw [show (⟨u * u, C.centralizer_Y_le hS (D.Mc_le (D.U_le (mul_mem hu hu)))⟩ :
        Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) = ⟨u, huC⟩ * ⟨u, huC⟩
        from rfl, map_mul, hum]
      exact hM.mul_self_eq_one_of_mem_rootCenter hm)
    rcases eq_or_ne u 1 with rfl | hu1
    · left
      rw [← hum]
      exact map_one (C.piM hS)
    · right
      have hux := h u ((D.mem_V_iff u hu).mpr hu2) hu1
      subst hux
      exact hum.symm
  have hcard := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({1, C.piM hS ⟨C.x, hxC⟩} : Set (Equiv.Perm (C.Dv.Ψc C.i))).ncard ≤ 2 :=
    (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  have h4 : 4 ≤ (R : Set (Equiv.Perm (C.Dv.Ψc C.i))).ncard := by
    rw [← Nat.card_coe_set_eq]
    exact (hA.card_rootCenter_seRadical γi).symm ▸ hA.four_le_q
  omega

end Shape

end FinConfig

namespace FinConfig

section Theorem43


variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

theorem isConj_x (hS : Sec4Setting G Ω) (D : C.Splitting hS) : IsConj v C.x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hx
  have hV : ∀ r ∈ D.V, r ≠ 1 → ¬ IsConj v r := fun r hr hr1 hvr => by
    obtain ⟨h, -, rfl⟩ := D.exists_conj_x r hr hr1
    exact hx (hvr.trans (isConj_iff.mpr ⟨h⁻¹, by group⟩))
  have hconj1 : ∀ {s : G}, IsConj v s → s ≠ 1 := fun {s} hs h1 => C.v_ne_one (by
    obtain ⟨g, rfl⟩ := isConj_iff.mp hs
    calc v = g⁻¹ * (g * v * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group)
  obtain ⟨T, hUT, hT⟩ := exists_fusionIsSylowIn_ge (C.isPGroup_U_sup_Y hS D) (C.U_sup_Y_le hS D)
  have hconjT : ∀ {s : G},
      s ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) → s * s = 1 →
        ∃ c ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G),
          c⁻¹ * s * c ∈ T := by
    intro s hsC hs2
    obtain ⟨T', hsT', hT'⟩ := exists_fusionIsSylowIn_ge
      (isPGroup_zpowers_of_pow_eq_one (k := 1) (by rw [pow_one, sq, hs2]))
      (Subgroup.zpowers_le.mpr hsC)
    obtain ⟨c, hc, hcT⟩ := exists_mem_conj_of_fusionIsSylowIn hT hT'
    exact ⟨c, hc, (hcT s).mp (hsT' (Subgroup.mem_zpowers s))⟩
  have hconjv : ∀ {c : G},
      c ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) →
        c⁻¹ * v * c = v := fun {c} hc => by
    have h1 := conj_eq_self_of_mem_centralizer_zpowers (inv_mem hc)
    rwa [inv_inv] at h1
  obtain ⟨s₀, hs₀, hvs₀, hFs₀⟩ := C.exists_isConj_commute_fixSet_ne hS
  obtain ⟨c₀, hc₀, hs₁T⟩ := hconjT (mem_centralizer_zpowers hvs₀)
    (mul_self_eq_one_of_isConj C.v_mul_self hs₀)
  have hs₁ : IsConj v (c₀⁻¹ * s₀ * c₀) := hs₀.trans (isConj_iff.mpr ⟨c₀⁻¹, by group⟩)
  have hFs₁ : fixSet Ω (Subgroup.zpowers (c₀⁻¹ * s₀ * c₀)) ≠
      fixSet Ω (Subgroup.zpowers v) := fun h => hFs₀ (by
    have h1 := fixSet_zpowers_conj (Ω := Ω) c₀⁻¹ s₀
    rw [show c₀⁻¹ * s₀ * c₀⁻¹⁻¹ = c₀⁻¹ * s₀ * c₀ by rw [inv_inv], h] at h1
    rw [eq_inv_smul_iff] at h1
    rw [← h1, smul_fixSet_zpowers_of_mem_centralizer hc₀])
  obtain ⟨r₀, hr₀, hr₀1, p₀, hp₀, hp₀2, hp₀Z, hs₁e⟩ : ∃ r₀ ∈ D.V, r₀ ≠ 1 ∧
      ∃ p₀ ∈ T ⊓ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)), p₀ * p₀ = 1 ∧ p₀ ∉ C.Z ∧
        c₀⁻¹ * s₀ * c₀ = r₀ * p₀ := by
    rcases C.isConj_shape hS D hT hUT hs₁ hs₁T with hZ | hV' | h
    · exact absurd (C.fixSet_eq_of_mem_Z hS hZ (hconj1 hs₁)) hFs₁
    · exact absurd hs₁ (hV _ hV' (hconj1 hs₁))
    · exact h
  have hall : ∀ r ∈ D.V, r ≠ 1 →
      ∀ p ∈ T ⊓ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)), p * p = 1 → p ∉ C.Z →
        IsConj v (r * p) := fun r hr hr1 p hp hp2 hpZ =>
    C.isConj_mul_of_isConj_mul hS D hT hUT hr₀ hr₀1 hp₀ hp₀2 hp₀Z hr hr1 hp hp2 hpZ
      (hs₁e ▸ hs₁)
  have hvZ := C.v_mem_Z hS
  have hPP : ∀ s : G, IsConj v s → Commute v s → s ≠ v → IsConj v (v * s) := by
    intro s hs hvs hsv
    obtain ⟨c, hc, hsT⟩ := hconjT (mem_centralizer_zpowers hvs)
      (mul_self_eq_one_of_isConj C.v_mul_self hs)
    have hs' : IsConj v (c⁻¹ * s * c) := hs.trans (isConj_iff.mpr ⟨c⁻¹, by group⟩)
    have hs'v : c⁻¹ * s * c ≠ v := fun h => hsv (by
      calc s = c * (c⁻¹ * s * c) * c⁻¹ := by group
        _ = c * (c⁻¹ * v * c) * c⁻¹ := by rw [h, hconjv hc]
        _ = v := by group)
    suffices h : IsConj v (v * (c⁻¹ * s * c)) by
      refine h.trans (isConj_iff.mpr ⟨c, ?_⟩)
      calc c * (v * (c⁻¹ * s * c)) * c⁻¹ = c * (c⁻¹ * v * c) * c⁻¹ * s := by
            rw [hconjv hc]; group
        _ = v * s := by group
    rcases C.isConj_shape hS D hT hUT hs' hsT with hZ | hV' | ⟨r, hr, hr1, p, hp, hp2, hpZ, he⟩
    · obtain ⟨h, -, -, hh⟩ := C.exists_conj_eq_of_mem_Z hS hvZ C.v_ne_one (mul_mem hvZ hZ)
        (C.v_mul_ne_one hs'v)
      exact isConj_iff.mpr ⟨h, hh⟩
    · exact absurd hs' (hV _ hV' (hconj1 hs'))
    · have hvr : v * r = r * v := (Subgroup.mem_centralizer_iff.mp
        (D.Mc_le (D.U_le (D.V_le hr))) v (C.Z_le_Y hvZ))
      have hvs' : v * (c⁻¹ * s * c) = c⁻¹ * s * c * v :=
        Subgroup.mem_centralizer_iff.mp (hT.1 hsT) v (Subgroup.mem_zpowers v)
      have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right
        ((D.mem_V_iff r (D.V_le hr)).mp hr)
      have hpe : p = r * (c⁻¹ * s * c) := by rw [he, ← mul_assoc,
        (D.mem_V_iff r (D.V_le hr)).mp hr, one_mul]
      have hvp : v * p = p * v := by
        rw [hpe]
        calc v * (r * (c⁻¹ * s * c)) = (v * r) * (c⁻¹ * s * c) := by group
          _ = r * (v * (c⁻¹ * s * c)) := by rw [hvr]; group
          _ = r * (c⁻¹ * s * c) * v := by rw [hvs']; group
      have hvpT : v * p ∈ T ⊓ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) :=
        mul_mem (C.Z_le_inf hS D hUT hvZ) hp
      have hvp2 : v * p * (v * p) = 1 := by
        calc v * p * (v * p) = v * (p * v) * p := by group
          _ = v * (v * p) * p := by rw [hvp]
          _ = (v * v) * (p * p) := by group
          _ = 1 := by rw [C.v_mul_self, hp2, mul_one]
      have hvpZ : v * p ∉ C.Z := fun h => hpZ (by
        have h1 := mul_mem (inv_mem hvZ) h
        rwa [inv_mul_cancel_left] at h1)
      have h1 := hall r hr hr1 (v * p) hvpT hvp2 hvpZ
      rw [he]
      rwa [show v * (r * p) = r * (v * p) by
        calc v * (r * p) = (v * r) * p := by group
          _ = r * (v * p) := by rw [hvr]; group]
  obtain ⟨x', hx'V, hx'1, hx'x⟩ := C.exists_mem_V_ne hS D
  have hx1 : C.x ≠ 1 := fun h => C.ne (by
    have h1 := (C.x_smul hS).1
    rwa [h, one_smul] at h1)
  have hxp := hall C.x D.x_mem_V hx1 p₀ hp₀ hp₀2 hp₀Z
  have hx'p := hall x' hx'V hx'1 p₀ hp₀ hp₀2 hp₀Z
  have hV2 : ∀ u ∈ D.V, u * u = 1 := fun u hu => (D.mem_V_iff u (D.V_le hu)).mp hu
  have hcxx' := FinalC.commute_of_forall_mul_self_eq_one hV2 D.x_mem_V hx'V
  have hcxp := C.commute_of_mem_V hS D hT hUT D.x_mem_V hp₀
  have hcx'p := C.commute_of_mem_V hS D hT hUT hx'V hp₀
  have hprod : C.x * p₀ * (x' * p₀) = C.x * x' := by
    calc C.x * p₀ * (x' * p₀) = C.x * (p₀ * x') * p₀ := by group
      _ = C.x * (x' * p₀) * p₀ := by rw [hcx'p]
      _ = C.x * x' * (p₀ * p₀) := by group
      _ = C.x * x' := by rw [hp₀2, mul_one]
  have hcomm : C.x * p₀ * (x' * p₀) = x' * p₀ * (C.x * p₀) := by
    rw [hprod]
    calc C.x * x' = x' * C.x * (p₀ * p₀) := by rw [hp₀2, mul_one, hcxx'.eq]
      _ = x' * (C.x * p₀) * p₀ := by group
      _ = x' * (p₀ * C.x) * p₀ := by rw [hcxp]
      _ = x' * p₀ * (C.x * p₀) := by group
  obtain ⟨g, hg⟩ := isConj_iff.mp hxp
  have ht : IsConj v (g⁻¹ * (x' * p₀) * g) := hx'p.trans (isConj_iff.mpr ⟨g⁻¹, by group⟩)
  have hvt : Commute v (g⁻¹ * (x' * p₀) * g) := by
    show v * (g⁻¹ * (x' * p₀) * g) = g⁻¹ * (x' * p₀) * g * v
    calc v * (g⁻¹ * (x' * p₀) * g) = g⁻¹ * ((g * v * g⁻¹) * (x' * p₀)) * g := by group
      _ = g⁻¹ * ((x' * p₀) * (g * v * g⁻¹)) * g := by rw [hg, hcomm]
      _ = g⁻¹ * (x' * p₀) * g * v := by group
  have htv : g⁻¹ * (x' * p₀) * g ≠ v := fun h => hx'x (by
    have h1 : x' * p₀ = C.x * p₀ := by
      calc x' * p₀ = g * (g⁻¹ * (x' * p₀) * g) * g⁻¹ := by group
        _ = C.x * p₀ := by rw [h, hg]
    exact mul_right_cancel h1)
  have h1 := hPP _ ht hvt htv
  have h2 : g * (v * (g⁻¹ * (x' * p₀) * g)) * g⁻¹ = C.x * x' := by
    rw [← hprod, ← hg]
    group
  have hxx'1 : C.x * x' ≠ 1 := fun h => hx'x (by
    have h3 := hV2 _ D.x_mem_V
    calc x' = C.x * (C.x * x') := by rw [← mul_assoc, h3, one_mul]
      _ = C.x := by rw [h, mul_one])
  exact hV _ (mul_mem D.x_mem_V hx'V) hxx'1 (h1.trans (isConj_iff.mpr ⟨g, h2⟩))

end Theorem43

end FinConfig

end CFSG.Holt.H78

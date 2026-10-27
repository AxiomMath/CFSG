module

public import CFSG.Holt.H78.Sec4FinalA4
public import CFSG.Holt.H78.Sec4SEAutFix

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open
open CFSG.GH74.Uniqueness.Bender (rootCenter)
open scoped Pointwise

@[expose] def SETwoCoverConj : Prop :=
  ∀ (E : Type) [Group E] [Finite E] (Δ : Type) [Finite Δ] (π : E →* Equiv.Perm Δ),
    IsNaturalSE π.range → π.ker ≤ Subgroup.center E → (∀ z ∈ π.ker, z * z = 1) →
      4 ≤ Nat.card π.ker → commutator E = ⊤ →
        ∀ a : E, a * a = 1 → a ∉ π.ker → ∀ z ∈ π.ker, ∃ g : E, g * a * g⁻¹ = a * z

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

theorem le_oddCoreOf {B N : Subgroup G} (hNB : N ≤ B)
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

theorem conj_mem_oddCoreOf {B : Subgroup G} {g : G} (hg : ∀ b, b ∈ B ↔ g * b * g⁻¹ ∈ B)
    {q : G} (hq : q ∈ oddCoreOf B) : g * q * g⁻¹ ∈ oddCoreOf B := by
  have hle : (oddCoreOf B).map (MulAut.conj g).toMonoidHom ≤ oddCoreOf B := by
    refine le_oddCoreOf ?_ ?_ ?_
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

section Fixing

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω]

theorem mem_fixingSubgroup_iff_conj {Γ : Set Ω} {g : G} (hg : g • Γ = Γ) (b : G) :
    b ∈ fixingSubgroup G Γ ↔ g * b * g⁻¹ ∈ fixingSubgroup G Γ := by
  have hin : ∀ ω ∈ Γ, g⁻¹ • ω ∈ Γ := fun ω hω => by
    rw [← Set.mem_smul_set_iff_inv_smul_mem, hg]
    exact hω
  have hout : ∀ ω ∈ Γ, g • ω ∈ Γ := fun ω hω => by
    rw [← hg]
    exact Set.smul_mem_smul_set hω
  simp only [mem_fixingSubgroup_iff]
  constructor
  · intro hb ω hω
    rw [mul_smul, mul_smul, hb _ (hin ω hω), smul_inv_smul]
  · intro hb ω hω
    have h1 := hb (g • ω) (hout ω hω)
    rwa [mul_smul, mul_smul, inv_smul_smul, smul_left_cancel_iff] at h1

end Fixing

section Conj

variable {G : Type} [Group G]

theorem conj_pow_mem {H : Subgroup G} {h : G} (hh : ∀ y ∈ H, h * y * h⁻¹ ∈ H) (k : ℕ) {y : G}
    (hy : y ∈ H) : h ^ k * y * (h ^ k)⁻¹ ∈ H := by
  induction k with
  | zero => simpa using hy
  | succ k ih =>
    have h1 := hh _ ih
    rw [pow_succ']
    simpa [mul_assoc, mul_inv_rev] using h1

theorem inv_conj_mem [Finite G] {H : Subgroup G} {h : G} (hh : ∀ y ∈ H, h * y * h⁻¹ ∈ H) {y : G}
    (hy : y ∈ H) : h⁻¹ * y * h ∈ H := by
  have h1 := conj_pow_mem hh (orderOf h - 1) hy
  have h2 : h ^ (orderOf h - 1) = h⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel (orderOf_pos h),
      pow_orderOf_eq_one]
  rwa [h2, inv_inv] at h1

theorem conj_mem_centralizer [Finite G] {H : Subgroup G} {h : G}
    (hh : ∀ y ∈ H, h * y * h⁻¹ ∈ H) {c : G} (hc : c ∈ Subgroup.centralizer (H : Set G)) :
    h * c * h⁻¹ ∈ Subgroup.centralizer (H : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro y hy
  have h1 := hc _ (inv_conj_mem hh hy)
  calc y * (h * c * h⁻¹) = h * ((h⁻¹ * y * h) * c) * h⁻¹ := by group
    _ = h * (c * (h⁻¹ * y * h)) * h⁻¹ := by rw [h1]
    _ = h * c * h⁻¹ * y := by group

end Conj

section Simple

theorem closure_involutions_eq_top {K : Type*} [Group K] [IsSimpleGroup K] {k : K}
    (hk : k * k = 1) (hk1 : k ≠ 1) : Subgroup.closure {a : K | a * a = 1 ∧ a ≠ 1} = ⊤ := by
  set S : Set K := {a : K | a * a = 1 ∧ a ≠ 1}
  have hN : (Subgroup.closure S).Normal := ⟨fun n hn g => by
    have h1 : (Subgroup.closure S).map (MulAut.conj g).toMonoidHom ≤ Subgroup.closure S := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨a, ⟨ha, ha1⟩, rfl⟩
      refine Subgroup.subset_closure ⟨?_, ?_⟩
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
          _ = 1 := by rw [ha, mul_one, mul_inv_cancel]
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        intro h
        exact ha1 (by rw [mul_inv_eq_one, mul_eq_left] at h; exact h)
    exact h1 ⟨n, hn, rfl⟩⟩
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ _ _ hN with h | h
  · have hkb : k ∈ (⊥ : Subgroup K) := h ▸ Subgroup.subset_closure ⟨hk, hk1⟩
    exact absurd (Subgroup.mem_bot.mp hkb) hk1
  · exact h

end Simple

section Sup

variable {G : Type} [Group G]

theorem exists_mul_of_mem_sup {K O : Subgroup G} (hKO : ∀ k ∈ K, ∀ o ∈ O, k * o * k⁻¹ ∈ O)
    {g : G} (hg : g ∈ K ⊔ O) : ∃ k ∈ K, ∃ o ∈ O, g = k * o := by
  let S : Subgroup G :=
    { carrier := {x | ∃ k ∈ K, ∃ o ∈ O, x = k * o}
      mul_mem' := by
        rintro _ _ ⟨k, hk, o, ho, rfl⟩ ⟨k', hk', o', ho', rfl⟩
        refine ⟨k * k', K.mul_mem hk hk', k'⁻¹ * o * k' * o', O.mul_mem ?_ ho', by group⟩
        simpa using hKO k'⁻¹ (K.inv_mem hk') o ho
      one_mem' := ⟨1, K.one_mem, 1, O.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨k, hk, o, ho, rfl⟩
        exact ⟨k⁻¹, K.inv_mem hk, k * o⁻¹ * k⁻¹, hKO k hk _ (O.inv_mem ho), by group⟩ }
  have hle : K ⊔ O ≤ S := sup_le (fun k hk => ⟨k, hk, 1, O.one_mem, by simp⟩)
    (fun o ho => ⟨1, K.one_mem, o, ho, by simp⟩)
  exact hle hg

theorem conj_mem_commutator_sup {L O : Subgroup G} {h : G} (hL : ∀ g ∈ L, h * g * h⁻¹ ∈ L)
    (hO : ∀ o ∈ O, h * o * h⁻¹ ∈ O) {g : G} (hg : g ∈ ⁅L, L⁆ ⊔ O) :
    h * g * h⁻¹ ∈ ⁅L, L⁆ ⊔ O := by
  have hLm : L.map (MulAut.conj h).toMonoidHom ≤ L := by
    rintro _ ⟨g, hg, rfl⟩
    exact hL g hg
  have hOm : O.map (MulAut.conj h).toMonoidHom ≤ O := by
    rintro _ ⟨o, ho, rfl⟩
    exact hO o ho
  have hle : (⁅L, L⁆ ⊔ O).map (MulAut.conj h).toMonoidHom ≤ ⁅L, L⁆ ⊔ O := by
    rw [Subgroup.map_sup, Subgroup.map_commutator]
    exact sup_le_sup (Subgroup.commutator_mono hLm hLm) hOm
  exact hle ⟨g, hg, rfl⟩

end Sup

section Comm

theorem mem_commutator_of_mem {G : Type*} [Group G] {L : Subgroup G} {c : G} (hc : c ∈ ⁅L, L⁆) :
    ∃ hcL : c ∈ L, (⟨c, hcL⟩ : L) ∈ commutator L := by
  have h1 : (commutator L).map L.subtype = ⁅L, L⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← h1] at hc
  obtain ⟨c₀, hc₀, rfl⟩ := hc
  exact ⟨c₀.2, hc₀⟩

theorem exists_zpowers_conj_eq_mul {X : Type*} [Group X] {o t : X} (ho : Odd (orderOf o))
    (ht : t * t = 1) (hot : o * t * (o * t) = 1) :
    ∃ p ∈ Subgroup.zpowers o, p * t * p⁻¹ = o * t := by
  obtain ⟨k, hk⟩ := ho
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have h1 : t * o * t⁻¹ = o⁻¹ := by
    rw [hti]
    apply eq_inv_of_mul_eq_one_left
    calc t * o * t * o = t * (o * t * (o * t)) * t⁻¹ := by group
      _ = 1 := by rw [hot, mul_one, mul_inv_cancel]
  have h2 : t * o ^ (k + 1) * t⁻¹ = (o ^ (k + 1))⁻¹ := by rw [← conj_pow, h1, inv_pow]
  have h3 : o ^ (k + 1) * o ^ (k + 1) = o := by
    rw [← pow_add, show k + 1 + (k + 1) = orderOf o + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  refine ⟨o ^ (k + 1), Subgroup.npow_mem_zpowers o _, ?_⟩
  have h4 : t * (o ^ (k + 1))⁻¹ * t⁻¹ = o ^ (k + 1) := by
    rw [show t * (o ^ (k + 1))⁻¹ * t⁻¹ = (t * o ^ (k + 1) * t⁻¹)⁻¹ by group, h2, inv_inv]
  calc o ^ (k + 1) * t * (o ^ (k + 1))⁻¹ = o ^ (k + 1) * (t * (o ^ (k + 1))⁻¹ * t⁻¹) * t := by
        group
    _ = o * t := by rw [h4, h3]

theorem exists_conj_eq_of_odd_mul_inv {G : Type*} [Group G] {t w : G} (ht : t * t = 1)
    (hw : w * w = 1) (ho : Odd (orderOf (w * t⁻¹))) : ∃ p : G, p * t * p⁻¹ = w := by
  obtain ⟨p, -, hp⟩ := exists_zpowers_conj_eq_mul ho ht (by rw [inv_mul_cancel_right]; exact hw)
  exact ⟨p, by rw [hp, inv_mul_cancel_right]⟩

end Comm

namespace FinConfig

section Basic

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)


theorem conj_mem_Z_of_normalizes_Y (hS : Sec4Setting G Ω) {h : G}
    (hh : ∀ y ∈ C.Y, h * y * h⁻¹ ∈ C.Y) {z : G} (hz : z ∈ C.Z) : h * z * h⁻¹ ∈ C.Z := by
  refine C.mem_Z_of_mem_Y_of_mul_self (hh z (C.Z_le_Y hz)) ?_
  calc h * z * h⁻¹ * (h * z * h⁻¹) = h * (z * z) * h⁻¹ := by group
    _ = 1 := by rw [C.mul_self_eq_one_of_mem_Z hS hz, mul_one, mul_inv_cancel]

theorem smul_fixSet_eq_of_normalizes_Y (hS : Sec4Setting G Ω) {h : G}
    (hh : ∀ y ∈ C.Y, h * y * h⁻¹ ∈ C.Y) :
    h • fixSet Ω (Subgroup.zpowers v) = fixSet Ω (Subgroup.zpowers v) :=
  C.smul_fixSet_eq_of_normalizes_Z hS fun _ hz => C.conj_mem_Z_of_normalizes_Y hS hh hz

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem smul_fixSet_eq_of_mem_centralizer {c : G}
    (hc : c ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) :
    c • fixSet Ω (Subgroup.zpowers v) = fixSet Ω (Subgroup.zpowers v) :=
  mem_stabilizer_iff.mp (centralizer_le_stabilizer_fixSet _ hc)

omit [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem conj_mem_fixCore {h : G}
    (hh : h • fixSet Ω (Subgroup.zpowers v) = fixSet Ω (Subgroup.zpowers v)) {q : G}
    (hq : q ∈ oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)))) :
    h * q * h⁻¹ ∈ oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) :=
  conj_mem_oddCoreOf (mem_fixingSubgroup_iff_conj hh) hq

end Basic

end FinConfig

namespace FinConfig

section Lemma31

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)


theorem exists_centralizer_Y_piM_eq (hS : Sec4Setting G Ω) {m : Equiv.Perm (C.Dv.Ψc C.i)}
    (hm : m ∈ C.Dv.M C.i) :
    ∃ c, ∃ hc : c ∈ Subgroup.centralizer (C.Y : Set G),
      C.piM hS ⟨c, C.centralizer_Y_le hS hc⟩ = m := by
  obtain ⟨l, -, rfl⟩ := C.Dv.mem_M.mp hm
  obtain ⟨h, hY, hhl⟩ := C.exists_centralizer_Y_of_mem_jHull hS l.2
  have hhC := C.centralizer_Y_le hS hY
  refine ⟨h, hY, ?_⟩
  have h1 : centralizerImageElt (Ω := Ω) hhC = (l : typeLSection G Ω v) :=
    Subtype.ext (Equiv.ext fun ω => Subtype.ext (hhl ω).symm)
  ext c
  obtain ⟨ω, rfl⟩ := C.Dv.exists_coord_apply_eq C.i c
  rw [C.piM_coord, ← C.Dv.coord_smul]
  exact congrArg (fun π : typeLSection G Ω v => C.Dv.coord (π • ω) C.i) h1

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
include C in
theorem mem_stabilizer_inf_of_mem_fixingSubgroup {g : G}
    (hg : g ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) :
    g ∈ stabilizer G α ⊓ stabilizer G β :=
  ⟨(mem_fixingSubgroup_iff G).mp hg α C.isTypeL.mem_fixSet,
    (mem_fixingSubgroup_iff G).mp hg β C.mem_fixSet⟩

omit [FaithfulSMul G Ω] in
theorem mem_fixCore_of_psi_eq_one (hS : Sec4Setting G Ω) {g : G}
    (hg : g ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)))
    (hψ : C.psi ⟨g, stabilizer_inf_le_stabilizer_pair α β
      (C.mem_stabilizer_inf_of_mem_fixingSubgroup hg)⟩ = 1) :
    g ∈ oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) := by
  set P := fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) with hP
  have hst : ∀ b ∈ P, b ∈ stabilizer G ({α, β} : Set Ω) := fun b hb =>
    stabilizer_inf_le_stabilizer_pair α β (C.mem_stabilizer_inf_of_mem_fixingSubgroup hb)
  have hK₀ : P ⊓ C.psiPre ⊥ ≤ oddCoreOf P := by
    refine le_oddCoreOf inf_le_left ?_ ?_
    · intro b hb n hn
      obtain ⟨hn2, hn3⟩ := C.mem_psiPre.mp hn.2
      have hb2 := hst b hb
      refine ⟨P.mul_mem (P.mul_mem hb hn.1) (P.inv_mem hb), C.mem_psiPre.mpr
        ⟨mul_mem (mul_mem hb2 hn2) (inv_mem hb2), ?_⟩⟩
      rw [C.psi_mul (mul_mem hb2 hn2) (inv_mem hb2), C.psi_mul hb2 hn2, C.psi_inv hb2,
        Subgroup.mem_bot.mp hn3, mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    · intro n hn
      obtain ⟨hn2, hn3⟩ := C.mem_psiPre.mp hn.2
      exact C.odd_orderOf_of_psi_eq_one hS (C.mem_stabilizer_inf_of_mem_fixingSubgroup hn.1)
        (Subgroup.mem_bot.mp hn3) fun δ _ hδ => (mem_fixingSubgroup_iff G).mp hn.1 δ hδ
  exact hK₀ ⟨hg, C.mem_psiPre.mpr ⟨hst g hg, Subgroup.mem_bot.mpr hψ⟩⟩

theorem exists_mem_Z_inv_mul_mem (hS : Sec4Setting G Ω) {c : G}
    (hcY : c ∈ Subgroup.centralizer (C.Y : Set G))
    (hcP : c ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) :
    ∃ z ∈ C.Z, z⁻¹ * c ∈ oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) := by
  have hc2 := stabilizer_inf_le_stabilizer_pair α β (C.mem_stabilizer_inf_of_mem_fixingSubgroup hcP)
  have hRZ : C.psi ⟨c, hc2⟩ ∈ C.Zhat := by
    refine C.isNaturalSE_N.mem_rootCenter_seRadical_of_commute (C.psi_mem_normalizer _) ?_
    intro r hr
    obtain ⟨y, hy, rfl⟩ := C.exists_mem_Y_of_mem_Rhat hS hr
    rw [← C.psi_mul hc2 _, ← C.psi_mul _ hc2]
    exact congrArg C.psi (Subtype.ext ((Subgroup.mem_centralizer_iff.mp hcY y hy).symm))
  obtain ⟨z, hz, hzc⟩ := C.exists_mem_Z_of_mem_Zhat hS hRZ
  have hzP := C.Z_le_fixingSubgroup hS hz
  have hzc' : z⁻¹ * c ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) :=
    mul_mem (inv_mem hzP) hcP
  refine ⟨z, hz, C.mem_fixCore_of_psi_eq_one hS hzc' ?_⟩
  have hz2 := C.X_le_stabilizer_pair (C.Y_le_X (C.Z_le_Y hz))
  rw [C.psi_mul (inv_mem hz2) hc2, C.psi_inv hz2, hzc, inv_mul_cancel]

end Lemma31

end FinConfig

namespace FinConfig

section Lpre

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)


noncomputable def Lpre (hS : Sec4Setting G Ω) : Subgroup G :=
  ((C.Dv.M C.i).comap (C.piM hS)).map
      (Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)).subtype ⊓
    Subgroup.centralizer (C.Y : Set G)

theorem mem_Lpre (hS : Sec4Setting G Ω) {g : G} :
    g ∈ C.Lpre hS ↔ ∃ hg : g ∈ Subgroup.centralizer (C.Y : Set G),
      C.piM hS ⟨g, C.centralizer_Y_le hS hg⟩ ∈ C.Dv.M C.i := by
  constructor
  · rintro ⟨⟨g', hg', rfl⟩, hY⟩
    exact ⟨hY, hg'⟩
  · rintro ⟨hY, hM⟩
    exact ⟨⟨⟨g, C.centralizer_Y_le hS hY⟩, hM, rfl⟩, hY⟩

theorem Lpre_le (hS : Sec4Setting G Ω) : C.Lpre hS ≤ Subgroup.centralizer (C.Y : Set G) :=
  inf_le_right

theorem piM_conj (hS : Sec4Setting G Ω) {c g : G}
    (hc : c ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G))
    (hg : g ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) :
    C.piM hS ⟨c * g * c⁻¹, mul_mem (mul_mem hc hg) (inv_mem hc)⟩ =
      C.piM hS ⟨c, hc⟩ * C.piM hS ⟨g, hg⟩ * (C.piM hS ⟨c, hc⟩)⁻¹ := by
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem conj_mem_Lpre (hS : Sec4Setting G Ω) {c g : G}
    (hc : c ∈ Subgroup.centralizer (C.Y : Set G)) (hg : g ∈ C.Lpre hS) :
    c * g * c⁻¹ ∈ C.Lpre hS := by
  obtain ⟨hgY, hgM⟩ := (C.mem_Lpre hS).mp hg
  have hcv := C.centralizer_Y_le hS hc
  refine (C.mem_Lpre hS).mpr ⟨mul_mem (mul_mem hc hgY) (inv_mem hc), ?_⟩
  rw [C.piM_conj hS hcv (C.centralizer_Y_le hS hgY)]
  exact (Subgroup.mem_normalizer_iff.mp (C.piM_mem_normalizer hS ⟨c, hcv⟩) _).mp hgM

theorem mem_Lpre_of_mem_fixingSubgroup (hS : Sec4Setting G Ω) {g : G}
    (hgY : g ∈ Subgroup.centralizer (C.Y : Set G))
    (hgP : g ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) : g ∈ C.Lpre hS := by
  refine (C.mem_Lpre hS).mpr ⟨hgY, ?_⟩
  rw [(C.piM_eq_one_iff hS _).mpr fun ω hω => (mem_fixingSubgroup_iff G).mp hgP ω hω]
  exact Subgroup.one_mem _

theorem coord_i_injective (hS : Sec4Setting G Ω) :
    Function.Injective fun ω : fixSet Ω (Subgroup.zpowers v) => C.Dv.coord ω C.i :=
  fun _ _ h => C.coord_Dv_injective (funext fun j => by rcases C.eq_i hS j with rfl; exact h)

theorem existsUnique_fixed_piM_iff (hS : Sec4Setting G Ω)
    (g : Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) :
    (∃! c : C.Dv.Ψc C.i, C.piM hS g c = c) ↔
      ∃! ω : fixSet Ω (Subgroup.zpowers v), (g : G) • (ω : Ω) = ω := by
  constructor
  · rintro ⟨c, hc, hu⟩
    obtain ⟨ω, rfl⟩ := C.Dv.exists_coord_apply_eq C.i c
    refine ⟨ω, (C.smul_eq_iff_piM_apply_eq hS g ω).mpr hc, fun ω' hω' => ?_⟩
    exact C.coord_i_injective hS (hu _ ((C.smul_eq_iff_piM_apply_eq hS g ω').mp hω'))
  · rintro ⟨ω, hω, hu⟩
    refine ⟨C.Dv.coord ω C.i, (C.smul_eq_iff_piM_apply_eq hS g ω).mp hω, fun c hc => ?_⟩
    obtain ⟨ω', rfl⟩ := C.Dv.exists_coord_apply_eq C.i c
    rw [hu ω' ((C.smul_eq_iff_piM_apply_eq hS g ω').mpr hc)]

theorem piM_conj_mem_of_normalizes_Y (hS : Sec4Setting G Ω) {h : G}
    (hh : ∀ y ∈ C.Y, h * y * h⁻¹ ∈ C.Y) {c : G} (hc : c ∈ Subgroup.centralizer (C.Y : Set G))
    (hcM : C.piM hS ⟨c, C.centralizer_Y_le hS hc⟩ ∈ C.Dv.M C.i)
    (hc2 : orderOf (C.piM hS ⟨c, C.centralizer_Y_le hS hc⟩) = 2) :
    C.piM hS ⟨h * c * h⁻¹, C.centralizer_Y_le hS (conj_mem_centralizer hh hc)⟩ ∈
      C.Dv.M C.i := by
  have hhΦ := C.smul_fixSet_eq_of_normalizes_Y hS hh
  have hmem : ∀ ω : Ω, ω ∈ fixSet Ω (Subgroup.zpowers v) →
      h • ω ∈ fixSet Ω (Subgroup.zpowers v) := fun ω hω => by
    rw [← hhΦ]
    exact Set.smul_mem_smul_set hω
  have hmem' : ∀ ω : Ω, ω ∈ fixSet Ω (Subgroup.zpowers v) →
      h⁻¹ • ω ∈ fixSet Ω (Subgroup.zpowers v) := fun ω hω => by
    rw [← Set.mem_smul_set_iff_inv_smul_mem, hhΦ]
    exact hω
  have hu : ∃! δ, C.piM hS ⟨c, C.centralizer_Y_le hS hc⟩ δ = δ :=
    (C.isNaturalSE_Dv C.i).existsUnique_fixed (x := ⟨_, hcM⟩) (by rwa [Subgroup.orderOf_mk])
  obtain ⟨ω₀, hω₀, hu₀⟩ := (C.existsUnique_fixed_piM_iff hS _).mp hu
  have hu' : ∃! ω : fixSet Ω (Subgroup.zpowers v), (h * c * h⁻¹) • (ω : Ω) = ω := by
    refine ⟨⟨h • (ω₀ : Ω), hmem _ ω₀.2⟩, ?_, fun ω hω => ?_⟩
    · change (h * c * h⁻¹) • (h • (ω₀ : Ω)) = h • (ω₀ : Ω)
      rw [mul_smul, mul_smul, inv_smul_smul]
      exact congrArg (h • ·) hω₀
    · have hω' : (h * c * h⁻¹) • (ω : Ω) = ω := hω
      have h1 : c • (h⁻¹ • (ω : Ω)) = h⁻¹ • (ω : Ω) := by
        rw [← mul_smul, show c * h⁻¹ = h⁻¹ * (h * c * h⁻¹) by group, mul_smul, hω']
      have h2 := hu₀ ⟨h⁻¹ • (ω : Ω), hmem' _ ω.2⟩ h1
      apply Subtype.ext
      rw [← h2]
      exact (smul_inv_smul h (ω : Ω)).symm
  have hfix := (C.existsUnique_fixed_piM_iff hS
    ⟨h * c * h⁻¹, C.centralizer_Y_le hS (conj_mem_centralizer hh hc)⟩).mpr hu'
  have hcc : C.piM hS ⟨c * c, mul_mem (C.centralizer_Y_le hS hc) (C.centralizer_Y_le hS hc)⟩ =
      1 := by
    rw [show (⟨c * c, mul_mem (C.centralizer_Y_le hS hc) (C.centralizer_Y_le hS hc)⟩ :
        Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) =
        ⟨c, C.centralizer_Y_le hS hc⟩ * ⟨c, C.centralizer_Y_le hS hc⟩ from rfl, map_mul,
      ← pow_two, ← hc2, pow_orderOf_eq_one]
  have hcc' := (C.piM_eq_one_iff hS _).mp hcc
  have hsq : C.piM hS ⟨h * c * h⁻¹, C.centralizer_Y_le hS (conj_mem_centralizer hh hc)⟩ *
      C.piM hS ⟨h * c * h⁻¹, C.centralizer_Y_le hS (conj_mem_centralizer hh hc)⟩ = 1 := by
    rw [← map_mul, C.piM_eq_one_iff]
    intro ω hω
    have h1 := hcc' (h⁻¹ • ω) (hmem' ω hω)
    change (h * c * h⁻¹ * (h * c * h⁻¹)) • ω = ω
    rw [show h * c * h⁻¹ * (h * c * h⁻¹) = h * (c * c) * h⁻¹ by group, mul_smul, mul_smul, h1,
      smul_inv_smul]
  exact (C.isNaturalSE_Dv C.i).mem_of_existsUnique_fixed (C.piM_mem_normalizer hS _) hsq hfix

theorem conj_mem_Lpre_of_normalizes_Y (hS : Sec4Setting G Ω) {h : G}
    (hh : ∀ y ∈ C.Y, h * y * h⁻¹ ∈ C.Y) {g : G} (hg : g ∈ C.Lpre hS) :
    h * g * h⁻¹ ∈ C.Lpre hS := by
  set Lh : Subgroup G := C.Lpre hS ⊓ (C.Lpre hS).comap (MulAut.conj h).toMonoidHom with hLh
  set T : Subgroup (C.Dv.M C.i) :=
    ((Lh.subgroupOf (Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G))).map
      (C.piM hS)).subgroupOf (C.Dv.M C.i) with hT
  have := C.Dv.isSimpleGroup_M C.i
  obtain ⟨hx1, hx2, -, -⟩ := C.piM_x hS
  have hT : T = ⊤ := by
    rw [eq_top_iff, ← closure_involutions_eq_top (k := ⟨_, hx1⟩) ?_ ?_, Subgroup.closure_le]
    · rintro ⟨m, hm⟩ ⟨hm2, hm1⟩
      have hm2' : m * m = 1 := congrArg Subtype.val hm2
      have hm1' : m ≠ 1 := fun h1 => hm1 (Subtype.ext h1)
      obtain ⟨c, hc, rfl⟩ := C.exists_centralizer_Y_piM_eq hS hm
      have hco : orderOf (C.piM hS ⟨c, C.centralizer_Y_le hS hc⟩) = 2 :=
        orderOf_eq_prime (by rw [pow_two]; exact hm2') hm1'
      refine ⟨⟨c, C.centralizer_Y_le hS hc⟩, ⟨(C.mem_Lpre hS).mpr ⟨hc, hm⟩, ?_⟩, rfl⟩
      exact (C.mem_Lpre hS).mpr ⟨conj_mem_centralizer hh hc,
        C.piM_conj_mem_of_normalizes_Y hS hh hc hm hco⟩
    · have h1 : C.piM hS ⟨C.x, C.x_mem_centralizer hS⟩ ^ 2 = 1 := hx2 ▸ pow_orderOf_eq_one _
      rw [pow_two] at h1
      exact Subtype.ext h1
    · intro h1
      have h2 : C.piM hS ⟨C.x, C.x_mem_centralizer hS⟩ = 1 := congrArg Subtype.val h1
      rw [h2, orderOf_one] at hx2
      exact absurd hx2 (by norm_num)
  obtain ⟨hgY, hgM⟩ := (C.mem_Lpre hS).mp hg
  have hgT : (⟨_, hgM⟩ : C.Dv.M C.i) ∈ T := hT ▸ Subgroup.mem_top _
  obtain ⟨c', hc'L, hc'g⟩ := hgT
  have hc'L' := Subgroup.mem_subgroupOf.mp hc'L
  have hc'Y : (c' : G) ∈ Subgroup.centralizer (C.Y : Set G) := C.Lpre_le hS hc'L'.1
  have hpY : (c' : G)⁻¹ * g ∈ Subgroup.centralizer (C.Y : Set G) := mul_mem (inv_mem hc'Y) hgY
  have hpP : (c' : G)⁻¹ * g ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) := by
    have h1 : C.piM hS ⟨(c' : G)⁻¹ * g, C.centralizer_Y_le hS hpY⟩ = 1 := by
      rw [show (⟨(c' : G)⁻¹ * g, C.centralizer_Y_le hS hpY⟩ :
          Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) =
          c'⁻¹ * ⟨g, C.centralizer_Y_le hS hgY⟩ from rfl, map_mul, map_inv, hc'g]
      exact inv_mul_cancel _
    exact (mem_fixingSubgroup_iff G).mpr ((C.piM_eq_one_iff hS _).mp h1)
  have hhp : h * ((c' : G)⁻¹ * g) * h⁻¹ ∈ C.Lpre hS :=
    C.mem_Lpre_of_mem_fixingSubgroup hS (conj_mem_centralizer hh hpY)
      ((mem_fixingSubgroup_iff_conj (C.smul_fixSet_eq_of_normalizes_Y hS hh) _).mp hpP)
  have hhc : h * (c' : G) * h⁻¹ ∈ C.Lpre hS := by simpa using hc'L'.2
  have := mul_mem hhc hhp
  rwa [show h * (c' : G) * h⁻¹ * (h * ((c' : G)⁻¹ * g) * h⁻¹) = h * g * h⁻¹ by group] at this

end Lpre

end FinConfig

namespace FinConfig

section Dsub

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)


@[expose] noncomputable def Dsub (hS : Sec4Setting G Ω) : Subgroup G :=
  ⁅C.Lpre hS, C.Lpre hS⁆ ⊔ (Subgroup.centralizer (C.Y : Set G) ⊓
    oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))))

theorem conj_mem_centralizer_inf_fixCore (hS : Sec4Setting G Ω) {c : G}
    (hc : c ∈ Subgroup.centralizer (C.Y : Set G)) {o : G}
    (ho : o ∈ Subgroup.centralizer (C.Y : Set G) ⊓
      oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)))) :
    c * o * c⁻¹ ∈ Subgroup.centralizer (C.Y : Set G) ⊓
      oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) :=
  Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hc (Subgroup.mem_inf.mp ho).1) (inv_mem hc),
    conj_mem_fixCore (smul_fixSet_eq_of_mem_centralizer (C.centralizer_Y_le hS hc))
      (Subgroup.mem_inf.mp ho).2⟩

theorem centralizer_inf_fixCore_le_Lpre (hS : Sec4Setting G Ω) :
    Subgroup.centralizer (C.Y : Set G) ⊓
      oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) ≤ C.Lpre hS :=
  fun _ ho => C.mem_Lpre_of_mem_fixingSubgroup hS (Subgroup.mem_inf.mp ho).1
    (Subgroup.map_subtype_le _ (Subgroup.mem_inf.mp ho).2)

theorem Dsub_le_Lpre (hS : Sec4Setting G Ω) : C.Dsub hS ≤ C.Lpre hS :=
  sup_le (Subgroup.commutator_le_self _) (C.centralizer_inf_fixCore_le_Lpre hS)

theorem exists_commutator_piM_eq (hS : Sec4Setting G Ω) {m : Equiv.Perm (C.Dv.Ψc C.i)}
    (hm : m ∈ C.Dv.M C.i) :
    ∃ d, ∃ hd : d ∈ ⁅C.Lpre hS, C.Lpre hS⁆,
      C.piM hS ⟨d, C.centralizer_Y_le hS (C.Lpre_le hS (Subgroup.commutator_le_self _ hd))⟩ =
        m := by
  set A : Subgroup (Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) :=
    (C.Lpre hS).subgroupOf (Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G))
  have hA : A.map (C.piM hS) = C.Dv.M C.i := by
    ext m'
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨hY, hM⟩ := (C.mem_Lpre hS).mp (Subgroup.mem_subgroupOf.mp ha)
      exact hM
    · intro hm'
      obtain ⟨c, hc, rfl⟩ := C.exists_centralizer_Y_piM_eq hS hm'
      exact ⟨_, Subgroup.mem_subgroupOf.mpr ((C.mem_Lpre hS).mpr ⟨hc, hm'⟩), rfl⟩
  have := C.Dv.isPerfect_M C.i
  have hcomm : (⁅A, A⁆).map (C.piM hS) = C.Dv.M C.i := by
    rw [Subgroup.map_commutator, hA, Subgroup.commutator_eq_self]
  rw [← hcomm] at hm
  obtain ⟨a, ha, rfl⟩ := hm
  have hLv : C.Lpre hS ≤ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) :=
    (C.Lpre_le hS).trans (C.centralizer_Y_le hS)
  have hmap : (⁅A, A⁆).map (Subgroup.centralizer
      ((Subgroup.zpowers v : Subgroup G) : Set G)).subtype = ⁅C.Lpre hS, C.Lpre hS⁆ := by
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hLv]
  have had : (a : G) ∈ ⁅C.Lpre hS, C.Lpre hS⁆ := hmap ▸ ⟨a, ha, rfl⟩
  exact ⟨a, had, rfl⟩

theorem exists_decomp (hS : Sec4Setting G Ω) {g : G} (hg : g ∈ C.Lpre hS) :
    ∃ d ∈ ⁅C.Lpre hS, C.Lpre hS⁆, ∃ z ∈ C.Z, z⁻¹ * (d⁻¹ * g) ∈
      Subgroup.centralizer (C.Y : Set G) ⊓
        oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) := by
  obtain ⟨hgY, hgM⟩ := (C.mem_Lpre hS).mp hg
  obtain ⟨d, hd, hdg⟩ := C.exists_commutator_piM_eq hS hgM
  have hdY := C.Lpre_le hS (Subgroup.commutator_le_self _ hd)
  have hpY : d⁻¹ * g ∈ Subgroup.centralizer (C.Y : Set G) := mul_mem (inv_mem hdY) hgY
  have hpP : d⁻¹ * g ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) := by
    have h1 : C.piM hS ⟨d⁻¹ * g, C.centralizer_Y_le hS hpY⟩ = 1 := by
      rw [show (⟨d⁻¹ * g, C.centralizer_Y_le hS hpY⟩ :
          Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) =
          (⟨d, C.centralizer_Y_le hS hdY⟩)⁻¹ * ⟨g, C.centralizer_Y_le hS hgY⟩ from rfl, map_mul,
        map_inv, hdg, inv_mul_cancel]
    exact (mem_fixingSubgroup_iff G).mpr ((C.piM_eq_one_iff hS _).mp h1)
  obtain ⟨z, hz, hzq⟩ := C.exists_mem_Z_inv_mul_mem hS hpY hpP
  have hzY : z ∈ Subgroup.centralizer (C.Y : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy => (C.commute_of_mem_Z hS hz hy).symm
  exact ⟨d, hd, z, hz, Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hzY) hpY, hzq⟩⟩

theorem conj_mem_Dsub_of_normalizes_Y (hS : Sec4Setting G Ω) {h : G}
    (hh : ∀ y ∈ C.Y, h * y * h⁻¹ ∈ C.Y) {g : G} (hg : g ∈ C.Dsub hS) :
    h * g * h⁻¹ ∈ C.Dsub hS :=
  conj_mem_commutator_sup (fun _ hl => C.conj_mem_Lpre_of_normalizes_Y hS hh hl)
    (fun _ ho => Subgroup.mem_inf.mpr ⟨conj_mem_centralizer hh (Subgroup.mem_inf.mp ho).1,
      conj_mem_fixCore (C.smul_fixSet_eq_of_normalizes_Y hS hh) (Subgroup.mem_inf.mp ho).2⟩) hg

theorem conj_mem_Dsub (hS : Sec4Setting G Ω) {c : G}
    (hc : c ∈ Subgroup.centralizer (C.Y : Set G)) {g : G} (hg : g ∈ C.Dsub hS) :
    c * g * c⁻¹ ∈ C.Dsub hS :=
  conj_mem_commutator_sup (fun _ hl => C.conj_mem_Lpre hS hc hl)
    (fun _ ho => C.conj_mem_centralizer_inf_fixCore hS hc ho) hg

theorem Dsub_dichotomy (hS : Sec4Setting G Ω) :
    (∀ z ∈ C.Z, z ∈ C.Dsub hS → z = 1) ∨ ∀ z ∈ C.Z, z ∈ C.Dsub hS := by
  by_cases hall : ∀ z ∈ C.Z, z ∈ C.Dsub hS
  · exact Or.inr hall
  · refine Or.inl fun a haZ haD => ?_
    by_contra ha1
    refine hall fun b hbZ => ?_
    by_cases hb1 : b = 1
    · rw [hb1]
      exact one_mem _
    obtain ⟨h, -, hhY, hab⟩ := C.exists_conj_eq_of_mem_Z hS haZ ha1 hbZ hb1
    exact hab ▸ C.conj_mem_Dsub_of_normalizes_Y hS hhY haD

end Dsub

section Facts

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)


theorem Z_le_centralizer_Y (hS : Sec4Setting G Ω) :
    C.Z ≤ Subgroup.centralizer (C.Y : Set G) := fun _ hz =>
  Subgroup.mem_centralizer_iff.mpr fun _ hy => (C.commute_of_mem_Z hS hz hy).symm

theorem Z_le_Lpre (hS : Sec4Setting G Ω) : C.Z ≤ C.Lpre hS := fun _ hz =>
  C.mem_Lpre_of_mem_fixingSubgroup hS (C.Z_le_centralizer_Y hS hz) (C.Z_le_fixingSubgroup hS hz)

theorem x_mem_centralizer_Y (hS : Sec4Setting G Ω) :
    C.x ∈ Subgroup.centralizer (C.Y : Set G) :=
  Subgroup.mem_centralizer_iff.mpr fun _ hy => (C.commute_x hS hy).symm

theorem x_mem_Lpre (hS : Sec4Setting G Ω) : C.x ∈ C.Lpre hS :=
  (C.mem_Lpre hS).mpr ⟨C.x_mem_centralizer_Y hS, (C.piM_x hS).1⟩

theorem four_le_card_Z (hS : Sec4Setting G Ω) : 4 ≤ Nat.card C.Z := by
  obtain ⟨n, i, e, hA⟩ := C.isNaturalSE_N.exists_isBenderAction
  rw [C.card_Z hS]
  exact (hA.card_rootCenter_seRadical C.bγ).symm ▸ hA.four_le_q

theorem exists_mem_Z_ne_one (hS : Sec4Setting G Ω) : ∃ z ∈ C.Z, z ≠ 1 := by
  have h1 : C.Z ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot _).mp (by
    have := C.four_le_card_Z hS
    omega)
  obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h1
  exact ⟨z, hz, fun h => hz1 (Subtype.ext h)⟩

theorem exists_mem_Z_ne_one_ne (hS : Sec4Setting G Ω) (z : G) :
    ∃ z' ∈ C.Z, z' ≠ 1 ∧ z' ≠ z := by
  by_contra hcon
  have hsub : ∀ z' ∈ C.Z, z' ∈ ({1, z} : Set G) := fun z' hz' => by
    by_contra hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
    exact hcon ⟨z', hz', hne⟩
  have h1 : Nat.card C.Z ≤ Nat.card ({1, z} : Set G) :=
    Nat.card_le_card_of_injective (fun z' : C.Z => (⟨z', hsub z' z'.2⟩ : ({1, z} : Set G)))
      fun a b h => Subtype.ext (congrArg (fun s : ({1, z} : Set G) => (s : G)) h)
  have h2 : Nat.card ({1, z} : Set G) ≤ 2 := by
    rw [Nat.card_coe_set_eq]
    exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  have := C.four_le_card_Z hS
  omega

end Facts

end FinConfig

end CFSG.Holt.H78

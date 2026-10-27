module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4G2Setup
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4N0StructOdd

public section

namespace CFSG.OddStandard.AltStdSmall4.G2

open Subgroup Matrix
open scoped Pointwise

section Growth

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_normalizer_not_mem_of_lt {X S : Subgroup G} (hS : IsPGroup 2 S) (hXS : X ≤ S)
    (hlt : Nat.card X < Nat.card S) : ∃ y ∈ S, y ∈ normalizer (X : Set G) ∧ y ∉ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent S := hS.isNilpotent
  have hlt' : X.subgroupOf S < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => ?_
    have hSX : S ≤ X := fun s hs => by
      have : (⟨s, hs⟩ : S) ∈ X.subgroupOf S := by
        rw [htop]
        trivial
      exact this
    have := Subgroup.card_le_of_le hSX
    omega
  obtain ⟨⟨y, hyS⟩, hyN, hyX⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (X.subgroupOf S) hlt')
  refine ⟨y, hyS, mem_normalizer_iff.2 fun h => ⟨fun hh => ?_, fun hh => ?_⟩, fun h => hyX h⟩
  · exact (mem_normalizer_iff.1 hyN ⟨h, hXS hh⟩).1 hh
  · have hhS : h ∈ S := by
      rw [show h = y⁻¹ * (y * h * y⁻¹) * y by group]
      exact S.mul_mem (S.mul_mem (S.inv_mem hyS) (hXS hh)) hyS
    exact (mem_normalizer_iff.1 hyN ⟨h, hhS⟩).2 hh

theorem exists_pgroup_le {H X P : Subgroup G} (hX : X ≤ H) (hXp : IsPGroup 2 X) (hP : P ≤ H)
    (hPp : IsPGroup 2 P) :
    ∃ S : Subgroup G, S ≤ H ∧ IsPGroup 2 S ∧ X ≤ S ∧ Nat.card P ≤ Nat.card S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX' : IsPGroup 2 (X.subgroupOf H) := hXp.of_equiv (subgroupOfEquivOfLe hX).symm
  have hP' : IsPGroup 2 (P.subgroupOf H) := hPp.of_equiv (subgroupOfEquivOfLe hP).symm
  obtain ⟨S₂, hS₂⟩ := hX'.exists_le_sylow
  obtain ⟨S₁, hS₁⟩ := hP'.exists_le_sylow
  refine ⟨(S₂ : Subgroup H).map H.subtype, map_subtype_le _, S₂.isPGroup'.map _, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hX hx⟩, hS₂ hx, rfl⟩
  · rw [card_map_of_injective H.subtype_injective,
      ← Nat.card_congr (subgroupOfEquivOfLe hP).toEquiv, Sylow.card_eq_multiplicity S₂,
      ← Sylow.card_eq_multiplicity S₁]
    exact Subgroup.card_le_of_le hS₁

end Growth

section Conj

variable {G : Type} [Group G] {z : G}

theorem beta_conj_of_comm {κ : G} (hκz : κ * z = z * κ) (r : G) :
    κ * r * κ⁻¹ * z * (κ * r * κ⁻¹)⁻¹ * z⁻¹ = κ * (r * z * r⁻¹ * z⁻¹) * κ⁻¹ := by
  have hκz' : κ⁻¹ * z = z * κ⁻¹ := by
    calc κ⁻¹ * z = κ⁻¹ * (z * κ) * κ⁻¹ := by group
      _ = κ⁻¹ * (κ * z) * κ⁻¹ := by rw [hκz]
      _ = z * κ⁻¹ := by group
  calc κ * r * κ⁻¹ * z * (κ * r * κ⁻¹)⁻¹ * z⁻¹
      = κ * r * (κ⁻¹ * z) * κ * r⁻¹ * κ⁻¹ * z⁻¹ := by group
    _ = κ * r * (z * κ⁻¹) * κ * r⁻¹ * κ⁻¹ * z⁻¹ := by rw [hκz']
    _ = κ * (r * z * r⁻¹ * (κ⁻¹ * z⁻¹)) := by group
    _ = κ * (r * z * r⁻¹ * (z⁻¹ * κ⁻¹)) := by
        rw [show κ⁻¹ * z⁻¹ = z⁻¹ * κ⁻¹ by
          rw [← _root_.mul_inv_rev, ← _root_.mul_inv_rev, hκz]]
    _ = κ * (r * z * r⁻¹ * z⁻¹) * κ⁻¹ := by group

theorem betaHat_conj_of_comm {k : ℕ} {κ : G} (hκz : κ * z = z * κ) (r : G) :
    betaHat k z (κ * r * κ⁻¹) = κ * betaHat k z r * κ⁻¹ := by
  rw [betaHat, beta_conj_of_comm hκz, conj_pow]
  rfl

variable {L A : Subgroup G}

theorem KA_le_normalizer : KA L z A ≤ normalizer (A : Set G) := fun _ h =>
  (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 h).1).1

theorem KA_le_centralizer : KA L z A ≤ centralizer ({z} : Set G) := fun _ h =>
  (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 h).1).2

theorem KA_le_Lfree : KA L z A ≤ Lfree L z := fun _ h => (Subgroup.mem_inf.1 h).2

end Conj

section Beta

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G} {k : ℕ} {A : Subgroup G}
  (c : Config G L Q n θ z) (h : LevelDatum θ c.hn8 z k A)
include c h

theorem RA_le_normalizer : RA θ c.hn8 z A ≤ normalizer (A : Set G) := fun _ hr =>
  h.normalizer_sup_le (z_mul_self c) (Subgroup.mem_inf.1 hr).1

omit h in
theorem RA_le_centralizer_E : RA θ c.hn8 z A ≤ centralizer (E θ c.hn8 : Set G) := fun _ hr =>
  (Subgroup.mem_inf.1 hr).2

theorem z_mem_centralizer_E : z ∈ centralizer (E θ c.hn8 : Set G) := by
  rw [mem_centralizer_iff]
  intro e he
  exact (N0.comm_z_of_mem_L c (ModIso.E_le_L c.hn8 he))

theorem sup_le_RA : A ⊔ zpowers z ≤ RA θ c.hn8 z A := by
  refine le_inf Subgroup.le_normalizer (sup_le h.le_centralizer_E ?_)
  rw [zpowers_le]
  exact z_mem_centralizer_E c h

theorem conj_z_not_mem (r : G) : r * z * r⁻¹ ∉ A := by
  intro hr
  have h2 : (r * z * r⁻¹) ^ 2 = 1 := by
    rw [conj_pow, sq, z_mul_self c, mul_one, mul_inv_cancel]
  have hE := (h.mem_E_iff_sq_eq_one hr).2 h2
  exact N0.conj_z_not_mem_L c r (ModIso.E_le_L c.hn8 hE)

theorem beta_mem {r : G} (hr : r ∈ RA θ c.hn8 z A) : r * z * r⁻¹ * z⁻¹ ∈ A := by
  have h1 : r * z * r⁻¹ ∈ A ⊔ zpowers z :=
    (mem_normalizer_iff.1 (Subgroup.mem_inf.1 hr).1 z).1 (mem_sup_right (mem_zpowers z))
  rcases (h.mem_sup_iff (z_mul_self c)).1 h1 with h2 | h2
  · exact absurd h2 (conj_z_not_mem c h r)
  · rwa [z_inv c]

theorem betaHat_mem_E {r : G} (hr : r ∈ RA θ c.hn8 z A) : betaHat k z r ∈ E θ c.hn8 :=
  h.pow_mem_E (beta_mem c h hr)

omit c h in
theorem betaHat_one : betaHat k z (1 : G) = 1 := by
  simp [betaHat]

theorem betaHat_mul {r s : G} (hr : r ∈ RA θ c.hn8 z A) (hs : s ∈ RA θ c.hn8 z A) :
    betaHat k z (r * s) = betaHat k z r * betaHat k z s := by
  have hrN := RA_le_normalizer c h hr
  have hbs := beta_mem c h hs
  have hbr := beta_mem c h hr
  have h1 : r * s * z * (r * s)⁻¹ * z⁻¹ =
      (r * (s * z * s⁻¹ * z⁻¹) * r⁻¹) * (r * z * r⁻¹ * z⁻¹) := by group
  have hcs : r * (s * z * s⁻¹ * z⁻¹) * r⁻¹ ∈ A := (mem_normalizer_iff.1 hrN _).1 hbs
  rw [betaHat, h1, (Commute.mul_pow (h.comm hcs hbr) _), conj_pow]
  have hE := betaHat_mem_E c h hs
  have hrE : r * betaHat k z s * r⁻¹ = betaHat k z s := by
    have := mem_centralizer_iff.1 (RA_le_centralizer_E c hr) _ hE
    rw [← this, mul_inv_cancel_right]
  rw [show (s * z * s⁻¹ * z⁻¹) ^ 2 ^ (k - 1) = betaHat k z s from rfl, hrE,
    show (r * z * r⁻¹ * z⁻¹) ^ 2 ^ (k - 1) = betaHat k z r from rfl]
  exact E_comm θ c.hn8 hE (betaHat_mem_E c h hr)

theorem betaHat_pow {r : G} (hr : r ∈ RA θ c.hn8 z A) (m : ℕ) :
    betaHat k z (r ^ m) = betaHat k z r ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, betaHat_one]
  | succ m ih => rw [pow_succ, betaHat_mul c h (pow_mem hr m) hr, ih, pow_succ]

@[expose] noncomputable def betaHom : RA θ c.hn8 z A →* G where
  toFun r := betaHat k z r
  map_one' := betaHat_one
  map_mul' r s := betaHat_mul c h r.2 s.2

theorem KA_conj_mem_E {κ : G} (hκ : κ ∈ KA L z A) {e : G} (he : e ∈ E θ c.hn8) :
    κ * e * κ⁻¹ ∈ E θ c.hn8 := by
  have hκN : κ ∈ normalizer (A : Set G) := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hκ).1).1
  have h1 : κ * e * κ⁻¹ ∈ A := (mem_normalizer_iff.1 hκN e).1 (h.E_le he)
  rw [h.mem_E_iff_sq_eq_one h1, conj_pow, sq_eq_one_of_mem_E θ c.hn8 he, mul_one,
    mul_inv_cancel]

theorem KA_conj_mem_RA {κ : G} (hκ : κ ∈ KA L z A) {r : G} (hr : r ∈ RA θ c.hn8 z A) :
    κ * r * κ⁻¹ ∈ RA θ c.hn8 z A := by
  have hκN : κ ∈ normalizer (A : Set G) := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hκ).1).1
  have hκz : κ * z = z * κ :=
    mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hκ).1).2
  have hκNz : κ ∈ normalizer ((A ⊔ zpowers z : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    rw [h.mem_sup_iff (z_mul_self c), h.mem_sup_iff (z_mul_self c)]
    have e : κ * x * κ⁻¹ * z = κ * (x * z) * κ⁻¹ := by
      calc κ * x * κ⁻¹ * z = κ * x * (κ⁻¹ * (z * κ)) * κ⁻¹ := by group
        _ = κ * x * (κ⁻¹ * (κ * z)) * κ⁻¹ := by rw [hκz]
        _ = κ * (x * z) * κ⁻¹ := by group
    rw [e, ← mem_normalizer_iff.1 hκN, ← mem_normalizer_iff.1 hκN]
  have hrN := (Subgroup.mem_inf.1 hr).1
  refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hκNz hrN) (inv_mem hκNz), ?_⟩
  rw [mem_centralizer_iff]
  intro e he
  have hκ' : κ⁻¹ ∈ KA L z A := inv_mem hκ
  have he' : κ⁻¹ * e * κ⁻¹⁻¹ ∈ E θ c.hn8 := KA_conj_mem_E c h hκ' he
  rw [inv_inv] at he'
  have hre := mem_centralizer_iff.1 (RA_le_centralizer_E c hr) _ he'
  calc e * (κ * r * κ⁻¹) = κ * ((κ⁻¹ * e * κ) * r) * κ⁻¹ := by group
    _ = κ * (r * (κ⁻¹ * e * κ)) * κ⁻¹ := by rw [hre]
    _ = κ * r * κ⁻¹ * e := by group

theorem betaHat_conj {κ : G} (hκ : κ ∈ KA L z A) (r : G) :
    betaHat k z (κ * r * κ⁻¹) = κ * betaHat k z r * κ⁻¹ :=
  betaHat_conj_of_comm (mem_centralizer_singleton_iff.1 (KA_le_centralizer hκ)) r

theorem betaHat_inv {r : G} (hr : r ∈ RA θ c.hn8 z A) :
    betaHat k z r⁻¹ = (betaHat k z r)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← betaHat_mul c h (inv_mem hr) hr, inv_mul_cancel, betaHat_one]

theorem pow_beta_of_mem {a : G} (ha : a ∈ A) : (a * z * a⁻¹ * z⁻¹) ^ 2 ^ (k - 1) = 1 := by
  have hk := h.two_le
  have e : a * z * a⁻¹ * z⁻¹ = a * (z * a⁻¹ * z⁻¹) := by group
  have hsq : (a ^ 2) ^ 2 ^ (k - 1) = 1 := by
    rw [← pow_mul, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ k)]
    exact h.pow_two_pow ha
  rcases h.zact with h1 | ⟨hk3, h1⟩
  · rw [e, h1 _ (inv_mem ha), inv_inv, ← sq]
    exact hsq
  · have hw : a * (z * a⁻¹ * z⁻¹) = a ^ 2 * (a ^ 2 ^ (k - 1))⁻¹ := by
      rw [h1 _ (inv_mem ha), inv_inv, inv_pow, ← mul_assoc, ← sq]
    have hc : Commute (a ^ 2) (a ^ 2 ^ (k - 1))⁻¹ := (Commute.pow_pow_self a 2 _).inv_right
    rw [e, hw, hc.mul_pow, hsq, one_mul, inv_pow, ← pow_mul]
    have e2 : 2 ^ (k - 1) * 2 ^ (k - 1) = 2 ^ k * 2 ^ (k - 2) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    rw [e2, pow_mul, h.pow_two_pow ha, one_pow, inv_one]

theorem exists_beta_eq_sq {b : G} (hb : b ∈ A) : ∃ a ∈ A, a * z * a⁻¹ * z⁻¹ = b ^ 2 := by
  have hk := h.two_le
  rcases h.zact with h1 | ⟨hk3, h1⟩
  · refine ⟨b, hb, ?_⟩
    have e : b * z * b⁻¹ * z⁻¹ = b * (z * b⁻¹ * z⁻¹) := by group
    rw [e, h1 _ (inv_mem hb), inv_inv, sq]
  · set a := b * b ^ 2 ^ (k - 2) with ha
    have haA : a ∈ A := mul_mem hb (pow_mem hb _)
    have hcb : Commute b (b ^ 2 ^ (k - 2)) := Commute.self_pow b _
    have hpow : ∀ m, a ^ m = b ^ m * b ^ (2 ^ (k - 2) * m) := fun m => by
      rw [ha, hcb.mul_pow, ← pow_mul]
    refine ⟨a, haA, ?_⟩
    have e : a * z * a⁻¹ * z⁻¹ = a * (z * a⁻¹ * z⁻¹) := by group
    have hw : a * (z * a⁻¹ * z⁻¹) = a ^ 2 * (a ^ 2 ^ (k - 1))⁻¹ := by
      rw [h1 _ (inv_mem haA), inv_inv, inv_pow, ← mul_assoc, ← sq]
    have h2 : a ^ 2 = b ^ 2 * b ^ 2 ^ (k - 1) := by
      rw [hpow, ← pow_succ, show k - 2 + 1 = k - 1 by omega]
    have h3 : a ^ 2 ^ (k - 1) = b ^ 2 ^ (k - 1) := by
      have e2 : 2 ^ (k - 2) * 2 ^ (k - 1) = 2 ^ k * 2 ^ (k - 3) := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      rw [hpow, e2, pow_mul, h.pow_two_pow hb, one_pow, mul_one]
    rw [e, hw, h2, h3, mul_inv_cancel_right]

theorem betaHat_eq_one_iff {r : G} (hr : r ∈ RA θ c.hn8 z A) :
    betaHat k z r = 1 ↔ ∃ a ∈ A, a⁻¹ * r ∈ centralizer ({z} : Set G) := by
  have hβ := beta_mem c h hr
  constructor
  · intro h1
    obtain ⟨b, hb, hb2⟩ := (h.pow_eq_one_iff_sq hβ).1 h1
    obtain ⟨a, ha, hab⟩ := exists_beta_eq_sq c h hb
    refine ⟨a, ha, ?_⟩
    rw [mem_centralizer_singleton_iff]
    have e : r * z * r⁻¹ = a * z * a⁻¹ := (mul_right_cancel (hab.trans hb2)).symm
    calc a⁻¹ * r * z = a⁻¹ * (r * z * r⁻¹) * r := by group
      _ = a⁻¹ * (a * z * a⁻¹) * r := by rw [e]
      _ = z * (a⁻¹ * r) := by group
  · rintro ⟨a, ha, hc⟩
    have hc' := mem_centralizer_singleton_iff.1 hc
    have e : r * z * r⁻¹ * z⁻¹ = a * z * a⁻¹ * z⁻¹ := by
      calc r * z * r⁻¹ * z⁻¹ = a * (a⁻¹ * r * z) * r⁻¹ * z⁻¹ := by group
        _ = a * (z * (a⁻¹ * r)) * r⁻¹ * z⁻¹ := by rw [hc']
        _ = a * z * a⁻¹ * z⁻¹ := by group
    rw [betaHat, e]
    exact pow_beta_of_mem c h ha

theorem betaHat_eq_one_of_mem_sup {x : G} (hx : x ∈ A ⊔ zpowers z) : betaHat k z x = 1 := by
  refine (betaHat_eq_one_iff c h (sup_le_RA c h hx)).2 ?_
  rcases (h.mem_sup_iff (z_mul_self c)).1 hx with hxA | hxA
  · exact ⟨x, hxA, by rw [inv_mul_cancel]; exact one_mem _⟩
  · refine ⟨x * z, hxA, ?_⟩
    rw [show (x * z)⁻¹ * x = z⁻¹ by group]
    exact inv_mem (mem_centralizer_singleton_iff.2 rfl)

omit h in
theorem mem_of_two_pow_RA {r : G} (hr : r ∈ RA θ c.hn8 z A)
    (hrz : r ∈ centralizer ({z} : Set G)) {j : ℕ} (hj : r ^ 2 ^ j = 1) :
    r ∈ E θ c.hn8 ⊔ zpowers z := by
  have hC0 : r ∈ N0.C0 θ c.hn8 z := by
    rw [N0.mem_C0_iff c.hn8 c]
    exact ⟨(N0.mem_centralizer_E_iff θ c.hn8 r).1 (RA_le_centralizer_E c hr),
      mem_centralizer_singleton_iff.1 hrz⟩
  exact N0.mem_B0_of_two_pow c.hn8 c hC0 hj

theorem mem_sup_of_betaHat_eq_one {S : Subgroup G} (hSR : S ≤ RA θ c.hn8 z A)
    (hSp : IsPGroup 2 S) (hAS : A ≤ S) {r : G} (hr : r ∈ S) (hr1 : betaHat k z r = 1) :
    r ∈ A ⊔ zpowers z := by
  obtain ⟨a, ha, haz⟩ := (betaHat_eq_one_iff c h (hSR hr)).1 hr1
  have har : a⁻¹ * r ∈ S := mul_mem (inv_mem (hAS ha)) hr
  obtain ⟨j, hj⟩ := hSp ⟨a⁻¹ * r, har⟩
  have hj' : (a⁻¹ * r) ^ 2 ^ j = 1 := by
    have := congrArg Subtype.val hj
    simpa using this
  have h1 := mem_of_two_pow_RA c (hSR har) haz hj'
  rw [show r = a * (a⁻¹ * r) by group]
  exact mul_mem (mem_sup_left ha) ((sup_le_sup_right h.E_le _) h1)

theorem isPGroup_sup : IsPGroup 2 (A ⊔ zpowers z : Subgroup G) :=
  IsPGroup.of_card (n := 3 * k + 1) (by rw [h.card_sup (z_mul_self c), h.card]; ring)

theorem terminal_or_onto :
    Terminal θ c.hn8 A ∨ ∀ e ∈ E θ c.hn8, ∃ r ∈ RA θ c.hn8 z A, betaHat k z r = e := by
  set W : Set (Fin 3 → ZMod 2) :=
    {v | ∃ r ∈ RA θ c.hn8 z A, betaHat k z r = epsV θ c.hn8 v} with hW
  have hW0 : (0 : Fin 3 → ZMod 2) ∈ W := ⟨1, one_mem _, by rw [betaHat_one, epsV_zero]⟩
  have hWM : ∀ M : GL (Fin 3) (ZMod 2), ∀ v ∈ W,
      (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v ∈ W := by
    rintro M v ⟨r, hr, hrv⟩
    obtain ⟨κ, hκ, hκv⟩ := h.cover M
    exact ⟨κ * r * κ⁻¹, KA_conj_mem_RA c h hκ hr, by rw [betaHat_conj c h hκ, hrv, hκv]⟩
  rcases IRR_of_zero_mem W hW0 (hWM x2G) (hWM y2G) with h0 | hall
  · left
    intro P hP hPE
    by_contra hlt
    push Not at hlt
    have hX : A ⊔ zpowers z ≤ centralizer (E θ c.hn8 : Set G) :=
      (sup_le_RA c h).trans inf_le_right
    obtain ⟨S, hSE, hSp, hXS, hPS⟩ := exists_pgroup_le hX (isPGroup_sup c h) hPE hP
    have hlt' : Nat.card (A ⊔ zpowers z : Subgroup G) < Nat.card S := by
      rw [h.card_sup (z_mul_self c)]
      omega
    obtain ⟨y, hyS, hyN, hyX⟩ := exists_mem_normalizer_not_mem_of_lt hSp hXS hlt'
    have hyR : y ∈ RA θ c.hn8 z A := Subgroup.mem_inf.2 ⟨hyN, hSE hyS⟩
    obtain ⟨v, hv⟩ := (mem_E_iff_epsV θ c.hn8 _).1 (betaHat_mem_E c h hyR)
    have hv0 : v = 0 := h0 v ⟨y, hyR, hv.symm⟩
    rw [hv0, epsV_zero] at hv
    have hSR : S ⊓ RA θ c.hn8 z A ≤ RA θ c.hn8 z A := inf_le_right
    have hSRp : IsPGroup 2 (S ⊓ RA θ c.hn8 z A : Subgroup G) := hSp.to_le inf_le_left
    have hASR : A ≤ S ⊓ RA θ c.hn8 z A :=
      le_inf (le_sup_left.trans hXS) (le_sup_left.trans (sup_le_RA c h))
    exact hyX (mem_sup_of_betaHat_eq_one c h hSR hSRp hASR ⟨hyS, hyR⟩ hv.symm)
  · right
    intro e he
    obtain ⟨v, rfl⟩ := (mem_E_iff_epsV θ c.hn8 e).1 he
    exact hall v

theorem exists_P (hT : ¬ Terminal θ c.hn8 A) :
    ∃ P : Subgroup G, P ≤ RA θ c.hn8 z A ∧ IsPGroup 2 P ∧ A ⊔ zpowers z ≤ P ∧
      (∀ e ∈ E θ c.hn8, ∃ p ∈ P, betaHat k z p = e) ∧
      (∀ p ∈ P, betaHat k z p = 1 → p ∈ A ⊔ zpowers z) ∧ Nat.card P = 16 * Nat.card A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have honto := (terminal_or_onto c h).resolve_left hT
  set R := RA θ c.hn8 z A with hR
  have hXR : A ⊔ zpowers z ≤ R := sup_le_RA c h
  have hX' : IsPGroup 2 ((A ⊔ zpowers z).subgroupOf R) :=
    (isPGroup_sup c h).of_equiv (subgroupOfEquivOfLe hXR).symm
  obtain ⟨S, hS⟩ := hX'.exists_le_sylow
  set P := (S : Subgroup R).map R.subtype with hP
  have hPR : P ≤ R := map_subtype_le _
  have hPp : IsPGroup 2 P := S.isPGroup'.map _
  have hXP : A ⊔ zpowers z ≤ P := fun x hx => ⟨⟨x, hXR hx⟩, hS hx, rfl⟩
  have hker : ∀ p ∈ P, betaHat k z p = 1 → p ∈ A ⊔ zpowers z := fun p hp hp1 =>
    mem_sup_of_betaHat_eq_one c h hPR hPp (le_sup_left.trans hXP) hp hp1
  have honto' : ∀ e ∈ E θ c.hn8, ∃ p ∈ P, betaHat k z p = e := by
    intro e he
    obtain ⟨r, hr, hre⟩ := honto e he
    obtain ⟨a, m, hm, hrm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos r).ne'
    have hr'R : r ^ m ∈ R := pow_mem hr m
    have hr'2 : (r ^ m) ^ 2 ^ a = 1 := by
      rw [← pow_mul, mul_comm, ← hrm, pow_orderOf_eq_one]
    have hβr' : betaHat k z (r ^ m) = e := by
      rw [betaHat_pow c h hr, hre]
      obtain ⟨t, rfl⟩ := hm
      rw [pow_succ, pow_mul, sq_eq_one_of_mem_E θ c.hn8 he, one_pow, one_mul]
    have hr'p : IsPGroup 2 (zpowers (⟨r ^ m, hr'R⟩ : R)) := by
      have h1 : (⟨r ^ m, hr'R⟩ : R) ^ 2 ^ a = 1 := Subtype.ext (by simpa using hr'2)
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h1)
      exact IsPGroup.of_card (by rw [Nat.card_zpowers, hi])
    obtain ⟨S₁, hS₁⟩ := hr'p.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq R S₁ S
    have hgr : g * (⟨r ^ m, hr'R⟩ : R) * g⁻¹ ∈ (S : Subgroup R) := by
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨_, hS₁ (mem_zpowers _), by simp [MulAut.conj_apply]⟩
    refine ⟨(g : G) * r ^ m * (g : G)⁻¹, ⟨_, hgr, rfl⟩, ?_⟩
    have hg1 : betaHat k z (g : G)⁻¹ = (betaHat k z (g : G))⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← betaHat_mul c h (inv_mem g.2) g.2, inv_mul_cancel,
        betaHat_one]
    rw [betaHat_mul c h (mul_mem g.2 hr'R) (inv_mem g.2), betaHat_mul c h g.2 hr'R, hβr', hg1,
      E_comm θ c.hn8 (betaHat_mem_E c h g.2) he, mul_inv_cancel_right]
  refine ⟨P, hPR, hPp, hXP, honto', hker, ?_⟩
  set f := (betaHom c h).comp (Subgroup.inclusion hPR) with hf
  have hfker : f.ker = (A ⊔ zpowers z).subgroupOf P := by
    ext p
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact ⟨hker p p.2, betaHat_eq_one_of_mem_sup c h⟩
  have hfrange : f.range = E θ c.hn8 := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact betaHat_mem_E c h (hPR p.2)
    · intro hx
      obtain ⟨p, hp, hpx⟩ := honto' x hx
      exact ⟨⟨p, hp⟩, hpx⟩
  have hcard := Subgroup.card_ker_mul_card_range f
  rw [hfker, hfrange, card_E, Nat.card_congr (subgroupOfEquivOfLe hXP).toEquiv,
    h.card_sup (z_mul_self c)] at hcard
  rw [← hcard]
  ring

end Beta

end CFSG.OddStandard.AltStdSmall4.G2

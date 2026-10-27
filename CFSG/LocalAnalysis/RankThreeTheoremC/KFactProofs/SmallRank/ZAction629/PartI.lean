module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction629.General
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpCoreA
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629

section
open Subgroup
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K] {p d : ℕ} {S : Subgroup K} {z t : K}

theorem Setup.S_le_normalizer (h : Setup p d S z t) :
    S ≤ normalizer ((RR S z : Subgroup K) : Set K) :=
  Subgroup.normalizer_commutator_ge_right _ _

theorem Setup.zpowers_le_normalizer (h : Setup p d S z t) :
    zpowers z ≤ normalizer ((RR S z : Subgroup K) : Set K) :=
  Subgroup.normalizer_commutator_ge_left _ _
end

section
open Subgroup
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]
variable {p d : ℕ} {S : Subgroup K} {z t : K}

theorem setupBasic_mem_zpowers_involution {u x : K} (hu2 : u ^ 2 = 1) (hx : x ∈ zpowers u) :
    x = 1 ∨ x = u := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · left
    rw [hm, zpow_mul]
    simp [hu2]
  · right
    rw [hm, zpow_add_one, zpow_mul]
    simp [hu2]

theorem setupBasic_conj_t (h : Setup p d S z t) {g : K}
    (hg : g ∈ normalizer ((RR S z : Subgroup K) : Set K)) : g * t = t * g := by
  have hrR : g * t * g⁻¹ ∈ RR S z :=
    (Subgroup.mem_normalizer_iff.1 hg t).1 h.shape.t_mem
  have hcomm : ∀ r ∈ RR S z, (g * t * g⁻¹) * r = r * (g * t * g⁻¹) := by
    intro r hr
    have hr' : g⁻¹ * r * g ∈ RR S z := by
      refine (Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * r * g)).2 ?_
      have e : g * (g⁻¹ * r * g) * g⁻¹ = r := by group
      rw [e]
      exact hr
    have key := h.shape.t_comm _ hr'
    calc (g * t * g⁻¹) * r = g * (t * (g⁻¹ * r * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * r * g * t) * g⁻¹ := by rw [← key]
      _ = r * (g * t * g⁻¹) := by group
  have hmem : g * t * g⁻¹ ∈ zpowers t := h.shape.center_le _ hrR hcomm
  rcases setupBasic_mem_zpowers_involution h.shape.t_sq hmem with h1 | h1
  · exfalso
    apply h.shape.t_ne
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by simp [h1]
  · calc g * t = g * t * g⁻¹ * g := by group
      _ = t * g := by rw [h1]

theorem Setup.RR_le (h : Setup p d S z t) : RR S z ≤ S := by
  refine Subgroup.commutator_le.2 ?_
  intro g hg s hs
  have hgN : g ∈ normalizer (S : Set K) := h.zS hg
  have hconj : g * s * g⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 hgN s).1 hs
  rw [commutatorElement_def]
  exact S.mul_mem hconj (S.inv_mem hs)

theorem Setup.t_comm_S (h : Setup p d S z t) : ∀ s ∈ S, s * t = t * s :=
  fun s hs => setupBasic_conj_t h (h.S_le_normalizer hs)

theorem Setup.z_comm_t (h : Setup p d S z t) : z * t = t * z :=
  setupBasic_conj_t h (h.zpowers_le_normalizer (Subgroup.mem_zpowers z))

theorem Setup.orderOf_z (h : Setup p d S z t) : orderOf z = p := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  exact orderOf_eq_prime h.zp h.zne
end

section
open Subgroup
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]
variable {p d : ℕ} {S : Subgroup K} {z t : K}

theorem Setup.commutator_RR (h : Setup p d S z t) : ⁅RR S z, zpowers z⁆ = RR S z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq h.two
  have hz : Nat.card (zpowers z) = p := by
    rw [Nat.card_zpowers, Setup.orderOf_z h]
  have hcop2 : Nat.Coprime p 2 := (Nat.coprime_primes h.prime Nat.prime_two).mpr h.odd
  have hcop : Nat.Coprime (Nat.card (zpowers z)) (Nat.card S) := by
    rw [hz, hn]
    exact Nat.Coprime.pow_right n hcop2
  have key := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.CoreA.commutator_commutator_eq_of_coprime
    h.zS hcop
  show ⁅⁅zpowers z, S⁆, zpowers z⁆ = ⁅zpowers z, S⁆
  rw [Subgroup.commutator_comm (zpowers z) S]
  exact key
end

section
open Subgroup
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]
variable {p d : ℕ} {S : Subgroup K} {z t : K}

theorem fixRR_commute_of_zpowers {a y w : K} (ha : Commute a y) (hw : w ∈ zpowers a) :
    Commute w y := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact ha.zpow_left k

theorem fixRR_key {r s w c s' : K} (hc : c = r * s * r⁻¹ * s⁻¹) (hs' : s' = w * s⁻¹ * w⁻¹)
    (hrw : Commute r w) (hcw : Commute c w) (hcs : Commute c s) (hcs' : Commute c s') :
    r * (s * s') = s * s' * r := by
  have hK1 : r * s = c * s * r := by rw [hc]; group
  have hK3 : r * s⁻¹ = s⁻¹ * c⁻¹ * r := by rw [hc]; group
  have hrw' : r * w⁻¹ = w⁻¹ * r := hrw.inv_right.eq
  have hwc : w * c⁻¹ = c⁻¹ * w := hcw.symm.inv_right.eq
  have hK2 : r * s' = s' * c⁻¹ * r := by
    rw [hs']
    calc r * (w * s⁻¹ * w⁻¹) = (r * w) * s⁻¹ * w⁻¹ := by group
      _ = (w * r) * s⁻¹ * w⁻¹ := by rw [hrw.eq]
      _ = w * (r * s⁻¹) * w⁻¹ := by group
      _ = w * (s⁻¹ * c⁻¹ * r) * w⁻¹ := by rw [hK3]
      _ = w * s⁻¹ * c⁻¹ * (r * w⁻¹) := by group
      _ = w * s⁻¹ * c⁻¹ * (w⁻¹ * r) := by rw [hrw']
      _ = (w * s⁻¹ * w⁻¹) * (w * c⁻¹ * w⁻¹) * r := by group
      _ = (w * s⁻¹ * w⁻¹) * (c⁻¹ * w * w⁻¹) * r := by rw [hwc]
      _ = (w * s⁻¹ * w⁻¹) * c⁻¹ * r := by group
  have hcss : c * (s * s') = s * s' * c := (hcs.mul_right hcs').eq
  calc r * (s * s') = (r * s) * s' := by group
    _ = (c * s * r) * s' := by rw [hK1]
    _ = c * s * (r * s') := by group
    _ = c * s * (s' * c⁻¹ * r) := by rw [hK2]
    _ = c * (s * s') * c⁻¹ * r := by group
    _ = (s * s') * c * c⁻¹ * r := by rw [hcss]
    _ = s * s' * r := by group

theorem Setup.fix_RR (h : Setup p d S z t) : ∀ r ∈ RR S z, z * r = r * z → r ∈ zpowers t := by
  intro r hr hzr
  refine h.shape.center_le r hr ?_
  have hzr' : Commute z r := hzr
  have hzt : Commute z t := h.z_comm_t
  have hle : ⁅RR S z, zpowers z⁆ ≤ Subgroup.centralizer ({r} : Set K) := by
    rw [Subgroup.commutator_le]
    intro s hs w hw
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    have hrw : Commute r w := (fixRR_commute_of_zpowers hzr' hw).symm
    have hwt : Commute t w := (fixRR_commute_of_zpowers hzt hw).symm
    have hwN : w ∈ normalizer ((RR S z : Subgroup K) : Set K) := h.zpowers_le_normalizer hw
    obtain ⟨c, hc, hcR⟩ : ∃ c : K, c = r * s * r⁻¹ * s⁻¹ ∧ c ∈ zpowers t :=
      ⟨r * s * r⁻¹ * s⁻¹, rfl, h.shape.comm_mem r hr s hs⟩
    obtain ⟨s', hs'eq⟩ : ∃ s' : K, s' = w * s⁻¹ * w⁻¹ := ⟨_, rfl⟩
    have hs'R : s' ∈ RR S z := by
      rw [hs'eq]
      exact (Subgroup.mem_normalizer_iff.mp hwN s⁻¹).mp ((RR S z).inv_mem hs)
    have hst : Commute s t := h.shape.t_comm s hs
    have hs't : Commute s' t := h.shape.t_comm s' hs'R
    have hcs : Commute c s := fixRR_commute_of_zpowers hst.symm hcR
    have hcs' : Commute c s' := fixRR_commute_of_zpowers hs't.symm hcR
    have hcw : Commute c w := fixRR_commute_of_zpowers hwt hcR
    have hX : ⁅s, w⁆ = s * s' := by
      rw [hs'eq, commutatorElement_def]
      group
    rw [hX]
    exact fixRR_key hc hs'eq hrw hcw hcs hcs'
  intro x hx
  have hx' : x ∈ ⁅RR S z, zpowers z⁆ := by
    rw [h.commutator_RR]
    exact hx
  exact Subgroup.mem_centralizer_iff.mp (hle hx') r (Set.mem_singleton r)
end

section
open Subgroup
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]
variable {p d : ℕ} {S : Subgroup K} {z t : K}

theorem keyRR_fwd {A B : Subgroup K} {g : K} (hA : ∀ x ∈ A, g * x * g⁻¹ ∈ A)
    (hB : ∀ x ∈ B, g * x * g⁻¹ ∈ B) : ∀ x ∈ A ⊔ B, g * x * g⁻¹ ∈ A ⊔ B := by
  let W : Subgroup K := (A ⊔ B).comap (MulAut.conj g).toMonoidHom
  have hle : A ⊔ B ≤ W := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · exact Subgroup.mem_sup_left (hA a ha)
    · exact Subgroup.mem_sup_right (hB b hb)
  intro x hx
  exact hle hx

theorem keyRR_mem_normalizer_of {A : Subgroup K} {g : K} (hA : ∀ x ∈ A, g * x * g⁻¹ ∈ A)
    (hA' : ∀ x ∈ A, g⁻¹ * x * g⁻¹⁻¹ ∈ A) : g ∈ normalizer (A : Set K) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hA x hx, fun hx => ?_⟩
  simpa [mul_assoc] using hA' (g * x * g⁻¹) hx

theorem keyRR_conj_mem {A : Subgroup K} {g : K} (hg : g ∈ normalizer (A : Set K)) :
    ∀ x ∈ A, g * x * g⁻¹ ∈ A :=
  fun x hx => (Subgroup.mem_normalizer_iff.mp hg x).mp hx

theorem keyRR_normalizer_sup {A B : Subgroup K} {g : K} (hA : g ∈ normalizer (A : Set K))
    (hB : g ∈ normalizer (B : Set K)) : g ∈ normalizer ((A ⊔ B : Subgroup K) : Set K) :=
  keyRR_mem_normalizer_of (keyRR_fwd (keyRR_conj_mem hA) (keyRR_conj_mem hB))
    (keyRR_fwd (keyRR_conj_mem (inv_mem hA)) (keyRR_conj_mem (inv_mem hB)))

theorem keyRR_zpowers_conj {g t : K} (hc : Commute g t) :
    ∀ x ∈ zpowers t, g * x * g⁻¹ ∈ zpowers t := by
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have e : g * t ^ k * g⁻¹ = t ^ k := by
    rw [(hc.zpow_right k).eq]
    simp
  rw [e]
  exact zpow_mem_zpowers t k

theorem keyRR_mem_normalizer_zpowers {g t : K} (hc : Commute g t) :
    g ∈ normalizer ((zpowers t : Subgroup K) : Set K) :=
  keyRR_mem_normalizer_of (keyRR_zpowers_conj hc) (keyRR_zpowers_conj hc.inv_left)

theorem keyRR_sq_zpowers {t b : K} (ht : t ^ 2 = 1) (hb : b ∈ zpowers t) : b ^ 2 = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht, one_zpow]

theorem keyRR_mem_sup_of_comm {A B : Subgroup K} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ∀ x ∈ A ⊔ B, ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let T : Subgroup K :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := fun {x y} hx hy => by
        obtain ⟨a, ha, b, hb, rfl⟩ := hx
        obtain ⟨a', ha', b', hb', rfl⟩ := hy
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        have e : b * a' = a' * b := (hAB a' ha' b hb).symm
        calc a * b * (a' * b') = a * (b * a') * b' := by simp only [mul_assoc]
          _ = a * (a' * b) * b' := by rw [e]
          _ = a * a' * (b * b') := by simp only [mul_assoc]
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      inv_mem' := fun {x} hx => by
        obtain ⟨a, ha, b, hb, rfl⟩ := hx
        exact ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, by rw [hAB a ha b hb, mul_inv_rev]⟩ }
  have hle : A ⊔ B ≤ T :=
    sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
      (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  intro x hx
  exact hle hx

theorem keyRR_arith {p d j : ℕ} (hpd : (p = 3 ∧ d = 2) ∨ (p = 5 ∧ d = 4)) (hj2 : 2 ≤ j)
    (hjd : j ≤ d + 1) (hmod : 2 ^ j ≡ 2 [MOD p]) : j = d + 1 := by
  rcases hpd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hj3 : j ≤ 3 := by omega
    interval_cases j <;> first | rfl | (exfalso; revert hmod; decide)
  · have hj5 : j ≤ 5 := by omega
    interval_cases j <;> first | rfl | (exfalso; revert hmod; decide)

theorem Setup.key_RR (h : Setup p d S z t) {U : Subgroup K} (hU : U ≤ RR S z)
    (hz : zpowers z ≤ normalizer (U : Set K)) (hnt : ¬ U ≤ zpowers t) : U = RR S z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V, hVdef⟩ : ∃ V : Subgroup K, V = U ⊔ zpowers t := ⟨_, rfl⟩
  have htR : t ∈ RR S z := h.shape.t_mem
  have hVR : V ≤ RR S z := by
    rw [hVdef]
    exact sup_le hU (Subgroup.zpowers_le.mpr htR)
  have hVS : V ≤ S := hVR.trans h.RR_le
  have htV : t ∈ V := by
    rw [hVdef]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have htV' : zpowers t ≤ V := Subgroup.zpowers_le.mpr htV
  have hUV : U ≤ V := by
    rw [hVdef]
    exact le_sup_left
  have hzU : z ∈ normalizer (U : Set K) := hz (Subgroup.mem_zpowers z)
  have hzV : z ∈ normalizer (V : Set K) := by
    rw [hVdef]
    exact keyRR_normalizer_sup hzU (keyRR_mem_normalizer_zpowers (show Commute z t from h.z_comm_t))
  obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq h.two
  have hdvd : Nat.card V ∣ 2 ^ n := by
    rw [← hn]
    exact Subgroup.card_dvd_of_le hVS
  obtain ⟨j, -, hjV⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hcardR : Nat.card (RR S z) = 2 ^ (d + 1) := h.shape.card
  have hjd : j ≤ d + 1 := by
    have h1 : Nat.card V ≤ Nat.card (RR S z) := Subgroup.card_le_of_le hVR
    rw [hjV, hcardR] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
  have hcardt : Nat.card (zpowers t) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime h.shape.t_sq h.shape.t_ne]
  have hfix : V ⊓ centralizer ({z} : Set K) = zpowers t := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxV, hxC⟩ := Subgroup.mem_inf.mp hx
      have hzx : z * x = x * z := Subgroup.mem_centralizer_iff.mp hxC z (Set.mem_singleton z)
      exact h.fix_RR x (hVR hxV) hzx
    · refine Subgroup.zpowers_le.mpr ?_
      refine Subgroup.mem_inf.mpr ⟨htV, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro g hg
      rw [Set.mem_singleton_iff.mp hg]
      exact h.z_comm_t
  have hcardfix : Nat.card ↥(V ⊓ centralizer ({z} : Set K)) = 2 := by
    rw [hfix, hcardt]
  have hmod : Nat.card V ≡ Nat.card ↥(V ⊓ centralizer ({z} : Set K)) [MOD p] :=
    card_modEq_card_inf_centralizer h.prime h.zp hzV
  rw [hcardfix, hjV] at hmod
  have hj2 : 2 ≤ j := by
    by_contra hlt
    have hj01 : j = 0 ∨ j = 1 := by omega
    have hle2 : Nat.card (zpowers t) ≤ Nat.card V := Subgroup.card_le_of_le htV'
    rw [hcardt, hjV] at hle2
    rcases hj01 with rfl | rfl
    · norm_num at hle2
    · have hcle : Nat.card V ≤ Nat.card (zpowers t) :=
        le_of_eq (by rw [hjV, hcardt, pow_one])
      have hVeq : zpowers t = V := Subgroup.eq_of_le_of_card_ge htV' hcle
      exact hnt (by rw [hVeq]; exact hUV)
  have hj : j = d + 1 := keyRR_arith h.shape.pd hj2 hjd hmod
  have hVeqR : V = RR S z := by
    apply Subgroup.eq_of_le_of_card_ge hVR
    exact le_of_eq (by rw [hcardR, hjV, hj])
  obtain ⟨i, hiR, hi2⟩ := h.shape.sqrt
  have hiV : i ∈ U ⊔ zpowers t := by
    rw [← hVdef, hVeqR]
    exact hiR
  have hcomm : ∀ a ∈ U, ∀ b ∈ zpowers t, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((show Commute a t from h.shape.t_comm a (hU ha)).zpow_right k).eq
  obtain ⟨u, hu, b, hb, hieq⟩ := keyRR_mem_sup_of_comm hcomm i hiV
  have hb2 : b ^ 2 = 1 := keyRR_sq_zpowers h.shape.t_sq hb
  have ht_eq : t = u ^ 2 := by
    calc t = i ^ 2 := hi2.symm
      _ = (u * b) ^ 2 := by rw [hieq]
      _ = u ^ 2 * b ^ 2 := (show Commute u b from hcomm u hu b hb).mul_pow 2
      _ = u ^ 2 := by rw [hb2, mul_one]
  have htU : t ∈ U := by
    rw [ht_eq]
    exact pow_mem hu 2
  have hVU : V = U := by
    rw [hVdef]
    exact sup_eq_left.mpr (Subgroup.zpowers_le.mpr htU)
  exact hVU.symm.trans hVeqR
end

section
open Subgroup
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

def centZ_U (R T : Subgroup K) (c : K) (hT : ∀ r ∈ R, ∀ τ ∈ T, r * τ = τ * r) :
    Subgroup K where
  carrier := {r | r ∈ R ∧ ⁅c, r⁆ ∈ T}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    show a * b ∈ R ∧ ⁅c, a * b⁆ ∈ T
    refine ⟨R.mul_mem ha hb, ?_⟩
    have e : ⁅c, a * b⁆ = ⁅c, a⁆ * (a * ⁅c, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]; group
    have hcomm : a * ⁅c, b⁆ * a⁻¹ = ⁅c, b⁆ := by
      rw [hT a ha _ hb']; group
    rw [e, hcomm]
    exact T.mul_mem ha' hb'
  one_mem' := by
    show (1 : K) ∈ R ∧ ⁅c, (1 : K)⁆ ∈ T
    refine ⟨R.one_mem, ?_⟩
    rw [commutatorElement_one_right]
    exact T.one_mem
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    show a⁻¹ ∈ R ∧ ⁅c, a⁻¹⁆ ∈ T
    refine ⟨R.inv_mem ha, ?_⟩
    have hc : Commute a ⁅c, a⁆ := hT a ha _ ha'
    have e : ⁅c, a⁻¹⁆ = a⁻¹ * ⁅c, a⁆⁻¹ * a := by
      simp only [commutatorElement_def]; group
    have hcomm : a⁻¹ * ⁅c, a⁆⁻¹ * a = ⁅c, a⁆⁻¹ := by
      have h2 : a * ⁅c, a⁆⁻¹ = ⁅c, a⁆⁻¹ * a := hc.inv_right.eq
      calc a⁻¹ * ⁅c, a⁆⁻¹ * a = a⁻¹ * (⁅c, a⁆⁻¹ * a) := by group
        _ = a⁻¹ * (a * ⁅c, a⁆⁻¹) := by rw [h2]
        _ = ⁅c, a⁆⁻¹ := by group
    rw [e, hcomm]
    exact T.inv_mem ha'

theorem centZ_mem_U {R T : Subgroup K} {c r : K}
    {hT : ∀ x ∈ R, ∀ τ ∈ T, x * τ = τ * x} :
    r ∈ centZ_U R T c hT ↔ r ∈ R ∧ ⁅c, r⁆ ∈ T :=
  Iff.rfl

theorem centZ_comm_conj {z c : K} (hcz : z * c = c * z) (n : K) :
    ⁅c, z * n * z⁻¹⁆ = z * ⁅c, n⁆ * z⁻¹ := by
  have key : c * (z * n * z⁻¹) * c⁻¹ = z * (c * n * c⁻¹) * z⁻¹ := by
    have e : c * (z * n * z⁻¹) * c⁻¹ = (c * z) * n * (c * z)⁻¹ := by group
    rw [e, ← hcz]
    group
  simp only [commutatorElement_def]
  rw [key]
  group

theorem centZ_conj_fix {z t x : K} (hzt : z * t = t * z) (hx : x ∈ zpowers t) :
    z * x * z⁻¹ = x := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  have hc : Commute z (t ^ k) := Commute.zpow_right (show Commute z t from hzt) k
  rw [hc.eq, mul_inv_cancel_right]

theorem centZ_conj_mem {z t x : K} (hzt : z * t = t * z) (hx : z * x * z⁻¹ ∈ zpowers t) :
    x ∈ zpowers t := by
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hx
  have hc : Commute z⁻¹ (t ^ k) :=
    (Commute.zpow_right (show Commute z t from hzt) k).inv_left
  have hx' : x = z⁻¹ * t ^ k * z := by rw [hk]; group
  rw [hx', hc.eq, inv_mul_cancel_right]
  exact (zpowers t).zpow_mem (mem_zpowers t) k

theorem centZ_conj_comm {G : Type*} [Group G] {c s w τ : G}
    (h1 : c * s * c⁻¹ = τ * s) (h2 : c * w * c⁻¹ = w)
    (hτw : τ * w = w * τ) (hτg : τ * (s * w * s⁻¹ * w⁻¹) = (s * w * s⁻¹ * w⁻¹) * τ) :
    c * (s * w * s⁻¹ * w⁻¹) * c⁻¹ = s * w * s⁻¹ * w⁻¹ := by
  have h3 : c * s⁻¹ * c⁻¹ = s⁻¹ * τ⁻¹ := by
    rw [show c * s⁻¹ * c⁻¹ = (c * s * c⁻¹)⁻¹ by group, h1, mul_inv_rev]
  have h4 : c * w⁻¹ * c⁻¹ = w⁻¹ := by
    rw [show c * w⁻¹ * c⁻¹ = (c * w * c⁻¹)⁻¹ by group, h2]
  have hτw' : τ⁻¹ * w⁻¹ = w⁻¹ * τ⁻¹ := (Commute.inv_inv (show Commute τ w from hτw)).eq
  calc c * (s * w * s⁻¹ * w⁻¹) * c⁻¹
      = (c * s * c⁻¹) * (c * w * c⁻¹) * (c * s⁻¹ * c⁻¹) * (c * w⁻¹ * c⁻¹) := by group
    _ = (τ * s) * w * (s⁻¹ * τ⁻¹) * w⁻¹ := by rw [h1, h2, h3, h4]
    _ = τ * s * w * s⁻¹ * (τ⁻¹ * w⁻¹) := by group
    _ = τ * s * w * s⁻¹ * (w⁻¹ * τ⁻¹) := by rw [hτw']
    _ = τ * (s * w * s⁻¹ * w⁻¹) * τ⁻¹ := by group
    _ = (s * w * s⁻¹ * w⁻¹) * τ * τ⁻¹ := by rw [hτg]
    _ = s * w * s⁻¹ * w⁻¹ := by group

variable {p d : ℕ} {S : Subgroup K} {z t : K}

theorem Setup.centralizer_z (h : Setup p d S z t) {c : K} (hc : c ∈ S) (hcz : z * c = c * z) :
    ∀ r ∈ RR S z, c * r = r * c := by
  have hRS : RR S z ≤ S := h.RR_le
  have hzt : z * t = t * z := h.z_comm_t
  have hTR : ∀ r ∈ RR S z, ∀ τ ∈ zpowers t, r * τ = τ * r := by
    intro r hr τ hτ
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hτ
    exact (Commute.zpow_right (show Commute r t from h.shape.t_comm r hr) k).eq
  have hTS : ∀ n ∈ S, ∀ τ ∈ zpowers t, n * τ = τ * n := by
    intro n hn τ hτ
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hτ
    exact (Commute.zpow_right (show Commute n t from h.t_comm_S n hn) k).eq
  have hN_le : RR S z ⊔ zpowers c ≤ S := sup_le hRS (zpowers_le.mpr hc)
  have hN2 : IsPGroup 2 (RR S z ⊔ zpowers c : Subgroup K) := h.two.to_le hN_le
  have hNR : RR S z ⊔ zpowers c ≤ normalizer ((RR S z : Subgroup K) : Set K) :=
    sup_le (hRS.trans h.S_le_normalizer) (zpowers_le.mpr (h.S_le_normalizer hc))
  have hZR : zpowers t ≤ RR S z := zpowers_le.mpr h.shape.t_mem
  have hZ : ∀ n ∈ RR S z ⊔ zpowers c, ∀ y ∈ zpowers t, n * y = y * n :=
    fun n hn y hy => hTS n (hN_le hn) y hy
  have hRT : ¬ RR S z ≤ zpowers t := by
    intro hle
    have h1 : Nat.card (RR S z) ≤ Nat.card (zpowers t) := Subgroup.card_le_of_le hle
    have h2 : Nat.card (zpowers t) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h.shape.t_sq)
    have hd : 2 ≤ d := by
      rcases h.shape.pd with ⟨_, h'⟩ | ⟨_, h'⟩ <;> omega
    have h3 : 8 ≤ Nat.card (RR S z) := by
      rw [h.shape.card]
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨r, hrR, hrT, hr⟩ :=
    exists_mem_not_mem_commutator_mem hN2 le_sup_left hNR hZR hZ hRT
  have hcN : c ∈ RR S z ⊔ zpowers c := Subgroup.mem_sup_right (mem_zpowers c)
  have hcr : ⁅c, r⁆ ∈ zpowers t := by
    have e : ⁅c, r⁆ = ⁅r, c⁆⁻¹ := by simp only [commutatorElement_def]; group
    rw [e]
    exact (zpowers t).inv_mem (hr c hcN)
  have hnt : ¬ centZ_U (RR S z) (zpowers t) c hTR ≤ zpowers t := by
    intro hle
    exact hrT (hle (centZ_mem_U.mpr ⟨hrR, hcr⟩))
  have hU : centZ_U (RR S z) (zpowers t) c hTR ≤ RR S z :=
    fun x hx => (centZ_mem_U.mp hx).1
  have hzN : z ∈ normalizer ((centZ_U (RR S z) (zpowers t) c hTR : Subgroup K) : Set K) := by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    have hzRn : n ∈ RR S z ↔ z * n * z⁻¹ ∈ RR S z :=
      Subgroup.mem_normalizer_iff.mp (h.zpowers_le_normalizer (mem_zpowers z)) n
    simp only [SetLike.mem_coe, centZ_mem_U]
    constructor
    · rintro ⟨hn, hcn⟩
      refine ⟨hzRn.mp hn, ?_⟩
      rw [centZ_comm_conj hcz n, centZ_conj_fix hzt hcn]
      exact hcn
    · rintro ⟨hm, hcm⟩
      refine ⟨hzRn.mpr hm, ?_⟩
      rw [centZ_comm_conj hcz n] at hcm
      exact centZ_conj_mem hzt hcm
  have hUeq : centZ_U (RR S z) (zpowers t) c hTR = RR S z :=
    h.key_RR hU (zpowers_le.mpr hzN) hnt
  have hall : ∀ s ∈ RR S z, ⁅c, s⁆ ∈ zpowers t := by
    intro s hs
    have hsU : s ∈ centZ_U (RR S z) (zpowers t) c hTR := by
      rw [hUeq]; exact hs
    exact (centZ_mem_U.mp hsU).2
  have hcw : ∀ w ∈ zpowers z, Commute c w := by
    intro w hw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    exact Commute.zpow_right (show Commute c z from hcz.symm) k
  have hTw : ∀ τ ∈ zpowers t, ∀ w ∈ zpowers z, Commute τ w := by
    intro τ hτ w hw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hτ
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hw
    exact Commute.zpow_zpow (show Commute t z from hzt.symm) k j
  have hgen : ∀ s ∈ RR S z, ∀ w ∈ zpowers z, c * ⁅s, w⁆ = ⁅s, w⁆ * c := by
    intro s hs w hw
    have hgR : ⁅s, w⁆ ∈ RR S z := by
      have hmem := commutator_mem_commutator hs hw
      rwa [h.commutator_RR] at hmem
    have hτT : ⁅c, s⁆ ∈ zpowers t := hall s hs
    have h1 : c * s * c⁻¹ = ⁅c, s⁆ * s := by
      rw [commutatorElement_def]; group
    have h2 : c * w * c⁻¹ = w := by
      rw [(hcw w hw).eq]; group
    have hτw : ⁅c, s⁆ * w = w * ⁅c, s⁆ := (hTw _ hτT w hw).eq
    have hτg : ⁅c, s⁆ * (s * w * s⁻¹ * w⁻¹) = (s * w * s⁻¹ * w⁻¹) * ⁅c, s⁆ :=
      (hTR _ hgR _ hτT).symm
    have hconj : c * ⁅s, w⁆ * c⁻¹ = ⁅s, w⁆ := centZ_conj_comm h1 h2 hτw hτg
    calc c * ⁅s, w⁆ = c * ⁅s, w⁆ * c⁻¹ * c := by group
      _ = ⁅s, w⁆ * c := by rw [hconj]
  have hsub : ⁅RR S z, zpowers z⁆ ≤ centralizer ({c} : Set K) := by
    rw [Subgroup.commutator_le]
    intro s hs w hw
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact hgen s hs w hw
  rw [h.commutator_RR] at hsub
  intro r hr
  exact Subgroup.mem_centralizer_iff.mp (hsub hr) c (Set.mem_singleton c)
end

section
open Subgroup
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]
variable {p d : ℕ} {S : Subgroup K} {z t : K}

theorem ccStruct_sq_of_mem_zpowers {u x : K} (hu2 : u ^ 2 = 1) (hx : x ∈ zpowers u) :
    x ^ 2 = 1 := by
  have hu : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one hu2
  have hx' : orderOf x ∣ 2 := (orderOf_dvd_of_mem_zpowers hx).trans hu
  exact orderOf_dvd_iff_pow_eq_one.1 hx'

theorem Setup.RR_inf_CC (h : Setup p d S z t) : RR S z ⊓ CC S z = zpowers t := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxR, hxC⟩ := Subgroup.mem_inf.1 hx
    have hxZ : x ∈ Subgroup.centralizer ((RR S z : Subgroup K) : Set K) :=
      (Subgroup.mem_inf.1 hxC).2
    exact h.shape.center_le x hxR (fun r hr => (Subgroup.mem_centralizer_iff.1 hxZ r hr).symm)
  · apply Subgroup.zpowers_le.2
    refine Subgroup.mem_inf.2 ⟨h.shape.t_mem, Subgroup.mem_inf.2 ⟨h.RR_le h.shape.t_mem, ?_⟩⟩
    exact Subgroup.mem_centralizer_iff.2 (fun r hr => h.shape.t_comm r hr)

theorem Setup.CC_sup (h : Setup p d S z t) : RR S z ⊔ CC S z = S := by
  apply le_antisymm
  · exact sup_le h.RR_le inf_le_left
  · have hp2 : Nat.Coprime p 2 := (Nat.coprime_primes h.prime Nat.prime_two).2 h.odd
    obtain ⟨n, hn⟩ := h.two.exists_card_eq
    have hsolv : Group.IsSolvable ↥S := by
      have := h.two.isNilpotent
      infer_instance
    have hcop : Nat.Coprime (Nat.card ↥(zpowers z)) (Nat.card ↥S) := by
      rw [Nat.card_zpowers, h.orderOf_z, hn]
      exact Nat.Coprime.pow_right n hp2
    have hmain := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.CoreA.le_commutator_sup_inf_centralizer
      (A := K) (P := S) (X := zpowers z) h.zS hsolv hcop
    rw [Subgroup.commutator_comm S (zpowers z)] at hmain
    refine hmain.trans (sup_le_sup le_rfl ?_)
    intro c hc
    obtain ⟨hcS, hcZ⟩ := Subgroup.mem_inf.1 hc
    have hzc : z * c = c * z := Subgroup.mem_centralizer_iff.1 hcZ z (Subgroup.mem_zpowers z)
    exact Subgroup.mem_inf.2
      ⟨hcS, Subgroup.mem_centralizer_iff.2 (fun r hr => (h.centralizer_z hcS hzc r hr).symm)⟩

theorem Setup.z_comm_CC (h : Setup p d S z t) : ∀ c ∈ CC S z, z * c = c * z := by
  intro c hcC
  have hcS : c ∈ S := (Subgroup.mem_inf.1 hcC).1
  have hcR : ∀ r ∈ RR S z, r * c = c * r := fun r hr =>
    Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hcC).2 r hr
  have hzN : z ∈ normalizer ((RR S z : Subgroup K) : Set K) :=
    h.zpowers_le_normalizer (Subgroup.mem_zpowers z)
  have hzS : z ∈ normalizer (S : Set K) := h.zS (Subgroup.mem_zpowers z)
  have hzcS : z * c * z⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 hzS c).1 hcS
  have hzcR : ∀ r ∈ RR S z, (z * c * z⁻¹) * r = r * (z * c * z⁻¹) := by
    intro r hr
    have hr' : z⁻¹ * r * z ∈ RR S z := (Subgroup.mem_normalizer_iff''.1 hzN r).1 hr
    calc (z * c * z⁻¹) * r = z * (c * (z⁻¹ * r * z)) * z⁻¹ := by group
      _ = z * ((z⁻¹ * r * z) * c) * z⁻¹ := by rw [hcR _ hr']
      _ = r * (z * c * z⁻¹) := by group
  have hzcC : z * c * z⁻¹ ∈ CC S z :=
    Subgroup.mem_inf.2 ⟨hzcS, Subgroup.mem_centralizer_iff.2 (fun r hr => (hzcR r hr).symm)⟩
  obtain ⟨w, hw⟩ : ∃ w : K, w = z * c * z⁻¹ * c⁻¹ := ⟨_, rfl⟩
  have hwR : w ∈ RR S z := by
    have hc' : ⁅z, c⁆ ∈ RR S z :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers z) hcS
    rw [commutatorElement_def] at hc'
    rw [hw]
    exact hc'
  have hwC : w ∈ CC S z := by
    rw [hw]
    exact mul_mem hzcC (inv_mem hcC)
  have hwt : w ∈ zpowers t := by
    have hI : w ∈ RR S z ⊓ CC S z := Subgroup.mem_inf.2 ⟨hwR, hwC⟩
    rwa [h.RR_inf_CC] at hI
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hwt
  have hzt : Commute z t := h.z_comm_t
  have hzw : Commute z w := by
    rw [← hm]
    exact hzt.zpow_right m
  have hzc : z * c = w * c * z := by
    rw [hw]
    group
  have hind : ∀ k : ℕ, z ^ k * c = w ^ k * c * z ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc z ^ (k + 1) * c = z * (z ^ k * c) := by rw [pow_succ' z k, mul_assoc]
        _ = z * (w ^ k * c * z ^ k) := by rw [ih]
        _ = (z * w ^ k) * c * z ^ k := by simp only [mul_assoc]
        _ = (w ^ k * z) * c * z ^ k := by rw [(hzw.pow_right k).eq]
        _ = w ^ k * (z * c) * z ^ k := by simp only [mul_assoc]
        _ = w ^ k * (w * c * z) * z ^ k := by rw [hzc]
        _ = (w ^ k * w) * c * (z * z ^ k) := by simp only [mul_assoc]
        _ = w ^ (k + 1) * c * z ^ (k + 1) := by rw [pow_succ w k, pow_succ' z k]
  have hwp : w ^ p = 1 := by
    have e := hind p
    rw [h.zp, one_mul, mul_one] at e
    exact mul_right_cancel (e.symm.trans (one_mul c).symm)
  have hw2 : w ^ 2 = 1 := ccStruct_sq_of_mem_zpowers h.shape.t_sq hwt
  have hw1 : w = 1 := by
    obtain ⟨q, hq⟩ := h.prime.odd_of_ne_two h.odd
    have hwodd : w ^ p = w := by
      rw [hq, pow_succ, pow_mul, hw2, one_pow, one_mul]
    exact hwodd.symm.trans hwp
  have hkey : z * c * z⁻¹ * c⁻¹ = 1 := by
    rw [← hw]
    exact hw1
  calc z * c = (z * c * z⁻¹ * c⁻¹) * (c * z) := by group
    _ = c * z := by rw [hkey, one_mul]
end

section
open Subgroup
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]
variable {p d : ℕ} {S : Subgroup K} {z t : K}

theorem conclC_comm_zpowers {z t σ : K} (hzt : z * t = t * z) (hσ : σ ∈ zpowers t) :
    z * σ = σ * z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hσ
  exact (show Commute z t from hzt).zpow_right k

theorem conclC_sq_one {t σ : K} (ht2 : t ^ 2 = 1) (hσ : σ ∈ zpowers t) : σ ^ 2 = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hσ
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht2, one_zpow]

theorem conclC_pow_conj {z a σ : K} (hza : z * a = σ * a * z) (hσz : z * σ = σ * z) (k : ℕ) :
    z ^ k * a = σ ^ k * a * z ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hc : z * σ ^ k = σ ^ k * z := (show Commute z σ from hσz).pow_right k
    calc z ^ (k + 1) * a = z * (z ^ k * a) := by rw [pow_succ' z k, mul_assoc]
      _ = z * (σ ^ k * a * z ^ k) := by rw [ih]
      _ = (z * σ ^ k) * a * z ^ k := by simp only [mul_assoc]
      _ = (σ ^ k * z) * a * z ^ k := by rw [hc]
      _ = σ ^ k * (z * a) * z ^ k := by simp only [mul_assoc]
      _ = σ ^ k * (σ * a * z) * z ^ k := by rw [hza]
      _ = σ ^ (k + 1) * a * z ^ (k + 1) := by
        rw [pow_succ σ k, pow_succ' z k]; simp only [mul_assoc]

theorem conclC_sigma_eq_one {q : ℕ} (hodd : Odd q) {z t a σ : K} (hzq : z ^ q = 1)
    (ht2 : t ^ 2 = 1) (hzt : z * t = t * z) (hσ : σ ∈ zpowers t) (hza : z * a = σ * a * z) :
    σ = 1 := by
  have hσ2 : σ ^ 2 = 1 := conclC_sq_one ht2 hσ
  have hσz : z * σ = σ * z := conclC_comm_zpowers hzt hσ
  have hk := conclC_pow_conj hza hσz q
  rw [hzq, one_mul, mul_one] at hk
  have hσq : σ ^ q = 1 := mul_right_cancel (b := a) (by rw [one_mul]; exact hk.symm)
  obtain ⟨m, hm⟩ := hodd
  rw [hm, pow_succ, pow_mul, hσ2, one_pow, one_mul] at hσq
  exact hσq

theorem conclC_commute_of_mem {q : ℕ} (hodd : Odd q) {z t a : K} (hzq : z ^ q = 1)
    (ht2 : t ^ 2 = 1) (hzt : z * t = t * z) (hτ : ⁅a, z⁆ ∈ zpowers t) : a * z = z * a := by
  have hza : z * a = (⁅a, z⁆)⁻¹ * a * z := by
    simp only [commutatorElement_def]; group
  have hσ : (⁅a, z⁆)⁻¹ = 1 := conclC_sigma_eq_one hodd hzq ht2 hzt (inv_mem hτ) hza
  exact commutatorElement_eq_one_iff_mul_comm.mp (inv_eq_one.mp hσ)

theorem conclC_conj_mem {H : Subgroup K} {g : K} (hg : g ∈ normalizer (H : Set K)) (x : K) :
    x ∈ H ↔ g * x * g⁻¹ ∈ H :=
  Subgroup.mem_normalizer_iff.mp hg x

theorem Setup.conclusion_C (h : Setup p d S z t) :
    ∀ A : Subgroup K, A ≤ S → zpowers z ≤ normalizer (A : Set K) → ⁅A, zpowers z⁆ ≠ ⊥ →
      ⁅zpowers z, S⁆ ≤ A := by
  intro A hAS hzA hcomm
  have hodd : Odd p := h.prime.odd_of_ne_two h.odd
  have hzA' : z ∈ normalizer (A : Set K) := hzA (Subgroup.mem_zpowers z)
  obtain ⟨a, haA, hau⟩ : ∃ a ∈ A, ⁅a, z⁆ ∉ zpowers t := by
    by_contra hcon
    have hcon' : ∀ b ∈ A, ⁅b, z⁆ ∈ zpowers t := fun b hb => by
      by_contra hnb
      exact hcon ⟨b, hb, hnb⟩
    refine hcomm ?_
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro b hb w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [Subgroup.mem_bot]
    have hbz : Commute b z := conclC_commute_of_mem hodd h.zp h.shape.t_sq h.z_comm_t (hcon' b hb)
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hbz.zpow_right k)
  have hzU : zpowers z ≤ normalizer ((A ⊓ RR S z : Subgroup K) : Set K) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := conclC_conj_mem (hzA hg) x
    have h2 := conclC_conj_mem (h.zpowers_le_normalizer hg) x
    simp only [SetLike.mem_coe, Subgroup.mem_inf]
    exact and_congr h1 h2
  have huA : ⁅a, z⁆ ∈ A := by
    have e : ⁅a, z⁆ = a * (z * a⁻¹ * z⁻¹) := by
      simp only [commutatorElement_def, mul_assoc]
    rw [e]
    exact A.mul_mem haA ((conclC_conj_mem hzA' a⁻¹).mp (A.inv_mem haA))
  have huR : ⁅a, z⁆ ∈ RR S z := by
    have hz' : ⁅z, a⁆ ∈ RR S z :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers z) (hAS haA)
    have e : ⁅a, z⁆ = ⁅z, a⁆⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (RR S z).inv_mem hz'
  have hUmem : ⁅a, z⁆ ∈ A ⊓ RR S z := Subgroup.mem_inf.mpr ⟨huA, huR⟩
  have hnt : ¬ (A ⊓ RR S z) ≤ zpowers t := fun hle => hau (hle hUmem)
  have hUeq : A ⊓ RR S z = RR S z := h.key_RR (U := A ⊓ RR S z) inf_le_right hzU hnt
  exact (le_of_eq hUeq.symm).trans inf_le_left
end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629

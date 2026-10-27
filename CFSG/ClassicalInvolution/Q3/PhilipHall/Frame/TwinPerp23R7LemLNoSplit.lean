module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Not9
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8YGamData

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section Q8

variable {G : Type*} [Group G] {P : Subgroup G}

theorem q8_facts_of_equiv (φ : ↥P ≃* QuaternionGroup 2) {q : G} (hq : q ∈ P)
    (hq2 : q * q ≠ 1) :
    (∀ b ∈ P, q * b = b * q → b = 1 ∨ b = q ∨ b = q * q ∨ b = q * q * q) ∧
      (∀ r ∈ P, r * q * r⁻¹ = q ∨ r * q * r⁻¹ = q * q * q) ∧
      ∀ b ∈ P, b * b * b * b = 1 := by
  have k1 : ∀ a c : QuaternionGroup 2, a * a ≠ 1 → a * c = c * a →
      c = 1 ∨ c = a ∨ c = a * a ∨ c = a * a * a := by decide
  have k2 : ∀ a c : QuaternionGroup 2, a * a ≠ 1 →
      c * a * c⁻¹ = a ∨ c * a * c⁻¹ = a * a * a := by decide
  have k3 : ∀ a : QuaternionGroup 2, a * a * a * a = 1 := by decide
  have hinj : ∀ x y : ↥P, φ x = φ y → (x : G) = y := fun x y h =>
    congrArg Subtype.val (φ.injective h)
  have ha : φ ⟨q, hq⟩ * φ ⟨q, hq⟩ ≠ 1 := by
    intro h
    exact hq2 (hinj (⟨q, hq⟩ * ⟨q, hq⟩) 1 (by rw [map_mul, h, map_one]))
  refine ⟨fun b hb hqb => ?_, fun r hr => ?_, fun b hb => ?_⟩
  · have hc : φ ⟨q, hq⟩ * φ ⟨b, hb⟩ = φ ⟨b, hb⟩ * φ ⟨q, hq⟩ := by
      rw [← map_mul, ← map_mul]
      exact congrArg φ (Subtype.ext hqb)
    rcases k1 _ _ ha hc with h | h | h | h
    · exact Or.inl (hinj ⟨b, hb⟩ 1 (by rw [h, map_one]))
    · exact Or.inr (Or.inl (hinj ⟨b, hb⟩ ⟨q, hq⟩ h))
    · exact Or.inr (Or.inr (Or.inl (hinj ⟨b, hb⟩ (⟨q, hq⟩ * ⟨q, hq⟩) (by rw [h, map_mul]))))
    · exact Or.inr (Or.inr (Or.inr (hinj ⟨b, hb⟩ (⟨q, hq⟩ * ⟨q, hq⟩ * ⟨q, hq⟩)
        (by rw [h, map_mul, map_mul]))))
  · rcases k2 _ (φ ⟨r, hr⟩) ha with h | h
    · exact Or.inl (hinj (⟨r, hr⟩ * ⟨q, hq⟩ * ⟨r, hr⟩⁻¹) ⟨q, hq⟩
        (by rw [map_mul, map_mul, map_inv, h]))
    · exact Or.inr (hinj (⟨r, hr⟩ * ⟨q, hq⟩ * ⟨r, hr⟩⁻¹) (⟨q, hq⟩ * ⟨q, hq⟩ * ⟨q, hq⟩)
        (by rw [map_mul, map_mul, map_inv, h, map_mul, map_mul]))
  · exact hinj (⟨b, hb⟩ * ⟨b, hb⟩ * ⟨b, hb⟩ * ⟨b, hb⟩) 1
      (by rw [map_mul, map_mul, map_mul, k3, map_one])

theorem conj_ne_inv_of_odd_orderOf {w q : G} (hodd : Odd (orderOf w)) (hq2 : q * q ≠ 1) :
    w * q * w⁻¹ ≠ q⁻¹ := by
  intro h
  have h1 : w * q⁻¹ * w⁻¹ = q := by
    calc w * q⁻¹ * w⁻¹ = (w * q * w⁻¹)⁻¹ := by group
      _ = q := by rw [h, inv_inv]
  have hc : Commute (w * w) q := by
    show w * w * q = q * (w * w)
    calc w * w * q = w * (w * q * w⁻¹) * w := by group
      _ = w * q⁻¹ * w⁻¹ * (w * w) := by rw [h]; group
      _ = q * (w * w) := by rw [h1]
  obtain ⟨k, hk⟩ := hodd
  have hw : w * (w * w) ^ k = 1 := by
    rw [← sq, ← pow_mul, ← pow_succ', ← hk, pow_orderOf_eq_one]
  have hw' : w = ((w * w) ^ k)⁻¹ := eq_inv_of_mul_eq_one_left hw
  have hcw : Commute ((w * w) ^ k)⁻¹ q := (hc.pow_left k).inv_left
  rw [← hw'] at hcw
  have hqq : q = q⁻¹ := by rw [← h, hcw.eq, mul_inv_cancel_right]
  exact hq2 (mul_eq_one_iff_eq_inv.mpr hqq)

theorem conj_pow_eq_mul_pow_of_conj_fix {w r d : G} (hr : w * r * w⁻¹ = r * d)
    (hd : w * d * w⁻¹ = d) (m : ℕ) : w ^ m * r * (w ^ m)⁻¹ = r * d ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hdm : w * d ^ m * w⁻¹ = d ^ m := by rw [← conj_pow, hd]
    calc w ^ (m + 1) * r * (w ^ (m + 1))⁻¹ = w * (w ^ m * r * (w ^ m)⁻¹) * w⁻¹ := by
          rw [pow_succ', mul_inv_rev]; simp only [mul_assoc]
      _ = w * r * w⁻¹ * (w * d ^ m * w⁻¹) := by
          rw [ih]; simp only [mul_assoc, inv_mul_cancel_left]
      _ = r * d ^ (m + 1) := by rw [hr, hdm, pow_succ']; simp only [mul_assoc]

theorem centralizes_of_odd_of_q8 (φ : ↥P ≃* QuaternionGroup 2) {q w : G} (hq : q ∈ P)
    (hq2 : q * q ≠ 1) (hwP : ∀ x ∈ P, w * x * w⁻¹ ∈ P)
    (hcomm : q * (w * q * w⁻¹) = w * q * w⁻¹ * q) (hodd : Odd (orderOf w)) :
    ∀ x ∈ P, w * x = x * w := by
  obtain ⟨hC, hN, h4⟩ := q8_facts_of_equiv φ hq hq2
  have hwq : w * q * w⁻¹ = q := by
    have hsq : w * q * w⁻¹ * (w * q * w⁻¹) = w * (q * q) * w⁻¹ := by group
    rcases hC _ (hwP q hq) hcomm with h | h | h | h
    · exfalso
      apply hq2
      have hq1 : q = 1 := by
        calc q = w⁻¹ * (w * q * w⁻¹) * w := by group
          _ = 1 := by rw [h]; group
      rw [hq1, mul_one]
    · exact h
    · exfalso
      apply hq2
      have h1 : w * (q * q) * w⁻¹ = 1 := by
        rw [← hsq, h, ← mul_assoc, h4 q hq]
      calc q * q = w⁻¹ * (w * (q * q) * w⁻¹) * w := by group
        _ = 1 := by rw [h1]; group
    · exact absurd (h.trans (eq_inv_of_mul_eq_one_left (h4 q hq)))
        (conj_ne_inv_of_odd_orderOf hodd hq2)
  have hwq' : w⁻¹ * q * w = q := by
    calc w⁻¹ * q * w = w⁻¹ * (w * q * w⁻¹) * w := by rw [hwq]
      _ = q := by group
  have hfix : ∀ b : G, (b = 1 ∨ b = q ∨ b = q * q ∨ b = q * q * q) → w * b * w⁻¹ = b := by
    rintro b (rfl | rfl | rfl | rfl)
    · group
    · exact hwq
    · calc w * (q * q) * w⁻¹ = w * q * w⁻¹ * (w * q * w⁻¹) := by group
        _ = q * q := by rw [hwq]
    · calc w * (q * q * q) * w⁻¹ = w * q * w⁻¹ * (w * q * w⁻¹) * (w * q * w⁻¹) := by group
        _ = q * q * q := by rw [hwq]
  intro r hr
  obtain ⟨d, hd⟩ : ∃ d : G, d = r⁻¹ * (w * r * w⁻¹) := ⟨_, rfl⟩
  have hdP : d ∈ P := hd ▸ P.mul_mem (P.inv_mem hr) (hwP r hr)
  have hs : w * r * w⁻¹ = r * d := by rw [hd, mul_inv_cancel_left]
  have hrq : w * (r * q * r⁻¹) * w⁻¹ = r * q * r⁻¹ := by
    apply hfix
    rcases hN r hr with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
  have hdq : q * d = d * q := by
    have h1 : w * r * w⁻¹ * q * (w * r * w⁻¹)⁻¹ = r * q * r⁻¹ := by
      calc w * r * w⁻¹ * q * (w * r * w⁻¹)⁻¹ = w * r * (w⁻¹ * q * w) * r⁻¹ * w⁻¹ := by group
        _ = r * q * r⁻¹ := by rw [hwq', ← hrq]; group
    rw [hs] at h1
    calc q * d = r⁻¹ * (r * q * r⁻¹) * (r * d) := by group
      _ = r⁻¹ * (r * d * q * (r * d)⁻¹) * (r * d) := by rw [h1]
      _ = d * q := by group
  have hdfix : w * d * w⁻¹ = d := hfix d (hC d hdP hdq)
  have hk := conj_pow_eq_mul_pow_of_conj_fix hs hdfix (orderOf w)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hk
  have hdk : d ^ orderOf w = 1 := by
    calc d ^ orderOf w = r⁻¹ * (r * d ^ orderOf w) := by rw [inv_mul_cancel_left]
      _ = r⁻¹ * r := by rw [← hk]
      _ = 1 := inv_mul_cancel r
  have hd4 : d ^ (2 ^ 2) = 1 := by
    rw [show (2 ^ 2 : ℕ) = 1 + 1 + 1 + 1 from rfl, pow_succ, pow_succ, pow_succ, pow_one]
    exact h4 d hdP
  have hcop : Nat.Coprime (2 ^ 2) (orderOf w) :=
    Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd)
  have hd1 : d = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one hd4) (orderOf_dvd_of_pow_eq_one hdk))
  calc w * r = w * r * w⁻¹ * w := by group
    _ = r * w := by rw [hs, hd1, mul_one]

end Q8


section NoSplit

theorem centralizes_of_odd_normalizes {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} {K' W : Subgroup Y} {u e g : Y} (hc : P23Cfg n Y R S t K' W u e g)
    (hE : ECase1 R W e) {J : Subgroup Y} (hJ : J = tightCore R ∨ J = K') {P : Subgroup Y}
    (hP : IsSylow2In P J) (hPe : P ≤ Subgroup.centralizer ({e} : Set Y)) {w : Y}
    (hwe : w ∈ Subgroup.centralizer ({e} : Set Y)) (hwodd : Odd (orderOf w))
    (hwP : ∀ x ∈ P, w * x * w⁻¹ ∈ P) : ∀ x ∈ P, w * x = x * w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  have hc2 : IsPGroup 2 (Subgroup.zpowers e) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.he2
  have hNe := normalizer_le_centralizer_e hd
  obtain ⟨R₁, R₁', b₁, b', hR₁, hR₁', hRD, hR'D, -, hb₁R, hb'R', hb₁W, hb'W, ob₁, ob', -⟩ :=
    YGam.e_decomp_W hc
  obtain ⟨hJΩ, hzJ, R₀, b, hR₀, hR₀D, hbR, hbW, hbb⟩ : J ∈ Om R ∧ IsUniqueInvolution J t ∧
      ∃ (R₀ : Subgroup Y) (b : Y), IsSylow2In R₀ J ∧ R₀ ∈ DSet (Om R) W ∧ b ∈ R₀ ∧ b ∈ W ∧
        b * b = t := by
    rcases hJ with rfl | rfl
    · exact ⟨CoreAssembly.mem_conjClass_self _, hz, R₁, b₁, hR₁, hRD, hb₁R, hb₁W, ob₁⟩
    · exact ⟨hc.std.hK'.1, hz', R₁', b', hR₁', hR'D, hb'R', hb'W, ob'⟩
  have hJtq : J ∈ tqMembers3 (Om R) e :=
    ⟨hJΩ, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJΩ ⟨P, hP, hPe⟩⟩
  have hPc : IsSylow2In P (TwinADescent.coreAt e J) :=
    (TwinADescent.isSylow2In_coreAt_iff hc2 hJtq.2).mpr ⟨hP, hPe⟩
  have hR₀c : IsSylow2In R₀ (TwinADescent.coreAt e J) :=
    (TwinADescent.isSylow2In_coreAt_iff hc2 hJtq.2).mpr ⟨hR₀, hR₀D.2.trans hNe⟩
  obtain ⟨x, hxc, hxR⟩ := Asc77.Thompson.exists_conj_of_isSylow2In hR₀c hPc
  have hcE : TwinADescent.coreAt e J ≤ rLayer (Om R) e := TwinDisc.coreAt_le_rLayer hΩ hc2 hJtq
  have hxJ : x ∈ J := TwinADescent.coreAt_le_left e J hxc
  have hqP : x * b * x⁻¹ ∈ P := by
    rw [← hxR]
    exact conj_mem_conjSub hbR
  have hqq : x * b * x⁻¹ * (x * b * x⁻¹) = t := by
    have hxt : x * t * x⁻¹ = t := hzJ.conj_eq (conjSub_eq_self_of_mem hxJ)
    calc x * b * x⁻¹ * (x * b * x⁻¹) = x * (b * b) * x⁻¹ := by group
      _ = t := by rw [hbb, hxt]
  have htP : t ∈ P := by
    rw [← hqq]
    exact P.mul_mem hqP hqP
  have hwt : w * t * w⁻¹ = t := by
    have hm : w * t * w⁻¹ ∈ J := hP.1 (hwP t htP)
    have hsq : w * t * w⁻¹ * (w * t * w⁻¹) = 1 := by
      calc w * t * w⁻¹ * (w * t * w⁻¹) = w * (t * t) * w⁻¹ := by group
        _ = 1 := by rw [hzJ.sq, mul_one, mul_inv_cancel]
    rcases hzJ.unique _ hm hsq with h1 | h1
    · exact absurd (by simpa using h1 : t = 1) hzJ.ne_one
    · exact h1
  have hwtC : w ∈ Subgroup.centralizer ({t} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc w * t = w * t * w⁻¹ * w := by group
      _ = t * w := by rw [hwt]
  obtain ⟨c, hcO, -, hcN⟩ := p23_wnorm hc hE hwtC hwe
  have hE' : rLayer (Om R) e ≤ oddCoreOf (rLayer (Om R) e) ⊔
      (rLayer (Om R) e ⊓ Subgroup.normalizer (W : Set Y)) := hE
  set E := rLayer (Om R) e
  set O := oddCoreOf E
  have hEN : E ≤ Subgroup.normalizer (O : Set Y) := fun _ hy =>
    AscFusion.mem_normalizer_oddCoreOf_of_mem_normalizer' (Subgroup.le_normalizer hy)
  have hcE' : c ∈ E := oddCoreOf_le_self E hcO
  have hxE : x ∈ E := hcE hxc
  have hbE : b ∈ E := hcE (hR₀c.1 hbR)
  have hwNE : w ∈ Subgroup.normalizer (E : Set Y) :=
    mem_normalizer_iff_conjSub_eq.mpr (conjSub_rLayer_eq hΩ hwe)
  have hsplit : ∀ y ∈ E, ∃ o ∈ O, ∃ m ∈ E ⊓ Subgroup.normalizer (W : Set Y), y = o * m := by
    intro y hy
    have h1 : y ∈ ((O ⊔ (E ⊓ Subgroup.normalizer (W : Set Y)) : Subgroup Y) : Set Y) := hE' hy
    rw [Subgroup.coe_mul_of_right_le_normalizer_left O (E ⊓ Subgroup.normalizer (W : Set Y))
      (inf_le_left.trans hEN)] at h1
    obtain ⟨o, ho, m, hm, rfl⟩ := Set.mem_mul.mp h1
    exact ⟨o, ho, m, hm, rfl⟩
  have hqOW : ∃ o ∈ O, ∃ v ∈ W ⊓ E, x * b * x⁻¹ = o * v := by
    obtain ⟨o, ho, m, hm, rfl⟩ := hsplit x hxE
    have hv : m * b * m⁻¹ ∈ W ⊓ E :=
      ⟨(Subgroup.mem_normalizer_iff.mp hm.2 b).mp hbW,
        E.mul_mem (E.mul_mem hm.1 hbE) (E.inv_mem hm.1)⟩
    refine ⟨o * (m * b * m⁻¹ * o⁻¹ * (m * b * m⁻¹)⁻¹), O.mul_mem ho ?_, m * b * m⁻¹, hv,
      by group⟩
    exact (Subgroup.mem_normalizer_iff.mp (hEN hv.2) o⁻¹).mp (O.inv_mem ho)
  have hwOW : ∀ a : Y, (∃ o ∈ O, ∃ v ∈ W ⊓ E, a = o * v) →
      ∃ o ∈ O, ∃ v ∈ W ⊓ E, w * a * w⁻¹ = o * v := by
    rintro _ ⟨o, ho, v, hv, rfl⟩
    obtain ⟨v₂, hv₂⟩ : ∃ v₂ : Y, v₂ = c⁻¹ * w * v * (c⁻¹ * w)⁻¹ := ⟨_, rfl⟩
    have hv₂W : v₂ ∈ W := hv₂ ▸ (Subgroup.mem_normalizer_iff.mp hcN v).mp hv.1
    have hv₂E : v₂ ∈ E := by
      have h1 : w * v * w⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hwNE v).mp hv.2
      have e1 : v₂ = c⁻¹ * (w * v * w⁻¹) * c := by rw [hv₂]; group
      rw [e1]
      exact E.mul_mem (E.mul_mem (E.inv_mem hcE') h1) hcE'
    refine ⟨w * o * w⁻¹ * c * (v₂ * c⁻¹ * v₂⁻¹), ?_, v₂, ⟨hv₂W, hv₂E⟩, by rw [hv₂]; group⟩
    exact O.mul_mem (O.mul_mem (mem_normalizer_oddCoreOf_of_mem_normalizer hwNE ho) hcO)
      ((Subgroup.mem_normalizer_iff.mp (hEN hv₂E) c⁻¹).mp (O.inv_mem hcO))
  have hOP : ∀ k ∈ O, k ∈ P → k = 1 := fun k hkO hkP =>
    eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard E) hkO
      (hP.2.1.to_le (Subgroup.zpowers_le.mpr hkP))
  have hWab := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have hcomm : ∀ a ∈ P, ∀ a' ∈ P, (∃ o ∈ O, ∃ v ∈ W ⊓ E, a = o * v) →
      (∃ o ∈ O, ∃ v ∈ W ⊓ E, a' = o * v) → a * a' = a' * a := by
    rintro _ ha _ ha' ⟨o₁, ho₁, v₁, hv₁, rfl⟩ ⟨o₂, ho₂, v₂, hv₂, rfl⟩
    have h12 : v₁⁻¹ * v₂ = v₂ * v₁⁻¹ :=
      (show Commute v₁ v₂ from hWab v₁ hv₁.1 v₂ hv₂.1).inv_left.eq
    have hk : o₁ * v₁ * (o₂ * v₂) * (o₂ * v₂ * (o₁ * v₁))⁻¹ ∈ O := by
      have e1 : o₁ * v₁ * (o₂ * v₂) * (o₂ * v₂ * (o₁ * v₁))⁻¹ =
          o₁ * (v₁ * o₂ * v₁⁻¹) * (v₂ * o₁⁻¹ * v₂⁻¹) * o₂⁻¹ := by
        calc o₁ * v₁ * (o₂ * v₂) * (o₂ * v₂ * (o₁ * v₁))⁻¹ =
            o₁ * v₁ * o₂ * (v₂ * v₁⁻¹) * o₁⁻¹ * v₂⁻¹ * o₂⁻¹ := by group
          _ = o₁ * v₁ * o₂ * (v₁⁻¹ * v₂) * o₁⁻¹ * v₂⁻¹ * o₂⁻¹ := by rw [h12]
          _ = o₁ * (v₁ * o₂ * v₁⁻¹) * (v₂ * o₁⁻¹ * v₂⁻¹) * o₂⁻¹ := by group
      rw [e1]
      exact O.mul_mem (O.mul_mem (O.mul_mem ho₁
        ((Subgroup.mem_normalizer_iff.mp (hEN hv₁.2) o₂).mp ho₂))
        ((Subgroup.mem_normalizer_iff.mp (hEN hv₂.2) o₁⁻¹).mp (O.inv_mem ho₁))) (O.inv_mem ho₂)
    exact mul_inv_eq_one.mp
      (hOP _ hk (P.mul_mem (P.mul_mem ha ha') (P.inv_mem (P.mul_mem ha' ha))))
  obtain ⟨φ⟩ := members_sylow_q8 hc.std.perp J hJΩ P hP
  have hq2 : x * b * x⁻¹ * (x * b * x⁻¹) ≠ 1 := by
    rw [hqq]
    exact hzJ.ne_one
  exact centralizes_of_odd_of_q8 φ hqP hq2 hwP
    (hcomm _ hqP _ (hwP _ hqP) hqOW (hwOW _ hqOW)) hwodd

theorem centralizes_of_odd_normalizes_orb {n : ℕ} {Y : Type} [Group Y] [Finite Y]
    {R : Subgroup Y} {S : Sylow 2 R} {t : Y} {K' W : Subgroup Y} {u e g : Y}
    (hc : P23Cfg n Y R S t K' W u e g) (hE : ECase1 R W e) {Z : Subgroup Y} {f : Y}
    (hf : f ∈ p23Orb Z t e) {J : Subgroup Y} (hJ : J = tightCore R ∨ J = K') {P : Subgroup Y}
    (hP : IsSylow2In P J) (hPf : P ≤ Subgroup.centralizer ({f} : Set Y)) {w : Y}
    (hwf : w ∈ Subgroup.centralizer ({f} : Set Y)) (hwodd : Odd (orderOf w))
    (hwP : ∀ x ∈ P, w * x * w⁻¹ ∈ P) : ∀ x ∈ P, w * x = x * w := by
  obtain ⟨m, hm, rfl⟩ := hf
  have hmt : m⁻¹ ∈ Subgroup.centralizer ({t} : Set Y) := Subgroup.inv_mem _ hm.1
  have hJ' : conjSub m⁻¹ J = tightCore R ∨ conjSub m⁻¹ J = K' := by
    rcases p23_conj_twins hc hmt with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hJ with rfl | rfl
    · exact Or.inl h1
    · exact Or.inr h2
    · exact Or.inr h1
    · exact Or.inl h2
  have hcent : ∀ y : Y, y * (m * e * m⁻¹) = m * e * m⁻¹ * y →
      m⁻¹ * y * m * e = e * (m⁻¹ * y * m) := by
    intro y hy
    calc m⁻¹ * y * m * e = m⁻¹ * (y * (m * e * m⁻¹)) * m := by group
      _ = m⁻¹ * (m * e * m⁻¹ * y) * m := by rw [hy]
      _ = e * (m⁻¹ * y * m) := by group
  have hP'e : conjSub m⁻¹ P ≤ Subgroup.centralizer ({e} : Set Y) := by
    intro y hy
    rw [mem_conjSub_iff, inv_inv] at hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hcent _ (Subgroup.mem_centralizer_singleton_iff.mp (hPf hy))
    rwa [show m⁻¹ * (m * y * m⁻¹) * m = y by group] at h1
  have hw'e : m⁻¹ * w * m ∈ Subgroup.centralizer ({e} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (hcent w (Subgroup.mem_centralizer_singleton_iff.mp hwf))
  have hw'odd : Odd (orderOf (m⁻¹ * w * m)) := by
    have h := MulEquiv.orderOf_eq (MulAut.conj m⁻¹) w
    rw [MulAut.conj_apply, inv_inv] at h
    rw [h]
    exact hwodd
  have hw'P : ∀ y ∈ conjSub m⁻¹ P, m⁻¹ * w * m * y * (m⁻¹ * w * m)⁻¹ ∈ conjSub m⁻¹ P := by
    intro y hy
    rw [mem_conjSub_iff, inv_inv] at hy ⊢
    rw [show m * (m⁻¹ * w * m * y * (m⁻¹ * w * m)⁻¹) * m⁻¹ = w * (m * y * m⁻¹) * w⁻¹ by group]
    exact hwP _ hy
  have key := centralizes_of_odd_normalizes hc hE hJ' (hP.conj m⁻¹) hP'e hw'e hw'odd hw'P
  intro y hy
  have hy' : m⁻¹ * y * m ∈ conjSub m⁻¹ P := by
    rw [mem_conjSub_iff, inv_inv, show m * (m⁻¹ * y * m) * m⁻¹ = y by group]
    exact hy
  have h1 := key _ hy'
  calc w * y = m * (m⁻¹ * w * m * (m⁻¹ * y * m)) * m⁻¹ := by group
    _ = m * (m⁻¹ * y * m * (m⁻¹ * w * m)) * m⁻¹ := by rw [h1]
    _ = y * w := by group

end NoSplit

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113ClaimsCtx
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113ClaimsT

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut)
open scoped MatrixGroups Pointwise commutatorElement

namespace Lemma113Claims

open scoped Lemma113Claims

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {E A : Subgroup G} {e : G} {K Q : Subgroup G}

theorem exists_x' (c : Ctx E A e K Q) :
    ∃ x : G, x ∈ K ∧ (∀ q ∈ (Q ⊓ K : Subgroup G), x * q * x⁻¹ ∈ (Q ⊓ K : Subgroup G)) ∧
      (∃ a : ℕ, x ^ 13 ^ a = 1) ∧
      (∀ q ∈ (Q ⊓ K : Subgroup G), x ^ 13 * q * (x ^ 13)⁻¹ = q) ∧
      ∀ j : ℕ, 0 < j → j < 13 → ∀ q ∈ (Q ⊓ K : Subgroup G),
        x ^ j * q * (x ^ j)⁻¹ = q → q = 1 := by
  classical
  obtain ⟨e0⟩ := c.hKI
  obtain ⟨t, htN, ht13, htfree⟩ := L2.exists_torus_element e0 (W0 K Q) c.card_W0
  obtain ⟨h, hhK, hhn, w, hw, hh⟩ := c.exists_lift (inv_mem htN)
  have hpow := c.lift_pow hhK hhn hw hh
  have h13 : ∀ q ∈ (Q ⊓ K : Subgroup G), h ^ 13 * q * (h ^ 13)⁻¹ = q := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := hpow 13 q hq
    apply c.pi0_injOn hq1 hq
    rw [hq2]
    have := ht13 (pi0 K q) (pi0_mem_W0 hq)
    simp only [inv_pow, inv_inv]
    exact this
  have h13s : ∀ s : ℕ, ∀ q ∈ (Q ⊓ K : Subgroup G), h ^ (13 * s) * q * (h ^ (13 * s))⁻¹ = q := by
    intro s
    induction s with
    | zero => intro q _; simp
    | succ s ih =>
      intro q hq
      have e1 : h ^ (13 * (s + 1)) * q * (h ^ (13 * (s + 1)))⁻¹ =
          h ^ 13 * (h ^ (13 * s) * q * (h ^ (13 * s))⁻¹) * (h ^ 13)⁻¹ := by
        rw [show 13 * (s + 1) = 13 + 13 * s by ring, pow_add]; group
      rw [e1, ih q hq]
      exact h13 q hq
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos h).ne' 13 (by norm_num)
  have hordh : orderOf h = 13 ^ a * b := hab
  have hmod : ∀ k : ℕ, ∀ q ∈ (Q ⊓ K : Subgroup G),
      h ^ k * q * (h ^ k)⁻¹ = h ^ (k % 13) * q * (h ^ (k % 13))⁻¹ := by
    intro k q hq
    have hk' : k = 13 * (k / 13) + k % 13 := (Nat.div_add_mod k 13).symm
    have hqr := (hpow (k % 13) q hq).1
    conv_lhs => rw [hk', pow_add]
    have e1 : h ^ (13 * (k / 13)) * h ^ (k % 13) * q * (h ^ (13 * (k / 13)) * h ^ (k % 13))⁻¹ =
        h ^ (13 * (k / 13)) * (h ^ (k % 13) * q * (h ^ (k % 13))⁻¹) *
          (h ^ (13 * (k / 13)))⁻¹ := by group
    rw [e1]
    exact h13s _ _ hqr
  have hfreeh : ∀ r : ℕ, r % 13 ≠ 0 → ∀ q ∈ (Q ⊓ K : Subgroup G),
      h ^ r * q * (h ^ r)⁻¹ = q → q = 1 := by
    intro r hr0 q hq hfix
    rw [hmod r q hq] at hfix
    have hrlt : r % 13 < 13 := Nat.mod_lt _ (by norm_num)
    obtain ⟨hq1, hq2⟩ := hpow (r % 13) q hq
    have hpi := congrArg (pi0 K) hfix
    rw [hq2] at hpi
    have hfree := htfree (r % 13) (Nat.pos_of_ne_zero hr0) hrlt (pi0 K q) (pi0_mem_W0 hq) (by
      rw [← inv_pow] at hpi
      simpa [inv_pow] using hpi)
    have h1 : pi0 K 1 = 1 := by
      rw [pi0_of_mem K.one_mem]
      exact QuotientGroup.mk_one _
    apply c.pi0_injOn hq (one_mem _)
    rw [hfree, h1]
  refine ⟨h ^ b, K.pow_mem hhK b, fun q hq => (hpow b q hq).1, ⟨a, ?_⟩, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, ← hordh, pow_orderOf_eq_one]
  · intro q hq
    rw [← pow_mul]
    have := h13s b q hq
    rwa [mul_comm] at this
  · intro j hj0 hj13 q hq hfix
    rw [← pow_mul] at hfix
    apply hfreeh (b * j) _ q hq hfix
    intro h0
    have hdvd : 13 ∣ b * j := Nat.dvd_of_mod_eq_zero h0
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 13)).1 hdvd with h1 | h1
    · exact hb h1
    · have := Nat.le_of_dvd hj0 h1
      omega

theorem ncard_orbit (c : Ctx E A e K Q)
    (hB : ¬ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G)) :
    (MulAction.orbit ↥(Subgroup.normalizer (E : Set G)) (Subgroup.zpowers e : Subgroup G)).ncard
      = 27 := by
  have h1 := c.index_eq hB
  have h2 := card_eq_ncard_orbit_mul (Subgroup.normalizer (E : Set G)) (Subgroup.zpowers e)
  have hpos : 0 < Nat.card ↥(Subgroup.normalizer (E : Set G) ⊓
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G)) := Nat.card_pos
  have : 27 * Nat.card ↥(Subgroup.normalizer (E : Set G) ⊓
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G)) =
      (MulAction.orbit ↥(Subgroup.normalizer (E : Set G))
        (Subgroup.zpowers e : Subgroup G)).ncard *
      Nat.card ↥(Subgroup.normalizer (E : Set G) ⊓
        Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G)) := h1.symm.trans h2
  exact (Nat.eq_of_mul_eq_mul_right hpos this).symm

theorem orbit_eq_image (c : Ctx E A e K Q)
    (hB : ¬ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G)) :
    (MulAction.orbit ↥(Subgroup.normalizer (E : Set G)) (Subgroup.zpowers e : Subgroup G) :
      Set (Subgroup G)) =
      (fun q : G => Subgroup.zpowers (e * q)) '' ((Q ⊓ K : Subgroup G) : Set G) := by
  have hsub : MulAction.orbit ↥(Subgroup.normalizer (E : Set G))
      (Subgroup.zpowers e : Subgroup G) ⊆
      (fun q : G => Subgroup.zpowers (e * q)) '' ((Q ⊓ K : Subgroup G) : Set G) := by
    intro S hS
    obtain ⟨q, hq, rfl⟩ := c.mem_orbit_form hB hS
    exact ⟨q, hq, rfl⟩
  have hle : ((fun q : G => Subgroup.zpowers (e * q)) '' ((Q ⊓ K : Subgroup G) : Set G)).ncard ≤
      (MulAction.orbit ↥(Subgroup.normalizer (E : Set G))
        (Subgroup.zpowers e : Subgroup G)).ncard := by
    rw [c.ncard_orbit hB]
    calc _ ≤ ((Q ⊓ K : Subgroup G) : Set G).ncard := Set.ncard_image_le (Set.toFinite _)
      _ = 27 := by rw [← Nat.card_coe_set_eq]; exact c.card_Q0
  exact Set.eq_of_subset_of_ncard_le hsub hle (Set.toFinite _)

theorem zpowers_form (c : Ctx E A e K Q) {y : G} (hyE : y ∈ E)
    (hyQ0 : y ∉ (Q ⊓ K : Subgroup G)) :
    ∃ q ∈ (Q ⊓ K : Subgroup G), Subgroup.zpowers y = Subgroup.zpowers (e * q) := by
  have hyE' : y ∈ (Q ⊓ K : Subgroup G) ⊔ Subgroup.zpowers e := c.hEeq ▸ hyE
  have hcent : (Q ⊓ K : Subgroup G) ≤ Subgroup.centralizer (Subgroup.zpowers e : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    exact ((Commute.zpow_left (show Commute e q from c.hKe q hq.2) k).eq)
  obtain ⟨q', hq', b, hb, hqb⟩ := exists_mul_of_mem_sup hcent hyE'
  rcases mem_zpowers_cases c.he3 hb with h1 | h1 | h1
  · exfalso
    apply hyQ0
    rw [hqb, h1, mul_one]
    exact hq'
  · refine ⟨q', hq', ?_⟩
    rw [hqb, h1]
    have : q' * e = e * q' := (c.hKe q' hq'.2).symm
    rw [this]
  · refine ⟨q'⁻¹, (Q ⊓ K : Subgroup G).inv_mem hq', ?_⟩
    have : y⁻¹ = e * q'⁻¹ := by
      rw [hqb, h1]
      group
    rw [← this]
    exact Subgroup.zpowers_inv.symm

theorem Q0_invariant (c : Ctx E A e K Q)
    (hB : ¬ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G))
    {n : G} (hn : n ∈ Subgroup.normalizer (E : Set G)) {q : G} (hq : q ∈ (Q ⊓ K : Subgroup G)) :
    n * q * n⁻¹ ∈ (Q ⊓ K : Subgroup G) := by
  by_contra hcon
  set y : G := n * q * n⁻¹ with hy
  have hyE : y ∈ E := (Subgroup.mem_normalizer_iff.1 hn q).1 (c.Q0_le_E hq)
  obtain ⟨q', hq', hzy⟩ := c.zpowers_form hyE hcon
  have hmem : Subgroup.zpowers y ∈ MulAction.orbit ↥(Subgroup.normalizer (E : Set G))
      (Subgroup.zpowers e : Subgroup G) := by
    rw [c.orbit_eq_image hB, hzy]
    exact ⟨q', hq', rfl⟩
  obtain ⟨m, hm⟩ := MulAction.mem_orbit_iff.1 hmem
  have hmw : ∀ w : G, w ∈ Subgroup.zpowers y ↔ (m : G)⁻¹ * w * m ∈ Subgroup.zpowers e := by
    intro w
    rw [← hm, connAct_mem_smul_iff]
  have hme : (m : G) * e * (m : G)⁻¹ ∈ Subgroup.zpowers y := by
    rw [hmw]
    have : (m : G)⁻¹ * ((m : G) * e * (m : G)⁻¹) * m = e := by group
    rw [this]
    exact Subgroup.mem_zpowers e
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hme
  apply c.not_conj_e_into_Q0 hB ((n : G)⁻¹ * m)
  have h0 : (m : G) * e * (m : G)⁻¹ = (n : G) * q ^ k * (n : G)⁻¹ := by
    rw [← hk, hy, conj_zpow]
  have e1 : ((n : G)⁻¹ * (m : G)) * e * ((n : G)⁻¹ * (m : G))⁻¹ = q ^ k := by
    calc ((n : G)⁻¹ * (m : G)) * e * ((n : G)⁻¹ * (m : G))⁻¹
        = (n : G)⁻¹ * ((m : G) * e * (m : G)⁻¹) * (n : G) := by group
      _ = (n : G)⁻¹ * ((n : G) * q ^ k * (n : G)⁻¹) * (n : G) := by rw [h0]
      _ = q ^ k := by group
  rw [e1]
  exact (Q ⊓ K : Subgroup G).zpow_mem hq k

end Ctx

@[expose] def N0 (E Q0 : Subgroup G) : Subgroup G where
  carrier := {n | n ∈ Subgroup.normalizer (E : Set G) ∧ (∀ q ∈ Q0, n * q * n⁻¹ = q) ∧
    ∀ y ∈ E, n * y * n⁻¹ * y⁻¹ ∈ Q0}
  mul_mem' := by
    rintro a b ⟨ha, haq, hay⟩ ⟨hb, hbq, hby⟩
    refine ⟨mul_mem ha hb, fun q hq => ?_, fun y hy => ?_⟩
    · have : a * b * q * (a * b)⁻¹ = a * (b * q * b⁻¹) * a⁻¹ := by group
      rw [this, hbq q hq, haq q hq]
    · have hs := hby y hy
      have e1 : a * b * y * (a * b)⁻¹ * y⁻¹ =
          (a * (b * y * b⁻¹ * y⁻¹) * a⁻¹) * (a * y * a⁻¹ * y⁻¹) := by group
      rw [e1, haq _ hs]
      exact Q0.mul_mem hs (hay y hy)
  one_mem' := ⟨one_mem _, fun q _ => by group, fun y _ => by simp [one_mem]⟩
  inv_mem' := by
    rintro a ⟨ha, haq, hay⟩
    refine ⟨inv_mem ha, fun q hq => ?_, fun y hy => ?_⟩
    · have h1 := haq q hq
      have h2 : a * q = q * a := by
        calc a * q = (a * q * a⁻¹) * a := by group
          _ = q * a := by rw [h1]
      calc a⁻¹ * q * a⁻¹⁻¹ = a⁻¹ * (q * a) := by group
        _ = a⁻¹ * (a * q) := by rw [h2]
        _ = q := by group
    · have hy' : a⁻¹ * y * a ∈ E := by
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem ha) y).1 hy
        simpa using this
      have hu := hay _ hy'
      have e1 : a * (a⁻¹ * y * a) * a⁻¹ * (a⁻¹ * y * a)⁻¹ = (a⁻¹ * y * a * y⁻¹)⁻¹ := by group
      rw [e1] at hu
      have := Q0.inv_mem hu
      simpa [inv_inv] using this

theorem mem_N0 {E Q0 : Subgroup G} {n : G} :
    n ∈ N0 E Q0 ↔ n ∈ Subgroup.normalizer (E : Set G) ∧ (∀ q ∈ Q0, n * q * n⁻¹ = q) ∧
      ∀ y ∈ E, n * y * n⁻¹ * y⁻¹ ∈ Q0 := Iff.rfl

theorem N0_conj {E Q0 : Subgroup G} (hQ : ∀ n ∈ Subgroup.normalizer (E : Set G), ∀ q ∈ Q0,
    n * q * n⁻¹ ∈ Q0) {n k : G} (hn : n ∈ Subgroup.normalizer (E : Set G)) (hk : k ∈ N0 E Q0) :
    n * k * n⁻¹ ∈ N0 E Q0 := by
  obtain ⟨hkN, hkq, hky⟩ := mem_N0.1 hk
  refine mem_N0.2 ⟨?_, fun q hq => ?_, fun y hy => ?_⟩
  · exact mul_mem (mul_mem hn hkN) (inv_mem hn)
  · have hq' : n⁻¹ * q * n ∈ Q0 := by
      have := hQ n⁻¹ (inv_mem hn) q hq
      simpa using this
    have := hkq _ hq'
    calc n * k * n⁻¹ * q * (n * k * n⁻¹)⁻¹ = n * (k * (n⁻¹ * q * n) * k⁻¹) * n⁻¹ := by group
      _ = n * (n⁻¹ * q * n) * n⁻¹ := by rw [this]
      _ = q := by group
  · have hy' : n⁻¹ * y * n ∈ E := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) y).1 hy
      simpa using this
    have hu := hky _ hy'
    have := hQ n hn _ hu
    have e1 : n * (k * (n⁻¹ * y * n) * k⁻¹ * (n⁻¹ * y * n)⁻¹) * n⁻¹ =
        n * k * n⁻¹ * y * (n * k * n⁻¹)⁻¹ * y⁻¹ := by group
    rw [e1] at this
    exact this

theorem centralizer_le_N0 {E Q0 : Subgroup G} (hQE : Q0 ≤ E) :
    Subgroup.centralizer (E : Set G) ≤ N0 E Q0 := by
  intro n hn
  have hc : ∀ y ∈ E, n * y * n⁻¹ = y := by
    intro y hy
    have := Subgroup.mem_centralizer_iff.1 hn y hy
    calc n * y * n⁻¹ = (y * n) * n⁻¹ := by rw [this]
      _ = y := by group
  exact mem_N0.2 ⟨Subgroup.centralizer_le_normalizer (E : Set G) hn, fun q hq => hc q (hQE hq),
    fun y hy => by rw [hc y hy]; simp [Q0.one_mem]⟩

@[expose] def N1 (E Q0 : Subgroup G) : Subgroup G where
  carrier := {n | n ∈ Subgroup.normalizer (E : Set G) ∧ n ∈ Subgroup.normalizer (Q0 : Set G) ∧
    ∀ y ∈ E, n * y * n⁻¹ * y⁻¹ ∈ Q0}
  mul_mem' := by
    rintro a b ⟨ha, haq, hay⟩ ⟨hb, hbq, hby⟩
    refine ⟨mul_mem ha hb, mul_mem haq hbq, fun y hy => ?_⟩
    have e1 : a * b * y * (a * b)⁻¹ * y⁻¹ =
        (a * (b * y * b⁻¹ * y⁻¹) * a⁻¹) * (a * y * a⁻¹ * y⁻¹) := by group
    rw [e1]
    exact Q0.mul_mem ((Subgroup.mem_normalizer_iff.1 haq _).1 (hby y hy)) (hay y hy)
  one_mem' := ⟨one_mem _, one_mem _, fun y _ => by simp [one_mem]⟩
  inv_mem' := by
    rintro a ⟨ha, haq, hay⟩
    refine ⟨inv_mem ha, inv_mem haq, fun y hy => ?_⟩
    have hy' : a⁻¹ * y * a ∈ E := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem ha) y).1 hy
      simpa using this
    have hu := hay _ hy'
    have e1 : a * (a⁻¹ * y * a) * a⁻¹ * (a⁻¹ * y * a)⁻¹ = (a⁻¹ * y * a * y⁻¹)⁻¹ := by group
    rw [e1] at hu
    have := Q0.inv_mem hu
    simpa [inv_inv] using this

theorem mem_N1 {E Q0 : Subgroup G} {n : G} :
    n ∈ N1 E Q0 ↔ n ∈ Subgroup.normalizer (E : Set G) ∧
      n ∈ Subgroup.normalizer (Q0 : Set G) ∧ ∀ y ∈ E, n * y * n⁻¹ * y⁻¹ ∈ Q0 := Iff.rfl

theorem N0_le_N1 {E Q0 : Subgroup G} : N0 E Q0 ≤ N1 E Q0 := by
  intro n hn
  obtain ⟨hnN, hnq, hny⟩ := mem_N0.1 hn
  refine mem_N1.2 ⟨hnN, mem_normalizer_of_conj_le fun q hq => ?_, hny⟩
  rw [hnq q hq]
  exact hq

section Generic

@[expose] noncomputable def conjPermOn (X : Set G) (g : G) (h : ∀ y ∈ X, g * y * g⁻¹ ∈ X) :
    Equiv.Perm ↥X :=
  Equiv.ofBijective (fun y : ↥X => (⟨g * (y : G) * g⁻¹, h y y.2⟩ : ↥X)) (by
    have hinj : Function.Injective (fun y : ↥X => (⟨g * (y : G) * g⁻¹, h y y.2⟩ : ↥X)) := by
      intro a b hab
      have h1 : g * (a : G) * g⁻¹ = g * (b : G) * g⁻¹ := congrArg Subtype.val hab
      exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
    exact Finite.injective_iff_bijective.1 hinj)

theorem conjPermOn_apply (X : Set G) (g : G) (h : ∀ y ∈ X, g * y * g⁻¹ ∈ X) (y : ↥X) :
    (((conjPermOn X g h) y : ↥X) : G) = g * (y : G) * g⁻¹ := rfl

theorem conjPermOn_pow (X : Set G) (g : G) (h : ∀ y ∈ X, g * y * g⁻¹ ∈ X) (k : ℕ) (y : ↥X) :
    (((conjPermOn X g h) ^ k) y : G) = g ^ k * (y : G) * (g ^ k)⁻¹ := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, conjPermOn_apply, ih, pow_succ']
    group

theorem exists_fixed_conj {X : Set G} {g : G} {a : ℕ} (hga : g ^ 13 ^ a = 1)
    (hcl : ∀ y ∈ X, g * y * g⁻¹ ∈ X) (hcard : ¬ 13 ∣ Nat.card ↥X) :
    ∃ y ∈ X, g * y * g⁻¹ = y := by
  classical
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  haveI : Fintype ↥X := Fintype.ofFinite _
  have hσ : (conjPermOn X g hcl) ^ 13 ^ a = 1 := by
    ext y
    rw [conjPermOn_pow, hga]
    simp
  obtain ⟨y, hy⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 13) (n := a)
    (by rwa [← Nat.card_eq_fintype_card]) hσ
  refine ⟨y, y.2, ?_⟩
  have := congrArg Subtype.val hy
  simpa [conjPermOn] using this

theorem invariant_subgroup_eq {Q0 S : Subgroup G} (hcard : Nat.card ↥Q0 = 27) (hS : S ≤ Q0)
    {x : G} {a : ℕ} (hxa : x ^ 13 ^ a = 1)
    (hfree : ∀ q ∈ Q0, x * q * x⁻¹ = q → q = 1) (hxS : ∀ s ∈ S, x * s * x⁻¹ ∈ S) :
    S = ⊥ ∨ S = Q0 := by
  classical
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  haveI : Fintype ↥(S : Set G) := Fintype.ofFinite _
  have hS1 : (1 : G) ∈ (S : Set G) := S.one_mem
  have hσ : (conjPermOn (S : Set G) x hxS) ^ 13 ^ a = 1 := by
    ext y
    rw [conjPermOn_pow, hxa]
    simp
  have hmod := Equiv.Perm.card_compl_support_modEq (p := 13) hσ
  have hsupp : (conjPermOn (S : Set G) x hxS).supportᶜ = {⟨(1 : G), hS1⟩} := by
    ext y
    simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not, Finset.mem_singleton]
    constructor
    · intro hy
      have hy' : x * (y : G) * x⁻¹ = (y : G) := by
        have := congrArg Subtype.val hy
        simpa [conjPermOn] using this
      exact Subtype.ext (hfree y (hS y.2) hy')
    · intro hy
      subst hy
      apply Subtype.ext
      simp [conjPermOn]
  rw [hsupp, Finset.card_singleton, ← Nat.card_eq_fintype_card] at hmod
  have hdvd : Nat.card ↥S ∣ 27 := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le hS
  have hcardS : Nat.card ↥(S : Set G) = Nat.card ↥S := rfl
  rw [hcardS] at hmod
  obtain ⟨i, hi, hiS⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).1
    (show Nat.card ↥S ∣ 3 ^ 3 by simpa using hdvd)
  have hmod' : 1 % 13 = Nat.card ↥S % 13 := hmod
  interval_cases i
  · left
    exact Subgroup.card_eq_one.1 (by simpa using hiS)
  · rw [hiS] at hmod'; norm_num at hmod'
  · rw [hiS] at hmod'; norm_num at hmod'
  · right
    exact Subgroup.eq_of_le_of_card_ge hS (by rw [hcard, hiS]; norm_num)

theorem exists_pow_pPart (p : ℕ) [hp : Fact p.Prime] (n : G) :
    ∃ k a : ℕ, (n ^ k) ^ p ^ a = 1 ∧ k % p = 1 := by
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos n).ne' p hp.out.ne_one
  refine ⟨b ^ (p - 1), a, ?_, ?_⟩
  · have h1 : n ^ (p ^ a * b) = 1 := by rw [← hab]; exact pow_orderOf_eq_one n
    have hpos : 0 < p - 1 := Nat.sub_pos_of_lt hp.out.one_lt
    obtain ⟨t, ht⟩ : ∃ t, p - 1 = t + 1 := ⟨p - 2, by omega⟩
    rw [← pow_mul]
    have : b ^ (p - 1) * p ^ a = (p ^ a * b) * b ^ t := by rw [ht]; ring
    rw [this, pow_mul, h1, one_pow]
  · have hcop : Nat.Coprime b p := (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hb))
    have := Nat.ModEq.pow_totient hcop
    rw [Nat.totient_prime hp.out] at this
    have h2 : b ^ (p - 1) % p = 1 % p := this
    rwa [Nat.mod_eq_of_lt hp.out.one_lt] at h2

theorem isSylowIn_inf_normal {p : ℕ} [Fact p.Prime] {N N₀ R : Subgroup G} (hN₀ : N₀ ≤ N)
    (hnorm : ∀ n ∈ N, ∀ k ∈ N₀, n * k * n⁻¹ ∈ N₀) (hR : IsSylowIn p N R) :
    IsSylowIn p N₀ (R ⊓ N₀) := by
  refine ⟨inf_le_right, hR.2.1.to_le inf_le_left, fun S hSN₀ hSp hle => ?_⟩
  obtain ⟨c, hcN, hc⟩ := Lemma113b.exists_conj_mem_of_isSylowIn hR (hSN₀.trans hN₀) hSp
  have hsub : S.map (MulAut.conj c).toMonoidHom ≤ R ⊓ N₀ := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨hc s hs, hnorm c hcN s (hSN₀ hs)⟩
  have hcard : Nat.card ↥S ≤ Nat.card ↥(R ⊓ N₀ : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective (f := (MulAut.conj c).toMonoidHom)
      (MulAut.conj c).injective]
    exact Subgroup.card_le_of_le hsub
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem exists_conj_normalizes {p : ℕ} [Fact p.Prime] {N₀ T : Subgroup G} (hT : IsSylowIn p N₀ T)
    {x : G} (hx : ∀ k ∈ N₀, x * k * x⁻¹ ∈ N₀) :
    ∃ c ∈ N₀, c * x ∈ Subgroup.normalizer (T : Set G) := by
  have hS : T.map (MulAut.conj x).toMonoidHom ≤ N₀ := by
    rintro _ ⟨t, ht, rfl⟩
    exact hx t (hT.1 ht)
  obtain ⟨c, hcN, hc⟩ := Lemma113b.exists_conj_mem_of_isSylowIn hT hS (hT.2.1.map _)
  refine ⟨c, hcN, mem_normalizer_of_conj_le fun t ht => ?_⟩
  have := hc (x * t * x⁻¹) ⟨t, ht, rfl⟩
  have e1 : c * x * t * (c * x)⁻¹ = c * (x * t * x⁻¹) * c⁻¹ := by group
  rw [e1]
  exact this

theorem isPGroup_zpowers {p : ℕ} {x : G} {a : ℕ} (hx : x ^ p ^ a = 1) :
    IsPGroup p ↥(Subgroup.zpowers x) := by
  intro g
  refine ⟨a, ?_⟩
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 g.2
  apply Subtype.ext
  show (g : G) ^ p ^ a = 1
  rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

theorem pow_conj_mem {Q0 : Subgroup G} {g : G} (hg : ∀ q ∈ Q0, g * q * g⁻¹ ∈ Q0) (j : ℕ) :
    ∀ q ∈ Q0, g ^ j * q * (g ^ j)⁻¹ ∈ Q0 := by
  induction j with
  | zero => intro q hq; simpa using hq
  | succ j ih =>
    intro q hq
    have : g ^ (j + 1) * q * (g ^ (j + 1))⁻¹ = g ^ j * (g * q * g⁻¹) * (g ^ j)⁻¹ := by
      rw [pow_succ]; group
    rw [this]
    exact ih _ (hg q hq)

theorem pow_act_mod {Q0 : Subgroup G} {g : G} (hg : ∀ q ∈ Q0, g * q * g⁻¹ ∈ Q0) {n : ℕ}
    (hn : ∀ q ∈ Q0, g ^ n * q * (g ^ n)⁻¹ = q) (k : ℕ) :
    ∀ q ∈ Q0, g ^ k * q * (g ^ k)⁻¹ = g ^ (k % n) * q * (g ^ (k % n))⁻¹ := by
  have hns : ∀ s : ℕ, ∀ q ∈ Q0, g ^ (n * s) * q * (g ^ (n * s))⁻¹ = q := by
    intro s
    induction s with
    | zero => intro q _; simp
    | succ s ih =>
      intro q hq
      have e1 : g ^ (n * (s + 1)) * q * (g ^ (n * (s + 1)))⁻¹ =
          g ^ n * (g ^ (n * s) * q * (g ^ (n * s))⁻¹) * (g ^ n)⁻¹ := by
        rw [show n * (s + 1) = n + n * s by ring, pow_add]; group
      rw [e1, ih q hq]
      exact hn q hq
  intro q hq
  have hk : k = n * (k / n) + k % n := (Nat.div_add_mod k n).symm
  conv_lhs => rw [hk, pow_add]
  have e1 : g ^ (n * (k / n)) * g ^ (k % n) * q * (g ^ (n * (k / n)) * g ^ (k % n))⁻¹ =
      g ^ (n * (k / n)) * (g ^ (k % n) * q * (g ^ (k % n))⁻¹) * (g ^ (n * (k / n)))⁻¹ := by
    group
  rw [e1]
  exact hns _ _ (pow_conj_mem hg _ q hq)

omit [Finite G] in
theorem exists_mul_of_mem_sup_norm {H K : Subgroup G} (hH : H ≤ Subgroup.normalizer (K : Set G))
    {x : G} (hx : x ∈ H ⊔ K) : ∃ y ∈ H, ∃ z ∈ K, y * z = x := by
  set L := H ⊔ K with hL
  have : (K.subgroupOf L).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hH
  have hx' : (⟨x, hx⟩ : L) ∈ H.subgroupOf L ⊔ K.subgroupOf L := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.mp hx'
  exact ⟨y, hy, z, hz, congrArg Subtype.val hyz⟩

theorem thompsonJ_eq_of_key {R E : Subgroup G} (hE : IsEkIn 3 4 R E)
    (key : ∀ E1 : Subgroup G, E1 ≤ R → IsElemAbelian 3 E1 → 3 ^ 4 ≤ Nat.card E1 → E1 ≤ E) :
    thompsonJ 3 R = E ∧ CFSG.Open.pRank 3 R = 4 := by
  have hpR : CFSG.Open.pRank 3 R = 4 := by
    unfold CFSG.Open.pRank
    apply le_antisymm
    · apply csSup_le
      · exact ⟨4, E, hE.1, hE.2.1, hE.2.2⟩
      · rintro k ⟨E1, hE1R, hE1ab, hE1card⟩
        by_contra hk
        push Not at hk
        have h81 : 3 ^ 4 ≤ Nat.card E1 := by
          rw [hE1card]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
        have hle : Nat.card E1 ≤ Nat.card E := Subgroup.card_le_of_le (key E1 hE1R hE1ab h81)
        rw [hE.2.2, hE1card] at hle
        have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 hle
        omega
    · apply le_csSup
      · refine ⟨4, ?_⟩
        rintro k ⟨E1, hE1R, hE1ab, hE1card⟩
        by_contra hk
        push Not at hk
        have h81 : 3 ^ 4 ≤ Nat.card E1 := by
          rw [hE1card]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
        have hle : Nat.card E1 ≤ Nat.card E := Subgroup.card_le_of_le (key E1 hE1R hE1ab h81)
        rw [hE.2.2, hE1card] at hle
        have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 hle
        omega
      · exact ⟨E, hE.1, hE.2.1, hE.2.2⟩
  refine ⟨?_, hpR⟩
  unfold thompsonJ
  simp only [hpR]
  apply le_antisymm
  · refine iSup₂_le fun E' hE' => ?_
    exact key E' hE'.1 hE'.2.1 (le_of_eq hE'.2.2.symm)
  · exact le_iSup₂ (f := fun (E'' : Subgroup G) (_ : IsEkIn 3 4 R E'') => E'') E hE

theorem card_eq_of_isSylowIn {p : ℕ} [Fact p.Prime] {Y R R' : Subgroup G} (h : IsSylowIn p Y R)
    (h' : IsSylowIn p Y R') : Nat.card ↥R' = Nat.card ↥R := by
  have key : ∀ {X X' : Subgroup G}, IsSylowIn p Y X → IsSylowIn p Y X' →
      Nat.card ↥X' ≤ Nat.card ↥X := by
    intro X X' hX hX'
    obtain ⟨c, -, hc⟩ := Lemma113b.exists_conj_mem_of_isSylowIn hX hX'.1 hX'.2.1
    have hsub : X'.map (MulAut.conj c).toMonoidHom ≤ X := by
      rintro _ ⟨s, hs, rfl⟩
      exact hc s hs
    rw [← Subgroup.card_map_of_injective (f := (MulAut.conj c).toMonoidHom)
      (MulAut.conj c).injective]
    exact Subgroup.card_le_of_le hsub
  exact le_antisymm (key h h') (key h' h)

end Generic

namespace Ctx

variable {E A : Subgroup G} {e : G} {K Q : Subgroup G}

theorem E_comm (c : Ctx E A e K Q) {x y : G} (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x :=
  Lemma113f.comm_of_isElemAbelian c.hEel hx hy

theorem Q0_comm (c : Ctx E A e K Q) {x y : G} (hx : x ∈ (Q ⊓ K : Subgroup G))
    (hy : y ∈ (Q ⊓ K : Subgroup G)) : x * y = y * x :=
  c.E_comm (c.Q0_le_E hx) (c.Q0_le_E hy)

theorem Q0_pow_three (c : Ctx E A e K Q) {q : G} (hq : q ∈ (Q ⊓ K : Subgroup G)) : q ^ 3 = 1 :=
  c.Q0_elemAbelian.2 q hq

theorem e_not_mem_Q0 (c : Ctx E A e K Q) : e ∉ (Q ⊓ K : Subgroup G) := by
  intro h
  have hmem : e ∈ (Q ⊓ K : Subgroup G) ⊓ centBar 3 Q K := ⟨h, c.e_mem_centBar⟩
  rw [c.Q0_inf_centBar, Subgroup.mem_bot] at hmem
  exact c.he1 hmem

theorem E_le_centralizer (c : Ctx E A e K Q) : E ≤ Subgroup.centralizer (E : Set G) :=
  fun y hy => Subgroup.mem_centralizer_iff.2 fun z hz => c.E_comm hz hy

theorem e_conj_Q0 (c : Ctx E A e K Q) {q : G} (hq : q ∈ (Q ⊓ K : Subgroup G)) :
    e * q * e⁻¹ = q := by
  calc e * q * e⁻¹ = q * e * e⁻¹ := by rw [c.hKe q hq.2]
    _ = q := by group

theorem Q0_le_centralizer_zpowers (c : Ctx E A e K Q) :
    (Q ⊓ K : Subgroup G) ≤ Subgroup.centralizer (Subgroup.zpowers e : Set G) := by
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  exact ((Commute.zpow_left (show Commute e q from c.hKe q hq.2) k).eq)

theorem inf_centralizer_R (c : Ctx E A e K Q)
    (hB : ¬ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G))
    {R : Subgroup G} (hR : IsSylowIn 3 (Subgroup.normalizer (E : Set G)) R) (hQR : Q ≤ R) :
    R ⊓ Subgroup.centralizer (E : Set G) = E :=
  (c.sylow_centralizer_E hB).2.2 _ inf_le_right (hR.2.1.to_le inf_le_left)
    (le_inf (c.hEQ.trans hQR) c.E_le_centralizer)

theorem mem_normalizer_Q0 (c : Ctx E A e K Q)
    (hB : ¬ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G))
    {n : G} (hn : n ∈ Subgroup.normalizer (E : Set G)) :
    n ∈ Subgroup.normalizer (((Q ⊓ K : Subgroup G)) : Set G) :=
  mem_normalizer_of_conj_le fun _ hq => c.Q0_invariant hB hn hq

theorem mem_N0_of_e (c : Ctx E A e K Q) {n : G} (hn : n ∈ Subgroup.normalizer (E : Set G))
    (hnq : ∀ q ∈ (Q ⊓ K : Subgroup G), n * q * n⁻¹ = q)
    (hne : n * e * n⁻¹ * e⁻¹ ∈ (Q ⊓ K : Subgroup G)) : n ∈ N0 E (Q ⊓ K) := by
  refine mem_N0.2 ⟨hn, hnq, fun y hy => ?_⟩
  have hyE' : y ∈ (Q ⊓ K : Subgroup G) ⊔ Subgroup.zpowers e := c.hEeq ▸ hy
  obtain ⟨q', hq', b, hb, hqb⟩ := exists_mul_of_mem_sup c.Q0_le_centralizer_zpowers hyE'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  set u := n * e * n⁻¹ * e⁻¹ with hu
  have hune : n * e * n⁻¹ = u * e := by rw [hu]; group
  have hcomm : Commute u e := (c.hKe u hne.2).symm
  have hconj : n * e ^ i * n⁻¹ = (u * e) ^ i := by rw [← hune]; exact conj_zpow.symm
  have key : n * y * n⁻¹ * y⁻¹ = q' * u ^ i * q'⁻¹ := by
    rw [hqb]
    have h1 : n * (q' * e ^ i) * n⁻¹ * (q' * e ^ i)⁻¹ =
        (n * q' * n⁻¹) * (n * e ^ i * n⁻¹) * (e ^ i)⁻¹ * q'⁻¹ := by group
    rw [h1, hnq q' hq', hconj, hcomm.mul_zpow]
    group
  rw [key]
  exact (Q ⊓ K : Subgroup G).mul_mem
    ((Q ⊓ K : Subgroup G).mul_mem hq' ((Q ⊓ K : Subgroup G).zpow_mem hne i))
    ((Q ⊓ K : Subgroup G).inv_mem hq')

theorem sq_mem_N0 (c : Ctx E A e K Q)
    (hB : ¬ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G))
    {n : G} (hn : n ∈ Subgroup.normalizer (E : Set G))
    (hnq : ∀ q ∈ (Q ⊓ K : Subgroup G), n * q * n⁻¹ = q) : n * n ∈ N0 E (Q ⊓ K) := by
  apply c.mem_N0_of_e (mul_mem hn hn)
  · intro q hq
    calc n * n * q * (n * n)⁻¹ = n * (n * q * n⁻¹) * n⁻¹ := by group
      _ = q := by rw [hnq q hq, hnq q hq]
  · have hy₁E : n * e * n⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.1 hn e).1 c.heE
    have hy₁Q : n * e * n⁻¹ ∉ (Q ⊓ K : Subgroup G) := fun h => c.not_conj_e_into_Q0 hB n h
    obtain ⟨q, hq, hzy⟩ := c.zpowers_form hy₁E hy₁Q
    have hy₁mem : n * e * n⁻¹ ∈ Subgroup.zpowers (e * q) := hzy ▸ Subgroup.mem_zpowers _
    have hy3 : (e * q) ^ 3 = 1 := by
      have hqe : Commute e q := c.hKe q hq.2
      rw [hqe.mul_pow, c.he3, c.Q0_pow_three hq, one_mul]
    have heq : e * q * e⁻¹ = q := c.e_conj_Q0 hq
    rcases mem_zpowers_cases hy3 hy₁mem with h1 | h1 | h1
    · exfalso
      apply c.he1
      calc e = n⁻¹ * (n * e * n⁻¹) * n := by group
        _ = 1 := by rw [h1]; group
    ·
      have h2 : n * n * e * (n * n)⁻¹ * e⁻¹ = (e * q * e⁻¹) * (e * q * e⁻¹) := by
        have h3 : n * n * e * (n * n)⁻¹ = n * (n * e * n⁻¹) * n⁻¹ := by group
        rw [h3, h1]
        have h4 : n * (e * q) * n⁻¹ = (n * e * n⁻¹) * (n * q * n⁻¹) := by group
        rw [h4, h1, hnq q hq]
        group
      rw [h2, heq]
      exact (Q ⊓ K : Subgroup G).mul_mem hq hq
    ·
      have h2 : n * (e * q)⁻¹ * n⁻¹ = ((e * q)⁻¹ * q)⁻¹ := by
        have h4 : n * (e * q) * n⁻¹ = (n * e * n⁻¹) * (n * q * n⁻¹) := by group
        rw [h1, hnq q hq] at h4
        calc n * (e * q)⁻¹ * n⁻¹ = (n * (e * q) * n⁻¹)⁻¹ := by group
          _ = _ := by rw [h4]
      have h3 : n * n * e * (n * n)⁻¹ = n * (n * e * n⁻¹) * n⁻¹ := by group
      have h5 : ((e * q)⁻¹ * q)⁻¹ = e := by
        have : q⁻¹ * e * q = e := by
          have h6 : e * q = q * e := c.hKe q hq.2
          calc q⁻¹ * e * q = q⁻¹ * (e * q) := by group
            _ = q⁻¹ * (q * e) := by rw [h6]
            _ = e := by group
        calc ((e * q)⁻¹ * q)⁻¹ = q⁻¹ * e * q := by group
          _ = e := this
      rw [h3, h1, h2, h5]
      simp [(Q ⊓ K : Subgroup G).one_mem]

theorem mem_N0_of_odd (c : Ctx E A e K Q)
    (hB : ¬ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G))
    {r : G} (hr : r ∈ Subgroup.normalizer (E : Set G))
    (hrq : ∀ q ∈ (Q ⊓ K : Subgroup G), r * q * r⁻¹ = q) {k : ℕ} (hk : Odd k) (hrk : r ^ k = 1) :
    r ∈ N0 E (Q ⊓ K) := by
  obtain ⟨t, rfl⟩ := hk
  have h1 : r = (r * r) ^ (t + 1) := by
    have : r ^ (2 * t + 1) = 1 := hrk
    calc r = r * r ^ (2 * t + 1) := by rw [this, mul_one]
      _ = (r * r) ^ (t + 1) := by rw [← pow_succ', ← sq, ← pow_mul]; ring_nf
  rw [h1]
  exact (N0 E (Q ⊓ K)).pow_mem (c.sq_mem_N0 hB hr hrq) _

end Ctx

section Shear

variable {E Q0 : Subgroup G}

theorem N0.centralizes {n q : G} (hn : n ∈ N0 E Q0) (hq : q ∈ Q0) : n * q * n⁻¹ = q :=
  (mem_N0.1 hn).2.1 q hq

theorem N0.shear_mem {n y : G} (hn : n ∈ N0 E Q0) (hy : y ∈ E) : n * y * n⁻¹ * y⁻¹ ∈ Q0 :=
  (mem_N0.1 hn).2.2 y hy

theorem N0.mem_normalizer {n : G} (hn : n ∈ N0 E Q0) : n ∈ Subgroup.normalizer (E : Set G) :=
  (mem_N0.1 hn).1

theorem shear_mul (hab : ∀ a ∈ Q0, ∀ b ∈ Q0, a * b = b * a) {n m y : G} (hn : n ∈ N0 E Q0)
    (hm : m ∈ N0 E Q0) (hy : y ∈ E) :
    (n * m) * y * (n * m)⁻¹ * y⁻¹ = (n * y * n⁻¹ * y⁻¹) * (m * y * m⁻¹ * y⁻¹) := by
  have h1 := N0.centralizes hn (N0.shear_mem hm hy)
  have h2 := hab _ (N0.shear_mem hn hy) _ (N0.shear_mem hm hy)
  calc (n * m) * y * (n * m)⁻¹ * y⁻¹
      = (n * (m * y * m⁻¹ * y⁻¹) * n⁻¹) * (n * y * n⁻¹ * y⁻¹) := by group
    _ = (m * y * m⁻¹ * y⁻¹) * (n * y * n⁻¹ * y⁻¹) := by rw [h1]
    _ = (n * y * n⁻¹ * y⁻¹) * (m * y * m⁻¹ * y⁻¹) := h2.symm

@[expose] noncomputable def shear (hab : ∀ a ∈ Q0, ∀ b ∈ Q0, a * b = b * a) {y : G} (hy : y ∈ E) :
    ↥(N0 E Q0) →* ↥Q0 where
  toFun n := ⟨(n : G) * y * (n : G)⁻¹ * y⁻¹, N0.shear_mem n.2 hy⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' n m := by
    apply Subtype.ext
    exact shear_mul hab n.2 m.2 hy

theorem shear_apply (hab : ∀ a ∈ Q0, ∀ b ∈ Q0, a * b = b * a) {y : G} (hy : y ∈ E)
    (n : ↥(N0 E Q0)) : ((shear hab hy n : ↥Q0) : G) = (n : G) * y * (n : G)⁻¹ * y⁻¹ := rfl

theorem shear_eq_one_iff (hab : ∀ a ∈ Q0, ∀ b ∈ Q0, a * b = b * a) {y : G} (hy : y ∈ E)
    (n : ↥(N0 E Q0)) : shear hab hy n = 1 ↔ (n : G) * y = y * (n : G) := by
  constructor
  · intro h
    have h1 : (n : G) * y * (n : G)⁻¹ * y⁻¹ = 1 := by
      have := congrArg Subtype.val h
      simpa [shear_apply] using this
    have h2 : (n : G) * y = y * (n : G) := by
      have := mul_inv_eq_one.1 (show (n : G) * y * (n : G)⁻¹ * y⁻¹ = 1 from h1)
      calc (n : G) * y = (n : G) * y * (n : G)⁻¹ * (n : G) := by group
        _ = (y) * (n : G) := by
          have h3 : (n : G) * y * (n : G)⁻¹ = y := mul_inv_eq_one.1 h1
          rw [h3]
    exact h2
  · intro h
    apply Subtype.ext
    show (n : G) * y * (n : G)⁻¹ * y⁻¹ = 1
    rw [h]
    group

end Shear

section Counting2

theorem relIndex_inf_centralizer_dvd {R Q0 : Subgroup G} (hR : R ≤ Subgroup.normalizer (Q0 : Set G)) :
    (Subgroup.centralizer (Q0 : Set G) ⊓ R).relIndex R ∣ Nat.card (MulAut ↥Q0) := by
  set ρ : ↥R →* MulAut ↥Q0 := (Subgroup.normalizerMonoidHom Q0).comp (Subgroup.inclusion hR)
    with hρ
  have hker : ρ.ker = (Subgroup.centralizer (Q0 : Set G) ⊓ R).subgroupOf R := by
    rw [← MonoidHom.comap_ker, Subgroup.normalizerMonoidHom_ker]
    ext r
    simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    simp [Subgroup.inclusion]
  have h1 : (Subgroup.centralizer (Q0 : Set G) ⊓ R).relIndex R = Nat.card ρ.range := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  rw [h1]
  exact Subgroup.card_subgroup_dvd_card _

theorem card_le_mul_inf_centralizer {R Q0 : Subgroup G} (hR : R ≤ Subgroup.normalizer (Q0 : Set G))
    (hRp : IsPGroup 3 ↥R) (hcard : Nat.card (MulAut ↥Q0) = 11232) :
    Nat.card ↥R ≤ 27 * Nat.card ↥(Subgroup.centralizer (Q0 : Set G) ⊓ R : Subgroup G) := by
  have hdvd := relIndex_inf_centralizer_dvd hR
  rw [hcard] at hdvd
  have hmul := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (Q0 : Set G) ⊓ R) (K := R)
  rw [inf_assoc, inf_idem] at hmul
  obtain ⟨t, ht⟩ := (IsPGroup.iff_card (p := 3)).1 hRp
  have hdvdR : (Subgroup.centralizer (Q0 : Set G) ⊓ R).relIndex R ∣ 3 ^ t := by
    rw [← ht, ← hmul]
    exact Dvd.intro _ rfl
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvdR
  have hj3 : j ≤ 3 := by
    by_contra h
    push Not at h
    have h81 : 81 ∣ 3 ^ j := by
      have : 3 ^ 4 ∣ 3 ^ j := pow_dvd_pow 3 (by omega)
      simpa using this
    rw [← hj] at h81
    have := h81.trans hdvd
    omega
  have hle : (Subgroup.centralizer (Q0 : Set G) ⊓ R).relIndex R ≤ 27 := by
    rw [hj]
    calc 3 ^ j ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hj3
      _ = 27 := by norm_num
  calc Nat.card ↥R = (Subgroup.centralizer (Q0 : Set G) ⊓ R).relIndex R *
        Nat.card ↥(Subgroup.centralizer (Q0 : Set G) ⊓ R : Subgroup G) := hmul.symm
    _ ≤ 27 * Nat.card ↥(Subgroup.centralizer (Q0 : Set G) ⊓ R : Subgroup G) :=
        Nat.mul_le_mul_right _ hle

end Counting2

structure RCfg (E A : Subgroup G) (e : G) (K Q R : Subgroup G) : Prop where
  ctx : Ctx E A e K Q
  hB : ¬ Subgroup.normalizer (E : Set G) ≤
    Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G)
  hR : IsSylowIn 3 (Subgroup.normalizer (E : Set G)) R
  hQR : Q ≤ R
  hR8 : Nat.card ↥R = 3 ^ 8

namespace RCfg

variable {E A : Subgroup G} {e : G} {K Q R : Subgroup G} (r : RCfg E A e K Q R)

include r

theorem hRN : R ≤ Subgroup.normalizer (E : Set G) := r.hR.1

theorem hRp : IsPGroup 3 ↥R := r.hR.2.1

theorem R_le_normalizer_Q0 : R ≤ Subgroup.normalizer (((Q ⊓ K : Subgroup G)) : Set G) :=
  fun _ hn => r.ctx.mem_normalizer_Q0 r.hB (r.hRN hn)

theorem E_le_R : E ≤ R := r.ctx.hEQ.trans r.hQR

theorem inf_centralizer_E : R ⊓ Subgroup.centralizer (E : Set G) = E :=
  r.ctx.inf_centralizer_R r.hB r.hR r.hQR

theorem card_mulAut_Q0 : Nat.card (MulAut ↥(Q ⊓ K : Subgroup G)) = 11232 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ a b : ↥(Q ⊓ K : Subgroup G), a * b = b * a := fun a b =>
    Subtype.ext (r.ctx.Q0_comm a.2 b.2)
  have hpow : ∀ a : ↥(Q ⊓ K : Subgroup G), a ^ 3 = 1 := fun a =>
    Subtype.ext (by simpa using r.ctx.Q0_pow_three a.2)
  obtain ⟨eQ⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 3) hcomm hpow
    (n := 3) r.ctx.card_Q0
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL eQ,
    CFSG.SectionRank.Ccomm.card_GL_zmod (p := 3) 3]
  simp [Fin.prod_univ_three]

theorem three_pow_five_le_card_centralizer :
    3 ^ 5 ≤ Nat.card ↥(Subgroup.centralizer (((Q ⊓ K : Subgroup G)) : Set G) ⊓ R : Subgroup G) := by
  have h := card_le_mul_inf_centralizer r.R_le_normalizer_Q0 r.hRp r.card_mulAut_Q0
  rw [r.hR8] at h
  omega

theorem exists_centralizing_not_mem_E :
    ∃ r₀ ∈ R, (∀ q ∈ (Q ⊓ K : Subgroup G), r₀ * q * r₀⁻¹ = q) ∧ r₀ ∉ E := by
  by_contra hcon
  push Not at hcon
  have hle : (Subgroup.centralizer (((Q ⊓ K : Subgroup G)) : Set G) ⊓ R : Subgroup G) ≤ E := by
    rintro x ⟨hxC, hxR⟩
    apply hcon x hxR
    intro q hq
    have := Subgroup.mem_centralizer_iff.1 hxC q hq
    calc x * q * x⁻¹ = (q * x) * x⁻¹ := by rw [this]
      _ = q := by group
  have h1 := Subgroup.card_le_of_le hle
  rw [r.ctx.hEcard] at h1
  have h2 := r.three_pow_five_le_card_centralizer
  omega

theorem mem_N0_of_mem_R {x : G} (hxR : x ∈ R)
    (hx : ∀ q ∈ (Q ⊓ K : Subgroup G), x * q * x⁻¹ = q) : x ∈ N0 E (Q ⊓ K) := by
  obtain ⟨a, ha⟩ := r.hRp ⟨x, hxR⟩
  have ha' : x ^ 3 ^ a = 1 := by
    have := congrArg Subtype.val ha
    simpa using this
  exact r.ctx.mem_N0_of_odd r.hB (r.hRN hxR) hx (Odd.pow (by decide)) ha'

theorem hab : ∀ a ∈ (Q ⊓ K : Subgroup G), ∀ b ∈ (Q ⊓ K : Subgroup G), a * b = b * a :=
  fun _ ha _ hb => r.ctx.Q0_comm ha hb

theorem N0_normal : ∀ n ∈ Subgroup.normalizer (E : Set G), ∀ k ∈ N0 E (Q ⊓ K),
    n * k * n⁻¹ ∈ N0 E (Q ⊓ K) :=
  fun _ hn _ hk => N0_conj (fun _ hm _ hq => r.ctx.Q0_invariant r.hB hm hq) hn hk

theorem N0_le_normalizer : N0 E (Q ⊓ K) ≤ Subgroup.normalizer (E : Set G) :=
  fun _ hn => N0.mem_normalizer hn

theorem mem_E_of_comm_e {x : G} (hxR : x ∈ R)
    (hx : ∀ q ∈ (Q ⊓ K : Subgroup G), x * q * x⁻¹ = q) (hcomm : x * e = e * x) : x ∈ E := by
  have hcent : x ∈ Subgroup.centralizer (E : Set G) := by
    have hE : E ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [r.ctx.hEeq]
      apply sup_le
      · intro q hq
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff.1 hw]
        have := hx q hq
        calc x * q = (x * q * x⁻¹) * x := by group
          _ = q * x := by rw [this]
      · rw [Subgroup.zpowers_le]
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff.1 hw]
        exact hcomm
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.1 (hE hy) x (Set.mem_singleton x)).symm
  have : x ∈ R ⊓ Subgroup.centralizer (E : Set G) := ⟨hxR, hcent⟩
  rwa [r.inf_centralizer_E] at this

theorem shear_ne_one : ∃ n : ↥(N0 E (Q ⊓ K)), shear r.hab r.ctx.heE n ≠ 1 := by
  obtain ⟨r₀, hr₀R, hr₀q, hr₀E⟩ := r.exists_centralizing_not_mem_E
  have hr₀N : r₀ ∈ N0 E (Q ⊓ K) := r.mem_N0_of_mem_R hr₀R hr₀q
  refine ⟨⟨r₀, hr₀N⟩, fun h => hr₀E ?_⟩
  exact r.mem_E_of_comm_e hr₀R hr₀q ((shear_eq_one_iff r.hab r.ctx.heE ⟨r₀, hr₀N⟩).1 h)

theorem exists_shear_eq {q : G} (hq : q ∈ (Q ⊓ K : Subgroup G)) :
    ∃ n ∈ N0 E (Q ⊓ K), n * e * n⁻¹ * e⁻¹ = q := by
  classical
  obtain ⟨x, hxK, hxn, ⟨a, hxa⟩, -, hxfree⟩ := r.ctx.exists_x'
  have hxN : x ∈ Subgroup.normalizer (E : Set G) := r.ctx.mem_normalizer_E hxK hxn
  have hxe : x * e * x⁻¹ = e := by
    calc x * e * x⁻¹ = (e * x) * x⁻¹ := by rw [← r.ctx.hKe x hxK]
      _ = e := by group
  have hxe' : x * e⁻¹ * x⁻¹ = e⁻¹ := by
    calc x * e⁻¹ * x⁻¹ = (x * e * x⁻¹)⁻¹ := by group
      _ = e⁻¹ := by rw [hxe]
  set θ : ↥(N0 E (Q ⊓ K)) →* ↥(Q ⊓ K : Subgroup G) := shear r.hab r.ctx.heE with hθ
  set S : Subgroup G := ((Q ⊓ K : Subgroup G).subtype.comp θ).range with hS
  have hSQ : S ≤ (Q ⊓ K : Subgroup G) := by
    rintro _ ⟨n, rfl⟩
    exact (θ n).2
  have hinv : ∀ s ∈ S, x * s * x⁻¹ ∈ S := by
    rintro _ ⟨n, rfl⟩
    refine ⟨⟨x * (n : G) * x⁻¹, r.N0_normal x hxN n n.2⟩, ?_⟩
    simp only [MonoidHom.comp_apply, Subgroup.subtype_apply]
    show (x * (n : G) * x⁻¹) * e * (x * (n : G) * x⁻¹)⁻¹ * e⁻¹ =
      x * ((n : G) * e * (n : G)⁻¹ * e⁻¹) * x⁻¹
    calc (x * (n : G) * x⁻¹) * e * (x * (n : G) * x⁻¹)⁻¹ * e⁻¹
        = (x * (n : G) * x⁻¹) * (x * e * x⁻¹) * (x * (n : G)⁻¹ * x⁻¹) * (x * e⁻¹ * x⁻¹) := by
          rw [hxe, hxe']; group
      _ = x * ((n : G) * e * (n : G)⁻¹ * e⁻¹) * x⁻¹ := by group
  have hfree : ∀ q ∈ (Q ⊓ K : Subgroup G), x * q * x⁻¹ = q → q = 1 := by
    intro q hq hfix
    exact hxfree 1 (by norm_num) (by norm_num) q hq (by simpa using hfix)
  have hdich := invariant_subgroup_eq r.ctx.card_Q0 hSQ hxa hfree hinv
  have hne : S ≠ ⊥ := by
    obtain ⟨n, hn⟩ := r.shear_ne_one
    intro hbot
    apply hn
    have hmem : ((Q ⊓ K : Subgroup G).subtype.comp θ) n ∈ S := ⟨n, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    apply Subtype.ext
    simpa using hmem
  have hSeq : S = (Q ⊓ K : Subgroup G) := hdich.resolve_left hne
  have hqS : q ∈ S := hSeq ▸ hq
  obtain ⟨n, hn⟩ := hqS
  exact ⟨n, n.2, hn⟩

theorem shear_conj_eq {y : G} (hy : y ∈ E) (c n : ↥(N0 E (Q ⊓ K))) :
    shear r.hab hy (c * n * c⁻¹) = shear r.hab hy n := by
  letI : CommGroup ↥(Q ⊓ K : Subgroup G) :=
    { (inferInstance : Group ↥(Q ⊓ K : Subgroup G)) with
      mul_comm := fun a b => Subtype.ext (r.hab a a.2 b b.2) }
  rw [map_mul, map_mul, map_inv, mul_comm (shear r.hab hy c) (shear r.hab hy n), mul_assoc,
    mul_inv_cancel, mul_one]

theorem T_sylow : IsSylowIn 3 (N0 E (Q ⊓ K)) (R ⊓ N0 E (Q ⊓ K)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact isSylowIn_inf_normal r.N0_le_normalizer r.N0_normal r.hR

theorem exists_three_element {n : G} (hn : n ∈ N0 E (Q ⊓ K)) :
    ∃ k a : ℕ, (n ^ k) ^ 3 ^ a = 1 ∧ n ^ k * e * (n ^ k)⁻¹ * e⁻¹ = n * e * n⁻¹ * e⁻¹ := by
  obtain ⟨k, a, hka, hk1⟩ := exists_pow_pPart (G := G) 3 n
  refine ⟨k, a, hka, ?_⟩
  have h1 := map_pow (shear r.hab r.ctx.heE) (⟨n, hn⟩ : ↥(N0 E (Q ⊓ K))) k
  have h3 : ∀ a : ↥(Q ⊓ K : Subgroup G), a ^ k = a := by
    intro a
    have ha3 : a ^ 3 = 1 := Subtype.ext (by simpa using r.ctx.Q0_pow_three a.2)
    calc a ^ k = a ^ (3 * (k / 3) + k % 3) := by rw [Nat.div_add_mod]
      _ = a := by rw [pow_add, pow_mul, ha3, one_pow, one_mul, hk1, pow_one]
  rw [h3] at h1
  have h2 := congrArg Subtype.val h1
  exact h2

theorem theta_T_surj {q : G} (hq : q ∈ (Q ⊓ K : Subgroup G)) :
    ∃ t ∈ R ⊓ N0 E (Q ⊓ K), t * e * t⁻¹ * e⁻¹ = q := by
  obtain ⟨n, hn, hθ⟩ := r.exists_shear_eq hq
  obtain ⟨k, a, hka, hθk⟩ := r.exists_three_element hn
  have hnk : n ^ k ∈ N0 E (Q ⊓ K) := (N0 E (Q ⊓ K)).pow_mem hn k
  have hSle : Subgroup.zpowers (n ^ k) ≤ N0 E (Q ⊓ K) := Subgroup.zpowers_le.2 hnk
  obtain ⟨c, hcN, hc⟩ := Lemma113b.exists_conj_mem_of_isSylowIn r.T_sylow hSle
    (isPGroup_zpowers hka)
  refine ⟨c * n ^ k * c⁻¹, hc _ (Subgroup.mem_zpowers _), ?_⟩
  have := congrArg Subtype.val
    (r.shear_conj_eq r.ctx.heE (⟨c, hcN⟩ : ↥(N0 E (Q ⊓ K))) ⟨n ^ k, hnk⟩)
  simp only [shear_apply, Subgroup.coe_mul, Subgroup.coe_inv] at this
  rw [this, hθk, hθ]

theorem card_T : Nat.card ↥(R ⊓ N0 E (Q ⊓ K) : Subgroup G) = 3 ^ 7 := by
  set T : Subgroup G := R ⊓ N0 E (Q ⊓ K) with hT
  have hET : E ≤ T := by
    refine le_inf r.E_le_R ?_
    intro y hy
    refine mem_N0.2 ⟨Subgroup.le_normalizer hy, fun q hq => ?_, fun y' hy' => ?_⟩
    · calc y * q * y⁻¹ = (q * y) * y⁻¹ := by rw [r.ctx.E_comm hy (r.ctx.Q0_le_E hq)]
        _ = q := by group
    · rw [show y * y' * y⁻¹ * y'⁻¹ = 1 by
        rw [r.ctx.E_comm hy hy']; group]
      exact (Q ⊓ K : Subgroup G).one_mem
  set shearT : ↥T →* ↥(Q ⊓ K : Subgroup G) :=
    (shear r.hab r.ctx.heE).comp (Subgroup.inclusion (inf_le_right : T ≤ N0 E (Q ⊓ K))) with hsT
  have hker : shearT.ker = E.subgroupOf T := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have hsh := shear_eq_one_iff r.hab r.ctx.heE (Subgroup.inclusion (inf_le_right : T ≤ N0 E (Q ⊓ K)) t)
    constructor
    · intro h
      have hcomm := hsh.1 h
      exact r.mem_E_of_comm_e t.2.1 (fun q hq => N0.centralizes t.2.2 hq) hcomm
    · intro h
      apply hsh.2
      exact r.ctx.E_comm (t.2.2.1 |> fun _ => h) r.ctx.heE |> fun h' => by
        simpa using h'
  have hrange : shearT.range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    intro q
    obtain ⟨t, htT, hθ⟩ := r.theta_T_surj q.2
    refine ⟨⟨t, htT⟩, ?_⟩
    apply Subtype.ext
    simpa [hsT, shear_apply] using hθ
  have hcardker : Nat.card ↥shearT.ker = 3 ^ 4 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hET).toEquiv]
    exact r.ctx.hEcard
  have h := Subgroup.card_ker_mul_card_range shearT
  rw [hrange, Subgroup.card_top, hcardker, r.ctx.card_Q0] at h
  rw [← h]
  norm_num

theorem E_le_T : E ≤ R ⊓ N0 E (Q ⊓ K) := by
  refine le_inf r.E_le_R ?_
  intro y hy
  refine mem_N0.2 ⟨Subgroup.le_normalizer hy, fun q hq => ?_, fun y' hy' => ?_⟩
  · calc y * q * y⁻¹ = (q * y) * y⁻¹ := by rw [r.ctx.E_comm hy (r.ctx.Q0_le_E hq)]
      _ = q := by group
  · rw [show y * y' * y⁻¹ * y'⁻¹ = 1 by
      rw [r.ctx.E_comm hy hy']; group]
    exact (Q ⊓ K : Subgroup G).one_mem

theorem exists_m :
    ∃ m e' : G, m ∈ Subgroup.normalizer (E : Set G) ∧
      m ∈ Subgroup.normalizer ((R ⊓ N0 E (Q ⊓ K) : Subgroup G) : Set G) ∧
      (∃ q₀ ∈ (Q ⊓ K : Subgroup G), e' = e * q₀) ∧ m * e' * m⁻¹ = e' ∧
      (∃ a : ℕ, m ^ 13 ^ a = 1) ∧
      (∀ q ∈ (Q ⊓ K : Subgroup G), m * q * m⁻¹ ∈ (Q ⊓ K : Subgroup G)) ∧
      (∀ q ∈ (Q ⊓ K : Subgroup G), m ^ 13 * q * (m ^ 13)⁻¹ = q) ∧
      ∀ j : ℕ, 0 < j → j < 13 → ∀ q ∈ (Q ⊓ K : Subgroup G),
        m ^ j * q * (m ^ j)⁻¹ = q → q = 1 := by
  classical
  obtain ⟨x, hxK, hxn, ⟨a, hxa⟩, hx13, hxfree⟩ := r.ctx.exists_x'
  have hxN : x ∈ Subgroup.normalizer (E : Set G) := r.ctx.mem_normalizer_E hxK hxn
  obtain ⟨c, hcN₀, hcm⟩ := exists_conj_normalizes r.T_sylow
    (fun k hk => r.N0_normal x hxN k hk)
  have hcN : c ∈ Subgroup.normalizer (E : Set G) := r.N0_le_normalizer hcN₀
  set m : G := c * x with hm
  have hmN : m ∈ Subgroup.normalizer (E : Set G) := mul_mem hcN hxN
  have hcq : ∀ q ∈ (Q ⊓ K : Subgroup G), c * q * c⁻¹ = q := fun q hq => N0.centralizes hcN₀ hq
  have hmq : ∀ q ∈ (Q ⊓ K : Subgroup G), m * q * m⁻¹ = x * q * x⁻¹ := by
    intro q hq
    have : m * q * m⁻¹ = c * (x * q * x⁻¹) * c⁻¹ := by rw [hm]; group
    rw [this]
    exact hcq _ (hxn q hq)
  have hmq_pow : ∀ j : ℕ, ∀ q ∈ (Q ⊓ K : Subgroup G),
      m ^ j * q * (m ^ j)⁻¹ = x ^ j * q * (x ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro q _; simp
    | succ j ih =>
      intro q hq
      have h1 : m ^ (j + 1) * q * (m ^ (j + 1))⁻¹ = m ^ j * (m * q * m⁻¹) * (m ^ j)⁻¹ := by
        rw [pow_succ]; group
      rw [h1, hmq q hq, ih _ (hxn q hq), pow_succ]
      group
  have hxe : x * e * x⁻¹ = e := by
    calc x * e * x⁻¹ = (e * x) * x⁻¹ := by rw [← r.ctx.hKe x hxK]
      _ = e := by group
  have hme : ∃ u ∈ (Q ⊓ K : Subgroup G), m * e * m⁻¹ = u * e := by
    refine ⟨c * e * c⁻¹ * e⁻¹, N0.shear_mem hcN₀ r.ctx.heE, ?_⟩
    have : m * e * m⁻¹ = c * (x * e * x⁻¹) * c⁻¹ := by rw [hm]; group
    rw [this, hxe]
    group
  obtain ⟨u, hu, hmeu⟩ := hme
  have hmX : ∀ y ∈ ((fun q : G => e * q) '' ((Q ⊓ K : Subgroup G) : Set G)),
      m * y * m⁻¹ ∈ ((fun q : G => e * q) '' ((Q ⊓ K : Subgroup G) : Set G)) := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨u * (x * q * x⁻¹), (Q ⊓ K : Subgroup G).mul_mem hu (hxn q hq), ?_⟩
    have h1 : m * (e * q) * m⁻¹ = (m * e * m⁻¹) * (m * q * m⁻¹) := by group
    show e * (u * (x * q * x⁻¹)) = m * (e * q) * m⁻¹
    rw [h1, hmeu, hmq q hq]
    have h2 : e * u * e⁻¹ = u := r.ctx.e_conj_Q0 hu
    calc e * (u * (x * q * x⁻¹)) = (e * u * e⁻¹) * e * (x * q * x⁻¹) := by group
      _ = u * e * (x * q * x⁻¹) := by rw [h2]
  have hmXpow : ∀ j : ℕ, ∀ y ∈ ((fun q : G => e * q) '' ((Q ⊓ K : Subgroup G) : Set G)),
      m ^ j * y * (m ^ j)⁻¹ ∈ ((fun q : G => e * q) '' ((Q ⊓ K : Subgroup G) : Set G)) := by
    intro j
    induction j with
    | zero => intro y hy; simpa using hy
    | succ j ih =>
      intro y hy
      have : m ^ (j + 1) * y * (m ^ (j + 1))⁻¹ = m ^ j * (m * y * m⁻¹) * (m ^ j)⁻¹ := by
        rw [pow_succ]; group
      rw [this]
      exact ih _ (hmX y hy)
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨k, a₁, hk13, hk1⟩ := exists_pow_pPart (G := G) 13 m
  have hxinv : ∀ q ∈ (Q ⊓ K : Subgroup G), x * q * x⁻¹ ∈ (Q ⊓ K : Subgroup G) := hxn
  have hact : ∀ j : ℕ, ∀ q ∈ (Q ⊓ K : Subgroup G),
      (m ^ k) ^ j * q * ((m ^ k) ^ j)⁻¹ = x ^ (j % 13) * q * (x ^ (j % 13))⁻¹ := by
    intro j q hq
    rw [← pow_mul, hmq_pow (k * j) q hq, pow_act_mod hxinv hx13 (k * j) q hq]
    have : (k * j) % 13 = j % 13 := by
      rw [Nat.mul_mod, hk1, one_mul, Nat.mod_mod]
    rw [this]
  have hcardX : ¬ 13 ∣ Nat.card ↥((fun q : G => e * q) '' ((Q ⊓ K : Subgroup G) : Set G)) := by
    have hinj : Function.Injective (fun q : G => e * q) := fun a b h => mul_left_cancel h
    rw [Nat.card_image_of_injective hinj, Nat.card_coe_set_eq]
    have : ((Q ⊓ K : Subgroup G) : Set G).ncard = 27 := by
      rw [← Nat.card_coe_set_eq]; exact r.ctx.card_Q0
    rw [this]
    norm_num
  obtain ⟨y₀, ⟨q₀, hq₀, rfl⟩, hfix⟩ := exists_fixed_conj (g := m ^ k) (a := a₁) hk13
    (fun y hy => by
      have := hmXpow k y hy
      exact this) hcardX
  refine ⟨m ^ k, e * q₀, (Subgroup.normalizer (E : Set G)).pow_mem hmN k, pow_mem hcm k, ⟨q₀, hq₀, rfl⟩, hfix,
    ⟨a₁, hk13⟩, fun q hq => ?_, fun q hq => ?_, fun j hj0 hj13 q hq hqfix => ?_⟩
  · rw [← pow_one (m ^ k), hact 1 q hq]
    simpa using hxn q hq
  · rw [hact 13 q hq]
    simp
  · rw [hact j q hq, Nat.mod_eq_of_lt hj13] at hqfix
    exact hxfree j hj0 hj13 q hq hqfix

theorem exists_b : ∃ b ∈ A, b ∉ E := SetLike.not_le_iff_exists.1 r.ctx.hAnE

theorem card_inf_centralizer_b_le_three {b : G} (hbA : b ∈ A) (hbE : b ∉ E) :
    Nat.card ↥((Q ⊓ K : Subgroup G) ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) ≤ 3 := by
  have c := r.ctx
  set Y : Subgroup G := (Q ⊓ K : Subgroup G) ⊓ Subgroup.centralizer ({b} : Set G) with hY
  have hb3 : b ^ 3 = 1 := c.hAel.2 b hbA
  have hb1 : b ≠ 1 := fun h => hbE (h ▸ E.one_mem)
  have hbQ : b ∈ Q := c.hAQ hbA
  have hbN : b ∈ Subgroup.normalizer (E : Set G) := r.hRN (r.hQR hbQ)
  have hQeq : E ⊔ Subgroup.zpowers b = Q := by
    have hle : E ⊔ Subgroup.zpowers b ≤ Q := sup_le c.hEQ (Subgroup.zpowers_le.2 hbQ)
    have hcard : Nat.card ↥(E ⊔ Subgroup.zpowers b : Subgroup G) = 3 * Nat.card ↥E :=
      l113_card_sup_zpowers E hb3 hb1 hbE (Subgroup.zpowers_le.2 hbN)
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, c.card_Q r.hB, c.hEcard]; norm_num)
  have hYA : ∀ y ∈ Y, y ∈ A := by
    intro y hy
    have hyC : E ⊔ Subgroup.zpowers b ≤ Subgroup.centralizer ({y} : Set G) := by
      apply sup_le
      · intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff.1 hw]
        exact c.E_comm (c.Q0_le_E hy.1) hz
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff.1 hw]
        exact (Subgroup.mem_centralizer_iff.1 hy.2 b (Set.mem_singleton b)).symm
    rw [hQeq] at hyC
    have hyZ : ∀ q ∈ Q, q * y = y * q := fun q hq =>
      (Subgroup.mem_centralizer_iff.1 (hyC hq) y (Set.mem_singleton y)).symm
    exact Lemma113c.mem_of_central_order_three (E := A) ⟨le_top, c.hAel, c.hAmax⟩ c.hAQ hyZ
      (c.Q0_pow_three hy.1)
  have hsup : Y ⊔ Subgroup.zpowers e ≤ E ⊓ A := by
    apply sup_le
    · intro y hy
      exact ⟨c.Q0_le_E hy.1, hYA y hy⟩
    · exact Subgroup.zpowers_le.2 ⟨c.heE, c.heA⟩
  have hEA9 : Nat.card ↥(E ⊓ A : Subgroup G) ≤ 9 := by
    have hdvd : Nat.card ↥(E ⊓ A : Subgroup G) ∣ 3 ^ 3 := by
      rw [← c.hAcard]
      exact Subgroup.card_dvd_of_le inf_le_right
    obtain ⟨i, hi, hiEA⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    by_contra hgt
    push Not at hgt
    have hi3 : i = 3 := by
      by_contra hne
      have : i ≤ 2 := by omega
      have : 3 ^ i ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
      omega
    subst hi3
    apply c.hAnE
    have heq : E ⊓ A = A := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hiEA, c.hAcard])
    rw [← heq]
    exact inf_le_left
  have heY : e ∉ Y := fun h => c.e_not_mem_Q0 h.1
  have hnormY : Subgroup.zpowers e ≤ Subgroup.normalizer (Y : Set G) := by
    rw [Subgroup.zpowers_le]
    refine mem_normalizer_of_conj_le fun y hy => ?_
    rw [c.e_conj_Q0 hy.1]
    exact hy
  have hcardsup := l113_card_sup_zpowers Y c.he3 c.he1 heY hnormY
  have hle := Subgroup.card_le_of_le hsup
  omega

theorem hfix {x : G} (hxR : x ∈ R) {W : Subgroup G} (hWQ : W ≤ Q ⊓ K) (hW9 : 9 ≤ Nat.card ↥W)
    (hxW : ∀ w ∈ W, x * w = w * x) : ∀ q ∈ (Q ⊓ K : Subgroup G), x * q = q * x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨q₁, hq₁, hq₁ne⟩ := hcon
  set T : Subgroup G := R ⊓ N0 E (Q ⊓ K) with hT
  have hxT : x ∉ T := fun hxT => hq₁ne (by
    have := N0.centralizes hxT.2 hq₁
    calc x * q₁ = (x * q₁ * x⁻¹) * x := by group
      _ = q₁ * x := by rw [this])
  have hxNT : x ∈ Subgroup.normalizer (T : Set G) := mem_normalizer_of_conj_le fun t ht =>
    ⟨R.mul_mem (R.mul_mem hxR ht.1) (R.inv_mem hxR), r.N0_normal x (r.hRN hxR) t ht.2⟩
  have hRsup : T ⊔ Subgroup.zpowers x = R := by
    have hle : T ⊔ Subgroup.zpowers x ≤ R := sup_le inf_le_left (Subgroup.zpowers_le.2 hxR)
    have h1 : Nat.card ↥T ∣ Nat.card ↥(T ⊔ Subgroup.zpowers x : Subgroup G) :=
      Subgroup.card_dvd_of_le le_sup_left
    have h2 : Nat.card ↥(T ⊔ Subgroup.zpowers x : Subgroup G) ∣ 3 ^ 8 := by
      rw [← r.hR8]
      exact Subgroup.card_dvd_of_le hle
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h2
    rw [r.card_T, hjeq] at h1
    have h7 : 7 ≤ j := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h1
    by_cases hj8 : j = 8
    · apply Subgroup.eq_of_le_of_card_ge hle
      rw [r.hR8, hjeq, hj8]
    · exfalso
      have hj7 : j = 7 := by omega
      apply hxT
      have hTeq : T = T ⊔ Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [r.card_T, hjeq, hj7])
      rw [hTeq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  obtain ⟨b, hbA, hbE⟩ := r.exists_b
  have hbR : b ∈ R := r.hQR (r.ctx.hAQ hbA)
  have hbsup : b ∈ Subgroup.zpowers x ⊔ T := by
    rw [sup_comm, hRsup]
    exact hbR
  obtain ⟨y', hy', t, ht, hbyt⟩ := exists_mul_of_mem_sup_norm
    (Subgroup.zpowers_le.2 hxNT) hbsup
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy'
  have hWb : W ≤ (Q ⊓ K : Subgroup G) ⊓ Subgroup.centralizer ({b} : Set G) := by
    intro w hw
    refine ⟨hWQ hw, ?_⟩
    show w ∈ Subgroup.centralizer ({b} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff.1 hz]
    have hxi : x ^ i * w = w * x ^ i :=
      ((Commute.zpow_left (show Commute x w from hxW w hw) i)).eq
    have htw : t * w * t⁻¹ = w := N0.centralizes ht.2 (hWQ hw)
    rw [← hbyt]
    calc x ^ i * t * w = x ^ i * (t * w * t⁻¹) * t := by group
      _ = x ^ i * w * t := by rw [htw]
      _ = w * x ^ i * t := by rw [hxi]
      _ = w * (x ^ i * t) := by group
  have := Subgroup.card_le_of_le hWb
  have h3 := r.card_inf_centralizer_b_le_three hbA hbE
  omega

theorem key_of_hΩ (hΩ : ∀ y ∈ R ⊓ N0 E (Q ⊓ K), y ^ 3 = 1 → y ∈ E) :
    ∀ E1 : Subgroup G, E1 ≤ R → IsElemAbelian 3 E1 → 3 ^ 4 ≤ Nat.card E1 → E1 ≤ E := by
  intro E1 hE1R hE1ab hE1card
  set T : Subgroup G := R ⊓ N0 E (Q ⊓ K) with hT
  have h1 : 27 ≤ Nat.card ↥(E1 ⊓ T : Subgroup G) := by
    have hc := Lemma113f.card_mul_le_card_inf_mul (A := E1) (B := T) hE1R inf_le_left
    rw [r.card_T, r.hR8] at hc
    have h81 : 3 ^ 4 * 3 ^ 7 ≤ Nat.card E1 * 3 ^ 7 := Nat.mul_le_mul_right _ hE1card
    by_contra hlt
    push Not at hlt
    have : Nat.card ↥(E1 ⊓ T : Subgroup G) * 3 ^ 8 ≤ 26 * 3 ^ 8 :=
      Nat.mul_le_mul_right _ (by omega)
    norm_num at h81 this hc
    omega
  have h2 : (E1 ⊓ T : Subgroup G) ≤ E := fun y hy => hΩ y hy.2 (hE1ab.2 y hy.1)
  have h3 : 9 ≤ Nat.card ↥((E1 ⊓ T) ⊓ (Q ⊓ K) : Subgroup G) := by
    have hc := Lemma113f.card_mul_le_card_inf_mul (A := E1 ⊓ T) (B := Q ⊓ K) h2 r.ctx.Q0_le_E
    rw [r.ctx.card_Q0, r.ctx.hEcard] at hc
    have h27 : 27 * 27 ≤ Nat.card ↥(E1 ⊓ T : Subgroup G) * 27 := Nat.mul_le_mul_right _ h1
    by_contra hlt
    push Not at hlt
    have : Nat.card ↥((E1 ⊓ T) ⊓ (Q ⊓ K) : Subgroup G) * 3 ^ 4 ≤ 8 * 3 ^ 4 :=
      Nat.mul_le_mul_right _ (by omega)
    norm_num at h27 this hc
    omega
  intro x hx
  have hxR : x ∈ R := hE1R hx
  have hxc : ∀ q ∈ (Q ⊓ K : Subgroup G), x * q = q * x :=
    r.hfix hxR (W := (E1 ⊓ T) ⊓ (Q ⊓ K)) inf_le_right h3
      (fun w hw => Lemma113f.comm_of_isElemAbelian hE1ab hx hw.1.1)
  have hxT : x ∈ T := ⟨hxR, r.mem_N0_of_mem_R hxR fun q hq => by
    calc x * q * x⁻¹ = (q * x) * x⁻¹ := by rw [hxc q hq]
      _ = q := by group⟩
  exact hΩ x hxT (hE1ab.2 x hx)

theorem isEkIn_E : IsEkIn 3 4 R E := ⟨r.E_le_R, r.ctx.hEel, r.ctx.hEcard⟩

theorem thompsonJ_eq (hΩ : ∀ y ∈ R ⊓ N0 E (Q ⊓ K), y ^ 3 = 1 → y ∈ E) : thompsonJ 3 R = E :=
  (thompsonJ_eq_of_key r.isEkIn_E (r.key_of_hΩ hΩ)).1

theorem R_normalizes_T {x : G} (hxR : x ∈ R) :
    x ∈ Subgroup.normalizer ((R ⊓ N0 E (Q ⊓ K) : Subgroup G) : Set G) :=
  mem_normalizer_of_conj_le fun t ht =>
    ⟨R.mul_mem (R.mul_mem hxR ht.1) (R.inv_mem hxR), r.N0_normal x (r.hRN hxR) t ht.2⟩

theorem no_big_abelian {M : Subgroup G} {a : G} (haA : a ∈ A)
    (hNM : Subgroup.normalizer (E : Set G) ≤ M)
    (h0 : ∀ E1 : Subgroup G, E1 ≤ M → IsElemAbelian 3 E1 → 5 ≤ CFSG.Open.pRank 3 E1 →
      a ∉ Subgroup.normalizer (E1 : Set G)) :
    ¬ ∃ F : Subgroup G, F ≤ R ⊓ N0 E (Q ⊓ K) ∧ Nat.card ↥F = 3 ^ 6 ∧ IsElemAbelian 3 F ∧
      ∀ g : G, (∀ t ∈ R ⊓ N0 E (Q ⊓ K), g * t * g⁻¹ ∈ R ⊓ N0 E (Q ⊓ K)) →
        ∀ f ∈ F, g * f * g⁻¹ ∈ F := by
  rintro ⟨F, hFT, hF6, hFel, hFinv⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have haR : a ∈ R := r.hQR (r.ctx.hAQ haA)
  have haN : a ∈ Subgroup.normalizer (F : Set G) :=
    mem_normalizer_of_conj_le (hFinv a fun t ht => by
      have := Subgroup.mem_normalizer_iff.1 (r.R_normalizes_T haR) t
      exact this.1 ht)
  have hFM : F ≤ M := fun f hf => hNM (r.hRN (hFT hf).1)
  have hrank : CFSG.Open.pRank 3 F = 6 := by
    have h := l113_card_eq_pow_pRank hFel
    rw [hF6] at h
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h).symm
  exact h0 F hFM hFel (by omega) haN

theorem card_R_of {R' : Subgroup G} (hR' : IsSylowIn 3 (Subgroup.normalizer (E : Set G)) R') :
    Nat.card ↥R' = 3 ^ 8 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [card_eq_of_isSylowIn r.hR hR', r.hR8]

theorem dichotomy :
    (∃ F : Subgroup G, F ≤ R ⊓ N0 E (Q ⊓ K) ∧ Nat.card ↥F = 3 ^ 6 ∧
      (∀ a ∈ F, ∀ b ∈ F, a * b = b * a) ∧ (∀ f ∈ F, f ^ 3 ∈ (Q ⊓ K : Subgroup G)) ∧
      (∀ f ∈ F, f ^ 3 = 1 → f ∈ (Q ⊓ K : Subgroup G)) ∧
      (∀ q ∈ (Q ⊓ K : Subgroup G), ∃ f ∈ F, f ^ 3 = q) ∧
      (∀ t ∈ R ⊓ N0 E (Q ⊓ K), ∃ f ∈ F, ∃ y ∈ E, t = f * y) ∧
      (∀ g : G, (∀ t ∈ R ⊓ N0 E (Q ⊓ K), g * t * g⁻¹ ∈ R ⊓ N0 E (Q ⊓ K)) →
        ∀ f ∈ F, g * f * g⁻¹ ∈ F) ∧
      (∀ t ∈ R ⊓ N0 E (Q ⊓ K), t ^ 3 = 1 → t ∈ E)) ∨
    (∃ F : Subgroup G, F ≤ R ⊓ N0 E (Q ⊓ K) ∧ Nat.card ↥F = 3 ^ 6 ∧ IsElemAbelian 3 F ∧
      ∀ g : G, (∀ t ∈ R ⊓ N0 E (Q ⊓ K), g * t * g⁻¹ ∈ R ⊓ N0 E (Q ⊓ K)) →
        ∀ f ∈ F, g * f * g⁻¹ ∈ F) := by
  obtain ⟨m, e', hmN, hmT, ⟨q₀, hq₀, he'⟩, hme', hm13, hmQ, hm13Q, hmfree⟩ := r.exists_m
  have c := r.ctx
  have he'E : e' ∈ E := by rw [he']; exact E.mul_mem c.heE (c.Q0_le_E hq₀)
  have he'Q : e' ∉ (Q ⊓ K : Subgroup G) := by
    intro h
    apply c.e_not_mem_Q0
    have : e = e' * q₀⁻¹ := by rw [he']; group
    rw [this]
    exact (Q ⊓ K : Subgroup G).mul_mem h ((Q ⊓ K : Subgroup G).inv_mem hq₀)
  have hTcent : ∀ t ∈ R ⊓ N0 E (Q ⊓ K), ∀ q ∈ (Q ⊓ K : Subgroup G), t * q * t⁻¹ = q :=
    fun t ht q hq => N0.centralizes ht.2 hq
  refine Lemma113Claims.T.T_structure (T := R ⊓ N0 E (Q ⊓ K)) (E := E) (Q0 := Q ⊓ K) (e := e')
    (m := m) (r.hRp.to_le inf_le_left) r.card_T c.hEel c.hEcard r.E_le_T c.Q0_elemAbelian
    (by rw [c.card_Q0]; norm_num) c.Q0_le_E he'E he'Q ?_ ?_ ?_ ?_ ?_ ?_ ?_ hmQ hme' hm13 hm13Q
    hmfree
  · intro t ht q hq
    have := hTcent t ht q hq
    calc t * q = (t * q * t⁻¹) * t := by group
      _ = q * t := by rw [this]
  · intro t ht
    exact N0.shear_mem ht.2 he'E
  · intro t ht hcomm
    have hte : t * e * t⁻¹ = e := by
      have h1 : t * e' * t⁻¹ = e' := by
        calc t * e' * t⁻¹ = (e' * t) * t⁻¹ := by rw [hcomm]
          _ = e' := by group
      have h2 : t * (e' * q₀⁻¹) * t⁻¹ = (t * e' * t⁻¹) * (t * q₀⁻¹ * t⁻¹) := by group
      have h3 : t * q₀⁻¹ * t⁻¹ = q₀⁻¹ := by
        have := hTcent t ht q₀ hq₀
        calc t * q₀⁻¹ * t⁻¹ = (t * q₀ * t⁻¹)⁻¹ := by group
          _ = q₀⁻¹ := by rw [this]
      have : e = e' * q₀⁻¹ := by rw [he']; group
      rw [this, h2, h1, h3]
    exact r.mem_E_of_comm_e ht.1 (fun q hq => hTcent t ht q hq) (by
      calc t * e = (t * e * t⁻¹) * t := by group
        _ = e * t := by rw [hte])
  · intro q hq
    obtain ⟨t, ht, htq⟩ := r.theta_T_surj hq
    refine ⟨t, ht, ?_⟩
    have h1 : t * e' * t⁻¹ * e'⁻¹ = t * e * t⁻¹ * e⁻¹ := by
      have h2 : t * (e * q₀) * t⁻¹ = (t * e * t⁻¹) * (t * q₀ * t⁻¹) := by group
      rw [he', h2, hTcent t ht q₀ hq₀]
      group
    rw [h1, htq]
  · intro t ht
    exact (Subgroup.mem_normalizer_iff.1 hmT t).1 ht
  · intro t ht
    have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem hmT) t).1 ht
    simpa using this
  · intro y hy
    exact (Subgroup.mem_normalizer_iff.1 hmN y).1 hy

theorem omega_le_E {M : Subgroup G} {a : G} (haA : a ∈ A)
    (hNM : Subgroup.normalizer (E : Set G) ≤ M)
    (h0 : ∀ E1 : Subgroup G, E1 ≤ M → IsElemAbelian 3 E1 → 5 ≤ CFSG.Open.pRank 3 E1 →
      a ∉ Subgroup.normalizer (E1 : Set G)) :
    ∀ t ∈ R ⊓ N0 E (Q ⊓ K), t ^ 3 = 1 → t ∈ E := by
  rcases r.dichotomy with ⟨F, -, -, -, -, -, -, -, -, hΩ⟩ | hF
  · exact hΩ
  · exact absurd hF (r.no_big_abelian haA hNM h0)

theorem R_eq_sup_zpowers {x : G} (hxR : x ∈ R) (hxT : x ∉ R ⊓ N0 E (Q ⊓ K)) :
    (R ⊓ N0 E (Q ⊓ K)) ⊔ Subgroup.zpowers x = R := by
  set T : Subgroup G := R ⊓ N0 E (Q ⊓ K) with hT
  have hle : T ⊔ Subgroup.zpowers x ≤ R := sup_le inf_le_left (Subgroup.zpowers_le.2 hxR)
  have h1 : Nat.card ↥T ∣ Nat.card ↥(T ⊔ Subgroup.zpowers x : Subgroup G) :=
    Subgroup.card_dvd_of_le le_sup_left
  have h2 : Nat.card ↥(T ⊔ Subgroup.zpowers x : Subgroup G) ∣ 3 ^ 8 := by
    rw [← r.hR8]
    exact Subgroup.card_dvd_of_le hle
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h2
  rw [r.card_T, hjeq] at h1
  have h7 : 7 ≤ j := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h1
  by_cases hj8 : j = 8
  · apply Subgroup.eq_of_le_of_card_ge hle
    rw [r.hR8, hjeq, hj8]
  · exfalso
    have hj7 : j = 7 := by omega
    apply hxT
    have hTeq : T = T ⊔ Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [r.card_T, hjeq, hj7])
    rw [hTeq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)

theorem b_not_mem_T {b : G} (hbA : b ∈ A) (hbE : b ∉ E) : b ∉ R ⊓ N0 E (Q ⊓ K) := by
  intro hbT
  apply hbE
  exact r.mem_E_of_comm_e hbT.1 (fun q hq => N0.centralizes hbT.2 hq)
    (Lemma113f.comm_of_isElemAbelian r.ctx.hAel hbA r.ctx.heA)

theorem R_le_N1 : R ≤ N1 E (Q ⊓ K) := by
  obtain ⟨b, hbA, hbE⟩ := r.exists_b
  have hbR : b ∈ R := r.hQR (r.ctx.hAQ hbA)
  have hbN1 : b ∈ N1 E (Q ⊓ K) := by
    refine mem_N1.2 ⟨r.hRN hbR, r.ctx.mem_normalizer_Q0 r.hB (r.hRN hbR), fun y hy => ?_⟩
    have hyE' : y ∈ (Q ⊓ K : Subgroup G) ⊔ Subgroup.zpowers e := r.ctx.hEeq ▸ hy
    obtain ⟨q', hq', b', hb', hqb⟩ := exists_mul_of_mem_sup r.ctx.Q0_le_centralizer_zpowers hyE'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb'
    have hbe : b * e = e * b := Lemma113f.comm_of_isElemAbelian r.ctx.hAel hbA r.ctx.heA
    have hbei : b * e ^ i = e ^ i * b := ((Commute.zpow_right (show Commute b e from hbe) i)).eq
    have hbq : b * q' * b⁻¹ ∈ (Q ⊓ K : Subgroup G) :=
      r.ctx.Q0_invariant r.hB (r.hRN hbR) hq'
    have key : b * y * b⁻¹ * y⁻¹ = (b * q' * b⁻¹) * q'⁻¹ := by
      rw [hqb]
      have h1 : b * (q' * e ^ i) * b⁻¹ = (b * q' * b⁻¹) * (b * e ^ i * b⁻¹) := by group
      have h2 : b * e ^ i * b⁻¹ = e ^ i := by
        calc b * e ^ i * b⁻¹ = (e ^ i * b) * b⁻¹ := by rw [hbei]
          _ = e ^ i := by group
      calc b * (q' * e ^ i) * b⁻¹ * (q' * e ^ i)⁻¹
          = ((b * q' * b⁻¹) * (b * e ^ i * b⁻¹)) * (q' * e ^ i)⁻¹ := by rw [h1]
        _ = (b * q' * b⁻¹) * q'⁻¹ := by rw [h2]; group
    rw [key]
    exact (Q ⊓ K : Subgroup G).mul_mem hbq ((Q ⊓ K : Subgroup G).inv_mem hq')
  intro x hxR
  by_cases hxT : x ∈ R ⊓ N0 E (Q ⊓ K)
  · exact N0_le_N1 hxT.2
  ·
    have hRb := r.R_eq_sup_zpowers hbR (r.b_not_mem_T hbA hbE)
    have hle : R ≤ N1 E (Q ⊓ K) := by
      rw [← hRb]
      exact sup_le (inf_le_right.trans N0_le_N1) (Subgroup.zpowers_le.2 hbN1)
    exact hle hxR

end RCfg

end Lemma113Claims


end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end

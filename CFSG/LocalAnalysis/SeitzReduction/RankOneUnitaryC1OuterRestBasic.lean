module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterDataHigh

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

@[expose] def outerRestPt {G : Type*} [Group G] (t : G) (k : ℕ) (n : G) : G :=
  (n * t * n⁻¹ * t⁻¹) ^ 2 ^ k

theorem outerRestPt_def {G : Type*} [Group G] (t : G) (k : ℕ) (n : G) :
    outerRestPt t k n = (n * t * n⁻¹ * t⁻¹) ^ 2 ^ k :=
  rfl

@[expose] def outerRestStab {G : Type*} [Group G] (L T V : Subgroup G) (t : G) : Subgroup G :=
  V ⊔ (normalizer (szR (szT₁ L T) V t : Set G) ⊓ centralizer ({t} : Set G))

namespace U3C1OuterConf

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D V : Subgroup G} {k : ℕ}

theorem outerRest_pow_mem_szA₁ (hc : U3C1OuterConf G L f t T R₂ D V k) {r : G} (hr : r ∈ V) :
    r ^ 2 ^ k ∈ szA₁ (szT₁ L T) :=
  hc.omega _ (pow_mem hr _) (by rw [← pow_mul, ← pow_succ]; exact hc.pow r hr)

theorem outerRest_exists_pow_eq
    (hc : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {b : G}
    (hb : b ∈ szA₁ (szT₁ L T)) : ∃ r ∈ V, r ^ 2 ^ k = b := by
  obtain ⟨-, hA₁card, -, -, -, hsqA₁, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨z, hz, hzb⟩ := pushUp_exists_pow_eq hc.comm (pow_pos (by norm_num) f) hc.card hc.pow
    hc.omega (le_of_eq hA₁card) (show 1 ≤ k + 1 by omega) (hc.le hb)
    (by rw [pow_one]; exact hsqA₁ b hb)
  exact ⟨z, hz, by rwa [show k + 1 - 1 = k by omega] at hzb⟩

theorem outerRest_exists_sq
    (hc : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {r : G} (hr : r ∈ V)
    (h1 : r ^ 2 ^ k = 1) : ∃ s ∈ V, s ^ 2 = r := by
  obtain ⟨-, hA₁card, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨z, hz, hzr⟩ := pushUp_exists_pow_eq hc.comm (pow_pos (by norm_num) f) hc.card hc.pow
    hc.omega (le_of_eq hA₁card) (show k ≤ k + 1 by omega) hr h1
  exact ⟨z, hz, by rwa [show k + 1 - k = 1 by omega, pow_one] at hzr⟩

theorem outerRest_conj_t (hc : U3C1OuterConf G L f t T R₂ D V k) {s : G} (hs : s ∈ V) :
    s * t * s⁻¹ = s ^ 2 * t := by
  have h1 := hc.inv s hs
  calc s * t * s⁻¹ = s * (t * s * t⁻¹)⁻¹ * t := by group
    _ = s ^ 2 * t := by rw [h1, inv_inv, sq]

theorem outerRest_comm_t_mem
    (hc : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) (hk : 2 ≤ k) {n : G}
    (hn : n ∈ normalizer (szR (szT₁ L T) V t : Set G)) : n * t * n⁻¹ * t⁻¹ ∈ V :=
  (hc.normalizer_szR_le h hS2 hk hn).2.2.2

theorem outerRestPt_mem
    (hc : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) (hk : 2 ≤ k) {n : G}
    (hn : n ∈ normalizer (szR (szT₁ L T) V t : Set G)) : outerRestPt t k n ∈ szA₁ (szT₁ L T) :=
  hc.outerRest_pow_mem_szA₁ (hc.outerRest_comm_t_mem h hS2 hk hn)

theorem outerRestPt_mul
    (hc : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) (hk : 2 ≤ k) {n m : G}
    (hn : n ∈ normalizer (szR (szT₁ L T) V t : Set G))
    (hm : m ∈ normalizer (szR (szT₁ L T) V t : Set G)) :
    outerRestPt t k (n * m) = n * outerRestPt t k m * n⁻¹ * outerRestPt t k n := by
  have hσn := hc.outerRest_comm_t_mem h hS2 hk hn
  have hσm := hc.outerRest_comm_t_mem h hS2 hk hm
  have hnV := (hc.normalizer_szR_le h hS2 hk hn).2.1
  have hc1 : n * (m * t * m⁻¹ * t⁻¹) * n⁻¹ ∈ V := (mem_normalizer_iff.mp hnV _).mp hσm
  rw [outerRestPt_def, outerRestPt_def, outerRestPt_def, SzC1.comm_t_mul,
    (Commute.mul_pow (hc.comm _ hc1 _ hσn) _), conj_pow]

theorem outerRestPt_mul_of_conj
    (hc : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) (hk : 2 ≤ k) {n m : G}
    (hn : n ∈ normalizer (szR (szT₁ L T) V t : Set G))
    (hm : m ∈ normalizer (szR (szT₁ L T) V t : Set G))
    (hnA : ∀ b ∈ szA₁ (szT₁ L T), n * b * n⁻¹ = b) :
    outerRestPt t k (n * m) = outerRestPt t k m * outerRestPt t k n := by
  rw [hc.outerRestPt_mul h hS2 hk hn hm, hnA _ (hc.outerRestPt_mem h hS2 hk hm)]

theorem outerRestPt_of_mem (hc : U3C1OuterConf G L f t T R₂ D V k) {s : G} (hs : s ∈ V) :
    outerRestPt t k s = 1 := by
  rw [outerRestPt_def, hc.outerRest_conj_t hs, mul_inv_cancel_right, ← pow_mul, ← pow_succ',
    hc.pow s hs]

omit [Finite G] in
theorem outerRestPt_of_comm {c : G} (hc : c * t = t * c) : outerRestPt t k c = 1 := by
  rw [outerRestPt_def, hc, mul_inv_cancel_right, mul_inv_cancel, one_pow]

theorem outerRestPt_inv
    (hc : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) (hk : 2 ≤ k) {n : G}
    (hn : n ∈ normalizer (szR (szT₁ L T) V t : Set G)) :
    outerRestPt t k n⁻¹ = n⁻¹ * (outerRestPt t k n)⁻¹ * n := by
  have e := hc.outerRestPt_mul h hS2 hk hn (inv_mem hn)
  rw [mul_inv_cancel, outerRestPt_of_comm (by rw [one_mul, mul_one])] at e
  have e2 : outerRestPt t k n⁻¹ = n⁻¹ * (n * outerRestPt t k n⁻¹ * n⁻¹) * n := by group
  rw [e2, show n * outerRestPt t k n⁻¹ * n⁻¹ = (outerRestPt t k n)⁻¹ from
    eq_inv_of_mul_eq_one_left e.symm]

theorem mem_outerRestStab_iff
    (hc : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) (hk : 2 ≤ k) {n : G} :
    n ∈ outerRestStab L T V t ↔
      n ∈ normalizer (szR (szT₁ L T) V t : Set G) ∧ outerRestPt t k n = 1 := by
  have hVY : V ≤ normalizer (szR (szT₁ L T) V t : Set G) :=
    (le_szR_mid _ _ _).trans Subgroup.le_normalizer
  have hCV : normalizer (szR (szT₁ L T) V t : Set G) ⊓ centralizer ({t} : Set G) ≤
      normalizer (V : Set G) := fun x hx => (hc.normalizer_szR_le h hS2 hk (mem_inf.mp hx).1).2.1
  constructor
  · intro hn
    rw [outerRestStab, sup_comm] at hn
    obtain ⟨a, ha, b, hb, rfl⟩ := ncyc_exists_mul_of_mem_sup hCV hn
    obtain ⟨haY, hat⟩ := mem_inf.mp ha
    refine ⟨mul_mem haY (hVY hb), ?_⟩
    rw [hc.outerRestPt_mul h hS2 hk haY (hVY hb), hc.outerRestPt_of_mem hb,
      outerRestPt_of_comm (mem_centralizer_singleton_iff.mp hat)]
    group
  · rintro ⟨hnY, hn1⟩
    obtain ⟨s, hs, hs2⟩ := hc.outerRest_exists_sq h hS2 (hc.outerRest_comm_t_mem h hS2 hk hnY) hn1
    have hc' : s⁻¹ * n ∈ normalizer (szR (szT₁ L T) V t : Set G) ⊓ centralizer ({t} : Set G) := by
      refine mem_inf.mpr ⟨mul_mem (inv_mem (hVY hs)) hnY, mem_centralizer_singleton_iff.mpr ?_⟩
      have e : n * t * n⁻¹ = s * t * s⁻¹ := by
        rw [hc.outerRest_conj_t hs, hs2]; group
      calc s⁻¹ * n * t = s⁻¹ * (n * t * n⁻¹) * n := by group
        _ = s⁻¹ * (s * t * s⁻¹) * n := by rw [e]
        _ = t * (s⁻¹ * n) := by group
    rw [show n = s * (s⁻¹ * n) by group]
    exact mul_mem_sup hs hc'

theorem outerRestStab_le
    (hc : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) (hk : 2 ≤ k) :
    outerRestStab L T V t ≤ normalizer (szR (szT₁ L T) V t : Set G) := fun _ hn =>
  ((hc.mem_outerRestStab_iff h hS2 hk).mp hn).1

theorem szR_le_outerRestStab (h : U3Start G L f t T) :
    szR (szT₁ L T) V t ≤ outerRestStab L T V t := by
  have htC := h.mem_centralizer_szT₁
  refine sup_le (sup_le (fun y hy => mem_sup_right (mem_inf.mpr ⟨Subgroup.le_normalizer
    (le_szR_left _ _ _ hy), mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp htC y hy)⟩)) le_sup_left) (zpowers_le.mpr
    (mem_sup_right (mem_inf.mpr ⟨Subgroup.le_normalizer (mem_szR_right _ _ _),
      mem_centralizer_singleton_iff.mpr rfl⟩)))

theorem outerRestPt_eq_iff
    (hc : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) (hk : 2 ≤ k) {x y : G}
    (hx : x ∈ normalizer (szR (szT₁ L T) V t : Set G))
    (hy : y ∈ normalizer (szR (szT₁ L T) V t : Set G)) :
    outerRestPt t k x = outerRestPt t k y ↔ x⁻¹ * y ∈ outerRestStab L T V t := by
  have hxy := mul_mem (inv_mem hx) hy
  have e := hc.outerRestPt_mul h hS2 hk hx hxy
  rw [mul_inv_cancel_left] at e
  rw [hc.mem_outerRestStab_iff h hS2 hk, e]
  constructor
  · intro h1
    refine ⟨hxy, ?_⟩
    have h2 : x * outerRestPt t k (x⁻¹ * y) * x⁻¹ = 1 :=
      mul_right_cancel (h1.symm.trans (one_mul _).symm)
    calc outerRestPt t k (x⁻¹ * y) = x⁻¹ * (x * outerRestPt t k (x⁻¹ * y) * x⁻¹) * x := by group
      _ = 1 := by rw [h2]; group
  · rintro ⟨-, h1⟩
    rw [h1]; group

theorem outerRest_card_le
    (hc : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) (hk : 2 ≤ k)
    {H : Subgroup G} (hH : H ≤ normalizer (szR (szT₁ L T) V t : Set G)) :
    Nat.card H ≤ 2 ^ f * Nat.card (H ⊓ outerRestStab L T V t : Subgroup G) ∧
      ((∀ b ∈ szA₁ (szT₁ L T), ∃ x ∈ H, outerRestPt t k x = b) →
        Nat.card H = 2 ^ f * Nat.card (H ⊓ outerRestStab L T V t : Subgroup G)) := by
  classical
  obtain ⟨-, hA₁card, -⟩ := h.facts_of_card_sylow hS2
  set N := H ⊓ outerRestStab L T V t with hNdef
  set N' := N.subgroupOf H with hN'
  let φ : H → szA₁ (szT₁ L T) := fun x => ⟨outerRestPt t k x, hc.outerRestPt_mem h hS2 hk (hH x.2)⟩
  have key : ∀ x y : H, φ x = φ y ↔ x⁻¹ * y ∈ N' := by
    intro x y
    rw [mem_subgroupOf, Subtype.ext_iff]
    simp only [φ, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hc.outerRestPt_eq_iff h hS2 hk (hH x.2) (hH y.2)]
    exact ⟨fun h1 => mem_inf.mpr ⟨mul_mem (inv_mem x.2) y.2, h1⟩, fun h1 => (mem_inf.mp h1).2⟩
  let ψ : H ⧸ N' → szA₁ (szT₁ L T) := Quotient.lift φ fun a b hab =>
    (key a b).mpr (QuotientGroup.leftRel_apply.mp hab)
  have hψ : Function.Injective ψ := by
    intro a b hab
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    exact QuotientGroup.eq.mpr ((key a b).mp hab)
  have h1 : N'.index ≤ 2 ^ f := by
    rw [← hA₁card]; exact Nat.card_le_card_of_injective ψ hψ
  have h3 := N'.card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : N ≤ H)).toEquiv] at h3
  refine ⟨by rw [← h3, mul_comm]; exact Nat.mul_le_mul_right _ h1, fun htr => ?_⟩
  have hsurj : Function.Surjective ψ := by
    rintro ⟨b, hb⟩
    obtain ⟨x, hx, hxb⟩ := htr b hb
    exact ⟨(⟨x, hx⟩ : H), Subtype.ext hxb⟩
  have h4 : N'.index = 2 ^ f := by
    rw [← hA₁card]
    exact Nat.card_eq_of_bijective ψ ⟨hψ, hsurj⟩
  rw [← h3, h4, mul_comm]

end U3C1OuterConf

end CFSG.SeitzReduction.RankOne

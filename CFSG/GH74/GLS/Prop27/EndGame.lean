module

public import CFSG.GH74.Uniqueness.Bender.Lemma32
public import CFSG.Walter.J1Props.Hyp
public import CFSG.Walter.Models
public import CFSG.Assembly.OddCoreSpan

public section

namespace CFSG.GH74.GLS.Prop27

open Subgroup CFSG CFSG.Blueprint
open scoped Pointwise

theorem pPrimeCore_two_eq_bot_of_forall {K : Type*} [Group K] (C : Subgroup K)
    (h : ∀ N : Subgroup K, N ≤ C → (∀ c ∈ C, ∀ x ∈ N, c * x * c⁻¹ ∈ N) → Odd (Nat.card N) →
      N = ⊥) : pPrimeCore 2 ↥C = ⊥ := by
  rw [pPrimeCore_eq_bot_iff]
  intro N hN hcop
  have hodd : Odd (Nat.card (N.map C.subtype)) := by
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact Nat.coprime_two_left.mp hcop
  refine (Subgroup.map_eq_bot_iff_of_injective N C.subtype_injective).mp
    (h (N.map C.subtype) ?_ ?_ hodd)
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · rintro c hc _ ⟨y, hy, rfl⟩
    exact ⟨⟨c, hc⟩ * y * ⟨c, hc⟩⁻¹, hN.conj_mem y hy ⟨c, hc⟩, rfl⟩

theorem involutionOddCore_eq_bot_iff {G : Type*} [Group G] (a : G) :
    Assembly.Dichotomy.involutionOddCore a = ⊥ ↔
      pPrimeCore 2 ↥(centralizer ({a} : Set G)) = ⊥ := by
  unfold Assembly.Dichotomy.involutionOddCore
  rw [Assembly.Dichotomy.oddCore_eq_pPrimeCore]
  exact Subgroup.map_eq_bot_iff_of_injective _ (centralizer ({a} : Set G)).subtype_injective

theorem pPrimeCore_centralizer_eq_bot_of_mulEquiv {G X : Type*} [Group G] [Group X] (e : G ≃* X)
    {a : G} (h : pPrimeCore 2 ↥(centralizer ({e a} : Set X)) = ⊥) :
    pPrimeCore 2 ↥(centralizer ({a} : Set G)) = ⊥ := by
  rw [← involutionOddCore_eq_bot_iff] at h ⊢
  rw [← Assembly.Dichotomy.involutionOddCore_map e a] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h

theorem center_eq_bot_of_simple_of_not_comm {K : Type*} [Group K] [IsSimpleGroup K]
    (hnc : ¬ ∀ x y : K, x * y = y * x) : Subgroup.center K = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · exact h
  · exfalso
    refine hnc fun x y => ?_
    have hy : y ∈ Subgroup.center K := h ▸ Subgroup.mem_top y
    exact Subgroup.mem_center_iff.mp hy x

theorem eq_one_of_isPGroup_two_of_odd_orderOf {K : Type*} [Group K] {Q : Subgroup K}
    (hQ : IsPGroup 2 Q) {x : K} (hx : x ∈ Q) (hodd : Odd (orderOf x)) : x = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ) ⟨x, hx⟩
  have hk' : orderOf x = 2 ^ k := by
    rw [← hk, ← Subgroup.orderOf_coe]
  rw [hk'] at hodd
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · rw [pow_zero] at hk'
    exact orderOf_eq_one_iff.mp hk'
  · exact absurd (Nat.even_pow.mpr ⟨even_two, hpos.ne'⟩) (Nat.not_even_iff_odd.mpr hodd)

section J1

open CFSG.Walter CFSG.Walter.J1 CFSG.Walter.J1Props CFSG.Open

theorem pPrimeCore_centralizer_t_eq_bot {G : Type} [Group G] [Finite G] (jh : JankoHyp₀ G) :
    pPrimeCore 2 ↥(centralizer ({jh.t} : Set G)) = ⊥ := by
  apply pPrimeCore_two_eq_bot_of_forall
  intro N hNC hNn hodd
  have hF : ∀ x ∈ N, x ∈ jh.F := fun x hx =>
    jh.mem_F_of_odd (hNC hx) (Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard N hx))
  have hsimple : IsSimpleGroup jh.F := A5Sub.isSimpleGroup jh.iso
  have hn : (N.subgroupOf jh.F).Normal :=
    ⟨fun x hx g => hNn g (jh.le_centralizer g.2) x hx⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf jh.F) with h0 | h0
  · rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hF x hx⟩ : jh.F) ∈ N.subgroupOf jh.F := hx
    rw [h0, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx')
  · exfalso
    have hle : jh.F ≤ N := fun x hx => by
      have : (⟨x, hx⟩ : jh.F) ∈ N.subgroupOf jh.F := h0 ▸ Subgroup.mem_top _
      exact this
    have hdvd : Nat.card jh.F ∣ Nat.card N := Subgroup.card_dvd_of_le hle
    rw [jh.card_F] at hdvd
    obtain ⟨k, hk⟩ := hodd
    omega

theorem pPrimeCore_centralizer_eq_bot_of_J1
    {G : Type} [Group G] [Finite G]
    (h : NativeSporadic.IsSporadic G .J1) :
    ∀ u : G, orderOf u = 2 → pPrimeCore 2 ↥(centralizer ({u} : Set G)) = ⊥ := by
  obtain ⟨e⟩ := h
  intro u hu
  let ε : G ≃* walterJ1 := e.trans walterJ1EquivNative.symm
  have hεu : orderOf (ε u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hu
  obtain ⟨g, hg⟩ := jankoHyp₀.exists_conj_eq_t hεu
  refine pPrimeCore_centralizer_eq_bot_of_mulEquiv (ε.trans (MulAut.conj g)) ?_
  have hεt : (ε.trans (MulAut.conj g)) u = jankoHyp₀.t := by
    simpa [MulAut.conj_apply] using hg
  rw [hεt]
  exact pPrimeCore_centralizer_t_eq_bot jankoHyp₀

end J1

section Bender

open CFSG.GH74.Uniqueness.Bender

theorem pPrimeCore_centralizer_eq_bot_of_benderCore
    {K : Type*} [Group K] [Finite K]
    {n i e : ℕ} (h : BenderType K n i e) (Q : Sylow 2 K) {t : K}
    (hc : BenderCore (2 ^ n) i e (Q : Subgroup K) t) {z : K}
    (hz : z ∈ rootCenter (Q : Subgroup K)) (hz1 : z ≠ 1) :
    pPrimeCore 2 ↥(centralizer ({z} : Set K)) = ⊥ := by
  have : IsSimpleGroup K := h.isSimple
  have hnc : ¬ ∀ x y : K, x * y = y * x := h.isSimpleBenderGroup.not_commutative
  obtain ⟨hle, hcen, -⟩ := h.lemma_3_4_b Q hc.sq_eq_one hc.not_mem (hc.involution_iff.mpr ⟨hz, hz1⟩)
  apply pPrimeCore_two_eq_bot_of_forall
  intro N hNC hNn hodd
  have hQC : (Q : Subgroup K) ≤ centralizer ({z} : Set K) := hcen ▸ le_sup_left
  have hQ2 : IsPGroup 2 (Q : Subgroup K) := Q.isPGroup'
  have hQnorm : ∀ c ∈ centralizer ({z} : Set K), ∀ q ∈ (Q : Subgroup K),
      c * q * c⁻¹ ∈ (Q : Subgroup K) := fun c hc' q hq =>
    (Subgroup.mem_normalizer_iff.mp (hle hc') q).mp hq
  have hNodd : ∀ x ∈ N, Odd (orderOf x) := fun x hx =>
    Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard N hx)
  have hcomm : ∀ x ∈ N, ∀ q ∈ (Q : Subgroup K), x * q = q * x := by
    intro x hx q hq
    have hw : q * x⁻¹ * q⁻¹ ∈ N := hNn q (hQC hq) x⁻¹ (N.inv_mem hx)
    have h1 : x * (q * x⁻¹ * q⁻¹) ∈ N := N.mul_mem hx hw
    have h2 : x * (q * x⁻¹ * q⁻¹) ∈ (Q : Subgroup K) := by
      have : x * (q * x⁻¹ * q⁻¹) = (x * q * x⁻¹) * q⁻¹ := by group
      rw [this]
      exact Q.mul_mem (hQnorm x (hNC hx) q hq) (Q.inv_mem hq)
    have h3 := eq_one_of_isPGroup_two_of_odd_orderOf hQ2 h2 (hNodd _ h1)
    calc x * q = x * (q * x⁻¹ * q⁻¹) * q * x := by group
      _ = q * x := by rw [h3, one_mul]
  have hFQ : fixCartan (Q : Subgroup K) t ≤ normalizer ((Q : Subgroup K) : Set K) :=
    (fixCartan_le_cartan _ t).trans (cartan_le_borel _ t)
  have hQF : (Q : Subgroup K) ⊓ fixCartan (Q : Subgroup K) t = ⊥ := by
    rw [eq_bot_iff, ← hc.inf_eq]
    exact inf_le_inf_left _ (fixCartan_le_cartan _ t)
  rw [eq_bot_iff]
  intro n hn
  have hnC : n ∈ (Q : Subgroup K) ⊔ fixCartan (Q : Subgroup K) t := hcen ▸ hNC hn
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left (Q : Subgroup K)
    (fixCartan (Q : Subgroup K) t) hFQ
  have hn' : n ∈ ((Q : Subgroup K) : Set K) * (fixCartan (Q : Subgroup K) t : Set K) := by
    rw [← hset]
    exact hnC
  obtain ⟨q, hq, f, hf, rfl⟩ := Set.mem_mul.mp hn'
  have hqf : q * f = f * q := by
    have h1 := hcomm (q * f) hn q hq
    calc q * f = q⁻¹ * (q * (q * f)) := by group
      _ = q⁻¹ * ((q * f) * q) := by rw [h1]
      _ = f * q := by group
  have hpow : (q * f) ^ orderOf (q * f) = 1 := pow_orderOf_eq_one _
  have hcf : Commute q f := hqf
  rw [hcf.mul_pow] at hpow
  have hqm : q ^ orderOf (q * f) ∈ (Q : Subgroup K) ⊓ fixCartan (Q : Subgroup K) t := by
    refine ⟨Q.pow_mem hq _, ?_⟩
    have : q ^ orderOf (q * f) = (f ^ orderOf (q * f))⁻¹ := eq_inv_of_mul_eq_one_left hpow
    rw [this]
    exact (fixCartan (Q : Subgroup K) t).inv_mem ((fixCartan (Q : Subgroup K) t).pow_mem hf _)
  rw [hQF, Subgroup.mem_bot] at hqm
  have hq1 : q = 1 :=
    eq_one_of_isPGroup_two_of_odd_orderOf hQ2 hq
      (Odd.of_dvd_nat (hNodd _ hn) (orderOf_dvd_of_pow_eq_one hqm))
  subst hq1
  rw [one_mul] at hn ⊢
  have hft : f * t = t * f := by
    have h1 := (hc.mem_fixCartan_iff.mp hf).2
    calc f * t = t * f * t * t := by rw [h1]
      _ = t * f := by rw [mul_assoc (t * f) t t, hc.sq_eq_one, mul_one]
  have hcent : ∀ g : K, g * f = f * g := by
    intro g
    have hg : g ∈ (Q : Subgroup K) ⊔ Subgroup.zpowers t := by
      rw [hc.sup_zpowers_eq_top hc.not_mem]
      exact Subgroup.mem_top g
    have hle2 : (Q : Subgroup K) ⊔ Subgroup.zpowers t ≤ centralizer ({f} : Set K) := by
      refine sup_le ?_ ?_
      · intro q hq
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hcomm f hn q hq).symm
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact hft.symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle2 hg)
  have hfc : f ∈ Subgroup.center K := Subgroup.mem_center_iff.mpr hcent
  rw [center_eq_bot_of_simple_of_not_comm hnc] at hfc
  exact hfc

theorem pPrimeCore_centralizer_eq_bot_of_benderType
    {K : Type*} [Group K] [Finite K] {n i e : ℕ}
    (h : BenderType K n i e) :
    ∀ u : K, orderOf u = 2 → pPrimeCore 2 ↥(centralizer ({u} : Set K)) = ⊥ := by
  intro u hu
  obtain ⟨t, hc⟩ := h.exists_benderCore (default : Sylow 2 K)
  have hu2 : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu, sq] at this
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu
    omega
  obtain ⟨g, hg, hg1⟩ := hc.exists_conj_rootCenter hu2 hu1
  refine pPrimeCore_centralizer_eq_bot_of_mulEquiv (MulAut.conj g⁻¹) ?_
  have hgu : (MulAut.conj g⁻¹ : MulAut K) u = g⁻¹ * u * g := by
    simp
  rw [hgu]
  exact pPrimeCore_centralizer_eq_bot_of_benderCore h _ hc hg hg1

theorem pPrimeCore_centralizer_eq_bot_of_isBenderGroup
    {G : Type} [Group G] [Finite G]
    (h : CFSG.BenderSuzuki.IsBenderGroup G) :
    ∀ u : G, orderOf u = 2 → pPrimeCore 2 ↥(centralizer ({u} : Set G)) = ⊥ := by
  obtain ⟨n, i, e, hG⟩ := isBenderGroup_iff_exists_benderType.mp h
  exact pPrimeCore_centralizer_eq_bot_of_benderType hG

end Bender

end CFSG.GH74.GLS.Prop27

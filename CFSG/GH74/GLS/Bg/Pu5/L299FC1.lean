module

public import CFSG.GH74.GLS.Bg.Pu5.L299FAB
public import CFSG.GH74.GLS.Bg.Pu5.BalBBasic

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.Iii2 CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_forall_conj_mem {N : Subgroup G} {g : G}
    (h : ∀ x ∈ N, g * x * g⁻¹ ∈ N) : g ∈ normalizer (N : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : N.map (MulAut.conj g).toMonoidHom ≤ N := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  exact Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge

omit [Finite G] in
theorem mem_of_pow_four_mem_of_odd_relIndex {N H : Subgroup G} {c : G} (hNH : N ≤ H) (hcH : c ∈ H)
    (hHN : H ≤ normalizer (N : Set G)) (hc4 : c ^ 4 ∈ N) (hodd : ¬ 2 ∣ N.relIndex H) : c ∈ N := by
  have hnorm : (N.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).2 hHN
  let c' : ↥H := ⟨c, hcH⟩
  have h4 : (QuotientGroup.mk c' : ↥H ⧸ N.subgroupOf H) ^ 4 = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hc4
  have hdvd1 : orderOf (QuotientGroup.mk c' : ↥H ⧸ N.subgroupOf H) ∣ 2 ^ 2 :=
    orderOf_dvd_of_pow_eq_one (by simpa using h4)
  have hdvd2 : orderOf (QuotientGroup.mk c' : ↥H ⧸ N.subgroupOf H) ∣ N.relIndex H :=
    orderOf_dvd_natCard _
  obtain ⟨j, hj, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd1
  have hj0 : j = 0 := by
    by_contra hne
    apply hodd
    refine (dvd_trans ?_ hdvd2)
    rw [hjo]
    exact dvd_pow_self 2 hne
  rw [hj0, pow_zero] at hjo
  have h1 : (QuotientGroup.mk c' : ↥H ⧸ N.subgroupOf H) = 1 := orderOf_eq_one_iff.1 hjo
  exact (QuotientGroup.eq_one_iff c').1 h1

omit [Finite G] in
theorem comm_of_exp_two {Q : Subgroup G} (hexp : ∀ q ∈ Q, q * q = 1) {a b : G} (ha : a ∈ Q)
    (hb : b ∈ Q) : a * b = b * a := by
  have h1 := hexp (a * b) (mul_mem ha hb)
  have h2 := hexp a ha
  have h3 := hexp b hb
  calc a * b = a * b * (a * b * (b * a)) := by
        have : a * b * (b * a) = 1 := by
          calc a * b * (b * a) = a * (b * b) * a := by group
            _ = 1 := by rw [h3, mul_one, h2]
        rw [this, mul_one]
    _ = (a * b * (a * b)) * (b * a) := by group
    _ = b * a := by rw [h1, one_mul]

omit [Finite G] in
theorem pPrimeCoreOf_le_cSec (K : Subgroup G) : pPrimeCoreOf 2 K ≤ cSec K := by
  intro r hr
  have hrK : r ∈ K := TwoThin.pPrimeCoreOf_le K hr
  refine ⟨le_normalizer hrK, TwoThin.mem_normalizer_pPrimeCoreOf (le_normalizer hrK), fun κ hκ => ?_⟩
  have hκN : κ ∈ normalizer (pPrimeCoreOf 2 K : Set G) :=
    TwoThin.mem_normalizer_pPrimeCoreOf (le_normalizer hκ)
  exact mul_mem ((mem_normalizer_iff.1 hκN r).1 hr) (inv_mem hr)

variable {z t : G} {S : Subgroup G}

theorem not_inducesInner_t (h44 : II4_44) (hquat : II4_4_quat) (h296 : L296) (hC : Cfg G z t S)
    (hcard : Set.ncard {K : Subgroup G | IsRigidRankOneComp z K} = 1) {K : Subgroup G}
    (hK : IsRigidRankOneComp z K) (hQ4 : Nat.card ↥(S ⊓ cSec K) = 4)
    (hQnc : ¬ IsCyclic ↥(S ⊓ cSec K)) : ¬ InducesInner t K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨k, hkK, hc⟩
  have hz2 : z * z = 1 := hC.z_mul_self
  have ht2 : t * t = 1 := hC.t_mul_self
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hKC : K ≤ centralizer ({z} : Set G) := (rr_pcomp hK).1
  have hSC : S ≤ centralizer ({z} : Set G) := hC.sylow.le
  have htN : t ∈ normalizer (K : Set G) := mem_normalizer_of_ncard_one hcard hK hC.tC
  set R : Subgroup G := pPrimeCoreOf 2 K with hR
  have hRodd : Odd (Nat.card R) := TwoThin.card_pPrimeCoreOf_odd K
  have hRK : R ≤ K := TwoThin.pPrimeCoreOf_le K
  have hCz : ∀ g ∈ centralizer ({z} : Set G), g ∈ normalizer (R : Set G) := fun g hg =>
    TwoThin.mem_normalizer_pPrimeCoreOf (mem_normalizer_of_ncard_one hcard hK hg)
  set Q : Subgroup G := S ⊓ cSec K with hQ
  set D : Subgroup G := cSec K ⊓ centralizer ({z} : Set G) with hD
  have hQD : Q ≤ D := fun q hq => ⟨hq.2, hSC hq.1⟩
  have hRD : R ≤ D := fun r hr => ⟨pPrimeCoreOf_le_cSec K hr, hKC (hRK hr)⟩
  set N : Subgroup G := Q ⊔ R with hN
  have hND : N ≤ D := sup_le hQD hRD
  set c : G := t * k⁻¹ with hcdef
  have hkz : k⁻¹ ∈ centralizer ({z} : Set G) := (centralizer ({z} : Set G)).inv_mem (hKC hkK)
  have hcD : c ∈ D := ⟨hc, (centralizer ({z} : Set G)).mul_mem hC.tC hkz⟩
  have hcCz : c ∈ centralizer ({z} : Set G) := hcD.2
  have hQK : IsSL2Or2A7 (Hat K) := h44 G hC.simple z hC.hz K (rr_pcomp hK) hK.2
  have hc2K : c * c ∈ K := by
    have e : c * c = (t * k⁻¹ * t⁻¹) * k⁻¹ := by
      rw [hcdef, htinv]
      group
    rw [e]
    exact mul_mem ((mem_normalizer_iff.1 htN k⁻¹).1 (inv_mem hkK)) (inv_mem hkK)
  have hc4R : (c * c) * (c * c) ∈ R := by
    have hc2S : c * c ∈ cSec K := mul_mem hc hc
    have hmem : hatMk K ⟨c * c, hc2K⟩ ∈ Subgroup.center (Hat K) := by
      rw [Subgroup.mem_center_iff]
      intro x
      obtain ⟨κ, rfl⟩ := hatMk_surjective K x
      have h1 : hatMk K ⁅κ, (⟨c * c, hc2K⟩ : ↥K)⁆ = 1 :=
        (hatMk_eq_one_iff K _).2 (hc2S.2.2 (κ : G) κ.2)
      rw [map_commutatorElement] at h1
      exact commutatorElement_eq_one_iff_mul_comm.1 h1
    have hsq : (⟨hatMk K ⟨c * c, hc2K⟩, hmem⟩ : ↥(Subgroup.center (Hat K))) ^ 2 = 1 := by
      have := pow_card_eq_one' (G := ↥(Subgroup.center (Hat K)))
        (x := ⟨hatMk K ⟨c * c, hc2K⟩, hmem⟩)
      rwa [hQK.2] at this
    have hsq' : hatMk K ⟨c * c, hc2K⟩ * hatMk K ⟨c * c, hc2K⟩ = 1 := by
      have := congrArg Subtype.val hsq
      simpa [pow_two] using this
    have hK4 : (c * c) * (c * c) ∈ K := mul_mem hc2K hc2K
    refine (hatMk_eq_one_iff K ⟨(c * c) * (c * c), hK4⟩).1 ?_
    rw [show (⟨(c * c) * (c * c), hK4⟩ : ↥K) = ⟨c * c, hc2K⟩ * ⟨c * c, hc2K⟩ from rfl, map_mul]
    exact hsq'
  have hcQ : ∀ q ∈ Q, c * q * c⁻¹ ∈ N := by
    intro q hq
    have hqinv : q⁻¹ ∈ cSec K := (cSec K).inv_mem hq.2
    have hρ : q⁻¹ * k⁻¹ * q * k ∈ R := by
      have h1 : ⁅k⁻¹, q⁻¹⁆ ∈ R := hqinv.2.2 k⁻¹ (inv_mem hkK)
      have h2 := inv_mem h1
      have e : (⁅k⁻¹, q⁻¹⁆)⁻¹ = q⁻¹ * k⁻¹ * q * k := by
        simp only [commutatorElement_def]
        group
      rwa [e] at h2
    have e : c * q * c⁻¹ = (t * q * t⁻¹) * (t * (q⁻¹ * k⁻¹ * q * k) * t⁻¹) := by
      rw [hcdef]
      group
    rw [e]
    refine mul_mem (mem_sup_left (Q_conj hC hcard hK hC.tS hq)) (mem_sup_right ?_)
    exact (mem_normalizer_iff.1 (hCz t hC.tC) _).1 hρ
  have hcR : ∀ r ∈ R, c * r * c⁻¹ ∈ N := fun r hr =>
    mem_sup_right ((mem_normalizer_iff.1 (hCz c hcCz) r).1 hr)
  have hcNorm : c ∈ normalizer (N : Set G) := by
    refine mem_normalizer_of_forall_conj_mem fun x hx => ?_
    have hle : N ≤ N.comap (MulAut.conj c).toMonoidHom := by
      refine sup_le (fun q hq => ?_) (fun r hr => ?_)
      · exact hcQ q hq
      · exact hcR r hr
    exact hle hx
  have hcN : c ∈ N := by
    set H : Subgroup G := N ⊔ Subgroup.zpowers c with hH
    have hNH : N ≤ H := le_sup_left
    have hcH : c ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
    have hHN : H ≤ normalizer (N : Set G) :=
      sup_le (fun x hx => le_normalizer hx) (Subgroup.zpowers_le.2 hcNorm)
    have hHD : H ≤ D := sup_le hND (Subgroup.zpowers_le.2 hcD)
    have hQsyl : IsSylowOf 2 Q D :=
      (isSylowOf_inf_cSec hC hcard hK).of_le hQD inf_le_left
    have hQodd : ¬ 2 ∣ Q.relIndex D := (isSylowOf_iff.1 hQsyl).2.2
    have hQN : Q ≤ N := le_sup_left
    have h1 := Subgroup.relIndex_mul_relIndex Q N H hQN hNH
    have h2 := Subgroup.relIndex_mul_relIndex Q H D (hQN.trans hNH) hHD
    have hodd : ¬ 2 ∣ N.relIndex H := by
      intro hd
      apply hQodd
      rw [← h2, ← h1]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left hd _) _
    have hc4N : c ^ 4 ∈ N := by
      have e : c ^ 4 = (c * c) * (c * c) := by
        rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      rw [e]
      exact mem_sup_right hc4R
    exact mem_of_pow_four_mem_of_odd_relIndex hNH hcH hHN hc4N hodd
  have hz1 : z ≠ 1 := by
    intro h
    have := hC.hz
    rw [h, orderOf_one] at this
    omega
  have hexp := exp_two_of_card_four hQ4 hQnc
  obtain ⟨w, hwQ, hw1, hwz⟩ := exists_ne_of_card_four (Q := Q) hQ4 hz2 hz1
  have htw : t * w * t⁻¹ = z * w := t_conj_w h44 hquat h296 hC hcard hK hexp hwQ hw1 hwz
  have hwC : w ∈ centralizer ({z} : Set G) := hSC hwQ.1
  have hcw : ⁅c, w⁆ ∈ R := by
    have hS' : ∀ M ∈ ({Q, R} : Set (Subgroup G)), M ≤ centralizer ({z} : Set G) := by
      intro M hM
      rcases hM with rfl | hM
      · exact fun q hq => hSC hq.1
      · rw [Set.mem_singleton_iff.1 hM]
        exact fun r hr => hKC (hRK hr)
    have key := commutator_mem_of_le_sSup (C := centralizer ({z} : Set G)) (N := R) (y := w)
      hCz (S := {Q, R}) hS' (by
        intro M hM m hm
        rcases hM with rfl | hM
        · have := comm_of_exp_two hexp hm hwQ
          rw [commutatorElement_eq_one_iff_mul_comm.2 this]
          exact one_mem _
        · rw [Set.mem_singleton_iff.1 hM] at hm
          have e : ⁅m, w⁆ = m * (w * m⁻¹ * w⁻¹) := by
            simp only [commutatorElement_def]
            group
          rw [e]
          exact mul_mem hm ((mem_normalizer_iff.1 (hCz w hwC) m⁻¹).1 (inv_mem hm)))
    rw [sSup_pair] at key
    exact key c hcN
  have hkw : ⁅k, w⁆ ∈ R := hwQ.2.2.2 k hkK
  have hzR : z ∈ R := by
    have e : z = (c * ⁅k, w⁆ * c⁻¹) * ⁅c, w⁆ := by
      have h1 : t * w * t⁻¹ * w⁻¹ = z := by
        rw [htw]
        group
      rw [← h1, hcdef]
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem ((mem_normalizer_iff.1 (hCz c hcCz) _).1 hkw) hcw
  have hdvd : orderOf z ∣ Nat.card R := Subgroup.orderOf_dvd_natCard R hzR
  rw [hC.hz] at hdvd
  exact (Nat.not_even_iff_odd.2 hRodd) (even_iff_two_dvd.2 hdvd)

end CFSG.GH74.GLS.Bg.Pu5

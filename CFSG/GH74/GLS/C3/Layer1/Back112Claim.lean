module

public import CFSG.GH74.GLS.C3.Layer1.Back112Gamma
public import CFSG.GH74.GLS.C3.Layer1.Back112Iv2
public import CFSG.GH74.GLS.C3.Layer1.Back112Lift
public import CFSG.GH74.GLS.C3.Layer1.Back112Omega
public import CFSG.GH74.GLS.C3.Layer1.Back91Setup

public section

namespace CFSG.GH74.GLS.C3.Layer1.Back

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.U1a
open CFSG.GH74.GLS.C3.Layer1.Back.Setup91 (mem_pPrimeCoreOf_iff)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem conj_mem_CMK {L M : Subgroup G} (hLM : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L) {m c : G}
    (hm : m ∈ M) (hc : c ∈ CMK M L) : m * c * m⁻¹ ∈ CMK M L := by
  obtain ⟨hcM, hcL, hcO, hcomm⟩ := mem_CMK_iff.1 hc
  refine mem_CMK_iff.2 ⟨M.mul_mem (M.mul_mem hm hcM) (M.inv_mem hm), ?_, ?_, ?_⟩
  · exact mul_mem (mul_mem (mem_normalizer_of_norm hLM hm) hcL)
      (inv_mem (mem_normalizer_of_norm hLM hm))
  · exact mul_mem (mul_mem (mem_normalizer_pPrimeCoreOf hLM hm) hcO)
      (inv_mem (mem_normalizer_pPrimeCoreOf hLM hm))
  · intro k hk
    have hk' : m⁻¹ * k * m ∈ L := by simpa using hLM m⁻¹ (M.inv_mem hm) k hk
    have h1 := hcomm _ hk'
    have h2 : ⁅k, m * c * m⁻¹⁆ = m * ⁅m⁻¹ * k * m, c⁆ * m⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h2]
    exact pPrimeCoreOf_norm hLM hm h1

theorem exists_bar_of_conj {K : Subgroup G} {p z : G} (hp : p ∈ K) (hz : z ∈ K)
    (hconj : IsConj (QuotientGroup.mk (⟨p, hp⟩ : ↥K) : kBar K) (QuotientGroup.mk ⟨z, hz⟩)) :
    ∃ k ∈ K, k⁻¹ * p * k * z⁻¹ ∈ pPrimeCoreOf 2 K := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective c
  have hc' : (QuotientGroup.mk (k' * ⟨p, hp⟩ * k'⁻¹) : kBar K) = QuotientGroup.mk ⟨z, hz⟩ := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hc
  rw [QuotientGroup.eq_iff_div_mem] at hc'
  refine ⟨((k'⁻¹ : ↥K) : G), (k'⁻¹).2, ?_⟩
  have e : ((k' * ⟨p, hp⟩ * k'⁻¹ / ⟨z, hz⟩ : ↥K) : G) =
      ((k'⁻¹ : ↥K) : G)⁻¹ * p * ((k'⁻¹ : ↥K) : G) * z⁻¹ := by
    simp [div_eq_mul_inv]
  rw [← e]
  exact mem_pPrimeCoreOf_iff.2 ⟨(k' * ⟨p, hp⟩ * k'⁻¹ / ⟨z, hz⟩ : ↥K).2, hc'⟩

theorem eq_one_of_conj_eq_one {g x : G} (h : g⁻¹ * x * g = 1) : x = 1 := by
  have e : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
  rw [e, h]; group

variable [Finite G]

theorem claim112 {x : G} {K M T Q : Subgroup G} (hh : Hyp9A x K K M T Q)
    (hG : IsKProperSimple G) (h81 : B_iv2_8_1) (h92 : B_lemma92)
    (hlist : HasL2Model (kBar K) Odd ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    (hs : IsSimpleGroup (kBar K)) (hn : ∃ a b : kBar K, a * b ≠ b * a)
    (hconj : ∀ a b : kBar K, orderOf a = 2 → orderOf b = 2 → IsConj a b)
    (hQe : CFSG.IsElementaryAbelian 2 ↥Q ∧ Nat.card ↥Q = 4)
    {g : G} (hgR : conjugate Q g ≤ (T ⊓ K) ⊔ Q) (hgQ : conjugate Q g ⊓ Q = ⊥)
    {z : G} (hzP : z ∈ T ⊓ K) (hz2 : orderOf z = 2)
    {W : Subgroup G} (hWT : W ≤ T)
    (hwc : ∀ g : G, conjugate W g ≤ T → conjugate W g = W)
    (hQE : Q ≤ omegaZ W) (hzE : z ∈ omegaZ W) (hcard : Nat.card ↥(omegaZ W) ≤ 8) : False := by
  set E : Subgroup G := omegaZ W with hEdef
  have hET : E ≤ T := (omegaZ_le W).trans hWT
  have hEW : ∀ e ∈ E, ∀ w ∈ W, e * w = w * e := fun e he w hw => he.2.1 w hw
  have hEN : ∀ n ∈ normalizer (W : Set G), ∀ e ∈ E, n⁻¹ * e * n ∈ E :=
    fun n hn e he => omegaZ_conj hn he
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hR, hcomm, hPQ⟩ := hh.R_eq hs hn
  have hQ2 : IsPGroup 2 ↥Q := hh.sylowQ.isPGroup
  obtain ⟨hQab, hQsq⟩ := forall_of_isElementaryAbelian hQe.1
  have hTp : IsPGroup 2 ↥T := hh.sylowT.isPGroup
  have hQT : Q ≤ T := Setup91.Q_le_T hh
  have hTM : T ≤ M := hh.sylowTM.le
  have hxQ : x ∈ Q := hh.x_mem_Q
  have hx1 : x ≠ 1 := by
    intro h1
    have := hh.orderOf_x
    rw [h1, orderOf_one] at this
    omega
  have hNM : ∀ n ∈ normalizer (W : Set G), n ∈ M := by
    intro n hnW
    by_contra hnM
    have hVE : conjugate Q n ≤ E := by
      intro v hv
      have hv' := mem_conjugate_iff'.1 hv
      have h1 := hEN n hnW _ (hQE hv')
      have e : n⁻¹ * (n * v * n⁻¹) * n = v := by group
      rw [e] at h1; exact h1
    have hVT : conjugate Q n ≤ T := hVE.trans hET
    have hV0 : conjugate Q n ≠ ⊥ := by
      intro h0
      have h1 : Nat.card ↥(conjugate Q n) = 4 := by rw [card_conjugate']; exact hQe.2
      rw [h0, Subgroup.card_bot] at h1
      omega
    have hV2 : 2 ≤ pRank 2 ↥(conjugate Q n) := by
      rw [pRank_conjugate']; exact hh.rankQ
    have hbot : conjugate Q n ⊓ CMK M K = ⊥ :=
      inf_CMK_eq_bot_of_not_mem hh hG h81 h92 hlist hnM le_rfl (hVT.trans hTM) hV0 hV2
    have hQV : conjugate Q n ⊓ Q = ⊥ := by
      refine eq_bot_iff.2 fun y hy => ?_
      have hy' : y ∈ conjugate Q n ⊓ CMK M K := ⟨hy.1, hh.sylowQ.le hy.2⟩
      rw [hbot] at hy'
      exact hy'
    have hcardprod := CFSG.GH74.GLS.C3.Layer1.P34.card_mul_inf (conjugate Q n) Q
    rw [hQV, Subgroup.card_bot, mul_one, card_conjugate', hQe.2] at hcardprod
    have hsub : ((conjugate Q n : Subgroup G) : Set G) * (Q : Set G) ⊆ (E : Set G) := by
      rintro _ ⟨a, ha, b, hb, rfl⟩
      exact E.mul_mem (hVE ha) (hQE hb)
    have hle : Nat.card ↥(((conjugate Q n : Subgroup G) : Set G) * (Q : Set G)) ≤
        Nat.card ↥(E : Set G) := Nat.card_mono (Set.toFinite _) hsub
    have hE' : Nat.card ↥(E : Set G) = Nat.card ↥E := rfl
    omega
  have hux : g⁻¹ * x * g ∈ conjugate Q g := by
    rw [mem_conjugate_iff']
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [e]; exact hxQ
  obtain ⟨p, hpP, q, hqQ, hpq⟩ := exists_mul_of_mem_sup_of_commute hcomm (hgR hux)
  have hx2 : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hh.orderOf_x, sq] at this
  have hu2 : (p * q) * (p * q) = 1 := by
    rw [← hpq]
    have e : g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
    rw [e, hx2]; group
  have hq2 : q * q = 1 := hQsq q hqQ
  have hpqc : p * q = q * p := hcomm p hpP q hqQ
  have hp2 : p * p = 1 := by
    have e : (p * q) * (p * q) = (p * p) * (q * q) := by
      calc (p * q) * (p * q) = p * (q * p) * q := by group
        _ = p * (p * q) * q := by rw [← hpqc]
        _ = (p * p) * (q * q) := by group
    rw [e, hq2, mul_one] at hu2
    exact hu2
  have hp1 : p ≠ 1 := by
    intro hp1
    rw [hp1, one_mul] at hpq
    have hq' : g⁻¹ * x * g ∈ Q := by rw [hpq]; exact hqQ
    have hmem : g⁻¹ * x * g ∈ conjugate Q g ⊓ Q := ⟨hux, hq'⟩
    rw [hgQ, Subgroup.mem_bot] at hmem
    exact hx1 (eq_one_of_conj_eq_one hmem)
  have hpo : orderOf p = 2 := orderOf_eq_prime (by rw [sq]; exact hp2) hp1
  have hpK : p ∈ K := hpP.2
  have hzK : z ∈ K := hzP.2
  have hbarP : (QuotientGroup.mk (⟨p, hpK⟩ : ↥K) : kBar K) ≠ 1 := by
    intro h1
    have hO : p ∈ pPrimeCoreOf 2 K := mem_pPrimeCoreOf_iff.2 ⟨hpK, (QuotientGroup.eq_one_iff _).1 h1⟩
    have hmem : p ∈ T ⊓ pPrimeCoreOf 2 K := ⟨hpP.1, hO⟩
    rw [Setup91.inf_pPrimeCoreOf_eq_bot K hTp, Subgroup.mem_bot] at hmem
    exact hp1 hmem
  have hbarZ : (QuotientGroup.mk (⟨z, hzK⟩ : ↥K) : kBar K) ≠ 1 := by
    intro h1
    have hO : z ∈ pPrimeCoreOf 2 K := mem_pPrimeCoreOf_iff.2 ⟨hzK, (QuotientGroup.eq_one_iff _).1 h1⟩
    have hmem : z ∈ T ⊓ pPrimeCoreOf 2 K := ⟨hzP.1, hO⟩
    rw [Setup91.inf_pPrimeCoreOf_eq_bot K hTp, Subgroup.mem_bot] at hmem
    rw [hmem, orderOf_one] at hz2
    omega
  have hz2' : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, sq] at this
  have hbarP2 : orderOf (QuotientGroup.mk (⟨p, hpK⟩ : ↥K) : kBar K) = 2 := by
    refine orderOf_eq_prime ?_ hbarP
    rw [sq, ← QuotientGroup.mk_mul]
    have : (⟨p, hpK⟩ : ↥K) * ⟨p, hpK⟩ = 1 := Subtype.ext hp2
    rw [this]; rfl
  have hbarZ2 : orderOf (QuotientGroup.mk (⟨z, hzK⟩ : ↥K) : kBar K) = 2 := by
    refine orderOf_eq_prime ?_ hbarZ
    rw [sq, ← QuotientGroup.mk_mul]
    have : (⟨z, hzK⟩ : ↥K) * ⟨z, hzK⟩ = 1 := Subtype.ext hz2'
    rw [this]; rfl
  have hbar := exists_bar_of_conj hpK hzK (hconj _ _ hbarP2 hbarZ2)
  have hQK : ∀ q ∈ Q, ∀ k ∈ K, q * k * q⁻¹ ∈ K := fun q hq k hk =>
    (mem_normalizer_iff.1 (mem_CMK_iff.1 (hh.sylowQ.le hq)).2.1 k).1 hk
  have hQt : ∀ q ∈ Q, ∀ k ∈ K, ⁅k, q⁆ ∈ pPrimeCoreOf 2 K := fun q hq k hk =>
    (mem_CMK_iff.1 (hh.sylowQ.le hq)).2.2.2 k hk
  obtain ⟨h, hhK, hhQ, hpz⟩ := exists_conj_centralizing hQ2 hQK hQt hpK hzK hpo hz2
    (fun q hq => hcomm p hpP q hq) (fun q hq => hcomm z hzP q hq) hbar
  have hqh : h⁻¹ * q * h = q := by
    have h1 := hhQ q hqQ
    calc h⁻¹ * q * h = h⁻¹ * (q * h) := by group
      _ = h⁻¹ * (h * q) := by rw [h1]
      _ = q := by group
  have hw : (g * h)⁻¹ * x * (g * h) = z * q := by
    have e : (g * h)⁻¹ * x * (g * h) = h⁻¹ * (g⁻¹ * x * g) * h := by group
    rw [e, hpq]
    calc h⁻¹ * (p * q) * h = (h⁻¹ * p * h) * (h⁻¹ * q * h) := by group
      _ = z * q := by rw [hpz, hqh]
  have hwE : z * q ∈ E := E.mul_mem hzE (hQE hqQ)
  have hwy : z * q ∈ centralizer (W : Set G) ⊓ T :=
    ⟨Subgroup.mem_centralizer_iff.2 fun w hw' => (hEW _ hwE w hw').symm, hET hwE⟩
  obtain ⟨n, hnW, hn⟩ := iv2_3_2 hh.sylowT hWT hwc hwy hw.symm
  have hnM : n ∈ M := hNM n hnW
  have hxC : x ∈ CMK M K := hh.sylowQ.le hxQ
  have hnC : n⁻¹ * x * n ∈ CMK M K := by
    have := conj_mem_CMK hh.L_normal.2 (M.inv_mem hnM) hxC
    rwa [inv_inv] at this
  have hTC : T ⊓ CMK M K = Q :=
    hh.sylowQ.eq_of_le (le_inf hQT hh.sylowQ.le) inf_le_right hTp.to_inf_left
  have hwQ : z * q ∈ Q := by
    have hmem : z * q ∈ T ⊓ CMK M K := ⟨hwy.2, by rw [hn]; exact hnC⟩
    rwa [hTC] at hmem
  have hu : g⁻¹ * x * g ∈ Q := by
    have e : g⁻¹ * x * g = h * (z * q) * h⁻¹ := by
      rw [← hw]; group
    have hc := hhQ (z * q) hwQ
    rw [e, hc]
    simpa using hwQ
  have hmem : g⁻¹ * x * g ∈ conjugate Q g ⊓ Q := ⟨hux, hu⟩
  rw [hgQ, Subgroup.mem_bot] at hmem
  exact hx1 (eq_one_of_conj_eq_one hmem)

end CFSG.GH74.GLS.C3.Layer1.Back

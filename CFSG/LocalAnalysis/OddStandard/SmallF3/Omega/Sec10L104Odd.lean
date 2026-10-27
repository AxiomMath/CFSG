module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L104Cent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109Dg

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec10L104_odd_orderOf [Finite G] {X : Subgroup G} {x : G} (hx : x ∈ oddCoreIn X) :
    Odd (orderOf x) :=
  (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn X).of_dvd_nat
    ((oddCoreIn X).orderOf_dvd_natCard hx)

theorem sec10L104_two_pow_Q {K1 K2 : Subgroup G} {x : G} (hx : x ∈ secQ K1 K2) :
    ∃ m : ℕ, x ^ (2 ^ m) = 1 := by
  obtain ⟨m, hm⟩ := isPGroup_twoCoreIn (K1 ⊔ K2) (⟨x, hx⟩ : ↥(secQ K1 K2))
  exact ⟨m, congrArg Subtype.val hm⟩

theorem sec10L104_Ot_le_centralizer [Finite G] (h36 : Asc82Lemma36) (hb : Asc82Basic10)
    {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    (hctx : Sec10Ctx G t L S z K1 K2) :
    oddCoreIn (centralizer ({t} : Set G)) ≤ centralizer (L : Set G) := by
  have hpsp : IsPSp43 L := (hb G t L S z hctx.toSec10Z).1
  have hLt : L ≤ centralizer ({t} : Set G) := hctx.component.le
  have hN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    sec4_mem_normalizer h36 hctx.toSec10Z.toSec10Setting.toSec3SettingLB
  have hzL : z ∈ L := (hctx.pocket1.2.1 hctx.pocket1.1).1
  have hz2 : orderOf z = 2 := hctx.toSec10Z.pocket.1
  exact sec10K0_oddCore_le_centralizer hpsp hzL hz2 hLt hN

theorem sec10L104_oddK0_le_centralizer [Finite G] (hK0 : Asc82Lemma10K0)
    (h36 : Asc82Lemma36) (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5)
    (hb : Asc82Basic10) {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    (hctx : Sec10Ctx G t L S z K1 K2) :
    oddCoreIn (secK0 t z) ≤ centralizer (L : Set G) := by
  have hpsp : IsPSp43 L := (hb G t L S z hctx.toSec10Z).1
  have hOleC := sec10L104_Ot_le_centralizer h36 hb hctx
  have hOle : oddCoreIn (centralizer ({t} : Set G)) ≤ oddCoreIn (secK0 t z) :=
    sec10D_oddC_le_oddK0 hK0 hctx
  have hK1L : K1 ≤ L := hctx.pocket1.2.1.trans inf_le_left
  have hK2L : K2 ≤ L := hctx.pocket2.2.1.trans inf_le_left
  have hKsupL : K1 ⊔ K2 ≤ L := sup_le hK1L hK2L
  have hcOK : ∀ h ∈ oddCoreIn (centralizer ({t} : Set G)), ∀ k ∈ K1 ⊔ K2, h * k = k * h := by
    intro h hh k hk
    exact (Subgroup.mem_centralizer_iff.mp (hOleC hh) k (hKsupL hk)).symm
  have hK0le : K1 ⊔ K2 ≤ secK0 t z := by
    obtain ⟨hK1, hK2, -⟩ := sec10D_K0_contains hK0 hctx
    exact sup_le hK1 hK2
  have hz2 : orderOf z = 2 := hctx.toSec10Z.pocket.1
  intro x hxN
  have hxK0 : x ∈ secK0 t z := CFSG.ClassicalInvolution.Balance.oddCoreIn_le _ hxN
  have hxO : x ∈ oddCoreIn (centralizer ({t} : Set G)) ⊔ (K1 ⊔ K2) := by
    have h := (hK0 G t L S z K1 K2 hctx).1
    rw [← sup_assoc, ← h]
    exact hxK0
  obtain ⟨n, hn, k, hk, hxnk⟩ := exists_mul_of_mem_sup_of_commute hcOK hxO
  have hnN : n ∈ oddCoreIn (secK0 t z) := hOle hn
  have hkN : k ∈ oddCoreIn (secK0 t z) := by
    have h : k = n⁻¹ * x := by rw [hxnk]; group
    rw [h]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hnN) hxN
  have hkcQ : ∀ q ∈ secQ K1 K2, k * q = q * k := by
    intro q hq
    have hqK : q ∈ K1 ⊔ K2 := twoCoreIn_le_self (K1 ⊔ K2) hq
    have h1 : q * k⁻¹ * q⁻¹ ∈ oddCoreIn (secK0 t z) :=
      CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn (X := secK0 t z) (hK0le hqK)
        (Subgroup.inv_mem _ hkN)
    have hcomm1 : k * q * k⁻¹ * q⁻¹ ∈ oddCoreIn (secK0 t z) := by
      have h2 := Subgroup.mul_mem _ hkN h1
      have e : k * (q * k⁻¹ * q⁻¹) = k * q * k⁻¹ * q⁻¹ := by group
      rwa [e] at h2
    have hcomm2 : k * q * k⁻¹ * q⁻¹ ∈ secQ K1 K2 :=
      Subgroup.mul_mem _ (sec10L104_conj_Q k hk q hq) (Subgroup.inv_mem _ hq)
    have h1' : k * q * k⁻¹ * q⁻¹ = 1 :=
      sec10L104_eq_one_of_odd_two (sec10L104_odd_orderOf hcomm1) (sec10L104_two_pow_Q hcomm2)
    calc k * q = (k * q * k⁻¹ * q⁻¹) * (q * k) := by group
      _ = q * k := by rw [h1', one_mul]
  have hkZ : k ∈ zpowers z := sec10L104_cent_Q hP5 hC5 hpsp hctx k hk hkcQ
  have hk1 : k = 1 := by
    refine sec10L104_eq_one_of_odd_two (sec10L104_odd_orderOf hkN) ⟨1, ?_⟩
    have hdvd : orderOf k ∣ 2 := (orderOf_dvd_of_mem_zpowers hkZ).trans (by rw [hz2])
    simpa using orderOf_dvd_iff_pow_eq_one.mp hdvd
  rw [hxnk, hk1, mul_one]
  exact hOleC hn

theorem sec10L104_decomp [Finite G] (hK0 : Asc82Lemma10K0) (h36 : Asc82Lemma36)
    (hb : Asc82Basic10) {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    (hctx : Sec10Ctx G t L S z K1 K2) :
    ∀ x ∈ secK0 t z, ∃ n ∈ oddCoreIn (secK0 t z), ∃ k ∈ K1 ⊔ K2, x = n * k := by
  have hOleC := sec10L104_Ot_le_centralizer h36 hb hctx
  have hOle : oddCoreIn (centralizer ({t} : Set G)) ≤ oddCoreIn (secK0 t z) :=
    sec10D_oddC_le_oddK0 hK0 hctx
  have hK1L : K1 ≤ L := hctx.pocket1.2.1.trans inf_le_left
  have hK2L : K2 ≤ L := hctx.pocket2.2.1.trans inf_le_left
  have hKsupL : K1 ⊔ K2 ≤ L := sup_le hK1L hK2L
  have hcOK : ∀ h ∈ oddCoreIn (centralizer ({t} : Set G)), ∀ k ∈ K1 ⊔ K2, h * k = k * h := by
    intro h hh k hk
    exact (Subgroup.mem_centralizer_iff.mp (hOleC hh) k (hKsupL hk)).symm
  intro x hx
  have hxO : x ∈ oddCoreIn (centralizer ({t} : Set G)) ⊔ (K1 ⊔ K2) := by
    have h := (hK0 G t L S z K1 K2 hctx).1
    rw [← sup_assoc, ← h]
    exact hx
  obtain ⟨n, hn, k, hk, hxnk⟩ := exists_mul_of_mem_sup_of_commute hcOK hxO
  exact ⟨n, hOle hn, k, hk, hxnk⟩

end CFSG.OddStandard.SmallF3.Omega

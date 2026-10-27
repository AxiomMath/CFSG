module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Steps
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ZStar
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ZSub
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ZIso
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ZNorm

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private theorem isSubnormal_subgroupOf_of_eq {X : Type*} [Group X] {K A B : Subgroup X}
    (hAB : A = B) (h : (K.subgroupOf A).IsSubnormal) : (K.subgroupOf B).IsSubnormal := by
  subst hAB
  exact h

theorem asc82Step105Z_of (h36 : Asc82Lemma36) (hb : Asc82Basic10) (hP5 : Asc82FactPockets5) :
    Asc82Step105Z := by
  intro G _ _ t L S z K1 K2 hctx hS hsc
  obtain ⟨hpsp, -, -, htS, -, -⟩ := hb G t L S z hctx.toSec10Z
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [hctx.involution] at h
    simpa [pow_two] using h
  have hz2 : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hctx.toSec10Z.pocket.1] at h
    simpa [pow_two] using h
  have ht1 : t ≠ 1 := by
    intro h
    have hinv : orderOf (1 : G) = 2 := by simpa only [h] using hctx.involution
    rw [orderOf_one] at hinv
    exact absurd hinv (by norm_num)
  let H : Subgroup G := centralizer ({z} : Set G)
  have htH : t ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr (hctx.central t htS)
  have hiso : ∀ h ∈ H, (h * t * h⁻¹) * t = t * (h * t * h⁻¹) → h * t * h⁻¹ = t :=
    sec10Z_isolated (S := S) (t := t) (z := z) hS hctx.central htS ht2 hz2 hsc
  have hZ : ∀ h ∈ H, h * t * h⁻¹ * t⁻¹ ∈ oddCoreIn H :=
    sec10_zStar (H := H) htH ht1 ht2 hiso
  have hdecz : ∀ h ∈ H, ∃ o ∈ oddCoreIn H, ∃ c ∈ H ⊓ centralizer ({t} : Set G), h = o * c :=
    sec10_zStar_decomp (H := H) htH ht2 hZ
  have hK1H : K1 ≤ H := hctx.pocket1.2.1.trans inf_le_right
  have hK2H : K2 ≤ H := hctx.pocket2.2.1.trans inf_le_right
  have hK1t : K1 ≤ centralizer ({t} : Set G) :=
    (hctx.pocket1.2.1.trans inf_le_left).trans hctx.component.le
  have hK2t : K2 ≤ centralizer ({t} : Set G) :=
    (hctx.pocket2.2.1.trans inf_le_left).trans hctx.component.le
  have hcomm12 : ∀ a ∈ K1, ∀ b ∈ K2, a * b = b * a :=
    fun a ha b hb => sec10Z_comm hP5 hpsp hctx a ha b hb
  have hN : oddCoreIn H ≤ H := CFSG.ClassicalInvolution.Balance.oddCoreIn_le H
  have hNn : ∀ h ∈ H, ∀ n ∈ oddCoreIn H, h * n * h⁻¹ ∈ oddCoreIn H :=
    fun h hh n hn => CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn (X := H) hh hn
  have hC : H ⊓ centralizer ({t} : Set G) ≤ H := inf_le_left
  have hK : K1 ⊔ K2 ≤ H ⊓ centralizer ({t} : Set G) :=
    sup_le (le_inf hK1H hK1t) (le_inf hK2H hK2t)
  have hKn : ∀ c ∈ H ⊓ centralizer ({t} : Set G), ∀ x ∈ K1 ⊔ K2, c * x * c⁻¹ ∈ K1 ⊔ K2 := by
    intro c hc x hx
    exact sec10Z_normalizes h36 hP5 hpsp hctx (Subgroup.mem_inf.mp hc).2
      (Subgroup.mem_inf.mp hc).1 x hx
  have hK1n : ∀ k ∈ K1 ⊔ K2, ∀ x ∈ K1, k * x * k⁻¹ ∈ K1 := by
    intro k hk x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm12 hk
    have hbxb : b * x * b⁻¹ = x := by
      have hcomm : b * x = x * b := (hcomm12 x hx b hb).symm
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have hconj : a * b * x * (a * b)⁻¹ = a * x * a⁻¹ := by
      rw [mul_inv_rev]
      calc a * b * x * (b⁻¹ * a⁻¹) = a * (b * x * b⁻¹) * a⁻¹ := by group
        _ = a * x * a⁻¹ := by rw [hbxb]
    rw [hconj]
    exact K1.mul_mem (K1.mul_mem ha hx) (K1.inv_mem ha)
  have hsub : ((K1 ⊔ oddCoreIn H).subgroupOf H).IsSubnormal :=
    sec10_isSubnormal_sup_odd (H := H) (C := H ⊓ centralizer ({t} : Set G))
      (K := K1 ⊔ K2) (K1 := K1) (N := oddCoreIn H) hN hNn hC hdecz hK hKn le_sup_left hK1n
  have hSL : IsSL23Mod ↥(K1 ⊔ oddCoreIn H) :=
    isSL23Mod_sup_odd (K1 := K1) (N := oddCoreIn H) hctx.pocket1.2.2.2
      (fun k hk n hn =>
        CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn (X := H) (hK1H hk) hn)
      (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn H)
  refine ⟨hctx.toSec10Z.pocket.1, K1 ⊔ oddCoreIn H, Subgroup.mem_sup_left hctx.pocket1.1,
    ?_, ?_, hSL⟩
  · exact le_inf le_top (sup_le hK1H hN)
  · exact isSubnormal_subgroupOf_of_eq (K := K1 ⊔ oddCoreIn H) (A := H)
      (B := ⊤ ⊓ centralizer ({z} : Set G)) (top_inf_eq H).symm hsub

end CFSG.OddStandard.SmallF3.Omega

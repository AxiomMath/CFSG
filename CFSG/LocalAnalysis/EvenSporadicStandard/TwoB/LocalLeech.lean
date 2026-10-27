module

public import CFSG.Assembly.Defs
public import CFSG.Monster.GMS.CoTwoCentral

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Co1.Module hiding co1Act
open scoped commutatorElement

namespace LeechSystem

variable {G : Type*} [Group G] {w : G} (L : LeechSystem w)

include L

theorem mem_commutator_centralizer_inf_one
    (hF : Co2McLFacts) {t : G} (htL : t ∈ L.typeSet 0) :
    t ∈ ⁅leechQ w ⊓ Subgroup.centralizer ({t} : Set G),
      Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({w} : Set G)⁆ := by
  have htQ : t ∈ leechQ w := htL.1
  have hu : L.vec t ∈ co1Orbit 0 := htL.2
  set N : Subgroup G := leechQ w ⊓ Subgroup.centralizer ({t} : Set G) with hN
  set D : Subgroup G :=
    Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({w} : Set G) with hD
  have hND : N ≤ D := fun x hx => ⟨hx.2, L.mem_centralizer hx.1⟩
  have htN : t ∈ N := ⟨htQ, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hperp : ∀ q ∈ N, bil₀ (L.vec q) (L.vec t) = 0 := fun q hq =>
    (L.comm_eq_one_iff hq.1 htQ).1
      (commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_singleton_iff.1 hq.2))
  have hTN : ⁅N, D⁆ ≤ N := by
    refine Subgroup.commutator_le.2 fun n hn d hd => ?_
    have hdw : d ∈ Subgroup.centralizer ({w} : Set G) := hd.2
    have h1 : d * n⁻¹ * d⁻¹ ∈ leechQ w := L.conj_mem' hdw (inv_mem hn.1)
    have h2 : n * (d * n⁻¹ * d⁻¹) ∈ leechQ w := mul_mem hn.1 h1
    have h3 : n * (d * n⁻¹ * d⁻¹) ∈ Subgroup.centralizer ({t} : Set G) :=
      mul_mem hn.2 (mul_mem (mul_mem hd.1 (inv_mem hn.2)) (inv_mem hd.1))
    have : ⁅n, d⁆ = n * (d * n⁻¹ * d⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [this]
    exact ⟨h2, h3⟩
  have hTnorm : ∀ c ∈ D, ∀ p ∈ ⁅N, D⁆, c * p * c⁻¹ ∈ ⁅N, D⁆ := by
    intro c hc p hp
    have h1 : ⁅c, p⁆ ∈ ⁅N, D⁆ := by
      have h5 : ⁅c, p⁆ = (⁅p, c⁆)⁻¹ := (commutatorElement_inv p c).symm
      rw [h5]
      exact inv_mem (Subgroup.commutator_mem_commutator (hTN hp) hc)
    have h2 : c * p * c⁻¹ = ⁅c, p⁆ * p := by
      rw [commutatorElement_def]
      group
    rw [h2]
    exact mul_mem h1 hp
  have himg := L.image_centralizer_inf_one htQ (L.vec_ne_zero_of_mem_typeSet htL)
  have hmain := hF.comm_span_co2 _ hu (L.vecSpace ⁅N, D⁆)
    (by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := L.mem_vecSpace.1 hx
      exact hperp p (hTN (Subgroup.mem_inf.1 hp).2))
    (by
      intro A hA x hx
      obtain ⟨c, hc, rfl⟩ := L.mem_image.1 (himg.symm ▸ hA)
      obtain ⟨p, hp, rfl⟩ := L.mem_vecSpace.1 hx
      refine L.mem_vecSpace.2 ⟨(c : G) * p * (c : G)⁻¹,
        ⟨L.conj_mem c hp.1, hTnorm _ hc _ (Subgroup.mem_inf.1 hp).2⟩, ?_⟩
      exact L.vec_conj c p hp.1)
    (by
      intro A hA y hy
      obtain ⟨c, hc, rfl⟩ := L.mem_image.1 (himg.symm ▸ hA)
      obtain ⟨q, hq, rfl⟩ := L.vec_surj y
      have hqN : q ∈ N := by
        refine ⟨hq, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        exact commutatorElement_eq_one_iff_mul_comm.1 ((L.comm_eq_one_iff hq htQ).2 hy)
      obtain ⟨hcQ, hcv⟩ := L.vec_commutator c.2 hq
      have h5 : ⁅(c : G), q⁆ = (⁅q, (c : G)⁆)⁻¹ := (commutatorElement_inv q (c : G)).symm
      have hmem : ⁅(c : G), q⁆ ∈ ⁅N, D⁆ := by
        rw [h5]
        exact inv_mem (Subgroup.commutator_mem_commutator hqN hc)
      exact L.mem_vecSpace.2 ⟨⁅(c : G), q⁆, Subgroup.mem_inf.2 ⟨hcQ, hmem⟩, hcv⟩)
    (L.vec t) (hperp t htN)
  obtain ⟨p, hp, hpv⟩ := L.mem_vecSpace.1 hmain
  have hwT : w ∈ ⁅N, D⁆ := by
    obtain ⟨y₁, y₂, h1, h2, h3⟩ := hF.nondeg_co2 _ hu
    obtain ⟨n₁, hn₁, rfl⟩ := L.vec_surj y₁
    obtain ⟨n₂, hn₂, rfl⟩ := L.vec_surj y₂
    have hn₁N : n₁ ∈ N := ⟨hn₁, Subgroup.mem_centralizer_singleton_iff.2
      (commutatorElement_eq_one_iff_mul_comm.1 ((L.comm_eq_one_iff hn₁ htQ).2 h1))⟩
    have hn₂N : n₂ ∈ N := ⟨hn₂, Subgroup.mem_centralizer_singleton_iff.2
      (commutatorElement_eq_one_iff_mul_comm.1 ((L.comm_eq_one_iff hn₂ htQ).2 h2))⟩
    rw [← (L.comm_eq_z_iff hn₁ hn₂).2 h3]
    exact Subgroup.commutator_mem_commutator hn₁N (hND hn₂N)
  have hp2 : p ∈ ⁅N, D⁆ := (Subgroup.mem_inf.1 hp).2
  rcases L.eq_or_eq_mul_z (Subgroup.mem_inf.1 hp).1 htQ hpv with h | h
  · rw [← h]
    exact hp2
  · have : t = p * w⁻¹ := by
      rw [h]
      have hww : w * w = 1 := L.z_mul_self
      have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
      rw [hwi, mul_assoc, hww, mul_one]
    rw [this]
    exact mul_mem hp2 (inv_mem hwT)

end LeechSystem

end CFSG.Monster.GMS

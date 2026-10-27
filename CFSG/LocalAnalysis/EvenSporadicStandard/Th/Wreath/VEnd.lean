module

public import CFSG.GroupTheory.AbelianSubgroupEnd
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SecondLayerVMod

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd CFSG.GroupTheory

variable {G : Type} [Group G] {A Aa D : Subgroup G} {t : G}

abbrev VSub (hD : DHyp A Aa t D) : Type :=
  AbelianSub (omega1 D hD.comm) fun x hx y hy => hD.comm x hx.1 y hy.1

noncomputable abbrev vConj (hD : DHyp A Aa t D) (n : G) : AddMonoid.End (VSub hD) :=
  AbelianSub.conj (omega1 D hD.comm) (fun x hx y hy => hD.comm x hx.1 y hy.1) n

theorem VSub.add_self (hD : DHyp A Aa t D) (f : AddMonoid.End (VSub hD)) : f + f = 0 :=
  AbelianSub.add_self_eq_zero (fun v hv => by rw [← pow_two]; exact hv.2) f

theorem normalizer_D_le_normalizer_omega1 (hD : DHyp A Aa t D) :
    normalizer (D : Set G) ≤ normalizer (omega1 D hD.comm : Set G) := by
  intro n hn
  refine mem_normalizer_iff.2 fun v => ⟨fun hv => ⟨(mem_normalizer_iff.1 hn v).1 hv.1, ?_⟩,
    fun hv => ⟨(mem_normalizer_iff.1 hn v).2 hv.1, ?_⟩⟩
  · rw [conj_pow, hv.2, mul_one, mul_inv_cancel]
  · have h := hv.2
    rw [conj_pow] at h
    simpa using h

theorem val_vConj_apply (hD : DHyp A Aa t D) {n : G}
    (hn : n ∈ normalizer (omega1 D hD.comm : Set G)) (x : VSub hD) :
    (vConj hD n x).val = n * x.val * n⁻¹ :=
  AbelianSub.val_conj_apply (AbelianSub.conj_mem_of_mem_normalizer hn) x

theorem vConj_mul (hD : DHyp A Aa t D) {n m : G}
    (hn : n ∈ normalizer (omega1 D hD.comm : Set G))
    (hm : m ∈ normalizer (omega1 D hD.comm : Set G)) :
    vConj hD (n * m) = vConj hD n * vConj hD m :=
  AbelianSub.conj_mul (AbelianSub.conj_mem_of_mem_normalizer hn)
    (AbelianSub.conj_mem_of_mem_normalizer hm)

theorem vConj_one (hD : DHyp A Aa t D) : vConj hD 1 = 1 :=
  AbelianSub.conj_one

theorem vConj_inv_mul (hD : DHyp A Aa t D) {n : G}
    (hn : n ∈ normalizer (omega1 D hD.comm : Set G)) :
    vConj hD n⁻¹ * vConj hD n = 1 :=
  AbelianSub.conj_inv_mul hn

theorem vConj_mul_inv (hD : DHyp A Aa t D) {n : G}
    (hn : n ∈ normalizer (omega1 D hD.comm : Set G)) :
    vConj hD n * vConj hD n⁻¹ = 1 :=
  AbelianSub.conj_mul_inv hn

end CFSG.EvenSporadicStandard.ThStd

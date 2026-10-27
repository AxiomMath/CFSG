module

public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLDescentCentral

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section QuotConj

variable {X : Type*} [Group X] (K : Subgroup X) [K.Normal]

@[expose] noncomputable def quotConj (t : X) : MulAut (K ⧸ center K) :=
  QuotientGroup.congr (center K) (center K) (MulAut.conjNormal t) (Subgroup.map_center_eq _)

variable {K}

@[simp] theorem quotConj_mk (t : X) (k : K) :
    quotConj K t (QuotientGroup.mk k) = QuotientGroup.mk (MulAut.conjNormal t k) := by
  simp [quotConj]

theorem quotConj_mul_self {t : X} (ht : t * t = 1) : quotConj K t * quotConj K t = 1 := by
  ext x
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
  rw [MulAut.mul_apply, quotConj_mk, quotConj_mk, MulAut.one_apply]
  have hk : MulAut.conjNormal t (MulAut.conjNormal t k) = k := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply]
    rw [inv_eq_of_mul_eq_one_right ht]
    calc t * (t * (k : X) * t) * t = (t * t) * (k : X) * (t * t) := by group
      _ = (k : X) := by rw [ht]; simp
  rw [hk]

theorem mk_mem_fixedSubgroup_quotConj_iff (t : X) (k : K) :
    (QuotientGroup.mk k : K ⧸ center K) ∈ fixedSubgroup (quotConj K t) ↔
      (MulAut.conjNormal t k)⁻¹ * k ∈ center K := by
  change quotConj K t (QuotientGroup.mk k) = QuotientGroup.mk k ↔
    (MulAut.conjNormal t k)⁻¹ * k ∈ center K
  rw [quotConj_mk]
  exact QuotientGroup.eq

theorem le_centralizer_of_quotConj_eq_one (hK : ⁅K, K⁆ = K) {t : X} (h : quotConj K t = 1) :
    K ≤ centralizer ({t} : Set X) := by
  refine le_centralizer_of_perfect hK (QuotientGroup.mk' (center K)) (by rw [QuotientGroup.ker_mk'])
    ?_
  intro k
  have hx := DFunLike.congr_fun h (QuotientGroup.mk k)
  rw [quotConj_mk, MulAut.one_apply] at hx
  simpa using hx

theorem map_le_fixedSubgroup_quotConj {t : X} {A : Subgroup X} (hAK : A ≤ K)
    (hAc : A ≤ centralizer ({t} : Set X)) :
    (A.subgroupOf K).map (QuotientGroup.mk' (center K)) ≤ fixedSubgroup (quotConj K t) := by
  rintro - ⟨a, ha, rfl⟩
  change (QuotientGroup.mk a : K ⧸ center K) ∈ fixedSubgroup (quotConj K t)
  rw [mk_mem_fixedSubgroup_quotConj_iff]
  have ha' : (a : X) * t = t * (a : X) :=
    Subgroup.mem_centralizer_singleton_iff.mp (hAc (Subgroup.mem_subgroupOf.mp ha))
  have hconj : MulAut.conjNormal t a = a := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, ← ha']
    simp
  rw [hconj]
  simp

private lemma conj_mul_inv_eq_of_central {G : Type*} [Group G] {p q s c : G}
    (hq : q = p * s) (hs : s * c * s⁻¹ = c) : q * c * q⁻¹ = p * c * p⁻¹ := by
  rw [hq]
  calc p * s * c * (p * s)⁻¹
      = p * (s * c * s⁻¹) * p⁻¹ := by rw [mul_inv_rev]; group
    _ = p * c * p⁻¹ := by rw [hs]

theorem conj_mem_map_centralizer {t : X} {f m : K ⧸ center K}
    (hf : f ∈ fixedSubgroup (quotConj K t))
    (hm : m ∈ ((K ⊓ centralizer ({t} : Set X)).subgroupOf K).map
      (QuotientGroup.mk' (center K))) :
    f * m * f⁻¹ ∈ ((K ⊓ centralizer ({t} : Set X)).subgroupOf K).map
      (QuotientGroup.mk' (center K)) := by
  obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective f
  rw [Subgroup.mem_map] at hm ⊢
  obtain ⟨c, hc, rfl⟩ := hm
  have hz : (MulAut.conjNormal t p)⁻¹ * p ∈ Subgroup.center K :=
    (mk_mem_fixedSubgroup_quotConj_iff t p).mp hf
  have hthis : MulAut.conjNormal t p * ((MulAut.conjNormal t p)⁻¹ * p) = p := by
    apply Subtype.ext
    change (MulAut.conjNormal t p : X) * ((MulAut.conjNormal t p : X)⁻¹ * (p : X)) = (p : X)
    group
  have hcC : (c : X) ∈ Subgroup.centralizer ({t} : Set X) :=
    (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hc)).2
  have hconj_c : MulAut.conjNormal t c = c := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, ← Subgroup.mem_centralizer_singleton_iff.mp hcC]
    simp
  have hSc : ((MulAut.conjNormal t p)⁻¹ * p)⁻¹ * c * ((MulAut.conjNormal t p)⁻¹ * p) = c := by
    rw [← Subgroup.mem_center_iff.mp ((Subgroup.center K).inv_mem hz) c]
    rw [mul_assoc, inv_mul_cancel, mul_one]
  have hfix : MulAut.conjNormal t (p * c * p⁻¹) = p * c * p⁻¹ := by
    rw [map_mul, map_mul, map_inv, hconj_c]
    exact conj_mul_inv_eq_of_central
      ((eq_mul_inv_iff_mul_eq).mpr hthis) (by simpa using hSc)
  refine ⟨p * c * p⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    refine ⟨K.mul_mem (K.mul_mem p.2 c.2) (K.inv_mem p.2), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hx : t * ((p * c * p⁻¹ : K) : X) * t⁻¹ = ((p * c * p⁻¹ : K) : X) := by
      have h := congrArg Subtype.val hfix
      rw [MulAut.conjNormal_apply] at h
      exact h
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm
  · simp

end QuotConj

theorem isSubnormal_subgroupOf_of_chain {G : Type*} [Group G] {N M F : Subgroup G}
    (hNM : N ≤ M) (hMF : M ≤ F) (hN : ∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N)
    (hM : ∀ f ∈ F, ∀ m ∈ M, f * m * f⁻¹ ∈ M) : (N.subgroupOf F).IsSubnormal := by
  have hNMF : N.subgroupOf F ≤ M.subgroupOf F := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hNM hx
  have hMnorm : (M.subgroupOf F).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hMF]
    exact Subgroup.le_normalizer_iff.mpr (fun f hf m hm => hM f hf m hm)
  have hNnorm : ((N.subgroupOf F).subgroupOf (M.subgroupOf F)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNMF, Subgroup.le_normalizer_iff]
    intro m hm n hn
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hN (m : G) (Subgroup.mem_subgroupOf.mp hm) (n : G) (Subgroup.mem_subgroupOf.mp hn)
  exact Subgroup.IsSubnormal.step _ _ hNMF hMnorm.isSubnormal hNnorm

variable {X : Type*} [Group X] {K : Subgroup X} [K.Normal]

theorem isSubnormal_map_subgroupOf_fixedSubgroup {t : X} {A : Subgroup X} (hAK : A ≤ K)
    (hAc : A ≤ centralizer ({t} : Set X))
    (hAn : K ⊓ centralizer ({t} : Set X) ≤ normalizer (A : Set X)) :
    (((A.subgroupOf K).map (QuotientGroup.mk' (center K))).subgroupOf
      (fixedSubgroup (quotConj K t))).IsSubnormal := by
  refine isSubnormal_subgroupOf_of_chain (G := K ⧸ center K)
    (N := (A.subgroupOf K).map (QuotientGroup.mk' (center K)))
    (M := ((K ⊓ centralizer ({t} : Set X)).subgroupOf K).map
      (QuotientGroup.mk' (center K)))
    (F := fixedSubgroup (quotConj K t)) ?_ ?_ ?_ ?_
  · exact Subgroup.map_mono (Subgroup.subgroupOf_mono K (le_inf hAK hAc))
  · exact map_le_fixedSubgroup_quotConj inf_le_left inf_le_right
  · intro m hm n hn
    rw [Subgroup.mem_map] at hm hn ⊢
    obtain ⟨c, hc, rfl⟩ := hm
    obtain ⟨a, ha, rfl⟩ := hn
    refine ⟨c * a * c⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      have hcn : (c : X) ∈ normalizer (A : Set X) :=
        hAn (Subgroup.mem_subgroupOf.mp hc)
      have hA : (a : X) ∈ A := Subgroup.mem_subgroupOf.mp ha
      have hconj : (c : X) * (a : X) * (c : X)⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp hcn) (a : X) |>.mp hA
      simpa using hconj
    · simp
  · intro f hf m hm
    exact conj_mem_map_centralizer hf hm

end CFSG.OddStandard.AltStdSec.SwapPartner

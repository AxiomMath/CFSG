module

public import CFSG.GH74.GLS.Classes
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.PerfectAutomorphisms
  (onCenterQuotient onCenterQuotient_apply_mk onCenterQuotient_eq_one_imp centerQuotientHom)

theorem nfdc_isSubnormal_subgroupOf {G : Type*} [Group G] {A B C : Subgroup G} (hAB : A ≤ B)
    (hBC : B ≤ C) (hA : ∀ a q, a ∈ A → q ∈ B → q * a * q⁻¹ ∈ A)
    (hB : ∀ q c, q ∈ B → c ∈ C → c * q * c⁻¹ ∈ B) : (A.subgroupOf C).IsSubnormal := by
  have hBn : (B.subgroupOf C).Normal := (Subgroup.normal_subgroupOf_iff hBC).2 hB
  have hle : A.subgroupOf C ≤ B.subgroupOf C := fun x hx => hAB hx
  refine Subgroup.IsSubnormal.step (A.subgroupOf C) (B.subgroupOf C) hle hBn.isSubnormal ?_
  refine (Subgroup.normal_subgroupOf_iff hle).2 fun h k hh hk => ?_
  exact hA _ _ (Subgroup.mem_subgroupOf.1 hh) (Subgroup.mem_subgroupOf.1 hk)

section Aut

variable {X : Type*} [Group X] {K : Subgroup X}

theorem nfdc_mem_fixedSubgroup {G : Type*} [Group G] {σ : MulAut G} {x : G} :
    x ∈ fixedSubgroup σ ↔ σ x = x := Iff.rfl

theorem nfdc_conj_mem_fixed (α : MulAut ↥K) {y : ↥K} (hy : α y = y) {x : ↥K}
    (hx : onCenterQuotient α (QuotientGroup.mk' (center ↥K) x) =
      QuotientGroup.mk' (center ↥K) x) : α (x * y * x⁻¹) = x * y * x⁻¹ := by
  rw [onCenterQuotient_apply_mk] at hx
  have hw : (α x)⁻¹ * x ∈ center ↥K := QuotientGroup.eq.1 hx
  set w := (α x)⁻¹ * x with hwdef
  have hαx : α x = x * w⁻¹ := by rw [hwdef]; group
  have hcomm : y * w⁻¹ = w⁻¹ * y := Subgroup.mem_center_iff.1 (inv_mem hw) y
  calc α (x * y * x⁻¹) = α x * α y * (α x)⁻¹ := by simp only [map_mul, map_inv]
    _ = x * w⁻¹ * y * (x * w⁻¹)⁻¹ := by rw [hαx, hy]
    _ = x * (w⁻¹ * y * w) * x⁻¹ := by group
    _ = x * y * x⁻¹ := by rw [← hcomm]; group

theorem nfdc_map_fixed_le (α : MulAut ↥K) :
    (fixedSubgroup α).map (QuotientGroup.mk' (center ↥K)) ≤
      fixedSubgroup (onCenterQuotient α) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [nfdc_mem_fixedSubgroup, onCenterQuotient_apply_mk, nfdc_mem_fixedSubgroup.1 hy]

theorem nfdc_conj_mem_map_fixed (α : MulAut ↥K) {q c : ↥K ⧸ center ↥K}
    (hq : q ∈ (fixedSubgroup α).map (QuotientGroup.mk' (center ↥K)))
    (hc : c ∈ fixedSubgroup (onCenterQuotient α)) :
    c * q * c⁻¹ ∈ (fixedSubgroup α).map (QuotientGroup.mk' (center ↥K)) := by
  obtain ⟨y, hy, rfl⟩ := hq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center ↥K) c
  exact ⟨x * y * x⁻¹, nfdc_mem_fixedSubgroup.2
    (nfdc_conj_mem_fixed α (nfdc_mem_fixedSubgroup.1 hy) (nfdc_mem_fixedSubgroup.1 hc)),
    by simp⟩

theorem nfdc_fixed_iff (α : MulAut ↥K) {t : X}
    (hα : ∀ x : ↥K, ((α x : ↥K) : X) = t * x * t⁻¹) (y : ↥K) :
    α y = y ↔ (y : X) ∈ centralizer ({t} : Set X) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.1 hg]
    have h' := congrArg Subtype.val h
    rw [hα] at h'
    calc t * (y : X) = (t * y * t⁻¹) * t := by group
      _ = y * t := by rw [h']
  · intro h
    apply Subtype.ext
    rw [hα]
    have h' := (Subgroup.mem_centralizer_iff.1 h) t (Set.mem_singleton t)
    calc t * (y : X) * t⁻¹ = (y * t) * t⁻¹ := by rw [h']
      _ = y := by group

end Aut

section Cover

variable {X : Type*} [Group X] {K B : Subgroup X}

@[expose] noncomputable def nfdcMap (hBK : B ≤ K) : ↥B →* ↥K ⧸ center ↥K :=
  (QuotientGroup.mk' (center ↥K)).comp (Subgroup.inclusion hBK)

theorem nfdcMap_apply (hBK : B ≤ K) (b : ↥B) :
    nfdcMap hBK b = QuotientGroup.mk' (center ↥K) ⟨b, hBK b.2⟩ := rfl

theorem nfdcMap_ker (hBK : B ≤ K)
    (hZ : ∀ z ∈ B, (∀ b ∈ B, z * b = b * z) → ∀ x ∈ K, z * x = x * z) :
    (nfdcMap hBK).ker = center ↥B := by
  ext b
  rw [MonoidHom.mem_ker, nfdcMap_apply]
  have h1 : QuotientGroup.mk' (center ↥K) (⟨b, hBK b.2⟩ : ↥K) = 1 ↔
      (⟨b, hBK b.2⟩ : ↥K) ∈ center ↥K := QuotientGroup.eq_one_iff _
  rw [h1, Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h b'
    have h' := congrArg Subtype.val (h ⟨b', hBK b'.2⟩)
    exact Subtype.ext h'
  · intro h x
    have hb : ∀ b' ∈ B, (b : X) * b' = b' * b := fun b' hb' =>
      congrArg Subtype.val (h ⟨b', hb'⟩).symm
    exact Subtype.ext (hZ b b.2 hb x x.2).symm

theorem nfdcMap_range_quasisimple (hBK : B ≤ K)
    (hZ : ∀ z ∈ B, (∀ b ∈ B, z * b = b * z) → ∀ x ∈ K, z * x = x * z)
    (hBq : CFSG.IsQuasisimple ↥B) : CFSG.IsQuasisimple ↥(nfdcMap hBK).range :=
  CFSG.LocalCores.isQuasisimple_of_surjective hBq (nfdcMap hBK).rangeRestrict
    (nfdcMap hBK).rangeRestrict_surjective
    (by rw [MonoidHom.ker_rangeRestrict, nfdcMap_ker hBK hZ])

noncomputable def nfdcRangeEquiv (hBK : B ≤ K)
    (hZ : ∀ z ∈ B, (∀ b ∈ B, z * b = b * z) → ∀ x ∈ K, z * x = x * z) :
    ↥(nfdcMap hBK).range ≃* ↥B ⧸ center ↥B :=
  (QuotientGroup.quotientKerEquivRange (nfdcMap hBK)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (nfdcMap_ker hBK hZ))

theorem nfdc_range_conj_mem (hBK : B ≤ K) {t : X}
    (hBn : ∀ b y : X, b ∈ B → y ∈ K → y ∈ centralizer ({t} : Set X) → y * b * y⁻¹ ∈ B)
    {y : ↥K} (hy : (y : X) ∈ centralizer ({t} : Set X)) {a : ↥K ⧸ center ↥K}
    (ha : a ∈ (nfdcMap hBK).range) :
    QuotientGroup.mk' (center ↥K) y * a * (QuotientGroup.mk' (center ↥K) y)⁻¹ ∈
      (nfdcMap hBK).range := by
  obtain ⟨b, rfl⟩ := ha
  refine ⟨⟨(y : X) * b * (y : X)⁻¹, hBn b y b.2 y.2 hy⟩, ?_⟩
  rw [nfdcMap_apply, nfdcMap_apply, ← map_inv, ← map_mul, ← map_mul]
  rfl

end Cover

theorem nfdc_reduce {X : Type} [Group X] [Finite X] {K B : Subgroup X} {t : X} {k : ℕ}
    (hk : 5 ≤ k) (hKq : CFSG.IsQuasisimple ↥K) (ht : orderOf t = 2)
    (htK : t ∈ normalizer (K : Set X)) (hBK : B ≤ K) (hBt : B ≤ centralizer ({t} : Set X))
    (hB : CFSG.GH74.GLS.IsDoubleCoverOfAlt ↥B k)
    (hZ : ∀ z ∈ B, (∀ b ∈ B, z * b = b * z) → ∀ x ∈ K, z * x = x * z)
    (hBn : (B.subgroupOf (K ⊓ centralizer ({t} : Set X))).Normal) :
    Nonempty (↥K ⧸ center ↥K ≃* alternatingGroup (Fin k)) ∨
      ∃ σ : MulAut (↥K ⧸ center ↥K), orderOf σ = 2 ∧ ∃ D : Subgroup ↥(fixedSubgroup σ),
        IsComponent D ∧ Nonempty (↥D ≃* alternatingGroup (Fin k)) := by
  have _ := hk
  obtain ⟨hBq, -, ⟨eB⟩⟩ := hB
  haveI hperf : Group.IsPerfect ↥K := hKq.1
  haveI hsimple : IsSimpleGroup (↥K ⧸ center ↥K) := hKq.2.1
  obtain ⟨α, hα⟩ : ∃ α : MulAut ↥K, ∀ x : ↥K, ((α x : ↥K) : X) = t * x * t⁻¹ :=
    ⟨K.normalizerMonoidHom ⟨t, htK⟩, fun x =>
      Subgroup.normalizerMonoidHom_apply_apply_coe K ⟨t, htK⟩ x⟩
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hαα : α * α = 1 := by
    ext x
    change ((α (α x) : ↥K) : X) = (x : X)
    rw [hα, hα]
    calc t * (t * (x : X) * t⁻¹) * t⁻¹ = (t * t) * (x : X) * (t * t)⁻¹ := by group
      _ = x := by rw [ht2]; group
  have hττ : onCenterQuotient α * onCenterQuotient α = 1 := by
    have h := map_mul (centerQuotientHom ↥K) α α
    rw [hαα, map_one] at h
    exact h.symm
  have hBn' : ∀ b y : X, b ∈ B → y ∈ K → y ∈ centralizer ({t} : Set X) → y * b * y⁻¹ ∈ B :=
    fun b y hb hyK hyC =>
      (Subgroup.normal_subgroupOf_iff (le_inf hBK hBt)).1 hBn b y hb ⟨hyK, hyC⟩
  have hq : CFSG.IsQuasisimple ↥(nfdcMap hBK).range := nfdcMap_range_quasisimple hBK hZ hBq
  let eR : ↥(nfdcMap hBK).range ≃* alternatingGroup (Fin k) := (nfdcRangeEquiv hBK hZ).trans eB
  by_cases hτ1 : onCenterQuotient α = 1
  ·
    left
    have hα1 : α = 1 := onCenterQuotient_eq_one_imp α hτ1
    have hfix : ∀ y : ↥K, (y : X) ∈ centralizer ({t} : Set X) := fun y =>
      (nfdc_fixed_iff α hα y).1 (by rw [hα1]; rfl)
    haveI hnormal : (nfdcMap hBK).range.Normal :=
      ⟨fun a ha c => by
        obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center ↥K) c
        exact nfdc_range_conj_mem hBK hBn' (hfix y) ha⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (nfdcMap hBK).range with h | h
    · exfalso
      haveI := CFSG.LocalCores.isQuasisimple_nontrivial hq
      exact (Subgroup.nontrivial_iff_ne_bot _).1 this h
    · exact ⟨(Subgroup.topEquiv (G := ↥K ⧸ center ↥K)).symm.trans
        ((MulEquiv.subgroupCongr h.symm).trans eR)⟩
  ·
    right
    have hτo : orderOf (onCenterQuotient α) = 2 :=
      orderOf_eq_prime (by rw [sq]; exact hττ) hτ1
    have hQC : (fixedSubgroup α).map (QuotientGroup.mk' (center ↥K)) ≤
        fixedSubgroup (onCenterQuotient α) := nfdc_map_fixed_le α
    have hBQ : (nfdcMap hBK).range ≤ (fixedSubgroup α).map (QuotientGroup.mk' (center ↥K)) := by
      rintro _ ⟨b, rfl⟩
      exact ⟨⟨b, hBK b.2⟩, nfdc_mem_fixedSubgroup.2 ((nfdc_fixed_iff α hα _).2 (hBt b.2)), rfl⟩
    have hA : ∀ a q, a ∈ (nfdcMap hBK).range →
        q ∈ (fixedSubgroup α).map (QuotientGroup.mk' (center ↥K)) →
        q * a * q⁻¹ ∈ (nfdcMap hBK).range := by
      rintro a _ ha ⟨y, hy, rfl⟩
      exact nfdc_range_conj_mem hBK hBn' ((nfdc_fixed_iff α hα y).1 hy) ha
    have hle : (nfdcMap hBK).range ≤ fixedSubgroup (onCenterQuotient α) := hBQ.trans hQC
    refine ⟨onCenterQuotient α, hτo,
      (nfdcMap hBK).range.subgroupOf (fixedSubgroup (onCenterQuotient α)), ⟨?_, ?_⟩,
      ⟨(Subgroup.subgroupOfEquivOfLe hle).trans eR⟩⟩
    · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm hq
    · exact nfdc_isSubnormal_subgroupOf hBQ hQC hA fun q c hq' hc =>
        nfdc_conj_mem_map_fixed α hq' hc

end CFSG.ComponentClassification.CatFC

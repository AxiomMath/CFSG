module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitHypothesisISupport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5.SevenFour

open AschbacherToolkit CFSG.ABGLocalTools

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem exists_isSylowOf_le {p : ℕ} [Fact p.Prime] {Q K : Subgroup G} (hQK : Q ≤ K)
    (hQ : IsPGroup p Q) : ∃ P : Subgroup G, IsSylowOf p P K ∧ Q ≤ P := by
  have hQ' : IsPGroup p (Q.subgroupOf K) := hQ.comap_subtype
  obtain ⟨S, hS⟩ := hQ'.exists_le_sylow
  refine ⟨(S : Subgroup K).map K.subtype, ⟨S, rfl⟩, ?_⟩
  intro x hx
  exact ⟨⟨x, hQK hx⟩, hS (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

theorem IsSylowOf.exists_conj {p : ℕ} [Fact p.Prime] {P P' K : Subgroup G}
    (h : IsSylowOf p P K) (h' : IsSylowOf p P' K) :
    ∃ k ∈ K, P' = P.map (MulAut.conj k).toMonoidHom := by
  obtain ⟨S, rfl⟩ := h
  obtain ⟨S', rfl⟩ := h'
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K S S'
  refine ⟨k, k.2, ?_⟩
  rw [← hk]
  ext x
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy
    refine ⟨K.subtype ((MulAut.conj k)⁻¹ • y), ⟨_, hy, rfl⟩, ?_⟩
    simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨MulAut.conj k s, ?_, ?_⟩
    · rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hs
    · simp [MulAut.conj_apply]

theorem exists_mul_fixed_of_lt {P : Subgroup G} (hP : IsPGroup 2 P) {t : G} (ht : t * t = 1)
    (htP : t ∈ Subgroup.normalizer (P : Set G))
    (hlt : P ⊓ Subgroup.centralizer ({t} : Set G) < P) :
    ∃ w ∈ P, w ∉ Subgroup.centralizer ({t} : Set G) ∧
      w⁻¹ * (t * w * t⁻¹) ∈ P ⊓ Subgroup.centralizer ({t} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := P ⊓ Subgroup.centralizer ({t} : Set G) with hR
  set N := P ⊓ Subgroup.normalizer (R : Set G) with hN
  have hRN : R ≤ N := le_inf inf_le_left Subgroup.le_normalizer
  have hnil : Group.IsNilpotent P := hP.isNilpotent
  have hRP : R.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hlt.ne
    apply le_antisymm inf_le_left
    intro x hx
    have : (⟨x, hx⟩ : P) ∈ R.subgroupOf P := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  obtain ⟨y, hyN, hyR⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent _ hRP)
  have hyN' : (y : G) ∈ N := by
    refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hxP : x ∈ R → x ∈ P := fun hx => hx.1
    constructor
    · intro hx
      have hx' : (⟨x, hxP hx⟩ : P) ∈ R.subgroupOf P := Subgroup.mem_subgroupOf.mpr hx
      exact Subgroup.mem_subgroupOf.mp ((Subgroup.mem_normalizer_iff.mp hyN _).mp hx')
    · intro hx
      have hxP' : x ∈ P := by
        have h1 := P.mul_mem (P.mul_mem (P.inv_mem y.2) hx.1) y.2
        simpa [mul_assoc] using h1
      have hx' : y * ⟨x, hxP'⟩ * y⁻¹ ∈ R.subgroupOf P := Subgroup.mem_subgroupOf.mpr hx
      exact Subgroup.mem_subgroupOf.mp ((Subgroup.mem_normalizer_iff.mp hyN _).mpr hx')
  have hyRN : (y : G) ∉ R := fun h => hyR (Subgroup.mem_subgroupOf.mpr h)
  have htR : t ∈ Subgroup.normalizer (R : Set G) := by
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_singleton_iff.mp hx.2)
  have htN : N.map (MulAut.conj t).toMonoidHom = N := by
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mp ?_
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨hxP, hxR⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp htP x).mp hxP, ?_⟩
      have := Subgroup.mul_mem _ (Subgroup.mul_mem _ htR hxR) (Subgroup.inv_mem _ htR)
      exact this
    · intro hx
      obtain ⟨hxP, hxR⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp htP x).mpr hxP, ?_⟩
      have h1 := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ htR) hxR) htR
      simpa [mul_assoc] using h1
  have : (R.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRN).mpr inf_le_right
  set γ := restrictAut (MulAut.conj t) N htN
  have hγ2 : γ ^ 2 = 1 := by
    apply restrictAut_sq
    ext x
    simp only [sq, MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply]
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht
    rw [htinv, ← mul_assoc, ← mul_assoc, ht, one_mul, mul_assoc, ht, mul_one]
  have hγR : (R.subgroupOf N).map (γ : N →* N) = R.subgroupOf N := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hx' : (x : G) ∈ R := Subgroup.mem_subgroupOf.mp hx
      refine Subgroup.mem_subgroupOf.mpr ?_
      change t * (x : G) * t⁻¹ ∈ R
      have hxt := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx').2
      rw [← hxt, mul_inv_cancel_right]
      exact hx'
    · intro x hx
      refine ⟨x, hx, Subtype.ext ?_⟩
      have hx' : (x : G) ∈ R := Subgroup.mem_subgroupOf.mp hx
      change t * (x : G) * t⁻¹ = x
      have hxt := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx').2
      rw [← hxt, mul_inv_cancel_right]
  set δ := QuotientGroup.congr (R.subgroupOf N) (R.subgroupOf N) γ hγR
  have hδ2 : δ ^ 2 = 1 := quotient_congr_sq γ hγ2 _ hγR
  have hQ2 : IsPGroup 2 (N ⧸ R.subgroupOf N) :=
    ((hP.to_le inf_le_left).to_quotient (R.subgroupOf N))
  have hQnt : Nontrivial (N ⧸ R.subgroupOf N) := by
    refine ⟨⟨QuotientGroup.mk ⟨y, hyN'⟩, 1, ?_⟩⟩
    rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hyRN
  obtain ⟨q, hq1, hδq⟩ := exists_fixed_ne_one hQ2 δ hδ2
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
  have hwR : (w : G) ∉ R := by
    intro h
    exact hq1 ((QuotientGroup.eq_one_iff w).mpr (Subgroup.mem_subgroupOf.mpr h))
  have hδw : (QuotientGroup.mk (γ w) : N ⧸ R.subgroupOf N) = QuotientGroup.mk w := hδq
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hδw
  have hwP : (w : G) ∈ P := (Subgroup.mem_inf.mp w.2).1
  refine ⟨w, hwP, fun h => hwR (Subgroup.mem_inf.mpr ⟨hwP, h⟩), ?_⟩
  have h1 := R.inv_mem hδw
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv] at h1
  exact h1

end CFSG.ComponentClassification.AschbacherTheorem5.SevenFour

module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeEmbedding
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6A312Over
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinGen

public section

namespace CFSG.QuasithinUnique.Unc25G2

namespace A312Sub

open CFSG.Open CFSG.Quasithin
open CFSG.QuasithinUnique.Vol2Native

section Quasisimple

theorem pCore_two_le_center_of_quasisimple {Q : Type*} [Group Q] [Finite Q]
    (hQ : CFSG.IsQuasisimple Q) : CFSG.pCore 2 Q ≤ Subgroup.center Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ (CFSG.pCore_normal) with h | h
  · exfalso
    have h2 : IsPGroup 2 Q := by
      have := CFSG.pCore_isPGroup (p := 2) (G := Q)
      rw [h] at this
      exact IsPGroup.of_equiv this Subgroup.topEquiv
    have : Group.IsNilpotent Q := h2.isNilpotent
    have hs : Group.IsSolvable Q := inferInstance
    obtain ⟨a, b, hab⟩ := hQ.2.2
    have : Nontrivial (Q ⧸ Subgroup.center Q) := ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
    have hne : Nontrivial Q := (QuotientGroup.mk_surjective (s := Subgroup.center Q)).nontrivial
    have hperf : commutator Q = ⊤ := Group.isPerfect_def.mp hQ.1
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := Q)).ne hperf
  · exact h

end Quasisimple

section Surjection

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_modO2_surjection_of_le {H L : Subgroup G} (hLH : L ≤ H) :
    ∃ ψ : ↥L →* ↥(modO2Image H L), Function.Surjective ψ ∧ IsPGroup 2 ψ.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNn : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  set N := CFSG.pCore 2 ↥H with hN
  let φ : ↥L →* (↥H ⧸ N) := (QuotientGroup.mk' N).comp (Subgroup.inclusion hLH)
  have hrange : φ.range = modO2Image H L := by
    unfold modO2Image
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hkp : IsPGroup 2 φ.ker := by
    intro x
    have hx : Subgroup.inclusion hLH (x : ↥L) ∈ N := by
      have := x.2
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at this
      exact this
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨_, hx⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : (Subgroup.inclusion hLH (x : ↥L)) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [← map_pow] at h1
    exact (Subgroup.inclusion_injective hLH) (by simpa using h1)
  refine ⟨((MulEquiv.subgroupCongr hrange).toMonoidHom).comp φ.rangeRestrict, ?_, ?_⟩
  · exact (MulEquiv.subgroupCongr hrange).surjective.comp φ.rangeRestrict_surjective
  · rw [MonoidHom.ker_comp_of_injective _ _ (MulEquiv.subgroupCongr hrange).injective,
      MonoidHom.ker_rangeRestrict]
    exact hkp

end Surjection

section Sub

variable {G : Type} [Group G] [Finite G]

@[expose] def phiOf {H L : Subgroup G} (hLH : L ≤ H) : ↥L →* (↥H ⧸ CFSG.pCore 2 ↥H) :=
  (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (Subgroup.inclusion hLH)

omit [Finite G] in
theorem phiOf_apply {H L : Subgroup G} (hLH : L ≤ H) (x : ↥L) :
    phiOf hLH x = QuotientGroup.mk (Subgroup.inclusion hLH x) := rfl

omit [Finite G] in
theorem isPGroup_ker_phiOf {H L : Subgroup G} (hLH : L ≤ H) : IsPGroup 2 (phiOf hLH).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x
  have hx : Subgroup.inclusion hLH (x : ↥L) ∈ CFSG.pCore 2 ↥H := by
    have := x.2
    rw [MonoidHom.mem_ker, phiOf_apply, QuotientGroup.eq_one_iff] at this
    exact this
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨_, hx⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : (Subgroup.inclusion hLH (x : ↥L)) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  rw [← map_pow] at h1
  exact (Subgroup.inclusion_injective hLH) (by simpa using h1)

theorem sub_of_over {X S K L : Subgroup G} (hS : IsSylowTwoOf S X)
    (hKc : IsComponentIn K (K ⊔ S)) (hKL : K ≤ L) (hLX : IsComponentIn L X)
    {P : Subgroup ↥(modO2Image X L) → Prop} (hover : Over ↥(modO2Image X L) P) :
    K = L ∨ (P ((modO2Image X K).subgroupOf (modO2Image X L)) ∧
      ∃ ψ : ↥K →* ↥((modO2Image X K).subgroupOf (modO2Image X L)),
        Function.Surjective ψ ∧ IsPGroup 2 ψ.ker) := by
  have hLc : L ∈ cComp X := mem_cComp_of_isComponentIn hLX
  have hKX : K ≤ X := hKL.trans hLX.1
  have hK : K ∈ lFamily S := mem_cComp_of_isComponentIn hKc
  have hSb := isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hS)
    (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) (QuotientGroup.mk'_surjective _)
  have hKb := modO2Image_mem_lFamily hS hKX hK
  have hLb := modO2Image_mem_cComp hLc
  have hKLb : modO2Image X K ≤ modO2Image X L := Subgroup.map_mono (fun x hx => hKL hx)
  obtain ⟨hT', hB'⟩ := A312.isSylowTwoOf_lFamily_subgroupOf hSb hLb hKLb hKb
  by_cases htop : (modO2Image X K).subgroupOf (modO2Image X L) = ⊤
  · left
    have hLle : modO2Image X L ≤ modO2Image X K := Subgroup.subgroupOf_eq_top.mp htop
    have hLq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hLX
    have hker : (phiOf hLX.1).ker ≤ Subgroup.center ↥L := by
      have hle : (phiOf hLX.1).ker ≤ CFSG.pCore 2 ↥L :=
        le_sSup ⟨inferInstance, isPGroup_ker_phiOf hLX.1⟩
      exact hle.trans (pCore_two_le_center_of_quasisimple hLq)
    have hdec : ∀ x : ↥L, ∃ k ∈ K.subgroupOf L, ∃ z ∈ Subgroup.center ↥L, x = k * z := by
      intro x
      have hx : QuotientGroup.mk (Subgroup.inclusion hLX.1 x) ∈ modO2Image X K :=
        hLle ⟨Subgroup.inclusion hLX.1 x, x.2, rfl⟩
      obtain ⟨k₀, hk₀, hk₀x⟩ := hx
      have hk₀L : (k₀ : G) ∈ L := hKL hk₀
      set kL : ↥L := ⟨(k₀ : G), hk₀L⟩ with hkL
      have hz : kL⁻¹ * x ∈ (phiOf hLX.1).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, phiOf_apply, phiOf_apply]
        have : Subgroup.inclusion hLX.1 kL = k₀ := Subtype.ext rfl
        rw [this, inv_mul_eq_one]
        exact hk₀x
      exact ⟨kL, hk₀, kL⁻¹ * x, hker hz, by group⟩
    have hcomm : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ ≤ K.subgroupOf L := by
      rw [Subgroup.commutator_le]
      intro x _ y _
      obtain ⟨k₁, hk₁, z₁, hz₁, rfl⟩ := hdec x
      obtain ⟨k₂, hk₂, z₂, hz₂, rfl⟩ := hdec y
      rw [Unc25G2.commutator_mul_central hz₁ hz₂, commutatorElement_def]
      exact (K.subgroupOf L).mul_mem
        ((K.subgroupOf L).mul_mem ((K.subgroupOf L).mul_mem hk₁ hk₂)
          ((K.subgroupOf L).inv_mem hk₁)) ((K.subgroupOf L).inv_mem hk₂)
    have hperf : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = ⊤ := Group.isPerfect_def.mp hLq.1
    rw [hperf] at hcomm
    exact le_antisymm hKL (Subgroup.subgroupOf_eq_top.mp (eq_top_iff.mpr hcomm))
  · right
    refine ⟨hover _ hT' _ hB' htop, ?_⟩
    obtain ⟨ψ, hψs, hψk⟩ := exists_modO2_surjection_of_le hKX
    refine ⟨((Subgroup.subgroupOfEquivOfLe hKLb).symm.toMonoidHom).comp ψ, ?_, ?_⟩
    · exact (Subgroup.subgroupOfEquivOfLe hKLb).symm.surjective.comp hψs
    · rw [MonoidHom.ker_comp_of_injective _ _ (Subgroup.subgroupOfEquivOfLe hKLb).symm.injective]
      exact hψk

end Sub


end A312Sub

end CFSG.QuasithinUnique.Unc25G2

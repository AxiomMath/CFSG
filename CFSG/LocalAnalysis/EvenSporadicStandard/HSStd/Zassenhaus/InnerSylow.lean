module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5SylowConj

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.InnerCert

open Subgroup CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CFSG.Blueprint
  CFSG.Blueprint.NativeSporadic

theorem innerCentralizer_map_equiv {M N : Type*} [Group M] [Group N] (σ : M ≃* N)
    (T : Subgroup M) (z : M) (h : centralizer (T : Set M) = zpowers z) :
    centralizer ((T.map σ.toMonoidHom : Subgroup N) : Set N) = zpowers (σ z) := by
  ext x
  obtain ⟨y, rfl⟩ := σ.surjective x
  rw [mem_centralizer_iff]
  have h1 : (∀ h' ∈ (T.map σ.toMonoidHom : Subgroup N), h' * σ y = σ y * h') ↔
      y ∈ centralizer (T : Set M) := by
    rw [mem_centralizer_iff]
    constructor
    · intro hh t ht
      have := hh (σ t) ⟨t, ht, rfl⟩
      exact σ.injective (by simpa using this)
    · rintro hh _ ⟨t, ht, rfl⟩
      simpa using congrArg σ (hh t ht)
  have h2 : σ y ∈ zpowers (σ z) ↔ y ∈ zpowers z := by
    rw [mem_zpowers_iff, mem_zpowers_iff]
    refine exists_congr fun k => ?_
    rw [← map_zpow]
    exact σ.injective.eq_iff
  rw [h2, ← h]
  exact h1

section Sylow

set_option linter.unusedSectionVars false


theorem exists_std_sylow : ∃ S₀ : Subgroup ↥hsP, IsPGroup 2 S₀ ∧ ¬ 2 ∣ S₀.index ∧
    ∀ x ∈ S₀, zM * x = x * zM := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcard, hT0C1, -⟩ := hs_t0_spec
  have hT0P : hsT0 ≤ hsP := hT0C1.trans inf_le_left
  have hT0Hcard : Nat.card (hsT0.subgroupOf hsP) = 2 ^ (Nat.card ↥hsP).factorization 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hT0P).toEquiv, hcard, card_hsP,
      show (44352000 : ℕ) = 2 ^ 9 * 86625 by norm_num, factorization_two_pow_mul (by norm_num)]
    norm_num
  let T : Sylow 2 ↥hsP := Sylow.ofCard (hsT0.subgroupOf hsP) hT0Hcard
  have hTe : (T : Subgroup ↥hsP) = hsT0.subgroupOf hsP := Sylow.coe_ofCard _ _
  refine ⟨hsT0.subgroupOf hsP, ?_, ?_, fun x hx => ?_⟩
  · rw [← hTe]
    exact T.isPGroup'
  · rw [← hTe]
    exact T.not_dvd_index
  · have hx' : (x : Equiv.Perm (Fin 3850)) ∈ hsT0 := hx
    have := mem_centralizer_singleton_iff.1 (mem_inf.1 (hT0C1 hx')).2
    exact Subtype.ext (by simpa only [Subgroup.coe_mul, coe_zM] using this.symm)

end Sylow

section Main

set_option linter.unusedSectionVars false


theorem exists_equiv_zM {G : Type} [Group G] {L S : Subgroup G} {z : G}
    (hL : IsSporadic L .HS) (hS : IsPGroup 2 S) (hSL : ¬ 2 ∣ (S ⊓ L).relIndex L)
    (hz : z ∈ S ⊓ L) (hz2 : orderOf z = 2)
    (hcent : centralizer ((S ⊓ L : Subgroup G) : Set G) ⊓ L = zpowers z) :
    ∃ σ : ↥L ≃* ↥hsP, σ ⟨z, hz.2⟩ = zM := by
  obtain ⟨e₀⟩ := hL
  have e : ↥L ≃* NativeSporadic.HS := e₀
  let σ₀ : ↥L ≃* ↥hsP := e.trans hsPermEquiv
  set z' : ↥L := ⟨z, hz.2⟩ with hz'
  set T : Subgroup ↥L := (S ⊓ L).subgroupOf L with hT
  have hTp : IsPGroup 2 T := (hS.to_le inf_le_left).comap_subtype
  have hTi : ¬ 2 ∣ T.index := hSL
  have hz'2 : orderOf z' = 2 := by rw [← Subgroup.orderOf_coe]; exact hz2
  have hcentT : centralizer (T : Set ↥L) = zpowers z' := by
    ext x
    rw [mem_centralizer_iff]
    have hx : ∀ k : ℤ, ((z' ^ k : ↥L) : G) = z ^ k := fun k => by simp [hz']
    constructor
    · intro hx0
      have hxC : (x : G) ∈ centralizer ((S ⊓ L : Subgroup G) : Set G) ⊓ L := by
        refine ⟨mem_centralizer_iff.2 fun s hs => ?_, x.2⟩
        have hs' : s ∈ S ⊓ L := hs
        have := hx0 ⟨s, hs'.2⟩ (mem_subgroupOf.2 hs')
        exact congrArg Subtype.val this
      rw [hcent, mem_zpowers_iff] at hxC
      obtain ⟨k, hk⟩ := hxC
      exact mem_zpowers_iff.2 ⟨k, Subtype.ext (by rw [hx]; exact hk)⟩
    · rintro hx0 t ht
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx0
      have hzc : (z ^ k : G) ∈ centralizer ((S ⊓ L : Subgroup G) : Set G) ⊓ L := by
        rw [hcent]
        exact zpow_mem_zpowers z k
      have := mem_centralizer_iff.1 hzc.1 (t : G) ht
      exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hx]; exact this)
  obtain ⟨S₀, hS₀p, hS₀i, hS₀c⟩ := exists_std_sylow
  have hSw : IsPGroup 2 (T.map σ₀.toMonoidHom) :=
    IsPGroup.of_injective hTp (MulEquiv.subgroupMap σ₀ T).symm.toMonoidHom
      (MulEquiv.subgroupMap σ₀ T).symm.injective
  have hSwi : ¬ 2 ∣ (T.map σ₀.toMonoidHom).index := by
    have h : (T.map σ₀.toMonoidHom).index = T.index := Subgroup.index_map_equiv T σ₀
    rwa [h]
  have hzw2 : orderOf (σ₀ z') = 2 :=
    (orderOf_injective σ₀.toMonoidHom σ₀.injective z').trans hz'2
  have hcentQ : centralizer (((T.map σ₀.toMonoidHom : Subgroup ↥hsP) ⊓ ⊤ : Subgroup ↥hsP) :
      Set ↥hsP) ⊓ ⊤ = zpowers (σ₀ z') := by
    simp only [inf_top_eq]
    exact innerCentralizer_map_equiv σ₀ T z' hcentT
  have hzM1 : zM ≠ 1 := by
    intro h
    have h2 : orderOf zM = 2 := by rw [← Subgroup.orderOf_coe, coe_zM]; exact hsT1_mem_ord.2
    rw [h, orderOf_one] at h2
    omega
  obtain ⟨g, hg1, hg2⟩ := exists_conj_of_one_sylow (⊤ : Subgroup ↥hsP) S₀ hS₀p hS₀i zM
    (mem_top _) hzM1 (fun x hx => hS₀c x hx.1) (T.map σ₀.toMonoidHom) hSw hSwi (σ₀ z') hzw2
    hcentQ
  refine ⟨σ₀.trans (MulAut.conj g⁻¹), ?_⟩
  show g⁻¹ * σ₀ z' * g⁻¹⁻¹ = zM
  rw [← hg2]
  group

end Main

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.InnerCert

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup CFSG.Sporadic.Schreier CFSG.Blueprint.NativeSporadic

section Final

set_option linter.unusedSectionVars false


theorem innerData_of_sylow {G : Type} [Group G]
    {L S : Subgroup G} {z : G} (hL : IsSporadic L .HS) (hS : IsPGroup 2 S)
    (hSL : ¬ 2 ∣ (S ⊓ L).relIndex L) (hz : z ∈ S ⊓ L) (hz2 : orderOf z = 2)
    (hcent : centralizer ((S ⊓ L : Subgroup G) : Set G) ⊓ L = zpowers z) :
    Nonempty (InnerData L z) := by
  obtain ⟨σ, hσ⟩ := InnerCert.exists_equiv_zM hL hS hSL hz hz2 hcent
  obtain ⟨D⟩ := InnerCert.innerData_model
  let ψ : ↥hsP →* G := L.subtype.comp σ.symm.toMonoidHom
  refine ⟨InnerCert.innerDataMap ψ ?_ ?_ ?_ D⟩
  · exact Subtype.val_injective.comp σ.symm.injective
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (σ.symm x).2
    · intro hy
      exact ⟨σ ⟨y, hy⟩, by simp [ψ]⟩
  · show ((σ.symm InnerCert.zM : ↥L) : G) = z
    rw [← hσ]
    simp

end Final

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus

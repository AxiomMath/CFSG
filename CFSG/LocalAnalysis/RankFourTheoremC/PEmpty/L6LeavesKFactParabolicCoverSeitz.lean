module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Even

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPCov

open CFSG.Open CFSG.LieType.Seitz Subgroup
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (Seitz2313Even)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover (EvenScope)

theorem hyperGenSet_of_seitzHyperGamma {A : Type*} [Group A] {K E : Subgroup A} {f : ℕ}
    (hEK : E ≤ K)
    (h : seitzHyperGamma f ((E.subgroupOf K).map (MulAut.conj : ↥K →* MulAut ↥K)) = ⊤) :
    K ≤ Subgroup.closure {k : A | k ∈ K ∧ ∃ F : Subgroup A, F ≤ E ∧ F.relIndex E = f ∧
      ∀ y ∈ F, y * k = k * y} := by
  intro k hk
  have hk' : (⟨k, hk⟩ : ↥K) ∈
      seitzHyperGamma f ((E.subgroupOf K).map (MulAut.conj : ↥K →* MulAut ↥K)) :=
    h ▸ Subgroup.mem_top _
  have hE : (E.subgroupOf K).map K.subtype = E := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hEK]
  have hle : seitzHyperGamma f ((E.subgroupOf K).map (MulAut.conj : ↥K →* MulAut ↥K)) ≤
      (Subgroup.closure {k : A | k ∈ K ∧ ∃ F : Subgroup A, F ≤ E ∧ F.relIndex E = f ∧
        ∀ y ∈ F, y * k = k * y}).comap K.subtype := by
    refine iSup₂_le fun F' hF' k₀ hk₀ => ?_
    apply Subgroup.subset_closure
    refine ⟨k₀.2, ((E.subgroupOf K) ⊓
      F'.comap (MulAut.conj : ↥K →* MulAut ↥K)).map K.subtype, ?_, ?_, ?_⟩
    · exact (Subgroup.map_mono inf_le_left).trans hE.le
    · calc (((E.subgroupOf K) ⊓
            F'.comap (MulAut.conj : ↥K →* MulAut ↥K)).map K.subtype).relIndex E
          = (((E.subgroupOf K) ⊓
            F'.comap (MulAut.conj : ↥K →* MulAut ↥K)).map K.subtype).relIndex
              ((E.subgroupOf K).map K.subtype) := by rw [hE]
        _ = ((E.subgroupOf K) ⊓ F'.comap (MulAut.conj : ↥K →* MulAut ↥K)).relIndex
              (E.subgroupOf K) :=
            Subgroup.relIndex_map_map_of_injective _ _ K.subtype_injective
        _ = (F'.comap (MulAut.conj : ↥K →* MulAut ↥K)).relIndex (E.subgroupOf K) :=
            Subgroup.inf_relIndex_left _ _
        _ = F'.relIndex ((E.subgroupOf K).map (MulAut.conj : ↥K →* MulAut ↥K)) :=
            Subgroup.relIndex_comap _ _ _
        _ = f := hF'.2
    · rintro _ ⟨y, ⟨-, hyF⟩, rfl⟩
      have h1 : (MulAut.conj y) k₀ = k₀ := hk₀ (MulAut.conj y) hyF
      have h2 : y * k₀ = k₀ * y := by
        have h3 : y * k₀ * y⁻¹ = k₀ := h1
        calc y * k₀ = (y * k₀ * y⁻¹) * y := by group
          _ = k₀ * y := by rw [h3]
      exact congrArg Subtype.val h2
  exact hle hk'

theorem exists_hyperplane {A : Type*} [Group A] [Finite A] {f : ℕ} [hf : Fact f.Prime]
    {E : Subgroup A} (hEcard : Nat.card E = f ^ 2) :
    ∃ F : Subgroup A, F ≤ E ∧ F.relIndex E = f := by
  obtain ⟨F₀, hF₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E) f (n := 1)
    (by rw [hEcard]; exact pow_dvd_pow f (by norm_num))
  refine ⟨F₀.map E.subtype, Subgroup.map_subtype_le _, ?_⟩
  have h := Subgroup.relIndex_mul_card (H := F₀.map E.subtype) (K := E)
  rw [inf_eq_left.mpr (Subgroup.map_subtype_le _),
    Subgroup.card_map_of_injective E.subtype_injective, hF₀, pow_one, hEcard] at h
  exact Nat.eq_of_mul_eq_mul_right hf.out.pos (by rw [h]; ring)

theorem hyperGenSet_of_seitz2313Even {A : Type} [Group A] [Finite A] (hS : Seitz2313Even)
    {K E U : Subgroup A} {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) {d : TauCeti.ValidLieTypeIndex}
    (hd : Nonempty (↥K ≃* (TauCeti.CFSGIndex.lie d).Group)) (hs : EvenScope d.1)
    (hEK : E ≤ K) (hE : IsElemAbelian f E) (hEcard : Nat.card E = f ^ 2) (hUK : U ≤ K)
    (hU0 : U ≠ ⊥) (hU2 : IsPGroup 2 U) (hEU : E ≤ normalizer (U : Set A)) :
    K ≤ Subgroup.closure {k : A | k ∈ K ∧ ∃ F : Subgroup A, F ≤ E ∧ F.relIndex E = f ∧
      ∀ y ∈ F, y * k = k * y} := by
  haveI : Fact f.Prime := ⟨hf⟩
  by_cases hcen : ∀ e ∈ E, ∀ k ∈ K, e * k = k * e
  · obtain ⟨F, hFE, hrel⟩ := exists_hyperplane hEcard
    intro k hk
    exact Subgroup.subset_closure ⟨hk, F, hFE, hrel, fun y hy => hcen y (hFE hy) k hk⟩
  · push Not at hcen
    obtain ⟨e, heE, k, hkK, hek⟩ := hcen
    set Eb : Subgroup (MulAut ↥K) :=
      (E.subgroupOf K).map (MulAut.conj : ↥K →* MulAut ↥K) with hEb
    have hEbab : IsElemAbelian f Eb := (hE.subgroupOf K).map _
    have hEbne : Eb ≠ ⊥ := by
      intro hbot
      have he' : (⟨e, hEK heE⟩ : ↥K) ∈ E.subgroupOf K := heE
      have hmem : (MulAut.conj (⟨e, hEK heE⟩ : ↥K)) ∈ Eb := Subgroup.mem_map_of_mem _ he'
      rw [hbot, Subgroup.mem_bot] at hmem
      have h1 : (MulAut.conj (⟨e, hEK heE⟩ : ↥K)) ⟨k, hkK⟩ = ⟨k, hkK⟩ := by
        have := DFunLike.congr_fun hmem ⟨k, hkK⟩
        simpa using this
      have h3 : (⟨e, hEK heE⟩ : ↥K) * ⟨k, hkK⟩ * (⟨e, hEK heE⟩ : ↥K)⁻¹ = ⟨k, hkK⟩ := h1
      have h2 : (⟨e, hEK heE⟩ : ↥K) * ⟨k, hkK⟩ = ⟨k, hkK⟩ * ⟨e, hEK heE⟩ :=
        calc (⟨e, hEK heE⟩ : ↥K) * ⟨k, hkK⟩
            = ((⟨e, hEK heE⟩ : ↥K) * ⟨k, hkK⟩ * (⟨e, hEK heE⟩ : ↥K)⁻¹) * ⟨e, hEK heE⟩ := by
              group
          _ = ⟨k, hkK⟩ * ⟨e, hEK heE⟩ := by rw [h3]
      exact hek (congrArg Subtype.val h2)
    have hUinv : ∃ U' : Subgroup ↥K, U' ≠ ⊥ ∧ IsPGroup 2 ↥U' ∧ ∀ ψ ∈ Eb, ∀ u ∈ U', ψ u ∈ U' := by
      refine ⟨U.subgroupOf K, ?_, hU2.comap_subtype, ?_⟩
      · intro hbot
        apply hU0
        have hmap := Subgroup.subgroupOf_map_subtype U K
        rw [hbot, Subgroup.map_bot, inf_eq_left.mpr hUK] at hmap
        exact hmap.symm
      · rintro ψ ⟨y, hy, rfl⟩ u hu
        have hyN : (y : A) ∈ normalizer (U : Set A) := hEU hy
        have hu' : (u : A) ∈ U := hu
        exact (Subgroup.mem_normalizer_iff.mp hyN _).mp hu'
    have h1 := hS f hf hf2 ↥K d hd hs Eb hEbab hEbne hUinv
    have h2 : seitzHyperGamma f Eb = ⊤ := by
      rw [eq_top_iff, ← h1]
      refine iSup₂_le fun F hF => ?_
      exact le_trans (Subgroup.map_subtype_le _) (le_iSup₂_of_le F hF le_rfl)
    exact hyperGenSet_of_seitzHyperGamma hEK h2

end KPCov

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

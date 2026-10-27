module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.InnerFusionG2
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.G2Subgroup
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutG2

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.InnerFusion

open CFSG.Open Subgroup TauCeti CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley
open CFSG.GH74.GLS.Stage2.Bender.Thm1 (d4_mem_trialityFieldImage_self_iff
  d4_trialityFieldImage_self_le)

section Conj

theorem conj_conj_mul_eq {C : Type} [Group C] (δ : MulAut C) {j : C} (hj : δ j = j) (s : C) :
    MulAut.conj j * (MulAut.conj s * δ) * (MulAut.conj j)⁻¹ =
      MulAut.conj (j * s * j⁻¹) * δ := by
  refine MulEquiv.ext fun x => ?_
  have hj' : δ j⁻¹ = j⁻¹ := by rw [map_inv, hj]
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, MulAut.conj_symm_apply,
    map_mul, hj, hj']
  group

end Conj

section Subfield


variable {K : Type} [Field K] [Finite K]

@[expose] noncomputable def d4SubfieldJ (σ : K ≃+* K) :
    Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
  (trialityFieldImage σ σ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)

theorem mem_d4SubfieldJ {σ : K ≃+* K} (hσ3 : ∀ c, σ (σ (σ c)) = c)
    {x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} :
    x ∈ d4SubfieldJ σ ↔ fieldActor (t := TwistTag.D4) σ σ x = x :=
  (Subgroup.mem_subgroupOf).trans (d4_mem_trialityFieldImage_self_iff σ hσ3 x)

theorem nonempty_d4SubfieldJ_equiv (σ : K ≃+* K) :
    Nonempty (d4SubfieldJ σ ≃* adjointGroup .G2 (CFSG.LieType.Chevalley.fixSubfield σ)) := by
  have e₁ : d4SubfieldJ σ ≃* trialityFieldImage σ σ :=
    Subgroup.subgroupOfEquivOfLe (d4_trialityFieldImage_self_le σ)
  by_cases hk : (3 : ℕ∞) ≤ ENat.card (CFSG.LieType.Chevalley.fixSubfield σ)
  · exact ⟨e₁.trans (CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.trialityFieldImageEquivG2 σ hk)⟩
  · have : Finite (CFSG.LieType.Chevalley.fixSubfield σ) := Subtype.finite
    have hk2 : Nat.card (CFSG.LieType.Chevalley.fixSubfield σ) = 2 := by
      rw [ENat.card_eq_coe_natCard] at hk
      have h1 : 1 < Nat.card (CFSG.LieType.Chevalley.fixSubfield σ) := Finite.one_lt_card
      have h3 : Nat.card (CFSG.LieType.Chevalley.fixSubfield σ) < 3 := by exact_mod_cast not_le.1 hk
      omega
    have h2 : (2 : CFSG.LieType.Chevalley.fixSubfield σ) = 0 := by
      have : Fintype (CFSG.LieType.Chevalley.fixSubfield σ) := Fintype.ofFinite _
      have h := FiniteField.cast_card_eq_zero (CFSG.LieType.Chevalley.fixSubfield σ)
      rw [← Nat.card_eq_fintype_card, hk2] at h
      exact_mod_cast h
    exact ⟨e₁.trans ((CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.trialityFieldImageEquivRoot
      σ).trans ((MulEquiv.subgroupCongr
        (CFSG.RankThree.PartTwo.KFacts.d4_twistedFixedGroup_id_eq_graphFixedRootGroup
          (K := CFSG.LieType.Chevalley.fixSubfield σ))).symm.trans
        (CFSG.RankThree.PartTwo.KFacts.d4FixedG2Equiv _ h2)))⟩

end Subfield

section Fixed


theorem fusesIntoFixedE9_conj_mul_of_g2 {C : Type} [Group C] {k : Type} [Field k] [Finite k]
    (hk3 : ringChar k ≠ 3) (δ : MulAut C) (J : Subgroup C) (hJ : ∀ x, x ∈ J ↔ δ x = x)
    (Φ : J ≃* adjointGroup .G2 k) (hT : ∀ x : C, orderOf x = 3 → ∃ g, g * x * g⁻¹ ∈ J)
    {s : C} (hs : s ∈ J) (hs3 : s ^ 3 = 1) : FusesIntoFixedE9 (MulAut.conj s * δ) := by
  set ι : adjointGroup .G2 k →* C := J.subtype.comp Φ.symm.toMonoidHom with hιdef
  have hιinj : Function.Injective ι := J.subtype_injective.comp Φ.symm.injective
  have hιJ : ∀ h, ι h ∈ J := fun h => (Φ.symm h).2
  have hιΦ : ∀ y (hy : y ∈ J), ι (Φ ⟨y, hy⟩) = y := fun y hy => by
    show ((Φ.symm (Φ ⟨y, hy⟩) : J) : C) = y
    rw [MulEquiv.symm_apply_apply]
  set E : Subgroup C := (g2Plane k).map ι with hEdef
  have hE : IsElemAbelian 3 E := isElemAbelian_g2Plane.map ι
  have hE9 : Nat.card E = 9 := by
    rw [hEdef, Subgroup.card_map_of_injective hιinj,
      card_g2Plane (three_ne_zero_of_ringChar hk3)]
  have hEJ : ∀ e ∈ E, δ e = e := by
    rintro _ ⟨h, -, rfl⟩
    exact (hJ _).1 (hιJ h)
  have hrep : ∀ x : C, orderOf x = 3 → ∃ g, g * x * g⁻¹ ∈ E := by
    intro x hx
    obtain ⟨g, hg⟩ := hT x hx
    have hy : orderOf (Φ ⟨g * x * g⁻¹, hg⟩) = 3 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, orderOf_conj_eq, hx]
    obtain ⟨h, hh⟩ := exists_conj_mem_g2Plane hk3 hy
    refine ⟨ι h * g, ?_⟩
    have e1 : ι h * g * x * (ι h * g)⁻¹ = ι (h * Φ ⟨g * x * g⁻¹, hg⟩ * h⁻¹) := by
      rw [map_mul, map_mul, map_inv, hιΦ]
      group
    rw [e1]
    exact ⟨_, hh, rfl⟩
  by_cases hs1 : s = 1
  · subst hs1
    rw [map_one, one_mul]
    exact fusesIntoFixedE9_of_reps hE hE9 hEJ hrep
  · have ht : orderOf (Φ ⟨s, hs⟩) = 3 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      exact orderOf_eq_three hs3 hs1
    obtain ⟨h, hh⟩ := exists_conj_eq_g2Three hk3 ht
    have hjδ : δ (ι h) = ι h := (hJ _).1 (hιJ h)
    have hs' : ι h * s * (ι h)⁻¹ ∈ E := by
      have e1 : ι h * s * (ι h)⁻¹ = ι (h * Φ ⟨s, hs⟩ * h⁻¹) := by
        rw [map_mul, map_mul, map_inv, hιΦ]
      rw [e1]
      refine ⟨_, ?_, rfl⟩
      rcases hh with hh | hh <;> rw [hh]
      · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    refine FusesIntoFixedE9.of_conj (MulAut.conj (ι h)) ?_
    rw [conj_conj_mul_eq δ hjδ]
    refine fusesIntoFixedE9_of_reps hE hE9 (fun e he => ?_) hrep
    rw [MulAut.mul_apply, hEJ e he, MulAut.conj_apply, hE.comm hs' he, mul_inv_cancel_right]

end Fixed

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.InnerFusion

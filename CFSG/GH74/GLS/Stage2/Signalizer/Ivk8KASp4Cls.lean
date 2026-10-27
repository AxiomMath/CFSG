module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAGen
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSp4Cls

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSp4
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldEquiv)
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

@[expose] def KASp4U1 : Prop :=
  ∀ (F : Type) [Field F] [Finite F], ringChar F ≠ 2 → 5 ≤ Nat.card F →
    KAAll (MulAut.conj (u1 F))

@[expose] def KASp4I : Prop :=
  ∀ (F : Type) [Field F] [Finite F], ringChar F ≠ 2 → 5 ≤ Nat.card F →
    ∀ (a : F) (ha : a ≠ 0), KAAll (alphaI ha)

@[expose] def KASp4II : Prop :=
  ∀ (F : Type) [Field F] [Finite F], ringChar F ≠ 2 →
    ∀ (A : gsp 2 F) (d : Fˣ),
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = (d : F) • 1 →
      (d : F) = (multiplierUnit A : F) → (∀ l : F, l ^ 2 ≠ (multiplierUnit A : F)) →
      KAAll (conjAut 2 F A)

@[expose] def KASp4Field : Prop :=
  ∀ (F : Type) [Field F] [Finite F], ringChar F ≠ 2 →
    ∀ (A : gsp 2 F) (σ : F ≃+* F), σ ≠ 1 → σ ^ 2 = 1 →
      (∃ d : Fˣ, (A : GL (Fin 2 ⊕ Fin 2) F) *
        glFieldEquiv (Fin 2 ⊕ Fin 2) σ (A : GL (Fin 2 ⊕ Fin 2) F) =
          Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) d) →
      Nat.card F = Nat.card {c : F // σ c = c} ^ 2 →
      KAAll (conjAut 2 F A * fieldAut 2 F σ)

@[expose] def KASp4U1Three : Prop :=
  ∀ (F : Type) [Field F] [Finite F], Nat.card F = 3 → KAAll (MulAut.conj (u1 F))

@[expose] def KASp4IThree : Prop :=
  ∀ (F : Type) [Field F] [Finite F], Nat.card F = 3 → ∀ (a : F) (ha : a ≠ 0), KAAll (alphaI ha)

theorem ka_congr_eq_mul {Y : Type} [Group Y] (e α : MulAut Y) :
    MulAut.congr e α = e * α * e⁻¹ := by
  ext x
  simp [MulAut.congr_apply]

theorem kaAll_of_typeI {F : Type} [Field F] [Finite F] (hodd : ringChar F ≠ 2)
    (hI : ∀ (a : F) (ha : a ≠ 0), KAAll (alphaI ha)) (A : gsp 2 F) (d : Fˣ)
    (hAA : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = (d : F) • 1)
    (hdm : (d : F) = -(multiplierUnit A : F)) : KAAll (conjAut 2 F A) := by
  have h2 := Ring.two_ne_zero hodd
  have hd0 : (d : F) ≠ 0 := d.ne_zero
  have hA : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * formJ 2 F *
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      (-(d : F)) • formJ 2 F := by
    rw [multiplierUnit_spec, hdm, neg_neg]
  obtain ⟨g, hg⟩ := exists_frame_typeI h2 hd0 hA hAA
  set g' : gsp 2 F := ⟨(g : GL (Fin 2 ⊕ Fin 2) F), statedSp_le_gsp g.2⟩ with hg'
  have hAg : A * g' = g' * aIgsp hd0 := by
    apply Subtype.ext
    apply Units.ext
    exact hg
  have hAeq : A = g' * aIgsp hd0 * g'⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    exact hAg
  have hconj : conjAut 2 F A =
      MulAut.conj (proj 2 F g) * alphaI hd0 * (MulAut.conj (proj 2 F g))⁻¹ := by
    rw [hAeq, map_mul, map_mul, map_inv, alphaI]
    have : conjAut 2 F g' = MulAut.conj (proj 2 F g) := conjAut_statedSp g
    rw [this]
  have h' := KAAll.of_mulEquiv (MulAut.conj (proj 2 F g) : StatedProj (StatedSp 2 F) ≃*
    StatedProj (StatedSp 2 F)) (hI (d : F) hd0)
  have key : MulAut.congr (MulAut.conj (proj 2 F g) : StatedProj (StatedSp 2 F) ≃*
      StatedProj (StatedSp 2 F)) (alphaI hd0) = conjAut 2 F A := by
    rw [ka_congr_eq_mul, hconj]
  rwa [key] at h'

theorem kaAll_psp4 (h1 : KASp4U1) (hI : KASp4I) (hII : KASp4II) (hF : KASp4Field)
    (h1' : KASp4U1Three) (hI' : KASp4IThree)
    {F : Type} [Field F] [Finite F] (hodd : ringChar F ≠ 2)
    {α : MulAut (StatedProj (StatedSp 2 F))} (hα2 : α * α = 1) (hα1 : α ≠ 1) : KAAll α := by
  classical
  have hoddc : Odd (Nat.card F) := by
    have : Fintype F := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two hodd)
  have hcard : Nat.card F = 3 ∨ 5 ≤ Nat.card F := by
    have hlt := Finite.one_lt_card (α := F)
    obtain ⟨k, hk⟩ := hoddc
    omega
  have hU1 : KAAll (MulAut.conj (u1 F)) := by
    rcases hcard with h3 | h5
    · exact h1' F h3
    · exact h1 F hodd h5
  have hIc : ∀ (a : F) (ha : a ≠ 0), KAAll (alphaI ha) := by
    rcases hcard with h3 | h5
    · exact hI' F h3
    · exact hI F hodd h5
  have hsimple := isSimpleGroup_psp4_of_odd hodd
  obtain ⟨A, σ, hα, hσ2, ⟨d, hd⟩, hlin, hfield⟩ :=
    (CatalogueBSymplecticRepresentation.odd_symplectic_automorphism_semilinear_representation hodd
      le_rfl).2.2 α hα2 hα1
  by_cases hσ : σ = 1
  · subst hσ
    have hα' : α = conjAut 2 F A := by rw [hα, map_one, mul_one]
    have hAA := mul_self_of_rep A d hd
    by_cases hsq : ∃ l : F, l ^ 2 = (multiplierUnit A : F)
    · obtain ⟨u, hu⟩ := conjAut_mem_range_of_sq A hsq.choose_spec
      have hαu : α = MulAut.conj u := by rw [hα', ← hu]
      have hu1 : u ≠ 1 := fun h1' => hα1 (by rw [hαu, h1', map_one])
      have hu2 : u * u = 1 := by
        have hc : MulAut.conj (u * u) = 1 := by rw [map_mul, ← hαu, hα2]
        have hz : u * u ∈ center (StatedProj (StatedSp 2 F)) := by
          rw [Subgroup.mem_center_iff]
          intro g
          have := congrArg (fun φ : MulAut (StatedProj (StatedSp 2 F)) => φ g) hc
          simp only [MulAut.conj_apply, MulAut.one_apply] at this
          calc g * (u * u) = u * u * g * (u * u)⁻¹ * (u * u) := by rw [this]
            _ = u * u * g := by group
        rw [center_psp4_eq_bot hodd] at hz
        exact Subgroup.mem_bot.mp hz
      have hord : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
      obtain ⟨g, hg⟩ := exists_conj_of_orderOf_eq_two hoddc hord
      have key : ∀ v : StatedProj (StatedSp 2 F), KAAll (MulAut.conj v) → g⁻¹ * u * g = v →
          KAAll (MulAut.conj u) := by
        intro v hv hgv
        have h' := KAAll.of_mulEquiv (MulAut.conj g : StatedProj (StatedSp 2 F) ≃*
          StatedProj (StatedSp 2 F)) hv
        rw [ka_congr_conj, ← hgv] at h'
        have e1 : g * (g⁻¹ * u * g) * g⁻¹ = u := by group
        rwa [MulAut.conj_apply, e1] at h'
      rw [hαu]
      rcases hg with hg | hg
      · exact key _ hU1 hg
      · refine key _ ?_ hg
        have hT2 : u2 F = proj 2 F (T2 F) := rfl
        rw [hT2, ← conjAut_statedSp (T2 F)]
        refine kaAll_of_typeI hodd hIc
          ⟨(T2 F : GL (Fin 2 ⊕ Fin 2) F), statedSp_le_gsp (T2 F).2⟩ (-1) ?_ ?_
        · rw [Units.val_neg, Units.val_one, neg_one_smul]
          exact T2_mul_T2
        · have hm : multiplierUnit (⟨(T2 F : GL (Fin 2 ⊕ Fin 2) F), statedSp_le_gsp (T2 F).2⟩ :
              gsp 2 F) = 1 :=
            multiplierUnit_eq _ (by simpa using symplectic_of_mem (T2 F))
          rw [hm]
          simp
    · push Not at hsq
      rcases eq_or_eq_neg_multiplier A hAA with hdm | hdm
      · rw [hα']
        exact hII F hodd A d hAA hdm hsq
      · rw [hα']
        exact kaAll_of_typeI hodd hIc A d hAA hdm
  · rw [hα]
    exact hF F hodd A σ hσ hσ2 ⟨d, hd⟩ (hfield hσ).1

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

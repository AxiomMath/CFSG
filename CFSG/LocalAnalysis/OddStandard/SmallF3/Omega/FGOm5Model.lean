module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelFix
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK1Aux1
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFShapes
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeLowCent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Block

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem fg_twoPrimeRes_le {G : Type} [Group G] (H : Subgroup G) :
    twoPrimeRes H ≤ H := by
  unfold twoPrimeRes
  rw [Subgroup.closure_le]
  exact fun x hx => hx.1

theorem fg_model_om5_involutions (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1) {t : OGroup Q}
    (htt : t * t = 1) {α : ℤˣ} (htype : invType t = (1, α)) :
    ∃ w₀ w₁ : ↥(ffFix hQ (by omega : 2 ≤ Module.finrank (ZMod 3) V)
        (projOrthToProjSim Q (toProj Q t))),
      w₀ ∈ twoRes (⊤ : Subgroup ↥(ffFix hQ (by omega : 2 ≤ Module.finrank (ZMod 3) V)
        (projOrthToProjSim Q (toProj Q t)))) ∧
      w₁ ∈ twoRes (⊤ : Subgroup ↥(ffFix hQ (by omega : 2 ≤ Module.finrank (ZMod 3) V)
        (projOrthToProjSim Q (toProj Q t)))) ∧
      w₀ * w₀ = 1 ∧ w₁ * w₁ = 1 ∧
      HasType ((w₀ : ↥(omegaProj hQ)) : ProjOrth Q) 4 1 ∧
      HasType ((w₁ : ↥(omegaProj hQ)) : ProjOrth Q) 2 (-1) := by
  haveI : Finite V := Module.finite_of_finite (ZMod 3)
  haveI : Finite (OGroup Q) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hcdim : Module.finrank (ZMod 3) (commSp t) = 1 := congrArg Prod.fst htype
  have hUdim : Module.finrank (ZMod 3) (fixSp t) = 5 := by
    have h := finrank_fixSp_add_finrank_commSp (Q := Q) t
    rw [hcdim, hdim] at h
    omega
  have hW : 2 ≤ Module.finrank (ZMod 3) (fixSp t) := by omega
  have hR := nondegenerate_restrict_fixSp hQ htt
  obtain ⟨e, he⟩ := ff_fixEquiv hQ hdim hsgn htt
  let ψ₁ : omegaGroup hR →* OGroup Q :=
    ((blockHom htt).comp (MonoidHom.inl _ _)).comp (omegaGroup hR).subtype
  have hψ₁ : ∀ g, ψ₁ g ∈ omegaGroup hQ ⊓ Subgroup.centralizer ({t} : Set (OGroup Q)) := by
    intro g
    refine Subgroup.mem_inf.mpr ⟨blockHom_left_mem_omegaGroup hQ htt hW g.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact (ff_blockHom_inl_commute htt (g : OGroup (Q.restrict (fixSp t)))).symm
  let ψ : omegaGroup hR →* ↥(ffFix hQ h2
      (projOrthToProjSim Q (toProj Q t))) :=
    e.toMonoidHom.comp (ψ₁.codRestrict _ hψ₁)
  have hψinj : Function.Injective ψ := by
    refine e.injective.comp ?_
    intro a b hab
    have h1 : ψ₁ a = ψ₁ b := congrArg Subtype.val hab
    exact Subtype.ext (congrArg Prod.fst (blockHom_injective htt h1))
  have hψval : ∀ g, (((ψ g : ↥(ffFix hQ h2
      (projOrthToProjSim Q (toProj Q t)))) : ↥(omegaProj hQ)) : ProjOrth Q) =
        toProj Q (ψ₁ g) := fun g => he _
  have hlie : LieModel (omegaGroup hR) .PSp 2 3 1 := by
    have hZ : Subgroup.center (omegaGroup hR) = ⊥ :=
      Subgroup.eq_bot_of_card_eq (Subgroup.center (omegaGroup hR))
        (natCard_center_omegaGroup_five hR hUdim)
    exact LieModel.of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot) (lieModel_quotient_center_omegaGroup_five hR hUdim)
  have hlieR : LieModel ↥ψ.range .PSp 2 3 1 :=
    hlie.of_mulEquiv (MonoidHom.ofInjective hψinj)
  obtain ⟨hS, hnc⟩ := ff_simple_of_lieModel_psp hlieR
  haveI : Finite ↥ψ.range := inferInstance
  have hX : ∀ g : omegaGroup hR, ψ g * ψ g = 1 → ψ g ∈ twoRes (⊤ : Subgroup ↥(ffFix hQ
      h2 (projOrthToProjSim Q (toProj Q t)))) := by
    intro g hg
    exact fg_twoPrimeRes_le _ (ff_mem_X_of_simple (C := ⊤) ψ.range le_top hS hnc ⟨g, rfl⟩ hg)
  obtain ⟨y₀, hy₀2, hy₀t⟩ := (exists_involution_of_type hR 4 1).mpr
    ⟨by omega, fun _ => rfl, fun h => absurd h (by omega)⟩
  obtain ⟨y₁, hy₁2, hy₁t⟩ := (exists_involution_of_type hR 2 (-1)).mpr
    ⟨by omega, fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
  have hy₀Ω : y₀ ∈ omegaGroup hR := by
    refine (involution_mem_omegaGroup_iff hR hy₀2).mpr ⟨?_, ?_⟩
    · rw [show invDim y₀ = 4 from congrArg Prod.fst hy₀t]
      decide
    · rw [show invDim y₀ = 4 from congrArg Prod.fst hy₀t,
        show invSign y₀ = 1 from congrArg Prod.snd hy₀t]
      decide
  have hy₁Ω : y₁ ∈ omegaGroup hR := by
    refine (involution_mem_omegaGroup_iff hR hy₁2).mpr ⟨?_, ?_⟩
    · rw [show invDim y₁ = 2 from congrArg Prod.fst hy₁t]
      decide
    · rw [show invDim y₁ = 2 from congrArg Prod.fst hy₁t,
        show invSign y₁ = -1 from congrArg Prod.snd hy₁t]
      decide
  have hT : ∀ (g : omegaGroup hR) (r : ℕ) (a : ℤˣ),
      (g : OGroup (Q.restrict (fixSp t))) * g = 1 →
      invType (g : OGroup (Q.restrict (fixSp t))) = (r, a) → 0 < r →
      HasType (((ψ g : ↥(ffFix hQ h2 (projOrthToProjSim Q (toProj Q t)))) :
        ↥(omegaProj hQ)) : ProjOrth Q) r a := by
    intro g r a hgg hty hr
    have hg1 : g ≠ 1 := by
      intro h
      have h' : (g : OGroup (Q.restrict (fixSp t))) = 1 := congrArg Subtype.val h
      rw [h', invType_one] at hty
      have h0 := congrArg Prod.fst hty
      simp only at h0
      omega
    have hne : ψ g ≠ 1 := fun h => hg1 (hψinj (h.trans (map_one ψ).symm))
    have hg2 : g * g = 1 := Subtype.ext hgg
    have hbb : ψ₁ g * ψ₁ g = 1 := by
      rw [← map_mul, hg2, map_one]
    refine ⟨fun h => hne (Subtype.ext (Subtype.ext h)), ψ₁ g, hbb, ?_, (hψval g).symm⟩
    exact (ff_invType_blockHom_inl hQ htt hgg).trans hty
  have hg₀2 : (⟨y₀, hy₀Ω⟩ : omegaGroup hR) * ⟨y₀, hy₀Ω⟩ = 1 := Subtype.ext hy₀2
  have hg₁2 : (⟨y₁, hy₁Ω⟩ : omegaGroup hR) * ⟨y₁, hy₁Ω⟩ = 1 := Subtype.ext hy₁2
  have hw₀ : ψ ⟨y₀, hy₀Ω⟩ * ψ ⟨y₀, hy₀Ω⟩ = 1 := by rw [← map_mul, hg₀2, map_one]
  have hw₁ : ψ ⟨y₁, hy₁Ω⟩ * ψ ⟨y₁, hy₁Ω⟩ = 1 := by rw [← map_mul, hg₁2, map_one]
  exact ⟨ψ ⟨y₀, hy₀Ω⟩, ψ ⟨y₁, hy₁Ω⟩, hX _ hw₀, hX _ hw₁, hw₀, hw₁,
    hT ⟨y₀, hy₀Ω⟩ 4 1 hy₀2 hy₀t (by norm_num), hT ⟨y₁, hy₁Ω⟩ 2 (-1) hy₁2 hy₁t (by norm_num)⟩

end CFSG.OddStandard.SmallF3.Omega

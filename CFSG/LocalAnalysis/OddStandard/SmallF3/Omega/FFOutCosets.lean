module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFOutModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFOutAdapt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {G : Type} [Group G] {L : Subgroup G}

theorem ff_outCosets_of_model [Finite G] (hL : IsOm6M L) {S B : Subgroup G}
    (hS : IsSylow2Of S (normalizer (L : Set G))) (hB : IsNormalE16In (S ⊓ L) B)
    (h1 : ∀ y ∈ S, ∀ α : ℤˣ,
      ¬ InducesTypeSome L y 6 (-1) 1 α ∧ ¬ InducesTypeSome L y 6 (-1) 3 α)
    (hAut : autIn S B ≤ autIn L B) (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = -1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (fr : NFrame Q (Fin 6) 1)
    (hBfr : ffImg (ff6mPhi e) B = ffB1 hQ fr)
    (hPfr : ffImg (ff6mPhi e) (S ⊓ L) = ffP1 hQ fr) :
    S ≤ (S ⊓ L) ⊔ centralizer (L : Set G) ∨
      ∃ γ ∈ S, InducesOutsideGStar L 6 (-1) γ ∧
        S ≤ zpowers γ ⊔ (S ⊓ L) ⊔ centralizer (L : Set G) := by
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) := ff6m_odd_center hL
  have hb := ff_transfer_bounds hQ hdim hsgn e fr hS.1 hPfr
  have hi := ff_transfer_i hQ hdim hsgn e h1
  have hii := ff_transfer_ii hL hQ hdim hsgn e fr hS hB hAut hBfr
  rcases ff_out_model hQ hdim hsgn fr hb.1 hb.2 hi hii with hΩ | ⟨x, hxQ, hxG, hxx, hcl⟩
  · exact Or.inl (ff_theta_back_left hL.1 hQ hdim hsgn e hodd hS hΩ)
  · obtain ⟨γ, hγN, hγS, hθ⟩ := mem_ffThetaImg_iff.mp hxQ
    refine Or.inr ⟨γ, hγS, ?_, ?_⟩
    · refine ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ, e, x, hdim, hsgn, ?_, hxx,
        hxG⟩
      have hind := ffTheta_induces hQ (Or.inr ⟨hdim, Or.inr hsgn⟩) e ⟨γ, hγN⟩
      rwa [show ffTheta hQ (Or.inr ⟨hdim, Or.inr hsgn⟩) e ⟨γ, hγN⟩ = x from hθ] at hind
    · refine ff_theta_back_right hL.1 hQ hdim hsgn e hS.1 hγS (fun _ => hθ) ?_
      intro q hq
      obtain ⟨n, p, hp, hqp⟩ := hcl q hq
      exact ⟨n, p, by rwa [ff_thetaImg_cap_eq hQ hdim hsgn e fr hPfr], hqp⟩

theorem ff_asc82OutCosets : Asc82OutCosets := by
  intro G _ _ L S B hL hS hB h1 hAut
  obtain ⟨V, _, _, _, Q, hQ, e, fr, hdim, hsgn, hBfr, hPfr⟩ :=
    ff_exists_model_P1 hL (ff_sylow_inf_normalizer hS) hB
  exact ff_outCosets_of_model hL hS hB h1 hAut hQ hdim hsgn e fr hBfr hPfr

end CFSG.OddStandard.SmallF3.Omega

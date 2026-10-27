module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutAll
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutAlpha
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrInnerY
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OddCoreBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

@[expose] def Asc82OmegaPlusAutInvolutions : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate), Module.finrank (ZMod 3) V = 8 →
      quadSign Q = 1 → ∀ α : MulAut (omegaProj hQ), α * α = 1 →
        (¬ ∃ p : omegaProj hQ, α = MulAut.conj p) →
          ∃ (β : MulAut (omegaProj hQ)) (x : OGroup Q), x * x = 1 ∧ x ∉ omegaGroup hQ ∧
            β⁻¹ * α * β = MulAut.conjNormal (toProj Q x)

theorem asc82OmegaPlusOuter_of_autInvolutions (h : Asc82OmegaPlusAutInvolutions) :
    Asc82OmegaPlusOuter := by
  intro G _ _ Y hY s hs hsN hsout
  obtain ⟨V, i1, i2, i3, Q, hQ, hdim, hσ, ⟨e⟩⟩ := isOmegaStar_of_lieModel_plus hY.2
  letI := i1
  letI := i2
  letI := i3
  have hρ := oddCentralCover_quotient_oddCore hY.1.1 e
  have hss : s * s = 1 := by
    rw [← pow_two]
    exact hs ▸ pow_orderOf_eq_one s
  have hσ2 : conjAut Y hss hsN * conjAut Y hss hsN = 1 := conjAut_mul_self Y hss hsN
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk' (oddCore ↥Y))).ker = oddCore ↥Y := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hker' : ∀ n ∈ (e.toMonoidHom.comp (QuotientGroup.mk' (oddCore ↥Y))).ker,
      conjAut Y hss hsN n ∈ (e.toMonoidHom.comp (QuotientGroup.mk' (oddCore ↥Y))).ker := by
    intro n hn
    rw [hker] at hn ⊢
    exact map_oddCore_le (conjAut Y hss hsN) ⟨n, hn, rfl⟩
  obtain ⟨α, hα, hαα⟩ := exists_induced_aut hρ.surjective hσ2 hker'
  have hinner : ¬ ∃ p : omegaProj hQ, α = MulAut.conj p := by
    rintro ⟨p, hp⟩
    obtain ⟨y₀, hy₀⟩ := exists_inner_of_conj hρ hY.1.1.1.commutator_eq_top hα hp
    apply hsout
    refine ⟨(y₀ : G), y₀.2, (y₀ : G)⁻¹ * s, ?_, by group⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := congrArg Subtype.val (hy₀ ⟨y, hy⟩)
    change s * y * s⁻¹ = (y₀ : G) * y * (y₀ : G)⁻¹ at h1
    calc y * ((y₀ : G)⁻¹ * s) = (y₀ : G)⁻¹ * ((y₀ : G) * y * (y₀ : G)⁻¹) * s := by group
      _ = (y₀ : G)⁻¹ * (s * y * s⁻¹) * s := by rw [h1]
      _ = ((y₀ : G)⁻¹ * s) * y := by group
  obtain ⟨β, x, hxx, hxΩ, hβ⟩ := h V Q hQ hdim hσ α hαα hinner
  have hdata : OuterData ↥(omegaProj hQ) α := by
    refine OuterData.of_conj β ?_
    rw [hβ]
    exact outerData_of_involution hQ hdim hσ hxx hxΩ
  exact exists_outer_of_outerData Y _ hρ hss hsN α hα hdata

end CFSG.OddStandard.SmallF3.Omega

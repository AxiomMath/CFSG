module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2CosetDefs
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2CosetLift
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2CosetLang
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2CosetB
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2KillRoot
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Cube
import CFSG.HardMathSupport.Timmesfeld.LangTorus.AlgebraicZMod
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Reduce

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus

section Coset

set_option linter.unusedSectionVars false


theorem d4t2CosetPart_of_residuals (hC : D4T2CentralTorus) (hT : D4T2CubeToral)
    : D4T2CosetPart := by
  have hU := @d4t2KernelRootUnip_holds
  intro L _ _ p₀ S hS hAlg l f hl hf hq hl3 h3 h3q a hdT hap hall Eh hEhM hab hcard hdE _ hR _ _
  classical
  by_cases hEM : Eh ≤ toralRootGroup .E6 L a
  swap
  · exact d4t2c_caseB hC S hS hAlg hl hf hq hl3 h3 h3q hdT hap hall hEhM hab hcard hdE hEM
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨hch, halg⟩ := S.exists_charP_isAlgebraic_zmod hAlg hl hf hq
  haveI := hch
  obtain ⟨g, hgC, hgE⟩ := hT hl hl3 halg hap hall Eh hEM hab hcard hdE
  obtain ⟨S', c, hΦ', hq', hcC, hΓ', hEc⟩ :=
    d4t2c_exists_conj_setup S hS hl hf hq hEhM hdE hgC hgE
  have hS' : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S'.D.q) ∧
      ∀ g, S'.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹ := by
    rw [hΦ', hq']
    exact hS
  have hAlg' : S'.IsAlgebraic := by
    show ∀ x : L, ∃ n : ℕ, 0 < n ∧ x ^ (S'.D.q ^ n) = x
    rw [hq']
    exact hAlg
  have hq'' : S'.D.q = l ^ f := hq'.trans hq
  have hcomm : Commute c (rootDiagUnit .E6 a) :=
    (mul_inv_eq_iff_eq_mul.1 (mem_toralCentralizer.1 hcC).2).symm
  have hcd : c * rootDiagUnit .E6 a * c⁻¹ = rootDiagUnit .E6 a := by
    rw [hcomm.eq, mul_inv_cancel_right]
  obtain ⟨A, hAdef⟩ : ∃ A : Subgroup (ModGL Tag.E6 L),
      A = Eh.map (MulAut.conj c⁻¹).toMonoidHom := ⟨_, rfl⟩
  have hmemA : ∀ y, y ∈ A ↔ c * y * c⁻¹ ∈ Eh := fun y => by
    rw [hAdef, Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
  have hAT : A ≤ S'.D.torus := fun y hy => by
    have h := hEc _ ((hmemA y).1 hy)
    rwa [show c⁻¹ * (c * y * c⁻¹) * c = y by group] at h
  have hab' : IsElemAbelian 3 A := by
    rw [hAdef]
    exact hab.map _
  have hcard' : Nat.card A = 3 ^ 3 := by
    rw [hAdef, Subgroup.card_map_of_injective (f := (MulAut.conj c⁻¹).toMonoidHom)
      (MulAut.conj c⁻¹).injective, hcard]
  have hdA : rootDiagUnit .E6 a ∈ A := (hmemA _).2 (by rw [hcd]; exact hdE)
  have hroot : ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot .E6 γ →
      ¬ ∀ b : Fin Tag.E6.rank → Lˣ, rootDiagUnit .E6 b ∈ A → rootChar b γ = 1 := by
    intro γ hγ hkill
    obtain ⟨u, huΓ, hu1, hul, hucomm⟩ := hU S' hS' hAlg' hl hf hq'' hl3 A hAT γ hγ hkill
    have hu₀1 : c * u * c⁻¹ ≠ 1 := fun h => hu1 (by
      calc u = c⁻¹ * (c * u * c⁻¹) * c := by group
        _ = 1 := by rw [h]; group)
    have hu₀l : (c * u * c⁻¹) ^ l = 1 := by rw [conj_pow, hul, mul_one, mul_inv_cancel]
    obtain ⟨ε, hεE, hεR⟩ := hR (Subgroup.zpowers (c * u * c⁻¹))
      (Subgroup.zpowers_le.2 ((hΓ' u).1 huΓ)) (fun h => hu₀1 (Subgroup.zpowers_eq_bot.1 h))
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hu₀l hu₀1, pow_one]))
    apply hεR
    rw [MonoidHom.map_zpowers]
    refine congrArg Subgroup.zpowers ?_
    have h := hucomm (c⁻¹ * ε * c) ((hmemA _).2 (by
      rw [show c * (c⁻¹ * ε * c) * c⁻¹ = ε by group]
      exact hεE))
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc ε * (c * u * c⁻¹) * ε⁻¹ = c * (c⁻¹ * ε * c * u) * c⁻¹ * ε⁻¹ := by group
      _ = c * (u * (c⁻¹ * ε * c)) * c⁻¹ * ε⁻¹ := by rw [h]
      _ = c * u * c⁻¹ := by group
  obtain ⟨ε, hεA, hεZ, y, hyΓ, hyd, hyε, hyM⟩ :=
    d4t2c_toral hC S' hS' hAlg' hl hf hq'' hl3 h3 h3q hap hall hAT hab' hcard' hdA hroot
  have hε₀E : c * ε * c⁻¹ ∈ Eh := (hmemA ε).1 hεA
  have hε₀Z : c * ε * c⁻¹ ∉ Subgroup.zpowers (rootDiagUnit .E6 a) := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    refine hεZ (Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩)
    have e1 : ε = c⁻¹ * (c * ε * c⁻¹) * c := by group
    rw [e1, ← hk, ((hcomm.zpow_right k).inv_left).eq, inv_mul_cancel_right]
  have hy₀d : Commute (c * y * c⁻¹) (rootDiagUnit .E6 a) :=
    (hcomm.mul_left hyd).mul_left hcomm.inv_left
  have hy₀ε : c * ε * c⁻¹ * (c * y * c⁻¹) = c * y * c⁻¹ * (c * ε * c⁻¹) := by
    calc c * ε * c⁻¹ * (c * y * c⁻¹) = c * (ε * y) * c⁻¹ := by group
      _ = c * (y * ε) * c⁻¹ := by rw [hyε]
      _ = c * y * c⁻¹ * (c * ε * c⁻¹) := by group
  have hy₀M : c * y * c⁻¹ ∉ toralRootGroup .E6 L a := fun h =>
    hyM ((Subgroup.mem_normalizer_iff.1 (toralCentralizer_le_normalizer a hcC) y).2 h)
  have hFE : Subgroup.zpowers (rootDiagUnit .E6 a) ⊔ Subgroup.zpowers (c * ε * c⁻¹) ≤ Eh :=
    sup_le (Subgroup.zpowers_le.2 hdE) (Subgroup.zpowers_le.2 hε₀E)
  have hFC : Subgroup.zpowers (rootDiagUnit .E6 a) ⊔ Subgroup.zpowers (c * ε * c⁻¹) ≤
      Subgroup.centralizer {c * y * c⁻¹} :=
    sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hy₀d.eq.symm))
      (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hy₀ε))
  refine ⟨_, hFE, KSNotAll24.relIndex_eq_three hFE hcard
    (KSNotAll24.card_zpowers_sup_zpowers (hab.comm hdE hε₀E) (d4t2_rootDiagUnit_ne_one hall)
      (hab.2 _ hdE) (hab.2 _ hε₀E) hε₀Z), Subgroup.mem_sup_left (Subgroup.mem_zpowers _),
    c * y * c⁻¹, ⟨(hΓ' y).1 hyΓ, Subgroup.mem_centralizer_iff.2 fun h hh =>
      Subgroup.mem_centralizer_singleton_iff.1 (hFC hh)⟩, hy₀M⟩

theorem d4t2CosetPart_of_centralTorus
    (hC : D4T2CentralTorus) : D4T2CosetPart :=
  d4t2CosetPart_of_residuals hC d4t2CubeToral_holds

end Coset

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

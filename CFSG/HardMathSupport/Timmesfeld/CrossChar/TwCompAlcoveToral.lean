module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompKac
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcMonomial
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

theorem exists_conj_rootDiagUnit_normal
    {τ : Tag} (K : KacData τ) (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : Lˣ} (hζ : orderOf ζ = p)
    {u : ModGL τ L} (hu : u ∈ adjointGroup τ L) (hup : u ^ p = 1) :
    ∃ g ∈ adjointGroup τ L, ∃ μ : Fin τ.rank → ℤ, K.IsNormal p μ ∧
      g⁻¹ * u * g = rootDiagUnit τ (fun i => ζ ^ μ i) := by
  have hτ' : τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with rfl | rfl | rfl | rfl <;> simp
  have hmon : MonomialToralAt τ p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five hτ' hp hp2
  obtain ⟨g₁, hg₁, hg₁t⟩ :=
    exists_conj_torusGroup_of_pow_eq_one (ℓ := 2) hp hmon (Ne.symm hp2) halg hu hup
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hg₁t
  have hconj : (g₁⁻¹ * u * g₁) ^ p = 1 := by
    simpa using conj_pow_eq_one' (p := p) (c := g₁⁻¹) hup
  have hdap : rootDiagUnit τ (a ^ p) = 1 := by
    rw [← rootDiagUnit_pow, ← ha]
    exact hconj
  have hap_eq : a ^ p = 1 :=
    rootDiagUnit_injective (τ := τ) (K := L) (by rw [hdap, rootDiagUnit_one])
  have hap : ∀ i, a i ^ p = 1 := fun i => by simpa using congrFun hap_eq i
  have hζprim : IsPrimitiveRoot (ζ : L) p :=
    IsPrimitiveRoot.iff_orderOf.2 (by rw [orderOf_units]; exact hζ)
  obtain ⟨w, μ, hμ, hchar⟩ := K.exists_weyl_normal hp.pos hζprim a hap
  have hd : rootDiagUnit τ (fun i => ζ ^ μ i) =
      canonicalRep (coxeterSystem τ) L w * rootDiagUnit τ a *
        (canonicalRep (coxeterSystem τ) L w)⁻¹ := by
    refine (rootDiagUnit_eq_conj_canonicalRep_iff (K := L) _ a w).2 fun v => ?_
    rw [KacData.rootChar_eq_zpow, ← hchar v]
  have hn : canonicalRep (coxeterSystem τ) L w ∈ adjointGroup τ L :=
    canonicalRep_mem_adjointGroup _ L w
  refine ⟨g₁ * (canonicalRep (coxeterSystem τ) L w)⁻¹,
    mul_mem hg₁ (inv_mem hn), μ, hμ, ?_⟩
  calc (g₁ * (canonicalRep (coxeterSystem τ) L w)⁻¹)⁻¹ * u *
        (g₁ * (canonicalRep (coxeterSystem τ) L w)⁻¹)
      = canonicalRep (coxeterSystem τ) L w * (g₁⁻¹ * u * g₁) *
          (canonicalRep (coxeterSystem τ) L w)⁻¹ := by group
    _ = canonicalRep (coxeterSystem τ) L w * rootDiagUnit τ a *
          (canonicalRep (coxeterSystem τ) L w)⁻¹ := by rw [ha]
    _ = rootDiagUnit τ (fun i => ζ ^ μ i) := hd.symm

end CFSG.HardMathSupport.Timmesfeld.CrossChar

module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcLangNormalizer
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Inner
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  (langCentralizer_le_normalizer_rationalComponent)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  (fixSubgroup_congr components_of_langSetup map_fixSubgroup_eq_of_conj)

theorem compNormal_of_congr {S G : Type*} [Group S] [Group G] (e : S ≃* G) (β : MulAut S)
    (h : CompNormal (MulAut.congr e β)) : CompNormal β := by
  intro J hJ
  have hfix : fixSubgroup (MulAut.congr e β) = (fixSubgroup β).map (e : S →* G) :=
    fixSubgroup_congr e β
  have hJ' : IsComponentOf (J.map (e : S →* G)) (fixSubgroup (MulAut.congr e β)) := by
    rw [hfix]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hJ
  have hN := Subgroup.le_normalizer_iff.1 (h _ hJ')
  refine Subgroup.le_normalizer_iff.2 fun g hg k hk => ?_
  have hg' : (e : S →* G) g ∈ fixSubgroup (MulAut.congr e β) := by
    rw [hfix]
    exact Subgroup.mem_map_of_mem _ hg
  have h1 := hN _ hg' _ (Subgroup.mem_map_of_mem (e : S →* G) hk)
  rw [← map_inv, ← map_mul, ← map_mul] at h1
  exact (Subgroup.mem_map_iff_mem (f := (e : S →* G)) e.injective).1 h1


theorem compNormal_of_langSetup {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) (hp : p.Prime) {C : Type} [Group C] [Finite C]
    (ι : C →* ModGL τ L) (hι : Function.Injective ι) (hrange : ι.range = S.Γ) (β : MulAut C)
    {a : Fin τ.rank → Lˣ}
    (hβ : ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hW : rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a) : CompNormal β := by
  intro K hK
  obtain ⟨i, -, hKR⟩ := components_of_langSetup S hp ι hι hrange β hβ hT hap h1 hTame hK
  have hfix : (fixSubgroup β).map ι = S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} := by
    rw [map_fixSubgroup_eq_of_conj ι hι β _ hβ, hrange]
  have hN := langCentralizer_le_normalizer_rationalComponent S hT hW i
  refine Subgroup.le_normalizer_iff.2 fun g hg k hk => ?_
  have hg' : ι g ∈ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} := by
    rw [← hfix]
    exact Subgroup.mem_map_of_mem ι hg
  have hk' : ι k ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    rw [← hKR]
    exact Subgroup.mem_map_of_mem ι hk
  have h2 := (hN hg' (ι k)).1 hk'
  rw [← hKR, ← map_inv, ← map_mul, ← map_mul] at h2
  exact (Subgroup.mem_map_iff_mem hι).1 h2

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen

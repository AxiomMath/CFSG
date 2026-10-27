module

public import CFSG.RankThree.Lattice.SteinbergBIGenCharElem
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenD5SpinExport
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256j

public section
namespace CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.RankThree.Lattice CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement


theorem twoD_two_mem_rationalComponent
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ : ℕ} (S : LangSetup τ L p₀) (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (hk : twistKind S.ρ (rootCharHom a) i = .twoD)
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)) :
    ∀ g ∈ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i),
      g ∈ S.D.model → (∃ n : ℕ, g ^ 2 ^ n = 1) →
      g ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  classical
  have hTwo : CharP L 2 := inferInstance
  obtain ⟨r, e, m, hr, hchar, hm, z, eps, D, hq, he, hDe, hperf, hDs, hDt, hCart, hmap⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.exists_twoD_export_fixed
      S hτ hT i hk h5
  have hr2 : r = 2 := CharP.eq L hchar hTwo
  cases hr2
  haveI := hr
  have hrr := S.rationalRoots_eq_of_five_leT hT i h5
  let f := (MulAut.conj z⁻¹).toMonoidHom
  let P := D.orbitGroup.map (MulAut.conj z).toMonoidHom
  have hFix : D.orbitGroup ≤ D.fixedGroup.map (adjointGroup τ L).subtype := by
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, D.orbitGroup_le_adjointGroup hx⟩,
      D.orbitGroupC_le_fixedGroup hx, rfl⟩
  have hP : P ≤ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) ⊓ S.D.model := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp (hmap.symm ▸ hFix hx)
    have hxy' : z⁻¹ * y * z = x := by simpa using hxy
    have heq : z * x * z⁻¹ = y := by rw [← hxy']; group
    change z * x * z⁻¹ ∈ _
    rw [heq, hrr]
    exact hy
  have hPperf : ⁅P, P⁆ = P := by
    dsimp only [P]
    rw [← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hperf]
  have hPR := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256j.le_rationalComponent_of_perfect S i hP hPperf
  intro g hg hm ⟨n, hn⟩
  have hgf : f g ∈ D.fixedGroup.map (adjointGroup τ L).subtype := by
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨g, ⟨hrr ▸ hg, hm⟩, rfl⟩
  obtain ⟨v, hv, hvg⟩ := Subgroup.mem_map.mp hgf
  change (v : ModGL τ L) = f g at hvg
  have hvn : v ^ 2 ^ n = 1 := by
    apply Subtype.ext
    change (v : ModGL τ L) ^ 2 ^ n = 1
    rw [hvg]
    change (f g) ^ 2 ^ n = 1
    rw [← map_pow, hn, map_one]
  have hvC := D.mem_orbitGroupC_of_charElem hv hvn
  have hvO : (v : ModGL τ L) ∈ D.orbitGroup :=
    D.coe_mem_orbitGroup_of_mem_orbitGroupC hvC
  apply hPR
  refine Subgroup.mem_map.mpr ⟨v, hvO, ?_⟩
  change z * (v : ModGL τ L) * z⁻¹ = g
  rw [hvg]
  change z * (z⁻¹ * g * z) * z⁻¹ = g
  group

end CFSG.HardMathSupport.Timmesfeld.LangTorus

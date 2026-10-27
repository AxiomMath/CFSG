module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcLang
import CFSG.HardMathSupport.Timmesfeld.Steinberg.ToralCentralizerGenerated

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open CFSG.HardMathSupport.Timmesfeld.Steinberg (toralCentralizer_eq_toralRootGroup_of_stabilizer_le)


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
  {a : Fin τ.rank → Lˣ}

private theorem mem_normalizer_commutator_self {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    g ∈ Subgroup.normalizer ((⁅H, H⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
  rw [Subgroup.map_commutator, hg]

theorem toralRootGroup_le_normalizer_rationalRoots (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) :
    toralRootGroup τ L a ≤ Subgroup.normalizer
      (rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) : Set (ModGL τ L)) := by
  have hker := rho_mem_kernelRoots_of_mem_torus S hT
  refine sup_le (torusGroup_le_normalizer_rootSpan fun γ hγ =>
    (rationalRoots_subset_kernelRoots hker i hγ).1) (iSup₂_le fun α hα => ?_)
  by_cases hαi : α ∈ rationalRoots S.ρ (rootCharHom a) i
  · exact (le_iSup₂_of_le (f := fun β (_ : β ∈ rationalRoots S.ρ (rootCharHom a) i) =>
      rootSubgroup τ L β) α hαi le_rfl).trans (Subgroup.le_normalizer)
  ·
    have hαj : α ∈ rationalRoots S.ρ (rootCharHom a) ⟦⟨α, hα⟩⟧ := ⟨0, α, ⟨hα, rfl⟩, rfl⟩
    have hne : rationalRoots S.ρ (rootCharHom a) i ≠
        rationalRoots S.ρ (rootCharHom a) ⟦⟨α, hα⟩⟧ := fun h => hαi (h ▸ hαj)
    have hc := commute_rootSpan_rationalRoots hker S.frob.iform_eq hne
    have hle : rootSubgroup τ L α ≤
        rootSpan τ L (rationalRoots S.ρ (rootCharHom a) ⟦⟨α, hα⟩⟧) :=
      le_iSup₂_of_le (f := fun β (_ : β ∈ rationalRoots S.ρ (rootCharHom a) ⟦⟨α, hα⟩⟧) =>
        rootSubgroup τ L β) α hαj le_rfl
    refine hle.trans (le_trans ?_ (Subgroup.centralizer_le_normalizer _))
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hc x hx y hy).symm.eq.symm

theorem langCentralizer_le_normalizer_rationalComponent (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hW : rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a)
    (i : KernelComponent (rootCharHom a)) :
    S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} ≤
      Subgroup.normalizer (rationalComponent S.ρ S.Γ (rootCharHom a) i : Set (ModGL τ L)) := by
  have hΓ : S.Γ ≤ adjointGroup τ L :=
    (Subgroup.commutator_le_self S.D.model).trans inf_le_left
  intro g hg
  obtain ⟨hgΓ, hgc⟩ := Subgroup.mem_inf.1 hg
  have hgM : g ∈ toralRootGroup τ L a := by
    rw [← toralCentralizer_eq_toralRootGroup_of_stabilizer_le τ L a hW]
    exact Subgroup.mem_inf.2 ⟨hΓ hgΓ, hgc⟩
  have h1 := toralRootGroup_le_normalizer_rationalRoots S hT i hgM
  have h2 : g ∈ Subgroup.normalizer (S.Γ : Set (ModGL τ L)) := Subgroup.le_normalizer hgΓ
  exact mem_normalizer_commutator_self (Subgroup.inf_normalizer_le_normalizer_inf ⟨h1, h2⟩)

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

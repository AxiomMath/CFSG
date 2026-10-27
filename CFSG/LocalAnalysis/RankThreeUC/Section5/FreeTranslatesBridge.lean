module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.FreeTranslates
public import CFSG.LocalAnalysis.RankThreeUC.Section5.CanonicalBFixedHyperplane
import CFSG.LocalAnalysis.RankThreeUC.Section5.DeltaSemiregularity

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.FreeTranslates

open CFSG.LocalAnalysis.RankThreeUC

variable {G : Type} [Group G] [Finite G]

theorem regularConfig_of_counterexample {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ)
    (hK : ∀ s ∈ twoCoreCommutator T B, s ∈ Subgroup.normalizer ((⁅B, P⁆ : Subgroup G) : Set G) →
      ∀ E ∈ Delta p P ρ, E.map (MulAut.conj s).toMonoidHom = E) :
    RegularConfig (DeltaConjugationAction.act hc.faithfulBinaryIrreducibleAction.normal ρ)
      (twoCoreCommutator T B) B ⟨⁅B, P⁆, (CanonicalBFixedHyperplane.canonical hc).1⟩ := by
  have hP : P.Normal := hc.faithfulBinaryIrreducibleAction.normal
  obtain ⟨hD₀, -, huniq⟩ := CanonicalBFixedHyperplane.canonical hc
  have hBS : B ≤ Subgroup.normalizer (twoCoreCommutator T B : Set G) :=
    Subgroup.normalizer_commutator_ge_right _ B
  have hBD : B ≤ Subgroup.normalizer ((⁅B, P⁆ : Subgroup G) : Set G) := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.normalizer_commutator_ge_right _ B
  have hact : ∀ (g : G) (D : Delta p P ρ),
      DeltaConjugationAction.act hP ρ g D = D ↔ g ∈ Subgroup.normalizer ((D : Subgroup G) : Set G) := by
    intro g D
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← Subtype.coe_inj]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b hb s hs
    exact (Subgroup.mem_normalizer_iff.mp (hBS hb) s).mp hs
  · intro b hb
    exact (hact b _).mpr (hBD hb)
  · intro D
    obtain ⟨s, hs, hsD⟩ := DeltaTransitivity.transitive hc _ hD₀ D.1 D.2
    refine ⟨s, hs, Subtype.ext ?_⟩
    exact hsD.symm
  · intro s hs hsD
    have hsN := (hact s _).mp hsD
    refine Equiv.ext fun E => Subtype.ext ?_
    exact hK s hs hsN E.1 E.2
  · intro b hb hb1 D hbD
    by_contra hne
    exact DeltaSemiregularity.semiregular hc b hb hb1 D.1 D.2
      (fun h => hne (Subtype.ext h)) ((hact b D).mp hbD)

theorem eq_one_of_mem_all_Delta {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) {x : G} (hx : ∀ D ∈ Delta p P ρ, x ∈ D) :
    x = 1 := by
  classical
  have htop := (isInternal_hyperplane_fixedSubmodule_of_binary_rank_counterexample hc).submodule_iSup_eq_top
  apply hc.faithfulBinaryIrreducibleAction.faithful
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ ⨆ D : ↥(Delta p P ρ), fixedSubmodule ρ (D : Subgroup G) := by
    rw [htop]
    trivial
  rw [map_one]
  refine Submodule.iSup_induction _ (motive := fun v => ρ x v = v) hv ?_ ?_ ?_
  · intro D w hw
    exact (QuadraticSetConjugationTransport.mem_fixedSubmodule_iff ρ _ w).mp hw x (hx D D.2)
  · simp
  · intro a b ha hb
    rw [map_add, ha, hb]

end CFSG.LocalAnalysis.RankThreeUC.Section5.FreeTranslates

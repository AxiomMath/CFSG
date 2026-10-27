module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.IsInternalHyperplaneFixedSubmoduleOfBinaryRankCounterexample
public import CFSG.LocalAnalysis.RankThreeUC.Section5.DeltaConjugationAction
public import CFSG.GroupTheory.CoprimeActionSupport.IndependentOrbitSumFixedProjection

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.NormalizerFixedSpaceBTrivial

open CFSG.LocalAnalysis.RankThreeUC.Section5 CFSG.LocalAnalysis.RankThreeUC.Section5.DeltaConjugationAction

variable {G : Type} [Group G] [Finite G]

theorem fixes {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ)
    (E : Subgroup G) (hE : E ∈ Delta p P ρ)
    (hBN : B ≤ Subgroup.normalizer (E : Set G))
    (w : V) (hw : w ∈ fixedSubmodule ρ E) (hw0 : w ≠ 0)
    (hNfix : ∀ s ∈ twoCoreCommutator T B, s ∈ Subgroup.normalizer (E : Set G) → ρ s w = w) :
    ∀ b ∈ B, ρ b w = w := by
  classical
  have hP : P.Normal := hc.faithfulBinaryIrreducibleAction.normal
  have hint := isInternal_hyperplane_fixedSubmodule_of_binary_rank_counterexample hc
  set I := ↥(Delta p P ρ) with hI
  let U : I → Submodule (ZMod 2) V := fun D => fixedSubmodule ρ D.1
  have hind : iSupIndep U := hint.submodule_iSupIndep
  have hconj : ∀ (g : G) (D : I), (act (p := p) hP ρ g D).1 = D.1 ↔ g ∈ Subgroup.normalizer (D.1 : Set G) := by
    intro g D
    rw [apply_eq]
    exact Iff.symm (Subgroup.mem_normalizer_iff_map_conj_eq)
  let Es : I := ⟨E, hE⟩
  letI : MulAction (twoCoreCommutator T B) I := MulAction.compHom I ((act (p := p) hP ρ).comp (twoCoreCommutator T B).subtype)
  have hsmul : ∀ (s : twoCoreCommutator T B) (D : I), s • D = act (p := p) hP ρ s.1 D := fun _ _ => rfl
  let σ : Representation (ZMod 2) (twoCoreCommutator T B) V := ρ.comp (twoCoreCommutator T B).subtype
  have hmap : ∀ (s : twoCoreCommutator T B) (D : I), (U D).map (σ s) = U (s • D) := by
    intro s D
    exact fixed_map hP ρ s.1 D
  obtain ⟨v, hvfix, hvw⟩ := CFSG.GroupTheory.CoprimeActionSupport.IndependentOrbitSumFixedProjection.exists_fixed_projection
    σ U hind hmap Es w hw hw0 (fun s hs => by
      apply hNfix s.1 s.2
      exact (hconj s.1 Es).1 (by rw [← hsmul]; exact congrArg Subtype.val hs))
  have hvS : v ∈ fixedSubmodule ρ (twoCoreCommutator T B) := by
    rw [QuadraticSetConjugationTransport.mem_fixedSubmodule_iff]
    intro n hn
    exact hvfix ⟨n, hn⟩
  have hBv : ∀ b ∈ B, ρ b v = v := fun b hb =>
    (characteristic_actor_fixes_commutator_fixedSpace_and_centralizes_odd_invariants hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction B le_rfl (fun φ => by
      simp [Subgroup.subgroupOf_self])).1 b hb v hvS
  intro b hb
  have hbE : act (p := p) hP ρ b Es = Es :=
    Subtype.ext ((hconj b Es).2 (hBN hb))
  have hstable : ∀ x ∈ (⨆ j ∈ {j : I | j ≠ Es}, U j), ρ b x ∈ (⨆ j ∈ {j : I | j ≠ Es}, U j) := by
    intro x hx
    have : (⨆ j ∈ {j : I | j ≠ Es}, U j).map (ρ b) ≤ (⨆ j ∈ {j : I | j ≠ Es}, U j) := by
      rw [Submodule.map_iSup]
      refine iSup_le fun j => ?_
      rw [Submodule.map_iSup]
      refine iSup_le fun hj => ?_
      have h1 : (U j).map (ρ b) = U (act (p := p) hP ρ b j) := fixed_map hP ρ b j
      rw [h1]
      refine le_iSup₂_of_le (act (p := p) hP ρ b j) ?_ le_rfl
      intro h
      apply hj
      have : act (p := p) hP ρ b j = act (p := p) hP ρ b Es := h.trans hbE.symm
      exact (act (p := p) hP ρ b).injective this
    exact this ⟨x, hx, rfl⟩
  have hbw : ρ b w ∈ U Es := by
    have h1 : (U Es).map (ρ b) = U (act (p := p) hP ρ b Es) := fixed_map hP ρ b Es
    rw [hbE] at h1
    rw [← h1]; exact ⟨w, hw, rfl⟩
  have h2 : ρ b w - w ∈ (⨆ j ∈ {j : I | j ≠ Es}, U j) := by
    have h3 := Submodule.sub_mem _ (hstable _ hvw) hvw
    have h4 : ρ b w - w = -(ρ b (v - w) - (v - w)) := by
      rw [map_sub, hBv b hb]; abel
    rw [h4]; exact Submodule.neg_mem _ h3
  have hd : Disjoint (U Es) (⨆ j ∈ {j : I | j ≠ Es}, U j) := hind Es
  have := Submodule.disjoint_def.1 hd _ (Submodule.sub_mem _ hbw hw) h2
  exact sub_eq_zero.1 this

end CFSG.LocalAnalysis.RankThreeUC.Section5.NormalizerFixedSpaceBTrivial

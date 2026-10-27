module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.HyperplaneOrbitStructure
public import CFSG.LinearAlgebra.CoprimeActions.CyclicOrbitGeneratedCentralizerScalar
public import CFSG.LocalAnalysis.RankThreeUC.Section5.AmbientConjugateGenerationToSstar.AmbientConjugateGenerationToSstar
public import CFSG.GroupTheory.AutomorphismAction.FixedSubgroup
public import CFSG.LocalAnalysis.RankThreeUC.Section5.OddExponentCommutatorImage

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.AbelianImageCentralizerScalar

open CFSG.LocalAnalysis.RankThreeUC.Section5 CFSG.LocalAnalysis.RankThreeUC.Section5.FaithfulPImageVocabulary

variable {G : Type} [Group G] [Finite G]

theorem scalar {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ)
    (hTab : IsMulCommutative (T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal))) (he : Odd e) :
    ∀ φ ∈ (T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal)) ⊓
        Subgroup.centralizer (Bstar P B : Set (MulAut P)),
      ∃ k : ℤ, ∀ x : P, φ x = x ^ k := by
  have hP : P.Normal := hc.faithfulBinaryIrreducibleAction.normal
  have h51 := hc.oddPrimeClassTwoAction
  have hset := h51.setting
  obtain ⟨_, ⟨hQne, hcomm⟩, _, _, _, ⟨hgenP, hirr⟩⟩ := cyclic_actor_and_hyperplane_transitivity_and_irreducible_commutator_action hc
  have hPab : ∀ x y : P, x * y = y * x := by
    haveI : (⁅P, P⁆ : Subgroup G).Normal := Subgroup.commutator_normal P P
    have hle : (⁅P, P⁆ : Subgroup G) ≤ P := Subgroup.commutator_le_left P P
    have hbot : (⁅P, P⁆ : Subgroup G) = ⊥ := by
      by_contra hne
      have hPP := hirr _ hle (by rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]; exact le_top)
        (by rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]; exact le_top) hne
      have h2 := hset.class_le_two
      rw [hPP] at h2
      exact hne h2
    intro x y
    have := Subgroup.commutator_mem_commutator x.2 y.2
    rw [hbot, Subgroup.mem_bot, commutatorElement_def] at this
    apply Subtype.ext
    simpa [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] using this
  intro φ hφ
  set Q : Subgroup G := P ⊓ Subgroup.centralizer (B : Set G) with hQdef
  have hQP : Q ≤ P := inf_le_left
  have hgen := CFSG.LocalAnalysis.RankThreeUC.Section5.AmbientConjugateGenerationToSstar.generated hP hQP hgenP
  have hcyc : IsCyclic (Q.subgroupOf P) := by
    obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 h51.actor_ne_bot
    have hbB : (b : G) ∈ B := b.2
    have hbne : (b : G) ≠ 1 := fun h => hb1 (Subtype.ext h)
    have hc1 := h51.cyclic_centralizer b.1 hbB hbne
    have hQeq : Q = P ⊓ Subgroup.centralizer ({b.1} : Set G) := (hcomm b.1 hbB hbne).symm
    rw [← hQeq] at hc1
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hQP).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hQP).symm.surjective
  have hSH : Sstar P T B ≤ T.map (conjOnP P hP) := by
    rintro _ ⟨⟨g, hg⟩, hgX, rfl⟩
    have hgT : g ∈ T := OddExponentCommutatorImage.xs_le h51 he (Subgroup.mem_subgroupOf.mp hgX)
    exact ⟨g, hgT, rfl⟩
  have hφS : ∀ g ∈ Sstar P T B, φ * g = g * φ := by
    intro g hg
    have := hTab.is_comm.comm (⟨φ, hφ.1⟩ : T.map (conjOnP P hP)) ⟨g, hSH hg⟩
    exact congrArg Subtype.val this
  have hφBc : ∀ g ∈ Bstar P B, φ * g = g * φ := by
    intro g hg
    exact ((Subgroup.mem_centralizer_iff.mp hφ.2) g hg).symm
  have hBG := hφBc
  have hQφ : (Q.subgroupOf P).map (φ : MulAut P).toMonoidHom = Q.subgroupOf P := by
    refine CFSG.GroupTheory.AutomorphismAction.map_fixedSubgroup_eq
      (Bstar P B) (Q.subgroupOf P) ?_ _ ?_
    · intro x
      rw [Subgroup.mem_subgroupOf, hQdef, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
      constructor
      · rintro ⟨_, hx⟩ a
        obtain ⟨y, hy, hya⟩ := Subgroup.mem_map.mp a.2
        have hyB : (y : G) ∈ B := Subgroup.mem_subgroupOf.mp hy
        have hay : (a : MulAut P) = P.normalizerMonoidHom y := hya.symm
        apply Subtype.ext
        rw [hay]
        show (y : G) * (x : G) * (y : G)⁻¹ = x
        rw [hx _ hyB, mul_inv_cancel_right]
      · intro hx
        refine ⟨x.2, ?_⟩
        intro h hh
        have hN : h ∈ Subgroup.normalizer (P : Set G) := hset.normB hh
        let a : Bstar P B := ⟨P.normalizerMonoidHom ⟨h, hN⟩,
          Subgroup.mem_map.mpr ⟨⟨h, hN⟩, Subgroup.mem_subgroupOf.mpr hh, rfl⟩⟩
        have h2 := congrArg Subtype.val (hx a)
        have h3 : h * (x : G) * h⁻¹ = x := h2
        rw [mul_inv_eq_iff_eq_mul] at h3
        exact h3
    · intro a
      exact hφBc a.1 a.2
  letI : CommGroup P := { (inferInstance : Group P) with mul_comm := hPab }
  haveI : IsCyclic (Q.subgroupOf P) := hcyc
  have key := CFSG.LinearAlgebra.CoprimeActions.CyclicOrbitGeneratedCentralizerScalar.scalar (A := P)
    (Sstar P T B) (Q.subgroupOf P) ?_ φ ?_ hQφ
  · exact key
  · convert hgen using 3
    ext x
    exact ⟨fun ⟨h, hh, hx⟩ => ⟨⟨h, hh⟩, hx⟩, fun ⟨h, hx⟩ => ⟨h.1, h.2, hx⟩⟩
  · intro h hh
    exact hφS h hh

end CFSG.LocalAnalysis.RankThreeUC.Section5.AbelianImageCentralizerScalar

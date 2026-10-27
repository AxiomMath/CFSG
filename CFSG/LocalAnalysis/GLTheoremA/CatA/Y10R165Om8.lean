module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om7
public import CFSG.HardMathSupport.Dickson.I271.Support.EngineKL
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2711
public import CFSG.HardMathSupport.Solomon.Coordinator.L5Conj
public import CFSG.LocalAnalysis.GL83PartI.I_22_6
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input319

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks QuadraticMap Polynomial
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

namespace OmEngine

variable {F V : Type} [Field F] [Finite F] [CharP F 2] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V}

variable {p : ℕ}

theorem commute_of_mem_supportedFixedDerived {x g : V ≃ₗ[F] V}
    (hg : g ∈ supportedFixedDerived Q x) : Commute g x :=
  (Subgroup.mem_centralizer_iff.mp
    (Subgroup.mem_inf.mp (supportedFixedDerived_le_isometryCentralizer hg)).2 x
    (Set.mem_singleton x)).symm

theorem subtype_mem_orthImage_iff {Ã : Subgroup ↥(orthDerived Q)} {x : ↥(orthDerived Q)} :
    x ∈ Ã ↔ (x : V ≃ₗ[F] V) ∈ orthImage Ã := by
  rw [show orthImage Ã = Ã.map (orthDerived Q).subtype from rfl, Subgroup.mem_map]
  exact ⟨fun h => ⟨x, h, rfl⟩, by rintro ⟨y, hy, hxy⟩; rwa [← Subtype.ext hxy]⟩

theorem card_zpowers_orthDerived {Ã : Subgroup ↥(orthDerived Q)} [Fintype ↥(orthImage Ã)]
    (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p (orthImage Ã))
    (t : Hyperplane (orthImage Ã) p → ↥(orthImage Ã))
    (ht : ∀ D, t D ∉ D.1) {D : Hyperplane (orthImage Ã) p}
    (hD : blockSpace (orthImage Ã) D.1 ≠ ⊥)
    (hxH : blockEnd (orthImage Ã) hp hpF hA t ht D ∈ orthDerived Q) :
    Nat.card (Subgroup.zpowers (⟨blockEnd (orthImage Ã) hp hpF hA t ht D, hxH⟩ :
      ↥(orthDerived Q))) = p := by
  rw [Nat.card_zpowers, Subgroup.orderOf_mk]
  exact CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks.orderOf_blockEnd
    (orthImage Ã) hp hpF hA t ht hD

theorem card_closure_pair_orthDerived {Ã : Subgroup ↥(orthDerived Q)} [Fintype ↥(orthImage Ã)]
    (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p (orthImage Ã))
    (t : Hyperplane (orthImage Ã) p → ↥(orthImage Ã))
    (ht : ∀ D, t D ∉ D.1) {D E : Hyperplane (orthImage Ã) p}
    (hDE : D ≠ E) (hD : blockSpace (orthImage Ã) D.1 ≠ ⊥) (hE : blockSpace (orthImage Ã) E.1 ≠ ⊥)
    (hxD : blockEnd (orthImage Ã) hp hpF hA t ht D ∈ orthImage Ã)
    (hxE : blockEnd (orthImage Ã) hp hpF hA t ht E ∈ orthImage Ã)
    (hxDH : blockEnd (orthImage Ã) hp hpF hA t ht D ∈ orthDerived Q)
    (hxEH : blockEnd (orthImage Ã) hp hpF hA t ht E ∈ orthDerived Q) :
    Nat.card (Subgroup.closure
      ({⟨blockEnd (orthImage Ã) hp hpF hA t ht D, hxDH⟩,
        ⟨blockEnd (orthImage Ã) hp hpF hA t ht E, hxEH⟩} : Set ↥(orthDerived Q))) = p ^ 2 := by
  set xD := blockEnd (orthImage Ã) hp hpF hA t ht D
  set xE := blockEnd (orthImage Ã) hp hpF hA t ht E
  have h := CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks.card_closure_pair_blockEnd
    (orthImage Ã) hp hpF hA t ht hDE hD hE hxD hxE
  have hmap : (Subgroup.closure
      ({⟨xD, hxDH⟩, ⟨xE, hxEH⟩} : Set ↥(orthDerived Q))).map (orthDerived Q).subtype =
      Subgroup.closure ({xD, xE} : Set (V ≃ₗ[F] V)) := by
    rw [MonoidHom.map_closure]
    congr 1
    simp
  rw [← h, ← hmap, Subgroup.card_map_of_injective (orthDerived Q).subtype_injective]

theorem pRank_comap_mulEquiv {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    {q : ℕ} (hq : 1 < q) (e : X ≃* Y) (T : Subgroup Y) :
    CFSG.Open.pRank q (T.comap e.toMonoidHom) = CFSG.Open.pRank q T := by
  have h1 : CFSG.Open.pRank q ((T.comap e.toMonoidHom).map e.toMonoidHom) =
      CFSG.Open.pRank q (T.comap e.toMonoidHom) :=
    CFSG.LocalAnalysis.GLTheoremB.pRank_map_eq_of_injective hq e.toMonoidHom e.injective _
  rw [Subgroup.map_comap_eq_self_of_surjective e.surjective] at h1
  exact h1.symm

section Support

variable (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] {p : ℕ}

theorem othersSpace_blockEnd_eq_blockSpace (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) (hQ : (polarBilin Q).Nondegenerate)
    (hQinv : ∀ a : ↥A, ∀ v : V, Q ((a : V ≃ₗ[F] V) v) = Q v)
    (hB : ∀ a : ↥A, ∀ u v : V,
      polarBilin Q ((a : V ≃ₗ[F] V) u) ((a : V ≃ₗ[F] V) v) = polarBilin Q u v)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) (D : Hyperplane A p) :
    othersSpace (blockEnd A hp hpF hA t ht D).toLinearMap (X - 1) = blockSpace A D.1 := by
  set x : V ≃ₗ[F] V := blockEnd A hp hpF hA t ht D with hx
  have hxodd : OddOrderIsometry Q p x :=
    blockEnd_oddOrderIsometry A hp hpF hA hQ hQinv t ht D
  set K : Submodule F V := LinearMap.ker (projBlock A hp hpF hA D) with hK
  have hKfix : K = fixedSpace x := (fixedSpace_blockEnd_eq_ker_projBlock A hp hpF hA t ht D).symm
  have hKnd : (polarBilin (Q.comp K.subtype)).Nondegenerate := by
    rw [hKfix]
    exact hxodd.polarBilin_fixed_nondegenerate
  have hcompl := CFSG.RankThree.PartOne.KCOrthogonal.isCompl_orthPerp hKnd
  have hdim : Module.finrank F ↥(orthPerp Q K) = Module.finrank F ↥(blockSpace A D.1) := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hcompl
    have h2 := finrank_ker_projBlock_add_finrank_blockSpace A hp hpF hA D
    exact Nat.add_left_cancel (h1.trans h2.symm)
  have hle : blockSpace A D.1 ≤ orthPerp Q K := by
    intro v hv
    rw [mem_orthPerp]
    intro r hr
    rw [QuadraticMap.polar_comm]
    exact blockSpace_ker_orthogonal A hp hpF hA (polarBilin Q) hB D hv hr
  have hOK : orthPerp Q K = blockSpace A D.1 :=
    (Submodule.eq_of_le_of_finrank_eq hle hdim.symm).symm
  rw [← CFSG.RankThree.PartOne.KCOrthogonalD4.orthPerp_fixedSpace hxodd, ← hKfix]
  exact hOK

end Support

theorem exists_mem_ne_of_three_le_card {α : Type*} [DecidableEq α] {S : Finset α} {D E : α}
    (hD : D ∈ S) (hE : E ∈ S) (hDE : D ≠ E) (h3 : 3 ≤ S.card) :
    ∃ G ∈ S, G ≠ D ∧ G ≠ E := by
  classical
  by_contra h
  push Not at h
  have hsub : S ⊆ ({D, E} : Finset α) := by
    intro x hx
    by_cases hxD : x = D
    · simp [hxD]
    · have hxE : x = E := by
        by_contra hxE
        exact hxE (h x hx hxD)
      simp [hxE]
  have hcard : S.card ≤ ({D, E} : Finset α).card := Finset.card_le_card hsub
  rw [Finset.card_pair hDE] at hcard
  omega

theorem othersSpace_le_range {W : Type} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {Q : QuadraticForm F W} {p : ℕ} {x : W ≃ₗ[F] W} (hx : OddOrderIsometry Q p x) :
    othersSpace x.toLinearMap (X - 1) ≤ LinearMap.range (x.toLinearMap - 1) := by
  set O := othersSpace x.toLinearMap (X - 1) with hO
  have hxO : ∀ v ∈ O, (x.toLinearMap - 1) v ∈ O := by
    intro v hv
    have h1 : x v ∈ O :=
      mem_othersSpace_of_apply (Subgroup.mem_centralizer_singleton_iff.mpr rfl) hv
    simpa using O.sub_mem h1 hv
  set f : O →ₗ[F] O := (x.toLinearMap - 1).restrict hxO with hf
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    have h1 : (v : W) ∈ fixedSpace x := by
      rw [fixedSpace, LinearMap.mem_ker]
      have := congrArg Subtype.val (LinearMap.mem_ker.mp hv)
      simpa [f] using this
    exact Subtype.ext (Submodule.disjoint_def.mp hx.fixed_others.1.disjoint _ h1 v.2)
  intro r hr
  haveI : Finite ↥O := Module.finite_of_finite F
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
  obtain ⟨r', hr'⟩ := hsurj ⟨r, hr⟩
  refine ⟨r', ?_⟩
  have hval : (f r' : W) = r := congrArg Subtype.val hr'
  rw [hf] at hval
  simpa [LinearMap.restrict_apply, LinearMap.sub_apply] using hval

end OmEngine

end CFSG.LocalAnalysis.GLTheoremA.Y10F

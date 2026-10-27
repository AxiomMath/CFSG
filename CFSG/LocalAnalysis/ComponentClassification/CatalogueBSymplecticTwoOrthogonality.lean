module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoKernel

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBSymplecticTwo

open Module Submodule CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher

section Family

variable {ι G : Type*} [Group G]

theorem exists_equiv_of_map_mem [Finite ι] (η : ι → Subgroup G) (hη : Function.Injective η)
    (α : MulAut G) (hα : ∀ i, ∃ j, (η i).map α.toMonoidHom = η j) :
    ∃ f : ι ≃ ι, ∀ i, (η i).map α.toMonoidHom = η (f i) := by
  choose f₀ hf₀ using hα
  have hinj : Function.Injective f₀ := fun i j h => hη (Subgroup.map_injective
    (f := α.toMonoidHom) α.injective (by rw [hf₀, hf₀, h]))
  exact ⟨Equiv.ofBijective f₀ ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩, hf₀⟩

theorem eq_of_map_eq (η : ι → Subgroup G) (hη : Function.Injective η) (α : MulAut G)
    {f g : ι → ι} (hf : ∀ i, (η i).map α.toMonoidHom = η (f i))
    (hg : ∀ i, (η i).map α.toMonoidHom = η (g i)) : f = g :=
  funext fun i => hη (by rw [← hf, ← hg])

end Family

variable {K : Type} [Field K]

theorem isoSubspaces_two_ne_bot (W : isoSubspaces 2 K 2) : W.1 ≠ ⊥ :=
  ne_bot_of_finrank_pos (by rw [W.2.2]; norm_num)

theorem pointStabilizer_injective :
    Function.Injective fun L : SpPoint 2 K => projStabilizer 2 K L.line :=
  fun L M h => SpPoint.ext (projStabilizer_inj L.line_ne_bot (isTotallyIsotropic_line L)
    M.line_ne_bot (isTotallyIsotropic_line M) h)

theorem planeStabilizer_injective :
    Function.Injective fun W : isoSubspaces 2 K 2 => projStabilizer 2 K W.1 :=
  fun W W' h => Subtype.ext (projStabilizer_inj (isoSubspaces_two_ne_bot W) W.2.1
    (isoSubspaces_two_ne_bot W') W'.2.1 h)

instance [Finite K] : Finite (isoSubspaces 2 K 2) := by
  have : Finite (Submodule K (Fin 2 ⊕ Fin 2 → K)) :=
    Finite.of_injective _ SetLike.coe_injective
  infer_instance

theorem spOrth_iff_exists_plane {L M : SpPoint 2 K} (hLM : L ≠ M) :
    SpOrth L M ↔ ∃ W : isoSubspaces 2 K 2, L.line ≤ W.1 ∧ M.line ≤ W.1 := by
  constructor
  · intro h
    exact ⟨supPlane h hLM, le_sup_left, le_sup_right⟩
  · rintro ⟨W, hL, hM⟩ x hx y hy
    exact W.2.1 x (hL hx) y (hM hy)

theorem kernel_orthogonality [Finite K] {α : MulAut (StatedProj (StatedSp 2 K))}
    (hα : α ∈ typeKernel K) :
    (∃! f : SpPoint 2 K ≃ SpPoint 2 K, ∀ L : SpPoint 2 K,
      (projStabilizer 2 K L.line).map α.toMonoidHom = projStabilizer 2 K (f L).line) ∧
    (∃! h : isoSubspaces 2 K 2 ≃ isoSubspaces 2 K 2, ∀ W : isoSubspaces 2 K 2,
      (projStabilizer 2 K W.1).map α.toMonoidHom = projStabilizer 2 K (h W).1) ∧
    ∀ (f : SpPoint 2 K ≃ SpPoint 2 K) (h : isoSubspaces 2 K 2 ≃ isoSubspaces 2 K 2),
      (∀ L : SpPoint 2 K,
        (projStabilizer 2 K L.line).map α.toMonoidHom = projStabilizer 2 K (f L).line) →
      (∀ W : isoSubspaces 2 K 2,
        (projStabilizer 2 K W.1).map α.toMonoidHom = projStabilizer 2 K (h W).1) →
      (∀ (L : SpPoint 2 K) (W : isoSubspaces 2 K 2), L.line ≤ W.1 ↔ (f L).line ≤ (h W).1) ∧
      ∀ L M : SpPoint 2 K, SpOrth L M ↔ SpOrth (f L) (f M) := by
  classical
  obtain ⟨p, hchar⟩ := CharP.exists K
  have hp : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  obtain ⟨hparts, -, -, -⟩ := type_kernel (K := K) p
  obtain ⟨-, -, hdisj, hXne, -, -, -, -⟩ := extremal_parabolics (K := K) p rfl
  have hX : (fun M => M.map α.toMonoidHom) '' pointParabolics K = pointParabolics K := hα
  have hY : (fun M => M.map α.toMonoidHom) '' planeParabolics K = planeParabolics K := by
    obtain ⟨-, -, hΦ⟩ := hparts α
    rcases hΦ with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exfalso
      obtain ⟨M, hM⟩ := hXne
      have hMY : M ∈ planeParabolics K := by
        rw [← h, hX]
        exact hM
      exact Set.disjoint_left.mp hdisj hM hMY
  have hptex : ∀ L : SpPoint 2 K, ∃ L' : SpPoint 2 K,
      (projStabilizer 2 K L.line).map α.toMonoidHom = projStabilizer 2 K L'.line := by
    intro L
    have hmem : (projStabilizer 2 K L.line).map α.toMonoidHom ∈ pointParabolics K := by
      rw [← hX]
      exact ⟨_, ⟨L.line, L.finrank_line, rfl⟩, rfl⟩
    obtain ⟨L', hL', hLL'⟩ := hmem
    exact ⟨⟨L', hL'⟩, hLL'⟩
  have hplex : ∀ W : isoSubspaces 2 K 2, ∃ W' : isoSubspaces 2 K 2,
      (projStabilizer 2 K W.1).map α.toMonoidHom = projStabilizer 2 K W'.1 := by
    intro W
    have hmem : (projStabilizer 2 K W.1).map α.toMonoidHom ∈ planeParabolics K := by
      rw [← hY]
      exact ⟨_, ⟨W.1, W.2.1, W.2.2, rfl⟩, rfl⟩
    obtain ⟨W', hW', hW2, hWW'⟩ := hmem
    exact ⟨⟨W', hW', hW2⟩, hWW'⟩
  obtain ⟨f₀, hf₀⟩ := exists_equiv_of_map_mem _ pointStabilizer_injective α hptex
  obtain ⟨h₀, hh₀⟩ := exists_equiv_of_map_mem _ planeStabilizer_injective α hplex
  refine ⟨⟨f₀, hf₀, fun f hf => Equiv.ext fun L => congrFun
      (eq_of_map_eq _ pointStabilizer_injective α hf hf₀) L⟩,
    ⟨h₀, hh₀, fun h hh => Equiv.ext fun W => congrFun
      (eq_of_map_eq _ planeStabilizer_injective α hh hh₀) W⟩, fun f h hf hh => ?_⟩
  have hinc : ∀ (L : SpPoint 2 K) (W : isoSubspaces 2 K 2),
      L.line ≤ W.1 ↔ (f L).line ≤ (h W).1 := by
    intro L W
    have hΦL : graphAutHom K p α (pointVertex p L) = pointVertex p (f L) :=
      Subtype.ext (hf L)
    have hΦW : graphAutHom K p α (planeVertex p W) = planeVertex p (h W) :=
      Subtype.ext (hh W)
    rw [← pointVertex_adj_planeVertex (p := p), ← pointVertex_adj_planeVertex (p := p), ← hΦL,
      ← hΦW]
    exact ((graphAutHom K p α).map_rel_iff).symm
  refine ⟨hinc, fun L M => ?_⟩
  by_cases hLM : L = M
  · subst hLM
    exact iff_of_true (spOrth_self L) (spOrth_self _)
  have hfLM : f L ≠ f M := f.injective.ne hLM
  rw [spOrth_iff_exists_plane hLM, spOrth_iff_exists_plane hfLM]
  constructor
  · rintro ⟨W, h1, h2⟩
    exact ⟨h W, (hinc L W).mp h1, (hinc M W).mp h2⟩
  · rintro ⟨W', h1, h2⟩
    obtain ⟨W, rfl⟩ := h.surjective W'
    exact ⟨W, (hinc L W).mpr h1, (hinc M W).mpr h2⟩

end CFSG.ComponentClassification.CatalogueBSymplecticTwo

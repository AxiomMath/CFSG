module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Core3L3Sec
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Core3L3Stab
public import CFSG.RankThree.PartTwo.Sec15.Wales154KL3a

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I137C3

open Matrix CFSG.Open CFSG.BenderSuzuki.MatrixGroups

section Lift


theorem l3_card_simple_section_statedProj_three {K : Type} [Field K] [Finite K] {f : ℕ}
    (hf : f ≠ 0) (hK : Nat.card K = 2 ^ f) {T A : Subgroup (StatedProj (StatedSL 3 K))}
    (hT2 : IsPGroup 2 T) (hT : T ≠ ⊥)
    (hA : A ≤ Subgroup.normalizer (T : Set (StatedProj (StatedSL 3 K)))) {Q : Type} [Group Q]
    [IsSimpleGroup Q] (hab : ∃ a b : Q, a * b ≠ b * a) (g : A →* Q)
    (hg : Function.Surjective g) :
    Nat.card Q = 60 ∨ ∃ m : ℕ, 2 ≤ m ∧ Nat.card Q = 2 ^ m * (4 ^ m - 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hK)
  let ι₀ : StatedProj (StatedSL 3 K) →* Matrix.ProjGenLinGroup (Fin 3) K :=
    ((StatedSL 3 K).map
      (Matrix.ProjGenLinGroup.mk : GL (Fin 3) K →* Matrix.ProjGenLinGroup (Fin 3) K)).subtype.comp
      (CFSG.Open.StatedAPI.mapMkEquivStatedProj (StatedSL 3 K)).symm.toMonoidHom
  have hι₀ : Function.Injective ι₀ := Subtype.val_injective.comp (MulEquiv.injective _)
  have hι₀mk : ∀ x : StatedSL 3 K,
      ι₀ (x : StatedProj (StatedSL 3 K)) = Matrix.ProjGenLinGroup.mk (x : GL (Fin 3) K) :=
    fun x => rfl
  have hTm2 : IsPGroup 2 (T.map ι₀) := hT2.map ι₀
  have hTm : T.map ι₀ ≠ ⊥ := by
    rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ hι₀]
  obtain ⟨W, hW0, hWt, hW⟩ :=
    CFSG.RankThree.PartTwo.Sec15.Wales154.KL3aProof.exists_stable_subspace hTm2 hTm
  have hAn : A.map ι₀ ≤ Subgroup.normalizer ((T.map ι₀ : Subgroup _) : Set _) :=
    (Subgroup.map_mono hA).trans (Subgroup.le_normalizer_map _)
  let D : Subgroup (GL (Fin 3) K) :=
    ((A.map ι₀).comap
      (Matrix.ProjGenLinGroup.mk : GL (Fin 3) K →* Matrix.ProjGenLinGroup (Fin 3) K)) ⊓
      StatedSL 3 K
  have hDH : D ≤ StatedSL 3 K := inf_le_right
  have hDW : ∀ x ∈ D, ∀ v ∈ W, (x : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W := fun x hx v hv =>
    hW x (hAn (Subgroup.mem_comap.1 hx.1)) v hv
  have hdet : ∀ x ∈ D, ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := fun x hx => by
    have h1 : x ∈ (Matrix.GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).ker := by
      rw [← CFSG.Open.StatedAPI.statedSL_eq_ker_det]
      exact hx.2
    rw [MonoidHom.mem_ker] at h1
    rw [← Matrix.GeneralLinearGroup.val_det_apply, h1, Units.val_one]
  obtain ⟨ψ, hψ⟩ := l3_exists_levi_of_stable D hW0 hWt hDW hdet
  let πD₀ : D →* StatedProj (StatedSL 3 K) :=
    (QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K))).comp
      (Subgroup.inclusion hDH)
  have hπD₀ : ∀ x : D, ι₀ (πD₀ x) = Matrix.ProjGenLinGroup.mk (x : GL (Fin 3) K) := fun x =>
    hι₀mk ⟨x, hDH x.2⟩
  have hπA : ∀ x : D, πD₀ x ∈ A := fun x => by
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 x.2.1)
    have : a = πD₀ x := hι₀ (hax.trans (hπD₀ x).symm)
    rw [← this]
    exact ha
  let πD : D →* A := πD₀.codRestrict A hπA
  have hπD : Function.Surjective πD := fun a => by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective (a : StatedProj (StatedSL 3 K))
    have hhD : (h : GL (Fin 3) K) ∈ D := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_comap.2 ?_, h.2⟩
      refine Subgroup.mem_map.2 ⟨(a : StatedProj (StatedSL 3 K)), a.2, ?_⟩
      rw [← hh]
      exact hι₀mk h
    exact ⟨⟨h, hhD⟩, Subtype.ext hh⟩
  obtain ⟨Hb, ρ, hρ⟩ := l3_exists_psl2_section hab (g.comp πD) (hg.comp hπD) ψ hψ
  exact l3_card_simple_section_psl2_even hf hK Hb hab ρ hρ

end Lift

end CFSG.LocalAnalysis.GLTheoremA.I137C3

end

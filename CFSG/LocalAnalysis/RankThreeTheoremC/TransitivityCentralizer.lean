module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionStructure
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.RankThree.PartOne.Planes Subgroup

variable {G : Type} [Group G] [Finite G]

theorem ExtremalObstruction.mem_of_mem_centralizer_of_isMulCommutative (hS : Setting G)
    (hD1 : TheoremD1 G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hDab : IsMulCommutative D)
    (hCM : centralizer (D : Set G) ≤ M) {y : G} (hyC : y ∈ centralizer (D : Set G))
    (hyp : y ^ p = 1) : y ∈ D := by
  classical
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hM, hDP, hD2, hDM⟩ := hext.obstruction
  have hPp : IsPGroup p (P : Subgroup G) := P.isPGroup'
  have hiso := hext.isIsolatedPlane_of_isMulCommutative hprime hDab
  obtain ⟨hDe, hDc⟩ := hext.isElemAbelian_of_isMulCommutative hprime hDab
  by_contra hyD
  have hDy : ∀ d ∈ D, d * y = y * d := fun d hd => mem_centralizer_iff.mp hyC d hd
  have hEc : Nat.card ↥(D ⊔ zpowers y) = p ^ 3 := by
    rw [card_sup_zpowers hprime D hyp hyD hDy, hDc, ← pow_succ]
  have hDe' : CFSG.IsElementaryAbelian p D :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p D).2 hDe
  have hye : CFSG.IsElementaryAbelian p (zpowers y) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hyp
  have hEe : CFSG.IsElementaryAbelian p ↥(D ⊔ zpowers y) :=
    CFSG.IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr hyC)
  have hEC : D ⊔ zpowers y ≤ centralizer (D : Set G) :=
    sup_le (le_centralizer_iff_isMulCommutative.mpr hDab) (zpowers_le.mpr hyC)
  have hEN : D ⊔ zpowers y ≤ normalizer (D : Set G) := hEC.trans (centralizer_le_normalizer _)
  have hEM : D ⊔ zpowers y ≤ M := hEC.trans hCM
  have hEp : IsPGroup p ↥(D ⊔ zpowers y) := CFSG.IsElementaryAbelian.isPGroup p _
  obtain ⟨Q₁, hQ₁⟩ := (hEp.comap_subtype (K := normalizer (D : Set G))).exists_le_sylow
  set S₁ : Subgroup G := (Q₁ : Subgroup (normalizer (D : Set G))).map
    (normalizer (D : Set G)).subtype with hS₁
  have hS₁syl : CFSG.ABGLocalTools.IsSylowOf p S₁ (normalizer (D : Set G)) := ⟨Q₁, rfl⟩
  have hES₁ : D ⊔ zpowers y ≤ S₁ := fun e he => ⟨⟨e, hEN he⟩, hQ₁ he, rfl⟩
  obtain ⟨P₂, hS₁P₂⟩ := hS₁syl.isPGroup.exists_le_sylow
  obtain ⟨M₂, hM₂, -⟩ := exists_isCoreMaxLocal hS hp P₂
  have hDM₂ : ¬ normalizer (D : Set G) ≤ M₂ := by
    intro hN
    have h3 : 3 ≤ CFSG.Open.pRank p (M₂ ⊓ M) := by
      unfold CFSG.Open.pRank
      exact le_csSup (pRank_set_bddAbove p hprime.one_lt _) ⟨_, le_inf (hEN.trans hN) hEM,
        (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1 hEe, hEc⟩
    have hM₂M := le_of_three_le_pRank_inf hD1 hp hM hM₂.1.1 h3
    have heq : M = M₂ := hM₂.1.2 M hM.1.1 hM₂M
    exact hDM (heq ▸ hN)
  have hDP₂ : D ≤ (P₂ : Subgroup G) := (le_sup_left.trans hES₁).trans hS₁P₂
  have hcard := hext.maximal P₂ M₂ D ⟨hM₂, hDP₂, hD2, hDM₂⟩
  obtain ⟨Q₀, hQ₀⟩ := ((hPp.to_inf_left (K := normalizer (D : Set G))).comap_subtype
    (K := normalizer (D : Set G))).exists_le_sylow
  set S₀ : Subgroup G := (Q₀ : Subgroup (normalizer (D : Set G))).map
    (normalizer (D : Set G)).subtype with hS₀
  have hS₀syl : CFSG.ABGLocalTools.IsSylowOf p S₀ (normalizer (D : Set G)) := ⟨Q₀, rfl⟩
  have hPS₀ : (P : Subgroup G) ⊓ normalizer (D : Set G) ≤ S₀ := fun e he =>
    ⟨⟨e, he.2⟩, hQ₀ he, rfl⟩
  have hS₀eq : S₀ = (P : Subgroup G) ⊓ normalizer (D : Set G) := by
    refine (Subgroup.eq_of_le_of_card_ge hPS₀ ?_).symm
    calc Nat.card S₀ = Nat.card S₁ := by rw [hS₀syl.card_eq, hS₁syl.card_eq]
      _ ≤ Nat.card ↥((P₂ : Subgroup G) ⊓ normalizer (D : Set G)) :=
          card_le_of_le (le_inf hS₁P₂ hS₁syl.le)
      _ ≤ Nat.card ↥((P : Subgroup G) ⊓ normalizer (D : Set G)) := hcard
  obtain ⟨g, -, hconj⟩ := hS₀syl.exists_mem_conj hS₁syl
  have hE'le : (D ⊔ zpowers y).map (MulAut.conj g⁻¹).toMonoidHom ≤
      (P : Subgroup G) ⊓ normalizer (D : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    rw [← hS₀eq]
    have := (hconj e).mp (hES₁ he)
    simpa [MulAut.conj_apply] using this
  have hE'e : CFSG.IsElementaryAbelian p ↥((D ⊔ zpowers y).map (MulAut.conj g⁻¹).toMonoidHom) :=
    CFSG.IsElementaryAbelian.map _
  have hE'c : Nat.card ↥((D ⊔ zpowers y).map (MulAut.conj g⁻¹).toMonoidHom) = p ^ 3 := by
    rw [card_map_of_injective (MulAut.conj g⁻¹).injective, hEc]
  exact not_elemAbelian_cube_le_normalizer_of_isIsolatedPlane hprime hPp hiso hE'le hE'e hE'c

end CFSG.LocalAnalysis.RankThreeTheoremC

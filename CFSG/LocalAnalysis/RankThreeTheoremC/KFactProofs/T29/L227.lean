module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Alt
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2.EndGame
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoAutCard

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.HardMathSupport.Solomon.LocalBalance
open scoped MatrixGroups

section L227

theorem autFieldPart_conj {K : Type} [Field K] [Finite K] (g : PSL(2, K)) :
    CFSG.Quasithin.autFieldPart K (MulAut.conj g) = 1 := by
  have hx : (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearEquivAut K).symm
      (MulAut.conj g) = SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL g) := by
    apply (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearEquivAut K).injective
    rw [MulEquiv.apply_symm_apply]
    change MulAut.conj g =
      CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearAction K
        (SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL g))
    rw [CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearAction_inl,
      CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_toPGL]
  change SemidirectProduct.rightHom
    ((CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearEquivAut K).symm
      (MulAut.conj g)) = 1
  rw [hx, SemidirectProduct.rightHom_inl]

theorem index_eq_of_fieldAut_L227 {X : Type} [Group X] [Finite X] {L : Subgroup X} [L.Normal]
    (hC : centralizer (L : Set X) = ⊥) {x : X} (hx : InducesFieldAutL227 L x) :
    L.index = 3 ∨ L.index = 6 := by
  obtain ⟨e, h, hne⟩ := hx
  obtain ⟨ψ, hψ⟩ : ∃ ψ : X →* (GaloisField 3 3 ≃+* GaloisField 3 3), ∀ g : X,
      ψ g = CFSG.Quasithin.autFieldPart (GaloisField 3 3)
        (MulAut.congr e (MulAut.conjNormal g : MulAut L)) :=
    ⟨(CFSG.Quasithin.autFieldPart (GaloisField 3 3)).comp
      ((MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : X →* MulAut L)), fun g => rfl⟩
  have hψL : ∀ l : L, ψ (l : X) = 1 := by
    intro l
    have hc : MulAut.congr e (MulAut.conjNormal (l : X) : MulAut L) = MulAut.conj (e l) := by
      rw [MulAut.conjNormal_val]
      ext y
      show e (l * e.symm y * l⁻¹) = e l * y * (e l)⁻¹
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [hψ, hc]
    exact autFieldPart_conj (e l)
  have hψx : ψ x ≠ 1 := by
    have hn : (MulAut.conjNormal x : MulAut L) = L.normalizerMonoidHom ⟨x, h⟩ := by
      ext y
      rfl
    rw [hψ, hn]
    exact hne
  have hLker : L ≤ ψ.ker := by
    intro l hl
    rw [MonoidHom.mem_ker]
    exact hψL ⟨l, hl⟩
  have hidx1 : ψ.ker.index ∣ L.index := Subgroup.index_dvd_of_le hLker
  have hidx2 : ψ.ker.index = Nat.card ψ.range := Subgroup.index_ker ψ
  have hdvd3 : Nat.card ψ.range ∣ 3 := by
    have hd := Subgroup.card_subgroup_dvd_card ψ.range
    rwa [CFSG.RankThree.PartTwo.KFacts.card_ringAut_galoisField_three_three] at hd
  have hne1 : Nat.card ψ.range ≠ 1 := by
    intro h1
    rw [Subgroup.card_eq_one] at h1
    apply hψx
    have hmem : ψ x ∈ ψ.range := MonoidHom.mem_range.mpr ⟨x, rfl⟩
    rw [h1, Subgroup.mem_bot] at hmem
    exact hmem
  have hcard3 : Nat.card ψ.range = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h1 | h1
    · exact absurd h1 hne1
    · exact h1
  have h3 : 3 ∣ L.index := by
    have hh := hidx1
    rw [hidx2, hcard3] at hh
    exact hh
  have hLcard : Nat.card L = 9828 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2.tor_card_psl2_27
  have hAut : Nat.card (MulAut L) = 58968 := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    have hA : Nat.card (MulAut PSL(2, GaloisField 3 3)) = 3 ^ 3 * ((3 ^ 3) ^ 2 - 1) * 3 :=
      CFSG.AGLEmbedding.card_mulAut_psl2GF 3 3 (by norm_num)
    exact hA.trans (by norm_num)
  have hXdvd : Nat.card X ∣ Nat.card (MulAut L) :=
    Subgroup.card_dvd_of_injective (MulAut.conjNormal : X →* MulAut L)
      (conjNormal_injective_of_centralizer_eq_bot L hC)
  have hmul : Nat.card L * L.index = Nat.card X := Subgroup.card_mul_index L
  rw [hAut, ← hmul, hLcard] at hXdvd
  have hdiv6 : L.index ∣ 6 := by
    have h58968 : (58968 : ℕ) = 9828 * 6 := by norm_num
    rw [h58968] at hXdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hXdvd
  have hle : L.index ≤ 6 := Nat.le_of_dvd (by norm_num) hdiv6
  obtain ⟨n, hn⟩ : ∃ n, L.index = n := ⟨_, rfl⟩
  rw [hn] at hdiv6 h3 hle
  rw [hn]
  interval_cases n <;> omega

end L227

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29

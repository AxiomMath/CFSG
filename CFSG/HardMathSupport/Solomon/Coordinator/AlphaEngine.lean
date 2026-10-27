module

public import CFSG.HardMathSupport.Solomon.Coordinator.AlphaFunctor
public import CFSG.HardMathSupport.Solomon.Coordinator.CaseOne

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal

variable {G : Type} [Group G] [Finite G]

theorem exists_isEkIn_mem {p k n : ℕ} (hp : p.Prime) {A : Subgroup G} (hA : IsElemAbelian p A)
    (hcard : Nat.card A = p ^ n) (hkn : k + 1 ≤ n) {b : G} (hb : b ∈ A) :
    ∃ E : Subgroup G, IsEkIn p (k + 1) A E ∧ b ∈ E := by
  have : Fact p.Prime := ⟨hp⟩
  have hbA : Subgroup.zpowers b ≤ A := (Subgroup.zpowers_le).2 hb
  have hb1 : Nat.card (Subgroup.zpowers b) ∣ p ^ (k + 1) := by
    rw [Nat.card_zpowers]
    exact (orderOf_dvd_of_pow_eq_one (hA.2 b hb)).trans (dvd_pow_self p (by omega))
  obtain ⟨E, hEcard, hbE, hEA⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hp hb1
    (hcard ▸ pow_dvd_pow p hkn) hbA
  exact ⟨E, ⟨hEA, isElemAbelian_mono hA hEA, hEcard⟩, hbE (Subgroup.mem_zpowers b)⟩

theorem commutator_glaDelta_le_alphaE' {p k n : ℕ} (hp : p.Prime) (hk : 1 ≤ k)
    {A D₀ E₀ : Subgroup G} (hA : IsElemAbelian p A) (hcard : Nat.card A = p ^ n) (hkn : k + 1 ≤ n)
    (hbal : IsBalancedWrt p (k + 1) A) (hwb : IsWeaklyBalancedWrt p k A)
    (hgen : ∀ D₀ : Subgroup G, IsEkIn p k A D₀ → ∀ E' : Subgroup G, IsEkIn p (k + 1) A E' →
      ⁅GLADelta p D₀, E'⁆ ≤ ⨆ (D : Subgroup G) (_ : IsEkIn p k E' D),
        ⁅GLADelta p D₀ ⊓ Subgroup.centralizer (D : Set G), E'⁆)
    (hD₀ : IsEkIn p k A D₀) (hE₀ : IsEkIn p (k + 1) A E₀) :
    ⁅GLADelta p D₀, A⁆ ≤ alphaE p k E₀ := by
  refine Subgroup.commutator_le.2 fun x hx b hb => ?_
  obtain ⟨E, hE, hbE⟩ := exists_isEkIn_mem hp hA hcard hkn hb
  rw [← alphaE_eq_alphaE hp hk hA hbal hwb hgen hE hE₀]
  exact commutator_glaDelta_le_alphaE hp hk hA hwb (hgen D₀ hD₀ E hE) hD₀ hE
    (Subgroup.commutator_mem_commutator hx hbE)

theorem isKGroupCat_thetaStarValue (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge)
    (hK : CFSG.Open.IsKProper G) {p : ℕ} (hp : p.Prime) (hpG : p ∣ Nat.card G) {B D : Subgroup G}
    (hDB : D ≤ B) (hD : D ≠ ⊥) : CFSG.SectionRank.IsKGroupCat ↥(thetaStarValue p B D) := by
  have hne : thetaStarValue p B D ≠ ⊤ := by
    intro htop
    apply not_dvd_card_thetaStarValue hp hDB hD
    rw [htop, Subgroup.card_top]
    exact hpG
  exact CFSG.RankThree.PartTwo.Sec20.isKGroupCat_of_ne_top hbridge hK hne

theorem glbCore_le_normalizer_alphaE_and_even (hSF : SignalizerFunctorTheoremK)
    (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge) {m p : ℕ} (hS : GLStanding G m p)
    {B E₀ : Subgroup G} (hB : IsBOneMax p B) (hbal : IsBalancedWrt p 3 B)
    (hwb : IsWeaklyBalancedWrt p 2 B)
    (hgen : ∀ D₀ : Subgroup G, IsEkIn p 2 B D₀ → ∀ E' : Subgroup G, IsEkIn p 3 B E' →
      ⁅GLADelta p D₀, E'⁆ ≤ ⨆ (D : Subgroup G) (_ : IsEkIn p 2 E' D),
        ⁅GLADelta p D₀ ⊓ Subgroup.centralizer (D : Set G), E'⁆)
    (hE₀ : IsEkIn p 3 B E₀) (heven : Even (Nat.card (alphaE p 2 E₀))) :
    GLBCore p 3 B ≤ Subgroup.normalizer (alphaE p 2 E₀ : Set G) ∧
      Even (Nat.card (GLAPPrimeCoreOf p (Subgroup.normalizer (alphaE p 2 E₀ : Set G)))) := by
  have hp := hS.prime
  have hBel : IsElemAbelian p B := hB.1.1
  have hBcard : Nat.card B = p ^ m := hS.card_eq hB
  have hm4 := hS.four_le
  have hrank : p ^ (2 + 2) ≤ Nat.card B := hBcard ▸ Nat.pow_le_pow_right hp.pos (by omega)
  have hcop := alphaE_coprime hSF hp (by norm_num) hBel hrank hwb
    (fun D hD => isKGroupCat_thetaStarValue hbridge hS.kProper hp hS.beta.2.2.1 hD.1
      (hD.ne_bot hp (by norm_num))) hE₀
  refine ⟨glbCore_le_normalizer_alphaE hp (by norm_num) hBel hbal hwb hgen hE₀, ?_⟩
  exact even_iff_two_dvd.2 ((even_iff_two_dvd.1 heven).trans
    (Subgroup.card_dvd_of_le (le_glaPPrimeCoreOf_normalizer hcop)))

theorem exists_preUniquenessSubgroup_of_alphaE (hSF : SignalizerFunctorTheoremK)
    (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge) {m p : ℕ} (hS : GLStanding G m p)
    {B : Subgroup G} (hB : IsBOneMax p B) (hbal : IsBalancedWrt p 3 B)
    (hwb : IsWeaklyBalancedWrt p 2 B)
    (hgen : ∀ D₀ : Subgroup G, IsEkIn p 2 B D₀ → ∀ E' : Subgroup G, IsEkIn p 3 B E' →
      ⁅GLADelta p D₀, E'⁆ ≤ ⨆ (D : Subgroup G) (_ : IsEkIn p 2 E' D),
        ⁅GLADelta p D₀ ⊓ Subgroup.centralizer (D : Set G), E'⁆)
    (hΛ : lambdaStarGroup p B = psiStarGroup p B)
    (hD : ∃ D : Subgroup G, IsEkIn p 2 B D ∧ Even (Nat.card (⁅GLADelta p D, B⁆ : Subgroup G))) :
    ∃ M₀ : Subgroup G, IsPreUniquenessSubgroup p B M₀ := by
  have hp := hS.prime
  have hBel : IsElemAbelian p B := hB.1.1
  have hBcard : Nat.card B = p ^ m := hS.card_eq hB
  have hm4 := hS.four_le
  obtain ⟨E₀, hE₀B, hE₀el, hE₀card⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Proving.exists_elemAbelian_subgroup_card_pow hp hBel
      (by omega : 3 ≤ m) hBcard
  have hE₀ : IsEkIn p 3 B E₀ := ⟨hE₀B, hE₀el, hE₀card⟩
  obtain ⟨D, hDB, hDeven⟩ := hD
  have hbal3 : IsBalancedWrt p (2 + 1) B := hbal
  have heven : Even (Nat.card (alphaE p 2 E₀)) := by
    have hle := commutator_glaDelta_le_alphaE' hp (by norm_num) hBel hBcard (by omega) hbal3 hwb
      hgen hDB hE₀
    exact even_iff_two_dvd.2 ((even_iff_two_dvd.1 hDeven).trans (Subgroup.card_dvd_of_le hle))
  obtain ⟨hΓ, hO⟩ := glbCore_le_normalizer_alphaE_and_even hSF hbridge hS hB hbal hwb hgen hE₀ heven
  refine ⟨Subgroup.normalizer (alphaE p 2 E₀ : Set G), ?_, hΓ, hO⟩
  rw [hΛ]
  exact (psiStarGroup_le_glbCore hp hBel hBcard hm4).trans hΓ

end CFSG.HardMathSupport.Solomon.Coordinator

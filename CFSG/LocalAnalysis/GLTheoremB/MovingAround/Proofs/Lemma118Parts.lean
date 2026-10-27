module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma118

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

variable {G : Type} [Group G] [Finite G]

@[expose] def HasBigAltPComponent (p r : ℕ) (M : Subgroup G) : Prop :=
  ∃ (L : Subgroup G) (n : ℕ), GLAPComponent p M L ∧ IsAltType n (barOf p L) ∧ p ^ r < n

@[expose] def Lemma118Transport : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ) (B M E A : Subgroup G) (a : G) (K : Subgroup G),
    Cex117 G m p B M E A a K → Type117a p E A K →
      HasBigAltPComponent p (CFSG.Open.pRank p (E ⊓ A)) M

@[expose] def Lemma118Return : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ) (B M E A : Subgroup G),
    Sec11 G m p B M E A → HasBigAltPComponent p (CFSG.Open.pRank p (E ⊓ A)) M →
      ∀ a ∈ M, a ^ p = 1 → ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1

@[expose] def AltBalanceInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ) (B M E A : Subgroup G), Sec11 G m p B M E A →
    ∀ (t : G) (J : Subgroup G) (n : ℕ), t ∈ M → t ^ p = 1 → t ≠ 1 → J ≤ M →
      GLAPComponent p (Subgroup.centralizer ({t} : Set G)) J → IsAltType n (barOf p J) →
        10 ≤ n → ∃ (L : Subgroup G) (n' : ℕ), GLAPComponent p M L ∧ IsAltType n' (barOf p L) ∧ n ≤ n'

theorem lemma118_of_parts (hT : Lemma118Transport) (hR : Lemma118Return) :
    Lemma118Statement := by
  intro G _ _ m p B M E A a K h
  rcases h.ht with ht | ht | ht
  · exfalso
    have hbig := hT G m p B M E A a K h ht
    have hAM : A ≤ M := h.pair.1.2.1.1.1.1
    have hap : a ^ p = 1 := h.pair.1.2.1.1.1.2.1.2 a h.ha.1
    obtain ⟨A1, hA1, haA1⟩ :=
      hR G m p B M E A h.toSec11 hbig a (hAM h.ha.1) hap
    exact h.notD ⟨A1, hA1, haA1⟩
  · exact Or.inl ht
  · exact Or.inr ht

theorem exists_inD_of_centralizes_conj {m p : ℕ} [hp : Fact p.Prime] {B M E A : Subgroup G}
    (h : Sec11 G m p B M E A) {x a : G} (hx : x ∈ M) {F₁ : Subgroup G}
    (hF₁ : F₁ ≤ GLBConj x B) (hFab : IsElemAbelian p F₁)
    (hr : CFSG.Open.pRank p (E ⊓ A) + 1 ≤ CFSG.Open.pRank p F₁) (ha : a ^ p = 1)
    (hc : Subgroup.zpowers a ≤ Subgroup.centralizer (F₁ : Set G)) :
    ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1 := by
  have hBx : inD p M (GLBConj x B) :=
    (lemma101_i_of_conj isUniquenessTwoLocal_conj_holds h.toSec10Fails hx
      (lemma101_ii_holds h.toSec10Fails) h.pair.1.2.1).1
  have hX : IsElemAbelian p (Subgroup.zpowers a ⊔ F₁) :=
    isElemAbelian_sup_of_commute (CFSG.Open.isElemAbelian_zpowers ha) hFab hc
  obtain ⟨H, hH, hXH⟩ := c104_exists_isSCp_top hX
  refine ⟨H, inD_of_meet h.pair hBx hH ?_, hXH (le_sup_left (b := F₁) (Subgroup.mem_zpowers a))⟩
  exact hr.trans (CFSG.SectionRank.pRank_mono hp.out.one_lt (le_inf hF₁ (le_sup_right.trans hXH)))

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

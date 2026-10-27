module

public import CFSG.RankThree.PartTwo.Sec19.SimsTheoremC
public import CFSG.RankThree.PartTwo.Sec19.F194Item316X
public import CFSG.CGT.Foote82.T66.CitedL13

public section

namespace CFSG.CGT.Harada80

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec19 Matrix

@[expose] def H1Natural (m : ℕ) : Prop :=
  CFSG.CGT.Foote82.L13Aux.H1Zero ↥(omegaMinusTwo m) (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) fun g a =>
    ((g : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
      Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ a

theorem h1Natural_two (h : CFSG.CGT.Foote82.H1OmegaMinusSix) : H1Natural 2 := h

theorem h1Natural_three (h : CFSG.CGT.Foote82.H1OmegaMinusEight) : H1Natural 3 := h

structure Setting (G : Type) [Group G] [Finite G] (M J : Subgroup G) (m : ℕ) : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  kProper : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G
  charTwo : CFSG.Assembly.IsCharTwoType G
  evenRank : CFSG.Assembly.evenRank G = 3
  maxLocal : CFSG.IsMaximalTwoLocal M
  block : IsBlock M J
  perfect : ⁅J, J⁆ = J
  m_eq : m = 2 ∨ m = 3
  type : IsOmegaMinusType J m
  elemU : CFSG.Open.IsElemAbelian 2 (blockU J)
  uniq : CFSG.maximalTwoLocalsContaining (J : Set G) = {M}
  normalizer_eq : Subgroup.normalizer (J : Set G) = M

theorem lit316Harada_of_setting (hC : CFSG.CGT.PushingUpLit.FooteNonsolvableSimple)
    (h : ∀ (G : Type) [Group G] [Finite G] (M J : Subgroup G) (m : ℕ), Setting G M J m →
      CFSG.Assembly.InCatalog G) :
    Lit316Harada := by
  intro G _ _ hs hn hK hc he M J hM hB hperf htype hab huniq
  obtain ⟨m, hm, ht⟩ : ∃ m, (m = 2 ∨ m = 3) ∧ IsOmegaMinusType J m := by
    rcases htype with h2 | h3
    exacts [⟨2, Or.inl rfl, h2⟩, ⟨3, Or.inr rfl, h3⟩]
  have hq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) :=
    SimsTheoremC.isQuasisimple_of_isFType hB.1
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, by omega, ht⟩))))
  have hnorm : (J.subgroupOf M).Normal :=
    hC G hs hK hc M J hM hB.2.1 hB.2.2 (isShortGroup_of_isShort hB.1) hq huniq
  exact h G M J m ⟨hs, hn, hK, hc, he, hM, hB, hperf, hm, ht, hab, huniq,
    SimsTheoremC.normalizer_eq_of_normal hM hB.2.1 hnorm hB.1⟩

namespace Setting

variable {G : Type} [Group G] [Finite G] {M J : Subgroup G} {m : ℕ} (S : Setting G M J m)
include S

theorem le : J ≤ M := S.block.2.1

theorem short : IsShort J := S.block.1

theorem normal {x : G} (hx : x ∈ M) {y : G} (hy : y ∈ J) : x * y * x⁻¹ ∈ J := by
  rw [← S.normalizer_eq] at hx
  exact (Subgroup.mem_normalizer_iff.mp hx y).mp hy

theorem cent {t : G} (ht : t ∈ CFSG.Open.pCoreOf 2 M) (h1 : t ≠ 1) :
    CFSG.generalizedFitting ↥(Subgroup.centralizer ({t} : Set G)) =
      CFSG.pCore 2 ↥(Subgroup.centralizer ({t} : Set G)) :=
  generalizedFitting_centralizer_eq_pCore S.charTwo ht h1

noncomputable def alpha : ↥J →* ↥(omegaMinusTwo m) :=
  Classical.choose S.type

theorem alpha_surjective : Function.Surjective S.alpha :=
  (Classical.choose_spec S.type).1

theorem ker_alpha : S.alpha.ker = CFSG.pCore 2 ↥J :=
  (Classical.choose_spec S.type).2.1

noncomputable def beta : ↥(blockU J) →* Multiplicative (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) :=
  Classical.choose (Classical.choose_spec S.type).2.2

theorem beta_surjective : Function.Surjective S.beta :=
  (Classical.choose_spec (Classical.choose_spec S.type).2.2).1

theorem ker_beta : S.beta.ker = (blockZ J).subgroupOf (blockU J) :=
  (Classical.choose_spec (Classical.choose_spec S.type).2.2).2.1

theorem beta_conj (ℓ : ↥J) (u v : ↥(blockU J)) (h : (v : G) = ℓ * u * ℓ⁻¹) :
    Multiplicative.toAdd (S.beta v) =
      ((S.alpha ℓ : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2))
        *ᵥ Multiplicative.toAdd (S.beta u) :=
  (Classical.choose_spec (Classical.choose_spec S.type).2.2).2.2 ℓ u v h

end Setting

end CFSG.CGT.Harada80

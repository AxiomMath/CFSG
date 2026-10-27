module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialParameterSumProp
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialParameterSumHall
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialTorusFusion

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage

namespace CaseIData

variable {G : Type} [Group G] [Finite G] {t s₀ d d₁ : G} {J : Subgroup G} {q : ℕ}
  {F' : Type} [Field F'] [Finite F']
  {φ : torusH G t s₀ ⧸ CFSG.pPrimeCore 2 (torusH G t s₀) ≃* CFSG.GorensteinWalter.PGL2 F'}
  (h : CaseIData G t s₀ d d₁ J q F' φ)
include h

theorem coprime_relIndex_inf_torusH
    (hne : Nat.card (torusU G t s₀ d) ≠ Nat.card (torusW G t s₀)) (R : Subgroup G)
    (hRU : R ≤ Subgroup.centralizer (torusU G t s₀ d : Set G)) (hR : Odd (Nat.card R))
    (hWR : torusW G t s₀ ≤ R) :
    Nat.Coprime (Nat.card (torusW G t s₀))
      ((torusW G t s₀).relIndex (R ⊓ torusH G t s₀)) :=
  h.coprime_relIndex_inf_torusH_of_coprime (h.coprime_card_torusU_torusW hne) R hRU hR hWR

theorem card_torusU_eq_card_torusW :
    Nat.card (torusU G t s₀ d) = Nat.card (torusW G t s₀) :=
  h.card_torusU_eq_card_torusW_of_hall fun hne R hRU hR hWR =>
    h.coprime_relIndex_inf_torusH hne R hRU hR hWR

end CaseIData

theorem trivial_fixed_core_torus_parameter_sum
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 9 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hcov : EscapingLocalEigensubgroups.allLocalPrimeStationaryCovers t (fS (s n) : G))
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2)
    (hA₀ : (N t).map (C t).subtype ⊓ Subgroup.centralizer {(fS (s n) : G)} = ⊥)
    (hN : N t ≠ ⊥) (d : G) (F' : Type) [Field F'] [Finite F']
    (φ : torusH G t (fS (s n) : G) ⧸ CFSG.pPrimeCore 2 (torusH G t (fS (s n) : G)) ≃*
      CFSG.GorensteinWalter.PGL2 F')
    (hcl : TorusNormalizerClauses G t (fS (s n) : G) d (p ^ f) F' φ) :
    ((Nat.card F' : ℕ) : ℤ) + (if Nat.card F' % 4 = 1 then 1 else -1) =
      ((p ^ f : ℕ) : ℤ) + (if p ^ f % 4 = 1 then 1 else -1) := by
  obtain ⟨d₁, J, h⟩ := exists_caseIData G hGnonab hrecognition n hn S fS t ht hnonab hcentral
    hnc p f hp hpodd hf hq hmodel hcov hY hA₀ hN d F' φ hcl
  have hUW := h.card_torusU_eq_card_torusW
  have h1 := h.two_mul_card_U_int
  have h2 := h.two_mul_card_W_int
  rw [hUW] at h1
  rw [← h1, ← h2]

end CFSG.Semidihedral.FixedCoreNontrivial

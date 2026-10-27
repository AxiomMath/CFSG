module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialTorusEqualData
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialTorusPropThree
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterSylow
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterPositive

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem EqualParameterData.false_of_card_sylow {G : Type} [Group G] [Finite G] {t s₀ d d₁ : G}
    {J : Subgroup G} {p f : ℕ} {F : Type} [Field F] [Finite F] {κ : C t →* Equiv.Perm (Omega F)}
    {F' : Type} [Field F'] [Finite F']
    {φ : torusH G t s₀ ⧸ CFSG.pPrimeCore 2 (torusH G t s₀) ≃* CFSG.GorensteinWalter.PGL2 F'}
    (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ)
    (hsyl : ∀ T : Sylow p G, Nat.card T = p ^ f) : False :=
  h.false_of_card_sylow_of_facts hsyl (fun hQ => h.sylow_C_facts hQ)
    h.eq_bot_of_le_centralizer_kleinFour (fun hP => h.sylow_H_facts hP)

theorem trivial_fixed_core_torus_parameter_ne
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
    Nat.card F' ≠ p ^ f := by
  intro hq'
  obtain ⟨d₁, J, F, _, _, κ, h⟩ := exists_equalParameterData G hGnonab hrecognition n hn S fS t
    ht hnonab hcentral hnc p f hp hpodd hf hq hmodel hcov hY hA₀ hN d F' φ hcl hq'
  have hodd := Nat.odd_iff.mp (hpodd.pow : Odd (p ^ f))
  rcases (by omega : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3) with he | he
  · exact h.mod_four_ne_one he
  · exact h.false_of_card_sylow (h.card_sylow_of_mod_four_eq_three he)

end CFSG.Semidihedral.FixedCoreNontrivial

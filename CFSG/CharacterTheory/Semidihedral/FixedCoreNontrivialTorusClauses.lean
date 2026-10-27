module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialTorus
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialClauses

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage

theorem trivial_fixed_core_torus_clauses
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
    (hN : N t ≠ ⊥) :
    ∃ (d : G) (F' : Type) (_ : Field F') (_ : Finite F')
      (φ : torusH G t (fS (s n) : G) ⧸ CFSG.pPrimeCore 2 (torusH G t (fS (s n) : G)) ≃*
        CFSG.GorensteinWalter.PGL2 F'),
      TorusNormalizerClauses G t (fS (s n) : G) d (p ^ f) F' φ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, d, h13, h14, h15, h16, h17, h18, h19,
    h20, F', hF', hF'fin, φ, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ :=
    trivial_fixed_core_torus_normalizer_structure G hGnonab hrecognition n hn S fS t ht hnonab
      hcentral hnc p f hp hpodd hf hq hmodel hcov hY hA₀ hN
  exact ⟨d, F', hF', hF'fin, φ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩

end CFSG.Semidihedral.FixedCoreNontrivial

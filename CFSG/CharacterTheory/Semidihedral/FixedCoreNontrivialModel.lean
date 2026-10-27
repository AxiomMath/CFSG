module

public import CFSG.CharacterTheory.Semidihedral.Principal.FieldFactorOneTorusNormalizerSupport

public section

open scoped Classical

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open
open CFSG.Semidihedral.MatrixCoverData CFSG.Semidihedral.Principal

theorem commute_s_mod_N_of_commute_odd_core {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hC : Nat.card (C t) = 2 * Nat.card (N t) * p ^ f * ((p ^ f) ^ 2 - 1))
    (s : C t) (hs : orderOf s = 2) (hst : s ≠ tInC t)
    (hA₀ : N t ⊓ Subgroup.centralizer ({s} : Set (C t)) = ⊥) :
    ∀ x : ActualFourGroupCentralizer.R s, x ≠ 1 → ∀ c : C t,
      c * ((x : ActualFourGroupCentralizer.D s) : C t) =
        ((x : ActualFourGroupCentralizer.D s) : C t) * c →
      nu t c * nu t s = nu t s * nu t c := by
  obtain ⟨⟨-, F, hF, hFfin, A, a, hcard, hAodd, hAf, -, -, -, -, haF, -, -, -, hdata⟩, -⟩ :=
    ActualFourGroupNormalizer.actual_simple_layer_four_group_normalizer_action.{0} n hn S fS hG t ht
      hnonab hcentral hnc p f hp hpodd hf hmodel
  obtain ⟨Psi, -, hu, hcent, -, -, -, -⟩ := hdata s hs hst
  have hodd : Odd (Nat.card F) := hcard ▸ hpodd.pow
  have hq1 : 1 < p ^ f := Nat.one_lt_pow (by omega) hp.one_lt
  have hNcard : Nat.card (ActualFourGroupCentralizer.N0 s) *
      (ActualFourGroupCentralizer.N0 s).index = Nat.card (N t) :=
    Subgroup.card_mul_index _
  have hA1 : Nat.card A = 1 := by
    have h := hcent.C_card
    rw [hC] at h
    have hpos : 0 < 2 * Nat.card (N t) * p ^ f * ((p ^ f) ^ 2 - 1) := by
      have : 1 < (p ^ f) ^ 2 := by nlinarith
      have : 0 < (p ^ f) ^ 2 - 1 := by omega
      have : 0 < Nat.card (N t) := Nat.card_pos
      positivity
    have h' : (2 * Nat.card (N t) * p ^ f * ((p ^ f) ^ 2 - 1)) * Nat.card A =
        (2 * Nat.card (N t) * p ^ f * ((p ^ f) ^ 2 - 1)) * 1 := by
      rw [mul_one]
      calc 2 * Nat.card (N t) * p ^ f * ((p ^ f) ^ 2 - 1) * Nat.card A
          = 2 * (Nat.card (ActualFourGroupCentralizer.N0 s) *
              (ActualFourGroupCentralizer.N0 s).index) * Nat.card A * p ^ f *
                ((p ^ f) ^ 2 - 1) := by rw [hNcard]; ring
        _ = 2 * Nat.card (N t) * p ^ f * ((p ^ f) ^ 2 - 1) := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos h'
  have hAtriv : ∀ σ : A, σ = 1 := fun σ => by
    have : Subsingleton A := (Nat.card_eq_one_iff_unique.mp hA1).1
    exact Subsingleton.elim _ _
  have hN0R : ActualFourGroupCentralizer.N0InR s = ⊥ := by
    have h := hcent.kernel_original
    have hND : N t ⊓ ActualFourGroupCentralizer.D s = ⊥ := hA₀
    rw [hND] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _
      (fun a b hab => Subtype.ext (Subtype.ext hab))).mp h
  obtain ⟨e, he⟩ := hcent.original_quotient
  intro r hr c hc
  have hw := he r
  set w' := e (QuotientGroup.mk' (ActualFourGroupCentralizer.N0InR s) r) with hw'def
  have hright : w'.right = 1 := hAtriv _
  have hincl : ActualFourGroupCentralizer.originalOddInclusion F A _ _ w' =
      MatrixTorus.originalSlInH F _ A _ w'.left.val.val := by
    rw [ActualFourGroupCentralizer.originalOddInclusion_coordinates, hright]
    rfl
  have hX : w'.left.val.val ∈ MatrixTorus.Torus F (MatrixCover.fixedUnit F A a) :=
    w'.left.val.property
  have hX1 : w'.left.val.val ≠ 1 := by
    intro h
    apply hr
    have hl : w'.left = 1 := Subtype.ext (Subtype.ext h)
    have hw1 : w' = 1 := SemidirectProduct.ext hl hright
    have hmk : QuotientGroup.mk' (ActualFourGroupCentralizer.N0InR s) r = 1 := by
      apply e.injective
      rw [map_one]
      exact hw1
    have hmem : r ∈ (QuotientGroup.mk' (ActualFourGroupCentralizer.N0InR s)).ker := hmk
    rw [QuotientGroup.ker_mk', hN0R] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hXm1 : w'.left.val.val ≠ OddFieldSL2.minusIdentity F := by
    intro h
    have hzz : w'.left.val = MatrixTorus.z F (MatrixCover.fixedUnit F A a) := Subtype.ext h
    have hoddord := (MatrixTorus.mem_W_iff_odd_order F _ hodd haF w'.left.val).mp
      w'.left.property
    rw [hzz, MatrixTorus.z_orderOf F _ hodd] at hoddord
    exact absurd hoddord (by decide)
  have hcomm : Psi.symm (nu t c) * MatrixTorus.originalSlInH F _ A _ w'.left.val.val =
      MatrixTorus.originalSlInH F _ A _ w'.left.val.val * Psi.symm (nu t c) := by
    have h1 : nu t c * nu t ((r : ActualFourGroupCentralizer.D s) : C t) =
        nu t ((r : ActualFourGroupCentralizer.D s) : C t) * nu t c := by
      rw [← map_mul, ← map_mul, hc]
    rw [← hw, hincl] at h1
    apply Psi.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h1
  have hcu := originalH_commute_u_of_commute A hAtriv _ _ hX hX1 hXm1 _ hcomm
  have h3 := congrArg Psi hcu
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hu] at h3
  exact h3

end CFSG.Semidihedral.FixedCoreNontrivial

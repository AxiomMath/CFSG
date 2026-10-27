module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialParameterSumBasic
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialSetup
public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneFamily

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.StationaryConfinement
  (stationary_all_local_prime_covers_confine_every_nontrivial_odd_core_element)

theorem exists_caseIData
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
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
    ∃ (d₁ : G) (J : Subgroup G), CaseIData G t (fS (s n) : G) d d₁ J (p ^ f) F' φ := by
  classical
  obtain ⟨-, ht2, -, hsC, hs2, hst⟩ := Principal.supplied_t_s_facts hn fS ht
  have hG : ∀ U : Subgroup G, U.index ≠ 2 :=
    PerfectLayerNormalization.nonabelian_simple_has_no_subgroup_index_two hGnonab
  obtain ⟨J, d₁, hL, -, hsl2, -, -⟩ := trivial_fixed_core_local_data G hGnonab hrecognition n hn
    S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel hcov hY hA₀
  have : Group.IsPerfect G := Principal.isPerfect_of_isSimpleGroup hGnonab
  refine ⟨d₁, J, ⟨hcl, hL, hsl2, ⟨p, f, hp, hpodd, by omega, rfl⟩, hq, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro hbot
    exact hN ((Subgroup.map_eq_bot_iff_of_injective _ (C t).subtype_injective).mp hbot)
  · exact (stationary_all_local_prime_covers_confine_every_nontrivial_odd_core_element G hGnonab
      hrecognition n hn S fS t (fS (s n)) ht2 hs2 hsC (fun h => hst h.symm) hnonab hcentral hnc
      p f hp hpodd hf (by omega) hmodel hcov).2.1
  · intro x hx
    exact Principal.isConj_of_orderOf_eq_two hn S fS ht hx
  · intro u hu hu2 hut
    exact FieldFactorOne.exists_conj_s0 fS hn ht hu hu2 hut
  · intro x hx hx4
    have hx' : orderOf (⟨x, hx⟩ : C t) = 4 := by rw [Subgroup.orderOf_mk]; exact hx4
    obtain ⟨hK, -⟩ := actual_order_four_residual_and_square n hn S fS hG t ht2 ⟨x, hx⟩ hx'
    have hle : (K t).map (C t).subtype ≤ J ⊔ (N t).map (C t).subtype := by
      rw [K_eq_odd_order_closure, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨y, hy, rfl⟩
      exact hL.odd_mem y y.2 (by show Odd (orderOf (y : G)); rw [Subgroup.orderOf_coe]; exact hy)
    have hJB : x ∈ J ⊔ (N t).map (C t).subtype := hle ⟨⟨x, hx⟩, hK, rfl⟩
    obtain ⟨j, hj, b, hb, rfl⟩ := exists_mul_of_mem_sup hL.JB_comm hJB
    have hcomm : Commute j b := hL.JB_comm j hj b hb
    have h4 : j ^ 4 * b ^ 4 = 1 := by
      rw [← hcomm.mul_pow, ← hx4]
      exact pow_orderOf_eq_one _
    have hb4 : b ^ 4 ∈ J ⊓ (N t).map (C t).subtype := by
      refine ⟨?_, Subgroup.pow_mem _ hb 4⟩
      rw [eq_inv_of_mul_eq_one_right h4]
      exact J.inv_mem (J.pow_mem hj 4)
    rw [hL.JB_disj, Subgroup.mem_bot] at hb4
    have hcop : Nat.Coprime (orderOf b) 4 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr (hL.B_odd b hb))
    have hb1 : b = 1 :=
      orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hb4))
    rw [hb1, mul_one]
    exact hj

end CFSG.Semidihedral.FixedCoreNontrivial

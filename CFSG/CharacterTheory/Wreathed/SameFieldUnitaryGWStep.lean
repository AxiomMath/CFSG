module

public import CFSG.CharacterTheory.Wreathed.SameFieldUnitaryDValue
public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueGWCommon
public import CFSG.GroupTheory.ABGDGroups.HomocyclicSylow
public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueStep

public section

open scoped Classical

namespace CFSG.Wreathed.SameFieldUnitary

open CFSG.Semidihedral.UnitaryDValue CFSG.Semidihedral.UnitaryDValue.DValueData

section Abstract

variable {G : Type} [Group G] [Fintype G] (D : DValueData G)

theorem centralizer_le_normalizer_T {n : ℕ} (hn : 2 ≤ n)
    (eU : D.U ≃* Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n)))
    {w : G} (hw : w ∈ D.W) (hw1 : w ≠ 1) (htw : D.t * w = w * D.t) :
    Subgroup.centralizer {w} ≤ Subgroup.normalizer (D.T : Set G) := by
  have hwC : w ∈ D.C := D.W_le hw
  have hyp := GW.sylowU_hyp D hw hw1 htw
  have hUK : D.U ≤ Subgroup.centralizer ({w} : Set G) := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr (D.C_comm u hu.1 w hwC)
  let eP : (D.sylowU hwC hyp : Subgroup (Subgroup.centralizer ({w} : Set G))) ≃*
      Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n)) :=
    (Subgroup.subgroupOfEquivOfLe hUK).trans eU
  obtain ⟨hMnormal, -⟩ :=
    CFSG.ABGDGroups.homocyclic_sylow_oddCore_sup_index (D.sylowU hwC hyp) hn eP
  exact GW.centralizer_le_normalizer_T_of_normal D hw hw1 htw hMnormal

theorem gwStep_of_homocyclic {n : ℕ} (hn : 2 ≤ n)
    (eU : D.U ≃* Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))) : D.GWStep :=
  fun _ hw hw1 _ htw => Or.inl (centralizer_le_normalizer_T D hn eU hw hw1 htw)

end Abstract

section Wreathed

open CFSG.Wreathed.ActualProjectiveLayer CFSG.Wreathed.OriginalStationarityCoverageCriterion
  CFSG.Wreathed.SmallerRecognitionOriginalField

theorem nonempty_baseSubgroup_mulEquiv (m : ℕ) :
    Nonempty (baseSubgroup m ≃* Multiplicative (ZMod m) × Multiplicative (ZMod m)) := by
  refine ⟨MulEquiv.mk' ((baseCoordinateEquiv m).trans
    (Multiplicative.ofAdd.prodCongr Multiplicative.ofAdd)) fun x y => ?_⟩
  obtain ⟨⟨a, b⟩, rfl⟩ := (baseCoordinateEquiv m).symm.surjective x
  obtain ⟨⟨c, d⟩, rfl⟩ := (baseCoordinateEquiv m).symm.surjective y
  have hmul : (baseCoordinateEquiv m).symm (a, b) * (baseCoordinateEquiv m).symm (c, d) =
      (baseCoordinateEquiv m).symm (a + c, b + d) :=
    Subtype.ext (element_base_mul m a b c d 0)
  simp only [Equiv.trans_apply, hmul, Equiv.apply_symm_apply]
  rfl

theorem U_eq_modelBase {G : Type} [Group G] [Fintype G] {n : ℕ} (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (D : DValueData G)
    (hx : D.x = wreathModelHom S e (Original.x (2 ^ n)))
    (hz : D.z = wreathModelHom S e (Original.x2 (2 ^ n))) (hm : D.m = 2 ^ n) :
    D.U = modelBase S e := by
  have hxU : D.x ∈ modelBase S e := hx ▸ BrauerWong.modelHom_x_mem_modelBase S e
  have hzU : D.z ∈ modelBase S e := hz ▸ BrauerWong.modelHom_x2_mem_modelBase S e
  have hle : modelBase S e ≤ D.U := by
    intro u hu
    refine ⟨D.mem_C_iff.mpr ⟨BrauerWong.modelBase_commute S e _ _ hu hxU,
      BrauerWong.modelBase_commute S e _ _ hu hzU⟩, ?_⟩
    have h := AdaptedBaseFusion.pow_modulus_eq_one_of_mem_modelBase S e hu
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h)
    exact ⟨k, hk⟩
  obtain ⟨k₀, hk₀⟩ := D.m_dvd
  rw [hm] at hk₀
  have hk₀odd : Odd k₀ := by
    have h := D.odd_quot
    rw [hk₀, hm, Nat.mul_div_cancel_left _ (by positivity)] at h
    exact h
  have hUcard : Nat.card D.U = 2 ^ (2 * n) := by
    rw [D.card_primaryPart 2, D.card_C, hm, hk₀]
    congr 1
    have hsplit : 2 ^ n * Nat.card D.A * (2 ^ n * k₀) = 2 ^ (2 * n) * (Nat.card D.A * k₀) := by
      ring
    have hodd : Odd (Nat.card D.A * k₀) := D.A_odd.mul hk₀odd
    rw [hsplit, Nat.factorization_mul (by positivity) (by
        rintro h0; rw [h0] at hodd; exact absurd hodd (by decide)),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hodd)
        (even_iff_two_dvd.mpr h)), add_zero]
  symm
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [hUcard, AdaptedBaseFusion.card_modelBase S e, ← pow_mul, mul_comm]

theorem exists_dValueData_gwStep
    {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hrec : SmallerWreathedRecognition G)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq5 : 5 ≤ p ^ f)
    (hq3 : p ^ f % 4 = 3)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e)
      .PSL 2 p f)
    (hst : OriginalAllPrimeStationarity n S e) (hcov : OriginalAllPrimeCoverage n S e) :
    ∃ D : DValueData G, D.p = p ∧ D.f = f ∧ D.m = 2 ^ n ∧
      D.x = wreathModelHom S e (Original.x (2 ^ n)) ∧
      D.z = wreathModelHom S e (Original.x2 (2 ^ n)) ∧ D.S = S ∧
      D.A = (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype ∧
      D.CharacterExtend ∧ D.PrincipalPair ∧ D.GWStep := by
  obtain ⟨D, hDp, hDf, hDm, hDx, hDz, hDS, hDA, hext, hpair⟩ :=
    exists_dValueData hnonab hrec n hn S e hfour p f hp hpodd hf hq5 hq3 hmodel hst hcov
  obtain ⟨eB⟩ := nonempty_baseSubgroup_mulEquiv (2 ^ n)
  have hU := U_eq_modelBase S e D hDx hDz hDm
  let eU : D.U ≃* Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n)) :=
    (MulEquiv.subgroupCongr hU).trans ((modelBaseEquiv S e).symm.trans eB)
  exact ⟨D, hDp, hDf, hDm, hDx, hDz, hDS, hDA, hext, hpair, gwStep_of_homocyclic D hn eU⟩

end Wreathed

end CFSG.Wreathed.SameFieldUnitary

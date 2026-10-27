module

public import CFSG.CharacterTheory.Wreathed.ConditionalFlatTwistedBasesLocal
public import CFSG.CharacterTheory.Wreathed.ConditionalFlatTwistedBasesTwist
public import CFSG.CharacterTheory.Wreathed.ConditionalGeneralBaseGenericColumns

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.FlatTwistedBases

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.AdaptedBaseFusion CFSG.Wreathed.BrauerWong

variable {G : Type} [Group G] {n : ℕ} {S : Sylow 2 G} {e : S ≃* Wreath (2 ^ n)} {σ υ g : G}
  (h : IsAdaptedBase (modelBase S e) (wreathModelHom S e (Original.a (2 ^ n)))
    (wreathModelHom S e (Original.z (2 ^ n))) σ υ g)

theorem coe_aut_pow_apply (j : ℕ) (u : modelBase S e) :
    (((h.aut ^ j) u : modelBase S e) : G) = (g ^ j)⁻¹ * u * g ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ' h.aut j, MulAut.mul_apply, h.aut_apply_coe, ih, pow_succ g j]
    group

theorem exists_generic_representative [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hn : 2 ≤ n) {u : modelBase S e} (hu : u ∉ h.exc) :
    ∃ u' : modelBase S e, u' ∉ h.exc ∧
      wreathModelHom S e (Original.x (2 ^ n)) ∈ Subgroup.zpowers (u' : G) ∧
      IsConj (u : G) (u' : G) := by
  have cfg := CompatibleFamilies.localConfig S e hnonab hn h.mem_normalizer h.orderOf_conj
  obtain ⟨⟨k, hk1, hk⟩, -⟩ := ConditionalGeneralBase.orderOf_generic h hu
  have hdvd : 2 ^ (k - 1) ∣ orderOf (u : G) := by
    rw [hk]
    exact pow_dvd_pow 2 (Nat.sub_le k 1)
  have hord : orderOf ((u : G) ^ (2 ^ (k - 1))) = 2 := by
    rw [orderOf_pow_of_dvd (by positivity) hdvd, hk, Nat.pow_div (Nat.sub_le k 1) two_pos,
      show k - (k - 1) = 1 by omega, pow_one]
  have hmemU : (u : G) ^ (2 ^ (k - 1)) ∈ modelBase S e := Subgroup.pow_mem _ u.2 _
  have hTU : Subgroup.closure {wreathModelHom S e (Original.x (2 ^ n)),
      wreathModelHom S e (Original.x2 (2 ^ n))} ≤ modelBase S e := by
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | hz
    · exact modelHom_x_mem_modelBase S e
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact modelHom_x2_mem_modelBase S e
  have hcent : (u : G) ^ (2 ^ (k - 1)) ∈ Subgroup.centralizer (Subgroup.closure
      {wreathModelHom S e (Original.x (2 ^ n)), wreathModelHom S e (Original.x2 (2 ^ n))} :
        Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact modelBase_commute S e t _ (hTU ht) hmemU
  have hT := cfg.involution_mem _ hcent hord
  obtain ⟨j, hj⟩ := cfg.eta_cycle _ hT (CompatibleFamilies.ne_one_of_orderOf hord)
  have haut : h.aut ^ j ∈ Subgroup.closure {swapAut S e, h.aut} :=
    Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) j
  refine ⟨(h.aut ^ j) u, not_mem_exc_of_mem_closure h haut hu, ?_, ?_⟩
  · rw [coe_aut_pow_apply h, ← hj]
    have hpow : ((g ^ j)⁻¹ * (u : G) * g ^ j) ^ (2 ^ (k - 1)) =
        (g ^ j)⁻¹ * (u : G) ^ (2 ^ (k - 1)) * g ^ j := by
      have hc := conj_pow (a := (g ^ j)⁻¹) (b := (u : G)) (i := 2 ^ (k - 1))
      rwa [inv_inv] at hc
    rw [← hpow]
    exact Subgroup.npow_mem_zpowers _ _
  · rw [coe_aut_pow_apply h]
    exact isConj_iff.mpr ⟨(g ^ j)⁻¹, by rw [inv_inv]⟩

theorem generic_singleton_basis [Fintype G] (hn : 2 ≤ n) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (lam : involutionCentralizer n S e →* ℂˣ) {u : modelBase S e} (hu : u ∉ h.exc)
    (hxu : wreathModelHom S e (Original.x (2 ^ n)) ∈ Subgroup.zpowers (u : G))
    (localBasis : FiniteIrreducibleCharacterBasis
      (Subgroup.centralizer (Subgroup.zpowers (u : G) : Set G)))
    (ℓ : localBasis.index)
    (hℓ : ∀ c, (localBasis.representation ℓ).character c =
      lam (Subgroup.inclusion (centralizer_zpowers_le_involutionCentralizer S e hxu) c)) :
    SingletonTwistedBasisData localBasis ideal ℓ (fun c => (lam (Subgroup.inclusion
      (centralizer_zpowers_le_involutionCentralizer S e hxu) c) : ℂ)) ((2 ^ n) ^ 2) := by
  obtain ⟨N, hnormal, hodd, hquot, hcomm, hcard⟩ :=
    ConditionalGeneralBase.generic_centralizer_quotient h hn hu
  have := singletonTwistedBasisData_of_comm localBasis ideal (lam.comp (Subgroup.inclusion
    (centralizer_zpowers_le_involutionCentralizer S e hxu))) ℓ hℓ N hodd hquot
  rw [hcard] at this
  exact this

end CFSG.Wreathed.FlatTwistedBases

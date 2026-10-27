module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenProj
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenZsig
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcUntw

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Timmesfeld.ExceptionalOrders
  CFSG.RankThree.PartOne.KFU
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

theorem exists_zsigPrime {f₀ e p : ℕ} (hf₀ : 1 ≤ f₀) (he : 2 ≤ e) (hexc : ¬ (f₀ = 1 ∧ e = 6))
    (hp : p.Prime) (hpe : ¬ p ∣ e) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ (∀ k : ℕ, r ∣ (2 ^ f₀) ^ k - 1 ↔ e ∣ k) ∧
      orderOf (((2 ^ (p * f₀) : ℕ) : ZMod r)) = e := by
  obtain ⟨r, m, hrm, hm, hcorr⟩ := exists_ppd_data hf₀ he hexc
  have hppd := fun k => ppd_dvd_iff hrm hm hcorr hp hpe k
  refine ⟨r, hrm.1, hrm.ne_two hm, fun k => (hppd k).1, ?_⟩
  have key : ∀ k : ℕ, orderOf (((2 ^ (p * f₀) : ℕ) : ZMod r)) ∣ k ↔ e ∣ k := by
    intro k
    rw [orderOf_dvd_iff_pow_eq_one, ← (hppd k).2]
    have h1 : 1 ≤ (2 ^ (p * f₀)) ^ k := Nat.one_le_pow _ _ (by positivity)
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h1, Nat.cast_pow, sub_eq_zero]
    simp
  exact Nat.dvd_antisymm ((key e).2 dvd_rfl) ((key _).1 dvd_rfl)

theorem not_dvd_card_parabolicSubgroup_of_coatoms
    (τ : Tag) {F : Type} [Field F] [Finite F] [Fintype (WeylGroup τ)] {r e : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hrF : ¬ r ∣ Nat.card F)
    (he : orderOf ((Nat.card F : ℕ) : ZMod r) = e)
    (hH : ¬ r ∣ Nat.card (torusGroup τ F)) (coat : Fin τ.rank → ℕ)
    (fsC : Fin τ.rank → List (ℕ × ℕ))
    (hcov : ∀ i k : Fin τ.rank, k ≠ i → k ∈ maskSet τ (coat i))
    (hC : ∀ i q, parabolicSum τ (maskSet τ (coat i)) q =
      ((fsC i).map fun f => geomSum f.1 f.2 q).prod)
    (hGC : ∀ i, GoodFactors r e (fsC i)) (hcnt : ∀ i, cntFactors e (fsC i) = 0)
    (J : Set (Fin τ.rank)) (hJ : J ≠ Set.univ) :
    ¬ r ∣ Nat.card (parabolicSubgroup τ F J) := by
  classical
  haveI : Finite (ModGL τ F) := finite_modGL
  obtain ⟨i, hi⟩ := (Set.ne_univ_iff_exists_notMem J).1 hJ
  have hsub : J ⊆ ((maskSet τ (coat i) : Finset (Fin τ.rank)) : Set (Fin τ.rank)) := fun k hk => by
    exact_mod_cast hcov i k (fun h => hi (h ▸ hk))
  have hle : parabolicSubgroup τ F J ≤
      parabolicSubgroup τ F ((maskSet τ (coat i) : Finset (Fin τ.rank)) : Set (Fin τ.rank)) :=
    ((standard_parabolic_cells τ F).2.2.2.1 J _).2 hsub
  intro hrJ
  have hrC := hrJ.trans (Subgroup.card_dvd_of_le hle)
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  have hfac := factorization_card_parabolicSubgroup τ hr hrF
    ((maskSet τ (coat i) : Finset (Fin τ.rank)) : Set (Fin τ.rank))
  have hprod := (factorization_prod_geomSum hr hr2 hrF hq2 he (fsC i) (hGC i)).2
  rw [← hC i, hcnt i, mul_zero] at hprod
  rw [hprod, Nat.factorization_eq_zero_of_not_dvd hH, add_zero] at hfac
  have := hr.factorization_pos_of_dvd Nat.card_pos.ne' hrC
  omega

theorem not_dvd_card_normalizer_of_adjointEquiv
    (τ : Tag) {F : Type} [Field F] [Finite F] [CharP F 2] {K : Type} [Group K]
    (θ : K ≃* adjointGroup τ F) {r : ℕ}
    (hpar : ∀ J : Set (Fin τ.rank), J ≠ Set.univ → ¬ r ∣ Nat.card (parabolicSubgroup τ F J))
    (R : Subgroup K) (hR2 : IsPGroup 2 R) (hR1 : R ≠ ⊥) :
    ¬ r ∣ Nat.card (Subgroup.normalizer (R : Set K)) := by
  intro hrN
  haveI : Finite (ModGL τ F) := finite_modGL
  obtain ⟨J, hJ, hdvd⟩ := card_dvd_parabolic_of_normalizes τ (U := R.map θ.toMonoidHom)
    (E := Subgroup.normalizer ((R.map θ.toMonoidHom : Subgroup _) : Set _))
    (fun h => hR1 ((Subgroup.map_eq_bot_iff_of_injective _ θ.injective).1 h))
    (hR2.map θ.toMonoidHom) le_rfl
  exact hpar J hJ (hrN.trans ((card_normalizer_dvd_of_mulEquiv θ R).trans hdvd))

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

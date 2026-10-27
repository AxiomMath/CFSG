module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenProj
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenZsig
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcUntw

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KFU
  CFSG.Timmesfeld.ExceptionalOrders
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
  CFSG.LieType.SeitzGeneration

namespace OLExc

theorem orderOf_natCast_eq_of_dvd_iff {r q e : ℕ} (hq : 1 ≤ q)
    (h : ∀ d : ℕ, r ∣ q ^ d - 1 ↔ e ∣ d) : orderOf (q : ZMod r) = e := by
  obtain ⟨o, ho⟩ : ∃ o, orderOf (q : ZMod r) = o := ⟨_, rfl⟩
  have h1 : ∀ d : ℕ, r ∣ q ^ d - 1 ↔ o ∣ d := fun d => dvd_pow_sub_one_iff_orderOf hq ho
  rw [ho]
  exact Nat.dvd_antisymm ((h1 e).1 ((h e).2 dvd_rfl)) ((h o).1 ((h1 o).2 dvd_rfl))

section Chains


theorem not_dvd_card_normalizer_adjoint (τ : Tag) {K : Type} [Field K] [Finite K] [CharP K 2]
    [Fintype (WeylGroup τ)] {r e : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrK : ¬ r ∣ Nat.card K)
    (he : orderOf ((Nat.card K : ℕ) : ZMod r) = e) (hT : ¬ r ∣ Nat.card (torusGroup τ K))
    (coat : Fin τ.rank → ℕ) (fsC : Fin τ.rank → List (ℕ × ℕ))
    (hcov : ∀ i k : Fin τ.rank, k ≠ i → k ∈ maskSet τ (coat i))
    (hC : ∀ i q, parabolicSum τ (maskSet τ (coat i)) q =
      ((fsC i).map fun f => geomSum f.1 f.2 q).prod)
    (hGC : ∀ i, GoodFactors r e (fsC i)) (hcnt : ∀ i, cntFactors e (fsC i) = 0)
    (R : Subgroup (adjointGroup τ K)) (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R) :
    ¬ r ∣ Nat.card (Subgroup.normalizer (R : Set (adjointGroup τ K))) := by
  classical
  intro hdvd
  haveI hfin : Finite (ModGL τ K) := finite_modGL
  obtain ⟨J, hJ, hdvdJ⟩ := card_dvd_parabolic_of_normalizes τ hR hR2 le_rfl
  obtain ⟨i, hi⟩ := (Set.ne_univ_iff_exists_notMem J).1 hJ
  have hsub : J ⊆ ((maskSet τ (coat i) : Finset (Fin τ.rank)) : Set (Fin τ.rank)) :=
    fun k hk => by exact_mod_cast hcov i k (fun h => hi (h ▸ hk))
  have hle : parabolicSubgroup τ K J ≤
      parabolicSubgroup τ K ((maskSet τ (coat i) : Finset (Fin τ.rank)) : Set (Fin τ.rank)) :=
    ((standard_parabolic_cells τ K).2.2.2.1 J _).2 hsub
  have hr' := hdvd.trans (hdvdJ.trans (Subgroup.card_dvd_of_le hle))
  rw [card_parabolicSubgroup_eq] at hr'
  rcases (Nat.Prime.dvd_mul hr).1 hr' with h | h
  · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
    · exact hT h
    · exact hrK (hr.dvd_of_dvd_pow h)
  · have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
    rw [hC i] at h
    obtain ⟨hne, hval⟩ := factorization_prod_geomSum hr hr2 hrK hq2 he (fsC i) (hGC i)
    rw [hcnt i, mul_zero] at hval
    exact absurd hval (hr.factorization_pos_of_dvd hne h).ne'

theorem exists_ppd_prime_not_dvd_normalizer (τ : Tag) {K : Type} [Group K] {F : Type} [Field F]
    [Finite F] [Fintype (WeylGroup τ)] {f f₀ p e : ℕ} (hf : f = p * f₀) (hf₀ : 1 ≤ f₀)
    (hFcard : Nat.card F = 2 ^ f) (θ : K ≃* adjointGroup τ F) (hp : p.Prime) (he2 : 2 ≤ e)
    (he6 : ¬ (f₀ = 1 ∧ e = 6)) (hpe : ¬ p ∣ e)
    (hTor : ∀ r : ℕ, r.Prime → r ∣ Nat.card (torusGroup τ F) → r ∣ Nat.card F - 1)
    (coat : Fin τ.rank → ℕ) (fsC : Fin τ.rank → List (ℕ × ℕ))
    (hcov : ∀ i k : Fin τ.rank, k ≠ i → k ∈ maskSet τ (coat i))
    (hC : ∀ i q, parabolicSum τ (maskSet τ (coat i)) q =
      ((fsC i).map fun f => geomSum f.1 f.2 q).prod)
    (hbound : ∀ i, ∀ g ∈ fsC i, 0 < g.1 ∧ 0 < g.2 ∧ g.2 * g.1 ≤ e)
    (hcnt : ∀ i, cntFactors e (fsC i) = 0) :
    ∃ r : ℕ, r.Prime ∧ r ∣ (2 ^ f₀) ^ e - 1 ∧ ¬ r ∣ 2 ^ f₀ - 1 ∧
      ∀ R : Subgroup K, IsPGroup 2 R → R ≠ ⊥ →
        ¬ r ∣ Nat.card (Subgroup.normalizer (R : Set K)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf1 : 1 ≤ f := by
    rw [hf]
    exact Nat.mul_pos hp.pos hf₀
  haveI : Fintype F := Fintype.ofFinite F
  have hFcard' : Fintype.card F = 2 ^ f := by rw [← Nat.card_eq_fintype_card]; exact hFcard
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hFcard'
  haveI : Finite (ModGL τ F) := finite_modGL
  obtain ⟨r, m, hrm, hm, hcorr⟩ := exists_ppd_data hf₀ he2 he6
  have hppd := fun k => ppd_dvd_iff hrm hm hcorr hp hpe k
  have hr : r.Prime := hrm.1
  have hq2 : 1 < 2 ^ f₀ := Nat.one_lt_two_pow (by omega)
  have hqF : Nat.card F = (2 ^ (p * f₀)) := by rw [hFcard, hf]
  have hrK : ¬ r ∣ Nat.card F := by
    intro h
    rw [hqF] at h
    have h1 : r ∣ (2 ^ (p * f₀)) ^ e - 1 := ((hppd e).2).2 dvd_rfl
    have h2 : r ∣ (2 ^ (p * f₀)) ^ e := h.trans (dvd_pow_self _ (by omega))
    have hpos : 1 ≤ (2 ^ (p * f₀)) ^ e := Nat.one_le_pow _ _ (by positivity)
    have h3 : r ∣ 1 := (Nat.dvd_add_right h1).1 (by rwa [Nat.sub_add_cancel hpos])
    exact hr.one_lt.ne' (Nat.dvd_one.1 h3)
  have hr2 : r ≠ 2 := by
    rintro rfl
    apply hrK
    rw [hFcard]
    exact dvd_pow_self 2 (by omega)
  have hord : orderOf ((Nat.card F : ℕ) : ZMod r) = e := by
    rw [hqF]
    refine orderOf_natCast_eq_of_dvd_iff (Nat.one_le_two_pow) fun d => (hppd d).2
  have hq1F : ¬ r ∣ Nat.card F - 1 := by
    intro h
    rw [hqF] at h
    have h1 : r ∣ (2 ^ (p * f₀)) ^ 1 - 1 := by rwa [pow_one]
    have := ((hppd 1).2).1 h1
    exact absurd (Nat.le_of_dvd one_pos this) (by omega)
  have hrdvd : r ∣ (2 ^ f₀) ^ e - 1 := ((hppd e).1).2 dvd_rfl
  have hrq : ¬ r ∣ 2 ^ f₀ - 1 := by
    intro h
    have h1 : r ∣ (2 ^ f₀) ^ 1 - 1 := by rwa [pow_one]
    have := ((hppd 1).1).1 h1
    exact absurd (Nat.le_of_dvd one_pos this) (by omega)
  refine ⟨r, hr, hrdvd, hrq, fun R hR2 hR1 hrN => ?_⟩
  have hB : ∀ i, GoodFactors r e (fsC i) := fun i =>
    goodFactors_of_bound (by omega) (B := e) (by nlinarith [hr.two_le]) (hbound i)
  refine not_dvd_card_normalizer_adjoint τ hr hr2 hrK hord (fun h => hq1F (hTor r hr h)) coat fsC
    hcov hC hB hcnt (R.map θ.toMonoidHom) ?_ (hR2.map θ.toMonoidHom)
    (hrN.trans (card_normalizer_dvd_of_mulEquiv θ R))
  exact fun h => hR1 ((Subgroup.map_eq_bot_iff_of_injective _ θ.injective).1 h)

end Chains

end OLExc

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

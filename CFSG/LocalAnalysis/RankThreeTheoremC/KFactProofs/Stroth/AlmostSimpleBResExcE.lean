module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResExcFixed
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResOrthFamily
public import CFSG.LieType.SeitzGeneration.ExcTorusThreeCat

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge TauCeti
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevIndexTwo)

section


@[expose] def RankTwoData (τ : Tag) : Prop :=
  ∀ (p : ℕ), p.Prime → 3 < p → ∀ (K : Type) [Field K] [Finite K], ¬ p ∣ Nat.card K →
    ¬ RankLE1 p (adjointGroup τ K) → RankLE2 p (adjointGroup τ K) →
    ∀ (k : Type) [Field k] [Finite k], ¬ p ∣ Nat.card k →
      orderOf ((Nat.card k : ℕ) : ZMod p) = orderOf ((Nat.card K : ℕ) : ZMod p) →
        HasIndepPair p (adjointGroup τ k)

theorem exists_elemAbelian_sq_E6 (k : Type) [Field k] [Finite k] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpk : ¬ p ∣ Nat.card k)
    (hcnt : degCount Tag.E6 (orderOf ((Nat.card k : ℕ) : ZMod p)) = 2) :
    ∃ E : Subgroup (adjointGroup Tag.E6 k), IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card k : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rw [he] at hcnt
  have he0 : e ≠ 0 := he ▸ orderOf_natCast_ne_zero hp hpk
  have hle := le_thirty_of_degCount_pos (τ := Tag.E6) (by simp) (by omega : 0 < degCount Tag.E6 e)
  have h46 : e = 4 ∨ e = 6 := by
    interval_cases e <;> first | (left; rfl) | (right; rfl) | exact absurd hcnt (by decide)
  rcases h46 with rfl | rfl
  · exact (sylowTorus_E6_four k hp he).exists_elemAbelian
  · exact (sylowTorus_E6_six k hp he).exists_elemAbelian

theorem exists_elemAbelian_sq_E7 (k : Type) [Field k] [Finite k] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpk : ¬ p ∣ Nat.card k)
    (hcnt : degCount Tag.E7 (orderOf ((Nat.card k : ℕ) : ZMod p)) = 2) :
    ∃ E : Subgroup (adjointGroup Tag.E7 k), IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card k : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rw [he] at hcnt
  have he0 : e ≠ 0 := he ▸ orderOf_natCast_ne_zero hp hpk
  have hle := le_thirty_of_degCount_pos (τ := Tag.E7) (by simp) (by omega : 0 < degCount Tag.E7 e)
  have h4 : e = 4 := by
    interval_cases e <;> first | rfl | exact absurd hcnt (by decide)
  subst h4
  exact (sylowTorus_E7_four k hp he).exists_elemAbelian

theorem exists_elemAbelian_sq_E8 (k : Type) [Field k] [Finite k] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpk : ¬ p ∣ Nat.card k)
    (hcnt : degCount Tag.E8 (orderOf ((Nat.card k : ℕ) : ZMod p)) = 2) :
    ∃ E : Subgroup (adjointGroup Tag.E8 k), IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card k : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rw [he] at hcnt
  have he0 : e ≠ 0 := he ▸ orderOf_natCast_ne_zero hp hpk
  have hle := le_thirty_of_degCount_pos (τ := Tag.E8) (by simp) (by omega : 0 < degCount Tag.E8 e)
  have h5 : e = 5 ∨ e = 8 ∨ e = 10 ∨ e = 12 := by
    interval_cases e <;> first | (left; rfl) | (right; left; rfl) | (right; right; left; rfl) |
      (right; right; right; rfl) | exact absurd hcnt (by decide)
  rcases h5 with rfl | rfl | rfl | rfl
  · exact (sylowTorus_E8_five k hp he).exists_elemAbelian
  · exact (sylowTorus_E8_eight k hp he).exists_elemAbelian
  · exact (sylowTorus_E8_ten k hp he).exists_elemAbelian
  · exact (sylowTorus_E8_twelve k hp he).exists_elemAbelian

theorem rankTwoData_E6 : RankTwoData Tag.E6 := by
  intro p hp hp3 K _ _ hpK hnr1 hr2 k _ _ hpk hord
  have h1 : 2 ≤ degCount Tag.E6 (orderOf ((Nat.card K : ℕ) : ZMod p)) := by
    by_contra h
    exact hnr1 (rankLE1_E6 K hp hpK (by omega))
  have h3 : degCount Tag.E6 (orderOf ((Nat.card K : ℕ) : ZMod p)) ≤ 2 := by
    by_contra h
    exact not_rankLE2_E6 K hp hp3 hpK (by omega) hr2
  obtain ⟨E, hE, hEc⟩ := exists_elemAbelian_sq_E6 k hp hp3 hpk (by rw [hord]; omega)
  exact hasIndepPair_of_elemAbelian_sq hp hE hEc

theorem rankTwoData_E7 : RankTwoData Tag.E7 := by
  intro p hp hp3 K _ _ hpK hnr1 hr2 k _ _ hpk hord
  have h1 : 2 ≤ degCount Tag.E7 (orderOf ((Nat.card K : ℕ) : ZMod p)) := by
    by_contra h
    exact hnr1 (rankLE1_E7 K hp hpK (by omega))
  have h3 : degCount Tag.E7 (orderOf ((Nat.card K : ℕ) : ZMod p)) ≤ 2 := by
    by_contra h
    exact not_rankLE2_E7 K hp hp3 hpK (by omega) hr2
  obtain ⟨E, hE, hEc⟩ := exists_elemAbelian_sq_E7 k hp hp3 hpk (by rw [hord]; omega)
  exact hasIndepPair_of_elemAbelian_sq hp hE hEc

theorem rankTwoData_E8 : RankTwoData Tag.E8 := by
  intro p hp hp3 K _ _ hpK hnr1 hr2 k _ _ hpk hord
  have h1 : 2 ≤ degCount Tag.E8 (orderOf ((Nat.card K : ℕ) : ZMod p)) := by
    by_contra h
    exact hnr1 (rankLE1_E8 K hp hpK (by omega))
  have h3 : degCount Tag.E8 (orderOf ((Nat.card K : ℕ) : ZMod p)) ≤ 2 := by
    by_contra h
    exact not_rankLE2_E8 K hp hp3 hpK (by omega) hr2
  obtain ⟨E, hE, hEc⟩ := exists_elemAbelian_sq_E8 k hp hp3 hpk (by rw [hord]; omega)
  exact hasIndepPair_of_elemAbelian_sq hp hE hEc

theorem fixesPair_adjointE {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hR : RankTwoData τ)
    {f p : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = 2 ^ f) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hrk1 : ¬ RankLE1 p (adjointGroup τ K)) (hrk2 : RankLE2 p (adjointGroup τ K))
    {α : MulAut (adjointGroup τ K)} (hαp : α ^ p = 1) (hα : α ∉ inner (adjointGroup τ K)) :
    FixesIndepPair p α := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos (by norm_num) f).ne')
  have hp2 : p ≠ 2 := by omega
  have hdet : ¬ p ∣ τ.cartan.det.natAbs := by
    rcases hτ with rfl | rfl | rfl
    · rw [det_cartan_E6]
      intro h
      have := Nat.le_of_dvd (by norm_num) h
      omega
    · rw [det_cartan_E7]
      intro h
      have := Nat.le_of_dvd (by norm_num) h
      omega
    · rw [det_cartan_E8]
      intro h
      have := Nat.le_of_dvd (by norm_num) h
      omega
  obtain ⟨d, T, r, j, ψ, hd, hTo, hc, hαr, hψ⟩ :=
    CFSG.HardMathSupport.Lang.E6Descent.exists_conj_entrywise_of_outer_E τ hτ hf K hK hp hp2 hdet
      α hαp hα
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro hd'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd'))
  have hFk : Nat.card K = Nat.card (fixSubfield T) ^ p := by
    rw [hK, hc, ← pow_mul, hd, mul_comm]
  haveI : Finite (fixSubfield T) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact (pow_pos (by norm_num) d).ne')
  have hpk : ¬ p ∣ Nat.card (fixSubfield T) := fun h => hpK (by rw [hFk]; exact h.pow hp.ne_zero)
  have hord : orderOf ((Nat.card (fixSubfield T) : ℕ) : ZMod p) =
      orderOf ((Nat.card K : ℕ) : ZMod p) := by
    haveI : Fact p.Prime := ⟨hp⟩
    rw [hFk]
    push_cast
    rw [ZMod.pow_card]
  exact fixesPair_of_entrywise_conj T hαr hψ
    (hR p hp (by omega) K hpK hrk1 hrk2 (fixSubfield T) hpk hord)

theorem not_rankLE1_of_sq {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2) : ¬ RankLE1 p G := by
  intro h
  have h1 := h E hE
  rw [hEc] at h1
  have h2 : p < p ^ 2 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

theorem chevTwoOuterFixesPair_E6 : ChevTwoOuterFixesPair LieIndexE6 := by
  intro p hp hp2 L _ _ hrk ⟨d, hchar, hF, ⟨e⟩⟩ hne α hα hαp
  obtain ⟨d, hv⟩ := d
  cases d with
  | E6 q =>
    have hq2 : q.p = 2 := hchar
    by_cases hp3 : p = 3
    · exfalso
      subst hp3
      exact not_rankLE2_cat_E6_three q hv (by omega)
        (RankLE2.of_mulEquiv e (RankLE2.of_pRank hp hrk.le))
    · have hp5 := five_le_of_prime_ne hp hp2 hp3
      obtain ⟨K, _, _, hK, -, ⟨eK⟩⟩ :=
        exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
      let θ : L ≃* adjointGroup Tag.E6 K := e.trans eK
      obtain ⟨hrk2, E, hE, hEc⟩ := rank_data_of_pRank hp hrk θ
      have hK2 : Nat.card K = 2 ^ q.exponent := by rw [hK, PrimePower.card_def, hq2]
      exact FixesIndepPair.of_mulEquiv θ
        (fixesPair_adjointE (τ := Tag.E6) (by simp) rankTwoData_E6 q.exponent_pos K hK2 hp hp5
          (not_rankLE1_of_sq hp hE hEc) hrk2 (α := MulAut.congr θ α)
          (by rw [← map_pow, hαp, map_one]) ((congr_mem_inner_iff θ α).not.2 hα))
  | A _ _ => exact absurd hF (by simp [LieIndexE6])
  | twistedA _ _ => exact absurd hF (by simp [LieIndexE6])
  | B _ _ => exact absurd hF (by simp [LieIndexE6])
  | C _ _ => exact absurd hF (by simp [LieIndexE6])
  | D _ _ => exact absurd hF (by simp [LieIndexE6])
  | twistedD _ _ => exact absurd hF (by simp [LieIndexE6])
  | E7 _ => exact absurd hF (by simp [LieIndexE6])
  | E8 _ => exact absurd hF (by simp [LieIndexE6])
  | F4 _ => exact absurd hF (by simp [LieIndexE6])
  | G2 _ => exact absurd hF (by simp [LieIndexE6])
  | twistedE6 _ => exact absurd hF (by simp [LieIndexE6])
  | trialityD4 _ => exact absurd hF (by simp [LieIndexE6])
  | suzuki _ => exact absurd hF (by simp [LieIndexE6])
  | reeG2 _ => exact absurd hF (by simp [LieIndexE6])
  | reeF4 _ => exact absurd hF (by simp [LieIndexE6])
  | tits => exact absurd hF (by simp [LieIndexE6])

theorem chevTwoOuterFixesPair_E7 : ChevTwoOuterFixesPair LieIndexE7 := by
  intro p hp hp2 L _ _ hrk ⟨d, hchar, hF, ⟨e⟩⟩ hne α hα hαp
  obtain ⟨d, hv⟩ := d
  cases d with
  | E7 q =>
    have hq2 : q.p = 2 := hchar
    by_cases hp3 : p = 3
    · exfalso
      subst hp3
      exact not_rankLE2_cat_E7_three q hv (by omega)
        (RankLE2.of_mulEquiv e (RankLE2.of_pRank hp hrk.le))
    · have hp5 := five_le_of_prime_ne hp hp2 hp3
      obtain ⟨K, _, _, hK, -, ⟨eK⟩⟩ :=
        exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
      let θ : L ≃* adjointGroup Tag.E7 K := e.trans eK
      obtain ⟨hrk2, E, hE, hEc⟩ := rank_data_of_pRank hp hrk θ
      have hK2 : Nat.card K = 2 ^ q.exponent := by rw [hK, PrimePower.card_def, hq2]
      exact FixesIndepPair.of_mulEquiv θ
        (fixesPair_adjointE (τ := Tag.E7) (by simp) rankTwoData_E7 q.exponent_pos K hK2 hp hp5
          (not_rankLE1_of_sq hp hE hEc) hrk2 (α := MulAut.congr θ α)
          (by rw [← map_pow, hαp, map_one]) ((congr_mem_inner_iff θ α).not.2 hα))
  | A _ _ => exact absurd hF (by simp [LieIndexE7])
  | twistedA _ _ => exact absurd hF (by simp [LieIndexE7])
  | B _ _ => exact absurd hF (by simp [LieIndexE7])
  | C _ _ => exact absurd hF (by simp [LieIndexE7])
  | D _ _ => exact absurd hF (by simp [LieIndexE7])
  | twistedD _ _ => exact absurd hF (by simp [LieIndexE7])
  | E6 _ => exact absurd hF (by simp [LieIndexE7])
  | E8 _ => exact absurd hF (by simp [LieIndexE7])
  | F4 _ => exact absurd hF (by simp [LieIndexE7])
  | G2 _ => exact absurd hF (by simp [LieIndexE7])
  | twistedE6 _ => exact absurd hF (by simp [LieIndexE7])
  | trialityD4 _ => exact absurd hF (by simp [LieIndexE7])
  | suzuki _ => exact absurd hF (by simp [LieIndexE7])
  | reeG2 _ => exact absurd hF (by simp [LieIndexE7])
  | reeF4 _ => exact absurd hF (by simp [LieIndexE7])
  | tits => exact absurd hF (by simp [LieIndexE7])

theorem chevTwoOuterFixesPair_E8 : ChevTwoOuterFixesPair LieIndexE8 := by
  intro p hp hp2 L _ _ hrk ⟨d, hchar, hF, ⟨e⟩⟩ hne α hα hαp
  obtain ⟨d, hv⟩ := d
  cases d with
  | E8 q =>
    have hq2 : q.p = 2 := hchar
    by_cases hp3 : p = 3
    · exfalso
      subst hp3
      exact not_rankLE2_cat_E8_three q hv (by omega)
        (RankLE2.of_mulEquiv e (RankLE2.of_pRank hp hrk.le))
    · have hp5 := five_le_of_prime_ne hp hp2 hp3
      obtain ⟨K, _, _, hK, -, ⟨eK⟩⟩ :=
        exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
      let θ : L ≃* adjointGroup Tag.E8 K := e.trans eK
      obtain ⟨hrk2, E, hE, hEc⟩ := rank_data_of_pRank hp hrk θ
      have hK2 : Nat.card K = 2 ^ q.exponent := by rw [hK, PrimePower.card_def, hq2]
      exact FixesIndepPair.of_mulEquiv θ
        (fixesPair_adjointE (τ := Tag.E8) (by simp) rankTwoData_E8 q.exponent_pos K hK2 hp hp5
          (not_rankLE1_of_sq hp hE hEc) hrk2 (α := MulAut.congr θ α)
          (by rw [← map_pow, hαp, map_one]) ((congr_mem_inner_iff θ α).not.2 hα))
  | A _ _ => exact absurd hF (by simp [LieIndexE8])
  | twistedA _ _ => exact absurd hF (by simp [LieIndexE8])
  | B _ _ => exact absurd hF (by simp [LieIndexE8])
  | C _ _ => exact absurd hF (by simp [LieIndexE8])
  | D _ _ => exact absurd hF (by simp [LieIndexE8])
  | twistedD _ _ => exact absurd hF (by simp [LieIndexE8])
  | E6 _ => exact absurd hF (by simp [LieIndexE8])
  | E7 _ => exact absurd hF (by simp [LieIndexE8])
  | F4 _ => exact absurd hF (by simp [LieIndexE8])
  | G2 _ => exact absurd hF (by simp [LieIndexE8])
  | twistedE6 _ => exact absurd hF (by simp [LieIndexE8])
  | trialityD4 _ => exact absurd hF (by simp [LieIndexE8])
  | suzuki _ => exact absurd hF (by simp [LieIndexE8])
  | reeG2 _ => exact absurd hF (by simp [LieIndexE8])
  | reeF4 _ => exact absurd hF (by simp [LieIndexE8])
  | tits => exact absurd hF (by simp [LieIndexE8])

end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

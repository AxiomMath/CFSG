module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.LieDispatch
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.Transfer
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.SigmaDich
public import CFSG.GroupTheory.WeirSylow.Orthogonal
public import CFSG.ClassicalInvolution.Orders.OrthogonalIndex
import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

namespace CrossOmega

section Transfer

open CFSG.Open CFSG.ClassicalGroups.Orthogonal Module QuadraticMap

theorem mem_commutator_of_coe_mem {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {g : ↥(TauCeti.QuadraticMap.orthogonalGroup Q)}
    (hg : (g : V ≃ₗ[K] V) ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆) :
    g ∈ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := by
  rw [← Subgroup.map_subtype_commutator] at hg
  obtain ⟨g', hg', hgg'⟩ := hg
  rwa [← Subtype.ext hgg']

theorem not_dvd_index_commutator_of_sq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {O : Type*} [Group O]
    [Finite O] (hsq : ∀ g : O, g ^ 2 ∈ commutator O) : ¬ p ∣ (commutator O).index := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro hd
  rw [Subgroup.index] at hd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hd
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hx2 : (QuotientGroup.mk g : O ⧸ commutator O) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 (hsq g)
  have h2 : orderOf (QuotientGroup.mk g : O ⧸ commutator O) ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
  rw [hx] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)

theorem not_dvd_card_ker_of_sq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {G H : Type} [Group G]
    [Finite G] [Group H] (π : G →* H) (hker : ∀ x, π x = 1 → x ^ 2 = 1) :
    ¬ p ∣ Nat.card π.ker := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro hd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hd
  have hx2 : x ^ 2 = 1 := Subtype.ext (hker x.1 x.2)
  have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
  rw [hx] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)

theorem sylowDichotomyAt_projOmega {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι]
    [DecidableEq ι] {Q : QuadraticForm F (ι → F)} {Q₀ : (ι → F) → F} (hQ0 : ⇑Q = Q₀)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule F (ι → F), finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hO : SylowDichotomyAt ↥(TauCeti.QuadraticMap.orthogonalGroup Q) p) :
    SylowDichotomyAt (StatedProj (StatedOmega Q₀)) p := by
  classical
  obtain ⟨-, -, -, -, -, hsq', -, -, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have hsq : ∀ g : ↥(TauCeti.QuadraticMap.orthogonalGroup Q),
      g ^ 2 ∈ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := fun g =>
    mem_commutator_of_coe_mem (by simpa using hsq' (g : (ι → F) ≃ₗ[F] (ι → F)) g.2)
  haveI : Nontrivial (ι → F) := by
    obtain ⟨T, hT3, -⟩ := hT
    refine Module.nontrivial_of_finrank_pos (R := F) ?_
    have := Submodule.finrank_le T
    omega
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO'
  let Θ₁ : ↥O →* GL ι F := (toLinEquiv ι F).symm.toMonoidHom.comp O.subtype
  have hΘ₁ : ∀ x : ↥O, toLinEquiv ι F (Θ₁ x) = (x : (ι → F) ≃ₗ[F] (ι → F)) := fun x =>
    MulEquiv.apply_symm_apply _ _
  have hmemΩ : ∀ A : GL ι F, A ∈ StatedOmega Q₀ ↔ toLinEquiv ι F A ∈ ⁅O, O⁆ := fun A => by
    rw [statedOmega_eq_comap hQ0, Subgroup.mem_comap]
    rfl
  have hΘ₁Ω : ∀ x ∈ commutator ↥O, Θ₁ x ∈ StatedOmega Q₀ := by
    intro x hx
    rw [hmemΩ, hΘ₁]
    have : (x : (ι → F) ≃ₗ[F] (ι → F)) ∈ (commutator ↥O).map O.subtype := ⟨x, hx, rfl⟩
    rwa [Subgroup.map_subtype_commutator] at this
  let Θ₂ : ↥(commutator ↥O) →* ↥(StatedOmega Q₀) :=
    (Θ₁.comp (commutator ↥O).subtype).codRestrict (StatedOmega Q₀) (fun x => hΘ₁Ω x x.2)
  let pj : ↥(commutator ↥O) →* StatedProj (StatedOmega Q₀) :=
    (QuotientGroup.mk' ((StatedScalars ι F).subgroupOf (StatedOmega Q₀))).comp Θ₂
  have hker : ∀ x : ↥(commutator ↥O), pj x = 1 → x ^ 2 = 1 := by
    intro x hx
    have h1 : Θ₂ x ∈ (StatedScalars ι F).subgroupOf (StatedOmega Q₀) :=
      (QuotientGroup.eq_one_iff _).1 hx
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : ((x : ↥O) : (ι → F) ≃ₗ[F] (ι → F)) ∈ scalars F (ι → F) := by
      have := (mem_statedScalars_iff _).1 h1
      rwa [show ((Θ₂ x : ↥(StatedOmega Q₀)) : GL ι F) = Θ₁ (x : ↥O) from rfl, hΘ₁] at this
    obtain ⟨a₀, ha₀⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_map_ne_zero hQ
    obtain ⟨c, hc, hcv⟩ :=
      CFSG.RankThree.Classical.exists_sq_eq_one_of_mem_scalars h2 (x : ↥O).2 ha₀
    apply Subtype.ext
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_one]
    refine LinearEquiv.ext fun v => ?_
    rw [pow_two, LinearEquiv.mul_apply, hcv v, map_smul, hcv v, smul_smul, ← _root_.sq, hc,
      one_smul]
    rfl
  have hsurj : Function.Surjective pj := by
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
    have hz : toLinEquiv ι F (z : GL ι F) ∈ ⁅O, O⁆ := (hmemΩ _).1 z.2
    rw [← Subgroup.map_subtype_commutator] at hz
    obtain ⟨x, hx, hxz⟩ := hz
    refine ⟨⟨x, hx⟩, ?_⟩
    have h1 : Θ₂ ⟨x, hx⟩ = z := Subtype.ext (by
      show Θ₁ x = (z : GL ι F)
      apply (toLinEquiv ι F).injective
      rw [hΘ₁]
      exact hxz)
    show QuotientGroup.mk' _ (Θ₂ ⟨x, hx⟩) = _
    rw [h1]
    rfl
  have hN : SylowDichotomyAt ↥(commutator ↥O) p :=
    SylowDichotomyAt.of_normal_coprime_index hp (commutator ↥O)
      (not_dvd_index_commutator_of_sq hp hp2 hsq) hO
  exact SylowDichotomyAt.of_surjective_coprime_ker hp pj hsurj
    (not_dvd_card_ker_of_sq hp hp2 pj hker) hN

end Transfer

section Weir

open CFSG.GroupTheory.WeirSylow Module QuadraticMap

theorem exists_sigmaModel_sylow_orthogonal_odd {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {K : Type}
    [Field K] [Fintype K] (hK : Odd (Fintype.card K)) (hpK : ¬ p ∣ Fintype.card K) {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {n : ℕ}
    (hdim : finrank K V = 2 * n + 1) {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate) :
    ∃ N : ℕ, ∀ P : Sylow p ↥(TauCeti.QuadraticMap.orthogonalGroup Q),
      Nonempty (P ≃* sigmaModel p (weirE p K) (weirA p K) N) := by
  have hp : p.Prime := Fact.out
  refine ⟨if Even (weirE p K) then 2 * n else n, fun P => ?_⟩
  obtain ⟨P'⟩ : Nonempty (Sylow p (StatedSp n K)) := inferInstance
  obtain ⟨e₁⟩ := sylow_orthogonal_odd (hp.odd_of_ne_two hp2) hK hpK hdim Q hQ P P'
  obtain ⟨e₂⟩ := sylow_Sp (hp.odd_of_ne_two hp2) K hpK n P'
  exact ⟨e₁.trans e₂⟩

theorem exists_sigmaModel_sylow_orthogonal_even {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {K : Type}
    [Field K] [Fintype K] (hpK : ¬ p ∣ Fintype.card K) {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {n : ℕ} (hn : 1 ≤ n) (hdim : finrank K V = 2 * n)
    {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate) {ε : ℤ}
    (hε : (ε = 1 ∧ IsPlusType Q) ∨ (ε = -1 ∧ IsMinusType Q)) :
    ∃ N : ℕ, ∀ P : Sylow p ↥(TauCeti.QuadraticMap.orthogonalGroup Q),
      Nonempty (P ≃* sigmaModel p (weirE p K) (weirA p K) N) := by
  have hp : p.Prime := Fact.out
  have hp1 := hp.odd_of_ne_two hp2
  obtain ⟨P₀⟩ : Nonempty (Sylow p ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) := inferInstance
  by_cases hc : (p : ℤ) ∣ (Fintype.card K : ℤ) ^ n + ε
  · have hc' : ¬ (p : ℤ) ∣ (Fintype.card K : ℤ) ^ n - ε :=
      (sylow_orthogonal_even hp1 hpK hn hdim Q hQ hε P₀).2.2.resolve_left (not_not.2 hc)
    refine ⟨if Even (weirE p K) then 2 * (n - 1) else n - 1, fun P => ?_⟩
    obtain ⟨P'⟩ : Nonempty (Sylow p (StatedSp (n - 1) K)) := inferInstance
    obtain ⟨e₁⟩ := (sylow_orthogonal_even hp1 hpK hn hdim Q hQ hε P).2.1 hc' P'
    obtain ⟨e₂⟩ := sylow_Sp hp1 K hpK (n - 1) P'
    exact ⟨e₁.trans e₂⟩
  · refine ⟨if Even (weirE p K) then 2 * n else n, fun P => ?_⟩
    obtain ⟨P'⟩ : Nonempty (Sylow p (StatedSp n K)) := inferInstance
    obtain ⟨e₁⟩ := (sylow_orthogonal_even hp1 hpK hn hdim Q hQ hε P).1 hc P'
    obtain ⟨e₂⟩ := sylow_Sp hp1 K hpK n P'
    exact ⟨e₁.trans e₂⟩

private def minusHalfMap (n : ℕ) (F : Type) [Field F] :
    (Fin (n - 1) → F) →ₗ[F] (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) where
  toFun y := Sum.elim y (0 : Fin (n - 1) ⊕ Fin 2 → F)
  map_add' _ _ := by
    funext i
    rcases i with i | i <;> simp
  map_smul' _ _ := by
    funext i
    rcases i with i | i <;> simp

theorem isMinusType_quadMinus {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    IsMinusType (CFSG.LieType.Universal.Spin.quadMinus n F b c) := by
  refine ⟨?_, not_isPlusType_quadMinus hn hirr⟩
  have hj : Function.Injective (minusHalfMap n F) := fun x y hxy =>
    funext fun i => congrFun hxy (.inl i)
  refine ⟨LinearMap.range (minusHalfMap n F), ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hj, Module.finrank_fin_fun, finrank_quadMinus_space hn]
    omega
  · rintro _ ⟨y, rfl⟩
    rw [CFSG.LieType.Universal.Spin.quadMinus_apply]
    simp [minusHalfMap]

end Weir

theorem not_dvd_card_of_card_eq_pow {p ℓ f : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (hpℓ : p ≠ ℓ)
    {F : Type} [Fintype F] (hF : Nat.card F = ℓ ^ f) : ¬ p ∣ Fintype.card F := by
  rw [← Nat.card_eq_fintype_card, hF]
  intro hd
  exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow hd))

end CrossOmega

open CrossOmega CFSG.GroupTheory.WeirSylow Module

theorem sdLieCross_POmegaOdd : SDLieCrossAt .POmegaOdd := by
  intro K _ _ _ _ n ℓ f hadm hmodel p hp h5 hpℓ _
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hmodel.statedClassicalModel (by decide)
  have hn : 3 ≤ n := hadm.2.2.1
  have hℓ : ℓ.Prime := hadm.1
  have hℓ2 : ℓ ≠ 2 := hadm.2.2.2
  have hp2 : p ≠ 2 := by omega
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP F ℓ := charP_of_card_eq_prime_pow (p := ℓ) (f := f)
    (by rw [← Nat.card_eq_fintype_card]; exact hF)
  have h2 : ringChar F ≠ 2 := by rw [ringChar.eq F ℓ]; exact hℓ2
  have hpq : ¬ p ∣ Fintype.card F := not_dvd_card_of_card_eq_pow hp hℓ hpℓ hF
  obtain ⟨hQnd, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadOdd (K := F) (n := n)
    (Ring.two_ne_zero h2) hn
  have hdim : finrank F (Fin n ⊕ Fin n ⊕ Unit → F) = 2 * n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    omega
  obtain ⟨N, hN⟩ := exists_sigmaModel_sylow_orthogonal_odd hp2
    (Nat.odd_iff.2 (FiniteField.odd_card_of_char_ne_two h2)) hpq hdim hQnd
  exact SylowDichotomyAt.of_mulEquiv hp e (sylowDichotomyAt_projOmega
    (CFSG.LieType.Universal.Spin.coe_quadOdd n F) hQnd hT hp hp2
    (SylowDichotomyAt.of_sylow_sigmaModel hp h5 (one_le_weirA hpq) hN))

theorem sdLieCross_POmegaPlus : SDLieCrossAt .POmegaPlus := by
  intro K _ _ _ _ n ℓ f hadm hmodel p hp h5 hpℓ _
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hmodel.statedClassicalModel (by decide)
  have hn : 4 ≤ n := hadm.2.2
  have hℓ : ℓ.Prime := hadm.1
  have hp2 : p ≠ 2 := by omega
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hpq : ¬ p ∣ Fintype.card F := not_dvd_card_of_card_eq_pow hp hℓ hpℓ hF
  obtain ⟨hQnd, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := F) (n := n)
    (by omega)
  have hdim : finrank F (Fin n ⊕ Fin n → F) = 2 * n := finrank_quadPlus_space n
  obtain ⟨N, hN⟩ := exists_sigmaModel_sylow_orthogonal_even hp2 hpq (by omega) hdim hQnd
    (ε := 1) (Or.inl ⟨rfl, isPlusType_quadPlus F n⟩)
  exact SylowDichotomyAt.of_mulEquiv hp e (sylowDichotomyAt_projOmega
    (CFSG.LieType.Universal.Spin.coe_quadPlus n F) hQnd hT hp hp2
    (SylowDichotomyAt.of_sylow_sigmaModel hp h5 (one_le_weirA hpq) hN))

theorem sdLieCross_POmegaMinus : SDLieCrossAt .POmegaMinus := by
  intro K _ _ _ _ n ℓ f hadm hmodel p hp h5 hpℓ _
  obtain ⟨-, F, _, _, hF, b, c, hirr, ⟨e⟩⟩ := hmodel.statedClassicalModel (by decide)
  have hn : 4 ≤ n := hadm.2.2
  have hℓ : ℓ.Prime := hadm.1
  have hp2 : p ≠ 2 := by omega
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hpq : ¬ p ∣ Fintype.card F := not_dvd_card_of_card_eq_pow hp hℓ hpℓ hF
  obtain ⟨hQnd, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (K := F) (n := n) hn
    hirr
  have hdim : finrank F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) = 2 * n :=
    finrank_quadMinus_space (by omega)
  obtain ⟨N, hN⟩ := exists_sigmaModel_sylow_orthogonal_even hp2 hpq (by omega) hdim hQnd
    (ε := -1) (Or.inr ⟨rfl, isMinusType_quadMinus (by omega) hirr⟩)
  exact SylowDichotomyAt.of_mulEquiv hp e (sylowDichotomyAt_projOmega
    (CFSG.LieType.Universal.Spin.coe_quadMinus n F b c) hQnd hT hp hp2
    (SylowDichotomyAt.of_sylow_sigmaModel hp h5 (one_le_weirA hpq) hN))

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

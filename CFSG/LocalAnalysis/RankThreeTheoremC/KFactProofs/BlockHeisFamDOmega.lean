module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisHomC
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossOmega
import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Assembly.LowTwoRank CFSG.Open CFSG.GroupTheory.WeirSylow Module QuadraticMap
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis.CrossOmega

section Transfer

open CFSG.ClassicalGroups.Orthogonal

theorem heisD_sylowShape_statedProj_statedOmega {F : Type} [Field F] [Finite F] {ι : Type}
    [Fintype ι] [DecidableEq ι] {Q : QuadraticForm F (ι → F)} {Q₀ : (ι → F) → F} (hQ0 : ⇑Q = Q₀)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule F (ι → F), finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {M : Type*} [Group M]
    (hO : ∀ P : Sylow p ↥(TauCeti.QuadraticMap.orthogonalGroup Q), Nonempty (↥P ≃* M)) :
    ∀ S : Sylow p (StatedProj (StatedOmega Q₀)), Nonempty (↥S ≃* M) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite ((ι → F) ≃ₗ[F] (ι → F)) :=
    Finite.of_injective (fun g : (ι → F) ≃ₗ[F] (ι → F) => (g : (ι → F) → (ι → F)))
      fun g₁ g₂ h => LinearEquiv.ext (congrFun h)
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
  have hidx : ¬ p ∣ (commutator ↥O).index := not_dvd_index_commutator_of_sq hp hp2 hsq
  have hN : ∀ P : Sylow p ↥(commutator ↥O), Nonempty (↥P ≃* M) := by
    refine sylowShape_of_injective (commutator ↥O).subtype (commutator ↥O).subtype_injective ?_
      hO
    rw [← Subgroup.card_mul_index (commutator ↥O),
      Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite]
    simp [Nat.factorization_eq_zero_of_not_dvd hidx]
  exact sylowShape_of_surjective pj hsurj (not_dvd_card_ker_of_sq hp hp2 pj hker) hN

end Transfer

theorem heisD_sylowShape_of_mulEquiv {X Y : Type} [Group X] [Group Y] [Finite Y] {p : ℕ}
    [Fact p.Prime] {M : Type*} [Group M] (e : X ≃* Y)
    (hY : ∀ S : Sylow p Y, Nonempty (↥S ≃* M)) : ∀ S : Sylow p X, Nonempty (↥S ≃* M) := by
  have hker : ¬ p ∣ Nat.card (e.symm.toMonoidHom).ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 e.symm.injective, Subgroup.card_bot]
    exact (Fact.out : p.Prime).not_dvd_one
  exact sylowShape_of_surjective e.symm.toMonoidHom e.symm.surjective hker hY

theorem heisD_exists_sigmaModel_sylow_of_form {X : Type} [Group X] {K : Type} [Field K] [Fintype K]
    {ι : Type} [Fintype ι] [DecidableEq ι] {n f : ℕ} (hn : 1 ≤ n) (hK : Fintype.card K = 2 ^ f)
    {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ0 : ⇑Q = Q₀)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hdim : finrank K (ι → K) = 2 * n) {ε : ℤ}
    (hε : (ε = 1 ∧ IsPlusType Q) ∨ (ε = -1 ∧ IsMinusType Q))
    (e : X ≃* StatedProj (StatedOmega Q₀)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    1 ≤ padicValNat p ((2 ^ f) ^ orderOf ((2 ^ f : ℕ) : ZMod p) - 1) ∧
      ∃ N : ℕ, ∀ S : Sylow p X, Nonempty (↥(S : Subgroup X) ≃*
        sigmaModel p (orderOf ((2 ^ f : ℕ) : ZMod p))
          (padicValNat p ((2 ^ f) ^ orderOf ((2 ^ f : ℕ) : ZMod p) - 1)) N) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpK : ¬ p ∣ Fintype.card K := by
    rw [hK]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  have hE : weirE p K = orderOf ((2 ^ f : ℕ) : ZMod p) := by
    show orderOf ((Fintype.card K : ℕ) : ZMod p) = _
    rw [hK]
  have hA : weirA p K = padicValNat p ((2 ^ f) ^ orderOf ((2 ^ f : ℕ) : ZMod p) - 1) := by
    show padicValNat p (Fintype.card K ^ weirE p K - 1) = _
    rw [hE, hK]
  obtain ⟨N, hN⟩ := exists_sigmaModel_sylow_orthogonal_even hp2 hpK hn hdim hQ hε
  have hS := heisD_sylowShape_statedProj_statedOmega hQ0 hQ hT hp hp2 hN
  rw [hE, hA] at hS
  refine ⟨?_, N, heisD_sylowShape_of_mulEquiv e hS⟩
  rw [← hA]
  exact one_le_weirA hpK

theorem heisD_exists_sigmaModel_sylow_of_omegaModel {X : Type} [Group X] {t : StatedLieTag}
    {n f : ℕ} (ht : t = .POmegaPlus ∨ t = .POmegaMinus) (h : StatedClassicalModel X t n 2 f)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    1 ≤ padicValNat p ((2 ^ f) ^ orderOf ((2 ^ f : ℕ) : ZMod p) - 1) ∧
      ∃ N : ℕ, ∀ S : Sylow p X, Nonempty (↥(S : Subgroup X) ≃*
        sigmaModel p (orderOf ((2 ^ f : ℕ) : ZMod p))
          (padicValNat p ((2 ^ f) ^ orderOf ((2 ^ f : ℕ) : ZMod p) - 1)) N) := by
  rcases ht with rfl | rfl
  · obtain ⟨⟨-, -, hn⟩, K, _, _, hK, ⟨e⟩⟩ := h
    haveI : Fintype K := Fintype.ofFinite K
    have hcard : Fintype.card K = 2 ^ f := by rw [← Nat.card_eq_fintype_card, hK]
    obtain ⟨hQnd, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := K) (n := n)
      (by omega)
    exact heisD_exists_sigmaModel_sylow_of_form (by omega) hcard
      (CFSG.LieType.Universal.Spin.coe_quadPlus n K) hQnd hT (finrank_quadPlus_space n)
      (ε := 1) (Or.inl ⟨rfl, isPlusType_quadPlus K n⟩) e hp hp2
  · obtain ⟨⟨-, -, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h
    haveI : Fintype K := Fintype.ofFinite K
    have hcard : Fintype.card K = 2 ^ f := by rw [← Nat.card_eq_fintype_card, hK]
    obtain ⟨hQnd, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (K := K) (n := n) hn
      hirr
    exact heisD_exists_sigmaModel_sylow_of_form (by omega) hcard
      (CFSG.LieType.Universal.Spin.coe_quadMinus n K b c) hQnd hT
      (finrank_quadMinus_space (by omega)) (ε := -1)
      (Or.inr ⟨rfl, isMinusType_quadMinus (by omega) hirr⟩) e hp hp2

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

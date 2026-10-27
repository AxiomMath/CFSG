module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaOuterOrders
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenOuterOmega
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup QuadraticMap Matrix Module CFSG.ClassicalGroups.Orthogonal
open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatLeafProof (fixedInnerEquiv)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical

open scoped commutatorElement in
theorem commutator_eq_top_of_isSimpleGroup_of_not_prime {P : Type*} [Group P] [Finite P]
    (hs : IsSimpleGroup P) (hp : ¬ (Nat.card P).Prime) : commutator P = ⊤ := by
  rcases hs.eq_bot_or_eq_top_of_normal (commutator P) with h | h
  · exfalso
    have hcomm : ∀ a b : P, a * b = b * a := fun a b => by
      have hc : ⁅a, b⁆ ∈ commutator P := by
        rw [_root_.commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hc
    have h1 : Nat.card P ≠ 1 := by
      intro h1
      obtain ⟨a, b, hab⟩ := hs.exists_pair_ne
      exact hab ((Nat.card_eq_one_iff_unique.1 h1).1.elim a b)
    obtain ⟨p, hpp, hpd⟩ := Nat.exists_prime_and_dvd h1
    have : Fact p.Prime := ⟨hpp⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpd
    have hxn : (Subgroup.zpowers x).Normal :=
      ⟨fun y hy g => by rw [hcomm g y, mul_inv_cancel_right]; exact hy⟩
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.zpowers x) with h2 | h2
    · have : x = 1 := by
        have := Subgroup.mem_zpowers x
        rwa [h2, Subgroup.mem_bot] at this
      rw [this, orderOf_one] at hx
      exact hpp.one_lt.ne hx
    · apply hp
      rw [← Subgroup.card_top (G := P), ← h2, Nat.card_zpowers, hx]
      exact hpp
  · exact h

theorem commutator_top_transfer {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : commutator A = ⊤) : commutator B = ⊤ := by
  rw [_root_.commutator_def] at h ⊢
  have h1 := congrArg (Subgroup.map e.toMonoidHom) h
  rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.surjective] at h1
  exact h1

theorem not_prime_of_four_dvd {x : ℕ} (h : 4 ∣ x) : ¬ x.Prime := by
  intro hx
  have h2 : 2 ∣ x := (show 2 ∣ 4 by norm_num).trans h
  rcases (Nat.dvd_prime hx).1 h2 with h2 | h2
  · omega
  · rw [← h2] at h
    omega

theorem four_dvd_card_of_lieModel {Y : Type} [Group Y] {τ : StatedLieTag} {N g : ℕ}
    (hτ : τ = .POmegaPlus ∨ τ = .POmegaMinus) (hN : 2 ≤ N) (hg : 1 ≤ g)
    (hY : LieModel Y τ N 2 g) : 4 ∣ Nat.card Y := by
  have h4 : 4 ∣ (2 ^ g) ^ (N * (N - 1)) := by
    rw [← pow_mul]
    have h1 : 1 ≤ N - 1 := by omega
    have h2 : 2 ≤ N * (N - 1) := by nlinarith
    have h3 : 2 ≤ g * (N * (N - 1)) := by nlinarith
    exact (show 4 = 2 ^ 2 by norm_num) ▸ pow_dvd_pow 2 h3
  rcases hτ with rfl | rfl
  · rw [F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide) hY]
    change 4 ∣ Open.ordD N (2 ^ g)
    rw [ordD_two_pow_eq hg (by omega), mul_assoc]
    exact Dvd.dvd.mul_right h4 _
  · rw [F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide) hY]
    change 4 ∣ Open.ordTwistedD N (2 ^ g)
    rw [ordTwistedD_two_pow_eq hg (by omega), mul_assoc]
    exact Dvd.dvd.mul_right h4 _

theorem commutator_eq_top_of_lieModel_POmega {Y : Type} [Group Y] [Finite Y] {τ : StatedLieTag}
    {N g : ℕ} (hτ : τ = .POmegaPlus ∨ τ = .POmegaMinus) (hN : 2 ≤ N) (hg : 1 ≤ g)
    (hY : LieModel Y τ N 2 g) : commutator Y = ⊤ :=
  commutator_eq_top_of_isSimpleGroup_of_not_prime
    (LinearPilot.isSimpleGroup_of_lieModel_POmega hτ hY)
    (not_prime_of_four_dvd (four_dvd_card_of_lieModel hτ hN hg hY))

section Field

variable {K' : Type} [Field K'] [Finite K'] {f N : ℕ}

theorem exists_lieModel_le_fixedSubgroup_of_field (hf : 1 ≤ f) (hK : Nat.card K' = 2 ^ f)
    (hN : 4 ≤ N) {Q : QuadraticForm K' (Fin (2 * N) → K')} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K' (Fin (2 * N) → K'), Module.finrank K' T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) {γ : MulAut (matrixProjectiveDerived Q)}
    (hγ : γ ∈ matrixProjectiveImage Q) (hγ2 : orderOf γ = 2) {S : similarityPairs Q}
    (hS : S ∈ unitMultiplierPairs Q) (hSγ : matrixProjectiveConjugationHom Q S = γ)
    (hσ1 : S.val.right ≠ 1) :
    Even f ∧ ∃ (τ : StatedLieTag) (P : Subgroup (matrixProjectiveDerived Q)),
      (τ = .POmegaPlus ∨ τ = .POmegaMinus) ∧ P ≤ fixedSubgroup γ ∧ commutator P = ⊤ ∧
      LieModel P τ N 2 (f / 2) := by
  have : CharP K' 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  have := finite_mulAut_matrixProjectiveDerived Q
  have hd : 1 ≤ 2 * N := by omega
  obtain ⟨hfeven, hk, hsimple, -, ext, -, -, hinj, hinn, hNC, -, -⟩ :=
    evenOrthogonalFieldCentralizer_of_regular hf hK hN Q hQ hT hE γ hγ hγ2 S hS hSγ hσ1
  have hcj := UnbalancingLocal.EvenOrthogonalComponents.conj_injective_matrixProjectiveDerived
    hQ hT hE
  obtain ⟨-, -, -, -, -, -, -, -, hinv⟩ := evenOrthogonalRealization_of_regular hf hK hd Q hQ hT hE
  obtain ⟨hSS, hTT, -⟩ := hinv γ hγ hγ2 S hS hSγ
  have hσσ : S.val.right * S.val.right = 1 := by
    have h1 := congrArg (fun y : similarityPairs Q => y.val.right) hSS
    rw [Subgroup.coe_mul, Subgroup.coe_one] at h1
    exact h1
  obtain ⟨hfin, -, -, hQ₀, -, -, -, -⟩ := even_quadratic_semilinear_involution_descent
    hσσ hσ1 hQ (T := pairSemilinearMap S.val) hTT (pairSemilinearMap_quad hS)
  have hk2 : 1 ≤ f / 2 := by
    obtain ⟨m, hm⟩ := hfeven
    omega
  have : FiniteDimensional (descentField S.val.right) (pairFix S) := finite_fixSpace
  have hdim : Module.finrank (descentField S.val.right) (pairFix S) = 2 * N := by
    rw [hfin, Module.finrank_fin_fun]
  obtain ⟨τ, Y, _, hτ, -, hlie, ⟨eY⟩⟩ :=
    LinearPilot.exists_lieModel_derivedOrthogonal_tag hk2 hk hN (pairDescentForm hS) hQ₀ hdim
  obtain ⟨Nκ, hNκ⟩ : ∃ Nκ : Subgroup (MulAut (matrixProjectiveDerived Q)),
      Nκ = (extKappa Q ext).range := ⟨_, rfl⟩
  rw [← hNκ] at hinn hNC
  obtain ⟨P, hP⟩ : ∃ P : Subgroup (matrixProjectiveDerived Q), P = Nκ.comap MulAut.conj :=
    ⟨_, rfl⟩
  have hPN : ∀ x : P, MulAut.conj (x : matrixProjectiveDerived Q) ∈ Nκ := fun x => by
    have h : (x : matrixProjectiveDerived Q) ∈ Nκ.comap MulAut.conj := hP ▸ x.2
    exact h
  let φ : P →* Nκ :=
    { toFun := fun x => ⟨MulAut.conj (x : matrixProjectiveDerived Q), hPN x⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun x y => by apply Subtype.ext; simp }
  have hφinj : Function.Injective φ := fun x y hxy =>
    Subtype.ext (hcj (congrArg Subtype.val hxy))
  have hφsurj : Function.Surjective φ := by
    rintro ⟨a, ha⟩
    obtain ⟨x, rfl⟩ := hinn ha
    exact ⟨⟨x, by rw [hP]; exact ha⟩, rfl⟩
  have e1 : P ≃* Nκ := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have e2 : (pairDescentDerived hS) ≃* Nκ :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hNκ.symm)
  have eP : P ≃* Y := (e1.trans e2.symm).trans eY
  have hPlie : LieModel P τ N 2 (f / 2) := LieType.CurtisTits.lieModel_of_mulEquiv eP.symm hlie
  refine ⟨hfeven, τ, P, hτ, ?_, ?_, hPlie⟩
  · intro x hx
    rw [hP] at hx
    have h1 := (Subgroup.mem_inf.mp (hNC hx)).2
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    have h2 := RankThree.CASymplecticSubfield.mul_conj_eq γ x
    rw [← h1] at h2
    have h3 : MulAut.conj (γ x) = MulAut.conj x := (mul_right_cancel h2).symm
    exact hcj h3
  · have : Finite P := inferInstance
    exact commutator_eq_top_of_lieModel_POmega hτ (by omega) hk2 hPlie

theorem exists_conj_linear_or_lieModel (hf : 1 ≤ f) (hK : Nat.card K' = 2 ^ f) (hN : 4 ≤ N)
    {Q : QuadraticForm K' (Fin (2 * N) → K')} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K' (Fin (2 * N) → K'), Module.finrank K' T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hconj : ∀ α : MulAut (matrixProjectiveDerived Q), α * α = 1 →
      ∃ β, β⁻¹ * α * β ∈ matrixProjectiveImage Q)
    {α : MulAut (matrixProjectiveDerived Q)} (hαα : α * α = 1) :
    (∃ (β : MulAut (matrixProjectiveDerived Q)) (s : matrixIsometries Q), s * s = 1 ∧
      β⁻¹ * α * β = matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)) ∨
    (Even f ∧ ∃ (τ : StatedLieTag) (P : Subgroup (matrixProjectiveDerived Q)),
      (τ = .POmegaPlus ∨ τ = .POmegaMinus) ∧ P ≤ fixedSubgroup α ∧ commutator P = ⊤ ∧
      LieModel P τ N 2 (f / 2)) := by
  have : CharP K' 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  have := finite_mulAut_matrixProjectiveDerived Q
  obtain ⟨β, hβ⟩ := hconj α hαα
  have hγγ : (β⁻¹ * α * β) * (β⁻¹ * α * β) = 1 := by
    calc (β⁻¹ * α * β) * (β⁻¹ * α * β) = β⁻¹ * (α * α) * β := by group
      _ = 1 := by rw [hαα]; group
  obtain ⟨S, hS, hSγ⟩ := exists_unit_rep hβ
  obtain ⟨-, -, -, -, F, hF, hker, hinj, -⟩ :=
    evenOrthogonalRealization_of_regular hf hK (by omega) Q hQ hT hE
  by_cases hσ : S.val.right = 1
  · left
    have hmem : (⟨matrixProjectiveConjugationHom Q S, ⟨S, rfl⟩⟩ : matrixProjectiveImage Q) ∈
        F.ker := by
      rw [MonoidHom.mem_ker, hF, hσ]
    rw [hker, Subgroup.mem_subgroupOf] at hmem
    obtain ⟨s, hs⟩ := hmem
    have hs' : matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) =
        β⁻¹ * α * β := hs.trans hSγ
    refine ⟨β, s, hinj ?_, hs'.symm⟩
    change matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q (s * s)) =
      matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q 1)
    rw [map_mul, map_mul, hs', hγγ, map_one, map_one]
  · right
    have hγ1 : β⁻¹ * α * β ≠ 1 := by
      intro h1
      have h2 : (⟨matrixProjectiveConjugationHom Q S, ⟨S, rfl⟩⟩ : matrixProjectiveImage Q) = 1 :=
        Subtype.ext (hSγ.trans h1)
      have h3 := hF S
      rw [h2, map_one] at h3
      exact hσ h3.symm
    have hγ2 : orderOf (β⁻¹ * α * β) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hγγ) hγ1
    obtain ⟨hfe, τ, P, hτ, hPF, hPc, hPlie⟩ :=
      exists_lieModel_le_fixedSubgroup_of_field hf hK hN hQ hT hE hβ hγ2 hS hSγ hσ
    refine ⟨hfe, τ, P.map β.toMonoidHom, hτ, ?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      have h1 : (β⁻¹ * α * β) x = x := hPF hx
      change α (β x) = β x
      have h2 := congrArg β h1
      simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.apply_symm_apply] at h2
      exact h2
    · exact commutator_top_transfer
        (P.equivMapOfInjective β.toMonoidHom β.injective) hPc
    · exact LieType.CurtisTits.lieModel_of_mulEquiv
        (P.equivMapOfInjective β.toMonoidHom β.injective) hPlie

end Field

@[expose] def OmegaMinusSpNonembeddingInput : Prop :=
  ∀ (Y : Type) [Group Y] (N g : ℕ), 6 ≤ N → Even N → 1 ≤ g → LieModel Y .POmegaMinus N 2 g →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ (2 * g) →
      ∀ φ : Y →* StatedSp (N - 1) K, ¬ Function.Injective φ

section Reduction

variable {K' : Type} [Field K'] [Finite K'] {f N : ℕ} {K : Type} [Field K] [Finite K]

theorem exists_conj_linear_of_embedding (hf : 1 ≤ f) (hK' : Nat.card K' = 2 ^ f) (hN : 5 ≤ N)
    {Q : QuadraticForm K' (Fin (2 * N) → K')} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K' (Fin (2 * N) → K'), Module.finrank K' T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hconj : ∀ α : MulAut (matrixProjectiveDerived Q), α * α = 1 →
      ∃ β, β⁻¹ * α * β ∈ matrixProjectiveImage Q)
    (hK : Nat.card K = 2 ^ f) {α : MulAut (matrixProjectiveDerived Q)} (hαα : α * α = 1)
    (hemb : ∀ P : Subgroup (matrixProjectiveDerived Q), P ≤ fixedSubgroup α →
      commutator P = ⊤ → ∃ φ : P →* StatedSp (N - 1) K, Function.Injective φ) :
    (∃ (β : MulAut (matrixProjectiveDerived Q)) (s : matrixIsometries Q), s * s = 1 ∧
      β⁻¹ * α * β = matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)) ∨
    (Even f ∧ Even N ∧ ∃ P : Subgroup (matrixProjectiveDerived Q), P ≤ fixedSubgroup α ∧
      commutator P = ⊤ ∧ LieModel P .POmegaMinus N 2 (f / 2)) := by
  rcases exists_conj_linear_or_lieModel hf hK' (by omega) hQ hT hE hconj hαα with h | h
  · exact Or.inl h
  · right
    obtain ⟨⟨m, hm⟩, τ, P, hτ, hPF, hPc, hPlie⟩ := h
    have hg : 1 ≤ f / 2 := by omega
    have hKg : Nat.card K = 2 ^ (2 * (f / 2)) := by rw [hK]; congr 1; omega
    by_cases hex : τ = .POmegaMinus ∧ Even N
    · obtain ⟨rfl, hNe⟩ := hex
      exact ⟨⟨m, hm⟩, hNe, P, hPF, hPc, hPlie⟩
    · exfalso
      obtain ⟨φ, hφ⟩ := hemb P hPF hPc
      exact not_injective_of_lieModel hτ hN hg hPlie hKg hex φ hφ

end Reduction

end CFSG.SeitzReduction.SymplecticPilot

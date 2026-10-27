module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.Descent
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

namespace Up34Chev2

@[expose] def NoL34Layer {P : Type} [Group P] (ψ : MulAut P) : Prop :=
  ∀ A : Subgroup P, GLAPComponent 3 (fixSubgroup ψ) A → ¬ IsLThreeFour (barOf 3 A)

theorem up34Pumpup_iff {P : Type} [Group P] (ψ : MulAut P) :
    Up34Pumpup P ψ ↔ ψ ^ 3 = 1 ∧ ψ ≠ 1 ∧ ¬ NoL34Layer ψ := by
  unfold Up34Pumpup NoL34Layer
  constructor
  · rintro ⟨h3, h1, I, hI, hI34⟩
    exact ⟨h3, h1, fun h => h I hI hI34⟩
  · rintro ⟨h3, h1, h⟩
    push Not at h
    obtain ⟨I, hI, hI34⟩ := h
    exact ⟨h3, h1, I, hI, hI34⟩

theorem isQuasisimple_of_simple_up34 {S : Type*} [Group S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) : CFSG.Open.IsQuasisimple S := by
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have : ⁅a, b⁆ ∈ commutator S := by
        rw [commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    · exact h
  · exact ((QuotientGroup.quotientMulEquivOfEq (up34_center_eq_bot_of_simple hnab)).trans
      (QuotientGroup.quotientBot (G := S))).isSimpleGroup

theorem noL34Layer_of_fix_eq {P : Type} [Group P] {ψ ψ' : MulAut P}
    (h : fixSubgroup ψ = fixSubgroup ψ') (hψ' : NoL34Layer ψ') : NoL34Layer ψ := by
  intro A hA hT
  rw [h] at hA
  exact hψ' A hA hT

theorem mulAut_pow_apply_of_fixed_up34 {P : Type} [Group P] {β : MulAut P} {x : P} (h : β x = x)
    (n : ℕ) : (β ^ n) x = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, h, ih]

theorem fixSubgroup_pow_eq_of_pow_pow_up34 {P : Type} [Group P] {β : MulAut P} {r j : ℕ}
    (hrj : (β ^ r) ^ j = β) : fixSubgroup (β ^ r) = fixSubgroup β := by
  ext x
  constructor
  · intro hx
    have h := mulAut_pow_apply_of_fixed_up34 (β := β ^ r) (x := x) hx j
    rw [hrj] at h
    exact h
  · intro hx
    exact mulAut_pow_apply_of_fixed_up34 (β := β) (x := x) hx r

theorem noL34Layer_congr {P P' : Type} [Group P] [Finite P] [Group P'] [Finite P'] (θ : P ≃* P')
    {ψ : MulAut P} (h : NoL34Layer (MulAut.congr θ ψ)) : NoL34Layer ψ := by
  intro A hA hT
  have hker : θ.toMonoidHom.ker ≤ Subgroup.center P := by
    intro x hx
    have : x = 1 := θ.injective (by simpa using hx)
    rw [this]
    exact one_mem _
  obtain ⟨A', hA', hT'⟩ := isLThreeFour_barOf_of_central θ.toMonoidHom θ.surjective hker ψ
    (MulAut.congr θ ψ) (fun y => by simp [MulAut.congr_apply]) hA hT
  exact h A' hA' hT'

theorem noL34Layer_conj {P : Type} [Group P] [Finite P] {f : MulAut P} (γ : MulAut P)
    (h : NoL34Layer f) : NoL34Layer (γ * f * γ⁻¹) := by
  intro A hA hT
  let π : P →* P := (γ⁻¹ : MulAut P).toMonoidHom
  have hπ : Function.Surjective π := (γ⁻¹ : MulAut P).surjective
  have hker : π.ker ≤ Subgroup.center P := by
    intro x hx
    have : x = 1 := (γ⁻¹ : MulAut P).injective (by simpa [π] using hx)
    rw [this]
    exact one_mem _
  have hαψ : ∀ y, π ((γ * f * γ⁻¹) y) = f (π y) := fun y => by simp [π, MulAut.mul_apply]
  obtain ⟨A', hA', hT'⟩ := isLThreeFour_barOf_of_central π hπ hker (γ * f * γ⁻¹) f hαψ hA hT
  exact h A' hA' hT'

theorem noL34Layer_of_conj_pow {P : Type} [Group P] [Finite P] {β η δ : MulAut P} {r j : ℕ}
    (hrj : (β ^ r) ^ j = β) (hδ : δ * β ^ r * δ⁻¹ = η) (h : NoL34Layer η) : NoL34Layer β := by
  have h1 : NoL34Layer (δ⁻¹ * η * δ⁻¹⁻¹) := noL34Layer_conj δ⁻¹ h
  have h2 : δ⁻¹ * η * δ⁻¹⁻¹ = β ^ r := by
    rw [← hδ]
    group
  rw [h2] at h1
  exact noL34Layer_of_fix_eq (fixSubgroup_pow_eq_of_pow_pow_up34 hrj).symm h1

theorem noL34Layer_of_card_dvd {P : Type} [Group P] [Finite P] (ψ : MulAut P) {N : ℕ}
    (hdvd : Nat.card ↥(fixSubgroup ψ) ∣ N) (hN : ¬ 20160 ∣ N) : NoL34Layer ψ := by
  intro A hA hT
  have hc2 : Nat.card (barOf 3 A) ∣ Nat.card ↥A := Subgroup.card_quotient_dvd_card _
  have hc3 : Nat.card ↥A ∣ Nat.card ↥(fixSubgroup ψ) := Subgroup.card_dvd_of_le hA.1
  rw [card_eq_of_isLThreeFour hT] at hc2
  exact hN (hc2.trans (hc3.trans hdvd))

theorem barOf_equiv_of_component_eq {P : Type} [Group P] [Finite P]
    {D A S : Subgroup P} (hA : GLAPComponent 3 D A) (hAS : A = S)
    (hS : IsSimpleGroup ↥S) : Nonempty (barOf 3 A ≃* ↥S) := by
  subst hAS
  have hAq := isQuasisimple_barOf_of_glaPComponent Nat.prime_three hA
  have hcore : GLAPPrimeCore 3 ↥A = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore 3 ↥A) with h | h
    · exact h
    · exfalso
      have hsub : Subsingleton (barOf 3 A) := by
        refine ⟨fun a b => ?_⟩
        induction a using QuotientGroup.induction_on with
        | H a =>
          induction b using QuotientGroup.induction_on with
          | H b =>
            rw [QuotientGroup.eq]
            rw [h]
            exact Subgroup.mem_top _
      have hs2 : Subsingleton (barOf 3 A ⧸ Subgroup.center (barOf 3 A)) :=
        (QuotientGroup.mk'_surjective (Subgroup.center (barOf 3 A))).subsingleton
      exact (not_nontrivial_iff_subsingleton.2 hs2) hAq.2.toNontrivial
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hcore).trans
    (QuotientGroup.quotientBot (G := ↥A))⟩

theorem noL34_of_simple_normal_comm {P : Type} [Group P] [Finite P] (ψ : MulAut P)
    (S : Subgroup P) (hSle : S ≤ fixSubgroup ψ)
    (hcomm : ⁅fixSubgroup ψ, fixSubgroup ψ⁆ ≤ S) (hs : IsSimpleGroup ↥S)
    (hnab : ∃ a b : ↥S, a * b ≠ b * a) (hL34 : ¬ IsLThreeFour ↥S) : NoL34Layer ψ := by
  intro A hA hT
  have hq : CFSG.Open.IsQuasisimple ↥S := isQuasisimple_of_simple_up34 hnab
  have hAD : A ≤ fixSubgroup ψ := hA.1
  have hAS : A ≤ S := by
    have hperf := glaPComponent_perfect hA
    calc A = ⁅A, A⁆ := hperf.symm
      _ ≤ ⁅fixSubgroup ψ, fixSubgroup ψ⁆ := Subgroup.commutator_mono hAD hAD
      _ ≤ S := hcomm
  have hsn : IsSubnormal A S := isSubnormal_of_le_of_le hA.2.1 hAS hSle
  have hAeq : A = S :=
    Lemma510Ns.eq_of_isSubnormal_of_quasisimple hq hsn (glaPComponent_perfect hA)
      (glaPComponent_ne_bot hA)
  obtain ⟨e⟩ := barOf_equiv_of_component_eq hA hAeq hs
  exact hL34 (IsLThreeFour.of_mulEquiv e hT)

end Up34Chev2

end CFSG.HardMathSupport.Dickson.Sec6

module

public import CFSG.ClassicalInvolution.Q3.ModelCenter
public import CFSG.ClassicalInvolution.Q3.OddCentralizerModels
public import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance CFSG.Assembly.LowTwoRank

@[expose] def ModelSimpleOddCentralizerFree3 : Prop :=
  ∀ (t : StatedLieTag) (n : ℕ) (hp : Nat.Prime 3), IsFundTag t → StatedLieAdmissible t n 3 1 →
    ∀ s : (modelUniv t n 3 1 hp).K ⧸ Subgroup.center (modelUniv t n 3 1 hp).K, orderOf s = 2 →
      CFSG.Assembly.Dichotomy.involutionOddCore s = ⊥

@[expose] def SimpleOddCentralizerFreeTag (t : StatedLieTag) : Prop :=
  ∀ (n : ℕ) (hp : Nat.Prime 3), StatedLieAdmissible t n 3 1 →
    ∀ s : (modelUniv t n 3 1 hp).K ⧸ Subgroup.center (modelUniv t n 3 1 hp).K, orderOf s = 2 →
      CFSG.Assembly.Dichotomy.involutionOddCore s = ⊥

theorem modelSimpleOddCentralizerFree3_of_tags
    (h : ∀ t, IsFundTag t → SimpleOddCentralizerFreeTag t) : ModelSimpleOddCentralizerFree3 :=
  fun t n hp hFT hadm => h t hFT n hp hadm

section Central

variable {K X : Type} [Group K] [Group X] (ψ : K →* X) (hψ : Function.Surjective ψ)

include hψ

theorem center_le_map_center_of_perfect [Group.IsPerfect K] (hker : ψ.ker ≤ Subgroup.center K) :
    Subgroup.center X ≤ (Subgroup.center K).map ψ := by
  intro g hg
  obtain ⟨k, rfl⟩ := hψ g
  refine ⟨k, mem_center_of_commutator_mem hker fun h => ?_, rfl⟩
  rw [MonoidHom.mem_ker, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hg (ψ h)).symm

theorem map_center_le_center : (Subgroup.center K).map ψ ≤ Subgroup.center X := by
  rintro _ ⟨k, hk, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨h, rfl⟩ := hψ g
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hk h]

end Central

section Reduction

variable {X : Type} [Group X] [Finite X]

theorem oddCoreIn_top_eq_bot_of_isQuasisimple (hX : CFSG.Open.IsQuasisimple X)
    (hZ : IsPGroup 2 (Subgroup.center X)) (hinv : ∃ x : X, orderOf x = 2) :
    oddCoreIn (⊤ : Subgroup X) = ⊥ := by
  obtain ⟨x, hx⟩ := hinv
  set S := oddCoreIn (⊤ : Subgroup X) with hS
  have hSodd : Odd (Nat.card S) := odd_card_oddCoreIn _
  have hSn : S.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (normalizer_oddCoreIn ⊤))
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hX S with hc | htop
  · rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    obtain ⟨k, hk⟩ := hZ ⟨g, hc hg⟩
    have h1 : g ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have h2 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
    have h3 : Odd (orderOf g) :=
      Odd.of_dvd_nat hSodd (Subgroup.orderOf_dvd_natCard _ hg)
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
      ((Nat.coprime_two_right.mpr h3).pow_right k) h2)
  · exfalso
    have hodd : Odd (Nat.card (⊤ : Subgroup X)) := htop ▸ hSodd
    rw [Subgroup.card_top] at hodd
    have h2 : 2 ∣ Nat.card X := hx ▸ orderOf_dvd_natCard x
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

end Reduction

theorem modelOddCentralizerFree3_of_simple (h : ModelSimpleOddCentralizerFree3) :
    ModelOddCentralizerFree3 := by
  intro t n hp hFT hadm X _ _ ψ hψ hker x hx
  have hfin : Finite (modelUniv t n 3 1 hp).K :=
    ModelFacts.finite_modelUniv (by norm_num) hp hFT hadm
  have hKq : CFSG.Open.IsQuasisimple (modelUniv t n 3 1 hp).K :=
    (ModelFacts.modelClauseZero t n 3 1 hp hFT hadm).1
  have hKperf : Group.IsPerfect (modelUniv t n 3 1 hp).K := ⟨hKq.1⟩
  have hZK : IsPGroup 2 (Subgroup.center (modelUniv t n 3 1 hp).K) :=
    (modelFiniteCenterTwoGroup3 t n hp hFT hadm).2
  have hXq : CFSG.Open.IsQuasisimple X := isQuasisimple_of_centralQuotient hKq ψ hψ hker
  have hcen := center_le_map_center_of_perfect ψ hψ hker
  have hZX : IsPGroup 2 (Subgroup.center X) := (hZK.map ψ).to_le hcen
  have hOX : oddCoreIn (⊤ : Subgroup X) = ⊥ :=
    oddCoreIn_top_eq_bot_of_isQuasisimple hXq hZX ⟨x, hx⟩
  change oddCoreIn (Subgroup.centralizer ({x} : Set X)) = ⊥
  by_cases hxc : x ∈ Subgroup.center X
  · have hC : Subgroup.centralizer ({x} : Set X) = ⊤ := by
      refine eq_top_iff.mpr fun g _ => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_center_iff.mp hxc g)
    rw [hC]
    exact hOX
  ·
    set π := QuotientGroup.mk' (Subgroup.center X) with hπ
    set φ := π.comp ψ with hφ
    have hφs : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hψ
    have hφk : φ.ker = Subgroup.center (modelUniv t n 3 1 hp).K := by
      refine le_antisymm (fun k hk => ?_) (fun k hk => ?_)
      · have h1 : ψ k ∈ Subgroup.center X := (QuotientGroup.eq_one_iff _).mp hk
        obtain ⟨c, hc, hck⟩ := hcen h1
        have h2 : c⁻¹ * k ∈ ψ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hck, inv_mul_cancel]
        have h3 : k = c * (c⁻¹ * k) := by group
        rw [h3]
        exact mul_mem hc (hker h2)
      · rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
        exact (QuotientGroup.eq_one_iff _).mpr (map_center_le_center ψ hψ ⟨k, hk, rfl⟩)
    let e : (modelUniv t n 3 1 hp).K ⧸ Subgroup.center (modelUniv t n 3 1 hp).K ≃*
        X ⧸ Subgroup.center X :=
      (QuotientGroup.quotientMulEquivOfEq hφk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
    have hSq : CFSG.Open.IsQuasisimple
        ((modelUniv t n 3 1 hp).K ⧸ Subgroup.center (modelUniv t n 3 1 hp).K) :=
      isQuasisimple_of_centralQuotient hKq (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
        (le_of_eq (QuotientGroup.ker_mk' _))
    have hSfree := oddCoreFree_of_isQuasisimple hSq (h t n hp hFT hadm)
    have hQfree : OddCoreFree (X ⧸ Subgroup.center X) := OddCoreFree.of_mulEquiv e.symm hSfree
    have hx2 : π x * π x = 1 := by
      rw [← map_mul, ← sq, ← hx, pow_orderOf_eq_one, map_one]
    have h1 := oddCoreIn_centralizer_le_oddCoreIn_top_of_quotient (Subgroup.center X) le_rfl x
      (hQfree (π x) hx2)
    rw [hOX] at h1
    exact le_bot_iff.mp h1

end CFSG.ClassicalInvolution.Q3

module

public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerReduction

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.Assembly.LowTwoRank

@[expose] def ClassicalMembersExact3 : Prop :=
  ∀ (t : StatedLieTag) (n : ℕ) (hp : Nat.Prime 3), IsFundTag t → StatedLieAdmissible t n 3 1 →
    ∀ (X : Type) [Group X] [Finite X] (ψ : (modelUniv t n 3 1 hp).K →* X),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center _ →
      ∀ (L : Subgroup X) (z : X), IsClassicalMember3 L z → classicalInvolutionOddCore L = ⊥

@[expose] def OddCentralizerFreeTag (t : StatedLieTag) : Prop :=
  ∀ (n : ℕ) (hp : Nat.Prime 3), IsFundTag t → StatedLieAdmissible t n 3 1 →
    ∀ (X : Type) [Group X] [Finite X] (ψ : (modelUniv t n 3 1 hp).K →* X),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center _ →
      ∀ x : X, orderOf x = 2 → CFSG.Assembly.Dichotomy.involutionOddCore x = ⊥

theorem modelOddCentralizerFree3_of_tags (h : ∀ t, IsFundTag t → OddCentralizerFreeTag t) :
    ModelOddCentralizerFree3 :=
  fun t n hp hFT hadm X _ _ ψ hψ hker x hx => h t hFT n hp hFT hadm X ψ hψ hker x hx

theorem classicalMembersExact3_of_oddCentralizerFree (h : ModelOddCentralizerFree3) :
    ClassicalMembersExact3 :=
  fun t n hp hFT hadm X _ _ ψ hψ hker _ z hL =>
    hL.oddCore_eq_bot_of_centralizer (h t n hp hFT hadm X ψ hψ hker z hL.orderOf_eq_two)

theorem classicalIsFundamental3_of_exact (h1 : ClassicalMembersFundamental3)
    (h2 : ModelFiniteCenterTwoGroup3) (h3 : ClassicalMembersExact3) : ClassicalIsFundamental3 := by
  intro t n hp hFT hadm X _ _ ψ hψ hker L z hL
  obtain ⟨hfin, hZ2⟩ := h2 t n hp hFT hadm
  have hO : classicalInvolutionOddCore L = ⊥ := h3 t n hp hFT hadm X ψ hψ hker L z hL
  obtain ⟨L', z', hL', hmap, -, hO'⟩ := hL.exists_lift ψ hψ hker (hZ2.to_le hker) hO
  refine ⟨⟨L', h1 t n hp hFT hadm L' z' hL' hO', hmap.symm⟩, ?_⟩
  obtain ⟨e⟩ := hL.nonempty_equiv_sl2 hO
  rw [Nat.card_congr e.toEquiv, natCard_sl2Three]

theorem oddCentralizerFreeTag_of_simple (t : StatedLieTag) (h : SimpleOddCentralizerFreeTag t) :
    OddCentralizerFreeTag t := by
  intro n hp hFT hadm X _ _ ψ hψ hker x hx
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
    have hSfree := oddCoreFree_of_isQuasisimple hSq (h n hp hadm)
    have hQfree : OddCoreFree (X ⧸ Subgroup.center X) := OddCoreFree.of_mulEquiv e.symm hSfree
    have hx2 : π x * π x = 1 := by
      rw [← map_mul, ← sq, ← hx, pow_orderOf_eq_one, map_one]
    have h1 := oddCoreIn_centralizer_le_oddCoreIn_top_of_quotient (Subgroup.center X) le_rfl x
      (hQfree (π x) hx2)
    rw [hOX] at h1
    exact le_bot_iff.mp h1

end CFSG.ClassicalInvolution.Q3

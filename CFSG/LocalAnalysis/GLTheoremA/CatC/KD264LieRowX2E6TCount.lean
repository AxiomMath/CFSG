module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6TKac
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Inner
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.LieType.SeitzGeneration.HeisTorusU87Arith

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6.T

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerAbs
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
open CFSG.HardMathSupport.Lang.E6Descent CFSG.RankThree.E6
open scoped Matrix

section Tables

set_option maxRecDepth 100000
set_option synthInstance.maxSize 1024

@[expose] noncomputable def D4set : Finset (E6Idx → ℤ) :=
  R6.toFinset.filter fun γ => kacTest θ6 sD4 γ

theorem ker_card_ne_eight : ∀ c : E6Idx → ZMod 3,
    (D4set.filter fun γ => charVal (τ := Tag.E6) c γ = 0).card ≠ 8 := by
  unfold D4set
  decide +kernel

end Tables

section Count


@[expose] noncomputable def phiPair (u v : E6Idx → ZMod 3) : Finset (E6Idx → ℤ) :=
  R6.toFinset.filter fun α => charVal (τ := Tag.E6) u α = 0 ∧ charVal (τ := Tag.E6) v α = 0

theorem phiSet_eq_charVal (u : E6Idx → ZMod 3) :
    phiSet u = R6.toFinset.filter fun α => charVal (τ := Tag.E6) u α = 0 := rfl

theorem mem_phiPair_iff {u v : E6Idx → ZMod 3} {α : E6Idx → ℤ} :
    α ∈ phiPair u v ↔ α ∈ phiSet u ∧ α ∈ phiSet v := by
  unfold phiPair
  rw [phiSet_eq_charVal, phiSet_eq_charVal, Finset.mem_filter, Finset.mem_filter,
    Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, ⟨h1, h3⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨-, h3⟩⟩
    exact ⟨h1, h2, h3⟩

theorem card_phiSet_four (u v : E6Idx → ZMod 3) :
    (phiSet u).card + (phiSet v).card + (phiSet (u + v)).card + (phiSet (u - v)).card =
      3 * (phiPair u v).card + 72 := by
  classical
  have hR : R6.toFinset.card = 72 := by decide +kernel
  have lin1 : ∀ α : E6Idx → ℤ, charVal (τ := Tag.E6) (u + v) α =
      charVal (τ := Tag.E6) u α + charVal (τ := Tag.E6) v α := fun α => by
    simp only [charVal, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have lin2 : ∀ α : E6Idx → ℤ, charVal (τ := Tag.E6) (u - v) α =
      charVal (τ := Tag.E6) u α - charVal (τ := Tag.E6) v α := fun α => by
    simp only [charVal, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  have key : ∀ p q : ZMod 3, ((if p = 0 then 1 else 0) + (if q = 0 then 1 else 0) +
      (if p + q = 0 then 1 else 0) + (if p - q = 0 then 1 else 0) : ℕ) =
        3 * (if (p = 0 ∧ q = 0) then 1 else 0) + 1 := by decide
  rw [phiSet_eq_charVal u, phiSet_eq_charVal v, phiSet_eq_charVal (u + v),
    phiSet_eq_charVal (u - v)]
  simp only [phiPair, Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have h1 : ∀ α ∈ R6.toFinset,
      ((((if charVal (τ := Tag.E6) u α = 0 then 1 else 0) +
        (if charVal (τ := Tag.E6) v α = 0 then 1 else 0)) +
        (if charVal (τ := Tag.E6) (u + v) α = 0 then 1 else 0)) +
        (if charVal (τ := Tag.E6) (u - v) α = 0 then 1 else 0) : ℕ) =
      3 * (if (charVal (τ := Tag.E6) u α = 0 ∧ charVal (τ := Tag.E6) v α = 0) then 1 else 0) + 1 := by
    intro α _
    rw [lin1, lin2]
    exact key _ _
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, hR,
    smul_eq_mul, mul_one]

end Count

section D4

variable
  {Ω : Type} [Field Ω] [IsAlgClosed Ω]

theorem coe_phiSet_eq_kernel {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) (hζ' : orderOf ζ = 3)
    (u : E6Idx → ZMod 3) :
    (↑(phiSet u) : Set (E6Idx → ℤ)) = kernelRoots (rootCharHom (thetaTuple ζ u)) := by
  ext γ
  exact ((mem_kernelRoots_iff_phiU hζ hζ' u γ).trans
    (Set.ext_iff.1 (phiU_eq_phiSet u) γ)).symm

theorem mem_kernel_iff_mem_phiSet {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) (hζ' : orderOf ζ = 3)
    (u : E6Idx → ZMod 3) (β : E6Idx → ℤ) :
    β ∈ kernelRoots (rootCharHom (thetaTuple ζ u)) ↔ β ∈ phiSet u :=
  (Set.ext_iff.1 (coe_phiSet_eq_kernel hζ hζ' u) β).symm

theorem mem_D4set_iff {γ : E6Idx → ℤ} :
    γ ∈ D4set ↔ γ ∈ kacE6.rootsOf (↑sD4 : Set (Option (Fin Tag.E6.rank))) := by
  have hC : ∃ x, x ∉ sD4 := ⟨none, by decide⟩
  rw [mem_rootsOf_iff kacE6 facts_E6 hC]
  unfold D4set
  rw [Finset.mem_filter, List.mem_toFinset]
  exact and_congr ⟨isRoot_of_mem_R6, mem_R6_of_isRoot⟩ Iff.rfl

theorem kernel_eq_image_D4 {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) (hζ' : orderOf ζ = 3)
    (h3 : ((3 : ℕ) : Ω) ≠ 0) {u : E6Idx → ZMod 3} (hu : (phiSet u).card = 24) :
    ∃ w : WeylGroup Tag.E6, kernelRoots (rootCharHom (thetaTuple ζ u)) =
      (fun α => w⁻¹ • α) '' kacE6.rootsOf (↑sD4 : Set (Option (Fin Tag.E6.rank))) := by
  classical
  have hap : ∀ i, thetaTuple ζ u i ^ 3 = 1 := by
    intro i
    show (DiagTorus.theta ζ (u i)) ^ 3 = 1
    unfold DiagTorus.theta
    rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have hall : (kernelRoots (rootCharHom (thetaTuple ζ u))).ncard = 24 :=
    (ncard_kernel_eq_phiSet hζ hζ' u).trans hu
  obtain ⟨ζ', w, m0, m1, m2, m3, m4, m5, hprim, hsum, hchar, hcl⟩ := kac_class_data h3 hap
  obtain ⟨β₀, hβ₀⟩ : (kernelRoots (rootCharHom (thetaTuple ζ u))).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [hall]; norm_num)
  obtain ⟨x, hx, hroots, hncard, -, -⟩ :=
    hcl (⟦⟨β₀, hβ₀⟩⟧ : KernelComponent (rootCharHom (thetaTuple ζ u)))
  have hcn := (d4t2_class_of_card h3 hap hall
    (⟦⟨β₀, hβ₀⟩⟧ : KernelComponent (rootCharHom (thetaTuple ζ u)))).2
  have hD4 := d4t2in_cmpF_eq_sD4 hsum hx (hncard.symm.trans hcn)
  have hker : componentRoots (rootCharHom (thetaTuple ζ u))
      (⟦⟨β₀, hβ₀⟩⟧ : KernelComponent (rootCharHom (thetaTuple ζ u))) =
      kernelRoots (rootCharHom (thetaTuple ζ u)) :=
    Set.eq_of_subset_of_ncard_le (KSNotAll24.componentRoots_subset_kernelRoots _ _)
      (by rw [hall, hcn]) (KSNotAll24.finite_kernelRoots_E6 _)
  refine ⟨w, ?_⟩
  rw [← hker, hroots, hD4]

theorem card_phiPair_ne_eight {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) (hζ' : orderOf ζ = 3)
    (h3 : ((3 : ℕ) : Ω) ≠ 0) {u : E6Idx → ZMod 3} (hu : (phiSet u).card = 24)
    (v : E6Idx → ZMod 3) : (phiPair u v).card ≠ 8 := by
  classical
  obtain ⟨w, hw⟩ := kernel_eq_image_D4 hζ hζ' h3 hu
  have hbij : (phiPair u v).card =
      (D4set.filter fun γ => charVal (τ := Tag.E6)
        ((dualMatrix (ZMod 3) w⁻¹).mulVec v) γ = 0).card := by
    refine Finset.card_bij (fun β _ => w • β) ?_ ?_ ?_
    · intro β hβ
      obtain ⟨hβu, hβv⟩ := mem_phiPair_iff.1 hβ
      have hβk : β ∈ kernelRoots (rootCharHom (thetaTuple ζ u)) :=
        (mem_kernel_iff_mem_phiSet hζ hζ' u β).2 hβu
      rw [hw] at hβk
      obtain ⟨γ, hγ, rfl⟩ := hβk
      rw [Finset.mem_filter, smul_inv_smul]
      refine ⟨mem_D4set_iff.2 hγ, ?_⟩
      have hv0 : charVal (τ := Tag.E6) v (w⁻¹ • γ) = 0 := (Finset.mem_filter.1 hβv).2
      exact (charVal_dualMatrix v w⁻¹ γ).trans hv0
    · intro β₁ _ β₂ _ h
      exact MulAction.injective w h
    · intro γ hγ
      obtain ⟨hγD, hγc⟩ := Finset.mem_filter.1 hγ
      have hγr := mem_D4set_iff.1 hγD
      have hβk : w⁻¹ • γ ∈ kernelRoots (rootCharHom (thetaTuple ζ u)) := by
        rw [hw]
        exact ⟨γ, hγr, rfl⟩
      have hβu : w⁻¹ • γ ∈ phiSet u := (mem_kernel_iff_mem_phiSet hζ hζ' u _).1 hβk
      refine ⟨w⁻¹ • γ, ?_, smul_inv_smul w γ⟩
      rw [mem_phiPair_iff]
      refine ⟨hβu, ?_⟩
      rw [phiSet_eq_charVal, Finset.mem_filter]
      refine ⟨(Finset.mem_filter.1 hβu).1, ?_⟩
      exact (charVal_dualMatrix v w⁻¹ γ).symm.trans hγc
  rw [hbij]
  exact ker_card_ne_eight _

theorem arith_four {a b c d f : ℕ} (h : a + b + c + d = 3 * f + 72)
    (ha : a = 24 ∨ a = 40) (hb : b = 24 ∨ b = 40) (hc : c = 24 ∨ c = 40)
    (hd : d = 24 ∨ d = 40) :
    (f = 8 ∧ a = 24) ∨ (f = 24 ∧ (a = 24 ∨ b = 24 ∨ c = 24 ∨ d = 24)) := by
  omega

theorem exists_d4_element {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) (hζ' : orderOf ζ = 3)
    (h3 : ((3 : ℕ) : Ω) ≠ 0) {u v : E6Idx → ZMod 3} (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : u + v ≠ 0) (huv' : u - v ≠ 0) (hNu : ¬ PhiTypeA u) (hNv : ¬ PhiTypeA v)
    (hNuv : ¬ PhiTypeA (u + v)) (hNuv' : ¬ PhiTypeA (u - v)) :
    ∃ x ∈ ({u, v, u + v, u - v} : Set (E6Idx → ZMod 3)), (phiSet x).card = 24 ∧
      ∀ α, α ∈ phiSet x → α ∈ phiSet u ∧ α ∈ phiSet v := by
  classical
  have s1 := card_phiSet_of_not_typeA hζ hζ' h3 hu hNu
  have s2 := card_phiSet_of_not_typeA hζ hζ' h3 hv hNv
  have s3 := card_phiSet_of_not_typeA hζ hζ' h3 huv hNuv
  have s4 := card_phiSet_of_not_typeA hζ hζ' h3 huv' hNuv'
  have hid := card_phiSet_four u v
  have hsub : ∀ x : E6Idx → ZMod 3, (∀ α, charVal (τ := Tag.E6) u α = 0 →
      charVal (τ := Tag.E6) v α = 0 → charVal (τ := Tag.E6) x α = 0) →
      phiPair u v ⊆ phiSet x := by
    intro x hx α hα
    obtain ⟨hαu, hαv⟩ := mem_phiPair_iff.1 hα
    have h1 := (Finset.mem_filter.1 hαu)
    have h2 := (Finset.mem_filter.1 hαv)
    rw [phiSet_eq_charVal, Finset.mem_filter]
    exact ⟨h1.1, hx α h1.2 h2.2⟩
  have hcl : ∀ (x : E6Idx → ZMod 3), (∀ α, charVal (τ := Tag.E6) u α = 0 →
      charVal (τ := Tag.E6) v α = 0 → charVal (τ := Tag.E6) x α = 0) →
      (phiSet x).card = 24 → (phiPair u v).card = 24 →
      ∀ α, α ∈ phiSet x → α ∈ phiSet u ∧ α ∈ phiSet v := by
    intro x hx hx24 hf α hα
    have heq : phiPair u v = phiSet x :=
      Finset.eq_of_subset_of_card_le (hsub x hx) (by rw [hf, hx24])
    rw [← heq] at hα
    exact mem_phiPair_iff.1 hα
  have lin1 : ∀ α : E6Idx → ℤ, charVal (τ := Tag.E6) u α = 0 → charVal (τ := Tag.E6) v α = 0 →
      charVal (τ := Tag.E6) (u + v) α = 0 := fun α h1 h2 => by
    simp only [charVal, Pi.add_apply, mul_add, Finset.sum_add_distrib] at h1 h2 ⊢
    rw [h1, h2, add_zero]
  have lin2 : ∀ α : E6Idx → ℤ, charVal (τ := Tag.E6) u α = 0 → charVal (τ := Tag.E6) v α = 0 →
      charVal (τ := Tag.E6) (u - v) α = 0 := fun α h1 h2 => by
    simp only [charVal, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib] at h1 h2 ⊢
    rw [h1, h2, sub_zero]
  rcases arith_four hid s1 s2 s3 s4 with ⟨hf8, ha⟩ | ⟨hf24, hx⟩
  · exact absurd hf8 (card_phiPair_ne_eight hζ hζ' h3 ha v)
  · rcases hx with hx | hx | hx | hx
    · exact ⟨u, by simp, hx, hcl u (fun _ h _ => h) hx hf24⟩
    · exact ⟨v, by simp, hx, hcl v (fun _ _ h => h) hx hf24⟩
    · exact ⟨u + v, by simp, hx, hcl (u + v) lin1 hx hf24⟩
    · exact ⟨u - v, by simp, hx, hcl (u - v) lin2 hx hf24⟩

end D4


end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6.T

end

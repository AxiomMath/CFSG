module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6TTrans
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreKac

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6.T

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn
open CFSG.HardMathSupport.Lang.E6Descent
open scoped Matrix

section Tables

set_option maxRecDepth 100000
set_option synthInstance.maxSize 1024

theorem cntB_cases : ∀ m0 m1 m2 m3 m4 m5 : Fin 4,
    (m0.val + 2 * m1.val + 2 * m2.val + 3 * m3.val + 2 * m4.val + m5.val ≤ 3) →
    (cntB m0.val m1.val m2.val m3.val m4.val m5.val = 18 ∨
      cntB m0.val m1.val m2.val m3.val m4.val m5.val = 22 ∨
      cntB m0.val m1.val m2.val m3.val m4.val m5.val = 24 ∨
      cntB m0.val m1.val m2.val m3.val m4.val m5.val = 30 ∨
      cntB m0.val m1.val m2.val m3.val m4.val m5.val = 40 ∨
      cntB m0.val m1.val m2.val m3.val m4.val m5.val = 72) := by
  decide +kernel

theorem kc_typeA : ∀ m0 m1 m2 m3 m4 m5 : Fin 4,
    (m0.val + 2 * m1.val + 2 * m2.val + 3 * m3.val + 2 * m4.val + m5.val ≤ 3) →
    (cntB m0.val m1.val m2.val m3.val m4.val m5.val = 18 ∨
      cntB m0.val m1.val m2.val m3.val m4.val m5.val = 22 ∨
      cntB m0.val m1.val m2.val m3.val m4.val m5.val = 30) →
    ∀ x ∈ zlC m0 m1 m2 m3 m4 m5, 3 ≤ (cmpF (zlC m0 m1 m2 m3 m4 m5) x).card →
      szF (zlC m0 m1 m2 m3 m4 m5) x =
        (cmpF (zlC m0 m1 m2 m3 m4 m5) x).card * ((cmpF (zlC m0 m1 m2 m3 m4 m5) x).card + 1) := by
  decide +kernel

end Tables

section Bridge

variable
  {Ω : Type} [Field Ω]

@[expose] noncomputable def phiSet (u : E6Idx → ZMod 3) : Finset (E6Idx → ℤ) :=
  R6.toFinset.filter fun α => ∑ i, ((α i : ℤ) : ZMod 3) * u i = 0

theorem mem_phiSet_iff {u : E6Idx → ZMod 3} {α : E6Idx → ℤ} :
    α ∈ phiSet u ↔ IsRoot Tag.E6 α ∧ ∑ i, ((α i : ℤ) : ZMod 3) * u i = 0 := by
  unfold phiSet
  rw [Finset.mem_filter, List.mem_toFinset]
  exact and_congr ⟨isRoot_of_mem_R6, mem_R6_of_isRoot⟩ Iff.rfl

theorem phiU_eq_phiSet (u : E6Idx → ZMod 3) :
    (PhiU u : Set (E6Idx → ℤ)) = (↑(phiSet u) : Set (E6Idx → ℤ)) := by
  ext α
  exact (and_congr mem_rootsE6_iff Iff.rfl).trans mem_phiSet_iff.symm

theorem ncard_kernel_eq_phiSet {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) (hζ' : orderOf ζ = 3)
    (u : E6Idx → ZMod 3) :
    (kernelRoots (rootCharHom (thetaTuple ζ u))).ncard = (phiSet u).card := by
  have : kernelRoots (rootCharHom (thetaTuple ζ u)) = ↑(phiSet u) := by
    ext γ
    exact (mem_kernelRoots_iff_phiU hζ hζ' u γ).trans (Set.ext_iff.1 (phiU_eq_phiSet u) γ)
  rw [this, Set.ncard_coe_finset]

theorem exists_kernelComponent_eq {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) (hζ' : orderOf ζ = 3)
    (u : Fin 6 → ZMod 3) {C : Set (Fin 6 → ℤ)} (hC : IsPhiComponent u C)
    (hrk : 3 ≤ rootRankQ C) :
    ∃ i : KernelComponent (rootCharHom (thetaTuple ζ u)),
      componentRoots (rootCharHom (thetaTuple ζ u)) i = C := by
  have hker : ∀ γ, γ ∈ kernelRoots (rootCharHom (thetaTuple ζ u)) ↔ γ ∈ PhiU u :=
    mem_kernelRoots_iff_phiU hζ hζ' u
  have hCne : C.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    subst hne
    have h0 : rootRankQ (∅ : Set (Fin 6 → ℤ)) = 0 := by
      unfold rootRankQ
      simp
    omega
  obtain ⟨α₀, hα₀⟩ := hCne
  have hCk : ∀ x ∈ C, x ∈ kernelRoots (rootCharHom (thetaTuple ζ u)) := fun x hx =>
    (hker x).2 (hC.1 hx)
  refine ⟨(⟦⟨α₀, hCk α₀ hα₀⟩⟧ : KernelComponent (rootCharHom (thetaTuple ζ u))), ?_⟩
  have hD := isPhiComponent_componentRoots (rootCharHom (thetaTuple ζ u)) u hker
    (⟦⟨α₀, hCk α₀ hα₀⟩⟧ : KernelComponent (rootCharHom (thetaTuple ζ u)))
  have hCD : C ⊆ componentRoots (rootCharHom (thetaTuple ζ u))
      (⟦⟨α₀, hCk α₀ hα₀⟩⟧ : KernelComponent (rootCharHom (thetaTuple ζ u))) := by
    intro x hx
    refine (mem_componentRoots_iff (rootCharHom (thetaTuple ζ u)) ⟨α₀, hCk α₀ hα₀⟩ x).2
      ⟨hCk x hx, ?_⟩
    have hr := hC.2.1 α₀ hα₀ x hx
    refine (Relation.ReflTransGen.mono (r := fun p q => p ∈ C ∧ q ∈ C ∧ cartanForm p q ≠ 0)
      (p := KerAdj (rootCharHom (thetaTuple ζ u)))
      (fun p q hpq => ⟨hCk p hpq.1, hCk q hpq.2.1, ?_⟩)) _ _ hr
    exact fun h => hpq.2.2 ((iform_eq_cartanForm _ _).symm.trans h)
  exact Set.Subset.antisymm (hC.2.2 _ hD.1 hD.2.1 hCD) hCD

theorem eq_zero_of_card_phiSet_eq (u : E6Idx → ZMod 3) (h : (phiSet u).card = 72) : u = 0 := by
  classical
  have hR : (R6.toFinset).card = 72 := by decide +kernel
  have hall : phiSet u = R6.toFinset :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [h, hR])
  funext j
  have hj : (Pi.single j (1 : ℤ) : E6Idx → ℤ) ∈ phiSet u := by
    rw [hall, List.mem_toFinset]
    exact mem_R6_of_isRoot (IsRoot.basis j)
  have h1 := (mem_phiSet_iff.1 hj).2
  rw [Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_apply, hb])
    (fun hj' => absurd (Finset.mem_univ j) hj')] at h1
  simpa using h1

theorem card_phiSet_of_not_typeA [IsAlgClosed Ω] {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) (hζ' : orderOf ζ = 3)
    (h3 : ((3 : ℕ) : Ω) ≠ 0) {u : Fin 6 → ZMod 3} (hu : u ≠ 0) (hN : ¬ PhiTypeA u) :
    (phiSet u).card = 24 ∨ (phiSet u).card = 40 := by
  classical
  have hap : ∀ i, thetaTuple ζ u i ^ 3 = 1 := by
    intro i
    show (DiagTorus.theta ζ (u i)) ^ 3 = 1
    unfold DiagTorus.theta
    rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  obtain ⟨ζ', w, m0, m1, m2, m3, m4, m5, hprim, hsum, hchar, hcl⟩ := kac_class_data h3 hap
  have hcnt := ncard_kernelRoots_eq_cntB hprim w hchar
  have hk := ncard_kernel_eq_phiSet hζ hζ' u
  have hcard := hk.symm.trans hcnt
  have hA : (cntB (m0 : ℕ) m1 m2 m3 m4 m5 = 18 ∨ cntB m0.val m1.val m2.val m3.val m4.val m5.val = 22 ∨
      cntB m0.val m1.val m2.val m3.val m4.val m5.val = 30) → False := by
    intro hc
    apply hN
    intro C hC hrk
    obtain ⟨i, hi⟩ := exists_kernelComponent_eq hζ hζ' u hC hrk
    subst hi
    obtain ⟨x, hx, -, hncard, hrank, -⟩ := hcl i
    have hrk' : 3 ≤ (cmpF (zlC m0 m1 m2 m3 m4 m5) x).card := hrank ▸ hrk
    have key := kc_typeA m0 m1 m2 m3 m4 m5 hsum hc x hx hrk'
    have e1 : rootRankQ (componentRoots (rootCharHom (thetaTuple ζ u)) i) =
        (cmpF (zlC m0 m1 m2 m3 m4 m5) x).card := hrank
    rw [e1]
    exact hncard.trans key
  rcases cntB_cases m0 m1 m2 m3 m4 m5 hsum with h | h | h | h | h | h
  · exact (hA (Or.inl h)).elim
  · exact (hA (Or.inr (Or.inl h))).elim
  · exact Or.inl (hcard.trans h)
  · exact (hA (Or.inr (Or.inr h))).elim
  · exact Or.inr (hcard.trans h)
  · exact absurd (eq_zero_of_card_phiSet_eq u (hcard.trans h)) hu

theorem thetaTuple_pow_three {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) (u : Fin 6 → ZMod 3) (i : E6Idx) :
    thetaTuple ζ u i ^ 3 = 1 := by
  show (DiagTorus.theta ζ (u i)) ^ 3 = 1
  unfold DiagTorus.theta
  rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]

end Bridge

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6.T

end

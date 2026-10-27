module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwMaxSpan
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.PairLemma
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.BigCell
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4MaxBase

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration.ExcOuterLeOne CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.CTP
open scoped commutatorElement

section Close


theorem eq_top_of_theta_twD4 {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hσ3 : ∀ c : K, σ (σ (σ c)) = c) (hσ : orderOf σ = 3)
    (hD : ringChar K ≠ 2 ∨ 4 ∣ Nat.card (fixSubfield σ))
    {H : Subgroup (adjointGroup Tag.D4 K)} (hΓ : fixedSubgroup (d4Twist 1 σ) ≤ H)
    {t : K} (ht : t ∉ fixSubfield σ)
    (hmem : xPar (rootOperatorFamily Tag.D4) (d4Root 22) t ∈ H) : H = ⊤ := by
  have hσ1 : ∃ x : K, σ x ≠ x := by
    by_contra h
    push Not at h
    have h1 : σ = 1 := RingEquiv.ext fun x => by simpa using h x
    rw [h1, orderOf_one] at hσ
    norm_num at hσ
  have hF : ∀ c ∈ fixSubfield σ, σ c = c := fun c hc => (mem_fixSubfield σ).1 hc
  have ht0 : t ≠ 0 := fun h => ht (h ▸ (fixSubfield σ).zero_mem)
  have hcomm : ∀ c ∈ fixSubfield σ,
      xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 2) 1) (t * c) ∈ H := by
    intro c hc
    rw [← commutator_theta_negBeta t c]
    have ha : xPar (rootOperatorFamily Tag.D4) (d4Root 22) t ∈ H := hmem
    have hb : xPar (rootOperatorFamily Tag.D4) (d4Root 21) c ∈ H :=
      hΓ (xPar_negBeta_mem_fixed hσ3 (hF c hc))
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
  obtain ⟨φ, ε₁, ε₂, h1, h2, hφ⟩ :=
    exists_rootSL2 (K := K) (γ := Pi.single (nd 2) 1) (isRoot_single Tag.D4 (nd 2))
  have hε₁ : (ε₁ : K) ≠ 0 := by rcases h1 with rfl | rfl <;> simp
  have hε₂ : (ε₂ : K) ≠ 0 := by rcases h2 with rfl | rfl <;> simp
  set μ₁ : K := (ε₁ : K) * t with hμ₁def
  have hμ₁ : μ₁ ≠ 0 := mul_ne_zero hε₁ ht0
  have hlam : μ₁ * (ε₂ : K) ∉ fixSubfield σ := by
    intro hk
    apply ht
    have hsq : ((ε₁ : K) * (ε₂ : K)) * ((ε₁ : K) * (ε₂ : K)) = 1 := by
      rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> simp
    have hpm : (ε₁ : K) * (ε₂ : K) ∈ fixSubfield σ := by
      rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> simp
    have key : t = ((ε₁ : K) * (ε₂ : K)) * (μ₁ * (ε₂ : K)) := by
      rw [hμ₁def]
      linear_combination (-(t : K)) * hsq
    rw [key]
    exact (fixSubfield σ).mul_mem hpm hk
  have hu : ∀ c ∈ fixSubfield σ, φ (u2 (μ₁ * c)) ∈ H := by
    intro c hc
    rw [(hφ (μ₁ * c)).1]
    have e : (ε₁ : K) * (μ₁ * c) = t * c := by
      rw [hμ₁def]
      rcases h1 with rfl | rfl <;> simp <;> ring
    rw [e]
    exact hcomm c hc
  have hl : ∀ c ∈ fixSubfield σ, φ (l2 ((ε₂ : K) * c)) ∈ H := by
    intro c hc
    rw [(hφ _).2]
    have e : (ε₂ : K) * ((ε₂ : K) * c) = c := by
      rcases h2 with rfl | rfl <;> simp
    rw [e]
    exact hΓ (xPar_neg_e2_mem_fixed hσ3 (hF c hc))
  have hfull : ∀ c : K, φ (u2 (μ₁ * c)) ∈ H := fun c =>
    sl2_hom_mem_of_pair σ (p := 3) Nat.prime_three (by norm_num) hσ hD φ μ₁ (ε₂ : K) hμ₁
      hlam hu hl c
  have hE2 : ∀ u : K, xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 2) 1) u ∈ H := by
    intro u
    have h := hfull (((ε₁ : K) * μ₁)⁻¹ * u)
    rw [(hφ _).1] at h
    have e : (ε₁ : K) * (μ₁ * (((ε₁ : K) * μ₁)⁻¹ * u)) = u := by
      field_simp
    rw [e] at h
    exact h
  have hw1 : CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily Tag.D4))
      (nd 2) (1 : Kˣ) ∈ H := by
    unfold CFSG.LieType.Steinberg.weylElement
    refine H.mul_mem (H.mul_mem (hE2 _) ?_) (hE2 _)
    refine hΓ (xPar_neg_e2_mem_fixed hσ3 ?_)
    simp
  have hrefl : CFSG.LieType.RootSystem.reflection Tag.D4.cartan (nd 2)
      (Pi.single (nd 2) 1) = -Pi.single (nd 2) 1 := by
    erw [CFSG.LieType.RootSystem.reflection_apply]
    funext j
    fin_cases j <;> decide
  have hE2neg : ∀ u : K, xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 2) 1) u ∈ H := by
    intro u
    obtain ⟨ε, hε, hcj⟩ := weylElement_xPar_conj (F := rootOperatorFamily Tag.D4) (K := K) (nd 2)
      (isRoot_single Tag.D4 (nd 2))
    have hm := H.mul_mem (H.mul_mem hw1 (hE2 (ε * u))) (H.inv_mem hw1)
    rw [hcj 1 (ε * u), hrefl] at hm
    have e : (ε : K) * (((1 : Kˣ) ^ (-(∑ j, Tag.D4.cartan (nd 2) j *
        (Pi.single (nd 2) 1 : Fin Tag.D4.rank → ℤ) j)) : Kˣ) : K) * ((ε : K) * u) = u := by
      rcases hε with rfl | rfl <;> simp
    rw [e] at hm
    exact hm
  have hE' : ∀ c : K, xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 2) 1) c ∈ H ∧
      xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 2) 1) c ∈ H :=
    fun c => ⟨hE2 c, hE2neg c⟩
  obtain ⟨o0, o1, o3⟩ := outer_root_mem_of_triples hσ3 hσ1 hE'
    (fun s => hΓ (triple_pos_mem hσ3 s)) (fun s => hΓ (triple_neg_mem hσ3 s))
  have hsimple : ∀ i : Fin Tag.D4.rank, ∀ c : K,
      xPar (rootOperatorFamily Tag.D4) (Pi.single i 1) c ∈ H ∧
        xPar (rootOperatorFamily Tag.D4) (-Pi.single i 1) c ∈ H := by
    intro i
    fin_cases i
    · exact o0
    · exact o1
    · exact hE'
    · exact o3
  have hw : ∀ i : Fin Tag.D4.rank, CFSG.LieType.Steinberg.weylElement
      (xPar (rootOperatorFamily Tag.D4)) i (1 : Kˣ) ∈ H := by
    intro i
    unfold CFSG.LieType.Steinberg.weylElement
    exact H.mul_mem (H.mul_mem ((hsimple i _).1) ((hsimple i _).2)) ((hsimple i _).1)
  exact eq_top_of_forall_xPar_mem H fun γ hγ c =>
    (xPar_mem_iff_of_roots H hw cartanD4_connected hγ (isRoot_single Tag.D4 (nd 0)) c).2
      ((hsimple (nd 0) c).1)

end Close

end CFSG.LieType.SeitzGeneration.ExcWideThree

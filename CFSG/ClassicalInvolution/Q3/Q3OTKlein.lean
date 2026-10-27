module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15Alpha

public section

namespace CFSG.ClassicalInvolution.Q3.Q3OT

open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.ModelFacts.Orth15
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem oddCoreIn_commutes_of_inner_free {I : Subgroup G} [I.Normal] (f : G)
    (h1 : oddCoreIn (Subgroup.centralizer ({f} : Set G) ⊓ I) = ⊥) :
    ∀ n ∈ oddCoreIn (Subgroup.centralizer ({f} : Set G)),
      ∀ i ∈ Subgroup.centralizer ({f} : Set G) ⊓ I, n * i = i * n := by
  set C := Subgroup.centralizer ({f} : Set G) with hC
  set N := oddCoreIn C with hN
  have hNC : N ≤ C := oddCoreIn_le C
  have hM : N ⊓ (C ⊓ I) = ⊥ := by
    refine le_bot_iff.mp ?_
    have hnormS : ∀ y ∈ C ⊓ I, ∀ w, w ∈ N ⊓ (C ⊓ I) → y * w * y⁻¹ ∈ N ⊓ (C ⊓ I) := by
      intro y hy w hw
      exact ⟨conj_mem_oddCoreIn hy.1 hw.1,
        (C ⊓ I).mul_mem ((C ⊓ I).mul_mem hy hw.2) ((C ⊓ I).inv_mem hy)⟩
    have hle : N ⊓ (C ⊓ I) ≤ oddCoreIn (C ⊓ I) := by
      refine le_oddCoreIn_of_normalizes inf_le_right (fun y hy => ?_)
        ((odd_card_oddCoreIn C).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
      rw [Subgroup.mem_normalizer_iff]
      intro w
      refine ⟨hnormS y hy w, fun h => ?_⟩
      have := hnormS y⁻¹ ((C ⊓ I).inv_mem hy) _ h
      simpa [mul_assoc] using this
    rwa [h1] at hle
  intro n hn i hi
  have hc : ⁅n, i⁆ ∈ N ⊓ (C ⊓ I) := by
    refine ⟨?_, ?_, ?_⟩
    · have h3 : i * n⁻¹ * i⁻¹ ∈ N := conj_mem_oddCoreIn hi.1 (N.inv_mem hn)
      have : ⁅n, i⁆ = n * (i * n⁻¹ * i⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [this]
      exact N.mul_mem hn h3
    · have : ⁅n, i⁆ = n * i * n⁻¹ * i⁻¹ := commutatorElement_def n i
      rw [this]
      exact C.mul_mem (C.mul_mem (C.mul_mem (hNC hn) hi.1) (C.inv_mem (hNC hn))) (C.inv_mem hi.1)
    · have h4 : n * i * n⁻¹ ∈ I := Subgroup.Normal.conj_mem inferInstance i hi.2 n
      have : ⁅n, i⁆ = n * i * n⁻¹ * i⁻¹ := commutatorElement_def n i
      rw [this]
      exact I.mul_mem h4 (I.inv_mem hi.2)
  rw [hM, Subgroup.mem_bot] at hc
  exact commutatorElement_eq_one_iff_mul_comm.mp hc

omit [Finite G] in
theorem closure_pair_commute {a b : G} (hab : a * b = b * a) :
    ∀ g ∈ Subgroup.closure ({a, b} : Set G), ∀ h ∈ Subgroup.closure ({a, b} : Set G),
      g * h = h * g := by
  set A := Subgroup.closure ({a, b} : Set G) with hA
  have h1 : ∀ c : G, c * a = a * c → c * b = b * c → ∀ g ∈ A, g * c = c * g := by
    intro c hca hcb g hg
    have : A ≤ Subgroup.centralizer ({c} : Set G) := by
      refine (Subgroup.closure_le _).mpr ?_
      intro y hy
      rcases hy with rfl | hy
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hca.symm
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact Subgroup.mem_centralizer_singleton_iff.mpr hcb.symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (this hg)
  intro g hg h hh
  have hga : g * a = a * g := h1 a rfl hab g hg
  have hgb : g * b = b * g := h1 b hab.symm rfl g hg
  exact (h1 g hga hgb h hh).symm

theorem alphaOf_eq_bot_of_cover (I : Subgroup G) [I.Normal] {B : Subgroup G}
    (hcov : ∀ a ∈ B, a ≠ 1 → CFSG.Assembly.Dichotomy.involutionOddCore a = ⊥ ∨
      (oddCoreIn (Subgroup.centralizer ({a} : Set G) ⊓ I) = ⊥ ∧
        B ≤ Subgroup.zpowers a ⊔ (Subgroup.centralizer ({a} : Set G) ⊓ I)))
    {a₀ : G} (ha₀ : a₀ ∈ B) (ha₀1 : a₀ ≠ 1)
    (h₀ : CFSG.Assembly.Dichotomy.involutionOddCore a₀ = ⊥) : alphaOf B = ⊥ := by
  refine (alphaOf_eq_bot_iff B).mpr ⟨fun a ha ha1 => ?_, ?_⟩
  · rcases hcov a ha ha1 with h | ⟨h1, h2⟩
    · rw [h, Subgroup.commutator_bot_left]
    · refine commutator_eq_bot_of_comm fun n hn b hb => ?_
      have hle : Subgroup.zpowers a ⊔ (Subgroup.centralizer ({a} : Set G) ⊓ I) ≤
          Subgroup.centralizer ({n} : Set G) := by
        refine sup_le ?_ ?_
        · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_singleton_iff.mp (oddCoreIn_le _ hn)).symm
        · intro i hi
          exact Subgroup.mem_centralizer_singleton_iff.mpr
            (oddCoreIn_commutes_of_inner_free a h1 n hn i hi).symm
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hle (h2 hb))).symm
  · refine eq_bot_iff.mpr ?_
    calc (⨅ a ∈ B, ⨅ (_ : a ≠ 1), CFSG.Assembly.Dichotomy.involutionOddCore a)
        ≤ CFSG.Assembly.Dichotomy.involutionOddCore a₀ :=
          (iInf₂_le a₀ ha₀).trans (iInf_le _ ha₀1)
      _ = ⊥ := h₀
      _ ≤ ⊥ := le_rfl

theorem alphaOf_eq_bot_of_inner_good (I : Subgroup G) [I.Normal] {B : Subgroup G} (hBI : B ≤ I)
    (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hO : ∀ a ∈ B, a ≠ 1 → oddCoreIn (Subgroup.centralizer ({a} : Set G) ⊓ I) = ⊥)
    {a₀ : G} (ha₀ : a₀ ∈ B) (ha₀1 : a₀ ≠ 1)
    (h₀ : CFSG.Assembly.Dichotomy.involutionOddCore a₀ = ⊥) : alphaOf B = ⊥ :=
  alphaOf_eq_bot_of_cover I (fun a ha ha1 => Or.inr ⟨hO a ha ha1, fun b hb =>
    Subgroup.mem_sup_right ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hBab b hb a ha), hBI hb⟩⟩)
    ha₀ ha₀1 h₀

end CFSG.ClassicalInvolution.Q3.Q3OT

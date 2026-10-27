module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits

structure StdDatum (q : ℕ) (C : Type*) [Group C] (ι : Type*) where
  Q : Set ι → Subgroup C
  P : Set ι → Subgroup C
  U : Subgroup C
  U_sylow : ∃ S : Sylow q C, (S : Subgroup C) = U
  Q_pGroup : ∀ J, IsPGroup q (Q J)
  Q_le_U : ∀ J, Q J ≤ U
  normalizer_eq : ∀ J, Subgroup.normalizer (Q J : Set C) = P J
  centralizer_le : ∀ J, J ≠ Set.univ → ∀ x : C, (∀ r ∈ Q J, x * r = r * x) → x ∈ Q J
  std_position : ∀ R : Subgroup C, IsRadical q R →
    ∃ (g : C) (J : Set ι), J ≠ Set.univ ∧ R.map (MulAut.conj g⁻¹).toMonoidHom = Q J
  generation : ∃ F : Set (Set ι), (∀ J ∈ F, J ≠ Set.univ) ∧
    Subgroup.closure (⋃ J ∈ F, (P J : Set C)) = ⊤

namespace StdDatum

variable {q : ℕ} [Fact q.Prime] {C : Type*} [Group C] [Finite C] {ι : Type*}

theorem centralizer_le_of_isRadical (D : StdDatum q C ι) {R : Subgroup C} (hR : IsRadical q R) :
    ∀ x : C, (∀ r ∈ R, x * r = r * x) → x ∈ R := by
  obtain ⟨g, J, hJ, hRJ⟩ := D.std_position R hR
  intro x hx
  have hy : ∀ r ∈ D.Q J, (g⁻¹ * x * g) * r = r * (g⁻¹ * x * g) := by
    intro r hr
    rw [← hRJ] at hr
    obtain ⟨s, hs, rfl⟩ := hr
    have hs' := hx s hs
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * x * g * (g⁻¹ * s * g) = g⁻¹ * (x * s) * g := by group
      _ = g⁻¹ * (s * x) * g := by rw [hs']
      _ = g⁻¹ * s * g * (g⁻¹ * x * g) := by group
  have h1 := D.centralizer_le J hJ (g⁻¹ * x * g) hy
  rw [← hRJ] at h1
  obtain ⟨s, hs, hse⟩ := h1
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hse
  have : x = s := by
    have h2 : g * (g⁻¹ * s * g) * g⁻¹ = g * (g⁻¹ * x * g) * g⁻¹ := by rw [hse]
    simpa using h2.symm
  rw [this]
  exact hs

theorem radicalGen (D : StdDatum q C ι) : ∀ U : Sylow q C, RadicalGen q C (U : Subgroup C) := by
  intro U
  obtain ⟨U₀, hU₀⟩ := D.U_sylow
  refine RadicalGen.of_sylow U₀ ?_ U
  unfold RadicalGen
  rw [eq_top_iff]
  obtain ⟨F, hF, hgen⟩ := D.generation
  rw [← hgen]
  refine Subgroup.closure_mono ?_
  intro x hx
  obtain ⟨J, hJF, hxJ⟩ := Set.mem_iUnion₂.1 hx
  refine ⟨D.Q J, D.Q_pGroup J, hU₀ ▸ D.Q_le_U J, D.centralizer_le J (hF J hJF), ?_⟩
  rw [D.normalizer_eq]
  exact hxJ

theorem radRigid (D : StdDatum q C ι) (hBT : HoldsTits C q) : RadRigid q C :=
  radRigid_of_gen hBT (fun _ hR => D.centralizer_le_of_isRadical hR) D.radicalGen

end StdDatum

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

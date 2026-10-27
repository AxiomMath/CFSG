module

public import CFSG.CGT.Stroth77.Stroth39Kill
import CFSG.GroupTheory.FixedCosetCommutator

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

namespace StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
  {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

theorem exists_mem_R_conj_mem (h : F.IsD D dD)
    (hlt : D < (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G)) :
    ∃ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
      e ∉ D ∧ e⁻¹ * dD.uv * e * dD.uv⁻¹ ∈ D ∧ e⁻¹ * dD.t * e * dD.t⁻¹ ∈ D := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R : Subgroup G := (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
    Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) with hR
  have hRS : R ≤ (F.S : Subgroup G) := fun x hx =>
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).1
  have hRN : R ≤ Subgroup.normalizer (D : Set G) := fun x hx =>
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).2
  have hgen : ∀ x ∈ ({dD.uv, dD.t} : Set G), x ∈ (F.S : Subgroup G) ∧
      x ∈ Subgroup.normalizer (D : Set G) ∧ x * x = 1 := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨h.uv_mem_S, dD.uv_mem, dD.uv_sq⟩
    · exact ⟨h.t_mem_S, dD.t_mem, dD.t_sq⟩
  have hPS : Subgroup.closure ({dD.uv, dD.t} : Set G) ≤ (F.S : Subgroup G) :=
    (Subgroup.closure_le _).mpr fun x hx => (hgen x hx).1
  have hPQ : Subgroup.closure ({dD.uv, dD.t} : Set G) ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.closure_le _).mpr fun x hx =>
      mem_normalizer_inf_centralizer_omegaIn (hgen x hx).1 (hgen x hx).2.1 (hgen x hx).2.2
  have hPK : Subgroup.closure ({dD.uv, dD.t} : Set G) ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.closure_le _).mpr fun x hx => (hgen x hx).2.1
  obtain ⟨e, heR, heD, he⟩ := CFSG.GroupTheory.exists_commutatorElement_mem_of_isPGroup
    (F.S.isPGroup'.to_le hPS) (F.S.isPGroup'.to_le hRS) hlt hRN hPQ hPK
  have hr : ∀ x ∈ ({dD.uv, dD.t} : Set G), e⁻¹ * x * e * x⁻¹ ∈ D := fun x hx => by
    have h' := (Subgroup.mem_normalizer_iff''.mp (hRN heR) _).mp
      (he x (Subgroup.subset_closure hx))
    rw [commutatorElement_def] at h'
    convert h' using 1
    group
  exact ⟨e, heR, heD, hr _ (by simp), hr _ (by simp)⟩

theorem exists_proj_rho_eq (hS : Local.Setting (F.S : Subgroup G) D) {e : G} (he : e ∈ hS.R)
    (hc : ∀ d ∈ D, (dD.ρ⁻¹ * e * dD.ρ)⁻¹ * d * (dD.ρ⁻¹ * e * dD.ρ) = e⁻¹ * d * e) :
    ∃ d₀ ∈ D, hS.proj dD.ρ e = e * d₀ := by
  have hp := hS.proj_mem dD.ρ_mem he
  have hpe : hS.proj dD.ρ e * e⁻¹ ∈ D := hS.mul_inv_mem_of_conj_eq he hp fun d hd => by
    rw [hS.proj_conj_D dD.ρ_mem he hd, hc d hd]
  refine ⟨e⁻¹ * hS.proj dD.ρ e, ?_, by group⟩
  have := (Subgroup.mem_normalizer_iff''.mp (hS.R_le_normalizer he) _).mp hpe
  convert this using 1
  group

private theorem stroth_3_9_of_kill (h : F.IsD D dD)
    (hns : IsSylowIn 2 (Subgroup.normalizer (D : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)))
    (hkill : ∀ (hS : Local.Setting (F.S : Subgroup G) D) {e d₀ : G}, e ∈ hS.R →
      e⁻¹ * dD.uv * e * dD.uv⁻¹ ∈ D → e⁻¹ * dD.t * e * dD.t⁻¹ ∈ D → d₀ ∈ D →
      hS.proj dD.ρ e = e * d₀ → e ∈ D)
    {P : Prop}
    (hV : (∃ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        e ∉ D ∧ e⁻¹ * dD.uv * e * dD.uv⁻¹ ∈ D ∧ e⁻¹ * dD.t * e * dD.t⁻¹ ∈ D) →
      (∀ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        e⁻¹ * dD.uv * e * dD.uv⁻¹ ∈ D → e⁻¹ * dD.t * e * dD.t⁻¹ ∈ D →
        (∀ d ∈ D, (dD.ρ⁻¹ * e * dD.ρ)⁻¹ * d * (dD.ρ⁻¹ * e * dD.ρ) = e⁻¹ * d * e) → e ∈ D) → P) :
    (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ∨ P := by
  have hS := h.setting hns
  have hDR : D ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) := hS.D_le_R
  by_cases hRD : (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D
  · exact Or.inl hRD
  · refine Or.inr (hV (h.exists_mem_R_conj_mem (lt_of_le_of_ne hDR (Ne.symm hRD))) ?_)
    intro e he huv ht hc
    obtain ⟨d₀, hd₀, hp⟩ := exists_proj_rho_eq hS he hc
    exact hkill hS he huv ht hd₀ hp

theorem stroth_3_9_t321 {dD : StrothWeakTypeData D StrothTypeIndex.t321} (h : F.IsD D dD)
    (hns : IsSylowIn 2 (Subgroup.normalizer (D : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)))
    (hV : (∃ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        e ∉ D ∧ e⁻¹ * dD.uv * e * dD.uv⁻¹ ∈ D ∧ e⁻¹ * dD.t * e * dD.t⁻¹ ∈ D) →
      (∀ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        e⁻¹ * dD.uv * e * dD.uv⁻¹ ∈ D → e⁻¹ * dD.t * e * dD.t⁻¹ ∈ D →
        (∀ d ∈ D, (dD.ρ⁻¹ * e * dD.ρ)⁻¹ * d * (dD.ρ⁻¹ * e * dD.ρ) = e⁻¹ * d * e) → e ∈ D) →
      ∃ X : Subgroup G, IsMulCommutative X ∧ F.A ≤ X ∧ X ≤ (F.S : Subgroup G) ∧
        F.dA.L ≤ Subgroup.normalizer
          ((X ⊔ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) ∧
        Nat.card D < Nat.card X) :
    (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ∨
      ∃ X : Subgroup G, IsMulCommutative X ∧ F.A ≤ X ∧ X ≤ (F.S : Subgroup G) ∧
        F.dA.L ≤ Subgroup.normalizer
          ((X ⊔ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) ∧
        Nat.card D < Nat.card X :=
  stroth_3_9_of_kill h hns (fun hS _ _ he huv ht hd₀ hp =>
    h.mem_of_proj_rho_t321 hS he huv ht hd₀ hp) hV

theorem stroth_3_9_t331 {dD : StrothWeakTypeData D StrothTypeIndex.t331} (h : F.IsD D dD)
    (hns : IsSylowIn 2 (Subgroup.normalizer (D : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)))
    (hV : (∃ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        e ∉ D ∧ e⁻¹ * dD.uv * e * dD.uv⁻¹ ∈ D ∧ e⁻¹ * dD.t * e * dD.t⁻¹ ∈ D) →
      (∀ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        e⁻¹ * dD.uv * e * dD.uv⁻¹ ∈ D → e⁻¹ * dD.t * e * dD.t⁻¹ ∈ D →
        (∀ d ∈ D, (dD.ρ⁻¹ * e * dD.ρ)⁻¹ * d * (dD.ρ⁻¹ * e * dD.ρ) = e⁻¹ * d * e) → e ∈ D) →
      ∃ X : Subgroup G, IsMulCommutative X ∧ F.A ≤ X ∧ X ≤ (F.S : Subgroup G) ∧
        F.dA.L ≤ Subgroup.normalizer
          ((X ⊔ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) ∧
        Nat.card D < Nat.card X) :
    (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ∨
      ∃ X : Subgroup G, IsMulCommutative X ∧ F.A ≤ X ∧ X ≤ (F.S : Subgroup G) ∧
        F.dA.L ≤ Subgroup.normalizer
          ((X ⊔ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) ∧
        Nat.card D < Nat.card X :=
  stroth_3_9_of_kill h hns (fun hS _ _ he huv ht hd₀ hp =>
    h.mem_of_proj_rho_t331 hS he huv ht hd₀ hp) hV

end StrothFrame.IsD

end CFSG.CGT.Stroth77

module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellStruct2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellTr

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG CFSG.Quasithin CFSG.Quasithin.BlueprintB2
open scoped LinearAlgebra.Projectivization commutatorElement

section Local

variable {G : Type*} [Group G] {k : Type*} [Field k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}

@[expose] def Adm (H Y : Subgroup G) : Prop := ∃ A : Subgroup G, IsMaxElemAbelian H A ∧ Y ≤ A

theorem Adm.mono {H Y Y' : Subgroup G} (h : Adm H Y) (hY : Y' ≤ Y) : Adm H Y' :=
  let ⟨A, hA, hYA⟩ := h
  ⟨A, hA, hY.trans hYA⟩

theorem Adm.le {H Y : Subgroup G} (h : Adm H Y) : Y ≤ H := by
  obtain ⟨A, hA, hYA⟩ := h
  exact hYA.trans hA.1

theorem Adm.isElemAbelian {H Y : Subgroup G} (h : Adm H Y) : CFSG.Open.IsElemAbelian 2 Y := by
  obtain ⟨A, hA, hYA⟩ := h
  exact isElemAbelian_mono hA.2.1 hYA

theorem adm_tr {S₀ Y : Subgroup G} (α : S₀ ≃* S₀) (g : G) [Finite G] (h : Adm S₀ Y) :
    Adm (cj S₀ g) (tr S₀ α g Y) := by
  obtain ⟨A, hA, hYA⟩ := h
  exact ⟨tr S₀ α g A, isMaxElemAbelian_tr hA, tr_mono hYA⟩

theorem adm_trInv {S₀ Y : Subgroup G} (α : S₀ ≃* S₀) (g : G) [Finite G]
    (h : Adm (cj S₀ g) Y) : Adm S₀ (trInv S₀ α g Y) := by
  obtain ⟨A, hA, hYA⟩ := h
  exact ⟨trInv S₀ α g A, isMaxElemAbelian_trInv hA, aimg_mono (cj_mono hYA)⟩

namespace IsNatBase

theorem sylow_inf_centralizer_Vmod [Finite G] [Finite k] (h : IsNatBase S ρ (Ecore G) ψ) :
    (S : Subgroup G) ⊓ Subgroup.centralizer (Vmod G : Set G) = CFSG.pCore 2 G := by
  apply le_antisymm
  · rintro a ⟨haS, hac⟩
    have hρ : ρ a = 1 := by
      apply eq_one_of_forall_smul_eq'
      intro w
      obtain ⟨v, hv, hψ⟩ := h.ψ_Vmod_surj (Multiplicative.ofAdd w)
      have hva : (v : G) * a = a * v := Subgroup.mem_centralizer_iff.mp hac v hv
      have h1 := h.ψ_equiv a v v (by
        calc (v : G) = (v : G) * a * a⁻¹ := by group
          _ = a * v * a⁻¹ := by rw [hva])
      rw [hψ, toAdd_ofAdd] at h1
      rw [Matrix.SpecialLinearGroup.smul_def]
      exact h1.symm
    have hx : a ∈ (S : Subgroup G) ⊓ ρ.ker := ⟨haS, hρ⟩
    rwa [h.sylow_inf_ker] at hx
  · intro q hq
    refine ⟨core_le_sylow S hq, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    exact (Ecore_commute_core hq (Vmod_le_Ecore hv)).symm

end IsNatBase

namespace IsSeed

theorem Fcore_eq_Vmod_sup_cent [Finite G] [Finite k] (h : IsSeed S ρ (Ecore G) ψ)
    {A Y : Subgroup G} (hA : IsMaxElemAbelian (S : Subgroup G) A) (hYA : Y ≤ A) :
    Fcore G = Vmod G ⊔ (Fcore G ⊓ Subgroup.centralizer (Y : Set G)) := by
  apply le_antisymm
  · calc Fcore G = Vmod G ⊔ (A ⊓ Fcore G) := h.Fcore_eq_Vmod_sup hA
      _ ≤ Vmod G ⊔ (Fcore G ⊓ Subgroup.centralizer (Y : Set G)) := by
        refine sup_le_sup_left ?_ _
        rintro w ⟨hwA, hwF⟩
        refine ⟨hwF, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
        exact (isElemAbelian_iff.mp hA.2.1).1 y (hYA hy) w hwA
  · exact sup_le (Vmod_le_Ecore.trans h.Ecore_le_Fcore) inf_le_left

theorem not_sylow_le_core [Finite G] [Finite k] (h : IsSeed S ρ (Ecore G) ψ) :
    ∃ s ∈ (S : Subgroup G), s ∉ CFSG.pCore 2 G := by
  obtain ⟨A, hA, hAQ⟩ := h.exists_max_outside
  obtain ⟨a, haA, haQ⟩ := IsConcreteLE.not_le_iff_exists.mp hAQ
  exact ⟨a, hA.1 haA, haQ⟩

theorem sylow_not_core_comm_Vmod [Finite G] [Finite k] (h : IsSeed S ρ (Ecore G) ψ) {s : G}
    (hs : s ∈ (S : Subgroup G)) (hsQ : s ∉ CFSG.pCore 2 G) {v : G} (hv : v ∈ Vmod G)
    (hsv : s * v = v * s) : v ∈ Zfix S := by
  obtain ⟨ℓ, hℓ⟩ := h.exists_rootGrp_eq
  have hT1 := (h.natural_module_facts hℓ).1
  have hin : Multiplicative.toAdd (ψ ⟨v, Vmod_le_Ecore hv⟩) ∈ ℓ.submodule := by
    refine (hT1 s hs hsQ ⟨v, Vmod_le_Ecore hv⟩ hv).mp ?_
    calc s * v * s⁻¹ = (v * s) * s⁻¹ := by rw [hsv]
      _ = v := by group
  refine ⟨hv, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
  by_cases htQ : t ∈ CFSG.pCore 2 G
  · exact Ecore_commute_core htQ (Vmod_le_Ecore hv)
  · have := (hT1 t ht htQ ⟨v, Vmod_le_Ecore hv⟩ hv).mpr hin
    calc t * v = (t * v * t⁻¹) * t := by group
      _ = v * t := by rw [this]

theorem Vmod_inf_centralizer_of_not_le [Finite G] [Finite k] (h : IsSeed S ρ (Ecore G) ψ)
    {Y : Subgroup G} (hY : Y ≤ (S : Subgroup G)) (hYQ : ¬ Y ≤ CFSG.pCore 2 G) :
    Vmod G ⊓ Subgroup.centralizer (Y : Set G) = Zfix S := by
  apply le_antisymm
  · obtain ⟨y, hyY, hyQ⟩ := IsConcreteLE.not_le_iff_exists.mp hYQ
    rintro v ⟨hv, hvc⟩
    exact h.sylow_not_core_comm_Vmod (hY hyY) hyQ hv (Subgroup.mem_centralizer_iff.mp hvc y hyY)
  · rintro z ⟨hzV, hzc⟩
    exact ⟨hzV, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_iff.mp hzc y (hY hy)⟩

end IsSeed

namespace IsNatBase

theorem card_k_mul_card_core [Finite G] [Finite k] (h : IsNatBase S ρ (Ecore G) ψ) :
    Nat.card k * Nat.card (CFSG.pCore 2 G) = Nat.card (S : Subgroup G) := by
  obtain ⟨ℓ, hℓ⟩ := h.exists_rootGrp_eq
  have := card_eq_card_map_mul_card_inf_ker ρ (S : Subgroup G)
  rw [hℓ, card_rootGrp, h.sylow_inf_ker] at this
  exact this.symm

theorem card_k_mul_card_Zfix [Finite G] [Finite k] (h : IsNatBase S ρ (Ecore G) ψ) :
    Nat.card k * Nat.card (Zfix S) = Nat.card (Vmod G) := by
  obtain ⟨ℓ, hℓ⟩ := h.exists_rootGrp_eq
  have hidx := (h.natural_module_facts hℓ).2.2.1
  have := Subgroup.relIndex_mul_card (Vmod G ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G))
    (Vmod G)
  rw [inf_of_le_left inf_le_left, hidx] at this
  exact this

end IsNatBase

theorem Fcore_le_sylow : Fcore G ≤ (S : Subgroup G) := Fcore_le_core.trans (core_le_sylow S)

theorem Vmod_le_sylow : Vmod G ≤ (S : Subgroup G) :=
  Vmod_le_Ecore.trans (Ecore_le_core.trans (core_le_sylow S))

theorem Zfix_le_sylow : Zfix S ≤ (S : Subgroup G) := inf_le_left.trans Vmod_le_sylow

namespace IsSeed

variable [Finite G] [Finite k]

theorem tr_Fcore_rep (h : IsSeed S ρ (Ecore G) ψ) (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (g : G) {Y : Subgroup G} (hY : Adm (cj (S : Subgroup G) g) Y) :
    tr (S : Subgroup G) α g (Fcore G) = tr (S : Subgroup G) α g (Vmod G) ⊔
      (tr (S : Subgroup G) α g (Fcore G) ⊓ Subgroup.centralizer (Y : Set G)) := by
  obtain ⟨A, hA, hYA⟩ := adm_trInv α g hY
  have h1 := h.Fcore_eq_Vmod_sup_cent hA hYA
  have hY0 : trInv (S : Subgroup G) α g Y ≤ (S : Subgroup G) := trInv_le_S
  have h2 := congrArg (tr (S : Subgroup G) α g) h1
  rw [tr_sup Vmod_le_sylow (inf_le_left.trans Fcore_le_sylow), tr_centralizer hY0,
    tr_trInv hY.le] at h2
  exact h2

theorem isMaxElemAbelian_tr_Fcore_sup (h : IsSeed S ρ (Ecore G) ψ)
    (α : (S : Subgroup G) ≃* (S : Subgroup G)) (g : G) {A' : Subgroup G}
    (hA' : IsMaxElemAbelian (cj (S : Subgroup G) g) A') :
    IsMaxElemAbelian (cj (S : Subgroup G) g)
      (tr (S : Subgroup G) α g (Fcore G) ⊔
        (A' ⊓ Subgroup.centralizer ((tr (S : Subgroup G) α g (Fcore G) : Subgroup G) : Set G))) := by
  have hA := isMaxElemAbelian_trInv (α := α) hA'
  have h1 := (h.isMaxElemAbelian_core_sup_Fcore hA).2
  rw [← h.inf_centralizer_Fcore hA] at h1
  have h2 := isMaxElemAbelian_tr (α := α) (g := g) h1
  rw [tr_sup (inf_le_left.trans hA.1) Fcore_le_sylow, tr_centralizer Fcore_le_sylow,
    tr_trInv hA'.1, sup_comm] at h2
  exact h2

theorem tr_commutator_A_Fcore (h : IsSeed S ρ (Ecore G) ψ)
    (α : (S : Subgroup G) ≃* (S : Subgroup G)) (g : G) {A' : Subgroup G}
    (hA' : IsMaxElemAbelian (cj (S : Subgroup G) g) A') :
    (A' ≤ tr (S : Subgroup G) α g (CFSG.pCore 2 G) →
      ⁅A', tr (S : Subgroup G) α g (Fcore G)⁆ = ⊥) ∧
    (¬ A' ≤ tr (S : Subgroup G) α g (CFSG.pCore 2 G) →
      ⁅A', tr (S : Subgroup G) α g (Fcore G)⁆ = tr (S : Subgroup G) α g (Zfix S) ∧
        cj (S : Subgroup G) g = A' ⊔ tr (S : Subgroup G) α g (CFSG.pCore 2 G)) := by
  have hA := isMaxElemAbelian_trInv (α := α) hA'
  have hQS : CFSG.pCore 2 G ≤ (S : Subgroup G) := core_le_sylow S
  have hA'eq : tr (S : Subgroup G) α g (trInv (S : Subgroup G) α g A') = A' := tr_trInv hA'.1
  have hiff : trInv (S : Subgroup G) α g A' ≤ CFSG.pCore 2 G ↔
      A' ≤ tr (S : Subgroup G) α g (CFSG.pCore 2 G) := by
    rw [← tr_le_tr_iff (α := α) (g := g) trInv_le_S hQS, hA'eq]
  refine ⟨fun hle => ?_, fun hnle => ?_⟩
  · have h1 := commutator_A_Fcore_of_le hA (hiff.mpr hle)
    have h2 := congrArg (tr (S : Subgroup G) α g) h1
    rwa [tr_commutator trInv_le_S Fcore_le_sylow, hA'eq, tr_bot] at h2
  · have hnle' : ¬ trInv (S : Subgroup G) α g A' ≤ CFSG.pCore 2 G := fun hh => hnle (hiff.mp hh)
    refine ⟨?_, ?_⟩
    · have h1 := h.commutator_A_Fcore hA hnle'
      have h2 := congrArg (tr (S : Subgroup G) α g) h1
      rwa [tr_commutator trInv_le_S Fcore_le_sylow, hA'eq] at h2
    · have h1 := h.sylow_eq_sup hA hnle'
      have h2 := congrArg (tr (S : Subgroup G) α g) h1
      rwa [tr_self, tr_sup trInv_le_S hQS, hA'eq] at h2

end IsSeed

end Local

end CFSG.QuasithinUnique.Setup.Campbell

module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQ7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerOddAvg

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6 CFSG.QuasithinUnique
open scoped commutatorElement

universe v

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

theorem product_facts [Finite V] {s : ℕ} (hs : 2 ≤ s) (Lfam : Fin s → Subgroup (V ≃ₗ[k] V))
    (hinj : Function.Injective Lfam) (hq : ∀ i, CFSG.IsQuasisimple ↥(Lfam i))
    (hcomm : ∀ i j, i ≠ j → ⁅Lfam i, Lfam j⁆ = ⊥) {A : Subgroup (V ≃ₗ[k] V)}
    (hperm : ∀ a ∈ A, ∀ i, ∃ j, conjSub a (Lfam i) = Lfam j)
    (htrans : ∀ i j, ∃ a ∈ A, conjSub a (Lfam i) = Lfam j) :
    A ≤ Subgroup.normalizer ((⨆ i, Lfam i : Subgroup (V ≃ₗ[k] V)) : Set (V ≃ₗ[k] V)) ∧
      ⁅(⨆ i, Lfam i : Subgroup (V ≃ₗ[k] V)), A⁆ = ⨆ i, Lfam i ∧
      Group.IsPerfect ↥(⨆ i, Lfam i : Subgroup (V ≃ₗ[k] V)) ∧
      NoPQuotient 2 ↥(⨆ i, Lfam i : Subgroup (V ≃ₗ[k] V)) ∧
      CentralPChief 2 ↥(⨆ i, Lfam i : Subgroup (V ≃ₗ[k] V)) := by
  classical
  have : Finite (V ≃ₗ[k] V) := finite_linearEquiv
  obtain ⟨H, hH⟩ : ∃ H : Subgroup (V ≃ₗ[k] V), H = ⨆ i, Lfam i := ⟨_, rfl⟩
  rw [← hH]
  have hLle : ∀ i, Lfam i ≤ H := fun i => hH ▸ le_iSup Lfam i
  have hle : ∀ a ∈ A, conjSub a H ≤ H := by
    intro a ha
    rw [hH, OrderIso.map_iSup]
    refine iSup_le fun i => ?_
    obtain ⟨j, hj⟩ := hperm a ha i
    rw [hj]
    exact le_iSup Lfam j
  have hAnH : A ≤ Subgroup.normalizer (H : Set (V ≃ₗ[k] V)) := fun a ha =>
    mem_normalizer_of_conjSub_le (hle a ha) (hle a⁻¹ (A.inv_mem ha))
  let L' : Fin s → Subgroup ↥H := fun i => (Lfam i).subgroupOf H
  have hq' : ∀ i, CFSG.IsQuasisimple ↥(L' i) := fun i =>
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (hLle i)).symm (hq i)
  have hcomm' : ∀ i j, i ≠ j → ⁅L' i, L' j⁆ = ⊥ := by
    intro i j hij
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.2 fun x hx => ?_
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hcomm i j hij)
      (Subgroup.mem_subgroupOf.1 hx)
    have h2 := Subgroup.mem_centralizer_iff.1 h1 (y : V ≃ₗ[k] V) (Subgroup.mem_subgroupOf.1 hy)
    exact Subtype.ext h2
  have hgen : ⨆ i, L' i = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_iSup, map_subtype_top]
    calc ⨆ i, (L' i).map H.subtype = ⨆ i, Lfam i :=
          iSup_congr fun i => Subgroup.map_subgroupOf_eq_of_le (hLle i)
      _ = H := hH.symm
  obtain ⟨hperf, hno, -, hch, hclos⟩ := quasisimple_product L' hq' hcomm' hgen
  have hL'inj : Function.Injective L' := by
    intro i j h
    apply hinj
    have h1 := congrArg (Subgroup.map H.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le (hLle i),
      Subgroup.map_subgroupOf_eq_of_le (hLle j)] at h1
  let αH : ↥A →* MulAut ↥H := H.normalizerMonoidHom.comp (Subgroup.inclusion hAnH)
  have hαH : ∀ (a : ↥A) (x : ↥H), ((αH a x : ↥H) : V ≃ₗ[k] V) =
      (a : V ≃ₗ[k] V) * (x : V ≃ₗ[k] V) * (a : V ≃ₗ[k] V)⁻¹ := by
    intro a x
    simp [αH]
  have hmapα : ∀ (a : ↥A) (i j : Fin s), conjSub (a : V ≃ₗ[k] V) (Lfam i) = Lfam j →
      (L' i).map (αH a).toMonoidHom = L' j := by
    intro a i j h
    have := map_normalizerMonoidHom_subgroupOf (H := H) ⟨(a : V ≃ₗ[k] V), hAnH a.2⟩ (Lfam i)
    rw [h] at this
    exact this
  have hclos' := hclos hs hL'inj αH.range
    (by
      rintro _ ⟨a, rfl⟩ i
      obtain ⟨j, hj⟩ := hperm a a.2 i
      exact ⟨j, hmapα a i j hj⟩)
    (by
      intro i j
      obtain ⟨a, ha, h⟩ := htrans i j
      exact ⟨αH ⟨a, ha⟩, ⟨_, rfl⟩, hmapα ⟨a, ha⟩ i j h⟩)
  have hHle : H ≤ ⁅H, A⁆ := by
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥H) ∈ Subgroup.closure
        {x : ↥H | ∃ h : ↥H, ∃ a ∈ αH.range, x = h⁻¹ * a h} := by
      rw [hclos']
      trivial
    have hcl : Subgroup.closure {x : ↥H | ∃ h : ↥H, ∃ a ∈ αH.range, x = h⁻¹ * a h} ≤
        ⁅H, A⁆.subgroupOf H := by
      rw [Subgroup.closure_le]
      rintro _ ⟨h, a', ha', rfl⟩
      obtain ⟨a, rfl⟩ := ha'
      show ((h⁻¹ * (αH a) h : ↥H) : V ≃ₗ[k] V) ∈ ⁅H, A⁆
      have e : ((h⁻¹ * (αH a) h : ↥H) : V ≃ₗ[k] V) = ⁅(h : V ≃ₗ[k] V)⁻¹, (a : V ≃ₗ[k] V)⁆ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hαH, commutatorElement_def]
        group
      rw [e]
      exact Subgroup.commutator_mem_commutator (H.inv_mem h.2) a.2
    exact hcl hx'
  exact ⟨hAnH, le_antisymm (commutator_le_left hAnH) hHle, hperf, hno 2 Nat.prime_two,
    hch 2 Nat.prime_two⟩

end CFSG.QuasithinUnique.Setup.Layer

module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerQuasi
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup

section Generic

theorem OddPCoreInClosure.of_odd_card {p : ℕ} {G : Type*} [Group G] [Finite G]
    (h : Odd (Nat.card G)) : OddPCoreInClosure p G :=
  OddPCoreInClosure.of_odd_core fun K _ _ => Odd.of_dvd_nat h (Subgroup.card_subgroup_dvd_card K)

theorem oddPCoreInClosure_of_map_component {C G : Type*} [Group C] [Finite C] [Group G] {p : ℕ}
    (hp : p.Prime) (F : C →* G) (hF : Function.Injective F) (Q : Subgroup G)
    (hQD : Q ≤ F.range) (hQn : ∀ c : C, ∀ q ∈ Q, F c * q * (F c)⁻¹ ∈ Q)
    (hQs : IsSimpleGroup Q) (hQnab : ∃ x y : Q, x * y ≠ y * x) (hpQ : p ∣ Nat.card Q)
    (W : Subgroup G) (hW : ∀ c : C, (∀ q ∈ Q, F c * q = q * F c) → F c ∈ W)
    (hWodd : Odd (Nat.card W)) : OddPCoreInClosure p C := by
  classical
  haveI := hQs
  set Q' : Subgroup C := Q.comap F with hQ'
  haveI : Q'.Normal := ⟨fun q hq c => by
    rw [hQ', Subgroup.mem_comap] at hq ⊢
    rw [map_mul, map_mul, map_inv]
    exact hQn c _ hq⟩
  have hmap : Q'.map F = Q := by
    rw [hQ', Subgroup.map_comap_eq]
    exact inf_eq_right.2 hQD
  let e : Q' ≃* Q := (Subgroup.equivMapOfInjective Q' F hF).trans (MulEquiv.subgroupCongr hmap)
  have hq : CFSG.IsQuasisimple Q' :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hQnab).1
  have hcent : Odd (Nat.card (Subgroup.centralizer (Q' : Set C))) := by
    let ψ : Subgroup.centralizer (Q' : Set C) →* W :=
      { toFun := fun c => ⟨F c, hW c fun q hqQ => by
          obtain ⟨q', rfl⟩ : q ∈ F.range := hQD hqQ
          have hq' : q' ∈ Q' := hqQ
          have h1 : (c : C) * q' = q' * c := (Subgroup.mem_centralizer_iff.1 c.2 q' hq').symm
          rw [← map_mul, ← map_mul, h1]⟩
        map_one' := by ext; simp
        map_mul' := fun a b => by ext; simp }
    have hψ : Function.Injective ψ := fun a b h =>
      Subtype.ext (hF (congrArg Subtype.val h))
    exact hWodd.of_dvd_nat (Subgroup.card_dvd_of_injective ψ hψ)
  exact oddPCoreInClosure_of_quasisimple_normal hp Q' hq hcent
    (fun _ => by rw [Nat.card_congr e.toEquiv]; exact hpQ)

end Generic

section Pinned

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem even_pinned_component_data (τ : Tag) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    IsSimpleGroup (rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) : Subgroup (ModGL τ K)) ∧
      (∃ x y : (rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) : Subgroup (ModGL τ K)),
        x * y ≠ y * x) ∧
      Nat.card (rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) : Subgroup (ModGL τ K)) =
        Nat.card K * (Nat.card K ^ 2 - 1) := by
  obtain ⟨-, -, ⟨e, -⟩, -, -, -, -, -, -, -, -, hfin⟩ :=
    CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps τ K hα
  obtain ⟨hs, -, hnab⟩ := hfin inferInstance hq
  refine ⟨hs, hnab, ?_⟩
  rw [← Nat.card_congr e.toEquiv, ← CFSG.Open.StatedAPI.card_statedSL]
  exact CFSG.Open.StatedAPI.card_statedSL_two K

end Pinned

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

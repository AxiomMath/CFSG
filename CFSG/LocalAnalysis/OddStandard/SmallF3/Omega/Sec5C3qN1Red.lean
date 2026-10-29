module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qN1Hom
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qS59Facts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEIso2
public import Certificates.Data.ExceptionalSL3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Type3Bound : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V), Q.Nondegenerate → Module.finrank (ZMod 3) V = 6 →
      quadSign Q = -1 → ∀ F : Subgroup (ProjSim Q), (∀ x ∈ F, x * x = 1) →
        Set.ncard {x : ProjSim Q | x ∈ F ∧ SimHasDim x 3} ≤ 10

theorem sec5c3q_ncard_le_mul {α β : Type*} [Finite α] (f : α → β) (S : Set α) (c : ℕ)
    (hfib : ∀ y : β, {a | a ∈ S ∧ f a = y}.ncard ≤ c) : S.ncard ≤ c * (f '' S).ncard := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  have key := Finset.card_le_mul_card_image_of_maps_to (f := f) (s := S.toFinset)
    (t := (f '' S).toFinset)
    (fun a ha => by
      simp only [Set.mem_toFinset] at ha ⊢
      exact ⟨a, ha, rfl⟩) c
    (fun y _ => by
      have h := hfib y
      have e1 : ({a | a ∈ S ∧ f a = y} : Set α).ncard =
          (S.toFinset.filter fun a => f a = y).card := by
        rw [← Set.ncard_coe_finset]
        congr 1
        ext a
        simp
      rw [e1] at h
      exact h)
  rwa [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card' (f '' S)]

theorem asc82E64Kind3_of (h3 : Asc82Type3Bound) : Asc82E64Kind3 := by
  classical
  intro G _ _ L hL E hEN hE hC
  have hLp : commutator ↥L = ⊤ := hL.1.1.commutator_eq_top
  have hsq : ∀ x ∈ E, x * x = 1 := fun x hx => by
    rw [← pow_two]
    exact hE.1.2 x hx
  by_cases hne : {x : G | x ∈ E ∧ ∃ α : ℤˣ, InducesTypeSome L x 6 (-1) 3 α}.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Set.ncard_empty]
    exact Nat.zero_le _
  obtain ⟨s₀, -, α₀, V, _, _, _, Q, hQ, e, x₀, hdim, hsgn, -, -⟩ := hne
  haveI : Finite V := Module.finite_of_finite (ZMod 3)
  haveI : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun f : V ≃ₗ[ZMod 3] V => (f : V → V))
      (fun f g h => LinearEquiv.ext (congrFun h))
  haveI : Finite (simGroup Q) := Subtype.finite
  haveI : Finite (ProjSim Q) := inferInstance
  set ψ : ↥E →* ProjSim Q := sec5c3q_n1Psi hQ hdim hsgn e hEN with hψ
  have hF : ∀ y ∈ ψ.range, y * y = 1 := by
    rintro _ ⟨r, rfl⟩
    exact sec5c3q_n1Psi_sq hQ hdim hsgn e hEN hsq r
  have h10 := h3 V Q hQ hdim hsgn ψ.range hF
  let g : G → ProjSim Q := fun x => if hx : x ∈ E then ψ ⟨x, hx⟩ else 1
  have hg : ∀ (x : G) (hx : x ∈ E), g x = ψ ⟨x, hx⟩ := fun x hx => dif_pos hx
  set T : Set G := {x : G | x ∈ E ∧ ∃ α : ℤˣ, InducesTypeSome L x 6 (-1) 3 α} with hT
  have himg : g '' T ⊆ {y : ProjSim Q | y ∈ ψ.range ∧ SimHasDim y 3} := by
    rintro _ ⟨x, ⟨hxE, α, V', _, _, _, Q', hQ', e', x', hdim', hsgn', hind', hty'⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [hg x hxE]
      exact ⟨_, rfl⟩
    · rw [hg x hxE]
      exact simHasDim_of_inducesViaP hQ hQ' ⟨hdim, hsgn⟩ ⟨hdim', hsgn'⟩ e e'
        (sec5c3q_n1Psi_induces hQ hdim hsgn e hEN ⟨x, hxE⟩) hind' hty'.simHasDim
  have hfib : ∀ y : ProjSim Q, {a | a ∈ T ∧ g a = y}.ncard ≤ 2 := by
    intro y
    by_cases hy : ∃ a₀, a₀ ∈ T ∧ g a₀ = y
    · obtain ⟨a₀, ha₀T, ha₀y⟩ := hy
      have ha₀E : a₀ ∈ E := ha₀T.1
      have hinj : Set.InjOn (fun a : G => a₀⁻¹ * a) {a | a ∈ T ∧ g a = y} :=
        fun a _ b _ h => mul_left_cancel h
      have hmaps : ∀ a ∈ {a | a ∈ T ∧ g a = y},
          (fun a : G => a₀⁻¹ * a) a ∈ ((E ⊓ centralizer (L : Set G) : Subgroup G) : Set G) := by
        rintro a ⟨haT, hay⟩
        have haE : a ∈ E := haT.1
        refine Subgroup.mem_inf.mpr ⟨E.mul_mem (E.inv_mem ha₀E) haE, ?_⟩
        exact sec5c3q_n1Psi_fibre hQ hdim hsgn hLp e hEN (r := ⟨a₀, ha₀E⟩) (r' := ⟨a, haE⟩)
          (by rw [← hg a₀ ha₀E, ← hg a haE, ha₀y, hay])
      calc {a | a ∈ T ∧ g a = y}.ncard
          ≤ ((E ⊓ centralizer (L : Set G) : Subgroup G) : Set G).ncard :=
            Set.ncard_le_ncard_of_injOn _ hmaps hinj (Set.toFinite _)
        _ = Nat.card ↥(E ⊓ centralizer (L : Set G)) := rfl
        _ ≤ 2 := hC
    · push Not at hy
      have hempty : {a | a ∈ T ∧ g a = y} = ∅ :=
        Set.eq_empty_of_forall_notMem fun a ha => hy a ha.1 ha.2
      rw [hempty, Set.ncard_empty]
      exact Nat.zero_le _
  calc T.ncard ≤ 2 * (g '' T).ncard := sec5c3q_ncard_le_mul g T 2 hfib
    _ ≤ 2 * 10 := Nat.mul_le_mul_left 2 ((Set.ncard_le_ncard himg (Set.toFinite _)).trans h10)
    _ = 20 := rfl

end CFSG.OddStandard.SmallF3.Omega

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.ONAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSTransport

public noncomputable section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.ONSchreier CFSG.Sporadic.ONOddCore CFSG.Blueprint.NativeSporadic

theorem mem_center_iff_of_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (a : A) :
    a ∈ Subgroup.center A ↔ e a ∈ Subgroup.center B := by
  have hc : (Subgroup.center A).map e.toMonoidHom = Subgroup.center B := Subgroup.map_center_eq e
  constructor
  · intro ha
    rw [← hc]
    exact Subgroup.mem_map_of_mem _ ha
  · intro ha
    rw [← hc] at ha
    obtain ⟨y, hy, hya⟩ := ha
    have : y = a := e.injective hya
    rwa [this] at hy

theorem oneClassOutside_of_equiv {X Y : Type} [Group X] [Group Y] {A : Subgroup X}
    {B : Subgroup Y} (e : ↥A ≃* ↥B) (h : OneClassOutside B) : OneClassOutside A := by
  have hcen : ∀ a : A, a ∈ Subgroup.center ↥A ↔ e a ∈ Subgroup.center ↥B :=
    mem_center_iff_of_equiv e
  have key : ∀ {a : X} (ha : a ∈ A), a * a = 1 → a ≠ 1 →
      a ∉ (Subgroup.center ↥A).map A.subtype →
      (e ⟨a, ha⟩ : Y) * (e ⟨a, ha⟩ : Y) = 1 ∧ (e ⟨a, ha⟩ : Y) ≠ 1 ∧
        (e ⟨a, ha⟩ : Y) ∉ (Subgroup.center ↥B).map B.subtype := by
    intro a ha ha2 ha1 hac
    refine ⟨?_, fun h1 => ha1 ?_, fun h1 => hac ?_⟩
    · have : e (⟨a, ha⟩ * ⟨a, ha⟩) = e 1 := congrArg e (Subtype.ext ha2)
      rw [map_mul, map_one] at this
      exact congrArg Subtype.val this
    · have h2 : e ⟨a, ha⟩ = 1 := Subtype.ext h1
      have := e.injective (h2.trans (map_one e).symm)
      exact congrArg Subtype.val this
    · obtain ⟨y, hy, hya⟩ := h1
      have hy' : y = e ⟨a, ha⟩ := Subtype.ext hya
      rw [hy'] at hy
      exact ⟨⟨a, ha⟩, (hcen _).2 hy, rfl⟩
  intro v hv v' hv' hvv hv'v' hv1 hv'1 hvc hv'c
  obtain ⟨h1, h2, h3⟩ := key hv hvv hv1 hvc
  obtain ⟨h1', h2', h3'⟩ := key hv' hv'v' hv'1 hv'c
  obtain ⟨c, hcB, hcv⟩ := h _ (e ⟨v, hv⟩).2 _ (e ⟨v', hv'⟩).2 h1 h1' h2 h2' h3 h3'
  refine ⟨((e.symm ⟨c, hcB⟩ : ↥A) : X), (e.symm ⟨c, hcB⟩ : ↥A).2, ?_⟩
  have h5 : e (e.symm ⟨c, hcB⟩ * ⟨v, hv⟩ * (e.symm ⟨c, hcB⟩)⁻¹) = e ⟨v', hv'⟩ := by
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact Subtype.ext hcv
  exact congrArg Subtype.val (e.injective h5)

section Model


theorem on_model {G : Type} [Group G] {L : Subgroup G} {u : G} (hL : IsSporadic L .ONan)
    (hu : u ∈ L) (hu2 : orderOf u = 2) :
    ∃ Ψ : ↥L →* Equiv.Perm (Fin N), Function.Injective Ψ ∧ (∀ x, Ψ x ∈ Pv) ∧
      (∀ y ∈ Pv, ∃ x, Ψ x = y) ∧ Ψ ⟨u, hu⟩ = onz := by
  obtain ⟨f⟩ := on_equiv_Pv hL
  have ha : orderOf (f ⟨u, hu⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hu2]
  obtain ⟨g, hg⟩ := pv_conj_zP _ ha
  refine ⟨Pv.subtype.comp ((MulAut.conj g⁻¹).toMonoidHom.comp f.toMonoidHom), ?_, ?_, ?_, ?_⟩
  · exact Pv.subtype_injective.comp ((MulAut.conj g⁻¹).injective.comp f.injective)
  · intro x
    exact ((MulAut.conj g⁻¹) (f x)).2
  · intro y hy
    refine ⟨f.symm (g * ⟨y, hy⟩ * g⁻¹), ?_⟩
    show (((MulAut.conj g⁻¹) (f (f.symm (g * ⟨y, hy⟩ * g⁻¹))) : Pv) : Equiv.Perm (Fin N)) = y
    rw [MulEquiv.apply_symm_apply, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  · show (((MulAut.conj g⁻¹) (f ⟨u, hu⟩) : Pv) : Equiv.Perm (Fin N)) = onz
    rw [hg, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    show (g : Equiv.Perm (Fin N))⁻¹ *
      ((g : Equiv.Perm (Fin N)) * onz * (g : Equiv.Perm (Fin N))⁻¹) * g = onz
    group

theorem on_K₀_eq {G : Type} [Group G] {L K : Subgroup G} {u : G} (hu : u ∈ L) (hKL : K ≤ L)
    (hKu : ∀ k ∈ K, k * u = u * k) (hperf : Group.IsPerfect K) (hcard : Nat.card K = 80640)
    (Ψ : ↥L →* Equiv.Perm (Fin N)) (hΨ : Function.Injective Ψ) (hΨL : ∀ x, Ψ x ∈ Pv)
    (hΨu : Ψ ⟨u, hu⟩ = onz) : (K.subgroupOf L).map Ψ = onL := by
  have hperf' : Group.IsPerfect (K.subgroupOf L) := isPerfect_subgroupOf_of_le hKL hperf
  have hcard' : Nat.card (K.subgroupOf L) = 80640 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv]
    exact hcard
  set K₀ : Subgroup (Equiv.Perm (Fin N)) := (K.subgroupOf L).map Ψ with hK₀
  have hK₀M : K₀ ≤ onM := by
    rintro _ ⟨k, hk, rfl⟩
    rw [onM_eq_centralizer_z]
    refine ⟨hΨL k, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [← hΨu, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hKu k (Subgroup.mem_subgroupOf.1 hk))
  have hK₀perf : Group.IsPerfect K₀ := by
    have := hperf'
    exact Group.IsPerfect.map _
  have hK₀card : Nat.card K₀ = 80640 := by
    rw [hK₀, Subgroup.card_map_of_injective hΨ, hcard']
  have hEperf : Group.IsPerfect (onL.subgroupOf onM) :=
    isPerfect_subgroupOf_of_le onL_le_M onL_isPerfect
  have hFcard : Nat.card (K₀.subgroupOf onM) = 80640 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK₀M).toEquiv, hK₀card]
  have hEi : (onL.subgroupOf onM).index = 2 := by
    have h := (onL.subgroupOf onM).card_mul_index
    rw [card_L_subgroupOf, card_onM] at h
    omega
  have hFi : (K₀.subgroupOf onM).index = 2 := by
    have h := (K₀.subgroupOf onM).card_mul_index
    rw [hFcard, card_onM] at h
    omega
  have heq := eq_of_index_two_of_isPerfect hEperf hEi hFi
  rw [Subgroup.subgroupOf_inj, inf_eq_left.2 hK₀M, inf_eq_left.2 onL_le_M] at heq
  exact heq

end Model

end CFSG.EvenSporadicStandard.Solomon78

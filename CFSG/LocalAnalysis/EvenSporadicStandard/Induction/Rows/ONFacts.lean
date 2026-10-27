module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzONAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSONLocal
public import CFSG.Sporadic.SuzOddCore.CompQuot

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78 CFSG.ONSchreier
  CFSG.Sporadic.ONOddCore CFSG.Blueprint.NativeSporadic Cover


theorem on_perfect_le {G : Type} [Group G] [Finite G] {L K : Subgroup G} {u : G}
    (hL : IsSporadic L .ONan) (hQ : ONPair G L K u) :
    ∀ P : Subgroup G, P ≤ L ⊓ centralizer ({u} : Set G) → Group.IsPerfect ↥P → P ≤ K := by
  obtain ⟨hu, hu2, hKL, hKu, hperf, hcard⟩ := hQ
  obtain ⟨Ψ, hΨ, hΨL, hΨR, hΨu⟩ := on_model hL hu hu2
  have hK₀ := on_K₀_eq hu hKL hKu hperf hcard Ψ hΨ hΨL hΨu
  intro P hP hPperf
  have hPL : P ≤ L := fun x hx => (hP hx).1
  have hPM : (P.subgroupOf L).map Ψ ≤ onM := by
    rintro _ ⟨s, hs, rfl⟩
    rw [onM_eq_centralizer_z]
    refine ⟨hΨL _, mem_centralizer_singleton_iff.2 ?_⟩
    rw [← hΨu, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hP (Subgroup.mem_subgroupOf.1 hs)).2)
  have hP₀perf : Group.IsPerfect ↥((P.subgroupOf L).map Ψ) := by
    have : Group.IsPerfect (P.subgroupOf L) := isPerfect_subgroupOf_of_le hPL hPperf
    exact Group.IsPerfect.map _
  have hP₁ : Group.IsPerfect (((P.subgroupOf L).map Ψ).subgroupOf onM) :=
    isPerfect_subgroupOf_of_le hPM hP₀perf
  have hEi : (onL.subgroupOf onM).index = 2 := by
    have h := (onL.subgroupOf onM).card_mul_index
    rw [card_L_subgroupOf, card_onM] at h
    omega
  have hP₁le : ((P.subgroupOf L).map Ψ).subgroupOf onM ≤ onL.subgroupOf onM := by
    have h1 : ⁅((P.subgroupOf L).map Ψ).subgroupOf onM, ((P.subgroupOf L).map Ψ).subgroupOf onM⁆ =
        ((P.subgroupOf L).map Ψ).subgroupOf onM := isPerfect_iff.mp hP₁
    rw [← h1]
    exact (Subgroup.commutator_mono le_top le_top).trans
      (CFSG.Sporadic.SuzOddCore.commutator_le_of_index_two hEi)
  intro x hx
  have h2 : Ψ ⟨x, hPL hx⟩ ∈ onL := by
    have hmem : (⟨Ψ ⟨x, hPL hx⟩, hPM ⟨⟨x, hPL hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩⟩ : ↥onM) ∈
        ((P.subgroupOf L).map Ψ).subgroupOf onM :=
      Subgroup.mem_subgroupOf.2 ⟨⟨x, hPL hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hP₁le hmem)
  rw [← hK₀] at h2
  obtain ⟨k, hk, hkx⟩ := h2
  have hkx' : k = ⟨x, hPL hx⟩ := hΨ hkx
  rw [hkx'] at hk
  exact Subgroup.mem_subgroupOf.1 hk

theorem elemBound_two_of_isCyclic {X : Type*} [Group X] [IsCyclic X] : ElemBound 2 X := by
  intro E hE2 _
  have hcyc : IsCyclic ↥E := Subgroup.isCyclic E
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hg2 : g * g = 1 := Subtype.ext (hE2 g g.2)
  have hord : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hg2)
  have hcard : Nat.card ↥E = orderOf g := (orderOf_eq_card_of_forall_mem_zpowers hg).symm
  rw [hcard]
  exact Nat.le_of_dvd (by norm_num) hord

theorem on_autCentralizer_facts {G : Type} [Group G] [Finite G] {L K : Subgroup G} {u : G}
    (hL : IsSporadic L .ONan) (hQ : ONPair G L K u) :
    Group.IsSolvable ↥(autCentralizer L K) ∧ ElemBound 2 ↥(autCentralizer L K) ∧
      ∀ α ∈ autCentralizer L K, ∃ g : ↥L, α = MulAut.conj g := by
  obtain ⟨hu, hu2, hKL, hKu, hperf, hcard⟩ := hQ
  obtain ⟨Ψ, hΨ, hΨL, hΨR, hΨu⟩ := on_model hL hu hu2
  have hK₀ := on_K₀_eq hu hKL hKu hperf hcard Ψ hΨ hΨL hΨu
  let Ψ' : ↥L →* ↥Pv := Ψ.codRestrict Pv hΨL
  have hbij : Function.Bijective Ψ' := ⟨fun a b h => hΨ (congrArg Subtype.val h), fun y => by
    obtain ⟨x, hx⟩ := hΨR y y.2
    exact ⟨x, Subtype.ext hx⟩⟩
  let ψ : ↥L ≃* ↥Pv := MulEquiv.ofBijective Ψ' hbij
  let Θ : MulAut ↥L →* MulAut ↥Pv := (MulAut.congr ψ).toMonoidHom
  have hΘ : Function.Injective Θ := (MulAut.congr ψ).injective
  have hQP : onQ ≤ Pv := onQ_le_L.trans onL_le
  have h1 : (autCentralizer L K).map Θ ≤
      (onQ.subgroupOf Pv).map (MulAut.conj : ↥Pv →* MulAut ↥Pv) := by
    rintro _ ⟨α, hα, rfl⟩
    have hβ : ∀ x : Pv, (x : Equiv.Perm (Fin N)) ∈ onL → (MulAut.congr ψ α) x = x := by
      intro x hx
      obtain ⟨k, rfl⟩ := ψ.surjective x
      have h0 : Ψ k ∈ (K.subgroupOf L).map Ψ := by
        rw [hK₀]
        exact hx
      obtain ⟨k', hk', hkk⟩ := h0
      have hk'k : k' = k := hΨ hkk
      rw [hk'k] at hk'
      have hk : (k : G) ∈ K := Subgroup.mem_subgroupOf.1 hk'
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hα k hk]
    obtain ⟨p, hp⟩ := on_pointwise_L_inner _ hβ
    refine ⟨p, ?_, hp⟩
    show p ∈ onQ.subgroupOf Pv
    rw [Subgroup.mem_subgroupOf]
    have hcomm : ∀ y ∈ onL, y * (p : Equiv.Perm (Fin N)) = (p : Equiv.Perm (Fin N)) * y := by
      intro y hy
      have h2 := hβ ⟨y, onL_le hy⟩ hy
      rw [← hp, MulAut.conj_apply] at h2
      have h3 : p * (⟨y, onL_le hy⟩ : Pv) = (⟨y, onL_le hy⟩ : Pv) * p := by
        calc p * (⟨y, onL_le hy⟩ : Pv) = p * ⟨y, onL_le hy⟩ * p⁻¹ * p := by group
          _ = ⟨y, onL_le hy⟩ * p := by rw [h2]
      exact (congrArg Subtype.val h3).symm
    rw [← onM_centralizer_L]
    refine ⟨?_, Subgroup.mem_centralizer_iff.2 hcomm⟩
    rw [onM_eq_centralizer_z]
    exact ⟨p.2, Subgroup.mem_centralizer_singleton_iff.2 (hcomm _ onz_mem_L).symm⟩
  have hcardS : Nat.card ↥((onQ.subgroupOf Pv).map (MulAut.conj : ↥Pv →* MulAut ↥Pv)) ∣ 4 := by
    have h2 := Subgroup.card_map_dvd (onQ.subgroupOf Pv) (MulAut.conj : ↥Pv →* MulAut ↥Pv)
    have h3 : Nat.card (onQ.subgroupOf Pv) = 4 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv, card_onQ]
    rw [h3] at h2
    exact h2
  have hSsolv : Group.IsSolvable ↥((onQ.subgroupOf Pv).map
      (MulAut.conj : ↥Pv →* MulAut ↥Pv)) := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (show Nat.card ↥((onQ.subgroupOf Pv).map (MulAut.conj : ↥Pv →* MulAut ↥Pv)) ∣ 2 ^ 2 by
        simpa using hcardS)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hP : IsPGroup 2 ↥((onQ.subgroupOf Pv).map (MulAut.conj : ↥Pv →* MulAut ↥Pv)) :=
      IsPGroup.of_card hk
    have := hP.isNilpotent
    infer_instance
  let f : ↥(autCentralizer L K) →*
      ↥((onQ.subgroupOf Pv).map (MulAut.conj : ↥Pv →* MulAut ↥Pv)) :=
    (Θ.comp (autCentralizer L K).subtype).codRestrict _ (fun α => h1 ⟨α, α.2, rfl⟩)
  have hf : Function.Injective f := fun a b h => Subtype.ext (hΘ (congrArg Subtype.val h))
  have hcyc : IsCyclic ↥((onQ.subgroupOf Pv).map (MulAut.conj : ↥Pv →* MulAut ↥Pv)) := by
    have h5 : IsCyclic ↥(onQ.subgroupOf Pv) := by
      have : IsCyclic ↥onQ := by
        rw [onQ]
        infer_instance
      exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hQP).symm.toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hQP).symm.surjective
    exact isCyclic_of_surjective ((MulAut.conj : ↥Pv →* MulAut ↥Pv).subgroupMap
      (onQ.subgroupOf Pv)) ((MulAut.conj : ↥Pv →* MulAut ↥Pv).subgroupMap_surjective _)
  refine ⟨Group.isSolvable_of_isSolvable_injective hf, ElemBound.of_injective
    elemBound_two_of_isCyclic hf, ?_⟩
  · intro α hα
    obtain ⟨p, -, hp⟩ := h1 ⟨α, hα, rfl⟩
    refine ⟨ψ.symm p, hΘ ?_⟩
    rw [← hp]
    ext z
    simp [Θ, MulAut.congr_apply, MulAut.conj_apply]

theorem on_autFixFacts {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} {u : Y}
    (hY : IsSporadic ↥(⊤ : Subgroup Y) .ONan) (hQ : ONPair Y ⊤ K u) : AutFixFacts K 2 :=
  autFixFacts_of_top (on_autCentralizer_facts hY hQ).1 (on_autCentralizer_facts hY hQ).2.1
    (on_autCentralizer_facts hY hQ).2.2

end CFSG.EvenSporadicStandard.Induction

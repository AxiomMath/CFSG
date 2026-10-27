module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup
open scoped commutatorElement

@[expose] def IsSection (Y B : Type*) [Group Y] [Group B] : Prop :=
  ∃ (U : Subgroup B) (φ : ↥U →* Y), Function.Surjective φ

variable {Y B D : Type*} [Group Y] [Group B] [Group D]

theorem IsSection.of_surjective (f : D →* B) (hf : Function.Surjective f) (h : IsSection Y B) :
    IsSection Y D := by
  obtain ⟨U, φ, hφ⟩ := h
  let g : ↥(U.comap f) →* ↥U :=
    { toFun := fun x => ⟨f x, x.2⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp }
  refine ⟨U.comap f, φ.comp g, hφ.comp ?_⟩
  intro u
  obtain ⟨d, hd⟩ := hf u
  exact ⟨⟨d, by simp [hd]⟩, Subtype.ext hd⟩

theorem IsSection.of_le (U : Subgroup B) (h : IsSection Y ↥U) : IsSection Y B := by
  obtain ⟨V, φ, hφ⟩ := h
  exact ⟨V.map U.subtype, φ.comp (V.equivMapOfInjective U.subtype U.subtype_injective).symm.toMonoidHom,
    hφ.comp (V.equivMapOfInjective U.subtype U.subtype_injective).symm.surjective⟩

theorem IsSection.of_le_le {P L : Subgroup B} (hPL : P ≤ L) (h : IsSection Y ↥P) : IsSection Y ↥L := by
  refine IsSection.of_le (P.subgroupOf L) ?_
  exact IsSection.of_surjective (Subgroup.subgroupOfEquivOfLe hPL).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hPL).surjective h

theorem IsSection.of_equiv (e : D ≃* B) (h : IsSection Y B) : IsSection Y D :=
  IsSection.of_surjective e.toMonoidHom e.surjective h

theorem IsSection.dichotomy [IsSimpleGroup Y] (N : Subgroup B) [N.Normal] (h : IsSection Y B) :
    IsSection Y ↥N ∨ IsSection Y (B ⧸ N) := by
  classical
  obtain ⟨U, φ, hφ⟩ := h
  have hMn : (N.subgroupOf U).Normal := inferInstance
  have hmapn : ((N.subgroupOf U).map φ).Normal := hMn.map φ hφ
  have := hmapn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf U).map φ) with hbot | htop
  · right
    let ψ : ↥U →* B ⧸ N := (QuotientGroup.mk' N).comp U.subtype
    have hker : ψ.ker = N.subgroupOf U := by
      ext u
      simp [ψ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have hle : ψ.ker ≤ φ.ker := by
      rw [hker]
      intro u hu
      have : φ u ∈ (N.subgroupOf U).map φ := ⟨u, hu, rfl⟩
      rw [hbot] at this
      simpa using this
    let Φ : ↥ψ.range →* Y :=
      (QuotientGroup.lift ψ.ker φ hle).comp (QuotientGroup.quotientKerEquivRange ψ).symm.toMonoidHom
    refine ⟨ψ.range, Φ, ?_⟩
    have h1 : Function.Surjective (QuotientGroup.lift ψ.ker φ hle) := by
      intro y
      obtain ⟨u, hu⟩ := hφ y
      exact ⟨QuotientGroup.mk u, by simpa using hu⟩
    exact h1.comp (QuotientGroup.quotientKerEquivRange ψ).symm.surjective
  · left
    let g : ↥(U.subgroupOf N) →* ↥U :=
      { toFun := fun x => ⟨(x : N), x.2⟩
        map_one' := by ext; simp
        map_mul' := fun x y => by ext; simp }
    refine ⟨U.subgroupOf N, φ.comp g, ?_⟩
    intro y
    have hy : y ∈ (N.subgroupOf U).map φ := by rw [htop]; trivial
    obtain ⟨m, hm, rfl⟩ := hy
    exact ⟨⟨⟨(m : B), hm⟩, by simp [Subgroup.mem_subgroupOf]⟩, rfl⟩

theorem IsSection.isSolvable (hB : Group.IsSolvable B) (h : IsSection Y B) : Group.IsSolvable Y := by
  obtain ⟨U, φ, hφ⟩ := h
  have : Group.IsSolvable ↥U := inferInstance
  exact Group.isSolvable_of_surjective hφ

theorem IsSection.card_dvd [Finite B] (h : IsSection Y B) : Nat.card Y ∣ Nat.card B := by
  obtain ⟨U, φ, hφ⟩ := h
  exact (Subgroup.card_dvd_of_surjective hφ).trans (Subgroup.card_subgroup_dvd_card U)

theorem commutator_eq_top_of_simple [IsSimpleGroup Y] (hns : ¬ Group.IsSolvable Y) :
    commutator Y = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Y) with h | h
  · exfalso
    apply hns
    refine IsSimpleGroup.comm_iff_isSolvable.mp fun a b => ?_
    have : ⁅a, b⁆ ∈ commutator Y :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h] at this
    exact commutatorElement_eq_one_iff_mul_comm.mp (by simpa using this)
  · exact h

theorem exists_perfect_section [Finite B] [IsSimpleGroup Y] (hns : ¬ Group.IsSolvable Y)
    (h : IsSection Y B) : ∃ P : Subgroup B, Group.IsPerfect ↥P ∧ IsSection Y ↥P := by
  classical
  have hex : ∃ n : ℕ, ∃ U : Subgroup B, Nat.card ↥U = n ∧ ∃ φ : ↥U →* Y, Function.Surjective φ := by
    obtain ⟨U, φ, hφ⟩ := h
    exact ⟨_, U, rfl, φ, hφ⟩
  obtain ⟨U₀, hU₀, φ₀, hφ₀⟩ := Nat.find_spec hex
  have hY := commutator_eq_top_of_simple hns
  let C₀ : Subgroup ↥U₀ := commutator ↥U₀
  have hmap : C₀.map φ₀ = commutator Y := by
    have h1 := Subgroup.map_commutator (⊤ : Subgroup ↥U₀) ⊤ φ₀
    have h2 : Subgroup.map φ₀ (⊤ : Subgroup ↥U₀) = ⊤ := by
      rw [← MonoidHom.range_eq_map]; exact MonoidHom.range_eq_top.mpr hφ₀
    rw [h2] at h1
    exact h1
  let U₁ : Subgroup B := C₀.map U₀.subtype
  let e₁ : ↥C₀ ≃* ↥U₁ := C₀.equivMapOfInjective U₀.subtype U₀.subtype_injective
  have hcard₁ : Nat.card ↥U₁ = Nat.card ↥C₀ := (Nat.card_congr e₁.toEquiv).symm
  have hsec₁ : ∃ φ : ↥U₁ →* Y, Function.Surjective φ := by
    refine ⟨(φ₀.comp C₀.subtype).comp e₁.symm.toMonoidHom, ?_⟩
    intro y
    have hy : y ∈ C₀.map φ₀ := by rw [hmap, hY]; trivial
    obtain ⟨c, hc, rfl⟩ := hy
    exact ⟨e₁ ⟨c, hc⟩, by simp⟩
  have hle : Nat.find hex ≤ Nat.card ↥U₁ := Nat.find_min' hex ⟨U₁, rfl, hsec₁⟩
  have hC₀le : Nat.card ↥C₀ ≤ Nat.card ↥U₀ := Subgroup.card_le_card_group C₀
  have hC₀top : C₀ = ⊤ := by
    rw [← Subgroup.card_eq_iff_eq_top]
    omega
  refine ⟨U₀, Group.isPerfect_def.mpr hC₀top, ?_⟩
  exact ⟨⊤, φ₀.comp (⊤ : Subgroup ↥U₀).subtype, hφ₀.comp (fun u => ⟨⟨u, trivial⟩, rfl⟩)⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87

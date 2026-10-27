module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrCover

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem sec63PT_disjoint_ker {A P : Type} [Group A] [Finite A] [Group P] (ρ : A →* P)
    (hodd : Odd (Nat.card ρ.ker)) {Q : Subgroup A} (hQ : IsPGroup 2 Q) : Disjoint Q ρ.ker :=
  IsPGroup.disjoint_of_coprime hQ IsPGroup.card (Nat.coprime_two_left.mpr hodd)

theorem sec63PT_card_map_of_disjoint {A P : Type} [Group A] [Group P] (ρ : A →* P)
    {Q : Subgroup A} (hQ : Disjoint Q ρ.ker) : Nat.card (Q.map ρ) = Nat.card Q := by
  let φ : ↥Q → ↥(Q.map ρ) := fun q => ⟨ρ q, Subgroup.mem_map_of_mem ρ q.2⟩
  have hφinj : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    have hab' : ρ a.1 = ρ b.1 := Subtype.ext_iff.mp hab
    have hmem : a.1⁻¹ * b.1 ∈ Q := Q.mul_mem (Q.inv_mem a.2) b.2
    have hker : a.1⁻¹ * b.1 ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab', inv_mul_cancel]
    have h1 : a.1⁻¹ * b.1 = 1 := Subgroup.disjoint_def.mp hQ hmem hker
    rwa [inv_mul_eq_one] at h1
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, hxQ, hxρ⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hxQ⟩, Subtype.ext hxρ⟩
  exact (Nat.card_congr (Equiv.ofBijective φ ⟨hφinj, hφsurj⟩)).symm

theorem sec63PT_card_le_two_of_map {A P : Type} [Group A] [Finite A] [Group P] {ρ : A →* P}
    (hodd : Odd (Nat.card ρ.ker)) {Q : Subgroup A} (hQ : IsPGroup 2 Q)
    (h : Nat.card (Q.map ρ) ≤ 2) : Nat.card Q ≤ 2 := by
  rw [← sec63PT_card_map_of_disjoint ρ (sec63PT_disjoint_ker ρ hodd hQ)]
  exact h

theorem sec63PT_exists_pGroup_lift {A P : Type} [Group A] [Finite A] [Group P] (ρ : A →* P)
    (hodd : Odd (Nat.card ρ.ker)) (H : Subgroup A) (R : Subgroup P) (hR : IsPGroup 2 R)
    (hRH : R ≤ H.map ρ) :
    ∃ S : Subgroup A, S ≤ H ∧ IsPGroup 2 S ∧ Disjoint S ρ.ker ∧ S.map ρ = R := by
  let H' : Subgroup A := H ⊓ R.comap ρ
  have hH'le : H' ≤ H := inf_le_left
  have hH'comap : H' ≤ R.comap ρ := inf_le_right
  have hmap : H'.map ρ = R := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      exact hH'comap
    · intro r hr
      obtain ⟨h, hhH, hhρ⟩ := Subgroup.mem_map.mp (hRH hr)
      exact Subgroup.mem_map.mpr
        ⟨h, ⟨hhH, Subgroup.mem_comap.mpr (by rw [hhρ]; exact hr)⟩, hhρ⟩
  let f : ↥H' →* ↥R := (ρ.comp H'.subtype).codRestrict R (fun x => x.2.2)
  have hf_surj : Function.Surjective f := by
    intro y
    have hy : (y : P) ∈ H'.map ρ := hmap.symm ▸ y.2
    obtain ⟨x, hxH', hxρ⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hxH'⟩, Subtype.ext hxρ⟩
  let Ptop : Sylow 2 ↥R :=
    (hR.to_subgroup (⊤ : Subgroup ↥R)).toSylow (by rw [Subgroup.index_top]; norm_num)
  obtain ⟨S₀, hS₀⟩ := Sylow.mapSurjective_surjective hf_surj 2 Ptop
  have hS₀map : (S₀ : Subgroup ↥H').map f = ⊤ :=
    congrArg (fun P : Sylow 2 ↥R => (P : Subgroup ↥R)) hS₀
  let S : Subgroup A := (S₀ : Subgroup ↥H').map H'.subtype
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · exact (Subgroup.map_subtype_le (S₀ : Subgroup ↥H')).trans hH'le
  · exact S₀.isPGroup'.map H'.subtype
  · exact sec63PT_disjoint_ker ρ hodd (S₀.isPGroup'.map H'.subtype)
  · have hcomp : ρ.comp H'.subtype = R.subtype.comp f := MonoidHom.ext fun _ => rfl
    calc S.map ρ = ((S₀ : Subgroup ↥H').map H'.subtype).map ρ := rfl
      _ = (S₀ : Subgroup ↥H').map (ρ.comp H'.subtype) :=
            Subgroup.map_map (S₀ : Subgroup ↥H') ρ H'.subtype
      _ = (S₀ : Subgroup ↥H').map (R.subtype.comp f) := by rw [hcomp]
      _ = ((S₀ : Subgroup ↥H').map f).map R.subtype :=
            (Subgroup.map_map (S₀ : Subgroup ↥H') R.subtype f).symm
      _ = (⊤ : Subgroup ↥R).map R.subtype := by rw [hS₀map]
      _ = R := by rw [Subgroup.map_top, Subgroup.range_subtype]

theorem sec63PT_eq_closure_involutions {A P : Type} [Group A] [Group P] (ρ : A →* P)
    {S : Subgroup A} (hS : Disjoint S ρ.ker) {R : Subgroup P} (hSR : S.map ρ = R)
    (hR : R = closure {r : P | r ∈ R ∧ orderOf r = 2}) :
    S = closure {s : A | s ∈ S ∧ orderOf s = 2} := by
  let T : Set A := {s : A | s ∈ S ∧ orderOf s = 2}
  change S = closure T
  have hTS : closure T ≤ S := by
    rw [Subgroup.closure_le]
    intro x hx
    exact hx.1
  have hgen_sub : {r : P | r ∈ R ∧ orderOf r = 2} ⊆ ρ '' T := by
    rintro r ⟨hrR, hr2⟩
    have hr_map : r ∈ S.map ρ := hSR.symm ▸ hrR
    obtain ⟨s, hsS, hsρ⟩ := Subgroup.mem_map.mp hr_map
    refine ⟨s, ⟨hsS, ?_⟩, hsρ⟩
    have hss : s * s = 1 := by
      have hker : s * s ∈ ρ.ker := by
        rw [MonoidHom.mem_ker, map_mul, hsρ, ← pow_two, ← hr2, pow_orderOf_eq_one]
      exact Subgroup.disjoint_def.mp hS (S.mul_mem hsS hsS) hker
    have hs1 : s ≠ 1 := by
      intro h1
      have hr1 : r = 1 := by rw [← hsρ, h1, map_one]
      rw [hr1, orderOf_one] at hr2
      exact (by decide : (1 : ℕ) ≠ 2) hr2
    exact orderOf_eq_prime (by rw [pow_two]; exact hss) hs1
  have hRmap : (closure T).map ρ = R := by
    apply le_antisymm
    · calc (closure T).map ρ ≤ S.map ρ := Subgroup.map_mono hTS
        _ = R := hSR
    · rw [hR]
      calc closure {r : P | r ∈ R ∧ orderOf r = 2}
          ≤ closure (ρ '' T) := Subgroup.closure_mono hgen_sub
        _ = (closure T).map ρ := (MonoidHom.map_closure ρ T).symm
  apply le_antisymm
  · intro s hs
    have hρs : ρ s ∈ (closure T).map ρ := by
      rw [hRmap, ← hSR]
      exact Subgroup.mem_map_of_mem ρ hs
    obtain ⟨t, ht_cl, ht_eq⟩ := Subgroup.mem_map.mp hρs
    have hker : t⁻¹ * s ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ht_eq, inv_mul_cancel]
    have hmem : t⁻¹ * s ∈ S := S.mul_mem (S.inv_mem (hTS ht_cl)) hs
    have h1 : t⁻¹ * s = 1 := Subgroup.disjoint_def.mp hS hmem hker
    rw [inv_mul_eq_one] at h1
    rw [← h1]
    exact ht_cl
  · exact hTS

theorem sec63PT_exists_lift_gen {A P : Type} [Group A] [Finite A] [Group P] (ρ : A →* P)
    (hodd : Odd (Nat.card ρ.ker)) (H : Subgroup A) (R : Subgroup P) (hR2 : IsPGroup 2 R)
    (hRH : R ≤ H.map ρ) (hR8 : Nat.card R = 8)
    (hgen : R = closure {r : P | r ∈ R ∧ orderOf r = 2}) :
    ∃ S : Subgroup A, S ≤ H ∧ IsPGroup 2 S ∧ Nat.card S = 8 ∧
      S = closure {s : A | s ∈ S ∧ orderOf s = 2} := by
  obtain ⟨S, hSH, hS2, hSd, hSR⟩ := sec63PT_exists_pGroup_lift ρ hodd H R hR2 hRH
  exact ⟨S, hSH, hS2, by rw [← sec63PT_card_map_of_disjoint ρ hSd, hSR, hR8],
    sec63PT_eq_closure_involutions ρ hSd hSR hgen⟩

end CFSG.OddStandard.SmallF3.Omega

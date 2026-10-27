module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAAltPerm
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KNGen

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Equiv Equiv.Perm Subgroup CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

theorem kaAll_altGroup {n : ℕ} (hn5 : 5 ≤ n) (hn6 : n ≠ 6)
    {α : MulAut ↥(alternatingGroup (Fin n))} (hα2 : α * α = 1) : KAAll α := by
  intro p hp hp2 P hP
  obtain ⟨hPp, hP1, hcomm, hnorm⟩ := hP
  let c : Perm (Fin n) →* MulAut ↥(alternatingGroup (Fin n)) := MulAut.conjNormal
  have hbij : Function.Bijective c :=
    CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn5 hn6
  obtain ⟨y, hy⟩ := hbij.2 α
  have hy2 : y * y = 1 := hbij.1 (by rw [map_mul, hy, hα2, map_one])
  let P' : Subgroup (Perm (Fin n)) := P.comap c
  have hmap : P'.map c = P := Subgroup.map_comap_eq_self_of_surjective hbij.2 P
  have hP'p : IsPGroup p ↥P' := hPp.comap_of_injective c hbij.1
  have hP'1 : P' ≠ ⊥ := by
    intro h
    apply hP1
    rw [← hmap, h, Subgroup.map_bot]
  have hcomm' : ∀ e ∈ P', e * y = y * e := by
    intro e he
    apply hbij.1
    rw [map_mul, map_mul, hy]
    exact hcomm (c e) he
  have hD' : ∀ v : Perm (Fin n), Odd (orderOf v) → v * y = y * v →
      v ∈ normalizer (P' : Set (Perm (Fin n))) := by
    intro v hv hvy
    have hsign : Perm.sign v = 1 := KAAlt.sign_eq_one_of_odd' hv
    have hvA : v ∈ alternatingGroup (Fin n) := Equiv.Perm.mem_alternatingGroup.2 hsign
    have hfix : (⟨v, hvA⟩ : ↥(alternatingGroup (Fin n))) ∈ fixSub α := by
      rw [mem_fixSub, ← hy]
      apply Subtype.ext
      show y * v * y⁻¹ = v
      rw [← hvy]
      group
    have hodd : Odd (orderOf (⟨v, hvA⟩ : ↥(alternatingGroup (Fin n)))) := by
      rw [← Subgroup.orderOf_coe]
      exact hv
    have hN := hnorm _ hfix hodd
    have hcv : MulAut.conj (⟨v, hvA⟩ : ↥(alternatingGroup (Fin n))) = c v :=
      (MulAut.conjNormal_val (h := (⟨v, hvA⟩ : ↥(alternatingGroup (Fin n))))).symm
    rw [hcv, Subgroup.mem_normalizer_iff] at hN
    rw [Subgroup.mem_normalizer_iff]
    intro x
    show c x ∈ P ↔ c (v * x * v⁻¹) ∈ P
    rw [map_mul, map_mul, map_inv]
    exact hN _
  have hcyc' : IsCyclic ↥P' := KAAlt.alt_core2 hp hp2 hy2 hP'p hP'1 hcomm' hD'
  refine ⟨?_, ?_⟩
  · intro x
    obtain ⟨σ, rfl⟩ := hbij.2 x
    rw [← hy, ← map_commutatorElement]
    have h1 : Perm.sign ⁅σ, y⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.2 (mul_comm _ _)
    have hA : ⁅σ, y⁆ ∈ alternatingGroup (Fin n) := Equiv.Perm.mem_alternatingGroup.2 h1
    exact ⟨⟨⁅σ, y⁆, hA⟩, (MulAut.conjNormal_val (h := (⟨⁅σ, y⁆, hA⟩ :
      ↥(alternatingGroup (Fin n))))).symm⟩
  · let g : ↥P' →* ↥P := (c.comp P'.subtype).codRestrict P (fun x => x.2)
    have hg : Function.Surjective g := by
      rintro ⟨w, hw⟩
      obtain ⟨x, rfl⟩ := hbij.2 w
      exact ⟨⟨x, hw⟩, rfl⟩
    exact isCyclic_of_surjective g hg


theorem kay_Alt : KAY FAlt := by
  refine kay_of_kaAll fun Y _ _ hF _ α hα2 _ => ?_
  obtain ⟨n, hn7, hn11, ⟨e⟩⟩ := hF
  have hα'2 : MulAut.congr e α * MulAut.congr e α = 1 := by rw [← map_mul, hα2, map_one]
  have hK : KAAll (MulAut.congr e α) := kaAll_altGroup (by omega) (by omega) hα'2
  have h := KAAll.of_mulEquiv e.symm hK
  have key : MulAut.congr e.symm (MulAut.congr e α) = α := by
    ext y
    simp [MulAut.congr_apply]
  rwa [key] at h

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

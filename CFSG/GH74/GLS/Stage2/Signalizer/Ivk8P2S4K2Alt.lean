module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4K2AltPerm
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4K2Y

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K2

open Equiv Equiv.Perm Subgroup CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.KAAlt

theorem inner_alt7 {α : MulAut ↥(alternatingGroup (Fin 7))} (hα2 : α * α = 1) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup (MulAut ↥(alternatingGroup (Fin 7)))}
    (h : KAHyp α p P) : α ∈ innSub ↥(alternatingGroup (Fin 7)) := by
  obtain ⟨hPp, hP1, hcomm, hnorm⟩ := h
  let c : Perm (Fin 7) →* MulAut ↥(alternatingGroup (Fin 7)) := MulAut.conjNormal
  have hbij : Function.Bijective c :=
    CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
      (by norm_num)
  obtain ⟨y, hy⟩ := hbij.2 α
  have hy2 : y * y = 1 := hbij.1 (by rw [map_mul, hy, hα2, map_one])
  let P' : Subgroup (Perm (Fin 7)) := P.comap c
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
  have hD' : ∀ v : Perm (Fin 7), Odd (orderOf v) → v * y = y * v →
      v ∈ normalizer (P' : Set (Perm (Fin 7))) := by
    intro v hv hvy
    have hsign : Perm.sign v = 1 := sign_eq_one_of_odd' hv
    have hvA : v ∈ alternatingGroup (Fin 7) := Equiv.Perm.mem_alternatingGroup.2 hsign
    have hfix : (⟨v, hvA⟩ : ↥(alternatingGroup (Fin 7))) ∈ fixSub α := by
      rw [mem_fixSub, ← hy]
      apply Subtype.ext
      show y * v * y⁻¹ = v
      rw [← hvy]
      group
    have hodd : Odd (orderOf (⟨v, hvA⟩ : ↥(alternatingGroup (Fin 7)))) := by
      rw [← Subgroup.orderOf_coe]
      exact hv
    have hN := hnorm _ hfix hodd
    have hcv : MulAut.conj (⟨v, hvA⟩ : ↥(alternatingGroup (Fin 7))) = c v :=
      (MulAut.conjNormal_val (h := (⟨v, hvA⟩ : ↥(alternatingGroup (Fin 7))))).symm
    rw [hcv, Subgroup.mem_normalizer_iff] at hN
    rw [Subgroup.mem_normalizer_iff]
    intro x
    show c x ∈ P ↔ c (v * x * v⁻¹) ∈ P
    rw [map_mul, map_mul, map_inv]
    exact hN _
  have hsign : Perm.sign y = 1 :=
    sign_eq_one_of_seven (by simp) hp hp2 hy2 hP'p hP'1 hcomm' hD'
  have hyA : y ∈ alternatingGroup (Fin 7) := Equiv.Perm.mem_alternatingGroup.2 hsign
  refine ⟨⟨y, hyA⟩, ?_⟩
  rw [← hy]
  exact (MulAut.conjNormal_val (h := (⟨y, hyA⟩ : ↥(alternatingGroup (Fin 7))))).symm

theorem kaTwoY_alt7 : KATwoY ↥(alternatingGroup (Fin 7)) := by
  intro α β hα2 _ hβ2 _ p hp hp2 P Q hP hQ
  exact (innSub _).mul_mem (inner_alt7 hα2 hp hp2 hP) (inner_alt7 hβ2 hp hp2 hQ)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K2

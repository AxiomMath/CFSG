module

public import CFSG.GF2Type.Smith1979.CaseIIAssemblyDefs
public import CFSG.GF2Type.Smith1979.CaseIIDAlt
public import CFSG.GF2Type.Smith1979.CaseIIDOne
public import CFSG.GF2Type.Smith1979.CaseIIDSp
public import CFSG.GF2Type.Smith1979.CaseIIExclJ2
public import CFSG.GF2Type.Smith1979.CaseIIExclL34
public import CFSG.GF2Type.Smith1979.CaseIIExclL52

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.Case2

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.Open CFSG.ComponentClassification
  CFSG.Blueprint
open CFSG.Assembly (InCatalog KProper)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

section Embedding

variable {X R : Type} [Group X] [Group R]

theorem not_critII_carrier_J2 :
    ¬ CritII (NativeSporadic.Carrier .J2) :=
  not_outer_involution_1344_nativeJ2

theorem false_of_psl34_of_embedding
    (hX : StatedClassicalModel X .PSL 3 2 2) (j : R →* X) (hj : Function.Injective j) {x : R}
    (hx : orderOf x = 6) : False :=
  orderOf_ne_six_of_psl34 hX (j x) (by rw [orderOf_injective j hj, hx])

theorem false_of_psl52_of_embedding (hX : StatedClassicalModel X .PSL 5 2 1) (σ : MulAut X)
    (hσ : σ * σ = 1) (j : R →* X) (hj : Function.Injective j)
    (hfix : ∀ x, σ x = x ↔ x ∈ j.range) {y : R} (hy : orderOf y = 7)
    (hC : ∀ x : R, x * y = y * x → x ∈ Subgroup.zpowers y) : False := by
  refine false_of_psl52_fix_seven hX σ hσ (y := j y) (by rw [orderOf_injective j hj, hy])
    ((hfix _).mpr ⟨y, rfl⟩) ?_
  intro x hx hxy
  obtain ⟨r, hrx⟩ := (hfix x).mp hx
  have h1 : j r * j y = j y * j r := by rw [hrx]; exact hxy
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hC r (hj (by rw [map_mul, map_mul]; exact h1)))
  rw [← hrx, ← hk, map_zpow]
  exact Subgroup.zpow_mem_zpowers _ k

theorem false_of_psu43_of_embedding (hU : U43Frob56Free) (hX : StatedClassicalModel X .PSU 4 3 1)
    (j : R →* X) (hj : Function.Injective j) {y : R} (hy : orderOf y = 7) (A : Subgroup R)
    (hA2 : ∀ a ∈ A, a * a = 1) (hA8 : Nat.card A = 8) (hAy : ∀ a ∈ A, y * a * y⁻¹ ∈ A)
    (hAf : ∀ a ∈ A, y * a * y⁻¹ = a → a = 1) : False := by
  refine hU hX (y := j y) (by rw [orderOf_injective j hj, hy]) (A.map j) ?_ ?_ ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, hA2 a ha, map_one]
  · rw [Subgroup.card_map_of_injective hj]
    exact hA8
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨y * a * y⁻¹, hAy a ha, by rw [map_mul, map_mul, map_inv]⟩
  · rintro _ ⟨a, ha, rfl⟩ hfp
    have h1 : j (y * a * y⁻¹) = j a := by
      rw [map_mul, map_mul, map_inv]
      exact hfp
    rw [hAf a ha (hj h1), map_one]

end Embedding

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

namespace Data

theorem isSporadic_M22_of_filter
    (D : Data S g t) (hCE : S4.CentralExtInput.{0})
    (hS : SchreierFor InCatalog) (hK : KProper InCatalog G) (hM : S.M ≠ ⊤)
    (hq : CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar))
    (hodd : Nat.card (timmesfeldOddCore S.Mbar) ∣ 3) (hU : U43Frob56Free) (hR : RderFacts)
    (hfilter :
      (∃ n : ℕ, 8 ≤ n ∧ n ≤ 12 ∧
          Nonempty (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar) ≃*
            alternatingGroup (Fin n))) ∨
        StatedClassicalModel (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar))
          .PSL 3 2 2 ∨
        StatedClassicalModel (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar))
          .PSL 5 2 1 ∨
        StatedClassicalModel (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar))
          .PSp 3 2 1 ∨
        StatedClassicalModel (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar))
          .PSU 4 3 1 ∨
        Nonempty (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar) ≃*
          NativeSporadic.Carrier .J2) ∨
        Nonempty (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar) ≃*
          NativeSporadic.Carrier .M22)) :
    NativeSporadic.IsSporadic (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) .M22 := by
  obtain ⟨σ, hσ2, -, -, j, hj, hfix, -⟩ := critII_X_strong D hCE hS hK hM hq hodd
  have hcrit := (critII_X D hCE hS hK hM hq hodd).1
  obtain ⟨-, -, -, -, -, -, -, -, -, h10, -, -, h13⟩ := Rbar_structure_II D hCE
  obtain ⟨⟨y, hyR, hy7, hyfpf, hyC⟩, ⟨x6, hx6R, hx6⟩, hnorm⟩ := hR D hCE
  have hy7' : orderOf (⟨y, hyR⟩ : Rder S g t) = 7 := by rw [Subgroup.orderOf_mk, hy7]
  rcases hfilter with ⟨n, h8, h12, ⟨e⟩⟩ | hL34 | hL52 | hSp | hU43 | ⟨⟨e⟩⟩ | hM22
  · exact (not_critII_alternating h8 h12 (hcrit.of_mulEquiv e)).elim
  · exact (false_of_psl34_of_embedding hL34 j hj (x := ⟨x6, hx6R⟩)
      (by rw [Subgroup.orderOf_mk, hx6])).elim
  · refine (false_of_psl52_of_embedding hL52 σ hσ2 j hj hfix hy7' ?_).elim
    intro x hx
    have hx' := hyC x x.2 (congrArg Subtype.val hx)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx'
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
    simpa using hk
  · exact (not_critII_sp62 hSp hcrit).elim
  · let A : Subgroup (Rder S g t) := (Rder S g t ⊓ Nbar S g t).subgroupOf (Rder S g t)
    have hA : ∀ a : Rder S g t, a ∈ A ↔ (a : S.O) ∈ Rder S g t ⊓ Nbar S g t := fun a =>
      Subgroup.mem_subgroupOf
    refine (false_of_psu43_of_embedding hU hU43 j hj hy7' A ?_ ?_ ?_ ?_).elim
    · intro a ha
      exact Subtype.ext (h13 a (((hA a).mp ha).2))
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : Rder S g t ⊓ Nbar S g t ≤ Rder S g t)).toEquiv]
      exact h10
    · intro a ha
      exact (hA _).mpr (hnorm y hyR a ((hA a).mp ha))
    · intro a ha hfp
      exact Subtype.ext (hyfpf a ((hA a).mp ha) (congrArg Subtype.val hfp))
  · exact (not_critII_carrier_J2 (hcrit.of_mulEquiv e)).elim
  · exact hM22

end Data

end CFSG.GF2Type.Smith1979.Case2

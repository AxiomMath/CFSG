module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CBCard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CBModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CBSwap
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CDMain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Statements

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma58b_of (hS : Asc82SchurU43) (h57 : Asc82Lemma57) (hF : Asc82Fact58Swap) :
    Asc82Lemma58b := by
  intro G _ _ t L S z r B A hR B' hB'A hB'inv
  obtain ⟨φ, hφ, hφt, -, -, -, -, -⟩ := asc82Lemma58d_of hS G t L S z r B A hR
  have hinv : ∀ h ∈ L ⊓ normalizer (A : Set G), ∀ b ∈ B', h * b * h⁻¹ ∈ B' :=
    fun h hh b hb => hB'inv h (Subgroup.mem_inf.mp hh).2 b hb
  by_cases hv : ∃ v : Fin 6 → ZMod 2, v ≠ 0 ∧ φ v ∈ B'
  swap
  · left
    exact sec5cb_eq_bot hφ hB'A fun v hv' => by_contra fun hne => hv ⟨v, hne, hv'⟩
  right
  obtain ⟨v, hv0, hvB'⟩ := hv
  have htB' : t ∈ B' := hφt ▸ sec5cb_ones_mem hφ hinv hv0 hvB'
  obtain ⟨g, hg, α, hα⟩ := hF G t L S z r B A hR
  have hA : A = zpowers r ⊔ B := hR.A_eq
  have ht2 : orderOf t = 2 := hR.involution
  have htt : t * t = 1 := by rw [← pow_two, ← ht2]; exact pow_orderOf_eq_one t
  have hr2 : orderOf r = 2 := by rw [← hg, orderOf_conjugate_eq]; exact ht2
  have hOm : IsOm6Z2 L := hR.toSec5Ctx.toSec5Setting.isOm6Z2
  have htB : t ∈ B := hR.B_split.1
  have hBL : B ≤ L := fun b hb => (Subgroup.mem_inf.mp (hR.B_le hb)).1
  have htL : t ∈ L := hBL htB
  have htc : t ∈ centerIn L := sec5_mem_centerIn_iff.mpr ⟨htL, fun y hy =>
    Subgroup.mem_centralizer_iff.mp (hR.component.1 hy) t (Set.mem_singleton t)⟩
  have hgrg : g * r * g⁻¹ = t := by rw [← hg]; group
  have hrL' : r ∈ CFSG.conjugate L g := (mem_conjugate_iff L g r).mpr (by rw [hgrg]; exact htL)
  have hrc : r ∈ centerIn (CFSG.conjugate L g) := by
    refine sec5_mem_centerIn_iff.mpr ⟨hrL', fun y hy => ?_⟩
    have hy' : g * y * g⁻¹ ∈ L := (mem_conjugate_iff L g y).mp hy
    have hc := (sec5_mem_centerIn_iff.mp htc).2 _ hy'
    calc r * y = g⁻¹ * (t * (g * y * g⁻¹)) * g := by rw [← hg]; group
      _ = g⁻¹ * ((g * y * g⁻¹) * t) * g := by rw [hc]
      _ = y * r := by rw [← hg]; group
  have hrA : r ∈ A := by rw [hA]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers r)
  have htA : t ∈ A := by rw [hA]; exact Subgroup.mem_sup_right htB
  have htnot : t ∉ CFSG.conjugate L g := by
    obtain ⟨V, _, _, _, Q, hQ, e, x, hdim, hsgn, hx, hxt⟩ := hα
    exact sec5c_r_not_mem hdim hx hxt
  obtain ⟨hcommA, hsqA⟩ := sec5cb_perm_comm_sq hφ
  have h57' : A = (A ⊓ CFSG.conjugate L g) ⊔ zpowers t := (h57 G t L S z r B A hR).2 g hg
  have hcard : Nat.card ↥(A ⊓ CFSG.conjugate L g) = 2 ^ 5 := by
    have h := sec5cb_card_eq_two_mul htt hcommA inf_le_left htA
      (fun h => htnot (Subgroup.mem_inf.mp h).2) h57'
    rw [sec5cb_perm_card hφ] at h
    omega
  have hE : IsElemAb2 (A ⊓ CFSG.conjugate L g) 5 :=
    ⟨⟨IsMulCommutative.of_comm fun a b => Subtype.ext
        (hcommA _ (Subgroup.mem_inf.mp a.2).1 _ (Subgroup.mem_inf.mp b.2).1),
      fun x hx => by rw [pow_two]; exact hsqA x (Subgroup.mem_inf.mp hx).1⟩, hcard⟩
  obtain ⟨φ', hφ', -, j, hφ'j⟩ := sec5cb_permModule_of hS (isOm6Z2_conjugate hOm g) hr2 hrc
    (Subgroup.mem_inf.mpr ⟨hrA, hrL'⟩) inf_le_right hE
    (fun b hb => hcommA t htA b (Subgroup.mem_inf.mp hb).1) htt ⟨α, hα⟩
  have hAeq : zpowers t ⊔ (A ⊓ CFSG.conjugate L g) = A := by rw [sup_comm]; exact h57'.symm
  rw [hAeq] at hφ'
  have hinv' : ∀ h ∈ CFSG.conjugate L g ⊓ normalizer (A : Set G), ∀ b ∈ B', h * b * h⁻¹ ∈ B' :=
    fun h hh b hb => hB'inv h (Subgroup.mem_inf.mp hh).2 b hb
  exact le_antisymm hB'A (sec5cb_le_of_single hφ' hinv' (hφ'j ▸ htB'))

end CFSG.OddStandard.SmallF3.Omega

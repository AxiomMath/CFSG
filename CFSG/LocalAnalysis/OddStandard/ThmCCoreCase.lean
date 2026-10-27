module

public import CFSG.LocalAnalysis.OddStandard.ThmCCoreLev
public import CFSG.LocalAnalysis.OddStandard.ThmCO2Defs
public import CFSG.GroupTheory.ThompsonIndexTwo
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.OddStandard.ThmCCoreAlp
public import CFSG.LocalAnalysis.OddStandard.ThmCCoreStep

public section

namespace CFSG.OddStandard.ThmC.Core

open CFSG Subgroup CFSG.OddStandard.ThmC CFSG.OddStandard.ThmC.T CFSG.RankTwoShapes
open CFSG.GH74.GLS.Bg.TwoGroups

section Cases

variable {X : Type} [Group X] [Finite X] {T : Sylow 2 X} {Z A B L : Subgroup X} [L.Normal]

theorem not_frob (hS2 : O2Structure) (hT : IsT (T : Subgroup X))
    (hTA : TAmbient (T : Subgroup X) Z A B) (hZD : Z ≤ (T : Subgroup X) ⊓ L)
    (hAD : ¬ A ≤ (T : Subgroup X) ⊓ L) (hBD : ¬ B ≤ (T : Subgroup X) ⊓ L)
    [Group.IsPerfect L] (heven : 2 ∣ Nat.card L) : False := by
  obtain ⟨N, hNn, hNcop, k, hk⟩ := exists_normalComplement_of_alperin (sylowInfL T L) (by
    intro Q' hQ' x hx hodd
    obtain ⟨hQD, hZQ⟩ := alperin_img hTA hZD hQ'
    apply mem_centralizer_of_img
    exact frob_step hS2 hT hTA hZQ hQD hAD hBD x.2 (mem_nzr_img hx)
      (by rwa [Subgroup.orderOf_coe]))
  have : N.Normal := hNn
  have hq : IsPGroup 2 (L ⧸ N) := IsPGroup.of_card (n := k) hk
  have hNtop : N = ⊤ := eq_top_of_pGroup_quotient hq
  rw [hNtop, Subgroup.card_top] at hNcop
  exact absurd (Nat.Coprime.eq_one_of_dvd hNcop.symm heven) (by norm_num)

theorem not_u1 (hS2 : O2Structure) (hT : IsT (T : Subgroup X))
    (hTA : TAmbient (T : Subgroup X) Z A B) (hZD : Z ≤ (T : Subgroup X) ⊓ L)
    (hAD : A ≤ (T : Subgroup X) ⊓ L) (hBD : ¬ B ≤ (T : Subgroup X) ⊓ L)
    (hAne : A ≠ (T : Subgroup X) ⊓ L) [Group.IsPerfect L] : False := by
  set D : Subgroup X := (T : Subgroup X) ⊓ L with hD
  have hDT : D ≤ (T : Subgroup X) := inf_le_left
  obtain ⟨u, huD, huB, huA⟩ : ∃ u ∈ D, u ∈ B ∧ u ∉ A := by
    obtain ⟨d, hdD, hdA⟩ : ∃ d ∈ D, d ∉ A := by
      by_contra hall
      exact hAne (le_antisymm hAD fun d hd => by_contra fun h => hall ⟨d, hd, h⟩)
    obtain ⟨a, ha, b, hb, hdab⟩ := exists_mul_A_B hT hTA d hdD.1
    refine ⟨b, ?_, hb, fun hbA => hdA ?_⟩
    · have : b = a⁻¹ * d := by rw [hdab]; group
      rw [this]
      exact D.mul_mem (D.inv_mem (hAD ha)) hdD
    · rw [hdab]
      exact A.mul_mem ha hbA
  have hDcard : Nat.card D = 32 := by
    have hd1 : Nat.card D ∣ 64 := hTA.card_S ▸ Subgroup.card_dvd_of_le hDT
    have hd2 : 16 ∣ Nat.card D := hTA.card_A ▸ Subgroup.card_dvd_of_le hAD
    have hD16 : Nat.card D ≠ 16 := fun h =>
      hAne (Subgroup.eq_of_le_of_card_ge hAD (by rw [h, hTA.card_A]))
    have hD64 : Nat.card D ≠ 64 := fun h => by
      have hDeq : D = (T : Subgroup X) :=
        Subgroup.eq_of_le_of_card_ge hDT (by rw [h, hTA.card_S])
      exact hBD (hTA.B_le_S.trans (le_of_eq hDeq.symm))
    have hpos : 0 < Nat.card D := Nat.card_pos
    obtain ⟨m, hm⟩ := hd2
    have hle : Nat.card D ≤ 64 := Nat.le_of_dvd (by norm_num) hd1
    have hm4 : m ≤ 4 := by omega
    interval_cases m
    · omega
    · exact absurd (by omega) hD16
    · omega
    · rw [hm] at hd1
      norm_num at hd1
    · exact absurd (by omega) hD64
  set S' : Sylow 2 L := sylowInfL T L with hS'
  set U' : Subgroup L := A.subgroupOf L with hU'
  have hU'S' : U' ≤ (S' : Subgroup L) := fun a ha =>
    (mem_sylowInfL T L a).2 (hAD (Subgroup.mem_subgroupOf.1 ha)).1
  have hrel : U'.relIndex (S' : Subgroup L) = 2 := by
    have h1 : (S' : Subgroup L) = D.subgroupOf L := by
      rw [hS', sylowInfL, CFSG.QuasiDihedralFusion.sylowInfNormal_coe,
        ← Subgroup.inf_subgroupOf_right]
    rw [h1, hU', Subgroup.relIndex_subgroupOf inf_le_right]
    have := Subgroup.relIndex_mul_card (H := A) (K := D)
    rw [inf_eq_left.2 hAD, hTA.card_A, hDcard] at this
    show A.relIndex D = 2
    omega
  set x : L := ⟨u, huD.2⟩ with hx
  have hxT : x ∈ (S' : Subgroup L) := (mem_sylowInfL T L x).2 huD.1
  have hxU : x ∉ U' := fun h => huA (Subgroup.mem_subgroupOf.1 h)
  have hx1 : x ≠ 1 := fun h => hxU (h ▸ U'.one_mem)
  have hx2 : x ^ 2 = 1 := by
    rw [sq]
    exact Subtype.ext (hTA.B_sq u huB)
  have hxord : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  have hmin : ∀ y ∈ (S' : Subgroup L), y ∉ U' → orderOf x ≤ orderOf y := by
    intro y _ hyU
    have hy1 : y ≠ 1 := fun h => hyU (h ▸ U'.one_mem)
    have hpos : 0 < orderOf y := orderOf_pos y
    have hne : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.1 h)
    rw [hxord]
    omega
  let W : Set L := {w | (w : X) ∈ D ∧ (w : X) ∉ A}
  have hW : ∀ Q' : Subgroup L, IsAlperinSubgroup 2 (S' : Subgroup L) Q' → ∀ w ∈ W, w ∈ Q' →
      ∀ n ∈ normalizer (Q' : Set L), n⁻¹ * w * n ∈ W := by
    intro Q' hQ' w hw hwQ n hn
    obtain ⟨hQD, hZQ⟩ := alperin_img hTA hZD hQ'
    exact u1_step hS2 hT hTA hZQ hQD hAD hBD (mem_img.2 hwQ) hw.2 (mem_nzr_img hn)
  have hconj : ∀ g : L, g⁻¹ * x * g ∉ U' := by
    intro g hg
    have hxW : x ∈ W := ⟨huD, huA⟩
    have := track_alperin S' W hW hxT hxW (hU'S' hg)
    exact this.2 (Subgroup.mem_subgroupOf.1 hg)
  obtain ⟨N, hNn, hNidx⟩ := CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson
    S'.isPGroup' S'.not_dvd_index hU'S' hrel hxT hxU hmin hconj
  have hq : IsPGroup 2 (L ⧸ N) := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hNidx)
  have hNtop : N = ⊤ := eq_top_of_pGroup_quotient hq
  rw [hNtop, Subgroup.index_top] at hNidx
  exact absurd hNidx (by norm_num)

theorem not_abel (hS2 : O2Structure) (hGor : CFSG.OddStandard.ThmC.O2.Gor42)
    (hT : IsT (T : Subgroup X)) (hTA : TAmbient (T : Subgroup X) Z A B)
    (hAD : A = (T : Subgroup X) ⊓ L) [Group.IsPerfect L] (heven : 2 ∣ Nat.card L)
    (hO : pPrimeCore 2 L = ⊥) : False := by
  set S' : Sylow 2 L := sylowInfL T L with hS'
  have hAL : A ≤ L := hAD ▸ inf_le_right
  have hmem : ∀ r : L, r ∈ (S' : Subgroup L) ↔ (r : X) ∈ A := fun r => by
    rw [hS', mem_sylowInfL, hAD]
    exact ⟨fun h => ⟨h, r.2⟩, fun h => h.1⟩
  have hR : (S' : Subgroup L).Normal := by
    refine hGor L hO S' ?_ ?_ ?_ ?_
    · rw [hS', card_sylowInfL, ← hAD, hTA.card_A]
    · intro r hr
      exact Subtype.ext (hTA.A_sq r ((hmem r).1 hr))
    · intro r hr s hs
      exact Subtype.ext (hTA.A_abel r ((hmem r).1 hr) s ((hmem s).1 hs))
    · intro g hg
      have hgN : (g : X) ∈ nzr A := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · intro hx
          have := (Subgroup.mem_normalizer_iff.1 hg ⟨x, hAL hx⟩).1 ((hmem _).2 hx)
          exact (hmem _).1 this
        · intro hx
          have hxL : x ∈ L := by
            have h1 : (g : X) * x * (g : X)⁻¹ ∈ L := hAL hx
            have : x = (g : X)⁻¹ * ((g : X) * x * (g : X)⁻¹) * g := by group
            rw [this]
            exact L.mul_mem (L.mul_mem (L.inv_mem g.2) h1) g.2
          have := (Subgroup.mem_normalizer_iff.1 hg ⟨x, hxL⟩).2 ((hmem _).2 hx)
          exact (hmem _).1 this
      rcases abel_step hS2 hT hTA hAD g.2 hgN with h | ⟨h1, h3⟩
      · left
        intro r hr
        exact Subtype.ext (h r ((hmem r).1 hr))
      · right
        refine ⟨fun r hr hgr => ?_, fun r hr => ?_⟩
        · exact Subtype.ext (h1 r ((hmem r).1 hr) (congrArg Subtype.val hgr))
        · exact Subtype.ext (h3 r ((hmem r).1 hr))
  have hodd : Odd (Nat.card (L ⧸ (S' : Subgroup L))) := by
    have : ¬ 2 ∣ (S' : Subgroup L).index := S'.not_dvd_index
    show Odd (S' : Subgroup L).index
    exact Nat.odd_iff.2 (by omega)
  have hsolv : Group.IsSolvable (L ⧸ (S' : Subgroup L)) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have htop : (S' : Subgroup L) = ⊤ := eq_top_of_solvable_quotient hsolv
  obtain ⟨n, hn⟩ := S'.isPGroup'.exists_card_eq
  have hL2 : IsPGroup 2 L := IsPGroup.of_card (n := n) (by
    rw [← hn, htop, Subgroup.card_top])
  have : Group.IsNilpotent L := hL2.isNilpotent
  have : Nontrivial L := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have h1 : Nat.card L = 1 := Nat.card_unique
    omega
  exact Group.IsPerfect.not_isSolvable L inferInstance

end Cases

end CFSG.OddStandard.ThmC.Core

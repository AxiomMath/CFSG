module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.Vacuous
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.Inner

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open Subgroup TauCeti
open CFSG.RankThree.PartOne.Planes (card_sup_zpowers)

section Generic

variable {X : Type} [Group X] [Finite X]

theorem three_le_of_E9 {A : Subgroup X} (hA : IsElemAbelian 3 A) (hA9 : Nat.card A = 9) {x : X}
    (hx3 : x ^ 3 = 1) (hxA : x ∉ A) (hcomm : ∀ a ∈ A, a * x = x * a) :
    3 ≤ CFSG.Open.pRank 3 (centralizer ({x} : Set X)) := by
  have hZ : IsElemAbelian 3 (zpowers x) := by
    rw [Subgroup.zpowers_eq_closure]
    refine IsElemAbelian.closure_of_commute (fun a ha b hb => ?_) (fun a ha => ?_)
    · rw [Set.mem_singleton_iff] at ha hb
      rw [ha, hb]
    · rw [Set.mem_singleton_iff] at ha
      rw [ha, hx3]
  have hcomm' : ∀ a ∈ A, ∀ b ∈ zpowers x, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact ((Commute.zpow_right (hcomm a ha) k)).eq
  have hV : IsElemAbelian 3 (A ⊔ zpowers x) := hA.sup_of_commute hZ hcomm'
  have hV27 : Nat.card ↥(A ⊔ zpowers x) = 3 ^ 3 := by
    rw [card_sup_zpowers Nat.prime_three A hx3 hxA hcomm, hA9]; norm_num
  have hle : A ⊔ zpowers x ≤ centralizer ({x} : Set X) := by
    refine sup_le (fun a ha => ?_) (Subgroup.zpowers_le.2 ?_)
    · exact mem_centralizer_singleton_iff.2 (hcomm a ha)
    · exact mem_centralizer_singleton_iff.2 rfl
  exact CFSG.SectionRank.le_pRank (by norm_num) hle hV hV27

theorem mem_of_conjNormal_mem_range {L : Subgroup X} [L.Normal]
    (hC : centralizer (L : Set X) = ⊥) {g : X}
    (hg : (MulAut.conjNormal g : MulAut ↥L) ∈ (MulAut.conj : ↥L →* MulAut ↥L).range) : g ∈ L := by
  obtain ⟨l, hl⟩ := hg
  have hc : (l : X)⁻¹ * g ∈ centralizer (L : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := congrArg (fun α : MulAut ↥L => ((α ⟨y, hy⟩ : ↥L) : X)) hl
    simp only [MulAut.conjNormal_apply, MulAut.conj_apply] at h1
    change (l : X) * y * (l : X)⁻¹ = g * y * g⁻¹ at h1
    calc y * ((l : X)⁻¹ * g) = (l : X)⁻¹ * ((l : X) * y * (l : X)⁻¹) * g := by group
      _ = (l : X)⁻¹ * (g * y * g⁻¹) * g := by rw [h1]
      _ = (l : X)⁻¹ * g * y := by group
  rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hc
  rw [← hc]
  exact l.2

theorem three_le_of_outer_fixed {L : Subgroup X} [L.Normal]
    (hC : centralizer (L : Set X) = ⊥)
    (hfix : ∀ α : MulAut ↥L, α ^ 3 = 1 → α ∉ (MulAut.conj : ↥L →* MulAut ↥L).range →
      ∃ E : Subgroup ↥L, IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ ∀ e ∈ E, α e = e)
    {x : X} (hx : orderOf x = 3) (hxL : x ∉ L) :
    3 ≤ CFSG.Open.pRank 3 (centralizer ({x} : Set X)) := by
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hα3 : (MulAut.conjNormal x : MulAut ↥L) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hαo : (MulAut.conjNormal x : MulAut ↥L) ∉ (MulAut.conj : ↥L →* MulAut ↥L).range :=
    fun h => hxL (mem_of_conjNormal_mem_range hC h)
  obtain ⟨E, hE, hE9, hEfix⟩ := hfix _ hα3 hαo
  set A : Subgroup X := E.map L.subtype with hAdef
  have hA : IsElemAbelian 3 A := CFSG.SectionRank.isElemAbelian_map hE _
  have hA9 : Nat.card A = 9 := by
    rw [hAdef, Subgroup.card_map_of_injective L.subtype_injective, hE9]
  have hxA : x ∉ A := by
    rintro ⟨e, -, rfl⟩
    exact hxL e.2
  refine three_le_of_E9 hA hA9 hx3 hxA ?_
  rintro _ ⟨e, he, rfl⟩
  have h1 := congrArg Subtype.val (hEfix e he)
  simp only [MulAut.conjNormal_apply] at h1
  change x * (e : X) * x⁻¹ = (e : X) at h1
  calc (e : X) * x = x * (e : X) * x⁻¹ * x := by rw [h1]
    _ = x * (e : X) := by group

theorem exists_outer_of_noE27 {L : Subgroup X} (hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3)
    (hL : ∀ E : Subgroup ↥L, IsElemAbelian 3 E → Nat.card E ≠ 27) :
    ∃ y : X, orderOf y = 3 ∧ y ∉ L := by
  obtain ⟨E, hE, hE27⟩ := exists_elemAbelian_27 hX
  by_contra hcon
  push Not at hcon
  have hEL : E ≤ L := by
    intro g hg
    by_cases hg1 : g = 1
    · rw [hg1]; exact L.one_mem
    · exact hcon g (orderOf_eq_prime (hE.2 g hg) hg1)
  refine hL (E.subgroupOf L) ?_ ?_
  · refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun a ha => Subtype.ext (hE.2 _ ha)⟩
    show ((a : ↥L) : X) * ((b : ↥L) : X) = ((b : ↥L) : X) * ((a : ↥L) : X)
    exact hE.comm a.2 b.2
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv, hE27]

theorem three_le_of_inner_fusion {L : Subgroup X} [L.Normal] {x y : X} (hxL : x ∈ L)
    (hy : orderOf y = 3) (hyL : y ∉ L) {g : ↥L} {E : Subgroup ↥L} (hE : IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9) (hgx : g * ⟨x, hxL⟩ * g⁻¹ ∈ E)
    (hEfix : ∀ e ∈ E, (MulAut.conjNormal y : MulAut ↥L) e = e) :
    3 ≤ CFSG.Open.pRank 3 (centralizer ({x} : Set X)) := by
  have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  set A : Subgroup X := E.map L.subtype with hAdef
  have hA : IsElemAbelian 3 A := CFSG.SectionRank.isElemAbelian_map hE _
  have hA9 : Nat.card A = 9 := by
    rw [hAdef, Subgroup.card_map_of_injective L.subtype_injective, hE9]
  have hyA : y ∉ A := by
    rintro ⟨e, -, rfl⟩
    exact hyL e.2
  have hcomm : ∀ a ∈ A, a * y = y * a := by
    rintro _ ⟨e, he, rfl⟩
    have h1 := congrArg Subtype.val (hEfix e he)
    simp only [MulAut.conjNormal_apply] at h1
    change y * (e : X) * y⁻¹ = (e : X) at h1
    calc (e : X) * y = y * (e : X) * y⁻¹ * y := by rw [h1]
      _ = y * (e : X) := by group
  set x' : X := (g : X) * x * (g : X)⁻¹ with hx'
  have hx'A : x' ∈ A := ⟨_, hgx, rfl⟩
  have hZ : IsElemAbelian 3 (zpowers y) := by
    rw [Subgroup.zpowers_eq_closure]
    refine IsElemAbelian.closure_of_commute (fun a ha b hb => ?_) (fun a ha => ?_)
    · rw [Set.mem_singleton_iff] at ha hb
      rw [ha, hb]
    · rw [Set.mem_singleton_iff] at ha
      rw [ha, hy3]
  have hcomm' : ∀ a ∈ A, ∀ b ∈ zpowers y, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact ((Commute.zpow_right (hcomm a ha) k)).eq
  have hV : IsElemAbelian 3 (A ⊔ zpowers y) := hA.sup_of_commute hZ hcomm'
  have hV27 : Nat.card ↥(A ⊔ zpowers y) = 3 ^ 3 := by
    rw [card_sup_zpowers Nat.prime_three A hy3 hyA hcomm, hA9]; norm_num
  have hle : A ⊔ zpowers y ≤ centralizer ({x'} : Set X) := fun f hf =>
    mem_centralizer_singleton_iff.2 (hV.comm hf (le_sup_left (b := zpowers y) hx'A))
  have hk : 3 ≤ CFSG.Open.pRank 3 (centralizer ({x'} : Set X)) :=
    CFSG.SectionRank.le_pRank (by norm_num) hle hV hV27
  have hconj := le_pRank_centralizer_of_mulEquiv (MulAut.conj (g : X)) x
  simp only [MulAut.conj_apply] at hconj
  exact hk.trans hconj

theorem centRankAt_of_parts {d : ValidLieTypeIndex}
    (hin : ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), L.Normal → IsSimpleGroup ↥L →
      (∃ a b : ↥L, a * b ≠ b * a) → Nonempty (↥L ≃* (CFSGIndex.lie d).Group) →
      centralizer (L : Set X) = ⊥ → CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3 →
      ∀ x : X, orderOf x = 3 → x ∈ L → 3 ≤ CFSG.Open.pRank 3 (centralizer ({x} : Set X)))
    (hout : ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* (CFSGIndex.lie d).Group) →
      ∀ α : MulAut K, α ^ 3 = 1 → α ∉ (MulAut.conj : K →* MulAut K).range →
        ∃ E : Subgroup K, IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ ∀ e ∈ E, α e = e) :
    CentRankAt d := by
  intro X _ _ L hLn hs hnab he hC hX x hx
  by_cases hxL : x ∈ L
  · exact hin X L hLn hs hnab he hC hX x hx hxL
  · haveI := hLn
    exact three_le_of_outer_fixed hC (hout ↥L he) hx hxL

end Generic

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

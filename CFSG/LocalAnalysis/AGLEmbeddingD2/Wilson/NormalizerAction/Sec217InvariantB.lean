module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.Sec217Invariant
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3FrameCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.PerfCoreMap

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

section Main


set_option linter.unusedSectionVars false

set_option maxRecDepth 20000 in
theorem Cover217.B_eq_F₁ {A E U : Subgroup G} {c : G} {L : Subgroup G}
    (h : Cover217 A E U c L) (hθ : aschbacherSolvableCore 3 L = ⊥) (hAL : A ≤ L) {a : G}
    (ha : Valid217 A c L a) :
    ∃ F₁ : Subgroup ↥L, F₁ ≤ A.subgroupOf L ∧ Nat.card F₁ = 27 ∧
      (∀ y ∈ Subgroup.normalizer ((A.subgroupOf L : Subgroup ↥L) : Set ↥L), ∀ s ∈ F₁,
        y * s * y⁻¹ ∈ F₁) ∧
      (A ⊓ iCore L a) ⊔ Subgroup.zpowers c = F₁.map L.subtype := by
  obtain ⟨hq, hZ3⟩ := h.quasi_card_center hθ
  obtain ⟨e⟩ := h.quot
  have hab := h.isElemAbelian_A
  haveI : IsMulCommutative A := hab.1
  set F : Subgroup ↥L := A.subgroupOf L with hF
  have hFmap : F.map L.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAL
  have hF81 : Nat.card F = 81 := by
    rw [hF, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, h.card]
    norm_num
  have hZF : Subgroup.center ↥L ≤ F := by
    rw [h.center_eq hθ, Subgroup.zpowers_le]
    exact Subgroup.mem_subgroupOf.2 h.c_mem_A
  have hFab : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := by
    intro x hx y hy
    have hc := mul_comm' (⟨(x : G), Subgroup.mem_subgroupOf.1 hx⟩ : A)
      ⟨(y : G), Subgroup.mem_subgroupOf.1 hy⟩
    have := congrArg Subtype.val hc
    exact Subtype.ext this
  have hFel : CFSG.IsElementaryAbelian 3 (F.map (QuotientGroup.mk' (Subgroup.center ↥L))) := by
    have hFE : CFSG.IsElementaryAbelian 3 F := by
      rw [← isElemAbelian_iff_isElementaryAbelian]
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
      · apply Subtype.ext
        apply Subtype.ext
        have hc := mul_comm' (⟨((a : ↥L) : G), Subgroup.mem_subgroupOf.1 a.2⟩ : A)
          ⟨((b : ↥L) : G), Subgroup.mem_subgroupOf.1 b.2⟩
        have := congrArg Subtype.val hc
        exact this
      · exact Subtype.ext (hab.2 (x : G) (Subgroup.mem_subgroupOf.1 hx))
    exact CFSG.RankThree.Asc83Table.IsElementaryAbelian.map_hom _ hFE
  obtain ⟨F₁, hZF₁, hF₁F, hF₁27, hF₁inv, hnot, hcore⟩ :=
    frame_core_eq_F1 hq hZ3 e hFel hZF hF81 hFab
  set a' : ↥L := ⟨a, hAL ha.mem⟩ with ha'
  have ha'F : a' ∈ F := Subgroup.mem_subgroupOf.2 ha.mem
  have ha'c : a' ∉ Subgroup.center ↥L := by
    intro hmem
    rw [h.center_eq hθ] at hmem
    apply ha.not_mem
    have := Subgroup.mem_map_of_mem L.subtype hmem
    rw [MonoidHom.map_zpowers] at this
    exact this
  have ha3 : a' ^ 3 ∈ Subgroup.center ↥L := by
    have : a' ^ 3 = 1 := Subtype.ext (hab.2 a ha.mem)
    rw [this]; exact Subgroup.one_mem _
  have h5 : 5 ∣ Nat.card (Subgroup.centralizer
      ({e (a' : ↥L ⧸ Subgroup.center ↥L)} : Set NativeSporadic.J3)) := by
    obtain ⟨l, ⟨w, hw, hlw⟩, hnc⟩ := ha.proj
    have hwL : w ∈ L := by
      have : w = (l : G)⁻¹ * a := by rw [hlw]; group
      rw [this]
      exact L.mul_mem (L.inv_mem l.2) (hAL ha.mem)
    have hw' : (⟨w, hwL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro x
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hw x x.2)
    have hq : (a' : ↥L ⧸ Subgroup.center ↥L) = (l : ↥L ⧸ Subgroup.center ↥L) := by
      have : a' = l * ⟨w, hwL⟩ := Subtype.ext hlw
      rw [this, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 hw', mul_one]
    have hq3 : (a' : ↥L ⧸ Subgroup.center ↥L) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow]; exact (QuotientGroup.eq_one_iff _).2 ha3
    have hq1 : (a' : ↥L ⧸ Subgroup.center ↥L) ≠ 1 := fun h1 =>
      ha'c ((QuotientGroup.eq_one_iff _).1 h1)
    exact five_dvd_centralizer_of_nonCentral e hq3 hq1 (by rw [hq]; exact hnc)
  have ha'F₁ : a' ∉ F₁ := hnot a' ha'F ha'c h5
  obtain ⟨I', hI'C, hI'perf, -, hI'max, hFIZ⟩ := hcore a' ha'F ha'F₁
  have hC : Subgroup.centralizer ({a} : Set G) ⊓ L =
      (Subgroup.centralizer ({a'} : Set ↥L)).map L.subtype := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.coe_subtype]
    constructor
    · rintro ⟨hx, hxL⟩
      exact ⟨⟨x, hxL⟩, Subtype.ext hx, rfl⟩
    · rintro ⟨x', hx', rfl⟩
      exact ⟨congrArg Subtype.val hx', x'.2⟩
  have hI : iCore L a = I'.map L.subtype := by
    unfold iCore
    rw [hC]
    exact CFSG.AGLEmbeddingD2.Wilson.Proving.perfCore_map_of_greatest L.subtype
      L.subtype_injective _ I' hI'C hI'perf hI'max
  have hzc : Subgroup.zpowers c = (Subgroup.center ↥L).map L.subtype := (h.map_center hθ).symm
  refine ⟨F₁, hF₁F, hF₁27, hF₁inv, ?_⟩
  rw [hI, hzc, ← hFmap, ← Subgroup.map_inf_eq _ _ _ L.subtype_injective, ← Subgroup.map_sup,
    hFIZ]

set_option maxRecDepth 20000 in
theorem Cover217.invariant_B {A E U : Subgroup G} {c : G} {L : Subgroup G}
    (h : Cover217 A E U c L) (hθ : aschbacherSolvableCore 3 L = ⊥) (hAL : A ≤ L) {a : G}
    (ha : Valid217 A c L a) :
    Nat.card ↥((A ⊓ iCore L a) ⊔ Subgroup.zpowers c) = 27 ∧
    (∀ S : Subgroup G, S ≤ A →
      (∀ x ∈ L ⊓ Subgroup.normalizer (A : Set G), S.map (MulAut.conj x).toMonoidHom = S) →
      S = ⊥ ∨ S = A ∨ S = Subgroup.zpowers c ∨ S = (A ⊓ iCore L a) ⊔ Subgroup.zpowers c) := by
  obtain ⟨F₁X, hF₁Xle, hF₁X27, hF₁Xinv, hB⟩ := h.B_eq_F₁ hθ hAL ha
  obtain ⟨F₁, hF₁A, hF₁27, hF₁inv, hcases⟩ := h.invariant_subgroups hθ hAL
  have hBA : (A ⊓ iCore L a) ⊔ Subgroup.zpowers c ≤ A := by
    rw [hB]
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hF₁Xle hx)
  have hBcard : Nat.card ↥((A ⊓ iCore L a) ⊔ Subgroup.zpowers c) = 27 := by
    rw [hB, Subgroup.card_map_of_injective L.subtype_injective, hF₁X27]
  have hBinv : ∀ x ∈ L ⊓ Subgroup.normalizer (A : Set G),
      ((A ⊓ iCore L a) ⊔ Subgroup.zpowers c).map (MulAut.conj x).toMonoidHom =
        (A ⊓ iCore L a) ⊔ Subgroup.zpowers c := by
    intro y hy
    have hy' : (⟨y, hy.1⟩ : ↥L) ∈ Subgroup.normalizer ((A.subgroupOf L : Subgroup ↥L) : Set ↥L) :=
      (mem_normalizer_subgroupOf_iff hAL ⟨y, hy.1⟩).2 hy.2
    rw [hB]
    have hle : (F₁X.map L.subtype).map (MulAut.conj y).toMonoidHom ≤ F₁X.map L.subtype := by
      rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨⟨y, hy.1⟩ * f * ⟨y, hy.1⟩⁻¹, hF₁Xinv _ hy' f hf, rfl⟩
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj y).toMonoidHom)
      (MulAut.conj y).injective]
  refine ⟨hBcard, fun S hSA hSinv => ?_⟩
  have hBF : (A ⊓ iCore L a) ⊔ Subgroup.zpowers c = F₁ := by
    rcases hcases _ hBA hBinv with h0 | h0 | h0 | h0
    · rw [h0] at hBcard; simp at hBcard
    · rw [h0, Nat.card_zpowers, h.orderOf_c] at hBcard; omega
    · exact h0
    · rw [h0, h.card] at hBcard; omega
  rcases hcases S hSA hSinv with h0 | h0 | h0 | h0
  · exact Or.inl h0
  · exact Or.inr (Or.inr (Or.inl h0))
  · exact Or.inr (Or.inr (Or.inr (h0.trans hBF.symm)))
  · exact Or.inr (Or.inl h0)

end Main

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

module

public import CFSG.LargeExtraspecial.AS35DRes
public import CFSG.LargeExtraspecial.AS35DFourSeven

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup

namespace S14

@[expose] def AschbacherBelow (n : ℕ) : Prop :=
  ∀ (H : Type) [Group H] [Finite H], Nat.card H < n →
    ∀ T : Setting H, 2 ≤ T.width → T.AschConcl

theorem aschbacherMainStmt_of_step
    (step : ∀ (G : Type) [Group G] [Finite G], AschbacherBelow (Nat.card G) →
      ∀ S : Setting G, 2 ≤ S.width → S.AschConcl) : AschbacherMainStmt := by
  suffices h : ∀ (n : ℕ) (G : Type) [Group G] [Finite G], Nat.card G = n →
      ∀ S : Setting G, 2 ≤ S.width → S.AschConcl from
    fun G _ _ S hn => h _ G rfl S hn
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ hG S hn
    exact step G (fun H _ _ hlt T hT => ih _ (hG ▸ hlt) H rfl T hT) S hn

end S14

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

omit [Finite G] in
theorem zInOTwo_of_not_aschConcl (hS : ¬ S.AschConcl) {t : G} (htQ : t ∈ S.QG)
    (ht : orderOf t = 2) : S.ZInOTwo t := by
  by_contra h
  exact hS (Or.inr (Or.inr (Or.inl ⟨t, htQ, ht, h⟩)))

omit [Finite G] in
theorem weaklyClosed_of_not_aschConcl (hS : ¬ S.AschConcl) (g : G)
    (hg : g * S.z * g⁻¹ ∈ S.QG) : g * S.z * g⁻¹ = S.z := by
  by_contra h
  exact hS (Or.inr (Or.inr (Or.inr ⟨g, hg, h⟩)))

omit [Finite G] in
theorem conj_mem_zGen_sup_QG {m : G} (hm : m ∈ S.M) {h : G} (hh : h ∈ S.zGen ⊔ S.QG) :
    m * h * m⁻¹ ∈ S.zGen ⊔ S.QG := by
  have hle : (S.zGen ⊔ S.QG).map (MulAut.conj m).toMonoidHom ≤ S.zGen ⊔ S.QG := by
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact S.zGen_normal.conj_mem x hx m
    · rintro _ ⟨x, hx, rfl⟩
      exact S.conj_mem_QG hm hx
  exact hle ⟨h, hh, rfl⟩

theorem sixOne (ih : S14.AschbacherBelow (Nat.card G)) (hn : 2 ≤ S.width)
    (hS : ¬ S.AschConcl) :
    IsSimpleGroup S.zGen ∧ centralizer (S.zGen : Set G) = ⊥ ∧ S.zGen ⊔ S.QG = ⊤ := by
  have hZ : S.z ∉ center G := fun h => hS (Or.inl h)
  have hO : ∀ t ∈ S.QG, orderOf t = 2 → S.ZInOTwo t := fun t ht ht2 =>
    S.zInOTwo_of_not_aschConcl hS ht ht2
  have hW := S.weaklyClosed_of_not_aschConcl hS
  obtain ⟨hsimp, hC⟩ := S.isSimpleGroup_zGen_of_weaklyClosed hn hO hZ hW
  refine ⟨hsimp, hC, ?_⟩
  by_contra htop
  set H := S.zGen ⊔ S.QG with hHdef
  have hQH : S.QG ≤ H := le_sup_right
  have hLH : S.zGen ≤ H := le_sup_left
  have hMH : ∀ m ∈ S.M, ∀ h ∈ H, m * h * m⁻¹ ∈ H := fun m hm h hh =>
    S.conj_mem_zGen_sup_QG hm hh
  have hlt : Nat.card H < Nat.card G := by
    by_contra hle
    exact htop (Subgroup.eq_top_of_le_card _ (not_lt.mp hle))
  set T := S.restrict H hQH hMH with hTdef
  have hT := ih H hlt T (by rw [hTdef, S.restrict_width]; exact hn)
  have hzT : (T.zGen.map H.subtype : Subgroup G) = S.zGen := by
    refine le_antisymm (S.map_zGen_restrict_le H hQH hMH) ?_
    set L' := T.zGen.map H.subtype with hL'
    have hL'L : L' ≤ S.zGen := S.map_zGen_restrict_le H hQH hMH
    have hzL' : S.z ∈ L' := ⟨T.z, T.z_mem_zGen, rfl⟩
    have hn' : (L'.subgroupOf S.zGen).Normal := ⟨fun x hx l => by
      rw [mem_subgroupOf] at hx ⊢
      obtain ⟨y, hy, hyx⟩ := hx
      refine ⟨⟨l, hLH l.2⟩ * y * ⟨l, hLH l.2⟩⁻¹, T.zGen_normal.conj_mem y hy _, ?_⟩
      simp only [coe_mul, coe_inv, subtype_apply] at hyx ⊢
      rw [hyx]⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (L'.subgroupOf S.zGen) with h | h
    · exfalso
      have : (⟨S.z, S.z_mem_zGen⟩ : S.zGen) ∈ L'.subgroupOf S.zGen := by
        rw [mem_subgroupOf]
        exact hzL'
      rw [h, mem_bot] at this
      exact S.z_ne_one (congrArg Subtype.val this)
    · intro x hx
      have : (⟨x, hx⟩ : S.zGen) ∈ L'.subgroupOf S.zGen := by
        rw [h]
        exact mem_top _
      rwa [mem_subgroupOf] at this
  apply hS
  rcases hT with h1 | ⟨-, -, halt⟩ | ⟨t, htQ, ht2, ht⟩ | ⟨g, hgQ, hgne⟩
  ·
    exfalso
    have hzC : S.z ∈ centralizer (S.zGen : Set G) := by
      rw [mem_centralizer_iff]
      intro x hx
      have := congrArg Subtype.val (mem_center_iff.mp h1 ⟨x, hLH hx⟩)
      exact this
    rw [hC, mem_bot] at hzC
    exact S.z_ne_one hzC
  ·
    refine Or.inr (Or.inl ⟨hsimp, hC, ?_⟩)
    rcases halt with h3 | ⟨hw, ⟨e⟩⟩
    · left
      intro l₁ hl₁ l₂ hl₂
      rw [← hzT] at hl₁ hl₂
      obtain ⟨m₁, hm₁, rfl⟩ := hl₁
      obtain ⟨m₂, hm₂, rfl⟩ := hl₂
      have h := h3 m₁ hm₁ m₂ hm₂
      rw [← Subgroup.orderOf_coe] at h
      exact h
    · right
      refine ⟨by rw [← hw, hTdef, S.restrict_width], ⟨?_⟩⟩
      exact ((MulEquiv.subgroupCongr hzT).symm.trans
        (T.zGen.equivMapOfInjective H.subtype H.subtype_injective).symm).trans e
  ·
    exfalso
    have htQ' : (t : G) ∈ S.QG := (S.mem_restrict_QG H hQH hMH).mp htQ
    have ht2' : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht2
    exact ht (S.zInOTwo_restrict H hQH hMH (hO _ htQ' ht2'))
  ·
    exfalso
    have hgQ' : (g : G) * S.z * (g : G)⁻¹ ∈ S.QG := (S.mem_restrict_QG H hQH hMH).mp hgQ
    exact hgne (Subtype.ext (hW _ hgQ'))

end Setting

end CFSG.LargeExtraspecial

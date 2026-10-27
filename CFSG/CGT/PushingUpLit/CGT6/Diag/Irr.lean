module

public import CFSG.CGT.PushingUpLit.CGT6.Diag.Defs
public import CFSG.CGT.PushingUpLit.CGT6.EmbThompson
public import CFSG.CGT.PushingUpLit.CGT6.EmbConjMod

public section

namespace CFSG.CGT.PushingUpLit.CGT6

namespace Diag.Irr

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit
  CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

section Group

theorem exists_mul_of_sup {M : Type*} [Group M] {L T : Subgroup M}
    (hT : T ≤ Subgroup.normalizer (L : Set M)) {g : M} (hg : g ∈ L ⊔ T) :
    ∃ l ∈ L, ∃ x ∈ T, g = l * x := by
  let P : Subgroup M :=
    { carrier := {g | ∃ l ∈ L, ∃ x ∈ T, g = l * x}
      one_mem' := ⟨1, L.one_mem, 1, T.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨l₁, hl₁, x₁, hx₁, rfl⟩ ⟨l₂, hl₂, x₂, hx₂, rfl⟩
        refine ⟨l₁ * (x₁ * l₂ * x₁⁻¹), L.mul_mem hl₁ ?_, x₁ * x₂, T.mul_mem hx₁ hx₂, by group⟩
        exact (Subgroup.mem_normalizer_iff.mp (hT hx₁) l₂).mp hl₂
      inv_mem' := by
        rintro _ ⟨l, hl, x, hx, rfl⟩
        refine ⟨x⁻¹ * l⁻¹ * x, ?_, x⁻¹, T.inv_mem hx, by group⟩
        have h1 := (Subgroup.mem_normalizer_iff.mp (hT (T.inv_mem hx)) l⁻¹).mp (L.inv_mem hl)
        simpa using h1 }
  have hLP : L ≤ P := fun l hl => ⟨l, hl, 1, T.one_mem, by simp⟩
  have hTP : T ≤ P := fun x hx => ⟨1, L.one_mem, x, hx, by simp⟩
  exact (sup_le hLP hTP) hg

end Group

section Module

variable {V : Type} [CommGroup V]

theorem exists_minimal_inv [Finite V] (K : Subgroup (MulAut V)) {A : Subgroup V}
    (hA : GInv K A) (hA1 : A ≠ ⊥) : ∃ W : Subgroup V, W ≤ A ∧ DiagMinInv K W := by
  let S : Set (Subgroup V) := {B | GInv K B ∧ B ≤ A ∧ B ≠ ⊥}
  obtain ⟨W, hW, hWmin⟩ := Set.Finite.exists_minimalFor (fun B : Subgroup V => B) S
    (Set.toFinite S) ⟨A, hA, le_rfl, hA1⟩
  refine ⟨W, hW.2.1, hW.2.2, hW.1, fun B hB hBW => ?_⟩
  by_cases hB1 : B = ⊥
  · exact Or.inl hB1
  · right
    exact le_antisymm hBW (hWmin ⟨hB, hBW.trans hW.2.1, hB1⟩ hBW)

theorem diagImg_eq_of_inv [Finite V] {K : Subgroup (MulAut V)} {W : Subgroup V} (hW : GInv K W)
    {x : MulAut V} (hx : x ∈ K) : diagImg x W = W := by
  refine Subgroup.eq_of_le_of_card_ge (fun _ ⟨w, hw, e⟩ => ?_) ?_
  · rw [← e]
    exact hW x hx w hw
  · rw [diagImg, Subgroup.card_map_of_injective (f := x.toMonoidHom) x.injective]

end Module

section Comm

variable {V : Type} [CommGroup V] [Finite V]

theorem commOn_eq_commV {Y : Subgroup (MulAut V)} (hV : ∀ v : V, v ^ 2 = 1)
    (hperf : ⁅Y, Y⁆ = Y) (hY : ClassX4 Y) {D : Subgroup V} (hD : ∀ g ∈ Y, ∀ d ∈ D, g d ∈ D)
    (hnt : ∃ g ∈ Y, ∃ d ∈ D, g d ≠ d) : commOn Y D = commV Y := by
  have hPerf : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hperf
  have hle : commOn Y D ≤ commV Y := commOn_le_commV D
  have hDle : commOn Y D ≤ D := commOn_le_self hD
  have hNinv : ∀ g ∈ Y, ∀ n ∈ commOn Y D ⊔ (commV Y ⊓ fixV Y),
      g n ∈ commOn Y D ⊔ (commV Y ⊓ fixV Y) := by
    intro g hg n hn
    obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup.mp hn
    rw [map_mul, (mem_fixV.mp hc.2) g hg]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (commOn_invariant hD g hg a ha))
      (Subgroup.mem_sup_right hc)
  rcases ClassX4.invariant_irreducible hperf hV hY (commOn Y D ⊔ (commV Y ⊓ fixV Y)) hNinv
    (sup_le hle inf_le_left) le_sup_right with h | h
  · exfalso
    have hfix : ∀ g ∈ Y, ∀ a ∈ commOn Y D, g a = a := by
      intro g hg a ha
      have : a ∈ commV Y ⊓ fixV Y := by
        rw [← h]
        exact Subgroup.mem_sup_left ha
      exact (mem_fixV.mp this.2) g hg
    have hDY : GInv Y D := hD
    have h1 := trivial_of_unipotent (resG Y D hDY) ((commOn Y D).subgroupOf D)
      (fun g a ha => Subtype.ext (hfix g g.2 a ha))
      (fun g v => by
        rw [Subgroup.mem_subgroupOf]
        exact Subgroup.subset_closure ⟨g, g.2, v, v.2, rfl⟩)
    obtain ⟨g, hg, d, hd, hne⟩ := hnt
    exact hne (congrArg Subtype.val (h1 ⟨g, hg⟩ ⟨d, hd⟩))
  · apply le_antisymm hle
    refine (USelf_of_perfect hperf) (commOn Y D) (fun g hg u hu => ?_)
    rw [← h] at hu
    obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup.mp hu
    rw [map_mul, (mem_fixV.mp hc.2) g hg]
    have : g a * c * (a * c)⁻¹ = g a * a⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (commOn_invariant hD g hg a ha) (Subgroup.inv_mem _ ha)

end Comm

section Core

variable {V : Type} [CommGroup V] [Finite V]

theorem irr_core (hV : ∀ v : V, v ^ 2 = 1) {G T Y L : Subgroup (MulAut V)}
    (hLeq : conjClosure Y G = L) (hgen : L ⊔ T = G) (hTG : T ≤ G)
    (hTc : ∀ x ∈ T, ∀ y ∈ Y, y * x = x * y) (hperf : ⁅Y, Y⁆ = Y) (hY : ClassX4 Y)
    (hLne : L ≠ ⊥) (hirr : ∀ A : Subgroup V, GInv G A → A = ⊥ ∨ A = ⊤)
    {A : Subgroup V} (hA : GInv L A) (hA1 : A ≠ ⊥) : A = ⊤ := by
  have hGL : G ≤ Subgroup.normalizer (L : Set (MulAut V)) := by
    have := le_normalizer_conjClosure (Y := Y) (Xt := G)
    rwa [hLeq] at this
  have hLG : L ≤ G := hgen ▸ le_sup_left
  have hYL : Y ≤ L := hLeq ▸ le_conjClosure
  have hdec : ∀ g ∈ G, ∃ l ∈ L, ∃ x ∈ T, g = l * x := fun g hg =>
    exists_mul_of_sup (hTG.trans hGL) (hgen ▸ hg)
  obtain ⟨V₀, hV₀A, hV₀1, hV₀inv, hV₀min⟩ := exists_minimal_inv L hA hA1
  have hnt : ∃ y ∈ Y, ∃ v ∈ V₀, y v ≠ v := by
    by_contra hnot
    push Not at hnot
    have hLfix : L ≤ fixW V₀ := by
      rw [← hLeq, conjClosure, Subgroup.closure_le]
      rintro _ ⟨g, hg, y, hy, rfl⟩ v hv
      obtain ⟨l, hl, x, hx, rfl⟩ := hdec g hg
      have hxy : x * y * x⁻¹ = y := by
        rw [mul_inv_eq_iff_eq_mul]
        exact (hTc x hx y hy).symm
      have hcomm : l * x * y * (l * x)⁻¹ = l * y * l⁻¹ := by
        calc l * x * y * (l * x)⁻¹ = l * (x * y * x⁻¹) * l⁻¹ := by group
          _ = l * y * l⁻¹ := by rw [hxy]
      show (l * x * y * (l * x)⁻¹) v = v
      rw [hcomm]
      have h1 : l⁻¹ v ∈ V₀ := hV₀inv l⁻¹ (L.inv_mem hl) v hv
      show l (y (l⁻¹ v)) = v
      rw [hnot y hy _ h1]
      simp
    have hfixG : ∀ g ∈ G, ∀ v ∈ fixV L, g v ∈ fixV L := by
      intro g hg v hv l hl
      have h1 : g⁻¹ * l * g⁻¹⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hGL (G.inv_mem hg)) l).mp hl
      have h2 := (mem_fixV.mp hv) _ h1
      have : l (g v) = g ((g⁻¹ * l * g⁻¹⁻¹) v) := by simp [MulAut.mul_apply]
      rw [this, h2]
    have hV₀fix : V₀ ≤ fixV L := fun v hv l hl => hLfix hl v hv
    have htop := hirr (fixV L) hfixG
    have hfixtop : fixV L = ⊤ := by
      rcases htop with h0 | h0
      · exact absurd (le_bot_iff.mp (h0 ▸ hV₀fix)) hV₀1
      · exact h0
    apply hLne
    rw [eq_bot_iff]
    intro l hl
    rw [Subgroup.mem_bot]
    ext v
    have : v ∈ fixV L := hfixtop ▸ Subgroup.mem_top v
    exact (mem_fixV.mp this) l hl
  have hT₀ : ∀ x ∈ T, ∀ v ∈ V₀, x v ∈ V₀ := by
    intro x hx
    by_contra hnot
    push Not at hnot
    obtain ⟨v₁, hv₁, hxv₁⟩ := hnot
    have hne : diagImg x V₀ ≠ V₀ := fun heq => hxv₁ (heq ▸ ⟨v₁, hv₁, rfl⟩)
    have hxL : ∀ l ∈ L, ∀ w ∈ diagImg x V₀, l w ∈ diagImg x V₀ := by
      rintro l hl _ ⟨v, hv, rfl⟩
      have h1 : x⁻¹ * l * x⁻¹⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hGL (G.inv_mem (hTG hx))) l).mp hl
      refine ⟨(x⁻¹ * l * x⁻¹⁻¹ : MulAut V) v, hV₀inv _ h1 v hv, ?_⟩
      show x ((x⁻¹ * l * x⁻¹⁻¹) v) = l (x v)
      simp [MulAut.mul_apply]
    have hinf : V₀ ⊓ diagImg x V₀ = ⊥ := by
      have hinv : GInv L (V₀ ⊓ diagImg x V₀) := fun l hl w hw =>
        ⟨hV₀inv l hl w hw.1, hxL l hl w hw.2⟩
      rcases hV₀min _ hinv inf_le_left with h0 | h0
      · exact h0
      · exfalso
        have hle : V₀ ≤ diagImg x V₀ := fun w hw => by
          have : w ∈ V₀ ⊓ diagImg x V₀ := by
            rw [h0]
            exact hw
          exact this.2
        have hcard : Nat.card ↥(diagImg x V₀) ≤ Nat.card ↥V₀ := by
          rw [diagImg, Subgroup.card_map_of_injective (f := x.toMonoidHom) x.injective]
        exact hne (Subgroup.eq_of_le_of_card_ge hle hcard).symm
    have hV₀Y : ∀ g ∈ Y, ∀ d ∈ V₀, g d ∈ V₀ := fun g hg d hd => hV₀inv g (hYL hg) d hd
    have hxY : ∀ g ∈ Y, ∀ d ∈ diagImg x V₀, g d ∈ diagImg x V₀ := fun g hg d hd =>
      hxL g (hYL hg) d hd
    obtain ⟨y, hy, v, hv, hyv⟩ := hnt
    have hxnt : ∃ g ∈ Y, ∃ d ∈ diagImg x V₀, g d ≠ d := by
      refine ⟨y, hy, x v, ⟨v, hv, rfl⟩, fun e => hyv ?_⟩
      have h1 : y (x v) = x (y v) := by
        have := congrArg (fun φ : MulAut V => φ v) (hTc x hx y hy)
        simpa [MulAut.mul_apply] using this
      rw [h1] at e
      exact x.injective e
    have h1 := commOn_eq_commV hV hperf hY hV₀Y ⟨y, hy, v, hv, hyv⟩
    have h2 := commOn_eq_commV hV hperf hY hxY hxnt
    have hU₀ : commV Y ≤ V₀ ⊓ diagImg x V₀ :=
      le_inf (h1 ▸ commOn_le_self hV₀Y) (h2 ▸ commOn_le_self hxY)
    rw [hinf] at hU₀
    have hyv' : y v * v⁻¹ ∈ commV Y := Subgroup.subset_closure ⟨y, hy, v, rfl⟩
    have := hU₀ hyv'
    rw [Subgroup.mem_bot, mul_inv_eq_one] at this
    exact hyv this
  have hV₀G : GInv G V₀ := by
    intro g hg v hv
    obtain ⟨l, hl, x, hx, rfl⟩ := hdec g hg
    exact hV₀inv l hl _ (hT₀ x hx v hv)
  rcases hirr V₀ hV₀G with h0 | h0
  · exact absurd h0 hV₀1
  · exact top_le_iff.mp (h0 ▸ hV₀A)

end Core

end Diag.Irr

theorem diagModIrr_holds : DiagMod_irr := by
  intro V _ _ hV G T Y K K' t h A hA
  by_cases hA1 : A = ⊥
  · exact Or.inl hA1
  right
  have hClass : ClassX4 Y := by
    rcases h.cls with h1 | ⟨n, hn, h2⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨n, hn, h2⟩)
  have hKne : K ≠ ⊥ := by
    intro hK
    have hnt : Nontrivial (↥K ⧸ Subgroup.center ↥K) := h.quasi.2.toNontrivial
    have hone : ∀ k : ↥K, k = 1 := fun k => Subtype.ext (Subgroup.mem_bot.mp (hK ▸ k.2))
    obtain ⟨a, b, hab⟩ := exists_pair_ne (↥K ⧸ Subgroup.center ↥K)
    obtain ⟨k₁, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨k₂, rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (by rw [hone k₁, hone k₂])
  exact Diag.Irr.irr_core hV (L := K ⊔ K') h.L_eq h.gen h.T_le
    (fun x hx y hy => Subgroup.mem_centralizer_iff.mp (h.T_cent hx) y hy) h.perfY hClass
    (fun hbot => hKne (le_bot_iff.mp (hbot ▸ le_sup_left))) h.irr hA hA1

end CFSG.CGT.PushingUpLit.CGT6

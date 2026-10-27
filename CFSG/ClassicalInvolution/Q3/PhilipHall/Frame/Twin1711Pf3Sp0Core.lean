module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Struct

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

set_option linter.unusedSectionVars false

namespace Twin1711

namespace Sp0Core

variable {H : Type} [Group H]

@[expose] def TT (t : H) : Subgroup H := (⊤ : Subgroup H) ⊓ Subgroup.centralizer ({t} : Set H)

@[expose] def EE (R : Subgroup H) (t : H) : Subgroup H := ⨆ s ∈ TT t, conjSub s R

structure TFacts (R : Subgroup H) (t : H) : Prop where
  maximal : ∀ g : H, g ∉ TT t → Subgroup.closure ((TT t : Set H) ∪ {g}) = ⊤
  centE : Nat.card ↥(Subgroup.centralizer (EE R t : Set H)) ≤ 8
  index : ∀ N : Subgroup H, EE R t ≤ N → N ≤ TT t → (N.subgroupOf (TT t)).Normal →
    (∀ x : H, x * t * x⁻¹ ∈ N → x * t * x⁻¹ = t) → 8 < N.relIndex (TT t)

def stabB (B : Set (Subgroup H)) : Subgroup H where
  carrier := {g | conjSub g '' B = B}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    show conjSub (a * b) '' B = B
    have : conjSub (a * b) '' B = conjSub a '' (conjSub b '' B) := by
      rw [Set.image_image]
      exact Set.image_congr fun J _ => by rw [conjSub_mul]
    rw [this]
    have hb' : conjSub b '' B = B := hb
    have ha' : conjSub a '' B = B := ha
    rw [hb', ha']
  inv_mem' := by
    intro a ha
    show conjSub a⁻¹ '' B = B
    have ha' : conjSub a '' B = B := ha
    calc conjSub a⁻¹ '' B = conjSub a⁻¹ '' (conjSub a '' B) := by rw [ha']
      _ = B := by
        rw [Set.image_image]
        simp [conjSub_inv_conjSub]

theorem mem_stabB {B : Set (Subgroup H)} {g : H} : g ∈ stabB B ↔ conjSub g '' B = B := Iff.rfl

variable [Finite H]

theorem noSandwich_of_tfacts {R : Subgroup H} {t : H} {B : Set (Subgroup H)} {N : Subgroup H}
    (hF : TFacts R t) (hout : ∀ α : MulAut H, ∃ g : H, α = MulAut.conj g)
    (hinv : IsUniqueInvolution R t) (hS : SandwichData (⊤ : Subgroup H) R t B N) : False := by
  have hstab : ∀ g : H, conjSub g R ∈ B → g ∈ stabB B := by
    intro g hg
    rcases hS.block g (Subgroup.mem_top g) with h1 | h1
    · exact h1
    · exfalso
      exact Set.disjoint_left.mp h1 ⟨R, hS.mem, rfl⟩ hg
  have hTB : ∀ s ∈ TT t, conjSub s R ∈ B := fun s hs => hS.twins s hs
  have hBTw : ∀ J ∈ B, ∃ s ∈ TT t, conjSub s R = J := by
    intro J hJ
    by_contra hne
    push Not at hne
    obtain ⟨x, -, hx⟩ := hS.sub hJ
    have hxT : x ∉ TT t := fun h => hne x h hx
    have hxS : x ∈ stabB B := hstab x (hx ▸ hJ)
    have hTS : TT t ≤ stabB B := fun s hs => hstab s (hTB s hs)
    have hall : stabB B = ⊤ := by
      rw [eq_top_iff, ← hF.maximal x hxT]
      exact (Subgroup.closure_le _).mpr (Set.union_subset hTS (by simpa using hxS))
    apply hS.proper
    ext J'
    constructor
    · exact fun h => hS.sub h
    · rintro ⟨g, -, rfl⟩
      have h' : conjSub g '' B = B := (hall ▸ Subgroup.mem_top g : g ∈ stabB B)
      rw [← h']
      exact ⟨R, hS.mem, rfl⟩
  have hEN : EE R t ≤ N := iSup₂_le fun s hs => hS.twins_le s hs
  have hNT : N ≤ TT t := hS.le
  have hNn : (N.subgroupOf (TT t)).Normal := hS.normal
  have hNinv : ∀ x : H, x * t * x⁻¹ ∈ N → x * t * x⁻¹ = t := by
    intro x hx
    obtain ⟨J, hJ, hJu⟩ := hS.inv x (Subgroup.mem_top x) hx
    obtain ⟨s, hs, rfl⟩ := hBTw J hJ
    have h1 := (hinv.conj s).eq hJu
    have hs' : s * t * s⁻¹ = t := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hs).2
      rw [this, mul_inv_cancel_right]
    rw [← h1, hs']
  have h8 := hF.index N hEN hNT hNn hNinv
  have hidx : N.relIndex (TT t) ≤ Nat.card ↥(fixSet (⊤ : Subgroup H) B) := hS.index
  have hn : ∀ a : H, a ∈ Subgroup.normalizer ((⊤ : Subgroup H) : Set H) := fun a => by
    rw [Subgroup.mem_normalizer_iff]; simp
  have hBE : ∀ b ∈ B, b ≤ EE R t := by
    intro b hb
    obtain ⟨s, hs, rfl⟩ := hBTw b hb
    exact le_iSup₂ (f := fun s (_ : s ∈ TT t) => conjSub s R) s hs
  have hfix : Nat.card ↥(fixSet (⊤ : Subgroup H) B) ≤ 8 := by
    refine le_trans (Nat.card_le_card_of_surjective
      (fun g : ↥(Subgroup.centralizer (EE R t : Set H)) =>
        (⟨conjAut (⊤ : Subgroup H) g.1 (hn g.1), ?_⟩ : ↥(fixSet (⊤ : Subgroup H) B))) ?_)
      hF.centE
    · intro b hb y hy
      apply Subtype.ext
      rw [conjAut_apply]
      have := Subgroup.mem_centralizer_iff.mp g.2 (y : H) (hBE b hb hy)
      calc (g.1 : H) * (y : H) * (g.1 : H)⁻¹ = (y : H) * g.1 * (g.1 : H)⁻¹ := by rw [← this]
        _ = y := by group
    · rintro ⟨α, hα⟩
      let β : MulAut H := (Subgroup.topEquiv (G := H)).symm.trans
        (α.trans (Subgroup.topEquiv (G := H)))
      obtain ⟨g, hg⟩ := hout β
      have hβ : ∀ y : H, g * y * g⁻¹ = (α ⟨y, trivial⟩ : H) := by
        intro y
        have := congrArg (fun γ : MulAut H => γ y) hg
        have e : (Subgroup.topEquiv (G := H)).symm y = ⟨y, trivial⟩ := rfl
        simpa [β, e] using this.symm
      have hgE : ∀ y ∈ EE R t, y * g = g * y := by
        have hle : EE R t ≤ Subgroup.centralizer ({g} : Set H) := by
          refine iSup₂_le fun s hs => ?_
          intro y hy
          rw [Subgroup.mem_centralizer_singleton_iff]
          have h1 := hα (conjSub s R) (hTB s hs) ⟨y, trivial⟩ hy
          have h2 := hβ y
          rw [h1] at h2
          calc y * g = (g * y * g⁻¹) * g := by rw [h2]
            _ = g * y := by group
        intro y hy
        exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
      refine ⟨⟨g, fun y hy => hgE y hy⟩, ?_⟩
      apply Subtype.ext
      apply MulEquiv.ext
      intro y
      apply Subtype.ext
      rw [conjAut_apply]
      exact (by simpa using hβ y : g * (y : H) * g⁻¹ = (α y : H))
  omega

end Sp0Core

end Twin1711

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

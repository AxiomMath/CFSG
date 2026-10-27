module

public import CFSG.Quasithin.Background.FixVTransport
public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.CGT.PushingUpLit.BHS.Defs
public import CFSG.CGT.PushingUpLit.BHS.Replacement
public import CFSG.Quasithin.Background.B19Basic
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.LieType.BorelTits.Basic
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.Helpers
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Quasithin.Background.B1Solvable
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.GroupTheory.SteinbergCEQuaternionDihedral
public import CFSG.RankThree.LocalRank.SelectorCases

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.RankThree.PartOne CFSG.Open CFSG.QuasithinUnique

namespace Glauberman

variable {Γ : Type*} [Group Γ]

theorem mem_conj {g x : Γ} {H : Subgroup Γ} :
    x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem map_conj_le {g : Γ} {H K : Subgroup Γ} (hg : g ∈ K) (hH : H ≤ K) :
    H.map (MulAut.conj g).toMonoidHom ≤ K := by
  rintro _ ⟨x, hx, rfl⟩
  exact K.mul_mem (K.mul_mem hg (hH hx)) (K.inv_mem hg)

theorem map_conj_self {g : Γ} {K : Subgroup Γ} (hg : g ∈ K) :
    K.map (MulAut.conj g).toMonoidHom = K := by
  refine le_antisymm (map_conj_le hg le_rfl) fun x hx => mem_conj.2 ?_
  exact K.mul_mem (K.mul_mem (K.inv_mem hg) hx) hg

theorem map_conj_map_conj (x y : Γ) (H : Subgroup Γ) :
    (H.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      H.map (MulAut.conj (x * y)).toMonoidHom := by
  ext z
  simp only [mem_conj, mul_inv_rev, mul_assoc]

theorem map_conj_inv_map_conj (g : Γ) (H : Subgroup Γ) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = H := by
  rw [map_conj_map_conj, inv_mul_cancel, MulAut.conj.map_one]
  ext z
  simp

theorem card_map_conj (g : Γ) (H : Subgroup Γ) :
    Nat.card (H.map (MulAut.conj g).toMonoidHom) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem map_conj_map_conj_inv (g : Γ) (H : Subgroup Γ) :
    (H.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = H := by
  have := map_conj_inv_map_conj g⁻¹ H
  rwa [inv_inv] at this

def coreIn (G M : Subgroup Γ) : Subgroup Γ where
  carrier := {y | ∀ g ∈ G, g⁻¹ * y * g ∈ M}
  one_mem' := fun g _ => by simp
  mul_mem' := fun {x y} hx hy g hg => by
    have := M.mul_mem (hx g hg) (hy g hg)
    simpa [mul_assoc] using this
  inv_mem' := fun {x} hx g hg => by
    have := M.inv_mem (hx g hg)
    simpa [mul_assoc] using this

theorem mem_coreIn {G M : Subgroup Γ} {y : Γ} : y ∈ coreIn G M ↔ ∀ g ∈ G, g⁻¹ * y * g ∈ M :=
  Iff.rfl

theorem coreIn_le {G M : Subgroup Γ} : coreIn G M ≤ M := fun y hy => by
  simpa using mem_coreIn.1 hy 1 G.one_mem

theorem le_normalizer_coreIn (G M : Subgroup Γ) :
    G ≤ Subgroup.normalizer (coreIn G M : Set Γ) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro y
  simp only [mem_coreIn]
  constructor
  · intro hy g hg
    have := hy (h⁻¹ * g) (G.mul_mem (G.inv_mem hh) hg)
    simpa [mul_assoc] using this
  · intro hy g hg
    have := hy (h * g) (G.mul_mem hh hg)
    simpa [mul_assoc] using this

variable {V : Type*} [CommGroup V]

theorem fixV_map_conj (g : MulAut V) (X : Subgroup (MulAut V)) :
    fixV (X.map (MulAut.conj g).toMonoidHom) = (fixV X).map g.toMonoidHom :=
  CFSG.Quasithin.fixV_map_conj_eq X g

theorem mem_fixV_zpowers {x : MulAut V} {v : V} : v ∈ fixV (Subgroup.zpowers x) ↔ x v = v :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem card_sup_of_inf_eq_bot [Finite V] {U W : Subgroup V} (h : U ⊓ W = ⊥) :
    Nat.card (U ⊔ W : Subgroup V) = Nat.card U * Nat.card W := by
  have := card_sup_mul_card_inf' (X := U) (Y := W) fun x _ y _ => mul_comm x y
  rwa [h, Subgroup.card_bot, mul_one] at this

end Glauberman

open Glauberman

variable {V : Type*} [CommGroup V]

structure GlHyp (G M S A : Subgroup (MulAut V)) : Prop where
  hV : ∀ v : V, v ^ 2 = 1
  lt : M < G
  max : ∀ Y : Subgroup (MulAut V), M ≤ Y → Y ≤ G → Y = M ∨ Y = G
  syl : IsSylowOf 2 S M
  le : A ≤ S
  ne : A ≠ ⊥
  el : IsElemAbelian2 A
  o2 : pCoreOf 2 G = ⊥
  quad : IsQuadratic A
  gen : ∀ g ∈ G, g ∉ M → A ⊔ Subgroup.zpowers g = G
  fix : fixV G = ⊥
  off : Nat.card V ≤ Nat.card A * Nat.card (fixV A)

namespace GlHyp

variable {G M S A : Subgroup (MulAut V)}

theorem A_le_M (h : GlHyp G M S A) : A ≤ M := h.le.trans h.syl.1

theorem A_le_G (h : GlHyp G M S A) : A ≤ G := h.A_le_M.trans h.lt.le

theorem conj [Finite V] (h : GlHyp G M S A) {g : MulAut V} (hg : g ∈ G) :
    GlHyp G (M.map (MulAut.conj g).toMonoidHom) (S.map (MulAut.conj g).toMonoidHom)
      (A.map (MulAut.conj g).toMonoidHom) where
  hV := h.hV
  lt := by
    refine lt_of_le_of_ne (map_conj_le hg h.lt.le) fun he => h.lt.ne ?_
    rw [← map_conj_inv_map_conj g M, he, map_conj_self (G.inv_mem hg)]
  max := by
    intro Y hMY hYG
    have h1 : M ≤ Y.map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [← map_conj_inv_map_conj g M]
      exact Subgroup.map_mono hMY
    have h2 : Y.map (MulAut.conj g⁻¹).toMonoidHom ≤ G := map_conj_le (G.inv_mem hg) hYG
    rcases h.max _ h1 h2 with he | he
    · left
      rw [← map_conj_map_conj_inv g Y, he]
    · right
      rw [← map_conj_map_conj_inv g Y, he, map_conj_self hg]
  syl := by
    refine ⟨Subgroup.map_mono h.syl.1, h.syl.2.1.map _, ?_⟩
    rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
    exact h.syl.2.2
  le := Subgroup.map_mono h.le
  ne := by
    intro he
    apply h.ne
    rw [← map_conj_inv_map_conj g A, he, Subgroup.map_bot]
  el := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, h.el.1 a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_pow, h.el.2 a ha, map_one]
  o2 := h.o2
  quad := by
    show commV _ ≤ fixV _
    rw [B19.commV_map_conj, fixV_map_conj]
    exact Subgroup.map_mono h.quad
  gen := by
    intro y hy hyM
    have hy' : g⁻¹ * y * g ∈ G := G.mul_mem (G.mul_mem (G.inv_mem hg) hy) hg
    have hyM' : g⁻¹ * y * g ∉ M := fun hm => hyM (mem_conj.2 hm)
    have := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) (h.gen _ hy' hyM')
    rwa [Subgroup.map_sup, MonoidHom.map_zpowers, map_conj_self hg, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at this
  fix := h.fix
  off := by
    rw [card_map_conj, fixV_map_conj, Subgroup.card_map_of_injective g.injective]
    exact h.off

end GlHyp

end CFSG.CGT.PushingUpLit.BHS

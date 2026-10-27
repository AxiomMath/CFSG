
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246BlockCore
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeSection
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin CFSG.Open
open scoped commutatorElement

namespace L246

variable {G : Type} [Group G] [Finite G]

section Dictionary

variable {V : Subgroup G} {hV : IsElemAbelian 2 V}

@[expose] def intSub (hV : IsElemAbelian 2 V) (W : Subgroup G) : Subgroup (IntMod V hV) where
  carrier := {v | v.val ∈ W}
  one_mem' := by
    show (1 : IntMod V hV).val ∈ W
    rw [IntMod.val_one]; exact W.one_mem
  mul_mem' := fun {a b} ha hb => by
    show (a * b).val ∈ W
    rw [IntMod.val_mul]; exact W.mul_mem ha hb
  inv_mem' := fun {a} ha => by
    show (a⁻¹).val ∈ W
    rw [IntMod.val_inv]; exact W.inv_mem ha

omit [Finite G] in
theorem mem_intSub {W : Subgroup G} {v : IntMod V hV} : v ∈ intSub hV W ↔ v.val ∈ W := Iff.rfl

@[expose] def ambSub (J : Subgroup (IntMod V hV)) : Subgroup G where
  carrier := {g | ∃ v ∈ J, v.val = g}
  one_mem' := ⟨1, J.one_mem, IntMod.val_one⟩
  mul_mem' := fun {a b} ⟨x, hx, hxa⟩ ⟨y, hy, hyb⟩ =>
    ⟨x * y, J.mul_mem hx hy, by rw [IntMod.val_mul, hxa, hyb]⟩
  inv_mem' := fun {a} ⟨x, hx, hxa⟩ => ⟨x⁻¹, J.inv_mem hx, by rw [IntMod.val_inv, hxa]⟩

@[expose] def valHom (V : Subgroup G) (hV : IsElemAbelian 2 V) : IntMod V hV →* G where
  toFun := IntMod.val
  map_one' := IntMod.val_one
  map_mul' := IntMod.val_mul

omit [Finite G] in
theorem mem_ambSub {J : Subgroup (IntMod V hV)} {g : G} : g ∈ ambSub J ↔ ∃ v ∈ J, v.val = g :=
  Iff.rfl

omit [Finite G] in
theorem intSub_ambSub (J : Subgroup (IntMod V hV)) : intSub hV (ambSub J) = J := by
  ext v
  rw [mem_intSub, mem_ambSub]
  constructor
  · rintro ⟨w, hw, hwv⟩
    rwa [← IntMod.val_injective hwv]
  · intro hv
    exact ⟨v, hv, rfl⟩

omit [Finite G] in
theorem ambSub_le {J : Subgroup (IntMod V hV)} {W : Subgroup G} (h : J ≤ intSub hV W) :
    ambSub J ≤ W := by
  rintro _ ⟨v, hv, rfl⟩
  exact h hv

omit [Finite G] in
theorem le_ambSub {J : Subgroup (IntMod V hV)} {W : Subgroup G} (hWV : W ≤ V)
    (h : intSub hV W ≤ J) : W ≤ ambSub J := by
  intro w hw
  exact ⟨⟨w, hWV hw⟩, h hw, rfl⟩

omit [Finite G] in
theorem le_normalizer_of_forall_conj {X P : Subgroup G} (h : ∀ x ∈ X, ∀ p ∈ P, x * p * x⁻¹ ∈ P) :
    X ≤ Subgroup.normalizer (P : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro p
  refine ⟨fun hp => h x hx p hp, fun hp => ?_⟩
  have := h x⁻¹ (X.inv_mem hx) _ hp
  simpa [mul_assoc] using this

end Dictionary

section Commute

variable {V : Subgroup G} (hV : IsElemAbelian 2 V)

omit [Finite G] in
theorem convI_comm_iff {a b : G} (ha : a ∈ Subgroup.normalizer (V : Set G))
    (hb : b ∈ Subgroup.normalizer (V : Set G)) :
    convI hV ⟨a, ha⟩ * convI hV ⟨b, hb⟩ = convI hV ⟨b, hb⟩ * convI hV ⟨a, ha⟩ ↔
      a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
  CFSG.Quasithin.ConvI.convI_comm_iff hV ha hb

end Commute

section Stab

variable {V : Subgroup G} (hV : IsElemAbelian 2 V)

omit [Finite G] in
theorem convI_mem_stabSub_intSub {W : Subgroup G} {g : G}
    (hgN : g ∈ Subgroup.normalizer (V : Set G)) (hgW : g ∈ Subgroup.normalizer (W : Set G)) :
    convI hV ⟨g, hgN⟩ ∈ stabSub (intSub hV W) := by
  intro u
  show (convI hV ⟨g, hgN⟩ u) ∈ intSub hV W ↔ u ∈ intSub hV W
  rw [mem_intSub, mem_intSub, convI_apply_val]
  exact (Subgroup.mem_normalizer_iff.1 hgW u.val).symm

omit [Finite G] in
theorem nonempty_autI_equiv_alt {L : Subgroup G} (hL : L ≤ Subgroup.normalizer (V : Set G)) {m : ℕ}
    (h : IsAltQuotient L (Subgroup.centralizer (V : Set G)) m) :
    Nonempty (↥(autI hV L) ≃* alternatingGroup (Fin m)) := by
  obtain ⟨φ, hφ, hker⟩ := h
  have hk : (convHom hV L hL).ker = φ.ker := by
    rw [ker_convHom, hker]
    ext x
    simp [Subgroup.mem_subgroupOf]
  exact ⟨(MulEquiv.subgroupCongr (range_convHom hV L hL).symm).trans
    ((QuotientGroup.quotientKerEquivRange (convHom hV L hL)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hk).trans
        (QuotientGroup.quotientKerEquivOfSurjective φ hφ)))⟩

end Stab

section Block

variable {X T L : Subgroup G}

structure BlockData (X T L : Subgroup G) (m : ℕ) : Prop where
  charTwo : CharTwo X
  sylow : IsSylowTwoOf T X
  block : IsBlock2 X L
  normJ : thompsonJ T ≤ Subgroup.normalizer (L : Set G)
  uV : blockU L ≤ VZ T X
  notC : ¬ ⁅L, thompsonJ T⁆ ≤ Subgroup.centralizer (VZ T X : Set G)
  alt : IsAltQuotient L (Subgroup.centralizer (VZ T X : Set G)) m
  m_cases : m = 5 ∨ m = 7

namespace BlockData

variable {m : ℕ} (D : BlockData X T L m)

include D

omit [Finite G] in
theorem toCore : BlockCore X T L :=
  ⟨D.charTwo, D.sylow, D.block, D.normJ, D.uV, D.notC⟩

theorem red : IsTwoReducedIn X (VZ T X) :=
  D.toCore.red

theorem elem : IsElemAbelian 2 (VZ T X) :=
  D.toCore.elem

theorem XN : X ≤ Subgroup.normalizer (VZ T X : Set G) :=
  D.toCore.XN

omit [Finite G] in
theorem LX : L ≤ X :=
  D.toCore.LX

omit [Finite G] in
theorem TX : T ≤ X :=
  D.toCore.TX

theorem LN : L ≤ Subgroup.normalizer (VZ T X : Set G) :=
  D.toCore.LN

theorem VT : VZ T X ≤ T :=
  D.toCore.VT

theorem exists_offender : ∃ A : Subgroup G, IsMaxElemAbelian T A ∧
    ¬ ⁅L, A⁆ ≤ Subgroup.centralizer (VZ T X : Set G) :=
  D.toCore.exists_offender

omit [Finite G] D in
theorem le_J {A : Subgroup G} (hA : IsMaxElemAbelian T A) : A ≤ thompsonJ T :=
  BlockCore.le_J hA

omit [Finite G] in
theorem A_le_normalizer {A : Subgroup G} (hA : IsMaxElemAbelian T A) :
    A ≤ Subgroup.normalizer (L : Set G) :=
  D.toCore.A_le_normalizer hA

theorem not_le_centralizer {A : Subgroup G} (hA : IsMaxElemAbelian T A)
    (hAc : ¬ ⁅L, A⁆ ≤ Subgroup.centralizer (VZ T X : Set G)) :
    ¬ A ≤ Subgroup.centralizer (VZ T X : Set G) :=
  D.toCore.not_le_centralizer hA hAc

theorem isFFStarOffender {A : Subgroup G} (hA : IsMaxElemAbelian T A)
    (hAc : ¬ ⁅L, A⁆ ≤ Subgroup.centralizer (VZ T X : Set G)) :
    IsFFStarOffender (autI D.elem X) (autI D.elem A) :=
  D.toCore.isFFStarOffender hA hAc

theorem secHyp {A : Subgroup G} (hA : IsMaxElemAbelian T A)
    (hAc : ¬ ⁅L, A⁆ ≤ Subgroup.centralizer (VZ T X : Set G)) :
    Bridge.SecHyp (autI D.elem L) (autI D.elem A) (intSub D.elem (blockU L))
      (intSub D.elem (blockZ L)) m := by
  have hV := D.elem
  have hLN := D.LN
  have hAn : A ≤ Subgroup.normalizer (L : Set G) := D.A_le_normalizer hA
  have hshort : IsShort2 L := D.block.1
  refine ⟨?_, nonempty_autI_equiv_alt hV hLN D.alt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases D.m_cases with h | h <;> omega
  ·
    intro a ha l hl
    obtain ⟨a₀, ha₀, rfl⟩ := (mem_autI hV).1 ha
    obtain ⟨l₀, hl₀, rfl⟩ := (mem_autI hV).1 hl
    have h1 : (a₀ : G) * (l₀ : G) * (a₀ : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.1 (hAn ha₀) (l₀ : G)).1 hl₀
    refine (mem_autI hV).2 ⟨a₀ * l₀ * a₀⁻¹, h1, ?_⟩
    rw [map_mul, map_mul, map_inv]
  ·
    by_contra hcon
    push Not at hcon
    apply hAc
    rw [Subgroup.commutator_le]
    intro l hl a ha
    have haN : a ∈ Subgroup.normalizer (VZ T X : Set G) := hA.1.trans D.TX |>.trans D.XN <| ha
    have hlN : l ∈ Subgroup.normalizer (VZ T X : Set G) := hLN hl
    have := hcon (convI hV ⟨a, haN⟩) (convI_mem_autI hV ha haN) (convI hV ⟨l, hlN⟩)
      (convI_mem_autI hV hl hlN)
    exact (convI_comm_iff hV hlN haN).1 this.symm
  · intro φ hφ
    obtain ⟨l, hl, rfl⟩ := (mem_autI hV).1 hφ
    exact convI_mem_stabSub_intSub hV l.2 (C1.le_normalizer_blockU L hl)
  · intro φ hφ
    obtain ⟨a, ha, rfl⟩ := (mem_autI hV).1 hφ
    exact convI_mem_stabSub_intSub hV a.2 (C1.mem_normalizer_blockU (hAn ha))
  · intro φ hφ
    obtain ⟨a, ha, rfl⟩ := (mem_autI hV).1 hφ
    exact convI_mem_stabSub_intSub hV a.2 (C1.mem_normalizer_blockZ (hAn ha))
  ·
    ext v
    rw [Subgroup.mem_inf, mem_intSub, mem_intSub, mem_fixV_autI hV hLN v]
    exact Subgroup.mem_inf
  · refine lt_of_le_of_ne (fun v hv => ?_) ?_
    · exact (inf_le_left : blockZ L ≤ blockU L) hv
    · intro h
      obtain ⟨u, huU, huZ⟩ := IsConcreteLE.exists_of_lt hshort.2.2.2.2.1
      have hmem : IntMod.mk hV ⟨u, D.uV huU⟩ ∈ intSub hV (blockU L) := huU
      rw [← h] at hmem
      exact huZ hmem
  · intro J hZJ hJU hJinv
    have hZV : blockZ L ≤ VZ T X := (inf_le_left : blockZ L ≤ blockU L).trans D.uV
    have hnorm : L ≤ Subgroup.normalizer (ambSub J : Set G) := by
      refine le_normalizer_of_forall_conj fun l hl w hw => ?_
      obtain ⟨v, hv, rfl⟩ := hw
      exact ⟨convI hV ⟨l, hLN hl⟩ v, hJinv _ (convI_mem_autI hV hl (hLN hl)) v hv,
        convI_apply_val hV _ v⟩
    rcases hshort.2.2.2.2.2 (ambSub J) (le_ambSub hZV hZJ) (ambSub_le hJU) hnorm with h | h
    · left; rw [← intSub_ambSub J, h]
    · right; rw [← intSub_ambSub J, h]
  · intro u hu
    have h1 : u.val ∈ blockU L := hu
    have h2 : ⁅L, blockU L⁆ = blockU L := by
      rw [Subgroup.commutator_comm]; exact C1.commutator_blockU hshort
    have hle : ⁅L, blockU L⁆ ≤ (commSub (intSub hV (blockU L)) (autI hV L)).map (valHom (VZ T X) hV) := by
      rw [Subgroup.commutator_def, Subgroup.closure_le]
      rintro _ ⟨l, hl, w, hw, rfl⟩
      refine ⟨convI hV ⟨l, hLN hl⟩ (IntMod.mk hV ⟨w, D.uV hw⟩) * (IntMod.mk hV ⟨w, D.uV hw⟩)⁻¹,
        ?_, ?_⟩
      · exact Subgroup.subset_closure ⟨convI hV ⟨l, hLN hl⟩, convI_mem_autI hV hl (hLN hl),
          IntMod.mk hV ⟨w, D.uV hw⟩, hw, rfl⟩
      · show (convI hV ⟨l, hLN hl⟩ (IntMod.mk hV ⟨w, D.uV hw⟩) * (IntMod.mk hV ⟨w, D.uV hw⟩)⁻¹).val =
          ⁅l, w⁆
        rw [IntMod.val_mul, IntMod.val_inv, convI_apply_val]
        rfl
    rw [h2] at hle
    obtain ⟨x, hx, hxu⟩ := hle h1
    have hxu' : x = u := IntMod.val_injective hxu
    rwa [← hxu']

end BlockData

end Block

end L246

end CFSG.QuasithinUnique

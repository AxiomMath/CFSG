module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.LeafBal
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4LayerA
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65Pump
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65Y

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Lift

variable {G : Type} [Group G] [Finite G]

abbrev CY (z w : G) (hzw : z ∈ centralizer ({w} : Set G)) :
    Subgroup ↥(centralizer ({w} : Set G)) :=
  centralizer ({(⟨z, hzw⟩ : ↥(centralizer ({w} : Set G)))} : Set ↥(centralizer ({w} : Set G)))

@[expose] def FY (z w : G) (hzw : z ∈ centralizer ({w} : Set G)) : ↥(CY z w hzw) →* G :=
  (centralizer ({w} : Set G)).subtype.comp (CY z w hzw).subtype

omit [Finite G] in
theorem FY_injective (z w : G) (hzw : z ∈ centralizer ({w} : Set G)) :
    Function.Injective (FY z w hzw) := fun _ _ h => Subtype.ext (Subtype.ext h)

abbrev CX (z w : G) (hzw : z ∈ centralizer ({w} : Set G)) :
    Subgroup (barQ ↥(centralizer ({w} : Set G))) :=
  centralizer ({sBar z w hzw} : Set (barQ ↥(centralizer ({w} : Set G))))

theorem isPCompIn_of_lift {z w : G} (hzw : z ∈ centralizer ({w} : Set G))
    {lift : Subgroup ↥(CY z w hzw)} (hl : TwoComponents.IsTwoComponent lift) :
    IsPCompIn 2 (centralizer ({z} : Set G) ⊓ centralizer ({w} : Set G))
      (lift.map (FY z w hzw)) := by
  set W := centralizer ({z} : Set G) ⊓ centralizer ({w} : Set G) with hW
  have hWY : W ≤ centralizer ({w} : Set G) := inf_le_right
  let e : ↥(CY z w hzw) ≃* ↥W :=
    (MulEquiv.subgroupCongr (centralizer_singleton_eq_subgroupOf hzw)).trans
      (Subgroup.subgroupOfEquivOfLe hWY)
  have he : ∀ x : ↥(CY z w hzw), ((e x : ↥W) : G) = FY z w hzw x := fun x => rfl
  have hle : lift.map (FY z w hzw) ≤ W := by
    rintro _ ⟨x, -, rfl⟩
    rw [← he]
    exact (e x).2
  have heq : (lift.map (FY z w hzw)).subgroupOf W = lift.map e.toMonoidHom := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_subgroupOf.mp hx
      refine ⟨y, hy, ?_⟩
      apply Subtype.ext
      rw [← he] at hyx
      exact hyx
    · rintro ⟨y, hy, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr ⟨y, hy, (he y).symm ▸ rfl⟩
  refine isPCompIn_two_iff.mpr ⟨hle, ?_⟩
  rw [heq]
  exact (TwoComponentTransport.equiv_iff e lift).mpr hl

end Lift

theorem even_card_of_quasisimple {Q : Type*} [Group Q] [Finite Q] (hQ : IsQuasisimple Q) :
    Even (Nat.card Q) := by
  by_contra h
  have hs : Group.IsSolvable Q := CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.not_even_iff_odd.1 h)
  have : Nontrivial Q := CFSG.LocalCores.isQuasisimple_nontrivial hQ
  have : Group.IsPerfect Q := hQ.1
  exact Group.IsPerfect.not_isSolvable Q hs

namespace Cfg65

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {t : G}

variable (h : Cfg65 G z S K₁ K₂ t)

include h

theorem ABar_unique (hII : II4_4_4_center) (hFS : FStar_C) (h327 : IG_3_27)
    {B : Subgroup (barQ ↥(centralizer ({t * z} : Set G)))}
    (hBle : B ≤ CX z (t * z) (h.z_mem_cent_tz hII))
    (hB : CFSG.IsComponent (B.subgroupOf (CX z (t * z) (h.z_mem_cent_tz hII)))) :
    B = ABar (IDiag t K₁) (t * z) := by
  have hM := h.m4 hII
  have hso : orderOf (⟨z, h.z_mem_cent_tz hII⟩ : ↥(centralizer ({t * z} : Set G))) = 2 :=
    orderOf_mk_centralizer (h.z_mem_cent_tz hII) h.std.orderOf_z
  have hBq : IsQuasisimple ↥B :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hBle) hB.1
  have hB2 : IsPCompIn 2 (CX z (t * z) (h.z_mem_cent_tz hII)) B :=
    ⟨hBle, CatFactsSp4.isPComponent_two_of_quasisimple' hBle hBq hB.2
      (even_card_of_quasisimple hBq)⟩
  have hB₀ : TwoComponents.IsTwoComponent (B.subgroupOf (CX z (t * z) (h.z_mem_cent_tz hII))) :=
    (isPCompIn_two_iff.mp hB2).2
  obtain ⟨lift, hlift2, hlift⟩ := OddKernelTwoComponents.exists_lift (barMkCentralizer hso)
    (barMkCentralizer_surjective hso) (odd_card_ker_barMkCentralizer hso)
    (B.subgroupOf (CX z (t * z) (h.z_mem_cent_tz hII))) hB₀
  have hP : IsPCompIn 2 (centralizer ({z} : Set G) ⊓ centralizer ({t * z} : Set G))
      (lift.map (FY z (t * z) (h.z_mem_cent_tz hII))) := isPCompIn_of_lift (h.z_mem_cent_tz hII) hlift2
  have hW : centralizer ({z} : Set G) ⊓ centralizer ({t * z} : Set G) =
      centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) := inf_cent_mul_eq.trans (inf_comm _ _)
  have hP' : IsPCompIn 2 (centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G))
      (lift.map (FY z (t * z) (h.z_mem_cent_tz hII))) := hW ▸ hP
  have hbal := le_pLayerOf_of_isPCompIn_inf h.orderOf_t (h.t_mem_cent hII) hP'
  have hK : pLayerOf 2 (centralizer ({z} : Set G)) ≤ K₁ ⊔ K₂ :=
    Sec7.Leaf.pLayerOf_Cz_le hII hFS h.std h.hQ
  have hB'K : lift.map (FY z (t * z) (h.z_mem_cent_tz hII)) ≤ K₁ ⊔ K₂ := hbal.trans hK
  have hB't : lift.map (FY z (t * z) (h.z_mem_cent_tz hII)) ≤ centralizer ({t} : Set G) :=
    hP'.1.trans inf_le_left
  have hconj : conjugate K₁ t = K₂ := h.t_swap.1
  have hB'D : lift.map (FY z (t * z) (h.z_mem_cent_tz hII)) ≤
      centralizer ({t} : Set G) ⊓ (K₁ ⊔ conjugate K₁ t) := by
    rw [hconj]
    exact le_inf hB't hB'K
  have hDW : centralizer ({t} : Set G) ⊓ (K₁ ⊔ conjugate K₁ t) ≤
      centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) := by
    rw [hconj]
    exact inf_le_inf_left _ (sup_le hM.K₁_le hM.K₂_le)
  have hPD : IsPCompIn 2 (centralizer ({t} : Set G) ⊓ (K₁ ⊔ conjugate K₁ t))
      (lift.map (FY z (t * z) (h.z_mem_cent_tz hII))) :=
    isPCompIn_two_iff.mpr ⟨hB'D, TwoComponentTransport.restrict_nested _ _ _ hB'D hDW
      (isPCompIn_two_iff.mp hP').2⟩
  have hBI : lift.map (FY z (t * z) (h.z_mem_cent_tz hII)) ≤ IDiag t K₁ := le_sSup hPD
  have hI0 : IsPCompIn 2 (centralizer ({z} : Set G) ⊓ centralizer ({t * z} : Set G)) (IDiag t K₁) :=
    h.I_isPCompIn hII h327
  have hI : IsPCompIn 2 (centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G)) (IDiag t K₁) :=
    hW ▸ hI0
  have hBeq : lift.map (FY z (t * z) (h.z_mem_cent_tz hII)) = IDiag t K₁ := by
    rcases eq_or_eq_of_isPCompIn_le_sup hI hI hP' (hBI.trans le_sup_left) with h1 | h1 <;> exact h1
  have hzw := h.z_mem_cent_tz hII
  have hIz : IDiag t K₁ ≤ centralizer ({z} : Set G) := hI0.1.trans inf_le_left
  have hlift_eq : lift = (IDiag t K₁).comap (FY z (t * z) hzw) := by
    ext x
    constructor
    · intro hx
      show FY z (t * z) hzw x ∈ IDiag t K₁
      rw [← hBeq]
      exact ⟨x, hx, rfl⟩
    · intro hx
      have hx' : FY z (t * z) hzw x ∈ lift.map (FY z (t * z) hzw) := by rw [hBeq]; exact hx
      obtain ⟨y, hy, hyx⟩ := hx'
      exact (FY_injective z (t * z) hzw hyx) ▸ hy
  have hAle := ABar_le_centralizer h.std.orderOf_z hzw hI0
  have hsub : B.subgroupOf (CX z (t * z) hzw) =
      (ABar (IDiag t K₁) (t * z)).subgroupOf (CX z (t * z) hzw) := by
    rw [← hlift, hlift_eq]
    ext c
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine Subgroup.mem_subgroupOf.mpr ⟨((x : ↥(CY z (t * z) hzw)) :
        ↥(centralizer ({t * z} : Set G))), hx, ?_⟩
      exact (barMkCentralizer_apply hso x).symm
    · intro hc
      obtain ⟨y, hy, hyc⟩ := Subgroup.mem_subgroupOf.mp hc
      have hyI : ((y : ↥(centralizer ({t * z} : Set G))) : G) ∈ IDiag t K₁ := hy
      have hyz : y ∈ CY z (t * z) hzw := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply Subtype.ext
        exact Subgroup.mem_centralizer_singleton_iff.1 (hIz hyI)
      refine ⟨⟨y, hyz⟩, hyI, ?_⟩
      apply Subtype.ext
      rw [barMkCentralizer_apply]
      exact hyc
  have := Subgroup.subgroupOf_inj.1 hsub
  rwa [inf_eq_left.2 hBle, inf_eq_left.2 hAle] at this

end Cfg65

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65

module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs

public section

namespace CFSG.HardMathSupport.Cooperstein.Proving

open CFSG.Open CFSG.AGLEmbedding

variable {G : Type} [Group G] {X Y L K : Subgroup G}

@[expose] noncomputable def barMHomOf (hLX : L ≤ X) : ↥L →* ↥X ⧸ CFSG.pCore 2 ↥X :=
  (QuotientGroup.mk' (CFSG.pCore 2 ↥X)).comp (Subgroup.inclusion hLX)

theorem barM_eq_map_barMHomOf (hLX : L ≤ X) (hKL : K ≤ L) :
    barM X K = (K.subgroupOf L).map (barMHomOf hLX) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x.1, hKL hx⟩, hx, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨Subgroup.inclusion hLX l, hl, rfl⟩

theorem ker_barMHomOf (hLX : L ≤ X) :
    (barMHomOf hLX).ker = (CFSG.Open.pCoreOf 2 X).subgroupOf L := by
  ext l
  rw [MonoidHom.mem_ker, barMHomOf, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, CFSG.Open.pCoreOf, Subgroup.mem_map]
  constructor
  · intro h
    exact ⟨Subgroup.inclusion hLX l, h, rfl⟩
  · rintro ⟨y, hy, hyl⟩
    have hy' : y = Subgroup.inclusion hLX l := Subtype.ext hyl
    exact hy' ▸ hy

@[expose] noncomputable def barMHomSub (hLX : L ≤ X) : ↥L →* ↥(barM X L) :=
  (barMHomOf hLX).codRestrict (barM X L) fun l =>
    Subgroup.mem_map.mpr ⟨Subgroup.inclusion hLX l, l.2, rfl⟩

theorem coe_barMHomSub (hLX : L ≤ X) (l : ↥L) :
    ((barMHomSub hLX l : ↥(barM X L)) : ↥X ⧸ CFSG.pCore 2 ↥X) =
      QuotientGroup.mk (Subgroup.inclusion hLX l) := rfl

theorem barMHomSub_surjective (hLX : L ≤ X) : Function.Surjective (barMHomSub hLX) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
  exact ⟨⟨x.1, hx⟩, Subtype.ext hxy⟩

theorem ker_barMHomSub (hLX : L ≤ X) :
    (barMHomSub hLX).ker = (CFSG.Open.pCoreOf 2 X).subgroupOf L := by
  rw [← ker_barMHomOf hLX]
  ext l
  simp only [MonoidHom.mem_ker]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem subgroupOf_eq_of_inf_eq {A B : Subgroup G} (h : L ⊓ A = L ⊓ B) :
    A.subgroupOf L = B.subgroupOf L := by
  ext l
  have hl := SetLike.ext_iff.mp h (l : G)
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact ⟨fun ha => (hl.mp ⟨l.2, ha⟩).2, fun hb => (hl.mpr ⟨l.2, hb⟩).2⟩

noncomputable def barMEquiv (hLX : L ≤ X) (hLY : L ≤ Y)
    (h : L ⊓ CFSG.Open.pCoreOf 2 X = L ⊓ CFSG.Open.pCoreOf 2 Y) :
    ↥(barM X L) ≃* ↥(barM Y L) :=
  (QuotientGroup.quotientKerEquivOfSurjective _ (barMHomSub_surjective hLX)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq
        ((ker_barMHomSub hLX).trans ((subgroupOf_eq_of_inf_eq h).trans (ker_barMHomSub hLY).symm))).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (barMHomSub_surjective hLY)))

theorem barMEquiv_apply (hLX : L ≤ X) (hLY : L ≤ Y)
    (h : L ⊓ CFSG.Open.pCoreOf 2 X = L ⊓ CFSG.Open.pCoreOf 2 Y) (l : ↥L) :
    barMEquiv hLX hLY h (barMHomSub hLX l) = barMHomSub hLY l := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective _ (barMHomSub_surjective hLX)).symm
      (barMHomSub hLX l) = (QuotientGroup.mk l : ↥L ⧸ (barMHomSub hLX).ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  unfold barMEquiv
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, h1, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem subgroupOf_barM_eq_map (hLX : L ≤ X) (hKL : K ≤ L) :
    (barM X K).subgroupOf (barM X L) = (K.subgroupOf L).map (barMHomSub hLX) := by
  ext ⟨y, hy⟩
  constructor
  · intro hy'
    rw [barM_eq_map_barMHomOf hLX hKL] at hy'
    obtain ⟨l, hl, hlY⟩ := Subgroup.mem_map.mp hy'
    exact ⟨l, hl, Subtype.ext hlY⟩
  · rintro ⟨l, hl, hlY⟩
    rw [Subgroup.mem_subgroupOf, barM_eq_map_barMHomOf hLX hKL]
    refine Subgroup.mem_map.mpr ⟨l, hl, ?_⟩
    exact congrArg Subtype.val hlY

theorem barMEquiv_map_subgroupOf (hLX : L ≤ X) (hLY : L ≤ Y)
    (h : L ⊓ CFSG.Open.pCoreOf 2 X = L ⊓ CFSG.Open.pCoreOf 2 Y) (hKL : K ≤ L) :
    ((barM X K).subgroupOf (barM X L)).map (barMEquiv hLX hLY h).toMonoidHom =
      (barM Y K).subgroupOf (barM Y L) := by
  have hcomp : (barMEquiv hLX hLY h).toMonoidHom.comp (barMHomSub hLX) = barMHomSub hLY :=
    MonoidHom.ext fun l => barMEquiv_apply hLX hLY h l
  rw [subgroupOf_barM_eq_map hLX hKL, subgroupOf_barM_eq_map hLY hKL, Subgroup.map_map, hcomp]

end CFSG.HardMathSupport.Cooperstein.Proving

end

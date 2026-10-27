module

public import CFSG.Quasithin.H13.A6S1372L76N
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76J
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76M
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76P

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge Matrix
open scoped Pointwise IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {S : Setting4 G T L V}

namespace Ctx76_F4
open CFSG.Quasithin.H13.A6.Setting4.Ctx76_F4

variable {H K : Subgroup G} [IsMulCommutative ↥(conjClosure S.V3 H)] {D : FFModel}

theorem fix_v2_of_T_F4 (C : S.Ctx76_F4 H K D) {m : D.Amb} (hm : m ∈ D.sec)
    (hxm : C.βU_F4 ⟨S.v2, S.v2_mem_UH H⟩ = QuotientGroup.mk ⟨m, hm⟩) {t : ↥K} (htT : (t : G) ∈ T) :
    D.act (C.α_F4 t) m * m⁻¹ ∈ D.ker := by
  have htv : (t : G) * S.v2 * (t : G)⁻¹ ∈ S.V2 :=
    (Subgroup.mem_normalizer_iff.mp (S.T_le_normalizer_V2 htT) _).mp S.v2_mem_V2
  have hU := C.conj_mem_UH_F4 t.2 (S.v2_mem_UH H)
  have h1 := C.βU_equiv_F4 t ⟨S.v2, S.v2_mem_UH H⟩ hU hm hxm
  have h2 : C.βU_F4 ⟨_, hU⟩ = C.βU_F4 ⟨S.v2, S.v2_mem_UH H⟩ := by
    rcases S.mem_V2_cosets htv with h | h
    · exfalso
      apply S.v2_not_mem_V1
      have e := S.conj_V1_of_mem C.hH (H.inv_mem (C.hKH_F4 t.2)) h
      rw [show (t : G)⁻¹ * ((t : G) * S.v2 * (t : G)⁻¹) * (t : G)⁻¹⁻¹ = S.v2 by group] at e
      rw [e]
      exact h
    · exact C.βU_eq_of_mul_mem_F4 hU (S.v2_mem_UH H) S.v2_mul_self h
  rw [h1, hxm, QuotientGroup.eq] at h2
  have h3 : (D.act (C.α_F4 t) m)⁻¹ * m ∈ D.ker := h2
  have h4 := D.ker.inv_mem h3
  rwa [_root_.mul_inv_rev, inv_inv, mul_comm] at h4

theorem isPGroup_αT_F4 (C : S.Ctx76_F4 H K D) : IsPGroup 2 ↥(((T ⊓ K).subgroupOf K).map C.α_F4) := by
  have hTs : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow C.hTH_F4
  have hKn : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer C.hKH_F4).mpr C.hHK
  have hTK : IsSylowTwoOf (T ⊓ K) K :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hTs C.hKH_F4 hKn.isSubnormal
  exact (hTK.2.1.comap_of_injective K.subtype K.subtype_injective).map C.α_F4

theorem not_two_dvd_index_αT_F4 (C : S.Ctx76_F4 H K D) :
    ¬ 2 ∣ (((T ⊓ K).subgroupOf K).map C.α_F4).index := by
  have hTs : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow C.hTH_F4
  have hKn : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer C.hKH_F4).mpr C.hHK
  have hTK : IsSylowTwoOf (T ⊓ K) K :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hTs C.hKH_F4 hKn.isSubnormal
  exact fun h => hTK.2.2 (h.trans (Subgroup.index_map_dvd _ C.α_surj_F4))

theorem exists_conj_fix_F4 [Finite D.Gam] (C : S.Ctx76_F4 H K D) {m : D.Amb} (hm : m ∈ D.sec)
    (hxm : C.βU_F4 ⟨S.v2, S.v2_mem_UH H⟩ = QuotientGroup.mk ⟨m, hm⟩) {X : Subgroup D.Gam}
    (hX : IsPGroup 2 X) : ∃ g : D.Gam, ∀ x ∈ X,
      D.act (g⁻¹ * x * g) m * m⁻¹ ∈ D.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 D.Gam := (C.isPGroup_αT_F4).toSylow C.not_two_dvd_index_αT_F4
  obtain ⟨Q, hXQ⟩ := hX.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq D.Gam P Q
  refine ⟨g, fun x hx => ?_⟩
  have hxQ : x ∈ (Q : Subgroup D.Gam) := hXQ hx
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxQ
  have hP : g⁻¹ * x * g ∈ ((T ⊓ K).subgroupOf K).map C.α_F4 := by
    have e : (MulAut.conj g)⁻¹ • x = g⁻¹ * x * g := by
      rw [← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv]
    rw [← e]
    exact (IsPGroup.mem_toSylow _ _).1 hxQ
  obtain ⟨t, ht, hte⟩ := hP
  rw [← hte]
  exact C.fix_v2_of_T_F4 hm hxm (Subgroup.mem_subgroupOf.1 ht).1

theorem false_extSq5_F4 (h13314 : Stmt13_3_14_F4)
    (C : S.Ctx76_F4 H K (FFModel.extSq (ZMod 2) 5)) : False := by
  have : Finite (FFModel.extSq (ZMod 2) 5).Gam :=
    inferInstanceAs (Finite ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)))
  obtain ⟨m, hxm⟩ := QuotientGroup.mk_surjective (C.βU_F4 ⟨S.v2, S.v2_mem_UH H⟩)
  set x : Multiplicative (⋀[ZMod 2]^2 (Fin 5 → ZMod 2)) := m.1 with hx
  have hact : ∀ y : (FFModel.extSq (ZMod 2) 5).Gam,
      (FFModel.extSq (ZMod 2) 5).act y m.1 * m.1⁻¹ ∈ (FFModel.extSq (ZMod 2) 5).ker →
      extSqAct (ZMod 2) 5 y x = x := by
    intro y hy
    exact mul_inv_eq_one.1 ((Subgroup.mem_bot).1 hy)
  obtain ⟨g, hg⟩ : ∃ g : ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)), ∀ y ∈
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 5 (ZMod 2)).map
        (A6L76N.slHom 5 (ZMod 2)), extSqAct (ZMod 2) 5 (g⁻¹ * y * g) x = x := by
    obtain ⟨g, hg⟩ := C.exists_conj_fix_F4 m.2 hxm.symm (A6L76N.isPGroup_U 5)
    exact ⟨g, fun y hy => hact _ (hg y hy)⟩
  set w := extSqAct (ZMod 2) 5 g x with hw
  have hfixw : ∀ (i j : Fin 5) (h : i < j),
      extSqAct (ZMod 2) 5 (A6L76N.slHom 5 (ZMod 2) (A6L76N.tv i j h.ne)) w = w := by
    intro i j h
    have h1 := hg _ (Subgroup.mem_map_of_mem _ (A6L76N.tv_mem h))
    rw [extSqAct_mul_act, extSqAct_mul_act] at h1
    rw [hw, ← CFSG.Quasithin.H13.A6.Setting4.Ctx76.extSqAct_act_inv g (extSqAct (ZMod 2) 5 _ (extSqAct (ZMod 2) 5 g x)), h1]
  set y := JonesParshall.wedgeCoord (Multiplicative.toAdd w) with hy
  have hcoord : ∀ (a : ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)))
      (z : Multiplicative (⋀[ZMod 2]^2 (Fin 5 → ZMod 2))),
      JonesParshall.wedgeCoord (Multiplicative.toAdd (extSqAct (ZMod 2) 5 a z)) =
        JonesParshall.wedgeMat ((a : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ
          JonesParshall.wedgeCoord (Multiplicative.toAdd z) := fun a z =>
    JonesParshall.wedgeCoord_map _ _
  have hinj : ∀ z z' : Multiplicative (⋀[ZMod 2]^2 (Fin 5 → ZMod 2)),
      JonesParshall.wedgeCoord (Multiplicative.toAdd z) =
        JonesParshall.wedgeCoord (Multiplicative.toAdd z') → z = z' := fun z z' h =>
    Multiplicative.toAdd.injective (JonesParshall.wedgeCoord_bijective.1 h)
  have hU : ∀ (i j : Fin 5) (h : i < j),
      JonesParshall.wedgeMat (Matrix.transvection i j (1 : ZMod 2)) *ᵥ y = y := by
    intro i j h
    have := congrArg (fun z => JonesParshall.wedgeCoord (Multiplicative.toAdd z)) (hfixw i j h)
    simp only [hcoord] at this
    exact this
  rcases A6L76N.fixU5 y (hU 0 1 (by decide)) (hU 1 2 (by decide)) (hU 2 3 (by decide))
    (hU 3 4 (by decide)) with h0 | h01
  · apply C.βU_v2_ne_one_F4
    have hw1 : w = 1 := hinj w 1 (by rw [← hy, h0]; simp)
    have hx1 : x = 1 := by
      rw [← CFSG.Quasithin.H13.A6.Setting4.Ctx76.extSqAct_inv_act g x, ← hw, hw1, CFSG.Quasithin.H13.A6.Setting4.Ctx76.extSqAct_one_right]
    rw [← hxm, show m = 1 from Subtype.ext hx1, QuotientGroup.mk_one]
  · have h2 : (2 : ZMod 2) = 0 := rfl
    have hE := (A6L76M.e9_rot h2 (p := (0 : Fin 5)) (q := 1) (r := 2) (s := 3) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).map
        (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
    obtain ⟨hr1, hr2⟩ := A6L76N.rot_fix5
    have hfix : ∀ (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) (hM : M.det = 1),
        JonesParshall.wedgeMat M *ᵥ Pi.single 0 1 = Pi.single 0 1 →
        (FFModel.extSq (ZMod 2) 5).act ((MulAut.conj g⁻¹).toMonoidHom (A6L76M.slOf M hM)) m.1 *
          m.1⁻¹ ∈ (FFModel.extSq (ZMod 2) 5).ker := by
      intro M hM hMf
      refine (Subgroup.mem_bot).2 (mul_inv_eq_one.2 ?_)
      show extSqAct (ZMod 2) 5 (g⁻¹ * A6L76M.slOf M hM * g⁻¹⁻¹) x = x
      rw [inv_inv, extSqAct_mul_act, extSqAct_mul_act, ← hw]
      have hw' : extSqAct (ZMod 2) 5 (A6L76M.slOf M hM) w = w := by
        apply hinj
        rw [hcoord, ← hy, h01]
        exact hMf
      rw [hw', hw, CFSG.Quasithin.H13.A6.Setting4.Ctx76.extSqAct_inv_act]
    exact C.not_e9_F4 h13314 m.2 hxm.symm hE (hfix _ _ hr1) (hfix _ _ hr2)

theorem false_extSq4_F4 (h13314 : Stmt13_3_14_F4)
    (C : S.Ctx76_F4 H K (FFModel.extSq (ZMod 2) 4)) : False := by
  have : Finite (FFModel.extSq (ZMod 2) 4).Gam :=
    inferInstanceAs (Finite ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)))
  obtain ⟨m, hxm⟩ := QuotientGroup.mk_surjective (C.βU_F4 ⟨S.v2, S.v2_mem_UH H⟩)
  set x : Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2)) := m.1 with hx
  have hact : ∀ y : (FFModel.extSq (ZMod 2) 4).Gam,
      (FFModel.extSq (ZMod 2) 4).act y m.1 * m.1⁻¹ ∈ (FFModel.extSq (ZMod 2) 4).ker →
      extSqAct (ZMod 2) 4 y x = x := by
    intro y hy
    exact mul_inv_eq_one.1 ((Subgroup.mem_bot).1 hy)
  obtain ⟨g, hg⟩ : ∃ g : ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)), ∀ y ∈
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 4 (ZMod 2)).map
        (A6L76N.slHom 4 (ZMod 2)), extSqAct (ZMod 2) 4 (g⁻¹ * y * g) x = x := by
    obtain ⟨g, hg⟩ := C.exists_conj_fix_F4 m.2 hxm.symm (A6L76N.isPGroup_U 4)
    exact ⟨g, fun y hy => hact _ (hg y hy)⟩
  set w := extSqAct (ZMod 2) 4 g x with hw
  have hfixw : ∀ (i j : Fin 4) (h : i < j),
      extSqAct (ZMod 2) 4 (A6L76N.slHom 4 (ZMod 2) (A6L76N.tv i j h.ne)) w = w := by
    intro i j h
    have h1 := hg _ (Subgroup.mem_map_of_mem _ (A6L76N.tv_mem h))
    rw [extSqAct_mul_act, extSqAct_mul_act] at h1
    rw [hw, ← CFSG.Quasithin.H13.A6.Setting4.Ctx76.extSqAct_act_inv g (extSqAct (ZMod 2) 4 _ (extSqAct (ZMod 2) 4 g x)), h1]
  set y := B5FinWedge.wedgeCoord4 (Multiplicative.toAdd w) with hy
  have hcoord : ∀ (a : ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)))
      (z : Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))),
      B5FinWedge.wedgeCoord4 (Multiplicative.toAdd (extSqAct (ZMod 2) 4 a z)) =
        B5FinWedge.wedgeMat4 ((a : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
          B5FinWedge.wedgeCoord4 (Multiplicative.toAdd z) := fun a z =>
    B5FinWedge.wedgeCoord4_map _ _
  have hinj : ∀ z z' : Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2)),
      B5FinWedge.wedgeCoord4 (Multiplicative.toAdd z) =
        B5FinWedge.wedgeCoord4 (Multiplicative.toAdd z') → z = z' := fun z z' h =>
    Multiplicative.toAdd.injective (B5FinWedge.wedgeCoord4_bijective.1 h)
  have hU : ∀ (i j : Fin 4) (h : i < j),
      B5FinWedge.wedgeMat4 (Matrix.transvection i j (1 : ZMod 2)) *ᵥ y = y := by
    intro i j h
    have := congrArg (fun z => B5FinWedge.wedgeCoord4 (Multiplicative.toAdd z)) (hfixw i j h)
    simp only [hcoord] at this
    exact this
  rcases A6L76N.fixU4 y (hU 0 1 (by decide)) (hU 1 2 (by decide)) (hU 2 3 (by decide))
    with h0 | h01
  · apply C.βU_v2_ne_one_F4
    have hw1 : w = 1 := hinj w 1 (by rw [← hy, h0]; simp)
    have hx1 : x = 1 := by
      rw [← CFSG.Quasithin.H13.A6.Setting4.Ctx76.extSqAct_inv_act g x, ← hw, hw1, CFSG.Quasithin.H13.A6.Setting4.Ctx76.extSqAct_one_right]
    rw [← hxm, show m = 1 from Subtype.ext hx1, QuotientGroup.mk_one]
  · have h2 : (2 : ZMod 2) = 0 := rfl
    have hE := (A6L76M.e9_rot h2 (p := (0 : Fin 4)) (q := 1) (r := 2) (s := 3) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).map
        (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
    obtain ⟨hr1, hr2⟩ := A6L76N.rot_fix4
    have hfix : ∀ (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (hM : M.det = 1),
        B5FinWedge.wedgeMat4 M *ᵥ Pi.single 0 1 = Pi.single 0 1 →
        (FFModel.extSq (ZMod 2) 4).act ((MulAut.conj g⁻¹).toMonoidHom (A6L76M.slOf M hM)) m.1 *
          m.1⁻¹ ∈ (FFModel.extSq (ZMod 2) 4).ker := by
      intro M hM hMf
      refine (Subgroup.mem_bot).2 (mul_inv_eq_one.2 ?_)
      show extSqAct (ZMod 2) 4 (g⁻¹ * A6L76M.slOf M hM * g⁻¹⁻¹) x = x
      rw [inv_inv, extSqAct_mul_act, extSqAct_mul_act, ← hw]
      have hw' : extSqAct (ZMod 2) 4 (A6L76M.slOf M hM) w = w := by
        apply hinj
        rw [hcoord, ← hy, h01]
        exact hMf
      rw [hw', hw, CFSG.Quasithin.H13.A6.Setting4.Ctx76.extSqAct_inv_act]
    exact C.not_e9_F4 h13314 m.2 hxm.symm hE (hfix _ _ hr1) (hfix _ _ hr2)

end Ctx76_F4

variable (S)
include S

theorem lem1376_two_F4 (hB : Lem1376L1K_F4) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h13314 : Stmt13_3_14_F4) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
    (hNS : ¬ LieModel G .PSp 3 2 1) (hNU : ¬ LieModel G .PSU 4 3 1) {H : Subgroup G}
    (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
    [IsMulCommutative ↥(conjClosure S.V3 H)] {K : Subgroup G} (hK : K ∈ cComp H) :
    ¬ SLExteriorTwo (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 5 := by
  intro h5
  have hL1K := hB G T L V S hNS hNU H hH hab K hK (Or.inr (Or.inl h5))
  have : IsSimpleGroup (FFModel.extSq (ZMod 2) 5).Gam :=
    A6L76A.isSimpleGroup_statedSL (by norm_num) (Nat.card_zmod 2)
  obtain ⟨C⟩ := S.exists_ctx_F4 h37 h38 h13315 h1356two hNS hH hab hK hL1K
    (A6L76A.not_isSolvable_statedSL (by norm_num)) h5
  exact Ctx76_F4.false_extSq5_F4 h13314 C

theorem lem1376_extSq4_F4 (hB : Lem1376L1K_F4) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h13314 : Stmt13_3_14_F4) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
    (hNS : ¬ LieModel G .PSp 3 2 1) (hNU : ¬ LieModel G .PSU 4 3 1) {H : Subgroup G}
    (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
    [IsMulCommutative ↥(conjClosure S.V3 H)] {K : Subgroup G} (hK : K ∈ cComp H) :
    ¬ SLExteriorTwo (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 4 := by
  intro h4
  have hL1K := hB G T L V S hNS hNU H hH hab K hK (Or.inr (Or.inr (Or.inr (Or.inl h4))))
  have : IsSimpleGroup (FFModel.extSq (ZMod 2) 4).Gam :=
    A6L76A.isSimpleGroup_statedSL (by norm_num) (Nat.card_zmod 2)
  obtain ⟨C⟩ := S.exists_ctx_F4 h37 h38 h13315 h1356two hNS hH hab hK hL1K
    (A6L76A.not_isSolvable_statedSL (by norm_num)) h4
  exact Ctx76_F4.false_extSq4_F4 h13314 C

theorem lem1376_one_le_four_F4 (hB : Lem1376L1K_F4) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h13314 : Stmt13_3_14_F4) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
    (hNS : ¬ LieModel G .PSp 3 2 1) (hNU : ¬ LieModel G .PSU 4 3 1) {H : Subgroup G}
    (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
    [IsMulCommutative ↥(conjClosure S.V3 H)] {K : Subgroup G} (hK : K ∈ cComp H) (n : ℕ)
    (hn : 3 ≤ n)
    (hBN : BinaryNaturalSL (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) n 1) : n ≤ 4 := by
  by_contra h5
  have hL1K := hB G T L V S hNS hNU H hH hab K hK (Or.inl ⟨n, hn, hBN⟩)
  obtain ⟨F, _, _, hF, hR⟩ := hBN
  have hF2 : Nat.card F = 2 := by rw [hF, pow_one]
  have : IsSimpleGroup (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL n F)).Gam :=
    A6L76A.isSimpleGroup_statedSL hn hF2
  obtain ⟨C⟩ := S.exists_ctx_F4 h37 h38 h13315 h1356two hNS hH hab hK hL1K
    (A6L76A.not_isSolvable_statedSL hn) hR
  exact Ctx76_F4.false_nat_ge_five_F4 h13314 hF2 (by omega) C

end Setting4

end CFSG.Quasithin.H13.A6

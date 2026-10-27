module

public import CFSG.Quasithin.H13.A6S1372Twelve
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S13721b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372Eleven

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {S : Setting4 G T L V}

section NonAb

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

omit hab in

theorem QH_le_NV_F4 :
    pCoreOf 2 H ≤ Subgroup.normalizer (V : Set G) :=
  (S.QH_le_T_F4 hNS h13315 h1356two hH).trans S.frame.T_le

omit hab in

theorem relIndex_QH_le_eight_F4 :
    (pCoreOf 2 H ⊓ Subgroup.centralizer (V : Set G)).relIndex (pCoreOf 2 H) ≤ 8 := by
  have hQN := S.QH_le_NV_F4 hNS h13315 h1356two hH
  set φ : ↥(pCoreOf 2 H) →* Perm (Fin 6) := S.frame.ρ.comp (Subgroup.inclusion hQN) with hφ
  have hker : (pCoreOf 2 H ⊓ Subgroup.centralizer (V : Set G)).subgroupOf (pCoreOf 2 H) =
      φ.ker := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro hx
      exact (S.rho_eq_one_iff _).2 hx.2
    · intro hx
      exact ⟨x.2, (S.rho_eq_one_iff _).1 hx⟩
  have h1 : φ.ker.index = Nat.card φ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have hrange : φ.range ≤ A6Twelve.R8sub := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨hxN, hx⟩ := S.rho_QH_mem_R8_F4 hNS h13315 h1356two hH x.2
    exact hx
  rw [Subgroup.relIndex, hker, h1]
  exact (Subgroup.card_le_of_le hrange).trans A6Twelve.card_R8sub.le

namespace Conf

variable (C : S.Conf H)

theorem v_mem_QC_F4 :
    (C.v : G) ∈ pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G) :=
  ⟨S.VH_le_QH_F4 hNS h13315 h1356two hH hab C.v_mem,
    S.VH_le_centralizer_UH_F4 hNS h13315 h1356two hH hab C.v_mem⟩

include C in

theorem two_le_relIndex_sup_F4 :
    2 ≤ (pCoreOf 2 H ⊓ Subgroup.centralizer (V : Set G)).relIndex
      ((pCoreOf 2 H ⊓ Subgroup.centralizer (V : Set G)) ⊔
        (pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G))) := by
  have h0 : (pCoreOf 2 H ⊓ Subgroup.centralizer (V : Set G)).relIndex
      ((pCoreOf 2 H ⊓ Subgroup.centralizer (V : Set G)) ⊔
        (pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G))) ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have h1 : (pCoreOf 2 H ⊓ Subgroup.centralizer (V : Set G)).relIndex
      ((pCoreOf 2 H ⊓ Subgroup.centralizer (V : Set G)) ⊔
        (pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G))) ≠ 1 := by
    intro h
    rw [Subgroup.relIndex_eq_one] at h
    have hv := h (Subgroup.mem_sup_right (C.v_mem_QC_F4 hNS h13315 h1356two hH hab))
    exact C.v_not_mem_W ⟨C.v_mem, hv.2⟩
  omega

include C in

theorem relIndex_sup_le_four_F4 :
    ((pCoreOf 2 H ⊓ Subgroup.centralizer (V : Set G)) ⊔
        (pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G))).relIndex
      (pCoreOf 2 H) ≤ 4 := by
  have h := Subgroup.relIndex_mul_relIndex (pCoreOf 2 H ⊓ Subgroup.centralizer (V : Set G))
    ((pCoreOf 2 H ⊓ Subgroup.centralizer (V : Set G)) ⊔
      (pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G))) (pCoreOf 2 H)
    le_sup_left (sup_le inf_le_left inf_le_left)
  have h8 := S.relIndex_QH_le_eight_F4 hNS h13315 h1356two hH
  have h2 := C.two_le_relIndex_sup_F4 hNS h13315 h1356two hH hab
  rw [← h] at h8
  by_contra hc
  push Not at hc
  have : 2 * 5 ≤ _ := Nat.mul_le_mul h2 hc
  omega

end Conf

theorem card_mul_card_centralizer_F4 {X : Subgroup G}
    (hX : X ≤ pCoreOf 2 H) :
    Nat.card X * Nat.card ↥(conjClosure S.V3 H ⊓ Subgroup.centralizer (X : Set G)) =
      Nat.card (conjClosure S.V3 H) *
        Nat.card ↥(X ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G)) := by
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  have hV₁ : IsElemAbelian 2 (fsuV1 T V) := F7.isElemAbelian_mono hF.elemAbelian hF.V₁_le_V
  let _ : CommGroup ↥(conjClosure S.V3 H) := commGroupOfElemAbelian hab
  let _ : CommGroup ↥(fsuV1 T V) := commGroupOfElemAbelian hV₁
  have hB : ∀ u : ↥(conjClosure S.V3 H), u ^ 2 = 1 := fun u => Subtype.ext (by
    simpa using hab.2 u u.2)
  let β : ↥X → ↥(conjClosure S.V3 H) → ↥(fsuV1 T V) := fun x u =>
    ⟨x * u * x⁻¹ * u⁻¹, hF.commutator_mem_V₁ (hX x.2) u.2⟩
  have h1 : ∀ x₁ x₂ u, β (x₁ * x₂) u = β x₁ u * β x₂ u := fun x₁ x₂ u =>
    Subtype.ext (hF.commutator_mul_left (hX x₁.2) (hX x₂.2) u.2)
  have h2 : ∀ x u₁ u₂, β x (u₁ * u₂) = β x u₁ * β x u₂ := fun x u₁ u₂ =>
    Subtype.ext (hF.commutator_mul_right (hX x.2) u₁.2 u₂.2)
  have key := card_mul_card_radical_eq hB hF.card_V₁ β h1 h2
  have hcomm : ∀ (x u : G), x * u * x⁻¹ * u⁻¹ = 1 ↔ x * u = u * x := fun x u => by
    constructor
    · intro e
      calc x * u = (x * u * x⁻¹ * u⁻¹) * u * x := by group
        _ = u * x := by rw [e]; group
    · intro e
      calc x * u * x⁻¹ * u⁻¹ = (u * x) * x⁻¹ * u⁻¹ := by rw [e]
        _ = 1 := by group
  have c1 : Nat.card {b : ↥(conjClosure S.V3 H) // ∀ a, β a b = 1} =
      Nat.card ↥(conjClosure S.V3 H ⊓ Subgroup.centralizer (X : Set G)) := by
    refine Nat.card_congr
      { toFun := fun b => ⟨b.1, b.1.2, Subgroup.mem_centralizer_iff.mpr fun x hx => by
          have := congrArg Subtype.val (b.2 ⟨x, hx⟩)
          exact (hcomm x b.1).mp this⟩
        invFun := fun b => ⟨⟨b.1, b.2.1⟩, fun a => Subtype.ext (by
          show (a : G) * b.1 * (a : G)⁻¹ * b.1⁻¹ = 1
          exact (hcomm a b.1).mpr (Subgroup.mem_centralizer_iff.mp b.2.2 a a.2))⟩
        left_inv := fun b => rfl
        right_inv := fun b => rfl }
  have c2 : Nat.card {a : ↥X // ∀ b, β a b = 1} =
      Nat.card ↥(X ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G)) := by
    refine Nat.card_congr
      { toFun := fun a => ⟨a.1, a.1.2, Subgroup.mem_centralizer_iff.mpr fun u hu => by
          have := congrArg Subtype.val (a.2 ⟨u, hu⟩)
          exact ((hcomm a.1 u).mp this).symm⟩
        invFun := fun a => ⟨⟨a.1, a.2.1⟩, fun b => Subtype.ext (by
          show (a.1 : G) * b * (a.1 : G)⁻¹ * (b : G)⁻¹ = 1
          exact (hcomm a.1 b).mpr (Subgroup.mem_centralizer_iff.mp a.2.2 b b.2).symm)⟩
        left_inv := fun a => rfl
        right_inv := fun a => rfl }
  rw [c1, c2] at key
  exact key

theorem relIndex_centralizer_eq_F4 {X : Subgroup G}
    (hX : X ≤ pCoreOf 2 H) :
    (conjClosure S.V3 H ⊓ Subgroup.centralizer (X : Set G)).relIndex (conjClosure S.V3 H) =
      (X ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G)).relIndex X := by
  have key := S.card_mul_card_centralizer_F4 hNS h13315 h1356two hH hab hX
  have e1 := Subgroup.relIndex_mul_card
    (conjClosure S.V3 H ⊓ Subgroup.centralizer (X : Set G)) (conjClosure S.V3 H)
  have e2 := Subgroup.relIndex_mul_card (X ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G)) X
  rw [inf_eq_left.mpr inf_le_left] at e1 e2
  have hn : 0 < Nat.card ↥(conjClosure S.V3 H ⊓ Subgroup.centralizer (X : Set G)) := Nat.card_pos
  have hr : 0 < Nat.card ↥(X ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G)) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hn hr)
  calc (conjClosure S.V3 H ⊓ Subgroup.centralizer (X : Set G)).relIndex (conjClosure S.V3 H) *
        (Nat.card ↥(conjClosure S.V3 H ⊓ Subgroup.centralizer (X : Set G)) *
          Nat.card ↥(X ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G))) =
        ((conjClosure S.V3 H ⊓ Subgroup.centralizer (X : Set G)).relIndex (conjClosure S.V3 H) *
          Nat.card ↥(conjClosure S.V3 H ⊓ Subgroup.centralizer (X : Set G))) *
          Nat.card ↥(X ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G)) := by ring
    _ = Nat.card (conjClosure S.V3 H) *
          Nat.card ↥(X ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G)) := by rw [e1]
    _ = Nat.card X * Nat.card ↥(conjClosure S.V3 H ⊓ Subgroup.centralizer (X : Set G)) :=
        key.symm
    _ = ((X ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G)).relIndex X *
          Nat.card ↥(X ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G))) *
          Nat.card ↥(conjClosure S.V3 H ⊓ Subgroup.centralizer (X : Set G)) := by rw [e2]
    _ = (X ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G)).relIndex X *
          (Nat.card ↥(conjClosure S.V3 H ⊓ Subgroup.centralizer (X : Set G)) *
            Nat.card ↥(X ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G))) := by ring

omit hab in

theorem V1_le_centralizer_QH_F4 :
    fsuV1 T V ≤ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have h := hF.conj_eq_of_mem_V₁ (pCoreOf_le 2 H hq) ht
  calc q * t = q * t * q⁻¹ * q := by group
    _ = t * q := by rw [h]

omit hab in

theorem V1_le_U0_F4 :
    fsuV1 T V ≤ conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) :=
  le_inf S.V1_le_UH (S.V1_le_centralizer_QH_F4 hNS h13315 h1356two hH)

omit hab in

theorem V3_inf_U0_F4 (h13314 : Stmt13_3_14_F4) :
    S.V3 ⊓ (conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) = fsuV1 T V := by
  refine le_antisymm (fun w hw => ?_) (le_inf (S.V1_le_V2.trans S.V2_le_V3)
    (S.V1_le_U0_F4 hNS h13315 h1356two hH))
  refine S.mem_V1_of_fix_QH_F4 hNS h13315 h1356two hH h13314 hw.1 fun q hq => ?_
  have h := Subgroup.mem_centralizer_iff.mp hw.2.2 q hq
  rw [h, mul_inv_cancel_right]

theorem relIndex_U0_sup_F4 (h13314 : Stmt13_3_14_F4) :
    (conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)).relIndex
      (S.V3 ⊔ (conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G))) = 4 := by
  set U₀ := conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) with hU₀
  have hN : S.V3 ≤ Subgroup.normalizer (U₀ : Set G) := by
    refine A5.le_normalizer_of_forall_conj_mem fun v hv u hu => ?_
    have hc := F7.isElemAbelian_comm hab (le_conjClosure _ _ hv) hu.1
    rw [hc, mul_inv_cancel_right]
    exact hu
  have hprod := card_sup_mul_card_inf' hN
  rw [S.V3_inf_U0_F4 hNS h13315 h1356two hH h13314, S.card_V1, S.card_V3] at hprod
  have r := Subgroup.relIndex_mul_card U₀ (S.V3 ⊔ U₀)
  rw [inf_eq_left.mpr le_sup_right] at r
  have hpos : 0 < Nat.card U₀ := Nat.card_pos
  have h4 : Nat.card ↥(S.V3 ⊔ U₀) = 4 * Nat.card U₀ := by omega
  rw [h4] at r
  exact Nat.eq_of_mul_eq_mul_right hpos r

namespace Conf

variable (C : S.Conf H)

include C in

theorem centralizer_X_eq_F4 (h13314 : Stmt13_3_14_F4) :
    conjClosure S.V3 H ⊓
        Subgroup.centralizer ((pCoreOf 2 H ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) :
          Set G) =
      S.V3 ⊔ (conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) := by
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  set X := pCoreOf 2 H ⊓ Subgroup.centralizer (V : Set G) with hXdef
  set QC := pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G) with hQC
  set U₀ := conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) with hU₀
  set N := conjClosure S.V3 H ⊓ Subgroup.centralizer (X : Set G) with hN
  have hX : X ≤ pCoreOf 2 H := inf_le_left
  have hle := S.V3_sup_U0_le (H := H)

  have i1 := S.relIndex_centralizer_eq_F4 hNS h13315 h1356two hH hab hX
  have i2 := S.relIndex_inf_centralizer hX
  have i3 := hF.F97_relIndex hab
  have i4 := Subgroup.relIndex_mul_relIndex QC (X ⊔ QC) (pCoreOf 2 H) le_sup_right
    (sup_le hX inf_le_left)
  have i5 := C.relIndex_sup_le_four_F4 hNS h13315 h1356two hH hab
  have i6 := Subgroup.relIndex_mul_relIndex U₀ (S.V3 ⊔ U₀) (conjClosure S.V3 H) le_sup_right
    (sup_le (le_conjClosure _ _) inf_le_left)
  rw [S.relIndex_U0_sup_F4 hNS h13315 h1356two hH hab h13314] at i6
  have key : (S.V3 ⊔ U₀).relIndex (conjClosure S.V3 H) ≤ N.relIndex (conjClosure S.V3 H) := by
    have h1 : U₀.relIndex (conjClosure S.V3 H) ≤ N.relIndex (conjClosure S.V3 H) * 4 := by
      rw [← i3, ← i4, ← i2, ← i1]
      exact Nat.mul_le_mul_left _ i5
    omega

  have hNU : N ≤ conjClosure S.V3 H := inf_le_left
  have e1 := Subgroup.relIndex_mul_card N (conjClosure S.V3 H)
  rw [inf_eq_left.mpr hNU] at e1
  have e2 := Subgroup.relIndex_mul_card (S.V3 ⊔ U₀) (conjClosure S.V3 H)
  rw [inf_eq_left.mpr (hle.trans hNU)] at e2
  have hpos : 0 < N.relIndex (conjClosure S.V3 H) :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hcard : Nat.card N ≤ Nat.card ↥(S.V3 ⊔ U₀) := by
    by_contra hc
    push Not at hc
    have := Nat.mul_lt_mul_of_le_of_lt key hc hpos
    rw [e1, e2] at this
    exact lt_irrefl _ this
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

section Hat

variable (hhat : ¬ IsHatA6 L)
include hhat

omit hab in

theorem conj_X_A_mem_F4 {x a : G} (hxQ : x ∈ pCoreOf 2 H)
    (hxV : x ∈ Subgroup.centralizer (V : Set G)) (ha : a ∈ C.A) : x * a * x⁻¹ ∈ C.A := by
  have hxLT : x ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) :=
    ⟨le_sup_right (a := L) (S.QH_le_T_F4 hNS h13315 h1356two hH hxQ), hxV⟩
  have h1 := C.cLT_le_normalizer_VHg_F4 hNS h13315 h1356two hH hhat hxLT
  exact ⟨(Subgroup.mem_normalizer_iff.mp h1 a).mp ha.1,
    (Subgroup.centralizer (V : Set G)).mul_mem ((Subgroup.centralizer (V : Set G)).mul_mem hxV
      ha.2) ((Subgroup.centralizer (V : Set G)).inv_mem hxV)⟩

theorem comm_X_A_mem_ZI_F4
    (hna : ¬ IsElemAbelian 2 (conjClosure V H)) (h13314 : Stmt13_3_14_F4) {x a : G}
    (hxQ : x ∈ pCoreOf 2 H) (hxV : x ∈ Subgroup.centralizer (V : Set G)) (ha : a ∈ C.A) :
    x * a * x⁻¹ * a⁻¹ ∈ C.ZI := by
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  have haH : a ∈ H := hF.T_le_H (C.A_le_T_F4 hNS h13315 h1356two hH hab hhat ha)
  rw [← C.A_inf_QH_F4 hNS h13315 h1356two hH hab hhat hna h13314]
  refine ⟨C.A.mul_mem (C.conj_X_A_mem_F4 hNS h13315 h1356two hH hhat hxQ hxV ha) (C.A.inv_mem ha),
    ?_⟩
  have h1 : a * x⁻¹ * a⁻¹ ∈ pCoreOf 2 H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H haH) _).mp
      ((pCoreOf 2 H).inv_mem hxQ)
  have e : x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) := by group
  rw [e]
  exact (pCoreOf 2 H).mul_mem hxQ h1

theorem comm_X_comm_F4
    (hna : ¬ IsElemAbelian 2 (conjClosure V H)) (h13314 : Stmt13_3_14_F4) {x u a : G}
    (hxQ : x ∈ pCoreOf 2 H) (hxV : x ∈ Subgroup.centralizer (V : Set G))
    (hu : u ∈ conjClosure S.V3 H) (ha : a ∈ C.A) :
    x * (a * u * a⁻¹ * u⁻¹) = (a * u * a⁻¹ * u⁻¹) * x := by
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  have haH : a ∈ H := hF.T_le_H (C.A_le_T_F4 hNS h13315 h1356two hH hab hhat ha)
  have hxH : x ∈ H := pCoreOf_le 2 H hxQ
  have huH : u ∈ H := pCoreOf_le 2 H (hF.conjClosure_Vp_le_pCoreOf hu)

  have he : a⁻¹ * x * a * x⁻¹ ∈ C.ZI := by
    have h := C.comm_X_A_mem_ZI_F4 hNS h13315 h1356two hH hab hhat hna h13314 hxQ hxV
      (C.A.inv_mem ha)
    have e : a⁻¹ * x * a * x⁻¹ = (x * a⁻¹ * x⁻¹ * a⁻¹⁻¹)⁻¹ := by group
    rw [e]
    exact C.ZI.inv_mem h
  have heC : ∀ w ∈ conjClosure S.V3 H,
      (a⁻¹ * x * a * x⁻¹) * w * (a⁻¹ * x * a * x⁻¹)⁻¹ = w := fun w hw => by
    have h := Subgroup.mem_centralizer_iff.mp (S.VH_le_centralizer_UH_F4 hNS h13315 h1356two hH hab
      (C.ZI_le_VH he)) w hw
    rw [← h, mul_inv_cancel_right]

  have hkV : x * u * x⁻¹ * u⁻¹ ∈ fsuV1 T V := hF.commutator_mem_V₁ hxQ hu
  have hkc : ∀ h ∈ H, h * (x * u * x⁻¹ * u⁻¹) * h⁻¹ = x * u * x⁻¹ * u⁻¹ := fun h hh =>
    hF.conj_eq_of_mem_V₁ hh hkV
  have hxu : x * u * x⁻¹ ∈ conjClosure S.V3 H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H hxH) u).mp hu
  have h1 : x * (a * u * a⁻¹) * x⁻¹ = (x * u * x⁻¹ * u⁻¹) * (a * u * a⁻¹) := by
    calc x * (a * u * a⁻¹) * x⁻¹ =
        a * ((a⁻¹ * x * a * x⁻¹) * (x * u * x⁻¹) * (a⁻¹ * x * a * x⁻¹)⁻¹) * a⁻¹ := by group
      _ = a * (x * u * x⁻¹) * a⁻¹ := by rw [heC _ hxu]
      _ = (a * (x * u * x⁻¹ * u⁻¹) * a⁻¹) * (a * u * a⁻¹) := by group
      _ = (x * u * x⁻¹ * u⁻¹) * (a * u * a⁻¹) := by rw [hkc a haH]
  have hcH : a * u * a⁻¹ * u⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem (H.mul_mem haH huH) (H.inv_mem haH)) (H.inv_mem huH)
  have hck : (x * u * x⁻¹ * u⁻¹) * (a * u * a⁻¹ * u⁻¹) * (x * u * x⁻¹ * u⁻¹)⁻¹ =
      a * u * a⁻¹ * u⁻¹ := by
    have h := hkc _ hcH
    generalize x * u * x⁻¹ * u⁻¹ = k at h ⊢
    generalize a * u * a⁻¹ * u⁻¹ = c at h ⊢
    have h2 : c * k = k * c := by
      calc c * k = c * k * c⁻¹ * c := by group
        _ = k * c := by rw [h]
    rw [← h2]
    group
  calc x * (a * u * a⁻¹ * u⁻¹) = (x * (a * u * a⁻¹) * x⁻¹) * (x * u⁻¹ * x⁻¹) * x := by group
    _ = (x * u * x⁻¹ * u⁻¹) * (a * u * a⁻¹) * (x * u⁻¹ * x⁻¹) * x := by rw [h1]
    _ = (x * u * x⁻¹ * u⁻¹) * (a * u * a⁻¹ * u⁻¹) * (x * u * x⁻¹ * u⁻¹)⁻¹ * x := by group
    _ = (a * u * a⁻¹ * u⁻¹) * x := by rw [hck]

theorem comm_UH_A_mem_F4
    (hna : ¬ IsElemAbelian 2 (conjClosure V H)) (h13314 : Stmt13_3_14_F4) {u a : G}
    (hu : u ∈ conjClosure S.V3 H) (ha : a ∈ C.A) :
    a * u * a⁻¹ * u⁻¹ ∈
      S.V3 ⊔ (conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) := by
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  have haH : a ∈ H := hF.T_le_H (C.A_le_T_F4 hNS h13315 h1356two hH hab hhat ha)
  rw [← C.centralizer_X_eq_F4 hNS h13315 h1356two hH hab h13314]
  refine ⟨(conjClosure S.V3 H).mul_mem ((Subgroup.mem_normalizer_iff.mp
    (le_normalizer_conjClosure S.V3 H haH) u).mp hu) ((conjClosure S.V3 H).inv_mem hu), ?_⟩
  exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
    C.comm_X_comm_F4 hNS h13315 h1356two hH hab hhat hna h13314 hx.1 hx.2 hu ha

theorem comm_A_of_mem_F4
    (hna : ¬ IsElemAbelian 2 (conjClosure V H)) {a u : G} (ha : a ∈ C.A)
    (hu : u ∈ conjClosure S.V3 H) (hgu : (C.g : G) * u * (C.g : G)⁻¹ ∈ pCoreOf 2 H) :
    a * u = u * a := by
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  have hgg : (C.g : G) * C.g ∈ H := hF.L₁T_le_H (C.g_sq_mem hhat)
  have hxU : (C.g : G) * u * (C.g : G)⁻¹ ∈ conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) := by
    rw [mem_conjSub, inv_inv]
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H hgg) u).mp hu
    have e : (C.g : G) * ((C.g : G) * u * (C.g : G)⁻¹) * (C.g : G)⁻¹ =
        (C.g : G) * C.g * u * ((C.g : G) * C.g)⁻¹ := by group
    rw [e]
    exact this
  have hxC : (C.g : G) * u * (C.g : G)⁻¹ ∈
      Subgroup.centralizer (conjClosure S.V3 H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u' hu'
    exact (C.comm_DHg_UH_F4 hNS h13315 h1356two hH hab hhat hna ⟨hxU, hgu⟩ hu').symm
  have hy : (C.g : G) * a * (C.g : G)⁻¹ ∈ conjClosure V H := (C.mem_VHg).1 ha.1
  have h1 := S.comm_VH_HC_F4 hNS h13315 h1356two hH hgu hxC hy
  have h2 : a * u * a⁻¹ * u⁻¹ ∈ conjSub (C.g : G)⁻¹ (fsuV1 T V) := by
    rw [mem_conjSub, inv_inv]
    have e : (C.g : G) * (a * u * a⁻¹ * u⁻¹) * (C.g : G)⁻¹ =
        (C.g : G) * a * (C.g : G)⁻¹ * ((C.g : G) * u * (C.g : G)⁻¹) *
          ((C.g : G) * a * (C.g : G)⁻¹)⁻¹ * ((C.g : G) * u * (C.g : G)⁻¹)⁻¹ := by group
    rw [e]
    exact h1
  have haH : a ∈ H := hF.T_le_H (C.A_le_T_F4 hNS h13315 h1356two hH hab hhat ha)
  have h3 : a * u * a⁻¹ * u⁻¹ ∈ conjClosure S.V3 H :=
    (conjClosure S.V3 H).mul_mem ((Subgroup.mem_normalizer_iff.mp
      (le_normalizer_conjClosure S.V3 H haH) u).mp hu) ((conjClosure S.V3 H).inv_mem hu)
  have h4 := C.V1g_inf_UH hab hna h2 h3
  calc a * u = a * u * a⁻¹ * u⁻¹ * (u * a) := by group
    _ = u * a := by rw [h4, one_mul]

theorem DH_le_centralizer_A_F4
    (hna : ¬ IsElemAbelian 2 (conjClosure V H)) :
    conjClosure S.V3 H ⊓ conjSub (C.g : G)⁻¹ (pCoreOf 2 H) ≤
      Subgroup.centralizer (C.A : Set G) := by
  intro d hd
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hgd : (C.g : G) * d * (C.g : G)⁻¹ ∈ pCoreOf 2 H := by
    have := (mem_conjSub (g := (C.g : G)⁻¹)).1 hd.2
    rwa [inv_inv] at this
  exact C.comm_A_of_mem_F4 hNS h13315 h1356two hH hab hhat hna ha hd.1 hgd

omit hab in

theorem relIndex_DH_eq_F4 :
    (conjClosure S.V3 H ⊓ conjSub (C.g : G)⁻¹ (pCoreOf 2 H)).relIndex (conjClosure S.V3 H) =
      (conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) ⊓ pCoreOf 2 H).relIndex
        (conjSub (C.g : G)⁻¹ (conjClosure S.V3 H)) := by
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  have hgg : (C.g : G) * C.g ∈ H := hF.L₁T_le_H (C.g_sq_mem hhat)
  have hQ : conjSub ((C.g : G)⁻¹ * (C.g : G)⁻¹) (pCoreOf 2 H) = pCoreOf 2 H := by
    apply F7.conjSub_eq_of_mem_normalizer
    have : ((C.g : G) * C.g)⁻¹ ∈ H := H.inv_mem hgg
    rw [mul_inv_rev] at this
    exact le_normalizer_pCoreOf 2 H this
  rw [← A6Twelve.relIndex_conjSub_conjSub (C.g : G)⁻¹, conjSub_inf, ← conjSub_mul, hQ]

theorem relIndex_centralizer_A_le_F4
    (hna : ¬ IsElemAbelian 2 (conjClosure V H)) :
    (conjClosure S.V3 H ⊓ Subgroup.centralizer (C.A : Set G)).relIndex (conjClosure S.V3 H) ≤
      (C.A ⊓ pCoreOf 2 H).relIndex C.A := by
  have hD : conjClosure S.V3 H ⊓ conjSub (C.g : G)⁻¹ (pCoreOf 2 H) ≤
      conjClosure S.V3 H ⊓ Subgroup.centralizer (C.A : Set G) :=
    le_inf inf_le_left (C.DH_le_centralizer_A_F4 hNS h13315 h1356two hH hab hhat hna)
  refine (Subgroup.relIndex_le_of_le_left hD Subgroup.index_ne_zero_of_finite).trans ?_
  rw [C.relIndex_DH_eq_F4 hNS h13315 h1356two hH hhat, Subgroup.inf_relIndex_left,
    Subgroup.inf_relIndex_left]
  exact Subgroup.relIndex_le_of_le_right (C.UHg_le_A_F4 hNS h13315 h1356two hH hab)
    Subgroup.index_ne_zero_of_finite

theorem relIndex_centralizer_UHg_le_F4
    (hna : ¬ IsElemAbelian 2 (conjClosure V H)) :
    (conjClosure S.V3 H ⊓
        Subgroup.centralizer (conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) : Set G)).relIndex
      (conjClosure S.V3 H) ≤
      (conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) ⊓ pCoreOf 2 H).relIndex
        (conjSub (C.g : G)⁻¹ (conjClosure S.V3 H)) := by
  have hD : conjClosure S.V3 H ⊓ conjSub (C.g : G)⁻¹ (pCoreOf 2 H) ≤
      conjClosure S.V3 H ⊓
        Subgroup.centralizer (conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) : Set G) :=
    le_inf inf_le_left ((C.DH_le_centralizer_A_F4 hNS h13315 h1356two hH hab hhat hna).trans
      (Subgroup.centralizer_le (C.UHg_le_A_F4 hNS h13315 h1356two hH hab)))
  refine (Subgroup.relIndex_le_of_le_left hD Subgroup.index_ne_zero_of_finite).trans ?_
  rw [C.relIndex_DH_eq_F4 hNS h13315 h1356two hH hhat]

end Hat

end Conf

end NonAb

end Setting4

end CFSG.Quasithin.H13.A6

module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7C2
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7W714D
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7W14
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7ECent
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7EGen
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Fus
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Cover
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7E8
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6jB
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Mem
import CFSG.ClassicalInvolution.Q3.Sec13L94Tight
import CFSG.ClassicalInvolution.Q3.Q3CPSat
import CFSG.ClassicalInvolution.Q3.Q3CLBasic
import CFSG.ClassicalInvolution.Asc77.AscT7K1
import CFSG.ClassicalInvolution.Asc77.AscC25W1
import CFSG.ClassicalInvolution.Asc77.AscT7TZStar
import CFSG.ClassicalInvolution.Asc77.AscSixBasic
import CFSG.ClassicalInvolution.Asc77.AscE184Cent
import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonBasic
import CFSG.ClassicalInvolution.AschTight.Sec7L714F
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Cen3L
public import Certificates.Certificate393003
import CFSG.ClassicalInvolution.AschTight.Sec7L714D

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section Steps

variable {n : ℕ}

theorem p23E7N2_proved : P23E7N2 n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hE hZ Z hZd x hx hxe1 hxet heN
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  have hW : W ∈ WSet (Om R) := hd.hW
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hzg : IsUniqueInvolution (conjSub g (tightCore R)) (u * e) := by
    have := TwinPerpV3.A6jB.isUniqueInvolution_conjSub hz g
    rwa [hd.hgt] at this
  have hZ2 : IsPGroup 2 Z := hZd.isPGroup
  have he2 : e * e = 1 := hd.he2
  have ht2 : t * t = 1 := hZd.sq t hZd.ht
  have hte : t * e = e * t := hZd.comm t hZd.ht e hZd.he
  have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hx.1
  have hconjZ : ∀ {m : Y}, m ∈ Subgroup.normalizer (Z : Set Y) → ∀ {b : Y}, b ∈ Z → m * b * m⁻¹ ∈ Z := by
    intro m hm b hb
    have h := conjSub_eq_of_mem_normalizer hm
    rw [← h]
    exact conj_mem_conjSub hb
  have hxeZ : x * e * x⁻¹ ∈ Z := hconjZ hx.2 hZd.he
  have hx'eZ : x⁻¹ * e * x⁻¹⁻¹ ∈ Z := hconjZ (Subgroup.inv_mem _ hx.2) hZd.he
  obtain ⟨C, hCdef⟩ : ∃ C : Subgroup Y, C = Subgroup.centralizer ({t} : Set Y) := ⟨_, rfl⟩
  have hmemC : ∀ c : Y, c ∈ C ↔ c * t = t * c := fun c => by
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff]
  have htC : t ∈ C := (hmemC t).mpr rfl
  have heC : e ∈ C := (hmemC e).mpr hte.symm
  have hxC : x ∈ C := (hmemC x).mpr hxt
  have hZC : ∀ {b : Y}, b ∈ Z → b ∈ C := fun hb =>
    (hmemC _).mpr (Subgroup.mem_centralizer_singleton_iff.mp (hZd.le_t hb))
  obtain ⟨J, hJdef⟩ : ∃ J, J = conjSub x (conjSub g (tightCore R)) := ⟨_, rfl⟩
  rw [← hJdef] at heN ⊢
  have hJ : J ∈ Om R := by
    rw [hJdef]
    exact hΩ.conjInvariant x _ (hΩ.conjInvariant g _ hK)
  obtain ⟨a, hadef⟩ : ∃ a, a = x * (u * e) * x⁻¹ := ⟨_, rfl⟩
  have hzJ : IsUniqueInvolution J a := by
    rw [hJdef, hadef]
    exact TwinPerpV3.A6jB.isUniqueInvolution_conjSub hzg x
  have ha2 : a * a = 1 := hzJ.sq
  have hat : a * t = t * a := by
    have hueC : u * e ∈ C := (hmemC _).mpr (hWab _ (W.mul_mem hd.huW heW) t hd.hzW)
    have haC : a ∈ C := by
      rw [hadef]
      exact C.mul_mem (C.mul_mem hxC hueC) (C.inv_mem hxC)
    exact (hmemC a).mp haC
  have hae : a * e = e * a := by
    have h1 : (x⁻¹ * e * x⁻¹⁻¹) * u = u * (x⁻¹ * e * x⁻¹⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hZd.le_u hx'eZ)
    have h2 := hZd.comm _ hx'eZ e hZd.he
    have hc1 : (x⁻¹ * e * x⁻¹⁻¹) * (u * e) = (u * e) * (x⁻¹ * e * x⁻¹⁻¹) := by
      calc (x⁻¹ * e * x⁻¹⁻¹) * (u * e) = ((x⁻¹ * e * x⁻¹⁻¹) * u) * e := by group
        _ = (u * (x⁻¹ * e * x⁻¹⁻¹)) * e := by rw [h1]
        _ = u * ((x⁻¹ * e * x⁻¹⁻¹) * e) := by group
        _ = u * (e * (x⁻¹ * e * x⁻¹⁻¹)) := by rw [h2]
        _ = (u * e) * (x⁻¹ * e * x⁻¹⁻¹) := by group
    calc a * e = x * ((u * e) * (x⁻¹ * e * x⁻¹⁻¹)) * x⁻¹ := by rw [hadef]; group
      _ = x * ((x⁻¹ * e * x⁻¹⁻¹) * (u * e)) * x⁻¹ := by rw [hc1]
      _ = e * a := by rw [hadef]; group
  have hA : CentMod J e → x * e * x⁻¹ = e ∨ x * e * x⁻¹ = e * t := by
    intro hJe
    have hV2 : IsPGroup 2 (Subgroup.closure ({e, e, e} : Set Y)) :=
      F7V.isPGroup_closure_three he2 he2 he2 rfl rfl rfl
    have heV : e ∈ Subgroup.closure ({e, e, e} : Set Y) := Subgroup.subset_closure (by simp)
    obtain ⟨T, hT, -, hTe, -⟩ :=
      F7V.exists_sylow_comm_pair hV2 (F7V.closure_three_le heN heN heN) heV heV hJe hJe
    have hTC : T ≤ Subgroup.centralizer ({e} : Set Y) := fun r hr =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hTe r hr)
    have hTE : T ≤ rLayer (Om R) e := F7C.le_rLayer (Asc77.mem_RSet_of_isSylow2In hJ hT) hTC
    have hEc : rLayer (Om R) e ≤ oddCoreOf (rLayer (Om R) e) ⊔
        (rLayer (Om R) e ⊓ Subgroup.normalizer (W : Set Y)) := hE
    obtain ⟨o, ho, hoN⟩ := exists_oddCore_conj_le hEc hT.2.1 hTE
    have hmemQ : ∀ y ∈ conjSub o⁻¹ T, o * y * o⁻¹ ∈ T := by
      intro y hy
      rw [mem_conjSub_iff, inv_inv] at hy
      exact hy
    have hQN : conjSub o⁻¹ T ≤ Subgroup.normalizer (W : Set Y) := by
      intro y hy
      have := hoN _ (hmemQ y hy)
      have e1 : o⁻¹ * (o * y * o⁻¹) * o = y := by group
      rwa [e1] at this
    have hQR : conjSub o⁻¹ T ∈ RSet (Om R) :=
      Q3CL.Thompson.conjSub_mem_RSet hΩ (Asc77.mem_RSet_of_isSylow2In hJ hT) o⁻¹
    have hQD : conjSub o⁻¹ T ∈ DSet (Om R) W := ⟨hQR, hQN⟩
    have hJo : conjSub o⁻¹ J ∈ Om R := hΩ.conjInvariant o⁻¹ J hJ
    have hQJo : IsSylow2In (conjSub o⁻¹ T) (conjSub o⁻¹ J) := hT.conj o⁻¹
    have hzo : IsUniqueInvolution (conjSub o⁻¹ J) (o⁻¹ * a * o⁻¹⁻¹) :=
      TwinPerpV3.A6jB.isUniqueInvolution_conjSub hzJ o⁻¹
    have hwW : o⁻¹ * a * o⁻¹⁻¹ ∈ W := F7G.inv_mem_W hΩ hW hQD hJo hQJo hzo
    have haE : a ∈ rLayer (Om R) e := hTE (Q3CP.mem_of_isSylow2In_of_isUniqueInvolution hzJ hT)
    have hd2 : a⁻¹ * (o⁻¹ * a * o⁻¹⁻¹) ∈ oddCoreOf (rLayer (Om R) e) := by
      have hzN := Sec7.le_normalizer_oddCoreOf (rLayer (Om R) e) ((rLayer (Om R) e).inv_mem haE)
      have h1 : a⁻¹ * o⁻¹ * a⁻¹⁻¹ ∈ oddCoreOf (rLayer (Om R) e) :=
        (Subgroup.mem_normalizer_iff.mp hzN _).mp ((oddCoreOf (rLayer (Om R) e)).inv_mem ho)
      have e1 : a⁻¹ * (o⁻¹ * a * o⁻¹⁻¹) = (a⁻¹ * o⁻¹ * a⁻¹⁻¹) * o := by group
      rw [e1]
      exact (oddCoreOf (rLayer (Om R) e)).mul_mem h1 ho
    have hw2 : (o⁻¹ * a * o⁻¹⁻¹) * (o⁻¹ * a * o⁻¹⁻¹) = 1 := by
      calc (o⁻¹ * a * o⁻¹⁻¹) * (o⁻¹ * a * o⁻¹⁻¹) = o⁻¹ * (a * a) * o⁻¹⁻¹ := by group
        _ = 1 := by rw [ha2]; group
    obtain ⟨v, hv, hav⟩ := exists_conj_zpowers_of_mul_mem_odd (odd_natCard_oddCoreOf _) ha2 hw2 hd2
    have hawC : a * (o⁻¹ * a * o⁻¹⁻¹) ∈
        Subgroup.centralizer ({t} : Set Y) ⊓ Subgroup.centralizer ({e} : Set Y) := by
      refine ⟨Subgroup.mul_mem _ (Subgroup.mem_centralizer_singleton_iff.mpr hat)
          (Subgroup.mem_centralizer_singleton_iff.mpr (hWab _ hwW t hd.hzW)),
        Subgroup.mul_mem _ (Subgroup.mem_centralizer_singleton_iff.mpr hae)
          (Subgroup.mem_centralizer_singleton_iff.mpr (hWab _ hwW e heW))⟩
    have hvC2 := (Subgroup.zpowers_le.mpr hawC) hv
    have hvt : v * t = t * v := Subgroup.mem_centralizer_singleton_iff.mp hvC2.1
    have hve : v * e = e * v := Subgroup.mem_centralizer_singleton_iff.mp hvC2.2
    have hvC : v ∈ C := (hmemC v).mpr hvt
    have hyC : v⁻¹ * x ∈ C := C.mul_mem (C.inv_mem hvC) hxC
    have hyW : (v⁻¹ * x) * (u * e) * (v⁻¹ * x)⁻¹ ∈ W := by
      have e1 : (v⁻¹ * x) * (u * e) * (v⁻¹ * x)⁻¹ = v⁻¹ * a * v := by rw [hadef]; group
      have e2 : v⁻¹ * a * v = o⁻¹ * a * o⁻¹⁻¹ := by
        conv_lhs => rw [hav]
        group
      rw [e1, e2]
      exact hwW
    have hyeC : (v⁻¹ * x) * e * (v⁻¹ * x)⁻¹ ∈ C := C.mul_mem (C.mul_mem hyC heC) (C.inv_mem hyC)
    have hxeC : x * e * x⁻¹ ∈ C := hZC hxeZ
    have hrel : (⟨x * e * x⁻¹, hxeC⟩ : ↥C) =
        ⟨v, hvC⟩ * ⟨(v⁻¹ * x) * e * (v⁻¹ * x)⁻¹, hyeC⟩ * (⟨v, hvC⟩)⁻¹ :=
      Subtype.ext (by
        show x * e * x⁻¹ = v * ((v⁻¹ * x) * e * (v⁻¹ * x)⁻¹) * v⁻¹
        group)
    have hπ : F7I.piC C ⟨x * e * x⁻¹, hxeC⟩ = F7I.piC C ⟨v, hvC⟩ *
        F7I.piC C ⟨(v⁻¹ * x) * e * (v⁻¹ * x)⁻¹, hyeC⟩ * (F7I.piC C ⟨v, hvC⟩)⁻¹ := by
      rw [hrel, map_mul, map_mul, map_inv]
    have hπve : F7I.piC C ⟨v, hvC⟩ * F7I.piC C ⟨e, heC⟩ =
        F7I.piC C ⟨e, heC⟩ * F7I.piC C ⟨v, hvC⟩ := by
      rw [← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext hve)
    have hπvt : F7I.piC C ⟨v, hvC⟩ * F7I.piC C ⟨t, htC⟩ =
        F7I.piC C ⟨t, htC⟩ * F7I.piC C ⟨v, hvC⟩ := by
      rw [← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext hvt)
    rcases p23_conj_e_mod_t hc hCdef hyC htC heC hyeC hyW with h | h
    · left
      have h1 : F7I.piC C ⟨x * e * x⁻¹, hxeC⟩ = F7I.piC C ⟨e, heC⟩ := by
        rw [hπ, h, hπve, mul_inv_cancel_right]
      exact congrArg Subtype.val (F7I.piC_inj hZ2 hxeZ hZd.he h1)
    · right
      have hteZ : t * e ∈ Z := Z.mul_mem hZd.ht hZd.he
      have h1 : F7I.piC C ⟨x * e * x⁻¹, hxeC⟩ = F7I.piC C ⟨t * e, hZC hteZ⟩ := by
        rw [hπ, h]
        calc F7I.piC C ⟨v, hvC⟩ * (F7I.piC C ⟨t, htC⟩ * F7I.piC C ⟨e, heC⟩) *
              (F7I.piC C ⟨v, hvC⟩)⁻¹ =
            (F7I.piC C ⟨v, hvC⟩ * F7I.piC C ⟨t, htC⟩) * F7I.piC C ⟨e, heC⟩ *
              (F7I.piC C ⟨v, hvC⟩)⁻¹ := by group
          _ = (F7I.piC C ⟨t, htC⟩ * F7I.piC C ⟨v, hvC⟩) * F7I.piC C ⟨e, heC⟩ *
              (F7I.piC C ⟨v, hvC⟩)⁻¹ := by rw [hπvt]
          _ = F7I.piC C ⟨t, htC⟩ * (F7I.piC C ⟨v, hvC⟩ * F7I.piC C ⟨e, heC⟩) *
              (F7I.piC C ⟨v, hvC⟩)⁻¹ := by group
          _ = F7I.piC C ⟨t, htC⟩ * (F7I.piC C ⟨e, heC⟩ * F7I.piC C ⟨v, hvC⟩) *
              (F7I.piC C ⟨v, hvC⟩)⁻¹ := by rw [hπve]
          _ = F7I.piC C ⟨t, htC⟩ * F7I.piC C ⟨e, heC⟩ := by group
          _ = F7I.piC C ⟨t * e, hZC hteZ⟩ := (map_mul _ _ _).symm
      have h2 : x * e * x⁻¹ = t * e := congrArg Subtype.val (F7I.piC_inj hZ2 hxeZ hteZ h1)
      rw [h2, hte]
  refine ⟨fun hJe => ?_, fun hJet => ?_⟩
  · rcases hA hJe with h | h
    · exact hxe1 h
    · exact hxet h
  have het2 : (e * t) * (e * t) = 1 := by
    calc (e * t) * (e * t) = e * (t * e) * t := by group
      _ = e * (e * t) * t := by rw [hte]
      _ = (e * e) * (t * t) := by group
      _ = 1 := by rw [he2, ht2, one_mul]
  have hetN : e * t ∈ Subgroup.normalizer (J : Set Y) := F7E.mem_normalizer_of_centMod hJet het2
  have htN : t ∈ Subgroup.normalizer (J : Set Y) := by
    have h := Subgroup.mul_mem _ (Subgroup.inv_mem _ heN) hetN
    rwa [show e⁻¹ * (e * t) = t by group] at h
  have hZ' : t ∈ zStarOf (Subgroup.centralizer ({e * t} : Set Y)) := by
    have hgN : g ∈ Subgroup.normalizer (W : Set Y) := T7K.g_mem_normalizer hd
    have hge : g⁻¹ * e * g = e := by rw [mul_assoc, ← T7K.comm_e hd hgN, inv_mul_cancel_left]
    have hgz : g⁻¹ * (u * e) * g = t := by rw [← hd.hgt]; group
    have hgu : g⁻¹ * u * g = e * t := by
      have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right hd.he2
      calc g⁻¹ * u * g = g⁻¹ * (u * e) * g * (g⁻¹ * e⁻¹ * g) := by group
        _ = t * e := by rw [hgz, hei, hge]
        _ = e * t := hte
    have hZ1 := C25W.conj_mem_zStarOf_conjSub _ g⁻¹ hZ
    rw [← C25W.centralizer_conj, inv_inv, hgz, hgu] at hZ1
    exact hZ1
  have hc12 : e * t = t * e := hte.symm
  have hc13 : e * (e * t) = (e * t) * e := by rw [mul_assoc, ← hte, ← mul_assoc]
  have hc23 : t * (e * t) = (e * t) * t := by rw [← mul_assoc, hte]
  have hV2 : IsPGroup 2 (Subgroup.closure ({e, t, e * t} : Set Y)) :=
    F7V.isPGroup_closure_three he2 ht2 het2 hc12 hc13 hc23
  have hVN := F7V.closure_three_le heN htN hetN
  obtain ⟨P, hP, hVP⟩ := Asc77.IsSylow2In.exists_ge hV2
    (le_sup_right : Subgroup.closure ({e, t, e * t} : Set Y) ≤ J ⊔ Subgroup.closure ({e, t, e * t} : Set Y))
  have hTJ : IsSylow2In (P ⊓ J) J :=
    Asc77.isSylow2In_inf_of_le_normalizer hP le_sup_left (sup_le Subgroup.le_normalizer hVN)
  have htP : t ∈ P := hVP (Subgroup.subset_closure (by simp))
  have hetP : e * t ∈ P := hVP (Subgroup.subset_closure (by simp))
  have hc1 : ∀ r ∈ P ⊓ J, r * (e * t) = (e * t) * r := by
    intro r hr
    have hcT : (e * t) * r * (e * t)⁻¹ * r⁻¹ ∈ P :=
      P.mul_mem (P.mul_mem (P.mul_mem hetP hr.1) (P.inv_mem hetP)) (P.inv_mem hr.1)
    have h1 := Sec13.L94T.eq_one_of_isPGroup_of_odd hP.2.1 (odd_natCard_oddCoreOf J) hcT (hJet r hr.2)
    have := congrArg (· * (r * (e * t))) h1
    simp only [one_mul] at this
    rw [← this]
    group
  have hQ2 : IsPGroup 2 ↥(P ⊓ Subgroup.centralizer ({e * t} : Set Y)) := hP.2.1.to_le inf_le_left
  have htQ : t ∈ P ⊓ Subgroup.centralizer ({e * t} : Set Y) :=
    ⟨htP, Subgroup.mem_centralizer_singleton_iff.mpr hc23⟩
  have hQt := T7T.le_centralizer_of_mem_zStarOf hZ' htQ inf_le_right hQ2
  have hc2 : ∀ r ∈ P ⊓ J, r * t = t * r := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mp
      (hQt ⟨hr.1, Subgroup.mem_centralizer_singleton_iff.mpr (hc1 r hr)⟩)
  have hc3 : ∀ r ∈ P ⊓ J, r * e = e * r := by
    intro r hr
    calc r * e = r * (e * t) * t := by rw [mul_assoc r (e * t) t, mul_assoc e t t, ht2, mul_one]
      _ = (e * t) * r * t := by rw [hc1 r hr]
      _ = (e * t) * (t * r) := by rw [mul_assoc, hc2 r hr]
      _ = e * r := by rw [← mul_assoc, mul_assoc e t t, ht2, mul_one]
  have hJe : CentMod J e := F7W.centMod_of_sylow hzJ hTJ he2 heN hc3
  rcases hA hJe with h | h
  · exact hxe1 h
  · exact hxet h

theorem p23E7Y_of_lemL' (hT : Thm4RTwinBelow 3 n) (hT4 : TwinThmE.T4Supply)
    (hmodel : TwinDisc.ExitE4.E4ModelDStar) (hD4 : TwinCentRes.ModelFactD42) (hMu : P23E4Mu n)
    (hTwo : P23Two n) (hα : P23Alpha n) (hL : P23E7LemL n) (hM : E64CenComm) : P23E7Y n :=
  p23E7Y_of_lemL hT hT4 hmodel hD4 hMu hTwo hα hL p23E7N2_proved hM

end Steps

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

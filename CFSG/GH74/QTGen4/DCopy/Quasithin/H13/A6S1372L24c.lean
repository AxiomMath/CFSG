module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S13710e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L24b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372SixteenC1
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.G64RealizeSec
public import CFSG.Quasithin.H13.A6S1372L24a
public import CFSG.Quasithin.H13.A6S1372L24b

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative commutatorElement

@[expose] def Lem13719L1K_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 → ¬ IsHatA6 L →
    ∀ H : Subgroup G, H ∈ S.Hz → IsElemAbelian 2 (conjClosure S.V3 H) →
    ¬ IsElemAbelian 2 (conjClosure V H) →
    ∀ [IsMulCommutative ↥(conjClosure S.V3 H)] (C : S.Conf H)
      (B : Subgroup (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))))
      (K : Subgroup G), C.KData B K →
      BinaryNaturalSL (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
        (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
          commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 2 2 →
      S.L1 ≤ K

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {S : Setting4 G T L V}

section KTilde

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

namespace Conf

variable [IsMulCommutative ↥(conjClosure S.V3 H)] {C : S.Conf H}
  {B : Subgroup (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))))}
  {K : Subgroup G}

omit hab in

theorem exists_alpha_L24_F4 (hKH : K ≤ H)
    (hL : BinaryNaturalSL (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
        (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
          commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 2 2) :
    ∃ α : ↥K →* alternatingGroup (Fin 5), Function.Surjective α ∧
      ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H := by
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 hH
  obtain ⟨F, _, _, hF, π, hπ⟩ := hL
  have hF4 : Nat.card F = 4 := by rw [hF]; norm_num
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hF])
  have hπinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
  let e : ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F) ≃* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) :=
    MulEquiv.ofBijective π ⟨hπinj, hπ.1⟩
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 60 := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF4]
    norm_num
  obtain ⟨e5⟩ := CFSG.Quasithin.A5Model.sl2_four_equiv_alt5 F hF4 hSL
  let κ : ↥K →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) :=
    ((A6Mod.secAct hHU hHV).comp (Subgroup.inclusion hKH)).codRestrict _
      fun k => (A6Mod.mem_autSec_iff hHU hHV hKH).2 ⟨_, k.2, rfl⟩
  have hκs : Function.Surjective κ := by
    intro x
    obtain ⟨h, hhK, hx⟩ := (A6Mod.mem_autSec_iff hHU hHV hKH).1 x.2
    exact ⟨⟨h, hhK⟩, Subtype.ext hx⟩
  let eS := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F
  refine ⟨(e5.toMonoidHom.comp eS.symm.toMonoidHom).comp (e.symm.toMonoidHom.comp κ),
    e5.surjective.comp (eS.symm.surjective.comp (e.symm.surjective.comp hκs)), fun k => ?_⟩
  have hκk : κ k = 1 ↔ (k : G) ∈ pCoreOf 2 H := by
    rw [S.mem_QH_iff_tilde_F4 hNS h13315 h1356two hH (hKH k.2)]
    exact Subtype.ext_iff.trans (A6Mod.secAct_eq_one_iff hHU hHV ⟨k, hKH k.2⟩)
  show e5 (eS.symm (e.symm (κ k))) = 1 ↔ _
  rw [← hκk]
  constructor
  · intro h
    have h1 : eS.symm (e.symm (κ k)) = 1 := (MulEquiv.map_eq_one_iff e5).1 h
    have h2 : e.symm (κ k) = 1 := (MulEquiv.map_eq_one_iff eS.symm).1 h1
    exact (MulEquiv.map_eq_one_iff e.symm).1 h2
  · intro h
    rw [h, map_one, map_one, map_one]

omit hab in

theorem sixteen_le_nu_L24_F4 (hKH : K ≤ H)
    (hL : BinaryNaturalSL (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
        (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
          commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 2 2)
    {c : G} (hcK : c ∈ K) (hc3 : c ^ 3 = 1) (hcQ : c ∉ pCoreOf 2 H) :
    4 ^ 2 ≤ nu c (conjClosure S.V3 H) := by
  classical
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 hH
  set Kt := autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) with hKt
  obtain ⟨F, _, _, hF, π, hπ⟩ := hL
  have hF4 : Nat.card F = 4 := by rw [hF]; norm_num
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hF])
  have hπinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
  obtain ⟨-, -, -, -, -, -, -, β', hβs, hβk, hβe⟩ := id hπ

  set κc : ↥Kt :=
    ⟨A6Mod.secAct hHU hHV ⟨c, hKH hcK⟩, (A6Mod.mem_autSec_iff hHU hHV hKH).2 ⟨_, hcK, rfl⟩⟩
    with hκc
  obtain ⟨γ, hγ⟩ := hπ.1 κc
  have hc3' : (⟨c, hKH hcK⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
  have hγ3 : γ ^ 3 = 1 := by
    apply hπinj
    rw [map_pow, hγ, map_one]
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    show (A6Mod.secAct hHU hHV ⟨c, hKH hcK⟩) ^ 3 = 1
    rw [← map_pow, hc3', map_one]
  have hγ1 : γ ≠ 1 := by
    intro h1
    apply hcQ
    rw [S.mem_QH_iff_tilde_F4 hNS h13315 h1356two hH (hKH hcK)]
    have h2 : κc = 1 := by rw [← hγ, h1, map_one]
    exact (A6Mod.secAct_eq_one_iff hHU hHV ⟨c, hKH hcK⟩).1 (congrArg Subtype.val h2)

  let γ' : ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F) := γ
  have hγ3' : γ' ^ 3 = 1 := hγ3
  have hγ1' : γ' ≠ 1 := hγ1

  set M : Matrix (Fin 2) (Fin 2) F :=
    ((γ' : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hM
  have hdet : M.det = 1 := by
    obtain ⟨A, hA⟩ :=
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).surjective γ'
    rw [hM, ← hA, CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe]
    exact A.2
  have hM3 : M * M * M = 1 := by
    have h1 : ((γ' ^ 3 : ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F)) :
        Matrix.GeneralLinearGroup (Fin 2) F) = 1 := by rw [hγ3']; rfl
    rw [Subgroup.coe_pow] at h1
    have h2 := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) F =>
      (g : Matrix (Fin 2) (Fin 2) F)) h1
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at h2
    rw [← pow_three']
    exact h2
  have hM1 : M ≠ 1 := by
    intro h1
    apply hγ1'
    apply Subtype.ext
    apply Units.ext
    exact h1

  set q := InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) with hq
  have hqs : Function.Surjective q := InternalSec.secMk_surjective _
  set Y : Subgroup ↥(conjClosure S.V3 H) := (commV Kt).comap q with hY
  set Y₀ : Subgroup ↥(conjClosure S.V3 H) := (fixV Kt ⊓ commV Kt).comap q with hY₀
  have hker' : β'.ker = (fixV Kt ⊓ commV Kt).subgroupOf (commV Kt) := by
    ext x
    rw [MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]
  have hQ : Nat.card (↥(FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 2 F)).sec ⧸
      (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 2 F)).ker.subgroupOf
        (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 2 F)).sec) = 16 := by
    show ((⊥ : Subgroup (Multiplicative (Fin 2 → F))).subgroupOf ⊤).index = 16
    rw [← Subgroup.relIndex, Subgroup.relIndex_bot_left, Subgroup.card_top]
    show Nat.card (Fin 2 → F) = 16
    rw [Nat.card_fun, hF4, Nat.card_fin]
    norm_num
  have h16 : Y₀.relIndex Y = 16 := by
    rw [hY₀, hY, Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hqs,
      Subgroup.relIndex, ← hker', Subgroup.index_ker, MonoidHom.range_eq_top.mpr hβs,
      Subgroup.card_top, hQ]

  set C' : Subgroup ↥(conjClosure S.V3 H) :=
    (cfix c (conjClosure S.V3 H)).subgroupOf (conjClosure S.V3 H) with hC'
  have hle : C' ⊓ Y ≤ Y₀ := by
    intro u hu
    have hu1 : (u : G) ∈ cfix c (conjClosure S.V3 H) := hu.1
    have hu2 : q u ∈ commV Kt := hu.2
    rw [mem_cfix] at hu1
    have hcu : c * (u : G) * c⁻¹ = u := by rw [hu1.2, mul_inv_cancel_right]
    set x : ↥(commV Kt) := ⟨q u, hu2⟩ with hx
    have hfixx : ((π γ : ↥Kt) : MulAut _) (x : Sec _ _) = x.1 := by
      rw [hγ]
      show A6Mod.secAct hHU hHV ⟨c, hKH hcK⟩ (q u) = q u
      rw [hq, A6Mod.secAct_secMk]
      congr 1
      exact Subtype.ext (by rw [Setup.rho_apply_coe, hcu])
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β' x)
    have hu' : ((π γ : ↥Kt) : MulAut _) (x : Sec _ _) ∈ commV Kt := by
      rw [hfixx]
      exact x.2
    have h1 := hβe γ x m hu' (Subgroup.mem_top _) hm.symm
    have h2 : (⟨((π γ : ↥Kt) : MulAut _) (x : Sec _ _), hu'⟩ : ↥(commV Kt)) = x :=
      Subtype.ext hfixx
    rw [h2, ← hm, QuotientGroup.eq] at h1
    have h3 : (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 2 F)).act γ m.1 = m.1 := by
      have h4 := Subgroup.mem_subgroupOf.mp h1
      have h5 : m.1⁻¹ * (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 2 F)).act γ m.1 = 1 :=
        Subgroup.mem_bot.mp h4
      exact (inv_mul_eq_one.mp h5).symm
    have h6 : M.mulVec (Multiplicative.toAdd (m.1 : Multiplicative (Fin 2 → F))) =
        Multiplicative.toAdd (m.1 : Multiplicative (Fin 2 → F)) :=
      congrArg Multiplicative.toAdd h3
    have h7 := A6L24.eq_zero_of_mulVec_eq hdet hM3 hM1 h6
    have hm1 : m = 1 := by
      apply Subtype.ext
      have h8 : (m.1 : Multiplicative (Fin 2 → F)) = 1 :=
        Multiplicative.toAdd.injective (h7.trans toAdd_one.symm)
      exact h8
    have hβx : β' x = 1 := by rw [← hm, hm1, QuotientGroup.mk_one]
    exact (hβk x).1 hβx

  have hdvd := Subgroup.relIndex_dvd_of_le_left Y hle
  rw [h16] at hdvd
  have hne : (C' ⊓ Y).relIndex Y ≠ 0 := by
    show ((C' ⊓ Y).subgroupOf Y).index ≠ 0
    exact Subgroup.index_ne_zero_of_finite
  have h1 : 16 ≤ (C' ⊓ Y).relIndex Y := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
  have h2 : (C' ⊓ Y).relIndex Y ≤ C'.index := by
    rw [Subgroup.inf_relIndex_right, ← Subgroup.relIndex_top_right]
    exact Subgroup.relIndex_le_of_le_right le_top (by
      rw [Subgroup.relIndex_top_right]
      exact Subgroup.index_ne_zero_of_finite)
  calc 4 ^ 2 = 16 := by norm_num
    _ ≤ (C' ⊓ Y).relIndex Y := h1
    _ ≤ C'.index := h2
    _ = nu c (conjClosure S.V3 H) := rfl

theorem KData.relIndex_A_le_four_F4 (hhat : ¬ IsHatA6 L)
    (hNU : ¬ LieModel G .PSU 4 3 1) (hLem : Lem1374One_F4) (hK : C.KData B K)
    {α : ↥K →* alternatingGroup (Fin 5)} (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) :
    (C.VHg ⊓ pCoreOf 2 (L ⊔ T) ⊓ pCoreOf 2 H).relIndex (C.VHg ⊓ pCoreOf 2 (L ⊔ T)) ≤ 4 := by
  have hKH : K ≤ H := le_of_mem_cComp hK.2.2.1
  have hHK := hK.le_normalizer_F4 hNS h13315 h1356two hH hab hhat hNU hLem
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hHQ : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHC := S.le_normalizer_U0 (H := H)
  have hAT : C.VHg ⊓ pCoreOf 2 (L ⊔ T) ≤ T :=
    inf_le_right.trans (pCoreOf_le_of_sylow S.h13.sylow le_sup_right)
  have hAH := hAT.trans hTH

  have hsq : ∀ e ∈ C.VHg ⊓ pCoreOf 2 (L ⊔ T), e * e ∈ pCoreOf 2 H := by
    intro e he
    have he' : (C.g : G) * e * (C.g : G)⁻¹ ∈ conjClosure V H := C.mem_VHg.1 he.1
    have h1 := S.sq_VH_mem_V1_F4 hNS h13315 h1356two hH hab he'
    have h2 : (C.g : G) * e * (C.g : G)⁻¹ * ((C.g : G) * e * (C.g : G)⁻¹) ∈ V :=
      (S.V1_le_V2.trans (S.V2_le_V3.trans S.V3_le_V)) h1
    have h3 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ C.g.2) _).mp h2
    have e1 : ((C.g : G)⁻¹ * ((C.g : G) * e * (C.g : G)⁻¹ * ((C.g : G) * e * (C.g : G)⁻¹)) *
        (C.g : G)⁻¹⁻¹) = e * e := by group
    have h3' : e * e ∈ V := by rwa [e1] at h3
    exact S.V_le_QH_F4 hNS h13315 h1356two hH hab h3'

  have hone : ∀ y : ↥H, A6Mod.secAct hHU hHC y = 1 ↔ (y : G) ∈ pCoreOf 2 H := fun y =>
    (A6Mod.secAct_eq_one_iff hHU hHC y).trans
      (S.mem_QH_iff_plus_F4 hNS h13315 h1356two hH hab hNU hhat hLem y.2).symm
  have hfaith : ∀ e ∈ C.VHg ⊓ pCoreOf 2 (L ⊔ T),
      (∀ k ∈ K, e * k * e⁻¹ * k⁻¹ ∈ pCoreOf 2 H) → e ∈ pCoreOf 2 H := by
    intro e he hcomm
    have heH : e ∈ H := hAH he
    set ψ := A6Mod.secAct hHU hHC ⟨e, heH⟩ with hψ
    have hψT : ψ ∈ autSec (autOn T (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) :=
      (A6Mod.mem_autSec_iff hHU hHC hTH).2 ⟨⟨e, heH⟩, hAT he, rfl⟩
    have hψC : ψ ∈ Subgroup.centralizer ((autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) :
          Subgroup _) : Set _) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨k, hkK, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHC hKH).1 hx
      have hq : A6Mod.secAct hHU hHC (⟨e, heH⟩ * k * ⟨e, heH⟩⁻¹ * k⁻¹) = 1 :=
        (hone _).2 (hcomm k hkK)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hψ] at hq
      calc A6Mod.secAct hHU hHC k * ψ =
          (ψ * A6Mod.secAct hHU hHC k * ψ⁻¹ * (A6Mod.secAct hHU hHC k)⁻¹)⁻¹ * ψ *
            A6Mod.secAct hHU hHC k := by group
        _ = ψ * A6Mod.secAct hHU hHC k := by rw [hq, inv_one, one_mul]
    have h1 : ψ ∈ (⊥ : Subgroup _) := by
      rw [← hK.T_plus_inf_centralizer_eq_bot hab hTH]
      exact ⟨hψT, hψC⟩
    exact (hone ⟨e, heH⟩).1 (Subgroup.mem_bot.1 h1)
  have h := A6L24.relIndex_le_four (hKH.trans hHQ) (hAH.trans hHQ) (hAH.trans hHK) hαs hαk
    hfaith hsq
  rwa [inf_comm (pCoreOf 2 H)] at h

omit hab in

theorem KData.not_L24_F4 (hhat : ¬ IsHatA6 L)
    (hNU : ¬ LieModel G .PSU 4 3 1) (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    (h13314 : Stmt13_3_14_F4) (hLem : Lem1374One_F4) (h1352 : Stmt13_5_2_F4) (h51 : AsB51)
    (h13719 : Lem13719L1K_F4) (hab : IsElemAbelian 2 (conjClosure S.V3 H)) (hK : C.KData B K) :
    ¬ BinaryNaturalSL (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
        (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
          commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 2 2 := by
  intro hL
  have hKH : K ≤ H := le_of_mem_cComp hK.2.2.1
  have hHK := hK.le_normalizer_F4 hNS h13315 h1356two hH hab hhat hNU hLem
  have hL1K : S.L1 ≤ K := h13719 G T L V S hNS hNU hhat H hH hab hna C B K hK hL
  obtain ⟨α, hαs, hαk⟩ := exists_alpha_L24_F4 hNS h13315 h1356two hH hKH hL
  obtain ⟨c₁, hc₁L, hc₁3, hc₁O, hν⟩ := C.nu_O2L1_eq_F4 hNS h13315 h1356two hH hab hhat hna h13314
  have hle4 := hK.relIndex_A_le_four_F4 hNS h13315 h1356two hH hab hhat hNU hLem hαs hαk
  have hc₁Q := S.not_mem_QH_of_L1_F4 hNS h13315 h1356two hH hc₁L hc₁O
  have hO := S.exists_comm_not_mem_A5 hhat hH hKH hHK hL1K hαs hαk hc₁L hc₁3 hc₁Q
  have hU := sixteen_le_nu_L24_F4 hNS h13315 h1356two hH hKH hL (hL1K hc₁L) hc₁3 hc₁Q
  have hKU0 := hK.le_centralizer_U0_F4 hNS h13315 h1356two hH hhat hNU hna h13314 hLem h1352 h51 hab
  have h5 := S.four_pow_five_le_nu_F4 hNS h13315 h1356two hH hab hL1K hKU0 hc₁L hc₁3 hO hU
  rw [hν] at h5
  have hr := Nat.pow_le_pow_left hle4 2
  have h6 : 4 ^ 5 ≤ 16 * 4 ^ 2 := h5.trans (Nat.mul_le_mul_left 16 hr)
  norm_num at h6

end Conf

end KTilde

end Setting4

end CFSG.Quasithin.H13.A6

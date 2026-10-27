module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConf
public import CFSG.Quasithin.Vol2.KGFactC31J4Gen
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213FFe
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E14Iso
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E17Trans
public import CFSG.Quasithin.Vol2.Ch5Sec1L34D33
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Quasithin.Vol2.KGFactC31Concl
public import CFSG.Quasithin.Vol2.KGFactC31M22RefBase
public import CFSG.Quasithin.Vol2.KGFactC31M23Cases

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.H13.Ch4.E443
open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.M23
open scoped IsMulCommutative Matrix

private theorem not_isPGroup_two_of_three_dvd {Γ : Type*} [Group Γ] [Finite Γ]
    {H : Subgroup Γ} (h3 : 3 ∣ Nat.card ↥H) : ¬ IsPGroup 2 ↥H := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three (hk ▸ h3)) (by norm_num)

private theorem pCoreOf_eq_of_refData {Γ : Type} [Group Γ] [Finite Γ] {k : ℕ} {v : Fin k → Γ}
    (hv : EBasis v) {H : Subgroup Γ} (hd : RefData (eSub hv) H) (hE2 : IsPGroup 2 ↥(eSub hv))
    (hH2 : ¬ IsPGroup 2 ↥H) : pCoreOf 2 H = eSub hv :=
  pCoreOf_eq_of_max hd.le hd.norm hE2 hd.simple hH2

private theorem isPGroup_eSub_duad :
    IsPGroup 2 ↥(eSub basis_duad) :=
  IsPGroup.of_card (n := 4) (card_eSub basis_duad)

private theorem isPGroup_eSub_w :
    IsPGroup 2 ↥(eSub basis_w) :=
  IsPGroup.of_card (n := 4) (card_eSub basis_w)

private theorem isPGroup_eSub_e8 :
    IsPGroup 2 ↥(eSub basis_e8) :=
  IsPGroup.of_card (n := 3) (card_eSub basis_e8)

theorem conclK_m23_duad
    (MK : Subgroup G₀) : ConclK G₀ Mduad (eSub basis_duad) MK := by
  unfold ConclK
  have hO : pCoreOf 2 Mduad = eSub basis_duad :=
    pCoreOf_eq_of_refData basis_duad refData_duad isPGroup_eSub_duad
      (not_isPGroup_two_of_three_dvd (by rw [card_Mduad]; norm_num))
  have hVM : eSub basis_duad ≤ Mduad := hO ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 Mduad
  have hC : Mduad ⊓ Subgroup.centralizer (eSub basis_duad : Set G₀) ≤ eSub basis_duad :=
    inf_le_right.trans cent_duad
  let α₀ := Duad.f4Hom basis_duad Mduad_le_f4Stab Mduad_det
  have hker₀ : α₀.ker = (eSub basis_duad).subgroupOf Mduad := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      have h2 : Duad.f4Rep basis_duad (Subgroup.inclusion Mduad_le_f4Stab x) = 1 :=
        congrArg Subtype.val h1
      exact hC ⟨x.2, (Duad.f4Rep_eq_one_iff basis_duad _).mp h2⟩
    · intro hx
      apply Subtype.ext
      refine (Duad.f4Rep_eq_one_iff basis_duad (Subgroup.inclusion Mduad_le_f4Stab x)).mpr ?_
      exact Subgroup.mem_centralizer_iff.mpr fun y hy => eSub_comm basis_duad _ _ hy hx
  have hcM : Nat.card ↥Mduad = 960 := card_Mduad
  have hsurj₀ : Function.Surjective α₀ := by
    have h1 := CFSG.Quasithin.KGC31.M22.card_range_eq hVM α₀ hker₀
    rw [card_eSub, hcM] at h1
    have h2 : Nat.card α₀.range = Nat.card ↥(StatedSL 2 Duad.F4) := by
      rw [Duad.card_statedSL]; omega
    rw [← MonoidHom.range_eq_top]
    exact Subgroup.eq_top_of_card_eq _ h2
  have hpk : CFSG.pCore 2 ↥Mduad = α₀.ker := by
    rw [← Hex.pCoreOf_subgroupOf', hO, hker₀]
  let eQ : ↥Mduad ⧸ CFSG.pCore 2 ↥Mduad ≃* ↥(StatedSL 2 Duad.F4) :=
    (QuotientGroup.quotientMulEquivOfEq hpk).trans
      (QuotientGroup.quotientKerEquivOfSurjective α₀ hsurj₀)
  have hpsl : IsPSL 2 2 2 (↥Mduad ⧸ CFSG.pCore 2 ↥Mduad) := Duad.isPSL_of_equiv eQ
  have hcardX : Nat.card (↥Mduad ⧸ CFSG.pCore 2 ↥Mduad) = 60 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_four hpsl
  have hq : CFSG.IsQuasisimple (↥Mduad ⧸ CFSG.pCore 2 ↥Mduad) :=
    CFSG.Quasithin.H13.isQuasisimple_of_isPSL hpsl
      (by rw [hcardX]; norm_num) (by rw [hcardX]; norm_num)
  have hLM : LieModel (↥Mduad ⧸ CFSG.pCore 2 ↥Mduad) .PSL 2 2 2 :=
    Or.inl ⟨by decide, hpsl⟩
  have hshape : Shape443 (↥Mduad ⧸ CFSG.pCore 2 ↥Mduad) :=
    Or.inl ⟨2, by norm_num, hLM⟩
  let β : ↥(eSub basis_duad) →* Multiplicative (Fin 2 → Duad.F4) :=
    (AddMonoidHom.toMultiplicative Duad.toF4Hom).comp (ecoords basis_duad).toMonoidHom
  have hβ : ∀ x, Multiplicative.toAdd (β x) =
      Duad.toF4 (Multiplicative.toAdd (ecoords basis_duad x)) := fun _ => rfl
  have hβinj : Function.Injective β :=
    (Multiplicative.ofAdd.injective.comp Duad.toF4_injective).comp
      (ecoords basis_duad).injective
  have hβsurj : Function.Surjective β := by
    intro y
    obtain ⟨c, hc⟩ := Duad.toF4_surjective (Multiplicative.toAdd y)
    refine ⟨(ecoords basis_duad).symm (Multiplicative.ofAdd c), ?_⟩
    apply Multiplicative.toAdd.injective
    rw [hβ, MulEquiv.apply_symm_apply, toAdd_ofAdd, hc]
  have hsec : IsNaturalSection Mduad (eSub basis_duad) ⊥
      ((eSub basis_duad).subgroupOf Mduad) (StatedSL 2 Duad.F4) := by
    refine ⟨Mduad_le_eNorm, α₀, hsurj₀, hker₀, β, hβsurj, ?_, ?_⟩
    · rw [Subgroup.bot_subgroupOf]
      exact (MonoidHom.ker_eq_bot_iff β).mpr hβinj
    · intro a u w hw
      rw [hβ, hβ, ecoords_conj basis_duad ⟨a, Mduad_le_eNorm a.2⟩ u w hw]
      exact Duad.toF4_conj basis_duad (Subgroup.inclusion Mduad_le_f4Stab a) _
  have hsum : IsSumOfNaturalModules Mduad (eSub basis_duad) ⊥
      ((eSub basis_duad).subgroupOf Mduad) (StatedSL 2 Duad.F4) false 1 :=
    (isNaturalSection_iff_isSumOfNaturalModules_one _ _ bot_le).mp hsec
  have hcommV : IsMulCommutative ↥(eSub basis_duad) :=
    IsMulCommutative.of_setLike_mul_comm fun x hx y hy => eSub_comm basis_duad x y hx hy
  letI : IsMulCommutative ↥(eSub basis_duad) := hcommV
  have hFFM : IsFFModule (autOn Mduad (eSub basis_duad)) :=
    FFn.isFFModule_autOn_of_sum (n := 1) (k := 1) (by decide) le_rfl le_rfl hsum
  have hFF : IsFFModule (autOn (Subgroup.normalizer (eSub basis_duad : Set G₀))
      (eSub basis_duad)) :=
    isFFModule_of_le (autOn_mono' Mduad_le_eNorm) hFFM
  refine Or.inl ⟨hq, hshape, Or.inl ⟨⟨hcommV, hFF⟩, ?_, ?_, ?_, ?_⟩⟩
  ·
    intro h3
    have h1 := LieModel.card_psl_three_two h3
    rw [hcardX] at h1
    norm_num at h1
  ·
    intro h4
    have h1 := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two
      (h4.statedClassicalModel (by decide))
    rw [hcardX] at h1
    norm_num at h1
  ·
    rintro ⟨-, hc, -⟩
    rw [F420.center_eq_bot_of_statedPSL hpsl] at hc
    rw [Subgroup.card_bot] at hc
    norm_num at hc
  ·
    intro _ h64
    rw [card_eSub] at h64
    norm_num at h64

private noncomputable def quotEquiv_m23_w :
    ↥Mw ⧸ CFSG.pCore 2 ↥Mw ≃* ↥(alternatingGroup (Fin 7)) :=
  (QuotientGroup.quotientMulEquivOfEq (by
      rw [← Hex.pCoreOf_subgroupOf',
        pCoreOf_eq_of_refData basis_w refData_w isPGroup_eSub_w
          (not_isPGroup_two_of_three_dvd (by rw [card_Mw]; norm_num)),
        ker_wAlt])).trans
    (QuotientGroup.quotientKerEquivOfSurjective wAlt wAlt_surjective)

private theorem quasisimple_quot_m23_w :
    CFSG.IsQuasisimple (↥Mw ⧸ CFSG.pCore 2 ↥Mw) :=
  CFSG.IsQuasisimple.of_mulEquiv quotEquiv_m23_w
    (CFSG.Quasithin.KGC31.Hex.isQuasisimple_of_simple A7.alt7_simple A7.alt7_nonabelian)

private theorem card_quot_m23_w :
    Nat.card (↥Mw ⧸ CFSG.pCore 2 ↥Mw) = 2520 := by
  rw [Nat.card_congr quotEquiv_m23_w.toEquiv, A7.card_alt7]

private theorem shape_quot_m23_w :
    Shape443 (↥Mw ⧸ CFSG.pCore 2 ↥Mw) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨quotEquiv_m23_w⟩))))

private theorem isFFModule_m23_w
    [IsMulCommutative ↥(eSub basis_w)] : IsFFModule (autOn Mw (eSub basis_w)) := by
  let V := eSub basis_w
  letI : IsMulCommutative ↥V := ‹IsMulCommutative ↥(eSub basis_w)›
  let ρ : ↥Mw →* MulAut ↥V :=
    (conjAct V).comp (Subgroup.inclusion Mw_le_eNorm)
  have hρapply : ∀ (x : ↥Mw) (v : ↥V), ((ρ x) v : G₀) =
      (x : G₀) * (v : G₀) * (x : G₀)⁻¹ := fun x v =>
    CFSG.Quasithin.AutOn.coe_conjAct_apply V ⟨x, Mw_le_eNorm x.2⟩ v
  have hρker : ρ.ker = V.subgroupOf Mw := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      change conjAct V ⟨x, Mw_le_eNorm x.2⟩ = 1 at h
      have hmem : (x : G₀) ∈ Subgroup.centralizer (V : Set G₀) :=
        (CFSG.Quasithin.AutOn.conjAct_eq_one_iff (V := V) ⟨x, Mw_le_eNorm x.2⟩).mp h
      exact cent_w hmem
    · intro hx
      have hmem : (x : G₀) ∈ Subgroup.centralizer (V : Set G₀) :=
        Subgroup.mem_centralizer_iff.mpr fun y hy => eSub_comm basis_w y x hy hx
      show conjAct V ⟨x, Mw_le_eNorm x.2⟩ = 1
      exact (CFSG.Quasithin.AutOn.conjAct_eq_one_iff (V := V) ⟨x, Mw_le_eNorm x.2⟩).mpr hmem
  have hkerρw : wAlt.ker ≤ ρ.ker := by rw [hρker, ker_wAlt]
  let ρbar : ↥(alternatingGroup (Fin 7)) →* MulAut ↥V :=
    MonoidHom.liftOfSurjective wAlt wAlt_surjective ⟨ρ, hkerρw⟩
  have hρbar_apply : ∀ x : ↥Mw, ρbar (wAlt x) = ρ x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply wAlt _ _ ⟨ρ, hkerρw⟩ x
  have hρbar_ker : ρbar.ker = ⊥ := by
    ext y
    constructor
    · intro hy
      rw [Subgroup.mem_bot]
      obtain ⟨x, rfl⟩ := wAlt_surjective y
      have h1 : ρ x = 1 := by rw [← hρbar_apply x]; exact hy
      have h1' : x ∈ ρ.ker := by rwa [MonoidHom.mem_ker]
      rw [hρker, Subgroup.mem_subgroupOf] at h1'
      rw [← MonoidHom.mem_ker, ker_wAlt, Subgroup.mem_subgroupOf]
      exact h1'
    · intro hy
      rw [Subgroup.mem_bot] at hy
      rw [MonoidHom.mem_ker, hy, MonoidHom.map_one]
  have hρbar_inj : Function.Injective ρbar := (MonoidHom.ker_eq_bot_iff ρbar).mp hρbar_ker
  let E : Subgroup (MulAut ↥V) := (ρbar.comp FFe.k7).range
  have hcomp_inj : Function.Injective (ρbar.comp FFe.k7) := hρbar_inj.comp FFe.k7_injective
  have hEcard : Nat.card E = 4 := by
    change Nat.card ↥((ρbar.comp FFe.k7).range) = 4
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hcomp_inj, Subgroup.card_top]
    show Nat.card (Fin 2 → ZMod 2) = 4
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]
    rfl
  have hE_le : E ≤ autOn Mw V := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨x, hx⟩ := wAlt_surjective (FFe.k7 v)
    have hρx : ρ x = ρbar (FFe.k7 v) := by
      rw [← hρbar_apply x, hx]
    change ρbar (FFe.k7 v) ∈ autOn Mw V
    rw [← hρx]
    exact CFSG.Quasithin.AutOn.conjAct_mem_autOn (X := Mw) ⟨x, Mw_le_eNorm x.2⟩ x.2
  have hE2 : ∀ e ∈ E, e ^ 2 = 1 := by
    rintro _ ⟨v, rfl⟩
    rw [← map_pow]
    have hv : v ^ 2 = 1 := by
      apply Multiplicative.toAdd.injective
      funext j
      simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul,
        Nat.cast_ofNat]
      exact (show ∀ x : ZMod 2, 2 * x = 0 by decide) _
    rw [hv, map_one]
  have hNE : E ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card E = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hEcard] at h1
    norm_num at h1
  have hEcomm : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e := by
    rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
    change ρbar (FFe.k7 v) * ρbar (FFe.k7 w) = ρbar (FFe.k7 w) * ρbar (FFe.k7 v)
    calc ρbar (FFe.k7 v) * ρbar (FFe.k7 w)
        = ρbar (FFe.k7 (v * w)) := by rw [← map_mul, ← map_mul (f := FFe.k7) v w]
      _ = ρbar (FFe.k7 (w * v)) := by rw [mul_comm v w]
      _ = ρbar (FFe.k7 w * FFe.k7 v) := by rw [map_mul (f := FFe.k7) w v]
      _ = ρbar (FFe.k7 w) * ρbar (FFe.k7 v) := map_mul ρbar _ _
  let τ : MulAut ↥V := ρbar FFe.t7
  have hτ3 : τ ^ 3 = 1 := by rw [← map_pow, FFe.t7_pow_three, map_one]
  have hτ1 : τ ≠ 1 := by
    intro h
    exact FFe.t7_ne_one (hρbar_inj (h.trans (map_one ρbar).symm))
  have hτE : ∀ e ∈ E, e * τ = τ * e := by
    rintro _ ⟨v, rfl⟩
    change ρbar (FFe.k7 v) * ρbar FFe.t7 = ρbar FFe.t7 * ρbar (FFe.k7 v)
    calc ρbar (FFe.k7 v) * ρbar FFe.t7
        = ρbar (FFe.k7 v * FFe.t7) := (map_mul ρbar _ _).symm
      _ = ρbar (FFe.t7 * FFe.k7 v) := by rw [FFe.t7_comm]
      _ = ρbar FFe.t7 * ρbar (FFe.k7 v) := map_mul ρbar _ _
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => by
    rw [pow_two]
    exact Subtype.ext (eSub_sq basis_w (v : G₀) v.2)
  have hfix : 4 ≤ Nat.card (fixV E) := FFe.four_le_card_fixV hV2 hE2 hτ3 hτ1 hτE
  refine ⟨E, hE_le, hNE, ⟨hEcomm, hE2⟩, ?_⟩
  rw [card_eSub, hEcard]
  have h4 := Nat.mul_le_mul_left 4 hfix
  norm_num at h4 ⊢
  exact h4

theorem conclK_m23_w
    (MK : Subgroup G₀) : ConclK G₀ Mw (eSub basis_w) MK := by
  unfold ConclK
  have hq := quasisimple_quot_m23_w
  have hcardX := card_quot_m23_w
  have hshape := shape_quot_m23_w
  have hcommV : IsMulCommutative ↥(eSub basis_w) :=
    IsMulCommutative.of_setLike_mul_comm fun x hx y hy => eSub_comm basis_w x y hx hy
  letI : IsMulCommutative ↥(eSub basis_w) := hcommV
  have hFF : IsFFModule (autOn (Subgroup.normalizer (eSub basis_w : Set G₀))
      (eSub basis_w)) := by
    have h := isFFModule_m23_w
    rwa [Mw_eq] at h
  refine Or.inl ⟨hq, hshape, Or.inl ⟨⟨hcommV, hFF⟩, ?_, ?_, ?_, ?_⟩⟩
  ·
    intro h3
    have h1 := LieModel.card_psl_three_two h3
    rw [hcardX] at h1
    norm_num at h1
  ·
    intro h4
    have h1 := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two
      (h4.statedClassicalModel (by decide))
    rw [hcardX] at h1
    norm_num at h1
  ·
    rintro ⟨-, hc, -⟩
    rw [F420.center_eq_bot_of_mulEquiv' quotEquiv_m23_w
      (alternatingGroup.center_eq_bot (by norm_num))] at hc
    rw [Subgroup.card_bot] at hc
    norm_num at hc
  ·
    intro _ h64
    rw [card_eSub] at h64
    norm_num at h64

theorem conclK_m23_e8
    (MK : Subgroup G₀) : ConclK G₀ (eNorm basis_e8) (eSub basis_e8) MK := by
  unfold ConclK
  have hO : pCoreOf 2 (eNorm basis_e8) = eSub basis_e8 :=
    pCoreOf_eq_of_refData basis_e8 refData_e8 isPGroup_eSub_e8
      (not_isPGroup_two_of_three_dvd (by rw [card_eNorm_e8]; norm_num))
  have hVL : eSub basis_e8 ≤ eNorm basis_e8 :=
    hO ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 (eNorm basis_e8)
  let α := E8.e3Hom basis_e8 (X := eNorm basis_e8) le_rfl
  have hker₀ : α.ker = (eSub basis_e8).subgroupOf (eNorm basis_e8) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, E8.e3Hom_eq_one_iff]
    constructor
    · intro h
      exact cent_e8 h
    · intro hx
      exact Subgroup.mem_centralizer_iff.mpr fun y hy => eSub_comm basis_e8 _ _ hy hx
  have hcM : Nat.card ↥(eNorm basis_e8) = 1344 := card_eNorm_e8
  have hsurj₀ : Function.Surjective α := by
    have h1 := CFSG.Quasithin.KGC31.M22.card_range_eq hVL α hker₀
    rw [card_eSub, hcM] at h1
    have h2 : Nat.card α.range = Nat.card ↥(StatedSL 3 (ZMod 2)) := by
      rw [E8.card_statedSL3]; omega
    rw [← MonoidHom.range_eq_top]
    exact Subgroup.eq_top_of_card_eq _ h2
  have hpk : CFSG.pCore 2 ↥(eNorm basis_e8) = α.ker := by
    rw [← Hex.pCoreOf_subgroupOf', hO, hker₀]
  let eQ : ↥(eNorm basis_e8) ⧸ CFSG.pCore 2 ↥(eNorm basis_e8) ≃*
      ↥(StatedSL 3 (ZMod 2)) :=
    (QuotientGroup.quotientMulEquivOfEq hpk).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hsurj₀)
  have hpsl : IsPSL 3 2 1 (↥(eNorm basis_e8) ⧸ CFSG.pCore 2 ↥(eNorm basis_e8)) :=
    E8.isPSL_of_equiv3 eQ
  have hcardX : Nat.card (↥(eNorm basis_e8) ⧸
      CFSG.pCore 2 ↥(eNorm basis_e8)) = 168 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two hpsl
  have hq : CFSG.IsQuasisimple (↥(eNorm basis_e8) ⧸
      CFSG.pCore 2 ↥(eNorm basis_e8)) :=
    CFSG.Quasithin.H13.isQuasisimple_of_isPSL hpsl
      (by rw [hcardX]; norm_num) (by rw [hcardX]; norm_num)
  have hLM : LieModel (↥(eNorm basis_e8) ⧸ CFSG.pCore 2 ↥(eNorm basis_e8))
      .PSL 3 2 1 := Or.inl ⟨by decide, hpsl⟩
  have hshape : Shape443 (↥(eNorm basis_e8) ⧸ CFSG.pCore 2 ↥(eNorm basis_e8)) :=
    Or.inr (Or.inl hLM)
  let β : ↥(eSub basis_e8) →* Multiplicative (Fin 3 → ZMod 2) :=
    (ecoords basis_e8).toMonoidHom
  have hβinj : Function.Injective β := (ecoords basis_e8).injective
  have hβsurj : Function.Surjective β := (ecoords basis_e8).surjective
  have hsec : IsNaturalSection (eNorm basis_e8) (eSub basis_e8) ⊥
      ((eSub basis_e8).subgroupOf (eNorm basis_e8)) (StatedSL 3 (ZMod 2)) := by
    refine ⟨le_rfl, α, hsurj₀, hker₀, β, hβsurj, ?_, ?_⟩
    · rw [Subgroup.bot_subgroupOf]
      exact (MonoidHom.ker_eq_bot_iff β).mpr hβinj
    · intro a u w hw
      exact ecoords_conj basis_e8 a u w hw
  have hsum : IsSumOfNaturalModules (eNorm basis_e8) (eSub basis_e8) ⊥
      ((eSub basis_e8).subgroupOf (eNorm basis_e8)) (StatedSL 3 (ZMod 2)) false 1 :=
    (isNaturalSection_iff_isSumOfNaturalModules_one _ _ bot_le).mp hsec
  have hcommV : IsMulCommutative ↥(eSub basis_e8) :=
    IsMulCommutative.of_setLike_mul_comm fun x hx y hy => eSub_comm basis_e8 x y hx hy
  letI : IsMulCommutative ↥(eSub basis_e8) := hcommV
  have hFF : IsFFModule (autOn (Subgroup.normalizer (eSub basis_e8 : Set G₀))
      (eSub basis_e8)) := by
    exact FFn.isFFModule_autOn_of_sum (n := 2) (k := 1) (by decide) le_rfl (by norm_num) hsum
  have hbin : BinaryNaturalSL (V := ↥(eSub basis_e8)) (autOn (eNorm basis_e8) (eSub basis_e8))
      ⊤ ⊥ 3 1 := by
    refine ⟨ZMod 2, inferInstance, inferInstance, by norm_num, ?_⟩
    exact T4213N.realizes_of_equiv le_rfl (FFModel.nat (StatedSL 3 (ZMod 2)))
      (fun _ => trivial) (fun x => Subgroup.mem_bot)
      (fun _ => rfl)
      α hsurj₀
      (fun a ha => by
        have hmem : (a : G₀) ∈ eSub basis_e8 := by
          have : a ∈ α.ker := ha
          rwa [hker₀, Subgroup.mem_subgroupOf] at this
        exact Subgroup.mem_centralizer_iff.mpr fun y hy => eSub_comm basis_e8 _ _ hy hmem)
      (MulEquiv.ofBijective β ⟨hβinj, hβsurj⟩)
      (fun a w w' hw => by
        show β w' = (FFModel.nat (StatedSL 3 (ZMod 2))).act (α a) (β w)
        apply Multiplicative.toAdd.injective
        show Multiplicative.toAdd (β w') = (((α a : ↥(StatedSL 3 (ZMod 2))) :
          Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
          Multiplicative.toAdd (β w)
        rw [E8.e3Hom_coe]
        exact ecoords_conj basis_e8 a w w' hw)
  have hnat : IsNaturalSumUnder 3 (eNorm basis_e8) (eSub basis_e8) := by
    refine ⟨1, fun _ => eSub basis_e8, by norm_num, ?_, ?_, iSupIndep_subsingleton _, ?_⟩
    · intro i
      exact ⟨le_rfl, le_rfl, ⟨hcommV, hbin⟩⟩
    · intro i j
      exact isXSectionIso₂_of_isLEquiv (φ := MulEquiv.refl _) (fun l hl a a' ha' => ha')
    · rw [iSup_const]
  refine Or.inl ⟨hq, hshape, Or.inl ⟨⟨hcommV, hFF⟩, ?_, ?_, ?_, ?_⟩⟩
  ·
    intro _
    exact hnat
  ·
    intro h4
    have h1 := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two
      (h4.statedClassicalModel (by decide))
    rw [hcardX] at h1
    norm_num at h1
  ·
    rintro ⟨-, hc, -⟩
    rw [F420.center_eq_bot_of_statedPSL hpsl] at hc
    rw [Subgroup.card_bot] at hc
    norm_num at hc
  ·
    intro _ h64
    rw [card_eSub] at h64
    norm_num at h64


end CFSG.SectionRank.QTK.Insp443

end

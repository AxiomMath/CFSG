module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConf
public import CFSG.Quasithin.Vol2.KGFactC31M22Mod
public import CFSG.Quasithin.Vol2.KGFactC31J4Gen
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213FFa
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E14Iso
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E17Trans
public import CFSG.Quasithin.Vol2.Ch5Sec1L34D33
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213Nat
public import CFSG.Quasithin.Vol2.Ch4Sec4L446Nat

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.H13.Ch4.E443
open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.M22
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

private theorem isPGroup_eSub_hex :
    IsPGroup 2 ↥(eSub basis_hex) :=
  IsPGroup.of_card (n := 4) (card_eSub basis_hex)

private theorem isPGroup_eSub_duad :
    IsPGroup 2 ↥(eSub basis_duad) :=
  IsPGroup.of_card (n := 4) (card_eSub basis_duad)

private theorem isPGroup_eSub_e8 :
    IsPGroup 2 ↥(eSub basis_e8) :=
  IsPGroup.of_card (n := 3) (card_eSub basis_e8)

theorem pCoreOf_Mhex :
    pCoreOf 2 Mhex = eSub basis_hex :=
  pCoreOf_eq_of_refData basis_hex refData_hex isPGroup_eSub_hex
    (not_isPGroup_two_of_three_dvd (by rw [card_Mhex]; norm_num))

theorem nonempty_Mhex_quot_mulEquiv :
    Nonempty (↥Mhex ⧸ CFSG.pCore 2 ↥Mhex ≃* alternatingGroup (Fin 6)) := by
  have hO := pCoreOf_Mhex
  have hVL : eSub basis_hex ≤ Mhex := hO ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 Mhex
  have hC : Mhex ⊓ Subgroup.centralizer (eSub basis_hex : Set G₀) ≤ eSub basis_hex :=
    inf_le_right.trans cent_hex
  have hcard : Nat.card ↥Mhex = 360 * 16 := by rw [card_Mhex]
  obtain ⟨α, hα, hker, -⟩ := Hex.exists_ovAlt basis_hex Mhex_le_ovStab hVL hC hcard
  have hpk : α.ker = CFSG.pCore 2 ↥Mhex := by
    rw [hker, ← hO, Hex.pCoreOf_subgroupOf']
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hpk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα)⟩

theorem conclK_m22_hex
    (MK : Subgroup G₀) : ConclK G₀ Mhex (eSub basis_hex) MK := by
  unfold ConclK
  have hO := pCoreOf_Mhex
  have hVL : eSub basis_hex ≤ Mhex := hO ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 Mhex
  have hC : Mhex ⊓ Subgroup.centralizer (eSub basis_hex : Set G₀) ≤ eSub basis_hex :=
    inf_le_right.trans cent_hex
  have hcard : Nat.card ↥Mhex = 360 * 16 := by rw [card_Mhex]
  obtain ⟨α, hα, hker, hαperm⟩ :=
    Hex.exists_ovAlt basis_hex Mhex_le_ovStab hVL hC hcard
  have hpk : α.ker = CFSG.pCore 2 ↥Mhex := by
    rw [hker, ← hO, Hex.pCoreOf_subgroupOf']
  obtain ⟨eQ⟩ := nonempty_Mhex_quot_mulEquiv
  have hq : CFSG.IsQuasisimple (↥Mhex ⧸ CFSG.pCore 2 ↥Mhex) :=
    CFSG.IsQuasisimple.of_mulEquiv eQ
      (Hex.isQuasisimple_of_simple Hex.alt6_simple Hex.alt6_nonabelian)
  have hshape : Shape443 (↥Mhex ⧸ CFSG.pCore 2 ↥Mhex) :=
    Or.inr (Or.inr (Or.inr (Or.inl ⟨eQ⟩)))
  have hcardX : Nat.card (↥Mhex ⧸ CFSG.pCore 2 ↥Mhex) = 360 := by
    rw [Nat.card_congr eQ.toEquiv, Hex.card_alt6]
  let β : ↥(eSub basis_hex) →* Multiplicative (AltHeart 6) :=
    (AddMonoidHom.toMultiplicative Hex.hmap).comp (Hex.coords basis_hex).toMonoidHom
  have hβ : ∀ x, Multiplicative.toAdd (β x) =
      Hex.hmap (Multiplicative.toAdd (Hex.coords basis_hex x)) := fun _ => rfl
  have hβinj : Function.Injective β :=
    (Multiplicative.ofAdd.injective.comp Hex.hmap_injective).comp (Hex.coords basis_hex).injective
  have hβsurj : Function.Surjective β := by
    intro y
    obtain ⟨c, hc⟩ := Hex.hmap_surjective (Multiplicative.toAdd y)
    refine ⟨(Hex.coords basis_hex).symm (Multiplicative.ofAdd c), ?_⟩
    apply Multiplicative.toAdd.injective
    rw [hβ, MulEquiv.apply_symm_apply, toAdd_ofAdd, hc]
  have hequiv : ∀ (ℓ : ↥Mhex) (u w : ↥(eSub basis_hex)),
      (w : G₀) = ℓ * u * ℓ⁻¹ →
        Multiplicative.toAdd (β w) =
          FFh.hAct 6 (α ℓ : Equiv.Perm (Fin 6)) (Multiplicative.toAdd (β u)) := by
    intro ℓ u w hw
    set g : ↥(Hex.ovStab basis_hex) := Subgroup.inclusion Mhex_le_ovStab ℓ with hg
    have hcw : Multiplicative.toAdd (Hex.coords basis_hex w) =
        eMat basis_hex ⟨g, g.2.1⟩ *ᵥ Multiplicative.toAdd (Hex.coords basis_hex u) := by
      apply eElt_injective basis_hex
      rw [Hex.eElt_coords, ← conj_eq_eElt_mulVec, Hex.eElt_coords]
      exact hw
    rw [hβ, hβ, hcw, Hex.hmap_apply, Hex.hmap_apply, FFh.hAct_mk]
    congr 1
    apply Subtype.ext
    change Hex.ind _ = fun i => Hex.ind (Multiplicative.toAdd (Hex.coords basis_hex u))
      ((α ℓ : Equiv.Perm (Fin 6))⁻¹ i)
    rw [hαperm]
    exact Hex.ind_mulVec (Hex.mulVec_injective basis_hex _) (Hex.image_ovoid basis_hex g) _
  let hcommV : IsMulCommutative ↥(eSub basis_hex) :=
    IsMulCommutative.of_setLike_mul_comm fun x hx y hy => eSub_comm basis_hex x y hx hy
  letI : IsMulCommutative ↥(eSub basis_hex) := hcommV
  have hFFL : IsFFModule (autOn Mhex (eSub basis_hex)) :=
    FFn.isFFModule_autOn_of_equiv Mhex_le_eNorm
      ((FFh.heartAut 6).comp (alternatingGroup (Fin 6)).subtype) α hα
      (MulEquiv.ofBijective β ⟨hβinj, hβsurj⟩)
      (fun a u w hw => by
        show β w = FFh.heartAut 6 (α a) (β u)
        rw [FFh.heartAut_apply]
        exact congrArg Multiplicative.ofAdd (hequiv a u w hw))
      FFa.isFFModule_heart6
  have hFF : IsFFModule (autOn (Subgroup.normalizer (eSub basis_hex : Set G₀))
      (eSub basis_hex)) := by
    have h := hFFL
    rwa [Mhex_eq] at h
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
    rw [F420.center_eq_bot_of_mulEquiv' eQ (alternatingGroup.center_eq_bot (by norm_num))] at hc
    rw [Subgroup.card_bot] at hc
    norm_num at hc
  ·
    intro _ h64
    rw [card_eSub] at h64
    norm_num at h64

theorem conclK_m22_duad
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
    have h1 := M22.card_range_eq hVM α₀ hker₀
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

theorem conclK_m22_e8
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
    have h1 := M22.card_range_eq hVL α hker₀
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

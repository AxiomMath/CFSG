module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConf
public import CFSG.Quasithin.Vol2.KGFactC31HSMod
public import CFSG.Quasithin.Vol2.KGFactC31J4Gen
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213FFa
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
open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.HS
open scoped IsMulCommutative Matrix

private theorem not_isPGroup_two_of_three_dvd {Γ : Type*} [Group Γ] [Finite Γ]
    {H : Subgroup Γ} (h3 : 3 ∣ Nat.card ↥H) : ¬ IsPGroup 2 ↥H := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three (hk ▸ h3)) (by norm_num)

theorem conclK_hs_u16
    (MK : Subgroup G₀) :
    ConclK G₀ M16 (eSub basis_u16) MK := by
  unfold ConclK
  have hE2 : IsPGroup 2 ↥(eSub basis_u16) :=
    IsPGroup.of_card (n := 4) (card_eSub basis_u16)
  have hH2 : ¬ IsPGroup 2 ↥M16 :=
    not_isPGroup_two_of_three_dvd (by rw [card_M16]; norm_num)
  have hO : pCoreOf 2 M16 = eSub basis_u16 :=
    pCoreOf_eq_of_max refData_u16.le refData_u16.norm hE2 refData_u16.simple hH2
  have hVL : eSub basis_u16 ≤ M16 := hO ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 M16
  have hC : M16 ⊓ Subgroup.centralizer (eSub basis_u16 : Set G₀) ≤ eSub basis_u16 :=
    inf_le_right.trans cent_u16
  have hcard : Nat.card ↥M16 = 360 * 16 := by rw [card_M16]
  obtain ⟨α, hα, hker, hαperm⟩ :=
    Hex.exists_ovAlt basis_u16 M16_le_ovStab hVL hC hcard
  have hpk : α.ker = CFSG.pCore 2 ↥M16 := by
    rw [hker, ← hO, Hex.pCoreOf_subgroupOf']
  let eQ : ↥M16 ⧸ CFSG.pCore 2 ↥M16 ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.quotientMulEquivOfEq hpk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα)
  have hq : CFSG.IsQuasisimple (↥M16 ⧸ CFSG.pCore 2 ↥M16) :=
    CFSG.IsQuasisimple.of_mulEquiv eQ
      (Hex.isQuasisimple_of_simple Hex.alt6_simple Hex.alt6_nonabelian)
  have hshape : Shape443 (↥M16 ⧸ CFSG.pCore 2 ↥M16) :=
    Or.inr (Or.inr (Or.inr (Or.inl ⟨eQ⟩)))
  have hcardX : Nat.card (↥M16 ⧸ CFSG.pCore 2 ↥M16) = 360 := by
    rw [Nat.card_congr eQ.toEquiv, Hex.card_alt6]
  let β : ↥(eSub basis_u16) →* Multiplicative (AltHeart 6) :=
    (AddMonoidHom.toMultiplicative Hex.hmap).comp (Hex.coords basis_u16).toMonoidHom
  have hβ : ∀ x, Multiplicative.toAdd (β x) =
      Hex.hmap (Multiplicative.toAdd (Hex.coords basis_u16 x)) := fun _ => rfl
  have hβinj : Function.Injective β :=
    (Multiplicative.ofAdd.injective.comp Hex.hmap_injective).comp
      (Hex.coords basis_u16).injective
  have hβsurj : Function.Surjective β := by
    intro y
    obtain ⟨c, hc⟩ := Hex.hmap_surjective (Multiplicative.toAdd y)
    refine ⟨(Hex.coords basis_u16).symm (Multiplicative.ofAdd c), ?_⟩
    apply Multiplicative.toAdd.injective
    rw [hβ, MulEquiv.apply_symm_apply, toAdd_ofAdd, hc]
  have hequiv : ∀ (ℓ : ↥M16) (u w : ↥(eSub basis_u16)),
      (w : G₀) = ℓ * u * ℓ⁻¹ →
        Multiplicative.toAdd (β w) =
          FFh.hAct 6 (α ℓ : Equiv.Perm (Fin 6)) (Multiplicative.toAdd (β u)) := by
    intro ℓ u w hw
    set g : ↥(Hex.ovStab basis_u16) := Subgroup.inclusion M16_le_ovStab ℓ with hg
    have hcw : Multiplicative.toAdd (Hex.coords basis_u16 w) =
        eMat basis_u16 ⟨g, g.2.1⟩ *ᵥ Multiplicative.toAdd (Hex.coords basis_u16 u) := by
      apply eElt_injective basis_u16
      rw [Hex.eElt_coords, ← conj_eq_eElt_mulVec, Hex.eElt_coords]
      exact hw
    rw [hβ, hβ, hcw, Hex.hmap_apply, Hex.hmap_apply, FFh.hAct_mk]
    congr 1
    apply Subtype.ext
    change Hex.ind _ = fun i => Hex.ind (Multiplicative.toAdd (Hex.coords basis_u16 u))
      ((α ℓ : Equiv.Perm (Fin 6))⁻¹ i)
    rw [hαperm]
    exact Hex.ind_mulVec (Hex.mulVec_injective basis_u16 _) (Hex.image_ovoid basis_u16 g) _
  let hcommV : IsMulCommutative ↥(eSub basis_u16) :=
    IsMulCommutative.of_setLike_mul_comm fun x hx y hy => eSub_comm basis_u16 x y hx hy
  letI : IsMulCommutative ↥(eSub basis_u16) := hcommV
  have hFFL : IsFFModule (autOn M16 (eSub basis_u16)) :=
    FFn.isFFModule_autOn_of_equiv M16_le_eNorm
      ((FFh.heartAut 6).comp (alternatingGroup (Fin 6)).subtype) α hα
      (MulEquiv.ofBijective β ⟨hβinj, hβsurj⟩)
      (fun a u w hw => by
        show β w = FFh.heartAut 6 (α a) (β u)
        rw [FFh.heartAut_apply]
        exact congrArg Multiplicative.ofAdd (hequiv a u w hw))
      FFa.isFFModule_heart6
  have hFF : IsFFModule (autOn (Subgroup.normalizer (eSub basis_u16 : Set G₀))
      (eSub basis_u16)) :=
    isFFModule_of_le
      (Subgroup.map_mono (Subgroup.subgroupOf_mono
        (Subgroup.normalizer (eSub basis_u16 : Set G₀)) M16_le_eNorm)) hFFL
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

theorem conclK_hs_u8
    (MK : Subgroup G₀) :
    ConclK G₀ N8 (eSub basis_u8) MK := by
  unfold ConclK
  have hQ2 : IsPGroup 2 ↥Q8 := IsPGroup.of_card (n := 6) (by rw [card_Q8]; norm_num)
  have hH2 : ¬ IsPGroup 2 ↥N8 :=
    not_isPGroup_two_of_three_dvd (by rw [card_N8]; norm_num)
  haveI : IsSimpleGroup ↥(StatedSL 3 (ZMod 2)) := E8.isSimpleGroup_statedSL3
  have hO : pCoreOf 2 N8 = Q8 :=
    pCoreOf_eq_of_max Q8_le_N8 N8_le_normalizer_Q8 hQ2
      (simple_of_surj n8Hom n8Hom_surjective ker_n8Hom) hH2
  let α : ↥N8 →* ↥(StatedSL 3 (ZMod 2)) := E8.e3Hom basis_u8 N8_le_eNorm
  have hker₀ : α.ker = Q8.subgroupOf N8 := ker_n8Hom
  have hsurj₀ : Function.Surjective α := n8Hom_surjective
  have hpk : CFSG.pCore 2 ↥N8 = α.ker := by
    rw [← Hex.pCoreOf_subgroupOf', hO, hker₀]
  let eQ : ↥N8 ⧸ CFSG.pCore 2 ↥N8 ≃* ↥(StatedSL 3 (ZMod 2)) :=
    (QuotientGroup.quotientMulEquivOfEq hpk).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hsurj₀)
  have hpsl : IsPSL 3 2 1 (↥N8 ⧸ CFSG.pCore 2 ↥N8) := E8.isPSL_of_equiv3 eQ
  have hcardX : Nat.card (↥N8 ⧸ CFSG.pCore 2 ↥N8) = 168 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two hpsl
  have hq : CFSG.IsQuasisimple (↥N8 ⧸ CFSG.pCore 2 ↥N8) :=
    CFSG.Quasithin.H13.isQuasisimple_of_isPSL hpsl
      (by rw [hcardX]; norm_num) (by rw [hcardX]; norm_num)
  have hLM : LieModel (↥N8 ⧸ CFSG.pCore 2 ↥N8) .PSL 3 2 1 := Or.inl ⟨by decide, hpsl⟩
  have hshape : Shape443 (↥N8 ⧸ CFSG.pCore 2 ↥N8) := Or.inr (Or.inl hLM)
  let β : ↥(eSub basis_u8) →* Multiplicative (Fin 3 → ZMod 2) :=
    (ecoords basis_u8).toMonoidHom
  have hβinj : Function.Injective β := (ecoords basis_u8).injective
  have hβsurj : Function.Surjective β := (ecoords basis_u8).surjective
  have hsec : IsNaturalSection N8 (eSub basis_u8) ⊥ (Q8.subgroupOf N8)
      (StatedSL 3 (ZMod 2)) := by
    refine ⟨N8_le_eNorm, α, hsurj₀, hker₀, β, hβsurj, ?_, ?_⟩
    · rw [Subgroup.bot_subgroupOf]
      exact (MonoidHom.ker_eq_bot_iff β).mpr hβinj
    · intro a u w hw
      exact ecoords_conj basis_u8 ⟨a, N8_le_eNorm a.2⟩ u w hw
  have hsum : IsSumOfNaturalModules N8 (eSub basis_u8) ⊥ (Q8.subgroupOf N8)
      (StatedSL 3 (ZMod 2)) false 1 :=
    (isNaturalSection_iff_isSumOfNaturalModules_one _ _ bot_le).mp hsec
  let hcommV : IsMulCommutative ↥(eSub basis_u8) :=
    IsMulCommutative.of_setLike_mul_comm fun x hx y hy => eSub_comm basis_u8 x y hx hy
  letI : IsMulCommutative ↥(eSub basis_u8) := hcommV
  have hFFN : IsFFModule (autOn N8 (eSub basis_u8)) :=
    FFn.isFFModule_autOn_of_sum (n := 2) (k := 1) (by decide) le_rfl (by norm_num) hsum
  have hFF : IsFFModule (autOn (eNorm basis_u8) (eSub basis_u8)) := N8_eq ▸ hFFN
  have hbin : BinaryNaturalSL (V := ↥(eSub basis_u8)) (autOn N8 (eSub basis_u8))
      ⊤ ⊥ 3 1 := by
    have hkerα : ∀ a : ↥N8, α a = 1 →
        (a : G₀) ∈ Subgroup.centralizer (eSub basis_u8 : Set G₀) :=
      fun a ha => (E8.e3Hom_eq_one_iff basis_u8 N8_le_eNorm a).mp (by
        simpa only [α] using ha)
    refine ⟨ZMod 2, inferInstance, inferInstance, by norm_num, ?_⟩
    exact T4213N.realizes_of_equiv N8_le_eNorm (FFModel.nat (StatedSL 3 (ZMod 2)))
      (fun _ => trivial) (fun x => Subgroup.mem_bot)
      (fun _ => rfl)
      α hsurj₀ hkerα
      (MulEquiv.ofBijective β ⟨hβinj, hβsurj⟩)
      (fun a w w' hw => by
        show β w' = (FFModel.nat (StatedSL 3 (ZMod 2))).act (α a) (β w)
        apply Multiplicative.toAdd.injective
        show Multiplicative.toAdd (β w') = (((α a : ↥(StatedSL 3 (ZMod 2))) :
          Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
          Multiplicative.toAdd (β w)
        rw [E8.e3Hom_coe]
        exact ecoords_conj basis_u8 ⟨a, N8_le_eNorm a.2⟩ w w' hw)
  have hnat : IsNaturalSumUnder 3 N8 (eSub basis_u8) := by
    refine ⟨1, fun _ => eSub basis_u8, by norm_num, ?_, ?_, iSupIndep_subsingleton _, ?_⟩
    · intro i
      exact ⟨le_rfl, N8_le_eNorm, ⟨hcommV, hbin⟩⟩
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

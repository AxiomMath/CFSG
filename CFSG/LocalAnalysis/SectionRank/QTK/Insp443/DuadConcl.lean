module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConf
public import CFSG.Quasithin.Vol2.KGFactC31Duad
public import CFSG.Quasithin.Vol2.KGFactC31J4Gen
public import CFSG.Quasithin.Vol2.KGFactC31Concl
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213FFn
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E17Trans
public import CFSG.Quasithin.Vol2.Ch5Sec1L34D33
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E14Iso
public import CFSG.Quasithin.Vol2.KGFactC31Hex
public import CFSG.Quasithin.Vol2.KGFactC31Ident

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.H13.Ch4.E443
open CFSG.Quasithin.KGC31
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped IsMulCommutative Matrix

private theorem duad_not_isPGroup_two_of_three_dvd {Γ : Type*} [Group Γ] [Finite Γ]
    {H : Subgroup Γ} (h3 : 3 ∣ Nat.card ↥H) : ¬ IsPGroup 2 ↥H := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three (hk ▸ h3)) (by norm_num)

private theorem duad_pCoreOf_eq_of_refData {Γ : Type} [Group Γ] [Finite Γ] {k : ℕ}
    {v : Fin k → Γ} (hv : EBasis v) {H : Subgroup Γ} (hd : RefData (eSub hv) H)
    (hE2 : IsPGroup 2 ↥(eSub hv)) (hH2 : ¬ IsPGroup 2 ↥H) : pCoreOf 2 H = eSub hv :=
  pCoreOf_eq_of_max hd.le hd.norm hE2 hd.simple hH2

private theorem duad_ker_f4Hom {Γ : Type} [Group Γ] {v : Fin 4 → Γ} (hv : EBasis v)
    {M : Subgroup Γ} (hM : M ≤ Duad.f4Stab hv)
    (hdet : ∀ x : ↥M, (Duad.f4Mat (eMat hv ⟨x, (hM x.2).1⟩)).det = 1)
    (hcent : M ⊓ Subgroup.centralizer (eSub hv : Set Γ) ≤ eSub hv) :
    (Duad.f4Hom hv hM hdet).ker = (eSub hv).subgroupOf M := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h1
    have h2 : Duad.f4Rep hv (Subgroup.inclusion hM x) = 1 := congrArg Subtype.val h1
    exact hcent ⟨x.2, (Duad.f4Rep_eq_one_iff hv _).mp h2⟩
  · intro hx
    apply Subtype.ext
    refine (Duad.f4Rep_eq_one_iff hv (Subgroup.inclusion hM x)).mpr ?_
    exact Subgroup.mem_centralizer_iff.mpr fun y hy => eSub_comm hv _ _ hy hx

private theorem duad_surjective_f4Hom {Γ : Type} [Group Γ] {v : Fin 4 → Γ} (hv : EBasis v)
    {M : Subgroup Γ} (hle : eSub hv ≤ M) (hM : M ≤ Duad.f4Stab hv)
    (hdet : ∀ x : ↥M, (Duad.f4Mat (eMat hv ⟨x, (hM x.2).1⟩)).det = 1)
    (hker : (Duad.f4Hom hv hM hdet).ker = (eSub hv).subgroupOf M) (hcard : Nat.card M = 960) :
    Function.Surjective (Duad.f4Hom hv hM hdet) := by
  have h1 := CFSG.Quasithin.KGC31.card_range_eq hle (Duad.f4Hom hv hM hdet) hker
  rw [card_eSub, hcard] at h1
  have h2 : Nat.card (Duad.f4Hom hv hM hdet).range = Nat.card ↥(StatedSL 2 Duad.F4) := by
    rw [Duad.card_statedSL]; omega
  rw [← MonoidHom.range_eq_top]
  exact Subgroup.eq_top_of_card_eq _ h2

theorem duad_simple {G : Type} [Group G] [Finite G] {v : Fin 4 → G} (hv : EBasis v)
    {M : Subgroup G} (hle : eSub hv ≤ M) (hM : M ≤ Duad.f4Stab hv)
    (hdet : ∀ x : ↥M, (Duad.f4Mat (eMat hv ⟨x, (hM x.2).1⟩)).det = 1)
    (hcent : M ⊓ Subgroup.centralizer (eSub hv : Set G) ≤ eSub hv)
    (hcard : Nat.card M = 960) :
    ∀ K : Subgroup G, eSub hv ≤ K → K ≤ M → M ≤ Subgroup.normalizer (K : Set G) →
      K = eSub hv ∨ K = M := by
  have hker := duad_ker_f4Hom hv hM hdet hcent
  have := Duad.isSimpleGroup_statedSL
  exact CFSG.Quasithin.KGC31.simple_of_surj (Duad.f4Hom hv hM hdet)
    (duad_surjective_f4Hom hv hle hM hdet hker hcard) hker

theorem conclK_of_duad {G : Type} [Group G] [Finite G] {v : Fin 4 → G} (hv : EBasis v)
    {M : Subgroup G} (hd : RefData (eSub hv) M) (hM : M ≤ Duad.f4Stab hv)
    (hdet : ∀ x : ↥M, (Duad.f4Mat (eMat hv ⟨x, (hM x.2).1⟩)).det = 1)
    (hcard : Nat.card M = 960) (MK : Subgroup G) : ConclK G M (eSub hv) MK := by
  unfold ConclK
  have hO : pCoreOf 2 M = eSub hv :=
    duad_pCoreOf_eq_of_refData hv hd (IsPGroup.of_card (n := 4) (card_eSub hv))
      (duad_not_isPGroup_two_of_three_dvd (by rw [hcard]; norm_num))
  have hC : M ⊓ Subgroup.centralizer (eSub hv : Set G) ≤ eSub hv :=
    inf_le_right.trans hd.cent
  let α₀ := Duad.f4Hom hv hM hdet
  have hker₀ : α₀.ker = (eSub hv).subgroupOf M := duad_ker_f4Hom hv hM hdet hC
  have hsurj₀ : Function.Surjective α₀ := duad_surjective_f4Hom hv hd.le hM hdet hker₀ hcard
  have hpk : CFSG.pCore 2 ↥M = α₀.ker := by
    rw [← Hex.pCoreOf_subgroupOf', hO, hker₀]
  let eQ : ↥M ⧸ CFSG.pCore 2 ↥M ≃* ↥(StatedSL 2 Duad.F4) :=
    (QuotientGroup.quotientMulEquivOfEq hpk).trans
      (QuotientGroup.quotientKerEquivOfSurjective α₀ hsurj₀)
  have hpsl : IsPSL 2 2 2 (↥M ⧸ CFSG.pCore 2 ↥M) := Duad.isPSL_of_equiv eQ
  have hcardX : Nat.card (↥M ⧸ CFSG.pCore 2 ↥M) = 60 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_four hpsl
  have hq : CFSG.IsQuasisimple (↥M ⧸ CFSG.pCore 2 ↥M) :=
    CFSG.Quasithin.H13.isQuasisimple_of_isPSL hpsl
      (by rw [hcardX]; norm_num) (by rw [hcardX]; norm_num)
  have hLM : LieModel (↥M ⧸ CFSG.pCore 2 ↥M) .PSL 2 2 2 :=
    Or.inl ⟨by decide, hpsl⟩
  have hshape : Shape443 (↥M ⧸ CFSG.pCore 2 ↥M) :=
    Or.inl ⟨2, by norm_num, hLM⟩
  let β : ↥(eSub hv) →* Multiplicative (Fin 2 → Duad.F4) :=
    (AddMonoidHom.toMultiplicative Duad.toF4Hom).comp (ecoords hv).toMonoidHom
  have hβ : ∀ x, Multiplicative.toAdd (β x) =
      Duad.toF4 (Multiplicative.toAdd (ecoords hv x)) := fun _ => rfl
  have hβinj : Function.Injective β :=
    (Multiplicative.ofAdd.injective.comp Duad.toF4_injective).comp (ecoords hv).injective
  have hβsurj : Function.Surjective β := by
    intro y
    obtain ⟨c, hc⟩ := Duad.toF4_surjective (Multiplicative.toAdd y)
    refine ⟨(ecoords hv).symm (Multiplicative.ofAdd c), ?_⟩
    apply Multiplicative.toAdd.injective
    rw [hβ, MulEquiv.apply_symm_apply, toAdd_ofAdd, hc]
  have hsec : IsNaturalSection M (eSub hv) ⊥ ((eSub hv).subgroupOf M) (StatedSL 2 Duad.F4) := by
    refine ⟨hd.norm, α₀, hsurj₀, hker₀, β, hβsurj, ?_, ?_⟩
    · rw [Subgroup.bot_subgroupOf]
      exact (MonoidHom.ker_eq_bot_iff β).mpr hβinj
    · intro a u w hw
      rw [hβ, hβ, ecoords_conj hv ⟨a, hd.norm a.2⟩ u w hw]
      exact Duad.toF4_conj hv (Subgroup.inclusion hM a) _
  have hsum : IsSumOfNaturalModules M (eSub hv) ⊥ ((eSub hv).subgroupOf M)
      (StatedSL 2 Duad.F4) false 1 :=
    (isNaturalSection_iff_isSumOfNaturalModules_one _ _ bot_le).mp hsec
  have hcommV : IsMulCommutative ↥(eSub hv) :=
    IsMulCommutative.of_setLike_mul_comm fun x hx y hy => eSub_comm hv x y hx hy
  letI : IsMulCommutative ↥(eSub hv) := hcommV
  have hFFM : IsFFModule (autOn M (eSub hv)) :=
    FFn.isFFModule_autOn_of_sum (n := 1) (k := 1) (by decide) le_rfl le_rfl hsum
  have hFF : IsFFModule (autOn (Subgroup.normalizer (eSub hv : Set G)) (eSub hv)) :=
    isFFModule_of_le (autOn_mono' hd.norm) hFFM
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

end CFSG.SectionRank.QTK.Insp443

end

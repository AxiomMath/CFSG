module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltEightL
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltEightJ2
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltEInd
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGen

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoClassical

theorem commute_of_conj_mul_inv_mem {Q : Type*} [Group Q] [Finite Q] {M O : Subgroup Q}
    [IsSimpleGroup M] (hev : Even (Nat.card M)) (hO : Odd (Nat.card O))
    (hOM : O ≤ centralizer (M : Set Q)) {b : Q} (hb : ∀ ℓ ∈ M, b * ℓ * b⁻¹ * ℓ⁻¹ ∈ O)
    {ℓ : Q} (hℓ : ℓ ∈ M) : b * ℓ = ℓ * b := by
  have hcomm : ∀ ℓ₁ ∈ M, ∀ x ∈ O, x * ℓ₁⁻¹ = ℓ₁⁻¹ * x := fun ℓ₁ h₁ x hx =>
    (mem_centralizer_iff.mp (hOM hx) ℓ₁⁻¹ (inv_mem h₁)).symm
  let f : M →* Q :=
    { toFun := fun m => b * m * b⁻¹ * (m : Q)⁻¹
      map_one' := by simp
      map_mul' := fun m₁ m₂ => by
        have h := hcomm m₁ m₁.2 _ (hb m₂ m₂.2)
        simp only [Subgroup.coe_mul, mul_inv_rev]
        calc b * (↑m₁ * ↑m₂) * b⁻¹ * ((↑m₂)⁻¹ * (↑m₁)⁻¹) =
              b * ↑m₁ * b⁻¹ * (b * ↑m₂ * b⁻¹ * (↑m₂)⁻¹ * (↑m₁)⁻¹) := by group
          _ = b * ↑m₁ * b⁻¹ * ((↑m₁)⁻¹ * (b * ↑m₂ * b⁻¹ * (↑m₂)⁻¹)) := by rw [h]
          _ = b * ↑m₁ * b⁻¹ * (↑m₁)⁻¹ * (b * ↑m₂ * b⁻¹ * (↑m₂)⁻¹) := by group }
  have hfO : ∀ m, f m ∈ O := fun m => hb m m.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
  · exfalso
    have hinj : Function.Injective (f.codRestrict O hfO) := by
      rw [← MonoidHom.ker_eq_bot_iff, MonoidHom.ker_codRestrict]
      exact h
    exact (Nat.not_even_iff_odd.mpr (hO.of_dvd_nat (Subgroup.card_dvd_of_injective _ hinj))) hev
  · have hm : (⟨ℓ, hℓ⟩ : M) ∈ f.ker := h ▸ mem_top _
    have h1 : b * ℓ * b⁻¹ * ℓ⁻¹ = 1 := hm
    calc b * ℓ = b * ℓ * b⁻¹ * ℓ⁻¹ * ℓ * b := by group
      _ = ℓ * b := by rw [h1, one_mul]

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G} {n : ℕ}

namespace NormPair

variable (np : NormPair A R T g n) (hn : 8 ≤ n) (hc : Sec3 A R T g)
include hc

theorem exists_injective_mulAut_DW
    (hM : RankTwoHyp (centralizer (zpowers (np.wE hn) : Set G))
      (np.LE.subgroupOf (centralizer (zpowers (np.wE hn) : Set G)))) :
    ∃ φ : alternatingGroup (Fin n) →* MulAut (rankTwoX
      ((np.LE.subgroupOf (centralizer (zpowers (np.wE hn) : Set G))).map
        (QuotientGroup.mk' (standardComponentOddCore (centralizer (zpowers (np.wE hn) : Set G)))))),
      Function.Injective φ := by
  set C := centralizer (zpowers (np.wE hn) : Set G) with hCdef
  set M := np.LE.subgroupOf C with hMdef
  set O := standardComponentOddCore C with hOdef
  set π := QuotientGroup.mk' O with hπdef
  set X := rankTwoX (M.map π) with hXdef
  have hXn : X.Normal := normalClosure_normal
  have hBC : rightConjugate A g ≤ C := np.B_le_centralizer_W hn hc
  have hLC : np.LE ≤ C := np.LE_le_centralizer hn
  set ι : alternatingGroup (Fin n) →* C ⧸ O :=
    π.comp ((Subgroup.inclusion hBC).comp np.equivB.symm.toMonoidHom) with hιdef
  refine ⟨(MulAut.conjNormal (H := X)).comp ι, ?_⟩
  have : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((MulAut.conjNormal (H := X)).comp ι).ker with
    h | h
  · exact h
  · exfalso
    have : IsSimpleGroup (alternatingGroup (Fin (n - 3))) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
    let eM : M ≃* alternatingGroup (Fin (n - 3)) :=
      (subgroupOfEquivOfLe hLC).trans (np.LEEquiv hn)
    have : IsSimpleGroup M := eM.isSimpleGroup
    have hev : Even (Nat.card M) := by
      have : Nontrivial (Fin (n - 3)) := Fin.nontrivial_iff_two_le.mpr (by omega)
      rw [Nat.card_congr eM.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      obtain ⟨k, hk⟩ : 4 ∣ (n - 3).factorial := Nat.dvd_factorial (by norm_num) (by omega)
      exact ⟨k, by omega⟩
    apply np.false_of_le_centralizer_LE hn hc
    intro b hb
    rw [mem_centralizer_iff]
    intro ℓ hℓ
    set z := np.equivB ⟨b, hb⟩ with hz
    have hz' : z ∈ ((MulAut.conjNormal (H := X)).comp ι).ker := by
      rw [h]
      exact mem_top z
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hz'
    have hιz : ι z = π ⟨b, hBC hb⟩ := by
      rw [hιdef, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hz,
        MulEquiv.symm_apply_apply]
      rfl
    have hbO : ∀ m ∈ M, (⟨b, hBC hb⟩ : C) * m * (⟨b, hBC hb⟩ : C)⁻¹ * m⁻¹ ∈ O := by
      intro m hm
      have hmX : π m ∈ X := subset_normalClosure (mem_map_of_mem π hm)
      have h2 := congrArg (fun α : MulAut X => ((α ⟨π m, hmX⟩ : X) : C ⧸ O)) hz'
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
      have h3 : π ((⟨b, hBC hb⟩ : C) * m * (⟨b, hBC hb⟩ : C)⁻¹ * m⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hιz, h2, mul_inv_cancel]
      rwa [hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
    have hcomm := commute_of_conj_mul_inv_mem hev
      (RankTwoSporadic.odd_card_standardComponentOddCore (G := C)) (oddCore_le_of_rankTwoHyp hM)
      hbO (show (⟨ℓ, hLC hℓ⟩ : C) ∈ M from hℓ)
    exact (congrArg Subtype.val hcomm).symm

end NormPair

theorem NormPair.nonempty_DW_equiv_eight
    {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G} (np : NormPair A R T g 8)
    (hc : Sec3 A R T g) (hK : Assembly.KProper Blueprint.Catalog G) (h4 : Asc75Theorem4)
    (h32 : Lemma32) (h34 : Asc08Lemma34) (h5 : AltChildAt 5) :
    Nonempty (np.DW le_rfl ≃* alternatingGroup (Fin (8 + 1))) := by
  have hn : 8 ≤ 8 := le_rfl
  set C := centralizer (zpowers (np.wE hn) : Set G) with hCdef
  set M := np.LE.subgroupOf C with hMdef
  have hM : RankTwoHyp C M :=
    np.rankTwoHyp_LE_of hn hc hK h32 (np.standard_LE_of_lemma37 hn hc h4 h32 h34)
  let eM : M ≃* alternatingGroup (Fin (8 - 3)) :=
    (subgroupOfEquivOfLe (np.LE_le_centralizer hn)).trans (np.LEEquiv hn)
  have hZ : center ↥M = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : eM z ∈ center (alternatingGroup (Fin (8 - 3))) := by
      rw [mem_center_iff] at hz ⊢
      intro y
      obtain ⟨y', rfl⟩ := eM.surjective y
      rw [← map_mul, ← map_mul, hz y']
    rw [alternatingGroup.center_eq_bot (by simp), mem_bot, MulEquiv.map_eq_one_iff] at hz'
    rw [mem_bot]
    exact hz'
  let eQ : rankTwoQuot M ≃* alternatingGroup (Fin (8 - 3)) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans eM)
  rcases h5 _ _ (rankTwoHyp_map hM) RankTwoSporadic.standardComponentOddCore_quotient_eq_bot
      ⟨(quotCenterMap hM).symm.trans eQ⟩ with ⟨⟨e⟩⟩ | ⟨-, ⟨eJ⟩⟩ | ⟨-, ⟨eM12⟩, -⟩
  · exact np.nonempty_DW_equiv_of hn hM (e.trans (altCongrHom (finCongr (by norm_num))))
  · exfalso
    obtain ⟨φ, hφ⟩ := np.exists_injective_mulAut_DW hn hc hM
    exact not_injective_alt8_mulAut_J2 ((MulAut.congr eJ).toMonoidHom.comp φ)
      ((MulAut.congr eJ).injective.comp hφ)
  · exfalso
    obtain ⟨φ, hφ⟩ := np.exists_injective_mulAut_DW hn hc hM
    exact not_injective_alt8_mulAut_M12 ((MulAut.congr eM12).toMonoidHom.comp φ)
      ((MulAut.congr eM12).injective.comp hφ)

end CFSG.ComponentClassification.RankTwoAlt

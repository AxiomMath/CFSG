module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2G2
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoComponents
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2F7

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ} {t : G}
  {M₀ : Subgroup G} {x₀ : G} {q : ℕ} {W : Subgroup G}

theorem perfect_le_of_le_sup {K₂ K W : Subgroup G} (hK₂ : ⁅K₂, K₂⁆ = K₂) (hle : K₂ ≤ K ⊔ W)
    (hW : W ≤ Subgroup.normalizer (K : Set G)) (hp : IsPGroup 2 W) : K₂ ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKU : K ≤ K ⊔ W := le_sup_left
  have hWU : W ≤ K ⊔ W := le_sup_right
  have hN : (K.subgroupOf (K ⊔ W)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKU).mpr (sup_le Subgroup.le_normalizer hW)
  let φ : ↥W →* (K ⊔ W : Subgroup G) ⧸ K.subgroupOf (K ⊔ W) :=
    (QuotientGroup.mk' (K.subgroupOf (K ⊔ W))).comp (Subgroup.inclusion hWU)
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective (K.subgroupOf (K ⊔ W)) q
    obtain ⟨k, hk, w, hw, rfl⟩ := (mem_sup_iff_of_le_normalizer hW).1 hx
    refine ⟨⟨w, hw⟩, ?_⟩
    change QuotientGroup.mk' (K.subgroupOf (K ⊔ W)) (Subgroup.inclusion hWU ⟨w, hw⟩) =
      QuotientGroup.mk' (K.subgroupOf (K ⊔ W)) ⟨k * w, hx⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h := (Subgroup.mem_normalizer_iff.mp (hW (W.inv_mem hw)) k).mp hk
    rw [inv_inv] at h
    change w⁻¹ * (k * w) ∈ K
    rwa [← mul_assoc]
  have hsolvW : Group.IsSolvable ↥W := by
    have := IsPGroup.isNilpotent hp
    infer_instance
  have hsolvQ : Group.IsSolvable ((K ⊔ W : Subgroup G) ⧸ K.subgroupOf (K ⊔ W)) :=
    Group.isSolvable_of_surjective hφ
  have hperf₂ : Group.IsPerfect ↥K₂ := Subgroup.isPerfect_iff.mpr hK₂
  have hperf : Group.IsPerfect (K₂.subgroupOf (K ⊔ W)) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hle).symm.surjective
  have := CFSG.ComponentClassification.CatalogueBLinearTwo.perfect_le_normal_of_solvable_quotient
    (K.subgroupOf (K ⊔ W)) (K₂.subgroupOf (K ⊔ W))
  intro x hx
  have h := this (show (⟨x, hle hx⟩ : ↥(K ⊔ W)) ∈ K₂.subgroupOf (K ⊔ W) from hx)
  exact h

theorem isSylowTwoOf_sup_of_inf_aux {R K : Subgroup G} (hR : IsPGroup 2 R)
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) (h : IsSylowTwoOf (R ⊓ K) K) :
    IsSylowTwoOf R (K ⊔ R) := by
  rw [A4.isSylowTwoOf_iff_maximal]
  refine ⟨le_sup_right, hR, fun P hPH hP hRP => ?_⟩
  intro t ht
  have htH : t ∈ R ⊔ K := by rw [sup_comm]; exact hPH ht
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right R K hRK] at htH
  obtain ⟨r, hr, k, hk, rfl⟩ := htH
  have hkP : k ∈ P := by
    have := P.mul_mem (P.inv_mem (hRP hr)) ht
    simpa using this
  have hmax := ((A4.isSylowTwoOf_iff_maximal).mp h).2.2 (P ⊓ K) inf_le_right (hP.to_inf_left)
    (le_inf (inf_le_left.trans hRP) inf_le_right)
  have hkR : k ∈ R := (hmax ⟨hkP, hk⟩).1
  exact R.mul_mem hr hkR

omit [Finite G] in
theorem X_le_normalizer_Y' (X : Subgroup G) : X ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
  CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X

namespace S2Ok

variable {D₁ D₂ : Subgroup G} (O : S2Ok T M H S L D n t M₀ x₀ q W D₁ D₂)
include O

theorem R1_inf_L₂ : AppE.R1 S L ⊓ conjR L t = thompsonJ S ⊓ conjR L t := by
  have hB := O.base
  apply le_antisymm
  · rintro x ⟨hxS₀, hxL₂⟩
    have hx : x ∈ S ⊓ conjJoin S L := ⟨AppE.R1_le_S hxS₀, hB.L₂_le_L₀ hxL₂⟩
    rw [hB.S_inf_L₀_eq, ← hB.R_eq_R₁R₂ O.hC] at hx
    exact ⟨hx, hxL₂⟩
  · exact le_inf hB.R₂_le_R1 inf_le_right

theorem isSylow_S₀_L₂S₀ : IsSylowTwoOf (AppE.R1 S L) (conjR L t ⊔ AppE.R1 S L) := by
  have hB := O.base
  refine isSylowTwoOf_sup_of_inf_aux hB.R1_isPGroup hB.dbl.R1_le_normalizer_L₂ ?_
  rw [O.R1_inf_L₂]
  exact hB.isSylowTwoOf_R₂

theorem local_S₀ : quasithinIsLocal (AppE.R1 S L) (conjR L t) := by
  have hB := O.base
  have hN : ((conjR L t).subgroupOf (conjR L t ⊔ AppE.R1 S L)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hB.dbl.R1_le_normalizer_L₂)
  have hsub : IsSubnormal (conjR L t) (conjR L t ⊔ AppE.R1 S L) :=
    A3.subnormal_of_normal le_sup_left hN
  have hq : CFSG.IsQuasisimple (↥(conjR L t) ⧸ CFSG.pCore 2 ↥(conjR L t)) :=
    hB.hL₂.2.2.2.1.resolve_right
      (L238.card_ne_three_of_isLin2Type (by have := hB.hn; omega) hB.hlin₂)
  have hle : conjR L t ⊔ AppE.R1 S L ≤
      Subgroup.normalizer ((thompsonJ S ⊓ L : Subgroup G) : Set G) :=
    sup_le O.L₂_le_normalizer_R₁ O.R1_le_normalizer_R₁
  exact ⟨hB.R1_isPGroup, C1GN.mem_cComp_of_short hB.hL₂ hq hsub, O.isSylow_S₀_L₂S₀.2.2,
    O.pCore_ne_bot_of hle (R₁_le_R1.trans le_sup_right)⟩

theorem Y_le_S₁ (hT : M₀ = T) :
    pCoreOf 2 (conjR L t ⊔ s2S₁ M₀ S L) ≤ s2S₁ M₀ S L := (O.S₁_sylow_X hT).pCoreOf_le

theorem Y_inf_L₂_le_U₂ :
    pCoreOf 2 (conjR L t ⊔ s2S₁ M₀ S L) ⊓ conjR L t ≤ blockU (conjR L t) := by
  have hB := O.base
  have hnorm : conjR L t ≤ Subgroup.normalizer
      ((pCoreOf 2 (conjR L t ⊔ s2S₁ M₀ S L) ⊓ conjR L t : Subgroup G) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf _ _ _
      (le_sup_left.trans (X_le_normalizer_Y' _)) Subgroup.le_normalizer
  have := le_pCoreOf_of_normalizes (inf_le_right : pCoreOf 2 (conjR L t ⊔ s2S₁ M₀ S L) ⊓
    conjR L t ≤ conjR L t) hnorm
    ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 (conjR L t ⊔ s2S₁ M₀ S L)).to_le
      inf_le_left)
  rwa [hB.pCore_L₂] at this

theorem Y_inf_U₂ : pCoreOf 2 (conjR L t ⊔ s2S₁ M₀ S L) ⊓ blockU (conjR L t) = ⊥ := by
  have hB := O.base
  have hnormU : conjR L t ≤ Subgroup.normalizer ((blockU (conjR L t) : Subgroup G) : Set G) :=
    C1.le_normalizer_blockU (conjR L t)
  have hW : conjR L t ≤ Subgroup.normalizer
      ((pCoreOf 2 (conjR L t ⊔ s2S₁ M₀ S L) ⊓ blockU (conjR L t) : Subgroup G) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf _ _ _
      (le_sup_left.trans (X_le_normalizer_Y' _)) hnormU
  have hZ := hB.blockZ₂_eq_bot O.hC
  rcases hB.hL₂.2.2.2.2.2 _ (hZ ▸ bot_le) inf_le_right hW with h | h
  · rw [h, hZ]
  · exfalso
    have hUY : blockU (conjR L t) ≤ pCoreOf 2 (conjR L t ⊔ s2S₁ M₀ S L) := by
      rw [← h]; exact inf_le_left
    have hxX : x₀ ∈ conjR L t ⊔ s2S₁ M₀ S L := Subgroup.mem_sup_right O.x_mem_S₁
    have hxY : conjR (pCoreOf 2 (conjR L t ⊔ s2S₁ M₀ S L)) x₀ =
        pCoreOf 2 (conjR L t ⊔ s2S₁ M₀ S L) :=
      conjR_eq_self_iff.2 (X_le_normalizer_Y' _ hxX)
    have hU'Y : conjR (blockU (conjR L t)) x₀ ≤ pCoreOf 2 (conjR L t ⊔ s2S₁ M₀ S L) := by
      have := conjR_mono hUY x₀
      rwa [hxY] at this
    have hR₂Y : thompsonJ S ⊓ conjR L t ≤ pCoreOf 2 (conjR L t ⊔ s2S₁ M₀ S L) := by
      rw [O.UT3_R₂.sup_eq]
      exact sup_le hUY hU'Y
    have hR₂U : thompsonJ S ⊓ conjR L t ≤ blockU (conjR L t) := fun r hr =>
      O.Y_inf_L₂_le_U₂ ⟨hR₂Y hr, hr.2⟩
    have hU'U : conjR (blockU (conjR L t)) x₀ ≤ blockU (conjR L t) := O.UT3_R₂.U'_le_R.trans hR₂U
    have heq : conjR (blockU (conjR L t)) x₀ = blockU (conjR L t) :=
      Subgroup.eq_of_le_of_card_ge hU'U (by rw [card_conjR])
    exact O.U₂_ne_U₂' heq.symm

theorem Y_inf_L₂ : pCoreOf 2 (conjR L t ⊔ s2S₁ M₀ S L) ⊓ conjR L t = ⊥ := by
  rw [eq_bot_iff, ← O.Y_inf_U₂]
  exact le_inf inf_le_left (O.Y_inf_L₂_le_U₂)

theorem Y_le_R1 (hT : M₀ = T) :
    pCoreOf 2 (conjR L t ⊔ s2S₁ M₀ S L) ≤ AppE.R1 S L := by
  have hB := O.base
  intro y hy
  have hyS₁ : y ∈ s2S₁ M₀ S L := O.Y_le_S₁ hT hy
  by_cases hyS : y ∈ S
  · rw [← hB.S_inf_S₁]
    exact ⟨hyS, hyS₁⟩
  · exfalso
    obtain ⟨hyM, hyR₁⟩ := mem_s2S₁.1 hyS₁
    rcases O.R_perm_M₀ hyM with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hcomm : ∀ r ∈ thompsonJ S ⊓ conjR L t, y * r = r * y := by
        intro r hr
        have hr' : y * r * y⁻¹ ∈ thompsonJ S ⊓ conjR L t := by
          have : r ∈ conjR (thompsonJ S ⊓ conjR L t) y := by rw [h2]; exact hr
          exact mem_conjR.1 this
        have hrX : r ∈ conjR L t ⊔ s2S₁ M₀ S L := Subgroup.mem_sup_left hr.2
        have h3 : r * y⁻¹ * r⁻¹ ∈ pCoreOf 2 (conjR L t ⊔ s2S₁ M₀ S L) :=
          (Subgroup.mem_normalizer_iff.1 (X_le_normalizer_Y' _ hrX) y⁻¹).1
            ((pCoreOf 2 (conjR L t ⊔ s2S₁ M₀ S L)).inv_mem hy)
        have hc : y * r * y⁻¹ * r⁻¹ ∈ pCoreOf 2 (conjR L t ⊔ s2S₁ M₀ S L) ⊓ conjR L t := by
          refine ⟨?_, (conjR L t).mul_mem hr'.2 ((conjR L t).inv_mem hr.2)⟩
          have : y * r * y⁻¹ * r⁻¹ = y * (r * y⁻¹ * r⁻¹) := by group
          rw [this]
          exact Subgroup.mul_mem _ hy h3
        rw [O.Y_inf_L₂, Subgroup.mem_bot] at hc
        calc y * r = (y * r * y⁻¹ * r⁻¹) * (r * y) := by group
          _ = r * y := by rw [hc, one_mul]
      have hU : blockU (conjR L t) = conjR (blockU (conjR L t)) y := by
        refine Subgroup.eq_of_le_of_card_ge (fun u hu => ?_) (card_conjR _ _).le
        have huR : u ∈ thompsonJ S ⊓ conjR L t := O.UT3_R₂.U_le_R hu
        refine mem_conjR.2 ?_
        have : y * u * y⁻¹ = u := by
          calc y * u * y⁻¹ = u * y * y⁻¹ := by rw [hcomm u huR]
            _ = u := by group
        rw [this]
        exact hu
      have h' := O.conjR_U₂_of_nonswap hyM hyS h2
      rw [← DoubleA3.blockU_conjR] at h'
      exact O.U₂_ne_U₂' (hU.trans h')
    · exfalso
      have : thompsonJ S ⊓ L = thompsonJ S ⊓ conjR L t := hyR₁.symm.trans h1
      apply hB.R₁_ne_bot
      rw [eq_bot_iff, ← hB.R₁_inf_R₂]
      exact le_inf le_rfl (this ▸ le_rfl)

theorem L₂_le_centralizer_Y (hT : M₀ = T) :
    conjR L t ≤ Subgroup.centralizer (pCoreOf 2 (conjR L t ⊔ s2S₁ M₀ S L) : Set G) := by
  have hB := O.base
  intro l hl
  refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
  have hyS₀ : y ∈ AppE.R1 S L := O.Y_le_R1 hT hy
  have hylN : y * l * y⁻¹ ∈ conjR L t :=
    (Subgroup.mem_normalizer_iff.1 (hB.dbl.R1_le_normalizer_L₂ hyS₀) l).1 hl
  have hlX : l ∈ conjR L t ⊔ s2S₁ M₀ S L := Subgroup.mem_sup_left hl
  have h3 : l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 (conjR L t ⊔ s2S₁ M₀ S L) :=
    (Subgroup.mem_normalizer_iff.1 (X_le_normalizer_Y' _ hlX) y⁻¹).1
      ((pCoreOf 2 (conjR L t ⊔ s2S₁ M₀ S L)).inv_mem hy)
  have hc : y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 (conjR L t ⊔ s2S₁ M₀ S L) ⊓ conjR L t := by
    refine ⟨?_, (conjR L t).mul_mem hylN ((conjR L t).inv_mem hl)⟩
    have : y * l * y⁻¹ * l⁻¹ = y * (l * y⁻¹ * l⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hy h3
  rw [O.Y_inf_L₂, Subgroup.mem_bot] at hc
  calc y * l = (y * l * y⁻¹ * l⁻¹) * (l * y) := by group
    _ = l * y := by rw [hc, one_mul]

end S2Ok

end CFSG.QuasithinUnique.Lin2

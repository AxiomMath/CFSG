module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClSp4
public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamCl5

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools Blueprint Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace Sp4Out

variable {F : Type} [Field F]

theorem multiplierUnit_gspFieldMap (σ : F ≃+* F) (A : gsp 2 F) :
    ((multiplierUnit (gspFieldMap σ A) : Fˣ) : F) = σ ((multiplierUnit A : Fˣ) : F) := by
  have hμ := multiplierUnit_spec A
  set M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F := (((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) with hM
  have h : multiplierUnit (gspFieldMap σ A) =
      Units.map σ.toRingHom.toMonoidHom (multiplierUnit A) := by
    refine multiplierUnit_eq (gspFieldMap σ A) ?_
    change (M.map σ)ᵀ * formJ 2 F * M.map σ = σ ((multiplierUnit A : Fˣ) : F) • formJ 2 F
    have h1 : (Mᵀ * formJ 2 F * M).map σ = (M.map σ)ᵀ * formJ 2 F * M.map σ := by
      rw [map_mul_ringEquiv, map_mul_ringEquiv, transpose_map, formJ_map]
    rw [← h1, hμ]
    ext i j
    have h := congrFun (congrFun (formJ_map (r := 2) σ) i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul] at h ⊢
    rw [h]
  rw [h]
  rfl


variable [Finite F]

omit [Finite F] in
theorem isSquare_map_iff (σ : F ≃+* F) (a : F) : IsSquare (σ a) ↔ IsSquare a := by
  constructor
  · rintro ⟨l, hl⟩
    refine ⟨σ.symm l, ?_⟩
    apply σ.injective
    rw [map_mul, RingEquiv.apply_symm_apply, hl]
  · rintro ⟨l, rfl⟩
    exact ⟨σ l, map_mul σ l l⟩

omit [Finite F] in
theorem quadraticChar_ringEquiv [Fintype F] [DecidableEq F] (σ : F ≃+* F) {a : F} (ha : a ≠ 0) :
    quadraticChar F (σ a) = quadraticChar F a := by
  have hσa : σ a ≠ 0 := by simpa using ha
  rcases quadraticChar_dichotomy ha with h | h
  · rw [h, quadraticChar_one_iff_isSquare hσa, isSquare_map_iff]
    exact (quadraticChar_one_iff_isSquare ha).1 h
  · rw [h, quadraticChar_neg_one_iff_not_isSquare, isSquare_map_iff]
    exact quadraticChar_neg_one_iff_not_isSquare.1 h

omit [Finite F] in
theorem commutator_conjAut (A B : gsp 2 F) (σ τ : F ≃+* F)
    (hστ : fieldAut 2 F σ * fieldAut 2 F τ = fieldAut 2 F τ * fieldAut 2 F σ) :
    ⁅conjAut 2 F A * fieldAut 2 F σ, conjAut 2 F B * fieldAut 2 F τ⁆ =
      conjAut 2 F (A * gspFieldMap σ B * gspFieldMap τ A⁻¹ * B⁻¹) := by
  have h1 := fieldAut_mul_conjAut_mul_inv (r := 2) σ B
  have h2 := fieldAut_mul_conjAut_mul_inv (r := 2) τ A⁻¹
  rw [map_inv] at h2
  rw [map_mul, map_mul, map_mul, map_inv, ← h1, ← h2, commutatorElement_def]
  have h3 : fieldAut 2 F σ * fieldAut 2 F τ * (fieldAut 2 F σ)⁻¹ = fieldAut 2 F τ := by
    rw [hστ]
    group
  calc conjAut 2 F A * fieldAut 2 F σ * (conjAut 2 F B * fieldAut 2 F τ) *
        (conjAut 2 F A * fieldAut 2 F σ)⁻¹ * (conjAut 2 F B * fieldAut 2 F τ)⁻¹
      = conjAut 2 F A * (fieldAut 2 F σ * conjAut 2 F B * (fieldAut 2 F σ)⁻¹) *
          (fieldAut 2 F σ * fieldAut 2 F τ * (fieldAut 2 F σ)⁻¹) * (conjAut 2 F A)⁻¹ *
          (fieldAut 2 F τ)⁻¹ * (conjAut 2 F B)⁻¹ := by group
    _ = conjAut 2 F A * (fieldAut 2 F σ * conjAut 2 F B * (fieldAut 2 F σ)⁻¹) *
          fieldAut 2 F τ * (conjAut 2 F A)⁻¹ * (fieldAut 2 F τ)⁻¹ * (conjAut 2 F B)⁻¹ := by
        rw [h3]
    _ = conjAut 2 F A * (fieldAut 2 F σ * conjAut 2 F B * (fieldAut 2 F σ)⁻¹) *
          (fieldAut 2 F τ * (conjAut 2 F A)⁻¹ * (fieldAut 2 F τ)⁻¹) * (conjAut 2 F B)⁻¹ := by
        group

theorem multiplier_commutator_isSquare (A B : gsp 2 F) (σ τ : F ≃+* F) :
    IsSquare ((multiplierUnit (A * gspFieldMap σ B * gspFieldMap τ A⁻¹ * B⁻¹) : Fˣ) : F) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  let χ : Fˣ →* ℤˣ := (quadraticChar F).toUnitHom
  have hχσ : ∀ (σ : F ≃+* F) (u : Fˣ), χ (Units.map σ.toRingHom.toMonoidHom u) = χ u := by
    intro σ u
    apply Units.ext
    rw [MulChar.coe_toUnitHom, MulChar.coe_toUnitHom]
    exact quadraticChar_ringEquiv σ u.ne_zero
  have hmσ : ∀ (σ : F ≃+* F) (B : gsp 2 F), multiplier 2 F (gspFieldMap σ B) =
      Units.map σ.toRingHom.toMonoidHom (multiplier 2 F B) := fun σ B =>
    Units.ext (multiplierUnit_gspFieldMap σ B)
  set M := A * gspFieldMap σ B * gspFieldMap τ A⁻¹ * B⁻¹ with hM
  have hmM : multiplier 2 F M = multiplier 2 F A * Units.map σ.toRingHom.toMonoidHom (multiplier 2 F B) *
      (Units.map τ.toRingHom.toMonoidHom (multiplier 2 F A))⁻¹ * (multiplier 2 F B)⁻¹ := by
    rw [hM, map_mul, map_mul, map_mul, map_inv, hmσ, hmσ, map_inv, map_inv]
  have hχM : χ (multiplier 2 F M) = 1 := by
    rw [hmM, map_mul, map_mul, map_mul, map_inv, map_inv, hχσ, hχσ]
    exact (commutatorElement_eq_one_iff_mul_comm.2 (mul_comm (χ (multiplier 2 F A)) (χ (multiplier 2 F B))) :
      _)
  have h1 : quadraticChar F ((multiplier 2 F M : Fˣ) : F) = 1 := by
    have := congrArg (fun z : ℤˣ => (z : ℤ)) hχM
    simpa [χ, MulChar.coe_toUnitHom] using this
  exact (quadraticChar_one_iff_isSquare (multiplier 2 F M).ne_zero).1 h1


omit [Finite F] in
theorem commutator_mem_inner [Finite F] (hodd : ringChar F ≠ 2) (a b : MulAut (StatedProj (StatedSp 2 F))) :
    ⁅a, b⁆ ∈ (MulAut.conj : StatedProj (StatedSp 2 F) →* MulAut (StatedProj (StatedSp 2 F))).range := by
  obtain ⟨A, σ, rfl⟩ := automorphism_standard hodd (le_refl 2) a
  obtain ⟨B, τ, rfl⟩ := automorphism_standard hodd (le_refl 2) b
  have hστ : fieldAut 2 F σ * fieldAut 2 F τ = fieldAut 2 F τ * fieldAut 2 F σ := by
    rw [← map_mul, ← map_mul, ringAut_mul_comm F σ τ]
  rw [commutator_conjAut A B σ τ hστ]
  obtain ⟨l, hl⟩ := multiplier_commutator_isSquare A B σ τ
  obtain ⟨g, hg⟩ := IVK.psp4_inner_of_square_multiplier
    (A * gspFieldMap σ B * gspFieldMap τ A⁻¹ * B⁻¹) ⟨l, by rw [hl, sq]⟩
  exact ⟨g, hg.symm⟩

end Sp4Out

namespace Lem711Cfg

variable {X : Type} [Group X] [Finite X] {L K : Subgroup X} {x y : X}

theorem x_mem_L_of_psp4 {F : Type} [Field F] [Finite F] (hodd : ringChar F ≠ 2)
    (h : Lem711Cfg X L K x y) (θ : ↥L ≃* StatedProj (StatedSp 2 F)) : x ∈ L := by
  have := h.normal
  have := h.soc.simple
  have hnabP : ∃ a b : StatedProj (StatedSp 2 F), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := h.exists_noncomm
    exact ⟨θ a, θ b, fun h' => hab (θ.injective (by rw [map_mul, map_mul, h']))⟩
  have : IsSimpleGroup (StatedProj (StatedSp 2 F)) := θ.symm.isSimpleGroup
  have hZ := CFSG.ComponentClassification.OutcomeLocal.center_eq_bot_of_isSimpleGroup hnabP
  obtain ⟨ρ, hinj, hρW, -, -⟩ := CFSG.ComponentClassification.OutcomeLocal.socle_extension
    (W := L) h.centralizer_eq_bot θ hZ
  have h1 : ρ x ∈ (⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆).map ρ := ⟨x, h.x_mem_commutator, rfl⟩
  rw [Subgroup.map_commutator] at h1
  have hle : ⁅(⊤ : Subgroup (MulAut (StatedProj (StatedSp 2 F)))),
      (⊤ : Subgroup (MulAut (StatedProj (StatedSp 2 F))))⁆ ≤
      (MulAut.conj : StatedProj (StatedSp 2 F) →* MulAut (StatedProj (StatedSp 2 F))).range := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    exact Sp4Out.commutator_mem_inner hodd a b
  obtain ⟨g, hg⟩ := hle (Subgroup.commutator_mono le_top le_top h1)
  have hw : ρ ((θ.symm g : ↥L) : X) = ρ x := by
    rw [hρW, MulEquiv.apply_symm_apply, hg]
  have := hinj hw
  rw [← this]
  exact (θ.symm g).2

end Lem711Cfg



theorem lem711_sp4 (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    Lem711Empty (fun X _ => LieModel X .PSp 2 p f) := by
  intro X _ _ L K x y h hm
  obtain ⟨-, F, _, _, hF, ⟨θ⟩⟩ := IVK.stated_of_lieModel_PSp hm
  have hodd' : Odd (Nat.card F) := by rw [hF]; exact (hp.odd_of_ne_two hp2).pow
  have : CharP F p := finite_field_prime_power_characteristic hp hf hF
  have hchar : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  have hxL : x ∈ L := h.x_mem_L_of_psp4 hchar θ
  have hev : 2 ∣ Nat.card K := by
    have h360 : 360 ∣ Nat.card ↥K := by
      rw [← h.card_K_bar]
      exact Subgroup.card_quotient_dvd_card _
    exact (by norm_num : 2 ∣ 360).trans h360
  have hterm : ∀ u : X, orderOf u = 2 → u ∈ centralizer (K : Set X) →
      IsCompIn (centralizer ({u} : Set X)) K := fun u hu huK =>
    h.terminal u hu fun k hk => (Subgroup.mem_centralizer_iff.1 huK k hk).symm
  refine IVK.psp4_inner_false hodd' (W := ↥L) θ (K₀ := K.subgroupOf L) ?_ ?_
    (v := ⟨x, hxL⟩) ?_ ?_
  · have e := Subgroup.subgroupOfEquivOfLe h.K_le
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact h.odd_card_center
  · intro w hw hwK
    exact IVK.psp4_hterm_W h.K_le hev hterm w hw hwK
  · rw [← Subgroup.orderOf_coe]
    exact h.hx
  · rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hkK : (k : X) ∈ K := hk
    have := mem_centralizer_singleton_iff.1 (h.comp.1 hkK)
    exact Subtype.ext this

end CFSG.GH74.GLS

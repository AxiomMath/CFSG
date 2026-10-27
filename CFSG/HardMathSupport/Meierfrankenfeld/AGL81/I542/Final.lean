module

public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.L32Core
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.A6Core
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.Bridge
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.AutFactsU33
public import CFSG.Quasithin.Background.SmithB42L2L32
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.AGL81I542

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542

open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF CFSG.Open
open CFSG.QuasithinUnique.Setup.Family

theorem nonempty_gl32_of_statedClassicalModel {K : Type} [Group K]
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel K .PSL 3 2 1) : Nonempty (K ≃* GL32) := by
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have : Fintype F := Fintype.ofFinite F
  have hcardF : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card, hcard]; norm_num
  have hc : Fintype.card F = Fintype.card (ZMod 2) := by rw [hcardF, ZMod.card]
  let ε : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hc
  let e₂ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
    (QuotientGroup.quotientMulEquivOfEq (CFSG.Quasithin.B42L2.center_sl3_eq_bot hcardF)).trans
      QuotientGroup.quotientBot
  let e₃ : Matrix.SpecialLinearGroup (Fin 3) F ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map ε.toRingHom)
      (Matrix.SpecialLinearGroup.map ε.symm.toRingHom)
      (MonoidHom.ext fun A => Subtype.ext (by
        ext i j
        simp [Matrix.SpecialLinearGroup.map_apply_coe]))
      (MonoidHom.ext fun A => Subtype.ext (by
        ext i j
        simp [Matrix.SpecialLinearGroup.map_apply_coe]))
  exact ⟨e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
    ((e₂.trans e₃).trans CFSG.Quasithin.B42L2.slEquivGL32))⟩

theorem natCard_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

section AutIn

variable {Y : Type} [Group Y]

theorem innSub_le_autIn (L : Subgroup Y) : innSub ↥L ≤ autIn L := by
  rintro _ ⟨l, rfl⟩
  refine ⟨⟨l, Subgroup.le_normalizer l.2⟩, ?_⟩
  ext k
  rfl

theorem autIn_le_innSub {L : Subgroup Y}
    (h : ∀ g ∈ Subgroup.normalizer (L : Set Y), ∃ l ∈ L, ∀ k ∈ L, g * k * g⁻¹ = l * k * l⁻¹) :
    autIn L ≤ innSub ↥L := by
  rintro _ ⟨⟨g, hg⟩, rfl⟩
  obtain ⟨l, hl, hgl⟩ := h g hg
  refine ⟨⟨l, hl⟩, ?_⟩
  ext k
  exact (hgl k k.2).symm

end AutIn

theorem agl81I542 :
    AGL81I542 := by
  intro X _ _ T hGN L hL hJ hType
  classical
  obtain ⟨W, _, _, _, ρ, hρ, A, hA2, hAbest, hAN, hLA⟩ := exists_rep_offender X T hGN L hL hJ
  have hfaith : ∀ a ∈ A, (∀ v, ρ a v = v) → a = 1 := fun a _ h =>
    hρ (by rw [map_one]; exact LinearMap.ext h)
  have hb : IsBestOffenderOn ρ A ⊤ := (isBestOffender_iff_on ρ A hfaith).mp ⟨hA2, hAbest⟩
  have hinn := innSub_le_autIn L
  have : Finite (MulAut ↥L) := Finite.of_injective (fun σ : MulAut ↥L => (σ : ↥L → ↥L))
    DFunLike.coe_injective
  have hne : ∀ K : Subgroup (MulAut ↥L), (innSub ↥L).relIndex K ≠ 0 := fun K => by
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  have hcardA6 : Nonempty (↥L ≃* alternatingGroup (Fin 6)) → Nat.card ↥L = 360 := by
    rintro ⟨e⟩
    rw [Nat.card_congr e.toEquiv, natCard_alt6]
  have hcardL32 : StatedClassicalModel ↥L .PSL 3 2 1 → Nat.card ↥L = 168 := by
    intro h
    obtain ⟨e⟩ := nonempty_gl32_of_statedClassicalModel h
    rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.H13.NQTerm.natCard_GL32]
  rcases hType with hA6 | hL32 | hU33
  ·
    obtain ⟨eL⟩ := hA6
    have hcore := a6_core ρ hρ eL hA2 hAN hLA hb
    set φ : MulAut ↥L ≃* MulAut (alternatingGroup (Fin 6)) := MulAut.congr eL with hφ
    set S6L : Subgroup (MulAut ↥L) := s6Aut.map φ.symm.toMonoidHom with hS6L
    have hmemS6 : ∀ τ : MulAut ↥L, τ ∈ S6L ↔ φ τ ∈ s6Aut := fun τ => by
      rw [hS6L, Subgroup.mem_map_equiv, MulEquiv.symm_symm]
    have hle : autIn L ≤ S6L := by
      rintro _ ⟨⟨g, hg⟩, rfl⟩
      rw [hmemS6]
      exact hcore g hg
    have hinnmap : (innSub ↥L).map φ.toMonoidHom =
        (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range := by
      ext σ
      constructor
      · rintro ⟨_, ⟨l, rfl⟩, rfl⟩
        refine ⟨eL l, ?_⟩
        ext a
        simp [hφ, MulAut.congr_apply, MulAut.conj_apply]
      · rintro ⟨a, rfl⟩
        refine ⟨MulAut.conj (eL.symm a), ⟨eL.symm a, rfl⟩, ?_⟩
        ext b
        simp [hφ, MulAut.congr_apply, MulAut.conj_apply]
    have hS6map : S6L.map φ.toMonoidHom = s6Aut := by
      rw [hS6L, Subgroup.map_map]
      convert Subgroup.map_id s6Aut
      ext σ
      simp
    have hS6idx : (innSub ↥L).relIndex S6L = 2 := by
      rw [← Subgroup.relIndex_map_map_of_injective (f := φ.toMonoidHom) (innSub ↥L) S6L φ.injective,
        hinnmap, hS6map]
      exact relIndex_inner_s6Aut
    have hidx : (innSub ↥L).relIndex (autIn L) ≤ 2 := by
      rw [← hS6idx]
      exact Subgroup.relIndex_le_of_le_right hle (hne S6L)
    refine ⟨hidx, fun _ h2 => ?_, fun hP => absurd (hcardL32 hP) (by rw [hcardA6 ⟨eL⟩]; norm_num)⟩
    have h3 := Subgroup.relIndex_mul_relIndex (innSub ↥L) (autIn L) S6L hinn hle
    rw [h2, hS6idx] at h3
    have h4 : (autIn L).relIndex S6L = 1 := by omega
    have heq : autIn L = S6L := le_antisymm hle (Subgroup.relIndex_eq_one.mp h4)
    obtain ⟨e6⟩ := nonempty_s6Aut_equiv
    exact ⟨(MulEquiv.subgroupCongr heq).trans
      ((s6Aut.equivMapOfInjective φ.symm.toMonoidHom φ.symm.injective).symm.trans e6)⟩
  ·
    obtain ⟨eL⟩ := nonempty_gl32_of_statedClassicalModel hL32
    have hcore := l32_inner ρ hρ eL hA2 hAN hLA hb
    have heq : autIn L = innSub ↥L := le_antisymm (autIn_le_innSub hcore) hinn
    have h1 : (innSub ↥L).relIndex (autIn L) = 1 := by rw [heq]; exact Subgroup.relIndex_self _
    refine ⟨by rw [h1]; norm_num, fun hA6 _ => absurd (hcardA6 hA6) (by rw [hcardL32 hL32]; norm_num),
      fun _ => h1⟩
  ·
    have h1 := relIndex_inn_le_two_of_statedClassicalModel_psu33 hU33
    have h2 : (innSub ↥L).relIndex (autIn L) ≤ 2 :=
      (Subgroup.relIndex_le_of_le_right le_top (hne ⊤)).trans h1
    have hcardU : Nat.card ↥L = 6048 := by
      obtain ⟨e⟩ := nonempty_mulEquiv_u33G_of_statedClassicalModel hU33
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Quasithin.card_u33Pres
    refine ⟨h2, fun hA6 _ => absurd (hcardA6 hA6) (by rw [hcardU]; norm_num),
      fun hP => absurd (hcardL32 hP) (by rw [hcardU]; norm_num)⟩

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542

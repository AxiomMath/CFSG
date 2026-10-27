module

public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.Section

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open scoped commutatorElement

theorem irrSection_tauW_ne_one_of_fixedPointFree {V : Type} [CommGroup V] [Finite V]
    {L A : Subgroup (MulAut V)} (sec : IrrSection V L A) {x : ↥(L ⊔ A)}
    (hfree : ∀ v : V, (x : MulAut V) v = v → v = 1) : sec.τW x ≠ 1 := by
  intro hτ
  have hτI : sec.τI x = 1 := by
    ext v
    exact congrArg Subtype.val (sec.injective_image x (fun w => by rw [hτ]; rfl) v)
  have hI : sec.I = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Subgroup.mem_bot]
    apply hfree v
    have h := sec.τI_apply x ⟨v, hv⟩
    rw [hτI] at h
    simpa using h.symm
  have hsub : Subsingleton ↥sec.I := by rw [hI]; infer_instance
  have hWsub : Subsingleton sec.W :=
    ⟨fun a b => by
      obtain ⟨x, rfl⟩ := sec.π_surjective a
      obtain ⟨y, rfl⟩ := sec.π_surjective b
      rw [hsub.allEq x y]⟩
  exact (not_nontrivial_iff_subsingleton.mpr hWsub) sec.nontrivial

private noncomputable def sectionMap {X : Type} [Group X] {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) X W) (K B : Subgroup X)
    (U : Submodule (ZMod 2) W)
    (hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (K ⊔ B) U) :
    K →* ↥(imgBin ρ (K ⊔ B) U hinv K) where
  toFun k := ⟨resBin ρ (K ⊔ B) U hinv ⟨(k : X), Subgroup.mem_sup_left k.2⟩,
    resBin_mem_imgBin (b := (k : X)) k.2 (Subgroup.mem_sup_left k.2)⟩
  map_one' := by
    apply Subtype.ext
    change resBin ρ (K ⊔ B) U hinv (1 : ↥(K ⊔ B)) = 1
    rw [map_one]
  map_mul' a b := by
    apply Subtype.ext
    change resBin ρ (K ⊔ B) U hinv ⟨((a : X) * (b : X)), _⟩ =
      resBin ρ (K ⊔ B) U hinv ⟨(a : X), _⟩ *
        resBin ρ (K ⊔ B) U hinv ⟨(b : X), _⟩
    rw [← map_mul]
    rfl

private theorem sectionMap_surjective {X : Type} [Group X] {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) X W) (K B : Subgroup X)
    (U : Submodule (ZMod 2) W)
    (hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (K ⊔ B) U) :
    Function.Surjective (sectionMap ρ K B U hinv) := by
  rintro ⟨y, hy⟩
  rw [mem_imgBin] at hy
  obtain ⟨b, hbK, rfl⟩ := hy
  exact ⟨⟨b, hbK⟩, by apply Subtype.ext; rfl⟩

private theorem sectionMap_comp_ne_one {X : Type} [Group X] {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] (ρ : Representation (ZMod 2) X W) (K B : Subgroup X)
    (U : Submodule (ZMod 2) W)
    (hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (K ⊔ B) U)
    (sec : IrrSection (Multiplicative ↥U) (imgBin ρ (K ⊔ B) U hinv K)
      (imgBin ρ (K ⊔ B) U hinv B)) (k : K)
    (hkfix : ∀ w : W, ρ (k : X) w = w → w = 0) :
    (((sec.τW.comp (Subgroup.inclusion le_sup_left)).rangeRestrict).comp
      (sectionMap ρ K B U hinv)) k ≠ 1 := by
  intro hψk
  let f := sectionMap ρ K B U hinv
  let ψ : K →* ↥(sec.τW.comp (Subgroup.inclusion le_sup_left)).range :=
    ((sec.τW.comp (Subgroup.inclusion le_sup_left)).rangeRestrict).comp f
  set x : ↥(imgBin ρ (K ⊔ B) U hinv K ⊔ imgBin ρ (K ⊔ B) U hinv B) :=
    Subgroup.inclusion le_sup_left (f k) with hx
  have hτ : sec.τW x = 1 := congrArg Subtype.val hψk
  refine irrSection_tauW_ne_one_of_fixedPointFree sec (x := x) ?_ hτ
  intro v hv
  have hv' : (((f k : ↥(imgBin ρ (K ⊔ B) U hinv K)) : MulAut (Multiplicative ↥U))) v = v := hv
  have h1 : ((Multiplicative.toAdd (((f k : ↥(imgBin ρ (K ⊔ B) U hinv K)) :
      MulAut (Multiplicative ↥U)) v) : ↥U) : W) =
      ρ (k : X) (((Multiplicative.toAdd v : ↥U) : W)) :=
    resBin_apply_val (ρ := ρ) (H := K ⊔ B) (U := U) (hU := hinv)
      ⟨k, Subgroup.mem_sup_left k.2⟩ v
  have hw : ρ (k : X) (((Multiplicative.toAdd v : ↥U) : W)) =
      (((Multiplicative.toAdd v : ↥U) : W)) := by
    rw [← h1, hv']
  have hzero := hkfix _ hw
  have hv0 : (Multiplicative.toAdd v : ↥U) = 0 := Subtype.ext hzero
  exact Multiplicative.toAdd.injective (by simpa using hv0)

theorem exists_irrSection_fixedPointFree {X : Type} [Group X] [Finite X]
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) X W) (K A : Subgroup X)
    (hKq : CFSG.IsQuasisimple K) (hA2 : CFSG.IsElementaryAbelian 2 A)
    (hAK : A ≤ Subgroup.normalizer (K : Set X)) (hKA : ⁅K, A⁆ = K)
    (hKnt : ¬ K ≤ cenOn ρ K ⊤) (hb : IsBestOffenderOn ρ A ⊤)
    (k : K)
    (hkfix : ∀ w : W, ρ (k : X) w = w → w = 0) :
    ∃ (W' : Type) (_ : CommGroup W') (_ : Finite W') (Lb Eb : Subgroup (MulAut W')),
      (∀ w : W', w * w = 1) ∧ IsIrrOn Lb ∧ CFSG.IsQuasisimple ↥Lb ∧
      Eb ≠ ⊥ ∧ IsElemAbelian2 Eb ∧ IsQuadratic Eb ∧
      Eb ≤ Subgroup.normalizer (Lb : Set (MulAut W')) ∧
      Nat.card W' ≤ Nat.card Eb * Nat.card (fixV Eb) ∧
      ∃ ψ : K →* ↥Lb, Function.Surjective ψ ∧ ψ k ≠ 1 := by
  obtain ⟨B, hBA, hinv, hKU, hBU, hBbest, hBquad, hmove, hstrict⟩ :=
    exists_strictMin_moving K A hA2 hAK hKA hKnt hb
  set U := commOn ρ K ⊤ with hUdef
  have hKH : K ≤ K ⊔ B := le_sup_left
  have hBH : B ≤ K ⊔ B := le_sup_right
  have hHn : K ⊔ B ≤ Subgroup.normalizer (K : Set X) :=
    sup_le Subgroup.le_normalizer (hBA.trans hAK)
  have hK : ∀ h ∈ K ⊔ B, ∀ k ∈ K, h * k * h⁻¹ ∈ K :=
    fun h hh k hk => (Subgroup.mem_normalizer_iff.1 (hHn hh) k).1 hk
  have hmove' : ∃ b ∈ B, ∃ k ∈ K, ∃ u ∈ U, ρ b (ρ k u) ≠ ρ k (ρ b u) := by
    have : ¬ B ≤ cenOn ρ B U := hBU
    obtain ⟨b, hb, hbn⟩ := Set.not_subset.1 this
    obtain ⟨k, hk, u, hu, h⟩ := hmove b hb hbn
    exact ⟨b, hb, k, hk, u, hu, h⟩
  have hLG := isComp_imgBin (hU := hinv) hKH hKq hKU hK
  have hAG := isBestOffender_imgBin (hU := hinv) hBH hBbest hBU hstrict
  have hne := commutator_imgBin_ne_bot (hU := hinv) hKH hBH hmove'
  obtain ⟨hAn, hLL, ⟨sec⟩⟩ := CFSG.QuasithinUnique.Setup.Layer.Actor.irreducibleSectionProp
    (Multiplicative ↥U) (binU_sq U) _ _ _ hLG hAG hne
  let f := sectionMap ρ K B U hinv
  let ψ : K →* ↥(sec.τW.comp (Subgroup.inclusion le_sup_left)).range :=
    ((sec.τW.comp (Subgroup.inclusion le_sup_left)).rangeRestrict).comp f
  have hψ : Function.Surjective ψ :=
    (MonoidHom.rangeRestrict_surjective _).comp (sectionMap_surjective ρ K B U hinv)
  refine ⟨sec.W, sec.commGroup, sec.finite, _, _,
    irrSection_sq (binU_sq U) sec, irrSection_isIrrOn sec,
    sec.lbar_quasisimple, sec.abar_ne_bot, sec.abar_elem, sec.abar_quadratic,
    irrSection_range_le_normalizer sec hAn, sec.abar_offender, ψ, hψ, ?_⟩
  exact sectionMap_comp_ne_one ρ K B U hinv sec k hkfix

end CFSG.GroupTheory

end

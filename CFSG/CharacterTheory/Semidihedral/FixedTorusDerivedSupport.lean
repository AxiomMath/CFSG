module

public import CFSG.CharacterTheory.Semidihedral.MatrixTorus
public import CFSG.CharacterTheory.Wreathed.OddFieldFixedTorusDerivedCentralizerSupport

public section

namespace CFSG.Semidihedral.FixedTorusDerived

noncomputable section

open Matrix CFSG.Semidihedral.MatrixTorus CFSG.Semidihedral.MatrixCoverData
open CFSG.Wreathed.OddFieldTorus (fixedField mem_fixedField fixedIncl fixedIncl_coe
  fixedIncl_injective exists_fixedIncl fieldAction)

universe u

variable (F : Type u) [Field F] (a : Fˣ)

@[expose] def torusFieldAction (A : Subgroup (F ≃+* F))
    (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a) : A →* MulAut (W F a) where
  toFun sigma := WFieldEquiv F a sigma (hfix sigma)
  map_one' := by
    apply MulEquiv.ext
    intro X
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    rfl
  map_mul' := by
    intro sigma tau
    apply MulEquiv.ext
    intro X
    apply Subtype.ext
    apply Subtype.ext
    exact DFunLike.congr_fun (MatrixCover.slFieldEquiv_mul F sigma tau) X.val.val

theorem torusFieldAction_matrix (A : Subgroup (F ≃+* F))
    (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a) (sigma : A) (X : W F a) :
    ((torusFieldAction F a A hfix sigma X).val.val : Matrix (Fin 2) (Fin 2) F) =
      (sigma : F ≃+* F).toRingHom.mapMatrix (X.val.val : Matrix (Fin 2) (Fin 2) F) := rfl

theorem W_mul_comm (X Y : W F a) : X * Y = Y * X :=
  Subtype.ext (mul_comm (X : Torus F a) Y)

variable {F} {a}

theorem fixedIncl_mem_torus_iff (σ : F ≃+* F) (b : (fixedField σ)ˣ)
    (hb : ((b : fixedField σ) : F) = a) (g : SL (fixedField σ)) :
    fixedIncl σ g ∈ Torus F a ↔ g ∈ Torus (fixedField σ) b := by
  rw [mem_torus_iff, mem_torus_iff, fixedIncl_coe, fixedIncl_coe, fixedIncl_coe,
    fixedIncl_coe]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨Subtype.ext ?_, Subtype.ext h2⟩
    rw [h1, ← hb]
    simp
  · rintro ⟨h1, h2⟩
    refine ⟨?_, congrArg Subtype.val h2⟩
    rw [congrArg Subtype.val h1, ← hb]
    simp

theorem card_fixed_W [Finite F] (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a)
    (A : Subgroup (F ≃+* F)) (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)
    (sigma : A) :
    Nat.card {X : W F a // torusFieldAction F a A hfix sigma X = X} =
      torusSize (Nat.card (fixedField (sigma : F ≃+* F))) / 2 := by
  set σ := (sigma : F ≃+* F) with hσ
  let K := fixedField σ
  have haK : (a : F) ∈ K := mem_fixedField.mpr (hfix sigma)
  let b : Kˣ := Units.mk0 ⟨a, haK⟩ fun h => a.ne_zero (congrArg Subtype.val h)
  have hb : ((b : K) : F) = a := rfl
  have hKodd : Odd (Nat.card K) :=
    hodd.of_dvd_nat (AddSubgroup.card_dvd_of_le (H := K.toAddSubgroup) le_top |>.trans
      (by rw [AddSubgroup.card_top]))
  have hbK : ¬IsSquare b := by
    rintro ⟨r, hr⟩
    apply ha
    refine ⟨Units.map K.subtype.toMonoidHom r, Units.ext ?_⟩
    have h := congrArg (fun u : Kˣ => ((u : K) : F)) hr
    rw [← hb]
    simpa using h
  have hmemT : ∀ g : Torus K b, (fixedIncl σ).comp (Torus K b).subtype g ∈ Torus F a :=
    fun g => (fixedIncl_mem_torus_iff σ b hb g.val).mpr g.2
  let ιT : Torus K b →* Torus F a :=
    ((fixedIncl σ).comp (Torus K b).subtype).codRestrict (Torus F a) hmemT
  have hιT : Function.Injective ιT := fun g h hgh =>
    Subtype.ext (fixedIncl_injective σ (congrArg Subtype.val hgh))
  have hord : ∀ g : Torus K b, orderOf (ιT g) = orderOf g := fun g =>
    orderOf_injective ιT hιT g
  have hmemW : ∀ g : W K b, ιT.comp (W K b).subtype g ∈ W F a := fun g =>
    (mem_W_iff_odd_order F a hodd ha _).mpr (by
      change Odd (orderOf (ιT g.val))
      rw [hord]
      exact (mem_W_iff_odd_order K b hKodd hbK g.val).mp g.2)
  let ιW : W K b →* W F a := (ιT.comp (W K b).subtype).codRestrict (W F a) hmemW
  have hfixW : ∀ g : W K b, torusFieldAction F a A hfix sigma (ιW g) = ιW g := by
    intro g
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change σ.toRingHom.mapMatrix (fixedIncl σ g.val.val : Matrix (Fin 2) (Fin 2) F) =
      (fixedIncl σ g.val.val : Matrix (Fin 2) (Fin 2) F)
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, fixedIncl_coe]
    exact mem_fixedField.mp ((g.val.val : Matrix (Fin 2) (Fin 2) K) i j).2
  rw [← W_card K b hKodd hbK]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun g => ⟨ιW g, hfixW g⟩) ⟨?_, ?_⟩)
  · intro g h hgh
    apply Subtype.ext
    apply hιT
    exact congrArg (fun X : {X : W F a // torusFieldAction F a A hfix sigma X = X} =>
      (X.val : Torus F a)) hgh
  · rintro ⟨X, hX⟩
    have hfixSL : fieldAction F σ X.val.val = X.val.val :=
      congrArg (fun Y : W F a => (Y.val.val : SL F)) hX
    obtain ⟨g', hg'⟩ := exists_fixedIncl σ hfixSL
    have hg'T : g' ∈ Torus K b := (fixedIncl_mem_torus_iff σ b hb g').mp (hg' ▸ X.val.2)
    have hιg : ιT ⟨g', hg'T⟩ = X.val := Subtype.ext hg'
    have hg'W : (⟨g', hg'T⟩ : Torus K b) ∈ W K b := by
      rw [mem_W_iff_odd_order K b hKodd hbK, ← hord, hιg]
      exact (mem_W_iff_odd_order F a hodd ha _).mp X.2
    refine ⟨⟨⟨g', hg'T⟩, hg'W⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hιg

theorem torusSize_half_sq_lt {b m : ℕ} (hb : 3 ≤ b) (hbodd : Odd b) (hm : 3 ≤ m) :
    (torusSize b / 2) ^ 2 < torusSize (b ^ m) / 2 := by
  have hq : b ^ 3 ≤ b ^ m := Nat.pow_le_pow_right (by omega) hm
  have hqodd : Odd (b ^ m) := hbodd.pow
  have h1 := torusSize_two_mul_half hbodd
  have h2 := torusSize_two_mul_half hqodd
  have hb1 : torusSize b ≤ b + 1 := by
    unfold torusSize
    split_ifs <;> omega
  have hq1 : b ^ m ≤ torusSize (b ^ m) + 1 := by
    unfold torusSize
    split_ifs <;> omega
  have hb3 : b ^ 3 = b * b * b := by ring
  set c := torusSize b / 2
  set n := torusSize (b ^ m) / 2
  nlinarith

end

end CFSG.Semidihedral.FixedTorusDerived

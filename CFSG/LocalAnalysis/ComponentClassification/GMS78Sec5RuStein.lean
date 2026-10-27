module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuSimAct
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuOneDefs

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.BenderSuzuki.PFAppendixIII
open CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.Quasithin
open scoped MatrixGroups

namespace RuSimCode

@[expose] def bits (t : Fin 8) : Fin 3 → ZMod 2 := fun i => toZ (t.val.testBit i)

theorem bits_xor (s t : Fin 8) : bits (s ^^^ t) = bits s + bits t := by
  funext i
  simp only [bits, Pi.add_apply, testBit_xor, toZ_xor]

theorem bits_injective : Function.Injective bits := by
  intro s t h
  revert s t
  decide

theorem bits_surjective : Function.Surjective bits := by
  intro x
  revert x
  decide

theorem bits_zero : bits 0 = 0 := by
  funext i
  fin_cases i <;> rfl

theorem slZ_zero : slZ 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem toGF3_zero' : RuCode.toGF3 (0, 0, 0) = 0 := by
  simp only [RuCode.toGF3, RuCode.toGF_zero]
  rfl

theorem xiApply_zero (Xi : List V3) : xiApply Xi 0 = (0, 0, 0) := by
  simp only [xiApply, selV, Nat.zero_testBit, Bool.false_eq_true, ↓reduceIte, addV,
    fin8_xor_zero]

theorem xApply_zero (X : List Nat) {p q : Fin 8} (hpq : canon p q = true) :
    xApply X p q (0, 0, 0) = 0 := by
  have hs : sCoeff p q 0 = (false, false) := by
    revert p q
    decide
  simp only [xApply, hs, selB, Fin.val_zero, Nat.zero_testBit, Bool.false_eq_true, ↓reduceIte,
    Nat.xor_zero]

theorem bits_pow (j : Fin 3) : bits (⟨2 ^ j.val, by fin_cases j <;> decide⟩) = Pi.single j 1 := by
  fin_cases j <;> funext i <;> fin_cases i <;> rfl

end RuSimCode

namespace Sec3.SzR

variable {G : Type} [Group G] [Finite G] {L T R R₂ : Subgroup G} {y d : G}

theorem steinbergCoords
    (hS : SzR G L T R 1 y d)
    (h34 : NoStronglyClosedAbelian G) (hR₂ : IsR₂ L T R R₂ d)
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hNS : ¬ IsSylowOf 2 R (normalizer (R : Set G))) : SteinbergCoords L T R := by
  classical
  have h0 := ruSim0_check
  obtain ⟨v, φ, c, e, Λ, hC⟩ := hS.exists_rCoords h34 hR₂
  obtain ⟨⟨⟨c₀, e₀, p₀, q₀⟩, X₀, Xi₀⟩, hdd, hΛ, hc', he', hact⟩ :=
    hS.exists_action h34 hR₂ h4 hNS hC
  have hAR : gmsA L T ≤ R := gmsA_le_T.trans hS.T_le
  have hv1 : v 1 = 0 := by
    have h := hC.v_mul 1 (one_mem _) 1 (one_mem _)
    rw [mul_one (1 : G)] at h
    linear_combination -h
  have hφ1 : φ 1 = 0 := (hC.ker 1 (one_mem _)).mpr (one_mem _)
  set code := Function.surjInv RuCode.toGF_surjective with hcode
  have hcode1 : ∀ s, RuCode.toGF (code s) = s := Function.surjInv_eq RuCode.toGF_surjective
  have hcode2 : ∀ t, code (RuCode.toGF t) = t := fun t => RuCode.toGF_injective (hcode1 _)
  have hcode_add : ∀ s s', code (s + s') = code s ^^^ code s' := fun s s' =>
    RuCode.toGF_injective (by rw [hcode1, RuCode.toGF_xor, hcode1, hcode1])
  set code3 := Function.surjInv RuCode.toGF3_surjective with hcode3
  have hc3 : ∀ z, RuCode.toGF3 (code3 z) = z := Function.surjInv_eq RuCode.toGF3_surjective
  have hc3' : ∀ w, code3 (RuCode.toGF3 w) = w := fun w => RuCode.toGF3_injective (hc3 _)
  have hc3_add : ∀ z z', code3 (z + z') = addV (code3 z) (code3 z') := fun z z' =>
    RuCode.toGF3_injective (by rw [hc3, RuCode.toGF3_addV, hc3, hc3])
  have hW : ∀ x ∈ R, code3 (φ x) ∈ wList p₀ q₀ := by
    intro x hx
    rw [RuCode.mem_wList, ← hΛ]
    have h1 := hC.mem x hx
    rw [← hc3 (φ x)] at h1
    exact h1
  have hcanon := RuSimCode.canon_d h0 hdd
  have hXlt := RuSimCode.steinData_lt _ hdd
  let eH : gmsA L T →* Multiplicative (Fin 3 → ZMod 2) :=
    { toFun := fun b => Multiplicative.ofAdd (RuSimCode.bits (code (v b)))
      map_one' := by
        show Multiplicative.ofAdd (RuSimCode.bits (code (v 1))) = 1
        rw [hv1]
        have : code 0 = 0 := by rw [← RuCode.toGF_zero, hcode2]
        rw [this, RuSimCode.bits_zero]
        rfl
      map_mul' := fun b b' => by
        show Multiplicative.ofAdd (RuSimCode.bits (code (v ((b : G) * b')))) =
          Multiplicative.ofAdd (RuSimCode.bits (code (v b))) *
            Multiplicative.ofAdd (RuSimCode.bits (code (v b')))
        rw [hC.v_mul _ b.2 _ b'.2, hcode_add, RuSimCode.bits_xor]
        rfl }
  have heH_inj : Function.Injective eH := by
    intro b b' h
    have h1 : RuSimCode.bits (code (v b)) = RuSimCode.bits (code (v b')) := h
    have h2 := congrArg RuCode.toGF (RuSimCode.bits_injective h1)
    rw [hcode1, hcode1] at h2
    have h3 : v ((b : G) * (b' : G)⁻¹) = 0 := by
      rw [hC.v_mul _ b.2 _ (inv_mem b'.2), h2, ← hC.v_mul _ b'.2 _ (inv_mem b'.2),
        mul_inv_cancel, hv1]
    exact Subtype.ext (mul_inv_eq_one.mp (hC.v_inj _ (mul_mem b.2 (inv_mem b'.2)) h3))
  have heH_surj : Function.Surjective eH := by
    intro x
    obtain ⟨t, ht⟩ := RuSimCode.bits_surjective (Multiplicative.toAdd x)
    obtain ⟨b, hb, hbt⟩ := hC.v_surj (RuCode.toGF t)
    refine ⟨⟨b, hb⟩, ?_⟩
    show Multiplicative.ofAdd (RuSimCode.bits (code (v b))) = x
    rw [hbt, hcode2, ht]
    rfl
  set eA : gmsA L T ≃* Multiplicative (Fin 3 → ZMod 2) :=
    MulEquiv.ofBijective eH ⟨heH_inj, heH_surj⟩ with heA
  have heA_apply : ∀ b : gmsA L T, eA b = Multiplicative.ofAdd (RuSimCode.bits (code (v b))) :=
    fun _ => rfl
  let χ : R →* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
    { toFun := fun s => Multiplicative.ofAdd (RuSimCode.slZ (xApply X₀ p₀ q₀ (code3 (φ s))))
      map_one' := by
        show Multiplicative.ofAdd (RuSimCode.slZ (xApply X₀ p₀ q₀ (code3 (φ 1)))) = 1
        have h1 : code3 (φ 1) = (0, 0, 0) := by
          rw [hφ1]
          apply RuCode.toGF3_injective
          rw [hc3, RuSimCode.toGF3_zero']
        rw [h1, RuSimCode.xApply_zero X₀ hcanon, RuSimCode.slZ_zero]
        rfl
      map_mul' := fun s s' => by
        show Multiplicative.ofAdd (RuSimCode.slZ (xApply X₀ p₀ q₀ (code3 (φ ((s : G) * s'))))) =
          Multiplicative.ofAdd (RuSimCode.slZ (xApply X₀ p₀ q₀ (code3 (φ s)))) *
            Multiplicative.ofAdd (RuSimCode.slZ (xApply X₀ p₀ q₀ (code3 (φ s'))))
        rw [hC.mul _ s.2 _ s'.2, hc3_add,
          RuSimCode.xApply_addV X₀ hcanon (RuCode.mem_wList.mp (hW _ s.2))
            (RuCode.mem_wList.mp (hW _ s'.2)), RuSimCode.slZ_xor]
        rfl }
  have hχ : ∀ s : R, χ s =
      Multiplicative.ofAdd (RuSimCode.slZ (xApply X₀ p₀ q₀ (code3 (φ s)))) := fun _ => rfl
  have hslZ_inj : ∀ m < 256, ∀ m' < 256, RuSimCode.slZ m = RuSimCode.slZ m' → m = m' := by
    intro m hm m' hm' h
    have h1 : slToMat m = slToMat m' := by
      funext i j
      exact RuSimCode.toZ_injective (congrFun (congrFun h i) j)
    rw [← (RuSimCode.s0_parts h0).2.2.1 m hm, ← (RuSimCode.s0_parts h0).2.2.1 m' hm', h1]
  have hxlt : ∀ w, xApply X₀ p₀ q₀ w < 256 := RuSimCode.xApply_lt hXlt p₀ q₀
  refine ⟨eA, χ, ?_, ?_, ?_, ?_⟩
  ·
    ext s
    rw [MonoidHom.mem_ker, mem_subgroupOf, hχ]
    constructor
    · intro h1
      have h2 : RuSimCode.slZ (xApply X₀ p₀ q₀ (code3 (φ s))) = RuSimCode.slZ 0 := by
        rw [RuSimCode.slZ_zero]
        exact h1
      have h4 := hslZ_inj _ (hxlt _) 0 (by norm_num) h2
      have h5 := RuSimCode.xiApply_xApply h0 hdd (hW _ s.2)
      rw [h4, RuSimCode.xiApply_zero] at h5
      have h7 : φ s = 0 := by
        rw [← hc3 (φ s), ← h5, RuSimCode.toGF3_zero']
      exact (hC.ker _ s.2).mp h7
    · intro hs
      have h1 : φ s = 0 := (hC.ker _ s.2).mpr hs
      have h2 : code3 (φ s) = (0, 0, 0) := by
        rw [h1]
        apply RuCode.toGF3_injective
        rw [hc3, RuSimCode.toGF3_zero']
      rw [h2, RuSimCode.xApply_zero X₀ hcanon, RuSimCode.slZ_zero]
      rfl
  ·
    intro s
    rw [hχ]
    exact RuSimCode.trace_slZ _
  ·
    intro A hA
    obtain ⟨m, hm, hmA⟩ := RuSimCode.exists_slZ_eq hA
    have hw := RuSimCode.xiApply_mem h0 hdd hm
    obtain ⟨s, hs, hsφ⟩ := hC.surj (RuCode.toGF3 (xiApply Xi₀ m))
      ((hΛ _).mpr (RuCode.mem_wList.mp hw))
    refine ⟨⟨s, hs⟩, ?_⟩
    rw [hχ]
    show Multiplicative.ofAdd (RuSimCode.slZ (xApply X₀ p₀ q₀ (code3 (φ s)))) =
      Multiplicative.ofAdd A
    rw [hsφ, hc3', RuSimCode.xApply_xiApply h0 hdd hm, hmA]
  ·
    intro g hg P hP s t hst
    obtain ⟨r, hrGL, hrA, hrR⟩ := hact g hg
    have hPr : (P : Matrix (Fin 3) (Fin 3) (ZMod 2)) = RuSimCode.toZM (rhoMat r) := by
      ext i j
      set tj : Fin 8 := ⟨2 ^ j.val, by fin_cases j <;> decide⟩ with htj
      obtain ⟨b, hb, hbt⟩ := hC.v_surj (RuCode.toGF tj)
      have hgb : g * b * g⁻¹ ∈ gmsA L T := (mem_normalizer_iff.mp
        (hS.normalizer_le_normalizer_gmsA hR₂ hg) b).mp hb
      have h1 := hP ⟨b, hb⟩ ⟨g * b * g⁻¹, hgb⟩ rfl
      rw [heA_apply, heA_apply] at h1
      have h2 : RuSimCode.bits (code (v (g * b * g⁻¹))) =
          (P : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (RuSimCode.bits (code (v b))) :=
        congrArg Multiplicative.toAdd h1
      rw [hrA b hb tj hbt, hcode2, hbt, hcode2, RuSimCode.bits_pow] at h2
      have h3 : RuSimCode.bits (linApply r tj) i = (P : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j := by
        rw [h2]
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [← h3]
      simp only [RuSimCode.bits, RuSimCode.toZM, rhoMat, htj]
      fin_cases j <;> simp [RuSimCode.linApply_one, RuSimCode.linApply_two,
        RuSimCode.linApply_four]
    have hinv := ((RuSimCode.s0_parts h0).2.1 r hrGL).2.2.1
    have hPinv : ((P⁻¹ : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        RuSimCode.toZM (rhoMat (linInv r)) := by
      have h1 : RuSimCode.toZM (rhoMat r) * RuSimCode.toZM (rhoMat (linInv r)) = 1 := by
        rw [← RuSimCode.toZM_bmul, hinv, RuSimCode.toZM_one]
      have h2 : (P : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
          ((P⁻¹ : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
      rw [hPr] at h2
      have h3 := mul_eq_one_comm.mp h2
      calc ((P⁻¹ : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))
          = ((P⁻¹ : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            (RuSimCode.toZM (rhoMat r) * RuSimCode.toZM (rhoMat (linInv r))) := by
            rw [h1, mul_one]
        _ = RuSimCode.toZM (rhoMat (linInv r)) := by rw [← mul_assoc, h3, one_mul]
    have hw := hW _ s.2
    have h1 := hrR s s.2 (code3 (φ s)) (hc3 _).symm
    rw [hχ, hχ]
    show Multiplicative.ofAdd (RuSimCode.slZ (xApply X₀ p₀ q₀ (code3 (φ t)))) =
      Multiplicative.ofAdd (RuType.stAct P (RuSimCode.slZ (xApply X₀ p₀ q₀ (code3 (φ s)))))
    have h2 : xApply X₀ p₀ q₀ (RuSimCode.nMap ((c₀, e₀, p₀, q₀), X₀, Xi₀) r (code3 (φ s))) =
        maskApply (adMat r) (xApply X₀ p₀ q₀ (code3 (φ s))) := RuSimCode.xApply_nMap h0 hdd r _
    rw [hst, h1, hc3', h2]
    refine congrArg Multiplicative.ofAdd ?_
    rw [RuType.stAct, hPr, hPinv, RuSimCode.slZ,
      (RuSimCode.s0_parts h0).2.2.2.1 r hrGL _ (hxlt _), RuSimCode.toZM_bmul,
      RuSimCode.toZM_bmul]
    rfl

end Sec3.SzR

end CFSG.ComponentClassification.GMS78

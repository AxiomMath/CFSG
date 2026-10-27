module

public import CFSG.LocalAnalysis.RankThreeUC.K518HRkGrp
public import CFSG.GH74.Uniqueness.Bender.FrameTorus
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K518H

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.GH74.Uniqueness.Bender.Frame
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Torus

variable {f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F)

private theorem isOrthonormalFrame_single :
    IsOrthonormalFrame h (fun i : Fin 3 => (Pi.single i 1 : Fin 3 → F)) := by
  intro i j
  simp only [herm, Pi.single_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · have : ∀ k : Fin 3, (h.bar (if k = i then 1 else 0)) * (if k = j then 1 else 0) = 0 := by
      intro k
      by_cases hk : k = i
      · have : ¬ k = j := fun hkj => hij (hk.symm.trans hkj)
        simp [this]
      · simp [hk]
    simp [hij, Ne.symm hij]

private def diagTorus : Subgroup (Fin 3 → Fˣ) where
  carrier := {u | (∀ i, u i ^ (2 ^ f + 1) = 1) ∧ ∏ i, u i = 1}
  mul_mem' := by
    rintro u v ⟨hu, hup⟩ ⟨hv, hvp⟩
    refine ⟨fun i => ?_, ?_⟩
    · rw [Pi.mul_apply, mul_pow, hu, hv, one_mul]
    · show ∏ i, (u i * v i) = 1
      rw [Finset.prod_mul_distrib, hup, hvp, one_mul]
  one_mem' := ⟨fun i => by simp, by simp⟩
  inv_mem' := by
    rintro u ⟨hu, hup⟩
    refine ⟨fun i => ?_, ?_⟩
    · rw [Pi.inv_apply, inv_pow, hu, inv_one]
    · show ∏ i, (u i)⁻¹ = 1
      rw [Finset.prod_inv_distrib, hup, inv_one]

end Torus

section Tor

variable {f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F)

private theorem diagTorus_norm (u : diagTorus (f := f) (F := F)) (i : Fin 3) :
    h.norm ((u.1 i : Fˣ) : F) = 1 := by
  rw [h.norm_eq_pow, ← Units.val_pow_eq_pow_val, u.2.1 i, Units.val_one]

private theorem diagTorus_prod (u : diagTorus (f := f) (F := F)) : ∏ i, ((u.1 i : Fˣ) : F) = 1 := by
  rw [← Units.coe_prod, u.2.2, Units.val_one]

private noncomputable def torElt (u : diagTorus (f := f) (F := F)) :
    gramSU h (1 : Matrix (Fin 3) (Fin 3) F) :=
  frameDiagElt (isOrthonormalFrame_single h) (fun i => ((u.1 i : Fˣ) : F))
    (diagTorus_norm h u) (diagTorus_prod u)

private theorem torElt_mulVec (u : diagTorus (f := f) (F := F)) (i : Fin 3) :
    (((torElt h u : gramSU h (1 : Matrix (Fin 3) (Fin 3) F)) : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) *ᵥ (Pi.single i 1 : Fin 3 → F) = ((u.1 i : Fˣ) : F) • Pi.single i 1 :=
  frameDiagElt_mulVec (isOrthonormalFrame_single h) _ (diagTorus_norm h u) (diagTorus_prod u) i

private theorem torElt_mul (u w : diagTorus (f := f) (F := F)) :
    torElt h (u * w) = torElt h u * torElt h w := by
  refine gramSU_eq_of_frame (isOrthonormalFrame_single h) fun i => ?_
  rw [Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec, torElt_mulVec, torElt_mulVec, mulVec_smul,
    torElt_mulVec, smul_smul]
  show ((u.1 i * w.1 i : Fˣ) : F) • _ = _
  rw [Units.val_mul, mul_comm]

end Tor

section Tor2

variable {f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F)

private noncomputable def torHom : diagTorus (f := f) (F := F) →*
    gramSU h (1 : Matrix (Fin 3) (Fin 3) F) :=
  MonoidHom.mk' (torElt h) (torElt_mul h)

private theorem torElt_injective : Function.Injective (torElt h (f := f) (F := F)) := by
  intro u w huw
  apply Subtype.ext
  funext i
  have h1 := torElt_mulVec h u i
  rw [huw, torElt_mulVec] at h1
  have hne : (Pi.single i 1 : Fin 3 → F) ≠ 0 :=
    frame_ne_zero (isOrthonormalFrame_single h) i
  exact Units.ext (smul_left_injective F hne h1.symm)

private def permTor (π : Equiv.Perm (Fin 3)) (u : diagTorus (f := f) (F := F)) :
    diagTorus (f := f) (F := F) :=
  ⟨fun i => u.1 (π i), fun i => u.2.1 (π i), by
    have := u.2.2
    rw [← this]
    exact Equiv.prod_comp π u.1⟩

end Tor2

section Rot

variable {f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F)

private noncomputable def rotElt : gramSU h (1 : Matrix (Fin 3) (Fin 3) F) :=
  frameMonoElt (isOrthonormalFrame_single h) (finRotate 3) (fun _ => 1)
    (fun _ => by simp [UnitaryFieldData.norm]) (by simp)

private theorem rotElt_mulVec (i : Fin 3) :
    (((rotElt h : gramSU h (1 : Matrix (Fin 3) (Fin 3) F)) : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) *ᵥ (Pi.single i 1 : Fin 3 → F) =
      (Pi.single (finRotate 3 i) 1 : Fin 3 → F) := by
  have := frameMonoElt_mulVec (isOrthonormalFrame_single h) (finRotate 3) (fun _ => (1 : F))
    (fun _ => by simp [UnitaryFieldData.norm]) (by simp) i
  rw [one_smul] at this
  exact this

private theorem rotElt_inv_mulVec (j : Fin 3) :
    ((((rotElt h : gramSU h (1 : Matrix (Fin 3) (Fin 3) F))⁻¹ : gramSU h (1 : Matrix (Fin 3) (Fin 3) F)) :
      GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ (Pi.single j 1 : Fin 3 → F) =
      (Pi.single ((finRotate 3).symm j) 1 : Fin 3 → F) := by
  have h1 := rotElt_mulVec h ((finRotate 3).symm j)
  rw [Equiv.apply_symm_apply] at h1
  have := inv_mulVec_eq (g := ((rotElt h : gramSU h _) : GL (Fin 3) F)) (x := Pi.single ((finRotate 3).symm j) 1)
    (y := Pi.single j 1) (a := 1) one_ne_zero (by rw [one_smul]; exact h1)
  rw [inv_one, one_smul] at this
  exact this

private theorem rotElt_mul_torElt_mul_inv (u : diagTorus (f := f) (F := F)) :
    rotElt h * torElt h u * (rotElt h)⁻¹ = torElt h (permTor ((finRotate 3).symm) u) := by
  refine gramSU_eq_of_frame (isOrthonormalFrame_single h) fun j => ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, ← mulVec_mulVec,
    ← mulVec_mulVec, rotElt_inv_mulVec, torElt_mulVec, mulVec_smul, rotElt_mulVec,
    Equiv.apply_symm_apply, torElt_mulVec]
  rfl

end Rot

section Center

variable {f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F)

private theorem finRotate3_symm_zero : (finRotate 3).symm 0 = 2 := by decide
private theorem finRotate3_symm_one : (finRotate 3).symm 1 = 0 := by decide
private theorem finRotate3_symm_two : (finRotate 3).symm 2 = 1 := by decide

private theorem rotElt_inv_mul_torElt_mul (u : diagTorus (f := f) (F := F)) :
    (rotElt h)⁻¹ * torElt h u * rotElt h = torElt h (permTor (finRotate 3) u) := by
  have h1 := rotElt_mul_torElt_mul_inv h (permTor (finRotate 3) u)
  have h2 : permTor ((finRotate 3).symm) (permTor (finRotate 3) u) = u := by
    apply Subtype.ext
    funext i
    simp [permTor]
  rw [h2] at h1
  calc (rotElt h)⁻¹ * torElt h u * rotElt h
      = (rotElt h)⁻¹ * (rotElt h * torElt h (permTor (finRotate 3) u) * (rotElt h)⁻¹) *
          rotElt h := by rw [h1]
    _ = torElt h (permTor (finRotate 3) u) := by group

private theorem eq_of_torElt_mem_center (u : diagTorus (f := f) (F := F))
    (hz : torElt h u ∈ Subgroup.center (gramSU h (1 : Matrix (Fin 3) (Fin 3) F))) :
    u.1 0 = u.1 1 ∧ u.1 1 = u.1 2 := by
  have h1 := Subgroup.mem_center_iff.mp hz (rotElt h)
  have h2 : rotElt h * torElt h u * (rotElt h)⁻¹ = torElt h u := by
    rw [mul_inv_eq_iff_eq_mul]
    exact h1
  rw [rotElt_mul_torElt_mul_inv] at h2
  have h3 := torElt_injective h h2
  have h4 : ∀ i, u.1 ((finRotate 3).symm i) = u.1 i := fun i => congrFun (congrArg Subtype.val h3) i
  have e0 := h4 0
  have e1 := h4 1
  have e2 := h4 2
  rw [finRotate3_symm_zero] at e0
  rw [finRotate3_symm_one] at e1
  rw [finRotate3_symm_two] at e2
  exact ⟨e1, e2⟩

private theorem torElt_mem_center_of_eq (u : diagTorus (f := f) (F := F)) (h01 : u.1 0 = u.1 1)
    (h12 : u.1 1 = u.1 2) :
    torElt h u ∈ Subgroup.center (gramSU h (1 : Matrix (Fin 3) (Fin 3) F)) := by
  rw [Subgroup.mem_center_iff]
  intro g
  have hscalar : ((torElt h u : gramSU h (1 : Matrix (Fin 3) (Fin 3) F)) : GL (Fin 3) F) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (u.1 0) := by
    refine GL_eq_of_frame (isOrthonormalFrame_single h) fun i => ?_
    rw [torElt_mulVec, scalar_mulVec]
    fin_cases i
    · rfl
    · simp only [Fin.mk_one, Fin.isValue]; rw [h01]
    · simp only [Fin.reduceFinMk, Fin.isValue]; rw [h01, h12]
  apply Subtype.ext
  change (g : GL (Fin 3) F) * ((torElt h u : gramSU h _) : GL (Fin 3) F) =
    ((torElt h u : gramSU h _) : GL (Fin 3) F) * (g : GL (Fin 3) F)
  rw [hscalar]
  have hc : Matrix.GeneralLinearGroup.scalar (Fin 3) (u.1 0) ∈ Subgroup.center (GL (Fin 3) F) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨_, rfl⟩
  exact Subgroup.mem_center_iff.mp hc (g : GL (Fin 3) F)

end Center

section CaseOne

variable {f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F)

private theorem rotElt_pow_three : rotElt h ^ 3 = 1 := by
  refine gramSU_eq_of_frame (isOrthonormalFrame_single h) fun i => ?_
  rw [pow_succ, pow_succ, pow_one, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul,
    Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, rotElt_mulVec, rotElt_mulVec, rotElt_mulVec]
  have : finRotate 3 (finRotate 3 (finRotate 3 i)) = i := by fin_cases i <;> decide
  rw [this, Subgroup.coe_one, Units.val_one, one_mulVec]

private def mkTor (a b c : Fˣ) (ha : a ^ (2 ^ f + 1) = 1) (hb : b ^ (2 ^ f + 1) = 1)
    (hc : c ^ (2 ^ f + 1) = 1) (habc : a * b * c = 1) : diagTorus (f := f) (F := F) :=
  ⟨![a, b, c], fun i => by fin_cases i <;> simpa, by simpa [Fin.prod_univ_three] using habc⟩

end CaseOne

section CaseOneMain

variable {f : ℕ} {F : Type} [Field F] [Finite F] (h : UnitaryFieldData 2 f F)

include h in
private theorem exists_unit_orderOf_dvd {ℓ : ℕ} [Fact ℓ.Prime] (hℓq : ℓ ∣ 2 ^ f + 1) :
    ∃ ω : Fˣ, orderOf ω = ℓ ∧ ω ^ (2 ^ f + 1) = 1 := by
  have hcard : Nat.card Fˣ = (2 ^ f + 1) * (2 ^ f - 1) := by
    rw [Nat.card_units, h.card_eq_sq]
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    zify [h1, Nat.one_le_pow 2 (2 ^ f) (by omega)]
    ring
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' ℓ (hcard ▸ Dvd.dvd.mul_right hℓq _)
  exact ⟨ω, hω, orderOf_dvd_iff_pow_eq_one.mp (hω ▸ hℓq)⟩

end CaseOneMain

section CaseOneA

variable {f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F)

private theorem hasRankTwoPair_gramSU_aux_ne_three {ℓ : ℕ} [hℓF : Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (hℓ3 : ℓ ≠ 3) {ω : Fˣ} (hωo : orderOf ω = ℓ) (hωq : ω ^ (2 ^ f + 1) = 1)
    {J : Subgroup (MulAut (gramSU h (1 : Matrix (Fin 3) (Fin 3) F)))}
    (hJ : (MulAut.conj : gramSU h (1 : Matrix (Fin 3) (Fin 3) F) →* _).range ≤ J) :
    HasRankTwoPair J ℓ := by
  have hℓ := hℓF.out
  have hωℓ : ω ^ ℓ = 1 := hωo ▸ pow_orderOf_eq_one ω
  have hωinvq : ω⁻¹ ^ (2 ^ f + 1) = 1 := by rw [inv_pow, hωq, inv_one]
  have h1q : (1 : Fˣ) ^ (2 ^ f + 1) = 1 := one_pow _
  let uA : diagTorus (f := f) (F := F) := mkTor ω ω⁻¹ 1 hωq hωinvq h1q (by simp)
  let uB : diagTorus (f := f) (F := F) := mkTor 1 ω ω⁻¹ h1q hωq hωinvq (by simp)
  have huA : ∀ n : ℕ, (uA ^ n).1 = fun i => (uA.1 i) ^ n := fun n => by
    funext i; rfl
  have huAℓ : uA ^ ℓ = 1 := by
    apply Subtype.ext
    funext i
    rw [huA]
    fin_cases i <;> simp [uA, mkTor, hωℓ]
  have huBℓ : uB ^ ℓ = 1 := by
    apply Subtype.ext
    funext i
    show (uB.1 i) ^ ℓ = 1
    fin_cases i <;> simp [uB, mkTor, hωℓ]
  have hpow : ∀ (u : diagTorus (f := f) (F := F)) (n : ℕ), torElt h (u ^ n) = (torElt h u) ^ n :=
    fun u n => map_pow (torHom h) u n
  have hone : torElt h (1 : diagTorus (f := f) (F := F)) = 1 := map_one (torHom h)
  have hz1 : (1 : gramSU h (1 : Matrix (Fin 3) (Fin 3) F)) ∈ Subgroup.center _ := Subgroup.one_mem _
  have ha1 : (torElt h uA) ^ ℓ ∈ Subgroup.center (gramSU h (1 : Matrix (Fin 3) (Fin 3) F)) := by
    rw [← hpow, huAℓ, hone]; exact hz1
  have hb1 : (torElt h uB) ^ ℓ ∈ Subgroup.center (gramSU h (1 : Matrix (Fin 3) (Fin 3) F)) := by
    rw [← hpow, huBℓ, hone]; exact hz1
  have hcomm : uA * uB = uB * uA := Subtype.ext (mul_comm _ _)
  have hab : torElt h uA * torElt h uB * (torElt h uA)⁻¹ * (torElt h uB)⁻¹ ∈
      Subgroup.center (gramSU h (1 : Matrix (Fin 3) (Fin 3) F)) := by
    have : torElt h uA * torElt h uB = torElt h uB * torElt h uA := by
      rw [← torElt_mul, ← torElt_mul, hcomm]
    rw [this]
    simp
  have ha2 : torElt h uA ∉ Subgroup.center (gramSU h (1 : Matrix (Fin 3) (Fin 3) F)) := by
    intro hz
    obtain ⟨h01, -⟩ := eq_of_torElt_mem_center h uA hz
    have h02 : ω = ω⁻¹ := by simpa [uA, mkTor] using h01
    have h03 : ω ^ 2 = 1 := by rw [sq]; exact mul_eq_one_iff_eq_inv.mpr h02
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp (hωo ▸ orderOf_dvd_of_pow_eq_one h03))
  have hb2 : ∀ m : ℕ, (torElt h uB)⁻¹ * (torElt h uA) ^ m ∉
      Subgroup.center (gramSU h (1 : Matrix (Fin 3) (Fin 3) F)) := by
    intro m hz
    have e : (torElt h uB)⁻¹ * (torElt h uA) ^ m = torElt h (uB⁻¹ * uA ^ m) := by
      rw [torElt_mul, hpow]
      congr 1
      exact (map_inv (torHom h) uB).symm
    rw [e] at hz
    obtain ⟨h01, h12⟩ := eq_of_torElt_mem_center h _ hz
    simp [uA, uB, mkTor] at h01 h12
    have e1 : ω ^ m = ω := h01.trans h12
    rw [e1] at h12
    have h3 : ω ^ 3 = 1 := by
      calc ω ^ 3 = ω * ω * ω := by rw [pow_succ, pow_two]
        _ = ω * ω * (ω⁻¹ * ω⁻¹) := by rw [h12]
        _ = 1 := by group
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp
      (hωo ▸ orderOf_dvd_of_pow_eq_one h3))
  exact hasRankTwoPair_of_central_pair (torElt h uA) (torElt h uB) ha1 hb1 hab ha2 hb2 hJ

end CaseOneA

section CaseOneB

variable {f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F)

private theorem hasRankTwoPair_gramSU_aux_three {ω : Fˣ} (hωo : orderOf ω = 3)
    (hωq : ω ^ (2 ^ f + 1) = 1)
    {J : Subgroup (MulAut (gramSU h (1 : Matrix (Fin 3) (Fin 3) F)))}
    (hJ : (MulAut.conj : gramSU h (1 : Matrix (Fin 3) (Fin 3) F) →* _).range ≤ J) :
    HasRankTwoPair J 3 := by
  have hω3 : ω ^ 3 = 1 := hωo ▸ pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hωo
    omega
  have hω2q : (ω ^ 2) ^ (2 ^ f + 1) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hωq, one_pow]
  have h1q : (1 : Fˣ) ^ (2 ^ f + 1) = 1 := one_pow _
  have hω23 : (ω ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]
  have hωinv : (ω ^ 2)⁻¹ = ω := inv_eq_of_mul_eq_one_left (by rw [← pow_succ']; exact hω3)
  let uA : diagTorus (f := f) (F := F) :=
    mkTor 1 ω (ω ^ 2) h1q hωq hω2q (by rw [one_mul, ← pow_succ']; exact hω3)
  have hpow : ∀ (u : diagTorus (f := f) (F := F)) (n : ℕ), torElt h (u ^ n) = (torElt h u) ^ n :=
    fun u n => map_pow (torHom h) u n
  have hone : torElt h (1 : diagTorus (f := f) (F := F)) = 1 := map_one (torHom h)
  have hz1 : (1 : gramSU h (1 : Matrix (Fin 3) (Fin 3) F)) ∈ Subgroup.center _ :=
    Subgroup.one_mem _
  have huA3 : uA ^ 3 = 1 := by
    apply Subtype.ext
    funext i
    show (uA.1 i) ^ 3 = 1
    fin_cases i <;> simp [uA, mkTor, hω3, hω23]
  have ha1 : (torElt h uA) ^ 3 ∈ Subgroup.center (gramSU h (1 : Matrix (Fin 3) (Fin 3) F)) := by
    rw [← hpow, huA3, hone]; exact hz1
  have hb1 : (rotElt h) ^ 3 ∈ Subgroup.center (gramSU h (1 : Matrix (Fin 3) (Fin 3) F)) := by
    rw [rotElt_pow_three]; exact hz1
  have hab : torElt h uA * rotElt h * (torElt h uA)⁻¹ * (rotElt h)⁻¹ ∈
      Subgroup.center (gramSU h (1 : Matrix (Fin 3) (Fin 3) F)) := by
    have e1 : torElt h uA * rotElt h * (torElt h uA)⁻¹ * (rotElt h)⁻¹ =
        torElt h uA * (rotElt h * torElt h uA * (rotElt h)⁻¹)⁻¹ := by group
    rw [e1, rotElt_mul_torElt_mul_inv]
    have e2 : torElt h uA * (torElt h (permTor ((finRotate 3).symm) uA))⁻¹ =
        torElt h (uA * (permTor ((finRotate 3).symm) uA)⁻¹) := by
      rw [torElt_mul]
      congr 1
      exact (map_inv (torHom h) _).symm
    rw [e2]
    apply torElt_mem_center_of_eq
    · simp [permTor, uA, mkTor, hωinv]
    · simp [permTor, uA, mkTor, pow_two]
  have ha2 : torElt h uA ∉ Subgroup.center (gramSU h (1 : Matrix (Fin 3) (Fin 3) F)) := by
    intro hz
    obtain ⟨h01, -⟩ := eq_of_torElt_mem_center h uA hz
    exact hω1 (by simpa [uA, mkTor] using h01.symm)
  have hb2 : ∀ m : ℕ, (rotElt h)⁻¹ * (torElt h uA) ^ m ∉
      Subgroup.center (gramSU h (1 : Matrix (Fin 3) (Fin 3) F)) := by
    intro m hz
    have h1 := Subgroup.mem_center_iff.mp hz (torElt h uA)
    have h2 : torElt h uA * (rotElt h)⁻¹ = (rotElt h)⁻¹ * torElt h uA := by
      have h3 : torElt h uA * (rotElt h)⁻¹ * (torElt h uA) ^ m =
          (rotElt h)⁻¹ * torElt h uA * (torElt h uA) ^ m := by
        calc torElt h uA * (rotElt h)⁻¹ * (torElt h uA) ^ m
            = torElt h uA * ((rotElt h)⁻¹ * (torElt h uA) ^ m) := by rw [mul_assoc]
          _ = ((rotElt h)⁻¹ * (torElt h uA) ^ m) * torElt h uA := h1
          _ = (rotElt h)⁻¹ * ((torElt h uA) ^ m * torElt h uA) := by rw [mul_assoc]
          _ = (rotElt h)⁻¹ * (torElt h uA * (torElt h uA) ^ m) := by
              rw [(Commute.self_pow (torElt h uA) m).eq]
          _ = (rotElt h)⁻¹ * torElt h uA * (torElt h uA) ^ m := by rw [mul_assoc]
      exact mul_right_cancel h3
    have h4 : (rotElt h)⁻¹ * torElt h uA * rotElt h = torElt h uA := by
      rw [← h2, mul_assoc, inv_mul_cancel, mul_one]
    rw [rotElt_inv_mul_torElt_mul] at h4
    have h5 := torElt_injective h h4
    have h6 := congrFun (congrArg Subtype.val h5) 0
    simp [permTor, uA, mkTor] at h6
    exact hω1 h6
  exact hasRankTwoPair_of_central_pair (torElt h uA) (rotElt h) ha1 hb1 hab ha2 hb2 hJ

end CaseOneB

section CaseOneMain2

variable {f : ℕ} {F : Type} [Field F] [Finite F] (h : UnitaryFieldData 2 f F)

theorem hasRankTwoPair_gramSU_of_dvd {ℓ : ℕ} [hℓF : Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (hℓq : ℓ ∣ 2 ^ f + 1)
    {J : Subgroup (MulAut (gramSU h (1 : Matrix (Fin 3) (Fin 3) F)))}
    (hJ : inner (gramSU h (1 : Matrix (Fin 3) (Fin 3) F)) ≤ J) : HasRankTwoPair J ℓ := by
  obtain ⟨ω, hωo, hωq⟩ := exists_unit_orderOf_dvd h hℓq
  by_cases hℓ3 : ℓ = 3
  · subst hℓ3
    exact hasRankTwoPair_gramSU_aux_three h hωo hωq hJ
  · exact hasRankTwoPair_gramSU_aux_ne_three h hℓ2 hℓ3 hωo hωq hJ

end CaseOneMain2

end CFSG.LocalAnalysis.RankThreeUC.S15.K518H

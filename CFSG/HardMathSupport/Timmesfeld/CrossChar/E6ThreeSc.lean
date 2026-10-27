module

public import Certificates.Certificate13657
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharStabilizer

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.Blueprint.Chevalley.RootCertificate CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def e6Shift (w : WeylGroup .E6) : Fin Tag.E6.rank → ℤ :=
  fun i => ((w • e6Omega3) i - e6Omega3 i) / 3

theorem three_dvd_cartan_e6Omega3 : ∀ j : Fin Tag.E6.rank,
    (3 : ℤ) ∣ ∑ k, Tag.E6.cartan j k * e6Omega3 k := by
  decide +kernel

theorem three_dvd_smul_e6Omega3_sub (w : WeylGroup .E6) :
    ∀ i, (3 : ℤ) ∣ (w • e6Omega3) i - e6Omega3 i := by
  refine (coxeterSystem Tag.E6).simple_induction_left
    (p := fun w => ∀ i, (3 : ℤ) ∣ (w • e6Omega3) i - e6Omega3 i) w ?_ ?_
  · intro i
    simp
  · intro w j ih i
    rw [mul_smul]
    change (3 : ℤ) ∣ (simple Tag.E6 j • w • e6Omega3) i - e6Omega3 i
    rw [simple_smul, reflect]
    have hsum : (3 : ℤ) ∣ ∑ k, Tag.E6.cartan j k * (w • e6Omega3) k := by
      have e : ∑ k, Tag.E6.cartan j k * (w • e6Omega3) k =
          ∑ k, Tag.E6.cartan j k * e6Omega3 k +
            ∑ k, Tag.E6.cartan j k * ((w • e6Omega3) k - e6Omega3 k) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [e]
      exact dvd_add (three_dvd_cartan_e6Omega3 j)
        (Finset.dvd_sum fun k _ => Dvd.dvd.mul_left (ih k) _)
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have e : (w • e6Omega3) i - (∑ k, Tag.E6.cartan j k * (w • e6Omega3) k) *
        (Pi.single j 1 : Fin Tag.E6.rank → ℤ) i - e6Omega3 i =
        ((w • e6Omega3) i - e6Omega3 i) - (∑ k, Tag.E6.cartan j k * (w • e6Omega3) k) *
          (Pi.single j 1 : Fin Tag.E6.rank → ℤ) i := by ring
    rw [e]
    exact dvd_sub (ih i) (Dvd.dvd.mul_right hsum _)

theorem three_smul_e6Shift (w : WeylGroup .E6) :
    (3 : ℤ) • e6Shift w = w • e6Omega3 - e6Omega3 := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, e6Shift, Pi.sub_apply]
  exact Int.mul_ediv_cancel' (three_dvd_smul_e6Omega3_sub w i)

theorem e6Shift_eq_of_three_smul {w : WeylGroup .E6} {v : Fin Tag.E6.rank → ℤ}
    (h : (3 : ℤ) • v = w • e6Omega3 - e6Omega3) : e6Shift w = v := by
  funext i
  have h1 := congrFun ((three_smul_e6Shift w).trans h.symm) i
  simp only [Pi.smul_apply, smul_eq_mul] at h1
  omega

theorem e6Shift_one : e6Shift 1 = 0 :=
  e6Shift_eq_of_three_smul (by rw [one_smul, sub_self, smul_zero])

theorem e6Shift_mul (w₁ w₂ : WeylGroup .E6) :
    e6Shift (w₁ * w₂) = w₁ • e6Shift w₂ + e6Shift w₁ := by
  refine e6Shift_eq_of_three_smul ?_
  rw [smul_add, smul_comm, three_smul_e6Shift, three_smul_e6Shift, smul_sub, mul_smul]
  abel


theorem e6ShiftT_eq {t : List ℕ} {w : WeylGroup .E6} (h : e6Certificate.Represents t w) :
    e6ShiftT e6Certificate t = e6Shift w := by
  funext i
  rw [e6ShiftT, tupleVec_eq h, e6Shift]

section Hom

variable {b : Fin Tag.E6.rank → ZMod 3}

theorem triPairing_smul_of_mem {w : WeylGroup .E6} (hw : w ∈ charStabilizer (triChar b))
    (v : Fin Tag.E6.rank → ℤ) : triPairing b (w • v) = triPairing b v := by
  have h := hw v
  rw [triChar_apply, triChar_apply] at h
  exact Z3.ofAdd_eq_ofAdd_iff.1 h

theorem triPairing_e6Shift_mul {w₁ : WeylGroup .E6} (hw₁ : w₁ ∈ charStabilizer (triChar b))
    (w₂ : WeylGroup .E6) :
    triPairing b (e6Shift (w₁ * w₂)) = triPairing b (e6Shift w₂) + triPairing b (e6Shift w₁) := by
  rw [e6Shift_mul, triPairing_add, triPairing_smul_of_mem hw₁]

theorem triPairing_e6Shift_of_mem_kernelWeylGroup {u : WeylGroup .E6}
    (hu : u ∈ kernelWeylGroup (triChar b)) : triPairing b (e6Shift u) = 0 := by
  have hφ1 : triPairing b (e6Shift 1) = 0 := by rw [e6Shift_one, triPairing_zero]
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, i, hα, rfl⟩ := hx
    have hxW : w * simple Tag.E6 i * w⁻¹ ∈ charStabilizer (triChar b) :=
      kernelWeylGroup_le (Subgroup.subset_closure ⟨w, i, hα, rfl⟩)
    have hsq : w * simple Tag.E6 i * w⁻¹ * (w * simple Tag.E6 i * w⁻¹) = 1 := by
      have : simple Tag.E6 i * simple Tag.E6 i = 1 :=
        (coxeterSystem Tag.E6).simple_mul_simple_self i
      calc w * simple Tag.E6 i * w⁻¹ * (w * simple Tag.E6 i * w⁻¹) =
          w * (simple Tag.E6 i * simple Tag.E6 i) * w⁻¹ := by group
        _ = 1 := by rw [this, mul_one, mul_inv_cancel]
    have h2 := triPairing_e6Shift_mul hxW (w * simple Tag.E6 i * w⁻¹)
    rw [hsq, hφ1] at h2
    have h4 : (4 : ZMod 3) = 1 := by decide
    calc triPairing b (e6Shift (w * simple Tag.E6 i * w⁻¹)) =
        (4 : ZMod 3) * triPairing b (e6Shift (w * simple Tag.E6 i * w⁻¹)) := by
          rw [h4, one_mul]
      _ = 2 * (triPairing b (e6Shift (w * simple Tag.E6 i * w⁻¹)) +
          triPairing b (e6Shift (w * simple Tag.E6 i * w⁻¹))) := by ring
      _ = 0 := by rw [← h2, mul_zero]
  | one => exact hφ1
  | mul x y hx _ ihx ihy =>
    rw [triPairing_e6Shift_mul (kernelWeylGroup_le hx), ihx, ihy, add_zero]
  | inv x hx ihx =>
    have h := triPairing_e6Shift_mul (kernelWeylGroup_le hx) x⁻¹
    rw [mul_inv_cancel, hφ1, ihx, add_zero] at h
    exact h.symm

end Hom

theorem mem_kernelWeylGroup_of_stabCert {S : StabCert3} (hS : S.check e6Certificate = true)
    (hpass : ∀ t ∈ S.passing e6Certificate,
      t = List.range Tag.E6.rank ∨ e6ScTest e6Certificate S.vec t = true)
    {w : WeylGroup .E6} (hw : w ∈ charStabilizer (triChar (vec3 (τ := .E6) S.vec)))
    (h0 : triPairing (vec3 (τ := .E6) S.vec) (e6Shift w) = 0) :
    w ∈ kernelWeylGroup (triChar (vec3 (τ := .E6) S.vec)) := by
  obtain ⟨u, hu, hwu⟩ := exists_mul_mem_kernelPosStabilizer hw
  have hwu0 : triPairing (vec3 (τ := .E6) S.vec) (e6Shift (w * u)) = 0 := by
    rw [triPairing_e6Shift_mul hw, triPairing_e6Shift_of_mem_kernelWeylGroup hu, h0, add_zero]
  obtain ⟨t, ht, hrep⟩ := StabCert3.exists_passing_of_mem e6Certificate_check hS hwu
  rcases hpass t ht with rfl | htest
  · have h1 : w * u = 1 := represents_unique hrep (represents_one e6Certificate_check)
    rw [eq_inv_of_mul_eq_one_left h1]
    exact inv_mem hu
  · simp only [e6ScTest, decide_eq_true_eq] at htest
    rw [e6ShiftT_eq hrep] at htest
    exact absurd hwu0 htest

theorem e6ThreeScCheck_spec :
    orbitCheck3 .E6 e6ThreeReps e6ThreeOrbit = true ∧
      ∀ S ∈ e6ThreeStabs, S.check e6Certificate = true ∧ ∀ t ∈ S.passing e6Certificate,
        t = List.range Tag.E6.rank ∨ e6ScTest e6Certificate S.vec t = true := by
  have h := Certificates.certificate13657
  simp only [e6ThreeScCheck, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨h.1, fun S hS => ⟨(h.2 S hS).1, (h.2 S hS).2⟩⟩

theorem e6ThreeStabs_vec : e6ThreeStabs.map StabCert3.vec = e6ThreeReps := rfl

theorem e6Shift_mem_kernelWeylGroup (b : Fin Tag.E6.rank → ZMod 3)
    {w : WeylGroup .E6} (hw : w ∈ charStabilizer (triChar b)) (h0 : triPairing b (e6Shift w) = 0) :
    w ∈ kernelWeylGroup (triChar b) := by
  obtain ⟨horbit, hstab⟩ := e6ThreeScCheck_spec
  have hvec := e6ThreeStabs_vec
  obtain ⟨ρ, hρ, t, ht⟩ := exists_isCharConj_of_orbitCheck3 horbit (triChar b)
  have hlen : ρ < e6ThreeStabs.length := by
    rw [← List.length_map StabCert3.vec, hvec]
    exact hρ
  set S := e6ThreeStabs[ρ] with hSdef
  have hSv : S.vec = e6ThreeReps.getD ρ [] := by
    rw [List.getD_eq_getElem _ _ hρ, hSdef]
    have := congrArg (fun l => l[ρ]?) hvec
    simp only [List.getElem?_map, List.getElem?_eq_getElem hlen, List.getElem?_eq_getElem hρ,
      Option.map_some, Option.some.injEq] at this
    exact this
  obtain ⟨hScheck, hSpass⟩ := hstab S (List.getElem_mem hlen)
  rw [← hSv] at ht
  set bρ := vec3 (τ := .E6) S.vec with hbρ
  have hw₀ : t⁻¹ * w * t ∈ charStabilizer (triChar bρ) :=
    (charStabilizer_iff_of_isCharConj ht).1 hw
  have hpair : ∀ v, triPairing b v = triPairing bρ (t⁻¹ • v) := fun v => by
    have h := ht v
    rw [triChar_apply, triChar_apply] at h
    exact Z3.ofAdd_eq_ofAdd_iff.1 h
  have h00 : triPairing bρ (e6Shift (t⁻¹ * w * t)) = 0 := by
    have hinv : t⁻¹ • e6Shift t + e6Shift t⁻¹ = 0 := by
      rw [← e6Shift_mul, inv_mul_cancel, e6Shift_one]
    rw [mul_assoc, e6Shift_mul, e6Shift_mul, smul_add, triPairing_add, triPairing_add,
      ← hpair, ← hpair, triPairing_smul_of_mem hw, h0, add_zero, hpair, ← triPairing_add, hinv,
      triPairing_zero]
  have hk := mem_kernelWeylGroup_of_stabCert hScheck hSpass hw₀ h00
  rw [kernelWeylGroup_eq_map ht]
  exact ⟨t⁻¹ * w * t, hk, by simp [mul_assoc]⟩

theorem mem_kernelReflectionGroup_of_e6Shift {K : Type} [Field K]
    (a : Fin Tag.E6.rank → Kˣ) (h3 : ∀ i, a i ^ 3 = 1) {w : WeylGroup .E6}
    (hw : w ∈ rootCharStabilizerSubgroup a) (h1 : rootChar a (e6Shift w) = 1) :
    w ∈ kernelReflectionGroup a := by
  obtain ⟨χ', hker⟩ := exists_triChar_ker_eq (rootCharHom3 a) (rootCharHom3_pow_three a h3)
  have hS : rootCharStabilizerSubgroup a = charStabilizer (rootCharHom3 a) :=
    Subgroup.ext fun w => Iff.rfl
  have hW : kernelReflectionGroup a = kernelWeylGroup (rootCharHom3 a) := rfl
  rw [hS, charStabilizer_congr_ker hker] at hw
  rw [hW, kernelWeylGroup_congr_ker hker]
  have h1' : χ' (Multiplicative.ofAdd (e6Shift w)) = 1 :=
    (hker (Multiplicative.ofAdd (e6Shift w))).1 h1
  rw [eq_triChar χ'] at hw h1' ⊢
  rw [triChar_apply, Z3.ofAdd_eq_one] at h1'
  exact e6Shift_mem_kernelWeylGroup _ hw h1'

end CFSG.HardMathSupport.Timmesfeld.CrossChar

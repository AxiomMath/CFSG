module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeSc
public import Certificates.Certificate13616

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.Blueprint.Chevalley.RootCertificate CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem triPairing_three_smul (b : Fin Tag.E6.rank → ZMod 3) (v : Fin Tag.E6.rank → ℤ) :
    triPairing b ((3 : ℤ) • v) = 0 := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  simp [triPairing, Int.cast_mul, h3]

theorem mem_kernelWeylGroup_of_nonInner
    (b : Fin Tag.E6.rank → ZMod 3)
    (hb : triPairing b e6Omega3 ≠ 0) {w : WeylGroup .E6} (hw : w ∈ charStabilizer (triChar b)) :
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
  obtain ⟨hScheck, -⟩ := hstab S (List.getElem_mem hlen)
  rw [← hSv] at ht
  set bρ := vec3 (τ := .E6) S.vec with hbρ
  have hw₀ : t⁻¹ * w * t ∈ charStabilizer (triChar bρ) :=
    (charStabilizer_iff_of_isCharConj ht).1 hw
  have hpair : ∀ v, triPairing b v = triPairing bρ (t⁻¹ • v) := fun v => by
    have h := ht v
    rw [triChar_apply, triChar_apply] at h
    exact Z3.ofAdd_eq_ofAdd_iff.1 h
  have hbρ0 : triPairing bρ e6Omega3 ≠ 0 := by
    intro h0
    apply hb
    rw [hpair]
    have e : t⁻¹ • e6Omega3 = e6Omega3 + (3 : ℤ) • e6Shift t⁻¹ := by
      rw [three_smul_e6Shift]
      abel
    rw [e, triPairing_add, h0, triPairing_three_smul, add_zero]
  have hcert := Certificates.certificate13616
  unfold e6NonInnerCheck at hcert
  rw [List.all_eq_true] at hcert
  have hS := hcert S (List.getElem_mem hlen)
  rw [Bool.or_eq_true, decide_eq_true_eq] at hS
  have hpass : ∀ t' ∈ S.passing e6Certificate, t' = List.range Tag.E6.rank := by
    rcases hS with h | h
    · exact absurd h hbρ0
    · rw [List.all_eq_true] at h
      exact fun t' ht' => by simpa using h t' ht'
  obtain ⟨u, hu, hwu⟩ := exists_mul_mem_kernelPosStabilizer hw₀
  obtain ⟨t', ht', hrep⟩ := StabCert3.exists_passing_of_mem e6Certificate_check hScheck hwu
  rw [hpass t' ht'] at hrep
  have h1 : t⁻¹ * w * t * u = 1 := represents_unique hrep (represents_one e6Certificate_check)
  have hk : t⁻¹ * w * t ∈ kernelWeylGroup (triChar bρ) := by
    rw [eq_inv_of_mul_eq_one_left h1]
    exact inv_mem hu
  rw [kernelWeylGroup_eq_map ht]
  exact ⟨t⁻¹ * w * t, hk, by simp [mul_assoc]⟩

theorem mem_kernelReflectionGroup_of_nonInner
    {K : Type} [Field K] (a : Fin Tag.E6.rank → Kˣ)
    (h3 : ∀ i, a i ^ 3 = 1) (hnon : rootChar a e6Omega3 ≠ 1) {w : WeylGroup .E6}
    (hw : w ∈ rootCharStabilizerSubgroup a) : w ∈ kernelReflectionGroup a := by
  obtain ⟨χ', hker⟩ := exists_triChar_ker_eq (rootCharHom3 a) (rootCharHom3_pow_three a h3)
  have hS : rootCharStabilizerSubgroup a = charStabilizer (rootCharHom3 a) :=
    Subgroup.ext fun w => Iff.rfl
  have hW : kernelReflectionGroup a = kernelWeylGroup (rootCharHom3 a) := rfl
  rw [hS, charStabilizer_congr_ker hker] at hw
  rw [hW, kernelWeylGroup_congr_ker hker]
  have hnon' : χ' (Multiplicative.ofAdd e6Omega3) ≠ 1 := fun h =>
    hnon ((hker (Multiplicative.ofAdd e6Omega3)).2 h)
  rw [eq_triChar χ'] at hw hnon' ⊢
  rw [triChar_apply, Ne, Z3.ofAdd_eq_one] at hnon'
  exact mem_kernelWeylGroup_of_nonInner _ hnon' hw

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

end

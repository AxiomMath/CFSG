module

public import CFSG.GH74.Uniqueness.Bender.UnitaryFixed
public import CFSG.GH74.Uniqueness.Bender.Frame311
public import CFSG.GH74.Uniqueness.Bender.FrameReduction
public import CFSG.GH74.Uniqueness.Bender.FrameAbelian
public import CFSG.GH74.Uniqueness.Bender.FrameBorel
public import CFSG.GH74.Uniqueness.Bender.FrameNormalizer

public section

namespace CFSG.GH74.Uniqueness.Bender.Frame

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

variable {p f : ℕ} {E : Type} [Field E]

theorem exists_orthonormal_frame (hU : UnitaryFieldData 2 f E) (hf : 2 ≤ f)
    {C : Subgroup (GL (Fin 3) E)} {t : GL (Fin 3) E}
    (hC : C ≤ gramSU hU 1) (hodd : Odd (Nat.card C)) (ht : t ∈ gramSU hU 1) (ht2 : t * t = 1)
    (ht1 : t ≠ 1) (hnorm : ∀ c ∈ C, t * c * t⁻¹ ∈ C) (hiso : ¬ FixesIsotropicLine hU C) :
    ∃ v : Fin 3 → (Fin 3 → E), IsOrthonormalFrame hU v ∧ (∀ c ∈ C, PermutesLines v c) ∧
      PermutesLines v t := by
  have hchar : CharP E 2 := hU.charP
  have hns : ∃ c ∈ C, ¬ IsScalarMat c := by
    by_contra hall
    push Not at hall
    apply hiso
    refine ⟨![1, 1, 0], ?_, ?_, fun c hc => ?_⟩
    · intro h0
      have := congrFun h0 0
      simp at this
    · unfold herm
      simp [Fin.sum_univ_three, CharTwo.add_self_eq_zero]
    · obtain ⟨μ, hμ⟩ := hall c hc
      refine ⟨μ, ?_⟩
      rw [hμ, Matrix.smul_mulVec, Matrix.one_mulVec]
  obtain ⟨A, hAC, hAC', hAt, hAab, hAns⟩ := exists_abelian_normal_nonscalar hU
    (fun c hc => (mem_gramSU.mp (hC hc)).2) hodd ht2 hnorm hns
  exact frame_of_abelian_normal hU hf hC hodd ht ht2 ht1 hnorm hiso hAC hAC' hAt hAab hAns

end CFSG.GH74.Uniqueness.Bender.Frame

namespace CFSG.GH74.Uniqueness.Bender

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer
open CFSG.ComponentClassification.UnbalancedCatalog (IsCanonicalGram isCanonicalGram_one
  even_unitary_canonical_field_centralizer_transfer)
open CFSG.BenderSuzuki CFSG.ShultStronglyClosedTI CFSG.Assembly.LowTwoRank
open CFSG.GH74.Uniqueness.Bender.Frame
open scoped commutatorElement

section Glue

theorem BenderType.exists_equiv_unitaryModelP {K : Type*} [Group K] {n e : ℕ}
    (h : BenderType K n 3 e) :
    ∃ hU : UnitaryFieldData 2 n (GaloisField 2 (2 * n)), Nonempty (K ≃* UnitaryModelP n hU) := by
  obtain ⟨hn, ⟨e₁⟩⟩ : 2 ≤ n ∧ Nonempty (K ≃* PSU3Model n) := by
    cases h with
    | unitary n hn e => exact ⟨hn, ⟨e⟩⟩
  have hmodel : PSU3Model n = CFSG.Open.PSU3 2 n := CFSG.Models.benderPSU3Model_eq_psu3 n
  let E := GaloisField 2 (2 * n)
  have hU : UnitaryFieldData 2 n E := unitaryFieldData_gf (by omega)
  have e₀ : K ≃* StatedProj (StatedSU 3 (2 ^ n) E) :=
    (e₁.trans (MulEquiv.subgroupCongr hmodel)).trans (glaSUCanonicalEquivNative n).symm
  have hC : IsPrimeFormGram (1 : GL (Fin 3) E) := isPrimeFormGram_one
  obtain ⟨χ⟩ := nonempty_primeFormP_mulEquiv hU hC
  exact ⟨hU, ⟨e₀.trans ((unitaryPSUEquiv hU (by omega)).symm.trans χ.symm)⟩⟩


theorem frame311_of_unitary
    {E : Type} [Field E] {f : ℕ} (hU : UnitaryFieldData 2 f E)
    (hf : 2 ≤ f) {Cb : Subgroup (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))}
    (hodd : Odd (Nat.card Cb)) {tb : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)}
    (ht2 : tb * tb = 1) (ht1 : tb ≠ 1) (hnorm : ∀ c ∈ Cb, tb * c * tb⁻¹ ∈ Cb)
    (hborel : ∀ Q : Sylow 2 (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)),
      ¬ Cb ≤ Subgroup.normalizer ((Q : Subgroup (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))) :
        Set (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)))) :
    ∃ v : Fin 3 → (Fin 3 → E), IsOrthonormalFrame hU v ∧
      Frame311 (2 ^ f) (Nat.gcd 3 (2 ^ f + 1)) (frameTorus hU v) (frameMono hU v) tb ∧
      Cb ⊔ Subgroup.zpowers tb ≤ frameMono hU v ∧
      frameMono hU v = Subgroup.normalizer ((frameTorus hU v : Subgroup
        (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))) :
        Set (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E))) := by
  classical
  have hchar : CharP E 2 := hU.charP
  have hfin : Finite E := hU.finite
  let mk : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E) →*
      primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E) :=
    QuotientGroup.mk' (normOneScalars hU (gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) 3)
  have hmk_surj : Function.Surjective mk := QuotientGroup.mk'_surjective _
  have hmk_ker : ∀ s, mk s = 1 ↔
      s ∈ normOneScalars hU (gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) 3 :=
    fun s => QuotientGroup.eq_one_iff s
  have hZ3 : ∀ z ∈ normOneScalars hU (gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) 3, z ^ 3 = 1 := by
    intro z hz
    obtain ⟨c, -, hc3, hzc⟩ := hz
    apply Subtype.ext
    rw [Subgroup.coe_pow, hzc, ← map_pow, hc3, map_one]
    rfl
  let CS : Subgroup (gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) := Cb.comap mk
  let Cmat : Subgroup (GL (Fin 3) E) := CS.map (gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)).subtype
  have hCmat_le : Cmat ≤ gramSU hU (1 : Matrix (Fin 3) (Fin 3) E) := Subgroup.map_subtype_le CS
  have hmemCmat : ∀ g : GL (Fin 3) E, g ∈ Cmat ↔
      ∃ s : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E), mk s ∈ Cb ∧ (s : GL (Fin 3) E) = g := by
    intro g
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, rfl⟩
  have hCodd : Odd (Nat.card Cmat) := by
    by_contra hne
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hne
    obtain ⟨x, hx2⟩ := exists_prime_orderOf_dvd_card' 2 hne
    obtain ⟨s, hs, hsx⟩ := (hmemCmat (x : GL (Fin 3) E)).mp x.2
    have hord_s : orderOf s = 2 := by
      rw [← Subgroup.orderOf_coe s, hsx, Subgroup.orderOf_coe x]
      exact hx2
    have hm_odd : Odd (orderOf (mk s)) :=
      Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard Cb hs)
    have hsm : s ^ orderOf (mk s) ∈
        normOneScalars hU (gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) 3 := by
      rw [← hmk_ker, map_pow, pow_orderOf_eq_one]
    have h1 : s ^ (orderOf (mk s) * 3) = 1 := by
      rw [pow_mul]
      exact hZ3 _ hsm
    have h2 : 2 ∣ orderOf (mk s) * 3 := by
      have := orderOf_dvd_of_pow_eq_one h1
      rwa [hord_s] at this
    have h3 : Odd (orderOf (mk s) * 3) := hm_odd.mul (by decide)
    exact (Nat.not_even_iff_odd.mpr h3) (even_iff_two_dvd.mpr h2)
  obtain ⟨t₁, ht₁⟩ := hmk_surj tb
  have htS_mk : mk (t₁ ^ 3) = tb := by
    rw [map_pow, ht₁]
    calc tb ^ 3 = tb * (tb * tb) := pow_three tb
      _ = tb := by rw [ht2, mul_one]
  have htS_sq : t₁ ^ 3 * t₁ ^ 3 = 1 := by
    have h1 : t₁ ^ 2 ∈ normOneScalars hU (gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) 3 := by
      rw [← hmk_ker, map_pow, ht₁, sq, ht2]
    calc t₁ ^ 3 * t₁ ^ 3 = (t₁ ^ 2) ^ 3 := by group
      _ = 1 := hZ3 _ h1
  have htS_ne : t₁ ^ 3 ≠ 1 := fun h1 => ht1 (by rw [← htS_mk, h1, map_one])
  have htmat2 : ((t₁ ^ 3 : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) : GL (Fin 3) E) *
      ((t₁ ^ 3 : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) : GL (Fin 3) E) = 1 := by
    have := congrArg (fun x : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E) => (x : GL (Fin 3) E))
      htS_sq
    simpa using this
  have htmat1 : ((t₁ ^ 3 : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) : GL (Fin 3) E) ≠ 1 := by
    intro h1
    apply htS_ne
    exact Subtype.ext h1
  have hCnorm : ∀ c ∈ Cmat, ((t₁ ^ 3 : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) :
      GL (Fin 3) E) * c * ((t₁ ^ 3 : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) :
      GL (Fin 3) E)⁻¹ ∈ Cmat := by
    intro c hc
    obtain ⟨s, hs, rfl⟩ := (hmemCmat c).mp hc
    refine (hmemCmat _).mpr ⟨t₁ ^ 3 * s * (t₁ ^ 3)⁻¹, ?_, rfl⟩
    rw [map_mul, map_mul, map_inv, htS_mk]
    exact hnorm _ hs
  have hiso : ¬ FixesIsotropicLine hU Cmat := by
    rintro ⟨v, hv, hvi, hfix⟩
    obtain ⟨Q, hQ⟩ := exists_sylow_normalizer_of_isotropic hU hf hv hvi
    apply hborel Q
    intro c hc
    obtain ⟨s, hs⟩ := hmk_surj c
    have hsC : s ∈ CS := by
      show mk s ∈ Cb
      rw [hs]
      exact hc
    have hsmat : (s : GL (Fin 3) E) ∈ Cmat := ⟨s, hsC, rfl⟩
    obtain ⟨μ, hμ⟩ := hfix _ hsmat
    have := hQ s ⟨μ, hμ⟩
    rwa [show (QuotientGroup.mk s : primeFormP hU (1 : Matrix (Fin 3) (Fin 3) E)) = c from hs]
      at this
  obtain ⟨v, hv, hCperm, htperm⟩ := exists_orthonormal_frame hU hf hCmat_le hCodd
    (t₁ ^ 3 : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)).2 htmat2 htmat1 hCnorm hiso
  have hCle : Cb ≤ frameMono hU v := by
    intro c hc
    obtain ⟨s, rfl⟩ := hmk_surj c
    have hsC : s ∈ CS := hc
    have h1 : (s : GL (Fin 3) E) ∈ Cmat := ⟨s, hsC, rfl⟩
    have h2 : ((s⁻¹ : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) : GL (Fin 3) E) ∈ Cmat :=
      ⟨s⁻¹, CS.inv_mem hsC, rfl⟩
    exact ⟨s, ⟨hCperm _ h1, hCperm _ h2⟩, rfl⟩
  have htle : tb ∈ frameMono hU v := by
    refine ⟨t₁ ^ 3, ⟨htperm, ?_⟩, htS_mk⟩
    have hinv : ((t₁ ^ 3 : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) : GL (Fin 3) E)⁻¹ =
        ((t₁ ^ 3 : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) : GL (Fin 3) E) :=
      inv_eq_of_mul_eq_one_right htmat2
    show PermutesLines v ((t₁ ^ 3 : gramSU hU (1 : Matrix (Fin 3) (Fin 3) E)) : GL (Fin 3) E)⁻¹
    rw [hinv]
    exact htperm
  obtain ⟨hle, hnormal, hcomm, hexp, hcard, hiso', hperm⟩ := frame_group_structure hU hf hv
  obtain ⟨-, hcyc, hcardc, hinv, hcent⟩ := frame_involution hU hf hv htle ht2 ht1
  exact ⟨v, hv, ⟨hle, hnormal, hcomm, hexp, hcard, hiso', hperm, hcyc, hcardc, hinv, hcent⟩,
    sup_le hCle (Subgroup.zpowers_le.mpr htle), frameMono_eq_normalizer hf hv⟩


theorem BenderType.lemma_3_11_normalizer
    {K : Type*} [Group K] [Finite K] {n e : ℕ}
    (h : BenderType K n 3 e) {C : Subgroup K} (hodd : Odd (Nat.card C)) {t : K}
    (ht2 : t * t = 1) (ht1 : t ≠ 1) (hnorm : ∀ c ∈ C, t * c * t⁻¹ ∈ C)
    (hborel : ∀ Q : Sylow 2 K, ¬ C ≤ borel (Q : Subgroup K)) :
    ∃ F : Subgroup K, Frame311 (2 ^ n) (Nat.gcd 3 (2 ^ n + 1)) F (Subgroup.normalizer (F : Set K))
        t ∧ C ⊔ Subgroup.zpowers t ≤ Subgroup.normalizer (F : Set K) := by
  classical
  obtain ⟨hU, ⟨ψ0⟩⟩ := h.exists_equiv_unitaryModelP
  have hn2 : 2 ≤ n := h.two_le.2
  let ψ : K ≃* primeFormP hU (1 : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * n))) := ψ0
  have hodd' : Odd (Nat.card (C.map ψ.toMonoidHom)) := by
    rwa [Subgroup.card_map_of_injective ψ.injective]
  have hborel' : ∀ Q : Sylow 2
      (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * n)))),
      ¬ C.map ψ.toMonoidHom ≤ Subgroup.normalizer ((Q : Subgroup
        (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * n))))) :
        Set (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * n))))) := by
    intro Q hle
    have hsurj : Function.Surjective ψ.symm.toMonoidHom := ψ.symm.surjective
    apply hborel (Q.mapSurjective (f := ψ.symm.toMonoidHom) hsurj)
    intro c hc
    have h1 : ψ c ∈ borel (Q : Subgroup
        (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * n))))) :=
      hle (Subgroup.mem_map_of_mem _ hc)
    have h2 : c ∈ (borel (Q : Subgroup
        (primeFormP hU (1 : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * n)))))).map
          ψ.symm.toMonoidHom := ⟨ψ c, h1, by simp⟩
    rw [← borel_map] at h2
    rw [Sylow.coe_mapSurjective hsurj Q]
    exact h2
  obtain ⟨v, hv, hF, hle, hN⟩ := frame311_of_unitary hU hn2 hodd' (tb := ψ t)
    (by rw [← map_mul, ht2, map_one]) (fun h1 => ht1 (ψ.injective (by rw [h1, map_one])))
    (by
      intro c hc
      obtain ⟨c₀, hc₀, rfl⟩ := Subgroup.mem_map.mp hc
      exact ⟨t * c₀ * t⁻¹, hnorm c₀ hc₀, by simp⟩)
    hborel'
  have hsup : C ⊔ Subgroup.zpowers t ≤ (frameMono hU v).map ψ.symm.toMonoidHom := by
    apply sup_le
    · intro c hc
      have : ψ c ∈ frameMono hU v :=
        hle (Subgroup.mem_sup_left (Subgroup.mem_map_of_mem _ hc))
      exact ⟨ψ c, this, by simp⟩
    · refine Subgroup.zpowers_le.mpr ?_
      have : ψ t ∈ frameMono hU v :=
        hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
      exact ⟨ψ t, this, by simp⟩
  have hFN : (frameMono hU v).map ψ.symm.toMonoidHom =
      Subgroup.normalizer (((frameTorus hU v).map ψ.symm.toMonoidHom : Subgroup K) : Set K) := by
    rw [hN]
    exact Subgroup.map_equiv_normalizer_eq _ _
  refine ⟨(frameTorus hU v).map ψ.symm.toMonoidHom, ?_, hFN ▸ hsup⟩
  have := hF.map ψ.symm
  rw [MulEquiv.symm_apply_apply, hFN] at this
  exact this

theorem BenderType.lemma_3_11
    {K : Type*} [Group K] [Finite K] {n e : ℕ} (h : BenderType K n 3 e)
    {C : Subgroup K} (hodd : Odd (Nat.card C)) {t : K} (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hnorm : ∀ c ∈ C, t * c * t⁻¹ ∈ C) (hborel : ∀ Q : Sylow 2 K, ¬ C ≤ borel (Q : Subgroup K)) :
    ∃ F F₀ : Subgroup K, Frame311 (2 ^ n) (Nat.gcd 3 (2 ^ n + 1)) F F₀ t ∧
      C ⊔ Subgroup.zpowers t ≤ F₀ := by
  obtain ⟨F, hF, hle⟩ := h.lemma_3_11_normalizer hodd ht2 ht1 hnorm hborel
  exact ⟨F, _, hF, hle⟩

end Glue

end CFSG.GH74.Uniqueness.Bender

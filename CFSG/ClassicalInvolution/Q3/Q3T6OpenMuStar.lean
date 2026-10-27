module

public import CFSG.ClassicalInvolution.Q3.Q3T6OpenMuCtx

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6.Mu

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem ne_and_not_omegaNbr_of_noncomm (hΩ : HypOmegaGen Ω) (hW : W ∈ WSet Ω)
    (hkey : ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ J ∈ Ω, R ≤ J → T ≤ J → T ≤ R ⊔ W ⊔ OCW W)
    {K J R T : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W)
    (hRK : IsSylow2In R K) (hTJ : IsSylow2In T J) {r t : G} (hr : r ∈ R) (ht : t ∈ T)
    (hrW : r ∉ W) (htW : t ∉ W)
    (hnc : piG W r * piG W t ≠ piG W t * piG W r) : K ≠ J ∧ J ∉ omegaNbr Ω K := by
  have hKJ : K ≠ J := by
    intro h
    subst h
    exact hnc (Q3CL.Thompson.piG_comm_of_le hΩ hW hR hT
      (hkey R hR T hT K hK hRK.1 hTJ.1) hr ht hrW htW)
  exact ⟨hKJ, fun hnbr => hnc (Q3CL.Thompson.piG_comm_of_mem_omegaNbr Sec6Gen.l6_2Gen hΩ hW hkey
    hK hJ hKJ hR hT hRK hTJ hnbr hr ht hrW)⟩

theorem piG_comm_third (hΩ : HypOmegaGen Ω) (hW : W ∈ WSet Ω)
    (hkey : ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ J ∈ Ω, R ≤ J → T ≤ J → T ≤ R ⊔ W ⊔ OCW W)
    {K J L R T S : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hL : L ∈ Ω) (hR : R ∈ DSet Ω W)
    (hT : T ∈ DSet Ω W) (hS : S ∈ DSet Ω W) (hRK : IsSylow2In R K) (hTJ : IsSylow2In T J)
    (hSL : IsSylow2In S L) {r t s : G} (hr : r ∈ R) (ht : t ∈ T) (hs : s ∈ S) (hrW : r ∉ W)
    (htW : t ∉ W) (hsW : s ∉ W)
    (hrt : piG W r * piG W t ≠ piG W t * piG W r)
    (hsr : piG W s * piG W r ≠ piG W r * piG W s)
    (hst : piG W s * piG W t ≠ piG W t * piG W s) :
    piG W s * piG W (r * t * r⁻¹) = piG W (r * t * r⁻¹) * piG W s := by
  have hWab := Q3CL.Thompson.commutes_of_mem_WSet hΩ hW
  obtain ⟨hKJ, hnotJK⟩ := ne_and_not_omegaNbr_of_noncomm hΩ hW hkey hK hJ hR hT hRK hTJ
    hr ht hrW htW hrt
  obtain ⟨hLK, hnotKL⟩ := ne_and_not_omegaNbr_of_noncomm hΩ hW hkey hL hK hS hR hSL hRK
    hs hr hsW hrW hsr
  obtain ⟨hLJ, hnotJL⟩ := ne_and_not_omegaNbr_of_noncomm hΩ hW hkey hL hJ hS hT hSL hTJ
    hs ht hsW htW hst
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
  obtain ⟨j, hj⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ
  obtain ⟨ℓ, hℓ⟩ := Sec6Gen.exists_uniqueInvolution hΩ hL
  have hzW : z ∈ K ⊓ W := Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW hK hR hRK hz
  have hjW : j ∈ J ⊓ W := Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW hJ hT hTJ hj
  have hℓW : ℓ ∈ L ⊓ W := Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW hL hS hSL hℓ
  have hrj := Q3CL.Thompson.conj_involution_eq_mul Sec6Gen.l6_2Gen hΩ hW hK hJ hKJ hR hT hRK
    hTJ hnotJK hz hj hr hrW
  have hsz := Q3CL.Thompson.conj_involution_eq_mul Sec6Gen.l6_2Gen hΩ hW hL hK hLK hS hR hSL
    hRK hnotKL hℓ hz hs hsW
  have hsj := Q3CL.Thompson.conj_involution_eq_mul Sec6Gen.l6_2Gen hΩ hW hL hJ hLJ hS hT hSL
    hTJ hnotJL hℓ hj hs hsW
  have hszj : s * (z * j) = (z * j) * s := by
    have h1 : s * (z * j) * s⁻¹ = z * j := by
      calc s * (z * j) * s⁻¹ = (s * z * s⁻¹) * (s * j * s⁻¹) := by group
        _ = (ℓ * z) * (ℓ * j) := by rw [hsz, hsj]
        _ = ℓ * (z * ℓ) * j := by group
        _ = ℓ * (ℓ * z) * j := by rw [hWab z hzW.2 ℓ hℓW.2]
        _ = (ℓ * ℓ) * (z * j) := by group
        _ = z * j := by rw [hℓ.sq, one_mul]
    calc s * (z * j) = (s * (z * j) * s⁻¹) * s := by group
      _ = (z * j) * s := by rw [h1]
  have hzjW : z * j ∈ W := W.mul_mem hzW.2 hjW.2
  have hSc := Q3CL.Thompson.le_centralizer_of_mem hΩ hW hS hs hsW hzjW hszj
  have hrN : r ∈ Subgroup.normalizer (W : Set G) := hR.2 hr
  have hP : conjSub r T ∈ DSet Ω W := Q3CL.Thompson.conjSub_mem_D hΩ hT hrN
  have hKP : conjSub r J ∈ Ω := hΩ.conjInvariant r J hJ
  have hPKP : IsSylow2In (conjSub r T) (conjSub r J) := hTJ.conj r
  have hzP : IsUniqueInvolution (conjSub r J) (z * j) := hrj ▸ hj.conj r
  have hrtP : r * t * r⁻¹ ∈ conjSub r T := conj_mem_conjSub ht
  have hrtW : r * t * r⁻¹ ∉ W := fun h => htW ((mem_normalizer_iff_of_mem hrN t).mp h)
  by_cases hLP : L = conjSub r J
  · subst hLP
    have hle := hkey (conjSub r T) hP S hS (conjSub r J) hKP hPKP.1 hSL.1
    exact (Q3CL.Thompson.piG_comm_of_le hΩ hW hP hS hle hrtP hs hrtW hsW).symm
  · have hSN : S ≤ Subgroup.normalizer ((conjSub r J : Subgroup G) : Set G) :=
      Sec6Gen.le_normalizer_of_le_centralizer hΩ hKP hL (Ne.symm hLP) hzP hSL.1 hSL.2.1
        (by have := Sec6Gen.eight_le_of_mem_RSet hΩ hS.1; omega) hSc
    have hnbr : L ∈ omegaNbr Ω (conjSub r J) := ⟨hL, hLP, S, hS.1, hSL.1, hSN⟩
    exact (Q3CL.Thompson.piG_comm_of_mem_omegaNbr Sec6Gen.l6_2Gen hΩ hW hkey hKP hL
      (Ne.symm hLP) hP hS hPKP hSL hnbr hrtP hs hrtW).symm

theorem isStar_muDelta (c : Q3CL.Thompson.Ctx Ω W) : Star3T.IsStar (muDelta Ω W) := by
  rintro a ha b hb hab d hd
  have haa := muDelta_mul_self c.hΩ c.hW ha
  obtain ⟨R, hR, r, hr, hrW, hra⟩ := ha
  obtain ⟨T, hT, t, ht, htW, htb⟩ := hb
  obtain ⟨S, hS, s, hs, hsW, hsd⟩ := hd
  obtain ⟨K, hK, hRK⟩ := exists_isSylow2In_of_mem_RSet hR.1
  obtain ⟨J, hJ, hTJ⟩ := exists_isSylow2In_of_mem_RSet hT.1
  obtain ⟨L, hL, hSL⟩ := exists_isSylow2In_of_mem_RSet hS.1
  have hrN := hR.2 hr
  have htN := hT.2 ht
  have hnc : piG W r * piG W t ≠ piG W t * piG W r := fun h => hab (by
    apply Subtype.ext
    show (a : NQuot (W ⊔ OCW W)) * b = b * a
    rw [hra, htb]
    exact h)
  by_cases h1 : piG W s * piG W r = piG W r * piG W s
  · left
    apply Subtype.ext
    show (d : NQuot (W ⊔ OCW W)) * a = a * d
    rw [hra, hsd]
    exact h1
  by_cases h2 : piG W s * piG W t = piG W t * piG W s
  · right
    left
    apply Subtype.ext
    show (d : NQuot (W ⊔ OCW W)) * b = b * d
    rw [htb, hsd]
    exact h2
  right
  right
  apply Subtype.ext
  have hinv : (piG W r)⁻¹ = piG W r := by
    have : (a : NQuot (W ⊔ OCW W)) * a = 1 := congrArg Subtype.val haa
    rw [hra] at this
    exact inv_eq_of_mul_eq_one_left this
  have e : (a : NQuot (W ⊔ OCW W)) * b * a = piG W (r * t * r⁻¹) := by
    rw [hra, htb, piG_mul (Subgroup.mul_mem _ hrN htN) (Subgroup.inv_mem _ hrN),
      piG_mul hrN htN, piG_inv hrN, hinv]
  show (d : NQuot (W ⊔ OCW W)) * ((a : NQuot (W ⊔ OCW W)) * b * a) =
    ((a : NQuot (W ⊔ OCW W)) * b * a) * d
  rw [e, hsd]
  exact piG_comm_third c.hΩ c.hW c.hkey hK hJ hL hR hT hS hRK hTJ hSL hr ht hs hrW htW hsW
    hnc h1 h2

theorem isTT_muDelta (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω) :
    Star3T.IsTT (muDelta Ω W) where
  mul_self _ ha := muDelta_mul_self hP.hyp hW ha
  ne_one _ ha := muDelta_ne_one hW ha
  conj_mem _ ha g := muDelta_conj_mem hP.hyp ha g
  closure_eq_top := closure_muDelta_eq_top Ω W
  comm_or_cube := muDelta_comm_or_cube (Q3CL.thompsonCube hP W hW)

end CFSG.ClassicalInvolution.Q3.Q3T6.Mu

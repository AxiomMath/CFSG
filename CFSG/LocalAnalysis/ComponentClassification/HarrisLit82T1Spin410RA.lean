module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RF
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410b

public section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup QuadraticMap CliffordAlgebra CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.ModelFacts
open CFSG.GH74.GLS.Bg.Thompson (IsSylowIn)
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem transport_La_apply (A : SL(2, K)) (Y : Matrix (Fin 2) (Fin 2) K) :
    (frame01 K).transport ((frame01 K).La A) Y = (A : Matrix (Fin 2) (Fin 2) K) * Y := by
  rw [Frame.transport_apply, Frame.La_apply_incl, Frame.coords_incl]

theorem transport_swap_La_apply (A : SL(2, K)) (Y : Matrix (Fin 2) (Fin 2) K) :
    (frame01 K).transport ((frame01 K).swap.La A) Y =
      Y * ((Frame.sigmaSL A : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) := by
  rw [Frame.transport_apply, Frame.swap_La_eq_embGrp, Frame.embGrp_apply, Frame.embLin_apply]
  simp only [map_add, map_sub, Frame.coords_incl, LinearEquiv.coe_coe, rmulEquiv_apply]
  abel

theorem spinNormC_eq_one_of_transportHom_eq_one [Finite K] [Invertible (2 : K)]
    {c : centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))}
    (hW : transportHom (isUnit_of_invertible (2 : K)).ne_zero (spinCent K c) = 1) :
    spinNormC K c = 1 := by
  have h2 : (2 : K) ≠ 0 := (isUnit_of_invertible (2 : K)).ne_zero
  have hΦ := detSpinorNorm_perpEmbO (perpHom h2 (spinCent K c))
  have hΩ : detSpinorNorm (nondegenerate_quadOdd 3 K) (perpEmbO (perpHom h2 (spinCent K c))) =
      1 := by
    apply detSpinorNorm_eq_one_of_mem_elementaryGroup
    rw [coe_perpEmbO, ← spinAction_eq_perpEmb h2 hW, ← range_spinAction_quadOdd h2 (le_refl 3)]
    exact ⟨c, rfl⟩
  rw [hΩ] at hΦ
  have h := congrArg Prod.snd hΦ
  rw [detSpinorNorm_apply, Prod.snd_one] at h
  exact h.symm

section Model

variable [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
  (h5 : 5 ≤ p ^ f)
include hp hp2 hK h5

theorem mem_spinE_of_commute_sylow {y : spinGroup (quadOdd 3 K)}
    (hyC : y ∈ centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))))
    {Q₂ : Subgroup (spinGroup (quadOdd 3 K))} (hQ₂ : IsSylowIn 2 Q₂ (spinJ₂ K))
    (hy : ∀ x ∈ Q₂, y * x = x * y) : y ∈ spinE K := by
  have h2 := two_ne_zero_spin hp hp2 hK
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have := finite_spinSeven h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  set C : Subgroup (spinGroup (quadOdd 3 K)) :=
    centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) with hC
  set c : C := ⟨y, hyC⟩ with hcdef
  set g := spinAction (quadOdd 3 K) y with hg
  have hgc : g * (frame01 K).La (-1) = (frame01 K).La (-1) * g :=
    comm_of_mem_isoCentLa (spinCent K c).2
  set A := transportHom h2 (spinCent K c) with hA
  have hAapp : ∀ X, A.1 X = (frame01 K).transport g X :=
    fun X => rfl
  have hdet : LinearEquiv.det A.1 = 1 := by
    have := det_transportHom_spinCent hp hp2 hK h5 c
    rwa [QuadraticMap.orthogonalDet_apply] at this
  have hSO : A.1 ∈
      TauCeti.QuadraticMap.specialOrthogonalGroup (detQ (K := K)) :=
    TauCeti.QuadraticMap.mem_specialOrthogonalGroup_iff.mpr ⟨A.2, hdet⟩
  obtain ⟨a, b, hab⟩ := specialOrthogonalGroup_le_bimulGrp h2 hSO
  obtain ⟨-, hb⟩ := isUnit_det_of_bimul hab
  set ρ₂ := (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true true with hρ₂
  have hp' : IsPGroup 2 (Q₂.comap ρ₂) :=
    hQ₂.2.1.comap_of_injective ρ₂ (longSL2_injective _ fin3_zero_ne_one true true)
  have hi : ¬ 2 ∣ (Q₂.comap ρ₂).index := by rw [index_comap]; exact hQ₂.2.2
  set P : Sylow 2 SL(2, K) := hp'.toSylow hi with hP
  have hcomm : ∀ M ∈ (P : Subgroup SL(2, K)),
      a * (M : Matrix (Fin 2) (Fin 2) K) = M * a := by
    intro M hM
    have h1 : y * ρ₂ M = ρ₂ M * y := hy (ρ₂ M) hM
    have h1' : g * (frame01 K).La M = (frame01 K).La M * g := by
      have h := congrArg (spinAction (quadOdd 3 K)) h1
      rw [map_mul, map_mul, spinAction_longSL2] at h
      exact h
    have hLa : (frame01 K).La M * (frame01 K).La (-1) = (frame01 K).La (-1) * (frame01 K).La M := by
      rw [← map_mul, ← map_mul, mul_neg_one, neg_one_mul]
    have h3 : ∀ X, A.1 ((M : Matrix (Fin 2) (Fin 2) K) * X) =
        (M : Matrix (Fin 2) (Fin 2) K) * A.1 X := by
      intro X
      have h : (frame01 K).transport (g * (frame01 K).La M) X =
          (frame01 K).transport ((frame01 K).La M * g) X := by
        rw [h1']
      rw [Frame.transport_mul h2 hLa, Frame.transport_mul h2 hgc, Module.End.mul_apply,
        Module.End.mul_apply, transport_La_apply, transport_La_apply] at h
      rw [hAapp, hAapp]
      exact h
    have h4 := h3 (b⁻¹)
    rw [hab, hab] at h4
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hb, Matrix.mul_one] at h4
    exact h4
  obtain ⟨α, hα⟩ := eq_smul_one_of_commute_sylow_sl2 hodd P hcomm
  set b' := α • b with hb'
  have hAX : ∀ X, A.1 X = X * b' := fun X => by
    rw [hab, hα, hb', Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul]
  have hdetb' : b'.det = 1 := by
    have h := CFSG.ClassicalGroups.Orthogonal.map_of_mem A.2 (1 : Matrix (Fin 2) (Fin 2) K)
    rw [hAX, Matrix.one_mul, detQ_apply, detQ_apply, Matrix.det_one] at h
    exact h
  set B : SL(2, K) := Frame.sigmaSL ⟨b', hdetb'⟩ with hB
  set y₃ := (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false B with hy₃def
  have hy₃ : y₃ ∈ spinJ₃ K := ⟨B, rfl⟩
  have hy₃C : y₃ ∈ C := (spinJ_le_centralizer (K := K) hp hp2 hK).2.2 hy₃
  have hA₃ : transportHom h2 (spinCent K ⟨y₃, hy₃C⟩) = A := by
    apply Subtype.ext
    refine LinearEquiv.ext fun X => ?_
    rw [hAX]
    show (frame01 K).transport (spinAction (quadOdd 3 K) y₃) X = X * b'
    rw [hy₃def, spinAction_longSL2,
      show (oddFrame 3 K).toHypFrame.toFrame fin3_zero_ne_one true false = (frame01 K).swap from
        toFrame_not _ fin3_zero_ne_one true true, transport_swap_La_apply, hB,
      Frame.sigmaSL_sigmaSL (⟨b', hdetb'⟩ : SL(2, K))]
  have hW : transportHom (isUnit_of_invertible (2 : K)).ne_zero
      (spinCent K (c * (⟨y₃, hy₃C⟩ : C)⁻¹)) = 1 := by
    rw [map_mul, map_inv, map_mul, map_inv, hA₃, ← hA, mul_inv_cancel]
  have hc' : c * (⟨y₃, hy₃C⟩ : C)⁻¹ ∈ (spinNormC K).ker :=
    MonoidHom.mem_ker.mpr (spinNormC_eq_one_of_transportHom_eq_one hW)
  rw [ker_spinNormC hp hp2 hK h5] at hc'
  have e : y = ((c * (⟨y₃, hy₃C⟩ : C)⁻¹ : C) : spinGroup (quadOdd 3 K)) * y₃ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
  rw [e]
  exact mul_mem (Subgroup.mem_subgroupOf.mp hc') (mem_sup_right hy₃)

theorem mem_center_sylow_centralizer {T₀ : Subgroup (spinGroup (quadOdd 3 K))}
    (hT : IsSylowIn 2 T₀ (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))))
    {y : spinGroup (quadOdd 3 K)} (hy : y ∈ T₀) (hyc : ∀ x ∈ T₀, y * x = x * y) :
    y = 1 ∨ y = spinZ K ∨ y = tSeven K ∨ y = spinZ K * tSeven K := by
  have h2 := two_ne_zero_spin hp hp2 hK
  have := finite_spinSeven h2
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have h4 := four_le_card_spin hK h5
  have hQ : quadOdd 3 K ≠ 0 := (nondegenerate_quadOdd 3 K).ne_zero
  obtain ⟨hzz, -, hzc, htt, -, -, -, -, -, h3eq⟩ := spinZ_facts hp hp2 hK
  have hzcomm : ∀ g : spinGroup (quadOdd 3 K), spinZ K * g = g * spinZ K := fun g =>
    (mem_center_iff.mp hzc g).symm
  obtain ⟨l1, l2, l3⟩ := spinJ_le_centralizer (K := K) hp hp2 hK
  obtain ⟨n1, n2, n3⟩ := normal_spinJ (K := K) hp hp2 hK h5
  have hQ1 := isSylowIn_inf_of_normal hT l1 n1
  have hQ2 := isSylowIn_inf_of_normal hT l2 n2
  have hQ3 := isSylowIn_inf_of_normal hT l3 n3
  have hyE := mem_spinE_of_commute_sylow hp hp2 hK h5 (hT.1 hy) hQ2 fun x hx => hyc x hx.1
  rw [← range_spinMul h4] at hyE
  obtain ⟨⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, ⟨c, hc⟩⟩, rfl⟩ := hyE
  rw [spinMul_apply] at hyc ⊢
  change ∀ x ∈ T₀, a * b * c * x = x * (a * b * c) at hyc
  change a * b * c = 1 ∨ a * b * c = spinZ K ∨ a * b * c = tSeven K ∨
    a * b * c = spinZ K * tSeven K
  obtain ⟨-, g1⟩ := sylow_range_sl2_facts hodd (shortSeven K) injective_shortSeven hQ1
  obtain ⟨-, g2⟩ := sylow_range_sl2_facts hodd _
    (longSL2_injective _ fin3_zero_ne_one true true) hQ2
  obtain ⟨-, g3⟩ := sylow_range_sl2_facts hodd _
    (longSL2_injective _ fin3_zero_ne_one true false) hQ3
  rw [shortSeven_neg_one hQ] at g1
  rw [h3eq] at g3
  have ha' : a = 1 ∨ a = spinZ K := g1 a ha fun x hx => comm_left_of_comm
    (commute_spinJ₁_spinJ₂ hx.2 hb).symm (commute_spinJ₁_spinJ₃ hx.2 hc).symm (hyc x hx.1)
  have hb' : b = 1 ∨ b = tSeven K := g2 b hb fun x hx => comm_mid_of_comm
    (commute_spinJ₁_spinJ₂ ha hx.2) (commute_spinJ₂_spinJ₃ h4 hx.2 hc).symm (hyc x hx.1)
  have hc' : c = 1 ∨ c = spinZ K * tSeven K := g3 c hc fun x hx => comm_right_of_comm
    (commute_spinJ₁_spinJ₃ ha hx.2) (commute_spinJ₂_spinJ₃ h4 hb hx.2) (hyc x hx.1)
  have htzt : tSeven K * (spinZ K * tSeven K) = spinZ K := by
    rw [← mul_assoc, ← hzcomm, mul_assoc, htt, mul_one]
  have hzzt : spinZ K * (spinZ K * tSeven K) = tSeven K := by
    rw [← mul_assoc, hzz, one_mul]
  have hztzt : spinZ K * tSeven K * (spinZ K * tSeven K) = 1 := by
    rw [mul_assoc, htzt, hzz]
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl <;> rcases hc' with rfl | rfl
  · left; simp
  · right; right; right; simp
  · right; right; left; simp
  · right; left; rw [one_mul, htzt]
  · right; left; simp
  · right; right; left; rw [mul_one, hzzt]
  · right; right; right; rw [mul_one]
  · left; exact hztzt

omit h5 in
theorem conj_pow_tSeven_of_odd {n : spinGroup (quadOdd 3 K)}
    (hn : n * tSeven K * n⁻¹ = spinZ K * tSeven K) {k : ℕ} (hk : Odd k) :
    n ^ k * tSeven K * (n ^ k)⁻¹ = spinZ K * tSeven K := by
  obtain ⟨hzz, -, hzc, -, -, -, -, -, -, -⟩ := spinZ_facts hp hp2 hK
  have hz : ∀ g : spinGroup (quadOdd 3 K), g * spinZ K = spinZ K * g := mem_center_iff.mp hzc
  have hn' : n * tSeven K = spinZ K * tSeven K * n := by
    rw [← hn, inv_mul_cancel_right]
  have h2 : Commute (n ^ 2) (tSeven K) := by
    show n ^ 2 * tSeven K = tSeven K * n ^ 2
    calc n ^ 2 * tSeven K = n * (n * tSeven K) := by rw [pow_two, mul_assoc]
      _ = n * (spinZ K * tSeven K * n) := by rw [hn']
      _ = n * spinZ K * tSeven K * n := by simp only [mul_assoc]
      _ = spinZ K * (n * tSeven K) * n := by rw [hz n]; simp only [mul_assoc]
      _ = spinZ K * (spinZ K * tSeven K * n) * n := by rw [hn']
      _ = spinZ K * spinZ K * tSeven K * (n * n) := by simp only [mul_assoc]
      _ = tSeven K * n ^ 2 := by rw [hzz, one_mul, pow_two]
  obtain ⟨j, rfl⟩ := hk
  have hc : (n ^ 2) ^ j * tSeven K = tSeven K * (n ^ 2) ^ j := (h2.pow_left j).eq
  rw [pow_succ, pow_mul]
  calc (n ^ 2) ^ j * n * tSeven K * ((n ^ 2) ^ j * n)⁻¹ =
      (n ^ 2) ^ j * (n * tSeven K * n⁻¹) * ((n ^ 2) ^ j)⁻¹ := by group
    _ = (n ^ 2) ^ j * (spinZ K * tSeven K) * ((n ^ 2) ^ j)⁻¹ := by rw [hn]
    _ = spinZ K * ((n ^ 2) ^ j * tSeven K) * ((n ^ 2) ^ j)⁻¹ := by
      rw [← mul_assoc, hz]
      simp only [mul_assoc]
    _ = spinZ K * tSeven K := by rw [hc, mul_assoc, mul_inv_cancel_right]

theorem not_le_centralizer_tSeven {S : Subgroup (spinGroup (quadOdd 3 K))}
    (hS : IsSylowIn 2 S ⊤) : ¬ S ≤ centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) := by
  intro hSC
  have h2 := two_ne_zero_spin hp hp2 hK
  have := finite_spinSeven h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have h4 := four_le_card_spin hK h5
  obtain ⟨hzz, hz1, hzc, htt, ht1, htc, -, -, -, -⟩ := spinZ_facts hp hp2 hK
  have hzcomm : ∀ g : spinGroup (quadOdd 3 K), spinZ K * g = g * spinZ K := fun g =>
    (mem_center_iff.mp hzc g).symm
  have hztzt : spinZ K * tSeven K * (spinZ K * tSeven K) = 1 := by
    rw [mul_assoc, ← mul_assoc (tSeven K), ← hzcomm, mul_assoc, htt, mul_one, hzz]
  set C : Subgroup (spinGroup (quadOdd 3 K)) :=
    centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) with hC
  have hCzt : centralizer ({spinZ K * tSeven K} : Set (spinGroup (quadOdd 3 K))) = C :=
    centralizer_mul_of_mem_center hzc
  have hzt1 : spinZ K * tSeven K ≠ 1 := fun h => htc (by
    rw [(eq_inv_of_mul_eq_one_right h).trans (inv_eq_of_mul_eq_one_right hzz)]; exact hzc)
  have hzt2 : orderOf (spinZ K * tSeven K) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hztzt) hzt1
  have hztZ : spinZ K * tSeven K ∉ center (spinGroup (quadOdd 3 K)) := fun h => htc (by
    have := mul_mem (inv_mem hzc) h
    rwa [inv_mul_cancel_left] at this)
  obtain ⟨w, hw⟩ := spinSeven_lemma410b hodd h4 hzt2 hztZ
  have hSi : ¬ 2 ∣ S.index := by rw [← relIndex_top_right]; exact hS.2.2
  set Ssyl : Sylow 2 (spinGroup (quadOdd 3 K)) := hS.2.1.toSylow hSi with hSsyl
  have hwSC : S.map (MulAut.conj w).toMonoidHom ≤ C := by
    rintro _ ⟨s, hs, rfl⟩
    rw [← hCzt, ← hw, mem_centralizer_singleton_iff]
    have hst : s * tSeven K = tSeven K * s := mem_centralizer_singleton_iff.mp (hSC hs)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show w * s * w⁻¹ * (w * tSeven K * w⁻¹) = w * (s * tSeven K) * w⁻¹ by group, hst]
    group
  have hp1 : IsPGroup 2 (S.subgroupOf C) := hS.2.1.comap_of_injective _ C.subtype_injective
  have hi1 : ¬ 2 ∣ (S.subgroupOf C).index := fun hd =>
    hSi (hd.trans (relIndex_dvd_index_of_le hSC))
  have hp2' : IsPGroup 2 ((S.map (MulAut.conj w).toMonoidHom).subgroupOf C) :=
    (hS.2.1.map _).comap_of_injective _ C.subtype_injective
  have hi2 : ¬ 2 ∣ ((S.map (MulAut.conj w).toMonoidHom).subgroupOf C).index := by
    intro hd
    apply hSi
    have h' := hd.trans (relIndex_dvd_index_of_le hwSC)
    rwa [index_map_of_bijective (f := (MulAut.conj w).toMonoidHom)
      (MulAut.conj w).bijective] at h'
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C (hp1.toSylow hi1) (hp2'.toSylow hi2)
  have hcS : ∀ s ∈ S, (c : spinGroup (quadOdd 3 K)) * s * (c : spinGroup (quadOdd 3 K))⁻¹ ∈
      S.map (MulAut.conj w).toMonoidHom := by
    intro s hs
    have h1 : c * ⟨s, hSC hs⟩ * c⁻¹ ∈ ((hp2'.toSylow hi2 : Sylow 2 C) : Subgroup C) := by
      rw [← hc, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul (⟨s, hSC hs⟩ : C) (MulAut.conj c) _ hs
    exact h1
  set m := w⁻¹ * (c : spinGroup (quadOdd 3 K)) with hm
  have hmS : ((m • Ssyl : Sylow 2 (spinGroup (quadOdd 3 K))) :
      Subgroup (spinGroup (quadOdd 3 K))) ≤ (Ssyl : Subgroup (spinGroup (quadOdd 3 K))) := by
    intro x hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨s', hs', hss'⟩ := hcS s hs
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hss'
    show m * s * m⁻¹ ∈ S
    have e1 : m * s * m⁻¹ = w⁻¹ * ((c : spinGroup (quadOdd 3 K)) * s *
        (c : spinGroup (quadOdd 3 K))⁻¹) * w := by
      rw [hm]
      group
    rw [e1, ← hss', show w⁻¹ * (w * s' * w⁻¹) * w = s' by group]
    exact hs'
  have hmN : m ∈ normalizer ((Ssyl : Subgroup (spinGroup (quadOdd 3 K))) :
      Set (spinGroup (quadOdd 3 K))) :=
    Sylow.smul_eq_iff_mem_normalizer.mp
      (Sylow.ext ((m • Ssyl).is_maximal' Ssyl.isPGroup' hmS).symm)
  set n := m⁻¹ with hn
  have hnN : n ∈ normalizer ((Ssyl : Subgroup (spinGroup (quadOdd 3 K))) :
      Set (spinGroup (quadOdd 3 K))) := inv_mem hmN
  have hnt : n * tSeven K * n⁻¹ = spinZ K * tSeven K := by
    have hct : (c : spinGroup (quadOdd 3 K)) * tSeven K = tSeven K * c :=
      mem_centralizer_singleton_iff.mp c.2
    have e : n = (c : spinGroup (quadOdd 3 K))⁻¹ * w := by rw [hn, hm, mul_inv_rev, inv_inv]
    rw [e]
    calc (c : spinGroup (quadOdd 3 K))⁻¹ * w * tSeven K * ((c : spinGroup (quadOdd 3 K))⁻¹ * w)⁻¹
        = (c : spinGroup (quadOdd 3 K))⁻¹ * (w * tSeven K * w⁻¹) * c := by group
      _ = (c : spinGroup (quadOdd 3 K))⁻¹ * (spinZ K * tSeven K) * c := by rw [hw]
      _ = spinZ K * ((c : spinGroup (quadOdd 3 K))⁻¹ * (tSeven K * c)) := by
        rw [← mul_assoc, ← hzcomm]
        group
      _ = spinZ K * tSeven K := by rw [← hct]; group
  obtain ⟨a, k, hk, hnk⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n).ne'
  have hk0 : k ≠ 0 := fun h => by rw [h] at hk; exact (Nat.not_even_iff_odd.mpr hk) Even.zero
  have hord : orderOf (n ^ k) = 2 ^ a := by
    rw [orderOf_pow' n hk0, hnk, Nat.gcd_mul_left_left,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hk0)]
  have hzp : IsPGroup 2 (zpowers (n ^ k)) :=
    IsPGroup.of_card (n := a) (by rw [Nat.card_zpowers, hord])
  have hsup : IsPGroup 2 ↥(S ⊔ zpowers (n ^ k)) :=
    hS.2.1.to_sup_of_normal_left' hzp (zpowers_le.mpr (pow_mem hnN k))
  have heq := Ssyl.is_maximal' hsup le_sup_left
  have hnkS : n ^ k ∈ S := by
    have h := (le_sup_right : zpowers (n ^ k) ≤ S ⊔ zpowers (n ^ k)) (mem_zpowers _)
    rw [heq] at h
    exact h
  have h1 : n ^ k * tSeven K * (n ^ k)⁻¹ = tSeven K := by
    rw [mem_centralizer_singleton_iff.mp (hSC hnkS), mul_inv_cancel_right]
  rw [conj_pow_tSeven_of_odd hp hp2 hK hnt hk] at h1
  exact hz1 (mul_right_cancel (h1.trans (one_mul _).symm))

theorem spinSeven_lemma410a {S₀ : Subgroup (spinGroup (quadOdd 3 K))} (hS₀ : IsSylowIn 2 S₀ ⊤)
    {x : spinGroup (quadOdd 3 K)} (hx : x ∈ S₀) (hxc : ∀ y ∈ S₀, x * y = y * x) :
    x = 1 ∨ x = spinZ K := by
  have h2 := two_ne_zero_spin hp hp2 hK
  have := finite_spinSeven h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hzz, -, hzc, htt, -, -, -, -, -, -⟩ := spinZ_facts hp hp2 hK
  set C : Subgroup (spinGroup (quadOdd 3 K)) :=
    centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) with hC
  have hCzt : centralizer ({spinZ K * tSeven K} : Set (spinGroup (quadOdd 3 K))) = C :=
    centralizer_mul_of_mem_center hzc
  obtain ⟨T₁⟩ := (inferInstance : Nonempty (Sylow 2 C))
  set T₀ := (T₁ : Subgroup C).map C.subtype with hT₀
  have hT₀C : T₀ ≤ C := map_subtype_le _
  have hT₀sub : T₀.subgroupOf C = T₁ := comap_map_eq_self_of_injective C.subtype_injective _
  have hT : IsSylowIn 2 T₀ C := ⟨hT₀C, T₁.isPGroup'.map _, by
    show ¬ 2 ∣ (T₀.subgroupOf C).index
    rw [hT₀sub]
    exact Sylow.not_dvd_index T₁⟩
  obtain ⟨S', hTS'⟩ := hT.2.1.exists_le_sylow
  have hS₀i : ¬ 2 ∣ S₀.index := by rw [← relIndex_top_right]; exact hS₀.2.2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (spinGroup (quadOdd 3 K)) S'
    (hS₀.2.1.toSylow hS₀i)
  have hS₀eq : S₀ = ((g • S' : Sylow 2 (spinGroup (quadOdd 3 K))) : Subgroup _) := by
    rw [hg]
    rfl
  have hconj : ∀ y ∈ (S' : Subgroup (spinGroup (quadOdd 3 K))), g * y * g⁻¹ ∈ S₀ := by
    intro y hy
    rw [hS₀eq, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g) _ hy
  set x' := g⁻¹ * x * g with hx'
  have hx'S' : x' ∈ (S' : Subgroup (spinGroup (quadOdd 3 K))) := by
    have h := hx
    rw [hS₀eq, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h
    obtain ⟨s, hs, hsx⟩ := h
    simp only [MulAut.smul_def, MulAut.conj_apply] at hsx
    rw [hx', ← hsx, show g⁻¹ * (g * s * g⁻¹) * g = s by group]
    exact hs
  have hx'c : ∀ y ∈ (S' : Subgroup (spinGroup (quadOdd 3 K))), x' * y = y * x' := by
    intro y hy
    have h := hxc _ (hconj y hy)
    calc x' * y = g⁻¹ * (x * (g * y * g⁻¹)) * g := by rw [hx']; group
      _ = g⁻¹ * (g * y * g⁻¹ * x) * g := by rw [h]
      _ = y * x' := by rw [hx']; group
  have htT₀ : tSeven K ∈ T₀ := by
    have htC : tSeven K ∈ C := mem_centralizer_singleton_iff.mpr rfl
    have hcen : (⟨tSeven K, htC⟩ : C) ∈ center C := by
      rw [mem_center_iff]
      intro c
      exact Subtype.ext (mem_centralizer_singleton_iff.mp c.2)
    have hN : (zpowers (⟨tSeven K, htC⟩ : C)).Normal := by
      refine ⟨fun n hn c => ?_⟩
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
      rw [show c * (⟨tSeven K, htC⟩ : C) ^ k * c⁻¹ = (⟨tSeven K, htC⟩ : C) ^ k by
        rw [mem_center_iff.mp (zpow_mem hcen k) c, mul_inv_cancel_right]]
      exact zpow_mem (mem_zpowers _) k
    have hp2' : IsPGroup 2 (zpowers (⟨tSeven K, htC⟩ : C)) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext htt) (fun h => by
        obtain ⟨-, -, -, -, ht1, -⟩ := spinZ_facts hp hp2 hK
        exact ht1 (congrArg Subtype.val h))
    have h := hp2'.le_sylow_of_normal T₁ (mem_zpowers _)
    exact ⟨_, h, rfl⟩
  have hx'C : x' ∈ C := mem_centralizer_singleton_iff.mpr (hx'c _ (hTS' htT₀))
  have hx'T₀ : x' ∈ T₀ := by
    have hU : IsPGroup 2 ↥(T₀ ⊔ zpowers x') :=
      S'.isPGroup'.to_le (sup_le hTS' (zpowers_le.mpr hx'S'))
    have hUC : T₀ ⊔ zpowers x' ≤ C := sup_le hT₀C (zpowers_le.mpr hx'C)
    have hU' : IsPGroup 2 ((T₀ ⊔ zpowers x').subgroupOf C) :=
      hU.comap_of_injective _ C.subtype_injective
    have hle : (T₁ : Subgroup C) ≤ (T₀ ⊔ zpowers x').subgroupOf C := fun c hc =>
      mem_sup_left (⟨c, hc, rfl⟩ : (c : spinGroup (quadOdd 3 K)) ∈ T₀)
    have heq := T₁.is_maximal' hU' hle
    have hmem : (⟨x', hx'C⟩ : C) ∈ (T₀ ⊔ zpowers x').subgroupOf C :=
      mem_sup_right (mem_zpowers x')
    rw [heq] at hmem
    exact ⟨_, hmem, rfl⟩
  have hS'syl : IsSylowIn 2 (S' : Subgroup (spinGroup (quadOdd 3 K))) ⊤ :=
    ⟨le_top, S'.isPGroup', by rw [relIndex_top_right]; exact Sylow.not_dvd_index S'⟩
  have hxx' : x = g * x' * g⁻¹ := by rw [hx']; group
  rcases mem_center_sylow_centralizer hp hp2 hK h5 hT hx'T₀
    (fun y hy => hx'c y (hTS' hy)) with h | h | h | h
  · left
    rw [hxx', h, mul_one, mul_inv_cancel]
  · right
    rw [hxx', h, mem_center_iff.mp hzc g, mul_inv_cancel_right]
  · exfalso
    refine not_le_centralizer_tSeven hp hp2 hK h5 hS'syl fun y hy => ?_
    rw [mem_centralizer_singleton_iff, ← h]
    exact (hx'c y hy).symm
  · exfalso
    refine not_le_centralizer_tSeven hp hp2 hK h5 hS'syl fun y hy => ?_
    rw [← centralizer_mul_of_mem_center (t := tSeven K) hzc, mem_centralizer_singleton_iff, ← h]
    exact (hx'c y hy).symm

end Model

end CFSG.ComponentClassification.HarrisLit.T1

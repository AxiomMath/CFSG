module

public import CFSG.ClassicalInvolution.Q3.TL4MF164Ex
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.MF164

open CFSG CFSG.GorensteinWalter Matrix QuaternionGroup
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K]

theorem false_of_four_dvd {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hcard : Nat.card K = p ^ f) (h4f : 4 ∣ f) {P Q S : Subgroup (PGammaL2 K)} (hQP : Q ≤ P)
    (hQn : ∀ x ∈ P, ∀ y ∈ Q, x * y * x⁻¹ ∈ Q)
    (hPc : ∀ x ∈ P, x * SemidirectProduct.inl (pGammaL2FullSplitTorus K (-1)) =
      SemidirectProduct.inl (pGammaL2FullSplitTorus K (-1)) * x)
    (hnP : SemidirectProduct.inl (weylPGL K) ∈ P) (hexp : ∀ y ∈ Q, y ^ 8 = 1 → y ^ 4 = 1)
    (hSQ : S ≤ Q) (eS : S ≃* QuaternionGroup 2)
    (hs₀ : SemidirectProduct.inl (pGammaL2FullSplitTorus K (-1)) ∈ S) : False := by
  classical
  have hK : IsOddPrimePower (Nat.card K) := ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hcard⟩
  set z8 : S := ⟨_, hs₀⟩ with hz8def
  obtain ⟨hz8, hsqS⟩ := q8_sq_mem hK eS hs₀
  have hright : ∀ x : S, (x : PGammaL2 K).right ^ 2 = 1 := fun x => by
    have hr : ((x ^ 2 : S) : PGammaL2 K).right = (x : PGammaL2 K).right ^ 2 := by
      rw [Subgroup.coe_pow, ← SemidirectProduct.rightHom_eq_right, map_pow]
    rw [← hr]
    rcases hsqS x with h | h <;> rw [h] <;> rfl
  have hy : ∃ y : S, (y : PGammaL2 K).right ≠ 1 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    have hU : ∀ x : S, ∃ c : Kˣ,
        (x : PGammaL2 K) = SemidirectProduct.inl (pGammaL2FullSplitTorus K c) := by
      intro x
      have hx : (x : PGammaL2 K) = SemidirectProduct.inl (x : PGammaL2 K).left :=
        SemidirectProduct.ext rfl (by rw [hall x, SemidirectProduct.right_inl])
      have hc := left_commute_s0 (hPc _ (hQP (hSQ x.2)))
      by_cases hmem : (x : PGammaL2 K).left ∈ (pGammaL2FullSplitTorus K).range
      · obtain ⟨c, hc'⟩ := hmem
        exact ⟨c, hx.trans (by rw [hc'])⟩
      · exfalso
        have h2 : x ^ 2 = 1 := Subtype.ext (by
          rw [Subgroup.coe_pow, hx, ← map_pow, sq, sq_eq_one_of_not_mem_torus hK hc hmem,
            map_one, Subgroup.coe_one])
        rcases q8_inv_eq (eS x) (by rw [← map_pow, h2, map_one]) with h | h
        · have : x = 1 := eS.injective (by rw [h, map_one])
          apply hmem
          rw [this]
          exact ⟨1, by simp⟩
        · have : x = z8 := eS.injective (by rw [h, hz8])
          apply hmem
          rw [this]
          exact ⟨-1, rfl⟩
    obtain ⟨u, v, huv⟩ := q8_nonabelian
    apply huv
    obtain ⟨c₁, h₁⟩ := hU (eS.symm u)
    obtain ⟨c₂, h₂⟩ := hU (eS.symm v)
    have hc : eS.symm u * eS.symm v = eS.symm v * eS.symm u := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, h₁, h₂, ← map_mul, ← map_mul, ← map_mul,
        ← map_mul, mul_comm c₁])
    simpa using congrArg eS hc
  obtain ⟨y, hy⟩ := hy
  obtain ⟨-, hφ⟩ := even_and_eq_pow_of_involution_prime hp hf hcard hy
    (by rw [← sq]; exact hright y)
  set q := p ^ (f / 2) with hq
  have huniq : ∀ x : S, (x : PGammaL2 K).right ≠ 1 →
      (x : PGammaL2 K).right = (y : PGammaL2 K).right := by
    intro x hx
    obtain ⟨-, hx'⟩ := even_and_eq_pow_of_involution_prime hp hf hcard hx
      (by rw [← sq]; exact hright x)
    exact RingEquiv.ext fun t => by rw [hx', hφ]
  have hq8 : q % 8 = 1 := pow_half_mod_eight (hp.odd_of_ne_two hp2) h4f
  have hφT : ∀ c : Kˣ, pgl2FieldAut K (y : PGammaL2 K).right (pGammaL2FullSplitTorus K c) =
      pGammaL2FullSplitTorus K (c ^ q) := fun c => fieldAut_torus_pow hφ c
  have hφφ : (y : PGammaL2 K).right * (y : PGammaL2 K).right = 1 := by
    rw [← sq]; exact hright y
  have hy1 : eS y ≠ 1 := fun h => hy (by
    rw [show y = 1 from eS.injective (by rw [h, map_one])]; rfl)
  have hyz : eS y ≠ a 2 := fun h => hy (by
    rw [show y = z8 from eS.injective (by rw [h, hz8])]; rfl)
  obtain ⟨j, hj1, hj2, hj3, hj4⟩ := q8_exists_inv (eS y) hy1 hyz
  obtain ⟨c, hcr, hcy, hc2⟩ : ∃ c : S, (c : PGammaL2 K).right = 1 ∧ y * c * y⁻¹ = c⁻¹ ∧
      c ^ 2 ≠ 1 := by
    by_cases h : ((eS.symm j : S) : PGammaL2 K).right = 1
    · refine ⟨eS.symm j, h, eS.injective (by simp [hj1]), fun h' => hj3 ?_⟩
      simpa using congrArg eS h'
    · refine ⟨y * eS.symm j, ?_, eS.injective (by simp [hj2]), fun h' => hj4 ?_⟩
      · rw [Subgroup.coe_mul, SemidirectProduct.mul_right, huniq _ h, hφφ]
      · simpa using congrArg eS h'
  have hcl := left_commute_s0 (hPc _ (hQP (hSQ c.2)))
  have hcinl : (c : PGammaL2 K) = SemidirectProduct.inl (c : PGammaL2 K).left :=
    SemidirectProduct.ext rfl (by rw [hcr]; rfl)
  obtain ⟨a', ha'⟩ : (c : PGammaL2 K).left ∈ (pGammaL2FullSplitTorus K).range := by
    by_contra hmem
    apply hc2
    apply Subtype.ext
    rw [Subgroup.coe_pow, hcinl, ← map_pow, sq, sq_eq_one_of_not_mem_torus hK hcl hmem, map_one,
      Subgroup.coe_one]
  have hcT : (c : PGammaL2 K) = SemidirectProduct.inl (pGammaL2FullSplitTorus K a') := by
    rw [hcinl, ha']
  have ha2 : a' * a' = -1 := by
    have h := congrArg (fun x : S => (x : PGammaL2 K)) ((hsqS c).resolve_left hc2)
    simp only [Subgroup.coe_pow, hcT] at h
    rw [← map_pow, ← map_pow] at h
    exact (pGammaL2FullSplitTorus_injective K (SemidirectProduct.inl_injective h)).trans rfl
      |> fun h' => by rw [← sq]; exact h'
  have hneg : (-1 : Kˣ) ≠ 1 := fun h => s0_ne_one hK (by rw [h, map_one])
  have haq : a' ^ q = a' := by
    have h4 : a' ^ 4 = 1 := by
      have h2 : a' ^ 2 = -1 := by rw [sq]; exact ha2
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2]; simp
    obtain ⟨k, hk⟩ : ∃ k, q = 4 * k + 1 := ⟨q / 4, by omega⟩
    rw [hk, pow_succ, pow_mul, h4, one_pow, one_mul]
  have hyl := left_commute_s0 (hPc _ (hQP (hSQ y.2)))
  have hyU : (y : PGammaL2 K).left ∉ (pGammaL2FullSplitTorus K).range := by
    rintro ⟨b', hb'⟩
    have h := congrArg (fun x : S => (x : PGammaL2 K)) hcy
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hcT, conj_inl, ← hb', hφT, haq] at h
    have h1 : pGammaL2FullSplitTorus K b' * pGammaL2FullSplitTorus K a' *
        (pGammaL2FullSplitTorus K b')⁻¹ = pGammaL2FullSplitTorus K a' := by
      rw [← map_inv, ← map_mul, ← map_mul, mul_comm b' a', mul_assoc, mul_inv_cancel, mul_one]
    rw [h1, ← map_inv, ← map_inv] at h
    have h' := pGammaL2FullSplitTorus_injective K (SemidirectProduct.inl_injective h)
    apply hneg
    rw [← ha2]
    calc a' * a' = a'⁻¹ * a' := by rw [← h']
      _ = 1 := inv_mul_cancel a'
  obtain ⟨b, hb⟩ := (mem_torus_or_mul_weyl hK hyl).resolve_left hyU
  have hyleft : (y : PGammaL2 K).left = pGammaL2FullSplitTorus K b * weylPGL K := by
    rw [hb, mul_assoc, weylPGL_mul_self, mul_one]
  have hnT : ∀ c : Kˣ, weylPGL K * pGammaL2FullSplitTorus K c =
      (pGammaL2FullSplitTorus K c)⁻¹ * weylPGL K := fun c => by
    calc weylPGL K * pGammaL2FullSplitTorus K c
        = (weylPGL K * pGammaL2FullSplitTorus K c * (weylPGL K)⁻¹) * weylPGL K := by group
      _ = _ := by rw [weylPGL_conj_torus]
  have hy2 : y ^ 2 = z8 := (hsqS y).resolve_left fun h => by
    rcases q8_inv_eq (eS y) (by rw [← map_pow, h, map_one]) with h' | h'
    · exact hy1 h'
    · exact hyz h'
  have hbq : b ^ q = -b := by
    have h := congrArg (fun x : S => SemidirectProduct.left (x : PGammaL2 K)) hy2
    simp only [sq, Subgroup.coe_mul, SemidirectProduct.mul_left, hyleft, map_mul, hφT,
      pgl2FieldAut_weylPGL, hz8def, SemidirectProduct.left_inl] at h
    have h2 : pGammaL2FullSplitTorus K b * weylPGL K *
        (pGammaL2FullSplitTorus K (b ^ q) * weylPGL K) =
          pGammaL2FullSplitTorus K (b * (b ^ q)⁻¹) := by
      rw [map_mul, map_inv]
      calc _ = pGammaL2FullSplitTorus K b * (weylPGL K * pGammaL2FullSplitTorus K (b ^ q)) *
            weylPGL K := by group
        _ = pGammaL2FullSplitTorus K b * (pGammaL2FullSplitTorus K (b ^ q))⁻¹ *
            (weylPGL K * weylPGL K) := by rw [hnT]; group
        _ = _ := by rw [weylPGL_mul_self, mul_one]
    rw [h2] at h
    have h3 := pGammaL2FullSplitTorus_injective K h
    have h4 : b = -(b ^ q) := by
      calc b = b * (b ^ q)⁻¹ * b ^ q := by group
        _ = -(b ^ q) := by rw [h3, neg_one_mul]
    calc b ^ q = -(-(b ^ q)) := (neg_neg _).symm
      _ = -b := by rw [← h4]
  set a₁ : PGammaL2 K := (y : PGammaL2 K) * SemidirectProduct.inl (weylPGL K) with ha₁
  have ha₁l : a₁.left = pGammaL2FullSplitTorus K b := by
    rw [ha₁, SemidirectProduct.mul_left, SemidirectProduct.left_inl, pgl2FieldAut_weylPGL, hyleft,
      mul_assoc, weylPGL_mul_self, mul_one]
  have ha₁r : a₁.right = (y : PGammaL2 K).right := by
    rw [ha₁, SemidirectProduct.mul_right, SemidirectProduct.right_inl, mul_one]
  have ha₁y : a₁ * (y : PGammaL2 K) = SemidirectProduct.inl (pGammaL2FullSplitTorus K b *
      pGammaL2FullSplitTorus K (b ^ q) * weylPGL K) := by
    apply SemidirectProduct.ext
    · rw [SemidirectProduct.mul_left, ha₁l, ha₁r, hyleft, map_mul, hφT, pgl2FieldAut_weylPGL,
        SemidirectProduct.left_inl, mul_assoc]
    · rw [SemidirectProduct.mul_right, ha₁r, hφφ, SemidirectProduct.right_inl]
  have hya₁ : (y : PGammaL2 K) * a₁ = SemidirectProduct.inl (pGammaL2FullSplitTorus K b *
      weylPGL K * pGammaL2FullSplitTorus K (b ^ q)) := by
    apply SemidirectProduct.ext
    · rw [SemidirectProduct.mul_left, ha₁l, hyleft, hφT, SemidirectProduct.left_inl]
    · rw [SemidirectProduct.mul_right, ha₁r, hφφ, SemidirectProduct.right_inl]
  have ha₁P : a₁ ∈ P := P.mul_mem (hQP (hSQ y.2)) hnP
  have hcm : a₁ * (y : PGammaL2 K) * a₁⁻¹ * (y : PGammaL2 K)⁻¹ ∈ Q :=
    Q.mul_mem (hQn a₁ ha₁P _ (hSQ y.2)) (Q.inv_mem (hSQ y.2))
  have hcomm : a₁ * (y : PGammaL2 K) * a₁⁻¹ * (y : PGammaL2 K)⁻¹ =
      SemidirectProduct.inl (pGammaL2FullSplitTorus K (b * b)) := by
    have e1 : a₁ * (y : PGammaL2 K) * a₁⁻¹ * (y : PGammaL2 K)⁻¹ =
        (a₁ * (y : PGammaL2 K)) * ((y : PGammaL2 K) * a₁)⁻¹ := by group
    rw [e1, ha₁y, hya₁, ← map_inv, ← map_mul]
    congr 1
    calc pGammaL2FullSplitTorus K b * pGammaL2FullSplitTorus K (b ^ q) * weylPGL K *
          (pGammaL2FullSplitTorus K b * weylPGL K * pGammaL2FullSplitTorus K (b ^ q))⁻¹
        = pGammaL2FullSplitTorus K b * pGammaL2FullSplitTorus K (b ^ q) *
          (weylPGL K * (pGammaL2FullSplitTorus K (b ^ q))⁻¹ * (weylPGL K)⁻¹) *
            (pGammaL2FullSplitTorus K b)⁻¹ := by group
      _ = pGammaL2FullSplitTorus K (b * b ^ q * b ^ q * b⁻¹) := by
          rw [← map_inv, weylPGL_conj_torus, map_inv, inv_inv, ← map_inv, ← map_mul, ← map_mul,
            ← map_mul]
      _ = pGammaL2FullSplitTorus K (b * b) := by
          congr 1
          rw [hbq, mul_assoc b (-b) (-b), neg_mul_neg]
          group
  obtain ⟨w, hw⟩ : ∃ w, q - 1 = 8 * w := ⟨(q - 1) / 8, by omega⟩
  have hbq1 : b ^ (q - 1) = -1 := by
    have h1 : b ^ (q - 1) * b = b ^ q := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    rw [hbq] at h1
    calc b ^ (q - 1) = b ^ (q - 1) * b * b⁻¹ := by group
      _ = -1 := by rw [h1, neg_mul, mul_inv_cancel]
  have hbb : (b * b) ^ (4 * w) = -1 := by
    rw [← sq, ← pow_mul, show 2 * (4 * w) = q - 1 by omega, hbq1]
  have hx8 : ((a₁ * (y : PGammaL2 K) * a₁⁻¹ * (y : PGammaL2 K)⁻¹) ^ w) ^ 8 = 1 := by
    rw [hcomm, ← pow_mul, ← map_pow, ← map_pow, show w * 8 = 4 * w * 2 by ring, pow_mul, hbb]
    simp
  have hx4 := hexp _ (Q.pow_mem hcm w) hx8
  rw [hcomm, ← pow_mul, ← map_pow, ← map_pow, show w * 4 = 4 * w by ring, hbb] at hx4
  exact s0_ne_one hK (by
    have h := congrArg SemidirectProduct.left hx4
    simpa using h)

end CFSG.ClassicalInvolution.Q3.TL4.MF164

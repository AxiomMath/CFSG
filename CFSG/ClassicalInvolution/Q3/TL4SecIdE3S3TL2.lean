module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdE3S3TD
public import CFSG.ClassicalInvolution.Q3.TL4MF164L2
public import CFSG.ClassicalInvolution.Q3.TL4Thm6L2A
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoL2A
public import CFSG.ClassicalInvolution.Asc77.AscT8V1
public import CFSG.ClassicalInvolution.Asc77.AscT8V2
public import CFSG.ClassicalInvolution.Asc77.AscT8V3
public import CFSG.ClassicalInvolution.Asc77.WP2Branch
public import CFSG.ClassicalInvolution.AschTight.S1916F2a
public import CFSG.ClassicalInvolution.Q3.OddCoreCentral
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStarBasic
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmA
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.CentQuotAEmpty
public import CFSG.ClassicalInvolution.Q3.Q3CLNine3
public import CFSG.ClassicalInvolution.Q3.Q3CPOmega
public import CFSG.ClassicalInvolution.Q3.Q3DBFuzzyEdge
public import CFSG.ClassicalInvolution.Q3.Q3KCGen
public import CFSG.ClassicalInvolution.Q3.Q3NFLink
public import CFSG.ClassicalInvolution.Q3.Q3T6BSymEx
public import CFSG.ClassicalInvolution.Q3.Q3T7E9Comp
public import CFSG.ClassicalInvolution.Q3.Q3T7E9Main
public import CFSG.ClassicalInvolution.Q3.Q3T7T2Main
public import CFSG.ClassicalInvolution.Q3.Q3T8Defs
public import CFSG.ClassicalInvolution.Q3.Q3TIMain
public import CFSG.ClassicalInvolution.Q3.Q3TIYOAMain
public import CFSG.ClassicalInvolution.Q3.Q3TKMem
public import CFSG.ClassicalInvolution.Q3.Q3WAEDict
public import CFSG.ClassicalInvolution.Q3.Q3WMain
public import CFSG.ClassicalInvolution.Q3.Q3ZFraStd
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoS1
public import CFSG.ClassicalInvolution.SmallCases.NobqFinal
public import CFSG.ClassicalInvolution.Uniform.U3IH8
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.Sporadic.J4.QT2LocProof
public import CFSG.Sporadic.J4.QTOutChar
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2FullSplitTorusFieldFixed

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint CFSG.GorensteinWalter
open scoped commutatorElement

namespace E3S3TL2

variable {K : Type} [Field K]

theorem eq_of_pow_four {β d : Kˣ} (hβ : β * β = -1) (hd : d ^ 4 = 1) :
    d = 1 ∨ d = -1 ∨ d = β ∨ d = -β := by
  have hβ' : (β : K) * β = -1 := by rw [← Units.val_mul, hβ, Units.val_neg, Units.val_one]
  have hd' : (d : K) ^ 4 = 1 := by rw [← Units.val_pow_eq_pow_val, hd, Units.val_one]
  have h0 : ((d : K) - 1) * ((d : K) + 1) * ((d : K) - β) * ((d : K) + β) = 0 := by
    linear_combination hd' + (1 - (d : K) ^ 2) * hβ'
  rcases mul_eq_zero.mp h0 with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl (Units.ext (by rw [Units.val_one]; linear_combination h))
      · refine Or.inr (Or.inl (Units.ext ?_))
        rw [Units.val_neg, Units.val_one]
        linear_combination h
    · exact Or.inr (Or.inr (Or.inl (Units.ext (by linear_combination h))))
  · exact Or.inr (Or.inr (Or.inr (Units.ext (by rw [Units.val_neg]; linear_combination h))))

theorem q8_facts : (∀ q g : QuaternionGroup 2, g ^ 2 = QuaternionGroup.a 2 → q ≠ 1 →
    q ≠ QuaternionGroup.a 2 → q ≠ g → q ≠ g ^ 3 →
      q * g * q⁻¹ = g⁻¹ ∧ q ^ 2 = QuaternionGroup.a 2) ∧
    (∀ g : QuaternionGroup 2, g * QuaternionGroup.a 2 = QuaternionGroup.a 2 * g) ∧
    (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 ∧
    (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 = QuaternionGroup.a 2 := by
  decide

theorem unitsMap_neg_one (φ : K ≃+* K) : Units.map (φ.toRingHom : K →* K) (-1 : Kˣ) = -1 :=
  Units.ext (by simp)

theorem neg_eq_neg_one_mul' (β : Kˣ) : -β = -1 * β := (neg_one_mul β).symm

variable [Finite K]

local notation "𝕋" => pGammaL2FullSplitTorus K

local notation "𝕨" => MF164.weylPGL K

theorem comm_pow_ne_one (hK : IsOddPrimePower (Nat.card K)) {g : PGammaL2 K} {β : Kˣ}
    (hβ : β * β = -1)
    (hgs : g * SemidirectProduct.inl (pGammaL2FullSplitTorus K (-1)) =
      SemidirectProduct.inl (pGammaL2FullSplitTorus K (-1)) * g)
    (hg2 : g * g = SemidirectProduct.inl (pGammaL2FullSplitTorus K (-1)))
    (hgc : g * SemidirectProduct.inl (pGammaL2FullSplitTorus K β) * g⁻¹ =
      (SemidirectProduct.inl (pGammaL2FullSplitTorus K β))⁻¹)
    {m : ℕ} (hm : Odd m) :
    ((SemidirectProduct.inl (MF164.weylPGL K) * g * (SemidirectProduct.inl (MF164.weylPGL K))⁻¹ *
      g⁻¹) ^ 2) ^ m ≠ 1 := by
  obtain ⟨h, hh⟩ : ∃ x, x = g.left := ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ x, x = g.right := ⟨_, rfl⟩
  obtain ⟨φu, hφu⟩ : ∃ f : Kˣ →* Kˣ, f = Units.map φ.toRingHom := ⟨_, rfl⟩
  have hneg : (-1 : Kˣ) ≠ 1 := fun h1 => MF164.s0_ne_one hK (by rw [h1, map_one])
  have hTinj : ∀ {x y : Kˣ}, 𝕋 x = 𝕋 y → x = y := fun hxy =>
    pGammaL2FullSplitTorus_injective K hxy
  have hφT : ∀ b : Kˣ, pgl2FieldAut K φ (𝕋 b) = 𝕋 (φu b) := fun b => by
    rw [hφu]
    exact pGammaL2FullSplitTorus_map_field K φ b
  have hwT : ∀ b : Kˣ, 𝕨 * 𝕋 b * 𝕨⁻¹ = (𝕋 b)⁻¹ := MF164.weylPGL_conj_torus
  have hl : h * 𝕋 (-1) = 𝕋 (-1) * h := by
    rw [hh]
    exact MF164.left_commute_s0 hgs
  have hsq : h * pgl2FieldAut K φ h = 𝕋 (-1) := by
    have := congrArg SemidirectProduct.left hg2
    rwa [SemidirectProduct.mul_left, SemidirectProduct.left_inl, ← hh, ← hφ] at this
  have hconj : h * pgl2FieldAut K φ (𝕋 β) * h⁻¹ = (𝕋 β)⁻¹ := by
    have := hgc
    rw [MF164.conj_inl, ← map_inv, ← hh, ← hφ] at this
    exact SemidirectProduct.inl_injective this
  have hcomm : SemidirectProduct.inl 𝕨 * g * (SemidirectProduct.inl 𝕨)⁻¹ * g⁻¹ =
      SemidirectProduct.inl (𝕨 * h * 𝕨⁻¹ * h⁻¹) := by
    calc SemidirectProduct.inl 𝕨 * g * (SemidirectProduct.inl 𝕨)⁻¹ * g⁻¹
        = SemidirectProduct.inl 𝕨 * (g * SemidirectProduct.inl 𝕨⁻¹ * g⁻¹) := by
          rw [map_inv]; group
      _ = SemidirectProduct.inl (𝕨 * h * 𝕨⁻¹ * h⁻¹) := by
          rw [MF164.conj_inl, map_inv (pgl2FieldAut K g.right), MF164.pgl2FieldAut_weylPGL,
            ← map_mul, ← hh]
          congr 1
          group
  obtain ⟨a, hca, hcases⟩ : ∃ a : Kˣ, 𝕨 * h * 𝕨⁻¹ * h⁻¹ = 𝕋 (a⁻¹ * a⁻¹) ∧
      ((a * φu a = -1 ∧ φu β = β⁻¹) ∨ (a * (φu a)⁻¹ = -1 ∧ φu β = β)) := by
    rcases MF164.mem_torus_or_mul_weyl hK hl with ⟨a, ha⟩ | ⟨a, ha⟩
    · refine ⟨a, ?_, Or.inl ⟨?_, ?_⟩⟩
      · rw [← ha, hwT a, map_mul, map_inv]
      · apply hTinj
        rw [map_mul, ← hφT, ha]
        exact hsq
      · have h1 := hconj
        rw [← ha, hφT, ← map_inv, ← map_mul, ← map_mul, ← map_inv] at h1
        have h2 := hTinj h1
        rwa [mul_comm a, mul_assoc, mul_inv_cancel, mul_one] at h2
    · have hh' : h = 𝕋 a * 𝕨 := by
        rw [ha, mul_assoc, MF164.weylPGL_mul_self, mul_one]
      have hφh : pgl2FieldAut K φ h = 𝕋 (φu a) * 𝕨 := by
        rw [hh', map_mul, hφT, MF164.pgl2FieldAut_weylPGL]
      refine ⟨a, ?_, Or.inr ⟨?_, ?_⟩⟩
      · rw [hh']
        calc 𝕨 * (𝕋 a * 𝕨) * 𝕨⁻¹ * (𝕋 a * 𝕨)⁻¹ = 𝕨 * 𝕋 a * 𝕨⁻¹ * (𝕋 a)⁻¹ := by group
          _ = 𝕋 (a⁻¹ * a⁻¹) := by rw [hwT a, map_mul, map_inv]
      · apply hTinj
        rw [← hsq, hφh, hh', map_mul, map_inv]
        calc 𝕋 a * (𝕋 (φu a))⁻¹ = 𝕋 a * (𝕨 * 𝕋 (φu a) * 𝕨⁻¹) := by rw [hwT]
          _ = 𝕋 a * 𝕨 * (𝕋 (φu a) * 𝕨) * (𝕨 * 𝕨)⁻¹ := by group
          _ = 𝕋 a * 𝕨 * (𝕋 (φu a) * 𝕨) := by rw [MF164.weylPGL_mul_self, inv_one, mul_one]
      · have h1 := hconj
        rw [hh', hφT] at h1
        have h2 : 𝕋 a * 𝕨 * 𝕋 (φu β) * (𝕋 a * 𝕨)⁻¹ = 𝕋 (a * (φu β)⁻¹ * a⁻¹) := by
          rw [map_mul, map_mul, map_inv, map_inv]
          calc 𝕋 a * 𝕨 * 𝕋 (φu β) * (𝕋 a * 𝕨)⁻¹ = 𝕋 a * (𝕨 * 𝕋 (φu β) * 𝕨⁻¹) * (𝕋 a)⁻¹ := by
                group
            _ = 𝕋 a * (𝕋 (φu β))⁻¹ * (𝕋 a)⁻¹ := by rw [hwT]
        rw [h2, ← map_inv (pGammaL2FullSplitTorus K) β] at h1
        have h3 := hTinj h1
        rw [mul_comm a, mul_assoc, mul_inv_cancel, mul_one] at h3
        exact inv_injective h3
  intro hpow
  rw [hcomm, hca, ← map_pow, ← map_pow, ← map_pow, ← map_pow] at hpow
  have h1 : ((a⁻¹ * a⁻¹) ^ 2) ^ m = 1 := by
    have h2 : 𝕋 (((a⁻¹ * a⁻¹) ^ 2) ^ m) = 𝕋 1 :=
      (SemidirectProduct.inl_injective (hpow.trans (map_one _).symm)).trans (map_one _).symm
    exact hTinj h2
  have hd4 : (a ^ m) ^ 4 = 1 := by
    have e : ((a⁻¹ * a⁻¹) ^ 2) ^ m = ((a ^ m) ^ 4)⁻¹ := by group
    rw [e] at h1
    exact inv_eq_one.mp h1
  have hφ1 : φu 1 = 1 := map_one φu
  have hφn : φu (-1) = -1 := by
    rw [hφu]
    exact unitsMap_neg_one φ
  have hm1 : (-1 : Kˣ) ^ m = -1 := hm.neg_one_pow
  rcases hcases with ⟨ha1, hβ1⟩ | ⟨ha2, hβ2⟩
  · have hdd : a ^ m * φu (a ^ m) = -1 := by rw [map_pow, ← mul_pow, ha1, hm1]
    have hone : a ^ m * φu (a ^ m) = 1 := by
      rcases eq_of_pow_four hβ hd4 with hd | hd | hd | hd <;> rw [hd]
      · rw [hφ1, one_mul]
      · rw [hφn, neg_mul_neg, one_mul]
      · rw [hβ1, mul_inv_cancel]
      · rw [neg_eq_neg_one_mul' β, map_mul, hφn, hβ1]
        calc -1 * β * (-1 * β⁻¹) = -1 * -1 * (β * β⁻¹) := by rw [mul_mul_mul_comm]
          _ = 1 := by rw [neg_mul_neg, one_mul, one_mul, mul_inv_cancel]
    exact hneg (hdd.symm.trans hone)
  · have hdd : a ^ m * (φu (a ^ m))⁻¹ = -1 := by rw [map_pow, ← inv_pow, ← mul_pow, ha2, hm1]
    have hfix : φu (a ^ m) = a ^ m := by
      rcases eq_of_pow_four hβ hd4 with hd | hd | hd | hd <;> rw [hd]
      · exact hφ1
      · exact hφn
      · exact hβ2
      · rw [neg_eq_neg_one_mul' β, map_mul, hφn, hβ2]
    rw [hfix, mul_inv_cancel] at hdd
    exact hneg hdd.symm

end E3S3TL2

open E3S3TL2 in
theorem twKindL2_proved : TwKindL2 := by
  intro X _ _ R S z hm hs _ hidx p f hp hp2 hfe hL
  have : Fact p.Prime := ⟨hp⟩
  have hd := hm.datum
  obtain ⟨hQanti, hQcent, hQz1, hQa1⟩ := q8_facts
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := MF164.exists_fstar_equiv_psl2 hs hL
  set N := genFittingFStar X with hNdef
  have : N.Normal := genFittingFStar_normal X
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · have h1 : 1 < Nat.card F := Finite.one_lt_card
      rw [hF, h, pow_zero] at h1
      omega
    · exact h
  have hK : IsOddPrimePower (Nat.card F) := ⟨p, f, hp, hp.odd_of_ne_two hp2, hf1, hF⟩
  have hcard : 3 < Nat.card F := by
    obtain ⟨k, hk⟩ := hfe
    have h3 : 3 ≤ p := by have := hp.two_le; omega
    rw [hF, hk, ← two_mul, pow_mul]
    calc 3 < 3 ^ 2 := by norm_num
      _ ≤ (p ^ 2) := Nat.pow_le_pow_left h3 2
      _ ≤ (p ^ 2) ^ k := Nat.le_self_pow (by omega) _
  have hsurj := pGammaL2ToMulAutPSL2_surjective F hF hK hcard
  have hnab : ∃ a b : N, a * b ≠ b * a := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    have hc : Subgroup.center (PSL2 F) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      apply e.symm.injective
      rw [map_mul, map_mul, h]
    have hnt : Nontrivial (PSL2 F) := inferInstance
    rw [psl2_center_eq_bot F] at hc
    exact bot_ne_top hc
  have hC : Subgroup.centralizer (N : Set X) = ⊥ := centralizer_genFittingFStar_eq_bot hnab
  set ι := normalPSL2ToPGammaL2 N F hK hcard e hsurj with hιdef
  have hιinj : Function.Injective ι := normalPSL2ToPGammaL2_injective N F hK hcard e hC hsurj
  have hιN : ∀ w : PSL2 F, ∃ y : X, ι y = SemidirectProduct.inl
      (Matrix.ProjectiveSpecialLinearGroup.toPGL w) := fun w => ⟨(e.symm w : X), by
    rw [hιdef, normalPSL2ToPGammaL2_apply_subtype N F hK hcard e hsurj,
      MulEquiv.apply_symm_apply]⟩
  obtain ⟨i, hi⟩ : ∃ i : F, i * i = -1 := by
    have := Fintype.ofFinite F
    have h4 : Fintype.card F % 4 ≠ 3 := by
      rw [← Nat.card_eq_fintype_card, hF]
      obtain ⟨k, hk⟩ := hfe
      obtain ⟨m, hm'⟩ := (hp.odd_of_ne_two hp2).pow (n := k)
      rw [hk, show p ^ (k + k) = (p ^ k) ^ 2 by ring, hm',
        show (2 * m + 1) ^ 2 = 4 * (m * m + m) + 1 by ring]
      omega
    obtain ⟨i, hi⟩ := FiniteField.isSquare_neg_one_iff.2 h4
    exact ⟨i, hi.symm⟩
  obtain ⟨eS⟩ := hm.cls.1
  set φQ : QuaternionGroup 2 →* X :=
    R.subtype.comp ((S : Subgroup R).subtype.comp eS.symm.toMonoidHom) with hφQ
  have hφQi : Function.Injective φQ :=
    R.subtype_injective.comp ((S : Subgroup R).subtype_injective.comp eS.symm.injective)
  have hφQR : ∀ q, φQ q ∈ R := fun q => ((eS.symm q : ↥(S : Subgroup R)) : ↥R).2
  have hφQz : φQ (QuaternionGroup.a 2) = z := hd.eq_of_orderOf_eq_two (hφQR _)
    (by rw [orderOf_injective φQ hφQi]; exact orderOf_eq_prime (by decide) (by decide))
  have hzN : z ∈ N := by
    rw [← hφQz, ← hQa1, map_pow]
    exact MF164.sq_mem_of_index_le_two hidx _
  set x := Matrix.ProjectiveSpecialLinearGroup.toPGL (e ⟨z, hzN⟩) with hxdef
  have hιz : ι z = SemidirectProduct.inl x :=
    normalPSL2ToPGammaL2_apply_subtype N F hK hcard e hsurj ⟨z, hzN⟩
  have hx1 : x ≠ 1 := fun h => hd.isUniqueInvolution_core.ne_one
    (hιinj (by rw [hιz, h, map_one, map_one]))
  have hx2 : x * x = 1 := by
    apply SemidirectProduct.inl_injective (φ := pgl2FieldAut F)
    rw [map_mul, ← hιz, ← map_mul, hd.isUniqueInvolution_core.sq, map_one, map_one]
  obtain ⟨c, hc, hcx⟩ := MF164.exists_conj_s0 hK hcard hi ⟨_, rfl⟩ hx1 hx2
  set ψ : X →* PGammaL2 F := (MulAut.conj (SemidirectProduct.inl c)).toMonoidHom.comp ι with hψ
  have hψinj : Function.Injective ψ := (MulAut.conj _).injective.comp hιinj
  have hψa : ∀ y, ψ y = SemidirectProduct.inl c * ι y * (SemidirectProduct.inl c)⁻¹ :=
    fun y => rfl
  have hψz : ψ z = SemidirectProduct.inl (pGammaL2FullSplitTorus F (-1)) := by
    rw [hψa, hιz, ← hcx, map_mul, map_mul, map_inv]
  have hψright : ∀ y ∈ N, (ψ y).right = 1 := fun y hy => by
    have h1 : ι y = SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (e ⟨y, hy⟩)) := normalPSL2ToPGammaL2_apply_subtype N F hK hcard e hsurj ⟨y, hy⟩
    rw [hψa, h1, ← map_inv, ← map_mul, ← map_mul, SemidirectProduct.right_inl]
  obtain ⟨n₁, hn₁⟩ := MF164.weylPGL_mem_range (K := F)
  obtain ⟨c₁, rfl⟩ := hc
  obtain ⟨n₀, hn₀⟩ := hιN (c₁⁻¹ * n₁ * c₁)
  have hψn₀ : ψ n₀ = SemidirectProduct.inl (MF164.weylPGL F) := by
    rw [hψa, hn₀]
    have h1 : Matrix.ProjectiveSpecialLinearGroup.toPGL (c₁⁻¹ * n₁ * c₁) =
        (Matrix.ProjectiveSpecialLinearGroup.toPGL c₁)⁻¹ * MF164.weylPGL F *
          Matrix.ProjectiveSpecialLinearGroup.toPGL c₁ := by
      rw [map_mul, map_mul, map_inv, hn₁]
    rw [h1, map_mul, map_mul, map_inv]
    group
  have hn₀C : n₀ ∈ Subgroup.centralizer ({z} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.2 (hψinj (by
      rw [map_mul, map_mul, hψn₀, hψz, ← map_mul, ← map_mul, MF164.weylPGL_commute_s0]))
  set ρ : QuaternionGroup 2 →* PGammaL2 F := ψ.comp φQ with hρ
  have hρinj : Function.Injective ρ := hψinj.comp hφQi
  have hρz : ρ (QuaternionGroup.a 2) = SemidirectProduct.inl (pGammaL2FullSplitTorus F (-1)) := by
    rw [hρ, MonoidHom.comp_apply, hφQz, hψz]
  obtain ⟨σQ, hσQ⟩ := Thm6.exists_right_ne_one hK hρinj
  obtain ⟨cQ, hcQ2, hcQr⟩ := ExitTwo.L2.exists_right_eq_one hK ρ
  have hσ1 : σQ ≠ 1 := fun h => hσQ (by rw [h, map_one, SemidirectProduct.one_right])
  have hσz : σQ ≠ QuaternionGroup.a 2 := fun h => hσQ (by rw [h, hρz, SemidirectProduct.right_inl])
  have hσc : σQ ≠ cQ := fun h => hσQ (by rw [h]; exact hcQr)
  have hσc3 : σQ ≠ cQ ^ 3 := fun h => hσQ (by
    rw [h, map_pow, ← SemidirectProduct.rightHom_eq_right, map_pow,
      SemidirectProduct.rightHom_eq_right, hcQr, one_pow])
  obtain ⟨hσcσ, hσ2⟩ := hQanti σQ cQ hcQ2 hσ1 hσz hσc hσc3
  have h2 : 2 ∣ N.index := by
    have hσN : φQ σQ ∉ N := fun h => hσQ (hψright _ h)
    have h0 := N.index_ne_zero_of_finite
    rcases (show N.index = 1 ∨ N.index = 2 by omega) with h | h
    · exact absurd (by rw [Subgroup.index_eq_one.mp h]; exact Subgroup.mem_top _) hσN
    · rw [h]
  have hCinl : ρ cQ = SemidirectProduct.inl (ρ cQ).left :=
    SemidirectProduct.ext rfl (by rw [hcQr, SemidirectProduct.right_inl])
  have hCcomm : ρ cQ * SemidirectProduct.inl (pGammaL2FullSplitTorus F (-1)) =
      SemidirectProduct.inl (pGammaL2FullSplitTorus F (-1)) * ρ cQ := by
    rw [← hρz, ← map_mul, ← map_mul, hQcent]
  obtain ⟨β, hβ⟩ : (ρ cQ).left ∈ (pGammaL2FullSplitTorus F).range := by
    by_contra hmem
    have h1 := MF164.sq_eq_one_of_not_mem_torus hK (MF164.left_commute_s0 hCcomm) hmem
    have h3 : ρ (cQ ^ 2) = 1 := by rw [map_pow, sq, hCinl, ← map_mul, h1, map_one]
    rw [hcQ2] at h3
    exact hQz1 (hρinj (h3.trans (map_one ρ).symm))
  have hCT : ρ cQ = SemidirectProduct.inl (pGammaL2FullSplitTorus F β) := by rw [hCinl, ← hβ]
  have hββ : β * β = -1 := by
    have h1 : ρ (cQ ^ 2) = SemidirectProduct.inl (pGammaL2FullSplitTorus F (-1)) := by
      rw [hcQ2, hρz]
    rw [map_pow, sq, hCT, ← map_mul, ← map_mul] at h1
    exact pGammaL2FullSplitTorus_injective F (SemidirectProduct.inl_injective h1)
  have hgs : ρ σQ * SemidirectProduct.inl (pGammaL2FullSplitTorus F (-1)) =
      SemidirectProduct.inl (pGammaL2FullSplitTorus F (-1)) * ρ σQ := by
    rw [← hρz, ← map_mul, ← map_mul, hQcent]
  have hg2 : ρ σQ * ρ σQ = SemidirectProduct.inl (pGammaL2FullSplitTorus F (-1)) := by
    rw [← map_mul, ← sq, hσ2, hρz]
  have hgc : ρ σQ * SemidirectProduct.inl (pGammaL2FullSplitTorus F β) * (ρ σQ)⁻¹ =
      (SemidirectProduct.inl (pGammaL2FullSplitTorus F β))⁻¹ := by
    rw [← hCT, ← map_inv ρ σQ, ← map_mul, ← map_mul, hσcσ, map_inv]
  refine ⟨h2, n₀, hn₀C, φQ σQ, hφQR σQ, fun hmem => ?_⟩
  have hmo : Odd (orderOf (⁅n₀, φQ σQ⁆ ^ 2)) :=
    (odd_natCard_oddCoreImg R).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hmem)
  apply comm_pow_ne_one hK hββ hgs hg2 hgc hmo
  have h1 := congrArg ψ (pow_orderOf_eq_one (⁅n₀, φQ σQ⁆ ^ 2))
  rw [map_one, map_pow, map_pow, commutatorElement_def, map_mul, map_mul, map_mul, map_inv,
    map_inv, hψn₀] at h1
  exact h1

end CFSG.ClassicalInvolution.Q3.TL4

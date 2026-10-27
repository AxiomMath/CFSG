module

public import CFSG.Permutation.UnitaryThreeRecognition.ModelTransport
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U38Defs
public import CFSG.LargeExtraspecial.S9FiveB

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

namespace U38Heis

open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open scoped commutatorElement

section Field

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] def trMap (σ : K ≃+* K) : K →+ K where
  toFun b := b + σ b
  map_zero' := by simp
  map_add' x y := by rw [map_add]; ring

theorem add_conj_eq_zero_iff (σ : K ≃+* K) (b : K) : b + σ b = 0 ↔ σ b = b := by
  constructor
  · intro h
    have : b = -σ b := eq_neg_of_add_eq_zero_left h
    rw [CharTwo.neg_eq] at this
    exact this.symm
  · intro h
    rw [h]
    exact CharTwo.add_self_eq_zero b

theorem exists_trace_preimage (σ : K ≃+* K) (hσ : Function.Involutive σ)
    (hF : Nat.card {x : K // σ x = x} = 8) (hK : Nat.card K = 64) {f : K} (hf : σ f = f) :
    ∃ b, b + σ b = f := by
  have hker : Nat.card (trMap σ).ker = 8 := by
    rw [← hF]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun b => by
      rw [AddMonoidHom.mem_ker]
      exact add_conj_eq_zero_iff σ b)
  have hrange : Nat.card (trMap σ).range = 8 := by
    have h := AddSubgroup.card_ker_mul_card_range (trMap σ)
    rw [hker, hK] at h
    omega
  have hsub : ((trMap σ).range : Set K) ⊆ {x | σ x = x} := by
    rintro _ ⟨b, rfl⟩
    show σ (b + σ b) = b + σ b
    rw [map_add, hσ b, add_comm]
  have hcard1 : ({x : K | σ x = x}).ncard = 8 := by
    rw [← hF, ← Nat.card_coe_set_eq]
    rfl
  have hcard2 : ((trMap σ).range : Set K).ncard = 8 := by
    rw [← hrange, ← Nat.card_coe_set_eq]
    rfl
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hcard1, hcard2]) (Set.toFinite _)
  have hmem : f ∈ ((trMap σ).range : Set K) := heq ▸ hf
  obtain ⟨b, hb⟩ := hmem
  exact ⟨b, hb⟩

theorem exists_nonfixed (σ : K ≃+* K) (hF : Nat.card {x : K // σ x = x} = 8)
    (hK : Nat.card K = 64) : ∃ s, σ s ≠ s := by
  by_contra h
  push Not at h
  have : Nat.card {x : K // σ x = x} = Nat.card K :=
    Nat.card_congr (Equiv.subtypeUnivEquiv h)
  omega

end Field


section Heis

variable {K : Type} [Field K] [Finite K] [CharP K 2] (J : HermitianForm 3 K)

theorem mul_fst (z w : hermitianUnipotentCoord J) : (z * w).1.1 = z.1.1 + w.1.1 := rfl

theorem mul_snd (z w : hermitianUnipotentCoord J) :
    (z * w).1.2 = z.1.2 + w.1.2 - z.1.1 * J.conj w.1.1 := rfl

theorem one_fst : (1 : hermitianUnipotentCoord J).1.1 = 0 := rfl

theorem one_snd : (1 : hermitianUnipotentCoord J).1.2 = 0 := rfl

theorem ext_coord {z w : hermitianUnipotentCoord J} (h1 : z.1.1 = w.1.1) (h2 : z.1.2 = w.1.2) :
    z = w := Subtype.ext (Prod.ext h1 h2)

theorem comm_coord (z w : hermitianUnipotentCoord J) :
    (⁅z, w⁆ : hermitianUnipotentCoord J).1 =
      (0, w.1.1 * J.conj z.1.1 - z.1.1 * J.conj w.1.1) := by
  change (hermitianUnipotentMul J (hermitianUnipotentMul J
        (hermitianUnipotentMul J z w) (hermitianUnipotentInv J z)) (hermitianUnipotentInv J w)).1 = _
  apply Prod.ext
  · simp only [hermitianUnipotentMul, hermitianUnipotentInv]
    ring
  · simp only [hermitianUnipotentMul, hermitianUnipotentInv]
    rw [map_neg, map_neg]
    linear_combination z.2 + w.2

variable (hF : Nat.card {x : K // J.conj x = x} = 8) (hK : Nat.card K = 64)

include hF hK in
theorem exists_with_fst (a : K) : ∃ w : hermitianUnipotentCoord J, w.1.1 = a := by
  have hfix : J.conj (-(a * J.conj a)) = -(a * J.conj a) := by
    rw [map_neg, map_mul, J.conj_involutive, mul_comm]
  obtain ⟨b, hb⟩ := exists_trace_preimage J.conj J.conj_involutive hF hK hfix
  refine ⟨⟨(a, b), ?_⟩, rfl⟩
  show b + J.conj b + a * J.conj a = 0
  rw [hb]
  ring

theorem fst_eq_zero_mem_center {z : hermitianUnipotentCoord J} (hz : z.1.1 = 0) :
    z ∈ Subgroup.center (hermitianUnipotentCoord J) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply ext_coord
  · rw [mul_fst, mul_fst, add_comm]
  · rw [mul_snd, mul_snd, hz]
    simp only [zero_mul, map_zero, mul_zero, sub_zero]
    ring

include hF hK in
theorem center_fst_eq_zero {z : hermitianUnipotentCoord J}
    (hz : z ∈ Subgroup.center (hermitianUnipotentCoord J)) : z.1.1 = 0 := by
  by_contra ha
  obtain ⟨s, hs⟩ := exists_nonfixed J.conj hF hK
  obtain ⟨w, hw⟩ := exists_with_fst J hF hK (z.1.1 * s)
  have hc := Subgroup.mem_center_iff.1 hz w
  have h2 := congrArg (fun u : hermitianUnipotentCoord J => u.1.2) hc
  simp only [mul_snd, hw, map_mul] at h2
  have h3 : (z.1.1 * J.conj z.1.1) * (s - J.conj s) = 0 := by
    linear_combination (-1 : K) * h2
  have hne : z.1.1 * J.conj z.1.1 ≠ 0 :=
    mul_ne_zero ha (fun h => ha (J.conj.injective (by rw [h, map_zero])))
  rcases mul_eq_zero.1 h3 with h | h
  · exact hne h
  · exact hs (sub_eq_zero.1 h).symm


include hF hK in
theorem card_center : Nat.card (Subgroup.center (hermitianUnipotentCoord J)) = 8 := by
  rw [← hF]
  have key : ∀ z : Subgroup.center (hermitianUnipotentCoord J),
      J.conj (z : hermitianUnipotentCoord J).1.2 = (z : hermitianUnipotentCoord J).1.2 := by
    intro z
    have h0 := center_fst_eq_zero J hF hK z.2
    have h1 := (z : hermitianUnipotentCoord J).2
    rw [h0, zero_mul, add_zero] at h1
    exact (add_conj_eq_zero_iff J.conj _).1 h1
  refine Nat.card_eq_of_bijective (fun z => ⟨(z : hermitianUnipotentCoord J).1.2, key z⟩) ⟨?_, ?_⟩
  · intro z w h
    have h2 : (z : hermitianUnipotentCoord J).1.2 = (w : hermitianUnipotentCoord J).1.2 :=
      congrArg Subtype.val h
    apply Subtype.ext
    apply ext_coord
    · rw [center_fst_eq_zero J hF hK z.2, center_fst_eq_zero J hF hK w.2]
    · exact h2
  · rintro ⟨x, hx⟩
    refine ⟨⟨⟨(0, x), ?_⟩, fst_eq_zero_mem_center J rfl⟩, rfl⟩
    show x + J.conj x + 0 * J.conj 0 = 0
    rw [hx, zero_mul, add_zero]
    exact CharTwo.add_self_eq_zero x

theorem sq_of_fst_zero {z : hermitianUnipotentCoord J} (hz : z.1.1 = 0) : z ^ 2 = 1 := by
  rw [pow_two]
  apply ext_coord
  · rw [mul_fst, hz, one_fst]
    simp
  · rw [mul_snd, hz, one_snd]
    simp [CharTwo.add_self_eq_zero]

theorem sq_mem_center (z : hermitianUnipotentCoord J) :
    z ^ 2 ∈ Subgroup.center (hermitianUnipotentCoord J) := by
  apply fst_eq_zero_mem_center
  rw [pow_two, mul_fst]
  exact CharTwo.add_self_eq_zero _

theorem comm_mem_center (z w : hermitianUnipotentCoord J) :
    ⁅z, w⁆ ∈ Subgroup.center (hermitianUnipotentCoord J) := by
  apply fst_eq_zero_mem_center
  have := congrArg Prod.fst (comm_coord J z w)
  simpa using this

include hF hK in
theorem card_heis (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Nat.card (hermitianUnipotentCoord J) = 2 ^ 9 := by
  have hKcard : Nat.card K = 8 ^ 2 := by rw [hK]; norm_num
  rcases huppert_II_10_12 J 8 hKcard hF hJ with
    ⟨_hΩcard, _rho, _a, _hinj, _hnatural, _hUcard,
      ⟨R, _D, _hRle, _hDle, _hN, _hinf, _hsup, _hcyc, hRcard, _hcomm, _hcommcard, _hDcard, _hreg,
        ⟨coordR, _hcoordR⟩, _hDcoord, _hDsurj⟩, _htwo, _hGcard, _hthree⟩
  rw [Nat.card_congr coordR, hRcard]
  norm_num


include hF hK in
theorem center_conj_snd (z : Subgroup.center (hermitianUnipotentCoord J)) :
    J.conj (z : hermitianUnipotentCoord J).1.2 = (z : hermitianUnipotentCoord J).1.2 := by
  have h0 := center_fst_eq_zero J hF hK z.2
  have h1 := (z : hermitianUnipotentCoord J).2
  rw [h0, zero_mul, add_zero] at h1
  exact (add_conj_eq_zero_iff J.conj _).1 h1

include hF hK in
theorem isExtraspecial_heis_quot (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (V : Subgroup (hermitianUnipotentCoord J)) [V.Normal]
    (hVZ : V ≤ Subgroup.center (hermitianUnipotentCoord J)) (hV4 : Nat.card V = 4) :
    CFSG.IsExtraspecialPGroup 2 (hermitianUnipotentCoord J ⧸ V) := by
  have hcard := card_heis J hF hK hJ
  have hZcard := card_center J hF hK
  have hP : IsPGroup 2 (hermitianUnipotentCoord J) := IsPGroup.of_card hcard
  have hfsurj : Function.Surjective (QuotientGroup.mk' V) := QuotientGroup.mk'_surjective V
  let Zb : Subgroup (hermitianUnipotentCoord J ⧸ V) :=
    (Subgroup.center (hermitianUnipotentCoord J)).map (QuotientGroup.mk' V)
  have hZbcard : Nat.card Zb = 2 := by
    have h1 : (QuotientGroup.mk' V).ker.relIndex (Subgroup.center (hermitianUnipotentCoord J)) =
        Nat.card Zb := Subgroup.relIndex_ker _ _
    rw [QuotientGroup.ker_mk'] at h1
    have h2 := Subgroup.relIndex_mul_card (H := V)
      (K := Subgroup.center (hermitianUnipotentCoord J))
    rw [inf_eq_left.2 hVZ, hV4, hZcard, h1] at h2
    omega
  have hZbc : Zb ≤ Subgroup.center (hermitianUnipotentCoord J ⧸ V) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨a, rfl⟩ := hfsurj g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz a]
  have hcomm : ∀ x y : hermitianUnipotentCoord J ⧸ V, ⁅x, y⁆ ∈ Zb := by
    intro x y
    obtain ⟨a, rfl⟩ := hfsurj x
    obtain ⟨b, rfl⟩ := hfsurj y
    rw [← map_commutatorElement]
    exact Subgroup.mem_map_of_mem _ (comm_mem_center J a b)
  have hsq : ∀ x : hermitianUnipotentCoord J ⧸ V, x ^ 2 ∈ Zb := by
    intro x
    obtain ⟨a, rfl⟩ := hfsurj x
    rw [← map_pow]
    exact Subgroup.mem_map_of_mem _ (sq_mem_center J a)
  have hcent : ∀ x : hermitianUnipotentCoord J ⧸ V, (∀ y, x * y = y * x) → x ∈ Zb := by
    intro x hx
    obtain ⟨h, rfl⟩ := hfsurj x
    have hcommV : ∀ w : hermitianUnipotentCoord J, ⁅h, w⁆ ∈ V := by
      intro w
      have h1 := hx (QuotientGroup.mk' V w)
      rw [← map_mul, ← map_mul] at h1
      have h2 : (h * w) / (w * h) ∈ V := QuotientGroup.eq_iff_div_mem.1 h1
      have e : ⁅h, w⁆ = (h * w) / (w * h) := by
        rw [commutatorElement_def, div_eq_mul_inv, mul_inv_rev]
        group
      rw [e]
      exact h2
    have ha : h.1.1 = 0 := by
      by_contra ha
      have hZV : Subgroup.center (hermitianUnipotentCoord J) ≤ V := by
        intro z hz
        have hz0 := center_fst_eq_zero J hF hK hz
        have hzf := center_conj_snd J hF hK ⟨z, hz⟩
        have hN : J.conj (h.1.1 * J.conj h.1.1) = h.1.1 * J.conj h.1.1 := by
          rw [map_mul, J.conj_involutive, mul_comm]
        have hσne : J.conj h.1.1 ≠ 0 := fun h' => ha (J.conj.injective (by rw [h', map_zero]))
        have hNne : h.1.1 * J.conj h.1.1 ≠ 0 := mul_ne_zero ha hσne
        have hfx : J.conj (z.1.2 / (h.1.1 * J.conj h.1.1)) =
            z.1.2 / (h.1.1 * J.conj h.1.1) := by
          rw [map_div₀, hN]
          exact congrArg (· / (h.1.1 * J.conj h.1.1)) hzf
        obtain ⟨s, hs⟩ := exists_trace_preimage J.conj J.conj_involutive hF hK hfx
        obtain ⟨w, hw⟩ := exists_with_fst J hF hK (h.1.1 * s)
        have hc := hcommV w
        have hzeq : ⁅h, w⁆ = z := by
          apply ext_coord
          · have := congrArg Prod.fst (comm_coord J h w)
            simp only at this
            rw [this, hz0]
          · have h1 := congrArg Prod.snd (comm_coord J h w)
            simp only at h1
            rw [h1, hw, map_mul]
            have h2 : h.1.1 * J.conj h.1.1 * (s + J.conj s) = z.1.2 := by
              rw [hs]
              field_simp
            linear_combination h2 +
              (-(h.1.1 * J.conj h.1.1 * J.conj s)) * (CharTwo.two_eq_zero : (2 : K) = 0)
        rw [← hzeq]
        exact hc
      have := Subgroup.card_le_of_le hZV
      rw [hZcard, hV4] at this
      omega
    exact Subgroup.mem_map_of_mem _ (fst_eq_zero_mem_center J ha)
  have hnab : ∃ x : hermitianUnipotentCoord J ⧸ V, x ∉ Zb := by
    obtain ⟨w₀, hw₀⟩ := exists_with_fst J hF hK 1
    refine ⟨QuotientGroup.mk' V w₀, fun hmem => ?_⟩
    obtain ⟨z, hz, hzeq⟩ := hmem
    have h1 : z⁻¹ * w₀ ∈ V := QuotientGroup.eq.1 hzeq
    have hw0 : w₀ ∈ Subgroup.center (hermitianUnipotentCoord J) := by
      have := mul_mem hz (hVZ h1)
      simpa using this
    have := center_fst_eq_zero J hF hK hw0
    rw [hw₀] at this
    exact one_ne_zero this
  exact CFSG.LargeExtraspecial.S9.isExtraspecialPGroup_of_center (hP.to_quotient V)
    hZbcard hZbc hcomm hsq hcent hnab

include hF hK in
theorem sylowStr_heis (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    SylowStr (hermitianUnipotentCoord J) := by
  have hcard := card_heis J hF hK hJ
  have hZcard := card_center J hF hK
  have hP : IsPGroup 2 (hermitianUnipotentCoord J) := IsPGroup.of_card hcard
  refine ⟨hP, hcard, by rw [hZcard]; norm_num,
    fun z hz => sq_of_fst_zero J (center_fst_eq_zero J hF hK hz), ?_⟩
  intro V hVZ hV4
  haveI hVn : V.Normal := ⟨fun n hn g => by
    have := Subgroup.mem_center_iff.1 (hVZ hn) g
    rw [this, mul_inv_cancel_right]
    exact hn⟩
  refine ⟨hermitianUnipotentCoord J ⧸ V, inferInstance, QuotientGroup.mk' V,
    QuotientGroup.mk'_surjective V, QuotientGroup.ker_mk' V,
    isExtraspecial_heis_quot J hF hK hJ V hVZ hV4, ?_⟩
  have h1 := Subgroup.index_mul_card V
  rw [Subgroup.index_eq_card, hcard, hV4] at h1
  norm_num at h1 ⊢
  omega

end Heis


theorem exists_sylowAmb_u38 : ∃ T : Subgroup U38Model, SylowAmb T := by
  have hK : Nat.card (GaloisField 2 6) = (2 ^ 3) ^ 2 := by
    rw [GaloisField.card 2 6 (by norm_num)]
    norm_num
  obtain ⟨J, hJ, hconj, hfix⟩ :=
    CFSG.UnitaryThreeRecognition.Model.exists_standardHermitianForm (K := GaloisField 2 6) 2 3 hK
  obtain ⟨e⟩ := CFSG.UnitaryThreeRecognition.Model.nonempty_psu_equiv_statedProj_of_conj_eq_pow
    J 2 3 Nat.prime_two hK hconj
  let ψ : hermitianUnipotentCoord J →* U38Model :=
    e.toMonoidHom.comp (hermitianUnipotentPSU J hJ)
  have hψ : Function.Injective ψ := e.injective.comp
    (CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ)
  have hstr := sylowStr_heis J (by rw [hfix]; norm_num) (by rw [hK]; norm_num) hJ
  exact ⟨ψ.range, sylowAmb_of_str (hstr.of_mulEquiv (MonoidHom.ofInjective hψ))⟩

end U38Heis

end CFSG.LocalAnalysis.GLTheoremA.CatB

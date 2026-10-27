module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04LUGen
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSLDescent
public import CFSG.RankThree.PartOne.KC.LinearSubfieldFixedPoints
public import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise

public section

namespace CFSG.LocalAnalysis.GLTheoremA.YS04LUPSL

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCLinearSubfield
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b
  (card_le_mul_card_inf_inner_of_le mem_semilinearAutGroup_of_pow_eq_one)

theorem dvd_sub_one_of_pow_eq {p a b : ℕ} (hp : p.Prime) (hb : b = a ^ p) (hpb : p ∣ b - 1) :
    p ∣ a - 1 := by
  haveI := Fact.mk hp
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  have ha1 : 1 ≤ a := ha
  have hb1 : 1 ≤ b := by rw [hb]; exact Nat.one_le_pow _ _ ha
  have h1 : ((b : ℕ) : ZMod p) = 1 := by
    have h0 : ((b - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpb
    rw [Nat.cast_sub hb1] at h0
    simpa [sub_eq_zero] using h0
  have h2 : (a : ZMod p) = 1 := by
    have h3 : (a : ZMod p) ^ p = (b : ZMod p) := by rw [hb, Nat.cast_pow]
    rw [ZMod.pow_card, h1] at h3
    exact h3
  have h4 : ((a - 1 : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_sub ha1, h2, Nat.cast_one, sub_self]
  exact (ZMod.natCast_eq_zero_iff _ _).1 h4

theorem exists_orderOf_prime_range {n : ℕ} {K : Type} [Field K] [Finite K] (hn : 3 ≤ n) {p : ℕ}
    (hp : p.Prime) (k : Subfield K) (hpk : p ∣ Nat.card k - 1) :
    ∃ x : (linearSubfieldInclusion n k).range, orderOf x = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card (↥k)ˣ := by rw [Nat.card_units]; exact hpk
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hζ
    exact hp.one_lt.ne hζ
  set i0 : Fin n := ⟨0, by omega⟩ with hi0
  set i1 : Fin n := ⟨1, by omega⟩ with hi1
  set i2 : Fin n := ⟨2, by omega⟩ with hi2
  have hi01 : i0 ≠ i1 := by simp [hi0, hi1, Fin.ext_iff]
  have hi20 : i2 ≠ i0 := by simp [hi0, hi2, Fin.ext_iff]
  have hi21 : i2 ≠ i1 := by simp [hi1, hi2, Fin.ext_iff]
  let d : Fin n → (↥k)ˣ := Pi.mulSingle i0 ζ * Pi.mulSingle i1 ζ⁻¹
  have hdprod : ∏ i, d i = 1 := by
    simp only [d, Pi.mul_apply]
    rw [Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle', Fintype.prod_pi_mulSingle',
      mul_inv_cancel]
  have hdpow : ∀ i, (d i) ^ p = 1 := by
    intro i
    simp only [d, Pi.mul_apply]
    by_cases h0 : i = i0
    · subst h0
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hi01, mul_one, hζp]
    · by_cases h1 : i = i1
      · subst h1
        rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (Ne.symm hi01), one_mul, inv_pow, hζp,
          inv_one]
      · rw [Pi.mulSingle_eq_of_ne h0, Pi.mulSingle_eq_of_ne h1, mul_one, one_pow]
  have hdet : (Matrix.diagonal fun i => ((d i : (↥k)ˣ) : ↥k)).det = 1 := by
    rw [Matrix.det_diagonal, ← Units.coe_prod, hdprod, Units.val_one]
  let Ds : Matrix.SpecialLinearGroup (Fin n) ↥k :=
    ⟨Matrix.diagonal fun i => ((d i : (↥k)ˣ) : ↥k), hdet⟩
  have hcoe : (Ds : Matrix (Fin n) (Fin n) ↥k) = Matrix.diagonal fun i => ((d i : (↥k)ˣ) : ↥k) :=
    rfl
  have hfp : (fun i => ((d i : (↥k)ˣ) : ↥k)) ^ p = 1 := by
    funext i
    simp only [Pi.pow_apply, Pi.one_apply]
    rw [← Units.val_pow_eq_pow_val, hdpow i, Units.val_one]
  have hDs : (Ds ^ p : Matrix.SpecialLinearGroup (Fin n) ↥k) = 1 := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [Matrix.SpecialLinearGroup.coe_pow, hcoe, Matrix.diagonal_pow, hfp]
    simp
  have hpow : (proj n ↥k Ds) ^ p = 1 := by
    rw [← map_pow, hDs, map_one]
  have hne : proj n ↥k Ds ≠ 1 := by
    intro h
    rw [proj_eq_one_iff, mem_scalars] at h
    obtain ⟨c, -, hc⟩ := h
    have e0 := congrFun (congrFun hc i0) i0
    have e2 := congrFun (congrFun hc i2) i2
    have hd2 : d i2 = 1 := by
      simp only [d, Pi.mul_apply, Pi.mulSingle_eq_of_ne hi20, Pi.mulSingle_eq_of_ne hi21, mul_one]
    have hd0 : d i0 = ζ := by
      simp only [d, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hi01, mul_one]
    simp only [Ds, Matrix.diagonal_apply_eq, Matrix.scalar_apply] at e0 e2
    rw [hd0] at e0
    rw [hd2] at e2
    apply hζ1
    have h1 : ((ζ : (↥k)ˣ) : ↥k) = 1 := by
      rw [e0, ← e2]
      simp
    exact Units.ext h1
  refine ⟨⟨linearSubfieldInclusion n k (proj n ↥k Ds), MonoidHom.mem_range.2 ⟨proj n ↥k Ds, rfl⟩⟩,
    ?_⟩
  rw [Subgroup.orderOf_mk, orderOf_injective _ (linearSubfieldInclusion_injective (by omega) k) _]
  exact orderOf_eq_prime hpow hne

theorem psl_normalizes {n : ℕ} {K : Type} [Field K] [Finite K] (hn : 3 ≤ n) {σ : K ≃+* K}
    (k : Subfield K) (hk : ∀ x, x ∈ k ↔ σ x = x) (g : projectiveSL n K)
    (hg : fieldAut n K σ g = g) (z : projectiveSL n K)
    (hz : z ∈ (linearSubfieldInclusion n k).range) :
    g * z * g⁻¹ ∈ (linearSubfieldInclusion n k).range := by
  obtain ⟨G, rfl⟩ := proj_surjective n K g
  obtain ⟨N, hN, rfl⟩ := mem_range_linearSubfieldInclusion.1 hz
  obtain ⟨c, -, hGc⟩ := exists_scalar_of_fieldAut_proj_eq hg
  obtain ⟨i₀, j₀, hne⟩ := exists_ne_zero_entry (show 0 < n by omega) G
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  have hdetG : (G : Matrix (Fin n) (Fin n) K).det = 1 := G.2
  have hdetN : (N : Matrix (Fin n) (Fin n) K).det = 1 := N.2
  set Gm : Matrix (Fin n) (Fin n) K := (G : Matrix (Fin n) (Fin n) K) with hGm
  set Nm : Matrix (Fin n) (Fin n) K := (N : Matrix (Fin n) (Fin n) K) with hNm
  set u : K := (Gm i₀ j₀)⁻¹ with hu
  have hu0 : u ≠ 0 := inv_ne_zero hne
  have hσu : σ u = u * (c : K)⁻¹ := by
    rw [hu, map_inv₀, hGc i₀ j₀, mul_inv]
  set B : Matrix (Fin n) (Fin n) K := u • Gm with hB
  have hBk : ∀ a b, σ (B a b) = B a b := by
    intro a b
    rw [hB, Matrix.smul_apply, smul_eq_mul, map_mul, hσu, hGc a b]
    field_simp
  have hBdet : B.det = u ^ n := by
    rw [hB, Matrix.det_smul, hdetG, mul_one, Fintype.card_fin]
  let B0 : Matrix (Fin n) (Fin n) k := fun a b => ⟨B a b, (hk _).2 (hBk a b)⟩
  let N0 : Matrix (Fin n) (Fin n) k := fun a b => ⟨Nm a b, hN a b⟩
  have hB0 : B0.map k.subtype = B := rfl
  have hN0 : N0.map k.subtype = Nm := rfl
  have hdetB0 : B0.det ≠ 0 := by
    intro h
    have h1 : k.subtype B0.det = B.det := by
      rw [← hB0, RingHom.map_det]
      rfl
    rw [h, map_zero, hBdet] at h1
    exact pow_ne_zero n hu0 h1.symm
  have hudet : IsUnit B0.det := isUnit_iff_ne_zero.2 hdetB0
  have hdetN0 : N0.det = 1 := by
    apply Subtype.ext
    have h1 : k.subtype N0.det = Nm.det := by
      rw [← hN0, RingHom.map_det]
      rfl
    exact h1.trans hdetN
  have hinv : B0⁻¹ * B0 = 1 := Matrix.nonsing_inv_mul B0 hudet
  obtain ⟨P0k, hP0k⟩ : ∃ X : Matrix (Fin n) (Fin n) k, X = B0 * N0 * B0⁻¹ := ⟨_, rfl⟩
  have hkey : P0k * B0 = B0 * N0 := by
    rw [hP0k, Matrix.mul_assoc, hinv, Matrix.mul_one]
  have hdetP0 : P0k.det = 1 := by
    have h1 : P0k.det * B0.det = B0.det := by
      rw [← Matrix.det_mul, hkey, Matrix.det_mul, hdetN0, mul_one]
    exact mul_right_cancel₀ hdetB0 (h1.trans (one_mul _).symm)
  have hK1 : P0k.map k.subtype * B = B * Nm := by
    have h0 := congrArg (fun M : Matrix (Fin n) (Fin n) k => M.map k.subtype) hkey
    simp only [Matrix.map_mul, hB0, hN0] at h0
    exact h0
  rw [hB, Matrix.mul_smul, Matrix.smul_mul] at hK1
  have hPG := smul_right_injective _ hu0 hK1
  have hfin : P0k.map k.subtype = Gm * Nm * Matrix.adjugate Gm := by
    have h2 : Gm * Matrix.adjugate Gm = 1 := by rw [Matrix.mul_adjugate, hdetG, one_smul]
    calc P0k.map k.subtype = P0k.map k.subtype * (Gm * Matrix.adjugate Gm) := by rw [h2, Matrix.mul_one]
      _ = (P0k.map k.subtype * Gm) * Matrix.adjugate Gm := by rw [Matrix.mul_assoc]
      _ = Gm * Nm * Matrix.adjugate Gm := by rw [hPG]
  let Psl : Matrix.SpecialLinearGroup (Fin n) k := ⟨P0k, hdetP0⟩
  have hSL : G * N * G⁻¹ = Matrix.SpecialLinearGroup.map k.subtype Psl := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun a b => ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.SpecialLinearGroup.map_apply_coe]
    exact (congrFun (congrFun hfin a) b).symm
  rw [← map_inv, ← map_mul, ← map_mul, hSL, ← linearSubfieldInclusion_proj]
  exact MonoidHom.mem_range.2 ⟨_, rfl⟩

theorem psl_core {n : ℕ} {K : Type} [Field K] [Finite K] (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime)
    {σ : K ≃+* K} (k : Subfield K) (hk : ∀ x, x ∈ k ↔ σ x = x) (hpk : p ∣ Nat.card k - 1) :
    LUCore p (fieldAut n K σ) (linearSubfieldInclusion n k).range := by
  obtain ⟨hsimple, hna⟩ := simple_nonabelian_range_linearSubfieldInclusion hn k
  refine ⟨?_, hsimple, ?_, ?_, fun g hg z hz => psl_normalizes hn k hk g hg z hz⟩
  · rintro _ ⟨z, rfl⟩
    exact (mem_fixSub_iff _ _).2 (fieldAut_linearSubfieldInclusion (fun c hc => (hk c).1 hc) z)
  · push Not at hna
    exact hna
  · obtain ⟨x, hx⟩ := exists_orderOf_prime_range hn hp k hpk
    rw [← hx]
    exact orderOf_dvd_natCard x

theorem psl_LUGood {n : ℕ} {K : Type} [Field K] [Finite K] (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1) (D : Subgroup (MulAut (projectiveSL n K)))
    (hD : IsElemAbelian p D) (hc : Nat.card D = p ^ 2)
    (hinn : D ⊓ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range = ⊥) :
    LUGood p D := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hnot : ¬ D ≤ linearAutGroup n K := by
    intro hle
    have h1 := card_le_mul_card_inf_inner_of_le hn hp D hD hle
    rw [hinn, Subgroup.card_bot, hc] at h1
    nlinarith [hp.two_le]
  obtain ⟨x, hxD, hxL⟩ := SetLike.not_le_iff_exists.1 hnot
  have hx1 : x ≠ 1 := fun h => hxL (by rw [h]; exact one_mem _)
  have hxp : x ^ p = 1 := hD.2 x hxD
  have hord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hxS : x ∈ semilinearAutGroup n K := mem_semilinearAutGroup_of_pow_eq_one hn hp hp2 hxp
  haveI := Fintype.ofFinite K
  obtain ⟨ℓ, hchar, f, hℓ, hcard⟩ := FiniteField.card' K
  haveI : CharP K ℓ := hchar
  have hK : Nat.card K = ℓ ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  obtain ⟨hpf, σ, hσ, ⟨β, -, hxβ⟩, hkcard⟩ :=
    CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.higher_linear_prime_semilinear_field_descent'
      hℓ f.pos hn hK hp x hxS hxL hord
  have hk : ∀ c, c ∈ semilinearFixedSubfield σ ↔ σ c = c := fun c => RingHom.mem_eqLocusField
  have hpow : Nat.card K = (Nat.card (semilinearFixedSubfield σ)) ^ p := by
    rw [hkcard, hK, ← pow_mul, Nat.div_mul_cancel hpf]
  have hpk : p ∣ Nat.card (semilinearFixedSubfield σ) - 1 := dvd_sub_one_of_pow_eq hp hpow hpK
  exact LUGood_of_conj (psl_core hn hp (semilinearFixedSubfield σ) hk hpk) hxD hx1 hxβ

end CFSG.LocalAnalysis.GLTheoremA.YS04LUPSL

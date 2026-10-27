module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7E6ClsC
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7E6Sect

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CatFactsSp4 CFSG.ABGLocalTools

namespace Cat7E6

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag CFSG.DisconnectedInvolutionGraph.Helpers

variable {K : Type} [Field K]

theorem card_map_proj_mul_two [Finite K] (h2 : (2 : K) ≠ 0) {H : Subgroup (StatedSp 2 K)}
    (hle : spScalars 2 K ≤ H) : Nat.card (H.map (proj 2 K)) * 2 = Nat.card H := by
  have hker : ((proj 2 K).subgroupMap H).ker = (spScalars 2 K).subgroupOf H := by
    ext g
    rw [MonoidHom.mem_ker, mem_subgroupOf, ← ker_proj, MonoidHom.mem_ker]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hk2 : Nat.card ((proj 2 K).subgroupMap H).ker = 2 := by
    rw [hker, Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, card_spScalars h2]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ((proj 2 K).subgroupMap H).ker, hk2,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ((proj 2 K).subgroupMap H)
      ((proj 2 K).subgroupMap_surjective H)).toEquiv]

abbrev projConj : StatedSp 2 K →* MulAut (StatedProj (StatedSp 2 K)) :=
  (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut _).comp (proj 2 K)

theorem projConj_apply (x : StatedSp 2 K) : projConj x = conjAut 2 K (spG x) :=
  (conjAut_spG x).symm

theorem projConj_eq_one_iff [Finite K] (hodd : Odd (Nat.card K)) {x : StatedSp 2 K} :
    projConj x = 1 ↔ x ∈ spScalars 2 K := by
  have hc : ∀ z : StatedProj (StatedSp 2 K), z ∈ center _ → z = 1 :=
    fun z hz => center_P_eq_one hodd hz
  rw [← ker_proj, MonoidHom.mem_ker]
  constructor
  · intro h
    exact conj_injective_of_center hc (h.trans (map_one _).symm)
  · intro h
    change MulAut.conj (proj 2 K x) = 1
    rw [h, map_one]

theorem card_D_eq [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (c : Cat8.QConf (StatedProj (StatedSp 2 K)) (p ^ f)) {m c' : ℕ}
    (hc' : Odd c') (hqm : Nat.card K ^ 2 - 1 = 2 ^ m * c') : Nat.card c.D = 2 ^ m := by
  have hodd : Odd (Nat.card K) := odd_card_of_card_eq hp hp2 hK
  set q := Nat.card K with hqdef
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (Nat.card_pos.ne')
  obtain ⟨d, hd, hqd⟩ := sq_add_one_eq hodd
  obtain ⟨A, hA, d₀, hd0, hdsq, hAA, hμ⟩ := admissible_data hp hp2 hf (hqdef ▸ hK) c.adm
  obtain ⟨hQ, hcardC⟩ := fixOf_conjSp_nonsquare hp hp2 hf (hqdef ▸ hK) A hd0 hdsq hAA hμ
  have hL0 := card_L0 hodd A hQ.1
  rw [hcardC, ← hA] at hL0
  have hL0' : Nat.card (Cat8.L0 (StatedProj (StatedSp 2 K)) c.a) = 2 ^ m * (q ^ 2 * c' * d) := by
    have e : (p ^ f) ^ 2 * (((p ^ f) ^ 2) ^ 2 - 1) = (2 ^ m * (q ^ 2 * c' * d)) * 2 := by
      rw [← hK, show (q ^ 2) ^ 2 = q ^ 4 by ring, pow_four_sub_one hq1, hqm, hqd]
      ring
    rw [e] at hL0
    exact Nat.eq_of_mul_eq_mul_right two_pos hL0
  rw [(isSylowOf_D c).card_eq, hL0', factorization_two_pow_mul_odd
    (((hodd.pow).mul hc').mul hd)]

theorem exists_YZ [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (c : Cat8.QConf (StatedProj (StatedSp 2 K)) (p ^ f))
    {A : gsp 2 K} (hA : c.a = conjAut 2 K A) {d : K} (hd0 : d ≠ 0) (hdsq : ∀ l : K, l ^ 2 ≠ d)
    (hAA : mat A * mat A = d • 1) (hμ : (mat A)ᵀ * formJ 2 K * mat A = d • formJ 2 K) :
    ∃ Y Z : StatedSp 2 K, c.tau = conjAut 2 K (spG Y) ∧ c.z = conjAut 2 K (spG Z) ∧
      smat Y * smat Y = -1 ∧ smat Z * smat Z = -1 ∧ smat Y * mat A = -(mat A * smat Y) ∧
      smat Z * mat A = mat A * smat Z ∧ smat Z * smat Y = smat Y * smat Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card K) := odd_card_of_card_eq hp hp2 hK
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hc : ∀ z : StatedProj (StatedSp 2 K), z ∈ center _ → z = 1 :=
    fun z hz => center_P_eq_one hodd hz
  obtain ⟨hQs, -⟩ := fixOf_conjSp_nonsquare hp hp2 hf hK A hd0 hdsq hAA hμ
  have hperf := hQs.1
  obtain ⟨Y, hY, hYY, hYA⟩ := exists_Y hodd c hA hd0 hdsq hAA hμ
  obtain ⟨Z, hZC, hZ, hZZ⟩ := exists_Z hodd c hA hd0 hdsq hAA hμ hperf
  have hZA := smat_comm_of_mem_fixOf A hZC
  refine ⟨Y, Z, hY, hZ, hYY, hZZ, hYA, hZA, ?_⟩
  set Dt : Subgroup (StatedSp 2 K) := fixOf (conjSp 2 K A) ⊓ c.D.comap projConj
  have hsc : spScalars 2 K ≤ Dt := by
    intro x hx
    refine ⟨conjSp_scalar A hx, ?_⟩
    change projConj x ∈ c.D
    rw [(projConj_eq_one_iff hodd).mpr hx]
    exact one_mem _
  have hmap : Dt.map projConj = c.D := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (mem_inf.mp hx).2
    · intro w hw
      have hwL : w ∈ Cat8.L0 (StatedProj (StatedSp 2 K)) c.a := (mem_inf.mp hw).2
      rw [hA, L0_eq_map hodd A hperf] at hwL
      obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hwL
      exact ⟨x, mem_inf.mpr ⟨hx, hw⟩, rfl⟩
  obtain ⟨m, c', -, -, hm3, hc', hqm, -, -, -⟩ := exists_uv hodd
  have hD := card_D_eq hp hp2 hf hK c hc' hqm
  have hcard : Nat.card Dt = 2 ^ (m + 1) := by
    have h1 := card_map_proj_mul_two h2 hsc
    have e : Dt.map projConj = (Dt.map (proj 2 K)).map MulAut.conj := (Subgroup.map_map _ _ _).symm
    have e2 : Nat.card c.D = Nat.card (Dt.map (proj 2 K)) := by
      rw [← hmap, e, Subgroup.card_map_of_injective
        (fun g h hgh => conj_injective_of_center hc hgh)]
    rw [← h1, ← e2, hD, pow_succ]
  have h16 : 16 ≤ Nat.card Dt := by
    rw [hcard]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hDt2 : IsPGroup 2 Dt := IsPGroup.of_card hcard
  have hinv : ∀ t : Dt, orderOf t = 2 → smat (t : StatedSp 2 K) = -1 := by
    intro t ht
    have ht2 : t * t = 1 := by
      have h3 := pow_orderOf_eq_one t
      rw [ht, sq] at h3
      exact h3
    have hne : t ≠ 1 := by
      intro h
      rw [h, orderOf_one] at ht
      norm_num at ht
    have hTT : smat (t : StatedSp 2 K) * smat (t : StatedSp 2 K) = 1 :=
      congrArg (fun x : Dt => smat (x : StatedSp 2 K)) ht2
    rcases eq_one_or_neg_of_commute_typeII h2 hd0 hdsq hAA hμ t hTT
      (smat_comm_of_mem_fixOf A (mem_inf.mp t.2).1) with h | h
    · exact (hne (Subtype.ext (Subtype.ext (Units.ext h)))).elim
    · exact h
  have hrank : NoCommutingDistinctInvolutions Dt := by
    intro t₁ t₂ _
    exact Subtype.ext (Subtype.ext (Subtype.ext (Units.ext
      ((hinv _ t₁.2).trans (hinv _ t₂.2).symm))))
  have hZD : Z ∈ Dt := mem_inf.mpr ⟨hZC, by
    change projConj Z ∈ c.D
    rw [projConj_apply, ← hZ]
    exact c.z_mem⟩
  set Z₀ : Dt := ⟨Z, hZD⟩
  have hZ₀c : (Z₀ : StatedSp 2 K) = Z := rfl
  have hZ4 : Z₀ ^ 4 = 1 := by
    have e : Z₀ ^ 4 = (Z₀ * Z₀) * (Z₀ * Z₀) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e]
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    change smat Z * smat Z * (smat Z * smat Z) = 1
    rw [hZZ, Matrix.neg_mul, Matrix.one_mul, neg_neg]
  have hcomm : ∀ y : Dt, (Z₀ * y * Z₀⁻¹ * y⁻¹) ^ 2 = 1 := by
    intro y
    have hyD : projConj (y : StatedSp 2 K) ∈ c.Q ⊓ Cat8.L0 _ c.a := (mem_inf.mp y.2).2
    have h1 : projConj ((Z₀ * y * Z₀⁻¹ * y⁻¹ : Dt) : StatedSp 2 K) = 1 := by
      have h3 : projConj Z = c.z := by rw [projConj_apply, hZ]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hZ₀c, h3]
      rw [c.z_comm _ hyD, mul_inv_cancel_right, mul_inv_cancel]
    have h1' : smat ((Z₀ * y * Z₀⁻¹ * y⁻¹ : Dt) : StatedSp 2 K) = 1 ∨
        smat ((Z₀ * y * Z₀⁻¹ * y⁻¹ : Dt) : StatedSp 2 K) = -1 :=
      (mem_spScalars_iff _).mp ((projConj_eq_one_iff hodd).mp h1)
    rw [sq]
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    change smat ((Z₀ * y * Z₀⁻¹ * y⁻¹ : Dt) : StatedSp 2 K) *
      smat ((Z₀ * y * Z₀⁻¹ * y⁻¹ : Dt) : StatedSp 2 K) = 1
    rcases h1' with h | h
    · rw [h, Matrix.one_mul]
    · rw [h, Matrix.neg_mul, Matrix.one_mul, neg_neg]
  obtain ⟨W, hW⟩ := exists_sq_eq_of_unique_involution hDt2 hrank h16 hZ4 hcomm
  have hZW : smat Z = smat (W : StatedSp 2 K) * smat (W : StatedSp 2 K) := by
    rw [sq] at hW
    exact congrArg (fun x : Dt => smat (x : StatedSp 2 K)) hW
  have hWQ : projConj (W : StatedSp 2 K) ∈ c.Q := (mem_inf.mp (mem_inf.mp W.2).2).1
  have hτ : c.tau = projConj Y := by rw [projConj_apply]; exact hY
  have hτW := tau_comm c hWQ
  rw [hτ] at hτW
  have h1 : projConj (Y * (W : StatedSp 2 K) * Y⁻¹ * (W : StatedSp 2 K)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hτW, mul_inv_cancel_right, mul_inv_cancel]
  have h1' : smat (Y * (W : StatedSp 2 K) * Y⁻¹ * (W : StatedSp 2 K)⁻¹) = 1 ∨
      smat (Y * (W : StatedSp 2 K) * Y⁻¹ * (W : StatedSp 2 K)⁻¹) = -1 :=
    (mem_spScalars_iff _).mp ((projConj_eq_one_iff hodd).mp h1)
  have hu : Y * (W : StatedSp 2 K) =
      (Y * (W : StatedSp 2 K) * Y⁻¹ * (W : StatedSp 2 K)⁻¹) * ((W : StatedSp 2 K) * Y) := by
    group
  have hu' : smat Y * smat (W : StatedSp 2 K) =
      smat (Y * (W : StatedSp 2 K) * Y⁻¹ * (W : StatedSp 2 K)⁻¹) *
        (smat (W : StatedSp 2 K) * smat Y) := congrArg smat hu
  set Wm := smat (W : StatedSp 2 K)
  set Ym := smat Y
  rw [hZW]
  rcases h1' with h | h
  · rw [h, Matrix.one_mul] at hu'
    calc Wm * Wm * Ym = Wm * (Wm * Ym) := Matrix.mul_assoc _ _ _
      _ = Wm * (Ym * Wm) := by rw [hu']
      _ = Wm * Ym * Wm := (Matrix.mul_assoc _ _ _).symm
      _ = Ym * Wm * Wm := by rw [hu']
      _ = Ym * (Wm * Wm) := Matrix.mul_assoc _ _ _
  · rw [h, Matrix.neg_mul, Matrix.one_mul] at hu'
    calc Wm * Wm * Ym = Wm * (Wm * Ym) := Matrix.mul_assoc _ _ _
      _ = Wm * (-(Ym * Wm)) := by rw [hu', neg_neg]
      _ = -(Wm * Ym * Wm) := by rw [Matrix.mul_neg, Matrix.mul_assoc]
      _ = Ym * Wm * Wm := by rw [hu', Matrix.neg_mul]
      _ = Ym * (Wm * Wm) := Matrix.mul_assoc _ _ _

end Cat7E6

end CFSG.ComponentClassification.GSThmB

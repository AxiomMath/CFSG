module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29Ud
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29Ua
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29Lf
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PUt

public section

namespace CFSG.ComponentClassification.GSThmB.P29

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ComponentClassification.CatFactsL4U4
  UnitaryOut UnitaryConj HBlocks StabU DiagU CSU ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank

namespace U4M

variable {p f : ℕ} {K : Type} [Field K]

theorem exists_zw (h : UnitaryFieldData p f K) (hq : p ^ f % 4 = 1) {m : ℕ} (hm : 1 ≤ m)
    (hm1 : 2 ^ m ∣ p ^ f - 1) (hm2 : ¬ 2 ^ (m + 1) ∣ p ^ f - 1) {l : K} (hl : l ^ 2 = -1) :
    ∃ z w : K, z * w = 1 ∧ h.bar z = -z ∧ h.bar w = -w ∧
      (z ^ 2 ^ (m - 1) = l ∨ z ^ 2 ^ (m - 1) = -l) := by
  classical
  have : Finite K := h.finite
  have hq1 : 1 < p ^ f := Nat.one_lt_pow (by have := h.one_le; omega) h.prime.one_lt
  have hK : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hKu : Nat.card Kˣ = (p ^ f) ^ 2 - 1 := by rw [Nat.card_units, hK]
  have hdvd : 2 ^ (m + 1) ∣ (p ^ f) ^ 2 - 1 := by
    have e : (p ^ f) ^ 2 - 1 = (p ^ f - 1) * (p ^ f + 1) := by
      zify [(by omega : 1 ≤ p ^ f), Nat.one_le_pow 2 (p ^ f) (by omega)]
      ring
    rw [e, pow_succ]
    exact Nat.mul_dvd_mul hm1 (by omega)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hog : orderOf g = (p ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hKu]
  have hog0 : orderOf g ≠ 0 := by
    rw [hog]
    have : 4 ≤ (p ^ f) ^ 2 := by nlinarith
    omega
  obtain ⟨z, hoz⟩ : ∃ z : Kˣ, orderOf z = 2 ^ (m + 1) :=
    ⟨_, orderOf_pow_orderOf_div hog0 (by rw [hog]; exact hdvd)⟩
  have hz2 : (z : K) ^ 2 ^ m = -1 := by
    have h1 : (z : K) ^ 2 ^ m * (z : K) ^ 2 ^ m = 1 := by
      rw [← pow_add, ← two_mul, ← pow_succ', ← Units.val_pow_eq_pow_val, ← hoz,
        pow_orderOf_eq_one, Units.val_one]
    rcases mul_self_eq_one_iff.mp h1 with h | h
    · exfalso
      have h' : z ^ 2 ^ m = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
      have h3 := Nat.le_of_dvd (pow_pos two_pos _) (hoz ▸ orderOf_dvd_of_pow_eq_one h')
      have h4 := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (Nat.lt_succ_self m)
      omega
    · exact h
  have hzq : h.bar (z : K) = -z := by
    rw [h.bar_apply]
    obtain ⟨u, hu⟩ := hm1
    have hu_odd : Odd u := by
      rcases Nat.even_or_odd u with ⟨v, hv⟩ | hodd
      · exfalso
        exact hm2 ⟨v, by rw [hu, hv, pow_succ]; ring⟩
      · exact hodd
    have e : p ^ f = 2 ^ m * u + 1 := by rw [← hu]; omega
    rw [e, pow_succ, pow_mul, hz2, hu_odd.neg_one_pow, neg_one_mul]
  refine ⟨z, ((z⁻¹ : Kˣ) : K), by rw [← Units.val_mul, mul_inv_cancel, Units.val_one], hzq, ?_, ?_⟩
  · rw [Units.val_inv_eq_inv_val, map_inv₀, hzq, inv_neg]
  · have hi : (z : K) ^ 2 ^ (m - 1) * (z : K) ^ 2 ^ (m - 1) = l * l := by
      rw [← pow_add, ← two_mul, ← pow_succ', show m - 1 + 1 = m by omega, hz2, ← sq, hl]
    have h2 : ((z : K) ^ 2 ^ (m - 1) - l) * ((z : K) ^ 2 ^ (m - 1) + l) = 0 := by
      linear_combination hi
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact Or.inl (sub_eq_zero.mp h3)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h3)

end U4M

theorem cf82Prop29U4Corr : CF82Prop29U4Corr := by
  intro H _ _ p f hp hp2 hf _ hC hU hq1 ι hιF hι J₁ hJC hJ hJt S₁ hS
  classical
  have : (generalizedFitting H).Normal :=
    (LocalCores.generalized_fitting_characteristic (G := H)).2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, _, h, -, hJF, hO, hcard, e, Y, P, l, hek, hbl, hP, hYP, hJK⟩ :=
    exists_std_U4 hp hp2 hf hC hU hιF hι hJC hJ hJt
  have : Finite K := h.finite
  have hqodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hq3' : 3 ≤ (p ^ f) := by
    have : 1 < (p ^ f) := Nat.one_lt_pow (by omega) hp.one_lt
    obtain ⟨t, ht⟩ := hqodd
    omega
  have hl4 : l ^ 4 = 1 := by
    have hdet : ((Y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 :=
      ((mem_unitarySU_iff h).1 Y.2).1
    have h1 := congrArg Matrix.det hYP
    rw [Matrix.det_mul, Matrix.det_mul, hdet, one_mul, CSU.det_X1] at h1
    have hP0 : (P : Matrix (Fin 4) (Fin 4) K).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).1 P.isUnit).ne_zero
    exact (mul_right_eq_self₀.mp h1.symm).resolve_right hP0
  have hbl' : h.bar l = l := by
    rw [h.bar_apply]
    obtain ⟨s, hs⟩ : ∃ s, p ^ f = 4 * s + 1 := ⟨p ^ f / 4, by omega⟩
    rw [hs, pow_succ, pow_mul, hl4, one_pow, one_mul]
  have hl : l ^ 2 = -1 := by
    rw [hbl'] at hbl
    rw [sq]
    exact hbl
  set m := padicValNat 2 ((p ^ f) - 1) with hmdef
  have hm1 : 2 ^ m ∣ (p ^ f) - 1 := pow_padicValNat_dvd
  have hm2 : ¬ 2 ^ (m + 1) ∣ (p ^ f) - 1 := pow_succ_padicValNat_not_dvd (by omega)
  have hm : 2 ≤ m := (padicValNat_dvd_iff_le (by omega)).mp (by norm_num; omega)
  have hv1 : padicValNat 2 ((p ^ f) + 1) = 1 := by
    rw [← Nat.factorization_def _ Nat.prime_two]
    exact factorization_two_eq (by omega) (by norm_num; omega) (by norm_num; omega)
  have hv2 : padicValNat 2 ((p ^ f) ^ 2 - 1) = m + 1 := by
    have e2 : (p ^ f) ^ 2 - 1 = ((p ^ f) - 1) * ((p ^ f) + 1) := by
      zify [(by omega : 1 ≤ (p ^ f)), Nat.one_le_pow 2 (p ^ f) (by omega)]
      ring
    rw [e2, padicValNat.mul (by omega) (by omega), hv1]
  have hFcard : Nat.card ↥(generalizedFitting H) = Open.ordTwistedA 3 (p ^ f) :=
    GH74.card_of_lieModel_PSU (by norm_num) hp2 hU
  have hvF : padicValNat 2 (Nat.card ↥(generalizedFitting H)) = 2 * m + 3 := by
    rw [hFcard, P211.v2_ordTwistedA_three hqodd hq3' (by omega), hv2]
    ring
  have hPc : Nat.card (StatedProj (StatedSU 4 (p ^ f) K)) =
      Nat.card ↥(generalizedFitting H) := (Nat.card_congr e.toEquiv).symm
  have hL1 : 2 ^ (2 * m + 3) ∣ Nat.card (StatedProj (StatedSU 4 (p ^ f) K)) := by
    rw [hPc, ← hvF]
    exact pow_padicValNat_dvd
  have hL2 : ¬ 2 ^ (2 * m + 4) ∣ Nat.card (StatedProj (StatedSU 4 (p ^ f) K)) := by
    rw [hPc, show 2 * m + 4 = padicValNat 2 (Nat.card ↥(generalizedFitting H)) + 1 by omega]
    exact pow_succ_padicValNat_not_dvd Nat.card_pos.ne'
  have hJK' : (J₁.subgroupOf (generalizedFitting H)).map e.toMonoidHom = U4M.JU Y := hJK
  have hJcard : Nat.card (U4M.JU Y) = Nat.card J₁ := by
    rw [← hJK', Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJF).toEquiv]
  have hJc : (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) ≤ 2 * Nat.card (U4M.JU Y) := by
    rw [hJcard, hcard]
  have h4 : (p ^ f) ^ 4 - 1 ≠ 0 := by
    have : 1 < (p ^ f) ^ 4 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have hJ2 : ¬ 2 ^ (m + 2) ∣ Nat.card (U4M.JU Y) := by
    rw [hJcard]
    intro hd
    have h' : 2 ^ (m + 3) ∣ (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) := by
      rw [← hcard, show m + 3 = (m + 2) + 1 by ring, pow_succ, mul_comm (2 ^ (m + 2))]
      exact Nat.mul_dvd_mul_left 2 hd
    have hv : padicValNat 2 ((p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1)) = m + 2 := by
      rw [padicValNat.mul (by positivity) h4, padicValNat.pow (p ^ f) 2, P211.v2_odd hqodd,
        P211.v2_four hqodd hq3', hv2]
      ring
    have := pow_succ_padicValNat_not_dvd (p := 2) (n := (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1))
      (Nat.mul_ne_zero (by positivity) h4)
    rw [hv] at this
    exact this h'
  have hJp : ⁅J₁, J₁⁆ = J₁ := P211.commutator_eq_of_isPComp hJC hJ
  have hJp' : ⁅U4M.JU Y, U4M.JU Y⁆ = U4M.JU Y := by
    rw [← hJK', ← Subgroup.map_commutator, AZ.subgroupOf_perfect hJF hJp]
  have φ : ↥J₁ ≃* ↥(U4M.JU Y) :=
    (Subgroup.subgroupOfEquivOfLe hJF).symm.trans
      ((Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hJK'))
  have hJZ : U4M.JU Y ⊓ centralizer (U4M.JU Y : Set (StatedProj (StatedSU 4 (p ^ f) K))) = ⊥ :=
    inf_centralizer_eq_bot (center_eq_bot_of_mulEquiv φ (center_eq_bot_of_sec8 hp hp2 hf hO hJt))
  obtain ⟨z, w, hzw, hbz, hbw, hzl⟩ := U4M.exists_zw h hq1 (m := m) (by omega) hm1 hm2 hl
  obtain ⟨M⟩ := U4M.nonempty_modelU h hp2 hq1 P hP hl hbl' hYP hzw hbz hbw hm hzl hJp' hJc hJZ
    hL1 hL2 hJ2
  set ψ : StatedProj (StatedSU 4 (p ^ f) K) →* H :=
    (generalizedFitting H).subtype.comp e.symm.toMonoidHom with hψ
  have hψinj : Function.Injective ψ :=
    (generalizedFitting H).subtype_injective.comp e.symm.injective
  have hψr : ψ.range = generalizedFitting H := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact (e.symm w).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp [hψ]⟩
  have hψι : ψ (thU p f K Y) = ι := by
    rw [hψ, MonoidHom.comp_apply, ← hek]
    simp
  have hψJ : (U4M.JU Y).map ψ = J₁ := by
    rw [← hJK']
    ext x
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      simpa [hψ] using Subgroup.mem_subgroupOf.mp hw
    · intro hx
      exact ⟨e ⟨x, hJF hx⟩, ⟨⟨x, hJF hx⟩, hx, rfl⟩, by simp [hψ]⟩
  exact prop29ConclCorr_of_map M ψ hψinj hψr hψι hψJ hO hS

end CFSG.ComponentClassification.GSThmB.P29

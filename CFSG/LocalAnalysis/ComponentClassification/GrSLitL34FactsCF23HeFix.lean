module

public import Certificates.Certificate22227
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23Cover
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Real
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23HeModelQ
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealB

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.CF23L34

open CFSG Subgroup CFSG.QuasithinUnique.Setup.X1 CFSG.Monster.B.Co2
open CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
  CFSG.ComponentClassification.GrSLit.L34Facts.Real

theorem hjFixParts {i t : ℕ} (hi : i < 36) (ht : t < 64)
    (h2 : sq1M t i = true) (hτ : eqC2 (betaYM t i hjTau) hjTau = true) : hjFixM t i = true := by
  have h := Certificates.certificate22227
  simp only [hjFixOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h i hi t ht with (h' | h') | h'
  · rw [h2] at h'
    exact absurd h' (by decide)
  · rw [hτ] at h'
    exact absurd h' (by decide)
  · exact h'


theorem hjZt_pow_eq_one_iff (p q : ℕ) :
    hjZP ^ p * heGenPerm 0 ^ q = 1 ↔ p % 2 = 0 ∧ q % 2 = 0 := by
  have ht : heGenPerm 0 * heGenPerm 0 = 1 := by rw [← sq]; exact heGen0_sq
  rw [pow_eq_pow_mod_two hjZP_mul_self, pow_eq_pow_mod_two ht]
  rcases Nat.mod_two_eq_zero_or_one p with h1 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one q with h2 | h2 <;>
    simp only [h1, h2, pow_zero, pow_one, one_mul, mul_one, and_true, one_ne_zero, and_false,
      iff_false]
  · exact heA0_ne_one
  · exact hjZP_ne_one
  · intro h
    apply hjZP_ne_t
    calc hjZP = hjZP * heGenPerm 0 * heGenPerm 0 := by rw [mul_assoc, ht, mul_one]
      _ = heGenPerm 0 := by rw [h, one_mul]

theorem coe_zz_hj (i j : ZMod 4) :
    ((zz hjL i j : ↥hjJ) : Equiv.Perm (Fin 8330)) = hjZP ^ i.val * heGenPerm 0 ^ j.val := by
  rw [zz, psi_apply, toAdd_ofAdd, toAdd_ofAdd, Subgroup.coe_mul, Subgroup.coe_pow,
    Subgroup.coe_pow, coe_hjL, coe_hjL, hjLam_z₂]

theorem zz_hj_eq_one_iff (i j : ZMod 4) :
    zz hjL i j = 1 ↔ i.val % 2 = 0 ∧ j.val % 2 = 0 := by
  rw [← hjZt_pow_eq_one_iff, ← coe_zz_hj]
  exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩

theorem nfM_hj_eq_iff {x y : MElt} (hx : x.1 < 64)
    (hy : y.1 < 64) : nfM hjL x = nfM hjL y ↔ eqC2 x y = true := by
  rw [nfM, nfM, nf_eq_iff isQSetting_hj hx hy, zz_hj_eq_one_iff, eqC2]
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc]

theorem coe_nfM_hj (x : MElt) : ((nfM hjL x : ↥hjJ) : Equiv.Perm (Fin 8330)) =
    hjLam (cv (tw x.1)) * (hjZP ^ x.2.1.val * heGenPerm 0 ^ x.2.2.val) := by
  rw [nfM, nf, Subgroup.coe_mul, coe_hjL, coe_zz_hj]

theorem coe_nfM_label {l : ℕ × ℕ × ℕ × ℤ} (hl : l ∈ hjLabels) :
    ((nfM hjL (l.1, (l.2.1 : ZMod 4), (l.2.2.1 : ZMod 4)) : ↥hjJ) : Equiv.Perm (Fin 8330)) =
      hjNFP l.1 l.2.1 l.2.2.1 := by
  have v1 : (1 : ZMod 4).val = 1 := rfl
  simp only [hjLabels, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl <;> rw [coe_nfM_hj] <;> simp [hjNFP, v1, mul_assoc]

theorem coe_nfM_hjTau : ((nfM hjL hjTau : ↥hjJ) : Equiv.Perm (Fin 8330)) = heGenPerm 0 := by
  rw [coe_nfM_hj]
  have h0 : tw 0 = [] := by decide
  have h1 : hjLam (cv []) = 1 := map_one hjLam
  have v1 : (1 : ZMod 4).val = 1 := rfl
  simp only [hjTau, h0, h1, v1, ZMod.val_zero, pow_zero, pow_one, one_mul]

theorem exists_label_fixed
    {β : ↥hjJ ≃* ↥hjJ} (hβ2 : ∀ e, β (β e) = e) (hβT : ∀ e, hjQ e ∈ T0 → hjQ (β e) ∈ T0)
    (hβt : β (nfM hjL hjTau) = nfM hjL hjTau) :
    ∃ x : MElt, x.1 < 64 ∧ hjQ (nfM hjL x) ≠ 1 ∧ nfM hjL x * nfM hjL x = 1 ∧
      β (nfM hjL x) = nfM hjL x ∧ ∃ p ∈ heP,
        p * heGenPerm 0 * p⁻¹ = heGenPerm 0 * ((nfM hjL x : ↥hjJ) : Equiv.Perm (Fin 8330)) := by
  obtain ⟨y, hyR, hy⟩ := exists_realization hjQ hjQ_mem_S hjQ_surj β (fun e => by
    rw [ker_hjQ]
    exact mulEquiv_mem_center_iff β e)
  have hyN : ∀ t ∈ T0, y * t * y⁻¹ ∈ T0 := by
    intro t ht
    obtain ⟨e, he⟩ := hjQ_surj t (T0_le_S ht)
    rw [← he, ← hy]
    exact hβT e (he ▸ ht)
  have hy2 : y * y = 1 := by
    have h1 : ∀ e, hjQ ((fun e => β (β e)) e) = (y * y) * hjQ e * (y * y)⁻¹ := fun e => by
      simp only [hy]
      group
    have h2 : ∀ e, hjQ ((fun e => β (β e)) e) = 1 * hjQ e * 1⁻¹ := fun e => by
      simp only [hβ2]
      group
    exact GrS4.realization_unique hjQ_surj (R.mul_mem hyR hyR) R.one_mem h1 h2
  obtain ⟨i, hi, t, ht, rfl, hβt'⟩ := exists_betaRep isQSetting_hj hyR hyN hy
  have hsq := sq1M_of hi hy2
  have hτ64 : hjTau.1 < 64 := by decide
  have hτ : eqC2 (betaYM t i hjTau) hjTau = true := by
    rw [← nfM_hj_eq_iff (betaYM_lt ht hi hτ64) hτ64, ← betaY_nfM isQSetting_hj ht hi hβt' hτ64,
      hβt]
  have hfix := hjFixParts hi ht hsq hτ
  simp only [hjFixM, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hfix
  obtain ⟨x, hx, ⟨hne, hsq'⟩, hbx⟩ := hfix
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
  have hl64 : l.1 < 64 := by
    simp only [hjLabels, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl <;> decide
  refine ⟨(l.1, (l.2.1 : ZMod 4), (l.2.2.1 : ZMod 4)), hl64, ?_, ?_, ?_, hjPerm l.2.2.2,
    hjPerm_mem _, ?_⟩
  · rw [q_nfM isQSetting_hj hl64]
    intro h1
    have h2 := ((tabRep_wordTab (tg l.1)).beq_iff TabRep.idTab).2 h1
    rw [hne] at h2
    exact Bool.false_ne_true h2
  · rw [nfM_mul isQSetting_hj hl64 hl64,
      (nfM_hj_eq_iff (mulM_lt hl64 hl64) (by decide : oneM.1 < 64)).2 hsq', nfM_one]
  · rw [betaY_nfM isQSetting_hj ht hi hβt' hl64]
    exact (nfM_hj_eq_iff (betaYM_lt ht hi hl64) hl64).2 hbx
  · rw [hjLabel_conj hl, coe_nfM_label hl]

end CFSG.ComponentClassification.GSThmB.CF23L34

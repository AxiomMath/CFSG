module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWIsoCount
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWIsoE
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWNon

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real
  CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso CFSG.LieType.Multipliers.L34

theorem typeOf_lt_three {p : ℕ × ℕ} (hp : p ∈ outerInvs) :
    typeOf p.1 p.2 < 3 := by
  obtain ⟨ht, hi, hS, h2⟩ := outer_of_mem hp
  exact wIsoTypeParts.outer _ ht _ hi hS h2

variable {G : Type} [Group G] [Finite G] {J S : Subgroup G} {hSN : S ≤ normalizer (J : Set G)}

namespace WStd

theorem kb_eq_of_card_Z (D : WStd J S hSN) (hS2 : IsPGroup 2 S)
    (h16 : Nat.card ↥(S ⊓ zStarIn J) = 16) : D.kb = kbOfMask 1 := by
  obtain ⟨f⟩ := D.zEquiv hS2
  have hk : Nat.card D.q.ker = 16 := by rw [← Nat.card_congr f.toEquiv, h16]
  let φ : ZMod 4 × ZMod 4 → D.q.ker := fun p => ⟨zz D.l p.1 p.2, zz_mem_ker D.hQ _ _⟩
  have hsurj : Function.Surjective φ := by
    rintro ⟨e, he⟩
    obtain ⟨i, j, rfl⟩ := (mem_ker_iff_zz D.hQ).1 he
    exact ⟨(i, j), rfl⟩
  have hinj := (hsurj.bijective_of_nat_card_le
    (le_of_eq (by rw [hk, Nat.card_prod, Nat.card_zmod]))).1
  have key : ∀ kb ∈ kbList, (∀ i j : ZMod 4, inKB kb i j = true → i = 0 ∧ j = 0) →
      kb = kbOfMask 1 := by decide
  refine key D.kb D.hkbL fun i j hij => ?_
  have h1 : φ (i, j) = φ (0, 0) := Subtype.ext (by
    show zz D.l i j = zz D.l 0 0
    rw [(D.hkb i j).2 hij, zz_zero])
  have := hinj h1
  simp only [Prod.mk.injEq] at this
  exact this

theorem typeOf_eq_zero_of_field (D : WStd J S hSN) {e : G}
    (he : e ∈ S) {t i : ℕ} (hi : i < 36) (hy : (D.ψ ⟨e, he⟩)⁻¹ = yPerm t i)
    (hlab3 : typeOf t i < 3) (hF : HarrisLit.EndB.IsL34Field J e) : typeOf t i = 0 := by
  have hpos : 0 < Nat.card (zStarIn J) := Nat.card_pos
  rcases (show typeOf t i = 0 ∨ typeOf t i = 1 ∨ typeOf t i = 2 by omega) with h | h | h
  · exact h
  · exfalso
    have hc := D.card_conjSet_of_label he hi hy h (by norm_num)
    have h60 : Nat.card ↥(centralizer ({rhoPerm 1} : Set (Equiv.Perm (Fin 42))) ⊓ _) = 60 :=
      PSL3Four.card_C₃
    rw [h60, hF.2.2.2] at hc
    have := Nat.eq_of_mul_eq_mul_right hpos hc
    norm_num at this
  · exfalso
    have hU := D.isL34Unitary_of_label he hF.2.1 hF.2.2.1 hi hy h
    have := Nat.eq_of_mul_eq_mul_right hpos (hU.2.2.2.symm.trans hF.2.2.2)
    norm_num at this

theorem exists_zInvs (D : WStd J S hSN) (hS2 : IsPGroup 2 S) (hkb : D.kb = kbOfMask 1) {a : G}
    (haZ : a ∈ S ⊓ zStarIn J) (ha2 : a * a = 1) (ha1 : a ≠ 1) :
    ∃ z ∈ zInvs, ∃ haJ : a ∈ J, jq J ⟨a, haJ⟩ = nfM D.l z := by
  have hP2 : IsPGroup 2 (S ⊓ J : Subgroup G) := hS2.to_le inf_le_left
  have haJ : a ∈ J := (map_subtype_le _ : zStarIn J ≤ J) (mem_inf.mp haZ).2
  have haP : a ∈ S ⊓ J := mem_inf.mpr ⟨(mem_inf.mp haZ).1, haJ⟩
  have hker : jq J ⟨a, haJ⟩ ∈ D.q.ker := by
    rw [D.hQ.ker]
    exact (mem_zStarIn_iff haJ).1 (mem_inf.mp haZ).2
  obtain ⟨i, j, hij⟩ := (mem_ker_iff_zz D.hQ).1 hker
  have hnf : nfM D.l (0, i, j) = zz D.l i j := by
    have h0 := nf_zero (l := D.l)
    rw [nf, zz_zero, mul_one] at h0
    show D.l (cv (tw 0)) * zz D.l i j = zz D.l i j
    rw [h0, one_mul]
  refine ⟨(0, i, j), ?_, haJ, hij.trans hnf.symm⟩
  have hK : ∀ i' j' : ZMod 4, zz D.l i' j' = 1 → i' = 0 ∧ j' = 0 := fun i' j' h =>
    inKB_zero_iff.mp (hkb ▸ (D.hkb i' j').1 h)
  have h2 : zz D.l (i + i) (j + j) = 1 := by
    rw [← zz_mul, ← hij, ← map_mul,
      show (⟨a, haJ⟩ : ↥J) * ⟨a, haJ⟩ = 1 from Subtype.ext ha2, map_one]
  obtain ⟨hi, hj⟩ := hK _ _ h2
  have h0 : ¬ (i = 0 ∧ j = 0) := by
    rintro ⟨rfl, rfl⟩
    apply ha1
    exact eq_one_of_jq_eq_one inf_le_right hP2 haP (by rw [hij, zz_zero])
  have h4 : ∀ x : ZMod 4, x + x = 0 → x = 0 ∨ x = 2 := by decide
  rcases h4 i hi with rfl | rfl <;> rcases h4 j hj with rfl | rfl
  · exact absurd ⟨rfl, rfl⟩ h0
  all_goals simp [zInvs]

theorem exists_sq_eq_of_field
    (D : WStd J S hSN)
    (hJ : ⁅J, J⁆ = J) (hS2 : IsPGroup 2 S) {b : G} (hb : b ∈ S)
    (hF : HarrisLit.EndB.IsL34Field J b) (h16 : Nat.card ↥(S ⊓ zStarIn J) = 16) {a : G}
    (haZ : a ∈ S ⊓ zStarIn J) (ha2 : a * a = 1) (ha1 : a ≠ 1) (hab : a * b = b * a) :
    ∃ y ∈ S ⊓ J, y * b = b * y ∧ y * y = a := by
  have hkb := D.kb_eq_of_card_Z hS2 h16
  have hP2 : IsPGroup 2 (S ⊓ J : Subgroup G) := hS2.to_le inf_le_left
  have hPJ : S ⊓ J ≤ J := inf_le_right
  obtain ⟨t, ht, i, hi, hy, -, hβ⟩ := D.model hb
  have hp := D.mem_outerInvs hJ hb hF.2.1 hF.2.2.1 ht hi hy
  have hlab := D.typeOf_eq_zero_of_field hb hi hy (typeOf_lt_three hp) hF
  obtain ⟨z, hz, haJ, hae⟩ := D.exists_zInvs hS2 hkb haZ ha2 ha1
  have hz64 : z.1 < 64 := by
    simp only [zInvs, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl <;> norm_num
  have haP : a ∈ S ⊓ J := mem_inf.mpr ⟨(mem_inf.mp haZ).1, haJ⟩
  have hzf : fixKB (kbOfMask 1) t i z = true := by
    rw [← hkb]
    have hba : b⁻¹ * a * b = a := by
      rw [mul_assoc, hab, ← mul_assoc, inv_mul_cancel, one_mul]
    have h1 := (GrS4.conj_eq_iff_betaHat hPJ hP2 (hSN hb) (mem_normalizer_P hSN hb) haP).1 hba
    rw [hae, hβ z hz64] at h1
    exact (eqKB_iff D.hQ D.hkb (betaYM_lt ht hi hz64) hz64).2 h1
  obtain ⟨-, -, hS, h2⟩ := outer_of_mem hp
  obtain ⟨x, hx, hxf, hxz⟩ := fieldSq_spec ht hi hS h2 hlab hz hzf
  have hx64 := lt_of_mem_allM hx
  obtain ⟨y, hyP, hyJ, hye⟩ := exists_inv_of_model D hx
  refine ⟨y, hyP, D.comm_of_fix hS2 hb ht hi hβ hx64 (by rw [hkb]; exact hxf) hyP hye, ?_⟩
  apply eq_of_jq_eq hPJ hP2 (mul_mem hyP hyP) haP
  rw [show (⟨y * y, hPJ (mul_mem hyP hyP)⟩ : ↥J) = ⟨y, hyJ⟩ * ⟨y, hyJ⟩ from rfl, map_mul, hye,
    nfM_mul D.hQ hx64 hx64,
    (eqKB_iff D.hQ D.hkb (mulM_lt hx64 hx64) hz64).1 (by rw [hkb]; exact hxz)]
  exact hae.symm

end WStd

end CFSG.ComponentClassification.GrSLit.GrS5S

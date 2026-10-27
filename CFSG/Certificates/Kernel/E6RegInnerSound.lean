module

public import Certificates.Data.Kernel.E6RegInner
public import CFSG.Certificates.Kernel.E6RegPairSound
public import CFSG.Certificates.Kernel.E6PlaneLinesSound

public section

namespace CFSG.KC.E6RegInner

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.KC.E6RegPair CFSG.KC.E6PlaneLines
  CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagRegular


theorem vec3_combVec (c₁ c₂ : ℕ) (v₁ v₂ : List ℕ) :
    vec3 (τ := .E6) (combVec c₁ c₂ v₁ v₂) =
      (c₁ : ZMod 3) • vec3 (τ := .E6) v₁ + (c₂ : ZMod 3) • vec3 (τ := .E6) v₂ := by
  funext j
  simp only [vec3, combVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [getD_range_map' _ _ j.2, ZMod.natCast_mod]
  push_cast
  rfl

theorem shift_ne_zero_of_e6ScTest {vec t : List ℕ} {w : WeylGroup .E6}
    (hrep : e6Certificate.Represents t w) (h : e6ScTest e6Certificate vec t = true) :
    triPairing (vec3 (τ := .E6) vec) (e6Shift w) ≠ 0 := by
  simp only [e6ScTest, decide_eq_true_eq] at h
  rwa [e6ShiftT_eq hrep] at h

theorem e6ScTest_of_shift_ne_zero {vec t : List ℕ} {w : WeylGroup .E6}
    (hrep : e6Certificate.Represents t w)
    (h : triPairing (vec3 (τ := .E6) vec) (e6Shift w) ≠ 0) :
    e6ScTest e6Certificate vec t = true := by
  simp only [e6ScTest, decide_eq_true_eq]
  rw [e6ShiftT_eq hrep]
  exact h

theorem triPairing_eq_zero_of_mem_killIdx {kvec : List ℕ} {a : ℕ}
    (h : a ∈ killIdx (RootTables.ofCert e6Certificate) e6Certificate.roots.length kvec) :
    triPairing (vec3 (τ := .E6) kvec) (e6Certificate.root a) = 0 := by
  simp only [killIdx, List.mem_filter, List.mem_range, beq_iff_eq] at h
  exact (pairZ_emod_eq_zero_iff' h.1 kvec).1 h.2

theorem root_add_of_sumRootL {a b : ℕ} (ha : a < e6Certificate.roots.length)
    (hb : b < e6Certificate.roots.length)
    (h : sumRootL (RootTables.ofCert e6Certificate) e6Certificate.roots.length a b = true) :
    IsRoot Tag.E6 (e6Certificate.root a + e6Certificate.root b) := by
  simp only [sumRootL, List.any_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨c, hc, hcv⟩ := h
  rw [vecs_getD e6Certificate hc, vecs_getD e6Certificate ha, vecs_getD e6Certificate hb] at hcv
  have : e6Certificate.root c = e6Certificate.root a + e6Certificate.root b := by
    funext i
    have := congrArg (fun l : List ℤ => l[(i : ℕ)]?) hcv
    simpa [List.getElem?_zipWith, List.getElem?_ofFn] using this
  rw [← this]
  exact RootCertificate.isRoot_root e6Certificate_check c hc

theorem exists_a2_of_a2FixedL {kvec t : List ℕ} {w : WeylGroup .E6}
    (hrep : e6Certificate.Represents t w)
    (h : a2FixedL e6Certificate (RootTables.ofCert e6Certificate)
      (killIdx (RootTables.ofCert e6Certificate) e6Certificate.roots.length kvec) t = true) :
    ∃ β₁ β₂ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 β₁ ∧ IsRoot Tag.E6 β₂ ∧ IsRoot Tag.E6 (β₁ + β₂) ∧
      triPairing (vec3 (τ := .E6) kvec) β₁ = 0 ∧ triPairing (vec3 (τ := .E6) kvec) β₂ = 0 ∧
      w • β₁ = β₁ ∧ w • β₂ = β₂ := by
  simp only [a2FixedL, List.any_eq_true, List.mem_filter, Bool.and_eq_true] at h
  obtain ⟨a, ⟨hak, hafix⟩, b, ⟨hbk, hbfix⟩, hsum⟩ := h
  have hakill := hak
  have hbkill := hbk
  simp only [killIdx, List.mem_filter, List.mem_range] at hak hbk
  refine ⟨e6Certificate.root a, e6Certificate.root b,
    RootCertificate.isRoot_root e6Certificate_check a hak.1,
    RootCertificate.isRoot_root e6Certificate_check b hbk.1, root_add_of_sumRootL hak.1 hbk.1 hsum,
    triPairing_eq_zero_of_mem_killIdx hakill, triPairing_eq_zero_of_mem_killIdx hbkill, ?_, ?_⟩
  · rw [← RootCertificate.tupleVec_eq hrep]
    exact List.ofFn_injective (by simpa [fixesIdxL] using hafix)
  · rw [← RootCertificate.tupleVec_eq hrep]
    exact List.ofFn_injective (by simpa [fixesIdxL] using hbfix)

theorem isConj3_comb {a₁ a₂ b₁ b₂ : Fin Tag.E6.rank → ZMod 3} {t : WeylGroup .E6}
    (h₁ : IsConj3 a₁ b₁ t) (h₂ : IsConj3 a₂ b₂ t) (c₁ c₂ : ZMod 3) :
    IsConj3 (c₁ • a₁ + c₂ • a₂) (c₁ • b₁ + c₂ • b₂) t := fun v => by
  rw [triPairing_comb', triPairing_comb', h₁ v, h₂ v]

theorem shift_conj {a b : Fin Tag.E6.rank → ZMod 3} {t w : WeylGroup .E6} (h : IsConj3 a b t)
    (hw : w ∈ charStabilizer (triChar b)) :
    triPairing a (e6Shift (t⁻¹ * w * t)) = triPairing b (e6Shift w) :=
  shift_transport h.isCharConj hw

theorem e6RegularInnerLine_of_checks {rows : List (List ℕ)}
    {ps es : List (ℕ × List ℕ)} (hrows : ∀ ρ < 8, rowOK rows ps ρ = true)
    (hp : partnersOK ps = true) (hs : stabOK es = true) (ho : orbit7OK () = true)
    (hi : innerOK es = true) :
    ∀ (b₁ b₂ : Fin Tag.E6.rank → ZMod 3),
      (∀ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α → ¬ (triPairing b₁ α = 0 ∧ triPairing b₂ α = 0)) →
      ∀ w : WeylGroup Tag.E6, w ∈ charStabilizer (triChar b₁) → w ∈ charStabilizer (triChar b₂) →
        (triPairing b₁ (e6Shift w) ≠ 0 ∨ triPairing b₂ (e6Shift w) ≠ 0) →
        ∀ c₁ c₂ : ZMod 3, (c₁ ≠ 0 ∨ c₂ ≠ 0) →
          triPairing (c₁ • b₁ + c₂ • b₂) (e6Shift w) = 0 →
          ∃ β₁ β₂ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 β₁ ∧ IsRoot Tag.E6 β₂ ∧
            IsRoot Tag.E6 (β₁ + β₂) ∧ triPairing (c₁ • b₁ + c₂ • b₂) β₁ = 0 ∧
            triPairing (c₁ • b₁ + c₂ • b₂) β₂ = 0 ∧ w • β₁ = β₁ ∧ w • β₂ = β₂ := by
  intro b₁ b₂ hreg w hw₁ hw₂ hsh c₁ c₂ hc hk
  obtain ⟨h, h₁, h₂⟩ := regPair_conj hrows hp hreg
  obtain ⟨e, he, -, -, hrep⟩ := stabP_listed hp ho hs (conj_mem h₁ hw₁) (conj_mem h₂ hw₂)
  have hsh₁ := shift_conj h₁ hw₁
  have hsh₂ := shift_conj h₂ hw₂
  have hin : innerTupleOK (RootTables.ofCert e6Certificate)
      (tupleOfWord (RootTables.ofCert e6Certificate) e.2) = true := by
    simp only [innerOK, innerOKWith, List.all_eq_true] at hi
    exact hi e he
  rw [innerTupleOK, Bool.or_eq_true] at hin
  rcases hin with hin | hin
  · have hsc : (e6ScTest e6Certificate r7 (tupleOfWord (RootTables.ofCert e6Certificate) e.2) ||
        e6ScTest e6Certificate c0 (tupleOfWord (RootTables.ofCert e6Certificate) e.2)) = true := by
      rcases hsh with hsh | hsh
      · rw [e6ScTest_of_shift_ne_zero (vec := r7) hrep (by rw [hsh₁]; exact hsh), Bool.true_or]
      · rw [e6ScTest_of_shift_ne_zero (vec := c0) hrep (by rw [hsh₂]; exact hsh), Bool.or_true]
    rw [hsc] at hin
    exact absurd hin (by decide)
  · rw [List.all_eq_true] at hin
    have h4 := hin (c₁.val, c₂.val)
      (List.mem_product.2 ⟨List.mem_range.2 (ZMod.val_lt c₁), List.mem_range.2 (ZMod.val_lt c₂)⟩)
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h4
    have hne : ¬ (c₁.val = 0 ∧ c₂.val = 0) := by
      rintro ⟨e1, e2⟩
      rcases hc with hc | hc
      · exact hc ((ZMod.val_eq_zero c₁).1 e1)
      · exact hc ((ZMod.val_eq_zero c₂).1 e2)
    have hkP : vec3 (τ := .E6) (combVec c₁.val c₂.val r7 c0) =
        c₁ • vec3 (τ := .E6) r7 + c₂ • vec3 (τ := .E6) c0 := by
      rw [vec3_combVec, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    have hconj := isConj3_comb h₁ h₂ c₁ c₂
    have hkw : triPairing (vec3 (τ := .E6) (combVec c₁.val c₂.val r7 c0))
        (e6Shift (h⁻¹ * w * h)) = 0 := by
      rw [hkP, triPairing_comb', hsh₁, hsh₂, ← triPairing_comb']
      exact hk
    rcases h4 with h4 | h4 | h4
    · exact absurd h4 hne
    · exact absurd hkw (shift_ne_zero_of_e6ScTest hrep h4)
    · obtain ⟨β₁, β₂, r₁, r₂, r₁₂, k₁, k₂, f₁, f₂⟩ := exists_a2_of_a2FixedL hrep h4
      rw [hkP] at k₁ k₂
      refine ⟨h • β₁, h • β₂, IsRoot.smul r₁ h, IsRoot.smul r₂ h, ?_, ?_, ?_, ?_, ?_⟩
      · rw [← smul_add]
        exact IsRoot.smul r₁₂ h
      · rw [← hconj.apply]
        exact k₁
      · rw [← hconj.apply]
        exact k₂
      · have := congrArg (h • ·) f₁
        simp only [mul_smul, smul_inv_smul] at this
        exact this
      · have := congrArg (h • ·) f₂
        simp only [mul_smul, smul_inv_smul] at this
        exact this

end CFSG.KC.E6RegInner

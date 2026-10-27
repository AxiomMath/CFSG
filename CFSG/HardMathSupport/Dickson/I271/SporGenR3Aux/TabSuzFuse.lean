module

public import Certificates.Certificate17320
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzDefs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzThree

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
  CFSG.HardMathSupport.Dickson.I271.TabSuzFuse
open CFSG.Sporadic.SuzOddCore (suzM)

section Reps

@[expose] noncomputable def fuseXA : Equiv.Perm (Fin 1782) :=
  permOfArr 1782 (xAArr (levels ()))

@[expose] noncomputable def fuseXB : Equiv.Perm (Fin 1782) :=
  permOfArr 1782 (xBArr (levels ()))

end Reps

section Fuse


theorem fuseCheck_parts :
    (validA 1782 (xAArr (levels ())) = true ∧ inP (levels ()) (xAArr (levels ())) = true ∧
      eqA 1782 (powArr 1782 (xAArr (levels ())) 3) (idA 1782) = true ∧
      eqA 1782 (xAArr (levels ())) (idA 1782) = false) ∧
    (validA 1782 (xBArr (levels ())) = true ∧ inP (levels ()) (xBArr (levels ())) = true ∧
      eqA 1782 (powArr 1782 (xBArr (levels ())) 3) (idA 1782) = true ∧
      eqA 1782 (xBArr (levels ())) (idA 1782) = false) ∧
    ∀ k < 243, k ≠ 0 → validA 1782 (fuseArr (levels ()) k) = true ∧
      inP (levels ()) (fuseArr (levels ()) k) = true ∧
      (fuseCls[k]! = 0 → eqA 1782 (conjA 1782 (fuseArr (levels ()) k) (dElts ())[k]!)
        (xAArr (levels ())) = true) ∧
      (fuseCls[k]! ≠ 0 → eqA 1782 (conjA 1782 (fuseArr (levels ()) k) (dElts ())[k]!)
        (xBArr (levels ())) = true) := by
  have h : fuseCheck () = true := Certificates.certificate17320
  simp only [fuseCheck, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ha1, ha2⟩, ha3⟩, ha4⟩, hb1⟩, hb2⟩, hb3⟩, hb4⟩, -⟩, -⟩, hall⟩ := h
  refine ⟨⟨ha1, ha2, ha3, ha4⟩, ⟨hb1, hb2, hb3, hb4⟩, fun k hk hk0 => ?_⟩
  have := allLt_spec hall hk
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at this
  rcases this with h0 | ⟨⟨h1, h2⟩, h3⟩
  · exact absurd h0 hk0
  · exact ⟨h1, h2, fun hc => by rw [if_pos hc] at h3; exact h3,
      fun hc => by rw [if_neg hc] at h3; exact h3⟩

end Fuse

section Classes


theorem rep_fuseXA : Rep 1782 (xAArr (levels ())) fuseXA :=
  rep_of_validA fuseCheck_parts.1.1

theorem rep_fuseXB : Rep 1782 (xBArr (levels ())) fuseXB :=
  rep_of_validA fuseCheck_parts.2.1.1

theorem fuseXA_mem : fuseXA ∈ suzM := mem_suzM_of_inP rep_fuseXA fuseCheck_parts.1.2.1

theorem fuseXB_mem : fuseXB ∈ suzM := mem_suzM_of_inP rep_fuseXB fuseCheck_parts.2.1.2.1

theorem fuseXA_pow : fuseXA ^ 3 = 1 :=
  (eqA_iff (rep_powArr rep_fuseXA 3) rep_idA).1 fuseCheck_parts.1.2.2.1

theorem fuseXB_pow : fuseXB ^ 3 = 1 :=
  (eqA_iff (rep_powArr rep_fuseXB 3) rep_idA).1 fuseCheck_parts.2.1.2.2.1

theorem fuseXA_ne_one : fuseXA ≠ 1 := fun h => by
  have := (eqA_iff rep_fuseXA rep_idA).2 h
  rw [fuseCheck_parts.1.2.2.2] at this
  exact Bool.false_ne_true this

theorem fuseXB_ne_one : fuseXB ≠ 1 := fun h => by
  have := (eqA_iff rep_fuseXB rep_idA).2 h
  rw [fuseCheck_parts.2.1.2.2.2] at this
  exact Bool.false_ne_true this

theorem fuse_sound : ∀ k < 243, k ≠ 0 → ∃ h ∈ suzM,
    h * φ (Multiplicative.ofAdd (vec k)) * h⁻¹ = fuseXA ∨
      h * φ (Multiplicative.ofAdd (vec k)) * h⁻¹ = fuseXB := by
  intro k hk hk0
  obtain ⟨hv, hP, heA, heB⟩ := fuseCheck_parts.2.2 k hk hk0
  have hrep : Rep 1782 (conjA 1782 (fuseArr (levels ()) k) (dElts ())[k]!)
      (permOfArr 1782 (fuseArr (levels ()) k) * φ (Multiplicative.ofAdd (vec k)) *
        (permOfArr 1782 (fuseArr (levels ()) k))⁻¹) := rep_conjA hv (rep_dElts hk)
  refine ⟨permOfArr 1782 (fuseArr (levels ()) k),
    mem_suzM_of_inP (rep_of_validA hv) hP, ?_⟩
  by_cases hc : fuseCls[k]! = 0
  · left
    exact (eqA_iff hrep rep_fuseXA).1 (heA hc)
  · right
    exact (eqA_iff hrep rep_fuseXB).1 (heB hc)

theorem suz_exists_conj_classes {s : Equiv.Perm (Fin 1782)} (hs : s ∈ suzM) (hs3 : orderOf s = 3) :
    ∃ k ∈ suzM, ∃ c : Equiv.Perm (Fin 1782), (c = fuseXA ∨ c = fuseXB ∨ c = yPerm) ∧ ∃ e : ℕ,
      (e = 1 ∨ e = 2) ∧ k * c ^ e * k⁻¹ = s := by
  obtain ⟨h, hh, hcase⟩ := exists_conj_D_or_y hs hs3
  have hhinv : h⁻¹ ∈ suzM := suzM.inv_mem hh
  have hback : h⁻¹ * (h * s * h⁻¹) * h⁻¹⁻¹ = s := by group
  rcases hcase with hD | hy | hy2
  · obtain ⟨a, ha⟩ := hD
    have hk : idx a.toAdd < 243 := idx_lt _
    have hvec : φ (Multiplicative.ofAdd (vec (idx a.toAdd))) = h * s * h⁻¹ := by
      rw [vec_idx]
      exact ha
    have hk0 : idx a.toAdd ≠ 0 := by
      intro h0
      have ha0 : a.toAdd = 0 := (idx_eq_zero_iff _).1 h0
      have : a = 1 := by
        apply Multiplicative.toAdd.injective
        rw [toAdd_one]
        exact ha0
      rw [this, map_one] at ha
      have hs1 : s = 1 := by
        have : h * s * h⁻¹ = 1 := ha.symm
        simpa using this
      rw [hs1, orderOf_one] at hs3
      omega
    obtain ⟨h', hh', hfuse⟩ := fuse_sound _ hk hk0
    rw [hvec] at hfuse
    have hh'inv : h'⁻¹ ∈ suzM := suzM.inv_mem hh'
    refine ⟨h⁻¹ * h'⁻¹, suzM.mul_mem hhinv hh'inv, ?_⟩
    rcases hfuse with hf | hf
    · refine ⟨fuseXA, Or.inl rfl, 1, Or.inl rfl, ?_⟩
      have hinv : h * s * h⁻¹ = h'⁻¹ * fuseXA * h' := by rw [← hf]; group
      calc h⁻¹ * h'⁻¹ * fuseXA ^ 1 * (h⁻¹ * h'⁻¹)⁻¹
          = h⁻¹ * (h'⁻¹ * fuseXA * h') * h := by group
        _ = s := by rw [← hinv]; group
    · refine ⟨fuseXB, Or.inr (Or.inl rfl), 1, Or.inl rfl, ?_⟩
      have hinv : h * s * h⁻¹ = h'⁻¹ * fuseXB * h' := by rw [← hf]; group
      calc h⁻¹ * h'⁻¹ * fuseXB ^ 1 * (h⁻¹ * h'⁻¹)⁻¹
          = h⁻¹ * (h'⁻¹ * fuseXB * h') * h := by group
        _ = s := by rw [← hinv]; group
  · refine ⟨h⁻¹, hhinv, yPerm, Or.inr (Or.inr rfl), 1, Or.inl rfl, ?_⟩
    rw [pow_one, ← hy]
    exact hback
  · refine ⟨h⁻¹, hhinv, yPerm, Or.inr (Or.inr rfl), 2, Or.inr rfl, ?_⟩
    rw [← hy2]
    exact hback

end Classes

section Assembly


theorem centShapeSplit_suzM_of_entries
    (hA : SplitShapeAt 3 (⟨fuseXA, fuseXA_mem⟩ : ↥suzM))
    (hB : SplitShapeAt 3 (⟨fuseXB, fuseXB_mem⟩ : ↥suzM))
    (hY : SplitShapeAt 3 (⟨yPerm, yPerm_mem⟩ : ↥suzM)) :
    CentShapeSplit 3 ↥suzM := by
  intro k hk1 hkp
  have hs3 : orderOf (k : Equiv.Perm (Fin 1782)) = 3 := by
    have h1 : (k : Equiv.Perm (Fin 1782)) ^ 3 = 1 := by
      have := congrArg Subtype.val hkp
      simpa using this
    have h2 : (k : Equiv.Perm (Fin 1782)) ≠ 1 := fun h => hk1 (Subtype.ext h)
    exact orderOf_eq_prime h1 h2
  obtain ⟨h, hh, c, hc, e, he, hcon⟩ := suz_exists_conj_classes k.2 hs3
  have hrep : ∃ c' : ↥suzM, (c' : Equiv.Perm (Fin 1782)) = c ∧ c' ^ 3 = 1 ∧
      SplitShapeAt 3 c' := by
    rcases hc with rfl | rfl | rfl
    · exact ⟨⟨fuseXA, fuseXA_mem⟩, rfl, Subtype.ext (by simpa using fuseXA_pow), hA⟩
    · exact ⟨⟨fuseXB, fuseXB_mem⟩, rfl, Subtype.ext (by simpa using fuseXB_pow), hB⟩
    · exact ⟨⟨yPerm, yPerm_mem⟩, rfl, Subtype.ext (by simpa using yPerm_pow), hY⟩
  obtain ⟨c', hc'val, hc'3, hshape⟩ := hrep
  have hshape' : SplitShapeAt 3 (c' ^ e) := SplitShapeAt.pow hc'3 he hshape
  have hconj := SplitShapeAt.conj Nat.prime_three (⟨h, hh⟩ : ↥suzM) hshape'
  have hk : (⟨h, hh⟩ : ↥suzM) * (c' ^ e) * (⟨h, hh⟩ : ↥suzM)⁻¹ = k := by
    apply Subtype.ext
    rw [← hcon, ← hc'val]
    simp
  rw [hk] at hconj
  exact hconj

end Assembly

end CFSG.HardMathSupport.Dickson.I271

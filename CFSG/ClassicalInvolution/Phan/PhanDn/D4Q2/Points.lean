module

public import CFSG.ClassicalInvolution.Phan.PhanDn.D4Q2.Codes
public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwoHermitian

public section

namespace CFSG.ClassicalInvolution.PhanDn.D4Q2

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Unitary

variable {K : Type} [Field K] [CharP K 2] {σ : K ≃+* K} {ω : K}

private def d4p_coord (k : ℕ) : Fin 4 ⊕ Fin 4 :=
  match k % 8 with
  | 0 => .inl ⟨0, by norm_num⟩
  | 1 => .inl ⟨1, by norm_num⟩
  | 2 => .inl ⟨2, by norm_num⟩
  | 3 => .inl ⟨3, by norm_num⟩
  | 4 => .inr ⟨0, by norm_num⟩
  | 5 => .inr ⟨1, by norm_num⟩
  | 6 => .inr ⟨2, by norm_num⟩
  | _ => .inr ⟨3, by norm_num⟩

private lemma d4p_cidx_coord {k : ℕ} (hk : k < 8) : cidx (d4p_coord k) = k := by
  interval_cases k <;> simp [d4p_coord, cidx]

private lemma d4p_coord_cidx (x : Fin 4 ⊕ Fin 4) : d4p_coord (cidx x) = x := by
  cases x with
  | inl i => fin_cases i <;> simp [cidx, d4p_coord]
  | inr i => fin_cases i <;> simp [cidx, d4p_coord]

private lemma d4p_find?_range_eq_some {p : ℕ → Bool} {k : ℕ} (hk : k < 8)
    (h1 : p k = true) (h0 : ∀ j < k, p j = false) :
    (List.range 8).find? p = some k := by
  have hidx : (List.range 8).findIdx p = k := by
    rw [List.findIdx_eq (by simpa using hk)]
    refine ⟨?_, ?_⟩
    · simpa [List.getElem_range] using h1
    · intro j hj
      have hj8 : j < 8 := by omega
      simpa [List.getElem_range (by simpa [List.length_range] using hj8)] using h0 j hj
  rw [List.find?_eq_getElem?_findIdx, hidx, List.getElem?_range hk]

private lemma d4p_normC_iff {v : ℕ} :
    normC v = true ↔ ∃ k < 8, cd v k = 1 ∧ ∀ j < k, cd v j = 0 := by
  let p : ℕ → Bool := fun k => cd v k != 0
  constructor
  · intro h
    unfold normC at h
    cases hf : (List.range 8).find? p with
    | none => rw [hf] at h; simp at h
    | some k =>
      rw [hf] at h
      simp only at h
      have hk_mem : k ∈ List.range 8 := List.mem_of_find?_eq_some hf
      have hk8 : k < 8 := List.mem_range.mp hk_mem
      have hpk : p k = true := List.find?_some hf
      have hlt : (List.range 8).findIdx p < (List.range 8).length := by
        rw [List.findIdx_lt_length]
        exact ⟨k, hk_mem, hpk⟩
      have hidx : (List.range 8).findIdx p = k := by
        have h1 := List.find?_eq_getElem?_findIdx (xs := List.range 8) (p := p)
        rw [hf, List.getElem?_range (by simpa using hlt)] at h1
        exact (Option.some.inj h1).symm
      refine ⟨k, hk8, ?_, ?_⟩
      · simpa [p] using h
      · intro j hj
        have hfalse := ((List.findIdx_eq (p := p) (xs := List.range 8) (i := k) hk8).mp hidx).2
          j hj
        have hj8 : j < 8 := by omega
        simpa [p, List.getElem_range (by simpa [List.length_range] using hj8)] using hfalse
  · rintro ⟨k, hk8, h1, h0⟩
    have h1' : p k = true := by
      show (cd v k != 0) = true
      rw [h1]
      rfl
    have h0' : ∀ j < k, p j = false := by
      intro j hj
      show (cd v j != 0) = false
      rw [h0 j hj]
      rfl
    have hfind := d4p_find?_range_eq_some hk8 h1' h0'
    unfold normC
    rw [hfind]
    simp [h1]

theorem mem_ptCodes {c : ℕ} :
    c ∈ ptCodes () ↔ c < 65536 ∧ normC c = true ∧ quadC c = 0 ∧ hermC c c ≠ 0 := by
  rw [ptCodes, Array.mem_filter, Array.mem_range]
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, and_assoc]

omit [CharP K 2] in
private lemma d4p_first_coord {v : Fin 4 ⊕ Fin 4 → K} (hv0 : v ≠ 0) :
    ∃ k < 8, v (d4p_coord k) ≠ 0 := by
  by_contra h
  apply hv0
  funext x
  have hx : cidx x < 8 := by cases x <;> simp [cidx] <;> omega
  have hz : v (d4p_coord (cidx x)) = 0 := by
    by_contra hne
    exact h ⟨cidx x, hx, hne⟩
  rwa [d4p_coord_cidx x] at hz

private lemma d4p_vecC_ne_zero {hω : ω * ω = ω + 1} {c : ℕ} (hc1 : c < 65536)
    (hh : hermC c c ≠ 0) : vecC ω c ≠ 0 := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp [hermC, cd] at hh
  exact fun h => hc0 ((vecC_eq_zero_iff hω hc1).mp h)

section Omega

variable (hω : ω * ω = ω + 1) (hσω : σ ω = ω + 1)
include hω hσω

theorem isFlipflopPt_span_vecC {c : ℕ} (hc : c ∈ ptCodes ()) :
    IsFlipflopPt σ (K ∙ vecC ω c) := by
  rw [mem_ptCodes] at hc
  obtain ⟨hc1, -, hq, hh⟩ := hc
  have hvne : vecC ω c ≠ 0 := d4p_vecC_ne_zero (hω := hω) hc1 hh
  rw [isFlipflopPt_span_singleton_iff hvne]
  constructor
  · rw [quadPlus_vecC hω, hq]
    rfl
  · rw [flipHerm_vecC hω hσω]
    intro h
    exact hh ((enc_eq_zero_iff hω (hermC_lt c c)).mp h)

theorem exists_mem_ptCodes [Finite K] (hK : Nat.card K = 4)
    {p : Submodule K (Fin 4 ⊕ Fin 4 → K)} (hp : IsFlipflopPt σ p) :
    ∃ c ∈ ptCodes (), p = K ∙ vecC ω c := by
  classical
  obtain ⟨v, hpv, hvQ, hvh⟩ := hp.exists_eq_span
  have hv0 : v ≠ 0 := fun h => hvh (by rw [h]; simp)
  let pfun : ℕ → Bool := fun k => v (d4p_coord k) != 0
  let k0 := (List.range 8).findIdx pfun
  have hex : ∃ k < 8, pfun k = true := by
    obtain ⟨k, hk, hne⟩ := d4p_first_coord hv0
    exact ⟨k, hk, by simp [pfun, hne]⟩
  have hk0 : k0 < 8 := by
    have h : (List.range 8).findIdx pfun < (List.range 8).length := by
      rw [List.findIdx_lt_length]
      obtain ⟨k, hk, hpk⟩ := hex
      exact ⟨k, List.mem_range.mpr hk, hpk⟩
    simpa using h
  have hk0len : (List.range 8).findIdx pfun < (List.range 8).length := by
    simpa using hk0
  have hpk0 : pfun k0 = true := by
    have h := List.findIdx_getElem (p := pfun) (xs := List.range 8) (w := hk0len)
    simpa [k0, List.getElem_range (by simpa [List.length_range] using hk0)] using h
  have hbefore : ∀ j < k0, pfun j = false := by
    intro j hj
    have h := List.not_of_lt_findIdx (p := pfun) (xs := List.range 8)
      (i := j) (by simpa [k0] using hj)
    have hj8 : j < 8 := by omega
    simpa [List.getElem_range (by simpa [List.length_range] using hj8)] using h
  have hvk0 : v (d4p_coord k0) ≠ 0 := by
    simpa [pfun, bne_iff_ne] using hpk0
  have hvb : ∀ j < k0, v (d4p_coord j) = 0 := by
    intro j hj
    have h := hbefore j hj
    simpa [pfun, bne_iff_ne] using h
  let a : K := (v (d4p_coord k0))⁻¹
  let w : Fin 4 ⊕ Fin 4 → K := a • v
  have ha0 : a ≠ 0 := inv_ne_zero hvk0
  have hwk0 : w (d4p_coord k0) = 1 := by
    simp [w, a, smul_eq_mul, hvk0]
  have hwb : ∀ j < k0, w (d4p_coord j) = 0 := by
    intro j hj
    simp [w, hvb j hj]
  obtain ⟨c, hc1, hvec⟩ := exists_vecC (hω := hω) (K := K) hK w
  have hpw : p = K ∙ w := by
    rw [hpv]
    exact (Submodule.span_singleton_smul_eq (R := K) (isUnit_iff_ne_zero.mpr ha0) v).symm
  have hp_eq : p = K ∙ vecC ω c := by
    rw [hpw, ← hvec]
  have hcoord : ∀ j < 8, enc ω (cd c j) = w (d4p_coord j) := by
    intro j hj
    have h := congrFun hvec (d4p_coord j)
    simpa [vecC, d4p_cidx_coord hj] using h
  have hcd1 : cd c k0 = 1 := by
    apply enc_injOn hω (cd_lt c k0) (by norm_num : (1 : ℕ) < 4)
    rw [hcoord k0 hk0, hwk0]
    rfl
  have hcd0 : ∀ j < k0, cd c j = 0 := by
    intro j hj
    apply enc_injOn hω (cd_lt c j) (by norm_num : (0 : ℕ) < 4)
    rw [hcoord j (by omega), hwb j hj]
    rfl
  have hnorm : normC c = true := d4p_normC_iff.mpr ⟨k0, hk0, hcd1, hcd0⟩
  have hQw : quadPlus 4 K w = 0 := by
    rw [show w = a • v from rfl, QuadraticMap.map_smul]
    simp [hvQ]
  have hq : quadC c = 0 := by
    apply (enc_eq_zero_iff hω (quadC_lt c)).mp
    rw [← quadPlus_vecC hω c, hvec, hQw]
  have hHw : flipHerm σ w w ≠ 0 := by
    rw [show w = a • v from rfl, flipHerm_smul_left, flipHerm_smul_right]
    refine mul_ne_zero ha0 (mul_ne_zero ?_ hvh)
    intro h
    exact ha0 (σ.injective (by rw [h, map_zero]))
  have hh : hermC c c ≠ 0 := by
    intro h
    apply hHw
    rw [← hvec, flipHerm_vecC hω hσω c c, h]
    rfl
  exact ⟨c, mem_ptCodes.mpr ⟨hc1, hnorm, hq, hh⟩, hp_eq⟩

theorem eq_of_span_vecC_eq {c c' : ℕ} (hc : c ∈ ptCodes ()) (hc' : c' ∈ ptCodes ())
    (h : K ∙ vecC ω c = K ∙ vecC ω c') : c = c' := by
  rw [mem_ptCodes] at hc hc'
  obtain ⟨hc1, hcn, -, hh⟩ := hc
  obtain ⟨hc1', hcn', -, hh'⟩ := hc'
  have hvc0 : vecC ω c ≠ 0 := by
    intro hzero
    have hH : flipHerm σ (vecC ω c) (vecC ω c) ≠ 0 := by
      rw [flipHerm_vecC hω hσω c c]
      intro h
      exact hh ((enc_eq_zero_iff hω (hermC_lt c c)).mp h)
    exact hH (by rw [hzero]; simp)
  have hvc0' : vecC ω c' ≠ 0 := d4p_vecC_ne_zero (hω := hω) hc1' hh'
  have hmem : vecC ω c' ∈ K ∙ vecC ω c := by
    rw [h]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at ha
    exact hvc0' ha.symm
  obtain ⟨k, hk8, hk1, hk0⟩ := d4p_normC_iff.mp hcn
  obtain ⟨k', hk8', hk1', hk0'⟩ := d4p_normC_iff.mp hcn'
  have hcoord : ∀ j < 8, enc ω (cd c' j) = a * enc ω (cd c j) := by
    intro j hj
    have hj' := congrFun ha (d4p_coord j)
    simp only [Pi.smul_apply, vecC, d4p_cidx_coord hj, smul_eq_mul] at hj'
    exact hj'.symm
  have hk_eq : k' = k := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h := hcoord k' hk8'
      rw [hk1', hk0 k' hlt] at h
      simp [enc] at h
    · have h := hcoord k hk8
      rw [hk0' k hlt, hk1] at h
      simp [enc] at h
      exact ha0 h.symm
  have hk1'' : cd c' k = 1 := hk_eq ▸ hk1'
  have ha1 : a = 1 := by
    have h := hcoord k hk8
    rw [hk1'', hk1] at h
    simpa [enc] using h.symm
  have hvec : vecC ω c' = vecC ω c := by
    rw [← ha, ha1, one_smul]
  exact (vecC_injOn hω hc1' hc1 hvec).symm

theorem flipColl_span_vecC_iff [Finite K] (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    {c c' : ℕ} (hc : c ∈ ptCodes ()) (hc' : c' ∈ ptCodes ()) :
    FlipColl σ (K ∙ vecC ω c) (K ∙ vecC ω c') ↔ ptAdjC c c' = true := by
  constructor
  · intro h
    have hptc := isFlipflopPt_span_vecC hω hσω hc
    have hptc' := isFlipflopPt_span_vecC hω hσω hc'
    have hne : c ≠ c' := by
      intro heq
      exact h.1 (by rw [heq])
    have hpol : polarC c c' = 0 := by
      have hmem : vecC ω c ∈ qPerp 4 K (K ∙ vecC ω c') :=
        (FlipColl.le_qPerp h) (Submodule.mem_span_singleton_self _)
      have h0 := (mem_qPerp.mp hmem) (vecC ω c') (Submodule.mem_span_singleton_self _)
      rw [polar_comm] at h0
      rw [polar_vecC hω c c'] at h0
      exact (enc_eq_zero_iff hω (polarC_lt c c')).mp h0
    have hherm : hermC c c' = 0 := by
      have h0 := FlipColl.flipHerm_eq_zero_of_card_four hσ hK h hptc hptc'
        (Submodule.mem_span_singleton_self _) (Submodule.mem_span_singleton_self _)
      rw [flipHerm_vecC hω hσω c c'] at h0
      exact (enc_eq_zero_iff hω (hermC_lt c c')).mp h0
    simp [ptAdjC, bne_iff_ne, hne, hpol, hherm]
  · intro hadj
    simp only [ptAdjC, Bool.and_eq_true, bne_iff_ne, beq_iff_eq, and_assoc] at hadj
    obtain ⟨hne, hpol, hherm⟩ := hadj
    have hp : IsFlipflopPt σ (K ∙ vecC ω c) := isFlipflopPt_span_vecC hω hσω hc
    have hp' : IsFlipflopPt σ (K ∙ vecC ω c') := isFlipflopPt_span_vecC hω hσω hc'
    have hherm0 : flipHerm σ (vecC ω c) (vecC ω c') = 0 := by
      rw [flipHerm_vecC hω hσω c c', hherm]
      rfl
    have hf : K ∙ vecC ω c ≤ qPerp 4 K (K ∙ vecC ω c') := by
      rw [Submodule.span_singleton_le_iff_mem, mem_qPerp]
      intro w hw
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [polar_smul_left, ← polar_comm (quadPlus 4 K) (vecC ω c) (vecC ω c'),
        polar_vecC hω c c', hpol]
      simp [enc]
    have hh : K ∙ vecC ω c ≤ flipOrth σ (K ∙ vecC ω c') := by
      rw [Submodule.span_singleton_le_iff_mem, mem_flipOrth]
      intro w hw
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [flipHerm_smul_left, (flipHerm_eq_zero_iff hσ.invol).mp hherm0]
      simp
    exact flipColl_of_orth hσ.invol hp hp' hf hh

end Omega

end CFSG.ClassicalInvolution.PhanDn.D4Q2

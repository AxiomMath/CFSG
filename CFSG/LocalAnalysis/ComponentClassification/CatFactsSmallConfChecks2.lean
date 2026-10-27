module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfGen

public section

namespace CFSG.ComponentClassification.CatFactsSmall

open CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier Subgroup

variable {n : ℕ}

theorem coset_of_check {QA QQ : RawSchreierDatum n} (hQA : ValidSchreier QA)
    (hQQ : ValidSchreier QQ) {qgens : List (Equiv.Perm (Fin n))}
    (hq : ∀ q ∈ qgens, q ∈ QQ.originalSubgroup) {g₀ : Equiv.Perm (Fin n)}
    (h : (elemsT QA).all (fun x => !(qgens.all fun q => QQ.sift (x * q * x⁻¹) 0) ||
      QQ.sift x 0 || QQ.sift (g₀⁻¹ * x) 0) = true) :
    ∀ x ∈ QA.originalSubgroup, (∀ q ∈ QQ.originalSubgroup, x * q * x⁻¹ ∈ QQ.originalSubgroup) →
      x ∉ QQ.originalSubgroup → g₀⁻¹ * x ∈ QQ.originalSubgroup := by
  intro x hx hn hnot
  have h1 := List.all_eq_true.1 h x ((mem_elemsT QA hQA x).2 hx)
  have h2 : (qgens.all fun q => QQ.sift (x * q * x⁻¹) 0) = true :=
    List.all_eq_true.2 fun q hq' => (mem_iff_sift QQ hQQ _).1 (hn q (hq q hq'))
  rw [h2, Bool.not_true, Bool.false_or, Bool.or_eq_true] at h1
  rcases h1 with h1 | h1
  · exact absurd ((mem_iff_sift QQ hQQ x).2 h1) hnot
  · exact (mem_iff_sift QQ hQQ _).2 h1

theorem eq_of_normalizer_check {QA QH QR : RawSchreierDatum n} (hQA : ValidSchreier QA)
    (hQH : ValidSchreier QH) (hQR : ValidSchreier QR) {hgens : List (Equiv.Perm (Fin n))}
    (hH : QH.originalSubgroup = closure {g | g ∈ hgens})
    (h : (elemsT QA).all (fun x => !(hgens.all fun g => QH.sift (x * g * x⁻¹) 0) ||
      QR.sift x 0) = true)
    (R' : Subgroup (Equiv.Perm (Fin n))) (hR'A : R' ≤ QA.originalSubgroup)
    (hHR : QH.originalSubgroup ≤ R') (hcard : Nat.card R' = 2 * Nat.card QH.originalSubgroup)
    (hRcard : Nat.card QR.originalSubgroup ≤ Nat.card R') : R' = QR.originalSubgroup := by
  have hidx : (QH.originalSubgroup.subgroupOf R').index = 2 := by
    have h1 := index_mul_card (QH.originalSubgroup.subgroupOf R')
    rw [Nat.card_congr (subgroupOfEquivOfLe hHR).toEquiv, hcard] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hnorm : (QH.originalSubgroup.subgroupOf R').Normal := normal_of_index_eq_two hidx
  have hle : R' ≤ QR.originalSubgroup := by
    intro r hr
    have h1 := List.all_eq_true.1 h r ((mem_elemsT QA hQA r).2 (hR'A hr))
    have h2 : (hgens.all fun g => QH.sift (r * g * r⁻¹) 0) = true := by
      refine List.all_eq_true.2 fun g hg => (mem_iff_sift QH hQH _).1 ?_
      have hgH : g ∈ QH.originalSubgroup := by rw [hH]; exact subset_closure hg
      have := hnorm.conj_mem ⟨g, hHR hgH⟩ (mem_subgroupOf.2 hgH) ⟨r, hr⟩
      rw [mem_subgroupOf] at this
      exact this
    rw [h2, Bool.not_true, Bool.false_or] at h1
    exact (mem_iff_sift QR hQR r).2 h1
  exact eq_of_le_of_card_ge hle hRcard

theorem z_unique_of_check {QQ QL : RawSchreierDatum n} (hQQ : ValidSchreier QQ)
    (hQL : ValidSchreier QL) {z₀ : Equiv.Perm (Fin n)}
    (h : (elemsT QQ).all (fun w => !QL.sift w 0 || !decide (w * w = 1) || decide (w = 1) ||
      decide (w = z₀) || (elemsT QQ).any (fun v => QL.sift v 0 && !decide (w * v = v * w))) =
      true) :
    ∀ w ∈ QQ.originalSubgroup ⊓ QL.originalSubgroup,
      (∀ v ∈ QQ.originalSubgroup ⊓ QL.originalSubgroup, w * v = v * w) → w * w = 1 → w ≠ 1 →
        w = z₀ := by
  intro w hw hc h2 h1
  have h3 := List.all_eq_true.1 h w ((mem_elemsT QQ hQQ w).2 hw.1)
  have hL : QL.sift w 0 = true := (mem_iff_sift QL hQL w).1 hw.2
  simp only [hL, h2, h1, Bool.not_true, decide_true, decide_false, Bool.false_or,
    Bool.or_false, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not] at h3
  rcases h3 with h3 | ⟨v, hv, hvL, hvc⟩
  · exact h3
  · exact absurd (hc v ⟨(mem_elemsT QQ hQQ v).1 hv, (mem_iff_sift QL hQL v).2 hvL⟩) hvc

theorem Q_eq_of_check {QQ QL : RawSchreierDatum n} (hQL : ValidSchreier QL)
    {qgens : List (Equiv.Perm (Fin n))} (hQQe : QQ.originalSubgroup = closure {q | q ∈ qgens})
    {τ s : Equiv.Perm (Fin n)} (hτ : τ ∈ QQ.originalSubgroup) (hs : s ∈ QQ.originalSubgroup)
    (h : qgens.all (fun q => QL.sift q 0 || QL.sift (q * τ⁻¹) 0 || QL.sift (q * s⁻¹) 0 ||
      QL.sift (q * s⁻¹ * τ⁻¹) 0) = true) :
    QQ.originalSubgroup = QQ.originalSubgroup ⊓ QL.originalSubgroup ⊔ zpowers τ ⊔ zpowers s := by
  set Q₀ := QQ.originalSubgroup
  set S := Q₀ ⊓ QL.originalSubgroup ⊔ zpowers τ ⊔ zpowers s
  have hτS : τ ∈ S := mem_sup_left (mem_sup_right (mem_zpowers τ))
  have hsS : s ∈ S := mem_sup_right (mem_zpowers s)
  have hDS : ∀ d ∈ Q₀, d ∈ QL.originalSubgroup → d ∈ S := fun d hd hdL =>
    mem_sup_left (mem_sup_left (⟨hd, hdL⟩ : d ∈ Q₀ ⊓ QL.originalSubgroup))
  apply le_antisymm
  · have hgen : ∀ q ∈ qgens, q ∈ S := by
      intro q hq
      have hqQ : q ∈ Q₀ := by rw [hQQe]; exact subset_closure hq
      have h1 := List.all_eq_true.1 h q hq
      simp only [Bool.or_eq_true] at h1
      rcases h1 with ((h1 | h1) | h1) | h1
      · exact hDS q hqQ ((mem_iff_sift QL hQL q).2 h1)
      · have hd := hDS _ (mul_mem hqQ (inv_mem hτ)) ((mem_iff_sift QL hQL _).2 h1)
        simpa using mul_mem hd hτS
      · have hd := hDS _ (mul_mem hqQ (inv_mem hs)) ((mem_iff_sift QL hQL _).2 h1)
        simpa using mul_mem hd hsS
      · have hd := hDS _ (mul_mem (mul_mem hqQ (inv_mem hs)) (inv_mem hτ))
          ((mem_iff_sift QL hQL _).2 h1)
        simpa [mul_assoc] using mul_mem (mul_mem hd hτS) hsS
    have : closure {q | q ∈ qgens} ≤ S := (closure_le S).2 hgen
    rw [← hQQe] at this
    exact this
  · exact sup_le (sup_le inf_le_left (zpowers_le.2 hτ)) (zpowers_le.2 hs)

theorem unique_E16_of_check {QR QP QE : RawSchreierDatum n} (hQR : ValidSchreier QR)
    (hQP : ValidSchreier QP) (hQE : ValidSchreier QE)
    (h : ((elemsT QR).filter fun x => QP.sift x 0).all (fun x => !decide (x * x = 1) ||
      QE.sift x 0 || decide ((((elemsT QR).filter fun x => QP.sift x 0).filter
        fun y => decide (y * y = 1) && decide (y * x = x * y)).length < 16)) = true)
    (hE16 : Nat.card QE.originalSubgroup = 16) (E' : Subgroup (Equiv.Perm (Fin n)))
    (hE'le : E' ≤ QR.originalSubgroup ⊓ QP.originalSubgroup) (hE'2 : ∀ x ∈ E', x * x = 1)
    (hE'16 : Nat.card E' = 16) : E' = QE.originalSubgroup := by
  classical
  set LX := (elemsT QR).filter fun x => QP.sift x 0
  have hLX : ∀ x ∈ QR.originalSubgroup ⊓ QP.originalSubgroup, x ∈ LX := fun x hx =>
    List.mem_filter.2 ⟨(mem_elemsT QR hQR x).2 hx.1, (mem_iff_sift QP hQP x).1 hx.2⟩
  have hbad := forall_bad_of_count hLX (fun x => x ∈ QE.originalSubgroup) (k := 16)
    (fun x hx hx2 hxE => by
      have h1 := List.all_eq_true.1 h x hx
      have hs : QE.sift x 0 = false := by
        rcases Bool.eq_false_or_eq_true (QE.sift x 0) with h2 | h2
        · exact absurd ((mem_iff_sift QE hQE x).2 h2) hxE
        · exact h2
      simp only [hx2, hs, decide_true, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h1
      exact count_of_filter h1) hE'le hE'2 (by rw [hE'16])
  exact eq_of_le_of_card_ge (fun x hx => hbad x hx) (by rw [hE16, hE'16])

theorem no_E32_of_check {QR : RawSchreierDatum n} (hQR : ValidSchreier QR)
    (B : List (Equiv.Perm (Fin n))) (hB : B.length + 1 < 32)
    (h : (elemsT QR).all (fun x => !decide (x * x = 1) || decide (x = 1) || decide (x ∈ B) ||
      decide (((elemsT QR).filter fun y => decide (y * y = 1) && decide (y * x = x * y)).length <
        32)) = true)
    (A' : Subgroup (Equiv.Perm (Fin n))) (hA'R : A' ≤ QR.originalSubgroup)
    (hA'2 : ∀ x ∈ A', x * x = 1) : Nat.card A' ≠ 32 := by
  classical
  intro h32
  have hLX : ∀ x ∈ QR.originalSubgroup, x ∈ elemsT QR := fun x hx => (mem_elemsT QR hQR x).2 hx
  have hbad := forall_bad_of_count hLX (fun x => x = 1 ∨ x ∈ B) (k := 32)
    (fun x hx hx2 hxB => by
      have h1 := List.all_eq_true.1 h x hx
      have hx1 : x ≠ 1 := fun h' => hxB (Or.inl h')
      have hxB' : x ∉ B := fun h' => hxB (Or.inr h')
      simp only [hx2, hx1, hxB', decide_true, decide_false, Bool.not_true, Bool.false_or,
        decide_eq_true_eq] at h1
      exact count_of_filter h1) hA'R hA'2 (by rw [h32])
  have := card_le_length (E := A') (L := 1 :: B) fun x hx => by
    rcases hbad x hx with h1 | h1
    · rw [h1]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ h1
  simp only [List.length_cons] at this
  omega

theorem normal_E16_of_check {QR QP : RawSchreierDatum n} (hQR : ValidSchreier QR)
    (hQP : ValidSchreier QP) (inCls : Equiv.Perm (Fin n) → Bool)
    (h : (elemsT QR).all (fun w => !decide (w * w = 1) || QP.sift w 0 || inCls w ||
      (elemsT QR).any (fun r => !decide (w * (r * w * r⁻¹) = r * w * r⁻¹ * w)) ||
      decide (((elemsT QR).filter fun y => decide (y * y = 1) && !inCls y &&
        (elemsT QR).all fun r => decide (y * (r * w * r⁻¹) = r * w * r⁻¹ * y)).length < 16)) =
      true)
    (A' : Subgroup (Equiv.Perm (Fin n))) (hA'R : A' ≤ QR.originalSubgroup)
    (hA'2 : ∀ x ∈ A', x * x = 1) (hA'16 : Nat.card A' = 16)
    (hA'n : ∀ r ∈ QR.originalSubgroup, ∀ x ∈ A', r * x * r⁻¹ ∈ A')
    (hA'P : ¬ A' ≤ QP.originalSubgroup) : ∃ w ∈ A', inCls w = true := by
  classical
  by_contra hno
  push Not at hno
  have hno' : ∀ w ∈ A', inCls w = false := fun w hw => by simpa using hno w hw
  obtain ⟨w, hwA, hwP⟩ := Set.not_subset.1 hA'P
  have hwR := hA'R hwA
  have h1 := List.all_eq_true.1 h w ((mem_elemsT QR hQR w).2 hwR)
  have hs : QP.sift w 0 = false := by
    rcases Bool.eq_false_or_eq_true (QP.sift w 0) with h2 | h2
    · exact absurd ((mem_iff_sift QP hQP w).2 h2) hwP
    · exact h2
  have hany : (elemsT QR).any (fun r => !decide (w * (r * w * r⁻¹) = r * w * r⁻¹ * w)) =
      false := by
    rw [List.any_eq_false]
    intro r hr
    have hr' := (mem_elemsT QR hQR r).1 hr
    simp [mul_comm_of_sq hA'2 hwA (hA'n r hr' w hwA)]
  simp only [hA'2 w hwA, hs, hno' w hwA, hany, decide_true, Bool.not_true, Bool.false_or,
    decide_eq_true_eq] at h1
  have := card_le_length (E := A') (L := (elemsT QR).filter fun y => decide (y * y = 1) &&
      !inCls y && (elemsT QR).all fun r => decide (y * (r * w * r⁻¹) = r * w * r⁻¹ * y))
    fun y hy => by
      refine List.mem_filter.2 ⟨(mem_elemsT QR hQR y).2 (hA'R hy), ?_⟩
      simp only [hA'2 y hy, hno' y hy, decide_true, Bool.not_false, Bool.and_true,
        Bool.true_and, List.all_eq_true, decide_eq_true_eq]
      intro r hr
      exact mul_comm_of_sq hA'2 hy (hA'n r ((mem_elemsT QR hQR r).1 hr) w hwA)
  omega


theorem elemAb_of_check {Q : RawSchreierDatum n} (hQ : ValidSchreier Q)
    (h : (elemsT Q).all (fun x => decide (x * x = 1)) = true) :
    CFSG.ComponentClassification.GSThmB.Cat8.IsElemAb2 Q.originalSubgroup := fun x hx =>
  of_decide_eq_true (List.all_eq_true.1 h x ((mem_elemsT Q hQ x).2 hx))

end CFSG.ComponentClassification.CatFactsSmall

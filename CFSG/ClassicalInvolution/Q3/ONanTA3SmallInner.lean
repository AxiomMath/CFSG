module

public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallGood
public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallCheckN
public import CFSG.ClassicalInvolution.Q3.TL3Induct

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic Check

variable {Y : Type} [Group Y]

theorem not_selfGen_of_le [Finite Y] {N : Subgroup Y} (hN : N.Normal) (hNtop : N ≠ ⊤)
    {R : Subgroup Y} (hRN : R ≤ N) : ¬ TightSelfGen R := by
  intro h
  apply hNtop
  rw [eq_top_iff, ← h]
  refine iSup_le fun g => ?_
  intro x hx
  rw [mem_conjSub_iff] at hx
  have := hN.conj_mem _ (hRN (tightCore_le R hx)) g
  simpa [mul_assoc] using this

theorem mem_of_mem_q8List {N : Subgroup Y} {t a b : Y} (ha : a ∈ N) (hb : b ∈ N)
    (haa : a * a = t) {r : Y} (hr : r ∈ q8List t a b) : r ∈ N := by
  have ht : t ∈ N := haa ▸ N.mul_mem ha ha
  simp only [q8List, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact N.one_mem
  · exact ha
  · exact ht
  · exact N.mul_mem ht ha
  · exact hb
  · exact N.mul_mem hb ha
  · exact N.mul_mem hb ht
  · exact N.mul_mem hb (N.mul_mem ht ha)

@[expose] def GoodOrInnerPred (N : Subgroup Y) (t : Y) : Prop :=
  NoOddNormalAt t ∧
    ∀ a b : Y, a * a = t → b * b = t → b * a = t * a * b →
      (∀ c ∈ Subgroup.centralizer ({t} : Set Y),
        c * a * c⁻¹ ∈ q8List t a b ∧ c * b * c⁻¹ ∈ q8List t a b) →
      (a ∈ N ∧ b ∈ N) ∨
      ∃ x ∈ Subgroup.centralizer ({t} : Set Y), x ^ 3 = 1 ∧ ¬ (x * a = a * x ∧ x * b = b * x) ∧
        ∀ y ∈ Subgroup.centralizer ({t} : Set Y), y * a = a * y → y * b = b * y →
          x * y = y * x

theorem good_of_goodOrInner [Finite Y] {N : Subgroup Y} (hN : N.Normal) (hNtop : N ≠ ⊤)
    {R : Subgroup Y} {S : Sylow 2 R} {t : Y} (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hP : GoodOrInnerPred N t) : GoodThreeElement R t := by
  obtain ⟨hOR, -, a, b, ha, hb, haa, hbb, hba, hlist⟩ := datum_shape hd hc.1 hP.1
  have hOC : oddCoreImg (Subgroup.centralizer ({t} : Set Y)) = ⊥ :=
    oddCoreImg_eq_bot hP.1 le_rfl fun g hg => Subgroup.le_normalizer hg
  have hnorm : ∀ c ∈ Subgroup.centralizer ({t} : Set Y),
      c * a * c⁻¹ ∈ q8List t a b ∧ c * b * c⁻¹ ∈ q8List t a b := fun c hc =>
    ⟨hlist _ ((Subgroup.mem_normalizer_iff.mp (hd.le_normalizer hc) a).mp ha),
      hlist _ ((Subgroup.mem_normalizer_iff.mp (hd.le_normalizer hc) b).mp hb)⟩
  rcases hP.2 a b haa hbb hba hnorm with ⟨haN, hbN⟩ | ⟨x, hx, hx3, hmove, hcomm⟩
  · exact absurd hc.2.1 (not_selfGen_of_le hN hNtop fun r hr =>
      mem_of_mem_q8List haN hbN haa (hlist r hr))
  · exact good_of_witness hOR hOC ha hb hx hx3 hmove hcomm

section Sound

variable {M : Type} [Group M] [DecidableEq M] {ι : Y →* M} (hι : Function.Injective ι)
  {L : List M} (hL : ∀ m, m ∈ L ↔ ∃ y, ι y = m) {N : Subgroup Y} {LN : List M}
  (hLN : ∀ y, ι y ∈ LN ↔ y ∈ N)

include hι hL hLN in
theorem witness_of_pairsN {t : Y} (h : pairsN LN (ι t) (centB L (ι t)) = true) (a b : Y)
    (haa : a * a = t) (hbb : b * b = t) (hba : b * a = t * a * b)
    (hnorm : ∀ c ∈ Subgroup.centralizer ({t} : Set Y),
      c * a * c⁻¹ ∈ q8List t a b ∧ c * b * c⁻¹ ∈ q8List t a b) :
    (a ∈ N ∧ b ∈ N) ∨
    ∃ x ∈ Subgroup.centralizer ({t} : Set Y), x ^ 3 = 1 ∧ ¬ (x * a = a * x ∧ x * b = b * x) ∧
      ∀ y ∈ Subgroup.centralizer ({t} : Set Y), y * a = a * y → y * b = b * y →
        x * y = y * x := by
  have hta : a * t = t * a := by rw [← haa]; exact (mul_assoc a a a).symm
  have htb : b * t = t * b := by rw [← hbb]; exact (mul_assoc b b b).symm
  have haC : ι a ∈ centB L (ι t) := (mem_centB hι hL).2 ⟨a, hta, rfl⟩
  have hbC : ι b ∈ centB L (ι t) := (mem_centB hι hL).2 ⟨b, htb, rfl⟩
  unfold pairsN at h
  rw [List.all_eq_true] at h
  have h1 := h (ι a) (List.mem_filter.2 ⟨haC, decide_eq_true (by rw [← map_mul, haa])⟩)
  rw [List.all_eq_true] at h1
  have h2 := h1 (ι b) (List.mem_filter.2 ⟨hbC, decide_eq_true (by rw [← map_mul, hbb])⟩)
  rcases Bool.or_eq_true_iff.1 h2 with h3 | hD
  · rcases Bool.or_eq_true_iff.1 h3 with h4 | hN
    · rcases Bool.or_eq_true_iff.1 h4 with hA | hB
      · exfalso
        have hrel : ι b * ι a = ι t * ι a * ι b := by simp only [← map_mul, hba]
        rw [decide_eq_true hrel] at hA
        exact absurd hA (by decide)
      · exfalso
        have hall : (centB L (ι t)).all (fun c => memB (q8B (ι t) (ι a) (ι b)) (c * ι a * c⁻¹) &&
            memB (q8B (ι t) (ι a) (ι b)) (c * ι b * c⁻¹)) = true := by
          rw [List.all_eq_true]
          intro c hc
          obtain ⟨y, hy, rfl⟩ := (mem_centB hι hL).1 hc
          obtain ⟨hya, hyb⟩ := hnorm y (Subgroup.mem_centralizer_singleton_iff.mpr hy)
          rw [q8B_eq (ι := ι), Bool.and_eq_true]
          exact ⟨memB_iff.2 (List.mem_map.2 ⟨_, hya, by simp only [map_mul, map_inv]⟩),
            memB_iff.2 (List.mem_map.2 ⟨_, hyb, by simp only [map_mul, map_inv]⟩)⟩
        rw [hall] at hB
        exact absurd hB (by decide)
    · left
      obtain ⟨hNa, hNb⟩ := Bool.and_eq_true_iff.1 hN
      exact ⟨(hLN a).1 (memB_iff.1 hNa), (hLN b).1 (memB_iff.1 hNb)⟩
  · right
    obtain ⟨xm, hxm, hx⟩ := List.any_eq_true.1 hD
    obtain ⟨x, hxt, rfl⟩ := (mem_centB hι hL).1 hxm
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
      List.all_eq_true, Bool.or_eq_true] at hx
    obtain ⟨⟨hx3, hmv⟩, hy⟩ := hx
    refine ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr hxt, hι (by simpa using hx3), ?_,
      fun y hyc hya hyb => ?_⟩
    · rintro ⟨h7, h8⟩
      exact hmv ⟨by simp only [← map_mul, h7], by simp only [← map_mul, h8]⟩
    · have hyt : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp hyc
      have hyC : ι y ∈ centB L (ι t) := (mem_centB hι hL).2 ⟨y, hyt, rfl⟩
      rcases hy (ι y) hyC with hyn | hyn
      · exfalso
        exact hyn ⟨by simp only [← map_mul, hya], by simp only [← map_mul, hyb]⟩
      · exact hι (by simpa [map_mul] using hyn)

end Sound

end CFSG.ClassicalInvolution.Q3.TA3

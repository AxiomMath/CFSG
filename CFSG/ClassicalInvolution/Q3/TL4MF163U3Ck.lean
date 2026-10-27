module

public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallVerdictSound
public import Certificates.Data.TL4MF163U3Inv

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.MF163.U3

open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Check
  Certificates.TL4MF163U3Inv

variable {Y M : Type} [Group Y] [Group M] [DecidableEq M] {ι : Y →* M}
  (hι : Function.Injective ι) {L : List M} (hL : ∀ m, m ∈ L ↔ ∃ y, ι y = m)

include hι hL in
theorem centInv_of_check {N : Subgroup Y} {LN : List M} (hLN : ∀ y, ι y ∈ LN ↔ y ∈ N)
    {reps : List M} (h : centInvCheck LN L reps = true) {t : Y} (ht : ι t ∈ reps)
    {a b : Y} (haa : a * a = t) (hbb : b * b = t) (hba : b * a = t * a * b)
    (hnorm : ∀ c ∈ Subgroup.centralizer ({t} : Set Y),
      c * a * c⁻¹ ∈ q8List t a b ∧ c * b * c⁻¹ ∈ q8List t a b)
    (hN : ¬ (a ∈ N ∧ b ∈ N))
    (h3 : ∀ x ∈ Subgroup.centralizer ({t} : Set Y), x ^ 3 = 1 → x * a = a * x ∧ x * b = b * x)
    {c : Y} (hct : c * t = t * c) (hc2 : c * c = 1) (hca : c * a = a * c)
    (hcb : c * b = b * c) : c = 1 ∨ c = t := by
  have hta : a * t = t * a := by rw [← haa]; exact (mul_assoc a a a).symm
  have htb : b * t = t * b := by rw [← hbb]; exact (mul_assoc b b b).symm
  have haC : ι a ∈ centB L (ι t) := (mem_centB hι hL).2 ⟨a, hta, rfl⟩
  have hbC : ι b ∈ centB L (ι t) := (mem_centB hι hL).2 ⟨b, htb, rfl⟩
  have hcC : ι c ∈ centB L (ι t) := (mem_centB hι hL).2 ⟨c, hct, rfl⟩
  have h1 := List.all_eq_true.1 h (ι t) ht
  unfold centInvAt at h1
  rw [List.all_eq_true] at h1
  have h2 := h1 (ι a) (List.mem_filter.2 ⟨haC, decide_eq_true (by rw [← map_mul, haa])⟩)
  rw [List.all_eq_true] at h2
  have h4 := h2 (ι b) (List.mem_filter.2 ⟨hbC, decide_eq_true (by rw [← map_mul, hbb])⟩)
  have hrel : ι b * ι a = ι t * ι a * ι b := by simp only [← map_mul, hba]
  have hall : (centB L (ι t)).all (fun c =>
      memB (q8B (ι t) (ι a) (ι b)) (c * ι a * c⁻¹) &&
      memB (q8B (ι t) (ι a) (ι b)) (c * ι b * c⁻¹)) = true := by
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (mem_centB hι hL).1 hx
    obtain ⟨hya, hyb⟩ := hnorm y (Subgroup.mem_centralizer_singleton_iff.mpr hy)
    rw [q8B_eq (ι := ι), Bool.and_eq_true]
    exact ⟨memB_iff.2 (List.mem_map.2 ⟨_, hya, by simp only [map_mul, map_inv]⟩),
      memB_iff.2 (List.mem_map.2 ⟨_, hyb, by simp only [map_mul, map_inv]⟩)⟩
  have hLNf : (memB LN (ι a) && memB LN (ι b)) = false := by
    by_contra hc
    rw [Bool.not_eq_false, Bool.and_eq_true] at hc
    exact hN ⟨(hLN a).1 (memB_iff.1 hc.1), (hLN b).1 (memB_iff.1 hc.2)⟩
  have h3all : (centB L (ι t)).all (fun x => !decide (x ^ 3 = 1) ||
      decide (x * ι a = ι a * x ∧ x * ι b = ι b * x)) = true := by
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (mem_centB hι hL).1 hx
    by_cases hy3 : y ^ 3 = 1
    · obtain ⟨hya, hyb⟩ := h3 y (Subgroup.mem_centralizer_singleton_iff.mpr hy) hy3
      have hc : ι y * ι a = ι a * ι y ∧ ι y * ι b = ι b * ι y :=
        ⟨by rw [← map_mul, ← map_mul, hya], by rw [← map_mul, ← map_mul, hyb]⟩
      simp [hc]
    · have hc : ¬ ι y ^ 3 = 1 := fun h0 => hy3 (hι (by rw [map_pow, h0, map_one]))
      simp [hc]
  rw [decide_eq_true hrel, hall, hLNf, h3all] at h4
  simp only [Bool.not_true, Bool.false_or] at h4
  have h5 := List.all_eq_true.1 h4 (ι c) hcC
  have hprem : ι c * ι c = 1 ∧ ι c * ι a = ι a * ι c ∧ ι c * ι b = ι b * ι c :=
    ⟨by rw [← map_mul, hc2, map_one], by rw [← map_mul, ← map_mul, hca],
      by rw [← map_mul, ← map_mul, hcb]⟩
  rw [decide_eq_true hprem] at h5
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq] at h5
  rcases h5 with h5 | h5
  · exact Or.inl (hι (by rw [h5, map_one]))
  · exact Or.inr (hι h5)

omit [Group M] [DecidableEq M] in
theorem mem_q8List_conj (g : Y) {t a b x : Y} (hx : x ∈ q8List t a b) :
    g * x * g⁻¹ ∈ q8List (g * t * g⁻¹) (g * a * g⁻¹) (g * b * g⁻¹) := by
  simp only [q8List, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left; group
  · right; left; rfl
  · right; right; left; rfl
  · right; right; right; left; group
  · right; right; right; right; left; rfl
  · right; right; right; right; right; left; group
  · right; right; right; right; right; right; left; group
  · right; right; right; right; right; right; right; group

omit [Group M] [DecidableEq M] in
theorem conj_mem_centralizer (g : Y) {z x : Y} (hx : x ∈ Subgroup.centralizer ({z} : Set Y)) :
    g * x * g⁻¹ ∈ Subgroup.centralizer ({g * z * g⁻¹} : Set Y) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  calc g * x * g⁻¹ * (g * z * g⁻¹) = g * (x * z) * g⁻¹ := by group
    _ = g * (z * x) * g⁻¹ := by rw [hx]
    _ = g * z * g⁻¹ * (g * x * g⁻¹) := by group

omit [Group M] [DecidableEq M] in
theorem noOddNormalAt3_of_conj (g : Y) {z : Y} (h : NoOddNormalAt3 (g * z * g⁻¹)) :
    NoOddNormalAt3 z := by
  intro o ho hne hodd
  have hord : ∀ x : Y, orderOf (g * x * g⁻¹) = orderOf x := fun x => by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
  have hne' : g * o * g⁻¹ ≠ 1 := fun h0 => hne (by
    have := congrArg (fun w => g⁻¹ * w * g) h0
    simpa [mul_assoc] using this)
  have hback : ∀ c ∈ Subgroup.centralizer ({g * z * g⁻¹} : Set Y),
      g⁻¹ * c * g ∈ Subgroup.centralizer ({z} : Set Y) := fun c hc => by
    have := conj_mem_centralizer g⁻¹ hc
    simpa [mul_assoc] using this
  rcases h _ (conj_mem_centralizer g ho) hne' (by rw [hord]; exact hodd) with
    ⟨c, hc, hev⟩ | ⟨c, hc, d, hd, hev⟩
  · refine Or.inl ⟨g⁻¹ * c * g, hback c hc, ?_⟩
    rw [← hord (o * (g⁻¹ * c * g * o * (g⁻¹ * c * g)⁻¹))]
    convert hev using 2
    group
  · refine Or.inr ⟨g⁻¹ * c * g, hback c hc, g⁻¹ * d * g, hback d hd, ?_⟩
    rw [← hord (o * (g⁻¹ * c * g * o * (g⁻¹ * c * g)⁻¹) * (g⁻¹ * d * g * o * (g⁻¹ * d * g)⁻¹))]
    convert hev using 2
    group

include hι hL in
theorem eq_of_pair_of_check {N : Subgroup Y} (hNn : N.Normal) {LN : List M}
    (hLN : ∀ y, ι y ∈ LN ↔ y ∈ N) {reps : List M} (hcov : coverB reps L = true)
    (h : centInvCheck LN L reps = true) {t : Y} (ht : orderOf t = 2)
    {a b : Y} (haa : a * a = t) (hbb : b * b = t) (hba : b * a = t * a * b)
    (hnorm : ∀ c ∈ Subgroup.centralizer ({t} : Set Y),
      c * a * c⁻¹ ∈ q8List t a b ∧ c * b * c⁻¹ ∈ q8List t a b)
    (hN : ¬ (a ∈ N ∧ b ∈ N))
    (h3 : ∀ x ∈ Subgroup.centralizer ({t} : Set Y), x ^ 3 = 1 → x * a = a * x ∧ x * b = b * x)
    {c : Y} (hct : c * t = t * c) (hc2 : c * c = 1) (hca : c * a = a * c)
    (hcb : c * b = b * c) : c = 1 ∨ c = t := by
  obtain ⟨r, hr, g, hg⟩ := cover_of_coverB hι hL hcov ht
  have hconj : ∀ x y : Y, g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := fun x y => by group
  have hcomm : ∀ x y : Y, x * y = y * x → g * x * g⁻¹ * (g * y * g⁻¹) =
      g * y * g⁻¹ * (g * x * g⁻¹) := fun x y hxy => by rw [hconj, hconj, hxy]
  have hback : ∀ x ∈ Subgroup.centralizer ({g * t * g⁻¹} : Set Y),
      g⁻¹ * x * g ∈ Subgroup.centralizer ({t} : Set Y) := fun x hx => by
    have := conj_mem_centralizer g⁻¹ hx
    simpa [mul_assoc] using this
  have hgx : ∀ x : Y, g * (g⁻¹ * x * g) * g⁻¹ = x := fun x => by group
  subst hg
  rcases centInv_of_check hι hL hLN h hr (a := g * a * g⁻¹) (b := g * b * g⁻¹)
    (by rw [hconj, haa]) (by rw [hconj, hbb]) (by rw [hconj, hba, ← hconj, ← hconj])
    (fun x hx => by
      obtain ⟨h1, h2⟩ := hnorm _ (hback x hx)
      have e1 := mem_q8List_conj g h1
      have e2 := mem_q8List_conj g h2
      have f1 : g * (g⁻¹ * x * g * a * (g⁻¹ * x * g)⁻¹) * g⁻¹ = x * (g * a * g⁻¹) * x⁻¹ := by
        group
      have f2 : g * (g⁻¹ * x * g * b * (g⁻¹ * x * g)⁻¹) * g⁻¹ = x * (g * b * g⁻¹) * x⁻¹ := by
        group
      rw [f1] at e1
      rw [f2] at e2
      exact ⟨e1, e2⟩)
    (fun hab => hN ⟨by simpa [mul_assoc] using hNn.conj_mem _ hab.1 g⁻¹,
      by simpa [mul_assoc] using hNn.conj_mem _ hab.2 g⁻¹⟩)
    (fun x hx hx3 => by
      have hx3' : (g⁻¹ * x * g) ^ 3 = 1 := by
        rw [show (g⁻¹ * x * g) ^ 3 = g⁻¹ * x ^ 3 * g by
          simp only [pow_succ, pow_zero, one_mul]; group, hx3]
        group
      obtain ⟨h1, h2⟩ := h3 _ (hback x hx) hx3'
      exact ⟨by simpa [hgx] using hcomm _ _ h1, by simpa [hgx] using hcomm _ _ h2⟩)
    (c := g * c * g⁻¹) (hcomm _ _ hct) (by rw [hconj, hc2]; group) (hcomm _ _ hca)
    (hcomm _ _ hcb) with h0 | h0
  · left
    have := congrArg (fun w => g⁻¹ * w * g) h0
    simpa [mul_assoc] using this
  · right
    have := congrArg (fun w => g⁻¹ * w * g) h0
    simpa [mul_assoc] using this

end CFSG.ClassicalInvolution.Q3.TL4.MF163.U3

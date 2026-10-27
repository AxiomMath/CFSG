module

public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallVerdict
public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallCheckV

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution Check

section Order

variable {M : Type*} [Group M] [DecidableEq M]

theorem ordAux_lt (o : M) : ∀ (fuel k m : ℕ), ordAux o fuel k = m → m ≠ 0 → m < k + fuel := by
  intro fuel
  induction fuel with
  | zero =>
    intro k m h hm
    exact absurd h.symm hm
  | succ fuel ih =>
    intro k m h hm
    by_cases hk : o ^ k = 1
    · have hmk : m = k := by
        simp only [ordAux, hk, ite_true] at h
        exact h.symm
      omega
    · simp only [ordAux, hk, ite_false] at h
      have := ih (k + 1) m h hm
      omega

theorem ordB_le {B : ℕ} {o : M} (h : ordB B o ≠ 0) : ordB B o ≤ B := by
  have := ordAux_lt o B 1 (ordB B o) rfl h
  omega

end Order

section Sound

variable {Y M : Type} [Group Y] [Group M] [DecidableEq M] {ι : Y →* M}
  (hι : Function.Injective ι) {L : List M} (hL : ∀ m, m ∈ L ↔ ∃ y, ι y = m)

include hι hL in
theorem noOddNormalAt3_of_noOddB3 {B : ℕ} {t : Y} (h : noOddB3 B (centB L (ι t)) = true) :
    NoOddNormalAt3 t := by
  intro o ho hne hodd
  have hot : o * t = t * o := Subgroup.mem_centralizer_singleton_iff.mp ho
  have hmem : ι o ∈ centB L (ι t) := (mem_centB hι hL).2 ⟨o, hot, rfl⟩
  simp only [noOddB3, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    List.any_eq_true] at h
  obtain ⟨hne0, h1⟩ := h (ι o) hmem
  have hord : orderOf o = ordB B (ι o) := by
    rw [← orderOf_injective ι hι o]
    exact orderOf_eq_of_ordB hne0
  rcases h1 with ((h1 | h1) | ⟨c, hc, hc0, hc2⟩) | ⟨c, hc, d, hd, hc0, hc2⟩
  · exact absurd (hι (by rw [h1, map_one])) hne
  · have := Nat.odd_iff.mp hodd
    rw [hord] at this
    omega
  · obtain ⟨y, hy, rfl⟩ := (mem_centB hι hL).1 hc
    refine Or.inl ⟨y, Subgroup.mem_centralizer_singleton_iff.mpr hy, ?_⟩
    have hp : ι (o * (y * o * y⁻¹)) = ι o * (ι y * ι o * (ι y)⁻¹) := by
      simp only [map_mul, map_inv]
    have hp' : orderOf (o * (y * o * y⁻¹)) = ordB B (ι o * (ι y * ι o * (ι y)⁻¹)) := by
      rw [← orderOf_injective ι hι, hp]
      exact orderOf_eq_of_ordB hc0
    rw [hp']
    exact Nat.even_iff.mpr hc2
  · obtain ⟨y, hy, rfl⟩ := (mem_centB hι hL).1 hc
    obtain ⟨z, hz, rfl⟩ := (mem_centB hι hL).1 hd
    refine Or.inr ⟨y, Subgroup.mem_centralizer_singleton_iff.mpr hy, z,
      Subgroup.mem_centralizer_singleton_iff.mpr hz, ?_⟩
    have hp : ι (o * (y * o * y⁻¹) * (z * o * z⁻¹)) =
        ι o * (ι y * ι o * (ι y)⁻¹) * (ι z * ι o * (ι z)⁻¹) := by
      simp only [map_mul, map_inv]
    have hp' : orderOf (o * (y * o * y⁻¹) * (z * o * z⁻¹)) =
        ordB B (ι o * (ι y * ι o * (ι y)⁻¹) * (ι z * ι o * (ι z)⁻¹)) := by
      rw [← orderOf_injective ι hι, hp]
      exact orderOf_eq_of_ordB hc0
    rw [hp']
    exact Nat.even_iff.mpr hc2

include hι hL in
theorem edgeless_of_edgelessB {t a b : Y} (h : edgelessB L (ι t) (ι a) (ι b) = true) :
    Edgeless t a b := by
  intro g hg
  have h1 := List.all_eq_true.1 h (ι g) ((hL _).2 ⟨g, rfl⟩)
  rcases Bool.or_eq_true_iff.1 h1 with hA | hB
  · exfalso
    have hall : ((q8B (ι t) (ι a) (ι b)).all fun r =>
        decide (ι g * r * (ι g)⁻¹ * ι t = ι t * (ι g * r * (ι g)⁻¹))) = true := by
      rw [List.all_eq_true]
      intro r hr
      rw [q8B_eq (ι := ι)] at hr
      obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
      have hc : g * r' * g⁻¹ * t = t * (g * r' * g⁻¹) :=
        Subgroup.mem_centralizer_singleton_iff.mp (hg r' hr')
      apply decide_eq_true
      simpa only [map_mul, map_inv] using congrArg ι hc
    rw [hall] at hA
    exact absurd hA (by decide)
  · obtain ⟨r, hr, hgr⟩ := List.any_eq_true.1 hB
    rw [q8B_eq (ι := ι)] at hr
    obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
    have hgr' := of_decide_eq_true hgr
    exact ⟨r', hr', hι (by simpa only [map_mul, map_inv] using hgr')⟩

include hι hL in
theorem noActs3_of_noActs3B {B : ℕ} (hB : B < 243) {t a b : Y}
    (h : noActs3B B (centB L (ι t)) (ι a) (ι b) = true) : NoActs3 t a b := by
  intro x hx k hxk
  have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hx
  have hmem : ι x ∈ centB L (ι t) := (mem_centB hι hL).2 ⟨x, hxt, rfl⟩
  have h1 := List.all_eq_true.1 h (ι x) hmem
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not] at h1
  obtain ⟨⟨hne0, hno⟩, hcomm⟩ := h1
  have hord : orderOf x = ordB B (ι x) := by
    rw [← orderOf_injective ι hι x]
    exact orderOf_eq_of_ordB hne0
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
    (hord ▸ orderOf_dvd_of_pow_eq_one hxk)
  have hle := ordB_le hne0
  have hm : ordB B (ι x) = 1 ∨ ordB B (ι x) = 3 := by
    by_contra hnot
    push Not at hnot
    have h4 : j ≤ 4 := by
      by_contra h5
      push Not at h5
      have : 243 ≤ 3 ^ j :=
        calc 243 = 3 ^ 5 := by norm_num
          _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) h5
      omega
    interval_cases j <;> simp_all
  rcases hcomm with hc | ⟨hxa, hxb⟩
  · exact absurd hm hc
  · exact ⟨hι (by simpa only [map_mul] using hxa), hι (by simpa only [map_mul] using hxb)⟩

include hι hL in
theorem pairVerdict_of_pairsV {B : ℕ} (hB : B < 243) {N : Subgroup Y} {LN : List M}
    (hLN : ∀ y, ι y ∈ LN ↔ y ∈ N) {e3b : Bool} {t : Y}
    (h : pairsV B LN L e3b (ι t) (centB L (ι t)) = true) (a b : Y)
    (haa : a * a = t) (hbb : b * b = t) (hba : b * a = t * a * b)
    (hnorm : ∀ c ∈ Subgroup.centralizer ({t} : Set Y),
      c * a * c⁻¹ ∈ q8List t a b ∧ c * b * c⁻¹ ∈ q8List t a b) :
    PairVerdict N (e3b = true) t a b := by
  have hta : a * t = t * a := by rw [← haa]; exact (mul_assoc a a a).symm
  have htb : b * t = t * b := by rw [← hbb]; exact (mul_assoc b b b).symm
  have haC : ι a ∈ centB L (ι t) := (mem_centB hι hL).2 ⟨a, hta, rfl⟩
  have hbC : ι b ∈ centB L (ι t) := (mem_centB hι hL).2 ⟨b, htb, rfl⟩
  unfold pairsV at h
  rw [List.all_eq_true] at h
  have h1 := h (ι a) (List.mem_filter.2 ⟨haC, decide_eq_true (by rw [← map_mul, haa])⟩)
  rw [List.all_eq_true] at h1
  have h2 := h1 (ι b) (List.mem_filter.2 ⟨hbC, decide_eq_true (by rw [← map_mul, hbb])⟩)
  rcases Bool.or_eq_true_iff.1 h2 with h3 | hE
  · rcases Bool.or_eq_true_iff.1 h3 with h4 | hD
    · rcases Bool.or_eq_true_iff.1 h4 with h5 | hC
      · rcases Bool.or_eq_true_iff.1 h5 with hA | hB'
        · exfalso
          have hrel : ι b * ι a = ι t * ι a * ι b := by simp only [← map_mul, hba]
          rw [decide_eq_true hrel] at hA
          exact absurd hA (by decide)
        · exfalso
          have hall : (centB L (ι t)).all (fun c =>
              memB (q8B (ι t) (ι a) (ι b)) (c * ι a * c⁻¹) &&
              memB (q8B (ι t) (ι a) (ι b)) (c * ι b * c⁻¹)) = true := by
            rw [List.all_eq_true]
            intro c hc
            obtain ⟨y, hy, rfl⟩ := (mem_centB hι hL).1 hc
            obtain ⟨hya, hyb⟩ := hnorm y (Subgroup.mem_centralizer_singleton_iff.mpr hy)
            rw [q8B_eq (ι := ι), Bool.and_eq_true]
            exact ⟨memB_iff.2 (List.mem_map.2 ⟨_, hya, by simp only [map_mul, map_inv]⟩),
              memB_iff.2 (List.mem_map.2 ⟨_, hyb, by simp only [map_mul, map_inv]⟩)⟩
          rw [hall] at hB'
          exact absurd hB' (by decide)
      · left
        obtain ⟨hNa, hNb⟩ := Bool.and_eq_true_iff.1 hC
        exact ⟨(hLN a).1 (memB_iff.1 hNa), (hLN b).1 (memB_iff.1 hNb)⟩
    · right; left
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
  · obtain ⟨hEd, h3⟩ := Bool.and_eq_true_iff.1 hE
    have hEdge := edgeless_of_edgelessB hι hL hEd
    rcases Bool.or_eq_true_iff.1 h3 with he | hA
    · right; right; right
      exact ⟨hEdge, he⟩
    · right; right; left
      exact ⟨hEdge, noActs3_of_noActs3B hι hL hB hA⟩

include hι hL in
theorem verdictPred_of_check {B : ℕ} (hB : B < 243) {N : Subgroup Y} {LN : List M}
    (hLN : ∀ y, ι y ∈ LN ↔ y ∈ N) {e3b : Bool} {reps : List M}
    (h : verdictCheck B LN L e3b reps = true) {r : Y} (hr : ι r ∈ reps) :
    VerdictPred N (e3b = true) r := by
  have h2 := (Bool.and_eq_true_iff.1 h).2
  have h3 := List.all_eq_true.1 h2 (ι r) hr
  have h4 : noOddB3 B (centB L (ι r)) = true ∧ pairsV B LN L e3b (ι r) (centB L (ι r)) = true :=
    Bool.and_eq_true_iff.1 h3
  exact ⟨noOddNormalAt3_of_noOddB3 hι hL h4.1, fun a b haa hbb hba hnorm =>
    pairVerdict_of_pairsV hι hL hB hLN h4.2 a b haa hbb hba hnorm⟩

include hι hL in
theorem cover_of_coverB {reps : List M} (h : coverB reps L = true) {t : Y} (ht : orderOf t = 2) :
    ∃ r : Y, ι r ∈ reps ∧ ∃ g : Y, g * t * g⁻¹ = r := by
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht, pow_two] at this
  have ht1 : t ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at ht
    omega
  have h1 := List.all_eq_true.1 h (ι t) ((hL _).2 ⟨t, rfl⟩)
  rcases Bool.or_eq_true_iff.1 h1 with hA | hB
  · exfalso
    have hP : ι t * ι t = 1 ∧ ι t ≠ 1 :=
      ⟨by rw [← map_mul, ht2, map_one], fun h2 => ht1 (hι (by rw [h2, map_one]))⟩
    rw [decide_eq_true hP] at hA
    exact absurd hA (by decide)
  · unfold isCovered at hB
    obtain ⟨gm, hgm, hg⟩ := List.any_eq_true.1 hB
    obtain ⟨rm, hrm, hrt⟩ := List.any_eq_true.1 hg
    obtain ⟨g, rfl⟩ := (hL gm).1 hgm
    have hrt' := of_decide_eq_true hrt
    refine ⟨g * t * g⁻¹, ?_, g, rfl⟩
    simpa only [map_mul, map_inv, hrt'] using hrm

include hι hL in
theorem phi_all_of_verdictCheck [Finite Y] {B : ℕ} (hB : B < 243) {N : Subgroup Y}
    {LN : List M} (hLN : ∀ y, ι y ∈ LN ↔ y ∈ N) (hN : N.Normal) (hNtop : N ≠ ⊤) {e3b : Bool}
    (hE3b : e3b = true → ∃ f : Y →* CFSG.Blueprint.NativeSporadic.Carrier .M12,
      Function.Surjective f ∧ IsPGroup 2 ↥f.ker)
    {reps : List M} (h : verdictCheck B LN L e3b reps = true) {t : Y} (ht : orderOf t = 2) :
    Phi t := by
  refine phi_of_reps (reps := {r : Y | ι r ∈ reps}) (fun r hr R S hd hc _ => ?_)
    (fun t ht => cover_of_coverB hι hL (Bool.and_eq_true_iff.1 h).1 ht) ht
  exact verdict_of_verdictPred hN hNtop hE3b hd hc (verdictPred_of_check hι hL hB hLN h hr)

end Sound

end CFSG.ClassicalInvolution.Q3.TA3

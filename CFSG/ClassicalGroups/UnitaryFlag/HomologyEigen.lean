module

public import CFSG.ClassicalGroups.UnitaryFlag.InvolutionCenters

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {m : ℕ} {K : Type} [Field K]

theorem smul_subOne_of_commute (h : UnitaryFieldData 2 m K) {a t : unitarySU 2 m K 3}
    (hat : a * t = t * a) (x : Fin 3 → K) :
    a • subOne t x = subOne t (a • x) := by
  rw [subOne_apply h, subOne_apply h, smul_sub, ← mul_smul, ← mul_smul, hat]

theorem pow_smul_eq_smul_pow {a : unitarySU 2 m K 3} {e : Fin 3 → K} {c : K}
    (he : a • e = c • e) (k : ℕ) : (a ^ k) • e = c ^ k • e := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', mul_smul, ih, smul_comm, he, smul_smul, ← pow_succ]

theorem smul_eq_of_pow_smul_eq_of_coprime {a : unitarySU 2 m K 3} {c : K} {r k : ℕ}
    (har : a ^ r = 1) (hcr : c ^ r = 1) (hk : Nat.Coprime k r) (hr : 1 < r)
    {x : Fin 3 → K} (hx : (a ^ k) • x = (c ^ k) • x) : a • x = c • x := by
  obtain ⟨u, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hk hr
  have hku : k * u = r * (k * u / r) + 1 := by
    have h1 := Nat.div_add_mod (k * u) r
    omega
  have ha : a ^ (k * u) = a := by
    rw [hku, pow_add, pow_mul, har, one_pow, one_mul, pow_one]
  have hc : c ^ (k * u) = c := by
    rw [hku, pow_add, pow_mul, hcr, one_pow, one_mul, pow_one]
  have key : ∀ j : ℕ, ((a ^ k) ^ j) • x = ((c ^ k) ^ j) • x := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [pow_succ', mul_smul, ih, smul_comm (a ^ k) ((c ^ k) ^ j) x, hx, smul_smul,
          ← pow_succ]
  have h1 := key u
  rwa [← pow_mul, ha, ← pow_mul, hc] at h1

theorem scalar_or_homology_of_commute_involution (h : UnitaryFieldData 2 m K) {r : ℕ}
    (hr : Odd r) {a t : unitarySU 2 m K 3} (har : a ^ r = 1) (ht : t ^ 2 = 1) (ht1 : t ≠ 1)
    (hat : a * t = t * a) :
    (∃ c : K, ∀ x : Fin 3 → K, a • x = c • x) ∨
      ∃ (v : Fin 3 → K) (c d : K), stdHermForm h 3 v v ≠ 0 ∧ c ≠ 0 ∧ c ≠ d ∧ a • v = d • v ∧
        ∀ w : Fin 3 → K, stdHermForm h 3 v w = 0 → a • w = c • w := by
  classical
  have htwo : (2 : K) = 0 := (h.charP.cast_eq_zero_iff 2).mpr (dvd_refl 2)
  have hself : ∀ y : Fin 3 → K, y + y = 0 := by
    intro y
    rw [← two_smul (R := K) y, htwo, zero_smul]
  have hneg : ∀ y : Fin 3 → K, -y = y := by
    intro y
    rw [neg_eq_iff_add_eq_zero]
    exact hself y
  rcases eq_or_ne r 1 with rfl | hr1
  · refine Or.inl ⟨1, fun x => ?_⟩
    rw [pow_one] at har
    rw [har]
    simp
  have hr2 : 1 < r := by
    obtain ⟨k, hk⟩ := hr
    rw [hk] at hr1 ⊢
    omega
  have hcop2 : Nat.Coprime 2 r := (Odd.coprime_two_right hr).symm
  have hcop4 : Nat.Coprime 4 r := by
    simpa using (Nat.coprime_pow_left_iff (n := 2) (by norm_num) 2 r).mpr hcop2
  obtain ⟨hLmem, -, hker⟩ := involution_mem_isotropicTransvectionGroup h ht ht1
  obtain ⟨e, he0, -, hLe⟩ := exists_eq_span_of_mem_isotropicLines hLmem
  have heL : e ∈ LinearMap.range (subOne t) := by
    rw [hLe]
    exact Submodule.mem_span_singleton_self e
  have haL : ∀ x ∈ LinearMap.range (subOne t), a • x ∈ LinearMap.range (subOne t) := by
    rintro x ⟨y, rfl⟩
    exact ⟨a • y, (smul_subOne_of_commute h hat y).symm⟩
  obtain ⟨lam, hlam⟩ : ∃ lam : K, a • e = lam • e := by
    have hmem : a • e ∈ K ∙ e := by
      rw [← hLe]
      exact haL e heL
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    exact ⟨c, hc.symm⟩
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hlam
    have h1 : a⁻¹ • (a • e) = a⁻¹ • (0 : Fin 3 → K) := by rw [hlam]
    rw [← mul_smul, inv_mul_cancel, one_smul, smul_zero] at h1
    exact he0 h1
  have hlampow : lam ^ r = 1 := by
    have h1 : lam ^ r • e = e := by
      rw [← pow_smul_eq_smul_pow hlam r, har, one_smul]
    have h2 : (lam ^ r - 1) • e = 0 := by rw [sub_smul, one_smul, h1, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 he0
  have hact : ∀ l ∈ LinearMap.range (subOne t), a • l = lam • l := by
    intro l hl
    have hmem : l ∈ K ∙ e := by
      rw [← hLe]
      exact hl
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    rw [← hc, smul_comm a c e, hlam, smul_smul, smul_smul, mul_comm c lam]
  have haP : ∀ x ∈ hermPerp h (LinearMap.range (subOne t)),
      a • x ∈ hermPerp h (LinearMap.range (subOne t)) := by
    intro x hx
    rw [← hker, LinearMap.mem_ker] at hx ⊢
    rw [← smul_subOne_of_commute h hat x, hx, smul_zero]
  have hTperp : ∀ x : Fin 3 → K,
      a • x - lam • x ∈ hermPerp h (LinearMap.range (subOne t)) := by
    intro x
    rw [← hker, LinearMap.mem_ker]
    have h2 : subOne t x ∈ K ∙ e := by
      rw [← hLe]
      exact LinearMap.mem_range_self (subOne t) x
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h2
    rw [map_sub, LinearMap.map_smul (subOne t) lam x, ← smul_subOne_of_commute h hat x, ← hc,
      smul_comm a c e, hlam, smul_smul, smul_smul, mul_comm c lam, sub_self]
  by_cases hcase : ∀ z ∈ hermPerp h (LinearMap.range (subOne t)),
      a • z - lam • z ∈ LinearMap.range (subOne t)
  · left
    refine ⟨lam, fun x => ?_⟩
    have hA2 : ∀ x : Fin 3 → K, ∃ l ∈ LinearMap.range (subOne t),
        a • (a • x) = lam • (lam • x) + l := by
      intro x
      refine ⟨a • (a • x - lam • x) - lam • (a • x - lam • x), hcase _ (hTperp x), ?_⟩
      have h3 : lam • (a • x - lam • x) + lam • (a • x) = lam • (lam • x) := by
        rw [← smul_add]
        congr 1
        have h5 : a • x + a • x = 0 := hself (a • x)
        calc (a • x - lam • x) + a • x = (a • x + a • x) - lam • x := by abel
          _ = 0 - lam • x := by rw [h5]
          _ = lam • x := by rw [zero_sub, hneg]
      calc a • (a • x) = a • (a • x - lam • x) + lam • (a • x) := by
              rw [smul_sub, smul_comm a lam x, sub_add_cancel]
        _ = (a • (a • x - lam • x) - lam • (a • x - lam • x))
              + (lam • (a • x - lam • x) + lam • (a • x)) := by abel
        _ = (a • (a • x - lam • x) - lam • (a • x - lam • x)) + lam • (lam • x) := by
              rw [h3]
        _ = lam • (lam • x) + (a • (a • x - lam • x) - lam • (a • x - lam • x)) := by
              abel
    have hA2l : ∀ l ∈ LinearMap.range (subOne t), a • (a • l) = lam • (lam • l) := by
      intro l hl
      rw [hact l hl, smul_comm a lam l, hact l hl]
    have h4 : ∀ x : Fin 3 → K, (a ^ 4) • x = lam ^ 4 • x := by
      intro x
      obtain ⟨l, hlL, hl⟩ := hA2 x
      have h2 : (a ^ 2) • x = lam ^ 2 • x + l := by
        rw [pow_two, mul_smul, pow_two, ← smul_smul]
        exact hl
      have h3 : (a ^ 2) • l = lam ^ 2 • l := by
        rw [pow_two, mul_smul, pow_two, ← smul_smul]
        exact hA2l l hlL
      have h2' : (a ^ 2) • (lam ^ 2 • x) = lam ^ 2 • ((a ^ 2) • x) :=
        smul_comm (a ^ 2) (lam ^ 2) x
      have h1 : (a ^ 4) • x = (a ^ 2) • ((a ^ 2) • x) := by
        rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, mul_smul]
      calc (a ^ 4) • x = (a ^ 2) • ((a ^ 2) • x) := h1
        _ = (a ^ 2) • (lam ^ 2 • x + l) := by rw [h2]
        _ = (a ^ 2) • (lam ^ 2 • x) + (a ^ 2) • l := by rw [smul_add]
        _ = lam ^ 2 • ((a ^ 2) • x) + lam ^ 2 • l := by rw [h2', h3]
        _ = lam ^ 2 • (lam ^ 2 • x + l) + lam ^ 2 • l := by rw [h2]
        _ = (lam ^ 2 • (lam ^ 2 • x) + lam ^ 2 • l) + lam ^ 2 • l := by rw [smul_add]
        _ = lam ^ 2 • (lam ^ 2 • x) := by
              rw [add_assoc, hself, add_zero]
        _ = lam ^ 4 • x := by
              rw [smul_smul]
              congr 1
              ring
    exact smul_eq_of_pow_smul_eq_of_coprime har hlampow hcop4 hr2 (h4 x)
  · right
    push Not at hcase
    obtain ⟨z, hzmem, hznotL⟩ := hcase
    have hzL : z ∉ LinearMap.range (subOne t) := by
      intro hz
      apply hznotL
      rw [hact z hz, sub_self]
      exact Submodule.zero_mem _
    have hP : hermPerp h (LinearMap.range (subOne t)) = Submodule.span K {e, z} :=
      hermPerp_eq_span_pair h hLmem hLe hzmem hzL
    have haz : a • z ∈ Submodule.span K {e, z} := by
      rw [← hP]
      exact haP z hzmem
    obtain ⟨al, de, hald⟩ := Submodule.mem_span_pair.mp haz
    have hde : lam ≠ de := by
      rintro rfl
      apply hznotL
      have h1 : a • z - lam • z = al • e := by rw [← hald]; abel
      rw [h1, hLe]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)
    have hdlam : de - lam ≠ 0 := sub_ne_zero.mpr (Ne.symm hde)
    set v : Fin 3 → K := z + (al / (de - lam)) • e with hvdef
    have hvP : v ∈ hermPerp h (LinearMap.range (subOne t)) := by
      rw [hP, hvdef]
      exact Submodule.add_mem _ (Submodule.subset_span (by simp))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    have hvL : v ∉ LinearMap.range (subOne t) := by
      intro hv
      apply hzL
      have h1 : z = v - (al / (de - lam)) • e := by rw [hvdef]; abel
      rw [h1]
      exact Submodule.sub_mem _ hv (Submodule.smul_mem _ _ heL)
    have hvv : stdHermForm h 3 v v ≠ 0 :=
      stdHermForm_self_ne_zero_of_mem_hermPerp h hLmem hvP hvL
    have hav : a • v = de • v := by
      have hcoef : al + al / (de - lam) * lam = de * (al / (de - lam)) := by
        field_simp
        ring
      calc a • v = a • z + (al / (de - lam)) • (a • e) := by
              rw [hvdef, smul_add, smul_comm a (al / (de - lam)) e]
        _ = (al • e + de • z) + (al / (de - lam)) • (lam • e) := by rw [← hald, hlam]
        _ = (al + al / (de - lam) * lam) • e + de • z := by
              rw [smul_smul, add_smul]
              abel
        _ = (de * (al / (de - lam))) • e + de • z := by rw [hcoef]
        _ = de • v := by
              rw [hvdef, smul_add, smul_smul]
              abel
    have hv0 : v ≠ 0 := fun h0 => hvL (h0 ▸ Submodule.zero_mem _)
    have hde0 : de ≠ 0 := by
      intro h0
      have h1 : a • v = 0 := by rw [hav, h0, zero_smul]
      have h3 : a⁻¹ • (a • v) = a⁻¹ • (0 : Fin 3 → K) := by rw [h1]
      rw [← mul_smul, inv_mul_cancel, one_smul, smul_zero] at h3
      exact hv0 h3
    have hbarde : h.bar de ≠ 0 := by
      intro h0
      apply hde0
      rw [← h.bar_bar de, h0, map_zero]
    have hPv : hermPerp h (LinearMap.range (subOne t)) = Submodule.span K {e, v} :=
      hermPerp_eq_span_pair h hLmem hLe hvP hvL
    have hBve : stdHermForm h 3 v e = 0 := by
      rw [← (stdHermForm_isSymm h 3).eq e v, (mem_hermPerp.mp hvP) e heL, map_zero]
    refine ⟨v, lam, de, hvv, hlam0, hde, hav, fun w hw => ?_⟩
    have hTwP : a • w - lam • w ∈ hermPerp h (LinearMap.range (subOne t)) := hTperp w
    have hawe : stdHermForm h 3 v (a • w) = 0 := by
      have hiso : stdHermForm h 3 (a • v) (a • w) = stdHermForm h 3 v w :=
        stdHermForm_smul_smul h a v w
      rw [hav, hw, LinearMap.map_smulₛₗ (stdHermForm h 3) de v, LinearMap.smul_apply,
        smul_eq_mul] at hiso
      exact (mul_eq_zero.mp hiso).resolve_left hbarde
    have horth : stdHermForm h 3 v (a • w - lam • w) = 0 := by
      have h2 : stdHermForm h 3 v (lam • w) = 0 := by
        rw [LinearMap.map_smul (stdHermForm h 3 v) lam w, hw, smul_zero]
      rw [map_sub, hawe, h2, sub_self]
    have hTwS : a • w - lam • w ∈ Submodule.span K {e, v} := by
      rw [← hPv]
      exact hTwP
    obtain ⟨kap, tau, hkt⟩ := Submodule.mem_span_pair.mp hTwS
    have htau : tau = 0 := by
      have h1 : stdHermForm h 3 v (a • w - lam • w)
          = kap * stdHermForm h 3 v e + tau * stdHermForm h 3 v v := by
        rw [← hkt, map_add, LinearMap.map_smul (stdHermForm h 3 v) kap e,
          LinearMap.map_smul (stdHermForm h 3 v) tau v, smul_eq_mul, smul_eq_mul]
      rw [horth, hBve, mul_zero, zero_add] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_right hvv
    have hTwL : a • w - lam • w = kap • e := by
      rw [← hkt, htau, zero_smul, add_zero]
    have h2w : (a ^ 2) • w = lam ^ 2 • w := by
      have haw : a • w = lam • w + kap • e := by rw [← hTwL]; abel
      have h1 : (a ^ 2) • w = a • (a • w) := by rw [pow_two, mul_smul]
      have h2 : a • (a • w) = lam • (lam • w + kap • e) + kap • (lam • e) := by
        rw [haw, smul_add, smul_comm a lam w, smul_comm a kap e, haw, hlam]
      have h3 : lam • (lam • w + kap • e) + kap • (lam • e) = lam ^ 2 • w := by
        rw [smul_add, smul_smul, smul_smul, smul_smul, pow_two, mul_comm kap lam, add_assoc,
          hself, add_zero]
      rw [h1, h2, h3]
    exact smul_eq_of_pow_smul_eq_of_coprime har hlampow hcop2 hr2 h2w

end CFSG.ClassicalGroups.UnitaryFlag

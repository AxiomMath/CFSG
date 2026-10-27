module

public import CFSG.Fischer.Classification.PartII.O2Section

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer LocalU O2Twin

namespace O2Mod

variable {H : Type} [Group H] {E μ : Set H}

section Affine

variable {X : Type} [Group X] {E : Set X}

theorem Pair.affine_identity (hP : Pair X E) {d e z : X} (hd : d ∈ E) (he : e ∈ E)
    (hz : z ∈ E) (hde : d * e ≠ e * d) (hzl : z * (d * e * d) ≠ d * e * d * z) :
    e = d * e * d * (e * z * e) * (d * e * d) * (d * z * d) *
      (d * e * d * (e * z * e) * (d * e * d)) := by
  have hd2 : d * d = 1 := Pair.mul_self hP hd
  have hx3 : (d * e) ^ 3 = 1 := by
    rw [← Pair.orderOf_mul_eq_three hP hd he hde, pow_orderOf_eq_one]
  have hxy3 : (d * e * d * z) ^ 3 = 1 := by
    rw [← Pair.orderOf_mul_eq_three hP (Pair.mul_mul_mem hP hd he) hz fun h => hzl h.symm,
      pow_orderOf_eq_one]
  have he' : e = d * (d * e) := by rw [← mul_assoc, hd2, one_mul]
  have hz' : z = d * (d * z) := by rw [← mul_assoc, hd2, one_mul]
  set x := d * e with hx
  set y := d * z with hy
  have hxd : d * x * d = x⁻¹ := by
    rw [hx, mul_inv_rev, Pair.inv_eq hP hd, Pair.inv_eq hP he, ← mul_assoc, hd2, one_mul]
  have hyd : d * y * d = y⁻¹ := by
    rw [hy, mul_inv_rev, Pair.inv_eq hP hd, Pair.inv_eq hP hz, ← mul_assoc, hd2, one_mul]
  have hxd' : d * x⁻¹ * d = x := by
    rw [← hxd]
    calc d * (d * x * d) * d = (d * d) * x * (d * d) := by group
      _ = x := by rw [hd2, one_mul, mul_one]
  have hconj3 : ∀ u v w : X, d * (u * v * w) * d = (d * u * d) * (d * v * d) * (d * w * d) := by
    intro u v w
    calc d * (u * v * w) * d = d * u * (d * d) * v * (d * d) * w * d := by
          rw [hd2]; group
      _ = (d * u * d) * (d * v * d) * (d * w * d) := by group
  have hpt : ∀ n m : X, (n * d) * (m * d) * (n * d) = n * (d * m * d) * n * d := by
    intro n m; group
  have hxx : x * x = x⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← hx3]; simp only [pow_succ, pow_zero, one_mul]
  have hxy : (x * y) * (x * y) * (x * y) = 1 := by
    have : x * y = x * d * z := by simp only [hx, hy, mul_assoc]
    rw [this, ← hxy3]; simp only [pow_succ, pow_zero, one_mul]
  have hee : e = x⁻¹ * d := by
    rw [← hxd, mul_assoc (d * x) d d, hd2, mul_one]
    exact he'
  have hb : e * z * e = (x⁻¹ * y * x⁻¹) * d := by
    rw [hee, hz']
    calc x⁻¹ * d * (d * y) * (x⁻¹ * d) = x⁻¹ * (d * d) * y * x⁻¹ * d := by group
      _ = x⁻¹ * y * x⁻¹ * d := by rw [hd2, mul_one]
  have hab : (x * d) * ((x⁻¹ * y * x⁻¹) * d) * (x * d) = (x⁻¹ * y⁻¹ * x⁻¹) * d := by
    rw [hpt, hconj3, hxd', hyd]
    calc x * (x * y⁻¹ * x) * x * d = (x * x) * y⁻¹ * (x * x) * d := by group
      _ = x⁻¹ * y⁻¹ * x⁻¹ * d := by rw [hxx]
  have habc : ((x⁻¹ * y⁻¹ * x⁻¹) * d) * (y * d) * ((x⁻¹ * y⁻¹ * x⁻¹) * d) = x⁻¹ * d := by
    rw [hpt, hyd]
    have h1 : (x * y)⁻¹ * (x * y)⁻¹ * (x * y)⁻¹ = 1 := by
      rw [← mul_inv_rev, ← mul_inv_rev, ← mul_assoc, hxy, inv_one]
    calc x⁻¹ * y⁻¹ * x⁻¹ * y⁻¹ * (x⁻¹ * y⁻¹ * x⁻¹) * d
        = x⁻¹ * ((x * y)⁻¹ * (x * y)⁻¹ * (x * y)⁻¹) * d := by group
      _ = x⁻¹ * d := by rw [h1, mul_one]
  have hc : d * z * d = y * d := rfl
  rw [hb, hab, habc, ← hee]

end Affine

theorem not_commute_of_isTwin' {g g' f : H} (h : IsTwin E g g') (hf : f ∈ E)
    (hfg : f * g ≠ g * f) : f * g' ≠ g' * f := fun e =>
  (not_commute_of_isTwin h hf fun e' => hfg e'.symm) e.symm


noncomputable def mate (E μ : Set H) (f g : H) : H :=
  Classical.epsilon fun g' => g' ∈ twinClass E g ∧ g' ∉ μ ∧ f * g' * f ∈ μ

namespace IsTwinSection

variable (hμ : IsTwinSection E μ) (hP : Pair H E)
include hμ hP

theorem mate_spec {f g : H} (hf : f ∈ E) (hfμ : f ∉ μ) (hg : g ∈ E) (hfg : f * g ≠ g * f) :
    mate E μ f g ∈ twinClass E g ∧ mate E μ f g ∉ μ ∧ f * mate E μ f g * f ∈ μ :=
  Classical.epsilon_spec (hμ.existsUnique_match hP hf hfμ hg hfg).exists

theorem mate_eq {f g g' : H} (hf : f ∈ E) (hfμ : f ∉ μ) (hg : g ∈ E) (hfg : f * g ≠ g * f)
    (h1 : g' ∈ twinClass E g) (h2 : g' ∉ μ) (h3 : f * g' * f ∈ μ) : mate E μ f g = g' :=
  (hμ.existsUnique_match hP hf hfμ hg hfg).unique (hμ.mate_spec hP hf hfμ hg hfg) ⟨h1, h2, h3⟩

theorem mate_mem {f g : H} (hf : f ∈ E) (hfμ : f ∉ μ) (hg : g ∈ E) (hfg : f * g ≠ g * f) :
    mate E μ f g ∈ E :=
  (hμ.mate_spec hP hf hfμ hg hfg).1.2.1

theorem mate_notMem {f g : H} (hf : f ∈ E) (hfμ : f ∉ μ) (hg : g ∈ E) (hfg : f * g ≠ g * f) :
    mate E μ f g ∉ μ :=
  (hμ.mate_spec hP hf hfμ hg hfg).2.1

theorem isTwin_mate {f g : H} (hf : f ∈ E) (hfμ : f ∉ μ) (hg : g ∈ E) (hfg : f * g ≠ g * f) :
    IsTwin E g (mate E μ f g) :=
  (hμ.mate_spec hP hf hfμ hg hfg).1

theorem mul_mate_mul_mem {f g : H} (hf : f ∈ E) (hfμ : f ∉ μ) (hg : g ∈ E)
    (hfg : f * g ≠ g * f) : f * mate E μ f g * f ∈ μ :=
  (hμ.mate_spec hP hf hfμ hg hfg).2.2

theorem mate_not_commute {f g : H} (hf : f ∈ E) (hfμ : f ∉ μ) (hg : g ∈ E)
    (hfg : f * g ≠ g * f) : f * mate E μ f g ≠ mate E μ f g * f := fun e =>
  (not_commute_of_isTwin (hμ.isTwin_mate hP hf hfμ hg hfg) hf fun e' => hfg e'.symm) e.symm

theorem mate_congr {f g g' : H} (hf : f ∈ E) (hfμ : f ∉ μ) (hg : g ∈ E) (hfg : f * g ≠ g * f)
    (h : IsTwin E g g') : mate E μ f g' = mate E μ f g := by
  have hg' := h.2.1
  have hfg' : f * g' ≠ g' * f := fun e =>
    (not_commute_of_isTwin h hf fun e' => hfg e'.symm) e.symm
  refine hμ.mate_eq hP hf hfμ hg' hfg' ?_ (hμ.mate_notMem hP hf hfμ hg hfg)
    (hμ.mul_mate_mul_mem hP hf hfμ hg hfg)
  rw [mem_twinClass]
  exact isTwin_trans (isTwin_symm h) (hμ.isTwin_mate hP hf hfμ hg hfg)

theorem mate_mate {f g : H} (hf : f ∈ E) (hfμ : f ∉ μ) (hg : g ∈ E) (hfg : f * g ≠ g * f) :
    mate E μ (mate E μ f g) f = f := by
  set g' := mate E μ f g
  have hg'E := hμ.mate_mem hP hf hfμ hg hfg
  have hg'f : g' * f ≠ f * g' := fun e => hμ.mate_not_commute hP hf hfμ hg hfg e.symm
  refine hμ.mate_eq hP hg'E (hμ.mate_notMem hP hf hfμ hg hfg) hf hg'f (self_mem_twinClass hf)
    hfμ ?_
  rw [← Pair.mul_mul_eq hP hf hg'E fun e => hg'f e.symm]
  exact hμ.mul_mate_mul_mem hP hf hfμ hg hfg

theorem mate_conj {s f : H} (hs : s ∈ μ) (hf : f ∈ E) (hfμ : f ∉ μ) (hsf : s * f ≠ f * s) :
    mate E μ f (s * f * s) = s * f * s := by
  obtain ⟨-, -, hE, hnμ, hc, hm⟩ := hμ.isMatch_conj hP hs hf hfμ hsf
  exact hμ.mate_eq hP hf hfμ hE hc (self_mem_twinClass hE) hnμ hm

theorem mate_mate_mate_of_isTwin {f g k : H} (hf : f ∈ E) (hfμ : f ∉ μ) (hg : g ∈ E)
    (hfg : f * g ≠ g * f) (hk : IsTwin E (f * g * f) k) :
    mate E μ (mate E μ (mate E μ f g) k) f = f := by
  have hfE := hf
  have hkE := hk.2.1
  set f' := mate E μ f g with hf'
  have hf'E := hμ.mate_mem hP hf hfμ hg hfg
  have hf'μ := hμ.mate_notMem hP hf hfμ hg hfg
  have hgf' := hμ.isTwin_mate hP hf hfμ hg hfg
  have hff' := hμ.mate_not_commute hP hf hfμ hg hfg
  have h1 : IsTwin E (f * g * f) (f * f' * f) := by
    have := isTwin_conj hP f hgf'
    rwa [Pair.inv_eq hP hf] at this
  have hsk : f * f' * f = sec E μ k :=
    hμ.eq_sec (hμ.mul_mate_mul_mem hP hf hfμ hg hfg) (isTwin_trans (isTwin_symm hk) h1)
  have hgk : g * k ≠ k * g := by
    have h := Pair.mul_mul_not_commute_right hP hf hg hfg
    exact not_commute_of_isTwin' hk hg fun e => h e.symm
  have hf'k : f' * k ≠ k * f' := by
    have := not_commute_of_isTwin hgf' hkE hgk
    exact this
  set f'' := mate E μ f' k with hf''
  have hf''E := hμ.mate_mem hP hf'E hf'μ hkE hf'k
  have hkf'' := hμ.isTwin_mate hP hf'E hf'μ hkE hf'k
  have h2 : IsTwin E f (f' * f'' * f') := by
    have e1 : IsTwin E (g * k * g) (f' * f'' * f') := by
      have a := Pair.isTwin_mul_mul hP (isTwin_symm hgf') hkE hf'k
      have b := isTwin_conj hP f' hkf''
      rw [Pair.inv_eq hP hf'E] at b
      exact isTwin_trans (isTwin_symm a) b
    have e2 : IsTwin E f (g * k * g) := by
      have := isTwin_conj hP g hk
      rwa [Pair.inv_eq hP hg, Pair.mul_mul_eq hP hf hg hfg,
        Pair.mul_mul_mul_mul hP hg] at this
    exact isTwin_trans e2 e1
  have hsf : f' * f'' * f' = sec E μ f :=
    hμ.eq_sec (hμ.mul_mate_mul_mem hP hf'E hf'μ hkE hf'k) h2
  have hfk : f * k ≠ k * f := by
    have h := Pair.mul_mul_not_commute_left hP hf hfg
    exact not_commute_of_isTwin' hk hf fun e => h e.symm
  have hf''f : f'' * f ≠ f * f'' := fun e =>
    not_commute_of_isTwin' hkf'' hf hfk e.symm
  have hsg : sec E μ f * sec E μ k * sec E μ f = sec E μ g := by
    rw [← hμ.sec_mul_mul hP hf hkE hfk]
    refine hμ.sec_eq_sec ?_
    have := isTwin_conj hP f (isTwin_symm hk)
    rwa [Pair.inv_eq hP hf, Pair.mul_mul_mul_mul hP hf] at this
  have hmem : f'' * f * f'' ∈ μ := by
    have e1 : f'' = f' * sec E μ f * f' := by
      rw [← hsf, Pair.mul_mul_mul_mul hP hf'E]
    have hf'sg : f' * sec E μ g = sec E μ g * f' :=
      (isTwin_trans (isTwin_symm hgf') (hμ.isTwin_sec hg)).2.2.1
    have e2 : f'' * f * f'' = f' * (sec E μ f * (f' * f * f') * sec E μ f) * f' := by
      rw [e1]; simp only [mul_assoc]
    rw [e2, ← Pair.mul_mul_eq hP hf hf'E hff', hsk, hsg,
      (Pair.mul_mul_eq_self_iff hP hf'E _).2 hf'sg]
    exact hμ.sec_mem hg
  exact hμ.mate_eq hP hf''E (hμ.mate_notMem hP hf'E hf'μ hkE hf'k) hfE hf''f
    (self_mem_twinClass hfE) hfμ hmem

theorem mate_mate_mate_of_commute {f g k : H} (hf : f ∈ E) (hfμ : f ∉ μ) (hg : g ∈ E)
    (hk : k ∈ E) (hfg : f * g ≠ g * f) (hgk : g * k ≠ k * g) (hfk : f * k ≠ k * f)
    (hc : k * (f * g * f) = f * g * f * k) :
    mate E μ (mate E μ (mate E μ f g) k) f = f := by
  set f' := mate E μ f g with hf'
  have hf'E := hμ.mate_mem hP hf hfμ hg hfg
  have hf'μ := hμ.mate_notMem hP hf hfμ hg hfg
  have hgf' := hμ.isTwin_mate hP hf hfμ hg hfg
  have hff' := hμ.mate_not_commute hP hf hfμ hg hfg
  have hf'k : f' * k ≠ k * f' := not_commute_of_isTwin hgf' hk hgk
  set f'' := mate E μ f' k with hf''
  have hf''E := hμ.mate_mem hP hf'E hf'μ hk hf'k
  have hkf'' := hμ.isTwin_mate hP hf'E hf'μ hk hf'k
  have hf''f : f'' * f ≠ f * f'' := fun e => not_commute_of_isTwin' hkf'' hf hfk e.symm
  have hga : IsTwin E (f * g * f) (f * f' * f) := by
    have := isTwin_conj hP f hgf'
    rwa [Pair.inv_eq hP hf] at this
  have hka : f'' * (f * f' * f) = f * f' * f * f'' := by
    have h1 := (hkf''.2.2.2 _ (Pair.mul_mul_mem hP hf hg)).1 hc.symm
    exact (hga.2.2.2 _ hf''E).1 h1.symm
  have hbf : f * (f' * f'' * f') = f' * f'' * f' * f := by
    have h1 := (conj_commute_iff f' f'' (f * f' * f)).2 hka
    rw [Pair.inv_eq hP hf'E, Pair.mul_mul_eq hP hf hf'E hff', Pair.mul_mul_mul_mul hP hf'E] at h1
    exact h1.symm
  have hab : f * f' * f * (f' * f'' * f') * (f * f' * f) = f * f'' * f := by
    have e1 : f * f' * f * (f' * f'' * f') * (f * f' * f) =
        f * f' * (f * (f' * f'' * f') * f) * f' * f := by simp only [mul_assoc]
    rw [e1, hbf, mul_assoc (f' * f'' * f') f f, Pair.mul_self hP hf, mul_one]
    calc f * f' * (f' * f'' * f') * f' * f = f * (f' * f') * f'' * (f' * f') * f := by group
      _ = f * f'' * f := by rw [Pair.mul_self hP hf'E, mul_one, mul_one]
  have hmem : f'' * f * f'' ∈ μ := by
    rw [← Pair.mul_mul_eq hP hf hf''E fun e => hf''f e.symm, ← hab]
    exact hμ.mul_mul_mem _ (hμ.mul_mate_mul_mem hP hf hfμ hg hfg) _
      (hμ.mul_mate_mul_mem hP hf'E hf'μ hk hf'k)
  exact hμ.mate_eq hP hf''E (hμ.mate_notMem hP hf'E hf'μ hk hf'k) hf hf''f
    (self_mem_twinClass hf) hfμ hmem

theorem mate_mate_mate_ne_of_affine {f g k : H} (hf : f ∈ E) (hfμ : f ∉ μ) (hg : g ∈ E)
    (hk : k ∈ E) (hfg : f * g ≠ g * f) (hgk : g * k ≠ k * g) (hfk : f * k ≠ k * f)
    (hc : k * (f * g * f) ≠ f * g * f * k) :
    mate E μ (mate E μ (mate E μ f g) k) f ≠ f := by
  intro heq
  set f' := mate E μ f g with hf'
  have hf'E := hμ.mate_mem hP hf hfμ hg hfg
  have hf'μ := hμ.mate_notMem hP hf hfμ hg hfg
  have hgf' := hμ.isTwin_mate hP hf hfμ hg hfg
  have hff' := hμ.mate_not_commute hP hf hfμ hg hfg
  have hf'k : f' * k ≠ k * f' := not_commute_of_isTwin hgf' hk hgk
  set f'' := mate E μ f' k with hf''
  have hf''E := hμ.mate_mem hP hf'E hf'μ hk hf'k
  have hkf'' := hμ.isTwin_mate hP hf'E hf'μ hk hf'k
  have hf''f : f'' * f ≠ f * f'' := fun e => not_commute_of_isTwin' hkf'' hf hfk e.symm
  have hcμ : f * f'' * f ∈ μ := by
    have := hμ.mul_mate_mul_mem hP hf''E (hμ.mate_notMem hP hf'E hf'μ hk hf'k) hf hf''f
    rwa [heq, Pair.mul_mul_eq hP hf''E hf hf''f] at this
  have hga : IsTwin E (f * g * f) (f * f' * f) := by
    have := isTwin_conj hP f hgf'
    rwa [Pair.inv_eq hP hf] at this
  have hka : f'' * (f * f' * f) ≠ f * f' * f * f'' := by
    intro h
    have h2 := (hga.2.2.2 _ hf''E).2 h
    have h3 := (hkf''.2.2.2 _ (Pair.mul_mul_mem hP hf hg)).2 h2.symm
    exact hc h3.symm
  have hid := Pair.affine_identity hP hf hf'E hf''E hff' hka
  apply hf'μ
  rw [hid]
  have ha := hμ.mul_mate_mul_mem hP hf hfμ hg hfg
  have hb := hμ.mul_mate_mul_mem hP hf'E hf'μ hk hf'k
  exact hμ.mul_mul_mem _ (hμ.mul_mul_mem _ ha _ hb) _ hcμ

end IsTwinSection


end O2Mod

end CFSG.Fischer.Classification

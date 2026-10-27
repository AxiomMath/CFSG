module

public import CFSG.CGT.PushingUpLit.CGT6.RouteCSound
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.CGT.PushingUpLit.CGT6.RouteC

section Abstract

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def comm2 (f : Module.End (ZMod 2) V) : Submodule (ZMod 2) V := LinearMap.range (f - 1)

theorem mem_comm2 {f : Module.End (ZMod 2) V} {v : V} : v ∈ comm2 f ↔ ∃ w, f w + w = v := by
  simp only [comm2, LinearMap.mem_range, ZModModule.sub_eq_add, LinearMap.add_apply,
    Module.End.one_apply]

theorem f3_apply {f : Module.End (ZMod 2) V} (h3 : f * f * f = 1) (v : V) : f (f (f v)) = v := by
  have := LinearMap.congr_fun h3 v
  simpa using this

theorem pair_independent {u v : V} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    LinearIndependent (ZMod 2) ![u, v] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have hs : s = 0 ∨ s = 1 := (by decide : ∀ s : ZMod 2, s = 0 ∨ s = 1) s
  have ht : t = 0 ∨ t = 1 := (by decide : ∀ s : ZMod 2, s = 0 ∨ s = 1) t
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · simp only [zero_smul, one_smul, zero_add] at h
    exact absurd h hv
  · simp only [zero_smul, one_smul, add_zero] at h
    exact absurd h hu
  · simp only [one_smul] at h
    exact absurd ((eq_neg_of_add_eq_zero_left h).trans (ZModModule.neg_eq_self v)) huv

theorem finrank_span_pair' {u v : V} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (huv : u ≠ v) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {u, v}) = 2 := by
  have hind := pair_independent hu0 hv0 huv
  have := finrank_span_eq_card hind
  have hr : Set.range ![u, v] = {u, v} := by
    ext x
    simp [or_comm]
  rw [hr, Fintype.card_fin] at this
  exact this

theorem span_pair_eq_of_finrank [Module.Finite (ZMod 2) V] {S : Submodule (ZMod 2) V}
    (hrk : Module.finrank (ZMod 2) S = 2) {u v : V} (hu : u ∈ S) (hv : v ∈ S) (hu0 : u ≠ 0)
    (hv0 : v ≠ 0) (huv : u ≠ v) : S = Submodule.span (ZMod 2) {u, v} := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · exact Submodule.span_le.mpr (Set.insert_subset hu (Set.singleton_subset_iff.mpr hv))
  · rw [finrank_span_pair' hu0 hv0 huv, hrk]

theorem f_f_of_mem {f : Module.End (ZMod 2) V} (h3 : f * f * f = 1) {w : V} (hw : w ∈ comm2 f) :
    f (f w) = w + f w := by
  have hf3 := f3_apply h3
  obtain ⟨v, rfl⟩ := mem_comm2.mp hw
  have e1 : f (f (f v + v)) = v + f (f v) := by rw [map_add, map_add, hf3]
  have e2 : (f v + v) + f (f v + v) = v + f (f v) := by
    rw [map_add]
    calc (f v + v) + (f (f v) + f v) = (v + f v) + (f v + f (f v)) := by
          rw [add_comm (f v) v, add_comm (f (f v)) (f v)]
      _ = v + f (f v) := ZModModule.add_add_add_cancel _ _ _
  rw [e1, e2]

theorem refl_basis [Module.Finite (ZMod 2) V] (f : Module.End (ZMod 2) V)
    (h3 : f * f * f = 1) (hrk : Module.finrank (ZMod 2) (comm2 f) = 2) :
    ∃ u : V, u ∈ comm2 f ∧ u ≠ 0 ∧ f u ≠ u ∧ f u ≠ 0 ∧ f (f u) = u + f u ∧
      comm2 f = Submodule.span (ZMod 2) {u, f u} := by
  have hf3 := f3_apply h3
  have hker : ∀ w ∈ comm2 f, f (f w) = w + f w := by
    intro w hw
    obtain ⟨v, rfl⟩ := mem_comm2.mp hw
    have e1 : f (f (f v + v)) = v + f (f v) := by rw [map_add, map_add, hf3]
    have e2 : (f v + v) + f (f v + v) = v + f (f v) := by
      rw [map_add]
      calc (f v + v) + (f (f v) + f v) = (v + f v) + (f v + f (f v)) := by
            rw [add_comm (f v) v, add_comm (f (f v)) (f v)]
        _ = v + f (f v) := ZModModule.add_add_add_cancel _ _ _
    rw [e1, e2]
  have hne : comm2 f ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hrk
    omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hfu0 : f u ≠ 0 := by
    intro h
    apply hu0
    rw [← hf3 u, h, map_zero, map_zero]
  have hfuu : f u ≠ u := by
    intro h
    obtain ⟨v, rfl⟩ := mem_comm2.mp hu
    rw [map_add] at h
    have h1 : f (f v) = v := by
      have := ZModModule.add_add_add_cancel (f (f v)) (f v) v
      rw [h, ZModModule.add_self] at this
      exact (eq_neg_of_add_eq_zero_left this.symm).trans (ZModModule.neg_eq_self v)
    have h2 : f v = v := by
      have := hf3 v
      rw [h1] at this
      exact this
    exact hu0 (by rw [h2, ZModModule.add_self])
  have hfu_mem : f u ∈ comm2 f := by
    have : f u = (f u + u) + u := by rw [add_assoc, ZModModule.add_self, add_zero]
    rw [this]
    exact Submodule.add_mem _ (mem_comm2.mpr ⟨u, rfl⟩) hu
  exact ⟨u, hu, hu0, hfuu, hfu0, hker u hu,
    span_pair_eq_of_finrank hrk hu hfu_mem hu0 hfu0 (Ne.symm hfuu)⟩

theorem t_apply_comm {f t : Module.End (ZMod 2) V} (hcomm : t * f = f * t) (x : V) :
    t (f x) = f (t x) := by
  have := LinearMap.congr_fun hcomm x
  simpa using this

theorem t_apply_t {t : Module.End (ZMod 2) V} (ht2 : t * t = 1) (x : V) : t (t x) = x := by
  have := LinearMap.congr_fun ht2 x
  simpa using this

theorem t_mem_comm2 {f t : Module.End (ZMod 2) V} (hcomm : t * f = f * t) {x : V}
    (hx : x ∈ comm2 f) : t x ∈ comm2 f := by
  obtain ⟨w, rfl⟩ := mem_comm2.mp hx
  exact mem_comm2.mpr ⟨t w, by rw [map_add, t_apply_comm hcomm]⟩

theorem t_fixes_basis {f t : Module.End (ZMod 2) V} {u : V} (hu0 : u ≠ 0) (hfu : f u ≠ u)
    (hfu0 : f u ≠ 0) (hf2 : f (f u) = u + f u) (hcomm : t * f = f * t) (ht2 : t * t = 1)
    (htA : t u ∈ Submodule.span (ZMod 2) {u, f u}) : t u = u ∧ t (f u) = f u := by
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp htA
  have ha : a = 0 ∨ a = 1 := (by decide : ∀ s : ZMod 2, s = 0 ∨ s = 1) a
  have hb : b = 0 ∨ b = 1 := (by decide : ∀ s : ZMod 2, s = 0 ∨ s = 1) b
  have htt := t_apply_t ht2 u
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · simp only [zero_smul, add_zero] at hab
    exact absurd (by rw [← htt, ← hab, map_zero]) hu0
  · simp only [zero_smul, one_smul, zero_add] at hab
    have h1 : t (f u) = u := by rw [← hab] at htt; exact htt
    have h2 : t (f u) = u + f u := by rw [t_apply_comm hcomm, ← hab, hf2]
    rw [h1] at h2
    have : f u = 0 := by simpa using h2.symm
    exact absurd this hfu0
  · simp only [zero_smul, one_smul, add_zero] at hab
    exact ⟨hab.symm, by rw [t_apply_comm hcomm, ← hab]⟩
  · simp only [one_smul] at hab
    have h2 : t (f u) = u := by
      rw [t_apply_comm hcomm, ← hab, map_add, hf2, add_left_comm, ZModModule.add_self, add_zero]
    have h3 : t (t u) = f u := by
      rw [← hab, map_add, ← hab, h2, add_comm u (f u), add_assoc, ZModModule.add_self, add_zero]
    exact absurd (h3.symm.trans htt) hfu

theorem sup_map_eq_top {y d t : Module.End (ZMod 2) V} {u : V} (ht2 : t * t = 1)
    (hy : comm2 y = Submodule.span (ZMod 2) {u, y u}) (htu : t u = u) (htyu : t (y u) = y u)
    (hcomm : comm2 y ⊔ comm2 d ⊔ comm2 t = ⊤) :
    comm2 y ⊔ comm2 d ⊔ (comm2 d).map t = ⊤ := by
  have hfix : ∀ a ∈ comm2 y, t a = a := by
    intro a ha
    rw [hy] at ha
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp ha
    simp only [map_add, map_smul, htu, htyu]
  set S := comm2 y ⊔ comm2 d ⊔ (comm2 d).map t with hS
  have hy_le : comm2 y ≤ S := le_sup_of_le_left le_sup_left
  have hd_le : comm2 d ≤ S := le_sup_of_le_left le_sup_right
  have htd_le : (comm2 d).map t ≤ S := le_sup_right
  have hct : comm2 t ≤ S := by
    intro x hx
    obtain ⟨w, rfl⟩ := mem_comm2.mp hx
    have hw : w ∈ comm2 y ⊔ comm2 d ⊔ comm2 t := by rw [hcomm]; trivial
    obtain ⟨ab, hab, c, hc, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hab
    obtain ⟨z, rfl⟩ := mem_comm2.mp hc
    have e1 : t (a + b + (t z + z)) + (a + b + (t z + z)) = t b + b := by
      rw [map_add, map_add, map_add, hfix a ha, t_apply_t ht2]
      calc a + t b + (z + t z) + (a + b + (t z + z))
          = (t b + b) + (a + a) + (z + z) + (t z + t z) := by abel
        _ = t b + b := by simp only [ZModModule.add_self, add_zero]
    rw [e1]
    exact S.add_mem (htd_le (Submodule.mem_map_of_mem hb)) (hd_le hb)
  rw [eq_top_iff, ← hcomm]
  exact sup_le (sup_le hy_le hd_le) hct

structure ChartVec (y d t : Module.End (ZMod 2) V) (e : Fin 6 → V)
    (a1 a2 b1 b2 c11 c12 c21 c22 c31 c32 c41 c42 : ZMod 2) : Prop where
  y0 : y (e 0) = e 1
  y1 : y (e 1) = e 0 + e 1
  y2 : y (e 2) = e 2 + a1 • e 0 + a2 • e 1
  y3 : y (e 3) = e 3 + b1 • e 0 + b2 • e 1
  y4 : y (e 4) = e 4 + a1 • e 0 + a2 • e 1
  y5 : y (e 5) = e 5 + b1 • e 0 + b2 • e 1
  d0 : d (e 0) = e 0 + c11 • e 2 + c12 • e 3
  d1 : d (e 1) = e 1 + c21 • e 2 + c22 • e 3
  d2 : d (e 2) = e 3
  d3 : d (e 3) = e 2 + e 3
  d4 : d (e 4) = e 4 + c31 • e 2 + c32 • e 3
  d5 : d (e 5) = e 5 + c41 • e 2 + c42 • e 3
  t0 : t (e 0) = e 0
  t1 : t (e 1) = e 1
  t2 : t (e 2) = e 4
  t3 : t (e 3) = e 5
  t4 : t (e 4) = e 2
  t5 : t (e 5) = e 3
  span : Submodule.span (ZMod 2) (Set.range e) = ⊤
  nz : e 0 ≠ 0 ∧ e 1 ≠ 0 ∧ e 0 ≠ e 1 ∧ e 2 ≠ 0 ∧ e 3 ≠ 0 ∧ e 2 ≠ e 3

theorem apply_eq_of_mem_span {f : Module.End (ZMod 2) V} {v w x : V}
    (h : f x + x ∈ Submodule.span (ZMod 2) {v, w}) : ∃ α β : ZMod 2, f x = x + α • v + β • w := by
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp h
  refine ⟨α, β, ?_⟩
  rw [add_assoc, hαβ, add_comm (f x) x, ← add_assoc, ZModModule.add_self, zero_add]

theorem chart_vec [Module.Finite (ZMod 2) V] (y d t : Module.End (ZMod 2) V)
    (hy3 : y * y * y = 1) (hd3 : d * d * d = 1) (ht2 : t * t = 1) (hty : t * y = y * t)
    (hry : Module.finrank (ZMod 2) (comm2 y) = 2) (hrd : Module.finrank (ZMod 2) (comm2 d) = 2)
    (hcomm : comm2 y ⊔ comm2 d ⊔ comm2 t = ⊤) :
    ∃ (e : Fin 6 → V) (a1 a2 b1 b2 c11 c12 c21 c22 c31 c32 c41 c42 : ZMod 2),
      ChartVec y d t e a1 a2 b1 b2 c11 c12 c21 c22 c31 c32 c41 c42 := by
  obtain ⟨u, hu, hu0, hyu, hyu0, hyyu, hspy⟩ := refl_basis y hy3 hry
  obtain ⟨p, hp, hp0, hdp, hdp0, hddp, hspd⟩ := refl_basis d hd3 hrd
  have htu := t_fixes_basis hu0 hyu hyu0 hyyu hty ht2 (hspy ▸ t_mem_comm2 hty hu)
  have hsum := sup_map_eq_top ht2 hspy htu.1 htu.2 hcomm
  have hyA : ∀ x : V, y x + x ∈ comm2 y := fun x => mem_comm2.mpr ⟨x, rfl⟩
  have hdA : ∀ x : V, d x + x ∈ comm2 d := fun x => mem_comm2.mpr ⟨x, rfl⟩
  obtain ⟨a1, a2, hyp⟩ := apply_eq_of_mem_span (hspy ▸ hyA p)
  obtain ⟨b1, b2, hydp⟩ := apply_eq_of_mem_span (hspy ▸ hyA (d p))
  obtain ⟨c11, c12, hdu⟩ := apply_eq_of_mem_span (hspd ▸ hdA u)
  obtain ⟨c21, c22, hdyu⟩ := apply_eq_of_mem_span (hspd ▸ hdA (y u))
  obtain ⟨c31, c32, hdtp⟩ := apply_eq_of_mem_span (hspd ▸ hdA (t p))
  obtain ⟨c41, c42, hdtdp⟩ := apply_eq_of_mem_span (hspd ▸ hdA (t (d p)))
  have hty' := t_apply_comm hty
  have hyt : ∀ x, y (t x) = t (y x) := fun x => (hty' x).symm
  have htp : t p = t p := rfl
  refine ⟨![u, y u, p, d p, t p, t (d p)], a1, a2, b1, b2, c11, c12, c21, c22, c31, c32, c41,
    c42, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simpa using hyyu
  · simpa using hyp
  · simpa using hydp
  · simp only [Matrix.cons_val]
    rw [hyt, hyp, map_add, map_add, map_smul, map_smul, htu.1, htu.2]
  · simp only [Matrix.cons_val]
    rw [hyt, hydp, map_add, map_add, map_smul, map_smul, htu.1, htu.2]
  · simpa using hdu
  · simpa using hdyu
  · simp
  · simpa using hddp
  · simpa using hdtp
  · simpa using hdtdp
  · simpa using htu.1
  · simpa using htu.2
  · simp
  · simp
  · simpa using t_apply_t ht2 p
  · simpa using t_apply_t ht2 (d p)
  · rw [eq_top_iff, ← hsum, hspy, hspd, Submodule.map_span, Set.image_pair]
    refine sup_le (sup_le (Submodule.span_mono ?_) (Submodule.span_mono ?_))
      (Submodule.span_mono ?_)
    · rintro x (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · rintro x (rfl | rfl)
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
    · rintro x (rfl | rfl)
      · exact ⟨4, rfl⟩
      · exact ⟨5, rfl⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using hu0
    · simpa using hyu0
    · simpa using Ne.symm hyu
    · simpa using hp0
    · simpa using hdp0
    · simpa using Ne.symm hdp

theorem eq_of_add_eq_zero_V {a b : V} (h : a + b = 0) : a = b :=
  (eq_neg_of_add_eq_zero_left h).trans (ZModModule.neg_eq_self b)

theorem four_le_finrank [Module.Finite (ZMod 2) V] (f t : Module.End (ZMod 2) V)
    (h3 : f * f * f = 1) (hrk : Module.finrank (ZMod 2) (comm2 f) = 2) (ht2 : t * t = 1)
    (hty : t * f = f * t) (ht1 : t ≠ 1) : 4 ≤ Module.finrank (ZMod 2) V := by
  obtain ⟨u, hu, hu0, hfu, hfu0, hf2, hsp⟩ := refl_basis f h3 hrk
  have htu := t_fixes_basis hu0 hfu hfu0 hf2 hty ht2 (hsp ▸ t_mem_comm2 hty hu)
  have hfix : ∀ a ∈ comm2 f, t a = a := by
    intro a ha
    rw [hsp] at ha
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp ha
    simp only [map_add, map_smul, htu.1, htu.2]
  have hfixt : ∀ b ∈ comm2 t, t b = b := by
    intro b hb
    obtain ⟨z, rfl⟩ := mem_comm2.mp hb
    rw [map_add, t_apply_t ht2, add_comm]
  have hdisj : Disjoint (comm2 f) (comm2 t) := by
    rw [Submodule.disjoint_def]
    intro a ha hat
    obtain ⟨z, rfl⟩ := mem_comm2.mp hat
    have hb : f z + z ∈ comm2 f := mem_comm2.mpr ⟨z, rfl⟩
    have hfa : f (t z + z) = t z + z := by
      have h1 : f (t z + z) + (t z + z) = t (f z + z) + (f z + z) := by
        rw [map_add, map_add, ← t_apply_comm hty]
        abel
      rw [hfix _ hb, ZModModule.add_self] at h1
      exact eq_of_add_eq_zero_V h1
    have hff := f_f_of_mem h3 ha
    rw [hfa, hfa] at hff
    have h0 : t z + z + (t z + z) = 0 := ZModModule.add_self _
    rw [← hff] at h0
    exact h0
  have hW0 : comm2 t ≠ ⊥ := by
    intro h
    apply ht1
    refine LinearMap.ext fun v => ?_
    have hv : t v + v ∈ comm2 t := mem_comm2.mpr ⟨v, rfl⟩
    rw [h, Submodule.mem_bot] at hv
    simpa using eq_of_add_eq_zero_V hv
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (comm2 f) (comm2 t)
  rw [hdisj.eq_bot, finrank_bot, hrk] at hsup
  have hpos : 1 ≤ Module.finrank (ZMod 2) (comm2 t) := Submodule.one_le_finrank_iff.mpr hW0
  by_contra hlt
  have hle : Module.finrank (ZMod 2) ↥(comm2 f ⊔ comm2 t) ≤ Module.finrank (ZMod 2) V :=
    Submodule.finrank_le _
  have heq : Module.finrank (ZMod 2) ↥(comm2 f ⊔ comm2 t) = Module.finrank (ZMod 2) V := by omega
  have htop : comm2 f ⊔ comm2 t = ⊤ := Submodule.eq_top_of_finrank_eq heq
  apply ht1
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ comm2 f ⊔ comm2 t := by rw [htop]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  simp only [map_add, hfix a ha, hfixt b hb]
  rfl

end Abstract

section Matrices

@[expose] def chartYSem (a1 a2 b1 b2 : ZMod 2) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of ![![0, 1, a1, b1, a1, b1], ![1, 1, a2, b2, a2, b2], ![0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]

@[expose] def chartDSem (c11 c12 c21 c22 c31 c32 c41 c42 : ZMod 2) :
    Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![c11, c21, 0, 1, c31, c41],
    ![c12, c22, 1, 1, c32, c42], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]

@[expose] def chartTSem : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 1], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0]]

@[expose] def phiCode (a1 a2 b1 b2 : ZMod 2) : ℕ := a1.val + 2 * a2.val + 4 * b1.val + 8 * b2.val

@[expose] def psiCode (c11 c12 c21 c22 c31 c32 c41 c42 : ZMod 2) : ℕ :=
  c11.val + 2 * c12.val + 4 * c21.val + 8 * c22.val + 16 * c31.val + 32 * c32.val +
    64 * c41.val + 128 * c42.val

theorem toMat_chartY (a1 a2 b1 b2 : ZMod 2) :
    toMat 6 6 (chartY (phiCode a1 a2 b1 b2)) = chartYSem a1 a2 b1 b2 := by
  revert a1 a2 b1 b2
  decide

theorem toMat_chartT : toMat 6 6 chartT = chartTSem := by decide

theorem toMat_chartD (c11 c12 c21 c22 c31 c32 c41 c42 : ZMod 2) :
    toMat 6 6 (chartD (psiCode c11 c12 c21 c22 c31 c32 c41 c42)) =
      chartDSem c11 c12 c21 c22 c31 c32 c41 c42 := by
  revert c11 c12 c21 c22 c31 c32 c41 c42
  decide

variable {n : ℕ}

theorem mulE_apply (y : Matrix (Fin n) (Fin n) (ZMod 2)) (e : Fin 6 → Fin n → ZMod 2) (i : Fin n)
    (j : Fin 6) : (y * Matrix.of fun i j => e j i) i j = (Matrix.toLinAlgEquiv' y (e j)) i := by
  simp [Matrix.mul_apply, Matrix.toLinAlgEquiv'_apply, Matrix.mulVec, dotProduct]

theorem Emul_apply (e : Fin 6 → Fin n → ZMod 2) (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) (i : Fin n)
    (j : Fin 6) : ((Matrix.of fun i j => e j i) * M) i j = (∑ k, M k j • e k) i := by
  simp [Matrix.mul_apply, Finset.sum_apply, mul_comm]

theorem chartRel_of_chartVec {y d t : Matrix (Fin n) (Fin n) (ZMod 2)}
    {e : Fin 6 → Fin n → ZMod 2} {a1 a2 b1 b2 c11 c12 c21 c22 c31 c32 c41 c42 : ZMod 2}
    (h : ChartVec (Matrix.toLinAlgEquiv' y) (Matrix.toLinAlgEquiv' d) (Matrix.toLinAlgEquiv' t) e
      a1 a2 b1 b2 c11 c12 c21 c22 c31 c32 c41 c42) :
    ChartRel y d t (Matrix.of fun i j => e j i) (phiCode a1 a2 b1 b2)
      (psiCode c11 c12 c21 c22 c31 c32 c41 c42) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v
    have hle : Submodule.span (ZMod 2) (Set.range e) ≤
        LinearMap.range (Matrix.mulVecLin (Matrix.of fun i j => e j i)) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      refine ⟨Pi.single j 1, ?_⟩
      funext i
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
      rfl
    have := hle (h.span ▸ Submodule.mem_top (x := v))
    obtain ⟨x, hx⟩ := this
    exact ⟨x, hx⟩
  · rw [toMat_chartY]
    ext i j
    rw [mulE_apply, Emul_apply]
    fin_cases j
    · simp [chartYSem, Fin.sum_univ_succ, h.y0]
    · simp [chartYSem, Fin.sum_univ_succ, h.y1]
    · simp [chartYSem, Fin.sum_univ_succ, h.y2]
      ring
    · simp [chartYSem, Fin.sum_univ_succ, h.y3]
      ring
    · simp [chartYSem, Fin.sum_univ_succ, h.y4]
      ring
    · simp [chartYSem, Fin.sum_univ_succ, h.y5]
      ring
  · rw [toMat_chartD]
    ext i j
    rw [mulE_apply, Emul_apply]
    fin_cases j
    · simp [chartDSem, Fin.sum_univ_succ, h.d0]
      ring
    · simp [chartDSem, Fin.sum_univ_succ, h.d1]
      ring
    · simp [chartDSem, Fin.sum_univ_succ, h.d2]
    · simp [chartDSem, Fin.sum_univ_succ, h.d3]
    · simp [chartDSem, Fin.sum_univ_succ, h.d4]
      ring
    · simp [chartDSem, Fin.sum_univ_succ, h.d5]
      ring
  · rw [toMat_chartT]
    ext i j
    rw [mulE_apply, Emul_apply]
    fin_cases j
    · simp [chartTSem, Fin.sum_univ_succ, h.t0]
    · simp [chartTSem, Fin.sum_univ_succ, h.t1]
    · simp [chartTSem, Fin.sum_univ_succ, h.t2]
    · simp [chartTSem, Fin.sum_univ_succ, h.t3]
    · simp [chartTSem, Fin.sum_univ_succ, h.t4]
    · simp [chartTSem, Fin.sum_univ_succ, h.t5]

@[expose] def imSub (g : Matrix (Fin n) (Fin n) (ZMod 2)) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  LinearMap.range (Matrix.mulVecLin (g - 1))

theorem comm2_toLinAlgEquiv (g : Matrix (Fin n) (Fin n) (ZMod 2)) :
    comm2 (Matrix.toLinAlgEquiv' g) = imSub g := by
  unfold comm2 imSub
  congr 1
  ext v
  simp [Matrix.toLinAlgEquiv'_apply]

theorem E_mulVec_eq (e : Fin 6 → Fin n → ZMod 2) (v : Fin 6 → ZMod 2) :
    (Matrix.of fun i j => e j i).mulVec v = ∑ j, v j • e j := by
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem vec_eq_of_add_eq_zero' {u v : Fin n → ZMod 2} (h : u + v = 0) : u = v := by
  funext i
  have := congrFun h i
  simp only [Pi.add_apply, Pi.zero_apply] at this
  revert this
  generalize u i = a
  generalize v i = b
  revert a b
  decide

theorem chart_exists (y d t : Matrix (Fin n) (Fin n) (ZMod 2)) (hy3 : y * y * y = 1)
    (hd3 : d * d * d = 1) (ht2 : t * t = 1) (hty : t * y = y * t)
    (hry : Module.finrank (ZMod 2) (imSub y) = 2) (hrd : Module.finrank (ZMod 2) (imSub d) = 2)
    (hcomm : imSub y ⊔ imSub d ⊔ imSub t = ⊤) :
    ∃ (E : Matrix (Fin n) (Fin 6) (ZMod 2)) (φ ψ : ℕ), φ < 16 ∧ ψ < 256 ∧
      ChartRel y d t E φ ψ ∧ ∀ x ∈ [1, 2, 3, 4, 8, 12], E.mulVec (bitVec 6 x) ≠ 0 := by
  have h3 : ∀ g : Matrix (Fin n) (Fin n) (ZMod 2), g * g * g = 1 →
      Matrix.toLinAlgEquiv' g * Matrix.toLinAlgEquiv' g * Matrix.toLinAlgEquiv' g = 1 := by
    intro g hg
    rw [← map_mul, ← map_mul, hg, map_one]
  obtain ⟨e, a1, a2, b1, b2, c11, c12, c21, c22, c31, c32, c41, c42, h⟩ := chart_vec
    (Matrix.toLinAlgEquiv' y) (Matrix.toLinAlgEquiv' d) (Matrix.toLinAlgEquiv' t) (h3 y hy3)
    (h3 d hd3) (by rw [← map_mul, ht2, map_one]) (by rw [← map_mul, ← map_mul, hty])
    (by rw [comm2_toLinAlgEquiv]; exact hry) (by rw [comm2_toLinAlgEquiv]; exact hrd)
    (by rw [comm2_toLinAlgEquiv, comm2_toLinAlgEquiv, comm2_toLinAlgEquiv]; exact hcomm)
  refine ⟨Matrix.of fun i j => e j i, phiCode a1 a2 b1 b2, psiCode c11 c12 c21 c22 c31 c32 c41 c42,
    ?_, ?_, chartRel_of_chartVec h, ?_⟩
  · have := a1.val_lt; have := a2.val_lt; have := b1.val_lt; have := b2.val_lt
    unfold phiCode
    omega
  · have := c11.val_lt; have := c12.val_lt; have := c21.val_lt; have := c22.val_lt
    have := c31.val_lt; have := c32.val_lt; have := c41.val_lt; have := c42.val_lt
    unfold psiCode
    omega
  · obtain ⟨n0, n1, n01, n2, n3, n23⟩ := h.nz
    intro x hx
    rw [E_mulVec_eq]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    have hadd : ∀ {a b : Fin n → ZMod 2}, a ≠ b → a + b ≠ 0 := fun hab h0 =>
      hab (vec_eq_of_add_eq_zero' h0)
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have : bitVec 6 1 = ![1, 0, 0, 0, 0, 0] := by decide
      simpa [this, Fin.sum_univ_succ] using n0
    · have : bitVec 6 2 = ![0, 1, 0, 0, 0, 0] := by decide
      simpa [this, Fin.sum_univ_succ] using n1
    · have : bitVec 6 3 = ![1, 1, 0, 0, 0, 0] := by decide
      simpa [this, Fin.sum_univ_succ] using hadd n01
    · have : bitVec 6 4 = ![0, 0, 1, 0, 0, 0] := by decide
      simpa [this, Fin.sum_univ_succ] using n2
    · have : bitVec 6 8 = ![0, 0, 0, 1, 0, 0] := by decide
      simpa [this, Fin.sum_univ_succ] using n3
    · have : bitVec 6 12 = ![0, 0, 1, 1, 0, 0] := by decide
      simpa [this, Fin.sum_univ_succ] using hadd n23

theorem KRel_of_span {E : Matrix (Fin n) (Fin 6) (ZMod 2)} {Kb : List ℕ}
    (hKb : ∀ b ∈ Kb, b < 2 ^ 6)
    (hspan : LinearMap.ker (Matrix.mulVecLin E) = spanBits 6 Kb) : KRel E (spanList Kb) := by
  constructor
  · intro x hx
    have := mem_spanBits_of_mem_spanList (m := 6) hx
    rw [← hspan, LinearMap.mem_ker, Matrix.mulVecLin_apply] at this
    exact this
  · intro x hx h0
    refine mem_spanList_of_mem_spanBits hKb hx ?_
    rw [← hspan, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact h0

theorem finrank_ker_eq (E : Matrix (Fin n) (Fin 6) (ZMod 2))
    (hsurj : ∀ v, ∃ x, E.mulVec x = v) :
    Module.finrank (ZMod 2) (LinearMap.ker (Matrix.mulVecLin E)) + n = 6 := by
  have h := (Matrix.mulVecLin E).finrank_range_add_finrank_ker
  have hr : LinearMap.range (Matrix.mulVecLin E) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro v
    obtain ⟨x, hx⟩ := hsurj v
    exact ⟨x, hx⟩
  rw [hr, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h
  omega

theorem mem_kList_one {v : ℕ} (hv : v < 64) (hv0 : v ≠ 0) : [v] ∈ kList 1 := by
  simp only [kList, List.mem_filterMap, List.mem_range]
  exact ⟨v, hv, by simp [hv0]⟩

theorem mem_kList_two {a b : ℕ} (hb : b < 64) (ha0 : 0 < a) (hab : a < b) : [a, b] ∈ kList 2 := by
  simp only [kList, List.mem_flatMap, List.mem_filterMap, List.mem_range]
  exact ⟨a, by omega, b, hb, by simp [ha0, hab]⟩

theorem exists_ker_list (E : Matrix (Fin n) (Fin 6) (ZMod 2))
    (hsurj : ∀ v, ∃ x, E.mulVec x = v) (hn : n ≤ 6) :
    ∃ x : Fin (6 - n) → ℕ, (∀ i, x i < 2 ^ 6) ∧ (∀ i, bitVec 6 (x i) ≠ 0) ∧
      Function.Injective x ∧ LinearMap.ker (Matrix.mulVecLin E) = spanBits 6 (List.ofFn x) := by
  have hdim := finrank_ker_eq E hsurj
  set K := LinearMap.ker (Matrix.mulVecLin E) with hK
  have hr : Module.finrank (ZMod 2) K = 6 - n := by omega
  let b := Module.finBasisOfFinrankEq (ZMod 2) K hr
  choose x hx hbx using fun i => bitVec_surj ((b i : K) : Fin 6 → ZMod 2)
  refine ⟨x, hx, fun i h0 => ?_, fun i j hij => ?_, ?_⟩
  · rw [hbx] at h0
    exact b.ne_zero i (Subtype.ext h0)
  · have h1 : ((b i : K) : Fin 6 → ZMod 2) = ((b j : K) : Fin 6 → ZMod 2) := by
      rw [← hbx i, ← hbx j, hij]
    exact b.injective (Subtype.ext h1)
  · have hsp := b.span_eq
    have hmap := congrArg (Submodule.map K.subtype) hsp
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at hmap
    have hrange : bitVec 6 '' {y | y ∈ List.ofFn x} = Set.range (K.subtype ∘ b) := by
      ext z
      simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_ofFn, Set.mem_range,
        Function.comp_apply, Submodule.subtype_apply]
      constructor
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, (hbx i).symm⟩
      · rintro ⟨i, rfl⟩
        exact ⟨x i, ⟨i, rfl⟩, hbx i⟩
    unfold spanBits
    rw [hrange, hmap]

theorem exists_Kb (E : Matrix (Fin n) (Fin 6) (ZMod 2)) (hsurj : ∀ v, ∃ x, E.mulVec x = v)
    (hn4 : 4 ≤ n) (hn6 : n ≤ 6) : ∃ Kb ∈ kList (6 - n), KRel E (spanList Kb) := by
  obtain ⟨x, hx, hnz, hinj, hker⟩ := exists_ker_list E hsurj hn6
  have hn : n = 4 ∨ n = 5 ∨ n = 6 := by omega
  rcases hn with rfl | rfl | rfl
  · have hL : List.ofFn x = [x 0, x 1] := by simp [List.ofFn_succ]
    rw [hL] at hker
    have h01 : x 0 ≠ x 1 := fun h => absurd (hinj h) (by decide)
    have h0 : x 0 ≠ 0 := fun h => hnz 0 (by rw [h]; exact bitVec_zero 6)
    have h1 : x 1 ≠ 0 := fun h => hnz 1 (by rw [h]; exact bitVec_zero 6)
    have hx0 := hx 0
    have hx1 := hx 1
    rcases Nat.lt_or_gt_of_ne h01 with hlt | hlt
    · refine ⟨[x 0, x 1], mem_kList_two (by simpa using hx1) (Nat.pos_of_ne_zero h0) hlt, ?_⟩
      exact KRel_of_span (by intro b hb; simp at hb; rcases hb with rfl | rfl <;> simpa) hker
    · refine ⟨[x 1, x 0], mem_kList_two (by simpa using hx0) (Nat.pos_of_ne_zero h1) hlt, ?_⟩
      refine KRel_of_span (by intro b hb; simp at hb; rcases hb with rfl | rfl <;> simpa) ?_
      rw [hker]
      unfold spanBits
      congr 2
      ext z
      simp [or_comm]
  · have hL : List.ofFn x = [x 0] := by simp [List.ofFn_succ]
    rw [hL] at hker
    have h0 : x 0 ≠ 0 := fun h => hnz 0 (by rw [h]; exact bitVec_zero 6)
    exact ⟨[x 0], mem_kList_one (by simpa using hx 0) h0,
      KRel_of_span (by intro b hb; simp at hb; subst hb; simpa using hx 0) hker⟩
  · have hL : List.ofFn x = [] := by simp
    rw [hL] at hker
    exact ⟨[], by simp [kList], KRel_of_span (by simp) hker⟩

theorem four_le_n (y t : Matrix (Fin n) (Fin n) (ZMod 2)) (hy3 : y * y * y = 1)
    (hry : Module.finrank (ZMod 2) (imSub y) = 2) (ht2 : t * t = 1) (hty : t * y = y * t)
    (ht1 : t ≠ 1) : 4 ≤ n := by
  have h := four_le_finrank (Matrix.toLinAlgEquiv' y) (Matrix.toLinAlgEquiv' t)
    (by rw [← map_mul, ← map_mul, hy3, map_one]) (by rw [comm2_toLinAlgEquiv]; exact hry)
    (by rw [← map_mul, ht2, map_one]) (by rw [← map_mul, ← map_mul, hty])
    (fun h => ht1 (Matrix.toLinAlgEquiv'.injective (h.trans (map_one _).symm)))
  rw [Module.finrank_fin_fun] at h
  exact h

end Matrices

end CFSG.CGT.PushingUpLit.CGT6.RouteC

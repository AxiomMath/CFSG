module

public import CFSG.Fischer.Classification.Basic.WidthOne

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer

variable {X : Type} [Group X] {E : Set X}

section Words

theorem Pair.mul_conj_eq (hP : Pair X E) {p a : X} (hp : p ∈ E) (ha : a ∈ E)
    (hap : a * p ≠ p * a) : p * a * p * (p * a)⁻¹ = a := by
  rw [mul_inv_rev, Pair.inv_eq hP ha, Pair.inv_eq hP hp]
  calc p * a * p * (a * p) = p * (a * p * a) * p := by simp only [mul_assoc]
    _ = p * (p * a * p) * p := by rw [Pair.mul_mul_eq hP ha hp hap]
    _ = p * p * a * (p * p) := by simp only [mul_assoc]
    _ = a := by rw [Pair.mul_self hP hp, one_mul, mul_one]

theorem Pair.mul_conj_eq_conj (hP : Pair X E) {p q a : X} (hp : p ∈ E) (hq : q ∈ E) (ha : a ∈ E)
    (haq : a * q ≠ q * a) : p * a * q * (p * a)⁻¹ = p * q * a * (p * q)⁻¹ := by
  rw [mul_inv_rev, mul_inv_rev, Pair.inv_eq hP ha, Pair.inv_eq hP hp, Pair.inv_eq hP hq]
  calc p * a * q * (a * p) = p * (a * q * a) * p := by simp only [mul_assoc]
    _ = p * (q * a * q) * p := by rw [Pair.mul_mul_eq hP ha hq haq]
    _ = p * q * a * (q * p) := by simp only [mul_assoc]

theorem Pair.mul_conj_left_eq (hP : Pair X E) {x y : X} (hx : x ∈ E) (hy : y ∈ E)
    (hxy : x * y ≠ y * x) : x * y * x * (x * y)⁻¹ = y := by
  rw [mul_inv_rev, Pair.inv_eq hP hx, Pair.inv_eq hP hy]
  calc x * y * x * (y * x) = x * y * x * y * x := by simp only [mul_assoc]
    _ = y * x * y * y * x := by rw [Pair.mul_mul_eq hP hx hy hxy]
    _ = y * x * (y * y) * x := by simp only [mul_assoc]
    _ = y := by rw [Pair.mul_self hP hy, mul_one, mul_assoc, Pair.mul_self hP hx, mul_one]

theorem mul_conj_eq_self {x y a : X} (hx : a * x = x * a) (hy : a * y = y * a) :
    x * y * a * (x * y)⁻¹ = a := by
  have hc : Commute (x * y) a := Commute.mul_left hx.symm hy.symm
  rw [hc.eq, mul_inv_cancel_right]

end Words

section Rel

theorem Pair.exists_normal_of_conj_rel (hP : Pair X E) (R : X → X → Prop)
    (hrefl : ∀ a ∈ E, R a a) (hsymm : ∀ a ∈ E, ∀ b ∈ E, R a b → R b a)
    (htrans : ∀ a ∈ E, ∀ b ∈ E, ∀ c ∈ E, R a b → R b c → R a c)
    (hconj : ∀ g : X, ∀ a ∈ E, ∀ b ∈ E, R a b → R (g * a * g⁻¹) (g * b * g⁻¹)) :
    ∃ K : Subgroup X, K.Normal ∧ ∀ g, g ∈ K ↔ ∀ a ∈ E, R a (g * a * g⁻¹) := by
  let K : Subgroup X :=
    { carrier := {g | ∀ a ∈ E, R a (g * a * g⁻¹)}
      mul_mem' := by
        intro g h hg hh a ha
        have ha' := Pair.conj_mem hP ha h
        have h2 := hg _ ha'
        rw [show g * h * a * (g * h)⁻¹ = g * (h * a * h⁻¹) * g⁻¹ by group]
        exact htrans _ ha _ ha' _ (Pair.conj_mem hP ha' g) (hh a ha) h2
      one_mem' := by
        intro a ha
        simpa using hrefl a ha
      inv_mem' := by
        intro g hg a ha
        have ha' : g⁻¹ * a * g⁻¹⁻¹ ∈ E := Pair.conj_mem hP ha g⁻¹
        have h1 := hg _ ha'
        rw [show g * (g⁻¹ * a * g⁻¹⁻¹) * g⁻¹ = a by group] at h1
        exact hsymm _ ha' _ ha h1 }
  refine ⟨K, ⟨fun k hk g a ha => ?_⟩, fun g => Iff.rfl⟩
  have ha' : g⁻¹ * a * g⁻¹⁻¹ ∈ E := Pair.conj_mem hP ha g⁻¹
  have h2 := hconj g _ ha' _ (Pair.conj_mem hP ha' k) (hk _ ha')
  rwa [show g * (g⁻¹ * a * g⁻¹⁻¹) * g⁻¹ = a by group,
    show g * (k * (g⁻¹ * a * g⁻¹⁻¹) * k⁻¹) * g⁻¹ = g * k * g⁻¹ * a * (g * k * g⁻¹)⁻¹ by
      group] at h2

theorem Pair.rel_of_mem_commutator (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hs : IsSimpleGroup (commutator X)) (R : X → X → Prop)
    (hrefl : ∀ a ∈ E, R a a) (hsymm : ∀ a ∈ E, ∀ b ∈ E, R a b → R b a)
    (htrans : ∀ a ∈ E, ∀ b ∈ E, ∀ c ∈ E, R a b → R b c → R a c)
    (hconj : ∀ g : X, ∀ a ∈ E, ∀ b ∈ E, R a b → R (g * a * g⁻¹) (g * b * g⁻¹))
    {t : X} (ht1 : t ≠ 1) (ht : ∀ a ∈ E, R a (t * a * t⁻¹)) {k : X}
    (hk : k ∈ commutator X) : ∀ a ∈ E, R a (k * a * k⁻¹) := by
  obtain ⟨K, hKn, hK⟩ := Pair.exists_normal_of_conj_rel hP R hrefl hsymm htrans hconj
  have hKne : K ≠ ⊥ := by
    intro h
    have htK := (hK t).2 ht
    rw [h, Subgroup.mem_bot] at htK
    exact ht1 htK
  exact (hK k).1 (commutator_le_of_normal hZ hs hKne hk)

end Rel

section Reduced

theorem commute_conj_iff (g w a : X) :
    w * (g * a * g⁻¹) = g * a * g⁻¹ * w ↔ g⁻¹ * w * g * a = a * (g⁻¹ * w * g) := by
  have h := conj_commute_iff g (g⁻¹ * w * g) a
  rwa [show g * (g⁻¹ * w * g) * g⁻¹ = w by group] at h

theorem Pair.eq_of_forall_commute_iff (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hs : IsSimpleGroup (commutator X)) {x y : X} (hx : x ∈ E) (hy : y ∈ E)
    (h : ∀ w ∈ E, w * x = x * w ↔ w * y = y * w) : x = y := by
  by_contra hxy
  let R : X → X → Prop := fun a b => ∀ w ∈ E, (w * a = a * w ↔ w * b = b * w)
  have hrefl : ∀ a ∈ E, R a a := fun _ _ _ _ => Iff.rfl
  have hsymm : ∀ a ∈ E, ∀ b ∈ E, R a b → R b a := fun _ _ _ _ hab w hw => (hab w hw).symm
  have htrans : ∀ a ∈ E, ∀ b ∈ E, ∀ c ∈ E, R a b → R b c → R a c :=
    fun _ _ _ _ _ _ hab hbc w hw => (hab w hw).trans (hbc w hw)
  have hconj : ∀ g : X, ∀ a ∈ E, ∀ b ∈ E, R a b → R (g * a * g⁻¹) (g * b * g⁻¹) := by
    intro g a _ b _ hab w hw
    have hw' : g⁻¹ * w * g ∈ E := by simpa using Pair.conj_mem hP hw g⁻¹
    rw [commute_conj_iff, commute_conj_iff]
    exact hab _ hw'
  have hcomm : x * y = y * x := (h x hx).1 rfl
  have ht1 : x * y ≠ 1 := fun h1 =>
    hxy (by rw [← inv_eq_of_mul_eq_one_right h1, Pair.inv_eq hP hx])
  have ht : ∀ a ∈ E, R a (x * y * a * (x * y)⁻¹) := by
    intro a ha
    by_cases hax : a * x = x * a
    · rw [mul_conj_eq_self hax ((h a ha).1 hax)]
      exact hrefl a ha
    · have hay : a * y ≠ y * a := fun h' => hax ((h a ha).2 h')
      have := hconj (x * a) x hx y hy h
      rwa [Pair.mul_conj_eq hP hx ha hax, Pair.mul_conj_eq_conj hP hx hy ha hay] at this
  obtain ⟨a, ha, b, hb, hab⟩ := Pair.exists_not_commute hP hZ
  have hk : a * b ∈ commutator X := by
    have := Pair.mul_inv_mem_commutator hP hb ha
    rwa [Pair.inv_eq hP hb] at this
  have hR := Pair.rel_of_mem_commutator hP hZ hs R hrefl hsymm htrans hconj ht1 ht hk b hb
  rw [show a * b * b * (a * b)⁻¹ = a * b * a by
    rw [mul_inv_rev, Pair.inv_eq hP ha, Pair.inv_eq hP hb, mul_assoc (a * b) b,
      ← mul_assoc b b a, Pair.mul_self hP hb, one_mul]] at hR
  exact Pair.mul_mul_not_commute_right hP ha hb hab ((hR b hb).1 rfl).symm

theorem Pair.eq_of_localClass_eq (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hs : IsSimpleGroup (commutator X)) (hna : ¬ ∀ a b : commutator X, a * b = b * a)
    {x y : X} (hx : x ∈ E) (hy : y ∈ E) (h : LocalClass E x = LocalClass E y) : x = y := by
  by_contra hxy
  let R : X → X → Prop := fun a b => LocalClass E a = LocalClass E b
  have hrefl : ∀ a ∈ E, R a a := fun _ _ => rfl
  have hsymm : ∀ a ∈ E, ∀ b ∈ E, R a b → R b a := fun _ _ _ _ hab => hab.symm
  have htrans : ∀ a ∈ E, ∀ b ∈ E, ∀ c ∈ E, R a b → R b c → R a c :=
    fun _ _ _ _ _ _ hab hbc => hab.trans hbc
  have hconj : ∀ g : X, ∀ a ∈ E, ∀ b ∈ E, R a b → R (g * a * g⁻¹) (g * b * g⁻¹) := by
    intro g a _ b _ hab
    change LocalClass E _ = LocalClass E _
    rw [← Pair.image_conj_localClass hP g a, ← Pair.image_conj_localClass hP g b]
    exact congrArg _ hab
  have hxy' : x * y ≠ y * x := by
    intro hc
    have hmem : x ∈ LocalClass E y := ⟨hx, hxy, hc⟩
    rw [← h] at hmem
    exact hmem.2.1 rfl
  have ht1 : x * y ≠ 1 := fun h1 =>
    hxy (by rw [← inv_eq_of_mul_eq_one_right h1, Pair.inv_eq hP hx])
  have ht : ∀ a ∈ E, R a (x * y * a * (x * y)⁻¹) := by
    intro a ha
    by_cases hax : a * x = x * a
    · by_cases hax' : a = x
      · rw [hax', Pair.mul_conj_left_eq hP hx hy hxy']
        exact h
      · have hmem : a ∈ LocalClass E x := ⟨ha, hax', hax⟩
        rw [h] at hmem
        rw [mul_conj_eq_self hax hmem.2.2]
    · by_cases hay' : a = y
      · have h1 := hconj x x hx y hy h
        rw [show x * x * x⁻¹ = x by group] at h1
        rw [hay', show x * y * y * (x * y)⁻¹ = x * y * x⁻¹ by group]
        exact h.symm.trans h1
      · have hay : a * y ≠ y * a := by
          intro hc
          have hmem : a ∈ LocalClass E y := ⟨ha, hay', hc⟩
          rw [← h] at hmem
          exact hax hmem.2.2
        have := hconj (x * a) x hx y hy h
        rwa [Pair.mul_conj_eq hP hx ha hax, Pair.mul_conj_eq_conj hP hx hy ha hay] at this
  obtain ⟨d, hd, e, he, hde, hcomm⟩ := Pair.exists_ne_commute hP hs hna
  obtain ⟨k, hk, rfl⟩ := Pair.exists_mem_commutator_conj hP hd he
  have hR := Pair.rel_of_mem_commutator hP hZ hs R hrefl hsymm htrans hconj ht1 ht hk d hd
  have hmem : k * d * k⁻¹ ∈ LocalClass E d := ⟨he, fun h' => hde h'.symm, hcomm.symm⟩
  change LocalClass E d = LocalClass E (k * d * k⁻¹) at hR
  rw [hR] at hmem
  exact hmem.2.1 rfl

end Reduced

end CFSG.Fischer.Classification

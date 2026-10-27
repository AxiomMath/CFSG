module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.NoA5.Algebra
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.NoA5

variable {S : Type*} [Group S]

structure PureClass (E : S → Prop) : Prop where
  cube : ∀ p, E p → p ^ 3 = 1
  inv : ∀ p, E p → E p⁻¹
  conj : ∀ g p, E p → E (g⁻¹ * p * g)
  trans : ∀ p q, E p → E q → ∃ g, q = g⁻¹ * p * g ∨ q = g⁻¹ * p⁻¹ * g
  pair : ∀ p q, E p → E q → p * q = q * p ∨ (p * q) ^ 2 = 1 ∨ (p * q⁻¹) ^ 2 = 1
  no_tri : ∀ x y z, E x → E y → E z → (x * y) ^ 2 = 1 → (x * z) ^ 2 = 1 → (y * z) ^ 2 = 1 → False

theorem nc_inv_left {x y : S} (h : x * y ≠ y * x) : x⁻¹ * y ≠ y * x⁻¹ := by
  intro h'
  apply h
  have : Commute x⁻¹ y := h'
  simpa using this.inv_left.eq

theorem inv_of_pow [Finite S] {T : S → Prop} (hmul : ∀ g h, T g → T h → T (g * h)) (h1 : T 1)
    {g : S} (hg : T g) : T g⁻¹ := by
  have hk : ∀ k : ℕ, T (g ^ k) := fun k => by
    induction k with
    | zero => simpa using h1
    | succ k ih => rw [pow_succ]; exact hmul _ _ ih hg
  have hn := orderOf_pos g
  have hmulone : g * g ^ (orderOf g - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hn, pow_orderOf_eq_one]
  have : g⁻¹ = g ^ (orderOf g - 1) := (eq_inv_of_mul_eq_one_right hmulone).symm
  rw [this]; exact hk _

section Pure

variable {E : S → Prop} (hE : PureClass E)
include hE

theorem PureClass.orient {x y : S} (hx : E x) (hy : E y) (hxy : x * y ≠ y * x) :
    (x⁻¹ * y) ^ 2 = 1 ∨ (x⁻¹ * y⁻¹) ^ 2 = 1 := by
  rcases hE.pair x⁻¹ y (hE.inv x hx) hy with h | h | h
  · exact absurd (by simpa using (show Commute x⁻¹ y from h).inv_left.eq) hxy
  · exact Or.inl h
  · exact Or.inr h

theorem PureClass.adj_conj {y g : S} (hy : E y) (hg : E g) (hyg : y * g ≠ g * y) :
    y * (g⁻¹ * y * g) ≠ (g⁻¹ * y * g) * y := by
  intro hc
  apply hyg
  rcases hE.orient hy hg hyg with h | h
  · exact comm_of_comm_conj (hE.cube g hg) h hc
  · exact comm_of_comm_conj_inv (hE.cube g hg) h hc

theorem PureClass.l1' {a y z : S} (ha : E a) (hy : E y) (hz : E z)
    (hay : a * y ≠ y * a) (hyz : y * z ≠ z * y) (haz : a * z = z * a) : z = a ∨ z = a⁻¹ := by
  obtain ⟨q, hq, hqy, haq⟩ : ∃ q, E q ∧ (q = y ∨ q = y⁻¹) ∧ (a⁻¹ * q) ^ 2 = 1 := by
    rcases hE.orient ha hy hay with h | h
    · exact ⟨y, hy, Or.inl rfl, h⟩
    · exact ⟨y⁻¹, hE.inv y hy, Or.inr rfl, h⟩
  have hqz : q * z ≠ z * q := by
    rcases hqy with rfl | rfl
    · exact hyz
    · exact nc_inv_left hyz
  obtain ⟨r, hr, hrz, hqr⟩ : ∃ r, E r ∧ (r = z ∨ r = z⁻¹) ∧ (q⁻¹ * r) ^ 2 = 1 := by
    rcases hE.orient hq hz hqz with h | h
    · exact ⟨z, hz, Or.inl rfl, h⟩
    · exact ⟨z⁻¹, hE.inv z hz, Or.inr rfl, h⟩
  have har : a * r = r * a := by
    rcases hrz with rfl | rfl
    · exact haz
    · have : Commute a z := haz
      simpa using this.inv_right.eq
  have := l1 (hE.cube a ha) (hE.cube q hq) (hE.cube r hr) haq hqr har
  rcases hrz with rfl | rfl
  · exact Or.inl this.symm
  · right; rw [this]; simp

theorem PureClass.noncomm_or [Finite S] (hcl : Subgroup.closure {x | E x} = ⊤) {a y : S}
    (ha : E a) (hy : E y) : y = a ∨ y = a⁻¹ ∨ a * y ≠ y * a := by
  let Adj : S → S → Prop := fun y z => E y ∧ E z ∧ (y = z ∨ y = z⁻¹ ∨ y * z ≠ z * y)
  let Ω : S → Prop := Relation.ReflTransGen Adj a
  have hΩE : ∀ y, Ω y → E y := by
    intro y h
    induction h with
    | refl => exact ha
    | tail _ hs _ => exact hs.2.1
  have hinv : Ω a⁻¹ :=
    Relation.ReflTransGen.single ⟨ha, hE.inv a ha, Or.inr (Or.inl (by simp))⟩
  have hgE : ∀ g, E g → ∀ y, Ω y → Ω (g⁻¹ * y * g) := by
    intro g hg y hy
    refine Relation.ReflTransGen.tail hy ⟨hΩE y hy, hE.conj g y (hΩE y hy), ?_⟩
    by_cases hc : y * g = g * y
    · left
      calc y = g⁻¹ * (g * y) := by group
        _ = g⁻¹ * (y * g) := by rw [hc]
        _ = g⁻¹ * y * g := by group
    · exact Or.inr (Or.inr (hE.adj_conj (hΩE y hy) hg hc))
  have hall : ∀ g, g ∈ Subgroup.closure {x | E x} → ∀ y, Ω y → Ω (g⁻¹ * y * g) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hgE x hx
    | one => intro y hy; simpa using hy
    | mul g h _ _ ihg ihh =>
        intro y hy
        have e : (g * h)⁻¹ * y * (g * h) = h⁻¹ * (g⁻¹ * y * g) * h := by group
        rw [e]; exact ihh _ (ihg y hy)
    | inv g _ ih =>
        exact inv_of_pow (T := fun g => ∀ y, Ω y → Ω (g⁻¹ * y * g))
          (fun g h hg hh y hy => by
            have e : (g * h)⁻¹ * y * (g * h) = h⁻¹ * (g⁻¹ * y * g) * h := by group
            rw [e]; exact hh _ (hg y hy))
          (fun y hy => by simpa using hy) ih
  have hΩall : ∀ x, E x → Ω x := by
    intro x hx
    obtain ⟨g, hg | hg⟩ := hE.trans a x ha hx
    · rw [hg]; exact hall g (hcl ▸ Subgroup.mem_top g) a Relation.ReflTransGen.refl
    · rw [hg]; exact hall g (hcl ▸ Subgroup.mem_top g) _ hinv
  have key : ∀ y, Ω y → (y = a ∨ y = a⁻¹ ∨ a * y ≠ y * a) := by
    intro y hy
    induction hy with
    | refl => exact Or.inl rfl
    | @tail y' y hs hadj ih =>
        obtain ⟨hy', hy, hadj⟩ := hadj
        rcases hadj with rfl | rfl | hnc
        · exact ih
        · rcases ih with h | h | h
          · right; left; rw [← h]; simp
          · left; rw [← inv_inv a, ← h]; simp
          · right; right
            intro hc
            apply h
            simpa using (show Commute a y from hc).inv_right.eq
        · rcases ih with rfl | rfl | h
          · exact Or.inr (Or.inr hnc)
          · right; right
            intro hc
            apply hnc
            simpa using (show Commute a y from hc).inv_left.eq
          · by_cases hc : a * y = y * a
            · exact (hE.l1' ha (hΩE y' hs) hy h hnc hc).elim Or.inl (fun h => Or.inr (Or.inl h))
            · exact Or.inr (Or.inr hc)
  exact key y (hΩall y hy)

section C0

variable [Finite S] (hcl : Subgroup.closure {x | E x} = ⊤)
include hcl

theorem PureClass.c0_pair {a b c : S} (ha : E a) (hb : E b) (hc : E c)
    (hab : (a⁻¹ * b) ^ 2 = 1) (hac : (a⁻¹ * c) ^ 2 = 1) : (b⁻¹ * c) ^ 2 = 1 := by
  by_cases hbc : b = c
  · subst hbc; simp
  by_cases hbc' : c = b⁻¹
  · exfalso
    exact hE.no_tri a⁻¹ b c (hE.inv a ha) hb hc hab hac (by rw [hbc']; simp)
  rcases hE.noncomm_or hcl hb hc with h | h | h
  · exact absurd h.symm hbc
  · exact absurd h hbc'
  · rcases hE.orient hb hc h with h' | h'
    · exact h'
    · exact (hE.no_tri a⁻¹ b c (hE.inv a ha) hb hc hab hac (sq_inv' h')).elim

theorem PureClass.c0_conj {a x g : S} (ha : E a) (hx : E x) (hg : E g)
    (hax : (a⁻¹ * x) ^ 2 = 1) (hag : (a⁻¹ * g) ^ 2 = 1) :
    E (g⁻¹ * x * g) ∧ (a⁻¹ * (g⁻¹ * x * g)) ^ 2 = 1 := by
  refine ⟨hE.conj g x hx, ?_⟩
  have hxg : (x⁻¹ * g) ^ 2 = 1 := hE.c0_pair hcl ha hx hg hax hag
  have hw : (x⁻¹ * (g⁻¹ * x * g)) ^ 2 = 1 := conj_sq (hE.cube x hx) (hE.cube g hg) hxg
  have hwE : E (g⁻¹ * x * g) := hE.conj g x hx
  rcases hE.noncomm_or hcl ha hwE with h | h | h
  · rw [h]; simp
  · exfalso
    rw [h] at hw
    exact hE.no_tri a⁻¹ x a (hE.inv a ha) hx ha hax (by simp) (sq_inv' hw)
  · rcases hE.orient ha hwE h with h' | h'
    · exact h'
    · exfalso
      refine hE.no_tri a⁻¹ x (g⁻¹ * x * g)⁻¹ (hE.inv a ha) hx (hE.inv _ hwE) hax h' ?_
      have := sq_inv hw
      simpa using this

theorem PureClass.c0_comm {a p q r : S} (ha : E a) (hp : E p) (hq : E q) (hr : E r)
    (hap : (a⁻¹ * p) ^ 2 = 1) (haq : (a⁻¹ * q) ^ 2 = 1) (har : (a⁻¹ * r) ^ 2 = 1) :
    (p⁻¹ * q) * (p⁻¹ * r) = (p⁻¹ * r) * (p⁻¹ * q) := by
  have hpq : (p⁻¹ * q) ^ 2 = 1 := hE.c0_pair hcl ha hp hq hap haq
  have hpr : (p⁻¹ * r) ^ 2 = 1 := hE.c0_pair hcl ha hp hr hap har
  obtain ⟨hw1E, hw1⟩ := hE.c0_conj hcl ha hq hp haq hap
  obtain ⟨hw2E, hw2⟩ := hE.c0_conj hcl ha hp hq hap haq
  have e1 := hE.c0_pair hcl ha hr hw1E har hw1
  have e2 := hE.c0_pair hcl ha hr hw2E har hw2
  obtain ⟨t, rfl⟩ : ∃ t, q = p * t := ⟨p⁻¹ * q, by group⟩
  obtain ⟨s, rfl⟩ : ∃ s, r = p * s := ⟨p⁻¹ * r, by group⟩
  simp only [inv_mul_cancel_left] at hpq hpr ⊢
  have ht : t * t = 1 := by rw [← pow_two]; exact hpq
  have hs : s * s = 1 := by rw [← pow_two]; exact hpr
  have hsinv := eq_inv_of_mul_self hs
  have htinv := eq_inv_of_mul_self ht
  have hp3 := hE.cube p hp
  have hq3 := hE.cube (p * t) hq
  have h1 : (s * (p⁻¹ * t * p)) ^ 2 = 1 := by
    have : (p * s)⁻¹ * (p⁻¹ * (p * t) * p) = s * (p⁻¹ * t * p) := by
      rw [mul_inv_rev, hsinv]; group
    rw [← this]; exact e1
  have h2 : (s * (p * t * p⁻¹)) ^ 2 = 1 := by
    have hv := v_mul ht hp3 hq3
    have : (p * s)⁻¹ * ((p * t)⁻¹ * p * (p * t)) = s * (p * t * p⁻¹) := by
      rw [← hv, mul_inv_rev, mul_inv_rev, hsinv, htinv]; group
    rw [← this]; exact e2
  exact (l5_core hp3 ht hs hq3 h1 h2).symm

theorem PureClass.false_of_simple [IsSimpleGroup S] (hnab : ∃ x y : S, x * y ≠ y * x)
    {a : S} (ha : E a) : False := by
  let C0 : S → Prop := fun y => E y ∧ (a⁻¹ * y) ^ 2 = 1
  have haC : C0 a := ⟨ha, by simp⟩
  have hC0pair : ∀ b c, C0 b → C0 c → (b⁻¹ * c) ^ 2 = 1 := fun b c hb hc =>
    hE.c0_pair hcl ha hb.1 hc.1 hb.2 hc.2
  have hC0conj : ∀ x g, C0 x → C0 g → C0 (g⁻¹ * x * g) := fun x g hx hg =>
    hE.c0_conj hcl ha hx.1 hg.1 hx.2 hg.2
  have hgen : Subgroup.closure {y | C0 y} = ⊤ := by
    rw [eq_top_iff, ← hcl, Subgroup.closure_le]
    intro x hx
    have haM : a ∈ Subgroup.closure {y | C0 y} := Subgroup.subset_closure haC
    rcases hE.noncomm_or hcl ha hx with h | h | h
    · rw [h]; exact haM
    · rw [h]; exact Subgroup.inv_mem _ haM
    · rcases hE.orient ha hx h with h' | h'
      · exact Subgroup.subset_closure ⟨hx, h'⟩
      · have : x⁻¹ ∈ Subgroup.closure {y | C0 y} := Subgroup.subset_closure ⟨hE.inv x hx, h'⟩
        simpa using Subgroup.inv_mem _ this
  let T : Set S := {u | ∃ x y, C0 x ∧ C0 y ∧ u = x⁻¹ * y}
  have hTcomm : ∀ u ∈ T, ∀ v ∈ T, u * v = v * u := by
    rintro _ ⟨x, y, hx, hy, rfl⟩ _ ⟨z, w, hz, hw, rfl⟩
    have h1 : (x⁻¹ * y) * (x⁻¹ * z) = (x⁻¹ * z) * (x⁻¹ * y) :=
      hE.c0_comm hcl ha hx.1 hy.1 hz.1 hx.2 hy.2 hz.2
    have h2 : (x⁻¹ * y) * (x⁻¹ * w) = (x⁻¹ * w) * (x⁻¹ * y) :=
      hE.c0_comm hcl ha hx.1 hy.1 hw.1 hx.2 hy.2 hw.2
    have hc1 : Commute (x⁻¹ * y) (x⁻¹ * z)⁻¹ := (show Commute _ _ from h1).inv_right
    have hc2 : Commute (x⁻¹ * y) (x⁻¹ * w) := h2
    have := hc1.mul_right hc2
    have e : (x⁻¹ * z)⁻¹ * (x⁻¹ * w) = z⁻¹ * w := by group
    rw [e] at this
    exact this
  let N : Subgroup S := Subgroup.closure T
  have hNcomm : ∀ n ∈ N, ∀ m ∈ N, n * m = m * n := by
    have h1 : ∀ u ∈ T, ∀ m ∈ N, u * m = m * u := by
      intro u hu m hm
      induction hm using Subgroup.closure_induction with
      | mem v hv => exact hTcomm u hu v hv
      | one => simp
      | mul m1 m2 _ _ ih1 ih2 =>
          exact ((show Commute u m1 from ih1).mul_right (show Commute u m2 from ih2)).eq
      | inv m1 _ ih => exact (show Commute u m1 from ih).inv_right.eq
    intro n hn m hm
    induction hn using Subgroup.closure_induction with
    | mem u hu => exact h1 u hu m hm
    | one => simp
    | mul n1 n2 _ _ ih1 ih2 =>
        exact ((show Commute n1 m from ih1).mul_left (show Commute n2 m from ih2)).eq
    | inv n1 _ ih => exact (show Commute n1 m from ih).inv_left.eq
  have hTconj : ∀ g, C0 g → ∀ n ∈ N, g⁻¹ * n * g ∈ N := by
    intro g hg n hn
    induction hn using Subgroup.closure_induction with
    | mem u hu =>
        obtain ⟨x, y, hx, hy, rfl⟩ := hu
        apply Subgroup.subset_closure
        refine ⟨g⁻¹ * x * g, g⁻¹ * y * g, hC0conj x g hx hg, hC0conj y g hy hg, ?_⟩
        group
    | one => simp
    | mul n1 n2 _ _ ih1 ih2 =>
        have e : g⁻¹ * (n1 * n2) * g = (g⁻¹ * n1 * g) * (g⁻¹ * n2 * g) := by group
        rw [e]; exact N.mul_mem ih1 ih2
    | inv n1 _ ih =>
        have e : g⁻¹ * n1⁻¹ * g = (g⁻¹ * n1 * g)⁻¹ := by group
        rw [e]; exact N.inv_mem ih
  have hall : ∀ g, g ∈ Subgroup.closure {y | C0 y} → ∀ n ∈ N, g⁻¹ * n * g ∈ N := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hTconj x hx
    | one => intro n hn; simpa using hn
    | mul g h _ _ ihg ihh =>
        intro n hn
        have e : (g * h)⁻¹ * n * (g * h) = h⁻¹ * (g⁻¹ * n * g) * h := by group
        rw [e]; exact ihh _ (ihg n hn)
    | inv g _ ih =>
        exact inv_of_pow (T := fun g => ∀ n ∈ N, g⁻¹ * n * g ∈ N)
          (fun g h hg hh n hn => by
            have e : (g * h)⁻¹ * n * (g * h) = h⁻¹ * (g⁻¹ * n * g) * h := by group
            rw [e]; exact hh _ (hg n hn))
          (fun n hn => by simpa using hn) ih
  have hNnormal : N.Normal :=
    ⟨fun n hn g => by
      have := hall g⁻¹ (hgen ▸ Subgroup.mem_top _) n hn
      simpa using this⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hN | hN
  ·
    have hCa : ∀ y, C0 y → y = a := by
      intro y hy
      have : a⁻¹ * y ∈ N := Subgroup.subset_closure ⟨a, y, haC, hy, rfl⟩
      rw [hN, Subgroup.mem_bot] at this
      exact (inv_mul_eq_one.mp this).symm
    have hle : Subgroup.closure {y | C0 y} ≤ Subgroup.zpowers a := by
      rw [Subgroup.closure_le]
      intro y hy
      rw [SetLike.mem_coe, hCa y hy]
      exact Subgroup.mem_zpowers a
    obtain ⟨x, y, hxy⟩ := hnab
    apply hxy
    have hx : x ∈ Subgroup.zpowers a := hle (hgen ▸ Subgroup.mem_top x)
    have hy : y ∈ Subgroup.zpowers a := hle (hgen ▸ Subgroup.mem_top y)
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.zpow_zpow_self a i j).eq)
  · obtain ⟨x, y, hxy⟩ := hnab
    exact hxy (hNcomm x (hN ▸ Subgroup.mem_top x) y (hN ▸ Subgroup.mem_top y))

end C0

end Pure

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.NoA5

module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightCTrick

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3.FourEight

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open CFSG.SignalizerFunctor.Helpers
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]
variable {G T S Q H : Subgroup X} {g y : X}

omit [Finite X] in
theorem sq_mul_eq {a b : X} (h : (b⁻¹ * (a⁻¹ * b * a)) * b = b * (b⁻¹ * (a⁻¹ * b * a))) :
    (a * b) ^ 2 = a ^ 2 * b ^ 2 * (b⁻¹ * (a⁻¹ * b * a)) := by
  have h1 : b * a = a * b * (b⁻¹ * (a⁻¹ * b * a)) := by group
  calc (a * b) ^ 2 = a * (b * a) * b := by rw [pow_two]; group
    _ = a * (a * b * (b⁻¹ * (a⁻¹ * b * a))) * b := by rw [h1]
    _ = a * a * b * ((b⁻¹ * (a⁻¹ * b * a)) * b) := by group
    _ = a * a * b * (b * (b⁻¹ * (a⁻¹ * b * a))) := by rw [h]
    _ = a ^ 2 * b ^ 2 * (b⁻¹ * (a⁻¹ * b * a)) := by rw [pow_two, pow_two]; group

omit [Finite X] in
theorem comm_mul_of_comm {x a b : X}
    (h : (a⁻¹ * (x⁻¹ * a * x)) * b = b * (a⁻¹ * (x⁻¹ * a * x))) :
    (a * b)⁻¹ * (x⁻¹ * (a * b) * x) = (a⁻¹ * (x⁻¹ * a * x)) * (b⁻¹ * (x⁻¹ * b * x)) := by
  calc (a * b)⁻¹ * (x⁻¹ * (a * b) * x)
      = b⁻¹ * ((a⁻¹ * (x⁻¹ * a * x)) * b) * (b⁻¹ * (x⁻¹ * b * x)) := by group
    _ = b⁻¹ * (b * (a⁻¹ * (x⁻¹ * a * x))) * (b⁻¹ * (x⁻¹ * b * x)) := by rw [h]
    _ = (a⁻¹ * (x⁻¹ * a * x)) * (b⁻¹ * (x⁻¹ * b * x)) := by group

omit [Finite X] in
theorem conj_comm_eq_inv {w t : X} (hw2 : w ^ 2 = 1) :
    w⁻¹ * (w⁻¹ * (t⁻¹ * w * t)) * w = (w⁻¹ * (t⁻¹ * w * t))⁻¹ := by
  have hw' : w⁻¹ = w := Elem47.inv_eq_of_sq hw2
  have hww : w * w = 1 := by rw [← pow_two, hw2]
  have h1 : (w⁻¹ * (t⁻¹ * w * t))⁻¹ = t⁻¹ * w⁻¹ * t * w := by group
  calc w⁻¹ * (w⁻¹ * (t⁻¹ * w * t)) * w = (w * w)⁻¹ * (t⁻¹ * w * t * w) := by group
    _ = t⁻¹ * w * t * w := by rw [hww, inv_one, one_mul]
    _ = (w⁻¹ * (t⁻¹ * w * t))⁻¹ := by rw [h1, hw']

omit [Finite X] in
theorem exists_mem_not_mem_finset [DecidableEq X] {T : Subgroup X} (F : Finset X)
    (h : F.card < Nat.card T) : ∃ t ∈ T, t ∉ F := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hsub : (T : Set X) ⊆ ↑F := fun x hx => hcon x hx
  have h1 := Set.ncard_le_ncard hsub F.finite_toSet
  rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq] at h1
  have h2 : Nat.card (T : Set X) = Nat.card T := rfl
  omega

namespace ElemCtx

theorem comm_P_of_comm_w (c : ElemCtx G T S Q H g y) {w : X} (hwS : w ∈ S)
    (hwW : w ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) {z : X}
    (hz : z ∈ (T ⊔ rightConjugate T g) ⊓ G) (hzw : z * w = w * z) {p : X} (hp : p ∈ S) :
    z * p = p * z := by
  by_cases hpW : p ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)
  · exact c.elem.Z_comm hz hpW
  · exact ((commute_iff_of_not_mem c.elem hwS hp hwW hpW hz).mp hzw)

theorem comm_mul_T (c : ElemCtx G T S Q H g y) {w : X} (hwS : w ∈ S) (hwG : w ∈ G) {s t : X}
    (hs : s ∈ T) (ht : t ∈ T) :
    ∃ z ∈ (T ⊔ rightConjugate T g) ⊓ G, w⁻¹ * ((s * t)⁻¹ * w * (s * t)) =
      (w⁻¹ * (t⁻¹ * w * t)) * (w⁻¹ * (s⁻¹ * w * s)) * z := by
  have e := c.elem
  have hc := comm_mem_R e hwS hwG hs
  have htW : t ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) :=
    Subgroup.mem_sup_right (Subgroup.mem_sup_left ht)
  have hz := comm_mem_Z_of_mem_W e hc.1 htW
  refine ⟨_, hz, ?_⟩
  group

theorem sq_mem_Z (c : ElemCtx G T S Q H g y) {r : X}
    (hr : r ∈ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G) :
    r ^ 2 ∈ (T ⊔ rightConjugate T g) ⊓ G := by
  have e := c.elem
  have hVM := e.V_le_normalizer_M
  have hm : r ∈ (rightConjugate T y : Set X) * ((T ⊔ rightConjugate T g : Subgroup X) : Set X) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hVM]
    exact hr.1
  obtain ⟨v, hv, m, hm, hvm⟩ := Set.mem_mul.mp hm
  refine ⟨?_, G.pow_mem hr.2 2⟩
  rw [← hvm]
  have hvv : v * v = 1 := by rw [← pow_two, e.sq_V v hv]
  have hmv : v⁻¹ * m * v ∈ T ⊔ rightConjugate T g := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hVM hv)) m).mp hm
    simpa using this
  have h1 : (v * m) ^ 2 = (v⁻¹ * m * v) * m := by
    calc (v * m) ^ 2 = v * m * v * m := by rw [pow_two]; group
      _ = (v * v) * (v⁻¹ * m * v) * m := by group
      _ = (v⁻¹ * m * v) * m := by rw [hvv, one_mul]
  rw [h1]
  exact Subgroup.mul_mem _ hmv hm

theorem sq_mul_Z (c : ElemCtx G T S Q H g y) {x z : X}
    (hx : x ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g))
    (hz : z ∈ (T ⊔ rightConjugate T g) ⊓ G) : (x * z) ^ 2 = x ^ 2 := by
  have e := c.elem
  have hzx : z * x = x * z := e.Z_comm hz hx
  calc (x * z) ^ 2 = x * (z * x) * z := by rw [pow_two]; group
    _ = x * (x * z) * z := by rw [hzx]
    _ = x ^ 2 * z ^ 2 := by rw [pow_two, pow_two]; group
    _ = x ^ 2 := by rw [sq_Z e hz, mul_one]

theorem comm_comm_T_eq_sq (c : ElemCtx G T S Q H g y) {w : X} (hwS : w ∈ S) (hwG : w ∈ G)
    (hw2 : w ^ 2 = 1) {t : X} (ht : t ∈ T) :
    (w⁻¹ * (t⁻¹ * w * t))⁻¹ * (w⁻¹ * (w⁻¹ * (t⁻¹ * w * t)) * w) =
      (w⁻¹ * (t⁻¹ * w * t)) ^ 2 := by
  have hsq := c.sq_mem_Z (comm_mem_R c.elem hwS hwG ht)
  rw [conj_comm_eq_inv hw2, ← mul_inv_rev, ← pow_two, Elem47.inv_eq_of_sq (sq_Z c.elem hsq)]

theorem exists_comm_ne (c : ElemCtx G T S Q H g y) {w : X} (hwS : w ∈ S) (hwG : w ∈ G)
    (hwW : w ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) (hw2 : w ^ 2 = 1)
    (hq : 8 ≤ Nat.card T ∨ ∀ z ∈ (T ⊔ rightConjugate T g) ⊓ G, z * w = w * z) :
    ∃ s₁ ∈ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G,
      ∃ s₂ ∈ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G,
        s₁⁻¹ * (w⁻¹ * s₁ * w) ≠ 1 ∧ s₂⁻¹ * (w⁻¹ * s₂ * w) ≠ 1 ∧
          s₁⁻¹ * (w⁻¹ * s₁ * w) ≠ s₂⁻¹ * (w⁻¹ * s₂ * w) := by
  classical
  have e := c.elem
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hρR : ∀ t ∈ T, w⁻¹ * (t⁻¹ * w * t) ∈ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G :=
    fun t ht => comm_mem_R e hwS hwG ht
  have hρsq : ∀ t ∈ T, t ≠ 1 → (w⁻¹ * (t⁻¹ * w * t)) ^ 2 ≠ 1 := by
    intro t ht ht1 h
    exact ht1 (eq_one_of_comm_mem_Z e hwS hwW ht (mem_Z_of_sq e (hρR t ht).1 (hρR t ht).2 h))
  have hκ : ∀ t ∈ T, (w⁻¹ * (t⁻¹ * w * t))⁻¹ * (w⁻¹ * (w⁻¹ * (t⁻¹ * w * t)) * w) =
      (w⁻¹ * (t⁻¹ * w * t)) ^ 2 := fun t ht => c.comm_comm_T_eq_sq hwS hwG hw2 ht
  obtain ⟨t₁, ht₁, ht₁1⟩ := c.exists_ne_one
  set b := (w⁻¹ * (t₁⁻¹ * w * t₁)) ^ 2 with hbdef
  have hbZ : b ∈ (T ⊔ rightConjugate T g) ⊓ G := c.sq_mem_Z (hρR t₁ ht₁)
  have hbb : b * b = 1 := by rw [← pow_two, sq_Z e hbZ]
  have hb : ∀ t ∈ T, t ≠ 1 → (w⁻¹ * (t⁻¹ * w * t)) ^ 2 = b := by
    intro t ht ht1
    have h := hcon _ (hρR t ht) _ (hρR t₁ ht₁) (by rw [hκ t ht]; exact hρsq t ht ht1)
      (by rw [hκ t₁ ht₁]; exact hρsq t₁ ht₁ ht₁1)
    rwa [hκ t ht, hκ t₁ ht₁] at h
  have hK : ∀ t ∈ T, ∀ t' ∈ T, t ≠ 1 → t' ≠ 1 → t' * t ≠ 1 →
      (w⁻¹ * (t'⁻¹ * w * t'))⁻¹ * ((w⁻¹ * (t⁻¹ * w * t))⁻¹ * (w⁻¹ * (t'⁻¹ * w * t')) *
        (w⁻¹ * (t⁻¹ * w * t))) = b := by
    intro t ht t' ht' ht1 ht'1 htt
    obtain ⟨z, hz, hzeq⟩ := c.comm_mul_T hwS hwG ht' ht
    have hKZ := comm_mem_Z_of_mem_W e (hρR t' ht').1 (hρR t ht).1
    have hsq := sq_mul_eq (e.Z_comm hKZ (hρR t' ht').1)
    have h1 : (w⁻¹ * ((t' * t)⁻¹ * w * (t' * t))) ^ 2 = b :=
      hb _ (T.mul_mem ht' ht) htt
    rw [hzeq, c.sq_mul_Z (Subgroup.mul_mem _ (hρR t ht).1 (hρR t' ht').1) hz, hsq,
      hb t ht ht1, hb t' ht' ht'1, hbb, one_mul] at h1
    exact h1
  have hTinv : ∀ t ∈ T, t⁻¹ = t := fun t ht => Elem47.inv_eq_of_sq (e.sq_T t ht)
  have hne : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → t' * t ≠ 1 := by
    intro t ht t' ht' hne h
    apply hne
    have := eq_inv_of_mul_eq_one_left h
    rw [this, hTinv t ht]
  obtain ⟨t₂, ht₂, ht₂F⟩ := exists_mem_not_mem_finset (T := T) ({1, t₁} : Finset X)
    (lt_of_le_of_lt Finset.card_le_two (by linarith [e.four_le_card]))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht₂F
  obtain ⟨ht₂1, ht₂t₁⟩ := ht₂F
  have hK12 := hK t₁ ht₁ t₂ ht₂ ht₁1 ht₂1 (hne t₁ ht₁ t₂ ht₂ (Ne.symm ht₂t₁))
  rcases hq with hq | hq
  ·
    obtain ⟨t₃, ht₃, ht₃F⟩ := exists_mem_not_mem_finset (T := T) ({1, t₁, t₂, t₁ * t₂} : Finset X)
      (lt_of_le_of_lt Finset.card_le_four (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht₃F
    obtain ⟨ht₃1, ht₃t₁, ht₃t₂, ht₃t₁₂⟩ := ht₃F
    have ht₁₂ : t₁ * t₂ ∈ T := T.mul_mem ht₁ ht₂
    have ht₁₂1 : t₁ * t₂ ≠ 1 := by
      have := hne t₂ ht₂ t₁ ht₁ ht₂t₁
      exact this
    have hA := hK t₃ ht₃ (t₁ * t₂) ht₁₂ ht₃1 ht₁₂1 (hne t₃ ht₃ _ ht₁₂ ht₃t₁₂)
    have hB := hK t₃ ht₃ t₂ ht₂ ht₃1 ht₂1 (hne t₃ ht₃ t₂ ht₂ ht₃t₂)
    have hC := hK t₃ ht₃ t₁ ht₁ ht₃1 ht₁1 (hne t₃ ht₃ t₁ ht₁ ht₃t₁)
    obtain ⟨z, hz, hzeq⟩ := c.comm_mul_T hwS hwG ht₁ ht₂
    set x := w⁻¹ * (t₃⁻¹ * w * t₃) with hxdef
    set r₁ := w⁻¹ * (t₁⁻¹ * w * t₁) with hr₁def
    set r₂ := w⁻¹ * (t₂⁻¹ * w * t₂) with hr₂def
    rw [hzeq] at hA
    have hxW := (hρR t₃ ht₃).1
    have h2Z := comm_mem_Z_of_mem_W e (hρR t₂ ht₂).1 hxW
    have h21Z := comm_mem_Z_of_mem_W e (Subgroup.mul_mem _ (hρR t₂ ht₂).1 (hρR t₁ ht₁).1) hxW
    rw [comm_mul_of_comm (e.Z_comm h21Z (Subgroup.mem_sup_right hz.1)),
      comm_mul_of_comm (e.Z_comm h2Z (hρR t₁ ht₁).1),
      hB, hC, hbb, one_mul] at hA
    have hz1 : z⁻¹ * (x⁻¹ * z * x) = 1 := by
      rw [mul_assoc x⁻¹, e.Z_comm hz hxW, inv_mul_cancel_left, inv_mul_cancel]
    rw [hz1] at hA
    exact hρsq t₁ ht₁ ht₁1 hA.symm
  ·
    have hwZ : ∀ z ∈ (T ⊔ rightConjugate T g) ⊓ G, w⁻¹ * z * w = z := by
      intro z hz
      rw [mul_assoc, hq z hz]; group
    have hinv := fun {r : X} (hr : r ∈ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ⊓ G) =>
      conj_eq_inv_of_centralizes e hwS hwG hwW hw2 hwZ hr
    set r₁ := w⁻¹ * (t₁⁻¹ * w * t₁) with hr₁def
    set r₂ := w⁻¹ * (t₂⁻¹ * w * t₂) with hr₂def
    have hr₁ := hρR t₁ ht₁
    have hr₂ := hρR t₂ ht₂
    have hcomm : r₂ * r₁ = r₁ * r₂ := by
      have h1 := hinv (Subgroup.mul_mem _ hr₂ hr₁)
      have h2 : w⁻¹ * (r₂ * r₁) * w = (w⁻¹ * r₂ * w) * (w⁻¹ * r₁ * w) := by group
      rw [h2, hinv hr₂, hinv hr₁, mul_inv_rev] at h1
      have h3 := congrArg (fun x => x⁻¹) h1
      simpa using h3.symm
    have h1 : r₂⁻¹ * (r₁⁻¹ * r₂ * r₁) = 1 := by
      rw [mul_assoc r₁⁻¹, hcomm]; group
    rw [h1] at hK12
    exact hρsq t₁ ht₁ ht₁1 hK12.symm

end ElemCtx

end CFSG.ComponentClassification.AschbacherTheorem3.FourEight

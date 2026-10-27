module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.GH74.GLS.Stage4.Q9

@[expose] def Q8Cycle {G : Type*} [Group G] (K : Subgroup G) (z : G) : Prop :=
  ∀ p ∈ K, ∀ q ∈ K, p * p = z → q * q = z → q * p * q⁻¹ = p * z →
    ∃ r ∈ K, (r * p * r⁻¹ = q ∨ r * p * r⁻¹ = q * z) ∧
      (r * q * r⁻¹ = p * q ∨ r * q * r⁻¹ = p * q * z)

namespace Lemma82

variable {G : Type*} [Group G]

structure IsElem2Triple (z u w : G) : Prop where
  zz : z * z = 1
  uu : u * u = 1
  ww : w * w = 1
  zu : z * u = u * z
  zw : z * w = w * z
  uw : u * w = w * u

@[expose] def cubeEl (z u w : G) (v : Bool × Bool × Bool) : G :=
  (bif v.1 then z else 1) * (bif v.2.1 then u else 1) * (bif v.2.2 then w else 1)

theorem cubeEl_mul {z u w : G} (h : IsElem2Triple z u w) (v v' : Bool × Bool × Bool) :
    cubeEl z u w v * cubeEl z u w v' =
      cubeEl z u w (xor v.1 v'.1, xor v.2.1 v'.2.1, xor v.2.2 v'.2.2) := by
  obtain ⟨a, b, c⟩ := v
  obtain ⟨a', b', c'⟩ := v'
  have hz' : ∀ x : G, z * (z * x) = x := fun x => by rw [← mul_assoc, h.zz, one_mul]
  have hu' : ∀ x : G, u * (u * x) = x := fun x => by rw [← mul_assoc, h.uu, one_mul]
  have huz : u * z = z * u := h.zu.symm
  have hwz : w * z = z * w := h.zw.symm
  have hwu : w * u = u * w := h.uw.symm
  have huz' : ∀ x : G, u * (z * x) = z * (u * x) := fun x => by
    rw [← mul_assoc, huz, mul_assoc]
  have hwz' : ∀ x : G, w * (z * x) = z * (w * x) := fun x => by
    rw [← mul_assoc, hwz, mul_assoc]
  have hwu' : ∀ x : G, w * (u * x) = u * (w * x) := fun x => by
    rw [← mul_assoc, hwu, mul_assoc]
  cases a <;> cases b <;> cases c <;> cases a' <;> cases b' <;> cases c' <;>
    simp [cubeEl, mul_assoc, h.zz, h.uu, h.ww, hz', hu', huz, hwz, hwu, huz', hwz', hwu']

theorem cubeEl_false {z u w : G} : cubeEl z u w (false, false, false) = 1 := by
  simp [cubeEl]

theorem cubeEl_mul_self {z u w : G} (h : IsElem2Triple z u w) (v : Bool × Bool × Bool) :
    cubeEl z u w v * cubeEl z u w v = 1 := by
  rw [cubeEl_mul h]
  simp [cubeEl_false]

theorem cubeEl_eq_one {z u w : G} (h : IsElem2Triple z u w) (hz1 : z ≠ 1) (hu1 : u ≠ 1)
    (huz : u ≠ z) (hw1 : w ≠ 1) (hwz : w ≠ z) (hwu : w ≠ u) (hwuz : w ≠ u * z)
    (v : Bool × Bool × Bool) (hv : cubeEl z u w v = 1) : v = (false, false, false) := by
  obtain ⟨a, b, c⟩ := v
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right h.zz
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right h.uu
  cases a <;> cases b <;> cases c <;>
    simp only [cubeEl, Bool.cond_true, Bool.cond_false, mul_one, one_mul] at hv ⊢
  · exact absurd hv hw1
  · exact absurd hv hu1
  · exact absurd ((eq_inv_of_mul_eq_one_right hv).trans hui) hwu
  · exact absurd hv hz1
  · exact absurd ((eq_inv_of_mul_eq_one_right hv).trans hzi) hwz
  · exact absurd ((eq_inv_of_mul_eq_one_right hv).trans hzi) huz
  · exact absurd ((eq_inv_of_mul_eq_one_right hv).trans (by rw [mul_inv_rev, hui, hzi])) hwuz

theorem cubeEl_injective {z u w : G} (h : IsElem2Triple z u w) (hz1 : z ≠ 1) (hu1 : u ≠ 1)
    (huz : u ≠ z) (hw1 : w ≠ 1) (hwz : w ≠ z) (hwu : w ≠ u) (hwuz : w ≠ u * z) :
    Function.Injective (cubeEl z u w) := by
  intro v v' hvv'
  have h1 : cubeEl z u w (xor v.1 v'.1, xor v.2.1 v'.2.1, xor v.2.2 v'.2.2) = 1 := by
    rw [← cubeEl_mul h v v', hvv']
    exact cubeEl_mul_self h v'
  have h2 := cubeEl_eq_one h hz1 hu1 huz hw1 hwz hwu hwuz _ h1
  obtain ⟨a, b, c⟩ := v
  obtain ⟨a', b', c'⟩ := v'
  simp only [Prod.mk.injEq] at h2 ⊢
  obtain ⟨h3, h4, h5⟩ := h2
  refine ⟨?_, ?_, ?_⟩
  · cases a <;> cases a' <;> simp_all
  · cases b <;> cases b' <;> simp_all
  · cases c <;> cases c' <;> simp_all

theorem conj_cubeEl (z u w g : G) (v : Bool × Bool × Bool) :
    g * cubeEl z u w v * g⁻¹ = (bif v.1 then g * z * g⁻¹ else 1) *
      (bif v.2.1 then g * u * g⁻¹ else 1) * (bif v.2.2 then g * w * g⁻¹ else 1) := by
  obtain ⟨a, b, c⟩ := v
  cases a <;> cases b <;> cases c <;> simp [cubeEl]

theorem conj_mem_range_cubeEl {z u w g : G} (h : IsElem2Triple z u w)
    (hz : g * z * g⁻¹ ∈ Set.range (cubeEl z u w)) (hu : g * u * g⁻¹ ∈ Set.range (cubeEl z u w))
    (hw : g * w * g⁻¹ ∈ Set.range (cubeEl z u w)) :
    ∀ p ∈ Set.range (cubeEl z u w), g * p * g⁻¹ ∈ Set.range (cubeEl z u w) := by
  have hmul : ∀ p ∈ Set.range (cubeEl z u w), ∀ q ∈ Set.range (cubeEl z u w),
      p * q ∈ Set.range (cubeEl z u w) := by
    rintro _ ⟨v, rfl⟩ _ ⟨v', rfl⟩
    exact ⟨_, (cubeEl_mul h v v').symm⟩
  have hone : (1 : G) ∈ Set.range (cubeEl z u w) := ⟨(false, false, false), cubeEl_false⟩
  have key : ∀ (t : Bool) (p : G), p ∈ Set.range (cubeEl z u w) →
      (bif t then p else 1) ∈ Set.range (cubeEl z u w) := by
    intro t p hp
    cases t <;> simp [hp, hone]
  rintro _ ⟨⟨a, b, c⟩, rfl⟩
  rw [conj_cubeEl]
  exact hmul _ (hmul _ (key a _ hz) _ (key b _ hu)) _ (key c _ hw)

theorem ncard_conj_orbit_dvd_card [Finite G] (N : Subgroup G) (z : G) :
    {q : G | ∃ n ∈ N, n * z * n⁻¹ = q}.ncard ∣ Nat.card G := by
  let f : N →* ConjAct G := (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom.comp N.subtype
  let _ : MulAction N G := MulAction.compHom G f
  have hset : {q : G | ∃ n ∈ N, n * z * n⁻¹ = q} = MulAction.orbit N z := by
    ext q
    simp only [Set.mem_ofPred_eq, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, rfl⟩
    · rintro ⟨⟨n, hn⟩, rfl⟩
      exact ⟨n, hn, rfl⟩
  rw [hset, ← MulAction.index_stabilizer N z]
  exact (Subgroup.index_dvd_card _).trans (Subgroup.card_subgroup_dvd_card N)

theorem seven_dvd_card_of_cube [Finite G] {z u w a c d x : G} (h : IsElem2Triple z u w)
    (hz1 : z ≠ 1) (hu1 : u ≠ 1) (huz : u ≠ z) (hw1 : w ≠ 1) (hwz : w ≠ z) (hwu : w ≠ u)
    (hwuz : w ≠ u * z)
    (ha1 : a * z * a⁻¹ = u ∨ a * z * a⁻¹ = u * z)
    (ha2 : a * u * a⁻¹ = 1 ∨ a * u * a⁻¹ = z ∨ a * u * a⁻¹ = u ∨ a * u * a⁻¹ = u * z)
    (ha3 : a * w * a⁻¹ = w)
    (hc1 : c * z * c⁻¹ = z) (hc2 : c * u * c⁻¹ = u * z) (hc3 : c * w * c⁻¹ = w)
    (hd1 : d * z * d⁻¹ = z) (hd2 : d * u * d⁻¹ = u) (hd3 : d * w * d⁻¹ = w * z)
    (hx1 : x * z * x⁻¹ = z) (hx2 : x * u * x⁻¹ = w ∨ x * u * x⁻¹ = w * z)
    (hx3 : x * w * x⁻¹ = u * w ∨ x * w * x⁻¹ = u * w * z) :
    7 ∣ Nat.card G := by
  classical
  have hinj := cubeEl_injective h hz1 hu1 huz hw1 hwz hwu hwuz
  have hzE : z ∈ Set.range (cubeEl z u w) := ⟨(true, false, false), by simp [cubeEl]⟩
  have huE : u ∈ Set.range (cubeEl z u w) := ⟨(false, true, false), by simp [cubeEl]⟩
  have hwE : w ∈ Set.range (cubeEl z u w) := ⟨(false, false, true), by simp [cubeEl]⟩
  have honeE : (1 : G) ∈ Set.range (cubeEl z u w) := ⟨(false, false, false), cubeEl_false⟩
  have hmulE : ∀ p ∈ Set.range (cubeEl z u w), ∀ q ∈ Set.range (cubeEl z u w),
      p * q ∈ Set.range (cubeEl z u w) := by
    rintro _ ⟨v, rfl⟩ _ ⟨v', rfl⟩
    exact ⟨_, (cubeEl_mul h v v').symm⟩
  have huzE : u * z ∈ Set.range (cubeEl z u w) := hmulE _ huE _ hzE
  have hwzE : w * z ∈ Set.range (cubeEl z u w) := hmulE _ hwE _ hzE
  have huwE : u * w ∈ Set.range (cubeEl z u w) := hmulE _ huE _ hwE
  have huwzE : u * w * z ∈ Set.range (cubeEl z u w) := hmulE _ huwE _ hzE
  have hmemN : ∀ g : G, g * z * g⁻¹ ∈ Set.range (cubeEl z u w) →
      g * u * g⁻¹ ∈ Set.range (cubeEl z u w) → g * w * g⁻¹ ∈ Set.range (cubeEl z u w) →
      g ∈ Subgroup.normalizer (Set.range (cubeEl z u w)) := fun g hgz hgu hgw =>
    Subgroup.mem_normalizer_fintype (conj_mem_range_cubeEl h hgz hgu hgw)
  set N : Subgroup G := Subgroup.normalizer (Set.range (cubeEl z u w))
  have haN : a ∈ N := hmemN a (by rcases ha1 with h1 | h1 <;> rw [h1] <;> assumption)
    (by rcases ha2 with h1 | h1 | h1 | h1 <;> rw [h1] <;> assumption)
    (by rw [ha3]; exact hwE)
  have hcN : c ∈ N := hmemN c (by rw [hc1]; exact hzE) (by rw [hc2]; exact huzE)
    (by rw [hc3]; exact hwE)
  have hdN : d ∈ N := hmemN d (by rw [hd1]; exact hzE) (by rw [hd2]; exact huE)
    (by rw [hd3]; exact hwzE)
  have hxN : x ∈ N := hmemN x (by rw [hx1]; exact hzE)
    (by rcases hx2 with h1 | h1 <;> rw [h1] <;> assumption)
    (by rcases hx3 with h1 | h1 <;> rw [h1] <;> assumption)
  set O : Set G := {q : G | ∃ n ∈ N, n * z * n⁻¹ = q}
  have hzO : z ∈ O := ⟨1, N.one_mem, by simp⟩
  have hOcl : ∀ n ∈ N, ∀ q ∈ O, n * q * n⁻¹ ∈ O := by
    rintro n hn _ ⟨m, hm, rfl⟩
    exact ⟨n * m, N.mul_mem hn hm, by group⟩
  have huO : u ∈ O ∧ u * z ∈ O := by
    have hp := hOcl a haN z hzO
    rcases ha1 with h1 | h1
    · rw [h1] at hp
      refine ⟨hp, ?_⟩
      have := hOcl c hcN _ hp
      rwa [hc2] at this
    · rw [h1] at hp
      refine ⟨?_, hp⟩
      have := hOcl c hcN _ hp
      have e : c * (u * z) * c⁻¹ = u := by
        calc c * (u * z) * c⁻¹ = (c * u * c⁻¹) * (c * z * c⁻¹) := by group
          _ = u := by rw [hc2, hc1, mul_assoc, h.zz, mul_one]
      rwa [e] at this
  have hwO : w ∈ O ∧ w * z ∈ O := by
    have hp := hOcl x hxN u huO.1
    rcases hx2 with h1 | h1
    · rw [h1] at hp
      refine ⟨hp, ?_⟩
      have := hOcl d hdN _ hp
      rwa [hd3] at this
    · rw [h1] at hp
      refine ⟨?_, hp⟩
      have := hOcl d hdN _ hp
      have e : d * (w * z) * d⁻¹ = w := by
        calc d * (w * z) * d⁻¹ = (d * w * d⁻¹) * (d * z * d⁻¹) := by group
          _ = w := by rw [hd3, hd1, mul_assoc, h.zz, mul_one]
      rwa [e] at this
  have huwO : u * w ∈ O ∧ u * w * z ∈ O := by
    have hp := hOcl x hxN w hwO.1
    rcases hx3 with h1 | h1
    · rw [h1] at hp
      refine ⟨hp, ?_⟩
      have := hOcl c hcN _ hp
      have e : c * (u * w) * c⁻¹ = u * w * z := by
        calc c * (u * w) * c⁻¹ = (c * u * c⁻¹) * (c * w * c⁻¹) := by group
          _ = u * w * z := by rw [hc2, hc3, mul_assoc u z w, h.zw, ← mul_assoc]
      rwa [e] at this
    · rw [h1] at hp
      refine ⟨?_, hp⟩
      have := hOcl c hcN _ hp
      have e : c * (u * w * z) * c⁻¹ = u * w := by
        calc c * (u * w * z) * c⁻¹ = (c * u * c⁻¹) * (c * w * c⁻¹) * (c * z * c⁻¹) := by group
          _ = u * w := by
            rw [hc2, hc3, hc1, mul_assoc u z w, h.zw, ← mul_assoc, mul_assoc (u * w) z z, h.zz,
              mul_one]
      rwa [e] at this
  have hOeq : O = (cubeEl z u w) '' {v | v ≠ (false, false, false)} := by
    ext q
    constructor
    · rintro ⟨n, hn, rfl⟩
      have hnE : n * z * n⁻¹ ∈ Set.range (cubeEl z u w) :=
        (Subgroup.mem_set_normalizer_iff.mp hn z).mp hzE
      obtain ⟨v, hv⟩ := hnE
      refine ⟨v, ?_, hv⟩
      intro hv0
      rw [hv0, cubeEl_false] at hv
      apply hz1
      have h1 : n * z * n⁻¹ = 1 := hv.symm
      simpa using h1
    · rintro ⟨⟨a₁, b₁, c₁⟩, hv, rfl⟩
      cases a₁ <;> cases b₁ <;> cases c₁ <;>
        simp only [cubeEl, Bool.cond_true, Bool.cond_false, mul_one, one_mul]
      · exact absurd rfl hv
      · exact hwO.1
      · exact huO.1
      · exact huwO.1
      · exact hzO
      · rw [h.zw]; exact hwO.2
      · rw [h.zu]; exact huO.2
      · rw [h.zu, mul_assoc, h.zw, ← mul_assoc]; exact huwO.2
  have h7 : {v : Bool × Bool × Bool | v ≠ (false, false, false)}.ncard = 7 := by
    rw [Set.ncard_eq_toFinset_card']
    decide
  have hdiv : O.ncard ∣ Nat.card G := ncard_conj_orbit_dvd_card N z
  rwa [hOeq, Set.ncard_image_of_injective _ hinj, h7] at hdiv

theorem mem_sup_of_commute {K₁ K₂ : Subgroup G} (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x)
    {g : G} (hg : g ∈ K₁ ⊔ K₂) : ∃ k₁ ∈ K₁, ∃ k₂ ∈ K₂, k₁ * k₂ = g := by
  rw [Subgroup.sup_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, K₂.one_mem, mul_one x⟩
    · exact ⟨1, K₁.one_mem, x, hx, one_mul x⟩
  | one => exact ⟨1, K₁.one_mem, 1, K₂.one_mem, mul_one 1⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := ihx
    obtain ⟨a', ha', b', hb', rfl⟩ := ihy
    refine ⟨a * a', K₁.mul_mem ha ha', b * b', K₂.mul_mem hb hb', ?_⟩
    calc a * a' * (b * b') = a * (a' * b) * b' := by simp only [mul_assoc]
      _ = a * (b * a') * b' := by rw [hcomm a' ha' b hb]
      _ = a * b * (a' * b') := by simp only [mul_assoc]
  | inv x hx ih =>
    obtain ⟨a, ha, b, hb, rfl⟩ := ih
    refine ⟨a⁻¹, K₁.inv_mem ha, b⁻¹, K₂.inv_mem hb, ?_⟩
    rw [mul_inv_rev]
    exact hcomm a⁻¹ (K₁.inv_mem ha) b⁻¹ (K₂.inv_mem hb)

theorem mem_closure_pair_cases {z u g : G} (hzz : z * z = 1) (huu : u * u = 1)
    (hzu : z * u = u * z) (hg : g ∈ Subgroup.closure ({z, u} : Set G)) :
    g = 1 ∨ g = z ∨ g = u ∨ g = u * z := by
  have hu' : ∀ x : G, u * (u * x) = x := fun x => by rw [← mul_assoc, huu, one_mul]
  have hzu' : ∀ x : G, z * (u * x) = u * (z * x) := fun x => by
    rw [← mul_assoc, hzu, mul_assoc]
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · simp
    · rw [Set.mem_singleton_iff] at hx
      simp [hx]
  | one => simp
  | mul x y hx hy ihx ihy =>
    rcases ihx with rfl | rfl | rfl | rfl <;> rcases ihy with rfl | rfl | rfl | rfl <;>
      simp [mul_assoc, hzz, huu, hu', hzu, hzu']
  | inv x hx ih =>
    rcases ih with rfl | rfl | rfl | rfl <;> simp [hzi, hui, mul_inv_rev, hzu]

theorem sl2_sq_eq_one {F : Type*} [Field F] (hF : (2 : F) ≠ 0)
    (A : Matrix.SpecialLinearGroup (Fin 2) F) (h : A * A = 1) :
    (A : Matrix (Fin 2) (Fin 2) F) = 1 ∨ (A : Matrix (Fin 2) (Fin 2) F) = -1 := by
  have hA := congrArg (fun B : Matrix.SpecialLinearGroup (Fin 2) F =>
    (B : Matrix (Fin 2) (Fin 2) F)) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at hA
  have hdet : (A : Matrix (Fin 2) (Fin 2) F).det = 1 := A.2
  have h00 := congrFun (congrFun hA 0) 0
  have h01 := congrFun (congrFun hA 0) 1
  have h10 := congrFun (congrFun hA 1) 0
  have h11 := congrFun (congrFun hA 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  rw [Matrix.det_fin_two] at hdet
  by_cases hs : (A : Matrix (Fin 2) (Fin 2) F) 0 0 + (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 0
  · exfalso
    apply hF
    linear_combination (-1 : F) * hdet - h00 + (A : Matrix (Fin 2) (Fin 2) F) 0 0 * hs
  · have hb : (A : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
      have : (A : Matrix (Fin 2) (Fin 2) F) 0 1 *
          ((A : Matrix (Fin 2) (Fin 2) F) 0 0 + (A : Matrix (Fin 2) (Fin 2) F) 1 1) = 0 := by
        linear_combination h01
      exact (mul_eq_zero.mp this).resolve_right hs
    have hc : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      have : (A : Matrix (Fin 2) (Fin 2) F) 1 0 *
          ((A : Matrix (Fin 2) (Fin 2) F) 0 0 + (A : Matrix (Fin 2) (Fin 2) F) 1 1) = 0 := by
        linear_combination h10
      exact (mul_eq_zero.mp this).resolve_right hs
    rw [hb, hc] at h00 h11 hdet
    have ha2 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
      linear_combination h00
    have had : (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
      linear_combination hdet
    have ha0 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
      intro h0
      rw [h0] at ha2
      simp at ha2
    have hda : (A : Matrix (Fin 2) (Fin 2) F) 1 1 = (A : Matrix (Fin 2) (Fin 2) F) 0 0 :=
      (mul_left_cancel₀ ha0 (had.trans ha2.symm)).symm.symm
    rcases mul_self_eq_one_iff.mp ha2 with h1 | h1
    · left
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h1, hda, hb, hc]
    · right
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h1, hda, hb, hc]


theorem eq_one_or_eq_of_sq_eq_one_of_mulEquiv_sl2 {G F : Type*} [Group G] [Field F] (hF : (2 : F) ≠ 0)
    {K : Subgroup G} (φ : K ≃* Matrix.SpecialLinearGroup (Fin 2) F) {z : G} (hzK : z ∈ K)
    (hz : orderOf z = 2) : ∀ k ∈ K, k * k = 1 → k = 1 ∨ k = z := by
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz, sq] at this
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hsq : ∀ k : K, (k : G) * k = 1 → φ k * φ k = 1 := fun k hk => by
    rw [← map_mul, ← map_one φ]
    exact congrArg φ (Subtype.ext hk)
  intro k hk hkk
  rcases sl2_sq_eq_one hF _ (hsq ⟨k, hk⟩ hkk) with h1 | h1
  · left
    have : φ ⟨k, hk⟩ = 1 := Subtype.ext h1
    have := φ.injective (this.trans (map_one φ).symm)
    exact congrArg Subtype.val this
  · right
    rcases sl2_sq_eq_one hF _ (hsq ⟨z, hzK⟩ hzz) with h2 | h2
    · exfalso
      apply hz1
      have : φ ⟨z, hzK⟩ = 1 := Subtype.ext h2
      have := φ.injective (this.trans (map_one φ).symm)
      exact congrArg Subtype.val this
    · have : φ ⟨k, hk⟩ = φ ⟨z, hzK⟩ := Subtype.ext (h1.trans h2.symm)
      exact congrArg Subtype.val (φ.injective this)

theorem two_ne_zero_of_natCard_eq_nine {F : Type*} [Field F] (h : Nat.card F = 9) : (2 : F) ≠ 0 := by
  intro h2
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype F := Fintype.ofFinite F
  have hc : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by exact_mod_cast h2)
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  rw [Nat.card_eq_fintype_card] at h
  have : Even (2 ^ (n : ℕ)) := (Nat.even_pow.mpr ⟨even_two, n.pos.ne'⟩)
  rw [← hn, h] at this
  exact absurd this (by decide)

end Lemma82

open Lemma82

theorem seven_dvd_card {G : Type*} [Group G] [Finite G] {z : G} {K₁ K₂ : Subgroup G}
    (hz : orderOf z = 2)
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (hinter : K₁ ⊓ K₂ = Subgroup.zpowers z)
    (hK₁ : ∀ k ∈ K₁, k * k = 1 → k = 1 ∨ k = z)
    (hQ₁ : Q8Cycle K₁ z) (hQ₂ : Q8Cycle K₂ z) (u w₁ w₂ a : G)
    (hu : u ∈ K₁ ⊔ K₂) (huo : orderOf u = 2) (huz : u ≠ z)
    (hw₁ : w₁ ∈ K₁) (hw₂ : w₂ ∈ K₂) (hw₁s : w₁ * w₁ = z) (hw₂s : w₂ * w₂ = z)
    (hw₁u : w₁ * u * w₁⁻¹ = u * z) (hw₂u : w₂ * u * w₂⁻¹ = u * z)
    (ha₁ : a * z * a⁻¹ ∈ Subgroup.closure ({z, u} : Set G))
    (ha₂ : a * u * a⁻¹ ∈ Subgroup.closure ({z, u} : Set G))
    (ha₃ : a * z * a⁻¹ ≠ z) (ha₄ : a * (w₁ * w₂) * a⁻¹ = w₁ * w₂) : 7 ∣ Nat.card G := by
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz, sq] at this
  have huu : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [huo, sq] at this
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at huo
    exact absurd huo (by norm_num)
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hzK : z ∈ K₁ ⊓ K₂ := by
    rw [hinter]
    exact Subgroup.mem_zpowers z
  have hzK₁ : z ∈ K₁ := hzK.1
  have hzK₂ : z ∈ K₂ := hzK.2
  have hint : ∀ y, y ∈ K₁ → y ∈ K₂ → y = 1 ∨ y = z := by
    intro y h1 h2
    have hy : y ∈ Subgroup.zpowers z := by
      rw [← hinter]
      exact ⟨h1, h2⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hmod := zpow_mod_orderOf z k
    rw [hz] at hmod
    rcases Int.emod_two_eq_zero_or_one k with h0 | h0
    · left
      rw [← hmod]
      simp [h0]
    · right
      rw [← hmod]
      simp [h0]
  have hc1z : ∀ x ∈ K₁, x * z = z * x := fun x hx => hcomm x hx z hzK₂
  have hc2z : ∀ y ∈ K₂, y * z = z * y := fun y hy => (hcomm z hzK₁ y hy).symm
  have hZ₁ : ∀ x ∈ K₁, Commute z x := fun x hx => (hc1z x hx).symm
  have hZ₂ : ∀ y ∈ K₂, Commute z y := fun y hy => (hc2z y hy).symm
  have hcj₁ : ∀ g ∈ K₁, g * z * g⁻¹ = z := fun g hg => by
    rw [hc1z g hg, mul_inv_cancel_right]
  have hcj₂ : ∀ g ∈ K₂, g * z * g⁻¹ = z := fun g hg => by
    rw [hc2z g hg, mul_inv_cancel_right]
  have hfix₁ : ∀ g ∈ K₁, ∀ y ∈ K₂, g * y * g⁻¹ = y := fun g hg y hy => by
    rw [hcomm g hg y hy, mul_inv_cancel_right]
  have hfix₂ : ∀ g ∈ K₂, ∀ y ∈ K₁, g * y * g⁻¹ = y := fun g hg y hy => by
    rw [← hcomm y hy g hg, mul_inv_cancel_right]
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := mem_sup_of_commute hcomm hu
  have hu12c : u₁ * u₂ = u₂ * u₁ := hcomm u₁ hu₁ u₂ hu₂
  have hsq : u₁ * u₁ * (u₂ * u₂) = 1 := by
    calc u₁ * u₁ * (u₂ * u₂) = u₁ * (u₁ * u₂) * u₂ := by simp only [mul_assoc]
      _ = u₁ * (u₂ * u₁) * u₂ := by rw [hu12c]
      _ = u₁ * u₂ * (u₁ * u₂) := by simp only [mul_assoc]
      _ = 1 := huu
  have hu₁sq' : u₁ * u₁ = 1 ∨ u₁ * u₁ = z := by
    refine hint _ (K₁.mul_mem hu₁ hu₁) ?_
    have : u₁ * u₁ = (u₂ * u₂)⁻¹ := eq_inv_of_mul_eq_one_left hsq
    rw [this]
    exact K₂.inv_mem (K₂.mul_mem hu₂ hu₂)
  have hw₁u₁ : w₁ * u₁ * w₁⁻¹ = u₁ * z := by
    have e1 : w₁ * (u₁ * u₂) * w₁⁻¹ = (w₁ * u₁ * w₁⁻¹) * (w₁ * u₂ * w₁⁻¹) := by group
    have e2 : u₁ * u₂ * z = u₁ * z * u₂ := by
      rw [mul_assoc, hc2z u₂ hu₂, ← mul_assoc]
    have h3 := hw₁u
    rw [e1, hfix₁ w₁ hw₁ u₂ hu₂, e2] at h3
    exact mul_right_cancel h3
  have hw₂u₂ : w₂ * u₂ * w₂⁻¹ = u₂ * z := by
    have e1 : w₂ * (u₁ * u₂) * w₂⁻¹ = (w₂ * u₁ * w₂⁻¹) * (w₂ * u₂ * w₂⁻¹) := by group
    have h3 := hw₂u
    rw [e1, hfix₂ w₂ hw₂ u₁ hu₁, mul_assoc u₁ u₂ z] at h3
    exact mul_left_cancel h3
  have hnc : w₁ * u₁ ≠ u₁ * w₁ := by
    intro h
    have h1 : w₁ * u₁ * w₁⁻¹ = u₁ := by rw [h, mul_inv_cancel_right]
    rw [h1] at hw₁u₁
    apply hz1
    have h2 : u₁ * 1 = u₁ * z := by rw [mul_one]; exact hw₁u₁
    exact (mul_left_cancel h2).symm
  have hu₁sq : u₁ * u₁ = z := by
    rcases hu₁sq' with h1 | h1
    · exfalso
      rcases hK₁ u₁ hu₁ h1 with h2 | h2
      · apply hnc
        rw [h2]
        simp
      · apply hnc
        rw [h2]
        exact hc1z w₁ hw₁
    · exact h1
  have hu₂sq : u₂ * u₂ = z := by
    have h1 : z * (u₂ * u₂) = 1 := by rw [← hu₁sq]; exact hsq
    rw [eq_inv_of_mul_eq_one_right h1, hzi]
  have hu₁i : u₁⁻¹ = u₁ * z := by
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, hu₁sq, hzz]
  have hu₁w₁ : u₁ * w₁ * u₁⁻¹ = w₁ * z := by
    calc u₁ * w₁ * u₁⁻¹ = u₁ * (w₁ * u₁) * z := by rw [hu₁i]; simp only [mul_assoc]
      _ = u₁ * (u₁ * z * w₁) * z := by
        have : w₁ * u₁ = u₁ * z * w₁ := mul_inv_eq_iff_eq_mul.mp hw₁u₁
        rw [this]
      _ = (u₁ * u₁) * z * w₁ * z := by simp only [mul_assoc]
      _ = w₁ * z := by rw [hu₁sq, hzz, one_mul]
  obtain ⟨r₁, hr₁, hr₁u, hr₁w⟩ := hQ₁ u₁ hu₁ w₁ hw₁ hu₁sq hw₁s hw₁u₁
  obtain ⟨r₂, hr₂, hr₂u, hr₂w⟩ := hQ₂ u₂ hu₂ w₂ hw₂ hu₂sq hw₂s hw₂u₂
  have hw₁w₂c : w₁ * w₂ = w₂ * w₁ := hcomm w₁ hw₁ w₂ hw₂
  have hww : w₁ * w₂ * (w₁ * w₂) = 1 := by
    calc w₁ * w₂ * (w₁ * w₂) = w₁ * (w₂ * w₁) * w₂ := by simp only [mul_assoc]
      _ = w₁ * (w₁ * w₂) * w₂ := by rw [hw₁w₂c]
      _ = (w₁ * w₁) * (w₂ * w₂) := by simp only [mul_assoc]
      _ = 1 := by rw [hw₁s, hw₂s, hzz]
  have hzu : z * (u₁ * u₂) = u₁ * u₂ * z := ((hZ₁ u₁ hu₁).mul_right (hZ₂ u₂ hu₂)).eq
  have hzw : z * (w₁ * w₂) = w₁ * w₂ * z := ((hZ₁ w₁ hw₁).mul_right (hZ₂ w₂ hw₂)).eq
  have huw : u₁ * u₂ * (w₁ * w₂) = w₁ * w₂ * (u₁ * u₂) := by
    have hwu : w₁ * w₂ * (u₁ * u₂) * (w₁ * w₂)⁻¹ = u₁ * u₂ := by
      calc w₁ * w₂ * (u₁ * u₂) * (w₁ * w₂)⁻¹
          = w₁ * (w₂ * (u₁ * u₂) * w₂⁻¹) * w₁⁻¹ := by group
        _ = w₁ * (u₁ * u₂ * z) * w₁⁻¹ := by rw [hw₂u]
        _ = (w₁ * (u₁ * u₂) * w₁⁻¹) * (w₁ * z * w₁⁻¹) := by group
        _ = (u₁ * u₂ * z) * z := by rw [hw₁u, hcj₁ w₁ hw₁]
        _ = u₁ * u₂ := by rw [mul_assoc, hzz, mul_one]
    exact (mul_inv_eq_iff_eq_mul.mp hwu).symm
  have hcube : IsElem2Triple z (u₁ * u₂) (w₁ * w₂) := ⟨hzz, huu, hww, hzu, hzw, huw⟩
  have hw₁0 : w₁ ≠ 1 ∧ w₁ ≠ z := by
    constructor
    · intro h
      apply hz1
      rw [← hw₁s, h, mul_one]
    · intro h
      apply hz1
      have := hw₁s
      rw [h, hzz] at this
      exact this.symm
  have hdec : ∀ k₁ ∈ K₁, ∀ k₂ ∈ K₂, w₁ * w₂ = k₁ * k₂ → w₁ = k₁ ∨ w₁ = k₁ * z := by
    intro k₁ hk₁ k₂ hk₂ h
    have hmem : k₁⁻¹ * w₁ = k₂ * w₂⁻¹ := by
      calc k₁⁻¹ * w₁ = k₁⁻¹ * (w₁ * w₂) * w₂⁻¹ := by group
        _ = k₁⁻¹ * (k₁ * k₂) * w₂⁻¹ := by rw [h]
        _ = k₂ * w₂⁻¹ := by group
    have h1 : k₁⁻¹ * w₁ ∈ K₁ := K₁.mul_mem (K₁.inv_mem hk₁) hw₁
    have h2 : k₁⁻¹ * w₁ ∈ K₂ := hmem ▸ K₂.mul_mem hk₂ (K₂.inv_mem hw₂)
    rcases hint _ h1 h2 with h3 | h3
    · left
      exact (inv_mul_eq_one.mp h3).symm
    · right
      calc w₁ = k₁ * (k₁⁻¹ * w₁) := by group
        _ = k₁ * z := by rw [h3]
  have hw₁ne : ∀ y, (y = u₁ ∨ y = u₁ * z) → w₁ ≠ y := by
    rintro y (rfl | rfl) hy
    · exact hnc (by rw [hy])
    · apply hnc
      rw [hy, mul_assoc, ← hc1z u₁ hu₁]
  have hw1 : w₁ * w₂ ≠ 1 := by
    intro h
    rcases hdec 1 K₁.one_mem 1 K₂.one_mem (by rw [h, mul_one]) with h1 | h1
    · exact hw₁0.1 h1
    · exact hw₁0.2 (by rw [h1, one_mul])
  have hwz : w₁ * w₂ ≠ z := by
    intro h
    rcases hdec z hzK₁ 1 K₂.one_mem (by rw [h, mul_one]) with h1 | h1
    · exact hw₁0.2 h1
    · exact hw₁0.1 (by rw [h1, hzz])
  have hwu : w₁ * w₂ ≠ u₁ * u₂ := by
    intro h
    rcases hdec u₁ hu₁ u₂ hu₂ h with h1 | h1
    · exact hw₁ne u₁ (Or.inl rfl) h1
    · exact hw₁ne (u₁ * z) (Or.inr rfl) h1
  have hwuz : w₁ * w₂ ≠ u₁ * u₂ * z := by
    intro h
    have e : u₁ * u₂ * z = (u₁ * z) * u₂ := by
      rw [mul_assoc, hc2z u₂ hu₂, ← mul_assoc]
    rw [e] at h
    rcases hdec (u₁ * z) (K₁.mul_mem hu₁ hzK₁) u₂ hu₂ h with h1 | h1
    · exact hw₁ne (u₁ * z) (Or.inr rfl) h1
    · refine hw₁ne u₁ (Or.inl rfl) ?_
      rw [h1, mul_assoc, hzz, mul_one]
  have hzi' : ∀ g : G, g * z * g⁻¹ ≠ 1 := by
    intro g h
    apply hz1
    simpa using h
  have ha1 : a * z * a⁻¹ = u₁ * u₂ ∨ a * z * a⁻¹ = u₁ * u₂ * z := by
    rcases mem_closure_pair_cases hzz huu hzu ha₁ with h | h | h | h
    · exact absurd h (hzi' a)
    · exact absurd h ha₃
    · exact Or.inl h
    · exact Or.inr h
  have ha2 := mem_closure_pair_cases hzz huu hzu ha₂
  have hc3 : w₁ * (w₁ * w₂) * w₁⁻¹ = w₁ * w₂ := by
    calc w₁ * (w₁ * w₂) * w₁⁻¹ = w₁ * (w₂ * w₁) * w₁⁻¹ := by rw [hw₁w₂c]
      _ = w₁ * w₂ := by group
  have hd2 : u₁ * (u₁ * u₂) * u₁⁻¹ = u₁ * u₂ := by
    calc u₁ * (u₁ * u₂) * u₁⁻¹ = u₁ * (u₂ * u₁) * u₁⁻¹ := by rw [hu12c]
      _ = u₁ * u₂ := by group
  have hd3 : u₁ * (w₁ * w₂) * u₁⁻¹ = w₁ * w₂ * z := by
    calc u₁ * (w₁ * w₂) * u₁⁻¹ = (u₁ * w₁ * u₁⁻¹) * (u₁ * w₂ * u₁⁻¹) := by group
      _ = (w₁ * z) * w₂ := by rw [hu₁w₁, hfix₁ u₁ hu₁ w₂ hw₂]
      _ = w₁ * w₂ * z := by rw [mul_assoc, ← hc2z w₂ hw₂, ← mul_assoc]
  have hx1 : r₁ * r₂ * z * (r₁ * r₂)⁻¹ = z := by
    calc r₁ * r₂ * z * (r₁ * r₂)⁻¹ = r₁ * (r₂ * z * r₂⁻¹) * r₁⁻¹ := by group
      _ = r₁ * z * r₁⁻¹ := by rw [hcj₂ r₂ hr₂]
      _ = z := hcj₁ r₁ hr₁
  have hconj : ∀ k₁ ∈ K₁, ∀ k₂ ∈ K₂,
      r₁ * r₂ * (k₁ * k₂) * (r₁ * r₂)⁻¹ = (r₁ * k₁ * r₁⁻¹) * (r₂ * k₂ * r₂⁻¹) := by
    intro k₁ hk₁ k₂ hk₂
    have e1 : r₂ * k₁ * r₂⁻¹ = k₁ := hfix₂ r₂ hr₂ k₁ hk₁
    have e2 : r₁ * (r₂ * k₂ * r₂⁻¹) * r₁⁻¹ = r₂ * k₂ * r₂⁻¹ :=
      hfix₁ r₁ hr₁ _ (K₂.mul_mem (K₂.mul_mem hr₂ hk₂) (K₂.inv_mem hr₂))
    calc r₁ * r₂ * (k₁ * k₂) * (r₁ * r₂)⁻¹
        = r₁ * ((r₂ * k₁ * r₂⁻¹) * (r₂ * k₂ * r₂⁻¹)) * r₁⁻¹ := by group
      _ = r₁ * (k₁ * (r₂ * k₂ * r₂⁻¹)) * r₁⁻¹ := by rw [e1]
      _ = (r₁ * k₁ * r₁⁻¹) * (r₁ * (r₂ * k₂ * r₂⁻¹) * r₁⁻¹) := by group
      _ = (r₁ * k₁ * r₁⁻¹) * (r₂ * k₂ * r₂⁻¹) := by rw [e2]
  have hzmul : ∀ y ∈ K₂, z * y = y * z := fun y hy => (hc2z y hy).symm
  have hx2 : r₁ * r₂ * (u₁ * u₂) * (r₁ * r₂)⁻¹ = w₁ * w₂ ∨
      r₁ * r₂ * (u₁ * u₂) * (r₁ * r₂)⁻¹ = w₁ * w₂ * z := by
    rw [hconj u₁ hu₁ u₂ hu₂]
    rcases hr₁u with h1 | h1 <;> rcases hr₂u with h2 | h2 <;> rw [h1, h2]
    · exact Or.inl rfl
    · exact Or.inr (mul_assoc _ _ _).symm
    · refine Or.inr ?_
      rw [mul_assoc, ← hc2z w₂ hw₂, ← mul_assoc]
    · refine Or.inl ?_
      calc w₁ * z * (w₂ * z) = w₁ * (z * w₂) * z := by simp only [mul_assoc]
        _ = w₁ * (w₂ * z) * z := by rw [hzmul w₂ hw₂]
        _ = w₁ * w₂ * (z * z) := by simp only [mul_assoc]
        _ = w₁ * w₂ := by rw [hzz, mul_one]
  have hm : u₁ * w₁ * (u₂ * w₂) = u₁ * u₂ * (w₁ * w₂) := by
    calc u₁ * w₁ * (u₂ * w₂) = u₁ * (w₁ * u₂) * w₂ := by simp only [mul_assoc]
      _ = u₁ * (u₂ * w₁) * w₂ := by rw [hcomm w₁ hw₁ u₂ hu₂]
      _ = u₁ * u₂ * (w₁ * w₂) := by simp only [mul_assoc]
  have hx3 : r₁ * r₂ * (w₁ * w₂) * (r₁ * r₂)⁻¹ = u₁ * u₂ * (w₁ * w₂) ∨
      r₁ * r₂ * (w₁ * w₂) * (r₁ * r₂)⁻¹ = u₁ * u₂ * (w₁ * w₂) * z := by
    rw [hconj w₁ hw₁ w₂ hw₂]
    rcases hr₁w with h1 | h1 <;> rcases hr₂w with h2 | h2 <;> rw [h1, h2]
    · exact Or.inl hm
    · refine Or.inr ?_
      rw [← mul_assoc, hm]
    · refine Or.inr ?_
      calc u₁ * w₁ * z * (u₂ * w₂) = u₁ * w₁ * (z * (u₂ * w₂)) := by simp only [mul_assoc]
        _ = u₁ * w₁ * ((u₂ * w₂) * z) := by rw [hzmul _ (K₂.mul_mem hu₂ hw₂)]
        _ = u₁ * w₁ * (u₂ * w₂) * z := by simp only [mul_assoc]
        _ = u₁ * u₂ * (w₁ * w₂) * z := by rw [hm]
    · refine Or.inl ?_
      calc u₁ * w₁ * z * (u₂ * w₂ * z) = u₁ * w₁ * (z * (u₂ * w₂)) * z := by simp only [mul_assoc]
        _ = u₁ * w₁ * ((u₂ * w₂) * z) * z := by rw [hzmul _ (K₂.mul_mem hu₂ hw₂)]
        _ = u₁ * w₁ * (u₂ * w₂) * (z * z) := by simp only [mul_assoc]
        _ = u₁ * u₂ * (w₁ * w₂) := by rw [hzz, mul_one, hm]
  exact seven_dvd_card_of_cube (a := a) (c := w₁) (d := u₁) (x := r₁ * r₂) hcube hz1 hu1 huz
    hw1 hwz hwu hwuz ha1 ha2 ha₄ (hcj₁ w₁ hw₁) hw₁u hc3 (hcj₁ u₁ hu₁) hd2 hd3 hx1 hx2 hx3

end CFSG.GH74.GLS.Stage4.Q9

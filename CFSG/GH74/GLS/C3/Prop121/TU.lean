module

public import CFSG.GH74.GLS.C3.Prop121.Defs
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BenderGroupFactsAlternating
public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationTwelveOut

public section

namespace CFSG.GH74.GLS.C3.Prop121

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

namespace TU

variable {G : Type} [Group G]

lemma exists_y {Q : Subgroup G} (hcard : Nat.card Q = 4) {x : G} :
    ∃ y ∈ Q, y ≠ 1 ∧ y ≠ x := by
  by_contra h
  have h' : ∀ y ∈ Q, y ≠ 1 → y = x := fun y hy hy1 =>
    by_contra fun hyx => h ⟨y, hy, hy1, hyx⟩
  have hsub : (Q : Set G) ⊆ {1, x} := by
    intro q hq
    by_cases h1 : q = 1
    · simp [h1]
    · simp [h' q hq h1]
  have h2 : (Q : Set G).ncard ≤ ({1, x} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h3 : ({1, x} : Set G).ncard ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)
  have h4 : (Q : Set G).ncard = 4 := by
    rw [← hcard]
    exact (Nat.card_coe_set_eq (Q : Set G)).symm
  omega

lemma Q_four {Q : Subgroup G} (hcard : Nat.card Q = 4) (hQsq : ∀ q ∈ Q, q ^ 2 = 1) {x y : G}
    (hx : x ∈ Q) (hy : y ∈ Q) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hyx : y ≠ x) :
    ∀ q ∈ Q, q = 1 ∨ q = x ∨ q = y ∨ q = x * y := by
  intro q hq
  by_contra hne
  have hq1 : q ≠ 1 := fun h => hne (Or.inl h)
  have hqx : q ≠ x := fun h => hne (Or.inr (Or.inl h))
  have hqy : q ≠ y := fun h => hne (Or.inr (Or.inr (Or.inl h)))
  have hqxy : q ≠ x * y := fun h => hne (Or.inr (Or.inr (Or.inr h)))
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by simpa [sq] using hQsq x hx)
  have hxy1 : x * y ≠ 1 := by
    intro h
    apply hyx
    have := eq_inv_of_mul_eq_one_right h
    rw [this, hx']
  have hxyx : x ≠ x * y := by
    intro h
    apply hy1
    have : x * y = x * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel this
  have hxyy : y ≠ x * y := by
    intro h
    apply hx1
    have : 1 * y = x * y := by rw [one_mul]; exact h
    exact (mul_right_cancel this).symm
  have hsub : ({1, x, y, x * y, q} : Set G) ⊆ (Q : Set G) := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact Q.one_mem
    · exact hx
    · exact hy
    · exact Q.mul_mem hx hy
    · exact hq
  have h5 : ({1, x, y, x * y, q} : Set G).ncard = 5 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
      Set.ncard_pair]
    all_goals simp [Ne.symm hx1, Ne.symm hy1, Ne.symm hxy1, Ne.symm hq1, hyx.symm, hxyx, hxyy,
      Ne.symm hqx, Ne.symm hqy, Ne.symm hqxy]
  have h6 : (Q : Set G).ncard = 4 := by
    rw [← hcard]
    exact (Nat.card_coe_set_eq (Q : Set G)).symm
  have hfinQ : Finite Q := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hfin : (Q : Set G).Finite := Set.toFinite _
  have h7 := Set.ncard_le_ncard hsub hfin
  omega

section Relations

variable {x y z t u : G}

lemma klein_rels (hxx : x * x = 1) (hyy : y * y = 1) (hxy : x * y = z) (hyx : y * x = z) :
    z * z = 1 ∧ x * z = y ∧ z * x = y ∧ y * z = x ∧ z * y = x := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc z * z = (x * y) * (y * x) := by rw [hxy, hyx]
      _ = x * (y * y) * x := by simp only [mul_assoc]
      _ = 1 := by rw [hyy, mul_one, hxx]
  · calc x * z = x * (x * y) := by rw [hxy]
      _ = (x * x) * y := by simp only [mul_assoc]
      _ = y := by rw [hxx, one_mul]
  · calc z * x = (y * x) * x := by rw [hyx]
      _ = y * (x * x) := by simp only [mul_assoc]
      _ = y := by rw [hxx, mul_one]
  · calc y * z = y * (y * x) := by rw [hyx]
      _ = (y * y) * x := by simp only [mul_assoc]
      _ = x := by rw [hyy, one_mul]
  · calc z * y = (x * y) * y := by rw [hxy]
      _ = x * (y * y) := by simp only [mul_assoc]
      _ = x := by rw [hyy, mul_one]

lemma norm_of_rel {Q : Subgroup G} (hyQ : y ∈ Q) (hzQ : z ∈ Q)
    (hQall : ∀ q ∈ Q, q = 1 ∨ q = x ∨ q = y ∨ q = x * y)
    (htx : t * x = y * t) (hty : t * y = z * t) :
    ∀ r ∈ Q, t * r * t⁻¹ ∈ Q := by
  intro r hr
  have h1 : t * x * t⁻¹ = y := by rw [htx, mul_inv_cancel_right]
  have h2 : t * y * t⁻¹ = z := by rw [hty, mul_inv_cancel_right]
  rcases hQall r hr with h | h | h | h
  · rw [h]; simp
  · rw [h, h1]; exact hyQ
  · rw [h, h2]; exact hzQ
  · rw [h]
    have : t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by group
    rw [this, h1, h2]
    exact Q.mul_mem hyQ hzQ

lemma cube_of_rel (htx : t * x = y * t) (hty : t * y = z * t) (htz : t * z = x * t)
    (ht3 : t * t * t = 1) (hyz : y * z = x) (hxx : x * x = 1) :
    (t * x) * (t * x) * (t * x) = 1 := by
  calc t * x * (t * x) * (t * x) = y * t * (y * t) * (y * t) := by rw [htx]
    _ = y * (t * y) * t * (y * t) := by group
    _ = y * (z * t) * t * (y * t) := by rw [hty]
    _ = y * z * t * (t * y) * t := by group
    _ = y * z * t * (z * t) * t := by rw [hty]
    _ = y * z * (t * z) * t * t := by group
    _ = y * z * (x * t) * t * t := by rw [htz]
    _ = y * z * x * (t * t * t) := by group
    _ = 1 := by rw [ht3, hyz, hxx, mul_one]

lemma rel_pt {p : G} (hp : p = 1 ∨ p = x) (hzz : z * z = 1) (hxy : x * y = z)
    (hyx : y * x = z) (hxz : x * z = y) (hzx : z * x = y)
    (ht3 : t * t * t = 1) (htx : t * x = y * t) (hty : t * y = z * t) (htz : t * z = x * t) :
    (p * t) * (p * t) * (p * t) = 1 ∧ (p * t) * x = y * (p * t) ∧ (p * t) * y = z * (p * t) ∧
      (p * t) * z = x * (p * t) := by
  rcases hp with h | h
  · rw [h]; simpa using ⟨ht3, htx, hty, htz⟩
  · rw [h]
    refine ⟨?_, ?_, ?_, ?_⟩
    · calc x * t * (x * t) * (x * t) = x * (t * x) * (t * x) * t := by simp only [mul_assoc]
        _ = x * (y * t) * (y * t) * t := by rw [htx]
        _ = x * y * (t * y) * t * t := by simp only [mul_assoc]
        _ = x * y * (z * t) * t * t := by rw [hty]
        _ = x * y * z * (t * t * t) := by simp only [mul_assoc]
        _ = 1 := by rw [ht3, hxy, hzz, mul_one]
    · calc x * t * x = x * (t * x) := by simp only [mul_assoc]
        _ = x * (y * t) := by rw [htx]
        _ = (x * y) * t := by simp only [mul_assoc]
        _ = (y * x) * t := by rw [hxy, hyx]
        _ = y * (x * t) := by simp only [mul_assoc]
    · calc x * t * y = x * (t * y) := by simp only [mul_assoc]
        _ = x * (z * t) := by rw [hty]
        _ = (x * z) * t := by simp only [mul_assoc]
        _ = (z * x) * t := by rw [hxz, hzx]
        _ = z * (x * t) := by simp only [mul_assoc]
    · calc x * t * z = x * (t * z) := by simp only [mul_assoc]
        _ = x * (x * t) := by rw [htz]

lemma w_comm_x (htx : t * x = y * t) (huy : u * y = z * u) (htz : t * z = x * t)
    (hux : u * x = x * u) :
    u * t * u * t * x = x * (u * t * u * t) := by
  calc u * t * u * t * x = u * t * u * (t * x) := by group
    _ = u * t * (u * y) * t := by rw [htx]; group
    _ = u * (t * z) * u * t := by rw [huy]; group
    _ = (u * x) * t * u * t := by rw [htz]; group
    _ = x * (u * t * u * t) := by rw [hux]; group

lemma w_comm_y (hty : t * y = z * t) (huz : u * z = y * u) :
    u * t * u * t * y = y * (u * t * u * t) := by
  calc u * t * u * t * y = u * t * u * (t * y) := by group
    _ = u * t * (u * z) * t := by rw [hty]; group
    _ = u * (t * y) * u * t := by rw [huz]; group
    _ = (u * z) * t * u * t := by rw [hty]; group
    _ = y * (u * t * u * t) := by rw [huz]; group

lemma w_comm_Q {Q : Subgroup G} (hQall : ∀ q ∈ Q, q = 1 ∨ q = x ∨ q = y ∨ q = x * y)
    (htx : t * x = y * t) (hty : t * y = z * t) (htz : t * z = x * t)
    (hux : u * x = x * u) (huy : u * y = z * u) (huz : u * z = y * u) :
    ∀ q ∈ Q, u * t * u * t * q = q * (u * t * u * t) := by
  have hx := w_comm_x htx huy htz hux
  have hy := w_comm_y hty huz
  intro q hq
  rcases hQall q hq with h | h | h | h
  · rw [h]; simp
  · rw [h]; exact hx
  · rw [h]; exact hy
  · rw [h]
    calc u * t * u * t * (x * y) = (u * t * u * t * x) * y := by simp only [mul_assoc]
      _ = x * (u * t * u * t * y) := by rw [hx]; simp only [mul_assoc]
      _ = x * (y * (u * t * u * t)) := by rw [hy]
      _ = x * y * (u * t * u * t) := by simp only [mul_assoc]

lemma w_comm_k {k : G} (huu : u * u = 1) (htk : t * k = k * t)
    (htk' : t * (u * k * u) = (u * k * u) * t) :
    u * t * u * t * k = k * (u * t * u * t) := by
  have e1 : u * t * (u * k * u) * (u * t) = u * t * u * (k * t) := by
    calc u * t * (u * k * u) * (u * t) = u * t * u * k * (u * u) * t := by simp only [mul_assoc]
      _ = u * t * u * k * t := by rw [huu, mul_one]
      _ = u * t * u * (k * t) := by simp only [mul_assoc]
  have e2 : u * (u * k * u) = k * u := by
    calc u * (u * k * u) = (u * u) * k * u := by simp only [mul_assoc]
      _ = k * u := by rw [huu, one_mul]
  calc u * t * u * t * k = u * t * u * (t * k) := by simp only [mul_assoc]
    _ = u * t * u * (k * t) := by rw [htk]
    _ = u * t * (u * k * u) * (u * t) := e1.symm
    _ = u * (t * (u * k * u)) * (u * t) := by simp only [mul_assoc]
    _ = u * ((u * k * u) * t) * (u * t) := by rw [htk']
    _ = (u * (u * k * u)) * (t * (u * t)) := by simp only [mul_assoc]
    _ = k * u * (t * (u * t)) := by rw [e2]
    _ = k * (u * t * u * t) := by simp only [mul_assoc]

lemma cons_w (hyx' : y ≠ x) (hxy : x * y = z) (htx : t * x = y * t) (htz : t * z = x * t)
    (hux : u * x = x * u) (huz : u * z = y * u) (huu : u * u = 1)
    (hw : u * t * u * t = 1 ∨ u * t * u * t = x ∨ u * t * u * t = y ∨ u * t * u * t = x * y) :
    u * t * u * t = 1 ∨ u * t * u * t = y := by
  have key : t * (u * t * u * t) = (u * (u * t * u * t) * u) * t := by
    calc t * (u * t * u * t) = t * u * t * u * t := by group
      _ = (u * u) * t * u * t * u * t := by rw [huu, one_mul]
      _ = (u * (u * t * u * t) * u) * t := by group
  rcases hw with h | h | h | h
  · exact Or.inl h
  · exfalso
    rw [h] at key
    have h1 : u * x * u = x := by
      calc u * x * u = x * u * u := by rw [hux]
        _ = x := by rw [mul_assoc, huu, mul_one]
    rw [h1, htx] at key
    exact hyx' (mul_right_cancel key)
  · exact Or.inr h
  · exfalso
    rw [hxy] at h
    rw [h] at key
    have h1 : u * z * u = y := by
      calc u * z * u = y * u * u := by rw [huz]
        _ = y := by rw [mul_assoc, huu, mul_one]
    rw [h1, htz] at key
    exact hyx' (mul_right_cancel key).symm

lemma exists_p (hxy : x * y = z) (htz : t * z = x * t) (hxx : x * x = 1) (hux : u * x = x * u)
    (huu : u * u = 1)
    (hw : u * t * u * t = 1 ∨ u * t * u * t = y) :
    ∃ p : G, (p = 1 ∨ p = x) ∧ u * (p * t) * u⁻¹ = (p * t)⁻¹ := by
  have hu : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  rcases hw with h | h
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [one_mul, hu]
    exact eq_inv_of_mul_eq_one_left h
  · refine ⟨x, Or.inr rfl, ?_⟩
    rw [hu]
    have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
    have h1 : u * t * u = y * t⁻¹ := eq_mul_inv_of_mul_eq h
    have h2 : z * t⁻¹ = t⁻¹ * x := by
      calc z * t⁻¹ = t⁻¹ * (t * z) * t⁻¹ := by group
        _ = t⁻¹ * (x * t) * t⁻¹ := by rw [htz]
        _ = t⁻¹ * x := by group
    calc u * (x * t) * u = x * (u * t * u) := by
          calc u * (x * t) * u = (u * x) * t * u := by group
            _ = (x * u) * t * u := by rw [hux]
            _ = x * (u * t * u) := by group
      _ = x * (y * t⁻¹) := by rw [h1]
      _ = z * t⁻¹ := by rw [← mul_assoc, hxy]
      _ = t⁻¹ * x := h2
      _ = (x * t)⁻¹ := by rw [mul_inv_rev, hx']

lemma u_swaps {Q : Subgroup G} (hQall : ∀ q ∈ Q, q = 1 ∨ q = x ∨ q = y ∨ q = x * y)
    (hyQ : y ∈ Q) (hy1 : y ≠ 1) (hyx : y ≠ x)
    (hux : u * x = x * u) (huN : ∀ r ∈ Q, u * r * u⁻¹ ∈ Q)
    (huQ : ∃ q ∈ Q, u * q ≠ q * u) : u * y = x * y * u := by
  rcases hQall _ (huN y hyQ) with h | h | h | h
  · exfalso
    apply hy1
    have h' : u * y = u := by simpa using h
    simpa using h'
  · exfalso
    apply hyx
    have h' : u * y = x * u := by rwa [mul_inv_eq_iff_eq_mul] at h
    rw [← hux] at h'
    exact mul_left_cancel h'
  · exfalso
    have h' : u * y = y * u := by rwa [mul_inv_eq_iff_eq_mul] at h
    obtain ⟨q, hq, hne⟩ := huQ
    apply hne
    rcases hQall q hq with h1 | h1 | h1 | h1
    · rw [h1]; simp
    · rw [h1]; exact hux
    · rw [h1]; exact h'
    · rw [h1]
      calc u * (x * y) = (u * x) * y := by simp only [mul_assoc]
        _ = x * (u * y) := by rw [hux]; simp only [mul_assoc]
        _ = x * (y * u) := by rw [h']
        _ = x * y * u := by simp only [mul_assoc]
  · rwa [mul_inv_eq_iff_eq_mul] at h

lemma exists_m {Q : Subgroup G}
    (hQall : ∀ q ∈ Q, q = 1 ∨ q = x ∨ q = y ∨ q = x * y)
    (hy1 : y ≠ 1) (hyx : y ≠ x) (hxy : x * y = z) (hyx' : y * x = z) (hyz : y * z = x)
    (hux : u * x = x * u) (huy : u * y = z * u) (huz : u * z = y * u)
    (huN : ∀ r ∈ Q, u * r * u⁻¹ ∈ Q) (hyQ : y ∈ Q)
    {m₀ : G} (hm₀Q : ∀ r ∈ Q, m₀ * r * m₀⁻¹ ∈ Q) (hm₀x : m₀ * x * m₀⁻¹ = y) :
    ∃ m : G, (∀ r ∈ Q, m * r * m⁻¹ ∈ Q) ∧ m * x = y * m ∧ m * y = z * m ∧ m * z = x * m := by
  have hm₀x' : m₀ * x = y * m₀ := by rwa [mul_inv_eq_iff_eq_mul] at hm₀x
  have hb : m₀ * y * m₀⁻¹ ∈ Q := hm₀Q y hyQ
  rcases hQall _ hb with h | h | h | h
  · exfalso
    apply hy1
    have h' : m₀ * y = m₀ := by simpa using h
    simpa using h'
  · have h' : m₀ * y = x * m₀ := by rwa [mul_inv_eq_iff_eq_mul] at h
    have hz : m₀ * z = z * m₀ := by
      calc m₀ * z = m₀ * (y * x) := by rw [hyx']
        _ = (m₀ * y) * x := by simp only [mul_assoc]
        _ = x * (m₀ * x) := by rw [h']; simp only [mul_assoc]
        _ = x * (y * m₀) := by rw [hm₀x']
        _ = z * m₀ := by rw [← mul_assoc, hxy]
    refine ⟨m₀ * u, ?_, ?_, ?_, ?_⟩
    · intro r hr
      have : m₀ * u * r * (m₀ * u)⁻¹ = m₀ * (u * r * u⁻¹) * m₀⁻¹ := by group
      rw [this]
      exact hm₀Q _ (huN r hr)
    · calc m₀ * u * x = m₀ * (u * x) := by simp only [mul_assoc]
        _ = m₀ * (x * u) := by rw [hux]
        _ = (m₀ * x) * u := by simp only [mul_assoc]
        _ = y * (m₀ * u) := by rw [hm₀x']; simp only [mul_assoc]
    · calc m₀ * u * y = m₀ * (u * y) := by simp only [mul_assoc]
        _ = m₀ * (z * u) := by rw [huy]
        _ = (m₀ * z) * u := by simp only [mul_assoc]
        _ = z * (m₀ * u) := by rw [hz]; simp only [mul_assoc]
    · calc m₀ * u * z = m₀ * (u * z) := by simp only [mul_assoc]
        _ = m₀ * (y * u) := by rw [huz]
        _ = (m₀ * y) * u := by simp only [mul_assoc]
        _ = x * (m₀ * u) := by rw [h']; simp only [mul_assoc]
  · exfalso
    have h' : m₀ * y = y * m₀ := by rwa [mul_inv_eq_iff_eq_mul] at h
    exact hyx (mul_left_cancel (hm₀x'.trans h'.symm)).symm
  · have h' : m₀ * y = z * m₀ := by rw [← hxy]; rwa [mul_inv_eq_iff_eq_mul] at h
    refine ⟨m₀, hm₀Q, hm₀x', h', ?_⟩
    calc m₀ * z = m₀ * (x * y) := by rw [hxy]
      _ = (m₀ * x) * y := by simp only [mul_assoc]
      _ = y * (m₀ * y) := by rw [hm₀x']; simp only [mul_assoc]
      _ = y * (z * m₀) := by rw [h']
      _ = (y * z) * m₀ := by simp only [mul_assoc]
      _ = x * m₀ := by rw [hyz]

end Relations

lemma center_K_trivial {n : ℕ} (hn : 5 ≤ n) {K : Subgroup G}
    (e : K ≃* alternatingGroup (Fin n)) {k : G} (hk : k ∈ K)
    (hc : ∀ k' ∈ K, k * k' = k' * k) : k = 1 := by
  have hcenter : Subgroup.center (alternatingGroup (Fin n)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simpa using (by omega : 4 ≤ n))
  have hmem : e ⟨k, hk⟩ ∈ Subgroup.center (alternatingGroup (Fin n)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc k' k'.2).symm
  rw [hcenter, Subgroup.mem_bot] at hmem
  have := e.injective (hmem.trans (map_one e).symm)
  simpa using congrArg Subtype.val this

lemma mem_Q_of_comm {K Q : Subgroup G}
    (hCQ : ∀ c : G, (∀ q ∈ Q, c * q = q * c) → ∃ k ∈ K, ∃ q ∈ Q, c = k * q)
    (hKQ : ∀ k ∈ K, ∀ q ∈ Q, k * q = q * k)
    (hZ : ∀ k ∈ K, (∀ k' ∈ K, k * k' = k' * k) → k = 1)
    {c : G} (hcQ : ∀ q ∈ Q, c * q = q * c) (hcK : ∀ k ∈ K, c * k = k * c) : c ∈ Q := by
  obtain ⟨k, hk, q, hq, rfl⟩ := hCQ c hcQ
  have : k = 1 := by
    refine hZ k hk fun k' hk' => ?_
    have h1 := hcK k' hk'
    have h2 : k * q * k' = k * k' * q := by rw [mul_assoc, ← hKQ k' hk' q hq, ← mul_assoc]
    have h3 : k' * (k * q) = k' * k * q := by rw [mul_assoc]
    rw [h2, h3] at h1
    exact mul_right_cancel h1
  rw [this, one_mul]
  exact hq

lemma exists_inner_of_cube {K : Subgroup G}
    (hout : ∀ γ : MulAut K, γ ^ 3 ∈ (MulAut.conj : K →* MulAut K).range →
      γ ∈ (MulAut.conj : K →* MulAut K).range)
    {m : G} (hm : m ∈ Subgroup.normalizer (K : Set G))
    (h3 : ∃ k ∈ K, ∀ z ∈ K, m ^ 3 * z * (m ^ 3)⁻¹ = k * z * k⁻¹) :
    ∃ k ∈ K, ∀ z ∈ K, m * z * m⁻¹ = k * z * k⁻¹ := by
  obtain ⟨k, hk, hkz⟩ := h3
  have hγ3 : K.normalizerMonoidHom ⟨m, hm⟩ ^ 3 ∈ (MulAut.conj : K →* MulAut K).range := by
    refine ⟨⟨k, hk⟩, ?_⟩
    ext z
    rw [← map_pow]
    simp [Subgroup.normalizerMonoidHom_apply_apply_coe, hkz z z.2]
  obtain ⟨⟨k₂, hk₂⟩, hk₂γ⟩ := hout _ hγ3
  refine ⟨k₂, hk₂, fun z hz => ?_⟩
  have := congrArg (fun φ : MulAut K => ((φ ⟨z, hz⟩ : K) : G)) hk₂γ
  simpa [Subgroup.normalizerMonoidHom_apply_apply_coe] using this.symm

lemma cube_comm {Q : Subgroup G} {x y z m : G}
    (hQall : ∀ q ∈ Q, q = 1 ∨ q = x ∨ q = y ∨ q = x * y)
    (hmx : m * x = y * m) (hmy : m * y = z * m) (hmz : m * z = x * m) :
    ∀ q ∈ Q, m ^ 3 * q = q * m ^ 3 := by
  have hx3 : m ^ 3 * x = x * m ^ 3 := by
    rw [pow_three]
    calc m * (m * m) * x = m * (m * (m * x)) := by simp only [mul_assoc]
      _ = m * (m * (y * m)) := by rw [hmx]
      _ = m * ((m * y) * m) := by simp only [mul_assoc]
      _ = m * ((z * m) * m) := by rw [hmy]
      _ = (m * z) * (m * m) := by simp only [mul_assoc]
      _ = (x * m) * (m * m) := by rw [hmz]
      _ = x * (m * (m * m)) := by simp only [mul_assoc]
  have hy3 : m ^ 3 * y = y * m ^ 3 := by
    rw [pow_three]
    calc m * (m * m) * y = m * (m * (m * y)) := by simp only [mul_assoc]
      _ = m * (m * (z * m)) := by rw [hmy]
      _ = m * ((m * z) * m) := by simp only [mul_assoc]
      _ = m * ((x * m) * m) := by rw [hmz]
      _ = (m * x) * (m * m) := by simp only [mul_assoc]
      _ = (y * m) * (m * m) := by rw [hmx]
      _ = y * (m * (m * m)) := by simp only [mul_assoc]
  intro q hq
  rcases hQall q hq with h | h | h | h
  · rw [h]; simp
  · rw [h]; exact hx3
  · rw [h]; exact hy3
  · rw [h]
    calc m ^ 3 * (x * y) = (m ^ 3 * x) * y := by simp only [mul_assoc]
      _ = x * (m ^ 3 * y) := by rw [hx3]; simp only [mul_assoc]
      _ = x * (y * m ^ 3) := by rw [hy3]
      _ = x * y * m ^ 3 := by simp only [mul_assoc]

lemma exists_t0 {K Q : Subgroup G} {x y z m : G}
    (hout : ∀ γ : MulAut K, γ ^ 3 ∈ (MulAut.conj : K →* MulAut K).range →
      γ ∈ (MulAut.conj : K →* MulAut K).range)
    (hQsq : ∀ q ∈ Q, q ^ 2 = 1)
    (hKQ : ∀ k ∈ K, ∀ q ∈ Q, k * q = q * k)
    (hCQ : ∀ c : G, (∀ q ∈ Q, c * q = q * c) → ∃ k ∈ K, ∃ q ∈ Q, c = k * q)
    (hZ : ∀ k ∈ K, (∀ k' ∈ K, k * k' = k' * k) → k = 1)
    (hxQ : x ∈ Q) (hyQ : y ∈ Q) (hzQ : z ∈ Q)
    (hQall : ∀ q ∈ Q, q = 1 ∨ q = x ∨ q = y ∨ q = x * y)
    (hm : m ∈ Subgroup.normalizer (K : Set G))
    (hmx : m * x = y * m) (hmy : m * y = z * m) (hmz : m * z = x * m) :
    ∃ t₀ : G, t₀ * t₀ * t₀ = 1 ∧ t₀ * x = y * t₀ ∧ t₀ * y = z * t₀ ∧ t₀ * z = x * t₀ ∧
      ∀ k ∈ K, t₀ * k = k * t₀ := by
  obtain ⟨k₁, hk₁, q₁, hq₁, hm3eq⟩ := hCQ (m ^ 3) (cube_comm hQall hmx hmy hmz)
  have hcube : ∃ k ∈ K, ∀ w ∈ K, m ^ 3 * w * (m ^ 3)⁻¹ = k * w * k⁻¹ := by
    refine ⟨k₁, hk₁, fun w hw => ?_⟩
    rw [hm3eq]
    have hq : q₁ * w = w * q₁ := (hKQ w hw q₁ hq₁).symm
    calc k₁ * q₁ * w * (k₁ * q₁)⁻¹ = k₁ * (q₁ * w) * q₁⁻¹ * k₁⁻¹ := by group
      _ = k₁ * (w * q₁) * q₁⁻¹ * k₁⁻¹ := by rw [hq]
      _ = k₁ * w * k₁⁻¹ := by group
  obtain ⟨k₂, hk₂, hconj⟩ := exists_inner_of_cube hout hm hcube
  obtain ⟨m', hm'⟩ : ∃ m' : G, m' = k₂⁻¹ * m := ⟨_, rfl⟩
  have hk₂inv : k₂⁻¹ ∈ K := K.inv_mem hk₂
  have hm'K : ∀ w ∈ K, m' * w = w * m' := by
    intro w hw
    have h1 := hconj w hw
    calc m' * w = k₂⁻¹ * (m * w * m⁻¹) * m := by rw [hm']; group
      _ = k₂⁻¹ * (k₂ * w * k₂⁻¹) * m := by rw [h1]
      _ = w * m' := by rw [hm']; group
  have hrel : ∀ r r' : G, r' ∈ Q → m * r = r' * m → m' * r = r' * m' := by
    intro r r' hr' h
    have hc : k₂⁻¹ * r' = r' * k₂⁻¹ := hKQ _ hk₂inv r' hr'
    calc m' * r = k₂⁻¹ * (m * r) := by rw [hm']; group
      _ = k₂⁻¹ * (r' * m) := by rw [h]
      _ = (k₂⁻¹ * r') * m := by group
      _ = (r' * k₂⁻¹) * m := by rw [hc]
      _ = r' * m' := by rw [hm']; group
  have hm'x : m' * x = y * m' := hrel x y hyQ hmx
  have hm'y : m' * y = z * m' := hrel y z hzQ hmy
  have hm'z : m' * z = x * m' := hrel z x hxQ hmz
  have hc3 : m' ^ 3 ∈ Q :=
    mem_Q_of_comm hCQ hKQ hZ (cube_comm hQall hm'x hm'y hm'z)
      (fun k hk => (Commute.pow_left (hm'K k hk) 3 : Commute (m' ^ 3) k))
  have hc2 : m' ^ 3 * m' ^ 3 = 1 := by rw [← sq]; exact hQsq _ hc3
  have hcx := cube_comm hQall hm'x hm'y hm'z
  refine ⟨m' ^ 4, ?_, ?_, ?_, ?_, ?_⟩
  · calc m' ^ 4 * m' ^ 4 * m' ^ 4 = (m' ^ 3 * m' ^ 3) ^ 2 := by group
      _ = 1 := by rw [hc2]; simp
  · calc m' ^ 4 * x = m' * (m' ^ 3 * x) := by group
      _ = m' * (x * m' ^ 3) := by rw [hcx x hxQ]
      _ = (m' * x) * m' ^ 3 := by group
      _ = y * m' ^ 4 := by rw [hm'x]; group
  · calc m' ^ 4 * y = m' * (m' ^ 3 * y) := by group
      _ = m' * (y * m' ^ 3) := by rw [hcx y hyQ]
      _ = (m' * y) * m' ^ 3 := by group
      _ = z * m' ^ 4 := by rw [hm'y]; group
  · calc m' ^ 4 * z = m' * (m' ^ 3 * z) := by group
      _ = m' * (z * m' ^ 3) := by rw [hcx z hzQ]
      _ = (m' * z) * m' ^ 3 := by group
      _ = x * m' ^ 4 := by rw [hm'z]; group
  · intro k hk
    exact (Commute.pow_left (hm'K k hk) 4 : Commute (m' ^ 4) k)

end TU

theorem not_three_dvd_card_outer {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7) {K : Type*} [Group K]
    (e : K ≃* alternatingGroup (Fin n)) : ¬ 3 ∣ Nat.card (Outer K) := by
  rcases hn with rfl | rfl | rfl
  · rw [CFSG.ProperTwoGeneratedCore.BenderFacts.card_outer_eq_two_of_mulEquiv_alternatingGroup_five
      e]
    norm_num
  · exact CFSG.Quasithin.A10.three_not_dvd_card_outer e
  · rw [CFSG.ProperTwoGeneratedCore.BenderFacts.card_outer_eq_two_of_mulEquiv_alternatingGroup_seven
      e]
    norm_num

theorem inner_of_cube_inner {K : Type*} [Group K] (hOut : ¬ 3 ∣ Nat.card (Outer K)) :
    ∀ γ : MulAut K, γ ^ 3 ∈ (MulAut.conj : K →* MulAut K).range →
      γ ∈ (MulAut.conj : K →* MulAut K).range := by
  intro γ hγ
  have hb3 : (QuotientGroup.mk γ : Outer K) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 hγ
  have hd : orderOf (QuotientGroup.mk γ : Outer K) ∣ 3 := orderOf_dvd_of_pow_eq_one hb3
  have hd' : orderOf (QuotientGroup.mk γ : Outer K) ∣ Nat.card (Outer K) :=
    orderOf_dvd_natCard _
  rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h3
  · exact (QuotientGroup.eq_one_iff _).1 (orderOf_eq_one_iff.1 h1)
  · exact absurd (h3 ▸ hd') hOut

theorem exists_t_u_aux {G : Type} [Group G] [Finite G] {n : ℕ} {x : G} {K Q : Subgroup G}
    (hout : ∀ γ : MulAut K, γ ^ 3 ∈ (MulAut.conj : K →* MulAut K).range →
      γ ∈ (MulAut.conj : K →* MulAut K).range)
    (hZ : ∀ k ∈ K, (∀ k' ∈ K, k * k' = k' * k) → k = 1)
    (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) (hxQ : x ∈ Q) (hQcard : Nat.card Q = 4)
    (hQsq : ∀ q ∈ Q, q ^ 2 = 1) (hQcomm : ∀ q ∈ Q, ∀ r ∈ Q, q * r = r * q)
    (hKalt : Nonempty (K ≃* alternatingGroup (Fin n)))
    (hKQ : ∀ k ∈ K, ∀ q ∈ Q, k * q = q * k) (hKQ1 : ∀ k ∈ K, k ∈ Q → k = 1)
    (hCQ : ∀ c : G, (∀ q ∈ Q, c * q = q * c) → ∃ k ∈ K, ∃ q ∈ Q, c = k * q)
    (hTR : ∀ q ∈ Q, q ≠ 1 → ∃ m : G, (∀ r ∈ Q, m * r * m⁻¹ ∈ Q) ∧ m * x * m⁻¹ = q)
    {u₀ : G} (hu2 : u₀ ^ 2 = 1) (hux : u₀ * x = x * u₀) (huK : ∀ k ∈ K, u₀ * k * u₀⁻¹ ∈ K)
    (huKQ : ∀ k ∈ K, ∀ q ∈ Q, u₀ ≠ k * q) (huQ : ∃ q ∈ Q, u₀ * q ≠ q * u₀)
    (huN : ∀ r ∈ Q, u₀ * r * u₀⁻¹ ∈ Q)
    (hKN : ∀ m : G, (∀ r ∈ Q, m * r * m⁻¹ ∈ Q) → ∀ k ∈ K, m * k * m⁻¹ ∈ K) :
    ∃ t : G, Stage3Base n x K Q t u₀ := by
  obtain ⟨y, hyQ, hy1, hyx⟩ := TU.exists_y hQcard (x := x)
  have hQall := TU.Q_four hQcard hQsq hxQ hyQ hx1 hy1 hyx
  obtain ⟨z, hxy⟩ : ∃ z, x * y = z := ⟨_, rfl⟩
  have hxx : x * x = 1 := by rw [← sq]; exact hx2
  have hyy : y * y = 1 := by rw [← sq]; exact hQsq y hyQ
  have hyx' : y * x = z := by rw [← hxy]; exact hQcomm y hyQ x hxQ
  obtain ⟨hzz, hxz, hzx, hyz, -⟩ := TU.klein_rels hxx hyy hxy hyx'
  have hzQ : z ∈ Q := hxy ▸ Q.mul_mem hxQ hyQ
  have huu : u₀ * u₀ = 1 := by rw [← sq]; exact hu2
  have huinv : u₀⁻¹ = u₀ := inv_eq_of_mul_eq_one_right huu
  have huy : u₀ * y = z * u₀ := by
    have := TU.u_swaps hQall hyQ hy1 hyx hux huN huQ
    rwa [hxy] at this
  have huz : u₀ * z = y * u₀ := by
    calc u₀ * z = u₀ * (x * y) := by rw [hxy]
      _ = (u₀ * x) * y := by simp only [mul_assoc]
      _ = x * (u₀ * y) := by rw [hux]; simp only [mul_assoc]
      _ = x * (z * u₀) := by rw [huy]
      _ = (x * z) * u₀ := by simp only [mul_assoc]
      _ = y * u₀ := by rw [hxz]
  obtain ⟨m₀, hm₀Q, hm₀x⟩ := hTR y hyQ hy1
  obtain ⟨m, hmQ, hmx, hmy, hmz⟩ :=
    TU.exists_m hQall hy1 hyx hxy hyx' hyz hux huy huz huN hyQ hm₀Q hm₀x
  have hmK : m ∈ Subgroup.normalizer (K : Set G) := Subgroup.mem_normalizer_fintype (hKN m hmQ)
  obtain ⟨t₀, ht3, htx, hty, htz, htK⟩ :=
    TU.exists_t0 hout hQsq hKQ hCQ hZ hxQ hyQ hzQ hQall hmK hmx hmy hmz
  have hwQ : u₀ * t₀ * u₀ * t₀ ∈ Q := by
    refine TU.mem_Q_of_comm hCQ hKQ hZ (TU.w_comm_Q hQall htx hty htz hux huy huz) ?_
    intro k hk
    have hk' : u₀ * k * u₀ ∈ K := by simpa [huinv] using huK k hk
    exact TU.w_comm_k huu (htK k hk) (htK _ hk')
  have hw := TU.cons_w hyx hxy htx htz hux huz huu (hQall _ hwQ)
  obtain ⟨p, hp, hpt⟩ := TU.exists_p hxy htz hxx hux huu hw
  obtain ⟨hp3, hptx, hpty, hptz⟩ := TU.rel_pt hp hzz hxy hyx' hxz hzx ht3 htx hty htz
  have hpK : ∀ k ∈ K, p * k = k * p := by
    intro k hk
    rcases hp with h | h
    · rw [h]; simp
    · rw [h]; exact (hKQ k hk x hxQ).symm
  have hne : p * t₀ ≠ 1 := by
    intro h
    rw [h] at hptx
    simp only [one_mul, mul_one] at hptx
    exact hyx hptx.symm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨p * t₀, ?_⟩
  exact
    { x_sq := hx2
      x_ne := hx1
      x_mem := hxQ
      Q_card := hQcard
      Q_sq := hQsq
      Q_comm := hQcomm
      K_alt := hKalt
      K_comm_Q := hKQ
      K_inf_Q := hKQ1
      t_order := orderOf_eq_prime (by rw [pow_three']; exact hp3) hne
      t_norm_Q := TU.norm_of_rel hyQ hzQ hQall hptx hpty
      t_comm_K := fun k hk => by
        calc p * t₀ * k = p * (t₀ * k) := by simp only [mul_assoc]
          _ = p * (k * t₀) := by rw [htK k hk]
          _ = (p * k) * t₀ := by simp only [mul_assoc]
          _ = (k * p) * t₀ := by rw [hpK k hk]
          _ = k * (p * t₀) := by simp only [mul_assoc]
      tx_cube := by rw [pow_three']; exact TU.cube_of_rel hptx hpty hptz hp3 hyz hxx
      u_sq := hu2
      u_comm_x := hux
      u_inv_t := hpt
      u_norm_K := huK
      u_not_KQ := huKQ
      u_nc_Q := huQ }

theorem exists_t_u {G : Type} [Group G] [Finite G] {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7)
    {x : G} {K Q : Subgroup G}
    (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) (hxQ : x ∈ Q) (hQcard : Nat.card Q = 4)
    (hQsq : ∀ q ∈ Q, q ^ 2 = 1) (hQcomm : ∀ q ∈ Q, ∀ r ∈ Q, q * r = r * q)
    (hKalt : Nonempty (K ≃* alternatingGroup (Fin n)))
    (hKQ : ∀ k ∈ K, ∀ q ∈ Q, k * q = q * k) (hKQ1 : ∀ k ∈ K, k ∈ Q → k = 1)
    (hCQ : ∀ c : G, (∀ q ∈ Q, c * q = q * c) → ∃ k ∈ K, ∃ q ∈ Q, c = k * q)
    (hTR : ∀ q ∈ Q, q ≠ 1 → ∃ m : G, (∀ r ∈ Q, m * r * m⁻¹ ∈ Q) ∧ m * x * m⁻¹ = q)
    {u₀ : G} (hu2 : u₀ ^ 2 = 1) (hux : u₀ * x = x * u₀) (huK : ∀ k ∈ K, u₀ * k * u₀⁻¹ ∈ K)
    (huKQ : ∀ k ∈ K, ∀ q ∈ Q, u₀ ≠ k * q) (huQ : ∃ q ∈ Q, u₀ * q ≠ q * u₀)
    (huN : ∀ r ∈ Q, u₀ * r * u₀⁻¹ ∈ Q)
    (hKN : ∀ m : G, (∀ r ∈ Q, m * r * m⁻¹ ∈ Q) → ∀ k ∈ K, m * k * m⁻¹ ∈ K) :
    ∃ t : G, Stage3Base n x K Q t u₀ := by
  obtain ⟨e⟩ := hKalt
  exact exists_t_u_aux (inner_of_cube_inner (not_three_dvd_card_outer hn e))
    (fun k hk hc => TU.center_K_trivial (by omega) e hk hc) hx2 hx1 hxQ hQcard hQsq hQcomm ⟨e⟩
    hKQ hKQ1 hCQ hTR hu2 hux huK huKQ huQ huN hKN

end CFSG.GH74.GLS.C3.Prop121

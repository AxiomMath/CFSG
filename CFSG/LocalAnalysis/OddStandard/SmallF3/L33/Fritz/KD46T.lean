module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD46H8
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KDBase
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDGeneric

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.KD46
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv SD SDKD

section Generic

variable {G : Type*} [Group G]

theorem closure_four_eq_sup (a b c d : G) :
    closure ({a, b, c, d} : Set G) = closure ({a, c, d} : Set G) ⊔ zpowers b := by
  apply le_antisymm
  · rw [closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact mem_sup_left (subset_closure (by simp))
    · exact mem_sup_right (mem_zpowers _)
    · exact mem_sup_left (subset_closure (by simp))
    · exact mem_sup_left (subset_closure (by simp))
  · refine sup_le ?_ ?_
    · rw [closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl <;> exact subset_closure (by simp)
    · rw [zpowers_le]
      exact subset_closure (by simp)

theorem closure_three_eq (a b c : G) :
    closure ({a, b, c} : Set G) = zpowers a ⊔ zpowers b ⊔ zpowers c := by
  apply le_antisymm
  · rw [closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact mem_sup_left (mem_sup_left (mem_zpowers _))
    · exact mem_sup_left (mem_sup_right (mem_zpowers _))
    · exact mem_sup_right (mem_zpowers _)
  · refine sup_le (sup_le ?_ ?_) ?_ <;> rw [zpowers_le] <;> exact subset_closure (by simp)

theorem mem_closure_three {a b c : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hc : c ^ 2 = 1)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) {g : G}
    (hg : g ∈ closure ({a, b, c} : Set G)) :
    ∃ i j l : ℕ, i < 2 ∧ j < 2 ∧ l < 2 ∧ g = a ^ i * b ^ j * c ^ l := by
  rw [closure_three_eq] at hg
  have mc : ∀ {x y : G}, x * y = y * x → x ∈ centralizer ({y} : Set G) := fun h =>
    mem_centralizer_singleton_iff.mpr h
  obtain ⟨l, hl, hgl⟩ := exists_pow_mem_of_mem_sup hc
    (sup_le (zpowers_le.mpr (mc hac)) (zpowers_le.mpr (mc hbc))) hg
  obtain ⟨j, hj, hgj⟩ := exists_pow_mem_of_mem_sup hb (zpowers_le.mpr (mc hab)) hgl
  have hi : ∃ i : ℕ, i < 2 ∧ g * c ^ l * b ^ j = a ^ i := by
    rcases eq_one_or_eq_of_mem_zpowers ha hgj with h | h
    · exact ⟨0, by norm_num, by rw [h, pow_zero]⟩
    · exact ⟨1, by norm_num, by rw [h, pow_one]⟩
  obtain ⟨i, hi, hgi⟩ := hi
  refine ⟨i, j, l, hi, hj, hl, ?_⟩
  calc g = g * c ^ l * b ^ j * (b ^ j)⁻¹ * (c ^ l)⁻¹ := by group
    _ = a ^ i * b ^ j * c ^ l := by rw [hgi, pow_inv_of_sq hb hj, pow_inv_of_sq hc hl]

end Generic

theorem word_PE : ∀ i : ZMod 8, (i = 0 ∨ i = 2) → ∀ e, pE i (-1) e → ∀ u b, pE i u b →
    ∃ a j l : Fin 2, aff8 u b = z8 ^ (a : ℕ) * aff8 (-1) e ^ (j : ℕ) * k8 ^ (l : ℕ) := by
  decide

theorem word_PB : ∀ u b, pB u b → ∃ a l : Fin 2, aff8 u b = z8 ^ (a : ℕ) * k8 ^ (l : ℕ) := by
  decide

theorem dbit8_two_mul : ∀ c : ZMod 8, dbit8 (2 * c) = 0 := by decide

theorem z8_mem_PB : z8 ∈ PB := mem_PB.mpr (by decide)

theorem k8_mem_PB : k8 ∈ PB := mem_PB.mpr (by decide)

theorem refl_not_mem_PB (e : ZMod 8) : aff8 (-1) e ∉ PB := by
  rw [mem_PB]
  revert e
  decide

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} (S : KDBase A C)

theorem z_def : S.z = S.x ^ 2 := rfl

theorem x_mem_T : S.x ∈ A.T := S.x_mem.1

theorem y_mem_T : S.y ∈ A.T := S.y_mem.1

theorem z_mem : S.z ∈ A.R := pow_mem S.x_mem 2

theorem z_mem_T : S.z ∈ A.T := (z_mem S).1

theorem k_mem_T : S.k ∈ A.T := C.k_mem

theorem d_mem_T : S.d ∈ A.T := C.d_mem

theorem xy_mem : S.x * S.y ∈ A.R := mul_mem S.x_mem S.y_mem

theorem k_sq : S.k ^ 2 = 1 := C.k_sq

theorem ψ_k : ψX A S.k = k8 := SDKD.ψX_k C

theorem ψ_d : ψX A S.d = d8 := SDKD.ψX_d C

omit [Finite X] in
include A in
theorem t_sq' : t ^ 2 = 1 := SD.t_sq (A := A)

omit [Finite X] in
include A in
theorem t_ne_one' : t ≠ 1 := SD.t_ne_one (A := A)

omit [Finite X] in
theorem comm_t {g : X} (hg : g ∈ A.T) : g * t = t * g := A.commute_t hg

theorem x_sq_ne_one : S.x ^ 2 ≠ 1 := by
  intro h
  have := orderOf_dvd_of_pow_eq_one h
  rw [S.orderOf_x] at this
  norm_num at this

theorem ψ_x : ψX A S.x = aff8 1 2 ∨ ψX A S.x = aff8 1 6 := by
  obtain ⟨v, c, hv, hψ⟩ := ψX_mem_R8 S.x_mem
  have h2 : aff8 v (2 * c) ^ 2 ≠ 1 := by
    intro h
    apply x_sq_ne_one S
    apply eq_one_of_ψX (pow_mem S.x_mem 2)
    rw [ψX_pow S.x_mem.1, ← hψ, h]
  rw [← hψ]
  exact inv_R8 v c hv h2

theorem ψ_z : ψX A S.z = z8 := by
  rw [z_def, ψX_pow S.x_mem.1]
  rcases ψ_x S with h | h <;> rw [h] <;> decide

theorem z_ne_one : S.z ≠ 1 := x_sq_ne_one S

theorem z_sq : S.z ^ 2 = 1 :=
  eq_one_of_ψX (pow_mem (z_mem S) 2) (by rw [ψX_pow (z_mem_T S), ψ_z]; decide)

theorem z_inv : S.z⁻¹ = S.z := by rw [inv_eq_iff_mul_eq_one, ← pow_two, z_sq]

theorem conj_mem_R {g r : X} (hg : g ∈ A.T) (hr : r ∈ A.R) : g * r * g⁻¹ ∈ A.R :=
  SD.conj_mem_R_of_mem_T hg hr

theorem z_comm {g : X} (hg : g ∈ A.T) : S.z * g = g * S.z := by
  have h := eq_of_ψX_eq (conj_mem_R hg (z_mem S)) (z_mem S) (by
    rw [ψX_conj hg (z_mem_T S), ψ_z]
    obtain ⟨u, b, hub⟩ := ψX_mem_H8' hg
    rw [← hub, z8_comm_aff8', mul_inv_cancel_right])
  calc S.z * g = g * S.z * g⁻¹ * g := by rw [h]
    _ = g * S.z := by group

theorem k_comm_R {r : X} (hr : r ∈ A.R) : S.k * r = r * S.k := SDKD.commute_k C hr

theorem k_comm_t : S.k * t = t * S.k := comm_t (k_mem_T S)

theorem z_comm_t : S.z * t = t * S.z := comm_t (z_mem_T S)

theorem z_comm_k : S.z * S.k = S.k * S.z := z_comm S (k_mem_T S)

theorem x_pow_four : S.x ^ 4 = 1 := by
  rw [← S.orderOf_x]
  exact pow_orderOf_eq_one _

theorem ψ_y : ∃ e : ZMod 8, dbit8 e = 0 ∧ ψX A S.y = aff8 (-1) e := by
  obtain ⟨v, c, hv, hψ⟩ := ψX_mem_R8 S.y_mem
  have h := congrArg (ψX A) S.y_inv
  rw [ψX_conj (y_mem_T S) (x_mem_T S), ψX_inv (x_mem_T S), ← hψ] at h
  rcases ψ_x S with hx | hx <;> rw [hx] at h
  · have := refl_R8 v c hv 2 (Or.inl rfl) h
    exact ⟨2 * c, dbit8_two_mul c, by rw [← hψ, this]⟩
  · have := refl_R8 v c hv 6 (Or.inr rfl) h
    exact ⟨2 * c, dbit8_two_mul c, by rw [← hψ, this]⟩

theorem xy_sq : (S.x * S.y) ^ 2 = 1 := by
  have h1 : S.y * S.x = S.x⁻¹ * S.y := by
    calc S.y * S.x = S.y * S.x * S.y⁻¹ * S.y := by group
      _ = S.x⁻¹ * S.y := by rw [S.y_inv]
  calc (S.x * S.y) ^ 2 = S.x * (S.y * S.x) * S.y := by rw [pow_two]; group
    _ = S.y ^ 2 := by rw [h1, pow_two]; group
    _ = 1 := S.y_sq

theorem z_comm_y : S.z * S.y = S.y * S.z := z_comm S (y_mem_T S)

theorem mem_B_z : S.z ∈ S.B := subset_closure (by simp)

theorem mem_B_t : t ∈ S.B := subset_closure (by simp)

theorem mem_B_k : S.k ∈ S.B := subset_closure (by simp)

theorem B_eq : S.B = pre A PB := by
  apply le_antisymm
  · rw [KDBase.B, closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact mem_pre.mpr ⟨z_mem_T S, by rw [ψ_z]; exact z8_mem_PB⟩
    · exact t_mem_pre PB
    · exact mem_pre.mpr ⟨k_mem_T S, by rw [ψ_k]; exact k8_mem_PB⟩
  · intro g hg
    obtain ⟨hgT, hgP⟩ := mem_pre.mp hg
    obtain ⟨u, b, hub⟩ := ψX_mem_H8' hgT
    rw [← hub] at hgP
    obtain ⟨a, l, h⟩ := word_PB u b (mem_PB.mp hgP)
    have hw : S.z ^ (a : ℕ) * S.k ^ (l : ℕ) ∈ S.B :=
      mul_mem (pow_mem (mem_B_z S) _) (pow_mem (mem_B_k S) _)
    have hwT : S.z ^ (a : ℕ) * S.k ^ (l : ℕ) ∈ A.T :=
      mul_mem (pow_mem (z_mem_T S) _) (pow_mem (k_mem_T S) _)
    refine mem_of_ψX_eq C (mem_B_t S) hgT hw hwT ?_
    rw [ψX_mul (pow_mem (z_mem_T S) _) (pow_mem (k_mem_T S) _), ψX_pow (z_mem_T S),
      ψX_pow (k_mem_T S), ψ_z, ψ_k, ← hub, h]

theorem B_le_T : S.B ≤ A.T := by rw [B_eq]; exact pre_le_T _

theorem mem_B_iff {g : X} : g ∈ S.B ↔ g ∈ A.T ∧ ψX A g ∈ PB := by rw [B_eq]; exact mem_pre

theorem eq_of_mem_B {g : X} (hg : g ∈ S.B) :
    ∃ a c l : ℕ, a < 2 ∧ c < 2 ∧ l < 2 ∧ g = S.z ^ a * t ^ c * S.k ^ l :=
  mem_closure_three (z_sq S) (t_sq' (A := A)) (k_sq S) (z_comm_t S) (z_comm_k S) (k_comm_t S).symm
    hg

theorem B_comm {a b : X} (ha : a ∈ S.B) (hb : b ∈ S.B) : a * b = b * a := by
  have hc : ({S.z, t, S.k} : Set X).Pairwise Commute := by
    intro u hu v hv _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    all_goals first
      | exact Commute.refl _
      | exact z_comm_t S
      | exact (z_comm_t S).symm
      | exact z_comm_k S
      | exact (z_comm_k S).symm
      | exact k_comm_t S
      | exact (k_comm_t S).symm
  have h : (⟨a, ha⟩ : closure ({S.z, t, S.k} : Set X)) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ :=
    (isMulCommutative_closure hc).is_comm.comm _ _
  exact congrArg Subtype.val h

theorem B_sq {a : X} (ha : a ∈ S.B) : a ^ 2 = 1 := by
  induction ha using Subgroup.closure_induction with
  | mem u hu =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl
    · exact z_sq S
    · exact t_sq' (A := A)
    · exact k_sq S
  | one => exact one_pow 2
  | mul u v hu hv ihu ihv =>
    rw [(show Commute u v from B_comm S hu hv).mul_pow, ihu, ihv, one_mul]
  | inv u hu ih => rw [inv_pow, ih, inv_one]

theorem E_eq_sup (yi : X) : S.E yi = S.B ⊔ zpowers yi := closure_four_eq_sup _ _ _ _

theorem mem_E_z (yi : X) : S.z ∈ S.E yi := subset_closure (by simp)

theorem mem_E_yi (yi : X) : yi ∈ S.E yi := subset_closure (by simp)

theorem mem_E_t (yi : X) : t ∈ S.E yi := subset_closure (by simp)

theorem mem_E_k (yi : X) : S.k ∈ S.E yi := subset_closure (by simp)

theorem B_le_E (yi : X) : S.B ≤ S.E yi := by
  rw [E_eq_sup]
  exact le_sup_left

theorem E_eq_pre {yi : X} (hyi : yi ∈ A.R) {P : Subgroup (Perm (ZMod 8))} (hzP : z8 ∈ P)
    (hkP : k8 ∈ P) (hyP : ψX A yi ∈ P)
    (hw : ∀ u b, aff8 u b ∈ P → ∃ a j l : Fin 2,
      aff8 u b = z8 ^ (a : ℕ) * ψX A yi ^ (j : ℕ) * k8 ^ (l : ℕ)) :
    S.E yi = pre A P := by
  apply le_antisymm
  · rw [KDBase.E, closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact mem_pre.mpr ⟨z_mem_T S, by rw [ψ_z]; exact hzP⟩
    · exact mem_pre.mpr ⟨hyi.1, hyP⟩
    · exact t_mem_pre P
    · exact mem_pre.mpr ⟨k_mem_T S, by rw [ψ_k]; exact hkP⟩
  · intro g hg
    obtain ⟨hgT, hgP⟩ := mem_pre.mp hg
    obtain ⟨u, b, hub⟩ := ψX_mem_H8' hgT
    rw [← hub] at hgP
    obtain ⟨a, j, l, h⟩ := hw u b hgP
    have hw' : S.z ^ (a : ℕ) * yi ^ (j : ℕ) * S.k ^ (l : ℕ) ∈ S.E yi :=
      mul_mem (mul_mem (pow_mem (mem_E_z S yi) _) (pow_mem (mem_E_yi S yi) _))
        (pow_mem (mem_E_k S yi) _)
    have hwT : S.z ^ (a : ℕ) * yi ^ (j : ℕ) * S.k ^ (l : ℕ) ∈ A.T :=
      mul_mem (mul_mem (pow_mem (z_mem_T S) _) (pow_mem hyi.1 _)) (pow_mem (k_mem_T S) _)
    refine mem_of_ψX_eq C (mem_E_t S yi) hgT hw' hwT ?_
    rw [ψX_mul (mul_mem (pow_mem (z_mem_T S) _) (pow_mem hyi.1 _)) (pow_mem (k_mem_T S) _),
      ψX_mul (pow_mem (z_mem_T S) _) (pow_mem hyi.1 _), ψX_pow (z_mem_T S), ψX_pow hyi.1,
      ψX_pow (k_mem_T S), ψ_z, ψ_k, ← hub, h]

theorem E_eq_PE₀ {yi : X} (hyi : yi ∈ A.R) {e : ZMod 8} (he : ψX A yi = aff8 (-1) e)
    (h0 : pE 0 (-1) e) : S.E yi = pre A PE₀ :=
  E_eq_pre S hyi (PB_le_PE₀ z8_mem_PB) (PB_le_PE₀ k8_mem_PB) (by rw [he]; exact mem_PE₀.mpr h0)
    (fun u b h => by rw [he]; exact word_PE 0 (Or.inl rfl) e h0 u b (mem_PE₀.mp h))

theorem E_eq_PE₂ {yi : X} (hyi : yi ∈ A.R) {e : ZMod 8} (he : ψX A yi = aff8 (-1) e)
    (h2 : pE 2 (-1) e) : S.E yi = pre A PE₂ :=
  E_eq_pre S hyi (PB_le_PE₂ z8_mem_PB) (PB_le_PE₂ k8_mem_PB) (by rw [he]; exact mem_PE₂.mpr h2)
    (fun u b h => by rw [he]; exact word_PE 2 (Or.inr rfl) e h2 u b (mem_PE₂.mp h))

theorem E_cases : (S.E S.y = pre A PE₀ ∧ S.E (S.x * S.y) = pre A PE₂) ∨
    (S.E S.y = pre A PE₂ ∧ S.E (S.x * S.y) = pre A PE₀) := by
  obtain ⟨e, he, hy⟩ := ψ_y S
  have hxy : ∃ s : ZMod 8, (s = 2 ∨ s = 6) ∧ ψX A (S.x * S.y) = aff8 (-1) (s + e) := by
    rw [ψX_mul (x_mem_T S) (y_mem_T S), hy]
    rcases ψ_x S with h | h <;> rw [h, aff8_mul, one_mul, Units.val_one, one_mul]
    · exact ⟨2, Or.inl rfl, rfl⟩
    · exact ⟨6, Or.inr rfl, rfl⟩
  obtain ⟨s, hs, hxy⟩ := hxy
  rcases refl_mem e he s hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨E_eq_PE₀ S S.y_mem hy h1, E_eq_PE₂ S (xy_mem S) hxy h2⟩
  · exact Or.inr ⟨E_eq_PE₂ S S.y_mem hy h1, E_eq_PE₀ S (xy_mem S) hxy h2⟩

theorem E₁_inf_E₂ : S.E S.y ⊓ S.E (S.x * S.y) = S.B := by
  rw [B_eq, ← PE₀_inf_PE₂, pre_inf]
  rcases E_cases S with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  exact inf_comm _ _

theorem E_le_T (yi : X) (hyi : yi ∈ A.R) : S.E yi ≤ A.T := by
  rw [KDBase.E, closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact z_mem_T S
  · exact hyi.1
  · exact A.t_mem_T
  · exact k_mem_T S

theorem eq_of_mem_E {yi : X} (hyi : yi ∈ A.R) (hyi2 : yi ^ 2 = 1) {g : X} (hg : g ∈ S.E yi) :
    ∃ a b c l : ℕ, a < 2 ∧ b < 2 ∧ c < 2 ∧ l < 2 ∧
      g = S.z ^ a * yi ^ b * t ^ c * S.k ^ l :=
  mem_closure_four (z_sq S) hyi2 (t_sq' (A := A)) (k_sq S) (z_comm S hyi.1) (z_comm_t S)
    (z_comm_k S) (comm_t hyi.1) (k_comm_R S hyi).symm (k_comm_t S).symm hg

theorem E_comm {yi : X} (hyi : yi ∈ A.R) {a b : X} (ha : a ∈ S.E yi) (hb : b ∈ S.E yi) :
    a * b = b * a := by
  have hc : ({S.z, yi, t, S.k} : Set X).Pairwise Commute := by
    intro u hu v hv _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl
    all_goals first
      | exact Commute.refl _
      | exact z_comm S hyi.1
      | exact (z_comm S hyi.1).symm
      | exact z_comm_t S
      | exact (z_comm_t S).symm
      | exact z_comm_k S
      | exact (z_comm_k S).symm
      | exact comm_t hyi.1
      | exact (comm_t hyi.1).symm
      | exact k_comm_R S hyi
      | exact (k_comm_R S hyi).symm
      | exact k_comm_t S
      | exact (k_comm_t S).symm
  have h : (⟨a, ha⟩ : closure ({S.z, yi, t, S.k} : Set X)) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ :=
    (isMulCommutative_closure hc).is_comm.comm _ _
  exact congrArg Subtype.val h

theorem E_sq {yi : X} (hyi : yi ∈ A.R) (hyi2 : yi ^ 2 = 1) {a : X} (ha : a ∈ S.E yi) :
    a ^ 2 = 1 := by
  induction ha using Subgroup.closure_induction with
  | mem u hu =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact z_sq S
    · exact hyi2
    · exact t_sq' (A := A)
    · exact k_sq S
  | one => exact one_pow 2
  | mul u v hu hv ihu ihv =>
    rw [(show Commute u v from E_comm S hyi hu hv).mul_pow, ihu, ihv, one_mul]
  | inv u hu ih => rw [inv_pow, ih, inv_one]

theorem elem_E {yi : X} (hyi : yi ∈ A.R) (hyi2 : yi ^ 2 = 1) : ElemAbelianTwo (S.E yi) :=
  ⟨fun _ ha _ hb => E_comm S hyi ha hb, fun _ ha => E_sq S hyi hyi2 ha⟩

theorem elem_B : ElemAbelianTwo S.B :=
  ⟨fun _ ha _ hb => B_comm S ha hb, fun _ ha => B_sq S ha⟩

theorem card_B : Nat.card S.B = 8 := by
  obtain ⟨hV1, hV1m, hV1c⟩ := ElemAbelianTwo.bot.sup_zpowers (z_sq S)
    (fun h => z_ne_one S (mem_bot.mp h)) (fun a ha => by rw [mem_bot.mp ha, one_mul, mul_one])
  have hV1R : (⊥ ⊔ zpowers S.z : Subgroup X) ≤ A.R := sup_le bot_le (zpowers_le.mpr (z_mem S))
  obtain ⟨hV2, hV2m, hV2c⟩ := hV1.sup_zpowers (t_sq' (A := A))
    (fun h => A.config.not_mem (hV1R h).2.1) (fun a ha => (comm_t (hV1R ha).1).symm)
  have hV2P : (⊥ ⊔ zpowers S.z ⊔ zpowers t : Subgroup X) ≤ pre A (zpowers z8) := by
    refine sup_le (sup_le bot_le ?_) ?_ <;> rw [zpowers_le]
    · exact mem_pre.mpr ⟨z_mem_T S, by rw [ψ_z]; exact mem_zpowers _⟩
    · exact t_mem_pre _
  obtain ⟨-, -, hV3c⟩ := hV2.sup_zpowers (k_sq S) (fun h => by
      have := (mem_pre.mp (hV2P h)).2
      rw [ψ_k] at this
      rcases eq_one_or_eq_of_mem_zpowers (by decide) this with h1 | h1 <;>
        exact absurd h1 (by decide))
    (fun a ha => (z_comm_k S).symm.trans (by rfl) |> fun _ => by
      have haB : a ∈ S.B := by
        have hle : (⊥ ⊔ zpowers S.z ⊔ zpowers t : Subgroup X) ≤ S.B :=
          sup_le (sup_le bot_le (zpowers_le.mpr (mem_B_z S))) (zpowers_le.mpr (mem_B_t S))
        exact hle ha
      exact B_comm S (mem_B_k S) haB)
  have hB : S.B = ⊥ ⊔ zpowers S.z ⊔ zpowers t ⊔ zpowers S.k := by
    rw [KDBase.B, closure_three_eq, bot_sup_eq]
  rw [hB, hV3c, hV2c, hV1c, card_bot]

theorem card_E {yi : X} (hyi : yi ∈ A.R) (hyi2 : yi ^ 2 = 1) (hyiB : yi ∉ S.B) :
    Nat.card (S.E yi) = 16 := by
  obtain ⟨-, -, hc⟩ := (elem_B S).sup_zpowers hyi2 hyiB (fun a ha =>
    E_comm S hyi (mem_E_yi S yi) (B_le_E S yi ha))
  rw [E_eq_sup, hc, card_B]

theorem y_not_mem_B : S.y ∉ S.B := by
  rw [mem_B_iff]
  rintro ⟨-, h⟩
  obtain ⟨e, -, hy⟩ := ψ_y S
  rw [hy] at h
  exact refl_not_mem_PB e h

theorem xy_not_mem_B : S.x * S.y ∉ S.B := by
  rw [mem_B_iff]
  rintro ⟨-, h⟩
  obtain ⟨e, -, hy⟩ := ψ_y S
  rw [ψX_mul (x_mem_T S) (y_mem_T S), hy] at h
  rcases ψ_x S with hx | hx <;> rw [hx, aff8_mul, one_mul, Units.val_one, one_mul] at h <;>
    exact refl_not_mem_PB _ h

theorem card_E₁ : Nat.card (S.E S.y) = 16 := card_E S S.y_mem S.y_sq (y_not_mem_B S)

theorem card_E₂ : Nat.card (S.E (S.x * S.y)) = 16 :=
  card_E S (xy_mem S) (xy_sq S) (xy_not_mem_B S)

end CFSG.OddStandard.SmallF3.L33.KD.KD46

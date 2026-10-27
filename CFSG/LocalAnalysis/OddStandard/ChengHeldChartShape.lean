module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldSetupCenter

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup

namespace ChartShape

section Calculus

variable {G : Type*} [Group G]

theorem cj_mul (a b y : G) : cj (a * b) y = cj a y * cj b y := by
  unfold cj; group

theorem cj_inv (a y : G) : cj a⁻¹ y = (cj a y)⁻¹ := by
  unfold cj; group

theorem cj_cj (a y y' : G) : cj (cj a y) y' = cj a (y * y') := by
  unfold cj; group

theorem cj_eq_mul_cm (a b : G) : cj a b = a * cm a b := by
  unfold cj cm; group

theorem cm_inv (a b : G) : (cm a b)⁻¹ = cm b a := by
  unfold cm; group

theorem cm_eq_one_iff {a b : G} : cm a b = 1 ↔ Commute a b := by
  unfold cm
  rw [show a⁻¹ * b⁻¹ * a * b = (b * a)⁻¹ * (a * b) by group, inv_mul_eq_one]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem cj_of_commute {a b : G} (h : Commute a b) : cj a b = a := by
  unfold cj
  rw [mul_assoc, h.eq, ← mul_assoc, inv_mul_cancel, one_mul]

theorem commute_of_mem_zpowers {t s w : G} (h : Commute t s) (hw : w ∈ zpowers t) :
    Commute w s := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hw
  exact h.zpow_left n

theorem cj_of_mem_zpowers {t s w : G} (h : Commute t s) (hw : w ∈ zpowers t) : cj w s = w :=
  cj_of_commute (commute_of_mem_zpowers h hw)

end Calculus

section Closure

variable {G : Type*} [Group G]

theorem cj_mem_of_closure_left {gens : Set G} {D : Subgroup G} (g : G)
    (h : ∀ z ∈ gens, cj z g ∈ D) : ∀ z ∈ closure gens, cj z g ∈ D := by
  intro z hz
  induction hz using Subgroup.closure_induction with
  | mem z hz => exact h z hz
  | one => simp [cj]
  | mul a b _ _ ha hb => rw [cj_mul]; exact mul_mem ha hb
  | inv a _ ha => rw [cj_inv]; exact inv_mem ha

theorem cj_mem_of_closure [Finite G] {gens : Set G} {D : Subgroup G}
    (h : ∀ g ∈ gens, ∀ z ∈ D, cj z g ∈ D) : ∀ s ∈ closure gens, ∀ z ∈ D, cj z s ∈ D := by
  have hle : closure gens ≤ normalizer (D : Set G) := by
    rw [closure_le]
    intro g hg
    rw [SetLike.mem_coe, ← inv_mem_iff]
    apply mem_normalizer_fintype
    intro n hn
    simpa [cj] using h g hg n hn
  intro s hs z hz
  have h1 := (mem_normalizer_iff.mp (inv_mem (hle hs)) z).mp hz
  simpa [cj] using h1

theorem cj_coset_of_closure {gens : Set G} {D : Subgroup G}
    (hD : ∀ s ∈ closure gens, ∀ z ∈ D, cj z s ∈ D) (x : G)
    (hgen : ∀ g ∈ gens, ∃ d ∈ D, cj x g = x * d) :
    ∀ s ∈ closure gens, ∃ d ∈ D, cj x s = x * d := by
  intro s hs
  induction hs using Subgroup.closure_induction with
  | mem g hg => exact hgen g hg
  | one => exact ⟨1, one_mem _, by simp [cj]⟩
  | mul a b ha hb iha ihb =>
    obtain ⟨d₁, hd₁, h₁⟩ := iha
    obtain ⟨d₂, hd₂, h₂⟩ := ihb
    refine ⟨d₂ * cj d₁ b, mul_mem hd₂ (hD b hb d₁ hd₁), ?_⟩
    rw [← cj_cj, h₁, cj_mul, h₂, mul_assoc]
  | inv a ha iha =>
    obtain ⟨d, hd, h⟩ := iha
    refine ⟨(cj d a⁻¹)⁻¹, inv_mem (hD a⁻¹ (inv_mem ha) d hd), ?_⟩
    have h1 : cj x a⁻¹ * cj d a⁻¹ = x := by
      rw [← cj_mul, ← h, cj_cj, mul_inv_cancel, cj]
      simp
    exact eq_mul_inv_iff_mul_eq.mpr h1

theorem cj_stab_of_closure {gens : Set G} {Z : Subgroup G}
    (hZ : ∀ s ∈ closure gens, ∀ w ∈ Z, s * w = w * s) (y : G)
    (hgen : ∀ g ∈ gens, ∃ w ∈ Z, cj g y = g * w) :
    ∀ s ∈ closure gens, ∃ w ∈ Z, cj s y = s * w := by
  intro s hs
  induction hs using Subgroup.closure_induction with
  | mem g hg => exact hgen g hg
  | one => exact ⟨1, one_mem _, by simp [cj]⟩
  | mul a b ha hb iha ihb =>
    obtain ⟨w₁, hw₁, h₁⟩ := iha
    obtain ⟨w₂, hw₂, h₂⟩ := ihb
    refine ⟨w₁ * w₂, mul_mem hw₁ hw₂, ?_⟩
    rw [cj_mul, h₁, h₂, mul_assoc, ← mul_assoc w₁ b w₂, ← hZ b hb w₁ hw₁, mul_assoc b w₁ w₂,
      ← mul_assoc a b]
  | inv a ha iha =>
    obtain ⟨w, hw, h⟩ := iha
    refine ⟨w⁻¹, inv_mem hw, ?_⟩
    have h1 : a * w = w * a := hZ a ha w hw
    rw [cj_inv, h, h1, mul_inv_rev]

end Closure

section Datum

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} (d : Datum A)

theorem conj_inv_mem_QS {y u : G} (hy : y ∈ d.X) (hu : u ∈ d.QS) : y⁻¹ * u * y ∈ d.QS := by
  obtain ⟨a, ha, s, hs, rfl⟩ := d.mem_QS_iff.mp hu
  refine d.mem_QS_iff.mpr ⟨y⁻¹ * a * y, ?_, y⁻¹ * s * y, ?_, by group⟩
  · simpa using d.conj_mem_Q (d.X.inv_mem hy) ha
  · simpa using d.conj_mem_S (d.X.inv_mem hy) hs

theorem mul_mem_QS_comm {y y' : G} (hy : y ∈ d.X) (h : y * y' ∈ d.QS) : y' * y ∈ d.QS := by
  have := conj_inv_mem_QS d hy h
  rwa [show y⁻¹ * (y * y') * y = y' * y by group] at this

theorem cj_of_mem_QS {x z : G} (hx : x ∈ d.S) (hz : z ∈ d.QS) :
    ∃ s ∈ d.S, cj x z = cj x s := by
  obtain ⟨u, hu, s, hs, rfl⟩ := d.mem_QS_iff.mp hz
  refine ⟨s, hs, ?_⟩
  have hxu : Commute x u := mem_centralizer_iff.mp (d.Q_le_centralizer_S hu) x hx
  rw [← cj_cj, cj_of_commute hxu]

end Datum

end ChartShape

namespace Chart4

open ChartShape

section Invariants

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {α : ℕ} (c : Chart4 d α)

theorem shape_t_sq_ne_one : c.t ^ 2 ≠ 1 := by
  intro h
  have := d.q_ord
  rw [c.q_eq, h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem shape_t_inv_ne : c.t⁻¹ ≠ c.t := by
  intro h
  apply c.shape_t_sq_ne_one
  rw [pow_two]
  nth_rewrite 1 [← h]
  exact inv_mul_cancel _

theorem shape_commute_t {s : G} (hs : s ∈ d.S) : Commute c.t s :=
  (mem_centralizer_iff.mp (d.Q_le_centralizer c.t_mem.1) s (d.S_le_A hs)).symm

theorem shape_gen_mem {g : G}
    (hg : g ∈ ({c.t, c.pi, c.tau, c.mu, c.lam, c.ze, c.xi} : Set G)) : g ∈ d.S :=
  c.gen ▸ subset_closure hg

theorem shape_D_le : closure ({c.t, c.pi, c.tau} : Set G) ≤ d.S := by
  rw [closure_le]
  obtain ⟨hpi, htau, _⟩ := c.mem
  rintro g (rfl | rfl | rfl)
  · exact c.t_mem.2
  · exact hpi
  · exact htau

theorem shape_cj_pi_gen {g : G}
    (hg : g ∈ ({c.t, c.pi, c.tau, c.mu, c.lam, c.ze, c.xi} : Set G)) :
    cj c.pi g = c.pi ∨ cj c.pi g = c.t ^ 2 * c.pi := by
  have hF := c.frame
  obtain ⟨hpi, _⟩ := c.mem
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (cj_of_commute (c.shape_commute_t hpi).symm)
  · exact Or.inl (cj_of_commute (Commute.refl _))
  · exact Or.inl (cj_of_commute (cm_eq_one_iff.mp hF.pi_tau))
  · exact Or.inr hF.pi_mu
  · exact Or.inr hF.pi_lam
  · exact Or.inr hF.pi_ze
  · exact Or.inl hF.pi_xi

theorem shape_cj_tau_gen {g : G}
    (hg : g ∈ ({c.t, c.pi, c.tau, c.mu, c.lam, c.ze, c.xi} : Set G)) :
    cj c.tau g = c.tau ∨ cj c.tau g = c.t ^ 2 * c.tau := by
  have hF := c.frame
  obtain ⟨_, htau, _⟩ := c.mem
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (cj_of_commute (c.shape_commute_t htau).symm)
  · exact Or.inl (cj_of_commute (cm_eq_one_iff.mp hF.pi_tau).symm)
  · exact Or.inl (cj_of_commute (Commute.refl _))
  · exact Or.inl (cj_of_commute (cm_eq_one_iff.mp hF.tau_mu))
  · exact Or.inr hF.tau_lam
  · exact Or.inr hF.tau_ze
  · exact Or.inr hF.tau_xi

theorem shape_tau_cj {s : G} (hs : s ∈ d.S) : ∃ w ∈ zpowers c.t, cj c.tau s = c.tau * w := by
  rw [← c.gen] at hs
  refine cj_coset_of_closure ?_ c.tau ?_ s hs
  · intro s hs z hz
    rw [c.gen] at hs
    rw [cj_of_mem_zpowers (c.shape_commute_t hs) hz]
    exact hz
  · intro g hg
    obtain ⟨_, htau, _⟩ := c.mem
    have hct2 : c.t ^ 2 * c.tau = c.tau * c.t ^ 2 := ((c.shape_commute_t htau).pow_left 2).eq
    rcases c.shape_cj_tau_gen hg with h | h
    · exact ⟨1, one_mem _, by rw [mul_one, h]⟩
    · exact ⟨c.t ^ 2, pow_mem (mem_zpowers _) 2, by rw [h, hct2]⟩

theorem shape_pi_not_mem_zpowers : c.pi ∉ zpowers c.t := by
  intro h
  obtain ⟨_, _, hmu, _⟩ := c.mem
  have h1 := cj_of_mem_zpowers (c.shape_commute_t hmu) h
  rw [c.frame.pi_mu] at h1
  exact c.shape_t_sq_ne_one (by simpa using h1)

theorem shape_D_normalized {s : G} (hs : s ∈ d.S) : ∀ z ∈ closure ({c.t, c.pi, c.tau} : Set G),
    cj z s ∈ closure ({c.t, c.pi, c.tau} : Set G) := by
  rw [← c.gen] at hs
  have ht : c.t ∈ closure ({c.t, c.pi, c.tau} : Set G) := subset_closure (by simp)
  have hpi : c.pi ∈ closure ({c.t, c.pi, c.tau} : Set G) := subset_closure (by simp)
  have htau : c.tau ∈ closure ({c.t, c.pi, c.tau} : Set G) := subset_closure (by simp)
  have ht2 : c.t ^ 2 * c.pi ∈ closure ({c.t, c.pi, c.tau} : Set G) :=
    mul_mem (pow_mem ht 2) hpi
  have ht2' : c.t ^ 2 * c.tau ∈ closure ({c.t, c.pi, c.tau} : Set G) :=
    mul_mem (pow_mem ht 2) htau
  refine cj_mem_of_closure (fun g hg => cj_mem_of_closure_left g fun z hz => ?_) s hs
  rcases hz with rfl | rfl | rfl
  · rw [cj_of_commute (c.shape_commute_t (c.shape_gen_mem hg))]
    exact ht
  · rcases c.shape_cj_pi_gen hg with h | h <;> rw [h]
    · exact hpi
    · exact ht2
  · rcases c.shape_cj_tau_gen hg with h | h <;> rw [h]
    · exact htau
    · exact ht2'

theorem shape_mu_cj {s : G} (hs : s ∈ d.S) :
    ∃ e ∈ closure ({c.t, c.pi, c.tau} : Set G), cj c.mu s = c.mu * e := by
  rw [← c.gen] at hs
  refine cj_coset_of_closure (fun s hs z hz => c.shape_D_normalized (c.gen ▸ hs) z hz) c.mu
    ?_ s hs
  intro g hg
  have hF := c.frame
  obtain ⟨hpi, _, hmu, _⟩ := c.mem
  have ht : c.t ∈ closure ({c.t, c.pi, c.tau} : Set G) := subset_closure (by simp)
  have hpi' : c.pi ∈ closure ({c.t, c.pi, c.tau} : Set G) := subset_closure (by simp)
  have htau' : c.tau ∈ closure ({c.t, c.pi, c.tau} : Set G) := subset_closure (by simp)
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, one_mem _, by rw [mul_one]; exact cj_of_commute (c.shape_commute_t hmu).symm⟩
  · refine ⟨(c.t ^ 2)⁻¹, inv_mem (pow_mem ht 2), ?_⟩
    have hct2 : c.t ^ 2 * c.pi = c.pi * c.t ^ 2 := ((c.shape_commute_t hpi).pow_left 2).eq
    have h1 := cj_eq_mul_cm c.pi c.mu
    rw [hF.pi_mu, hct2] at h1
    rw [cj_eq_mul_cm, ← cm_inv, ← mul_left_cancel h1]
  · exact ⟨1, one_mem _, by rw [mul_one]; exact cj_of_commute (cm_eq_one_iff.mp hF.tau_mu).symm⟩
  · exact ⟨1, one_mem _, by rw [mul_one]; exact cj_of_commute (Commute.refl _)⟩
  · exact ⟨1, one_mem _, by rw [mul_one]; exact cj_of_commute (cm_eq_one_iff.mp hF.mu_lam)⟩
  · exact ⟨c.t * c.pi, mul_mem ht hpi', by rw [cj_eq_mul_cm, hF.mu_ze]⟩
  · exact ⟨c.pi * c.tau, mul_mem hpi' htau', by rw [cj_eq_mul_cm, hF.mu_xi]⟩

theorem shape_D_xi {z : G} (hz : z ∈ closure ({c.t, c.pi, c.tau} : Set G)) :
    ∃ w ∈ zpowers c.t, cj z c.xi = z * w := by
  have hF := c.frame
  obtain ⟨_, htau, _, _, _, hxi⟩ := c.mem
  refine cj_stab_of_closure ?_ c.xi ?_ z hz
  · intro s hs w hw
    exact (commute_of_mem_zpowers (c.shape_commute_t (c.shape_D_le hs)) hw).symm.eq
  · intro g hg
    have hct2 : c.t ^ 2 * c.tau = c.tau * c.t ^ 2 := ((c.shape_commute_t htau).pow_left 2).eq
    rcases hg with rfl | rfl | rfl
    · exact ⟨1, one_mem _, by rw [mul_one]; exact cj_of_commute (c.shape_commute_t hxi)⟩
    · exact ⟨1, one_mem _, by rw [mul_one]; exact hF.pi_xi⟩
    · exact ⟨c.t ^ 2, pow_mem (mem_zpowers _) 2, by rw [hF.tau_xi, hct2]⟩

theorem shape_ze_xi_not_mem {e : G} (he : e ∈ closure ({c.t, c.pi, c.tau} : Set G)) :
    c.ze * c.xi ≠ c.mu * e := by
  intro h
  have hF := c.frame
  obtain ⟨_, _, hmu, _⟩ := c.mem
  obtain ⟨w, hw, hcj⟩ := c.shape_D_xi (inv_mem he)
  have hmu' : c.mu = c.ze * c.xi * e⁻¹ := by rw [h]; group
  have h1 : cj c.mu c.xi = c.mu * w := by
    rw [hmu', cj_mul, cj_mul, hcj, cj_of_commute (cm_eq_one_iff.mp hF.ze_xi),
      cj_of_commute (Commute.refl c.xi)]
    group
  have h2 : cj c.mu c.xi = c.mu * (c.pi * c.tau) := by rw [cj_eq_mul_cm, hF.mu_xi]
  have h3 : c.pi * c.tau = w := mul_left_cancel (h2.symm.trans h1)
  have h4 : cj (c.pi * c.tau) c.mu = c.pi * c.tau := by
    rw [h3]; exact cj_of_mem_zpowers (c.shape_commute_t hmu) hw
  rw [cj_mul, hF.pi_mu, cj_of_commute (cm_eq_one_iff.mp hF.tau_mu)] at h4
  exact c.shape_t_sq_ne_one (by simpa [mul_assoc] using h4)

end Invariants

section Products

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {α : ℕ} (c : Chart4 d α)

theorem shape_not_QS_of_t {y₁ y₂ : G}
    (ha : (cj c.t y₁ = c.t ∧ cj c.t y₂ = c.t⁻¹) ∨ (cj c.t y₁ = c.t⁻¹ ∧ cj c.t y₂ = c.t)) :
    y₁ * y₂ ∉ d.QS := by
  intro hz
  obtain ⟨s, hs, h⟩ := cj_of_mem_QS d c.t_mem.2 hz
  rw [cj_of_commute (c.shape_commute_t hs), ← cj_cj] at h
  apply c.shape_t_inv_ne
  rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2] at h
    exact h
  · rw [h1, cj_inv, h2] at h
    exact h

theorem shape_not_QS_tau {y₁ y₂ : G} (h1 : cj c.tau y₁ = c.tau⁻¹)
    (h2 : cj c.tau y₂ = c.pi * c.tau⁻¹) : y₁ * y₂ ∉ d.QS := by
  intro hz
  obtain ⟨_, htau, _⟩ := c.mem
  obtain ⟨s, hs, h⟩ := cj_of_mem_QS d htau hz
  obtain ⟨w, hw, hw'⟩ := c.shape_tau_cj hs
  rw [← cj_cj, h1, cj_inv, h2, mul_inv_rev, inv_inv, hw'] at h
  have h3 : c.pi⁻¹ = w := mul_left_cancel h
  exact c.shape_pi_not_mem_zpowers (by rw [← inv_inv c.pi, h3]; exact inv_mem hw)

theorem shape_not_QS_mu {y₁ y₂ : G} (h1 : cj c.mu y₁ = c.t ^ 2 * c.lam)
    (h2 : cj c.t y₂ = c.t⁻¹) (h3 : cj c.lam y₂ = c.t ^ 2 * c.ze * c.xi) :
    y₁ * y₂ ∉ d.QS := by
  intro hz
  obtain ⟨_, _, hmu, _⟩ := c.mem
  obtain ⟨s, hs, h⟩ := cj_of_mem_QS d hmu hz
  obtain ⟨e, he, he'⟩ := c.shape_mu_cj hs
  have h4 : cj c.mu (y₁ * y₂) = c.ze * c.xi := by
    rw [← cj_cj, h1, cj_mul, pow_two, cj_mul, h2, h3]
    group
  rw [h4, he'] at h
  exact c.shape_ze_xi_not_mem he h

theorem shape_not_QS_field_graph {y₁ y₂ : G} (h₁ : c.rep Kind.field = some y₁)
    (h₂ : c.rep Kind.graph = some y₂) : y₁ * y₂ ∉ d.QS := by
  have a₁ := (c.rep_mem _ _ h₁).2.2
  have a₂ := (c.rep_mem _ _ h₂).2.2
  by_cases h0 : α = 0
  · simp only [Kind.Act, h0, ite_true] at a₁ a₂
    exact c.shape_not_QS_of_t (Or.inl ⟨a₁.1, a₂.1⟩)
  · simp only [Kind.Act, h0, ite_false] at a₁ a₂
    exact c.shape_not_QS_of_t (Or.inr ⟨a₁.1, a₂.1⟩)

theorem shape_not_QS_field_unitary {y₁ y₂ : G} (h₁ : c.rep Kind.field = some y₁)
    (h₂ : c.rep Kind.unitary = some y₂) : y₁ * y₂ ∉ d.QS := by
  have a₁ := (c.rep_mem _ _ h₁).2.2
  have a₂ := (c.rep_mem _ _ h₂).2.2
  by_cases h0 : α = 0
  · simp only [Kind.Act, h0, ite_true] at a₁ a₂
    exact c.shape_not_QS_of_t (Or.inl ⟨a₁.1, a₂.1⟩)
  · simp only [Kind.Act, h0, ite_false] at a₁ a₂
    exact c.shape_not_QS_mu a₁.2.2.2.1 a₂.1 a₂.2.2.2.2.1

theorem shape_not_QS_graph_unitary {y₁ y₂ : G} (h₁ : c.rep Kind.graph = some y₁)
    (h₂ : c.rep Kind.unitary = some y₂) : y₁ * y₂ ∉ d.QS := by
  have a₁ := (c.rep_mem _ _ h₁).2.2
  have a₂ := (c.rep_mem _ _ h₂).2.2
  by_cases h0 : α = 0
  · simp only [Kind.Act, h0, ite_true] at a₁ a₂
    exact c.shape_not_QS_tau a₁.2.2.1 a₂.2.2.1
  · simp only [Kind.Act, h0, ite_false] at a₁ a₂
    exact c.shape_not_QS_of_t (Or.inl ⟨a₁.1, a₂.1⟩)

theorem shape_not_QS_mul {k₁ k₂ : Kind} (hne : k₁ ≠ k₂) {y₁ y₂ : G}
    (h₁ : c.rep k₁ = some y₁) (h₂ : c.rep k₂ = some y₂) : y₁ * y₂ ∉ d.QS := by
  have hX₁ := (c.rep_mem _ _ h₁).1
  cases k₁ <;> cases k₂
  · exact absurd rfl hne
  · exact c.shape_not_QS_field_graph h₁ h₂
  · exact c.shape_not_QS_field_unitary h₁ h₂
  · exact fun h => c.shape_not_QS_field_graph h₂ h₁ (mul_mem_QS_comm d hX₁ h)
  · exact absurd rfl hne
  · exact c.shape_not_QS_graph_unitary h₁ h₂
  · exact fun h => c.shape_not_QS_field_unitary h₂ h₁ (mul_mem_QS_comm d hX₁ h)
  · exact fun h => c.shape_not_QS_graph_unitary h₂ h₁ (mul_mem_QS_comm d hX₁ h)
  · exact absurd rfl hne

theorem shape_mem_kinds_third {a b k : Kind} (ha : a ∈ c.kinds) (hb : b ∈ c.kinds) (hab : a ≠ b)
    (hka : k ≠ a) (hkb : k ≠ b) : k ∈ c.kinds := by
  obtain ⟨y₁, h₁⟩ := Option.isSome_iff_exists.mp ha
  obtain ⟨y₂, h₂⟩ := Option.isSome_iff_exists.mp hb
  have a₁ := c.rep_mem a y₁ h₁
  have a₂ := c.rep_mem b y₂ h₂
  obtain ⟨k', y₀, hk', u, hu, heq⟩ :=
    c.cover (y₁ * y₂) (d.X.mul_mem a₁.1 a₂.1) (c.shape_not_QS_mul hab h₁ h₂)
  have hk'k : k' = k := by
    by_contra hne
    have hcases : k' = a ∨ k' = b := by
      cases a <;> cases b <;> cases k <;> cases k' <;> simp_all
    rcases hcases with rfl | rfl
    · rw [h₁] at hk'
      obtain rfl : y₀ = y₁ := (Option.some.inj hk').symm
      apply a₂.2.1
      have := conj_inv_mem_QS d a₁.1 hu
      rwa [show y₀⁻¹ * u * y₀ = y₂ by rw [mul_assoc, ← heq]; group] at this
    · rw [h₂] at hk'
      obtain rfl : y₀ = y₂ := (Option.some.inj hk').symm
      apply a₁.2.1
      rw [mul_right_cancel heq]
      exact hu
  rw [← hk'k]
  exact Option.isSome_iff_exists.mpr ⟨y₀, hk'⟩

end Products

section Main

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {α : ℕ}

theorem shape (_h : Hyp G A) (c : Chart4 d α) :
    c.kinds = ∅ ∨ c.kinds = {Kind.field} ∨ c.kinds = {Kind.graph} ∨ c.kinds = {Kind.unitary} ∨
      c.kinds = Set.univ := by
  have third := fun {a b k : Kind} => c.shape_mem_kinds_third (a := a) (b := b) (k := k)
  by_cases hf : Kind.field ∈ c.kinds <;> by_cases hg : Kind.graph ∈ c.kinds <;>
    by_cases hu : Kind.unitary ∈ c.kinds
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Set.eq_univ_of_forall fun k => ?_))))
    cases k <;> assumption
  · exact absurd (third hf hg (by simp) (by simp) (by simp)) hu
  · exact absurd (third hf hu (by simp) (by simp) (by simp)) hg
  · exact Or.inr (Or.inl (Set.ext fun k => by cases k <;> simp [hf, hg, hu]))
  · exact absurd (third hg hu (by simp) (by simp) (by simp)) hf
  · exact Or.inr (Or.inr (Or.inl (Set.ext fun k => by cases k <;> simp [hf, hg, hu])))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Set.ext fun k => by cases k <;> simp [hf, hg, hu]))))
  · exact Or.inl (Set.ext fun k => by cases k <;> simp [hf, hg, hu])

end Main

end Chart4

end CFSG.OddStandard.ChengHeld

module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Two

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b

section Config

variable {G : Type} [Group G]

structure IsCaseIITwo (A : Subgroup G) (t u : G) : Prop where
  mem_t : t ∈ A
  mem_u : u ∈ A
  t_sq : t ^ 2 = 1
  u_sq : u ^ 2 = 1
  comm : t * u = u * t
  t_ne_one : t ≠ 1
  u_ne_one : u ≠ 1
  u_ne : u ≠ t
  invariant : ∀ x ∈ ({t, u, t * u} : Set G), ∀ b ∈ A, b * x = x * b →
    ∀ y ∈ ({t, u, t * u} : Set G), b * y * b⁻¹ ∈ ({t, u, t * u} : Set G)
  swap : ∃ a ∈ A, a * t = t * a ∧ a * u * a⁻¹ = u * t

theorem IsCaseIITwo.not_noPairOrbit {A : Subgroup G} {t u : G} (h : IsCaseIITwo A t u) :
    ¬ NoPairOrbit A t := by
  intro hNP
  have htu : u * t = t * u := h.comm.symm
  have horb : ∀ b ∈ A ⊓ centralizer ({t} : Set G), b * u * b⁻¹ = u ∨ b * u * b⁻¹ = u * t := by
    intro b hb
    obtain ⟨hbA, hbt⟩ := mem_inf.mp hb
    have hbt' : b * t = t * b := mem_centralizer_singleton_iff.mp hbt
    have hmem := h.invariant t (by simp) b hbA hbt' u (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h1 | h1 | h1
    · exfalso
      apply h.u_ne
      calc u = b⁻¹ * (b * u * b⁻¹) * b := by group
        _ = b⁻¹ * t * b := by rw [h1]
        _ = t := by rw [mul_assoc, ← hbt', inv_mul_cancel_left]
    · exact Or.inl h1
    · exact Or.inr (h1.trans htu.symm)
  obtain ⟨a, ha, hat, hau⟩ := h.swap
  have hfix := hNP u (mem_inf.mpr ⟨h.mem_u, mem_centralizer_singleton_iff.mpr htu⟩) h.u_sq horb
    a (mem_inf.mpr ⟨ha, mem_centralizer_singleton_iff.mpr hat⟩)
  apply h.t_ne_one
  have h1 := hau.symm.trans hfix
  calc t = u⁻¹ * (u * t) := by group
    _ = 1 := by rw [h1, inv_mul_cancel]

end Config

@[expose] def LinearCaseIITwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A),
    D.family = .linear → CFSG.Open.IsQuasisimple ↥A → Odd (Nat.card (center A)) → D.q = 2 →
      ∀ t u : G, IsCaseIITwo A t u → D.HasRank t 2

@[expose] def UnitaryCaseIITwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A),
    D.family = .unitary → CFSG.Open.IsQuasisimple ↥A → Odd (Nat.card (center A)) → D.q = 2 →
      ∀ t u : G, ¬ IsCaseIITwo A t u

@[expose] def OrthCaseIITwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A),
    (D.family = .orthPlus ∨ D.family = .orthMinus) → CFSG.Open.IsQuasisimple ↥A →
      Odd (Nat.card (center A)) → D.q = 2 → ∀ t u : G, ¬ IsCaseIITwo A t u

namespace Hyp221

variable {G : Type} [Group G] [Finite G] {A T : Subgroup G} (hH : Hyp221 A T)
  (hZ : Odd (Nat.card (center ↥A)))
include hH hZ

theorem exists_isCaseIITwo
    (h212 : ¬ ∀ x ∈ T ⊔ A, rightConjugate T x ⊓ normalizer (T : Set G) ≤
      centralizer (T : Set G)) :
    Nat.card T = 4 ∧ ∃ t₀ ∈ T, t₀ ≠ 1 ∧
      (∃ a ∈ A, a * t₀ = t₀ * a ∧ a ∈ normalizer (T : Set G) ∧ a ∉ centralizer (T : Set G)) ∧
      ∃ u : G, IsCaseIITwo A t₀ u := by
  have hT4 : Nat.card T = 4 := by
    rcases hH.normalizer_cond with h | h
    · exact h
    · exact absurd h h212
  refine ⟨hT4, ?_⟩
  push Not at h212
  obtain ⟨x, hx, hnot⟩ := h212
  obtain ⟨y, hy, hyC⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  obtain ⟨hyx, hyN⟩ := mem_inf.mp hy
  rw [mem_rightConjugate_iff] at hyx
  have hyTA : y ∈ T ⊔ A := by
    have h : y = x⁻¹ * (x * y * x⁻¹) * x := by group
    rw [h]
    exact mul_mem (mul_mem (inv_mem hx) (mem_sup_left hyx)) hx
  obtain ⟨a, ha, τ, hτ, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hH.le_normalizer
    (show y ∈ A ⊔ T by rw [sup_comm]; exact hyTA)
  have hy2 : (a * τ) * (a * τ) = 1 := by
    have h := hH.sq_eq_one hyx
    rw [sq, show x * (a * τ) * x⁻¹ * (x * (a * τ) * x⁻¹) = x * ((a * τ) * (a * τ)) * x⁻¹ by
      group, conj_eq_one_iff] at h
    exact h
  have hact : ∀ v ∈ T, (a * τ) * v * (a * τ)⁻¹ = a * v * a⁻¹ := by
    intro v hv
    have h := hH.commute hτ hv
    calc (a * τ) * v * (a * τ)⁻¹ = a * (τ * v) * τ⁻¹ * a⁻¹ := by group
      _ = a * v * a⁻¹ := by rw [h]; group
  have haN : a ∈ normalizer (T : Set G) := by
    have h : a = (a * τ) * τ⁻¹ := by group
    rw [h]
    exact mul_mem hyN (Subgroup.le_normalizer (inv_mem hτ))
  have hconj : ∀ v ∈ T, a * v * a⁻¹ ∈ T := fun v hv => (mem_normalizer_iff.mp haN v).mp hv
  have ha2 : ∀ v ∈ T, a * (a * v * a⁻¹) * a⁻¹ = v := by
    intro v hv
    rw [← hact _ (hconj v hv), ← hact v hv]
    calc (a * τ) * ((a * τ) * v * (a * τ)⁻¹) * (a * τ)⁻¹ =
        ((a * τ) * (a * τ)) * v * ((a * τ) * (a * τ))⁻¹ := by group
      _ = v := by rw [hy2]; group
  obtain ⟨s, hs, has⟩ : ∃ s ∈ T, a * s * a⁻¹ ≠ s := by
    by_contra hall
    push Not at hall
    apply hyC
    rw [mem_centralizer_iff]
    intro v hv
    have h := hall v hv
    rw [← hact v hv] at h
    calc v * (a * τ) = (a * τ) * v * (a * τ)⁻¹ * (a * τ) := by rw [h]
      _ = (a * τ) * v := by group
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact has (by group)
  set s' := a * s * a⁻¹ with hs'
  have hs'T : s' ∈ T := hconj s hs
  have hss : s * s = 1 := by rw [← sq]; exact hH.sq_eq_one hs
  set t₀ := s * s' with ht₀
  have ht₀T : t₀ ∈ T := mul_mem hs hs'T
  have ht₀1 : t₀ ≠ 1 := by
    intro h
    apply has
    calc a * s * a⁻¹ = s' := rfl
      _ = s * (s * s') := by rw [← mul_assoc, hss, one_mul]
      _ = s := by rw [← ht₀, h, mul_one]
  have ht₀A : t₀ ∈ A := by
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
    have h1 : s * a * s⁻¹ ∈ A := (mem_normalizer_iff.mp (hH.le_normalizer hs) a).mp ha
    have h2 : t₀ = (s * a * s⁻¹) * a⁻¹ := by
      rw [ht₀, hs', hsinv]
      group
    rw [h2]
    exact mul_mem h1 (inv_mem ha)
  have hat₀ : a * t₀ * a⁻¹ = t₀ := by
    calc a * t₀ * a⁻¹ = (a * s * a⁻¹) * (a * s' * a⁻¹) := by rw [ht₀]; group
      _ = s' * s := by rw [← hs', hs', ha2 s hs]
      _ = t₀ := by rw [ht₀, hH.commute hs'T hs]
  have hat : a * t₀ = t₀ * a := by rw [← mul_inv_eq_iff_eq_mul.mp hat₀]
  have has' : a * s * a⁻¹ = s * t₀ := by
    rw [ht₀, ← mul_assoc, hss, one_mul]
  have hst₀ : s ≠ t₀ := by
    intro h
    apply has
    rw [hs', h]
    exact hat₀
  have haC : a ∉ centralizer (T : Set G) := by
    intro haC
    apply has
    show a * s * a⁻¹ = s
    rw [← (mem_centralizer_iff.mp haC) s hs, mul_inv_cancel_right]
  have hp₀ : IsAPart A t₀ t₀ :=
    ⟨ht₀A, ⟨1, by rw [pow_one]; exact hH.sq_eq_one ht₀T⟩, by
      rw [inv_mul_cancel]; exact one_mem _⟩
  obtain ⟨u, hu⟩ := hH.exists_aPart hZ hs
  have hp₀u := hH.isAPart_mul hZ ht₀T hs hp₀ hu
  have hup₀ : t₀ * u = u * t₀ := hH.commute_aPart hZ ht₀T hs hp₀ hu
  have haup : a * u * a⁻¹ = u * t₀ := by
    have h1 := hu.conj ha
    rw [has'] at h1
    rw [h1.unique hZ (hH.isAPart_mul hZ hs ht₀T hu hp₀)]
  have hst₀1 : t₀ * s ≠ 1 := by
    intro h
    apply hst₀
    have h1 : s = t₀⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [h1, inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hH.sq_eq_one ht₀T)]
  have hdata : ∀ x ∈ ({t₀, u, t₀ * u} : Set G), ∃ tx ∈ T, tx ≠ 1 ∧ IsAPart A tx x := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨_, ht₀T, ht₀1, hp₀⟩
    · exact ⟨s, hs, hs1, hu⟩
    · exact ⟨t₀ * s, mul_mem ht₀T hs, hst₀1, hp₀u⟩
  have hback : ∀ ty ∈ T, ty ≠ 1 → ∀ y, IsAPart A ty y → y ∈ ({t₀, u, t₀ * u} : Set G) := by
    intro ty hty hty1 y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases mem_four_of_card hH.elem hT4 ht₀T hs ht₀1 hs1 hst₀ hty with h | h | h | h
    · exact absurd h hty1
    · subst h
      exact Or.inl (hy.unique hZ hp₀)
    · subst h
      exact Or.inr (Or.inl (hy.unique hZ hu))
    · subst h
      exact Or.inr (Or.inr (hy.unique hZ hp₀u))
  have hu1 : u ≠ 1 := hH.aPart_ne_one hs hs1 hu
  have hut : u ≠ t₀ := by
    intro h
    apply hst₀
    have h1 : s⁻¹ * t₀ ∈ centralizer (A : Set G) := by
      have e : s⁻¹ * t₀ = (s⁻¹ * u) * (t₀⁻¹ * t₀)⁻¹ := by rw [h]; group
      rw [e]
      exact mul_mem hu.2.2 (inv_mem hp₀.2.2)
    have h2 := hH.eq_one_of_mem_centralizer (mul_mem (inv_mem hs) ht₀T) h1
    exact (inv_mul_eq_one.mp h2)
  refine ⟨t₀, ht₀T, ht₀1, ⟨a, ha, hat, haN, haC⟩, u, ?_⟩
  refine ⟨ht₀A, hu.1, hH.sq_eq_one ht₀T, hH.aPart_sq hZ hs hu, hup₀, ht₀1, hu1, hut, ?_,
    a, ha, hat, haup⟩
  intro x hx b hb hbx y hy
  obtain ⟨tx, htx, htx1, hxt⟩ := hdata x hx
  obtain ⟨ty, hty, hty1, hyt⟩ := hdata y hy
  have hbt : b * tx = tx * b := (hxt.commute_iff hb).mpr hbx
  have hbN := hH.mem_normalizer_of_commute hb htx htx1 hbt
  have hbty : b * ty * b⁻¹ ∈ T := (mem_normalizer_iff.mp hbN ty).mp hty
  have hbty1 : b * ty * b⁻¹ ≠ 1 := fun h => hty1 (by rwa [conj_eq_one_iff] at h)
  exact hback _ hbty hbty1 _ (hyt.conj hb)

end Hyp221

theorem classical222TwoB_of (hL : LinearCaseIITwo) (hU : UnitaryCaseIITwo)
    (hO : OrthCaseIITwo) : Classical222TwoB := by
  intro G _ _ A T D hq H hZ h212
  obtain ⟨hT4, t₀, ht₀T, ht₀1, ⟨a, ha, hat, haN, haC⟩, u, hconf⟩ := H.exists_isCaseIITwo hZ h212
  refine ⟨t₀, ht₀T, ht₀1, ?_⟩
  unfold CaseQTwo
  cases hfam : D.family with
  | linear => exact hL G A D hfam H.quasisimple hZ hq t₀ u hconf
  | unitary => exact hU G A D hfam H.quasisimple hZ hq t₀ u hconf
  | symplectic =>
    exact ⟨hZ, hT4, a, mem_inf.mpr ⟨ha, mem_centralizer_singleton_iff.mpr hat⟩, haN, haC⟩
  | orthPlus => exact hO G A D (Or.inl hfam) H.quasisimple hZ hq t₀ u hconf
  | orthMinus => exact hO G A D (Or.inr hfam) H.quasisimple hZ hq t₀ u hconf

end CFSG.ComponentClassification.RankTwoClassical

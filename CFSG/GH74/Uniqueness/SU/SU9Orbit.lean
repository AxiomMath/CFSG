module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.Uniqueness.SU.SU7Gen

public section

namespace CFSG.GH74.Uniqueness.SU.SU9

open Subgroup CFSG.GH74.Uniqueness.SU.SU7

section Orbit

variable {G : Type*} [Group G] [Finite G]

structure OrbitData (T A U : Subgroup G) (n : G) : Prop where
  card_T : Nat.card T = 64
  card_A : Nat.card A = 16
  card_U : Nat.card U = 4
  U_le_A : U ≤ A
  A_le_T : A ≤ T
  A_comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a
  A_sq : ∀ a ∈ A, a * a = 1
  U_central : ∀ u ∈ U, ∀ t ∈ T, u * t = t * u
  T_comm : ∀ t ∈ T, ∀ t' ∈ T, t * t' * t⁻¹ * t'⁻¹ ∈ U
  cent_A : ∀ a ∈ A, a ∉ U → centralizer ({a} : Set G) ⊓ T = A
  n_U : ∀ u ∈ U, n * u * n⁻¹ ∈ U
  n_A : ∀ a ∈ A, n * a * n⁻¹ ∈ A
  n_cube : n ^ 3 = 1
  n_fpf : ∀ t ∈ T, t ≠ 1 → n * t * n⁻¹ ≠ t

namespace OrbitData

variable {T A U : Subgroup G} {n : G} (h : OrbitData T A U n)

include h

omit [Finite G] in
theorem U_comm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
  h.A_comm a (h.U_le_A ha) b (h.U_le_A hb)

omit [Finite G] in
theorem U_sq : ∀ a ∈ U, a * a = 1 := fun a ha => h.A_sq a (h.U_le_A ha)

theorem n_inv_U : ∀ u ∈ U, n⁻¹ * u * n ∈ U := by
  have hn : n ∈ normalizer (U : Set G) := Gen.mem_normalizer_of_conj_le h.n_U
  intro u hu
  have := (mem_normalizer_iff.1 (inv_mem hn) u).1 hu
  simpa using this

theorem conj_mem (a : G) (ha : a ∈ A) (haU : a ∉ U) : n * a * n⁻¹ ∈ A ∧ n * a * n⁻¹ ∉ U := by
  refine ⟨h.n_A a ha, fun hU => haU ?_⟩
  have := h.n_inv_U _ hU
  simpa [mul_assoc] using this

omit h in
@[expose] noncomputable def commHom (hUc : ∀ u ∈ U, ∀ t ∈ T, u * t = t * u)
    (hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hcomm : ∀ t ∈ T, ∀ t' ∈ T, t * t' * t⁻¹ * t'⁻¹ ∈ U) (a : G) (haT : a ∈ T) :
    ↥T →* ↥U where
  toFun t := ⟨(t : G) * a * (t : G)⁻¹ * a⁻¹, hcomm t t.2 a haT⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    apply Subtype.ext
    show (x * y) * a * (x * y)⁻¹ * a⁻¹ = (x * a * x⁻¹ * a⁻¹) * (y * a * y⁻¹ * a⁻¹)
    have hc' := hUc _ (hcomm y hy a haT) x hx
    have e1 : x * (y * a * y⁻¹ * a⁻¹) * x⁻¹ = y * a * y⁻¹ * a⁻¹ := by
      rw [mul_inv_eq_iff_eq_mul]; exact hc'.symm
    have e2 : (x * y) * a * (x * y)⁻¹ * a⁻¹ =
        (x * (y * a * y⁻¹ * a⁻¹) * x⁻¹) * (x * a * x⁻¹ * a⁻¹) := by group
    rw [e2, e1]
    exact hUcomm _ (hcomm y hy a haT) _ (hcomm x hx a haT)

theorem orbit_cover (a : G) (ha : a ∈ A) (haU : a ∉ U) :
    ∀ u ∈ U, ∃ t ∈ T, t * a * t⁻¹ = u * a := by
  have haT : a ∈ T := h.A_le_T ha
  let κ : ↥T →* ↥U := commHom h.U_central h.U_comm h.T_comm a haT
  have hκ : ∀ t : ↥T, ((κ t : ↥U) : G) = (t : G) * a * (t : G)⁻¹ * a⁻¹ := fun t => rfl
  have hker : Nat.card κ.ker = Nat.card A := by
    refine Nat.card_congr
      { toFun := fun t => ⟨(t.1 : G), ?_⟩
        invFun := fun g => ⟨⟨(g : G), h.A_le_T g.2⟩, ?_⟩
        left_inv := fun t => rfl
        right_inv := fun g => rfl }
    · have h1 := t.2
      rw [MonoidHom.mem_ker] at h1
      have h2 : (t.1 : G) * a * (t.1 : G)⁻¹ * a⁻¹ = 1 := by
        rw [← hκ]; exact congrArg Subtype.val h1
      have h3 : (t.1 : G) * a = a * t.1 := by
        have h4 : (t.1 : G) * a * (t.1 : G)⁻¹ = a := by
          have := h2
          rw [mul_inv_eq_one] at this
          simpa [mul_assoc] using this
        rw [mul_inv_eq_iff_eq_mul] at h4
        exact h4
      rw [← h.cent_A a ha haU]
      exact ⟨mem_centralizer_singleton_iff.2 h3, t.1.2⟩
    · rw [MonoidHom.mem_ker]
      apply Subtype.ext
      rw [hκ]
      have e : (g : G) * a = a * g := h.A_comm _ g.2 a ha
      simp only [OneMemClass.coe_one]
      have : (g : G) * a * (g : G)⁻¹ * a⁻¹ = 1 := by
        rw [e]; group
      exact this
  have hc := Subgroup.card_ker_mul_card_range κ
  have hrange : Nat.card κ.range = 4 := by
    rw [hker, h.card_A, h.card_T] at hc
    omega
  have htop : κ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hrange, h.card_U]
  intro u hu
  have hmem : (⟨u, hu⟩ : ↥U) ∈ κ.range := by rw [htop]; exact Subgroup.mem_top _
  obtain ⟨t, ht⟩ := hmem
  refine ⟨(t : G), t.2, ?_⟩
  have h5 : (t : G) * a * (t : G)⁻¹ * a⁻¹ = u := by
    have := congrArg Subtype.val ht
    rw [hκ] at this
    exact this
  calc (t : G) * a * (t : G)⁻¹ = ((t : G) * a * (t : G)⁻¹ * a⁻¹) * a := by group
    _ = u * a := by rw [h5]

theorem not_conj_mem_coset (a : G) (ha : a ∈ A) (haU : a ∉ U) (u : G) (hu : u ∈ U) :
    n * a * n⁻¹ ≠ u * a := by
  intro heq
  let ψ : ↥U →* ↥U :=
    { toFun := fun w => ⟨(w : G) * (n * w * n⁻¹), U.mul_mem w.2 (h.n_U w w.2)⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        rintro ⟨w, hw⟩ ⟨w', hw'⟩
        apply Subtype.ext
        show (w * w') * (n * (w * w') * n⁻¹) = (w * (n * w * n⁻¹)) * (w' * (n * w' * n⁻¹))
        have hc : (n * w * n⁻¹) * w' = w' * (n * w * n⁻¹) := h.U_comm _ (h.n_U w hw) w' hw'
        calc (w * w') * (n * (w * w') * n⁻¹) = w * (w' * (n * w * n⁻¹)) * (n * w' * n⁻¹) := by group
          _ = w * ((n * w * n⁻¹) * w') * (n * w' * n⁻¹) := by rw [hc]
          _ = (w * (n * w * n⁻¹)) * (w' * (n * w' * n⁻¹)) := by group }
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have h1 : (w : G) * (n * w * n⁻¹) = 1 := congrArg Subtype.val hw
    have h2 : n * (w : G) * n⁻¹ = w := by
      have : n * (w : G) * n⁻¹ = (w : G)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [this]; exact inv_eq_of_mul_eq_one_right (h.U_sq w w.2)
    by_contra hne
    exact h.n_fpf w (h.A_le_T (h.U_le_A w.2)) (fun h0 => hne (Subtype.ext h0)) h2
  obtain ⟨w, hw⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨u, hu⟩
  have hw' : (w : G) * (n * w * n⁻¹) = u := congrArg Subtype.val hw
  have hsq : (n * (w : G) * n⁻¹) * (n * w * n⁻¹) = 1 := by
    have := h.U_sq w w.2
    calc (n * (w : G) * n⁻¹) * (n * w * n⁻¹) = n * (w * w) * n⁻¹ := by group
      _ = 1 := by rw [this]; group
  have hua : u * a = a * u := h.A_comm u (h.U_le_A hu) a ha
  have hfix : n * (a * w) * n⁻¹ = a * w := by
    calc n * (a * w) * n⁻¹ = (n * a * n⁻¹) * (n * w * n⁻¹) := by group
      _ = (u * a) * (n * w * n⁻¹) := by rw [heq]
      _ = a * (u * (n * w * n⁻¹)) := by rw [hua]; group
      _ = a * ((w * (n * w * n⁻¹)) * (n * w * n⁻¹)) := by rw [hw']
      _ = a * (w * ((n * w * n⁻¹) * (n * w * n⁻¹))) := by group
      _ = a * w := by rw [hsq]; group
  have hT : a * w ∈ T := T.mul_mem (h.A_le_T ha) (h.A_le_T (h.U_le_A w.2))
  have hne1 : a * (w : G) ≠ 1 := by
    intro h1
    apply haU
    have : a = (w : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]; exact U.inv_mem w.2
  exact h.n_fpf _ hT hne1 hfix

omit [Finite G] in
theorem card_quot : Nat.card (↥A ⧸ U.subgroupOf A) = 4 := by
  have h1 := Subgroup.card_mul_index (U.subgroupOf A)
  have h2 : Nat.card (U.subgroupOf A) = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.U_le_A).toEquiv
  rw [h2, h.card_U, h.card_A] at h1
  have h3 : (U.subgroupOf A).index = 4 := by omega
  rw [← Subgroup.index_eq_card, h3]

theorem exists_mem_coset (a : G) (ha : a ∈ A) (haU : a ∉ U) (a' : G) (ha' : a' ∈ A)
    (ha'U : a' ∉ U) : ∃ k < 3, ∃ u ∈ U, a' = (n ^ k * a * (n ^ k)⁻¹) * u := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hA1, hU1⟩ := h.conj_mem a ha haU
  obtain ⟨hA2, hU2⟩ := h.conj_mem _ hA1 hU1
  have e3 : n * n * n = 1 := by
    have := h.n_cube
    simpa [pow_succ, mul_assoc] using this
  have hn3 : n * (n * (n * a * n⁻¹) * n⁻¹) * n⁻¹ = a := by
    calc n * (n * (n * a * n⁻¹) * n⁻¹) * n⁻¹ = (n * n * n) * a * (n * n * n)⁻¹ := by group
      _ = a := by rw [e3]; group
  have hn2 : n ^ 2 * a * (n ^ 2)⁻¹ = n * (n * a * n⁻¹) * n⁻¹ := by rw [pow_two]; group
  have hnormal : (U.subgroupOf A).Normal := ⟨fun u hu g => by
    have hu' : (u : G) ∈ U := hu
    have hc : (g : G) * u = u * g := h.A_comm _ g.2 _ u.2
    rw [Subgroup.mem_subgroupOf]
    have : ((g * u * g⁻¹ : ↥A) : G) = u := by
      show (g : G) * u * (g : G)⁻¹ = u
      rw [hc]; group
    rw [this]; exact hu'⟩
  have hqeq : ∀ (g g' : G) (hg : g ∈ A) (hg' : g' ∈ A),
      (QuotientGroup.mk (⟨g, hg⟩ : ↥A) : ↥A ⧸ U.subgroupOf A) = QuotientGroup.mk ⟨g', hg'⟩ ↔
        g⁻¹ * g' ∈ U := by
    intro g g' hg hg'
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    rfl
  have hder : ∀ b ∈ A, b ∉ U → ∀ c, c = n * b * n⁻¹ → b⁻¹ * c ∉ U := by
    intro b hb hbU c hc hmem
    apply h.not_conj_mem_coset b hb hbU _ hmem
    calc n * b * n⁻¹ = c := hc.symm
      _ = b * (b⁻¹ * c) := by group
      _ = (b⁻¹ * c) * b := h.A_comm b hb _ (h.U_le_A hmem)
  have hcoset : ∀ k < 3, ∀ g : G, g = n ^ k * a * (n ^ k)⁻¹ → a'⁻¹ * g ∉ U ∧ g⁻¹ * a' ∉ U := by
    intro k hk g hg
    constructor
    · intro hmem
      apply hcon k hk (g⁻¹ * a') (by simpa using U.inv_mem hmem)
      rw [← hg]; group
    · intro hmem
      apply hcon k hk (g⁻¹ * a') hmem
      rw [← hg]; group
  have hU' : ∀ g : G, g ∈ A → g ∉ U → (1 : G)⁻¹ * g ∉ U := by
    intro g _ hgU; simpa using hgU
  have h1 := hder a ha haU _ rfl
  have h2 := hder _ hA1 hU1 _ rfl
  have h3 := hder _ hA2 hU2 (n * (n * (n * a * n⁻¹) * n⁻¹) * n⁻¹) rfl
  rw [hn3] at h3
  have c0 := hcoset 0 (by norm_num) a (by simp)
  have c1 := hcoset 1 (by norm_num) (n * a * n⁻¹) (by simp)
  have c2 := hcoset 2 (by norm_num) (n * (n * a * n⁻¹) * n⁻¹) hn2.symm
  have : Fintype (↥A ⧸ U.subgroupOf A) := Fintype.ofFinite _
  let q : ∀ g : G, g ∈ A → ↥A ⧸ U.subgroupOf A := fun g hg => QuotientGroup.mk ⟨g, hg⟩
  have hq : ∀ g g' : G, ∀ (hg : g ∈ A) (hg' : g' ∈ A), g⁻¹ * g' ∉ U → q g hg ≠ q g' hg' := by
    intro g g' hg hg' hn heq
    exact hn ((hqeq g g' hg hg').1 heq)
  have hnodup : [q 1 A.one_mem, q a ha, q _ hA1, q _ hA2, q a' ha'].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
      not_false_eq_true, and_true]
    refine ⟨⟨hq _ _ _ _ (by simpa using haU), hq _ _ _ _ (by simpa using hU1),
      hq _ _ _ _ (by simpa using hU2), hq _ _ _ _ (by simpa using ha'U)⟩,
      ⟨hq _ _ _ _ h1, hq _ _ _ _ (fun hh => h3 (by simpa using U.inv_mem hh)),
        hq _ _ _ _ c0.2⟩,
      ⟨hq _ _ _ _ h2, hq _ _ _ _ c1.2⟩, hq _ _ _ _ c2.2⟩
  have hlen := hnodup.length_le_card
  rw [← Nat.card_eq_fintype_card, card_quot h] at hlen
  simp at hlen

theorem pow_conj_mem (a : G) (ha : a ∈ A) (haU : a ∉ U) (k : ℕ) :
    n ^ k * a * (n ^ k)⁻¹ ∈ A ∧ n ^ k * a * (n ^ k)⁻¹ ∉ U := by
  induction k with
  | zero => simpa using And.intro ha haU
  | succ k ih =>
    have := h.conj_mem _ ih.1 ih.2
    rw [pow_succ']
    simpa [mul_assoc] using this

theorem exists_conj (a : G) (ha : a ∈ A) (haU : a ∉ U) (a' : G) (ha' : a' ∈ A) (ha'U : a' ∉ U) :
    ∃ t ∈ T, ∃ k : ℕ, (t * n ^ k) * a * (t * n ^ k)⁻¹ = a' := by
  obtain ⟨k, -, u, hu, rfl⟩ := h.exists_mem_coset a ha haU a' ha' ha'U
  obtain ⟨hA, hUk⟩ := h.pow_conj_mem a ha haU k
  obtain ⟨t, ht, hteq⟩ := h.orbit_cover _ hA hUk u hu
  refine ⟨t, ht, k, ?_⟩
  have hcomm : u * (n ^ k * a * (n ^ k)⁻¹) = (n ^ k * a * (n ^ k)⁻¹) * u :=
    h.A_comm u (h.U_le_A hu) _ hA
  calc t * n ^ k * a * (t * n ^ k)⁻¹ = t * (n ^ k * a * (n ^ k)⁻¹) * t⁻¹ := by group
    _ = u * (n ^ k * a * (n ^ k)⁻¹) := hteq
    _ = _ := hcomm

end OrbitData

end Orbit

end CFSG.GH74.Uniqueness.SU.SU9

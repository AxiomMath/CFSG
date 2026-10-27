module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.General
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

structure UT3 (R U U' W : Subgroup G) (q : ℕ) : Prop where
  sup_eq : R = U ⊔ U'
  sq₁ : ∀ a ∈ U, a * a = 1
  sq₂ : ∀ a ∈ U', a * a = 1
  inf_eq : U ⊓ U' = W
  comm_mem : ∀ a ∈ U, ∀ b ∈ U', a * b * a⁻¹ * b⁻¹ ∈ W
  cent : ∀ b ∈ U', b ∉ W → ∀ a ∈ U, a * b = b * a → a ∈ W
  card_U : Nat.card U = q ^ 2
  card_U' : Nat.card U' = q ^ 2
  card_W : Nat.card W = q
  one_lt : 1 < q

namespace UT3

variable {R U U' W : Subgroup G} {q : ℕ} (h : UT3 R U U' W q)
include h

omit [Finite G] in
theorem W_le_U : W ≤ U := h.inf_eq ▸ inf_le_left

omit [Finite G] in
theorem W_le_U' : W ≤ U' := h.inf_eq ▸ inf_le_right

omit [Finite G] in
theorem U_comm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb => by
  have h1 : (a * b) * (a * b) = 1 := h.sq₁ _ (U.mul_mem ha hb)
  have e1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (h.sq₁ a ha)
  have e2 : b⁻¹ = b := inv_eq_of_mul_eq_one_right (h.sq₁ b hb)
  have e3 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right h1
  rw [← e3, mul_inv_rev, e1, e2]

omit [Finite G] in
theorem U'_le_normalizer_U : U' ≤ Subgroup.normalizer (U : Set G) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ a ∈ U, b * a * b⁻¹ ∈ U := by
    intro a ha
    have h1 := h.comm_mem a⁻¹ (U.inv_mem ha) b hb
    have e : b * a * b⁻¹ = a * (a⁻¹ * b * a⁻¹⁻¹ * b⁻¹) := by group
    rw [e]
    exact U.mul_mem ha (h.W_le_U h1)
  intro a
  refine ⟨key a, fun hab => ?_⟩
  have := key _ hab
  have hbb : b * b = 1 := h.sq₂ b hb
  have hbb' : b⁻¹ * b⁻¹ = 1 := by rw [← mul_inv_rev, hbb, inv_one]
  have e2 : b * (b * a * b⁻¹) * b⁻¹ = a := by
    calc b * (b * a * b⁻¹) * b⁻¹ = (b * b) * a * (b⁻¹ * b⁻¹) := by group
      _ = a := by rw [hbb, hbb']; simp
  rwa [e2] at this

omit [Finite G] in
theorem mem_R_iff {r : G} : r ∈ R ↔ ∃ u ∈ U, ∃ u' ∈ U', r = u * u' := by
  rw [h.sup_eq]
  exact mem_sup_iff_of_le_normalizer h.U'_le_normalizer_U

omit [Finite G] in
theorem U_le_R : U ≤ R := h.sup_eq ▸ le_sup_left

omit [Finite G] in
theorem U'_le_R : U' ≤ R := h.sup_eq ▸ le_sup_right

omit [Finite G] in
theorem sq_mem_union {r : G} (hr : r ∈ R) (hr2 : r * r = 1) : r ∈ U ∨ r ∈ U' := by
  obtain ⟨u, hu, u', hu', rfl⟩ := h.mem_R_iff.1 hr
  have e1 : u⁻¹ = u := inv_eq_of_mul_eq_one_right (h.sq₁ u hu)
  have e2 : u'⁻¹ = u' := inv_eq_of_mul_eq_one_right (h.sq₂ u' hu')
  have e3 : (u * u')⁻¹ = u * u' := inv_eq_of_mul_eq_one_right hr2
  have hc : u * u' = u' * u := by
    have := e3
    rw [mul_inv_rev, e1, e2] at this
    exact this.symm
  by_cases hW : u' ∈ W
  · exact Or.inl (U.mul_mem hu (h.W_le_U hW))
  · exact Or.inr (U'.mul_mem (h.W_le_U' (h.cent u' hu' hW u hu hc)) hu')

theorem relIndex_U_R : U.relIndex R = q := by
  have hq : 0 < q := lt_trans zero_lt_one h.one_lt
  have h1 : U.relIndex (U' ⊔ U) = U.relIndex U' :=
    C5.relIndex_sup_eq_of_le_normalizer h.U'_le_normalizer_U
  have h2 : Nat.card U' = Nat.card (U ⊓ U' : Subgroup G) * (U ⊓ U').relIndex U' :=
    C5.card_eq_card_mul_relIndex inf_le_right
  rw [Subgroup.inf_relIndex_right, h.inf_eq, h.card_U', h.card_W] at h2
  have h3 : U.relIndex U' = q := by
    have : q * U.relIndex U' = q * q := by rw [← h2]; ring
    exact Nat.eq_of_mul_eq_mul_left hq this
  rw [h.sup_eq, sup_comm, h1, h3]

theorem card_le_sq {E : Subgroup G} (hE : E ≤ R) (hsq : ∀ e ∈ E, e * e = 1) :
    Nat.card E ≤ q ^ 2 := by
  have hq : 0 < q := lt_trans zero_lt_one h.one_lt
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb => by
    have h1 : (a * b) * (a * b) = 1 := hsq _ (E.mul_mem ha hb)
    have e1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
    have e2 : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
    have e3 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right h1
    rw [← e3, mul_inv_rev, e1, e2]
  by_cases hEU : E ≤ U
  · rw [← h.card_U]
    exact Subgroup.card_le_of_le hEU
  · obtain ⟨e, heE, heU⟩ : ∃ e ∈ E, e ∉ U := by
      by_contra hcon
      push Not at hcon
      exact hEU hcon
    obtain ⟨u, hu, u', hu', he⟩ := h.mem_R_iff.1 (hE heE)
    have hu'W : u' ∉ W := by
      intro hW
      apply heU
      rw [he]
      exact U.mul_mem hu (h.W_le_U hW)
    have hEU_W : E ⊓ U ≤ W := by
      rintro a ⟨haE, haU⟩
      apply h.cent u' hu' hu'W a haU
      have hae : Commute a e := hcomm a haE e heE
      have hau : Commute a u := h.U_comm a haU u hu
      have hu'e : u' = u⁻¹ * e := by rw [he]; group
      rw [hu'e]
      exact (Commute.mul_right hau.inv_right hae).eq
    have h1 : Nat.card E = Nat.card (E ⊓ U : Subgroup G) * (E ⊓ U).relIndex E :=
      C5.card_eq_card_mul_relIndex inf_le_left
    have h2 : (E ⊓ U).relIndex E = U.relIndex E := by
      rw [inf_comm, Subgroup.inf_relIndex_right]
    have h3 : U.relIndex E ≤ U.relIndex R :=
      Subgroup.relIndex_le_of_le_right hE (by rw [h.relIndex_U_R]; omega)
    calc Nat.card E = Nat.card (E ⊓ U : Subgroup G) * (E ⊓ U).relIndex E := h1
      _ ≤ Nat.card W * q := by
          rw [h2]
          exact Nat.mul_le_mul (Subgroup.card_le_of_le hEU_W) (h3.trans h.relIndex_U_R.le)
      _ = q ^ 2 := by rw [h.card_W]; ring

theorem eq_of_card {E : Subgroup G} (hE : E ≤ R) (hsq : ∀ e ∈ E, e * e = 1)
    (hc : Nat.card E = q ^ 2) : E = U ∨ E = U' := by
  have hcases : E ≤ U ∨ E ≤ U' := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hn1, hn2⟩ := hcon
    obtain ⟨a, haE, haU⟩ : ∃ a ∈ E, a ∉ U := by
      by_contra hh
      push Not at hh
      exact hn1 hh
    obtain ⟨b, hbE, hbU'⟩ : ∃ b ∈ E, b ∉ U' := by
      by_contra hh
      push Not at hh
      exact hn2 hh
    have ha' : a ∈ U' := (h.sq_mem_union (hE haE) (hsq a haE)).resolve_left haU
    have hb : b ∈ U := (h.sq_mem_union (hE hbE) (hsq b hbE)).resolve_right hbU'
    have hab : a * b ∈ E := E.mul_mem haE hbE
    rcases h.sq_mem_union (hE hab) (hsq _ hab) with h1 | h1
    · apply haU
      have := U.mul_mem h1 (U.inv_mem hb)
      simpa using this
    · apply hbU'
      have := U'.mul_mem (U'.inv_mem ha') h1
      simpa using this
  rcases hcases with h1 | h1
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge h1 (by rw [h.card_U, hc]))
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge h1 (by rw [h.card_U', hc]))

omit [Finite G] in
theorem mem_W_of_swap {a c : G} (ha : conjR U a = U') (ha2 : a * a = 1) (hcR : c ∈ R)
    (hc2 : c * c = 1) (hca : c * a = a * c) : c ∈ W := by
  have ha' : conjR U' a = U := by
    rw [← ha, conjR_conjR, ha2]
    exact conjR_one U
  have e : a⁻¹ * c * a = c := by
    rw [mul_assoc, hca, ← mul_assoc, inv_mul_cancel, one_mul]
  rcases h.sq_mem_union hcR hc2 with hcU | hcU'
  · have h1 : a⁻¹ * c * a ∈ conjR U a := mem_conjR_iff'.2 ⟨c, hcU, rfl⟩
    rw [e, ha] at h1
    rw [← h.inf_eq]
    exact ⟨hcU, h1⟩
  · have h1 : a⁻¹ * c * a ∈ conjR U' a := mem_conjR_iff'.2 ⟨c, hcU', rfl⟩
    rw [e, ha'] at h1
    rw [← h.inf_eq]
    exact ⟨h1, hcU'⟩

end UT3

omit [Finite G] in
theorem UT3.conj {R U U' W : Subgroup G} {q : ℕ} (h : UT3 R U U' W q) (g : G) :
    UT3 (conjR R g) (conjR U g) (conjR U' g) (conjR W g) q where
  sup_eq := by rw [h.sup_eq, conjR_sup]
  sq₁ a ha := by
    obtain ⟨b, hb, rfl⟩ := mem_conjR_iff'.1 ha
    have := h.sq₁ b hb
    calc g⁻¹ * b * g * (g⁻¹ * b * g) = g⁻¹ * (b * b) * g := by group
      _ = 1 := by rw [this]; group
  sq₂ a ha := by
    obtain ⟨b, hb, rfl⟩ := mem_conjR_iff'.1 ha
    have := h.sq₂ b hb
    calc g⁻¹ * b * g * (g⁻¹ * b * g) = g⁻¹ * (b * b) * g := by group
      _ = 1 := by rw [this]; group
  inf_eq := by rw [← conjR_inf, h.inf_eq]
  comm_mem a ha b hb := by
    obtain ⟨a₀, ha₀, rfl⟩ := mem_conjR_iff'.1 ha
    obtain ⟨b₀, hb₀, rfl⟩ := mem_conjR_iff'.1 hb
    refine mem_conjR_iff'.2 ⟨_, h.comm_mem a₀ ha₀ b₀ hb₀, ?_⟩
    group
  cent b hb hbW a ha hab := by
    obtain ⟨a₀, ha₀, rfl⟩ := mem_conjR_iff'.1 ha
    obtain ⟨b₀, hb₀, rfl⟩ := mem_conjR_iff'.1 hb
    have hb₀W : b₀ ∉ W := fun hh => hbW (mem_conjR_iff'.2 ⟨b₀, hh, rfl⟩)
    have hab₀ : a₀ * b₀ = b₀ * a₀ := by
      have h1 : g * (g⁻¹ * a₀ * g * (g⁻¹ * b₀ * g)) * g⁻¹ =
          g * (g⁻¹ * b₀ * g * (g⁻¹ * a₀ * g)) * g⁻¹ := by rw [hab]
      simpa [mul_assoc] using h1
    exact mem_conjR_iff'.2 ⟨a₀, h.cent b₀ hb₀ hb₀W a₀ ha₀ hab₀, rfl⟩
  card_U := by rw [card_conjR, h.card_U]
  card_U' := by rw [card_conjR, h.card_U']
  card_W := by rw [card_conjR, h.card_W]
  one_lt := h.one_lt

end CFSG.QuasithinUnique.Lin2

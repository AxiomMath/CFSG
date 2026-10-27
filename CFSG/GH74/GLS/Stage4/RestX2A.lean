module

public import CFSG.GH74.GLS.Stage4.T2Defs

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4
  CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] {D : Ch6Notation G}

theorem sl2_bruhat_cases {F : Type} [Field F] (g : SL2 F) :
    (∃ (s : F) (t : Fˣ), g = sl2U s * sl2D t) ∨
      (∃ (s s' : F) (t : Fˣ), g = sl2U s * sl2W F * sl2D t * sl2U s') := by
  obtain ⟨M, hM⟩ := g
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    rw [Matrix.det_fin_two] at hM
    exact hM
  by_cases hc : M 1 0 = 0
  · left
    have had : M 0 0 * M 1 1 = 1 := by rw [hc] at hdet; linear_combination hdet
    have ha : M 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one had
    have hd : M 1 1 = (M 0 0)⁻¹ := by
      field_simp
      linear_combination had
    refine ⟨M 0 1 * M 0 0, Units.mk0 (M 0 0) ha, ?_⟩
    apply sl2_ext
    rw [Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc, hd]
    field_simp
  · right
    have hu : (-(M 1 0)) ≠ 0 := neg_ne_zero.2 hc
    refine ⟨M 0 0 / M 1 0, M 1 1 / M 1 0, Units.mk0 (-(M 1 0)) hu, ?_⟩
    apply sl2_ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · field_simp
    · field_simp
      linear_combination (-1 : F) * hdet
    · field_simp

theorem sl2Phi_mem_bruhat {H : Subgroup G} {r : G} {Ya Yb : Subgroup G} (hP : SL2Phi H r Ya Yb) :
    ∀ k ∈ Ya ⊔ Yb, (∃ x ∈ Ya, ∃ h ∈ H, k = x * h) ∨
      (∃ x ∈ Ya, ∃ h ∈ H, ∃ x' ∈ Ya, k = x * r * h * x') := by
  obtain ⟨F, hF, hFin, hc, φ, hinj, hU, hL, hD, h₀, hh₀, hW⟩ := hP
  intro k hk
  have hle : Ya ⊔ Yb ≤ φ.range := by
    refine sup_le ?_ ?_
    · intro x hx
      obtain ⟨c, rfl⟩ := (hU x).1 hx
      exact ⟨_, rfl⟩
    · intro x hx
      obtain ⟨c, rfl⟩ := (hL x).1 hx
      exact ⟨_, rfl⟩
  obtain ⟨g, rfl⟩ := hle hk
  rcases sl2_bruhat_cases g with ⟨s, t, rfl⟩ | ⟨s, s', t, rfl⟩
  · left
    exact ⟨φ (sl2U s), (hU _).2 ⟨s, rfl⟩, φ (sl2D t), hD t, by simp [map_mul]⟩
  · right
    refine ⟨φ (sl2U s), (hU _).2 ⟨s, rfl⟩, h₀ * φ (sl2D t), H.mul_mem hh₀ (hD t), φ (sl2U s'),
      (hU _).2 ⟨s', rfl⟩, ?_⟩
    simp only [map_mul, hW]
    group

theorem Ch6Basics.sl2Phi₁ (h : Ch6Basics D) : SL2Phi D.H D.w₁ D.X₁ D.X₁' := by
  have h' : SL2Phi D.H D.w₁ (D.root 1) (D.root (-1)) :=
    SL2Pair.toSL2Phi (fun x hx y hy => by rw [root_p1] at hy ⊢; exact h.H_norm_X₁ x hx y hy)
      (fun x hx y hy => by rw [root_m1] at hy ⊢; exact h.H_norm_X₁' x hx y hy) h.sl2₁
  rwa [root_p1, root_m1] at h'

theorem Ch6S6.false_of_Q (hb : Ch6Basics D) (hS : Ch6S6 D) {Q : Subgroup G}
    (hQR : Q ≤ D.R₂) (hQH : DodecA.HInv D.H Q) (hQne : Q ≠ ⊥)
    (hQz : ∀ q ∈ Q, D.z * q * D.z⁻¹ = q⁻¹)
    (hQcomm : ∀ q ∈ Q, ∀ q' ∈ Q, q * q' = q' * q)
    (hQX : ∀ x ∈ D.X₁, ∀ q ∈ Q, x * q * x⁻¹ = q)
    (hQw : ∀ q ∈ Q, ∀ q' ∈ Q, q * (D.w₁ * q' * D.w₁⁻¹) = (D.w₁ * q' * D.w₁⁻¹) * q) : False := by
  have hP := hb.sl2Phi₁
  have hX₂K : D.X₂ ≤ D.K₂ := by rw [hb.K₂_eq]; exact le_sup_left
  have key : ∀ m ∈ D.K₁, ∀ q ∈ Q, ∀ q' ∈ Q, q * (m * q' * m⁻¹) = (m * q' * m⁻¹) * q := by
    intro m hm q hq q' hq'
    rw [hb.K₁_eq] at hm
    have h1 : ∀ h ∈ D.H, h * q' * h⁻¹ ∈ Q := fun h hh => hQH h hh q' hq'
    rcases sl2Phi_mem_bruhat hP m hm with ⟨x, hx, h, hh, rfl⟩ | ⟨x, hx, h, hh, x', hx', rfl⟩
    · have e : x * h * q' * (x * h)⁻¹ = h * q' * h⁻¹ := by
        calc x * h * q' * (x * h)⁻¹ = x * (h * q' * h⁻¹) * x⁻¹ := by group
          _ = h * q' * h⁻¹ := hQX x hx _ (h1 h hh)
      rw [e]
      exact hQcomm q hq _ (h1 h hh)
    · have h2 := hQX x' hx' q' hq'
      have e : x * D.w₁ * h * x' * q' * (x * D.w₁ * h * x')⁻¹ =
          x * (D.w₁ * (h * q' * h⁻¹) * D.w₁⁻¹) * x⁻¹ := by
        calc x * D.w₁ * h * x' * q' * (x * D.w₁ * h * x')⁻¹
            = x * D.w₁ * h * (x' * q' * x'⁻¹) * h⁻¹ * D.w₁⁻¹ * x⁻¹ := by group
          _ = x * (D.w₁ * (h * q' * h⁻¹) * D.w₁⁻¹) * x⁻¹ := by rw [h2]; group
      rw [e]
      have h3 := hQw q hq _ (h1 h hh)
      have h4 : x⁻¹ * q * x = q := by simpa using hQX x⁻¹ (D.X₁.inv_mem hx) q hq
      calc q * (x * (D.w₁ * (h * q' * h⁻¹) * D.w₁⁻¹) * x⁻¹)
          = x * ((x⁻¹ * q * x) * (D.w₁ * (h * q' * h⁻¹) * D.w₁⁻¹)) * x⁻¹ := by group
        _ = x * (q * (D.w₁ * (h * q' * h⁻¹) * D.w₁⁻¹)) * x⁻¹ := by rw [h4]
        _ = x * ((D.w₁ * (h * q' * h⁻¹) * D.w₁⁻¹) * q) * x⁻¹ := by rw [h3]
        _ = (x * (D.w₁ * (h * q' * h⁻¹) * D.w₁⁻¹) * x⁻¹) * (x * q * x⁻¹) := by group
        _ = (x * (D.w₁ * (h * q' * h⁻¹) * D.w₁⁻¹) * x⁻¹) * q := by rw [hQX x hx q hq]
  set S : Set G := (D.X₂ : Set G) ∪ {y | ∃ m ∈ D.K₁, ∃ q ∈ Q, y = m * q * m⁻¹} with hSdef
  have hSR : ∀ y ∈ S, y ∈ D.R₂ := by
    intro y hy
    rcases hy with hy | ⟨m, hm, q, hq, rfl⟩
    · exact hS.X₂_le_R₂ hy
    · exact hS.K₁_normR₂ m hm q (hQR hq)
  have hScomm : ∀ y ∈ S, ∀ y' ∈ S, y * y' = y' * y := by
    intro y hy y' hy'
    rcases hy with hy | ⟨m, hm, q, hq, rfl⟩
    · exact ((hS.R₂_center y (hS.X₂_le_R₂ hy)).2 hy y' (hSR y' hy')).symm
    · rcases hy' with hy' | ⟨m', hm', q', hq', rfl⟩
      · exact (hS.R₂_center y' (hS.X₂_le_R₂ hy')).2 hy' _ (hSR _ (Or.inr ⟨m, hm, q, hq, rfl⟩))
      · have hmm : m⁻¹ * m' ∈ D.K₁ := D.K₁.mul_mem (D.K₁.inv_mem hm) hm'
        have h5 := key _ hmm q hq q' hq'
        have e1 : m * q * m⁻¹ * (m' * q' * m'⁻¹) =
            m * (q * ((m⁻¹ * m') * q' * (m⁻¹ * m')⁻¹)) * m⁻¹ := by group
        have e2 : m' * q' * m'⁻¹ * (m * q * m⁻¹) =
            m * (((m⁻¹ * m') * q' * (m⁻¹ * m')⁻¹) * q) * m⁻¹ := by group
        rw [e1, e2, h5]
  have hcl : ∀ y ∈ Subgroup.closure S, ∀ y' ∈ Subgroup.closure S, y * y' = y' * y := by
    intro y hy y' hy'
    induction hy, hy' using Subgroup.closure_induction₂ with
    | mem x y hx hy => exact hScomm x hx y hy
    | one_left x hx => simp
    | one_right x hx => simp
    | mul_left x y z hx hy hz h1 h2 =>
      calc x * y * z = x * (y * z) := by group
        _ = x * (z * y) := by rw [h2]
        _ = (x * z) * y := by group
        _ = (z * x) * y := by rw [h1]
        _ = z * (x * y) := by group
    | mul_right y z x hy hz hx h1 h2 =>
      calc x * (y * z) = (x * y) * z := by group
        _ = (y * x) * z := by rw [h1]
        _ = y * (x * z) := by group
        _ = y * (z * x) := by rw [h2]
        _ = (y * z) * x := by group
    | inv_left x y hx hy h1 =>
      have : x⁻¹ * y = y * x⁻¹ := by
        calc x⁻¹ * y = x⁻¹ * (y * x) * x⁻¹ := by group
          _ = x⁻¹ * (x * y) * x⁻¹ := by rw [h1]
          _ = y * x⁻¹ := by group
      exact this
    | inv_right x y hx hy h1 =>
      have : x * y⁻¹ = y⁻¹ * x := by
        calc x * y⁻¹ = y⁻¹ * (y * x) * y⁻¹ := by group
          _ = y⁻¹ * (x * y) * y⁻¹ := by rw [h1]
          _ = y⁻¹ * x := by group
      exact this
  set V : Subgroup G := Subgroup.closure S with hV
  have hX₂V : D.X₂ ≤ V := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hQV : ∀ q ∈ Q, q ∈ V := fun q hq =>
    Subgroup.subset_closure (Or.inr ⟨1, D.K₁.one_mem, q, hq, by simp⟩)
  have hVR : V ≤ D.R₂ := by
    rw [hV, Subgroup.closure_le]
    exact hSR
  have hVinv : ∀ m ∈ D.K₁, ∀ v ∈ V, m * v * m⁻¹ ∈ V := by
    intro m hm v hv
    induction hv using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | ⟨m', hm', q, hq, rfl⟩
      · have h1 := hb.K_comm m hm y (hX₂K hy)
        have : m * y * m⁻¹ = y := by rw [h1]; group
        rw [this]
        exact Subgroup.subset_closure (Or.inl hy)
      · have : m * (m' * q * m'⁻¹) * m⁻¹ = (m * m') * q * (m * m')⁻¹ := by group
        rw [this]
        exact Subgroup.subset_closure (Or.inr ⟨m * m', D.K₁.mul_mem hm hm', q, hq, rfl⟩)
    | one => simp
    | mul y₁ y₂ _ _ ih₁ ih₂ =>
      have : m * (y₁ * y₂) * m⁻¹ = (m * y₁ * m⁻¹) * (m * y₂ * m⁻¹) := by group
      rw [this]
      exact V.mul_mem ih₁ ih₂
    | inv y _ ih =>
      have : m * y⁻¹ * m⁻¹ = (m * y * m⁻¹)⁻¹ := by group
      rw [this]
      exact V.inv_mem ih
  rcases hS.K₁_irred V hX₂V hVR hVinv with hVX | hVR₂
  ·
    obtain ⟨q, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hQne
    have hqX : (q : G) ∈ D.X₂ := by rw [← hVX]; exact hQV q q.2
    have h1 := hb.K_comm D.z hb.z_mem_K₁ q (hX₂K hqX)
    have h2 : D.z * q * D.z⁻¹ = q := by rw [h1]; group
    have h3 := hQz q q.2
    rw [h2] at h3
    have hsq : (q : G) * q = 1 := by
      calc (q : G) * q = q * (q : G)⁻¹ := by rw [← h3]
        _ = 1 := mul_inv_cancel _
    obtain ⟨k, hk⟩ := hb.prime.odd_of_ne_two hb.p_ne_two
    have h6 : ((q : G) * q) ^ k * q = 1 := by
      rw [← pow_two, ← pow_mul, ← pow_succ, ← hk]
      exact hb.X₂_exp q hqX
    rw [hsq, one_pow, one_mul] at h6
    exact hq1 (Subtype.ext h6)
  ·
    have hRX : D.R₂ ≤ D.X₂ := by
      intro y hy
      have hyV : y ∈ Subgroup.closure S := by rw [← hV, hVR₂]; exact hy
      refine (hS.R₂_center y hy).1 (fun x hx => ?_)
      have hxV : x ∈ Subgroup.closure S := by rw [← hV, hVR₂]; exact hx
      exact hcl x hxV y hyV
    have hEq : D.R₂ = D.X₂ := le_antisymm hRX hS.X₂_le_R₂
    have hcard := hS.R₂_card
    rw [hEq, hb.card_X₂] at hcard
    have h5 := hb.q₁_ge
    have h3 := hb.q₂_ge
    have : D.q₂ * 1 < D.q₁ ^ 2 * D.q₂ ^ 3 := by
      have h1 : 1 < D.q₁ ^ 2 := by nlinarith
      have h2 : 1 ≤ D.q₂ ^ 2 := Nat.one_le_pow _ _ (by omega)
      calc D.q₂ * 1 < D.q₂ * D.q₁ ^ 2 := by
            apply Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
        _ ≤ D.q₁ ^ 2 * D.q₂ ^ 3 := by
            calc D.q₂ * D.q₁ ^ 2 = D.q₁ ^ 2 * D.q₂ * 1 := by ring
              _ ≤ D.q₁ ^ 2 * D.q₂ * D.q₂ ^ 2 := Nat.mul_le_mul_left _ h2
              _ = D.q₁ ^ 2 * D.q₂ ^ 3 := by ring
    omega

end CFSG.GH74.GLS.Stage4.Rest

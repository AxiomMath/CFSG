module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2Norm2

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42
open scoped Pointwise

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB.L2Ctx

variable {hs : Setting46e t L p f S w z V i j} {W : Subgroup X}

theorem z_comm (hKC : AutPSL2CentralizerInput) (hc : L2Ctx hs W) {g : X} (hg : g ∈ W) :
    g * z = z * g := by
  have hzZW : z ∈ W ⊓ centralizer (W : Set X) := by
    rw [hc.center_eq hKC]
    exact subset_closure (Set.mem_insert_of_mem _ rfl)
  exact (mem_centralizer_iff.mp hzZW.2) g hg

theorem mem_A_cases (hKC : AutPSL2CentralizerInput) (hc : L2Ctx hs W) {x : X}
    (hx : x ∈ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ zpowers z) :
    ∃ q ∈ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W, x = q ∨ x = q * z := by
  have hzN : zpowers z ≤ normalizer
      ((qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W : Subgroup X) : Set X) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      exact hc.qTilde_normal hc.z_mem_W hq
    · intro hq
      have := hc.qTilde_normal (W.inv_mem hc.z_mem_W) hq
      simpa [mul_assoc] using this
  rw [sup_comm] at hx
  have hx' : x ∈ ((zpowers z : Set X) * ((qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W :
      Subgroup X) : Set X)) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ hzN]
    exact hx
  obtain ⟨y, hy, q, hq, rfl⟩ := hx'
  beta_reduce
  rcases eq_one_or_eq_of_mem_zpowers_two hs.setup.z_order hy with h | h
  · exact ⟨q, hq, Or.inl (by rw [h, one_mul])⟩
  · exact ⟨q, hq, Or.inr (by rw [h]; exact (hc.z_comm hKC (hc.qTilde_le hq)).symm)⟩

theorem A_normal (hKC : AutPSL2CentralizerInput) (hc : L2Ctx hs W) {g x : X} (hg : g ∈ W)
    (hx : x ∈ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ zpowers z) :
    g * x * g⁻¹ ∈ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ zpowers z := by
  obtain ⟨q, hq, rfl | rfl⟩ := hc.mem_A_cases hKC hx
  · exact mem_sup_left (hc.qTilde_normal hg hq)
  · have : g * (q * z) * g⁻¹ = (g * q * g⁻¹) * z := by
      rw [show g * (q * z) * g⁻¹ = g * q * (z * g⁻¹) by group,
        ← (hc.z_comm hKC (W.inv_mem hg))]
      group
    rw [this]
    exact mul_mem (mem_sup_left (hc.qTilde_normal hg hq)) (mem_sup_right (mem_zpowers z))

theorem t_comm_z (_hc : L2Ctx hs W) : t * z = z * t :=
  (mem_centralizer_singleton_iff.mp (hs.sylow.le hs.setup.z_mem.1)).symm

theorem mem_A_or_of_mem_N0 (hKC : AutPSL2CentralizerInput) (hc : L2Ctx hs W) {x : X}
    (hx : x ∈ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ closure ({t, z} : Set X)) :
    x ∈ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ zpowers z ∨
      ∃ a ∈ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ zpowers z, x = t * a := by
  have hle : qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ closure ({t, z} : Set X) ≤
      zpowers t ⊔ (qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ zpowers z) := by
    refine sup_le (le_sup_left.trans le_sup_right) ((closure_le _).mpr ?_)
    rintro y (rfl | rfl)
    · exact mem_sup_left (mem_zpowers _)
    · exact mem_sup_right (mem_sup_right (mem_zpowers _))
  have htN : zpowers t ≤ normalizer
      ((qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ zpowers z : Subgroup X) : Set X) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro a
    constructor
    · exact fun ha => hc.A_normal hKC hc.t_mem_W ha
    · intro ha
      have := hc.A_normal hKC (W.inv_mem hc.t_mem_W) ha
      simpa [mul_assoc] using this
  have hx' : x ∈ ((zpowers t : Set X) * ((qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔
      zpowers z : Subgroup X) : Set X)) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ htN]
    exact hle hx
  obtain ⟨y, hy, a, ha, rfl⟩ := hx'
  beta_reduce
  rcases eq_one_or_eq_of_mem_zpowers_two hs.standing.config.orderOf_eq hy with h | h
  · exact Or.inl (by rw [h, one_mul]; exact ha)
  · exact Or.inr ⟨a, ha, by rw [h]⟩

theorem mem_closure_of_comm (hKC : AutPSL2CentralizerInput) (hc : L2Ctx hs W) {a : X}
    (ha : a ∈ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ zpowers z) (hat : a * t = t * a) :
    a ∈ closure ({w ^ (orderOf w / 2) * t ^ i * z ^ j, z} : Set X) := by
  have hβc : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈
      closure ({w ^ (orderOf w / 2) * t ^ i * z ^ j, z} : Set X) :=
    subset_closure (Set.mem_insert _ _)
  have hzc : z ∈ closure ({w ^ (orderOf w / 2) * t ^ i * z ^ j, z} : Set X) :=
    subset_closure (Set.mem_insert_of_mem _ rfl)
  have hqt : ∀ q ∈ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W, q * t = t * q →
      q ∈ closure ({w ^ (orderOf w / 2) * t ^ i * z ^ j, z} : Set X) := fun q hq hqt => by
    have : q ∈ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊓ centralizer ({t} : Set X) :=
      ⟨hq, mem_centralizer_singleton_iff.mpr hqt⟩
    rw [hc.qTilde_inf_centralizer] at this
    exact (zpowers_le.mpr hβc) this
  obtain ⟨q, hq, ha' | ha'⟩ := hc.mem_A_cases hKC ha
  · rw [ha'] at hat ⊢
    exact hqt q hq hat
  · rw [ha'] at hat ⊢
    have htz := hc.t_comm_z
    have hqt' : q * t = t * q := by
      have h1 : q * z * t = t * (q * z) := hat
      calc q * t = q * z * t * z⁻¹ := by rw [mul_assoc q z t, ← htz]; group
        _ = t * (q * z) * z⁻¹ := by rw [h1]
        _ = t * q := by group
    exact mul_mem (hqt q hq hqt') hzc

theorem N0_le_X (hc : L2Ctx hs W)
    (h2 : Nat.card ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) = 2) :
    qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ closure ({t, z} : Set X) ≤
      closure {t, w ^ (orderOf w / 2), z} := by
  have hQ : qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W =
      zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
    refine (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hc.beta_mem_qTilde) ?_).symm
    rw [hc.card_qTilde, h2, hc.card_zpowers_beta]
  rw [hQ]
  refine sup_le (zpowers_le.mpr (beta_mem_X i j)) ((closure_le _).mpr ?_)
  rintro y (rfl | rfl)
  · exact subset_closure (by simp)
  · exact subset_closure (by simp)

theorem card_A_le (hKC : AutPSL2CentralizerInput) (hc : L2Ctx hs W) :
    Nat.card ↥(qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ zpowers z) ≤
      2 * Nat.card ↥(qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W) := by
  classical
  have h := L415.card_le_of_fiber (A := qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔
    zpowers z) (K := qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W)
    (fun x => decide (x ∈ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W)) (fun a ha b hb h => by
      by_cases haQ : a ∈ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W
      · have hbQ : b ∈ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W := by
          simpa [haQ] using h.symm
        exact mul_mem (inv_mem haQ) hbQ
      · have hbQ : b ∉ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W := by
          simpa [haQ] using h.symm
        obtain ⟨q, hq, ea | ea⟩ := hc.mem_A_cases hKC ha
        · exact absurd (ea ▸ hq) haQ
        obtain ⟨q2, hq2, eb | eb⟩ := hc.mem_A_cases hKC hb
        · exact absurd (eb ▸ hq2) hbQ
        rw [ea, eb]
        have : (q * z)⁻¹ * (q2 * z) = z⁻¹ * (q⁻¹ * q2) * z⁻¹⁻¹ := by group
        rw [this]
        exact hc.qTilde_normal (W.inv_mem hc.z_mem_W) (mul_mem (inv_mem hq) hq2))
    ({true, false} : Finset Bool) (fun a _ => by
      rcases Bool.eq_false_or_eq_true
        (decide (a ∈ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W)) with h | h <;> simp [h])
  have h2 : Nat.card ↥((qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ zpowers z) ⊓
      qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W) =
      Nat.card ↥(qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W) := by
    rw [inf_eq_right.mpr le_sup_left]
  rw [h2] at h
  simp at h
  linarith

theorem A_sq (hKC : AutPSL2CentralizerInput) (hc : L2Ctx hs W)
    (hQ2 : ∀ q ∈ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W, q * q = 1) {a : X}
    (ha : a ∈ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ zpowers z) : a * a = 1 := by
  have hz2 : z * z = 1 := by rw [← sq, ← hs.setup.z_order, pow_orderOf_eq_one]
  obtain ⟨q, hq, ea | ea⟩ := hc.mem_A_cases hKC ha
  · rw [ea]; exact hQ2 q hq
  · rw [ea]
    calc q * z * (q * z) = q * (z * q) * z := by group
      _ = q * (q * z) * z := by rw [← hc.z_comm hKC (hc.qTilde_le hq)]
      _ = (q * q) * (z * z) := by group
      _ = 1 := by rw [hQ2 q hq, hz2, one_mul]

theorem eq_X_or_eq_A (hKC : AutPSL2CentralizerInput) (hc : L2Ctx hs W)
    (h4 : Nat.card ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) = 4)
    (hQ2 : ∀ q ∈ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W, q * q = 1) {Y' : Subgroup X}
    (hYN : Y' ≤ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ closure ({t, z} : Set X))
    (hYc : ∀ a ∈ Y', ∀ b ∈ Y', a * b = b * a) (hY2 : ∀ y ∈ Y', y * y = 1)
    (hY8 : Nat.card Y' = 8) :
    Y' = closure {t, w ^ (orderOf w / 2), z} ∨
      Y' = qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ zpowers z := by
  have ht2 : t * t = 1 := by rw [← sq, ← hs.standing.config.orderOf_eq, pow_orderOf_eq_one]
  by_cases hYA : Y' ≤ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ zpowers z
  · right
    refine Subgroup.eq_of_le_of_card_ge hYA ?_
    have := hc.card_A_le hKC
    rw [hc.card_qTilde, h4] at this
    omega
  · left
    have hXc : closure ({w ^ (orderOf w / 2) * t ^ i * z ^ j, z} : Set X) ≤
        closure {t, w ^ (orderOf w / 2), z} := (closure_le _).mpr (by
      rintro x (rfl | rfl)
      · exact beta_mem_X i j
      · exact subset_closure (by simp))
    have htX : t ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
    obtain ⟨y, hyY, hyA⟩ := Set.not_subset.mp hYA
    obtain ⟨a, haA, rfl⟩ : ∃ a ∈ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ zpowers z,
        y = t * a := by
      rcases hc.mem_A_or_of_mem_N0 hKC (hYN hyY) with h | h
      · exact absurd h hyA
      · exact h
    have hAc : ∀ b ∈ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ zpowers z,
        ∀ c ∈ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ zpowers z, b * c = c * b := by
      intro b hb c hc'
      have h1 := hc.A_sq hKC hQ2 (mul_mem hb hc')
      have h2 := hc.A_sq hKC hQ2 hb
      have h3 := hc.A_sq hKC hQ2 hc'
      have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right h2
      have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right h3
      calc b * c = (b * c)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
        _ = c * b := by rw [mul_inv_rev, hbi, hci]
    have hle : Y' ≤ closure {t, w ^ (orderOf w / 2), z} := by
      intro y2 hy2
      rcases hc.mem_A_or_of_mem_N0 hKC (hYN hy2) with h | ⟨a2, ha2, rfl⟩
      ·
        have h1 := hYc _ hy2 _ hyY
        have h2 := hAc _ h _ haA
        have hyt : y2 * t = t * y2 := by
          have : y2 * t * a = t * y2 * a := by
            calc y2 * t * a = y2 * (t * a) := by group
              _ = t * a * y2 := h1
              _ = t * (a * y2) := by group
              _ = t * (y2 * a) := by rw [h2]
              _ = t * y2 * a := by group
          exact mul_right_cancel this
        exact hXc (hc.mem_closure_of_comm hKC h hyt)
      ·
        have h2 := hY2 _ hy2
        have ha2' := hc.A_sq hKC hQ2 ha2
        have h3 : t * a2 * t = a2 := by
          calc t * a2 * t = (t * a2 * (t * a2)) * a2⁻¹ := by group
            _ = a2⁻¹ := by rw [h2, one_mul]
            _ = a2 := inv_eq_of_mul_eq_one_right ha2'
        have hat : a2 * t = t * a2 := by
          calc a2 * t = t * a2 * t * t := by rw [h3]
            _ = t * a2 * (t * t) := by group
            _ = t * a2 := by rw [ht2, mul_one]
        exact mul_mem htX (hXc (hc.mem_closure_of_comm hKC ha2 hat))
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hY8]; exact hs.setup.card_X_le)

theorem X_normal (hKG : AutPSL2SylowInput) (hKC : AutPSL2CentralizerInput)
    (hFC : AutPSL2FieldCentralizerInput) (hc : L2Ctx hs W)
    (h4 : Nat.card ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) = 4)
    (hQ2 : ∀ q ∈ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W, q * q = 1) {g x : X}
    (hg : g ∈ W) (hx : x ∈ closure {t, w ^ (orderOf w / 2), z}) :
    g * x * g⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z} := by
  set Y' := (closure {t, w ^ (orderOf w / 2), z}).map (MulAut.conj g).toMonoidHom with hY'
  have hconj : ∀ y, (MulAut.conj g).toMonoidHom y = g * y * g⁻¹ := fun y => rfl
  have hzc : z ∈ closure ({t, z} : Set X) := subset_closure (Set.mem_insert_of_mem _ rfl)
  have htc : t ∈ closure ({t, z} : Set X) := subset_closure (Set.mem_insert _ _)
  have hXN : closure {t, w ^ (orderOf w / 2), z} ≤
      qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ closure ({t, z} : Set X) := by
    refine (closure_le _).mpr ?_
    rintro y (rfl | rfl | rfl)
    · exact mem_sup_right htc
    ·
      have h1 : (z ^ j)⁻¹ ∈ closure ({t, z} : Set X) := inv_mem (pow_mem hzc j)
      have h2 : (t ^ i)⁻¹ ∈ closure ({t, z} : Set X) := inv_mem (pow_mem htc i)
      have hmem : (w ^ (orderOf w / 2) * t ^ i * z ^ j) * (z ^ j)⁻¹ * (t ^ i)⁻¹ ∈
          qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ closure ({t, z} : Set X) :=
        mul_mem (mul_mem (mem_sup_left hc.beta_mem_qTilde) (mem_sup_right h1))
          (mem_sup_right h2)
      have hu : (w ^ (orderOf w / 2) * t ^ i * z ^ j) * (z ^ j)⁻¹ * (t ^ i)⁻¹ =
          w ^ (orderOf w / 2) := by group
      rw [hu] at hmem
      exact hmem
    · exact mem_sup_right hzc
  have hYN : Y' ≤ qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ closure ({t, z} : Set X) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hconj]
    exact hc.N0_normal hKC hFC hKG hg (hXN hy)
  have hXab : ∀ a ∈ closure {t, w ^ (orderOf w / 2), z},
      ∀ b ∈ closure {t, w ^ (orderOf w / 2), z}, a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.mp (hs.setup.X_le_center_T ha).2 b (hs.setup.X_le_T hb)).symm
  have hYc : ∀ a ∈ Y', ∀ b ∈ Y', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hXab a ha b hb]
  have hY2 : ∀ y ∈ Y', y * y = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← sq, hs.setup.sq_eq_one_of_mem_X hy, map_one]
  have hY8 : Nat.card Y' = 8 := by
    rw [hY', Subgroup.card_map_of_injective (MulAut.conj g).injective, hs.setup.card_X]
  rcases hc.eq_X_or_eq_A hKC h4 hQ2 hYN hYc hY2 hY8 with h | h
  · rw [← h, hY']
    exact ⟨x, hx, rfl⟩
  · exfalso
    have htY : g * t * g⁻¹ ∈ Y' := ⟨t, subset_closure (by simp), rfl⟩
    rw [h] at htY
    have htA := hc.A_normal hKC (W.inv_mem hg) htY
    rw [show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t by group] at htA
    exact hs.setup.not_mem_closure_beta_z (beta_mem_X i j) hs.beta.not_mem
      (hc.mem_closure_of_comm hKC htA rfl)

end EndB.L2Ctx

end CFSG.ComponentClassification.HarrisLit

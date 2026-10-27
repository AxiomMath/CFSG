module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD7Key

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD7

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X} {F : Frame S} {ui : X}

theorem v_mem_S₁ (D : S.Sec6 T₁ F.yF F.kF ui) : D.v ∈ D.S₁ := by
  rw [D.S₁_eq]; exact mem_sup_left (mem_sup_left (mem_sup_left (mem_sup_right (mem_zpowers _))))

theorem w₁_mem_S₁ (D : S.Sec6 T₁ F.yF F.kF ui) : D.w₁ ∈ D.S₁ := by
  rw [D.S₁_eq]; exact mem_sup_left (mem_sup_left (mem_sup_right (mem_zpowers _)))

theorem w₂_mem_S₁ (D : S.Sec6 T₁ F.yF F.kF ui) : D.w₂ ∈ D.S₁ := by
  rw [D.S₁_eq]; exact mem_sup_left (mem_sup_right (mem_zpowers _))

theorem exists_conj_t_mul (D : S.Sec6 T₁ F.yF F.kF ui) (hact : D.act = .one) {e : X}
    (he : e ∈ S.E0 F.yF F.kF) :
    ∃ g ∈ normalizer (S.E F.yF : Set X), (∀ a ∈ S.E0 F.yF F.kF, g * a * g⁻¹ = a) ∧
      g * t * g⁻¹ = t * e := by
  have hA := D.act_holds
  rw [hact] at hA
  obtain ⟨hE0, hv, hw₁, hw₂⟩ := hA
  induction he using closure_induction with
  | mem e he =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl
    · exact ⟨D.w₁, D.S₁_le (w₁_mem_S₁ D), fun a ha => (hE0 a ha).2.1, hw₁⟩
    · exact ⟨D.w₂, D.S₁_le (w₂_mem_S₁ D), fun a ha => (hE0 a ha).2.2, hw₂⟩
    · exact ⟨D.v, D.S₁_le (v_mem_S₁ D), fun a ha => (hE0 a ha).1, hv⟩
  | one => exact ⟨1, one_mem _, fun a _ => by group, by group⟩
  | mul a b ha hb iha ihb =>
    obtain ⟨g₁, hg₁N, hg₁, hg₁t⟩ := iha
    obtain ⟨g₂, hg₂N, hg₂, hg₂t⟩ := ihb
    refine ⟨g₁ * g₂, mul_mem hg₁N hg₂N, fun c hc => ?_, ?_⟩
    · calc g₁ * g₂ * c * (g₁ * g₂)⁻¹ = g₁ * (g₂ * c * g₂⁻¹) * g₁⁻¹ := by group
        _ = c := by rw [hg₂ c hc, hg₁ c hc]
    · calc g₁ * g₂ * t * (g₁ * g₂)⁻¹ = g₁ * (g₂ * t * g₂⁻¹) * g₁⁻¹ := by group
        _ = (g₁ * t * g₁⁻¹) * (g₁ * b * g₁⁻¹) := by rw [hg₂t]; group
        _ = t * (a * b) := by rw [hg₁t, hg₁ b hb, mul_assoc]
  | inv a ha iha =>
    obtain ⟨g, hgN, hg, hgt⟩ := iha
    have hginv : ∀ c ∈ S.E0 F.yF F.kF, g⁻¹ * c * g⁻¹⁻¹ = c := by
      intro c hc
      have := hg c hc
      calc g⁻¹ * c * g⁻¹⁻¹ = g⁻¹ * (g * c * g⁻¹) * g := by rw [this, inv_inv]
        _ = c := by group
    refine ⟨g⁻¹, inv_mem hgN, hginv, ?_⟩
    have h1 : t = g⁻¹ * (t * a) * g := by rw [← hgt]; group
    have h2 : g⁻¹ * a * g = a := by
      have := hginv a ha
      rwa [inv_inv] at this
    calc g⁻¹ * t * g⁻¹⁻¹ = g⁻¹ * t * g := by rw [inv_inv]
      _ = g⁻¹ * t * g * (g⁻¹ * a * g) * a⁻¹ := by rw [h2]; group
      _ = g⁻¹ * (t * a) * g * a⁻¹ := by group
      _ = t * a⁻¹ := by rw [← h1]

theorem not_conjTo_of_mem_E0 (D : S.Sec6 T₁ F.yF F.kF ui) (hact : D.act = .one) {e : X}
    (he : e ∈ S.E0 F.yF F.kF) : ¬ ConjTo t e := by
  classical
  intro hconj
  set B := {f : S.E F.yF // ConjTo t f} with hB
  have hcard : Nat.card B = 8 := D.card_conj
  set φ : S.E0 F.yF F.kF → B := fun f => ⟨⟨t * f, mul_mem (Frame.t_mem_E _) (F.E0_le_E f.2)⟩,
    by obtain ⟨g, -, -, hg⟩ := exists_conj_t_mul D hact f.2; exact ⟨g, hg⟩⟩ with hφ
  have hinj : Function.Injective φ := by
    intro f₁ f₂ hf
    have : t * (f₁ : X) = t * f₂ := congrArg (fun a : B => ((a : S.E F.yF) : X)) hf
    exact Subtype.ext (mul_left_cancel this)
  have hbij : Function.Bijective φ := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [hcard, F.card_E0]
  obtain ⟨f, hf⟩ := hbij.2 ⟨⟨e, F.E0_le_E he⟩, hconj⟩
  have hfe : t * (f : X) = e := congrArg (fun a : B => ((a : S.E F.yF) : X)) hf
  apply F.t_not_mem_E0
  have := mul_mem he (inv_mem f.2)
  rwa [← hfe, mul_inv_cancel_right] at this

theorem conj_mem_L_of_mem_E (D : S.Sec6 T₁ F.yF F.kF ui) (hact : D.act = .one) {n : X}
    (hn : ∀ e ∈ S.E F.yF, n * e * n⁻¹ ∈ S.E F.yF) {e : X} (he : e ∈ S.E F.yF)
    (heL : e ∈ L) : n * e * n⁻¹ ∈ L := by
  have hnt : n * t * n⁻¹ ∈ S.E F.yF := hn t (Frame.t_mem_E _)
  have hf : n * t * n⁻¹ * t ∈ S.E0 F.yF F.kF := by
    rcases F.mem_E0_or hnt with h | h
    · exact absurd ⟨n, rfl⟩ (not_conjTo_of_mem_E0 D hact h)
    · exact h
  have hc : t * (n * t * n⁻¹) = (n * t * n⁻¹) * t :=
    F.elemAbelianTwo_E.comm _ (Frame.t_mem_E _) _ hnt
  have htf : t * (n * t * n⁻¹ * t) = n * t * n⁻¹ := by
    rw [← mul_assoc, hc, mul_assoc, tt (A := A), mul_one]
  obtain ⟨s, hsN, hsE0, hst⟩ := exists_conj_t_mul D hact hf
  rw [htf] at hst
  have hmt : (s⁻¹ * n) * t = t * (s⁻¹ * n) := by
    have h1 : (s⁻¹ * n) * t * (s⁻¹ * n)⁻¹ = t := by
      calc (s⁻¹ * n) * t * (s⁻¹ * n)⁻¹ = s⁻¹ * (n * t * n⁻¹) * s := by group
        _ = s⁻¹ * (s * t * s⁻¹) * s := by rw [hst]
        _ = t := by group
    calc (s⁻¹ * n) * t = (s⁻¹ * n) * t * (s⁻¹ * n)⁻¹ * (s⁻¹ * n) := by group
      _ = t * (s⁻¹ * n) := by rw [h1]
  have hmC : s⁻¹ * n ∈ centralizer ({t} : Set X) := mem_centralizer_singleton_iff.mpr hmt
  have hmE : (s⁻¹ * n) * e * (s⁻¹ * n)⁻¹ ∈ S.E F.yF := by
    have h1 := (mem_normalizer_iff.mp (inv_mem hsN) _).mp (hn e he)
    rwa [show s⁻¹ * (n * e * n⁻¹) * s⁻¹⁻¹ = (s⁻¹ * n) * e * (s⁻¹ * n)⁻¹ by group] at h1
  have hmL : (s⁻¹ * n) * e * (s⁻¹ * n)⁻¹ ∈ L := L2K.conj_mem_L (A := A) hmC heL
  have hmE0 := F.mem_E0_of_mem_L hmE hmL
  have heq : n * e * n⁻¹ = (s⁻¹ * n) * e * (s⁻¹ * n)⁻¹ := by
    calc n * e * n⁻¹ = s * ((s⁻¹ * n) * e * (s⁻¹ * n)⁻¹) * s⁻¹ := by group
      _ = (s⁻¹ * n) * e * (s⁻¹ * n)⁻¹ := hsE0 _ hmE0
  rw [heq]
  exact hmL

namespace Setup

theorem false_of_conj (P : Setup S) {g : X} (hgC : g ∈ centralizer ({t} : Set X))
    (hg₁ : ∀ e ∈ S.E (P.F.xF * P.F.yF), g * e * g⁻¹ ∈ S.E P.F.yF)
    (hg₂ : ∀ e ∈ S.E P.F.yF, g⁻¹ * e * g ∈ S.E (P.F.xF * P.F.yF)) : False := by
  have hn : ∀ e ∈ S.E P.F.yF, (g * P.w₁' * g⁻¹) * e * (g * P.w₁' * g⁻¹)⁻¹ ∈ S.E P.F.yF := by
    intro e he
    have h2 := (mem_normalizer_iff.mp P.w₁'_normalizes _).mp (hg₂ e he)
    have h3 := hg₁ _ h2
    rwa [show g * (P.w₁' * (g⁻¹ * e * g) * P.w₁'⁻¹) * g⁻¹ =
      (g * P.w₁' * g⁻¹) * e * (g * P.w₁' * g⁻¹)⁻¹ by group] at h3
  have he : g * (P.F.xF * P.F.yF) * g⁻¹ ∈ S.E P.F.yF := hg₁ _ (Frame.yi_mem_E _)
  have heL : g * (P.F.xF * P.F.yF) * g⁻¹ ∈ L := L2K.conj_mem_L (A := A) hgC P.F.xyF_mem_R.2
  have h := conj_mem_L_of_mem_E P.D P.act_one hn he heL
  rw [show (g * P.w₁' * g⁻¹) * (g * (P.F.xF * P.F.yF) * g⁻¹) * (g * P.w₁' * g⁻¹)⁻¹ =
    g * (P.w₁' * (P.F.xF * P.F.yF) * P.w₁'⁻¹) * g⁻¹ by group] at h
  apply P.w₁'_xy_not_mem_L
  have := L2K.conj_mem_L (A := A) (inv_mem hgC) h
  rwa [show g⁻¹ * (g * (P.w₁' * (P.F.xF * P.F.yF) * P.w₁'⁻¹) * g⁻¹) * g⁻¹⁻¹ =
    P.w₁' * (P.F.xF * P.F.yF) * P.w₁'⁻¹ by group] at this

end Setup

variable (S)

theorem false_of_side₁ (D₁ : S.Sec6 T₁ S.y S.k (S.x * S.y))
    (hq : D₁.q0 = .e4q8 ∨ D₁.q0 = .exceptional) : False := by
  let P : Setup S :=
    { F := frame₁ S
      T₁ := T₁
      ui := S.x * S.y
      hui := Or.inl rfl
      D := D₁
      hq := hq }
  refine P.false_of_conj (g := C.d⁻¹) (inv_mem (L2KD.d_mem_C C)) (fun e he => ?_)
    (fun e he => ?_)
  · rw [inv_inv]
    exact d_inv_conj_E₂ S he
  · rw [inv_inv]
    exact d_conj_E₁ S he

theorem false_of_side₂ (D₂ : S.Sec6 T₁ (S.x * S.y) (S.z * S.k) (S.z * S.y))
    (hq : D₂.q0 = .e4q8 ∨ D₂.q0 = .exceptional) : False := by
  have e1 : (frame₂ S).xF * (frame₂ S).yF = S.y := inv_mul_cancel_left _ _
  let P : Setup S :=
    { F := frame₂ S
      T₁ := T₁
      ui := S.z * S.y
      hui := Or.inr (by rw [e1])
      D := D₂
      hq := hq }
  refine P.false_of_conj (g := C.d) (L2KD.d_mem_C C) (fun e he => ?_) (fun e he => ?_)
  · have he' : e ∈ S.E S.y := by
      have : e ∈ S.E ((frame₂ S).xF * (frame₂ S).yF) := he
      rwa [e1] at this
    exact d_conj_E₁ S he'
  · have := d_inv_conj_E₂ S he
    show C.d⁻¹ * e * C.d ∈ S.E ((frame₂ S).xF * (frame₂ S).yF)
    rw [e1]
    exact this

end KD7

theorem fritzKDSection7 : FritzKDSection7 := by
  intro _ X _ _ _ _ _ t L A C S T₁ _ D₁ D₂ hq
  rcases hq with h | h | h | h
  · exact KD7.false_of_side₁ S D₁ (Or.inl h)
  · exact KD7.false_of_side₁ S D₁ (Or.inr h)
  · exact KD7.false_of_side₂ S D₂ (Or.inl h)
  · exact KD7.false_of_side₂ S D₂ (Or.inr h)

end CFSG.ComponentClassification.HSFLit

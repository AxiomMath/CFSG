module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2F6

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ} {t : G}
  {M₀ : Subgroup G} {x₀ : G} {q : ℕ} {W : Subgroup G}

omit [Finite G] in
theorem sq_proj_gen {X Y E : Subgroup G} (hXY : ∀ a ∈ X, ∀ b ∈ Y, a * b = b * a) (hbot : X ⊓ Y = ⊥)
    (hEN : E ≤ Subgroup.normalizer (Y : Set G)) (hsq : ∀ e ∈ E, e * e = 1) :
    ∀ f ∈ (E ⊔ Y) ⊓ X, f * f = 1 := by
  rintro f ⟨hf, hfX⟩
  rw [sup_comm] at hf
  obtain ⟨k, hk, e, he, hfe⟩ := (mem_sup_iff_of_le_normalizer hEN).1 hf
  have hfk : f * k⁻¹ = k⁻¹ * f := hXY f hfX k⁻¹ (Y.inv_mem hk)
  have hee : (k⁻¹ * f) * (k⁻¹ * f) = 1 := by
    have : k⁻¹ * f = e := by rw [hfe]; group
    rw [this]
    exact hsq e he
  have hprod : (f * f) * (k⁻¹ * k⁻¹) = 1 * 1 := by
    calc (f * f) * (k⁻¹ * k⁻¹) = f * (f * k⁻¹) * k⁻¹ := by group
      _ = f * (k⁻¹ * f) * k⁻¹ := by rw [hfk]
      _ = (f * k⁻¹) * (f * k⁻¹) := by group
      _ = (k⁻¹ * f) * (k⁻¹ * f) := by rw [hfk]
      _ = 1 * 1 := by rw [hee, one_mul]
  exact (exists_unique_of_inf_bot hbot (X.mul_mem hfX hfX) X.one_mem
    (Y.mul_mem (Y.inv_mem hk) (Y.inv_mem hk)) Y.one_mem hprod).1

namespace S2Base

variable (B : S2Base T M H S L D n t M₀ x₀ q W)
include B

theorem sup_decomp {A₁ A₂ : Subgroup G} (h₁ : A₁ ≤ L) (h₂ : A₂ ≤ conjR L t) :
    ∀ e ∈ A₁ ⊔ A₂, ∃ a₁ ∈ A₁, ∃ a₂ ∈ A₂, e = a₁ * a₂ := fun _ he =>
  (mem_sup_iff_of_le_normalizer (le_normalizer_of_commute fun a ha b hb =>
    B.comm_elem a (h₁ ha) b (h₂ hb))).1 he

theorem sup_inf_L {A₁ A₂ : Subgroup G} (h₁ : A₁ ≤ L) (h₂ : A₂ ≤ conjR L t) :
    (A₁ ⊔ A₂) ⊓ L = A₁ :=
  sup_inf_left_of_commute B.comm_elem B.L_inf_L₂ h₁ h₂

theorem sup_inf_L₂ {A₁ A₂ : Subgroup G} (h₁ : A₁ ≤ L) (h₂ : A₂ ≤ conjR L t) :
    (A₁ ⊔ A₂) ⊓ conjR L t = A₂ :=
  sup_inf_right_of_commute B.comm_elem B.L_inf_L₂ h₁ h₂

theorem card_sup_L {A₁ A₂ : Subgroup G} (h₁ : A₁ ≤ L) (h₂ : A₂ ≤ conjR L t) :
    Nat.card ↥(A₁ ⊔ A₂) = Nat.card A₁ * Nat.card A₂ := by
  have hN : A₂ ≤ Subgroup.normalizer (A₁ : Set G) :=
    le_normalizer_of_commute fun a ha b hb => B.comm_elem a (h₁ ha) b (h₂ hb)
  have h := card_sup_mul_card_inf hN
  have hbot : A₂ ⊓ A₁ = ⊥ := by
    rw [eq_bot_iff, ← B.L_inf_L₂, inf_comm]
    exact inf_le_inf h₁ h₂
  rw [hbot, Subgroup.card_bot, mul_one, sup_comm] at h
  rw [h, mul_comm]

theorem sq_sup {A₁ A₂ : Subgroup G} (h₁ : A₁ ≤ L) (h₂ : A₂ ≤ conjR L t)
    (hs₁ : ∀ a ∈ A₁, a * a = 1) (hs₂ : ∀ a ∈ A₂, a * a = 1) : ∀ e ∈ A₁ ⊔ A₂, e * e = 1 := by
  intro e he
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := B.sup_decomp h₁ h₂ e he
  have hc : a₂ * a₁ = a₁ * a₂ := (B.comm_elem a₁ (h₁ ha₁) a₂ (h₂ ha₂)).symm
  calc a₁ * a₂ * (a₁ * a₂) = a₁ * (a₂ * a₁) * a₂ := by group
    _ = a₁ * (a₁ * a₂) * a₂ := by rw [hc]
    _ = (a₁ * a₁) * (a₂ * a₂) := by group
    _ = 1 := by rw [hs₁ a₁ ha₁, hs₂ a₂ ha₂, one_mul]

theorem sup_inj {A₁ A₂ A₁' A₂' : Subgroup G}
    (h₁ : A₁ ≤ L) (h₂ : A₂ ≤ conjR L t) (h₁' : A₁' ≤ L) (h₂' : A₂' ≤ conjR L t)
    (h : A₁ ⊔ A₂ = A₁' ⊔ A₂') : A₁ = A₁' ∧ A₂ = A₂' := by
  refine ⟨?_, ?_⟩
  · rw [← B.sup_inf_L h₁ h₂, h, B.sup_inf_L h₁' h₂']
  · rw [← B.sup_inf_L₂ h₁ h₂, h, B.sup_inf_L₂ h₁' h₂']

end S2Base

namespace S2Ok

variable {D₁ D₂ : Subgroup G} (O : S2Ok T M H S L D n t M₀ x₀ q W D₁ D₂)
include O

theorem max_R_card {E : Subgroup G} (hE : IsMaxElemAbelian (thompsonJ S) E) :
    Nat.card E = q ^ 4 := by
  have hB := O.base
  have hRS : thompsonJ S ≤ S := GammaExtra.thompsonJ_le_self S
  have h1 : Nat.card E ≤ q ^ 4 := by
    have := O.isMax_Q.2.2 E (hE.1.trans hRS) hE.2.1
    rwa [O.card_Q] at this
  have hQR : blockU L ⊔ conjR (blockU L) t ≤ thompsonJ S := by
    refine sup_le hB.U₁_le_R ?_
    rw [← DoubleA3.blockU_conjR]
    exact hB.U₂_le_R
  have h2 := hE.2.2 (blockU L ⊔ conjR (blockU L) t) hQR O.isMax_Q.2.1
  rw [O.card_Q] at h2
  exact le_antisymm h1 h2

theorem max_R_cases {E : Subgroup G} (hE : IsMaxElemAbelian (thompsonJ S) E) :
    ∃ A₁ A₂ : Subgroup G, (A₁ = blockU L ∨ A₁ = conjR (blockU L) x₀) ∧
      (A₂ = blockU (conjR L t) ∨ A₂ = conjR (blockU (conjR L t)) x₀) ∧ E = A₁ ⊔ A₂ := by
  have hB := O.base
  have hcard := O.max_R_card hE
  have hsq : ∀ e ∈ E, e * e = 1 := sq_of_isElemAbelian hE.2.1
  have hER : E ≤ thompsonJ S := hE.1
  have hR₁N₂ : thompsonJ S ⊓ L ≤
      Subgroup.normalizer ((thompsonJ S ⊓ conjR L t : Subgroup G) : Set G) :=
    le_normalizer_of_commute fun x hx y hy => (hB.comm_elem y hy.2 x hx.2).symm
  have hR₂N₁ : thompsonJ S ⊓ conjR L t ≤
      Subgroup.normalizer ((thompsonJ S ⊓ L : Subgroup G) : Set G) := hB.R₂_le_normalizer_R₁
  have hEN₂ : E ≤ Subgroup.normalizer ((thompsonJ S ⊓ conjR L t : Subgroup G) : Set G) := by
    intro r hr
    obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := O.R_decomp' (hER hr)
    exact mul_mem (hR₁N₂ hr₁) (Subgroup.le_normalizer hr₂)
  have hEN₁ : E ≤ Subgroup.normalizer ((thompsonJ S ⊓ L : Subgroup G) : Set G) := by
    intro r hr
    obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := O.R_decomp' (hER hr)
    exact mul_mem (Subgroup.le_normalizer hr₁) (hR₂N₁ hr₂)
  have hsq₁ := sq_proj_gen (X := thompsonJ S ⊓ L) (Y := thompsonJ S ⊓ conjR L t) (E := E)
    (fun a ha b hb => hB.comm_elem a ha.2 b hb.2) hB.R₁_inf_R₂ hEN₂ hsq
  have hsq₂ := sq_proj_gen (X := thompsonJ S ⊓ conjR L t) (Y := thompsonJ S ⊓ L) (E := E)
    (fun a ha b hb => (hB.comm_elem b hb.2 a ha.2).symm) (by rw [inf_comm]; exact hB.R₁_inf_R₂)
    hEN₁ hsq
  set F₁ := (E ⊔ (thompsonJ S ⊓ conjR L t)) ⊓ (thompsonJ S ⊓ L) with hF₁
  set F₂ := (E ⊔ (thompsonJ S ⊓ L)) ⊓ (thompsonJ S ⊓ conjR L t) with hF₂
  have hF₁L : F₁ ≤ L := inf_le_right.trans inf_le_right
  have hF₂L : F₂ ≤ conjR L t := inf_le_right.trans inf_le_right
  have hEF : E ≤ F₁ ⊔ F₂ := by
    intro e he
    obtain ⟨r₁, hr₁, r₂, hr₂, hdec⟩ := O.R_decomp' (hER he)
    have h1 : r₁ ∈ F₁ := by
      refine ⟨?_, hr₁⟩
      have : r₁ = e * r₂⁻¹ := by rw [hdec]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left he) (Subgroup.inv_mem _
        (Subgroup.mem_sup_right hr₂))
    have h2 : r₂ ∈ F₂ := by
      refine ⟨?_, hr₂⟩
      have hc : r₁ * r₂ = r₂ * r₁ := hB.comm_elem r₁ hr₁.2 r₂ hr₂.2
      have : r₂ = r₁⁻¹ * e := by rw [hdec]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_right hr₁))
        (Subgroup.mem_sup_left he)
    rw [hdec]
    exact (F₁ ⊔ F₂).mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)
  have hc₁ : Nat.card F₁ ≤ q ^ 2 := O.UT3_R₁.card_le_sq inf_le_right hsq₁
  have hc₂ : Nat.card F₂ ≤ q ^ 2 := O.UT3_R₂.card_le_sq inf_le_right hsq₂
  have hcardF : Nat.card ↥(F₁ ⊔ F₂) = Nat.card F₁ * Nat.card F₂ := hB.card_sup_L hF₁L hF₂L
  have hle : q ^ 4 ≤ Nat.card F₁ * Nat.card F₂ := by
    rw [← hcardF, ← hcard]
    exact Subgroup.card_le_of_le hEF
  have hq2 : 0 < q ^ 2 := pow_pos (lt_of_lt_of_le (by norm_num) hB.su.loc.q2) 2
  have hF₁c : Nat.card F₁ = q ^ 2 := by
    by_contra hne
    have hlt : Nat.card F₁ < q ^ 2 := lt_of_le_of_ne hc₁ hne
    have : Nat.card F₁ * Nat.card F₂ < q ^ 2 * q ^ 2 :=
      Nat.mul_lt_mul_of_lt_of_le hlt hc₂ hq2
    nlinarith
  have hF₂c : Nat.card F₂ = q ^ 2 := by
    by_contra hne
    have hlt : Nat.card F₂ < q ^ 2 := lt_of_le_of_ne hc₂ hne
    have : Nat.card F₁ * Nat.card F₂ < q ^ 2 * q ^ 2 :=
      Nat.mul_lt_mul_of_le_of_lt hc₁ hlt hq2
    nlinarith
  have hEeq : E = F₁ ⊔ F₂ := by
    refine Subgroup.eq_of_le_of_card_ge hEF ?_
    rw [hcardF, hF₁c, hF₂c, hcard]
    ring_nf
    exact le_rfl
  refine ⟨F₁, F₂, ?_, ?_, hEeq⟩
  · exact O.UT3_R₁.eq_of_card inf_le_right hsq₁ hF₁c
  · exact O.UT3_R₂.eq_of_card inf_le_right hsq₂ hF₂c

theorem sup_isMax_R {A₁ A₂ : Subgroup G} (h₁ : A₁ = blockU L ∨ A₁ = conjR (blockU L) x₀)
    (h₂ : A₂ = blockU (conjR L t) ∨ A₂ = conjR (blockU (conjR L t)) x₀) :
    IsMaxElemAbelian (thompsonJ S) (A₁ ⊔ A₂) := by
  have hB := O.base
  have hRS : thompsonJ S ≤ S := GammaExtra.thompsonJ_le_self S
  have hA₁ : A₁ ≤ thompsonJ S ⊓ L ∧ (∀ a ∈ A₁, a * a = 1) ∧ Nat.card A₁ = q ^ 2 := by
    rcases h₁ with rfl | rfl
    · exact ⟨O.UT3_R₁.U_le_R, O.UT3_R₁.sq₁, O.UT3_R₁.card_U⟩
    · exact ⟨O.UT3_R₁.U'_le_R, O.UT3_R₁.sq₂, O.UT3_R₁.card_U'⟩
  have hA₂ : A₂ ≤ thompsonJ S ⊓ conjR L t ∧ (∀ a ∈ A₂, a * a = 1) ∧ Nat.card A₂ = q ^ 2 := by
    rcases h₂ with rfl | rfl
    · exact ⟨O.UT3_R₂.U_le_R, O.UT3_R₂.sq₁, O.UT3_R₂.card_U⟩
    · exact ⟨O.UT3_R₂.U'_le_R, O.UT3_R₂.sq₂, O.UT3_R₂.card_U'⟩
  have hc : Nat.card ↥(A₁ ⊔ A₂) = q ^ 4 := by
    rw [hB.card_sup_L (hA₁.1.trans inf_le_right) (hA₂.1.trans inf_le_right), hA₁.2.2, hA₂.2.2]
    ring
  have hsq := hB.sq_sup (hA₁.1.trans inf_le_right) (hA₂.1.trans inf_le_right) hA₁.2.1 hA₂.2.1
  refine ⟨sup_le (hA₁.1.trans inf_le_left) (hA₂.1.trans inf_le_left), isElemAbelian_of_sq hsq,
    fun B' hB'R hB'e => ?_⟩
  have := O.isMax_Q.2.2 B' (hB'R.trans hRS) hB'e
  rwa [O.card_Q, ← hc] at this

theorem U₁_ne_U₁' : blockU L ≠ conjR (blockU L) x₀ := by
  have hB := O.base
  intro h
  have h1 : blockU L ⊓ conjR (blockU L) x₀ = W := O.UT3_R₁.inf_eq
  rw [← h, inf_idem] at h1
  have h2 := O.UT3_R₁.card_U
  have h3 := O.UT3_R₁.card_W
  rw [h1, h3] at h2
  have hq := hB.su.loc.q2
  nlinarith

theorem U₂_ne_U₂' : blockU (conjR L t) ≠ conjR (blockU (conjR L t)) x₀ := by
  have hB := O.base
  intro h
  have h1 : blockU (conjR L t) ⊓ conjR (blockU (conjR L t)) x₀ = conjR W t :=
    O.UT3_R₂.inf_eq
  rw [← h, inf_idem] at h1
  have h2 := O.UT3_R₂.card_U
  have h3 := O.UT3_R₂.card_W
  rw [h1, h3] at h2
  have hq := hB.su.loc.q2
  nlinarith

theorem ncard_maxElemAbelian_R :
    Set.ncard {A : Subgroup G | IsMaxElemAbelian (thompsonJ S) A} = 4 := by
  have hB := O.base
  have hU₁L : blockU L ≤ L := blockU_le L
  have hU₁'L : conjR (blockU L) x₀ ≤ L := O.UT3_R₁.U'_le_R.trans inf_le_right
  have hU₂L : blockU (conjR L t) ≤ conjR L t := blockU_le _
  have hU₂'L : conjR (blockU (conjR L t)) x₀ ≤ conjR L t := O.UT3_R₂.U'_le_R.trans inf_le_right
  have hne₁ := O.U₁_ne_U₁'
  have hne₂ := O.U₂_ne_U₂'
  have hset : {A : Subgroup G | IsMaxElemAbelian (thompsonJ S) A} =
      {blockU L ⊔ blockU (conjR L t), blockU L ⊔ conjR (blockU (conjR L t)) x₀,
        conjR (blockU L) x₀ ⊔ blockU (conjR L t),
        conjR (blockU L) x₀ ⊔ conjR (blockU (conjR L t)) x₀} := by
    ext A
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hA
      obtain ⟨A₁, A₂, h₁, h₂, rfl⟩ := O.max_R_cases hA
      rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;> simp
    · rintro (rfl | rfl | rfl | rfl)
      · exact O.sup_isMax_R (Or.inl rfl) (Or.inl rfl)
      · exact O.sup_isMax_R (Or.inl rfl) (Or.inr rfl)
      · exact O.sup_isMax_R (Or.inr rfl) (Or.inl rfl)
      · exact O.sup_isMax_R (Or.inr rfl) (Or.inr rfl)
  rw [hset]
  have d12 : blockU L ⊔ blockU (conjR L t) ≠ blockU L ⊔ conjR (blockU (conjR L t)) x₀ := fun h =>
    hne₂ (hB.sup_inj hU₁L hU₂L hU₁L hU₂'L h).2
  have d13 : blockU L ⊔ blockU (conjR L t) ≠ conjR (blockU L) x₀ ⊔ blockU (conjR L t) := fun h =>
    hne₁ (hB.sup_inj hU₁L hU₂L hU₁'L hU₂L h).1
  have d14 : blockU L ⊔ blockU (conjR L t) ≠
      conjR (blockU L) x₀ ⊔ conjR (blockU (conjR L t)) x₀ := fun h =>
    hne₁ (hB.sup_inj hU₁L hU₂L hU₁'L hU₂'L h).1
  have d23 : blockU L ⊔ conjR (blockU (conjR L t)) x₀ ≠ conjR (blockU L) x₀ ⊔ blockU (conjR L t) :=
    fun h => hne₁ (hB.sup_inj hU₁L hU₂'L hU₁'L hU₂L h).1
  have d24 : blockU L ⊔ conjR (blockU (conjR L t)) x₀ ≠
      conjR (blockU L) x₀ ⊔ conjR (blockU (conjR L t)) x₀ := fun h =>
    hne₁ (hB.sup_inj hU₁L hU₂'L hU₁'L hU₂'L h).1
  have d34 : conjR (blockU L) x₀ ⊔ blockU (conjR L t) ≠
      conjR (blockU L) x₀ ⊔ conjR (blockU (conjR L t)) x₀ := fun h =>
    hne₂ (hB.sup_inj hU₁'L hU₂L hU₁'L hU₂'L h).2
  rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair d34]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨d23, d24⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨d12, d13, d14⟩

end S2Ok

end CFSG.QuasithinUnique.Lin2

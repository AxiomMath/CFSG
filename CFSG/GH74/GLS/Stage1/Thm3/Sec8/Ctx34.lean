module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx33
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx32

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem card_Q₂_W₂_e2 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (he : (Pz S z).relIndex (S1 S K₁) = 4)
    (hP8 : Nat.card ↥(Pof S K₁) = 8) : Nat.card ↥(Qof S K₂) = 2 ^ 4 ∧ Nat.card ↥W₂ = 8 := by
  obtain ⟨e, he', hri, hNN, hq1, hq2⟩ := hs.lemma82_core hII hq hrec
  have he2 : e = 2 := by omega
  subst he2
  have h1 := hs.card_W₂ hII
  constructor
  · rw [hq2, hP8]
    norm_num
  · omega

theorem exists_q₂ (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (he : (Pz S z).relIndex (S1 S K₁) = 4)
    (hP8 : Nat.card ↥(Pof S K₁) = 8) {y₁ y₂ : G} (hy₁P : y₁ ∈ Pof S K₁) (hy₂P : y₂ ∈ Pof S K₂)
    (hy₁V : y₁ ∉ Vof S K₁ W₂) :
    ∃ q₂ ∈ W₂, W₂ = zpowers q₂ ∧ orderOf q₂ = 8 ∧ y₁ * q₂ * y₁⁻¹ = q₂⁻¹ ∧ y₂ * q₂ * y₂⁻¹ = q₂ := by
  obtain ⟨hQ16, hW8⟩ := hs.card_Q₂_W₂_e2 hII hq hrec he hP8
  obtain ⟨q₂, hq₂W, hgen⟩ := Basic.exists_generator_of_cyclic hs.W₂_max.2.1
  have hq₂o : orderOf q₂ = 8 := by
    have h := hW8
    rw [hgen, Nat.card_zpowers] at h
    exact h
  have hy₁Q : y₁ ∈ Qof S K₂ := hs.P₁_le_Q₂ hII hy₁P
  have hy₁W : y₁ ∉ W₂ := fun h' => hy₁V (Subgroup.mem_inf.2 ⟨h', hy₁P⟩)
  have hcard := hs.card_W₂ hII
  have hout := (hs.gq_Q₂ hII).outside_cyclic hQ16 hs.W₂_max.1 hs.W₂_max.2.1 (by omega) (by omega)
    hy₁Q hy₁W
  have hcomm : q₂ * y₂ = y₂ * q₂ :=
    hs.Q_comm_P hII (Or.inr rfl) q₂ (hs.W₂_le_Q₂ hq₂W) y₂ hy₂P
  refine ⟨q₂, hq₂W, hgen, hq₂o, hout.2 q₂ hq₂W, ?_⟩
  rw [← hcomm]
  group

theorem exists_invol_outside_e2 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (he : (Pz S z).relIndex (S1 S K₁) = 4)
    (hSne : S ≠ S1 S K₁) (hP8 : Nat.card ↥(Pof S K₁) = 8) :
    ∃ d ∈ S, d ∉ S1 S K₁ ∧ d * d = 1 := by
  have hV := hs.card_V₁ hII hq
  have hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1) := by norm_num; omega
  have hk2 : 2 ≤ 1 + 1 := le_refl _
  obtain ⟨y₁, hy₁P, hy₁sq, hy₁inv, hy₁V⟩ := hs.exists_y₁ hII hq hk
  obtain ⟨y₂, hy₂P, hy₂sq, hy₂inv, -⟩ := hs.exists_y₂ hII hq hrec hk
  obtain ⟨q₂, hq₂W, hgen, hq₂o, hy₁q₂, hy₂q₂⟩ := hs.exists_q₂ hII hq hrec he hP8 hy₁P hy₂P hy₁V
  have hyW : y₁ * y₂ ∈ Wsub S U := hs.y_mem_W hII hq hy₁P hy₂P hy₁inv hy₂inv
  have hyV₁ := hs.y_inv_V₁ hII hy₂P hy₁inv
  have hyA : y₁ * y₂ ∉ Aof S K₁ W₂ h := hs.not_mem_A_of_inv hII hq hrec hyV₁
  have hy2 : (y₁ * y₂) * (y₁ * y₂) = 1 := hs.y_sq hII hy₁P hy₂P hy₁sq hy₂sq
  have hyS1 : y₁ * y₂ ∈ S1 S K₁ :=
    mul_mem (hs.P_le_S1 hII (Or.inl rfl) hy₁P) (hs.P_le_S1 hII (Or.inr rfl) hy₂P)
  have hyq : (y₁ * y₂) * q₂ * (y₁ * y₂)⁻¹ = q₂⁻¹ := by
    calc (y₁ * y₂) * q₂ * (y₁ * y₂)⁻¹ = y₁ * (y₂ * q₂ * y₂⁻¹) * y₁⁻¹ := by group
      _ = y₁ * q₂ * y₁⁻¹ := by rw [hy₂q₂]
      _ = q₂⁻¹ := hy₁q₂
  have hAW₀ : Aof S K₁ W₂ h ≤ Wsub S U ⊓ S1 S K₁ :=
    le_inf (hs.A_le_W hII hq hrec hk2 hk) (hs.A_le_S1 hII hq hrec)
  have hq₂W₀ : q₂ ∈ Wsub S U ⊓ S1 S K₁ :=
    Subgroup.mem_inf.2 ⟨hs.W₂_le_W hII hq hq₂W, hs.Q₂_le_S1 hII (hs.W₂_le_Q₂ hq₂W)⟩
  have hq₂A : q₂ ∉ Aof S K₁ W₂ h := by
    intro hA
    have h4 : q₂ ^ 4 = 1 := by
      rw [Basic.pow_four_eq]
      exact hs.A_pow_four hII hq hrec hk hA
    have h5 := orderOf_dvd_of_pow_eq_one h4
    rw [hq₂o] at h5
    have := Nat.le_of_dvd (by norm_num) h5
    omega
  have hcV : ∀ c ∈ Vof S K₁ W₂, q₂ * c = c * q₂ := fun c hc =>
    Basic.cyclic_comm hs.W₂_max.2.1 q₂ hq₂W c hc.1
  have hcard : Nat.card ↥(Wsub S U ⊓ S1 S K₁) ≤ 4 * Nat.card ↥(Aof S K₁ W₂ h) := by
    have hr2 := hs.relIndex_W₀_S1 hII hq hy₁P hy₁inv
    have hmul : Nat.card ↥(Wsub S U ⊓ S1 S K₁) * (Wsub S U ⊓ S1 S K₁).relIndex (S1 S K₁) =
        Nat.card ↥(S1 S K₁) := Basic.card_mul_relIndex_of_le inf_le_right
    rw [hr2] at hmul
    obtain ⟨-, hS1c⟩ := hs.card_S1 hII
    rw [he] at hS1c
    have hPc := hs.card_P hII
    obtain ⟨e, -, -, hNN, -⟩ := hs.lemma82_core hII hq hrec
    have hAc := hs.card_A hII hq hrec hk
    norm_num at hAc
    rw [← hNN, hP8] at hPc
    omega
  generalize hy : y₁ * y₂ = y at hyW hyV₁ hyA hy2 hyS1 hyq
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hyW₀ : y ∈ Wsub S U ⊓ S1 S K₁ := Subgroup.mem_inf.2 ⟨hyW, hyS1⟩
  have e1 : y * q₂ * y = q₂⁻¹ := by
    have := hyq
    rwa [hyinv] at this
  have hg2 : (y * q₂) * (y * q₂) = 1 := by
    calc (y * q₂) * (y * q₂) = (y * q₂ * y) * q₂ := by group
      _ = q₂⁻¹ * q₂ := by rw [e1]
      _ = 1 := by group
  have hgW : y * q₂ ∈ Wsub S U := mul_mem hyW (hs.W₂_le_W hII hq hq₂W)
  have hgW₀ : y * q₂ ∈ Wsub S U ⊓ S1 S K₁ := mul_mem hyW₀ hq₂W₀
  have hgV₁ : ∀ c ∈ Vof S K₁ W₂, (y * q₂) * c * (y * q₂)⁻¹ = c⁻¹ := by
    intro c hc
    have h1 : q₂ * c * q₂⁻¹ = c := by rw [hcV c hc]; group
    calc (y * q₂) * c * (y * q₂)⁻¹ = y * (q₂ * c * q₂⁻¹) * y⁻¹ := by group
      _ = y * c * y⁻¹ := by rw [h1]
      _ = c⁻¹ := hyV₁ c hc
  have hgA : y * q₂ ∉ Aof S K₁ W₂ h := hs.not_mem_A_of_inv hII hq hrec hgV₁
  have hygA : y⁻¹ * (y * q₂) ∉ Aof S K₁ W₂ h := by
    have e : y⁻¹ * (y * q₂) = q₂ := by group
    rw [e]
    exact hq₂A
  have hnA : ∀ w ∈ Wsub S U ⊓ S1 S K₁, ∀ a ∈ Aof S K₁ W₂ h, w * a * w⁻¹ ∈ Aof S K₁ W₂ h :=
    fun w hw a ha => hs.A_normS hII hq hrec hw.1.1 ha
  have hcomm : ∀ w ∈ Wsub S U ⊓ S1 S K₁, ∀ w' ∈ Wsub S U ⊓ S1 S K₁,
      w * w' * w⁻¹ * w'⁻¹ ∈ Aof S K₁ W₂ h :=
    fun w hw w' hw' => hs.W_comm_mem_A hII hq hrec hk hw.1 hw'.1
  by_cases hψy : h⁻¹ * y * h ∈ Wsub S U ⊓ S1 S K₁
  · by_cases hψg : h⁻¹ * (y * q₂) * h ∈ Wsub S U ⊓ S1 S K₁
    · have hT := Basic.sup_eq_of_card_le hAW₀ hyW₀ hgW₀ hy2 hg2 hyA hgA hygA hnA hcomm hcard
      have hψW₀ : ∀ v ∈ Wsub S U ⊓ S1 S K₁, h⁻¹ * v * h ∈ Wsub S U ⊓ S1 S K₁ := by
        intro v hv
        rw [← hT] at hv
        let ψ : G →* G := MonoidHom.mk' (fun g => h⁻¹ * g * h) (by intro a b; group)
        have hle : Aof S K₁ W₂ h ⊔ zpowers y ⊔ zpowers (y * q₂) ≤
            (Wsub S U ⊓ S1 S K₁).comap ψ := by
          refine sup_le (sup_le ?_ ?_) ?_
          · intro a ha
            exact hAW₀ (hs.A_conj hII hq hrec hk ha).2
          · rw [zpowers_le]
            exact hψy
          · rw [zpowers_le]
            exact hψg
        exact hle hv
      exact hs.exists_invol_of_psi_inv hII hq hrec hSne hk hψW₀
    · refine ⟨h⁻¹ * (y * q₂) * h, (hs.W_conj_h hgW).1,
        fun hd => hψg (Subgroup.mem_inf.2 ⟨hs.W_conj_h hgW, hd⟩), ?_⟩
      calc h⁻¹ * (y * q₂) * h * (h⁻¹ * (y * q₂) * h)
          = h⁻¹ * ((y * q₂) * (y * q₂)) * h := by group
        _ = 1 := by rw [hg2]; group
  · refine ⟨h⁻¹ * y * h, (hs.W_conj_h hyW).1,
      fun hd => hψy (Subgroup.mem_inf.2 ⟨hs.W_conj_h hyW, hd⟩), ?_⟩
    calc h⁻¹ * y * h * (h⁻¹ * y * h) = h⁻¹ * (y * y) * h := by group
      _ = 1 := by rw [hy2]; group

theorem exists_invol_outside (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hP8 : Nat.card ↥(Pof S K₁) = 8) (hSne : S ≠ S1 S K₁) :
    ∃ d ∈ S, d ∉ S1 S K₁ ∧ d * d = 1 := by
  have hV := hs.card_V₁ hII hq
  have hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1) := by norm_num; omega
  obtain ⟨e, he, hri, -⟩ := hs.lemma82_core hII hq hrec
  rcases he with rfl | rfl
  · exact hs.exists_invol_outside_e1 hII hq hrec (by omega) hSne hk
  · exact hs.exists_invol_outside_e2 hII hq hrec (by omega) hSne hP8

theorem rank_ge_four_of_ne (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hP8 : Nat.card ↥(Pof S K₁) = 8) (hSne : S ≠ S1 S K₁) :
    4 ≤ CFSG.pRank 2 G := by
  obtain ⟨d, hdS, hdn, hd2⟩ := hs.exists_invol_outside hII hq hrec hP8 hSne
  exact hs.rank_ge_four_of_swap hII hq hP8 hdS hdn hd2

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8

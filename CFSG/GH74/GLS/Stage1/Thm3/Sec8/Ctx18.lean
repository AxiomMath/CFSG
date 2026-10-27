module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx17
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx15

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem card_A (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) :
    Nat.card ↥(Aof S K₁ W₂ h) = 2 ^ k * 2 ^ k := by
  have hVV : Vof S K₁ W₂ ⊓ conjugate (Vof S K₁ W₂) h = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ conjugate (Vof S K₁ W₂) h ⊓ Qof S K₂ := ⟨hx.2, hs.P₁_le_Q₂ hII hx.1.2⟩
    rw [hs.V₁h_inf_Q hII hq (Or.inr rfl)] at this
    exact this
  have hVc : Nat.card ↥(conjugate (Vof S K₁ W₂) h) = 2 ^ k := by rw [conjugate_card, hk]
  have h1 := M.card_sup_mul_card_inf (A := Vof S K₁ W₂) (B := conjugate (Vof S K₁ W₂) h)
    (M.le_normalizer_of_commute (hs.V₁V_comm hII hq hrec))
  rw [hVV, Subgroup.card_bot, mul_one, hk, hVc] at h1
  exact h1

theorem A_le_W (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk2 : 2 ≤ k)
    (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) : Aof S K₁ W₂ h ≤ Wsub S U := by
  have hUA := hs.U_le_A hII hq hrec hk2 hk
  intro a ha
  exact Subgroup.mem_inf.2 ⟨hs.A_le_S hII hq hrec ha,
    Subgroup.mem_centralizer_iff.2 (fun y hy => hs.A_comm hII hq hrec y (hUA hy) a ha)⟩

theorem A_normS (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {s : G} (hsS : s ∈ S) {a : G} (ha : a ∈ Aof S K₁ W₂ h) :
    s * a * s⁻¹ ∈ Aof S K₁ W₂ h :=
  (hs.lemma82d hII hq hrec).1 s ((le_sup_left : S ≤ S ⊔ zpowers h) hsS) a ha

theorem conj_u_of_not_mem_W (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {s : G}
    (hsS : s ∈ S) (hsW : s ∉ Wsub S U) : s * u * s⁻¹ = u * z := by
  rcases hs.conj_u hII hsS with h1 | h1
  · exfalso
    apply hsW
    rw [hs.mem_W_iff hII]
    refine ⟨hsS, ?_⟩
    calc s * u = (s * u * s⁻¹) * s := by group
      _ = u * s := by rw [h1]
  · exact h1

theorem not_mem_W_mul (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {b s : G}
    (hb : b ∈ S) (hs' : s ∈ S) (hbW : b ∉ Wsub S U) (hsW : s ∉ Wsub S U) : b * s ∈ Wsub S U := by
  have hbu := hs.conj_u_of_not_mem_W hII hb hbW
  have hsu := hs.conj_u_of_not_mem_W hII hs' hsW
  have hbz : b * z * b⁻¹ = z := by rw [← hs.z_comm hII hb]; group
  rw [hs.mem_W_iff hII]
  refine ⟨mul_mem hb hs', ?_⟩
  have e1 : (b * s) * u * (b * s)⁻¹ = u := by
    calc (b * s) * u * (b * s)⁻¹ = b * (s * u * s⁻¹) * b⁻¹ := by group
      _ = b * (u * z) * b⁻¹ := by rw [hsu]
      _ = (b * u * b⁻¹) * (b * z * b⁻¹) := by group
      _ = (u * z) * z := by rw [hbu, hbz]
      _ = u := by rw [mul_assoc, hs.z_sq, mul_one]
  calc (b * s) * u = ((b * s) * u * (b * s)⁻¹) * (b * s) := by group
    _ = u * (b * s) := by rw [e1]

theorem y₁_not_mem_W (hII : II4_4_4_center) (hq : II4_4_quat)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {y₁ : G}
    (hy₁P : y₁ ∈ Pof S K₁) (hy₁inv : ∀ c ∈ Vof S K₁ W₂, y₁ * c * y₁⁻¹ = c⁻¹) :
    y₁ ∉ Wsub S U := by
  intro hW
  have h1 := (hs.mem_W_iff hII).1 hW
  have h2 := hs.y₁_conj_u hII hq hy₁P hy₁inv
  have h3 : y₁ * u * y₁⁻¹ = u := by rw [h1.2]; group
  rw [h3] at h2
  apply hs.z_ne
  have := mul_left_cancel (a := u) (by simpa using h2.symm : u * 1 = u * z)
  exact this.symm

theorem relIndex_W₀_S1 (hII : II4_4_4_center) (hq : II4_4_quat)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {y₁ : G}
    (hy₁P : y₁ ∈ Pof S K₁) (hy₁inv : ∀ c ∈ Vof S K₁ W₂, y₁ * c * y₁⁻¹ = c⁻¹) :
    (Wsub S U ⊓ S1 S K₁).relIndex (S1 S K₁) = 2 := by
  have hy₁S1 : y₁ ∈ S1 S K₁ := hs.P_le_S1 hII (Or.inl rfl) hy₁P
  have hy₁W := hs.y₁_not_mem_W hII hq hy₁P hy₁inv
  refine Basic.relIndex_eq_two_of_mul (s₀ := y₁) hy₁S1 (fun h' => hy₁W h'.1) ?_
  intro b hb hbW
  have hbW' : b ∉ Wsub S U := fun h' => hbW ⟨h', hb⟩
  exact ⟨hs.not_mem_W_mul hII (S1_le_S hb) hy₁P.1 hbW' hy₁W, mul_mem hb hy₁S1⟩

theorem card_S1_e1 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (he : (Pz S z).relIndex (S1 S K₁) = 2) {k : ℕ}
    (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) :
    Nat.card ↥(S1 S K₁) = 2 * 2 ^ k * (2 * 2 ^ k) := by
  have hcardS1 := hs.card_S1_eq hII hq hrec
  have hVc : Nat.card ↥(conjugate (Vof S K₁ W₂) h) = 2 ^ k := by rw [conjugate_card, hk]
  obtain ⟨e, he', hri, hNN, hq1, hq2⟩ := hs.lemma82_core hII hq hrec
  have hV := hs.card_V₁ hII hq
  have hPcard : Nat.card ↥(Pof S K₁) = 2 * 2 ^ k := by rw [← hV, hk]
  have he1 : e = 1 := by omega
  subst he1
  have hQ₂c : Nat.card ↥(Qof S K₂) = 2 * 2 ^ k := by rw [hq2, hPcard]; ring
  rw [hcardS1, hVc, hQ₂c]

theorem A_relIndex_W₀ (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (he : (Pz S z).relIndex (S1 S K₁) = 2) {k : ℕ}
    (hk2 : 2 ≤ k) (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) {y₁ : G} (hy₁P : y₁ ∈ Pof S K₁)
    (hy₁inv : ∀ c ∈ Vof S K₁ W₂, y₁ * c * y₁⁻¹ = c⁻¹) :
    (Aof S K₁ W₂ h).relIndex (Wsub S U ⊓ S1 S K₁) = 2 := by
  have hr2 := hs.relIndex_W₀_S1 hII hq hy₁P hy₁inv
  have hmul : Nat.card ↥(Wsub S U ⊓ S1 S K₁) * (Wsub S U ⊓ S1 S K₁).relIndex (S1 S K₁) =
      Nat.card ↥(S1 S K₁) := Basic.card_mul_relIndex_of_le inf_le_right
  rw [hr2, hs.card_S1_e1 hII hq hrec he hk] at hmul
  have hAc := hs.card_A hII hq hrec hk
  have hAW : Aof S K₁ W₂ h ≤ Wsub S U ⊓ S1 S K₁ :=
    le_inf (hs.A_le_W hII hq hrec hk2 hk) (hs.A_le_S1 hII hq hrec)
  have h2 : Nat.card ↥(Aof S K₁ W₂ h) * (Aof S K₁ W₂ h).relIndex (Wsub S U ⊓ S1 S K₁) =
      Nat.card ↥(Wsub S U ⊓ S1 S K₁) := Basic.card_mul_relIndex_of_le hAW
  have hpos : 0 < 2 ^ k := by positivity
  have hWc : Nat.card ↥(Wsub S U ⊓ S1 S K₁) = 2 * (2 ^ k * 2 ^ k) := by
    nlinarith
  rw [hAc, hWc] at h2
  have hpos2 : 0 < 2 ^ k * 2 ^ k := by positivity
  exact Nat.eq_of_mul_eq_mul_left hpos2 (by linarith)

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8

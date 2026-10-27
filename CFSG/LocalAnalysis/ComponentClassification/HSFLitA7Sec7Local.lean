module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7Basic

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec7

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}
  {yi ki ui : X}

theorem le_E_of_le_centralizer (h : IsRefl F yi) {P : Subgroup X} (hP : IsPGroup 2 P)
    (hPE : P ≤ centralizer (S.E yi : Set X)) : P ≤ S.E yi :=
  le_of_le_centralizer h.elemAbelianTwo_E h.card_E (t_mem_E yi) hP hPE

theorem mem_E_of_centralizes (h : IsRefl F yi) {P : Subgroup X} (hP : IsPGroup 2 P) {g : X}
    (hg : g ∈ P) (hgE : ∀ e ∈ S.E yi, g * e * g⁻¹ = e) : g ∈ S.E yi := by
  have hle : P ⊓ centralizer (S.E yi : Set X) ≤ S.E yi :=
    le_E_of_le_centralizer h (hP.to_le inf_le_left) inf_le_right
  refine hle ⟨hg, mem_centralizer_iff.mpr fun e he => ?_⟩
  have := hgE e he
  calc e * g = g * e * g⁻¹ * g := by rw [this]
    _ = g * e := by group

variable (D : S.Sec6 T₁ yi ki ui)

theorem exists_conj_t_mul (hact : D.act = .one) {e : X} (he : e ∈ S.E0 yi ki) :
    ∃ g : X, (∀ a ∈ S.E0 yi ki, g * a * g⁻¹ = a) ∧ g * S.t * g⁻¹ = S.t * e := by
  have hA := D.act_holds
  rw [hact] at hA
  obtain ⟨hE0, hv, hw₁, hw₂⟩ := hA
  induction he using closure_induction with
  | mem e he =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl
    · exact ⟨D.w₁, fun a ha => (hE0 a ha).2.1, hw₁⟩
    · exact ⟨D.w₂, fun a ha => (hE0 a ha).2.2, hw₂⟩
    · exact ⟨D.v, fun a ha => (hE0 a ha).1, hv⟩
  | one => exact ⟨1, fun a _ => by group, by group⟩
  | mul a b ha hb iha ihb =>
    obtain ⟨g₁, hg₁, hg₁t⟩ := iha
    obtain ⟨g₂, hg₂, hg₂t⟩ := ihb
    refine ⟨g₁ * g₂, fun c hc => ?_, ?_⟩
    · calc g₁ * g₂ * c * (g₁ * g₂)⁻¹ = g₁ * (g₂ * c * g₂⁻¹) * g₁⁻¹ := by group
        _ = c := by rw [hg₂ c hc, hg₁ c hc]
    · calc g₁ * g₂ * S.t * (g₁ * g₂)⁻¹ = g₁ * (g₂ * S.t * g₂⁻¹) * g₁⁻¹ := by group
        _ = (g₁ * S.t * g₁⁻¹) * (g₁ * b * g₁⁻¹) := by rw [hg₂t]; group
        _ = S.t * (a * b) := by rw [hg₁t, hg₁ b hb, mul_assoc]
  | inv a ha iha =>
    obtain ⟨g, hg, hgt⟩ := iha
    have hginv : ∀ c ∈ S.E0 yi ki, g⁻¹ * c * g⁻¹⁻¹ = c := by
      intro c hc
      have := hg c hc
      calc g⁻¹ * c * g⁻¹⁻¹ = g⁻¹ * (g * c * g⁻¹) * g := by rw [this, inv_inv]
        _ = c := by group
    refine ⟨g⁻¹, hginv, ?_⟩
    have h1 : S.t = g⁻¹ * (S.t * a) * g := by rw [← hgt]; group
    have h2 : g⁻¹ * a * g = a := by
      have := hginv a ha
      rwa [inv_inv] at this
    calc g⁻¹ * S.t * g⁻¹⁻¹ = g⁻¹ * S.t * g := by rw [inv_inv]
      _ = g⁻¹ * S.t * g * (g⁻¹ * a * g) * a⁻¹ := by rw [h2]; group
      _ = g⁻¹ * (S.t * a) * g * a⁻¹ := by group
      _ = S.t * a⁻¹ := by rw [← h1]

theorem conjTo_t_mul (hact : D.act = .one) {e : X} (he : e ∈ S.E0 yi ki) :
    ConjTo S.t (S.t * e) := by
  obtain ⟨g, -, hg⟩ := exists_conj_t_mul D hact he
  exact ⟨g, hg⟩

theorem conjTo_t_mul_two (h : IsRefl F yi) (hk : IsK (S := S) ki) (hact : D.act = .two)
    {e : X} (he : e ∈ S.E0 yi ki) : ConjTo S.t (S.t * e) := by
  have hA := D.act_holds
  rw [hact] at hA
  obtain ⟨hE0, hv, hw₁t, hw₂t, -, -, -, hw₁y, hw₁k, -⟩ := hA
  have hkk : ki * ki = 1 := by rw [← pow_two, hk.sq]
  have hkz : ki * S.z = S.z * ki := commute_of_mem_B hk.mem z_mem_B
  have hky : ki * yi = yi * ki := (h.comm_B hk.mem).symm
  have hshift : ∀ b ∈ S.E0 yi ki, ConjTo S.t (S.t * b) → ConjTo S.t (S.t * (ki * b)) := by
    rintro b hb ⟨g, hg⟩
    refine ⟨D.v * g, ?_⟩
    calc D.v * g * S.t * (D.v * g)⁻¹ = D.v * (g * S.t * g⁻¹) * D.v⁻¹ := by group
      _ = (D.v * S.t * D.v⁻¹) * (D.v * b * D.v⁻¹) := by rw [hg]; group
      _ = S.t * (ki * b) := by rw [hv, hE0 b hb, mul_assoc]
  have hzE : S.z ∈ S.E0 yi ki := subset_closure (by simp)
  have hyE : yi ∈ S.E0 yi ki := subset_closure (by simp)
  have hkE : ki ∈ S.E0 yi ki := subset_closure (by simp)
  have h1 : ConjTo S.t (S.t * 1) := ⟨1, by group⟩
  have h2 : ConjTo S.t (S.t * (S.z * ki)) := ⟨D.w₁, by rw [hw₁t, mul_assoc]⟩
  have h3 : ConjTo S.t (S.t * (yi * ki)) := ⟨D.w₂, by rw [hw₂t, mul_assoc]⟩
  have h4 : ConjTo S.t (S.t * (S.z * ki * yi)) := by
    refine ⟨D.w₁ * D.w₂, ?_⟩
    calc D.w₁ * D.w₂ * S.t * (D.w₁ * D.w₂)⁻¹ = D.w₁ * (D.w₂ * S.t * D.w₂⁻¹) * D.w₁⁻¹ := by group
      _ = (D.w₁ * S.t * D.w₁⁻¹) * (D.w₁ * yi * D.w₁⁻¹) * (D.w₁ * ki * D.w₁⁻¹) := by
          rw [hw₂t]; group
      _ = S.t * (S.z * ki * yi) * (ki * ki) := by rw [hw₁t, hw₁y, hw₁k]; group
      _ = S.t * (S.z * ki * yi) := by rw [hkk, mul_one]
  have hzk : S.z * ki ∈ S.E0 yi ki := mul_mem hzE hkE
  have hyk : yi * ki ∈ S.E0 yi ki := mul_mem hyE hkE
  have hzky : S.z * ki * yi ∈ S.E0 yi ki := mul_mem hzk hyE
  have hzel : ElemAbelianTwo (zpowers S.z) :=
    ⟨fun a ha b hb => commute_of_mem_B (zpowers_le.mpr z_mem_B ha) (zpowers_le.mpr z_mem_B hb),
      fun a ha => S.sq_of_mem_B (zpowers_le.mpr z_mem_B ha)⟩
  have hcase : ∀ f ∈ (zpowers S.z ⊔ zpowers ki : Subgroup X), f = 1 ∨ f = S.z ∨ f = ki ∨
      f = S.z * ki := by
    intro f hf
    rcases mem_or_of_mem_sup hzel hk.sq (fun a ha => commute_of_mem_B hk.mem
        (zpowers_le.mpr z_mem_B ha)) hf with hf' | hf'
    · rcases eq_one_or_eq_of_mem_zpowers z_sq hf' with hf'' | hf''
      · exact Or.inl hf''
      · exact Or.inr (Or.inl hf'')
    · have hfe : f = f * ki * ki := by rw [mul_assoc, hkk, mul_one]
      rcases eq_one_or_eq_of_mem_zpowers z_sq hf' with hf'' | hf'' <;> rw [hf''] at hfe
      · exact Or.inr (Or.inr (Or.inl (by rw [hfe, one_mul])))
      · exact Or.inr (Or.inr (Or.inr hfe))
  have he' := he
  rw [E0_eq] at he'
  rcases mem_or_of_mem_sup (elemAbelianTwo_zk hk) h.sq (fun _ hb => h.comm_B (zk_le_B hk hb))
      he' with he1 | he1
  · rcases hcase e he1 with rfl | rfl | rfl | rfl
    · exact h1
    · have := hshift _ hzk h2
      have e1 : ki * (S.z * ki) = S.z := by rw [← mul_assoc, hkz, mul_assoc, hkk, mul_one]
      rwa [e1] at this
    · have := hshift _ (one_mem _) h1
      rwa [mul_one] at this
    · exact h2
  · have hey : e = e * yi * yi := by rw [mul_assoc, ← pow_two, h.sq, mul_one]
    rcases hcase _ he1 with hf | hf | hf | hf <;> rw [hf] at hey <;> rw [hey]
    · have := hshift _ hyk h3
      have e1 : ki * (yi * ki) = 1 * yi := by
        rw [← mul_assoc, hky, mul_assoc, hkk, mul_one, one_mul]
      rwa [e1] at this
    · have := hshift _ hzky h4
      have e1 : ki * (S.z * ki * yi) = S.z * yi := by
        rw [← mul_assoc, ← mul_assoc, hkz, mul_assoc S.z, hkk, mul_one]
      rwa [e1] at this
    · rw [hky]; exact h3
    · exact h4

theorem conjTo_t_mul_any (D : S.Sec6 T₁ yi ki ui) (h : IsRefl F yi) (hk : IsK (S := S) ki)
    {e : X} (he : e ∈ S.E0 yi ki) : ConjTo S.t (S.t * e) := by
  cases hact : D.act
  · exact conjTo_t_mul D hact he
  · exact conjTo_t_mul_two D h hk hact he

theorem not_conjTo_of_mem_E0_any (D : S.Sec6 T₁ yi ki ui) (h : IsRefl F yi)
    (hk : IsK (S := S) ki) {e : X} (he : e ∈ S.E0 yi ki) : ¬ ConjTo S.t e := by
  classical
  intro hconj
  set A := {f : S.E yi // ConjTo S.t f} with hA
  have hcard : Nat.card A = 8 := D.card_conj
  set φ : S.E0 yi ki → A := fun f => ⟨⟨S.t * f, mul_mem (t_mem_E yi) (E0_le_E hk yi f.2)⟩,
    conjTo_t_mul_any D h hk f.2⟩ with hφ
  have hinj : Function.Injective φ := by
    intro f₁ f₂ hf
    have : S.t * (f₁ : X) = S.t * f₂ := congrArg (fun a : A => ((a : S.E yi) : X)) hf
    exact Subtype.ext (mul_left_cancel this)
  have hbij : Function.Bijective φ := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [hcard, h.card_E0 hk]
  obtain ⟨f, hf⟩ := hbij.2 ⟨⟨e, E0_le_E hk yi he⟩, hconj⟩
  have hfe : S.t * (f : X) = e := congrArg (fun a : A => ((a : S.E yi) : X)) hf
  apply h.t_not_mem_E0 hk
  have := mul_mem he (inv_mem f.2)
  rwa [← hfe, mul_inv_cancel_right] at this

theorem v_act (D : S.Sec6 T₁ yi ki ui) :
    (∀ e ∈ S.E0 yi ki, D.v * e * D.v⁻¹ = e) ∧ D.v * S.t * D.v⁻¹ = S.t * ki := by
  have h := D.act_holds
  cases hact : D.act <;> rw [hact] at h
  · exact ⟨fun e he => (h.1 e he).1, h.2.1⟩
  · exact ⟨h.1, h.2.1⟩

theorem v_mem_S₁ (D : S.Sec6 T₁ yi ki ui) : D.v ∈ D.S₁ := by
  rw [D.S₁_eq]
  exact mem_sup_left (mem_sup_left (mem_sup_left (mem_sup_right (mem_zpowers _))))

theorem t_mem_C (D : S.Sec6 T₁ yi ki ui) : S.t ∈ D.Q₁ ⊓ centralizer (D.D₁₁ : Set X) := by
  rw [D.C_eq]; exact subset_closure (by simp)

variable {D : S.Sec6 T₁ yi ki ui}

theorem v_sq_mem_E0 (h : IsRefl F yi) (hk : IsK (S := S) ki) (hkF : F.kF ∈ S.E0 yi ki) :
    D.v ^ 2 ∈ S.E0 yi ki := by
  obtain ⟨hvE, hvt⟩ := v_act D
  have hzE : S.z ∈ S.E0 yi ki := subset_closure (by simp)
  have hyE : yi ∈ S.E0 yi ki := subset_closure (by simp)
  have hkiE : ki ∈ S.E0 yi ki := subset_closure (by simp)
  have hv2E : ∀ e ∈ S.E0 yi ki, D.v ^ 2 * e * (D.v ^ 2)⁻¹ = e := by
    intro e he
    rw [pow_two, show D.v * D.v * e * (D.v * D.v)⁻¹ = D.v * (D.v * e * D.v⁻¹) * D.v⁻¹ by group,
      hvE e he, hvE e he]
  have hv2t : D.v ^ 2 * S.t * (D.v ^ 2)⁻¹ = S.t := by
    rw [pow_two, show D.v * D.v * S.t * (D.v * D.v)⁻¹ = D.v * (D.v * S.t * D.v⁻¹) * D.v⁻¹ by
      group, hvt, Sec7.conj_mul_eq', hvt, hvE ki hkiE, mul_assoc,
      ← pow_two, hk.sq, mul_one]
  have hmem : D.v ^ 2 ∈ S.E yi := by
    refine mem_E_of_centralizes h D.isPGroup_S₁ (pow_mem (v_mem_S₁ D) 2) fun e he => ?_
    exact fix_E_of_fix F yi (hv2E _ hzE) hv2t (hv2E _ hkF) (hv2E _ hyE) he
  rcases h.mem_E0_or hk hmem with h1 | h1
  · exact h1
  · exfalso
    have hc : D.v * (D.v ^ 2 * S.t) * D.v⁻¹ = D.v ^ 2 * S.t := hvE _ h1
    rw [show D.v * (D.v ^ 2 * S.t) * D.v⁻¹ = D.v ^ 2 * (D.v * S.t * D.v⁻¹) by group, hvt,
      ← mul_assoc] at hc
    exact hk.ne_one (mul_left_cancel (hc.trans (mul_one _).symm))

theorem v_sq_eq (h : IsRefl F yi) (hk : IsK (S := S) ki) (hkF : F.kF ∈ S.E0 yi ki) :
    D.v ^ 2 = 1 ∨ D.v ^ 2 = ki := by
  have hC := D.card_C
  by_contra hne
  push Not at hne
  obtain ⟨hvE, hvt⟩ := v_act D
  have hv2 := v_sq_mem_E0 (D := D) h hk hkF
  set V : Subgroup X := zpowers S.t ⊔ zpowers ki with hV
  have hkiB := hk.mem
  have hVB : V ≤ S.B := sup_le (zpowers_le.mpr t_mem_B) (zpowers_le.mpr hkiB)
  have hVel : ElemAbelianTwo V :=
    ⟨fun _ ha _ hb => commute_of_mem_B (hVB ha) (hVB hb), fun _ ha => S.sq_of_mem_B (hVB ha)⟩
  have htel : ElemAbelianTwo (zpowers S.t) :=
    ⟨fun a ha b hb => commute_of_mem_B (zpowers_le.mpr t_mem_B ha) (zpowers_le.mpr t_mem_B hb),
      fun a ha => S.sq_of_mem_B (zpowers_le.mpr t_mem_B ha)⟩
  have hki_t : ki ∉ zpowers S.t := fun hh => hk.not_mem (mem_sup_right hh)
  have hcardV : Nat.card V = 4 := by
    rw [hV, card_sup_of_not_mem htel hk.sq hki_t (fun a ha => commute_of_mem_B hkiB
      (zpowers_le.mpr t_mem_B ha)), Nat.card_zpowers, orderOf_eq_prime S.t_sq S.t_ne_one]
  have hv2V : D.v ^ 2 ∉ V := by
    intro hmem
    rcases mem_or_of_mem_sup htel hk.sq (fun a ha => commute_of_mem_B hkiB
      (zpowers_le.mpr t_mem_B ha)) hmem with h1 | h1
    · rcases eq_one_or_eq_of_mem_zpowers S.t_sq h1 with h2 | h2
      · exact hne.1 h2
      · exact h.t_not_mem_E0 hk (h2 ▸ hv2)
    · rcases eq_one_or_eq_of_mem_zpowers S.t_sq h1 with h2 | h2
      · exact hne.2 (by
          have := congrArg (· * ki) h2
          simpa [mul_assoc, ← pow_two, hk.sq] using this)
      · apply h.t_not_mem_E0 hk
        rw [← h2]
        exact mul_mem hv2 (subset_closure (by simp))
  have hv2c : ∀ a ∈ V, D.v ^ 2 * a = a * D.v ^ 2 := by
    intro a ha
    have hE := (h.elemAbelianTwo_E)
    exact hE.comm _ (E0_le_E hk yi hv2) a (B_le_E yi (hVB ha))
  have hv2sq : (D.v ^ 2) ^ 2 = 1 := (h.elemAbelianTwo_E0 hk).sq_eq_one _ hv2
  set W : Subgroup X := V ⊔ zpowers (D.v ^ 2) with hW
  have hWel := (hVel.sup_zpowers hv2sq hv2V hv2c).1
  have hcardW : Nat.card W = 8 := by
    rw [hW, card_sup_of_not_mem hVel hv2sq hv2V hv2c, hcardV]
  have hCeq : D.Q₁ ⊓ centralizer (D.D₁₁ : Set X) = V ⊔ zpowers D.v := by
    rw [D.C_eq, Sec7.closure_triple_eq]
  have hWle : W ≤ V ⊔ zpowers D.v :=
    sup_le le_sup_left (zpowers_le.mpr (pow_mem (mem_sup_right (mem_zpowers _)) 2))
  have hvW : D.v ∉ W := by
    intro hvW
    have := hWel.comm _ hvW S.t (le_sup_left (a := V) (mem_sup_left (mem_zpowers _)))
    have h1 : D.v * S.t * D.v⁻¹ = S.t := by rw [this, mul_inv_cancel_right]
    rw [hvt] at h1
    exact hk.ne_one (mul_left_cancel (h1.trans (mul_one _).symm))
  have hlt : W < V ⊔ zpowers D.v := lt_of_le_of_ne hWle fun heq =>
    hvW (heq ▸ mem_sup_right (mem_zpowers _))
  have hdvd : Nat.card W ∣ Nat.card (V ⊔ zpowers D.v : Subgroup X) :=
    Subgroup.card_dvd_of_le hWle
  have hlt' : Nat.card W < Nat.card (V ⊔ zpowers D.v : Subgroup X) :=
    Subgroup.card_lt_of_lt hlt
  rw [← hCeq, hC, hcardW] at *
  obtain ⟨m, hm⟩ := hdvd
  omega

theorem exists_v' (h : IsRefl F yi) (hk : IsK (S := S) ki) (hkF : F.kF ∈ S.E0 yi ki) :
    ∃ v' : X, (v' = D.v ∨ v' = D.v * S.t) ∧ v' ^ 2 = 1 := by
  obtain ⟨-, hvt⟩ := v_act D
  rcases v_sq_eq (D := D) h hk hkF with h1 | h1
  · exact ⟨D.v, Or.inl rfl, h1⟩
  · refine ⟨D.v * S.t, Or.inr rfl, ?_⟩
    have hkt : ki * S.t = S.t * ki := commute_of_mem_B hk.mem t_mem_B
    calc (D.v * S.t) ^ 2 = (D.v * S.t * D.v⁻¹) * (D.v ^ 2) * S.t := by
          rw [pow_two, pow_two]; group
      _ = 1 := by
        rw [hvt, h1, mul_assoc S.t, ← pow_two, hk.sq, mul_one, ← pow_two, S.t_sq]

end Sec7

end CFSG.ComponentClassification.HSFLit

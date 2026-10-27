module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2S3Base

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

theorem zmod2_cases : ∀ q : ZMod 2, q = 0 ∨ q = 1 := by decide

theorem zmod2_zero_ne_one : (0 : ZMod 2) ≠ 1 := by decide

theorem dbit8_two_mul : ∀ c : ZMod 8, dbit8 (2 * c) = 0 := by decide

theorem dbit8_four_add : ∀ b : ZMod 8, dbit8 (4 + b) = dbit8 b := by decide

theorem type8_of_eq {σ : Perm (ZMod 8)} {hσ : σ ∈ H8} {u : (ZMod 8)ˣ} {b : ZMod 8}
    (h : σ = aff8 u b) : type8 ⟨σ, hσ⟩ = Multiplicative.ofAdd (dbit8 b, fbit8 u) := by
  subst h
  exact type8_aff8 u b

theorem dbit8_neg_mul : ∀ (u : (ZMod 8)ˣ) (b : ZMod 8), dbit8 (-(↑u⁻¹ * b)) = dbit8 b := by
  decide

theorem fbit8_inv : ∀ u : (ZMod 8)ˣ, fbit8 (↑u⁻¹ : ZMod 8) = fbit8 u := by decide

theorem mode_aux : ∀ p₁ p₂ q₁ q₂ : ZMod 2, q₁ = 0 ∨ q₂ = p₂ ∨ (p₁ = 0 ∧ q₁ = 1) ∨
    (p₂ = 0 ∧ q₂ = 1) ∨ (p₁ + p₂ = 0 ∧ q₁ + q₂ = 1) := by decide

theorem type8_eq_one_iff_aux : ∀ u : (ZMod 8)ˣ, ∀ b : ZMod 8,
    (dbit8 b = 0 ∧ fbit8 u = 0) ↔ aff8 u b ∈ R8 := by decide

namespace L2Data

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} (A : L2Data t L)

theorem eq_one_or_eq_t {κ : X} (hκ : κ ∈ A.K) (hκ2 : κ ^ 2 = 1) : κ = 1 ∨ κ = t := by
  by_cases h : κ = 1
  · exact Or.inl h
  · exact Or.inr (A.eq_t_of_mem_K hκ hκ2 h)

theorem eq_one_or_eq_t_of_card (hK : Nat.card A.K = 2) {κ : X} (hκ : κ ∈ A.K) :
    κ = 1 ∨ κ = t := by
  have ht2 : t ^ 2 = 1 := by rw [← A.orderOf_t, pow_orderOf_eq_one]
  have heq : zpowers t = A.K := Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr A.t_mem_K)
    (by rw [hK, Nat.card_zpowers, A.orderOf_t])
  rw [← heq] at hκ
  exact eq_one_or_eq_of_mem_zpowers ht2 hκ

omit [Finite X] in
theorem exists_eq_mul_of_mem_R8 {g : X} (hg : g ∈ A.T) (h : A.ψ ⟨g, hg⟩ ∈ R8) :
    ∃ r ∈ A.R, ∃ κ ∈ A.K, g = r * κ := by
  obtain ⟨r, hr, hψr⟩ := A.exists_mem_R_ψ_eq h
  have hm : r⁻¹ * g ∈ A.T := mul_mem (inv_mem hr.1) hg
  refine ⟨r, hr, r⁻¹ * g, ?_, by group⟩
  rw [A.mem_K_iff hm]
  have : (⟨r⁻¹ * g, hm⟩ : A.T) = (⟨r, hr.1⟩ : A.T)⁻¹ * ⟨g, hg⟩ := rfl
  rw [this, map_mul, map_inv, hψr, inv_mul_cancel]

theorem conj_mem_K {g κ : X} (hg : g ∈ A.T) (hκ : κ ∈ A.K) : g * κ * g⁻¹ ∈ A.K :=
  mem_inf.mpr ⟨mul_mem (mul_mem hg (mem_inf.mp hκ).1) (inv_mem hg),
    conj_mem_coreActionKernel (A.config.le_normalizer (A.T_le_centralizer hg))
      (mem_inf.mp hκ).2⟩

theorem commute_K_of_mem_RK {r κ₀ κ : X} (hr : r ∈ A.R) (hκ₀ : κ₀ ∈ A.K) (hκ : κ ∈ A.K) :
    r * κ₀ * κ = κ * (r * κ₀) := by
  have h1 := A.commute_of_mem_R_of_mem_K hr hκ
  have h2 : κ₀ * κ = κ * κ₀ := by
    have := (IsCyclic.commGroup (α := A.K)).mul_comm ⟨κ₀, hκ₀⟩ ⟨κ, hκ⟩
    exact congrArg Subtype.val this
  rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]

theorem eq_one_or_eq_t_of_mem_elem {E : Subgroup X} (hE : ElemAbelianTwo E) {κ : X} (hκE : κ ∈ E)
    (hκ : κ ∈ A.K) : κ = 1 ∨ κ = t :=
  A.eq_one_or_eq_t hκ (hE.sq_eq_one κ hκE)

theorem _root_.CFSG.ComponentClassification.HSFLit.exists_mem_not_mem_finset
    {G : Type*} [Group G] [Finite G] (E : Subgroup G) (s : Finset G)
    (hs : s.card < Nat.card E) : ∃ e ∈ E, e ∉ s := by
  classical
  by_contra h
  push Not at h
  have hle : Nat.card E ≤ s.card := by
    have hsub : (E : Set G) ⊆ (s : Set G) := fun e he => h e he
    calc Nat.card E = (E : Set G).ncard := Nat.card_coe_set_eq (E : Set G)
      _ ≤ (s : Set G).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet s)
      _ = s.card := Set.ncard_coe_finset s
  omega

theorem mem_of_commute_elem (M : (ZMod 8)ˣ → ZMod 8 → Prop)
    (hM : ∀ u₁ b₁ u₂ b₂ u b, kleinCent M u₁ b₁ u₂ b₂ u b)
    (hψM : ∀ (g : A.T) u b, aff8 u b = A.ψ g → M u b) (hK : Nat.card A.K = 2)
    {E : Subgroup X} (hET : E ≤ A.T) (hE : ElemAbelianTwo E) (hcard : Nat.card E = 8)
    (htE : t ∈ E) {g : X} (hg : g ∈ A.T) (hgE : ∀ e ∈ E, g * e = e * g) : g ∈ E := by
  classical
  obtain ⟨e₁, he₁, he₁s⟩ := exists_mem_not_mem_finset E {1, t} (by
    calc ({1, t} : Finset X).card ≤ 2 := Finset.card_le_two
      _ < Nat.card E := by rw [hcard]; norm_num)
  obtain ⟨e₂, he₂, he₂s⟩ := exists_mem_not_mem_finset E {1, t, e₁, e₁ * t} (by
    calc ({1, t, e₁, e₁ * t} : Finset X).card ≤ 4 := Finset.card_le_four
      _ < Nat.card E := by rw [hcard]; norm_num)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he₁s he₂s
  have hψK : ∀ {e : X} (he : e ∈ E), A.ψ ⟨e, hET he⟩ = 1 → e = 1 ∨ e = t := fun he h =>
    A.eq_one_or_eq_t_of_mem_elem hE he ((A.mem_K_iff (hET he)).mpr h)
  have hψ₁ : A.ψ ⟨e₁, hET he₁⟩ ≠ 1 := fun h => by
    rcases hψK he₁ h with h' | h'
    · exact he₁s.1 h'
    · exact he₁s.2 h'
  have hψ₂ : A.ψ ⟨e₂, hET he₂⟩ ≠ 1 := fun h => by
    rcases hψK he₂ h with h' | h'
    · exact he₂s.1 h'
    · exact he₂s.2.1 h'
  have hψ₁₂ : A.ψ ⟨e₁, hET he₁⟩ ≠ A.ψ ⟨e₂, hET he₂⟩ := fun h => by
    have hm : e₁⁻¹ * e₂ ∈ E := mul_mem (inv_mem he₁) he₂
    have h1 : A.ψ ⟨e₁⁻¹ * e₂, hET hm⟩ = 1 := by
      have : (⟨e₁⁻¹ * e₂, hET hm⟩ : A.T) = (⟨e₁, hET he₁⟩ : A.T)⁻¹ * ⟨e₂, hET he₂⟩ := rfl
      rw [this, map_mul, map_inv, h, inv_mul_cancel]
    rcases hψK hm h1 with h' | h'
    · exact he₂s.2.2.1 (by rw [← mul_inv_cancel_left e₁ e₂, h', mul_one])
    · exact he₂s.2.2.2 (by rw [← mul_inv_cancel_left e₁ e₂, h'])
  have hsq : ∀ {e : X} (he : e ∈ E), A.ψ ⟨e, hET he⟩ * A.ψ ⟨e, hET he⟩ = 1 := fun {e} he => by
    rw [← map_mul]
    have : (⟨e, hET he⟩ : A.T) * ⟨e, hET he⟩ = 1 := Subtype.ext (by
      rw [Subgroup.coe_mul, ← pow_two, hE.sq_eq_one e he]; rfl)
    rw [this, map_one]
  have hcomm : ∀ {e e' : X} (he : e ∈ E) (he' : e' ∈ E) (_ : e * e' = e' * e),
      A.ψ ⟨e, hET he⟩ * A.ψ ⟨e', hET he'⟩ = A.ψ ⟨e', hET he'⟩ * A.ψ ⟨e, hET he⟩ := by
    intro e e' he he' h
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h
  obtain ⟨u₁, b₁, h₁⟩ := A.exists_aff8 ⟨e₁, hET he₁⟩
  obtain ⟨u₂, b₂, h₂⟩ := A.exists_aff8 ⟨e₂, hET he₂⟩
  obtain ⟨u, b, hg'⟩ := A.exists_aff8 ⟨g, hg⟩
  have key := hM u₁ b₁ u₂ b₂ u b ⟨hψM _ _ _ h₁, hψM _ _ _ h₂, hψM _ _ _ hg',
    by rw [h₁]; exact hsq he₁, by rw [h₂]; exact hsq he₂,
    by rw [h₁, h₂]; exact hcomm he₁ he₂ (hE.comm _ he₁ _ he₂),
    by rw [h₁]; exact hψ₁, by rw [h₂]; exact hψ₂, by rw [h₁, h₂]; exact hψ₁₂,
    by rw [hg', h₁, ← map_mul, ← map_mul]; congr 1; exact Subtype.ext (hgE e₁ he₁),
    by rw [hg', h₂, ← map_mul, ← map_mul]; congr 1; exact Subtype.ext (hgE e₂ he₂)⟩
  obtain ⟨e, he, hψe⟩ : ∃ e, ∃ he : e ∈ E, A.ψ ⟨g, hg⟩ = A.ψ ⟨e, hET he⟩ := by
    rw [hg', h₁, h₂] at key
    rcases key with h | h | h | h
    · exact ⟨1, one_mem _, by rw [h]; exact (map_one A.ψ).symm⟩
    · exact ⟨e₁, he₁, h⟩
    · exact ⟨e₂, he₂, h⟩
    · refine ⟨e₁ * e₂, mul_mem he₁ he₂, ?_⟩
      rw [h, ← map_mul]
      rfl
  have hm : e⁻¹ * g ∈ A.T := mul_mem (inv_mem (hET he)) hg
  have hK' : e⁻¹ * g ∈ A.K := by
    rw [A.mem_K_iff hm]
    have : (⟨e⁻¹ * g, hm⟩ : A.T) = (⟨e, hET he⟩ : A.T)⁻¹ * ⟨g, hg⟩ := rfl
    rw [this, map_mul, map_inv, hψe, inv_mul_cancel]
  have hge : g = e * (e⁻¹ * g) := by group
  rcases A.eq_one_or_eq_t_of_card hK hK' with h | h
  · rw [hge, h, mul_one]; exact he
  · rw [hge, h]; exact mul_mem he htE

omit [Finite X] in
theorem _root_.CFSG.ComponentClassification.HSFLit.ElemAbelianTwo.map_conj {V : Subgroup X}
    (hV : ElemAbelianTwo V) (h : X) : ElemAbelianTwo (V.map (MulAut.conj h).toMonoidHom) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hV.comm a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_pow, hV.sq_eq_one a ha, map_one]

theorem _root_.CFSG.ComponentClassification.HSFLit.elem8_of {a b c : X} (ha : a ^ 2 = 1)
    (hb : b ^ 2 = 1) (hc : c ^ 2 = 1) (hab : a * b = b * a) (hac : a * c = c * a)
    (hbc : b * c = c * b) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hba : b ≠ a)
    (hc' : c ≠ 1 ∧ c ≠ a ∧ c ≠ b ∧ c ≠ a * b) :
    ElemAbelianTwo (⊥ ⊔ zpowers a ⊔ zpowers b ⊔ zpowers c : Subgroup X) ∧
      Nat.card (⊥ ⊔ zpowers a ⊔ zpowers b ⊔ zpowers c : Subgroup X) = 8 ∧
      c ∈ (⊥ ⊔ zpowers a ⊔ zpowers b ⊔ zpowers c : Subgroup X) := by
  have h1 := ElemAbelianTwo.bot.sup_zpowers (g := a) ha (by simpa using ha1)
    (fun x hx => by rw [mem_bot.mp hx, one_mul, mul_one])
  have hmem1 : ∀ x ∈ (⊥ ⊔ zpowers a : Subgroup X), x = 1 ∨ x = a := by
    intro x hx
    rcases h1.2.1 x hx with h | h
    · exact Or.inl (mem_bot.mp h)
    · right
      have := mem_bot.mp h
      calc x = x * a * a⁻¹ := by group
        _ = a := by rw [this, one_mul, inv_eq_of_mul_eq_one_right (by rw [← pow_two, ha])]
  have h2 := h1.1.sup_zpowers (g := b) hb (fun h => by
      rcases hmem1 b h with h | h
      · exact hb1 h
      · exact hba h)
    (fun x hx => by rcases hmem1 x hx with rfl | rfl <;> simp [hab])
  have hmem2 : ∀ x ∈ (⊥ ⊔ zpowers a ⊔ zpowers b : Subgroup X),
      x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
    intro x hx
    have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hb])
    rcases h2.2.1 x hx with h | h
    · rcases hmem1 x h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · rcases hmem1 _ h with h' | h'
      · right; right; left
        calc x = x * b * b⁻¹ := by group
          _ = b := by rw [h', one_mul, hbinv]
      · right; right; right
        calc x = x * b * b⁻¹ := by group
          _ = a * b := by rw [h', hbinv]
  have h3 := h2.1.sup_zpowers (g := c) hc (fun h => by
      rcases hmem2 c h with h | h | h | h
      · exact hc'.1 h
      · exact hc'.2.1 h
      · exact hc'.2.2.1 h
      · exact hc'.2.2.2 h)
    (fun x hx => by
      rcases hmem2 x hx with rfl | rfl | rfl | rfl
      · simp
      · exact hac.symm
      · exact hbc.symm
      · calc c * (a * b) = (c * a) * b := by rw [mul_assoc]
          _ = (a * c) * b := by rw [hac]
          _ = a * (c * b) := by rw [mul_assoc]
          _ = a * (b * c) := by rw [hbc]
          _ = a * b * c := by rw [mul_assoc])
  refine ⟨h3.1, ?_, mem_sup_right (mem_zpowers c)⟩
  rw [h3.2.2, h2.2.2, h1.2.2]
  simp

theorem sq_eq_one_of_mem_R {r : X} (hr : r ∈ A.R)
    (h : A.ψ ⟨r, hr.1⟩ * A.ψ ⟨r, hr.1⟩ = 1) : r ^ 2 = 1 := by
  have hm : r ^ 2 ∈ A.R := pow_mem hr 2
  refine A.eq_of_ψ_eq hm (one_mem _) ?_
  have : (⟨r ^ 2, hm.1⟩ : A.T) = (⟨r, hr.1⟩ : A.T) ^ 2 := rfl
  rw [this, map_pow, pow_two, h]
  exact (map_one A.ψ).symm

omit [Finite X] in
theorem ψ_mul {g h : X} (hg : g ∈ A.T) (hh : h ∈ A.T) :
    A.ψ ⟨g * h, mul_mem hg hh⟩ = A.ψ ⟨g, hg⟩ * A.ψ ⟨h, hh⟩ := by
  rw [← map_mul]
  rfl

omit [Finite X] in
theorem mode_of_no_field
    (hnF : ∀ (g : A.T) u b, aff8 u b = A.ψ g → ¬ (dbit8 b = 0 ∧ fbit8 u = 1)) :
    (∀ (g : A.T) u b, aff8 u b = A.ψ g → inD16 u b) ∨
      (∀ (g : A.T) u b, aff8 u b = A.ψ g → inSD16 u b) := by
  by_contra h
  push Not at h
  obtain ⟨⟨g₁, u₁, b₁, h₁, hn₁⟩, ⟨g₂, u₂, b₂, h₂, hn₂⟩⟩ := h
  have hF₁ := hnF g₁ u₁ b₁ h₁
  have hF₂ := hnF g₂ u₂ b₂ h₂
  have hF := hnF (g₁ * g₂) (u₁ * u₂) (b₁ + u₁ * b₂) (by rw [← aff8_mul, h₁, h₂, map_mul])
  obtain ⟨hd, hf⟩ := type8_mul_aux u₁ u₂ b₁ b₂
  unfold inD16 at hn₁
  unfold inSD16 at hn₂
  rw [hd, hf] at hF
  rcases mode_aux (dbit8 b₁) (dbit8 b₂) (fbit8 u₁) (fbit8 u₂) with h | h | h | h | h
  · exact hn₁ h
  · exact hn₂ h
  · exact hF₁ h
  · exact hF₂ h
  · exact hF h

omit [Finite X] in
theorem exists_z_y : ∃ z ∈ A.R, ∃ y ∈ A.R, ∃ hz : z ∈ A.R, ∃ hy : y ∈ A.R,
    A.ψ ⟨z, hz.1⟩ = z8 ∧ A.ψ ⟨y, hy.1⟩ = y8 := by
  obtain ⟨z, hz, hψz⟩ := A.exists_mem_R_ψ_eq (σ := z8) ⟨1, 2, Or.inl rfl, by decide⟩
  obtain ⟨y, hy, hψy⟩ := A.exists_mem_R_ψ_eq (σ := y8) ⟨-1, 0, Or.inr rfl, by decide⟩
  exact ⟨z, hz, y, hy, hz, hy, hψz, hψy⟩

theorem commute_z {z g : X} (hz : z ∈ A.R) (hψz : A.ψ ⟨z, hz.1⟩ = z8) (hg : g ∈ A.T) :
    g * z = z * g := by
  have hm : g * z * g⁻¹ ∈ A.R :=
    mem_inf.mpr ⟨mul_mem (mul_mem hg (mem_inf.mp hz).1) (inv_mem hg),
      (mem_normalizer_iff.mp (A.config.le_normalizer (A.T_le_centralizer hg)) z).mp
        (mem_inf.mp hz).2⟩
  have h := A.eq_of_ψ_eq hm hz (by
    obtain ⟨u, b, hub⟩ := A.exists_aff8 ⟨g, hg⟩
    have : (⟨g * z * g⁻¹, hm.1⟩ : A.T) = ⟨g, hg⟩ * ⟨z, hz.1⟩ * (⟨g, hg⟩ : A.T)⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, hψz, ← hub, z8_comm_aff8, mul_inv_cancel_right])
  calc g * z = g * z * g⁻¹ * g := by group
    _ = z * g := by rw [h]

theorem mem_zpowers_of_sq_ne_one {c κ : X} (hc : c ∈ A.K) (hco : orderOf c = 4) (hκ : κ ∈ A.K)
    (hκ2 : κ ^ 2 ≠ 1) : c ∈ zpowers κ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set c' : A.K := ⟨c, hc⟩
  set κ' : A.K := ⟨κ, hκ⟩
  have hKp : IsPGroup 2 A.K := (A.isPGroup_T.to_le inf_le_left)
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hKp) κ'
  have hκo : orderOf κ' = orderOf κ := Subgroup.orderOf_mk κ hκ
  have h4 : 4 ∣ orderOf κ := by
    rw [← hκo, hm]
    rcases Nat.lt_or_ge m 2 with h | h
    · exfalso
      apply hκ2
      have hdvd : orderOf κ ∣ 2 := by
        rw [← hκo, hm]
        interval_cases m <;> norm_num
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    · exact (show (4 : ℕ) = 2 ^ 2 by norm_num) ▸ Nat.pow_dvd_pow 2 h
  have hle : zpowers c' ≤ zpowers κ' := by
    rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers,
      Subgroup.orderOf_mk, Subgroup.orderOf_mk, hco]
    exact h4
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hle (mem_zpowers c'))
  exact mem_zpowers_iff.mpr ⟨k, by
    have := congrArg Subtype.val hk
    simpa using this⟩

theorem exists_sq_eq_t (hK : Nat.card A.K ≠ 2) : ∃ c ∈ A.K, orderOf c = 4 ∧ c ^ 2 = t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨γ, hγ⟩, hgen⟩ := IsCyclic.exists_generator (α := A.K)
  have hγo : orderOf γ = Nat.card A.K := by
    rw [← Subgroup.orderOf_mk γ hγ, orderOf_eq_card_of_forall_mem_zpowers hgen]
  have hKp : IsPGroup 2 A.K := A.isPGroup_T.to_le inf_le_left
  obtain ⟨n, hn⟩ := hKp.exists_card_eq
  have hn2 : 2 ≤ n := by
    rcases (show n = 0 ∨ n = 1 ∨ 2 ≤ n by omega) with rfl | rfl | h
    · exfalso
      rw [pow_zero] at hn
      have := Subgroup.eq_bot_of_card_eq A.K hn
      have ht : t ∈ (⊥ : Subgroup X) := this ▸ A.t_mem_K
      have h2 := A.orderOf_t
      rw [mem_bot.mp ht, orderOf_one] at h2
      exact absurd h2 (by norm_num)
    · exact absurd (by rw [hn, pow_one]) hK
    · exact h
  have h4 : 4 ∣ orderOf γ := by
    rw [hγo, hn, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.pow_dvd_pow 2 hn2
  set c := γ ^ (orderOf γ / 4) with hc
  have hco : orderOf c = 4 := by
    rw [hc, orderOf_pow_of_dvd (Nat.div_pos (Nat.le_of_dvd (orderOf_pos γ) h4)
      (by norm_num)).ne' (Nat.div_dvd_of_dvd h4), Nat.div_div_self h4 (orderOf_pos γ).ne']
  have hcK : c ∈ A.K := pow_mem hγ _
  refine ⟨c, hcK, hco, A.eq_t_of_mem_K (pow_mem hcK 2) ?_ ?_⟩
  · rw [← pow_mul, show 2 * 2 = orderOf c by rw [hco], pow_orderOf_eq_one]
  · intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hco] at this
    norm_num at this

theorem gen4_of_no_field (hH : HaradaInput)
    (hnF : ∀ (g : A.T) u b, aff8 u b = A.ψ g → ¬ (dbit8 b = 0 ∧ fbit8 u = 1)) :
    ∀ P : Subgroup X, IsPGroup 2 P → ∃ s : Finset X, s.card ≤ 4 ∧ closure (s : Set X) = P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz, y, hy, hz', hy', hψz, hψy⟩ := A.exists_z_y
  have ht2 : t ^ 2 = 1 := by rw [← A.orderOf_t, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := fun h => by
    have := A.orderOf_t
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have hψt : A.ψ ⟨t, A.t_mem_T⟩ = 1 := (A.mem_K_iff A.t_mem_T).mp A.t_mem_K
  have hz2 : z ^ 2 = 1 := A.sq_eq_one_of_mem_R hz (by rw [hψz]; decide)
  have hzt : z * t = t * z := A.commute_t hz.1
  have hne : ∀ {a b : X} (ha : a ∈ A.T) (hb : b ∈ A.T), A.ψ ⟨a, ha⟩ ≠ A.ψ ⟨b, hb⟩ → a ≠ b :=
    fun ha hb h e => h (by subst e; rfl)
  have hz1 : z ≠ 1 := hne hz.1 (one_mem _) (by
    rw [hψz, show (⟨1, one_mem _⟩ : A.T) = 1 from rfl, map_one]; decide)
  have hmapt : ∀ {h : X}, h ∈ centralizer ({t} : Set X) → ∀ {B : Subgroup X}, t ∈ B →
      t ∈ B.map (MulAut.conj h).toMonoidHom := by
    intro h hh B htB
    refine ⟨t, htB, ?_⟩
    change h * t * h⁻¹ = t
    rw [mem_centralizer_singleton_iff.mp hh, mul_inv_cancel_right]
  by_cases hK : Nat.card A.K = 2
  ·
    have hy2 : y ^ 2 = 1 := A.sq_eq_one_of_mem_R hy (by rw [hψy]; decide)
    have hyt : y * t = t * y := A.commute_t hy.1
    have hzy : z * y = y * z := (A.commute_z hz hψz hy.1).symm
    have hy1 : y ≠ 1 := hne hy.1 (one_mem _) (by
      rw [hψy, show (⟨1, one_mem _⟩ : A.T) = 1 from rfl, map_one]; decide)
    have hyz : y ≠ z := hne hy.1 hz.1 (by rw [hψy, hψz]; decide)
    have hzyT : z * y ∈ A.T := mul_mem hz.1 hy.1
    have htzy : t ≠ z * y := hne A.t_mem_T hzyT (by
      rw [hψt, A.ψ_mul hz.1 hy.1, hψz, hψy]; decide)
    have htz : t ≠ z := hne A.t_mem_T hz.1 (by rw [hψt, hψz]; decide)
    have hty : t ≠ y := hne A.t_mem_T hy.1 (by rw [hψt, hψy]; decide)
    obtain ⟨hBel, hB8, htB⟩ := elem8_of hz2 hy2 ht2 hzy hzt hyt hz1 hy1 hyz
      ⟨ht1, htz, hty, htzy⟩
    intro P hP
    refine A.gen4_of_harada hH hBel hB8 htB (fun h hh hBT g hg hgB => ?_) P hP
    have hel := hBel.map_conj h
    have hcard : Nat.card ((⊥ ⊔ zpowers z ⊔ zpowers y ⊔ zpowers t : Subgroup X).map
        (MulAut.conj h).toMonoidHom) = 8 := by
      rw [card_map_of_injective (MulAut.conj h).injective, hB8]
    rcases A.mode_of_no_field hnF with hD | hSD
    · exact A.mem_of_commute_elem inD16 kleinCent_D16 hD hK hBT hel hcard (hmapt hh htB) hg hgB
    · exact A.mem_of_commute_elem inSD16 kleinCent_SD16 hSD hK hBT hel hcard (hmapt hh htB) hg
        hgB
  ·
    obtain ⟨c, hcK, hco, hc2⟩ := A.exists_sq_eq_t hK
    by_cases hall : ∀ i ∈ A.T, i ^ 2 = 1 → c * i = i * c
    · exact A.gen4_of_fix (A.fix_of_sq (mem_inf.mp hcK).1 hc2 hall)
    push Not at hall
    obtain ⟨d, hd, hd2, hcd⟩ := hall
    have hdR : A.ψ ⟨d, hd⟩ ∉ R8 := fun h => by
      obtain ⟨r, hr, κ, hκ, rfl⟩ := A.exists_eq_mul_of_mem_R8 hd h
      exact hcd (A.commute_K_of_mem_RK hr hκ hcK).symm
    obtain ⟨u, b, hub⟩ := A.exists_aff8 ⟨d, hd⟩
    have hdsq : aff8 u b * aff8 u b = 1 := by
      rw [hub, ← map_mul]
      have : (⟨d, hd⟩ : A.T) * ⟨d, hd⟩ = 1 := Subtype.ext (by
        rw [Subgroup.coe_mul, ← pow_two, hd2]; rfl)
      rw [this, map_one]
    have hnR : ¬ (dbit8 b = 0 ∧ fbit8 u = 0) := fun h =>
      hdR (by rw [← hub]; exact (type8_eq_one_iff_aux u b).mp h)
    rcases A.mode_of_no_field hnF with hD | hSD
    swap
    ·
      exfalso
      have h1 : inSD16 u b := hSD _ u b hub
      unfold inSD16 at h1
      have hf : fbit8 u = 1 := by
        rcases zmod2_cases (fbit8 u) with h | h
        · exact absurd ⟨h1 ▸ h, h⟩ hnR
        · exact h
      exact not_inv_FD u b hf (h1 ▸ hf) hdsq
    have hf : fbit8 u = 0 := hD _ u b hub
    have hdb : dbit8 b = 1 := by
      rcases zmod2_cases (dbit8 b) with h | h
      · exact absurd ⟨h, hf⟩ hnR
      · exact h
    have hCK : ∀ {d' : X} (hd' : d' ∈ A.T), A.ψ ⟨d' * d⁻¹, mul_mem hd' (inv_mem hd)⟩ ∈ R8 →
        ∀ κ ∈ A.K, κ * d' = d' * κ → κ = 1 ∨ κ = t := by
      intro d' hd' hR κ hκ hκd
      obtain ⟨r, hr, κ₀, hκ₀, hdd⟩ := A.exists_eq_mul_of_mem_R8 _ hR
      have hd'eq : d' = r * κ₀ * d := by rw [← hdd]; group
      have hdκ : d * κ * d⁻¹ ∈ A.K := A.conj_mem_K hd hκ
      have hc1 : κ * d = d * κ := by
        have h1 : d' * κ * d'⁻¹ = d * κ * d⁻¹ := by
          rw [hd'eq]
          calc r * κ₀ * d * κ * (r * κ₀ * d)⁻¹ = r * κ₀ * (d * κ * d⁻¹) * (r * κ₀)⁻¹ := by
                group
            _ = (d * κ * d⁻¹) * (r * κ₀) * (r * κ₀)⁻¹ := by
                rw [A.commute_K_of_mem_RK hr hκ₀ hdκ]
            _ = d * κ * d⁻¹ := by group
        have h2 : d' * κ * d'⁻¹ = κ := by rw [← hκd]; group
        calc κ * d = (d * κ * d⁻¹) * d := by rw [← h1, h2]
          _ = d * κ := by group
      by_contra hne'
      push Not at hne'
      have hκ2 : κ ^ 2 ≠ 1 := fun h => by
        rcases A.eq_one_or_eq_t hκ h with h' | h'
        · exact hne'.1 h'
        · exact hne'.2 h'
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp (A.mem_zpowers_of_sq_ne_one hcK hco hκ hκ2)
      exact hcd (((Commute.zpow_left hc1 k)).eq)
    have hdt : d * t = t * d := A.commute_t hd
    have hzd : z * d = d * z := (A.commute_z hz hψz hd).symm
    have hd1 : d ≠ 1 := fun h => hdR (by
      subst h
      rw [show (⟨1, hd⟩ : A.T) = 1 from rfl, map_one]
      exact one_mem _)
    have hdz : d ≠ z := fun h => hdR (by subst h; rw [hψz]; exact ⟨1, 2, Or.inl rfl, by decide⟩)
    have hzdT : z * d ∈ A.T := mul_mem hz.1 hd
    have htd : t ≠ d := fun h => hd1 (by
      have := (A.mem_K_iff hd).mp (h ▸ A.t_mem_K)
      exact absurd (by rw [this]; exact one_mem _) hdR)
    have htz : t ≠ z := hne A.t_mem_T hz.1 (by rw [hψt, hψz]; decide)
    have htzd : t ≠ z * d := fun h => hdR (by
      have h1 : A.ψ ⟨z * d, hzdT⟩ = 1 := by
        rw [show (⟨z * d, hzdT⟩ : A.T) = ⟨t, A.t_mem_T⟩ by simp [h], hψt]
      rw [A.ψ_mul hz.1 hd, hψz] at h1
      rw [eq_inv_of_mul_eq_one_right h1]
      exact ⟨1, 2, Or.inl rfl, by decide⟩)
    obtain ⟨hBel, hB8, htB⟩ := elem8_of hz2 hd2 ht2 hzd hzt hdt hz1 hd1 hdz ⟨ht1, htz, htd, htzd⟩
    have hzB : z ∈ (⊥ ⊔ zpowers z ⊔ zpowers d ⊔ zpowers t : Subgroup X) :=
      mem_sup_left (mem_sup_left (mem_sup_right (mem_zpowers z)))
    have hdB : d ∈ (⊥ ⊔ zpowers z ⊔ zpowers d ⊔ zpowers t : Subgroup X) :=
      mem_sup_left (mem_sup_right (mem_zpowers d))
    intro P hP
    refine A.gen4_of_harada hH hBel hB8 htB (fun h hh hBT g hg hgB => ?_) P hP
    have hd''T : h * d * h⁻¹ ∈ A.T := hBT ⟨d, hdB, rfl⟩
    have hz''T : h * z * h⁻¹ ∈ A.T := hBT ⟨z, hzB, rfl⟩
    have htype := A.type8_conj hh hd hd''T
    obtain ⟨u'', b'', hub''⟩ := A.exists_aff8 ⟨h * d * h⁻¹, hd''T⟩
    have hdd : A.ψ ⟨h * d * h⁻¹ * d⁻¹, mul_mem hd''T (inv_mem hd)⟩ ∈ R8 := by
      have e1 : A.ψ ⟨h * d * h⁻¹ * d⁻¹, mul_mem hd''T (inv_mem hd)⟩ =
          A.ψ ⟨h * d * h⁻¹, hd''T⟩ * (A.ψ ⟨d, hd⟩)⁻¹ := by
        rw [← map_inv, ← map_mul]
        rfl
      have h1 := htype
      rw [type8_of_eq hub''.symm, type8_of_eq hub.symm] at h1
      have h1d := congrArg (fun p : Multiplicative (ZMod 2 × ZMod 2) => p.toAdd.1) h1
      have h1f := congrArg (fun p : Multiplicative (ZMod 2 × ZMod 2) => p.toAdd.2) h1
      simp only [toAdd_ofAdd] at h1d h1f
      rw [e1, ← hub'', ← hub, aff8_inv, aff8_mul]
      obtain ⟨h₁, h₂⟩ := type8_mul_aux u'' u⁻¹ b'' (-(↑u⁻¹ * b))
      refine (type8_eq_one_iff_aux _ _).mp ⟨?_, ?_⟩
      · rw [h₁, h1d, dbit8_neg_mul u b]
        exact CharTwo.add_self_eq_zero _
      · rw [h₂, h1f, fbit8_inv u]
        exact CharTwo.add_self_eq_zero _
    have hCK'' := hCK hd''T hdd
    have hgd : g * (h * d * h⁻¹) = (h * d * h⁻¹) * g := hgB _ ⟨d, hdB, rfl⟩
    obtain ⟨u₀, b₀, hub₀⟩ := A.exists_aff8 ⟨g, hg⟩
    have hd''2 : aff8 u'' b'' * aff8 u'' b'' = 1 := by
      rw [hub'', ← map_mul]
      have : (⟨h * d * h⁻¹, hd''T⟩ : A.T) * ⟨h * d * h⁻¹, hd''T⟩ = 1 := Subtype.ext (by
        rw [Subgroup.coe_mul, ← pow_two, conj_pow, hd2, mul_one, mul_inv_cancel]; rfl)
      rw [this, map_one]
    have hf'' : fbit8 u'' = 0 := hD _ u'' b'' hub''
    have hdb'' : dbit8 b'' = 1 := by
      have h1 := htype
      rw [type8_of_eq hub''.symm, type8_of_eq hub.symm] at h1
      have := congrArg (fun p : Multiplicative (ZMod 2 × ZMod 2) => p.toAdd.1) h1
      simp only [toAdd_ofAdd] at this
      rw [this, hdb]
    have hkey := reflCent_D16 u'' b'' u₀ b₀ hf'' hdb'' (hD _ u₀ b₀ hub₀) hd''2 (by
      rw [hub₀, hub'', ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hgd)
    have hz''L : h * z * h⁻¹ ∈ L :=
      (mem_normalizer_iff.mp (A.config.le_normalizer hh) z).mp hz.2
    have hz''R : h * z * h⁻¹ ∈ A.R := mem_inf.mpr ⟨hz''T, hz''L⟩
    have hψz'' : A.ψ ⟨h * z * h⁻¹, hz''T⟩ = z8 := by
      obtain ⟨u₁, b₁, hub₁⟩ := A.exists_aff8 ⟨h * z * h⁻¹, hz''T⟩
      have hR8 := A.ψ_mem_R8' hz''R
      rw [← hub₁] at hR8 ⊢
      have hzd'' : h * z * h⁻¹ * (h * d * h⁻¹) = h * d * h⁻¹ * (h * z * h⁻¹) := by
        calc h * z * h⁻¹ * (h * d * h⁻¹) = h * (z * d) * h⁻¹ := by group
          _ = h * (d * z) * h⁻¹ := by rw [hzd]
          _ = h * d * h⁻¹ * (h * z * h⁻¹) := by group
      have h1 := reflCent_D16 u'' b'' u₁ b₁ hf'' hdb'' (hD _ u₁ b₁ hub₁) hd''2 (by
        rw [hub₁, hub'', ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext hzd'')
      have hz''1 : aff8 u₁ b₁ ≠ 1 := by
        rw [hub₁]
        intro h1'
        apply hz1
        have : h * z * h⁻¹ = 1 := A.eq_of_ψ_eq hz''R (one_mem _) (by
          rw [h1']; exact (map_one A.ψ).symm)
        calc z = h⁻¹ * (h * z * h⁻¹) * h := by group
          _ = 1 := by rw [this]; group
      obtain ⟨uu, cc, -, hcc⟩ := hR8
      rcases h1 with h1 | h1 | h1 | h1
      · exact absurd h1 hz''1
      · exact h1
      · have := (aff8_injective (hcc.trans h1)).2
        rw [← this, dbit8_two_mul] at hdb''
        exact absurd hdb'' zmod2_zero_ne_one
      · rw [aff8_mul, Units.val_one, one_mul, one_mul] at h1
        have := (aff8_injective (hcc.trans h1)).2
        rw [← dbit8_four_add, ← this, dbit8_two_mul] at hdb''
        exact absurd hdb'' zmod2_zero_ne_one
    have hzB'' : h * z * h⁻¹ ∈ (⊥ ⊔ zpowers z ⊔ zpowers d ⊔ zpowers t : Subgroup X).map
        (MulAut.conj h).toMonoidHom := ⟨z, hzB, rfl⟩
    have hdB'' : h * d * h⁻¹ ∈ (⊥ ⊔ zpowers z ⊔ zpowers d ⊔ zpowers t : Subgroup X).map
        (MulAut.conj h).toMonoidHom := ⟨d, hdB, rfl⟩
    have htB'' := hmapt hh htB
    obtain ⟨e, he, hψe⟩ : ∃ e, ∃ he : e ∈ (⊥ ⊔ zpowers z ⊔ zpowers d ⊔ zpowers t :
        Subgroup X).map (MulAut.conj h).toMonoidHom, ∃ heT : e ∈ A.T,
        A.ψ ⟨g, hg⟩ = A.ψ ⟨e, heT⟩ ∧ e * (h * d * h⁻¹) = (h * d * h⁻¹) * e := by
      rcases hkey with h1 | h1 | h1 | h1
      · exact ⟨1, one_mem _, one_mem _, by rw [← hub₀, h1]; exact (map_one A.ψ).symm, by group⟩
      · exact ⟨h * z * h⁻¹, hzB'', hz''T, by rw [← hub₀, h1, hψz''], by
          calc h * z * h⁻¹ * (h * d * h⁻¹) = h * (z * d) * h⁻¹ := by group
            _ = h * (d * z) * h⁻¹ := by rw [hzd]
            _ = h * d * h⁻¹ * (h * z * h⁻¹) := by group⟩
      · exact ⟨h * d * h⁻¹, hdB'', hd''T, by rw [← hub₀, h1, hub''], rfl⟩
      · refine ⟨h * z * h⁻¹ * (h * d * h⁻¹), mul_mem hzB'' hdB'', mul_mem hz''T hd''T, ?_, ?_⟩
        · rw [← hub₀, h1, A.ψ_mul hz''T hd''T, hψz'', hub'']
        · calc h * z * h⁻¹ * (h * d * h⁻¹) * (h * d * h⁻¹) = h * (z * d * d) * h⁻¹ := by group
            _ = h * (d * z * d) * h⁻¹ := by rw [hzd]
            _ = h * d * h⁻¹ * (h * z * h⁻¹ * (h * d * h⁻¹)) := by group
    obtain ⟨heT, hψge, hed⟩ := hψe
    have hm : e⁻¹ * g ∈ A.T := mul_mem (inv_mem heT) hg
    have hκK : e⁻¹ * g ∈ A.K := by
      rw [A.mem_K_iff hm]
      have : (⟨e⁻¹ * g, hm⟩ : A.T) = (⟨e, heT⟩ : A.T)⁻¹ * ⟨g, hg⟩ := rfl
      rw [this, map_mul, map_inv, hψge, inv_mul_cancel]
    have hκd : e⁻¹ * g * (h * d * h⁻¹) = (h * d * h⁻¹) * (e⁻¹ * g) := by
      have hed' : e⁻¹ * (h * d * h⁻¹) = (h * d * h⁻¹) * e⁻¹ := by
        calc e⁻¹ * (h * d * h⁻¹) = e⁻¹ * ((h * d * h⁻¹) * e) * e⁻¹ := by group
          _ = e⁻¹ * (e * (h * d * h⁻¹)) * e⁻¹ := by rw [hed]
          _ = (h * d * h⁻¹) * e⁻¹ := by group
      rw [mul_assoc, hgd, ← mul_assoc, hed', mul_assoc]
    have hge : g = e * (e⁻¹ * g) := by group
    rcases hCK'' _ hκK hκd with h1 | h1
    · rw [hge, h1, mul_one]; exact he
    · rw [hge, h1]; exact mul_mem he htB''

end L2Data

end CFSG.ComponentClassification.HSFLit

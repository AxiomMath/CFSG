module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7C2g
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7C2c
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7C2f

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

theorem D8_inv_cases : ∀ σ ∈ D8, σ * σ = 1 → σ = 1 ∨ σ = swap 0 1 ∨ σ = swap 2 3 ∨
    σ = swap 0 1 * swap 2 3 ∨ σ = swap 0 2 * swap 1 3 ∨ σ = swap 0 3 * swap 1 2 := by decide

theorem K2_of_comm : ∀ τ : Perm (Fin 4), (τ = swap 0 2 * swap 1 3 ∨ τ = swap 0 3 * swap 1 2) →
    ∀ σ ∈ D8, (σ * σ = 1 ∧ σ * τ = τ * σ) →
      σ ∈ ({1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2} :
        Finset (Perm (Fin 4))) := by decide

theorem fix_K2 : ∀ τ : Perm (Fin 4), (τ = swap 0 2 * swap 1 3 ∨ τ = swap 0 3 * swap 1 2) →
    ∀ w : V4, (Mσ τ w = w ∧ Mσ (swap 2 3 * τ * (swap 2 3)⁻¹) w = w) →
      (w = (0, 0, 0, 0) ∨ w = (0, 1, 1, 0)) := by decide

theorem fix_center : ∀ w : V4, Mσ (swap 0 1 * swap 2 3) w = w →
    (w = (0, 0, 0, 0) ∨ w = (0, 1, 0, 0) ∨ w = (0, 0, 1, 0) ∨ w = (0, 1, 1, 0)) := by decide

theorem center_closed : ∀ p₀ p₁ p₂ p₃ : Perm (Fin 4),
    (p₀ = 1 ∨ p₀ = swap 0 1 * swap 2 3) → (p₁ = 1 ∨ p₁ = swap 0 1 * swap 2 3) →
    (p₂ = 1 ∨ p₂ = swap 0 1 * swap 2 3) → (p₃ = 1 ∨ p₃ = swap 0 1 * swap 2 3) →
    ∀ a b c d : Fin 2, p₀ ^ (a : ℕ) * (p₂ * p₃) ^ (b : ℕ) * (p₀ * p₁) ^ (c : ℕ) * p₂ ^ (d : ℕ) ∈
      ({1, swap 0 1 * swap 2 3} : Finset (Perm (Fin 4))) := by
  rintro p₀ p₁ p₂ p₃ (rfl | rfl) (rfl | rfl) (rfl | rfl) (rfl | rfl) <;> decide

namespace A7Base

variable {X : Type} [Group X] [Finite X] {S : A7Base X}

namespace Case2

variable (C : S.Case2)

section V

variable {V : Subgroup X} (hT₁V : C.T₁ ≤ V) (hVN : V ≤ normalizer (S.E C.yb : Set X))
  (hVc : Nat.card V = 4 * Nat.card S.data.T) (hVp : IsPGroup 2 V)
  (hVmax : ∀ Q : Subgroup X, IsPGroup 2 Q → V ≤ Q → Q ≤ normalizer (S.E C.yb : Set X) → Q = V)
  (hVE : ∀ v ∈ V, (∀ e ∈ S.E C.yb, v * e = e * v) → v ∈ S.E C.yb)

include hT₁V hVp in
theorem mem_T_of_mem_V {v : X} (hv : v ∈ V) (hvt : v * S.t * v⁻¹ = S.t) : v ∈ S.data.T := by
  have hvC : v ∈ centralizer ({S.t} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    calc v * S.t = v * S.t * v⁻¹ * v := by group
      _ = S.t * v := by rw [hvt]
  have hle : S.data.T ⊔ zpowers v ≤ V := sup_le (C.T_le.trans hT₁V) (zpowers_le.mpr hv)
  have heq := S.eq_T_of_le' (hVp.to_le hle) le_sup_left
    (sup_le S.data.T_le_centralizer (zpowers_le.mpr hvC))
  exact heq ▸ mem_sup_right (mem_zpowers v)

include hT₁V hVN hVc hVp hVmax hVE in
theorem exists_sylow : ∃ P : Sylow 2 X, (P : Subgroup X) = V := by
  by_contra hne
  push Not at hne
  obtain ⟨q, hqN, hqV, hqp⟩ := exists_mem_normalizer_not_mem hVp hne
  have hqE : q ∉ normalizer (S.E C.yb : Set X) := by
    intro h
    have := hVmax _ hqp le_sup_left (sup_le hVN (zpowers_le.mpr h))
    exact hqV (this ▸ mem_sup_right (mem_zpowers q))
  have hEV : S.E C.yb ≤ V := C.E_le_T.trans (C.T_le.trans hT₁V)
  set E' : Subgroup X := (S.E C.yb).map (MulAut.conj q).toMonoidHom with hE'
  have hE'V : E' ≤ V := by
    rintro _ ⟨e, he, rfl⟩
    exact (mem_normalizer_iff.mp hqN _).mp (hEV he)
  have hE'el : ElemAbelianTwo E' := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, C.comm ha hb]
    · rintro _ ⟨a, ha, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_pow, S.E_sq C.yb_mem C.yb_sq ha, map_one]
  have hE'c : Nat.card E' = 16 := by
    rw [hE', card_map_of_injective (MulAut.conj q).injective, C.card_E]
  have hE'ne : E' ≠ S.E C.yb := by
    intro h
    apply hqE
    refine mem_normalizer_of_conj_mem fun e he => ?_
    have : q * e * q⁻¹ ∈ E' := ⟨e, he, rfl⟩
    rwa [h] at this
  have hE'norm : ∀ v ∈ V, ∀ g ∈ E', v * g * v⁻¹ ∈ E' := by
    intro v hv g hg
    obtain ⟨e, he, rfl⟩ := hg
    have hq' : q⁻¹ * v * q ∈ V := by
      have := (mem_normalizer_iff.mp (inv_mem hqN) v).mp hv
      simpa using this
    have he' : (q⁻¹ * v * q) * e * (q⁻¹ * v * q)⁻¹ ∈ S.E C.yb :=
      (mem_normalizer_iff.mp (hVN hq') e).mp he
    refine ⟨_, he', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have ha_mem : ∀ i, q * C.e i * q⁻¹ ∈ E' := fun i => ⟨C.e i, C.e_mem i, rfl⟩
  have ha_conj : ∀ i, ConjTo S.t (q * C.e i * q⁻¹) := fun i =>
    (conjTo_conj_iff S.t (C.e i) q).mpr (C.conjTo_e i)
  set πV : ∀ g, g ∈ E' → Perm (Fin 4) := fun g hg => C.π (C.ofV hVN (hE'V hg)) with hπV
  have hπmul : ∀ g h (hg : g ∈ E') (hh : h ∈ E'),
      πV (g * h) (mul_mem hg hh) = πV g hg * πV h hh := by
    intro g h hg hh
    simp only [hπV]
    rw [← map_mul]
    rfl
  have hπD : ∀ g (hg : g ∈ E'), πV g hg ∈ D8 := fun g hg =>
    C.π_mem_D8 hT₁V hVN hVc (hE'V hg)
  have hπsq : ∀ g (hg : g ∈ E'), πV g hg * πV g hg = 1 := by
    intro g hg
    rw [← hπmul g g hg hg]
    have h1 : g * g = 1 := by rw [← pow_two, hE'el.sq_eq_one g hg]
    simp only [hπV]
    have : C.ofV hVN (hE'V (mul_mem hg hg)) = 1 := Subtype.ext h1
    rw [this, map_one]
  have hπcomm : ∀ g h (hg : g ∈ E') (hh : h ∈ E'), πV g hg * πV h hh = πV h hh * πV g hg := by
    intro g h hg hh
    rw [← hπmul g h hg hh, ← hπmul h g hh hg]
    simp only [hπV]
    have : C.ofV hVN (hE'V (mul_mem hg hh)) = C.ofV hVN (hE'V (mul_mem hh hg)) :=
      Subtype.ext (hE'el.comm g hg h hh)
    rw [this]
  have hπ1 : ∀ (g : X) (hg : g ∈ E'), πV g hg = 1 → g ∈ S.E C.yb := fun g hg h =>
    C.mem_E_of_π_eq_one hVN hVE (hE'V hg) h
  have hxV : S.x ∈ V := hT₁V C.x_mem_T₁
  have hπx : C.π (C.ofV hVN hxV) = swap 2 3 := C.π_x
  have hπconj : ∀ (g : X) (hg : g ∈ E'),
      πV (S.x * g * S.x⁻¹) (hE'norm S.x hxV g hg) = swap 2 3 * πV g hg * (swap 2 3)⁻¹ := by
    intro g hg
    simp only [hπV]
    have : C.ofV hVN (hE'V (hE'norm S.x hxV g hg)) =
        C.ofV hVN hxV * C.ofV hVN (hE'V hg) * (C.ofV hVN hxV)⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, hπx]
  have hfixE : ∀ (g : X) (hg : g ∈ E') (h : X) (hh : h ∈ E') (hhE : h ∈ S.E C.yb),
      ∃ w : V4, h = C.wordV w ∧ Mσ (πV g hg) w = w := by
    intro g hg h hh hhE
    obtain ⟨w, rfl⟩ := C.exists_wordV hhE
    refine ⟨w, rfl, ?_⟩
    rw [← C.conj_wordV_eq_iff]
    change g * C.wordV w * g⁻¹ = C.wordV w
    rw [hE'el.comm g hg _ hh]
    group
  have hcard16 : ¬ Nat.card E' ≤ 8 := by rw [hE'c]; norm_num
  have hcountK2 : ∀ (g₀ : X) (hg₀ : g₀ ∈ E'),
      (πV g₀ hg₀ = swap 0 2 * swap 1 3 ∨ πV g₀ hg₀ = swap 0 3 * swap 1 2) → False := by
    intro g₀ hg₀ hτ
    apply hcard16
    refine (C.card_le_of_π hVN hE'V
      (A := ((({1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2} :
        Finset (Perm (Fin 4))) : Set (Perm (Fin 4)))))
      (B' := {1, C.wordV (0, 1, 1, 0)}) (fun g hg => ?_) (fun g hg h1 => ?_)).trans ?_
    · exact Finset.mem_coe.mpr (K2_of_comm _ hτ _ (hπD g hg) ⟨hπsq g hg, hπcomm g g₀ hg hg₀⟩)
    · have hgE := hπ1 g hg h1
      obtain ⟨w, hgw, hw⟩ := hfixE g₀ hg₀ g hg hgE
      obtain ⟨w', hgw', hw'⟩ := hfixE _ (hE'norm S.x hxV g₀ hg₀) g hg hgE
      have hww : w' = w := C.wordV_injective (hgw'.symm.trans hgw)
      rw [hww, hπconj g₀ hg₀] at hw'
      rcases fix_K2 _ hτ w ⟨hw, hw'⟩ with rfl | rfl
      · left
        rw [hgw]
        simp [wordV, word]
      · right
        rw [hgw]
        rfl
    · rw [Set.ncard_coe_finset]
      calc _ ≤ 4 * (({C.wordV (0, 1, 1, 0)} : Set X).ncard + 1) :=
            Nat.mul_le_mul Finset.card_le_four (Set.ncard_insert_le _ _)
        _ = 8 := by rw [Set.ncard_singleton]
  have hπa : ∀ i, πV _ (ha_mem i) = 1 ∨ πV _ (ha_mem i) = swap 0 1 * swap 2 3 := by
    intro i
    have haE' := ha_mem i
    have haV := hE'V haE'
    set a := q * C.e i * q⁻¹ with ha
    have hspec : ∀ j, a * C.e j * a⁻¹ = C.e (πV _ haE' j) := fun j =>
      C.π_spec (C.ofV hVN haV) j
    have ha2 : a ^ 2 = 1 := hE'el.sq_eq_one _ haE'
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← pow_two, ha2])
    have hnotE : πV _ haE' ≠ 1 → a ∉ S.E C.yb := by
      intro hne hE
      apply hne
      exact C.π_of_mem_E hE
    rcases D8_inv_cases _ (hπD _ haE') (hπsq _ haE') with h | h | h | h | h | h
    · exact Or.inl h
    ·
      exfalso
      have hj : ∀ j, a * C.e j * a⁻¹ = C.e (swap 0 1 j) := fun j => by rw [hspec, h]
      have h0 : a * S.t * a⁻¹ = S.t * C.f := by
        have := hj 0
        rwa [C.e_zero, swap_apply_left, C.e_one] at this
      have hu' : a * C.u * a⁻¹ = C.u := by
        have := hj 2
        rwa [C.e_two, swap_apply_of_ne_of_ne (by decide) (by decide), C.e_two] at this
      have hzu' : a * (S.z * C.u) * a⁻¹ = S.z * C.u := by
        have := hj 3
        rwa [C.e_three, swap_apply_of_ne_of_ne (by decide) (by decide), C.e_three] at this
      have hcomm_of : ∀ g : X, a * g * a⁻¹ = g → a * g = g * a := fun g hg => by
        calc a * g = a * g * a⁻¹ * a := by group
          _ = g * a := by rw [hg]
      have hau := hcomm_of _ hu'
      have haz : a * S.z = S.z * a := by
        apply hcomm_of
        rw [C.z_eq, C.e_two, C.e_three,
          show a * (C.u * (S.z * C.u)) * a⁻¹ = (a * C.u * a⁻¹) * (a * (S.z * C.u) * a⁻¹) by
            group, hu', hzu']
      have haf : a * C.f = C.f * a := by
        apply hcomm_of
        have h1' : a * (S.t * C.f) * a⁻¹ = S.t := by
          have := hj 1
          rwa [C.e_one, swap_apply_right, C.e_zero] at this
        calc a * C.f * a⁻¹ = a * (S.t * (S.t * C.f)) * a⁻¹ := by
              rw [← mul_assoc S.t S.t, ← pow_two, S.t_sq, one_mul]
          _ = (a * S.t * a⁻¹) * (a * (S.t * C.f) * a⁻¹) := by group
          _ = S.t * C.f * S.t := by rw [h0, h1']
          _ = C.f := by
            rw [mul_assoc, C.comm C.f_mem_E C.t_mem_E, ← mul_assoc, ← pow_two, S.t_sq, one_mul]
      have haE : a ∉ S.E C.yb := hnotE (by rw [h]; decide)
      obtain ⟨hV1, -, hV1c⟩ := ElemAbelianTwo.bot.sup_zpowers S.z_sq
        (fun hz => S.z_ne_one (mem_bot.mp hz)) (fun g hg => by rw [mem_bot.mp hg, one_mul, mul_one])
      have hV1E : (⊥ ⊔ zpowers S.z : Subgroup X) ≤ S.E C.yb :=
        sup_le bot_le (zpowers_le.mpr C.z_mem_E)
      have hV1le : (⊥ ⊔ zpowers S.z : Subgroup X) ≤ zpowers S.t ⊔ zpowers S.z :=
        sup_le bot_le le_sup_right
      obtain ⟨hV2, -, hV2c⟩ := hV1.sup_zpowers C.f_sq (fun hf => C.f_not_mem (hV1le hf))
        (fun g hg => C.comm C.f_mem_E (hV1E hg))
      have hV2E : (⊥ ⊔ zpowers S.z ⊔ zpowers C.f : Subgroup X) ≤ S.E C.yb :=
        sup_le hV1E (zpowers_le.mpr C.f_mem_E)
      have hV2B : (⊥ ⊔ zpowers S.z ⊔ zpowers C.f : Subgroup X) ≤ S.B :=
        sup_le (sup_le bot_le (zpowers_le.mpr (subset_closure (by simp))))
          (zpowers_le.mpr C.f_mem)
      obtain ⟨hV3, -, hV3c⟩ := hV2.sup_zpowers C.u_sq (fun hu => C.u_not_mem (hV2B hu))
        (fun g hg => C.comm C.u_mem (hV2E hg))
      have hV3E : (⊥ ⊔ zpowers S.z ⊔ zpowers C.f ⊔ zpowers C.u : Subgroup X) ≤ S.E C.yb :=
        sup_le hV2E (zpowers_le.mpr C.u_mem)
      have hV3C : (⊥ ⊔ zpowers S.z ⊔ zpowers C.f ⊔ zpowers C.u : Subgroup X) ≤
          centralizer ({a} : Set X) := by
        refine sup_le (sup_le (sup_le bot_le ?_) ?_) ?_ <;>
          rw [zpowers_le, mem_centralizer_singleton_iff]
        · exact haz.symm
        · exact haf.symm
        · exact hau.symm
      obtain ⟨hF, -, hFc⟩ := hV3.sup_zpowers ha2 (fun h' => haE (hV3E h'))
        (fun g hg => (mem_centralizer_singleton_iff.mp (hV3C hg)).symm)
      set F : Subgroup X := ⊥ ⊔ zpowers S.z ⊔ zpowers C.f ⊔ zpowers C.u ⊔ zpowers a with hF'
      have haF : a ∈ F := mem_sup_right (mem_zpowers a)
      have huF : C.u ∈ F := mem_sup_left (mem_sup_right (mem_zpowers _))
      have hfF : C.f ∈ F := mem_sup_left (mem_sup_left (mem_sup_right (mem_zpowers _)))
      set P : Subgroup X := S.E C.yb ⊔ zpowers a with hP
      have hPV : P ≤ V := sup_le hEV (zpowers_le.mpr haV)
      have hPu : P ≤ centralizer ({C.u} : Set X) := by
        refine sup_le (fun g hg => mem_centralizer_singleton_iff.mpr (C.comm hg C.u_mem)) ?_
        rw [zpowers_le, mem_centralizer_singleton_iff]
        exact hau
      have hFP : F ≤ P :=
        sup_le (hV3E.trans le_sup_left) (zpowers_le.mpr (mem_sup_right (mem_zpowers a)))
      have hneF : S.E C.yb ≠ F := fun heq => haE (heq ▸ haF)
      have htat : S.t * a * S.t⁻¹ = a * C.f := by
        have ht2 : S.t * S.t = 1 := by rw [← pow_two, S.t_sq]
        have htinv : S.t⁻¹ = S.t := inv_eq_of_mul_eq_one_right ht2
        rw [htinv]
        calc S.t * a * S.t = S.t * (a * S.t * a⁻¹) * a := by group
          _ = S.t * (S.t * C.f) * a := by rw [h0]
          _ = C.f * a := by rw [← mul_assoc S.t S.t C.f, ht2, one_mul]
          _ = a * C.f := haf.symm
      have hafE : a * C.f ∉ S.E C.yb := fun h' => haE (by
        have : a = a * C.f * C.f⁻¹ := by group
        rw [this]
        exact mul_mem h' (inv_mem C.f_mem_E))
      refine C.two_E16 (u₀ := C.u) (C.conjTo_e 2 |> fun h' => C.e_two ▸ h') (hVp.to_le hPV) hPu
        (le_sup_left : S.E C.yb ≤ P) hFP ⟨fun a ha b hb => C.comm ha hb,
          fun a ha => S.E_sq C.yb_mem C.yb_sq ha⟩ hF C.card_E
          (by rw [hFc, hV3c, hV2c, hV1c, Subgroup.card_bot]) hneF ?_ ?_
      · refine ⟨C.e 0, C.e 1, C.e 2, C.e_mem 0, C.e_mem 1, C.e_mem 2, C.conjTo_e 0,
          C.conjTo_e 1, C.conjTo_e 2, ?_, ?_, ?_⟩ <;>
          exact fun h' => absurd (C.e_injective h') (by decide)
      · refine ⟨C.u, a, a * C.f, huF, haF, mul_mem haF hfF, C.e_two ▸ C.conjTo_e 2,
          ha_conj i, ?_, fun h' => haE (h' ▸ C.u_mem), fun h' => hafE (h' ▸ C.u_mem), ?_⟩
        · rw [← htat, conjTo_conj_iff]
          exact ha_conj i
        · intro h'
          apply C.f_ne_one
          have := mul_left_cancel (h'.symm.trans (mul_one a).symm)
          exact this
    ·
      exfalso
      have hat : a * S.t * a⁻¹ = S.t := by
        rw [← C.e_zero, hspec, h]
        rfl
      have haT := C.mem_T_of_mem_V hT₁V hVp haV hat
      have haEb : a ∉ S.E C.yb := hnotE (by rw [h]; decide)
      have haEs : a ∈ S.E C.ys := by
        rcases S.mem_E_or_of_sq haT ha2 with h1 | h1 <;>
          rcases C.hy with ⟨hb, hs⟩ | ⟨hb, hs⟩
        · exact absurd (hb ▸ h1) haEb
        · exact hs ▸ h1
        · exact hs ▸ h1
        · exact absurd (hb ▸ h1) haEb
      rcases (C.omega_small _ haEs).mp (ha_conj i) with h1 | h1
      · exact haEb (h1 ▸ C.t_mem_E)
      · exact haEb (h1 ▸ mul_mem C.t_mem_E C.f_mem_E)
    · exact Or.inr h
    · exact absurd (hcountK2 _ haE' (Or.inl h)) id
    · exact absurd (hcountK2 _ haE' (Or.inr h)) id
  have hπall : ∀ (g : X) (hg : g ∈ E'), πV g hg = 1 ∨ πV g hg = swap 0 1 * swap 2 3 := by
    intro g hg
    have hg' := hg
    obtain ⟨w, hw, hgw⟩ := hg'
    obtain ⟨a', b', c', d', rfl⟩ := C.exists_word hw
    have ha0 := hE'V (ha_mem 0)
    have ha1 := hE'V (ha_mem 1)
    have ha2 := hE'V (ha_mem 2)
    have ha3 := hE'V (ha_mem 3)
    have hX : g = (q * C.e 0 * q⁻¹) ^ (a' : ℕ) *
        ((q * C.e 2 * q⁻¹) * (q * C.e 3 * q⁻¹)) ^ (b' : ℕ) *
        ((q * C.e 0 * q⁻¹) * (q * C.e 1 * q⁻¹)) ^ (c' : ℕ) * (q * C.e 2 * q⁻¹) ^ (d' : ℕ) := by
      rw [← hgw]
      simp only [word, MulEquiv.coe_toMonoidHom, map_mul, map_pow]
      rw [← C.e_zero, C.z_eq, C.f_eq, ← C.e_two]
      simp only [map_mul, MulAut.conj_apply]
    have hN : C.ofV hVN (hE'V hg) = (C.ofV hVN ha0) ^ (a' : ℕ) *
        (C.ofV hVN ha2 * C.ofV hVN ha3) ^ (b' : ℕ) *
        (C.ofV hVN ha0 * C.ofV hVN ha1) ^ (c' : ℕ) * (C.ofV hVN ha2) ^ (d' : ℕ) :=
      Subtype.ext hX
    have hπg : πV g hg = C.π (C.ofV hVN ha0) ^ (a' : ℕ) *
        (C.π (C.ofV hVN ha2) * C.π (C.ofV hVN ha3)) ^ (b' : ℕ) *
        (C.π (C.ofV hVN ha0) * C.π (C.ofV hVN ha1)) ^ (c' : ℕ) *
        C.π (C.ofV hVN ha2) ^ (d' : ℕ) := by
      simp only [hπV]
      rw [hN]
      simp only [map_mul, map_pow]
    have := center_closed _ _ _ _ (hπa 0) (hπa 1) (hπa 2) (hπa 3) a' b' c' d'
    rw [← hπg] at this
    simpa using this
  have hex : ∃ (g₁ : X) (hg₁ : g₁ ∈ E'), πV g₁ hg₁ = swap 0 1 * swap 2 3 := by
    by_contra hcon
    push Not at hcon
    apply hE'ne
    refine Subgroup.eq_of_le_of_card_ge (fun g hg => hπ1 g hg ((hπall g hg).resolve_right
      (hcon g hg))) ?_
    rw [hE'c, C.card_E]
  obtain ⟨g₁, hg₁, hπg₁⟩ := hex
  apply hcard16
  refine (C.card_le_of_π hVN hE'V (A := {1, swap 0 1 * swap 2 3})
    (B' := {1, C.wordV (0, 1, 0, 0), C.wordV (0, 0, 1, 0), C.wordV (0, 1, 1, 0)})
    (fun g hg => ?_) (fun g hg h1 => ?_)).trans ?_
  · rcases hπall g hg with h | h
    · exact Or.inl h
    · exact Or.inr h
  · have hgE := hπ1 g hg h1
    obtain ⟨w, hgw, hw⟩ := hfixE g₁ hg₁ g hg hgE
    rw [hπg₁] at hw
    rw [hgw]
    rcases fix_center w hw with rfl | rfl | rfl | rfl
    · left
      simp [wordV, word]
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · have hA : ({1, swap 0 1 * swap 2 3} : Set (Perm (Fin 4))).ncard ≤ 2 := by
      calc _ ≤ ({swap 0 1 * swap 2 3} : Set (Perm (Fin 4))).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    have hB : ({1, C.wordV (0, 1, 0, 0), C.wordV (0, 0, 1, 0), C.wordV (0, 1, 1, 0)} :
        Set X).ncard ≤ 4 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
      refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
      rw [Set.ncard_singleton]
    calc _ ≤ 2 * 4 := Nat.mul_le_mul hA hB
      _ = 8 := rfl
end V

include C in
theorem sectRank4 (hH : HaradaInput) : SectRank4 X := by
  obtain ⟨V, hVp, hT₁V, hVN, hVc, hVmax, hVE⟩ := C.exists_V
  obtain ⟨P, hP⟩ := C.exists_sylow hT₁V hVN hVc hVp hVmax hVE
  obtain ⟨E₈, hE₈V, hel, hc, hcent⟩ := C.exists_E8 hT₁V hVN hVc hVp hVE
  intro Q hQ
  exact gen4_of_harada hH P (by rw [hP]; exact hE₈V) hel hc
    (fun x hx hxE => hcent x (by rw [← hP]; exact hx) hxE) Q hQ

end Case2

end A7Base

end CFSG.ComponentClassification.HSFLit

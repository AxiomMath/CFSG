module

public import CFSG.GroupTheory.PermSylowTwo.Pairing

public section

namespace CFSG.GroupTheory.PermSylowTwo

open Equiv Equiv.Perm

variable {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

theorem pairSwap_apply_inl (b : β) (c : Bool) :
    pairSwap β γ b (Sum.inl (b, c)) = Sum.inl (b, !c) := by
  cases c <;> simp [pairSwap]

theorem pairSwap_apply_inr (b : β) (x : γ) :
    pairSwap β γ b (Sum.inr x) = Sum.inr x :=
  Equiv.swap_apply_of_ne_of_ne (by simp) (by simp)

theorem pairSwap_apply_of_ne_inl {b b' : β} (h : b' ≠ b) (c : Bool) :
    pairSwap β γ b (Sum.inl (b', c)) = Sum.inl (b', c) :=
  Equiv.swap_apply_of_ne_of_ne (by simp [h]) (by simp [h])

theorem conj_pairSwap_apply_inl (h : Perm ((β × Bool) ⊕ γ)) (b : β) (c : Bool) :
    (h * pairSwap β γ b * h⁻¹) (h (Sum.inl (b, c))) = h (Sum.inl (b, !c)) := by
  rw [pairSwap, ← Equiv.swap_apply_apply h (Sum.inl (b, false)) (Sum.inl (b, true))]
  cases c <;> simp

theorem conj_pairSwap_apply_of_ne (h : Perm ((β × Bool) ⊕ γ)) (b : β)
    {p : (β × Bool) ⊕ γ} (hp0 : p ≠ Sum.inl (b, false)) (hp1 : p ≠ Sum.inl (b, true)) :
    (h * pairSwap β γ b * h⁻¹) (h p) = h p := by
  rw [pairSwap, ← Equiv.swap_apply_apply h (Sum.inl (b, false)) (Sum.inl (b, true))]
  exact Equiv.swap_apply_of_ne_of_ne (fun hh => hp0 (h.injective hh))
    (fun hh => hp1 (h.injective hh))

theorem conj_pairSwap_mul (h : Perm ((β × Bool) ⊕ γ)) (b b' : β) :
    h * (pairSwap β γ b * pairSwap β γ b') * h⁻¹ =
      (h * pairSwap β γ b * h⁻¹) * (h * pairSwap β γ b' * h⁻¹) := by
  group

theorem eq_inl_of_ne_inr [Subsingleton γ] {x : γ} {z : (β × Bool) ⊕ γ}
    (hz : z ≠ Sum.inr x) : ∃ b c, z = Sum.inl (b, c) := by
  rcases z with bc | y
  · exact ⟨bc.1, bc.2, rfl⟩
  · exact absurd (by rw [Subsingleton.elim y x]) hz

theorem not_three_cycle_pattern {Q : Subgroup (Perm ((β × Bool) ⊕ γ))}
    (hQ : ¬ 3 ∣ Nat.card Q) {x y : Perm ((β × Bool) ⊕ γ)} (hx : x ∈ Q) (hy : y ∈ Q)
    {a b e : (β × Bool) ⊕ γ} (hab : a ≠ b) (hae : a ≠ e) (hbe : b ≠ e)
    (hxa : x a = b) (hxb : x b = a) (hxe : x e = e)
    (hya : y a = e) (hye : y e = a) (hyb : y b = b) : False := by
  have h3 : 3 ∣ orderOf (x * y) :=
    three_dvd_orderOf_mul hab hae hbe hxa hxb hxe hya hye hyb
  exact hQ (h3.trans (Subgroup.orderOf_dvd_natCard Q (Q.mul_mem hx hy)))

theorem exists_ne_of_card_three {β : Type*} [Fintype β] [DecidableEq β]
    (hβ : 3 ≤ Fintype.card β) (a b : β) : ∃ c, c ≠ a ∧ c ≠ b := by
  have hcard : ({a, b} : Finset β).card < (Finset.univ : Finset β).card := by
    rw [Finset.card_univ]
    calc ({a, b} : Finset β).card ≤ 2 := Finset.card_le_two
      _ < 3 := by norm_num
      _ ≤ Fintype.card β := hβ
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨c, by simpa using hc⟩

theorem notMem_pair_of_ne_firstCoord {b' b₀ : β} {z : (β × Bool) ⊕ γ}
    (hne : b' ≠ Sum.elim Prod.fst (fun _ => b₀) z) :
    z ≠ Sum.inl (b', false) ∧ z ≠ Sum.inl (b', true) := by
  constructor <;> intro hz <;> apply hne <;> rw [hz] <;> rfl

theorem exists_config_of_moves_inr [Subsingleton γ] {h : Perm ((β × Bool) ⊕ γ)} {x : γ}
    (hne : h (Sum.inr x) ≠ Sum.inr x) :
    ∃ (b₀ : β) (c₀ : Bool) (b₂ : β) (c₂ : Bool),
      h⁻¹ (Sum.inr x) = Sum.inl (b₀, c₀) ∧
      h (Sum.inl (b₀, c₀)) = Sum.inr x ∧
      h (Sum.inl (b₀, !c₀)) = Sum.inl (b₂, c₂) ∧
      Sum.inl (b₂, !c₂) ≠ Sum.inr x ∧
      Sum.inl (b₂, !c₂) ≠ h (Sum.inl (b₀, !c₀)) ∧
      (∀ c : Bool, h⁻¹ (Sum.inl (b₂, !c₂)) ≠ Sum.inl (b₀, c)) := by
  classical
  have hz_ne : h⁻¹ (Sum.inr x) ≠ Sum.inr x := by
    intro hz'
    apply hne
    have h1 : h (h⁻¹ (Sum.inr x)) = Sum.inr x := Equiv.apply_symm_apply h (Sum.inr x)
    rw [hz'] at h1
    exact h1
  obtain ⟨b₀, c₀, hz⟩ := eq_inl_of_ne_inr hz_ne
  have hz_apply : h (Sum.inl (b₀, c₀)) = Sum.inr x := by
    rw [← hz]
    exact Equiv.apply_symm_apply h (Sum.inr x)
  have hw_ne : h (Sum.inl (b₀, !c₀)) ≠ Sum.inr x := by
    intro hw
    have h1 : Sum.inl (b₀, !c₀) = Sum.inl (b₀, c₀) := h.injective (hw.trans hz_apply.symm)
    have h2 : (!c₀) = c₀ := by simpa using h1
    exact (Bool.not_ne_self c₀) h2
  obtain ⟨b₂, c₂, hw⟩ := eq_inl_of_ne_inr hw_ne
  have he_ne_inr : Sum.inl (b₂, !c₂) ≠ Sum.inr x := by simp
  have he_ne_w : Sum.inl (b₂, !c₂) ≠ h (Sum.inl (b₀, !c₀)) := by
    intro hew
    rw [hw] at hew
    have h2 : (!c₂) = c₂ := by simpa using hew
    exact (Bool.not_ne_self c₂) h2
  have hfinv_ne : ∀ c : Bool, h⁻¹ (Sum.inl (b₂, !c₂)) ≠ Sum.inl (b₀, c) := by
    intro c hp
    have heq : Sum.inl (b₂, !c₂) = h (Sum.inl (b₀, c)) := by
      rw [← hp]
      exact (Equiv.apply_symm_apply h (Sum.inl (b₂, !c₂))).symm
    have hc : c = c₀ ∨ c = !c₀ := by cases c <;> cases c₀ <;> simp
    rcases hc with rfl | hc
    · exact he_ne_inr (heq.trans hz_apply)
    · rw [hc] at heq
      exact he_ne_w heq
  exact ⟨b₀, c₀, b₂, c₂, hz, hz_apply, hw, he_ne_inr, he_ne_w, hfinv_ne⟩

theorem fixes_inr_of_swaps [Subsingleton γ] {Q : Subgroup (Perm ((β × Bool) ⊕ γ))}
    (hQ : ¬ 3 ∣ Nat.card Q) (hsw : ∀ b, pairSwap β γ b ∈ Q)
    {h : Perm ((β × Bool) ⊕ γ)} (hh : ∀ b, h * pairSwap β γ b * h⁻¹ ∈ Q) (x : γ) :
    h (Sum.inr x) = Sum.inr x := by
  classical
  by_contra hne
  obtain ⟨b₀, c₀, b₂, c₂, hz, hz_apply, hw, he_ne_inr, he_ne_w, hfinv_ne⟩ :=
    exists_config_of_moves_inr hne
  let e : (β × Bool) ⊕ γ := Sum.inl (b₂, !c₂)
  have hw_ne : h (Sum.inl (b₀, !c₀)) ≠ Sum.inr x := by
    rw [hw]
    simp
  have hx_e : (h * pairSwap β γ b₀ * h⁻¹) e = e := by
    rw [show e = h (h⁻¹ e) from (Equiv.apply_symm_apply h e).symm]
    exact conj_pairSwap_apply_of_ne h b₀ (hfinv_ne false) (hfinv_ne true)
  have hx_w : (h * pairSwap β γ b₀ * h⁻¹) (h (Sum.inl (b₀, !c₀))) = Sum.inr x := by
    have hstep : (h * pairSwap β γ b₀ * h⁻¹) (h (Sum.inl (b₀, !c₀))) =
        h (Sum.inl (b₀, c₀)) := by
      simpa using conj_pairSwap_apply_inl h b₀ (!c₀)
    exact hstep.trans hz_apply
  have hx_inr : (h * pairSwap β γ b₀ * h⁻¹) (Sum.inr x) = h (Sum.inl (b₀, !c₀)) := by
    rw [← hz_apply]
    exact conj_pairSwap_apply_inl h b₀ c₀
  have hy_w : pairSwap β γ b₂ (h (Sum.inl (b₀, !c₀))) = e := by
    rw [hw]
    exact pairSwap_apply_inl b₂ c₂
  have hy_e : pairSwap β γ b₂ e = h (Sum.inl (b₀, !c₀)) := by
    rw [hw]
    simpa [e] using pairSwap_apply_inl b₂ (!c₂)
  have hy_inr : pairSwap β γ b₂ (Sum.inr x) = Sum.inr x := pairSwap_apply_inr b₂ x
  exact not_three_cycle_pattern hQ (hh b₀) (hsw b₂) hw_ne he_ne_w.symm he_ne_inr.symm
    hx_w hx_inr hx_e hy_w hy_e hy_inr

theorem maps_pair_to_pair_of_swaps [Subsingleton γ] {Q : Subgroup (Perm ((β × Bool) ⊕ γ))}
    (hQ : ¬ 3 ∣ Nat.card Q) (hsw : ∀ b, pairSwap β γ b ∈ Q)
    {h : Perm ((β × Bool) ⊕ γ)} (hh : ∀ b, h * pairSwap β γ b * h⁻¹ ∈ Q)
    (hfix : ∀ x : γ, h (Sum.inr x) = Sum.inr x) (b : β) :
    h (Sum.inl (b, true)) = pairInv β γ (h (Sum.inl (b, false))) := by
  classical
  have hinl : ∀ (b : β) (c : Bool), ∃ b₁ c₁, h (Sum.inl (b, c)) = Sum.inl (b₁, c₁) := by
    intro b c
    rcases hc : h (Sum.inl (b, c)) with bc | x
    · exact ⟨bc.1, bc.2, rfl⟩
    · exfalso
      have h : Sum.inl (b, c) = Sum.inr x := h.injective (by rw [hc, hfix x])
      exact (by simp : (Sum.inl (b, c) : (β × Bool) ⊕ γ) ≠ Sum.inr x) h
  obtain ⟨b₁, c₁, ha⟩ := hinl b false
  obtain ⟨b₆, c₆, hb'⟩ := hinl b true
  let e : (β × Bool) ⊕ γ := Sum.inl (b₁, !c₁)
  have hμa : pairInv β γ (h (Sum.inl (b, false))) = e := by
    rw [ha, pairInv_apply_inl]
  rw [hμa]
  by_contra hne
  have hfinv_ne : ∀ c : Bool, h⁻¹ e ≠ Sum.inl (b, c) := by
    intro c hp
    have heq : e = h (Sum.inl (b, c)) := by
      rw [← hp]
      exact (Equiv.apply_symm_apply h e).symm
    cases c
    · have hea : e = Sum.inl (b₁, c₁) := heq.trans ha
      have h2 : (!c₁) = c₁ := by simpa [e] using hea
      exact (Bool.not_ne_self c₁) h2
    · exact hne heq.symm
  have hx_e : (h * pairSwap β γ b * h⁻¹) e = e := by
    rw [show e = h (h⁻¹ e) from (Equiv.apply_symm_apply h e).symm]
    exact conj_pairSwap_apply_of_ne h b (hfinv_ne false) (hfinv_ne true)
  have hx_a : (h * pairSwap β γ b * h⁻¹) (h (Sum.inl (b, false))) =
      h (Sum.inl (b, true)) := conj_pairSwap_apply_inl h b false
  have hx_b : (h * pairSwap β γ b * h⁻¹) (h (Sum.inl (b, true))) =
      h (Sum.inl (b, false)) := by
    simpa using conj_pairSwap_apply_inl h b true
  have hy_a : pairSwap β γ b₁ (h (Sum.inl (b, false))) = e := by
    rw [ha]
    exact pairSwap_apply_inl b₁ c₁
  have hy_e : pairSwap β γ b₁ e = h (Sum.inl (b, false)) := by
    rw [ha]
    simpa [e] using pairSwap_apply_inl b₁ (!c₁)
  have hb₆_ne : b₆ ≠ b₁ := by
    intro hb₆
    rcases (show c₆ = c₁ ∨ c₆ = !c₁ by cases c₁ <;> cases c₆ <;> simp) with hc | hc
    · have hinj : (Sum.inl (b, false) : (β × Bool) ⊕ γ) = Sum.inl (b, true) := by
        apply h.injective
        rw [ha, hb', hb₆, hc]
      have hne_inl : (Sum.inl (b, false) : (β × Bool) ⊕ γ) ≠ Sum.inl (b, true) := by simp
      exact hne_inl hinj
    · apply hne
      rw [hb', hb₆, hc]
  have hy_b : pairSwap β γ b₁ (h (Sum.inl (b, true))) = h (Sum.inl (b, true)) := by
    rw [hb']
    exact pairSwap_apply_of_ne_inl hb₆_ne c₆
  have hab : h (Sum.inl (b, false)) ≠ h (Sum.inl (b, true)) := by
    intro hh
    have h1 : Sum.inl (b, false) = Sum.inl (b, true) := h.injective hh
    exact (by simp : (Sum.inl (b, false) : (β × Bool) ⊕ γ) ≠ Sum.inl (b, true)) h1
  have hae : h (Sum.inl (b, false)) ≠ e := by
    rw [ha]
    intro hh
    have h2 : c₁ = !c₁ := by simpa [e] using hh
    exact (Bool.not_ne_self c₁) h2.symm
  exact not_three_cycle_pattern hQ (hh b) (hsw b₁) hab hae hne
    hx_a hx_b hx_e hy_a hy_e hy_b

theorem mem_pairCent_of_apply [Subsingleton γ] {h : Perm ((β × Bool) ⊕ γ)}
    (hfix : ∀ x : γ, h (Sum.inr x) = Sum.inr x)
    (hpair : ∀ b : β, h (Sum.inl (b, true)) =
      pairInv β γ (h (Sum.inl (b, false)))) : h ∈ pairCent β γ := by
  rw [pairCent, Subgroup.mem_centralizer_iff]
  intro a ha
  rw [Set.mem_singleton_iff] at ha
  subst ha
  ext z
  rcases z with ⟨b, c⟩ | x
  · cases c
    · simp [Equiv.Perm.mul_apply, pairInv_apply_inl, hpair b]
    · simp [Equiv.Perm.mul_apply, pairInv_apply_inl, hpair b, pairInv_involutive]
  · simp [Equiv.Perm.mul_apply, pairInv_apply_inr, hfix x]

theorem mem_pairCent_of_swaps [Subsingleton γ] {Q : Subgroup (Perm ((β × Bool) ⊕ γ))}
    (hQ : ¬ 3 ∣ Nat.card Q) (hsw : ∀ b, pairSwap β γ b ∈ Q) {h : Perm ((β × Bool) ⊕ γ)}
    (hh : ∀ b, h * pairSwap β γ b * h⁻¹ ∈ Q) : h ∈ pairCent β γ := by
  have hfix : ∀ x : γ, h (Sum.inr x) = Sum.inr x :=
    fun x => fixes_inr_of_swaps hQ hsw hh x
  exact mem_pairCent_of_apply hfix fun b => maps_pair_to_pair_of_swaps hQ hsw hh hfix b

theorem fixes_inr_of_doubleSwaps [Subsingleton γ] (hβ : 3 ≤ Fintype.card β)
    {Q : Subgroup (Perm ((β × Bool) ⊕ γ))} (hQ : ¬ 3 ∣ Nat.card Q)
    (hsw : ∀ b b', pairSwap β γ b * pairSwap β γ b' ∈ Q)
    {h : Perm ((β × Bool) ⊕ γ)}
    (hh : ∀ b b', h * (pairSwap β γ b * pairSwap β γ b') * h⁻¹ ∈ Q) (x : γ) :
    h (Sum.inr x) = Sum.inr x := by
  classical
  by_contra hne
  obtain ⟨b₀, c₀, b₂, c₂, hz, hz_apply, hw, he_ne_inr, he_ne_w, hfinv_ne⟩ :=
    exists_config_of_moves_inr hne
  obtain ⟨b', hb'_ne_b₀, hb'_ne_b''⟩ :=
    exists_ne_of_card_three hβ b₀
      (Sum.elim Prod.fst (fun _ => b₀) (h⁻¹ (Sum.inl (b₂, !c₂))))
  have hw_ne : h (Sum.inl (b₀, !c₀)) ≠ Sum.inr x := by
    rw [hw]
    simp
  obtain ⟨b₃, hb₃, -⟩ := exists_ne_of_card_three hβ b₂ b₂
  have hfinv_ne' : h⁻¹ (Sum.inl (b₂, !c₂)) ≠ Sum.inl (b', false) ∧
      h⁻¹ (Sum.inl (b₂, !c₂)) ≠ Sum.inl (b', true) :=
    notMem_pair_of_ne_firstCoord hb'_ne_b''
  have hne_pair : ∀ c : Bool,
      (Sum.inl (b₀, c) : (β × Bool) ⊕ γ) ≠ Sum.inl (b', false) ∧
        (Sum.inl (b₀, c) : (β × Bool) ⊕ γ) ≠ Sum.inl (b', true) := by
    intro c
    constructor
    · intro hh
      have hh' : b₀ = b' ∧ c = false := by simpa using hh
      exact (Ne.symm hb'_ne_b₀) hh'.1
    · intro hh
      have hh' : b₀ = b' ∧ c = true := by simpa using hh
      exact (Ne.symm hb'_ne_b₀) hh'.1
  have hx_inr : (h * (pairSwap β γ b₀ * pairSwap β γ b') * h⁻¹) (Sum.inr x) =
      h (Sum.inl (b₀, !c₀)) := by
    rw [conj_pairSwap_mul, Equiv.Perm.mul_apply]
    rw [← hz_apply]
    have hstep : (h * pairSwap β γ b' * h⁻¹) (h (Sum.inl (b₀, c₀))) =
        h (Sum.inl (b₀, c₀)) :=
      conj_pairSwap_apply_of_ne h b' (hne_pair c₀).1 (hne_pair c₀).2
    rw [hstep]
    exact conj_pairSwap_apply_inl h b₀ c₀
  have hx_w : (h * (pairSwap β γ b₀ * pairSwap β γ b') * h⁻¹) (h (Sum.inl (b₀, !c₀))) =
      Sum.inr x := by
    rw [conj_pairSwap_mul, Equiv.Perm.mul_apply]
    have hstep : (h * pairSwap β γ b' * h⁻¹) (h (Sum.inl (b₀, !c₀))) =
        h (Sum.inl (b₀, !c₀)) :=
      conj_pairSwap_apply_of_ne h b' (hne_pair (!c₀)).1 (hne_pair (!c₀)).2
    rw [hstep]
    have hstep2 : (h * pairSwap β γ b₀ * h⁻¹) (h (Sum.inl (b₀, !c₀))) =
        h (Sum.inl (b₀, c₀)) := by
      simpa using conj_pairSwap_apply_inl h b₀ (!c₀)
    rw [hstep2, hz_apply]
  have hx_e : (h * (pairSwap β γ b₀ * pairSwap β γ b') * h⁻¹) (Sum.inl (b₂, !c₂)) =
      Sum.inl (b₂, !c₂) := by
    rw [conj_pairSwap_mul, Equiv.Perm.mul_apply]
    have hstep : (h * pairSwap β γ b' * h⁻¹) (Sum.inl (b₂, !c₂)) = Sum.inl (b₂, !c₂) := by
      rw [show Sum.inl (b₂, !c₂) = h (h⁻¹ (Sum.inl (b₂, !c₂))) from
        (Equiv.apply_symm_apply h (Sum.inl (b₂, !c₂))).symm]
      exact conj_pairSwap_apply_of_ne h b' hfinv_ne'.1 hfinv_ne'.2
    rw [hstep]
    rw [show Sum.inl (b₂, !c₂) = h (h⁻¹ (Sum.inl (b₂, !c₂))) from
      (Equiv.apply_symm_apply h (Sum.inl (b₂, !c₂))).symm]
    exact conj_pairSwap_apply_of_ne h b₀ (hfinv_ne false) (hfinv_ne true)
  have hy_w : (pairSwap β γ b₂ * pairSwap β γ b₃) (h (Sum.inl (b₀, !c₀))) =
      Sum.inl (b₂, !c₂) := by
    rw [Equiv.Perm.mul_apply, hw, pairSwap_apply_of_ne_inl (Ne.symm hb₃) c₂]
    exact pairSwap_apply_inl b₂ c₂
  have hy_e : (pairSwap β γ b₂ * pairSwap β γ b₃) (Sum.inl (b₂, !c₂)) =
      h (Sum.inl (b₀, !c₀)) := by
    rw [Equiv.Perm.mul_apply, pairSwap_apply_of_ne_inl (Ne.symm hb₃) (!c₂)]
    have hstep : pairSwap β γ b₂ (Sum.inl (b₂, !c₂)) = Sum.inl (b₂, c₂) := by
      simpa using pairSwap_apply_inl b₂ (!c₂)
    rw [hstep, hw]
  have hy_inr : (pairSwap β γ b₂ * pairSwap β γ b₃) (Sum.inr x) = Sum.inr x := by
    rw [Equiv.Perm.mul_apply, pairSwap_apply_inr, pairSwap_apply_inr]
  exact not_three_cycle_pattern hQ (hh b₀ b') (hsw b₂ b₃) hw_ne he_ne_w.symm he_ne_inr.symm
    hx_w hx_inr hx_e hy_w hy_e hy_inr

theorem maps_pair_to_pair_of_doubleSwaps [Subsingleton γ] (hβ : 3 ≤ Fintype.card β)
    {Q : Subgroup (Perm ((β × Bool) ⊕ γ))} (hQ : ¬ 3 ∣ Nat.card Q)
    (hsw : ∀ b b', pairSwap β γ b * pairSwap β γ b' ∈ Q)
    {h : Perm ((β × Bool) ⊕ γ)}
    (hh : ∀ b b', h * (pairSwap β γ b * pairSwap β γ b') * h⁻¹ ∈ Q)
    (hfix : ∀ x : γ, h (Sum.inr x) = Sum.inr x) (b : β) :
    h (Sum.inl (b, true)) = pairInv β γ (h (Sum.inl (b, false))) := by
  classical
  have hinl : ∀ (b : β) (c : Bool), ∃ b₁ c₁, h (Sum.inl (b, c)) = Sum.inl (b₁, c₁) := by
    intro b c
    rcases hc : h (Sum.inl (b, c)) with bc | x
    · exact ⟨bc.1, bc.2, rfl⟩
    · exfalso
      have h : Sum.inl (b, c) = Sum.inr x := h.injective (by rw [hc, hfix x])
      exact (by simp : (Sum.inl (b, c) : (β × Bool) ⊕ γ) ≠ Sum.inr x) h
  obtain ⟨b₁, c₁, ha⟩ := hinl b false
  obtain ⟨b₆, c₆, hb'⟩ := hinl b true
  let e : (β × Bool) ⊕ γ := Sum.inl (b₁, !c₁)
  have hμa : pairInv β γ (h (Sum.inl (b, false))) = e := by
    rw [ha, pairInv_apply_inl]
  rw [hμa]
  by_contra hne
  obtain ⟨b₇, c₇, hz⟩ : ∃ b₇ c₇, h⁻¹ e = Sum.inl (b₇, c₇) := by
    rcases hz0 : h⁻¹ e with bc | y
    · exact ⟨bc.1, bc.2, by simpa using hz0⟩
    · exfalso
      have heq : e = h (Sum.inr y) := by
        rw [← hz0]
        exact (Equiv.apply_symm_apply h e).symm
      rw [hfix y] at heq
      exact (by simp [e] : e ≠ Sum.inr y) heq
  obtain ⟨b₄, hb₄_ne_b, hb₄_ne_b₇⟩ := exists_ne_of_card_three hβ b b₇
  have hfinv_ne : ∀ c : Bool, h⁻¹ e ≠ Sum.inl (b, c) := by
    intro c hp
    have heq : e = h (Sum.inl (b, c)) := by
      rw [← hp]
      exact (Equiv.apply_symm_apply h e).symm
    cases c
    · have hea : e = Sum.inl (b₁, c₁) := heq.trans ha
      have h2 : (!c₁) = c₁ := by simpa [e] using hea
      exact (Bool.not_ne_self c₁) h2
    · exact hne heq.symm
  have hb_ne_b₄ : b ≠ b₄ := Ne.symm hb₄_ne_b
  have hpair_b : (Sum.inl (b, false) : (β × Bool) ⊕ γ) ≠ Sum.inl (b₄, false) ∧
      (Sum.inl (b, false) : (β × Bool) ⊕ γ) ≠ Sum.inl (b₄, true) := by
    constructor <;> intro hh
    · have hh' : b = b₄ ∧ false = false := by simpa using hh
      exact hb_ne_b₄ hh'.1
    · have hh' : b = b₄ ∧ false = true := by simpa using hh
      exact hb_ne_b₄ hh'.1
  have hpair_b' : (Sum.inl (b, true) : (β × Bool) ⊕ γ) ≠ Sum.inl (b₄, false) ∧
      (Sum.inl (b, true) : (β × Bool) ⊕ γ) ≠ Sum.inl (b₄, true) := by
    constructor <;> intro hh
    · have hh' : b = b₄ ∧ true = false := by simpa using hh
      exact hb_ne_b₄ hh'.1
    · have hh' : b = b₄ ∧ true = true := by simpa using hh
      exact hb_ne_b₄ hh'.1
  have hx_a : (h * (pairSwap β γ b * pairSwap β γ b₄) * h⁻¹) (h (Sum.inl (b, false))) =
      h (Sum.inl (b, true)) := by
    rw [conj_pairSwap_mul, Equiv.Perm.mul_apply]
    have hstep : (h * pairSwap β γ b₄ * h⁻¹) (h (Sum.inl (b, false))) =
        h (Sum.inl (b, false)) :=
      conj_pairSwap_apply_of_ne h b₄ hpair_b.1 hpair_b.2
    rw [hstep]
    exact conj_pairSwap_apply_inl h b false
  have hx_b : (h * (pairSwap β γ b * pairSwap β γ b₄) * h⁻¹) (h (Sum.inl (b, true))) =
      h (Sum.inl (b, false)) := by
    rw [conj_pairSwap_mul, Equiv.Perm.mul_apply]
    have hstep : (h * pairSwap β γ b₄ * h⁻¹) (h (Sum.inl (b, true))) =
        h (Sum.inl (b, true)) :=
      conj_pairSwap_apply_of_ne h b₄ hpair_b'.1 hpair_b'.2
    rw [hstep]
    simpa using conj_pairSwap_apply_inl h b true
  have hfinv_ne₄ : h⁻¹ e ≠ Sum.inl (b₄, false) ∧ h⁻¹ e ≠ Sum.inl (b₄, true) := by
    rw [hz]
    constructor <;> intro hh
    · have hh' : b₇ = b₄ ∧ c₇ = false := by simpa using hh
      exact hb₄_ne_b₇ hh'.1.symm
    · have hh' : b₇ = b₄ ∧ c₇ = true := by simpa using hh
      exact hb₄_ne_b₇ hh'.1.symm
  have hx_e : (h * (pairSwap β γ b * pairSwap β γ b₄) * h⁻¹) e = e := by
    rw [conj_pairSwap_mul, Equiv.Perm.mul_apply]
    have hstep : (h * pairSwap β γ b₄ * h⁻¹) e = e := by
      rw [show e = h (h⁻¹ e) from (Equiv.apply_symm_apply h e).symm]
      exact conj_pairSwap_apply_of_ne h b₄ hfinv_ne₄.1 hfinv_ne₄.2
    rw [hstep]
    rw [show e = h (h⁻¹ e) from (Equiv.apply_symm_apply h e).symm]
    exact conj_pairSwap_apply_of_ne h b (hfinv_ne false) (hfinv_ne true)
  obtain ⟨b₅, hb₅_ne_b₁, hb₅_ne_b₆⟩ := exists_ne_of_card_three hβ b₁ b₆
  have hb₆_ne : b₆ ≠ b₁ := by
    intro hb₆
    rcases (show c₆ = c₁ ∨ c₆ = !c₁ by cases c₁ <;> cases c₆ <;> simp) with hc | hc
    · have hinj : (Sum.inl (b, false) : (β × Bool) ⊕ γ) = Sum.inl (b, true) := by
        apply h.injective
        rw [ha, hb', hb₆, hc]
      have hne_inl : (Sum.inl (b, false) : (β × Bool) ⊕ γ) ≠ Sum.inl (b, true) := by simp
      exact hne_inl hinj
    · apply hne
      rw [hb', hb₆, hc]
  have hy_a : (pairSwap β γ b₁ * pairSwap β γ b₅) (h (Sum.inl (b, false))) = e := by
    rw [Equiv.Perm.mul_apply, ha, pairSwap_apply_of_ne_inl (Ne.symm hb₅_ne_b₁) c₁]
    exact pairSwap_apply_inl b₁ c₁
  have hy_e : (pairSwap β γ b₁ * pairSwap β γ b₅) e = h (Sum.inl (b, false)) := by
    rw [Equiv.Perm.mul_apply, pairSwap_apply_of_ne_inl (Ne.symm hb₅_ne_b₁) (!c₁), ha]
    simpa [e] using pairSwap_apply_inl b₁ (!c₁)
  have hy_b : (pairSwap β γ b₁ * pairSwap β γ b₅) (h (Sum.inl (b, true))) =
      h (Sum.inl (b, true)) := by
    rw [Equiv.Perm.mul_apply, hb', pairSwap_apply_of_ne_inl (Ne.symm hb₅_ne_b₆) c₆,
      pairSwap_apply_of_ne_inl hb₆_ne c₆]
  have hab : h (Sum.inl (b, false)) ≠ h (Sum.inl (b, true)) := by
    intro hh
    have h1 : (Sum.inl (b, false) : (β × Bool) ⊕ γ) = Sum.inl (b, true) := h.injective hh
    have hne_inl : (Sum.inl (b, false) : (β × Bool) ⊕ γ) ≠ Sum.inl (b, true) := by simp
    exact hne_inl h1
  have hae : h (Sum.inl (b, false)) ≠ e := by
    rw [ha]
    intro hh
    have h2 : c₁ = !c₁ := by simpa [e] using hh
    exact (Bool.not_ne_self c₁) h2.symm
  exact not_three_cycle_pattern hQ (hh b b₄) (hsw b₁ b₅) hab hae hne
    hx_a hx_b hx_e hy_a hy_e hy_b

theorem mem_pairCent_of_doubleSwaps [Subsingleton γ] (hβ : 3 ≤ Fintype.card β)
    {Q : Subgroup (Perm ((β × Bool) ⊕ γ))} (hQ : ¬ 3 ∣ Nat.card Q)
    (hsw : ∀ b b', pairSwap β γ b * pairSwap β γ b' ∈ Q) {h : Perm ((β × Bool) ⊕ γ)}
    (hh : ∀ b b', h * (pairSwap β γ b * pairSwap β γ b') * h⁻¹ ∈ Q) : h ∈ pairCent β γ := by
  have hfix : ∀ x : γ, h (Sum.inr x) = Sum.inr x :=
    fun x => fixes_inr_of_doubleSwaps hβ hQ hsw hh x
  exact mem_pairCent_of_apply hfix fun b =>
    maps_pair_to_pair_of_doubleSwaps hβ hQ hsw hh hfix b

end CFSG.GroupTheory.PermSylowTwo

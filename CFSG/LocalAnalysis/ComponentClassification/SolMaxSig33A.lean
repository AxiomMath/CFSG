module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig32C

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {α : Type*}

theorem apply_eq_of_odd_of_mem_pair {σ w : Perm α} (hσ : σ * σ = 1) (hw : w * σ = σ * w)
    (hodd : Odd (orderOf w)) {x : α} (hx : σ x ≠ x) (hwx : w x = x ∨ w x = σ x) : w x = x := by
  rcases hwx with h | h
  · exact h
  · exfalso
    obtain ⟨j, hj⟩ := hodd
    have hwσ : w (σ x) = x := by
      rw [← Perm.mul_apply, hw, Perm.mul_apply, h, ← Perm.mul_apply, hσ, Perm.one_apply]
    have key : ∀ i : ℕ, (w ^ (2 * i + 1)) x = σ x := by
      intro i
      induction i with
      | zero => simpa using h
      | succ i ih =>
        rw [show 2 * (i + 1) + 1 = 2 + (2 * i + 1) by ring, pow_add, Perm.mul_apply, ih, sq,
          Perm.mul_apply, hwσ, h]
    have h2 := key j
    rw [← hj, pow_orderOf_eq_one, Perm.one_apply] at h2
    exact hx h2.symm

theorem mem_of_pairSwap_apply_ne [DecidableEq α] {σ : Perm α} {x z v : α}
    (hv : (swap x (σ x) * swap z (σ z)) v ≠ v) : v = x ∨ v = σ x ∨ v = z ∨ v = σ z := by
  by_contra h
  push Not at h
  apply hv
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne h.2.2.1 h.2.2.2, swap_apply_of_ne_of_ne h.1 h.2.1]

theorem apply_eq_of_odd_commute_pairs [Fintype α] [DecidableEq α] {σ w : Perm α} (hσ : σ * σ = 1)
    (hw : w * σ = σ * w)
    (hodd : Odd (orderOf w))
    (hpairs : ∀ x z : α, σ x ≠ x → σ z ≠ z → z ≠ x → z ≠ σ x →
      w * (swap x (σ x) * swap z (σ z)) = (swap x (σ x) * swap z (σ z)) * w)
    {x : α} (hx : x ∈ σ.support) : w x = x := by
  classical
  have hσσ : ∀ v, σ (σ v) = v := fun v => by rw [← Perm.mul_apply, hσ, Perm.one_apply]
  have hx' : σ x ≠ x := Perm.mem_support.mp hx
  by_cases h4 : σ.support.card ≤ 4
  · exact apply_eq_of_odd_commute hσ h4 hw hodd hx
  · push Not at h4
    refine apply_eq_of_odd_of_mem_pair hσ hw hodd hx' ?_
    have hσx : σ x ∈ σ.support := Perm.mem_support.mpr (by rw [hσσ]; exact hx'.symm)
    have hc1 : 2 < ((σ.support.erase x).erase (σ x)).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hx', hσx⟩),
        Finset.card_erase_of_mem hx]
      omega
    obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < ((σ.support.erase x).erase (σ x)).card)
    simp only [Finset.mem_erase] at hz
    obtain ⟨hzσx, hzx, hzs⟩ := hz
    have hz' : σ z ≠ z := Perm.mem_support.mp hzs
    have hσz : σ z ∈ σ.support := Perm.mem_support.mpr (by rw [hσσ]; exact hz'.symm)
    have hσzx : σ z ≠ x := fun h => hzσx (by rw [← h, hσσ])
    have hσzσx : σ z ≠ σ x := fun h => hzx (σ.injective h)
    set T := (((σ.support.erase x).erase (σ x)).erase z).erase (σ z) with hT
    have hTc : 0 < T.card := by
      have h1 : z ∈ ((σ.support.erase x).erase (σ x)) :=
        Finset.mem_erase.mpr ⟨hzσx, Finset.mem_erase.mpr ⟨hzx, hzs⟩⟩
      have h2 : σ z ∈ (((σ.support.erase x).erase (σ x)).erase z) :=
        Finset.mem_erase.mpr ⟨hz', Finset.mem_erase.mpr ⟨hσzσx, Finset.mem_erase.mpr
          ⟨hσzx, hσz⟩⟩⟩
      rw [hT, Finset.card_erase_of_mem h2, Finset.card_erase_of_mem h1]
      omega
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hTc
    simp only [hT, Finset.mem_erase] at hu
    obtain ⟨huσz, huz, huσx, hux, hus⟩ := hu
    have hu' : σ u ≠ u := Perm.mem_support.mp hus
    have hσux : σ u ≠ x := fun h => huσx (by rw [← h, hσσ])
    have hσuσx : σ u ≠ σ x := fun h => hux (σ.injective h)
    have hσuz : σ u ≠ z := fun h => huσz (by rw [← h, hσσ])
    have hσuσz : σ u ≠ σ z := fun h => huz (σ.injective h)
    have hmem : ∀ v : α, σ v ≠ v → v ≠ x → v ≠ σ x →
        w x = x ∨ w x = σ x ∨ w x = v ∨ w x = σ v := by
      intro v hv hvx hvσx
      have hc := hpairs x v hx' hv hvx hvσx
      have hbx : (swap x (σ x) * swap v (σ v)) x ≠ x := by
        rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hvx) (fun h => hvσx (by
          rw [h, hσσ])), swap_apply_left]
        exact hx'
      apply mem_of_pairSwap_apply_ne
      intro h
      apply hbx
      apply w.injective
      rw [← Perm.mul_apply, hc, Perm.mul_apply, h]
    rcases hmem z hz' hzx hzσx with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · rcases hmem u hu' hux huσx with h' | h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
      · exact absurd (h.symm.trans h') (Ne.symm huz)
      · exact absurd (h.symm.trans h') (Ne.symm hσuz)
    · rcases hmem u hu' hux huσx with h' | h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
      · exact absurd (h.symm.trans h') (Ne.symm huσz)
      · exact absurd (h.symm.trans h') (Ne.symm hσuσz)

theorem swap_mul_comm_of_involution [DecidableEq α] {σ : Perm α} (hσ : σ * σ = 1) (v : α) :
    swap v (σ v) * σ = σ * swap v (σ v) := by
  have hσσ : σ (σ v) = v := by rw [← Perm.mul_apply, hσ, Perm.one_apply]
  have h1 : σ * swap v (σ v) * σ⁻¹ = swap v (σ v) := by
    rw [← swap_apply_apply, hσσ, swap_comm]
  have hσi : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ
  calc swap v (σ v) * σ = σ * swap v (σ v) * σ⁻¹ * σ := by rw [h1]
    _ = σ * swap v (σ v) := by rw [hσi, mul_assoc, hσ, mul_one]

theorem pairSwap_commute [Fintype α] [DecidableEq α] {σ : Perm α} (hσ : σ * σ = 1) (v w : α) :
    swap v (σ v) * swap w (σ w) = swap w (σ w) * swap v (σ v) := by
  classical
  have hσσ : ∀ u, σ (σ u) = u := fun u => by rw [← Perm.mul_apply, hσ, Perm.one_apply]
  by_cases hv : σ v = v
  · rw [hv, swap_self, ← Perm.one_def, one_mul, mul_one]
  by_cases hw : σ w = w
  · rw [hw, swap_self, ← Perm.one_def, one_mul, mul_one]
  by_cases hwv : w = v
  · rw [hwv]
  by_cases hwσv : w = σ v
  · rw [hwσv, hσσ, swap_comm]
  have hσwv : σ w ≠ v := fun h => hwσv (by rw [← h, hσσ])
  have hσwσv : σ w ≠ σ v := fun h => hwv (σ.injective h)
  have hd : (swap v (σ v)).Disjoint (swap w (σ w)) := by
    rw [Perm.disjoint_iff_disjoint_support, Perm.support_swap (Ne.symm hv),
      Perm.support_swap (Ne.symm hw), Finset.disjoint_left]
    intro u hu hu'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hu'
    rcases hu with rfl | rfl <;> rcases hu' with h | h
    · exact hwv h.symm
    · exact hσwv h.symm
    · exact hwσv h.symm
    · exact hσwσv h.symm
  exact hd.commute.eq

variable {n : ℕ}

theorem eq_bot_of_odd_normal_centralizer {τ : Perm (Fin n)} (hτ : τ * τ = 1)
    (h5 : 5 ≤ n - τ.support.card) {N : Subgroup (alternatingGroup (Fin n))}
    (hodd : Odd (Nat.card N)) (hc : ∀ g ∈ N, (g : Perm (Fin n)) * τ = τ * g)
    (hn : ∀ b : alternatingGroup (Fin n), (b : Perm (Fin n)) * τ = τ * b →
      ∀ g ∈ N, b * g * b⁻¹ ∈ N) : N = ⊥ := by
  classical
  have hpair : ∀ g ∈ N, ∀ x z : Fin n, τ x ≠ x → τ z ≠ z → z ≠ x → z ≠ τ x →
      (g : Perm (Fin n)) * (swap x (τ x) * swap z (τ z)) =
        (swap x (τ x) * swap z (τ z)) * g := by
    intro g hg x z hx hz hzx hzτx
    set b₀ : Perm (Fin n) := swap x (τ x) * swap z (τ z) with hb₀
    have hb₀A : b₀ ∈ alternatingGroup (Fin n) := by
      rw [Perm.mem_alternatingGroup, hb₀, Perm.sign_mul, Perm.sign_swap (Ne.symm hx),
        Perm.sign_swap (Ne.symm hz)]
      rfl
    have hb₀τ : b₀ * τ = τ * b₀ := by
      rw [hb₀, mul_assoc, swap_mul_comm_of_involution hτ z, ← mul_assoc,
        swap_mul_comm_of_involution hτ x, mul_assoc]
    set b : alternatingGroup (Fin n) := ⟨b₀, hb₀A⟩ with hbdef
    have hgτ := hc g hg
    have hgτ' : ∀ v, (g : Perm (Fin n)) (τ v) = τ ((g : Perm (Fin n)) v) := fun v => by
      rw [← Perm.mul_apply, hgτ, Perm.mul_apply]
    have hconj : (g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹ =
        swap ((g : Perm (Fin n)) x) (τ ((g : Perm (Fin n)) x)) *
          swap ((g : Perm (Fin n)) z) (τ ((g : Perm (Fin n)) z)) := by
      rw [← hgτ', ← hgτ', swap_apply_apply, swap_apply_apply, hb₀]
      group
    have hcomm : ((g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹) * b₀ =
        b₀ * ((g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹) := by
      rw [hconj, hb₀]
      set s₁ := swap ((g : Perm (Fin n)) x) (τ ((g : Perm (Fin n)) x))
      set s₂ := swap ((g : Perm (Fin n)) z) (τ ((g : Perm (Fin n)) z))
      set s₃ := swap x (τ x)
      set s₄ := swap z (τ z)
      have h13 : s₁ * s₃ = s₃ * s₁ := pairSwap_commute hτ _ _
      have h14 : s₁ * s₄ = s₄ * s₁ := pairSwap_commute hτ _ _
      have h23 : s₂ * s₃ = s₃ * s₂ := pairSwap_commute hτ _ _
      have h24 : s₂ * s₄ = s₄ * s₂ := pairSwap_commute hτ _ _
      calc s₁ * s₂ * (s₃ * s₄) = s₁ * (s₂ * s₃) * s₄ := by group
        _ = s₁ * (s₃ * s₂) * s₄ := by rw [h23]
        _ = (s₁ * s₃) * (s₂ * s₄) := by group
        _ = (s₃ * s₁) * (s₄ * s₂) := by rw [h13, h24]
        _ = s₃ * (s₁ * s₄) * s₂ := by group
        _ = s₃ * (s₄ * s₁) * s₂ := by rw [h14]
        _ = s₃ * s₄ * (s₁ * s₂) := by group
    have hb2 : b₀ * b₀ = 1 := by
      rw [hb₀]
      calc swap x (τ x) * swap z (τ z) * (swap x (τ x) * swap z (τ z)) =
          swap x (τ x) * (swap z (τ z) * swap x (τ x)) * swap z (τ z) := by group
        _ = swap x (τ x) * (swap x (τ x) * swap z (τ z)) * swap z (τ z) := by
            rw [pairSwap_commute hτ z x]
        _ = 1 := by simp [← mul_assoc]
    have hk : g * b * g⁻¹ * b⁻¹ ∈ N := by
      have h1 : b * g⁻¹ * b⁻¹ ∈ N := hn b hb₀τ g⁻¹ (inv_mem hg)
      have h2 : g * (b * g⁻¹ * b⁻¹) ∈ N := mul_mem hg h1
      simpa [mul_assoc] using h2
    have hk2 : (g * b * g⁻¹ * b⁻¹) * (g * b * g⁻¹ * b⁻¹) = 1 := by
      apply Subtype.ext
      have hbinv : (b⁻¹ : alternatingGroup (Fin n)) = b := by
        apply inv_eq_of_mul_eq_one_right
        exact Subtype.ext hb2
      rw [hbinv]
      change ((g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹ * b₀) *
        ((g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹ * b₀) = 1
      have hgb2 : ((g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹) *
          ((g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹) = 1 := by
        calc ((g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹) *
            ((g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹) =
            (g : Perm (Fin n)) * (b₀ * b₀) * (g : Perm (Fin n))⁻¹ := by group
          _ = 1 := by rw [hb2]; group
      calc ((g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹ * b₀) *
          ((g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹ * b₀) =
          ((g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹) *
            (b₀ * ((g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹)) * b₀ := by group
        _ = ((g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹) *
            (((g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹) * b₀) * b₀ := by rw [hcomm]
        _ = (((g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹) *
            ((g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹)) * (b₀ * b₀) := by group
        _ = 1 := by rw [hgb2, hb2, one_mul]
    have hk1 : g * b * g⁻¹ * b⁻¹ = 1 := by
      have h1 : orderOf (⟨_, hk⟩ : N) ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (by rw [sq]; exact Subtype.ext hk2)
      have h2 : orderOf (⟨_, hk⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
      have h3 : orderOf (⟨_, hk⟩ : N) = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
        · exact h
        · rw [h] at h2
          exact absurd (even_iff_two_dvd.mpr h2) (Nat.not_even_iff_odd.mpr hodd)
      have := congrArg Subtype.val (orderOf_eq_one_iff.mp h3)
      exact this
    have h5' : (g : Perm (Fin n)) * b₀ = b₀ * g := by
      have h6 := congrArg Subtype.val hk1
      change (g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹ * (b⁻¹ : alternatingGroup _) = 1 at h6
      have hbinv : ((b⁻¹ : alternatingGroup (Fin n)) : Perm (Fin n)) = b₀⁻¹ := rfl
      rw [hbinv] at h6
      calc (g : Perm (Fin n)) * b₀ = ((g : Perm (Fin n)) * b₀ * (g : Perm (Fin n))⁻¹ * b₀⁻¹) *
          (b₀ * g) := by group
        _ = b₀ * g := by rw [h6, one_mul]
    exact h5'
  have hle : N ≤ fixAlt τ := by
    intro g hg
    have hog : Odd (orderOf (g : Perm (Fin n))) := by
      rw [Subgroup.orderOf_coe]
      have h1 : orderOf g ∣ Nat.card N := by
        rw [← Subgroup.orderOf_mk g hg]
        exact orderOf_dvd_natCard _
      exact hodd.of_dvd_nat h1
    rw [mem_fixAlt]
    intro z hz
    rw [Finset.mem_compl]
    intro hzτ
    exact (Perm.mem_support.mp hz)
      (apply_eq_of_odd_commute_pairs hτ (hc g hg) hog (hpair g hg) hzτ)
  have : IsSimpleGroup (fixAlt τ) := isSimpleGroup_fixAlt h5
  have hnorm : (N.subgroupOf (fixAlt τ)).Normal := by
    constructor
    intro g hg b
    rw [mem_subgroupOf] at hg ⊢
    exact hn b (commute_of_mem_fixAlt b.2) g hg
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (fixAlt τ)) with h | h
  · rwa [subgroupOf_eq_bot, disjoint_iff, inf_of_le_left hle] at h
  · exfalso
    rw [subgroupOf_eq_top] at h
    have h1 : Nat.card (fixAlt τ) ∣ Nat.card N := card_dvd_of_le h
    have h2 : Even (Nat.card (fixAlt τ)) := by
      rw [Nat.card_congr (fixAltEquiv τ).symm.toEquiv]
      exact even_card_alternatingGroup (by
        rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
        omega)
    exact (Nat.not_even_iff_odd.mpr (hodd.of_dvd_nat h1)) h2

end CFSG.ComponentClassification.SolMax

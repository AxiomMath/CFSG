module

public import CFSG.ClassicalInvolution.Q3.Sec13StarCount

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.F94

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3

variable {G : Type} [Group G] [Finite G]

section Q8

variable {L : Subgroup G} {s : G}

theorem comm_of_mem_q8 (hs : IsUniqueInvolution L s) {x : G} (hx : x ∈ L) : x * s = s * x :=
  mul_inv_eq_iff_eq_mul.1 (hs.conj_eq (conjSub_eq_self_of_mem hx))

theorem orderOf_eq_four_of_sq_q8 (h8 : Nat.card L = 8)
    (hnab : ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x) {w : G} (hw : w ∈ L) (hw2 : w * w ≠ 1) :
    orderOf w = 4 := by
  have hdvd : orderOf w ∣ 8 := h8 ▸ L.orderOf_dvd_natCard hw
  have h1 : orderOf w ≠ 1 := fun h => hw2 (by rw [orderOf_eq_one_iff.1 h, mul_one])
  have h2 : orderOf w ≠ 2 := fun h => hw2 (by rw [← sq, ← h, pow_orderOf_eq_one])
  have h8' : orderOf w ≠ 8 := by
    intro h
    have heq : Subgroup.zpowers w = L :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hw) (by rw [h8, Nat.card_zpowers, h])
    obtain ⟨x, hx, y, hy, hxy⟩ := hnab
    rw [← heq, Subgroup.mem_zpowers_iff] at hx hy
    obtain ⟨m, rfl⟩ := hx
    obtain ⟨n, rfl⟩ := hy
    exact hxy (Commute.zpow_zpow_self w m n).eq
  obtain ⟨k, hk⟩ : ∃ k, orderOf w = k := ⟨_, rfl⟩
  rw [hk] at hdvd h1 h2 h8' ⊢
  have hpos : 0 < k := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  have hle : k ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases k <;> omega

theorem mul_self_eq_q8 (hs : IsUniqueInvolution L s) (h8 : Nat.card L = 8)
    (hnab : ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x) {w : G} (hw : w ∈ L) (hw1 : w ≠ 1) (hws : w ≠ s) :
    w * w = s := by
  have hw2 : w * w ≠ 1 := fun h => (hs.unique w hw h).elim hw1 hws
  have h4 : w ^ 4 = 1 := by
    rw [← orderOf_eq_four_of_sq_q8 h8 hnab hw hw2]
    exact pow_orderOf_eq_one w
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq] at h4
  exact (hs.unique _ (L.mul_mem hw hw) h4).resolve_left hw2

theorem orderOf_eq_four_q8 (hs : IsUniqueInvolution L s) (h8 : Nat.card L = 8)
    (hnab : ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x) {w : G} (hw : w ∈ L) (hw1 : w ≠ 1) (hws : w ≠ s) :
    orderOf w = 4 :=
  orderOf_eq_four_of_sq_q8 h8 hnab hw fun h => (hs.unique w hw h).elim hw1 hws

theorem commutator_eq_q8 (hs : IsUniqueInvolution L s) (h8 : Nat.card L = 8)
    (hnab : ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x) {x y : G} (hx : x ∈ L) (hy : y ∈ L) :
    x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = s := by
  have key : ∀ a ∈ L, a = 1 ∨ a = s → ∀ b ∈ L, a * b = b * a := by
    rintro a - (rfl | rfl) b hb
    · rw [one_mul, mul_one]
    · exact (comm_of_mem_q8 hs hb).symm
  by_cases hx1 : x = 1 ∨ x = s
  · left
    rw [key x hx hx1 y hy, mul_inv_cancel_right, mul_inv_cancel]
  by_cases hy1 : y = 1 ∨ y = s
  · left
    rw [← key y hy hy1 x hx, mul_inv_cancel_right, mul_inv_cancel]
  push Not at hx1 hy1
  have hxs := mul_self_eq_q8 hs h8 hnab hx hx1.1 hx1.2
  have hys := mul_self_eq_q8 hs h8 hnab hy hy1.1 hy1.2
  have hxi : x⁻¹ = x * s := by
    rw [inv_eq_iff_mul_eq_one, ← mul_assoc, hxs, hs.sq]
  have hyi : y⁻¹ = y * s := by
    rw [inv_eq_iff_mul_eq_one, ← mul_assoc, hys, hs.sq]
  have hxy : x * y * x⁻¹ * y⁻¹ = x * y * (x * y) := by
    rw [hxi, hyi]
    calc x * y * (x * s) * (y * s) = x * y * x * (s * y) * s := by group
      _ = x * y * x * (y * s) * s := by rw [comm_of_mem_q8 hs hy]
      _ = x * y * (x * y) * (s * s) := by group
      _ = x * y * (x * y) := by rw [hs.sq, mul_one]
  rw [hxy]
  by_cases h : x * y = 1 ∨ x * y = s
  · left
    rcases h with h | h <;> rw [h]
    · rw [mul_one]
    · exact hs.sq
  · push Not at h
    exact Or.inr (mul_self_eq_q8 hs h8 hnab (L.mul_mem hx hy) h.1 h.2)

theorem exists_fixed_q8 (hs : IsUniqueInvolution L s) (h8 : Nat.card L = 8)
    (hnab : ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x) {y : G} (hyL : ∀ l ∈ L, y * l * y⁻¹ ∈ L)
    (hy2 : y * y = 1) :
    ∃ x ∈ L, orderOf x = 4 ∧ (y * x * y⁻¹ = x ∨ y * x * y⁻¹ = x * s) := by
  obtain ⟨a, ha, b, hb, hab⟩ := hnab
  have hnab : ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x := ⟨a, ha, b, hb, hab⟩
  have ha1 : a ≠ 1 := by rintro rfl; exact hab (by rw [one_mul, mul_one])
  have has : a ≠ s := by rintro rfl; exact hab (comm_of_mem_q8 hs hb).symm
  have ha4 := orderOf_eq_four_q8 hs h8 hnab ha ha1 has
  have hasq := mul_self_eq_q8 hs h8 hnab ha ha1 has
  have hai : a⁻¹ = a * s := by
    rw [inv_eq_iff_mul_eq_one, ← mul_assoc, hasq, hs.sq]
  set a' := y * a * y⁻¹ with ha'
  have ha'L : a' ∈ L := hyL a ha
  by_cases hfix : a' = a ∨ a' = a * s
  · exact ⟨a, ha, ha4, hfix⟩
  push Not at hfix
  have hx1 : a * a' ≠ 1 := by
    intro h
    apply hfix.2
    rw [← hai]
    exact eq_inv_of_mul_eq_one_right h
  have hxs : a * a' ≠ s := by
    intro h
    apply hfix.1
    have : a' = a⁻¹ * s := by rw [← h, inv_mul_cancel_left]
    rw [this, hai, mul_assoc, hs.sq, mul_one]
  refine ⟨a * a', L.mul_mem ha ha'L, orderOf_eq_four_q8 hs h8 hnab (L.mul_mem ha ha'L) hx1 hxs, ?_⟩
  have hconj : y * (a * a') * y⁻¹ = a' * a := by
    calc y * (a * a') * y⁻¹ = a' * ((y * y) * a * (y * y)⁻¹) := by rw [ha']; group
      _ = a' * a := by rw [hy2, one_mul, inv_one, mul_one]
  rw [hconj]
  have hc : a' * a = (a' * a * a'⁻¹ * a⁻¹) * (a * a') := by group
  rcases commutator_eq_q8 hs h8 hnab ha'L ha with h | h
  · left
    rw [hc, h, one_mul]
  · right
    rw [hc, h, ← comm_of_mem_q8 hs (L.mul_mem ha ha'L)]

end Q8

theorem comm_of_conj_eq' {x y : G} (h : y * x * y⁻¹ = x) : x * y = y * x := by
  calc x * y = y * x * y⁻¹ * y := by rw [h]
    _ = y * x := by group

theorem conj_eq_of_comm' {x y : G} (h : x * y = y * x) : y * x * y⁻¹ = x := by
  rw [← h, mul_inv_cancel_right]

theorem core_false {L L' : Subgroup G} {s z e : G}
    (hs : IsUniqueInvolution L s) (hs' : IsUniqueInvolution L' s)
    (h8 : Nat.card L = 8) (h8' : Nat.card L' = 8)
    (hnab : ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x) (hnab' : ∃ x ∈ L', ∃ y ∈ L', x * y ≠ y * x)
    (hcomm : ∀ x ∈ L, ∀ y ∈ L', x * y = y * x) (hinf : ∀ w ∈ L, w ∈ L' → w = 1 ∨ w = s)
    (hz2 : z * z = 1) (he2 : e * e = 1) (hze : z * e = e * z)
    (hzP : (conjSub z L = L ∧ conjSub z L' = L') ∨ (conjSub z L = L' ∧ conjSub z L' = L))
    (heP : (conjSub e L = L ∧ conjSub e L' = L') ∨ (conjSub e L = L' ∧ conjSub e L' = L))
    (hV : ∀ d ∈ L ⊔ L', d * z = z * d → d * e = e * d)
    (F3 : ∀ d ∈ L ⊔ L', d * (e * z) = (e * z) * d → d * z = z * d)
    (F1 : ∀ x ∈ L, orderOf x = 4 → x * e ≠ e * x)
    (F2 : ∀ x ∈ L, orderOf x = 4 → x * z ≠ z * x)
    (F2' : ∀ x ∈ L', orderOf x = 4 → x * z ≠ z * x) : False := by
  have hdec : ∀ a ∈ L, ∀ a' ∈ L, ∀ b ∈ L', ∀ b' ∈ L', a * b = a' * b' →
      a' = a ∨ a' = a * s := by
    intro a ha a' ha' b hb b' hb' h
    have h1 : a⁻¹ * a' = b * b'⁻¹ := by
      calc a⁻¹ * a' = a⁻¹ * (a' * b') * b'⁻¹ := by group
        _ = a⁻¹ * (a * b) * b'⁻¹ := by rw [h]
        _ = b * b'⁻¹ := by group
    have hL1 : a⁻¹ * a' ∈ L := L.mul_mem (L.inv_mem ha) ha'
    have hL2 : a⁻¹ * a' ∈ L' := h1 ▸ L'.mul_mem hb (L'.inv_mem hb')
    rcases hinf _ hL1 hL2 with h3 | h3
    · left
      calc a' = a * (a⁻¹ * a') := by group
        _ = a := by rw [h3, mul_one]
    · right
      calc a' = a * (a⁻¹ * a') := by group
        _ = a * s := by rw [h3]
  have hcz : ∀ y : G, ∀ M N : Subgroup G, conjSub y M = N → ∀ m ∈ M, y * m * y⁻¹ ∈ N :=
    fun y M N h m hm => h ▸ conj_mem_conjSub hm
  have hes : e * s * e⁻¹ = s := by
    rcases heP with ⟨h, -⟩ | ⟨h, -⟩
    · exact (hs.conj e).eq (by rw [h]; exact hs)
    · exact (hs.conj e).eq (by rw [h]; exact hs')
  have hw2 : e * z * (e * z) = 1 := by
    calc e * z * (e * z) = e * (z * e) * z := by group
      _ = e * e * (z * z) := by rw [hze]; group
      _ = 1 := by rw [he2, hz2, mul_one]
  rcases hzP with ⟨hzL, hzL'⟩ | ⟨hzL, hzL'⟩
  ·
    rcases heP with ⟨heL, heL'⟩ | ⟨heL, heL'⟩
    ·
      obtain ⟨x₁, hx₁, hx₁4, hzx₁⟩ := exists_fixed_q8 hs h8 hnab (hcz z L L hzL) hz2
      have hzx₁' : z * x₁ * z⁻¹ = x₁ * s :=
        hzx₁.resolve_left fun h => F2 x₁ hx₁ hx₁4 (comm_of_conj_eq' h)
      obtain ⟨x₂, hx₂, hx₂4, hzx₂⟩ := exists_fixed_q8 hs' h8' hnab' (hcz z L' L' hzL') hz2
      have hzx₂' : z * x₂ * z⁻¹ = x₂ * s :=
        hzx₂.resolve_left fun h => F2' x₂ hx₂ hx₂4 (comm_of_conj_eq' h)
      have hdz : x₁ * x₂ * z = z * (x₁ * x₂) := by
        apply comm_of_conj_eq'
        calc z * (x₁ * x₂) * z⁻¹ = (z * x₁ * z⁻¹) * (z * x₂ * z⁻¹) := by group
          _ = x₁ * (s * x₂) * s := by rw [hzx₁', hzx₂']; group
          _ = x₁ * (x₂ * s) * s := by rw [comm_of_mem_q8 hs' hx₂]
          _ = x₁ * x₂ * (s * s) := by group
          _ = x₁ * x₂ := by rw [hs.sq, mul_one]
      have hde : x₁ * x₂ * e = e * (x₁ * x₂) :=
        hV _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hx₁) (Subgroup.mem_sup_right hx₂)) hdz
      have hex : e * x₁ * e⁻¹ = x₁ ∨ e * x₁ * e⁻¹ = x₁ * s := by
        refine hdec x₁ hx₁ _ (hcz e L L heL x₁ hx₁) x₂ hx₂ _ (hcz e L' L' heL' x₂ hx₂) ?_
        calc x₁ * x₂ = e * (x₁ * x₂) * e⁻¹ := (conj_eq_of_comm' hde).symm
          _ = e * x₁ * e⁻¹ * (e * x₂ * e⁻¹) := by group
      rcases hex with h | h
      · exact F1 x₁ hx₁ hx₁4 (comm_of_conj_eq' h)
      · refine F2 x₁ hx₁ hx₁4 (F3 x₁ (Subgroup.mem_sup_left hx₁) (comm_of_conj_eq' ?_))
        calc e * z * x₁ * (e * z)⁻¹ = e * (z * x₁ * z⁻¹) * e⁻¹ := by group
          _ = e * x₁ * e⁻¹ * (e * s * e⁻¹) := by rw [hzx₁']; group
          _ = x₁ := by rw [h, hes, mul_assoc, hs.sq, mul_one]
    ·
      have hwL : conjSub (e * z) L = L' := by rw [conjSub_mul, hzL, heL]
      have key : ∀ l ∈ L, z * l * z⁻¹ = l ∨ z * l * z⁻¹ = l * s := by
        intro l hl
        have hl' : e * z * l * (e * z)⁻¹ ∈ L' := hcz (e * z) L L' hwL l hl
        have hd : l * (e * z * l * (e * z)⁻¹) * (e * z) =
            (e * z) * (l * (e * z * l * (e * z)⁻¹)) := by
          apply comm_of_conj_eq'
          calc e * z * (l * (e * z * l * (e * z)⁻¹)) * (e * z)⁻¹ =
              (e * z * l * (e * z)⁻¹) * ((e * z * (e * z)) * l * (e * z * (e * z))⁻¹) := by
                group
            _ = e * z * l * (e * z)⁻¹ * l := by rw [hw2, one_mul, inv_one, mul_one]
            _ = l * (e * z * l * (e * z)⁻¹) := (hcomm l hl _ hl').symm
        have hdz := F3 _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hl)
          (Subgroup.mem_sup_right hl')) hd
        refine hdec l hl _ (hcz z L L hzL l hl) _ hl' _ (hcz z L' L' hzL' _ hl') ?_
        calc l * (e * z * l * (e * z)⁻¹) = z * (l * (e * z * l * (e * z)⁻¹)) * z⁻¹ :=
              (conj_eq_of_comm' hdz).symm
          _ = z * l * z⁻¹ * (z * (e * z * l * (e * z)⁻¹) * z⁻¹) := by group
      obtain ⟨x, hx, hx4, hxz⟩ := Sec13.exists_comm_orderOf_four hs h8 hnab key
      exact F2 x hx hx4 hxz.symm
  ·
    have hdle : ∀ l ∈ L, l * (z * l * z⁻¹) * e = e * (l * (z * l * z⁻¹)) := by
      intro l hl
      have hl' : z * l * z⁻¹ ∈ L' := hcz z L L' hzL l hl
      have hdz : l * (z * l * z⁻¹) * z = z * (l * (z * l * z⁻¹)) := by
        apply comm_of_conj_eq'
        calc z * (l * (z * l * z⁻¹)) * z⁻¹ = (z * l * z⁻¹) * ((z * z) * l * (z * z)⁻¹) := by
              group
          _ = z * l * z⁻¹ * l := by rw [hz2, one_mul, inv_one, mul_one]
          _ = l * (z * l * z⁻¹) := (hcomm l hl _ hl').symm
      exact hV _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right hl')) hdz
    rcases heP with ⟨heL, heL'⟩ | ⟨heL, heL'⟩
    ·
      have key : ∀ l ∈ L, e * l * e⁻¹ = l ∨ e * l * e⁻¹ = l * s := by
        intro l hl
        have hl' : z * l * z⁻¹ ∈ L' := hcz z L L' hzL l hl
        refine hdec l hl _ (hcz e L L heL l hl) _ hl' _ (hcz e L' L' heL' _ hl') ?_
        calc l * (z * l * z⁻¹) = e * (l * (z * l * z⁻¹)) * e⁻¹ :=
              (conj_eq_of_comm' (hdle l hl)).symm
          _ = e * l * e⁻¹ * (e * (z * l * z⁻¹) * e⁻¹) := by group
      obtain ⟨x, hx, hx4, hxe⟩ := Sec13.exists_comm_orderOf_four hs h8 hnab key
      exact F1 x hx hx4 hxe.symm
    ·
      have hwL : conjSub (e * z) L = L := by rw [conjSub_mul, hzL, heL']
      have key : ∀ l ∈ L, e * z * l * (e * z)⁻¹ = l ∨ e * z * l * (e * z)⁻¹ = l * s := by
        intro l hl
        have hl' : z * l * z⁻¹ ∈ L' := hcz z L L' hzL l hl
        have hel : e * l * e⁻¹ ∈ L' := hcz e L L' heL l hl
        have hwl : e * z * l * (e * z)⁻¹ ∈ L := hcz (e * z) L L hwL l hl
        refine hdec l hl _ hwl _ hl' _ hel ?_
        calc l * (z * l * z⁻¹) = e * (l * (z * l * z⁻¹)) * e⁻¹ :=
              (conj_eq_of_comm' (hdle l hl)).symm
          _ = e * l * e⁻¹ * (e * z * l * (e * z)⁻¹) := by group
          _ = e * z * l * (e * z)⁻¹ * (e * l * e⁻¹) := (hcomm _ hwl _ hel).symm
      obtain ⟨x, hx, hx4, hxw⟩ := Sec13.exists_comm_orderOf_four hs h8 hnab key
      exact F2 x hx hx4 (F3 x (Subgroup.mem_sup_left hx) hxw.symm)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.F94

module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BSL23

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G]

private lemma sec5b_mul_comm_prod {K₃ K₄ : Subgroup G}
    (hcomm : ∀ a ∈ K₃, ∀ b ∈ K₄, a * b = b * a)
    {a a' : G} (ha : a ∈ K₃) (ha' : a' ∈ K₃) {b b' : G} (hb : b ∈ K₄) (hb' : b' ∈ K₄) :
    (a * b) * (a' * b') = (a * a') * (b * b') := by
  rw [mul_assoc a b (a' * b'), ← mul_assoc b a' b', (hcomm a' ha' b hb).symm,
    mul_assoc a' b b', ← mul_assoc a a' (b * b')]

private lemma sec5b_conj_eq_of_comm {a x : G} (h : a * x = x * a) : x⁻¹ * a * x = a := by
  rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]

private lemma sec5b_conj_mul_eq {a m : G} (h : Commute a m) : a * m * a⁻¹ = m := by
  rw [h.eq, mul_assoc, mul_inv_cancel, mul_one]

private lemma sec5b_conj_mul_inv {a b c : G} (hbc : b * c = c * b) :
    c⁻¹ * (a * b) * c * (a * b)⁻¹ = c⁻¹ * a * c * a⁻¹ := by
  have habc : (a * b) * c = (a * c) * b := by
    rw [mul_assoc a b c, hbc, ← mul_assoc a c b]
  rw [mul_inv_rev, mul_assoc c⁻¹ (a * b) c, habc, ← mul_assoc c⁻¹ (a * c) b,
      mul_assoc (c⁻¹ * (a * c)) b (b⁻¹ * a⁻¹), ← mul_assoc b b⁻¹ a⁻¹,
      mul_inv_cancel, one_mul, ← mul_assoc c⁻¹ a c]

private lemma sec5b_conj_mul_inv_right {a₀ b₀ x : G} (hx : a₀ * x = x * a₀)
    (hb : a₀ * b₀ = b₀ * a₀) :
    x⁻¹ * (a₀ * b₀) * x * (a₀ * b₀)⁻¹ = x⁻¹ * b₀ * x * b₀⁻¹ := by
  have hxca : x⁻¹ * a₀ * x = a₀ := sec5b_conj_eq_of_comm hx
  have hax : Commute a₀ x := hx
  have hab : Commute a₀ b₀ := hb
  have hcomm_m : Commute a₀ (x⁻¹ * b₀ * x * b₀⁻¹) :=
    ((hax.inv_right.mul_right hab).mul_right hax).mul_right hab.inv_right
  have hconj : x⁻¹ * (a₀ * b₀) * x = (x⁻¹ * a₀ * x) * (x⁻¹ * b₀ * x) := by
    simpa using (conj_mul (b := x⁻¹) (a := a₀) (c := b₀)).symm
  calc x⁻¹ * (a₀ * b₀) * x * (a₀ * b₀)⁻¹
      = (x⁻¹ * a₀ * x) * (x⁻¹ * b₀ * x) * (a₀ * b₀)⁻¹ := by rw [hconj]
    _ = a₀ * (x⁻¹ * b₀ * x) * (a₀ * b₀)⁻¹ := by rw [hxca]
    _ = a₀ * (x⁻¹ * b₀ * x * b₀⁻¹) * a₀⁻¹ := by
        rw [mul_inv_rev]; simp only [mul_assoc]
    _ = x⁻¹ * b₀ * x * b₀⁻¹ := sec5b_conj_mul_eq hcomm_m

private lemma sec5b_eq_of_comm_conj_of_iso {K : Subgroup G} (e : ↥K ≃* SL23) {z a₀ a : G}
    (hz : z ∈ K) (hz2 : z * z = 1) (hz1 : z ≠ 1) (ha₀ : a₀ ∈ K) (ha : a ∈ K)
    (ha0 : a₀ * a₀ = z)
    (h : ∀ c ∈ K, a * (c⁻¹ * a₀ * c * a₀⁻¹) = (c⁻¹ * a₀ * c * a₀⁻¹) * a) :
    a = 1 ∨ a = z := by
  have hζ : e ⟨z, hz⟩ * e ⟨z, hz⟩ = 1 := by
    rw [← map_mul, ← map_one e]
    congr 1
    apply Subtype.ext
    simpa using hz2
  have hζ1 : e ⟨z, hz⟩ ≠ 1 := by
    intro hc
    have hsub : (⟨z, hz⟩ : ↥K) = 1 := e.injective (by rw [hc, map_one])
    exact hz1 (congrArg Subtype.val hsub)
  have hA0 : e ⟨a₀, ha₀⟩ * e ⟨a₀, ha₀⟩ = e ⟨z, hz⟩ := by
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    simpa using ha0
  have key : ∀ g : SL23,
      e ⟨a, ha⟩ * (g⁻¹ * e ⟨a₀, ha₀⟩ * g * (e ⟨a₀, ha₀⟩)⁻¹) =
        (g⁻¹ * e ⟨a₀, ha₀⟩ * g * (e ⟨a₀, ha₀⟩)⁻¹) * e ⟨a, ha⟩ := by
    intro g
    obtain ⟨c, rfl⟩ := e.surjective g
    let n : ↥K := c⁻¹ * ⟨a₀, ha₀⟩ * c * ⟨a₀, ha₀⟩⁻¹
    have hn : e n = (e c)⁻¹ * e ⟨a₀, ha₀⟩ * e c * (e ⟨a₀, ha₀⟩)⁻¹ := by
      simp only [n, map_mul, map_inv]
    have hh : e ⟨a, ha⟩ * e n = e n * e ⟨a, ha⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact h c.1 c.2
    simp only [← hn]
    exact hh
  rcases sec5b_sl23_eq_of_comm_conj hζ hζ1 hA0 key with h1 | h1
  · left
    have hsub : (⟨a, ha⟩ : ↥K) = 1 := e.injective (by rw [h1, map_one])
    exact congrArg Subtype.val hsub
  · right
    have hsub : (⟨a, ha⟩ : ↥K) = ⟨z, hz⟩ := e.injective h1
    exact congrArg Subtype.val hsub

theorem sec5b_mem_sup_of_comm {K₃ K₄ : Subgroup G} (hcomm : ∀ a ∈ K₃, ∀ b ∈ K₄, a * b = b * a)
    {x : G} (hx : x ∈ K₃ ⊔ K₄) : ∃ a ∈ K₃, ∃ b ∈ K₄, x = a * b := by
  let P : Subgroup G :=
    { carrier := {x | ∃ a ∈ K₃, ∃ b ∈ K₄, x = a * b}
      mul_mem' := by
        rintro x y ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        exact ⟨a * a', K₃.mul_mem ha ha', b * b', K₄.mul_mem hb hb',
          sec5b_mul_comm_prod hcomm ha ha' hb hb'⟩
      one_mem' := ⟨1, K₃.one_mem, 1, K₄.one_mem, by rw [mul_one]⟩
      inv_mem' := by
        rintro x ⟨a, ha, b, hb, rfl⟩
        exact ⟨a⁻¹, K₃.inv_mem ha, b⁻¹, K₄.inv_mem hb,
          by rw [mul_inv_rev, (hcomm a⁻¹ (K₃.inv_mem ha) b⁻¹ (K₄.inv_mem hb)).symm]⟩ }
  have h3 : K₃ ≤ P := fun a ha => ⟨a, ha, 1, K₄.one_mem, by rw [mul_one]⟩
  have h4 : K₄ ≤ P := fun b hb => ⟨1, K₃.one_mem, b, hb, by rw [one_mul]⟩
  exact (sup_le h3 h4) hx

theorem sec5b_centProd_cent {K₃ K₄ : Subgroup G} (e₃ : ↥K₃ ≃* SL23) (e₄ : ↥K₄ ≃* SL23)
    (hcomm : ∀ a ∈ K₃, ∀ b ∈ K₄, a * b = b * a) {z : G} (hz3 : z ∈ K₃) (hz4 : z ∈ K₄)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) {t : G} (ht : t ∈ K₃ ⊔ K₄) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (htz : t ≠ z) {y : G} (hy : y ∈ K₃ ⊔ K₄)
    (hyc : ∀ x ∈ K₃ ⊔ K₄, y * (x⁻¹ * t * x) = (x⁻¹ * t * x) * y) : y = 1 ∨ y = z := by
  obtain ⟨a₀, ha₀, b₀, hb₀, ht_eq⟩ := sec5b_mem_sup_of_comm hcomm ht
  subst ht_eq
  obtain ⟨a, ha, b, hb, hy_eq⟩ := sec5b_mem_sup_of_comm hcomm hy
  have hww : a₀ * a₀ * (b₀ * b₀) = 1 := by
    rw [← sec5b_mul_comm_prod hcomm ha₀ ha₀ hb₀ hb₀]
    exact ht2
  have hw4 : a₀ * a₀ ∈ K₄ := by
    have h : a₀ * a₀ = (b₀ * b₀)⁻¹ := eq_inv_of_mul_eq_one_left hww
    rw [h]
    exact K₄.inv_mem (K₄.mul_mem hb₀ hb₀)
  have hw_central : ∀ c : SL23,
      e₃ ⟨a₀ * a₀, K₃.mul_mem ha₀ ha₀⟩ * c = c * e₃ ⟨a₀ * a₀, K₃.mul_mem ha₀ ha₀⟩ := by
    intro c
    obtain ⟨c', rfl⟩ := e₃.surjective c
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (hcomm c'.1 c'.2 (a₀ * a₀) hw4).symm
  have hζ₃ : e₃ ⟨z, hz3⟩ * e₃ ⟨z, hz3⟩ = 1 := by
    rw [← map_mul, ← map_one e₃]
    congr 1
    apply Subtype.ext
    simpa using hz2
  have hζ₃1 : e₃ ⟨z, hz3⟩ ≠ 1 := by
    intro hc
    have hsub : (⟨z, hz3⟩ : ↥K₃) = 1 := e₃.injective (by rw [hc, map_one])
    exact hz1 (congrArg Subtype.val hsub)
  have hζ₄ : e₄ ⟨z, hz4⟩ * e₄ ⟨z, hz4⟩ = 1 := by
    rw [← map_mul, ← map_one e₄]
    congr 1
    apply Subtype.ext
    simpa using hz2
  have hζ₄1 : e₄ ⟨z, hz4⟩ ≠ 1 := by
    intro hc
    have hsub : (⟨z, hz4⟩ : ↥K₄) = 1 := e₄.injective (by rw [hc, map_one])
    exact hz1 (congrArg Subtype.val hsub)
  have hwz : a₀ * a₀ = 1 ∨ a₀ * a₀ = z := by
    rcases sec5b_sl23_eq_of_central hζ₃ hζ₃1 hw_central with h1 | h1
    · left
      have hsub : (⟨a₀ * a₀, K₃.mul_mem ha₀ ha₀⟩ : ↥K₃) = 1 :=
        e₃.injective (by rw [h1, map_one])
      exact congrArg Subtype.val hsub
    · right
      have hsub : (⟨a₀ * a₀, K₃.mul_mem ha₀ ha₀⟩ : ↥K₃) = ⟨z, hz3⟩ := e₃.injective h1
      exact congrArg Subtype.val hsub
  rcases hwz with hw1 | hwz'
  ·
    have ha0sq : a₀ * a₀ = 1 := hw1
    have hb0sq : b₀ * b₀ = 1 := by
      rw [ha0sq, one_mul] at hww
      exact hww
    have ha0 : a₀ = 1 ∨ a₀ = z := by
      have hsq : e₃ ⟨a₀, ha₀⟩ * e₃ ⟨a₀, ha₀⟩ = 1 := by
        rw [← map_mul, ← map_one e₃]
        congr 1
        apply Subtype.ext
        simpa using ha0sq
      rcases sec5b_sl23_eq_of_sq_eq_one hζ₃ hζ₃1 hsq with h1 | h1
      · left
        have hsub : (⟨a₀, ha₀⟩ : ↥K₃) = 1 := e₃.injective (by rw [h1, map_one])
        exact congrArg Subtype.val hsub
      · right
        have hsub : (⟨a₀, ha₀⟩ : ↥K₃) = ⟨z, hz3⟩ := e₃.injective h1
        exact congrArg Subtype.val hsub
    have hb0 : b₀ = 1 ∨ b₀ = z := by
      have hsq : e₄ ⟨b₀, hb₀⟩ * e₄ ⟨b₀, hb₀⟩ = 1 := by
        rw [← map_mul, ← map_one e₄]
        congr 1
        apply Subtype.ext
        simpa using hb0sq
      rcases sec5b_sl23_eq_of_sq_eq_one hζ₄ hζ₄1 hsq with h1 | h1
      · left
        have hsub : (⟨b₀, hb₀⟩ : ↥K₄) = 1 := e₄.injective (by rw [h1, map_one])
        exact congrArg Subtype.val hsub
      · right
        have hsub : (⟨b₀, hb₀⟩ : ↥K₄) = ⟨z, hz4⟩ := e₄.injective h1
        exact congrArg Subtype.val hsub
    rcases ha0 with rfl | rfl <;> rcases hb0 with rfl | rfl
    · exact absurd (by rw [one_mul]) ht1
    · exact absurd (by rw [one_mul]) htz
    · exact absurd (by rw [mul_one]) htz
    · exact absurd (by rw [hz2]) ht1
  ·
    have ha0sq : a₀ * a₀ = z := hwz'
    have hb0sq : b₀ * b₀ = z := by
      have h1 : (b₀ * b₀)⁻¹ = z := by rw [← eq_inv_of_mul_eq_one_left hww, hwz']
      calc b₀ * b₀ = ((b₀ * b₀)⁻¹)⁻¹ := (inv_inv _).symm
        _ = z⁻¹ := by rw [h1]
        _ = z := inv_eq_of_mul_eq_one_right hz2
    have hyt : Commute y (a₀ * b₀) := by
      show y * (a₀ * b₀) = (a₀ * b₀) * y
      simpa using hyc 1 (K₃ ⊔ K₄).one_mem
    have ha_comm : ∀ c ∈ K₃, a * (c⁻¹ * a₀ * c * a₀⁻¹) = (c⁻¹ * a₀ * c * a₀⁻¹) * a := by
      intro c hc
      have hyc_t : Commute y (c⁻¹ * (a₀ * b₀) * c) := hyc c (Subgroup.mem_sup_left hc)
      have hyn : Commute y ((c⁻¹ * (a₀ * b₀) * c) * (a₀ * b₀)⁻¹) :=
        hyc_t.mul_right hyt.inv_right
      have heq : c⁻¹ * (a₀ * b₀) * c * (a₀ * b₀)⁻¹ = c⁻¹ * a₀ * c * a₀⁻¹ :=
        sec5b_conj_mul_inv (hcomm c hc b₀ hb₀).symm
      rw [heq] at hyn
      have hn3 : c⁻¹ * a₀ * c * a₀⁻¹ ∈ K₃ :=
        K₃.mul_mem (K₃.mul_mem (K₃.mul_mem (K₃.inv_mem hc) ha₀) hc) (K₃.inv_mem ha₀)
      have hbn : Commute b (c⁻¹ * a₀ * c * a₀⁻¹) := (hcomm _ hn3 b hb).symm
      have h := hyn
      rw [hy_eq] at h
      change (a * b) * (c⁻¹ * a₀ * c * a₀⁻¹) = (c⁻¹ * a₀ * c * a₀⁻¹) * (a * b) at h
      rw [mul_assoc a b _, hbn.eq, ← mul_assoc a _ b, ← mul_assoc _ a b] at h
      exact mul_right_cancel h
    have hb_comm : ∀ c ∈ K₄, b * (c⁻¹ * b₀ * c * b₀⁻¹) = (c⁻¹ * b₀ * c * b₀⁻¹) * b := by
      intro c hc
      have hyc_t : Commute y (c⁻¹ * (a₀ * b₀) * c) := hyc c (Subgroup.mem_sup_right hc)
      have hyn : Commute y ((c⁻¹ * (a₀ * b₀) * c) * (a₀ * b₀)⁻¹) :=
        hyc_t.mul_right hyt.inv_right
      have heq : c⁻¹ * (a₀ * b₀) * c * (a₀ * b₀)⁻¹ = c⁻¹ * b₀ * c * b₀⁻¹ :=
        sec5b_conj_mul_inv_right (hcomm a₀ ha₀ c hc) (hcomm a₀ ha₀ b₀ hb₀)
      rw [heq] at hyn
      have hn4 : c⁻¹ * b₀ * c * b₀⁻¹ ∈ K₄ :=
        K₄.mul_mem (K₄.mul_mem (K₄.mul_mem (K₄.inv_mem hc) hb₀) hc) (K₄.inv_mem hb₀)
      have han : Commute a (c⁻¹ * b₀ * c * b₀⁻¹) := hcomm a ha _ hn4
      have h := hyn
      rw [hy_eq] at h
      change (a * b) * (c⁻¹ * b₀ * c * b₀⁻¹) = (c⁻¹ * b₀ * c * b₀⁻¹) * (a * b) at h
      rw [mul_assoc a b _, ← mul_assoc _ a b, (hcomm a ha _ hn4).symm, mul_assoc a _ b] at h
      exact mul_left_cancel h
    have ha_res := sec5b_eq_of_comm_conj_of_iso e₃ hz3 hz2 hz1 ha₀ ha ha0sq ha_comm
    have hb_res := sec5b_eq_of_comm_conj_of_iso e₄ hz4 hz2 hz1 hb₀ hb hb0sq hb_comm
    rcases ha_res with rfl | rfl <;> rcases hb_res with rfl | rfl
    · left; rw [hy_eq, one_mul]
    · right; rw [hy_eq, one_mul]
    · right; rw [hy_eq, mul_one]
    · left; rw [hy_eq, hz2]

end CFSG.OddStandard.SmallF3.Omega

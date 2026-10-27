module

public import CFSG.CGT.Foote81L6.Lemma1
public import CFSG.CGT.Foote81L6.TStruct.TAction
public import CFSG.Assembly.Defs

public section

namespace CFSG.CGT.Foote81L6.Normalizer

open Subgroup

variable {G : Type*} [Group G] {T : Subgroup G} {n : ℕ} (D : FooteCore G T 2 n)

theorem mem_Z_of_comm {x : G} (hx : x ∈ D.T₁) (hc : ∀ w ∈ D.T₁, x * w = w * x) :
    x ∈ D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁) := by
  obtain ⟨α, hα, w, hw, rfl⟩ := D.mem_T₁_iff.1 hx
  have hcw : ∀ w' ∈ D.B₀ ⊔ D.B₁, w' * w = w * w' := by
    intro w' hw'
    have h1 := hc w' (D.B₀B₁_le_T₁ hw')
    have h2 : α * w' = w' * α := D.A_comm_B α hα w' (D.B₀B₁_le_B hw')
    have : α * (w' * w) = α * (w * w') := by
      calc α * (w' * w) = (w' * α) * w := by rw [← mul_assoc, h2]
        _ = w' * (α * w) := mul_assoc _ _ _
        _ = α * w * w' := h1.symm
        _ = α * (w * w') := mul_assoc _ _ _
    exact mul_left_cancel this
  have hwZ : w ∈ zpowers D.b₀ ⊔ zpowers D.b₁ := by
    rcases D.eq_of_comm_B₀B₁ hw hcw with h | h | h | h <;> rw [h]
    · exact one_mem _
    · exact mem_sup_left (mem_zpowers _)
    · exact mem_sup_right (mem_zpowers _)
    · exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))
  exact mul_mem (mem_sup_left hα) (mem_sup_right hwZ)

theorem nonempty_T₁_equiv {m : ℕ} (D : FooteCore G T m n) : Nonempty (↥D.T₁ ≃* X m n n) := by
  obtain ⟨eA⟩ := D.A_iso
  obtain ⟨e₀⟩ := D.B₀_iso
  obtain ⟨e₁⟩ := D.B₁_iso
  have hmem : ∀ (a : ↥D.A) (x : ↥D.B₀) (y : ↥D.B₁), (a : G) * ((x : G) * y) ∈ D.T₁ :=
    fun a x y => mul_mem (mem_sup_left a.2) (mem_sup_right (mul_mem (mem_sup_left x.2)
      (mem_sup_right y.2)))
  let f : ↥D.A × ↥D.B₀ × ↥D.B₁ →* ↥D.T₁ :=
    { toFun := fun p => ⟨(p.1 : G) * ((p.2.1 : G) * p.2.2), hmem p.1 p.2.1 p.2.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun p q => Subtype.ext (by
        obtain ⟨a, x, y⟩ := p
        obtain ⟨a', x', y'⟩ := q
        show (a : G) * a' * ((x : G) * x' * ((y : G) * y')) =
          ((a : G) * ((x : G) * y)) * ((a' : G) * ((x' : G) * y'))
        have h1 : (a' : G) * ((x : G) * y) = ((x : G) * y) * a' :=
          D.A_comm_B _ a'.2 _ (D.B₀B₁_le_B (mul_mem (mem_sup_left x.2) (mem_sup_right y.2)))
        have h2 : (x' : G) * y = y * x' := D.B₀_comm_B₁ _ x'.2 _ y.2
        calc (a : G) * a' * ((x : G) * x' * ((y : G) * y'))
            = a * a' * x * ((x' : G) * y) * y' := by group
          _ = a * a' * x * ((y : G) * x') * y' := by rw [h2]
          _ = a * ((a' : G) * ((x : G) * y)) * x' * y' := by group
          _ = a * (((x : G) * y) * a') * x' * y' := by rw [h1]
          _ = ((a : G) * ((x : G) * y)) * ((a' : G) * ((x' : G) * y')) := by group) }
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, x, y⟩ h
    have h' : (a : G) * ((x : G) * y) = 1 := congrArg Subtype.val h
    have hxyB : (x : G) * y ∈ D.B := D.B₀B₁_le_B (mul_mem (mem_sup_left x.2) (mem_sup_right y.2))
    have ha : (a : G) = 1 := by
      have : (a : G) ∈ D.A ⊓ D.B := mem_inf.2 ⟨a.2, by
        rw [eq_inv_of_mul_eq_one_left h']; exact inv_mem hxyB⟩
      rwa [D.A_inf_B, mem_bot] at this
    rw [ha, one_mul] at h'
    have hx : (x : G) = 1 := by
      have : (x : G) ∈ D.B₀ ⊓ D.B₁ := mem_inf.2 ⟨x.2, by
        rw [eq_inv_of_mul_eq_one_left h']; exact inv_mem y.2⟩
      rwa [D.B₀_inf_B₁, mem_bot] at this
    rw [hx, one_mul] at h'
    exact Prod.ext (Subtype.ext ha) (Prod.ext (Subtype.ext hx) (Subtype.ext h'))
  have hsurj : Function.Surjective f := by
    rintro ⟨g, hg⟩
    obtain ⟨α, hα, w, hw, rfl⟩ := D.mem_T₁_iff.1 hg
    obtain ⟨x, hx, y, hy, rfl⟩ := D.mem_B₀B₁_iff.1 hw
    exact ⟨(⟨α, hα⟩, ⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  exact ⟨(MulEquiv.ofBijective f ⟨hinj, hsurj⟩).symm.trans
    (MulEquiv.prodCongr eA (MulEquiv.prodCongr e₀ e₁))⟩

private def conjOn {H : Subgroup G} {p : G} (hp : p ∈ normalizer (H : Set G)) : MulAut ↥H where
  toFun x := ⟨p * x * p⁻¹, (mem_normalizer_iff.1 hp x).1 x.2⟩
  invFun x := ⟨p⁻¹ * x * p, by
    have := (mem_normalizer_iff.1 (inv_mem hp) x).1 x.2
    rwa [inv_inv] at this⟩
  left_inv x := Subtype.ext (by show p⁻¹ * (p * (x : G) * p⁻¹) * p = x; group)
  right_inv x := Subtype.ext (by show p * (p⁻¹ * (x : G) * p) * p⁻¹ = x; group)
  map_mul' x y := Subtype.ext (by
    show p * ((x : G) * y) * p⁻¹ = (p * x * p⁻¹) * (p * y * p⁻¹); group)

private theorem conjOn_pow {H : Subgroup G} {p : G} (hp : p ∈ normalizer (H : Set G)) (k : ℕ)
    (x : ↥H) : (((conjOn hp) ^ k) x : G) = p ^ k * x * (p ^ k)⁻¹ := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, MulAut.mul_apply, ih, pow_succ]
    show p ^ k * (p * (x : G) * p⁻¹) * (p ^ k)⁻¹ = p ^ k * p * x * (p ^ k * p)⁻¹
    group

theorem lemma1_T₁ (hT₁ : Nonempty (↥D.T₁ ≃* X 2 n n)) {p : G}
    (hp : p ∈ normalizer (D.T₁ : Set G)) (hodd : Odd (orderOf p))
    (hmove : ∃ x ∈ D.T₁, p * x * p⁻¹ ≠ x) :
    (∀ x ∈ D.T₁, p ^ 3 * x * (p ^ 3)⁻¹ = x) ∧
      ∀ x ∈ D.T₁, p * x * p⁻¹ * x⁻¹ ∈ D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁) := by
  obtain ⟨ψ⟩ := hT₁
  set y := conjOn hp with hy
  have hyval : ∀ x : ↥D.T₁, (y x : G) = p * x * p⁻¹ := fun x => rfl
  have hy1 : y ≠ 1 := by
    obtain ⟨x, hx, hpx⟩ := hmove
    intro h
    apply hpx
    have := congrArg (fun f : MulAut ↥D.T₁ => (f ⟨x, hx⟩ : G)) h
    simpa [hyval] using this
  have hyodd : Odd (orderOf y) := by
    refine hodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one ?_)
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [conjOn_pow, pow_orderOf_eq_one, one_mul, inv_one, mul_one]
    rfl
  set y' := MulAut.congr ψ y with hy'
  have hy'1 : y' ≠ 1 := fun h => hy1 ((MulAut.congr ψ).injective (h.trans (map_one _).symm))
  have hy'odd : Odd (orderOf y') := by rw [hy', MulEquiv.orderOf_eq]; exact hyodd
  obtain ⟨-, hord, -, hsq, φ, hφ⟩ := lemma1_one (r := 2) (e := n) (f := n) le_rfl
    (by have := D.three_le_n; omega) le_rfl y' hy'1 hy'odd
  have hy3 : y ^ 3 = 1 := by
    have h3 : y' ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one y'
    exact (MulAut.congr ψ).injective (by rw [map_pow, ← hy', h3, map_one])
  have hcomm' : ∀ u ∈ commAut y', ∀ v ∈ commAut y', u * v = v * u := by
    intro u hu v hv
    have h1 : u * v * (u * v) = 1 := hsq _ (mul_mem hu hv)
    have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right (hsq u hu)
    have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right (hsq v hv)
    calc u * v = (u * v)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
      _ = v⁻¹ * u⁻¹ := mul_inv_rev u v
      _ = v * u := by rw [hu', hv']
  have hcent' : ∀ c ∈ commAut y', ∀ z : X 2 n n, c * z = z * c := by
    intro c hc z
    obtain ⟨⟨u, a, b⟩, rfl⟩ := φ.surjective z
    have hc' : φ (⟨c, hc⟩, 1, 1) = c := by
      rw [hφ]
      show (c : X 2 n n) * (1, 1, 1) * (1, 1, 1) = c
      rw [show ((1, 1, 1) : X 2 n n) = 1 from rfl, mul_one, mul_one]
    rw [← hc', ← map_mul, ← map_mul]
    congr 1
    refine Prod.ext (Subtype.ext (hcomm' c hc u u.2)) (Prod.ext ?_ ?_) <;> simp
  have hcent : ∀ c ∈ commAut y, ∀ z : ↥D.T₁, c * z = z * c := by
    intro c hc z
    have hc' : ψ c ∈ commAut y' := by
      rw [hy', commAut_congr]
      exact ⟨c, hc, rfl⟩
    apply ψ.injective
    rw [map_mul, map_mul]
    exact hcent' _ hc' _
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have h := congrArg (fun f : MulAut ↥D.T₁ => (f ⟨x, hx⟩ : G)) hy3
    rw [conjOn_pow] at h
    exact h
  · set c : ↥D.T₁ := (⟨x, hx⟩ : ↥D.T₁)⁻¹ * y ⟨x, hx⟩ with hc_def
    have hc : c ∈ commAut y := subset_closure ⟨⟨x, hx⟩, rfl⟩
    have hcval : (c : G) = x⁻¹ * (p * x * p⁻¹) := rfl
    have hcx := hcent c hc ⟨x, hx⟩
    have hcx' : (c : G) * x = x * c := congrArg Subtype.val hcx
    have hval : p * x * p⁻¹ * x⁻¹ = (c : G) := by
      calc p * x * p⁻¹ * x⁻¹ = x * (x⁻¹ * (p * x * p⁻¹)) * x⁻¹ := by group
        _ = x * c * x⁻¹ := by rw [hcval]
        _ = c := by rw [← hcx', mul_inv_cancel_right]
    rw [hval]
    exact mem_Z_of_comm D c.2 fun w hw => congrArg Subtype.val (hcent c hc ⟨w, hw⟩)

end CFSG.CGT.Foote81L6.Normalizer

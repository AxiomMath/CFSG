module

public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.B27ContradictionI

public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.GH74.QTGen4.Recog.G23.P7.B27A

variable {G : Type} [Group G]

section Quot

variable {Mf W₁ : Subgroup G}

theorem normal_W₁_sub (hWc : ∀ x ∈ Mf, ∀ n ∈ W₁, x * n * x⁻¹ = n) :
    (W₁.subgroupOf Mf).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have := hWc (g : G) g.2 n hn
  show (g : G) * (n : G) * (g : G)⁻¹ ∈ W₁
  rw [this]
  exact hn

theorem comm_quot [hN : (W₁.subgroupOf Mf).Normal]
    (hcomm : ∀ x ∈ Mf, ∀ y ∈ Mf, x⁻¹ * y⁻¹ * x * y ∈ W₁) :
    ∀ a b : ↥Mf ⧸ W₁.subgroupOf Mf, a * b = b * a := by
  intro a b
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have h := hcomm (y : G) y.2 (x : G) x.2
  show ((x : G) * (y : G))⁻¹ * ((y : G) * (x : G)) ∈ W₁
  have e : ((x : G) * (y : G))⁻¹ * ((y : G) * (x : G)) =
      (y : G)⁻¹ * (x : G)⁻¹ * (y : G) * (x : G) := by group
  rw [e]
  exact h

noncomputable def commGroupQ [hN : (W₁.subgroupOf Mf).Normal]
    (hcomm : ∀ x ∈ Mf, ∀ y ∈ Mf, x⁻¹ * y⁻¹ * x * y ∈ W₁) :
    CommGroup (↥Mf ⧸ W₁.subgroupOf Mf) :=
  { (inferInstance : Group (↥Mf ⧸ W₁.subgroupOf Mf)) with
    mul_comm := comm_quot hcomm }

noncomputable def conjQ [hN : (W₁.subgroupOf Mf).Normal] (g : G)
    (hg : ∀ x ∈ Mf, g * x * g⁻¹ ∈ Mf) (hgW : ∀ w ∈ W₁, g * w * g⁻¹ ∈ W₁) :
    (↥Mf ⧸ W₁.subgroupOf Mf) →* (↥Mf ⧸ W₁.subgroupOf Mf) :=
  QuotientGroup.map (W₁.subgroupOf Mf) (W₁.subgroupOf Mf)
    (MonoidHom.codRestrict ((MulAut.conj g).toMonoidHom.comp Mf.subtype) Mf
      (fun x => hg x.1 x.2))
    (by
      intro n hn
      rw [Subgroup.mem_subgroupOf] at hn
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      exact hgW _ hn)

theorem conjQ_mk [hN : (W₁.subgroupOf Mf).Normal] (g : G)
    (hg : ∀ x ∈ Mf, g * x * g⁻¹ ∈ Mf) (hgW : ∀ w ∈ W₁, g * w * g⁻¹ ∈ W₁) (x : ↥Mf) :
    conjQ g hg hgW (QuotientGroup.mk x) =
      QuotientGroup.mk (⟨g * (x : G) * g⁻¹, hg x x.2⟩ : ↥Mf) := by
  rfl

end Quot

section Facts

variable {Mf W₁ : Subgroup G}

theorem fixed_trivial_t (t : G) (ht2 : t ^ 2 = 1) (htW : ∀ w ∈ W₁, t * w * t⁻¹ = w)
    (htC : ∀ x ∈ Mf, t * x * t⁻¹ = x → x ∈ W₁)
    (hWexp : ∀ w ∈ W₁, w ^ 3 = 1)
    (x : G) (hx : x ∈ Mf) (w : G) (hw : w ∈ W₁) (h : t * x * t⁻¹ = x * w) : x ∈ W₁ := by
  have htt : t * t = 1 := by rw [← pow_two]; exact ht2
  have hw2 : w * w = 1 := by
    have h1 : t * (t * x * t⁻¹) * t⁻¹ = x := by
      calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
        _ = x := by rw [htt]; group
    have h2 : t * (x * w) * t⁻¹ = (t * x * t⁻¹) * (t * w * t⁻¹) := by group
    rw [h] at h1
    rw [h2, htW w hw, h] at h1
    have h3 : x * (w * w) = x * 1 := by rw [mul_one, ← mul_assoc]; exact h1
    exact mul_left_cancel h3
  have hw1 : w = 1 := by
    calc w = w ^ 3 * (w * w)⁻¹ := by group
      _ = 1 := by rw [hWexp w hw, hw2, inv_one, one_mul]
  have hx' : t * x * t⁻¹ = x := by rw [h, hw1, mul_one]
  exact htC x hx hx'

theorem lift_fixed_inv (g : G) (hgW : ∀ w ∈ W₁, g * w * g⁻¹ = w⁻¹)
    (hWexp : ∀ w ∈ W₁, w ^ 3 = 1) (x : G) (w : G) (hw : w ∈ W₁) (h : g * x * g⁻¹ = x * w) :
    g * (x * w ^ 2) * g⁻¹ = x * w ^ 2 := by
  have hw2 : g * (w ^ 2) * g⁻¹ = (w ^ 2)⁻¹ := by
    have e : g * (w ^ 2) * g⁻¹ = (g * w * g⁻¹) ^ 2 := by rw [conj_pow]
    rw [e, hgW w hw, inv_pow]
  have h4 : w ^ 4 = w := by
    calc w ^ 4 = w ^ 3 * w := by group
      _ = w := by rw [hWexp w hw, one_mul]
  have hmid : w * (w ^ 2)⁻¹ = w ^ 2 := by
    rw [mul_inv_eq_iff_eq_mul, ← pow_add]
    exact h4.symm
  calc g * (x * w ^ 2) * g⁻¹ = (g * x * g⁻¹) * (g * w ^ 2 * g⁻¹) := by group
    _ = (x * w) * (w ^ 2)⁻¹ := by rw [h, hw2]
    _ = x * (w * (w ^ 2)⁻¹) := by group
    _ = x * w ^ 2 := by rw [hmid]

end Facts

section Qcard

variable {Mf W₁ : Subgroup G}

theorem card_quot_81 [Finite G] [hN : (W₁.subgroupOf Mf).Normal] (hWMf : W₁ ≤ Mf)
    (hMf : Nat.card Mf = 243) (hW : Nat.card W₁ = 3) :
    Nat.card (↥Mf ⧸ W₁.subgroupOf Mf) = 81 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (W₁.subgroupOf Mf)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWMf).toEquiv, hW, hMf] at h1
  omega

theorem conjQ_pow_three [hN : (W₁.subgroupOf Mf).Normal] (g : G) (hg3 : g ^ 3 = 1)
    (hg : ∀ x ∈ Mf, g * x * g⁻¹ ∈ Mf) (hgW : ∀ w ∈ W₁, g * w * g⁻¹ ∈ W₁)
    (v : ↥Mf ⧸ W₁.subgroupOf Mf) :
    conjQ g hg hgW (conjQ g hg hgW (conjQ g hg hgW v)) = v := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
  rw [conjQ_mk, conjQ_mk, conjQ_mk]
  congr 1
  apply Subtype.ext
  show g * (g * (g * (x : G) * g⁻¹) * g⁻¹) * g⁻¹ = x
  have hggg : g * g * g = 1 := by
    have := hg3
    rw [pow_three] at this
    rwa [mul_assoc]
  calc g * (g * (g * (x : G) * g⁻¹) * g⁻¹) * g⁻¹ = (g * g * g) * (x : G) * (g * g * g)⁻¹ := by group
    _ = x := by rw [hggg]; group

theorem conjQ_sq [hN : (W₁.subgroupOf Mf).Normal] (g : G) (hg2 : g ^ 2 = 1)
    (hg : ∀ x ∈ Mf, g * x * g⁻¹ ∈ Mf) (hgW : ∀ w ∈ W₁, g * w * g⁻¹ ∈ W₁)
    (v : ↥Mf ⧸ W₁.subgroupOf Mf) :
    conjQ g hg hgW (conjQ g hg hgW v) = v := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
  rw [conjQ_mk, conjQ_mk]
  congr 1
  apply Subtype.ext
  show g * (g * (x : G) * g⁻¹) * g⁻¹ = x
  have hgg : g * g = 1 := by
    have := hg2
    rwa [pow_two] at this
  calc g * (g * (x : G) * g⁻¹) * g⁻¹ = (g * g) * (x : G) * (g * g)⁻¹ := by group
    _ = x := by rw [hgg]; group

end Qcard

section Concrete

variable {Mf W₁ : Subgroup G}

theorem mk_eq_exists [hN : (W₁.subgroupOf Mf).Normal] (a b : ↥Mf)
    (h : (QuotientGroup.mk a : ↥Mf ⧸ W₁.subgroupOf Mf) = QuotientGroup.mk b) :
    ∃ w ∈ W₁, (a : G) = (b : G) * w := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
  have h' : (a : G)⁻¹ * (b : G) ∈ W₁ := h
  have h2 : (b : G)⁻¹ * (a : G) = ((a : G)⁻¹ * (b : G))⁻¹ := by group
  refine ⟨(b : G)⁻¹ * (a : G), ?_, by group⟩
  rw [h2]
  exact W₁.inv_mem h'

theorem phi_arg (hWc : ∀ x ∈ Mf, ∀ n ∈ W₁, x * n * x⁻¹ = n) (hWMf : W₁ ≤ Mf)
    (hWexp : ∀ w ∈ W₁, w ^ 3 = 1) (t σ : G) (htσ : t * σ = σ * t)
    (htW : ∀ w ∈ W₁, t * w * t⁻¹ = w) (hσW : ∀ w ∈ W₁, σ * w * σ⁻¹ = w)
    (y : G) (hy : y ∈ Mf) (w w' : G) (hw : w ∈ W₁) (hw' : w' ∈ W₁)
    (h1 : σ * y * σ⁻¹ = y * w) (h2 : t * y * t⁻¹ = y⁻¹ * w') : w = 1 := by
  have hyw : y * w = w * y := by
    have := hWc y hy w hw
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have hww' : w * w' = w' * w := by
    have := hWc w (hWMf hw) w' hw'
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have hA : σ * (t * y * t⁻¹) * σ⁻¹ = t * (σ * y * σ⁻¹) * t⁻¹ := by
    have h' : σ * t = t * σ := htσ.symm
    calc σ * (t * y * t⁻¹) * σ⁻¹ = (σ * t) * y * (σ * t)⁻¹ := by group
      _ = (t * σ) * y * (t * σ)⁻¹ := by rw [h']
      _ = t * (σ * y * σ⁻¹) * t⁻¹ := by group
  have hB : σ * (t * y * t⁻¹) * σ⁻¹ = (σ * y * σ⁻¹)⁻¹ * (σ * w' * σ⁻¹) := by
    rw [h2]
    group
  have hLHS : σ * (t * y * t⁻¹) * σ⁻¹ = y⁻¹ * w' * w := by
    rw [hA, h1]
    have : t * (y * w) * t⁻¹ = (t * y * t⁻¹) * (t * w * t⁻¹) := by group
    rw [this, h2, htW w hw]
  have hRHS : (σ * y * σ⁻¹)⁻¹ * (σ * w' * σ⁻¹) = w⁻¹ * y⁻¹ * w' := by
    rw [h1, hσW w' hw']
    group
  have key : y⁻¹ * w' * w = w⁻¹ * y⁻¹ * w' := by
    rw [← hLHS, hB, hRHS]
  have hcomm : w⁻¹ * y⁻¹ = y⁻¹ * w⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, hyw]
  rw [hcomm] at key
  have key2 : w' * w = w⁻¹ * w' :=
    mul_left_cancel (a := y⁻¹) (by rw [← mul_assoc, key, mul_assoc])
  have hw_inv : w = w⁻¹ := mul_right_cancel (hww'.trans key2)
  have hw2 : w * w = 1 := by
    have := mul_inv_cancel w
    rw [← hw_inv] at this
    exact this
  calc w = w ^ 3 * (w * w)⁻¹ := by group
    _ = 1 := by rw [hWexp w hw, hw2, inv_one, one_mul]

theorem cube_of_lift [hN : (W₁.subgroupOf Mf).Normal] (g : G) (hgW : ∀ w ∈ W₁, g * w * g⁻¹ = w⁻¹)
    (hWMf : W₁ ≤ Mf) (hWexp : ∀ w ∈ W₁, w ^ 3 = 1)
    (hgC : ∀ c ∈ Mf, g * c = c * g → c ^ 3 = 1)
    (x : ↥Mf) (w : G) (hw : w ∈ W₁) (hxw : g * (x : G) * g⁻¹ = (x : G) * w) :
    (QuotientGroup.mk x : ↥Mf ⧸ W₁.subgroupOf Mf) ^ 3 = 1 := by
  have hc := lift_fixed_inv g hgW hWexp (x : G) w hw hxw
  have hcMf : (x : G) * w ^ 2 ∈ Mf := Mf.mul_mem x.2 (Mf.pow_mem (hWMf hw) 2)
  have hcomm' : g * ((x : G) * w ^ 2) = ((x : G) * w ^ 2) * g := by
    rw [← mul_inv_eq_iff_eq_mul]
    exact hc
  have h3 := hgC _ hcMf hcomm'
  have hmk : (QuotientGroup.mk (⟨(x : G) * w ^ 2, hcMf⟩ : ↥Mf) : ↥Mf ⧸ W₁.subgroupOf Mf) =
      QuotientGroup.mk x := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show ((x : G) * w ^ 2)⁻¹ * (x : G) ∈ W₁
    have e : ((x : G) * w ^ 2)⁻¹ * (x : G) = (w ^ 2)⁻¹ := by group
    rw [e]
    exact W₁.inv_mem (W₁.pow_mem hw 2)
  have hpow : (⟨(x : G) * w ^ 2, hcMf⟩ : ↥Mf) ^ 3 = 1 := by
    apply Subtype.ext
    exact h3
  rw [← hmk, ← QuotientGroup.mk_pow, hpow, QuotientGroup.mk_one]

theorem V_concrete [Finite G] {Mf W₁ : Subgroup G} {t z σ : G}
    (hWc : ∀ x ∈ Mf, ∀ n ∈ W₁, x * n * x⁻¹ = n)
    (hcomm : ∀ x ∈ Mf, ∀ y ∈ Mf, x⁻¹ * y⁻¹ * x * y ∈ W₁)
    (hWMf : W₁ ≤ Mf) (hMf : Nat.card Mf = 243) (hW : Nat.card W₁ = 3)
    (hWexp : ∀ w ∈ W₁, w ^ 3 = 1)
    (ht2 : t ^ 2 = 1) (hz2 : z ^ 2 = 1) (hσ3 : σ ^ 3 = 1)
    (htN : ∀ x ∈ Mf, t * x * t⁻¹ ∈ Mf) (hzN : ∀ x ∈ Mf, z * x * z⁻¹ ∈ Mf)
    (hσN : ∀ x ∈ Mf, σ * x * σ⁻¹ ∈ Mf)
    (htW : ∀ w ∈ W₁, t * w * t⁻¹ = w) (hzW : ∀ w ∈ W₁, z * w * z⁻¹ = w⁻¹)
    (hσW : ∀ w ∈ W₁, σ * w * σ⁻¹ = w)
    (htC : ∀ x ∈ Mf, t * x * t⁻¹ = x → x ∈ W₁)
    (hzC : ∀ c ∈ Mf, z * c = c * z → c ^ 3 = 1)
    (htzC : ∀ c ∈ Mf, (t * z) * c = c * (t * z) → c ^ 3 = 1)
    (htσ : t * σ = σ * t) :
    ∃ Q : Subgroup G, (∀ x ∈ Q, x ∈ Mf ∧ σ * x = x * σ) ∧ 27 ≤ Nat.card Q := by
  haveI hN : (W₁.subgroupOf Mf).Normal := normal_W₁_sub hWc
  letI : CommGroup (↥Mf ⧸ W₁.subgroupOf Mf) := commGroupQ hcomm
  have hσW' : ∀ w ∈ W₁, σ * w * σ⁻¹ ∈ W₁ := fun w hw => by rw [hσW w hw]; exact hw
  have hzW' : ∀ w ∈ W₁, z * w * z⁻¹ ∈ W₁ := fun w hw => by
    rw [hzW w hw]; exact W₁.inv_mem hw
  have htW' : ∀ w ∈ W₁, t * w * t⁻¹ ∈ W₁ := fun w hw => by rw [htW w hw]; exact hw
  have htzW : ∀ w ∈ W₁, (t * z) * w * (t * z)⁻¹ = w⁻¹ := by
    intro w hw
    calc (t * z) * w * (t * z)⁻¹ = t * (z * w * z⁻¹) * t⁻¹ := by group
      _ = t * w⁻¹ * t⁻¹ := by rw [hzW w hw]
      _ = (t * w * t⁻¹)⁻¹ := by group
      _ = w⁻¹ := by rw [htW w hw]
  have hzC' : ∀ c ∈ Mf, z * c = c * z → c ^ 3 = 1 := hzC
  have hα3 := hσ3
  let α := conjQ σ hσN hσW'
  let ζ := conjQ z hzN hzW'
  let τ := conjQ t htN htW'
  have hα : ∀ v, α (α (α v)) = v := conjQ_pow_three σ hσ3 hσN hσW'
  have hζ : ∀ v, ζ (ζ v) = v := conjQ_sq z hz2 hzN hzW'
  have hτ2 : ∀ v, τ (τ v) = v := conjQ_sq t ht2 htN htW'
  have hτfix : ∀ v, τ v = v → v = 1 := by
    intro v hv
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
    have hv' : QuotientGroup.mk (s := W₁.subgroupOf Mf) (⟨t * (x : G) * t⁻¹, htN x x.2⟩ : ↥Mf) = QuotientGroup.mk (s := W₁.subgroupOf Mf) x := by
      rw [← conjQ_mk t htN htW']
      exact hv
    obtain ⟨w, hw, hxw⟩ := mk_eq_exists _ _ hv'
    have hxW : (x : G) ∈ W₁ :=
      fixed_trivial_t t ht2 htW htC hWexp (x : G) x.2 w hw hxw
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hxW)
  have hτinv : ∀ v, τ v = v⁻¹ := by
    intro v
    have hu : τ (v * τ v) = v * τ v := by
      rw [map_mul, hτ2]
      exact mul_comm _ _
    exact eq_inv_of_mul_eq_one_right (hτfix _ hu)
  have hζfix : ∀ v, ζ v = v → v ^ 3 = 1 := by
    intro v hv
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
    have hv' : QuotientGroup.mk (s := W₁.subgroupOf Mf) (⟨z * (x : G) * z⁻¹, hzN x x.2⟩ : ↥Mf) = QuotientGroup.mk (s := W₁.subgroupOf Mf) x := by
      rw [← conjQ_mk z hzN hzW']
      exact hv
    obtain ⟨w, hw, hxw⟩ := mk_eq_exists _ _ hv'
    exact cube_of_lift z hzW hWMf hWexp hzC x w hw hxw
  have hτζfix : ∀ v, τ (ζ v) = v → v ^ 3 = 1 := by
    intro v hv
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
    have h1 : ζ (QuotientGroup.mk (s := W₁.subgroupOf Mf) x) =
        QuotientGroup.mk (s := W₁.subgroupOf Mf) (⟨z * (x : G) * z⁻¹, hzN x x.2⟩ : ↥Mf) :=
      conjQ_mk z hzN hzW' x
    have h2 : τ (QuotientGroup.mk (s := W₁.subgroupOf Mf) (⟨z * (x : G) * z⁻¹, hzN x x.2⟩ : ↥Mf)) =
        QuotientGroup.mk (s := W₁.subgroupOf Mf)
          (⟨t * (z * (x : G) * z⁻¹) * t⁻¹, htN _ (hzN x x.2)⟩ : ↥Mf) :=
      conjQ_mk t htN htW' _
    have hv' : QuotientGroup.mk (s := W₁.subgroupOf Mf)
        (⟨t * (z * (x : G) * z⁻¹) * t⁻¹, htN _ (hzN x x.2)⟩ : ↥Mf) =
        QuotientGroup.mk (s := W₁.subgroupOf Mf) x := by
      rw [← h2, ← h1]
      exact hv
    obtain ⟨w, hw, hxw⟩ := mk_eq_exists _ _ hv'
    have hxw' : (t * z) * (x : G) * (t * z)⁻¹ = (x : G) * w := by
      rw [show (t * z) * (x : G) * (t * z)⁻¹ = t * (z * (x : G) * z⁻¹) * t⁻¹ by group]
      exact hxw
    exact cube_of_lift (t * z) htzW hWMf hWexp htzC x w hw hxw'
  have hV : Nat.card (↥Mf ⧸ W₁.subgroupOf Mf) = 81 := card_quot_81 hWMf hMf hW
  obtain ⟨-, h9⟩ := V_abstract hV α ζ τ hα hζ hτinv hζfix hτζfix
  let Kc : Subgroup (↥Mf ⧸ W₁.subgroupOf Mf) :=
    { carrier := {v | α v = v}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, ha, hb]
      one_mem' := by
        simp only [Set.mem_setOf_eq]
        exact map_one α
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [map_inv, ha]
        rfl }
  have hKc : 9 ≤ Nat.card ↥Kc := h9
  let Q0 : Subgroup ↥Mf := Kc.comap (QuotientGroup.mk' (W₁.subgroupOf Mf))
  have hQ0idx : Q0.index = Kc.index :=
    Subgroup.index_comap_of_surjective Kc (QuotientGroup.mk'_surjective _)
  have h1 := Subgroup.card_mul_index Q0
  have h2 := Subgroup.card_mul_index Kc
  rw [hQ0idx, hMf] at h1
  rw [hV] at h2
  have hr : 0 < Kc.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hQ0 : 27 ≤ Nat.card ↥Q0 := by
    have h3 : Nat.card ↥Q0 = 3 * Nat.card ↥Kc := by
      apply Nat.eq_of_mul_eq_mul_right hr
      calc Nat.card ↥Q0 * Kc.index = 243 := h1
        _ = 3 * (Nat.card ↥Kc * Kc.index) := by rw [h2]
        _ = 3 * Nat.card ↥Kc * Kc.index := by ring
    omega
  let Q : Subgroup G := Q0.map Mf.subtype
  have hQcard : Nat.card ↥Q = Nat.card ↥Q0 :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  refine ⟨Q, ?_, by rw [hQcard]; exact hQ0⟩
  rintro x hx
  obtain ⟨y0, hy0, rfl⟩ := Subgroup.mem_map.mp hx
  have hk : α (QuotientGroup.mk y0) = QuotientGroup.mk y0 := hy0
  have hk1 : conjQ σ hσN hσW' (QuotientGroup.mk y0) = QuotientGroup.mk y0 := hk
  rw [conjQ_mk] at hk1
  obtain ⟨w, hw, hyw⟩ := mk_eq_exists _ _ hk1
  have hτ1 : QuotientGroup.mk (s := W₁.subgroupOf Mf)
      (⟨t * (y0 : G) * t⁻¹, htN _ y0.2⟩ : ↥Mf) = QuotientGroup.mk (s := W₁.subgroupOf Mf) (y0⁻¹) := by
    have h := hτinv (QuotientGroup.mk (s := W₁.subgroupOf Mf) y0)
    rw [conjQ_mk] at h
    rw [h, QuotientGroup.mk_inv]
    rfl
  obtain ⟨w', hw', hty⟩ := mk_eq_exists _ _ hτ1
  have h1' : σ * (y0 : G) * σ⁻¹ = (y0 : G) * w := hyw
  have h2' : t * (y0 : G) * t⁻¹ = (y0 : G)⁻¹ * w' := hty
  have hw1 : w = 1 :=
    phi_arg hWc hWMf hWexp t σ htσ htW hσW (y0 : G) y0.2 w w' hw hw' h1' h2'
  refine ⟨y0.2, ?_⟩
  have hfix : σ * (y0 : G) * σ⁻¹ = (y0 : G) := by rw [h1', hw1, mul_one]
  calc σ * (y0 : G) = σ * (y0 : G) * σ⁻¹ * σ := by group
    _ = (y0 : G) * σ := by rw [hfix]

end Concrete

end CFSG.GH74.QTGen4.Recog.G23.P7

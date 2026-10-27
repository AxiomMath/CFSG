module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerConfigC
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerThreePart
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.NoAbelianNormal
import CFSG.Mathlib.GroupTheory.PermCommute

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup Wreath CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section General

variable {G : Type*} [Group G]

abbrev Cm (H K : Subgroup G) : Prop := H ≤ centralizer (K : Set G)

theorem Cm.symm {H K : Subgroup G} (h : Cm H K) : Cm K H := Subgroup.le_centralizer_iff.1 h

theorem Cm.comm {H K : Subgroup G} (h : Cm H K) {a b : G} (ha : a ∈ H) (hb : b ∈ K) :
    a * b = b * a :=
  (mem_centralizer_iff.1 (h ha) b hb).symm

theorem Cm.sup_left {H H' K : Subgroup G} (h : Cm H K) (h' : Cm H' K) : Cm (H ⊔ H') K :=
  sup_le h h'

theorem Cm.sup_right {H K K' : Subgroup G} (h : Cm H K) (h' : Cm H K') : Cm H (K ⊔ K') :=
  (h.symm.sup_left h'.symm).symm

theorem Cm.mono {H H' K K' : Subgroup G} (h : Cm H K) (hH : H' ≤ H) (hK : K' ≤ K) : Cm H' K' :=
  fun _ ha => centralizer_le (show (K' : Set G) ⊆ K from hK) (h (hH ha))

theorem cm_zpowers_left {a : G} {K : Subgroup G} (h : ∀ b ∈ K, a * b = b * a) :
    Cm (zpowers a) K := by
  refine zpowers_le.2 ?_
  exact mem_centralizer_iff.2 fun b hb => (h b hb).symm

theorem cm_zpowers_zpowers {a b : G} (h : a * b = b * a) : Cm (zpowers a) (zpowers b) := by
  refine cm_zpowers_left fun w hw => ?_
  obtain ⟨k, rfl⟩ := hw
  exact ((Commute.zpow_right (show Commute a b from h) k).eq)

theorem Cm.conj (t : G) {H K : Subgroup G} (h : Cm H K) : Cm (conjSub t H) (conjSub t K) := by
  rintro _ ⟨a, ha, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨b, hb, rfl⟩
  have := h.comm ha hb
  show t * b * t⁻¹ * (t * a * t⁻¹) = t * a * t⁻¹ * (t * b * t⁻¹)
  calc t * b * t⁻¹ * (t * a * t⁻¹) = t * (b * a) * t⁻¹ := by group
    _ = t * (a * b) * t⁻¹ := by rw [this]
    _ = _ := by group

theorem mem_conjSub {t : G} {H : Subgroup G} {y : G} :
    y ∈ conjSub t H ↔ ∃ a ∈ H, t * a * t⁻¹ = y := by
  simp [conjSub, Subgroup.mem_map, MulAut.conj_apply]

theorem conjSub_conjSub {t : G} (ht : t * t = 1) (H : Subgroup G) :
    conjSub t (conjSub t H) = H := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  ext y
  simp only [mem_conjSub]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    have : t * (t * a * t⁻¹) * t⁻¹ = a := by
      rw [hti]
      calc t * (t * a * t) * t = (t * t) * a * (t * t) := by group
        _ = a := by rw [ht]; group
    rw [this]
    exact ha
  · intro hy
    refine ⟨t * y * t⁻¹, ⟨y, hy, rfl⟩, ?_⟩
    rw [hti]
    calc t * (t * y * t) * t = (t * t) * y * (t * t) := by group
      _ = y := by rw [ht]; group

theorem conjSub_zpowers (t a : G) : conjSub t (zpowers a) = zpowers (t * a * t⁻¹) := by
  rw [conjSub, MonoidHom.map_zpowers]
  rfl

theorem conjSub_sup (t : G) (H K : Subgroup G) : conjSub t (H ⊔ K) = conjSub t H ⊔ conjSub t K :=
  Subgroup.map_sup _ _ _

theorem eq_one_or_eq_of_mem_zpowers_of_mul_self {a w : G} (ha : a * a = 1) (hw : w ∈ zpowers a) :
    w = 1 ∨ w = a := by
  obtain ⟨k, rfl⟩ := hw
  have h2 : a ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ha
  have e : a ^ k = a ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul, h2, one_zpow, mul_one]
  show a ^ k = 1 ∨ a ^ k = a
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [e, h, zpow_zero]
  · right
    rw [e, h, zpow_one]

theorem mem_sup_iff_of_cm {H K : Subgroup G} (h : Cm H K) {x : G} :
    x ∈ H ⊔ K ↔ ∃ a ∈ H, ∃ b ∈ K, x = a * b := by
  constructor
  · intro hx
    have hc : ∀ (m : H) (n : K), Commute (H.subtype m) (K.subtype n) :=
      fun m n => (h.comm m.2 n.2 : (m : G) * n = n * m)
    have : x ∈ (MonoidHom.noncommCoprod H.subtype K.subtype hc).range := by
      rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
      exact hx
    obtain ⟨⟨m, n⟩, rfl⟩ := this
    exact ⟨m, m.2, n, n.2, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact mul_mem (mem_sup_left ha) (mem_sup_right hb)

theorem card_sup_of_cm {H K : Subgroup G} (h : Cm H K) (hd : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  have hc : ∀ (m : H) (n : K), Commute (H.subtype m) (K.subtype n) :=
    fun m n => (h.comm m.2 n.2 : (m : G) * n = n * m)
  have hφ : Function.Injective (MonoidHom.noncommCoprod H.subtype K.subtype hc) := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨H.subtype_injective, K.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    exact disjoint_iff.2 hd
  have h2 : (MonoidHom.noncommCoprod H.subtype K.subtype hc).range = H ⊔ K := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have h1 := Nat.card_congr
    ((MonoidHom.ofInjective hφ).toEquiv.trans (MulEquiv.subgroupCongr h2).toEquiv)
  rw [Nat.card_prod] at h1
  exact h1.symm

theorem centralizer_equiv_of_equiv {A B : Type*} [Group A] [Group B] (φ : A ≃* B) (a : A) :
    Nonempty (↥(centralizer ({φ a} : Set B)) ≃* ↥(centralizer ({a} : Set A))) :=
  ⟨{ toFun := fun k => ⟨φ.symm k, by
        rw [mem_centralizer_singleton_iff]
        have := mem_centralizer_singleton_iff.1 k.2
        apply φ.injective
        simpa using this⟩
     invFun := fun k => ⟨φ k, by
        rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
          mem_centralizer_singleton_iff.1 k.2]⟩
     left_inv := fun k => by ext; simp
     right_inv := fun k => by ext; simp
     map_mul' := fun k l => Subtype.ext (map_mul φ.symm _ _) }⟩

theorem centralizer_equiv_of_conj {A : Type*} [Group A] (h a : A) :
    Nonempty (↥(centralizer ({h * a * h⁻¹} : Set A)) ≃* ↥(centralizer ({a} : Set A))) := by
  have h' : (MulAut.conj h) a = h * a * h⁻¹ := rfl
  rw [← h']
  exact centralizer_equiv_of_equiv _ a

theorem s5_centralizer_pair : ∀ σ τ : Equiv.Perm (Fin 5), σ * (σ * σ) = 1 → σ ≠ 1 → τ * τ = 1 →
    τ ≠ 1 → σ * τ = τ * σ → ∀ g : Equiv.Perm (Fin 5), g * σ = σ * g → g * τ = τ * g →
      ∃ i : Fin 3, ∃ j : Fin 2, g = σ ^ (i : ℕ) * τ ^ (j : ℕ) := by
  decide +kernel

end General

theorem alt6_T1 : ∀ x x' : alternatingGroup (Fin 6), orderOf x = 3 → orderOf x' = 3 →
    ∃ α : MulAut (alternatingGroup (Fin 6)), α x = x' :=
  fun _ _ hx hx' => exists_mulAut_apply_eq_of_orderOf_eq_three hx hx'

theorem alt6_T2 : ∀ x : alternatingGroup (Fin 6), orderOf x = 3 →
    Nat.card (centralizer ({MulAut.conj x} : Set (MulAut (alternatingGroup (Fin 6))))) = 18 :=
  fun _ hx => card_centralizer_conj_of_orderOf_eq_three hx

theorem alt6_T3 : ∀ x : alternatingGroup (Fin 6), orderOf x = 3 →
    Nat.card (centralizer ({x} : Set (alternatingGroup (Fin 6)))) = 9 ∧
    (∀ a ∈ centralizer ({x} : Set (alternatingGroup (Fin 6))),
      ∀ b ∈ centralizer ({x} : Set (alternatingGroup (Fin 6))), a * b = b * a) ∧
    ∀ a ∈ centralizer ({x} : Set (alternatingGroup (Fin 6))), a ^ 3 = 1 :=
  fun _ hx => ⟨card_centralizer_of_orderOf_eq_three hx, centralizer_commute_of_orderOf_eq_three hx,
    pow_three_of_mem_centralizer hx⟩

section General2

variable {G : Type*} [Group G]

theorem conj_conj_of_sq {t : G} (ht : t * t = 1) (a : G) : t * (t * a * t⁻¹) * t⁻¹ = a := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  rw [hti]
  calc t * (t * a * t) * t = (t * t) * a * (t * t) := by group
    _ = a := by rw [ht]; group

theorem comm_middle {a b b' e : G} (hea : e * a = a * e) (heb' : e * b' = b' * e)
    (h : e * (a * b * b') = (a * b * b') * e) : e * b = b * e := by
  have h1 : a * (e * b) * b' = a * (b * e) * b' := by
    calc a * (e * b) * b' = (a * e) * b * b' := by group
      _ = (e * a) * b * b' := by rw [hea]
      _ = e * (a * b * b') := by group
      _ = (a * b * b') * e := h
      _ = a * b * (b' * e) := by group
      _ = a * b * (e * b') := by rw [heb']
      _ = a * (b * e) * b' := by group
  exact mul_left_cancel (mul_right_cancel h1)

end General2

section Config

set_option linter.unusedSectionVars false

variable
  {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}

namespace InnerD8ConfigC

variable (c : InnerD8ConfigC L t)

abbrev xt : G := t * c.x * t⁻¹

abbrev Asub : Subgroup G := zpowers c.x ⊔ zpowers c.xt

abbrev Bsub : Subgroup G := c.K₁ ⊔ zpowers c.u₁

abbrev Btsub : Subgroup G := conjSub t c.Bsub

abbrev Zc : Subgroup G := c.X3 ⊔ zpowers c.u₁

abbrev Jc : Subgroup G := centralizer (c.Zc : Set G)

include c in
theorem t_sq' : t * t = 1 := c.pair.t_sq

theorem conj_xt : t * c.xt * t⁻¹ = c.x := conj_conj_of_sq c.t_sq' c.x

theorem X_card : Nat.card c.X3 = 9 := (c.X3_facts alt6_T3).1

theorem X_comm {a b : G} (ha : a ∈ c.X3) (hb : b ∈ c.X3) : a * b = b * a :=
  (c.X3_facts alt6_T3).2.1 a ha b hb

theorem X_cube {a : G} (ha : a ∈ c.X3) : a ^ 3 = 1 := (c.X3_facts alt6_T3).2.2 a ha

theorem Xt_cube {a : G} (ha : a ∈ c.X3t) : a ^ 3 = 1 := by
  obtain ⟨b, hb, rfl⟩ := c.exists_conj_of_mem_X3t ha
  rw [conj_pow, c.X_cube hb]
  simp

theorem X3t_le : c.X3t ≤ conjSub t c.L₁ := Subgroup.map_mono inf_le_left

theorem xt_mem_X3t : c.xt ∈ c.X3t := ⟨c.x, c.x_mem_X3, rfl⟩

theorem xt_cube : c.xt ^ 3 = 1 := c.Xt_cube c.xt_mem_X3t

theorem x_cube : c.x ^ 3 = 1 := c.X_cube c.x_mem_X3

theorem xt_ne_one : c.xt ≠ 1 := by
  intro h
  apply c.x_ne_one
  simpa using h

theorem orderOf_xt : orderOf c.xt = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime c.xt_cube c.xt_ne_one

theorem c₃_cube : c.c₃ ^ 3 = 1 := by
  have := pow_orderOf_eq_one c.c₃
  rwa [c.c₃_ord] at this

theorem c₃_ne_one : c.c₃ ≠ 1 := by
  intro h
  have := c.c₃_ord
  rw [h, orderOf_one] at this
  omega

theorem c₃_mem_X3 : c.c₃ ∈ c.X3 := ⟨c.c₃_mem_L₁, mem_centralizer_singleton_iff.2 c.c₃_comm_x⟩

theorem zpowers_x_inf_zpowers_c₃ : zpowers c.x ⊓ zpowers c.c₃ = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hz1, hz2⟩
  rw [mem_bot]
  by_contra hz
  have e1 := zpowers_eq_of_mem_of_ne_one c.x_cube c.x_ne_one hz1 hz
  have e2 := zpowers_eq_of_mem_of_ne_one c.c₃_cube c.c₃_ne_one hz2 hz
  apply c.c₃_not_mem
  rw [← e1, e2]
  exact mem_zpowers _

theorem X_eq : c.X3 = zpowers c.x ⊔ zpowers c.c₃ := by
  have hle : zpowers c.x ⊔ zpowers c.c₃ ≤ c.X3 :=
    sup_le (zpowers_le.2 c.x_mem_X3) (zpowers_le.2 c.c₃_mem_X3)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  have hcm : Cm (zpowers c.x) (zpowers c.c₃) := cm_zpowers_zpowers c.c₃_comm_x.symm
  rw [card_sup_of_cm hcm c.zpowers_x_inf_zpowers_c₃, Nat.card_zpowers, Nat.card_zpowers,
    c.x_ord, c.c₃_ord, c.X_card]

theorem u₁_comm_L₁ {k : G} (hk : k ∈ c.L₁) : k * c.u₁ = c.u₁ * k :=
  mem_centralizer_iff.1 c.u₁_mem.1.2 k hk

theorem u₁_comm_L₁t {k : G} (hk : k ∈ conjSub t c.L₁) : k * c.u₁ = c.u₁ * k :=
  mem_centralizer_iff.1 c.u₁_mem.2 k hk

theorem u₁_mul_u : c.u₁ * c.u = c.u * c.u₁ := mem_centralizer_singleton_iff.1 c.u₁_mem.1.1

theorem u₁_sq : c.u₁ * c.u₁ = 1 := by
  have := pow_orderOf_eq_one c.u₁
  rwa [c.u₁_ord, pow_two] at this

theorem u₁_ne_one : c.u₁ ≠ 1 := by
  intro h
  have := c.u₁_ord
  rw [h, orderOf_one] at this
  omega

theorem u₁_cube : c.u₁ ^ 3 = c.u₁ := by
  rw [pow_succ, pow_two, c.u₁_sq, one_mul]

theorem cm_x_K₁ : Cm (zpowers c.x) c.K₁ := cm_zpowers_left fun b hb => (c.K₁_comm_x b hb).symm

theorem cm_xt_K₁ : Cm (zpowers c.xt) c.K₁ := cm_zpowers_left fun b hb => (c.K₁_comm_xt b hb).symm

theorem cm_x_u₁ : Cm (zpowers c.x) (zpowers c.u₁) :=
  cm_zpowers_zpowers (c.u₁_comm_L₁ c.x_mem)

theorem cm_xt_u₁ : Cm (zpowers c.xt) (zpowers c.u₁) :=
  cm_zpowers_zpowers (c.u₁_comm_L₁t (c.X3t_le c.xt_mem_X3t))

theorem cm_x_B : Cm (zpowers c.x) c.Bsub := Cm.sup_right c.cm_x_K₁ c.cm_x_u₁

theorem cm_xt_B : Cm (zpowers c.xt) c.Bsub := Cm.sup_right c.cm_xt_K₁ c.cm_xt_u₁

theorem cm_A_B : Cm c.Asub c.Bsub := Cm.sup_left c.cm_x_B c.cm_xt_B

theorem cm_x_Bt : Cm (zpowers c.x) c.Btsub := by
  have := Cm.conj t c.cm_xt_B
  rwa [conjSub_zpowers, c.conj_xt] at this

theorem cm_xt_Bt : Cm (zpowers c.xt) c.Btsub := by
  have := Cm.conj t c.cm_x_B
  rwa [conjSub_zpowers] at this

theorem cm_A_Bt : Cm c.Asub c.Btsub := Cm.sup_left c.cm_x_Bt c.cm_xt_Bt

theorem cm_K₁_conjK₁ : Cm c.K₁ (conjSub t c.K₁) := by
  intro a ha
  rw [mem_centralizer_iff]
  intro b hb
  obtain ⟨k, hk, rfl⟩ := mem_conjSub.1 hb
  exact (c.K₁_comm_K₁t a ha k hk).symm

theorem cm_u₁_conjK₁ : Cm (zpowers c.u₁) (conjSub t c.K₁) := by
  refine cm_zpowers_left fun b hb => ?_
  obtain ⟨k, hk, rfl⟩ := mem_conjSub.1 hb
  exact c.u₁_comm_K₁t k hk

theorem cm_K₁_conju₁ : Cm c.K₁ (conjSub t (zpowers c.u₁)) := by
  have := Cm.conj t c.cm_u₁_conjK₁
  rw [conjSub_conjSub c.t_sq'] at this
  exact this.symm

theorem cm_u₁_conju₁ : Cm (zpowers c.u₁) (conjSub t (zpowers c.u₁)) := by
  rw [conjSub_zpowers]
  refine cm_zpowers_zpowers ?_
  rw [c.u₁_conj]
  calc c.u₁ * (c.u * c.u₁) = (c.u₁ * c.u) * c.u₁ := by group
    _ = (c.u * c.u₁) * c.u₁ := by rw [c.u₁_mul_u]

theorem cm_B_Bt : Cm c.Bsub c.Btsub := by
  have h : Cm (c.K₁ ⊔ zpowers c.u₁) (conjSub t c.K₁ ⊔ conjSub t (zpowers c.u₁)) :=
    Cm.sup_left (Cm.sup_right c.cm_K₁_conjK₁ c.cm_K₁_conju₁)
      (Cm.sup_right c.cm_u₁_conjK₁ c.cm_u₁_conju₁)
  rwa [← conjSub_sup] at h

theorem cm_AB_Bt : Cm (c.Asub ⊔ c.Bsub) c.Btsub := Cm.sup_left c.cm_A_Bt c.cm_B_Bt

theorem Zc_le_AB : c.Zc ≤ c.Asub ⊔ c.Bsub := by
  refine sup_le ?_ (zpowers_le.2 (mem_sup_right (mem_sup_right (mem_zpowers _))))
  rw [c.X_eq]
  exact sup_le (le_sup_left.trans le_sup_left)
    (zpowers_le.2 (mem_sup_right (mem_sup_left c.c₃_mem_K₁)))

theorem cm_X_X3t : Cm c.X3 c.X3t := by
  intro a ha
  rw [mem_centralizer_iff]
  intro b hb
  exact (c.comm_L₁_conj ha.1 (c.X3t_le hb)).eq.symm

theorem cm_Z_X3t : Cm c.Zc c.X3t := by
  refine Cm.sup_left c.cm_X_X3t ?_
  refine cm_zpowers_left fun b hb => ?_
  exact (c.u₁_comm_L₁t (c.X3t_le hb)).symm

theorem cm_Z_xt : Cm c.Zc (zpowers c.xt) :=
  c.cm_Z_X3t.mono le_rfl (zpowers_le.2 c.xt_mem_X3t)

theorem cm_Z_Bt : Cm c.Zc c.Btsub := c.cm_AB_Bt.mono c.Zc_le_AB le_rfl

theorem cm_X_u₁ : Cm c.X3 (zpowers c.u₁) := by
  refine Cm.symm (cm_zpowers_left fun b hb => ?_)
  exact (c.u₁_comm_L₁ hb.1).symm

theorem cm_Z_Z : Cm c.Zc c.Zc := by
  have h1 : Cm c.X3 c.X3 := fun a ha => mem_centralizer_iff.2 fun b hb => (c.X_comm ha hb).symm
  exact Cm.sup_left (Cm.sup_right h1 c.cm_X_u₁)
    (Cm.sup_right c.cm_X_u₁.symm (cm_zpowers_zpowers rfl))

theorem Zc_le_Jc : c.Zc ≤ c.Jc := c.cm_Z_Z

theorem xt_mem_J : c.xt ∈ c.Jc := c.cm_Z_xt.symm (mem_zpowers _)

theorem X3t_le_J : c.X3t ≤ c.Jc := c.cm_Z_X3t.symm

theorem Bt_le_J : c.Btsub ≤ c.Jc := c.cm_Z_Bt.symm

theorem mem_Zc_iff {z : G} : z ∈ c.Zc ↔ ∃ a ∈ c.X3, ∃ w ∈ zpowers c.u₁, z = a * w :=
  mem_sup_iff_of_cm c.cm_X_u₁

theorem u₁_not_mem_X3 : c.u₁ ∉ c.X3 := by
  intro h
  have h1 := c.X_cube h
  rw [c.u₁_cube] at h1
  exact c.u₁_ne_one h1

theorem mem_X3_of_cube {z : G} (hz : z ∈ c.Zc) (h3 : z ^ 3 = 1) : z ∈ c.X3 := by
  obtain ⟨a, ha, w, hw, rfl⟩ := c.mem_Zc_iff.1 hz
  rcases eq_one_or_eq_of_mem_zpowers_of_mul_self c.u₁_sq hw with rfl | rfl
  · simpa using ha
  · exfalso
    have hc : Commute a c.u₁ := (c.cm_X_u₁.comm ha (mem_zpowers _) : a * c.u₁ = c.u₁ * a)
    rw [hc.mul_pow, c.X_cube ha, c.u₁_cube, one_mul] at h3
    exact c.u₁_ne_one h3

theorem eq_one_of_mem_Zc_X3t {z : G} (hz : z ∈ c.Zc) (hz' : z ∈ c.X3t) : z = 1 := by
  have h := c.mem_X3_of_cube hz (c.Xt_cube hz')
  have : z ∈ c.X3 ⊓ c.X3t := ⟨h, hz'⟩
  rw [c.X3_inf_X3t, mem_bot] at this
  exact this

theorem card_Zc : Nat.card c.Zc = 18 := by
  have hd : c.X3 ⊓ zpowers c.u₁ = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hz1, hz2⟩
    rw [mem_bot]
    rcases eq_one_or_eq_of_mem_zpowers_of_mul_self c.u₁_sq hz2 with h | h
    · exact h
    · exact absurd (h ▸ hz1) c.u₁_not_mem_X3
  rw [card_sup_of_cm c.cm_X_u₁ hd, c.X_card, Nat.card_zpowers, c.u₁_ord]

@[expose] noncomputable def eB : ↥c.Bsub ≃* Equiv.Perm (Fin 5) := c.u₁_S₅.some

theorem B_cent {b : G} (hb : b ∈ c.Bsub) (h1 : b * c.c₃ = c.c₃ * b) (h2 : b * c.u₁ = c.u₁ * b) :
    ∃ i : Fin 3, ∃ j : Fin 2, b = c.c₃ ^ (i : ℕ) * c.u₁ ^ (j : ℕ) := by
  let c3B : ↥c.Bsub := ⟨c.c₃, mem_sup_left c.c₃_mem_K₁⟩
  let u1B : ↥c.Bsub := ⟨c.u₁, mem_sup_right (mem_zpowers _)⟩
  let bB : ↥c.Bsub := ⟨b, hb⟩
  have e1 : c.eB c3B * (c.eB c3B * c.eB c3B) = 1 := by
    rw [← map_mul, ← map_mul, ← map_one c.eB]
    congr 1
    apply Subtype.ext
    have := c.c₃_cube
    simpa [pow_succ, mul_assoc] using this
  have e2 : c.eB c3B ≠ 1 := by
    intro h
    apply c.c₃_ne_one
    have := c.eB.injective (h.trans (map_one c.eB).symm)
    exact congrArg Subtype.val this
  have e3 : c.eB u1B * c.eB u1B = 1 := by
    rw [← map_mul, ← map_one c.eB]
    congr 1
    exact Subtype.ext c.u₁_sq
  have e4 : c.eB u1B ≠ 1 := by
    intro h
    apply c.u₁_ne_one
    have := c.eB.injective (h.trans (map_one c.eB).symm)
    exact congrArg Subtype.val this
  have e5 : c.eB c3B * c.eB u1B = c.eB u1B * c.eB c3B := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (c.u₁_comm_L₁ c.c₃_mem_L₁)
  have e6 : c.eB bB * c.eB c3B = c.eB c3B * c.eB bB := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h1
  have e7 : c.eB bB * c.eB u1B = c.eB u1B * c.eB bB := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h2
  obtain ⟨i, j, hij⟩ := s5_centralizer_pair _ _ e1 e2 e3 e4 e5 _ e6 e7
  refine ⟨i, j, ?_⟩
  have : bB = c3B ^ (i : ℕ) * u1B ^ (j : ℕ) := by
    apply c.eB.injective
    rw [hij, map_mul, map_pow, map_pow]
  exact congrArg Subtype.val this

abbrev Rc : Subgroup G := c.Jc ⊓ centralizer ({c.xt} : Set G)

theorem x_comm_xt : c.x * c.xt = c.xt * c.x := (c.pair.comm c.x c.x_mem c.x c.x_mem).eq

theorem cm_x_xt : Cm (zpowers c.x) (zpowers c.xt) := cm_zpowers_zpowers c.x_comm_xt

theorem Rc_le : c.Rc ≤ c.Zc ⊔ zpowers c.xt ⊔ c.Btsub := by
  rintro g ⟨hgJ, hgxt⟩
  have hx : c.x ∈ c.Zc := mem_sup_left c.x_mem_X3
  have hgx : g ∈ centralizer ({c.x} : Set G) :=
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hgJ c.x hx).symm
  have hD : g ∈ centralizer ({c.x} : Set G) ⊓ centralizer ({t * c.x * t⁻¹} : Set G) :=
    ⟨hgx, hgxt⟩
  rw [c.centralizer_x_xt] at hD
  obtain ⟨m, hm, b', hb', rfl⟩ := (mem_sup_iff_of_cm c.cm_AB_Bt).1 hD
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_cm c.cm_A_B).1 hm
  have key : ∀ e ∈ c.Bsub, e ∈ c.Zc → e * (a * b * b') = (a * b * b') * e →
      e * b = b * e := fun e he _ h =>
    comm_middle (c.cm_A_B.comm ha he).symm (c.cm_B_Bt.comm he hb') h
  have hc3 : c.c₃ * b = b * c.c₃ := key c.c₃ (mem_sup_left c.c₃_mem_K₁) (mem_sup_left c.c₃_mem_X3)
    (mem_centralizer_iff.1 hgJ c.c₃ (mem_sup_left c.c₃_mem_X3))
  have hu1 : c.u₁ * b = b * c.u₁ := key c.u₁ (mem_sup_right (mem_zpowers _))
    (mem_sup_right (mem_zpowers _))
    (mem_centralizer_iff.1 hgJ c.u₁ (mem_sup_right (mem_zpowers _)))
  obtain ⟨i, j, hij⟩ := c.B_cent hb hc3.symm hu1.symm
  have hbZ : b ∈ c.Zc := by
    rw [hij]
    exact mul_mem (mem_sup_left (pow_mem c.c₃_mem_X3 _))
      (mem_sup_right (pow_mem (mem_zpowers _) _))
  obtain ⟨p, hp, q, hq, rfl⟩ := (mem_sup_iff_of_cm c.cm_x_xt).1 ha
  have hpZ : p ∈ c.Zc := mem_sup_left (zpowers_le.2 c.x_mem_X3 hp)
  have hqb : q * b = b * q := c.cm_A_B.comm (mem_sup_right hq) hb
  have e : p * q * b * b' = (p * b) * q * b' := by
    calc p * q * b * b' = p * (q * b) * b' := by group
      _ = p * (b * q) * b' := by rw [hqb]
      _ = (p * b) * q * b' := by group
  rw [e]
  exact mul_mem (mul_mem (mem_sup_left (mem_sup_left (mul_mem hpZ hbZ)))
    (mem_sup_left (mem_sup_right hq))) (mem_sup_right hb')

theorem le_Rc : c.Zc ⊔ zpowers c.xt ⊔ c.Btsub ≤ c.Rc := by
  refine le_inf (sup_le (sup_le c.Zc_le_Jc (zpowers_le.2 c.xt_mem_J)) c.Bt_le_J) ?_
  refine sup_le (sup_le ?_ ?_) ?_
  · intro z hz
    exact mem_centralizer_singleton_iff.2 (c.cm_Z_xt.comm hz (mem_zpowers _))
  · exact zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)
  · intro b hb
    exact mem_centralizer_singleton_iff.2 (c.cm_xt_Bt.comm (mem_zpowers _) hb).symm

theorem centralizer_xt_inf_J :
    c.Jc ⊓ centralizer ({c.xt} : Set G) =
      c.Zc ⊔ zpowers c.xt ⊔ conjSub t (c.K₁ ⊔ zpowers c.u₁) :=
  le_antisymm c.Rc_le c.le_Rc

@[expose] noncomputable def cE : Multiplicative (ZMod 3) ≃* ↥(zpowers c.xt) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact mulEquivOfPrimeCardEq (p := 3) (by simp [Nat.card_eq_fintype_card])
    (by rw [Nat.card_zpowers]; exact c.orderOf_xt)

@[expose] noncomputable def eBt : Equiv.Perm (Fin 5) ≃* ↥c.Btsub :=
  c.eB.symm.trans (MulEquiv.subgroupMap (MulAut.conj t) c.Bsub)

@[expose] noncomputable def Phi0 : Multiplicative (ZMod 3) × Equiv.Perm (Fin 5) →* G :=
  MonoidHom.noncommCoprod ((zpowers c.xt).subtype.comp c.cE.toMonoidHom)
    (c.Btsub.subtype.comp c.eBt.toMonoidHom)
    (fun ζ σ => (c.cm_xt_Bt.comm (c.cE ζ).2 (c.eBt σ).2 :
      ((c.cE ζ : ↥(zpowers c.xt)) : G) * (c.eBt σ : G) = (c.eBt σ : G) * (c.cE ζ : G)))

theorem Phi0_apply (ζ : Multiplicative (ZMod 3)) (σ : Equiv.Perm (Fin 5)) :
    c.Phi0 (ζ, σ) = ((c.cE ζ : ↥(zpowers c.xt)) : G) * ((c.eBt σ : ↥c.Btsub) : G) := by
  simp [Phi0]

theorem Phi0_mem_J (p : Multiplicative (ZMod 3) × Equiv.Perm (Fin 5)) : c.Phi0 p ∈ c.Jc := by
  obtain ⟨ζ, σ⟩ := p
  rw [Phi0_apply]
  exact mul_mem (zpowers_le.2 c.xt_mem_J (c.cE ζ).2) (c.Bt_le_J (c.eBt σ).2)

theorem exists_Phi0 {g : G} (hg : g ∈ zpowers c.xt ⊔ c.Btsub) :
    ∃ p, c.Phi0 p = g := by
  obtain ⟨w, hw, b, hb, rfl⟩ := (mem_sup_iff_of_cm c.cm_xt_Bt).1 hg
  refine ⟨(c.cE.symm ⟨w, hw⟩, c.eBt.symm ⟨b, hb⟩), ?_⟩
  rw [Phi0_apply]
  simp

theorem Phi0_mem_sup (p : Multiplicative (ZMod 3) × Equiv.Perm (Fin 5)) :
    c.Phi0 p ∈ zpowers c.xt ⊔ c.Btsub := by
  obtain ⟨ζ, σ⟩ := p
  rw [Phi0_apply]
  exact mul_mem (mem_sup_left (c.cE ζ).2) (mem_sup_right (c.eBt σ).2)

theorem Phi0_mem_Zc {p : Multiplicative (ZMod 3) × Equiv.Perm (Fin 5)} (h : c.Phi0 p ∈ c.Zc) :
    p = 1 := by
  obtain ⟨ζ, σ⟩ := p
  rw [Phi0_apply] at h
  have hw : ((c.cE ζ : ↥(zpowers c.xt)) : G) ∈ zpowers c.xt := (c.cE ζ).2
  have hAB : ((c.eBt σ : ↥c.Btsub) : G) ∈ c.Asub ⊔ c.Bsub := by
    have e : ((c.eBt σ : ↥c.Btsub) : G) =
        (((c.cE ζ : ↥(zpowers c.xt)) : G))⁻¹ *
          (((c.cE ζ : ↥(zpowers c.xt)) : G) * (c.eBt σ : G)) := by group
    rw [e]
    exact mul_mem (inv_mem (mem_sup_left (mem_sup_right hw))) (c.Zc_le_AB h)
  have hσ : σ = 1 := by
    apply CFSG.perm_eq_one_of_forall_commute (by simp)
    intro g
    have h1 := c.cm_AB_Bt.comm hAB (c.eBt g).2
    apply c.eBt.injective
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul]
    exact h1
  rw [hσ, map_one] at h
  simp only [OneMemClass.coe_one, mul_one] at h
  have hw1 : ((c.cE ζ : ↥(zpowers c.xt)) : G) = 1 :=
    c.eq_one_of_mem_Zc_X3t h (zpowers_le.2 c.xt_mem_X3t hw)
  have hζ : ζ = 1 := c.cE.map_eq_one_iff.1 (Subtype.ext hw1)
  rw [hσ, hζ]
  rfl

theorem range_Phi0 : c.Phi0.range = zpowers c.xt ⊔ c.Btsub := by
  ext g
  constructor
  · rintro ⟨p, rfl⟩
    exact c.Phi0_mem_sup p
  · intro hg
    obtain ⟨p, hp⟩ := c.exists_Phi0 hg
    exact ⟨p, hp⟩

theorem Rc_eq : c.Rc = c.Zc ⊔ c.Phi0.range := by
  rw [c.range_Phi0, ← sup_assoc]
  exact c.centralizer_xt_inf_J

theorem conj_xt_eq_of_mem (hρ : c.rho.range = ⊤) {g : G}
    (hz : ∃ z ∈ c.Zc, g * c.xt * g⁻¹ = c.xt * z) : g * c.xt * g⁻¹ = c.xt := by
  obtain ⟨z, hzZ, hgz⟩ := hz
  have hcom : c.xt * z = z * c.xt := (c.cm_Z_xt.comm hzZ (mem_zpowers _)).symm
  have h1 : (g * c.xt * g⁻¹) ^ 3 = 1 := by
    rw [conj_pow, c.xt_cube]
    simp
  rw [hgz, (show Commute c.xt z from hcom).mul_pow, c.xt_cube, one_mul] at h1
  have hzX : z ∈ c.X3 := c.mem_X3_of_cube hzZ h1
  by_cases hz1 : z = 1
  · rw [hgz, hz1, mul_one]
  · exfalso
    have hxt : IsConj c.x c.xt :=
      c.isConj_x_of_mem alt6_T1 hρ (fun a ha => c.X_cube ha) (Or.inr c.xt_mem_X3t) c.xt_ne_one
    have hy : IsConj c.y (z * c.xt) :=
      c.isConj_y_mul alt6_T1 hρ (fun a ha => c.X_cube ha) hzX hz1 c.xt_mem_X3t c.xt_ne_one
    have hg : IsConj c.xt (g * c.xt * g⁻¹) := isConj_iff.2 ⟨g, rfl⟩
    rw [hgz, hcom] at hg
    exact c.not_isConj_x_y hρ alt6_T2 ((hxt.trans hg).trans hy.symm)

instance instNormalZcSubgroupOf (c : InnerD8ConfigC L t) :
    (c.Zc.subgroupOf c.Jc).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h : (n : G) * g = g * n := mem_centralizer_iff.1 g.2 n hn
    have e : (g * n * g⁻¹ : ↥c.Jc) = n := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [mul_inv_eq_iff_eq_mul]
      exact h.symm
    rw [e]
    exact hn⟩

abbrev Yq : Type := ↥c.Jc ⧸ c.Zc.subgroupOf c.Jc

@[expose] def mkY : ↥c.Jc →* c.Yq := QuotientGroup.mk' (c.Zc.subgroupOf c.Jc)

theorem mkY_surjective : Function.Surjective c.mkY := QuotientGroup.mk'_surjective _

theorem mkY_eq_one_iff (g : ↥c.Jc) : c.mkY g = 1 ↔ (g : G) ∈ c.Zc := by
  rw [mkY, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

@[expose] def xbar : c.Yq := c.mkY ⟨c.xt, c.xt_mem_J⟩

@[expose] noncomputable def Phi1 : Multiplicative (ZMod 3) × Equiv.Perm (Fin 5) →* c.Yq :=
  c.mkY.comp (c.Phi0.codRestrict c.Jc c.Phi0_mem_J)

theorem Phi1_apply (p : Multiplicative (ZMod 3) × Equiv.Perm (Fin 5)) :
    c.Phi1 p = c.mkY ⟨c.Phi0 p, c.Phi0_mem_J p⟩ := rfl

theorem Phi1_injective : Function.Injective c.Phi1 :=
  (injective_iff_map_eq_one _).2 fun p h =>
    c.Phi0_mem_Zc ((c.mkY_eq_one_iff ⟨c.Phi0 p, c.Phi0_mem_J p⟩).1 h)

theorem centralizer_xbar_eq (hρ : c.rho.range = ⊤) :
    centralizer ({c.xbar} : Set c.Yq) = c.Phi1.range := by
  ext y
  obtain ⟨g, rfl⟩ := c.mkY_surjective y
  constructor
  · intro hy
    rw [mem_centralizer_singleton_iff] at hy
    let xt' : ↥c.Jc := ⟨c.xt, c.xt_mem_J⟩
    have h1 : c.mkY (g * xt' * g⁻¹ * xt'⁻¹) = 1 := by
      have hy' : c.mkY g * c.mkY xt' = c.mkY xt' * c.mkY g := hy
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      calc c.mkY g * c.mkY xt' * (c.mkY g)⁻¹ * (c.mkY xt')⁻¹
          = (c.mkY xt' * c.mkY g) * (c.mkY g)⁻¹ * (c.mkY xt')⁻¹ := by rw [hy']
        _ = 1 := by group
    have h2 : (g : G) * c.xt * (g : G)⁻¹ * c.xt⁻¹ ∈ c.Zc := (c.mkY_eq_one_iff _).1 h1
    have hcom : c.xt * ((g : G) * c.xt * (g : G)⁻¹ * c.xt⁻¹) =
        ((g : G) * c.xt * (g : G)⁻¹ * c.xt⁻¹) * c.xt :=
      (c.cm_Z_xt.comm h2 (mem_zpowers _)).symm
    have h3 : (g : G) * c.xt * (g : G)⁻¹ = c.xt := by
      apply c.conj_xt_eq_of_mem hρ
      refine ⟨_, h2, ?_⟩
      calc (g : G) * c.xt * (g : G)⁻¹ = ((g : G) * c.xt * (g : G)⁻¹ * c.xt⁻¹) * c.xt := by group
        _ = c.xt * ((g : G) * c.xt * (g : G)⁻¹ * c.xt⁻¹) := hcom.symm
    have hR : (g : G) ∈ c.Rc :=
      ⟨g.2, mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 h3)⟩
    rw [c.Rc_eq] at hR
    obtain ⟨z0, hz0, e, ⟨p, rfl⟩, hge⟩ := (mem_sup_iff_of_cm
      (c.cm_Z_xt.sup_right c.cm_Z_Bt |>.mono le_rfl (c.range_Phi0 ▸ le_rfl))).1 hR
    refine ⟨p, ?_⟩
    rw [Phi1_apply]
    have : g = ⟨z0, c.Zc_le_Jc hz0⟩ * ⟨c.Phi0 p, c.Phi0_mem_J p⟩ := Subtype.ext hge
    rw [this, map_mul, (c.mkY_eq_one_iff ⟨z0, c.Zc_le_Jc hz0⟩).2 hz0, one_mul]
  · rintro ⟨p, hp⟩
    rw [mem_centralizer_singleton_iff, ← hp, Phi1_apply, xbar, ← map_mul, ← map_mul]
    congr 1
    have hR : c.Phi0 p ∈ c.Rc := by
      rw [c.Rc_eq]
      exact mem_sup_right ⟨p, rfl⟩
    exact Subtype.ext (mem_centralizer_singleton_iff.1 hR.2)

theorem centralizer_xbar_equiv (hρ : c.rho.range = ⊤) :
    Nonempty (↥(centralizer ({c.xbar} : Set c.Yq)) ≃*
      Multiplicative (ZMod 3) × Equiv.Perm (Fin 5)) :=
  ⟨(MulEquiv.subgroupCongr (c.centralizer_xbar_eq hρ)).trans
    (MonoidHom.ofInjective c.Phi1_injective).symm⟩

theorem Xt_comm {a b : G} (ha : a ∈ c.X3t) (hb : b ∈ c.X3t) : a * b = b * a := by
  obtain ⟨a₀, ha₀, rfl⟩ := c.exists_conj_of_mem_X3t ha
  obtain ⟨b₀, hb₀, rfl⟩ := c.exists_conj_of_mem_X3t hb
  calc t * a₀ * t⁻¹ * (t * b₀ * t⁻¹) = t * (a₀ * b₀) * t⁻¹ := by group
    _ = t * (b₀ * a₀) * t⁻¹ := by rw [c.X_comm ha₀ hb₀]
    _ = _ := by group

abbrev PsiCrit (c : InnerD8ConfigC L t) : Prop :=
  ∀ q : ↥c.P, Commute (q : G) c.u₁ ↔
    c.rho q ∈ (baseSubgroup : Subgroup (Wr2 (MulAut (alternatingGroup (Fin 6)))))

theorem exists_conj_in_J (hρ : c.rho.range = ⊤) (hψ : c.PsiCrit) {b : G} (hb : b ∈ c.X3t)
    (hb1 : b ≠ 1) : ∃ g ∈ c.Jc, g * c.xt * g⁻¹ = b := by
  obtain ⟨b₀, hb₀, rfl⟩ := c.exists_conj_of_mem_X3t hb
  have hb01 : b₀ ≠ 1 := by
    rintro rfl
    apply hb1
    simp
  have hb03 : orderOf b₀ = 3 :=
    c.orderOf_eq_three_of_mem_X3 (fun a ha => c.X_cube ha) hb₀ hb01
  have hord : orderOf (c.eL₁ ⟨b₀, hb₀.1⟩) = 3 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hb03
  obtain ⟨α, hα⟩ := alt6_T1 _ _ c.orderOf_eL₁_x hord
  let β : MulAut ↥c.L₁ := c.eL₁.trans (α.trans c.eL₁.symm)
  have hβ : β ⟨c.x, c.x_mem⟩ = ⟨b₀, hb₀.1⟩ := by
    show c.eL₁.symm (α (c.eL₁ ⟨c.x, c.x_mem⟩)) = _
    rw [hα]
    simp
  obtain ⟨p, hp⟩ := c.exists_pair_rho_eq hρ 1 β
  have hn : (p : G) ∈ normalizer (c.L₁ : Set G) := by
    rw [mem_normalizer_iff_map_eq, ← c.pair.rho_mem_baseSubgroup_iff p, hp, mem_baseSubgroup_iff,
      swapChar_base]
  have hr := c.pair.rho_of_normalizes p hn
  rw [hp, base_injective] at hr
  have hcomL : ∀ k ∈ c.L₁, Commute (p : G) k := (conjAutOf_eq_one_iff c.L₁ hn).1 hr.1.symm
  have h2 := congrArg (fun f : MulAut ↥c.L₁ => ((f ⟨c.x, c.x_mem⟩ : ↥c.L₁) : G)) hr.2
  simp only [hβ, conjAutOf_apply] at h2
  have hcomu : Commute (p : G) c.u₁ := by
    refine (hψ p).2 ?_
    rw [c.rho_apply, hp, mapEquiv_base, mem_baseSubgroup_iff, swapChar_base]
  have hle : c.Zc ≤ centralizer ({(p : G)} : Set G) := by
    refine sup_le (fun a ha => mem_centralizer_singleton_iff.2 (hcomL a ha.1).eq.symm) ?_
    exact zpowers_le.2 (mem_centralizer_singleton_iff.2 hcomu.eq.symm)
  refine ⟨p, mem_centralizer_iff.2 fun z hz => mem_centralizer_singleton_iff.1 (hle hz), ?_⟩
  have htg : t * (t * (p : G) * t) = (p : G) * t := by
    calc t * (t * (p : G) * t) = (t * t) * (p : G) * t := by group
      _ = (p : G) * t := by rw [c.t_sq', one_mul]
  calc (p : G) * (t * c.x * t⁻¹) * (p : G)⁻¹ = ((p : G) * t) * c.x * ((p : G) * t)⁻¹ := by group
    _ = (t * (t * (p : G) * t)) * c.x * (t * (t * (p : G) * t))⁻¹ := by rw [htg]
    _ = t * ((t * (p : G) * t) * c.x * (t * (p : G) * t)⁻¹) * t⁻¹ := by group
    _ = t * b₀ * t⁻¹ := by rw [← h2]

@[expose] def Pbar : Subgroup c.Yq := (c.X3t.subgroupOf c.Jc).map c.mkY

theorem mem_Pbar_iff {y : c.Yq} :
    y ∈ c.Pbar ↔ ∃ b ∈ c.X3t, ∃ hb : b ∈ c.Jc, c.mkY ⟨b, hb⟩ = y := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, g.2, rfl⟩
  · rintro ⟨b, hb, hbJ, rfl⟩
    exact ⟨⟨b, hbJ⟩, hb, rfl⟩

theorem Pbar_comm : ∀ a ∈ c.Pbar, ∀ b ∈ c.Pbar, a * b = b * a := by
  intro a ha b hb
  obtain ⟨a₀, ha₀, haJ, rfl⟩ := c.mem_Pbar_iff.1 ha
  obtain ⟨b₀, hb₀, hbJ, rfl⟩ := c.mem_Pbar_iff.1 hb
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (c.Xt_comm ha₀ hb₀)

theorem Pbar_cube : ∀ a ∈ c.Pbar, a ^ 3 = 1 := by
  intro a ha
  obtain ⟨a₀, ha₀, haJ, rfl⟩ := c.mem_Pbar_iff.1 ha
  rw [← map_pow, ← map_one c.mkY]
  congr 1
  exact Subtype.ext (c.Xt_cube ha₀)

theorem card_Pbar : Nat.card c.Pbar = 9 := by
  let φ : ↥(c.X3t.subgroupOf c.Jc) →* c.Yq := c.mkY.comp (c.X3t.subgroupOf c.Jc).subtype
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨g, hg⟩ h
    have h1 : c.mkY g = 1 := h
    have h2 := (c.mkY_eq_one_iff g).1 h1
    rw [Subgroup.mem_subgroupOf] at hg
    exact Subtype.ext (Subtype.ext (c.eq_one_of_mem_Zc_X3t h2 hg))
  have hr : φ.range = c.Pbar := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have h := Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv
  rw [← hr, ← h]
  exact (Nat.card_congr (subgroupOfEquivOfLe c.X3t_le_J).toEquiv).trans (c.card_X3t c.X_card)

theorem centralizer_equiv_of_mem_Pbar (hρ : c.rho.range = ⊤) (hψ : c.PsiCrit) {y : c.Yq}
    (hy : y ∈ c.Pbar) (hy1 : y ≠ 1) :
    Nonempty (↥(centralizer ({y} : Set c.Yq)) ≃*
      Multiplicative (ZMod 3) × Equiv.Perm (Fin 5)) := by
  obtain ⟨b, hb, hbJ, rfl⟩ := c.mem_Pbar_iff.1 hy
  have hb1 : b ≠ 1 := by
    rintro rfl
    exact hy1 (map_one c.mkY)
  obtain ⟨g, hgJ, hg⟩ := c.exists_conj_in_J hρ hψ hb hb1
  have e : c.mkY ⟨b, hbJ⟩ = c.mkY ⟨g, hgJ⟩ * c.xbar * (c.mkY ⟨g, hgJ⟩)⁻¹ := by
    rw [xbar, ← map_mul, ← map_inv, ← map_mul]
    congr 1
    exact Subtype.ext hg.symm
  rw [e]
  obtain ⟨e1⟩ := centralizer_equiv_of_conj (c.mkY ⟨g, hgJ⟩) c.xbar
  obtain ⟨e2⟩ := c.centralizer_xbar_equiv hρ
  exact ⟨e1.trans e2⟩

theorem eq_bot_of_normal (hρ : c.rho.range = ⊤) (hψ : c.PsiCrit) (A : Subgroup c.Yq)
    (hA : A.Normal) (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : A = ⊥ := by
  refine eq_bot_of_normal_of_commute c.Pbar c.Pbar_comm c.Pbar_cube c.card_Pbar ?_ A hA hAab
  intro a ha ha1 Q hQ hQn hQab
  obtain ⟨e⟩ := c.centralizer_equiv_of_mem_Pbar hρ hψ ha ha1
  exact le_zpowers_of_centralizer_equiv ha1 (c.Pbar_cube a ha) e Q hQ hQn hQab

end InnerD8ConfigC

end Config

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus

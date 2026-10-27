module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropTwelveA
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoStatements

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTwelve

open Subgroup CFSG.Semidihedral.Principal.PrimewiseScalar

variable {G : Type} [Group G] [Finite G] {z : G}

structure Hyp (fr : JankoFrame G z) : Prop where
  set : JankoSetting G z
  frs : JankoFrames G
  p7 : JankoProp7 fr
  p9 : ¬ centralizer (fr.P₁ : Set G) ≤ centralizer ({z} : Set G)
  p10 : JankoProp10 fr
  p11 : JankoProp11 fr

theorem mem_normalizer_centralizer {A : Subgroup G} {g : G} (hg : g ∈ normalizer (A : Set G)) :
    g ∈ normalizer (centralizer (A : Set G) : Set G) := by
  refine CFSG.Walter.J1.mem_normalizer_of_conj_mem fun x hx => ?_
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro a ha
  have ha' : g⁻¹ * a * g ∈ A := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) a).mp ha
    rwa [inv_inv] at this
  have h1 := hx _ ha'
  calc a * (g * x * g⁻¹) = g * ((g⁻¹ * a * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1]
    _ = g * x * g⁻¹ * a := by group

theorem mem_normalizer_centralizer_singleton {u g : G} (h : g * u = u * g) :
    g ∈ normalizer (centralizer ({u} : Set G) : Set G) := by
  refine CFSG.Walter.J1.mem_normalizer_of_conj_mem fun x hx => ?_
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  have hg' : g⁻¹ * u = u * g⁻¹ := by
    calc g⁻¹ * u = g⁻¹ * (u * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * u) * g⁻¹ := by rw [h]
      _ = u * g⁻¹ := by group
  calc g * x * g⁻¹ * u = g * x * (g⁻¹ * u) := by group
    _ = g * (x * u) * g⁻¹ := by rw [hg']; group
    _ = g * (u * x) * g⁻¹ := by rw [hx]
    _ = u * (g * x * g⁻¹) := by rw [← mul_assoc, h]; group

namespace Hyp

variable {fr : JankoFrame G z}

theorem z_mul_z (h : Hyp fr) : z * z = 1 :=
  (CFSG.Walter.J1.orderOf_eq_two_iff.mp h.set.orderOf_z).1

theorem z_ne_one (h : Hyp fr) : z ≠ 1 :=
  (CFSG.Walter.J1.orderOf_eq_two_iff.mp h.set.orderOf_z).2

theorem z_inv (h : Hyp fr) : z⁻¹ = z :=
  inv_eq_of_mul_eq_one_right h.z_mul_z

theorem t_mul_t (_h : Hyp fr) : fr.t * fr.t = 1 :=
  (CFSG.Walter.J1.orderOf_eq_two_iff.mp fr.orderOf_t).1

theorem t_ne_one (_h : Hyp fr) : fr.t ≠ 1 :=
  (CFSG.Walter.J1.orderOf_eq_two_iff.mp fr.orderOf_t).2

theorem t_inv (h : Hyp fr) : fr.t⁻¹ = fr.t :=
  inv_eq_of_mul_eq_one_right h.t_mul_t

theorem t_comm_z (_h : Hyp fr) : fr.t * z = z * fr.t :=
  Subgroup.mem_centralizer_singleton_iff.mp fr.t_mem

theorem tz_mul_tz (h : Hyp fr) : fr.t * z * (fr.t * z) = 1 := by
  calc fr.t * z * (fr.t * z) = fr.t * (z * fr.t) * z := by group
    _ = fr.t * (fr.t * z) * z := by rw [h.t_comm_z]
    _ = (fr.t * fr.t) * (z * z) := by group
    _ = 1 := by rw [h.t_mul_t, h.z_mul_z, one_mul]

theorem tz_ne_one (h : Hyp fr) : fr.t * z ≠ 1 := by
  intro h1
  apply fr.t_ne
  rw [← mul_one fr.t, ← h.z_mul_z, ← mul_assoc, h1, one_mul]

theorem orderOf_tz (h : Hyp fr) : orderOf (fr.t * z) = 2 :=
  CFSG.Walter.J1.orderOf_eq_two_iff.mpr ⟨h.tz_mul_tz, h.tz_ne_one⟩

theorem ℓ_mem_L (_h : Hyp fr) : fr.ℓ ∈ fr.L := by
  rw [fr.L_eq]
  exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem t_mem_L (_h : Hyp fr) : fr.t ∈ fr.L := by
  rw [fr.L_eq]
  exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem z_mem_L (h : Hyp fr) : z ∈ fr.L := by
  have := Subgroup.pow_mem _ h.ℓ_mem_L 4
  rwa [fr.ℓ_pow_four] at this

theorem L_le_H (_h : Hyp fr) : fr.L ≤ centralizer ({z} : Set G) :=
  fr.L_le_K.trans fr.K_le

theorem t_mem_K (h : Hyp fr) : fr.t ∈ fr.K := fr.L_le_K h.t_mem_L

theorem z_mem_K (h : Hyp fr) : z ∈ fr.K := fr.L_le_K h.z_mem_L

theorem ℓ_sq_conj_t (h : Hyp fr) : fr.ℓ ^ 2 * fr.t * (fr.ℓ ^ 2)⁻¹ = fr.t * z := by
  have hc : fr.t⁻¹ * fr.ℓ * fr.t = fr.ℓ ^ 3 := by
    have := fr.t_mul_ℓ
    rw [h.t_inv] at this ⊢
    exact this
  have hc2 : fr.t⁻¹ * fr.ℓ ^ 2 * fr.t = fr.ℓ ^ 6 := by
    rw [show fr.t⁻¹ * fr.ℓ ^ 2 * fr.t = (fr.t⁻¹ * fr.ℓ * fr.t) ^ 2 by
      rw [pow_two, pow_two]; group, hc, ← pow_mul]
  calc fr.ℓ ^ 2 * fr.t * (fr.ℓ ^ 2)⁻¹ = fr.t * (fr.t⁻¹ * fr.ℓ ^ 2 * fr.t) * (fr.ℓ ^ 2)⁻¹ := by
        group
    _ = fr.t * fr.ℓ ^ 6 * (fr.ℓ ^ 2)⁻¹ := by rw [hc2]
    _ = fr.t * fr.ℓ ^ 4 := by group
    _ = fr.t * z := by rw [fr.ℓ_pow_four]

theorem ℓ_sq_inv_conj_tz (h : Hyp fr) : (fr.ℓ ^ 2)⁻¹ * (fr.t * z) * fr.ℓ ^ 2 = fr.t := by
  rw [← h.ℓ_sq_conj_t]
  group

theorem s₁_mem_E (_h : Hyp fr) : fr.s₁ ∈ fr.E := by
  rw [fr.E_eq_closure]
  exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem s₂_mem_E (_h : Hyp fr) : fr.s₂ ∈ fr.E := by
  rw [fr.E_eq_closure]
  exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

theorem P₁_le_E (h : Hyp fr) : fr.P₁ ≤ fr.E := by
  rw [fr.P₁_eq, Subgroup.zpowers_le]
  exact h.s₁_mem_E

theorem P₂_le_E (h : Hyp fr) : fr.P₂ ≤ fr.E := by
  rw [fr.P₂_eq, Subgroup.zpowers_le]
  exact h.s₂_mem_E

theorem E_le_N (_h : Hyp fr) : fr.E ≤ fr.N := le_sup_left

theorem M_le_N (_h : Hyp fr) : fr.M ≤ fr.N := le_sup_right

theorem centralizer_P₁_eq (_h : Hyp fr) :
    centralizer (fr.P₁ : Set G) = centralizer ({fr.s₁} : Set G) := by
  rw [fr.P₁_eq]
  exact centralizer_zpowers fr.s₁

theorem M_le_centralizer_P₁ (_h : Hyp fr) : fr.M ≤ centralizer (fr.P₁ : Set G) :=
  oddCoreOf_le _

theorem E_le_centralizer_P₁ (h : Hyp fr) : fr.E ≤ centralizer (fr.P₁ : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact fr.E_comm y (h.P₁_le_E hy) x hx

theorem N_le_centralizer_P₁ (h : Hyp fr) : fr.N ≤ centralizer (fr.P₁ : Set G) :=
  sup_le h.E_le_centralizer_P₁ h.M_le_centralizer_P₁

theorem N_le_centralizer_s₁ (h : Hyp fr) : fr.N ≤ centralizer ({fr.s₁} : Set G) :=
  h.centralizer_P₁_eq ▸ h.N_le_centralizer_P₁

theorem isPGroup_N (h : Hyp fr) : IsPGroup 3 fr.N :=
  IsPGroup.of_card h.p11.card_N

theorem odd_card_N (h : Hyp fr) : Odd (Nat.card fr.N) := by
  rw [h.p11.card_N]
  decide

theorem L_le_normalizer_N (h : Hyp fr) : fr.L ≤ normalizer (fr.N : Set G) := by
  have := h.p11.normalizer_N_inf
  exact le_sup_right.trans (this.symm.le.trans inf_le_left)

theorem L_le_normalizer_P₁ (h : Hyp fr) : fr.L ≤ normalizer (fr.P₁ : Set G) := by
  have := h.p11.normalizer_N_inf
  exact le_sup_right.trans (this.symm.le.trans inf_le_right)

theorem t_mem_normalizer_P₁ (h : Hyp fr) : fr.t ∈ normalizer (fr.P₁ : Set G) :=
  h.L_le_normalizer_P₁ h.t_mem_L

theorem z_mem_centralizer_P₁ (_h : Hyp fr) : z ∈ centralizer (fr.P₁ : Set G) :=
  fr.F_le_centralizer fr.z_mem_F

theorem normalizer_P₁_le_normalizer_M (_h : Hyp fr) :
    normalizer (fr.P₁ : Set G) ≤ normalizer (fr.M : Set G) := fun _ hg =>
  mem_normalizer_oddCoreOf (mem_normalizer_centralizer hg)

theorem z_mem_normalizer_M (h : Hyp fr) : z ∈ normalizer (fr.M : Set G) :=
  le_normalizer_oddCoreOf _ h.z_mem_centralizer_P₁

theorem t_mem_normalizer_M (h : Hyp fr) : fr.t ∈ normalizer (fr.M : Set G) :=
  h.normalizer_P₁_le_normalizer_M h.t_mem_normalizer_P₁

theorem t_conj_s₁ (_h : Hyp fr) : fr.t * fr.s₁ * fr.t⁻¹ = fr.s₁⁻¹ := fr.t_mul_s₁

theorem eq_one_of_mem_P₁_of_comm_t (h : Hyp fr) {x : G} (hx : x ∈ fr.P₁)
    (hxt : x * fr.t = fr.t * x) : x = 1 := by
  have hx3 : x ^ 3 = 1 := by
    have hd := Subgroup.orderOf_dvd_natCard fr.P₁ hx
    rw [fr.P₁_eq, Nat.card_zpowers, fr.orderOf_s₁] at hd
    exact orderOf_dvd_iff_pow_eq_one.mp hd
  rw [fr.P₁_eq] at hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h1 : fr.t * fr.s₁ ^ k * fr.t⁻¹ = (fr.s₁ ^ k)⁻¹ := by
    rw [← conj_zpow, h.t_conj_s₁, inv_zpow]
  have h2 : fr.t * fr.s₁ ^ k * fr.t⁻¹ = fr.s₁ ^ k := by
    rw [← hxt, mul_inv_cancel_right]
  rw [h2] at h1
  have h3 : (fr.s₁ ^ k) ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [h1]
    exact mul_inv_cancel _
  calc fr.s₁ ^ k = (fr.s₁ ^ k) ^ 3 * ((fr.s₁ ^ k) ^ 2)⁻¹ := by group
    _ = 1 := by rw [hx3, h3, inv_one, mul_one]

end Hyp

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTwelve

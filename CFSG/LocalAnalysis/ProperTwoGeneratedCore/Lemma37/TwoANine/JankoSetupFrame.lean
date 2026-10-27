module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoSetupSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoStatements

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Subgroup CFSG.Semidihedral.Principal.PrimewiseScalar

namespace JankoFrame

variable {G : Type} [Group G] {z : G} (fr : JankoFrame G z)

theorem centralizer_P₁_eq : centralizer (fr.P₁ : Set G) = centralizer ({fr.s₁} : Set G) := by
  rw [fr.P₁_eq, centralizer_zpowers_eq_centralizer]

theorem centralizer_P₂_eq : centralizer (fr.P₂ : Set G) = centralizer ({fr.s₂} : Set G) := by
  rw [fr.P₂_eq, centralizer_zpowers_eq_centralizer]

theorem centralizer_P₃_eq : centralizer (fr.P₃ : Set G) = centralizer ({fr.s₃} : Set G) := by
  rw [fr.P₃_eq, centralizer_zpowers_eq_centralizer]

theorem s₁_mem_E : fr.s₁ ∈ fr.E := by
  rw [fr.E_eq_closure]
  exact subset_closure (by simp)

theorem s₂_mem_E : fr.s₂ ∈ fr.E := by
  rw [fr.E_eq_closure]
  exact subset_closure (by simp)

theorem P₁_le_E : fr.P₁ ≤ fr.E := by
  rw [fr.P₁_eq, zpowers_le]
  exact fr.s₁_mem_E

theorem P₂_le_E : fr.P₂ ≤ fr.E := by
  rw [fr.P₂_eq, zpowers_le]
  exact fr.s₂_mem_E

theorem card_P₂ : Nat.card fr.P₂ = 3 := by
  rw [fr.P₂_eq, Nat.card_zpowers, fr.orderOf_s₂]

theorem t_mem_centralizer_P₂ : fr.t ∈ centralizer (fr.P₂ : Set G) := by
  rw [mem_centralizer_iff]
  intro y hy
  have hy' : y ∈ fr.F ⊓ centralizer ({fr.t} : Set G) := fr.F₁_eq ▸ fr.P₂_le_F₁ hy
  exact mem_centralizer_singleton_iff.mp hy'.2

theorem s₂_mem_centralizer_t : fr.s₂ ∈ centralizer ({fr.t} : Set G) :=
  mem_centralizer_singleton_iff.mpr
    (mem_centralizer_iff.mp fr.t_mem_centralizer_P₂ _ (fr.P₂_eq ▸ mem_zpowers _))

theorem s₂_pow_three : fr.s₂ ^ 3 = 1 := by
  rw [← fr.orderOf_s₂]
  exact pow_orderOf_eq_one _

theorem t_mul_z : fr.t * z = z * fr.t :=
  mem_centralizer_singleton_iff.mp fr.t_mem

theorem t_mem_L : fr.t ∈ fr.L := by
  rw [fr.L_eq]
  exact subset_closure (by simp)

theorem t_mem_normalizer_E : fr.t ∈ normalizer (fr.E : Set G) :=
  fr.K_le_normalizer (fr.L_le_K fr.t_mem_L)

theorem card_S₁ : Nat.card fr.S₁ = 16 := by
  obtain ⟨e⟩ := fr.S₁_quaternion
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem z_mem_S₁ : z ∈ fr.S₁ := by
  have : Finite fr.S₁ := Nat.finite_of_card_ne_zero (by rw [fr.card_S₁]; norm_num)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := fr.S₁) 2 (by rw [fr.card_S₁]; norm_num)
  exact Eq.subst (motive := fun w => w ∈ fr.S₁)
    (fr.eq_z_of_mem_F x (fr.S₁_le x.2) (by rw [Subgroup.orderOf_coe, hx])) x.2

theorem normalizer_S₁_le (hz : orderOf z = 2) :
    normalizer (fr.S₁ : Set G) ≤ centralizer ({z} : Set G) :=
  normalizer_le_centralizer_of_involution fr.z_mem_S₁ hz fun x hx hx2 =>
    fr.eq_z_of_mem_F x (fr.S₁_le hx) hx2

theorem D_le : fr.D ≤ centralizer ({z} : Set G) := by
  rw [fr.D_eq, closure_le]
  rintro x (rfl | rfl)
  · exact fr.t_mem
  · exact pow_mem (fr.F_le fr.ℓ_mem_F) 2

theorem z_mem_D : z ∈ fr.D := by
  have h : fr.ℓ ^ 2 ∈ fr.D := by
    rw [fr.D_eq]
    exact subset_closure (by simp)
  have h4 : (fr.ℓ ^ 2) ^ 2 = z := by rw [← pow_mul]; exact fr.ℓ_pow_four
  exact Eq.subst (motive := fun w => w ∈ fr.D) h4 (pow_mem h 2)

theorem normalizer_D_le (hz : orderOf z = 2) :
    normalizer (fr.D : Set G) ≤ centralizer ({z} : Set G) :=
  normalizer_le_centralizer_of_center fr.z_mem_D (ne_one_of_orderOf_eq_two hz)
    (fun _ hy => (mem_centralizer_singleton_iff.mp (fr.D_le hy)).symm) fr.D_center

theorem isKleinFour_V (hz : orderOf z = 2) : IsKleinFour fr.V := by
  have ht := mul_self_eq_one_of_orderOf_eq_two fr.orderOf_t
  have hz' := mul_self_eq_one_of_orderOf_eq_two hz
  have hc : Commute fr.t z := fr.t_mul_z
  have htV : fr.t ∈ fr.V := by
    rw [fr.V_eq]
    exact subset_closure (by simp)
  have hzV : z ∈ fr.V := by
    rw [fr.V_eq]
    exact subset_closure (by simp)
  have heq : fr.V = GorensteinWalter.kleinFourOfCommutingInvolutions fr.t z ht hz' hc := by
    apply le_antisymm
    · rw [fr.V_eq, closure_le]
      intro x hx
      change x ∈ ({fr.t * z, fr.t, z, 1} : Set G)
      rcases hx with hx | hx
      · simp [hx]
      · simp [Set.mem_singleton_iff.mp hx]
    · intro x hx
      change x ∈ ({fr.t * z, fr.t, z, 1} : Set G) at hx
      rcases hx with hx | hx | hx | hx <;> rw [hx]
      · exact mul_mem htV hzV
      · exact htV
      · exact hzV
      · exact one_mem _
  rw [heq]
  exact GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions _ _ ht hz'
    (ne_one_of_orderOf_eq_two fr.orderOf_t) (ne_one_of_orderOf_eq_two hz) fr.t_ne hc

theorem card_V (hz : orderOf z = 2) : Nat.card fr.V = 4 :=
  (fr.isKleinFour_V hz).card_four

theorem isPGroup_V (hz : orderOf z = 2) : IsPGroup 2 fr.V :=
  IsPGroup.of_card (n := 2) (by rw [fr.card_V hz]; norm_num)

end JankoFrame

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropElevenA
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoStatementsSteps

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoEleven

open Subgroup CFSG.Semidihedral.Principal.PrimewiseScalar

variable {G : Type} [Group G] {z : G} {fr : JankoFrame G z}

theorem s₁_mem_E : fr.s₁ ∈ fr.E := by
  rw [fr.E_eq_closure]
  exact subset_closure (Set.mem_insert _ _)

theorem s₂_mem_E : fr.s₂ ∈ fr.E := by
  rw [fr.E_eq_closure]
  exact subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

theorem conj_s₂_mem_E : fr.ℓ * fr.s₂ * fr.ℓ⁻¹ ∈ fr.E := by
  rw [fr.E_eq_closure]
  exact subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))

theorem P₁_le_E : fr.P₁ ≤ fr.E := fr.P₁_eq ▸ zpowers_le.mpr s₁_mem_E

theorem P₂_le_E : fr.P₂ ≤ fr.E := fr.P₂_eq ▸ zpowers_le.mpr s₂_mem_E

theorem ℓ_mem_L : fr.ℓ ∈ fr.L := by
  rw [fr.L_eq]
  exact subset_closure (Set.mem_insert _ _)

theorem t_mem_L : fr.t ∈ fr.L := by
  rw [fr.L_eq]
  exact subset_closure (Set.mem_insert_of_mem _ rfl)

theorem centralizer_P₁_eq : centralizer (fr.P₁ : Set G) = centralizer ({fr.s₁} : Set G) := by
  rw [fr.P₁_eq, zpowers_eq_closure, centralizer_closure]

theorem centralizer_P₂_eq : centralizer (fr.P₂ : Set G) = centralizer ({fr.s₂} : Set G) := by
  rw [fr.P₂_eq, zpowers_eq_closure, centralizer_closure]

theorem card_P₁ : Nat.card fr.P₁ = 3 := by
  rw [fr.P₁_eq, Nat.card_zpowers, fr.orderOf_s₁]

theorem t_mul_t : fr.t * fr.t = 1 := by
  rw [← pow_two, ← fr.orderOf_t, pow_orderOf_eq_one]

theorem z_mul_z (hz : orderOf z = 2) : z * z = 1 := by
  rw [← pow_two, ← hz, pow_orderOf_eq_one]

theorem t_comm_z : fr.t * z = z * fr.t := mem_centralizer_singleton_iff.mp fr.t_mem

theorem t_conj_ℓ_sq : fr.t * fr.ℓ ^ 2 * fr.t⁻¹ = z * fr.ℓ ^ 2 := by
  have h : fr.t * fr.ℓ ^ 2 * fr.t⁻¹ = (fr.t * fr.ℓ * fr.t⁻¹) ^ 2 := by
    rw [pow_two, pow_two]; group
  have h6 : fr.ℓ ^ (3 * 2) = fr.ℓ ^ 4 * fr.ℓ ^ 2 := by rw [← pow_add]
  rw [h, fr.t_mul_ℓ, ← pow_mul, h6, fr.ℓ_pow_four]

theorem ℓ_sq_conj_t (hz : orderOf z = 2) : fr.ℓ ^ 2 * fr.t * (fr.ℓ ^ 2)⁻¹ = fr.t * z := by
  have h1 : fr.ℓ ^ 2 = fr.t⁻¹ * (z * fr.ℓ ^ 2) * fr.t := by
    rw [← t_conj_ℓ_sq]; group
  have hz' : z⁻¹ = z := (eq_inv_of_mul_eq_one_left (z_mul_z hz)).symm
  calc fr.ℓ ^ 2 * fr.t * (fr.ℓ ^ 2)⁻¹ = fr.ℓ ^ 2 * fr.t * (fr.t⁻¹ * (z * fr.ℓ ^ 2) * fr.t)⁻¹ := by
        nth_rewrite 2 [h1]; rfl
    _ = z⁻¹ * fr.t := by group
    _ = fr.t * z := by rw [hz', t_comm_z]

theorem t_not_mem_centralizer_P₁ : fr.t ∉ centralizer (fr.P₁ : Set G) := by
  intro h
  rw [centralizer_P₁_eq, mem_centralizer_singleton_iff] at h
  have h1 : fr.s₁⁻¹ = fr.s₁ := by rw [← fr.t_mul_s₁, h, mul_inv_cancel_right]
  have h2 : fr.s₁ ^ 2 = 1 := by rw [pow_two]; nth_rewrite 1 [← h1]; exact inv_mul_cancel _
  have h3 := orderOf_dvd_of_pow_eq_one h2
  rw [fr.orderOf_s₁] at h3
  norm_num at h3

theorem E_le_centralizer_P₁ : fr.E ≤ centralizer (fr.P₁ : Set G) := fun e he => by
  rw [centralizer_P₁_eq, mem_centralizer_singleton_iff]
  exact fr.E_comm e he _ s₁_mem_E

theorem z_mem_centralizer_P₁ : z ∈ centralizer (fr.P₁ : Set G) :=
  fr.F_le_centralizer fr.z_mem_F

theorem ℓ_mem_centralizer_P₁ : fr.ℓ ∈ centralizer (fr.P₁ : Set G) :=
  fr.F_le_centralizer fr.ℓ_mem_F

theorem M_le_centralizer_P₁ : fr.M ≤ centralizer (fr.P₁ : Set G) := oddCoreOf_le _

theorem centralizer_P₁_le_normalizer_M :
    centralizer (fr.P₁ : Set G) ≤ normalizer (fr.M : Set G) := le_normalizer_oddCoreOf _

theorem t_mem_normalizer_P₁ (p7 : JankoProp7 fr) : fr.t ∈ normalizer (fr.P₁ : Set G) := by
  rw [p7.normalizer_P₁]
  exact mem_sup_right (mem_zpowers _)

theorem centralizer_P₁_le_normalizer_P₁ :
    centralizer (fr.P₁ : Set G) ≤ normalizer (fr.P₁ : Set G) :=
  centralizer_le_normalizer _

theorem normalizer_P₁_le_normalizer_M [Finite G] :
    normalizer (fr.P₁ : Set G) ≤ normalizer (fr.M : Set G) := fun _ hg =>
  mem_normalizer_oddCoreOf (mem_normalizer_centralizer hg)

theorem E_inf_M (p10 : JankoProp10 fr) : fr.E ⊓ fr.M = fr.P₁ := by
  refine le_antisymm (fun x hx => ?_) (le_inf P₁_le_E p10.P₁_le_M)
  rw [← p10.M_inf_centralizer_z]
  exact ⟨hx.2, fr.E_le hx.1⟩

theorem E_le_normalizer_M : fr.E ≤ normalizer (fr.M : Set G) :=
  E_le_centralizer_P₁.trans centralizer_P₁_le_normalizer_M

theorem exists_mul_of_mem_N {x : G} (hx : x ∈ fr.N) : ∃ e ∈ fr.E, ∃ m ∈ fr.M, e * m = x :=
  exists_mul_of_mem_sup E_le_normalizer_M hx

theorem E_le_N : fr.E ≤ fr.N := le_sup_left

theorem M_le_N : fr.M ≤ fr.N := le_sup_right

theorem N_le_centralizer_P₁ : fr.N ≤ centralizer (fr.P₁ : Set G) :=
  sup_le E_le_centralizer_P₁ M_le_centralizer_P₁

theorem card_N (p10 : JankoProp10 fr) : Nat.card fr.N = 3 ^ 7 := by
  have h := card_sup_mul_card_inf (E_le_normalizer_M (fr := fr))
  rw [E_inf_M p10, card_P₁, fr.card_E, p10.card_M] at h
  change Nat.card fr.N * 3 = 27 * 3 ^ 5 at h
  omega

theorem isPGroup_N (p10 : JankoProp10 fr) : IsPGroup 3 fr.N :=
  IsPGroup.of_card (card_N p10)

theorem L_le_normalizer_E : fr.L ≤ normalizer (fr.E : Set G) :=
  fun _ hl => fr.K_le_normalizer (fr.L_le_K hl)

theorem z_mem_centralizer_E : z ∈ centralizer (fr.E : Set G) :=
  Subgroup.mem_centralizer_iff.mpr fun _ he => mem_centralizer_singleton_iff.mp (fr.E_le he)

theorem z_mem_normalizer_E : z ∈ normalizer (fr.E : Set G) :=
  centralizer_le_normalizer _ z_mem_centralizer_E

theorem t_mem_normalizer_E : fr.t ∈ normalizer (fr.E : Set G) := L_le_normalizer_E t_mem_L

theorem ℓ_mem_normalizer_E : fr.ℓ ∈ normalizer (fr.E : Set G) := L_le_normalizer_E ℓ_mem_L

theorem t_mem_normalizer_M [Finite G] (p7 : JankoProp7 fr) : fr.t ∈ normalizer (fr.M : Set G) :=
  normalizer_P₁_le_normalizer_M (t_mem_normalizer_P₁ p7)

theorem z_mem_normalizer_M : z ∈ normalizer (fr.M : Set G) :=
  centralizer_P₁_le_normalizer_M z_mem_centralizer_P₁

theorem ℓ_mem_normalizer_M : fr.ℓ ∈ normalizer (fr.M : Set G) :=
  centralizer_P₁_le_normalizer_M ℓ_mem_centralizer_P₁

theorem mem_normalizer_N {g : G} (hE : g ∈ normalizer (fr.E : Set G))
    (hM : g ∈ normalizer (fr.M : Set G)) : g ∈ normalizer (fr.N : Set G) :=
  mem_normalizer_sup hE hM

theorem t_mem_normalizer_N [Finite G] (p7 : JankoProp7 fr) : fr.t ∈ normalizer (fr.N : Set G) :=
  mem_normalizer_N t_mem_normalizer_E (t_mem_normalizer_M p7)

theorem z_mem_normalizer_N : z ∈ normalizer (fr.N : Set G) :=
  mem_normalizer_N z_mem_normalizer_E z_mem_normalizer_M

theorem ℓ_mem_normalizer_N : fr.ℓ ∈ normalizer (fr.N : Set G) :=
  mem_normalizer_N ℓ_mem_normalizer_E ℓ_mem_normalizer_M

theorem L_le_normalizer_N [Finite G] (p7 : JankoProp7 fr) : fr.L ≤ normalizer (fr.N : Set G) := by
  rw [fr.L_eq, closure_le]
  rintro _ (rfl | rfl)
  · exact ℓ_mem_normalizer_N
  · exact t_mem_normalizer_N p7

theorem L_le_normalizer_P₁ (p7 : JankoProp7 fr) : fr.L ≤ normalizer (fr.P₁ : Set G) := by
  rw [fr.L_eq, closure_le]
  rintro _ (rfl | rfl)
  · exact centralizer_P₁_le_normalizer_P₁ ℓ_mem_centralizer_P₁
  · exact t_mem_normalizer_P₁ p7

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoEleven

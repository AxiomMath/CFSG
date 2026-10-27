module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3G2Para
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import CFSG.LieType.Chevalley.OddF4G2AutomorphismNormalForm
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
import CFSG.GroupTheory.ElemAbelianClosure

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open scoped commutatorElement

abbrev rootA : Fin Tag.G2.rank → ℤ := g2r

abbrev rootB : Fin Tag.G2.rank → ℤ := g2a

abbrev rootAB : Fin Tag.G2.rank → ℤ := g2u

abbrev root2AB : Fin Tag.G2.rank → ℤ := g2v

abbrev root3AB : Fin Tag.G2.rank → ℤ := g2b

abbrev root3A2B : Fin Tag.G2.rank → ℤ := g2c

theorem le_normalizer_of_conj_mem {G : Type*} [Group G] {S H : Subgroup G}
    (h : ∀ s ∈ S, ∀ x ∈ H, s * x * s⁻¹ ∈ H) : S ≤ normalizer (H : Set G) := by
  intro s hs
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h s hs x, fun hx => ?_⟩
  have := h s⁻¹ (inv_mem hs) _ hx
  rwa [show s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x by group] at this

theorem isElementaryAbelian_of_forall {G : Type*} [Group G] {H : Subgroup G}
    (hcomm : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (hsq : ∀ x ∈ H, x * x = 1) :
    CFSG.IsElementaryAbelian 2 H := CFSG.IsElementaryAbelian.two_of_forall_mul_self hcomm hsq

theorem card_eq_of_param {G K : Type*} [Group G] [Finite K] {H : Subgroup G} {n : ℕ}
    (φ : (Fin n → K) → G) (hφ : Function.Injective φ)
    (hH : ∀ g, g ∈ H ↔ ∃ v, φ v = g) : Nat.card H = Nat.card K ^ n := by
  have hrange : Set.range φ = (H : Set G) := by
    ext g
    rw [SetLike.mem_coe, hH, Set.mem_range]
  rw [← SetLike.coe_sort_coe, ← hrange, Nat.card_range_of_injective hφ, Nat.card_fun,
    Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]

section Calculus


variable {K : Type} [Field K] [CharP K 2]

theorem g2N_mul_coords (A B C D E F a b c d e f : K) :
    g2N A B C D E F * g2N a b c d e f =
      g2N (A + a) (B + b) (C + c + B * a) (D + d + B * a ^ 2)
        (E + e + B * a ^ 3 + C * a ^ 2 + D * a)
        (F + f + B ^ 2 * a ^ 3 + B * C * a ^ 2 + C ^ 2 * a +
          b * (E + B * a ^ 3 + C * a ^ 2 + D * a) + c * (D + B * a ^ 2)) := by
  rw [mul_g2N, g2N_mul_r, g2N_mul_a, g2N_mul_u, g2N_mul_v, g2N_mul_b, g2N_mul_c]
  refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

theorem g2N_inv_coords (A B C D E F : K) :
    (g2N A B C D E F)⁻¹ =
      g2N A B (C + A * B) (D + A ^ 2 * B) (E + A ^ 3 * B + A ^ 2 * C + A * D)
        (F + A * C ^ 2 + B * E + C * D + A ^ 2 * B * C + A ^ 3 * B ^ 2) := by
  rw [inv_eq_iff_mul_eq_one, g2N_mul_coords, ← g2N_zero]
  refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> char2_ring

theorem g2N_conj_coords (A B C D E F a b c d e f : K) :
    g2N A B C D E F * g2N a b c d e f * (g2N A B C D E F)⁻¹ =
      g2N a b (A * b + B * a + c) (A ^ 2 * b + B * a ^ 2 + d)
        (A ^ 3 * b + A ^ 2 * B * a + A ^ 2 * c + A * B * a ^ 2 + A * d + B * a ^ 3 + C * a ^ 2 +
          D * a + e)
        (A ^ 3 * b ^ 2 + A ^ 2 * B * a * b + A ^ 2 * b * c + A * B ^ 2 * a ^ 2 + A * c ^ 2 +
          B * C * a ^ 2 + B * D * a + B * a ^ 3 * b + B * a ^ 2 * c + B * e + C ^ 2 * a +
          C * a ^ 2 * b + C * d + D * a * b + D * c + E * b + f) := by
  rw [g2N_inv_coords, g2N_mul_coords, g2N_mul_coords]
  refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> char2_ring

theorem g2N_commutator_coords (A B C D E F a b c d e f : K) :
    ⁅g2N A B C D E F, g2N a b c d e f⁆ =
      g2N 0 0 (A * b + B * a) (A ^ 2 * b + B * a ^ 2)
        (A ^ 3 * b + A ^ 2 * B * a + A ^ 2 * a * b + A ^ 2 * c + A * B * a ^ 2 + A * a ^ 2 * b +
          A * d + B * a ^ 3 + C * a ^ 2 + D * a)
        (A ^ 2 * a * b ^ 2 + A ^ 2 * b * c + A * B ^ 2 * a ^ 2 + A * B * a ^ 2 * b + A * b * d +
          A * c ^ 2 + B ^ 2 * a ^ 3 + B * C * a ^ 2 + B * D * a + B * e + C ^ 2 * a + C * d +
          D * c + E * b) := by
  rw [commutatorElement_def, g2N_inv_coords, g2N_inv_coords, g2N_mul_coords, g2N_mul_coords,
    g2N_mul_coords]
  refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> char2_ring

end Calculus

namespace Model

section Basic

variable (K : Type) [Field K]

abbrev S : Subgroup (ModGL .G2 K) := posUnipotent .G2 K

abbrev U : Subgroup (ModGL .G2 K) := rootSubgroup .G2 K g2c

abbrev J : Subgroup (ModGL .G2 K) := torusGroup .G2 K

@[expose] def torusFix (s : Fin Tag.G2.rank → ℤ) : Subgroup (ModGL .G2 K) :=
  torusGroup .G2 K ⊓ centralizer (rootSubgroup .G2 K s : Set (ModGL .G2 K))

abbrev J₁ : Subgroup (ModGL .G2 K) := torusFix K g2c

abbrev J₂ : Subgroup (ModGL .G2 K) := torusFix K g2v

abbrev J₃ : Subgroup (ModGL .G2 K) := torusFix K g2r

abbrev J₄ : Subgroup (ModGL .G2 K) := torusFix K g2a

abbrev J₅ : Subgroup (ModGL .G2 K) := torusFix K g2b

abbrev J₆ : Subgroup (ModGL .G2 K) := torusFix K g2u

abbrev leviA : Subgroup (ModGL .G2 K) := g2RankOne K g2ir

abbrev leviB : Subgroup (ModGL .G2 K) := g2RankOne K g2ia

@[expose] def wa : ModGL .G2 K := weylElt .G2 K g2ir 1

@[expose] def wb : ModGL .G2 K := weylElt .G2 K g2ia 1

theorem wa_mem_adjointGroup : wa K ∈ adjointGroup .G2 K := weylElt_mem_adjointGroup _ _

theorem wb_mem_adjointGroup : wb K ∈ adjointGroup .G2 K := weylElt_mem_adjointGroup _ _

theorem S_le_adjointGroup : S K ≤ adjointGroup .G2 K := posUnipotent_le_adjointGroup

theorem U_le_adjointGroup : U K ≤ adjointGroup .G2 K := rootSubgroup_le_adjointGroup _

theorem leviA_le_adjointGroup : leviA K ≤ adjointGroup .G2 K := g2RankOne_le_adjointGroup _

theorem leviB_le_adjointGroup : leviB K ≤ adjointGroup .G2 K := g2RankOne_le_adjointGroup _

theorem J_le_adjointGroup : J K ≤ adjointGroup .G2 K :=
  (closure_le _).2 (Set.range_subset_iff.2 fun p => torusElt_mem_adjointGroup p.1 p.2)

theorem torusFix_le_adjointGroup (s : Fin Tag.G2.rank → ℤ) :
    torusFix K s ≤ adjointGroup .G2 K :=
  inf_le_left.trans (J_le_adjointGroup K)

end Basic

section Radicals


variable (K : Type) [Field K] [CharP K 2]

abbrev Y : Subgroup (ModGL .G2 K) := g2BCGroup K

@[expose] def X : Subgroup (ModGL .G2 K) where
  carrier := {g | ∃ c e f : K, g = g2N 0 0 c 0 e f}
  mul_mem' := by
    rintro _ _ ⟨c, e, f, rfl⟩ ⟨c', e', f', rfl⟩
    exact ⟨c + c', e + e', f + f', by
      rw [g2N_mul_coords]; refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring⟩
  one_mem' := ⟨0, 0, 0, g2N_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨c, e, f, rfl⟩
    exact ⟨c, e, f, by rw [g2N_inv_coords]; refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring⟩

abbrev W : Subgroup (ModGL .G2 K) := g2ShortRadical K

@[expose] def F : Subgroup (ModGL .G2 K) where
  carrier := {g | ∃ c d e f : K, g = g2N 0 0 c d e f}
  mul_mem' := by
    rintro _ _ ⟨c, d, e, f, rfl⟩ ⟨c', d', e', f', rfl⟩
    exact ⟨c + c', d + d', e + e', f + f' + c' * d, by
      rw [g2N_mul_coords]; refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring⟩
  one_mem' := ⟨0, 0, 0, 0, g2N_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨c, d, e, f, rfl⟩
    exact ⟨c, d, e, f + c * d, by
      rw [g2N_inv_coords]; refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring⟩

abbrev D : Subgroup (ModGL .G2 K) := g2LongRadical K

abbrev M : Subgroup (ModGL .G2 K) := g2ShortParabolicRadical K

end Radicals

@[expose] def fieldAut
    (K : Type) [Field K] [Finite K]
    [CharP K 2] : MulAut (adjointGroup .G2 K) :=
  exactNormalAut .G2 K 1 (frobeniusEquiv K 2) 0

section Facts


variable {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem mem_S {g : ModGL .G2 K} : g ∈ S K ↔ ∃ A B C D E F : K, g = g2N A B C D E F := by
  constructor
  · intro hg
    obtain ⟨A, B, C, D, E, F, h⟩ := exists_g2N_of_mem_posUnipotent hg
    exact ⟨A, B, C, D, E, F, h.symm⟩
  · rintro ⟨A, B, C, D, E, F, rfl⟩
    exact g2N_mem_posUnipotent A B C D E F

omit
  [CharP K 2] in
theorem mem_U {g : ModGL .G2 K} : g ∈ U K ↔ ∃ F : K, g = g2N 0 0 0 0 0 F := by
  rw [mem_rootSubgroup]
  constructor
  · rintro ⟨F, rfl⟩
    exact ⟨F, pinnedX_c_eq_g2N F⟩
  · rintro ⟨F, rfl⟩
    exact ⟨F, pinnedX_c_eq_g2N F⟩

theorem mem_Y {g : ModGL .G2 K} : g ∈ Y K ↔ ∃ E F : K, g = g2N 0 0 0 0 E F := Iff.rfl

theorem mem_X {g : ModGL .G2 K} : g ∈ X K ↔ ∃ C E F : K, g = g2N 0 0 C 0 E F := Iff.rfl

theorem mem_W {g : ModGL .G2 K} : g ∈ W K ↔ ∃ D E F : K, g = g2N 0 0 0 D E F := Iff.rfl

theorem mem_F {g : ModGL .G2 K} : g ∈ F K ↔ ∃ C D E F : K, g = g2N 0 0 C D E F := Iff.rfl

theorem mem_D {g : ModGL .G2 K} : g ∈ D K ↔ ∃ B C D E F : K, g = g2N 0 B C D E F := Iff.rfl

theorem mem_M {g : ModGL .G2 K} : g ∈ M K ↔ ∃ A C D E F : K, g = g2N A 0 C D E F := Iff.rfl

omit
  [CharP K 2] in
theorem g2N_mem_U_iff {A B C D E F : K} :
    g2N A B C D E F ∈ U K ↔ A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 ∧ E = 0 := by
  rw [mem_U]
  constructor
  · rintro ⟨F', h⟩
    obtain ⟨h1, h2, h3, h4, h5, -⟩ := g2N_injective h
    exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
    exact ⟨F, rfl⟩

theorem g2N_mem_Y_iff {A B C D E F : K} :
    g2N A B C D E F ∈ Y K ↔ A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 := by
  rw [mem_Y]
  constructor
  · rintro ⟨E', F', h⟩
    obtain ⟨h1, h2, h3, h4, -, -⟩ := g2N_injective h
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨E, F, rfl⟩

theorem g2N_mem_X_iff {A B C D E F : K} :
    g2N A B C D E F ∈ X K ↔ A = 0 ∧ B = 0 ∧ D = 0 := by
  rw [mem_X]
  constructor
  · rintro ⟨C', E', F', h⟩
    obtain ⟨h1, h2, -, h4, -, -⟩ := g2N_injective h
    exact ⟨h1, h2, h4⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨C, E, F, rfl⟩

theorem g2N_mem_W_iff {A B C D E F : K} :
    g2N A B C D E F ∈ W K ↔ A = 0 ∧ B = 0 ∧ C = 0 := by
  rw [mem_W]
  constructor
  · rintro ⟨D', E', F', h⟩
    obtain ⟨h1, h2, h3, -, -, -⟩ := g2N_injective h
    exact ⟨h1, h2, h3⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨D, E, F, rfl⟩

theorem g2N_mem_F_iff {A B C D E F : K} : g2N A B C D E F ∈ Model.F K ↔ A = 0 ∧ B = 0 := by
  rw [mem_F]
  constructor
  · rintro ⟨C', D', E', F', h⟩
    obtain ⟨h1, h2, -, -, -, -⟩ := g2N_injective h
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨C, D, E, F, rfl⟩

theorem g2N_mem_D_iff {A B C D E F : K} : g2N A B C D E F ∈ Model.D K ↔ A = 0 := by
  rw [mem_D]
  constructor
  · rintro ⟨B', C', D', E', F', h⟩
    exact (g2N_injective h).1
  · rintro rfl
    exact ⟨B, C, D, E, F, rfl⟩

theorem g2N_mem_M_iff {A B C D E F : K} : g2N A B C D E F ∈ M K ↔ B = 0 := by
  rw [mem_M]
  constructor
  · rintro ⟨A', C', D', E', F', h⟩
    exact (g2N_injective h).2.1
  · rintro rfl
    exact ⟨A, C, D, E, F, rfl⟩

theorem U_le_Y : U K ≤ Y K := by
  intro g hg
  obtain ⟨F, rfl⟩ := mem_U.1 hg
  exact g2N_mem_Y_iff.2 ⟨rfl, rfl, rfl, rfl⟩

theorem Y_le_X : Y K ≤ X K := by
  rintro _ ⟨E, F, rfl⟩
  exact g2N_mem_X_iff.2 ⟨rfl, rfl, rfl⟩

theorem Y_le_W : Y K ≤ W K := by
  rintro _ ⟨E, F, rfl⟩
  exact g2N_mem_W_iff.2 ⟨rfl, rfl, rfl⟩

theorem X_le_F : X K ≤ Model.F K := by
  rintro _ ⟨C, E, F, rfl⟩
  exact g2N_mem_F_iff.2 ⟨rfl, rfl⟩

theorem W_le_F : W K ≤ Model.F K := by
  rintro _ ⟨D, E, F, rfl⟩
  exact g2N_mem_F_iff.2 ⟨rfl, rfl⟩

theorem F_le_D : Model.F K ≤ Model.D K := by
  rintro _ ⟨C, D, E, F, rfl⟩
  exact g2N_mem_D_iff.2 rfl

theorem F_le_M : Model.F K ≤ M K := by
  rintro _ ⟨C, D, E, F, rfl⟩
  exact g2N_mem_M_iff.2 rfl

theorem D_le_S : Model.D K ≤ S K := g2LongRadical_le_posUnipotent

theorem M_le_S : M K ≤ S K := by
  rintro _ ⟨A, C, D, E, F, rfl⟩
  exact g2N_mem_posUnipotent _ _ _ _ _ _

theorem F_le_S : Model.F K ≤ S K := (F_le_D (K := K)).trans D_le_S

theorem U_le_S : U K ≤ S K :=
  (U_le_Y (K := K)).trans ((Y_le_X (K := K)).trans ((X_le_F (K := K)).trans F_le_S))

theorem Y_le_S : Y K ≤ S K := (Y_le_X (K := K)).trans ((X_le_F (K := K)).trans F_le_S)

theorem X_le_S : X K ≤ S K := (X_le_F (K := K)).trans F_le_S

theorem W_le_S : W K ≤ S K := (W_le_F (K := K)).trans F_le_S

theorem X_inf_W : X K ⊓ W K = Y K := by
  refine le_antisymm ?_ (le_inf Y_le_X Y_le_W)
  rintro _ ⟨⟨C, E, F, rfl⟩, hW⟩
  obtain ⟨-, -, rfl⟩ := g2N_mem_W_iff.1 hW
  exact g2N_mem_Y_iff.2 ⟨rfl, rfl, rfl, rfl⟩

theorem D_inf_M : Model.D K ⊓ M K = Model.F K := by
  refine le_antisymm ?_ (le_inf F_le_D F_le_M)
  rintro _ ⟨⟨B, C, D, E, F, rfl⟩, hM⟩
  obtain rfl := g2N_mem_M_iff.1 hM
  exact g2N_mem_F_iff.2 ⟨rfl, rfl⟩

theorem X_sup_W : X K ⊔ W K = Model.F K := by
  refine le_antisymm (sup_le X_le_F W_le_F) ?_
  rintro _ ⟨C, D, E, F, rfl⟩
  have h : g2N (0 : K) 0 C D E F = g2N 0 0 C 0 0 0 * g2N 0 0 0 D E F := by
    rw [g2N_mul_coords]
    refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  rw [h]
  exact mul_mem (mem_sup_left (g2N_mem_X_iff.2 ⟨rfl, rfl, rfl⟩))
    (mem_sup_right (g2N_mem_W_iff.2 ⟨rfl, rfl, rfl⟩))

theorem D_sup_M : Model.D K ⊔ M K = S K := by
  refine le_antisymm (sup_le D_le_S M_le_S) fun g hg => ?_
  obtain ⟨A, B, C, D, E, F, rfl⟩ := mem_S.1 hg
  have h : g2N A B C D E F = g2N A 0 0 0 0 0 * g2N 0 B C D E F := by
    rw [g2N_mul_coords]
    refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  rw [h]
  exact mul_mem (mem_sup_right (g2N_mem_M_iff.2 rfl)) (mem_sup_left (g2N_mem_D_iff.2 rfl))

theorem rootSubgroup_b_sup_U : rootSubgroup .G2 K g2b ⊔ U K = Y K := by
  refine le_antisymm (sup_le ?_ U_le_Y) ?_
  · intro g hg
    obtain ⟨E, rfl⟩ := mem_rootSubgroup.1 hg
    rw [pinnedX_b_eq_g2N]
    exact g2N_mem_Y_iff.2 ⟨rfl, rfl, rfl, rfl⟩
  · rintro _ ⟨E, F, rfl⟩
    have h : g2N (0 : K) 0 0 0 E F = g2N 0 0 0 0 E 0 * g2N 0 0 0 0 0 F := by
      rw [g2N_mul_coords]
      refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
    rw [h]
    exact mul_mem (mem_sup_left (mem_rootSubgroup.2 ⟨E, pinnedX_b_eq_g2N E⟩))
      (mem_sup_right (mem_U.2 ⟨F, rfl⟩))

theorem rootSubgroup_u_sup_Y : rootSubgroup .G2 K g2u ⊔ Y K = X K := by
  refine le_antisymm (sup_le ?_ Y_le_X) ?_
  · intro g hg
    obtain ⟨C, rfl⟩ := mem_rootSubgroup.1 hg
    rw [pinnedX_u_eq_g2N]
    exact g2N_mem_X_iff.2 ⟨rfl, rfl, rfl⟩
  · rintro _ ⟨C, E, F, rfl⟩
    have h : g2N (0 : K) 0 C 0 E F = g2N 0 0 C 0 0 0 * g2N 0 0 0 0 E F := by
      rw [g2N_mul_coords]
      refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
    rw [h]
    exact mul_mem (mem_sup_left (mem_rootSubgroup.2 ⟨C, pinnedX_u_eq_g2N C⟩))
      (mem_sup_right ⟨E, F, rfl⟩)

theorem rootSubgroup_v_sup_Y : rootSubgroup .G2 K g2v ⊔ Y K = W K := by
  refine le_antisymm (sup_le ?_ Y_le_W) ?_
  · intro g hg
    obtain ⟨D, rfl⟩ := mem_rootSubgroup.1 hg
    rw [pinnedX_v_eq_g2N]
    exact g2N_mem_W_iff.2 ⟨rfl, rfl, rfl⟩
  · rintro _ ⟨D, E, F, rfl⟩
    have h : g2N (0 : K) 0 0 D E F = g2N 0 0 0 D 0 0 * g2N 0 0 0 0 E F := by
      rw [g2N_mul_coords]
      refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
    rw [h]
    exact mul_mem (mem_sup_left (mem_rootSubgroup.2 ⟨D, pinnedX_v_eq_g2N D⟩))
      (mem_sup_right ⟨E, F, rfl⟩)

theorem rootSubgroup_a_sup_F : rootSubgroup .G2 K g2a ⊔ Model.F K = Model.D K := by
  refine le_antisymm (sup_le ?_ F_le_D) ?_
  · intro g hg
    obtain ⟨B, rfl⟩ := mem_rootSubgroup.1 hg
    rw [pinnedX_a_eq_g2N]
    exact g2N_mem_D_iff.2 rfl
  · rintro _ ⟨B, C, D, E, F, rfl⟩
    have h : g2N (0 : K) B C D E F = g2N 0 B 0 0 0 0 * g2N 0 0 C D E F := by
      rw [g2N_mul_coords]
      refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
    rw [h]
    exact mul_mem (mem_sup_left (mem_rootSubgroup.2 ⟨B, pinnedX_a_eq_g2N B⟩))
      (mem_sup_right ⟨C, D, E, F, rfl⟩)

theorem rootSubgroup_r_sup_F : rootSubgroup .G2 K g2r ⊔ Model.F K = M K := by
  refine le_antisymm (sup_le ?_ F_le_M) ?_
  · intro g hg
    obtain ⟨A, rfl⟩ := mem_rootSubgroup.1 hg
    rw [pinnedX_r_eq_g2N]
    exact g2N_mem_M_iff.2 rfl
  · rintro _ ⟨A, C, D, E, F, rfl⟩
    have h : g2N A 0 C D E F = g2N A 0 0 0 0 0 * g2N 0 0 C D E F := by
      rw [g2N_mul_coords]
      refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
    rw [h]
    exact mul_mem (mem_sup_left (mem_rootSubgroup.2 ⟨A, pinnedX_r_eq_g2N A⟩))
      (mem_sup_right ⟨C, D, E, F, rfl⟩)

theorem Y_le_adjointGroup : Y K ≤ adjointGroup .G2 K := Y_le_S.trans (S_le_adjointGroup K)

theorem X_le_adjointGroup : X K ≤ adjointGroup .G2 K := X_le_S.trans (S_le_adjointGroup K)

theorem W_le_adjointGroup : W K ≤ adjointGroup .G2 K := W_le_S.trans (S_le_adjointGroup K)

theorem F_le_adjointGroup : Model.F K ≤ adjointGroup .G2 K := F_le_S.trans (S_le_adjointGroup K)

theorem D_le_adjointGroup : Model.D K ≤ adjointGroup .G2 K := D_le_S.trans (S_le_adjointGroup K)

theorem M_le_adjointGroup : M K ≤ adjointGroup .G2 K := M_le_S.trans (S_le_adjointGroup K)

theorem S_le_normalizer_U : S K ≤ normalizer (U K : Set (ModGL .G2 K)) := by
  refine le_normalizer_of_conj_mem fun s hs x hx => ?_
  obtain ⟨A, B, C, D, E, F, rfl⟩ := mem_S.1 hs
  obtain ⟨f, rfl⟩ := mem_U.1 hx
  rw [g2N_conj_coords, g2N_mem_U_iff]
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩ <;> ring

theorem S_le_normalizer_Y : S K ≤ normalizer (Y K : Set (ModGL .G2 K)) := by
  refine le_normalizer_of_conj_mem fun s hs x hx => ?_
  obtain ⟨A, B, C, D, E, F, rfl⟩ := mem_S.1 hs
  obtain ⟨e, f, rfl⟩ := mem_Y.1 hx
  rw [g2N_conj_coords, g2N_mem_Y_iff]
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> ring

theorem S_le_normalizer_X : S K ≤ normalizer (X K : Set (ModGL .G2 K)) := by
  refine le_normalizer_of_conj_mem fun s hs x hx => ?_
  obtain ⟨A, B, C, D, E, F, rfl⟩ := mem_S.1 hs
  obtain ⟨c, e, f, rfl⟩ := mem_X.1 hx
  rw [g2N_conj_coords, g2N_mem_X_iff]
  refine ⟨rfl, rfl, ?_⟩
  ring

theorem S_le_normalizer_W : S K ≤ normalizer (W K : Set (ModGL .G2 K)) := by
  refine le_normalizer_of_conj_mem fun s hs x hx => ?_
  obtain ⟨A, B, C, D, E, F, rfl⟩ := mem_S.1 hs
  obtain ⟨d, e, f, rfl⟩ := mem_W.1 hx
  rw [g2N_conj_coords, g2N_mem_W_iff]
  refine ⟨rfl, rfl, ?_⟩
  ring

theorem S_le_normalizer_F : S K ≤ normalizer (Model.F K : Set (ModGL .G2 K)) := by
  refine le_normalizer_of_conj_mem fun s hs x hx => ?_
  obtain ⟨A, B, C, D, E, F, rfl⟩ := mem_S.1 hs
  obtain ⟨c, d, e, f, rfl⟩ := mem_F.1 hx
  rw [g2N_conj_coords, g2N_mem_F_iff]
  exact ⟨rfl, rfl⟩

theorem S_le_normalizer_D : S K ≤ normalizer (Model.D K : Set (ModGL .G2 K)) := by
  refine le_normalizer_of_conj_mem fun s hs x hx => ?_
  obtain ⟨A, B, C, D, E, F, rfl⟩ := mem_S.1 hs
  obtain ⟨b, c, d, e, f, rfl⟩ := mem_D.1 hx
  rw [g2N_conj_coords, g2N_mem_D_iff]

theorem S_le_normalizer_M : S K ≤ normalizer (M K : Set (ModGL .G2 K)) := by
  refine le_normalizer_of_conj_mem fun s hs x hx => ?_
  obtain ⟨A, B, C, D, E, F, rfl⟩ := mem_S.1 hs
  obtain ⟨a, c, d, e, f, rfl⟩ := mem_M.1 hx
  rw [g2N_conj_coords, g2N_mem_M_iff]

theorem U_isElementaryAbelian : CFSG.IsElementaryAbelian 2 (U K) := by
  refine isElementaryAbelian_of_forall (fun x hx y hy => ?_) fun x hx => ?_
  · obtain ⟨a, rfl⟩ := mem_rootSubgroup.1 hx
    obtain ⟨b, rfl⟩ := mem_rootSubgroup.1 hy
    rw [← pinnedX_add, ← pinnedX_add, add_comm]
  · obtain ⟨a, rfl⟩ := mem_rootSubgroup.1 hx
    exact pinnedX_mul_self _ _

theorem Y_isElementaryAbelian : CFSG.IsElementaryAbelian 2 (Y K) := by
  refine isElementaryAbelian_of_forall (fun x hx y hy => ?_) fun x hx => ?_
  · obtain ⟨e, f, rfl⟩ := mem_Y.1 hx
    obtain ⟨e', f', rfl⟩ := mem_Y.1 hy
    rw [g2N_mul_coords, g2N_mul_coords]
    refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  · obtain ⟨e, f, rfl⟩ := mem_Y.1 hx
    rw [g2N_mul_self, ← g2N_zero]
    refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

theorem X_isElementaryAbelian : CFSG.IsElementaryAbelian 2 (X K) := by
  refine isElementaryAbelian_of_forall (fun x hx y hy => ?_) fun x hx => ?_
  · obtain ⟨c, e, f, rfl⟩ := mem_X.1 hx
    obtain ⟨c', e', f', rfl⟩ := mem_X.1 hy
    rw [g2N_mul_coords, g2N_mul_coords]
    refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  · obtain ⟨c, e, f, rfl⟩ := mem_X.1 hx
    rw [g2N_mul_self, ← g2N_zero]
    refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

theorem W_isElementaryAbelian : CFSG.IsElementaryAbelian 2 (W K) :=
  g2ShortRadical_isElementaryAbelian

omit
  [CharP K 2] in
theorem g2N_comp_injective {n : ℕ} (p₁ p₂ p₃ p₄ p₅ p₆ : (Fin n → K) → K)
    (h : ∀ v w, p₁ v = p₁ w → p₂ v = p₂ w → p₃ v = p₃ w → p₄ v = p₄ w → p₅ v = p₅ w →
      p₆ v = p₆ w → v = w) :
    Function.Injective fun v => g2N (p₁ v) (p₂ v) (p₃ v) (p₄ v) (p₅ v) (p₆ v) := by
  intro v w hvw
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := g2N_injective hvw
  exact h v w h1 h2 h3 h4 h5 h6

variable [Finite K]

omit
  [CharP K 2] [Finite K] in
theorem card_U : Nat.card (U K) = Nat.card K := card_rootSubgroup _

omit [Finite K] in
theorem card_Y : Nat.card (Y K) = Nat.card K ^ 2 := by
  rw [card_g2BCGroup, sq]

theorem card_X : Nat.card (X K) = Nat.card K ^ 3 := by
  refine card_eq_of_param (fun v => g2N 0 0 (v 0) 0 (v 1) (v 2))
    (g2N_comp_injective _ _ _ _ _ _ fun v w _ _ h3 _ h5 h6 => ?_) fun g => ?_
  · funext i
    fin_cases i
    exacts [h3, h5, h6]
  · rw [mem_X]
    exact ⟨fun ⟨c, e, f, h⟩ => ⟨![c, e, f], h.symm⟩, fun ⟨v, h⟩ => ⟨v 0, v 1, v 2, h.symm⟩⟩

theorem card_W : Nat.card (W K) = Nat.card K ^ 3 := by
  refine card_eq_of_param (fun v => g2N 0 0 0 (v 0) (v 1) (v 2))
    (g2N_comp_injective _ _ _ _ _ _ fun v w _ _ _ h4 h5 h6 => ?_) fun g => ?_
  · funext i
    fin_cases i
    exacts [h4, h5, h6]
  · rw [mem_W]
    exact ⟨fun ⟨d, e, f, h⟩ => ⟨![d, e, f], h.symm⟩, fun ⟨v, h⟩ => ⟨v 0, v 1, v 2, h.symm⟩⟩

theorem card_F : Nat.card (Model.F K) = Nat.card K ^ 4 := by
  refine card_eq_of_param (fun v => g2N 0 0 (v 0) (v 1) (v 2) (v 3))
    (g2N_comp_injective _ _ _ _ _ _ fun v w _ _ h3 h4 h5 h6 => ?_) fun g => ?_
  · funext i
    fin_cases i
    exacts [h3, h4, h5, h6]
  · rw [mem_F]
    exact ⟨fun ⟨c, d, e, f, h⟩ => ⟨![c, d, e, f], h.symm⟩,
      fun ⟨v, h⟩ => ⟨v 0, v 1, v 2, v 3, h.symm⟩⟩

theorem card_D : Nat.card (Model.D K) = Nat.card K ^ 5 := by
  refine card_eq_of_param (fun v => g2N 0 (v 0) (v 1) (v 2) (v 3) (v 4))
    (g2N_comp_injective _ _ _ _ _ _ fun v w _ h2 h3 h4 h5 h6 => ?_) fun g => ?_
  · funext i
    fin_cases i
    exacts [h2, h3, h4, h5, h6]
  · rw [mem_D]
    exact ⟨fun ⟨b, c, d, e, f, h⟩ => ⟨![b, c, d, e, f], h.symm⟩,
      fun ⟨v, h⟩ => ⟨v 0, v 1, v 2, v 3, v 4, h.symm⟩⟩

theorem card_M : Nat.card (M K) = Nat.card K ^ 5 := by
  refine card_eq_of_param (fun v => g2N (v 0) 0 (v 1) (v 2) (v 3) (v 4))
    (g2N_comp_injective _ _ _ _ _ _ fun v w h1 _ h3 h4 h5 h6 => ?_) fun g => ?_
  · funext i
    fin_cases i
    exacts [h1, h3, h4, h5, h6]
  · rw [mem_M]
    exact ⟨fun ⟨a, c, d, e, f, h⟩ => ⟨![a, c, d, e, f], h.symm⟩,
      fun ⟨v, h⟩ => ⟨v 0, v 1, v 2, v 3, v 4, h.symm⟩⟩

omit [CharP K 2] in
theorem card_S : Nat.card (S K) = Nat.card K ^ 6 := by
  refine card_eq_of_param (fun v => g2N (v 0) (v 1) (v 2) (v 3) (v 4) (v 5))
    (g2N_comp_injective _ _ _ _ _ _ fun v w h1 h2 h3 h4 h5 h6 => ?_) fun g => ?_
  · funext i
    fin_cases i
    exacts [h1, h2, h3, h4, h5, h6]
  · rw [mem_S]
    exact ⟨fun ⟨a, b, c, d, e, f, h⟩ => ⟨![a, b, c, d, e, f], h.symm⟩,
      fun ⟨v, h⟩ => ⟨v 0, v 1, v 2, v 3, v 4, v 5, h.symm⟩⟩

end Facts

end Model

structure G2Data {G : Type*} [Group G] (L : Subgroup G) (K : Type) [Field K] where
  equiv : L ≃* adjointGroup .G2 K

namespace G2Data

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] (d : G2Data L K)

@[expose] def emb : adjointGroup .G2 K →* G := L.subtype.comp d.equiv.symm.toMonoidHom

theorem emb_injective : Function.Injective d.emb :=
  Subtype.val_injective.comp d.equiv.symm.injective

theorem emb_mem (g : adjointGroup .G2 K) : d.emb g ∈ L := (d.equiv.symm g).2

theorem emb_equiv (x : L) : d.emb (d.equiv x) = x := by
  simp [emb]

theorem range_emb : d.emb.range = L := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact d.emb_mem g
  · intro hx
    exact ⟨d.equiv ⟨x, hx⟩, d.emb_equiv ⟨x, hx⟩⟩

theorem exists_emb_eq {x : G} (hx : x ∈ L) : ∃ g, d.emb g = x :=
  ⟨d.equiv ⟨x, hx⟩, d.emb_equiv ⟨x, hx⟩⟩

@[expose] def image (H : Subgroup (ModGL .G2 K)) : Subgroup G :=
  (H.subgroupOf (adjointGroup .G2 K)).map d.emb

theorem mem_image {H : Subgroup (ModGL .G2 K)} {x : G} :
    x ∈ d.image H ↔ ∃ g : adjointGroup .G2 K, (g : ModGL .G2 K) ∈ H ∧ d.emb g = x := by
  simp only [image, mem_map, mem_subgroupOf]

theorem emb_mem_image {H : Subgroup (ModGL .G2 K)} {g : adjointGroup .G2 K}
    (hg : (g : ModGL .G2 K) ∈ H) : d.emb g ∈ d.image H :=
  d.mem_image.2 ⟨g, hg, rfl⟩

theorem emb_mem_image_iff {H : Subgroup (ModGL .G2 K)} {g : adjointGroup .G2 K} :
    d.emb g ∈ d.image H ↔ (g : ModGL .G2 K) ∈ H := by
  refine ⟨fun h => ?_, d.emb_mem_image⟩
  obtain ⟨g', hg', he⟩ := d.mem_image.1 h
  rwa [← d.emb_injective he]

theorem image_le (H : Subgroup (ModGL .G2 K)) : d.image H ≤ L := by
  intro x hx
  obtain ⟨g, -, rfl⟩ := d.mem_image.1 hx
  exact d.emb_mem g

theorem image_mono {H₁ H₂ : Subgroup (ModGL .G2 K)} (h : H₁ ≤ H₂) : d.image H₁ ≤ d.image H₂ := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := d.mem_image.1 hx
  exact d.emb_mem_image (h hg)

theorem image_le_image_iff {H₁ H₂ : Subgroup (ModGL .G2 K)} (h₁ : H₁ ≤ adjointGroup .G2 K) :
    d.image H₁ ≤ d.image H₂ ↔ H₁ ≤ H₂ := by
  refine ⟨fun h g hg => ?_, d.image_mono⟩
  have := h (d.emb_mem_image (g := ⟨g, h₁ hg⟩) hg)
  exact d.emb_mem_image_iff.1 this

theorem image_inj {H₁ H₂ : Subgroup (ModGL .G2 K)} (h₁ : H₁ ≤ adjointGroup .G2 K)
    (h₂ : H₂ ≤ adjointGroup .G2 K) : d.image H₁ = d.image H₂ ↔ H₁ = H₂ :=
  ⟨fun h => le_antisymm ((d.image_le_image_iff h₁).1 h.le) ((d.image_le_image_iff h₂).1 h.ge),
    fun h => h ▸ rfl⟩

theorem image_inf (H₁ H₂ : Subgroup (ModGL .G2 K)) :
    d.image (H₁ ⊓ H₂) = d.image H₁ ⊓ d.image H₂ := by
  ext x
  simp only [mem_inf, d.mem_image]
  constructor
  · rintro ⟨g, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨g, h1, rfl⟩, ⟨g, h2, rfl⟩⟩
  · rintro ⟨⟨g, h1, rfl⟩, ⟨g', h2, he⟩⟩
    rw [d.emb_injective he] at h2
    exact ⟨g, ⟨h1, h2⟩, rfl⟩

theorem image_sup {H₁ H₂ : Subgroup (ModGL .G2 K)} (h₁ : H₁ ≤ adjointGroup .G2 K)
    (h₂ : H₂ ≤ adjointGroup .G2 K) : d.image (H₁ ⊔ H₂) = d.image H₁ ⊔ d.image H₂ := by
  rw [image, subgroupOf_sup h₁ h₂, Subgroup.map_sup]
  rfl

theorem image_adjointGroup : d.image (adjointGroup .G2 K) = L := by
  rw [image, subgroupOf_self, ← MonoidHom.range_eq_map, range_emb]

theorem card_image {H : Subgroup (ModGL .G2 K)} (h : H ≤ adjointGroup .G2 K) :
    Nat.card (d.image H) = Nat.card H := by
  rw [image, card_map_of_injective d.emb_injective]
  exact Nat.card_congr (subgroupOfEquivOfLe h).toEquiv

private theorem map_subtype_subgroupOf {H : Subgroup (ModGL .G2 K)}
    (h : H ≤ adjointGroup .G2 K) : (H.subgroupOf (adjointGroup .G2 K)).map
      (adjointGroup .G2 K).subtype = H := by
  rw [subgroupOf_map_subtype, inf_eq_left.2 h]

theorem image_commutator {H₁ H₂ : Subgroup (ModGL .G2 K)} (h₁ : H₁ ≤ adjointGroup .G2 K)
    (h₂ : H₂ ≤ adjointGroup .G2 K) : d.image ⁅H₁, H₂⁆ = ⁅d.image H₁, d.image H₂⁆ := by
  have key : ⁅H₁, H₂⁆.subgroupOf (adjointGroup .G2 K) =
      ⁅H₁.subgroupOf (adjointGroup .G2 K), H₂.subgroupOf (adjointGroup .G2 K)⁆ := by
    rw [← comap_map_eq_self_of_injective (adjointGroup .G2 K).subtype_injective
      ⁅H₁.subgroupOf (adjointGroup .G2 K), H₂.subgroupOf (adjointGroup .G2 K)⁆,
      map_commutator, map_subtype_subgroupOf h₁, map_subtype_subgroupOf h₂]
    rfl
  rw [image, key, map_commutator]
  rfl

theorem image_inf_centralizer (H₁ : Subgroup (ModGL .G2 K)) {H₂ : Subgroup (ModGL .G2 K)}
    (h₂ : H₂ ≤ adjointGroup .G2 K) :
    d.image (H₁ ⊓ centralizer (H₂ : Set (ModGL .G2 K))) =
      d.image H₁ ⊓ centralizer (d.image H₂ : Set G) := by
  ext x
  simp only [mem_inf, d.mem_image, SetLike.mem_coe, mem_centralizer_iff]
  constructor
  · rintro ⟨g, ⟨hg1, hg2⟩, rfl⟩
    refine ⟨⟨g, hg1, rfl⟩, fun y hy => ?_⟩
    obtain ⟨k, hk, rfl⟩ := d.mem_image.1 hy
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hg2 k hk)
  · rintro ⟨⟨g, hg1, rfl⟩, hc⟩
    refine ⟨g, ⟨hg1, fun k hk => ?_⟩, rfl⟩
    have := hc (d.emb ⟨k, h₂ hk⟩) (d.emb_mem_image hk)
    rw [← map_mul, ← map_mul] at this
    exact congrArg Subtype.val (d.emb_injective this)

theorem image_inf_normalizer {H : Subgroup (ModGL .G2 K)} (h : H ≤ adjointGroup .G2 K) :
    d.image (adjointGroup .G2 K ⊓ normalizer (H : Set (ModGL .G2 K))) =
      L ⊓ normalizer (d.image H : Set G) := by
  ext x
  simp only [mem_inf, d.mem_image, mem_normalizer_iff]
  constructor
  · rintro ⟨g, ⟨-, hgN⟩, rfl⟩
    refine ⟨d.emb_mem g, fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
    · obtain ⟨k, hk, rfl⟩ := d.mem_image.1 hy
      rw [← map_mul, ← map_inv, ← map_mul]
      exact d.emb_mem_image (by simpa using (hgN k).1 hk)
    · obtain ⟨k, hk, hke⟩ := d.mem_image.1 hy
      have hy' : y = d.emb (g⁻¹ * k * g) := by
        rw [map_mul, map_mul, hke, map_inv]
        group
      rw [hy']
      refine d.emb_mem_image ?_
      have := (hgN ((g⁻¹ * k * g : adjointGroup .G2 K) : ModGL .G2 K)).2
      simp only [coe_mul, coe_inv] at this ⊢
      exact this (by simpa [mul_assoc] using hk)
  · rintro ⟨hxL, hxN⟩
    obtain ⟨g, rfl⟩ := d.exists_emb_eq hxL
    refine ⟨g, ⟨g.2, fun m => ⟨fun hm => ?_, fun hm => ?_⟩⟩, rfl⟩
    · have := (hxN (d.emb ⟨m, h hm⟩)).1 (d.emb_mem_image hm)
      rw [← map_inv, ← map_mul, ← map_mul] at this
      exact d.emb_mem_image_iff.1 this
    · have hmA : m ∈ adjointGroup .G2 K := by
        have := mul_mem (mul_mem (inv_mem g.2) (h hm)) g.2
        simpa [mul_assoc] using this
      have h1 : d.emb g * d.emb ⟨m, hmA⟩ * (d.emb g)⁻¹ ∈ d.image H := by
        rw [← map_inv, ← map_mul, ← map_mul]
        exact d.emb_mem_image (by simpa using hm)
      exact d.emb_mem_image_iff.1 ((hxN _).2 h1)

private theorem mul_comm_of_mem' {M : Type*} [Group M] {H : Subgroup M} [IsMulCommutative H]
    {x y : M} (hx : x ∈ H) (hy : y ∈ H) : x * y = y * x :=
  congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : H) ⟨y, hy⟩)

theorem isElementaryAbelian_image {H : Subgroup (ModGL .G2 K)} [CFSG.IsElementaryAbelian 2 H] :
    CFSG.IsElementaryAbelian 2 (d.image H) := by
  refine isElementaryAbelian_of_forall (fun x hx y hy => ?_) fun x hx => ?_
  · obtain ⟨g, hg, rfl⟩ := d.mem_image.1 hx
    obtain ⟨k, hk, rfl⟩ := d.mem_image.1 hy
    rw [← map_mul, ← map_mul]
    exact congrArg d.emb (Subtype.ext (mul_comm_of_mem' hg hk))
  · obtain ⟨g, hg, rfl⟩ := d.mem_image.1 hx
    have h2 : (g : ModGL .G2 K) ^ 2 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian _ hg
    rw [← map_mul, ← map_one d.emb]
    exact congrArg d.emb (Subtype.ext (by rw [coe_mul, ← sq, h2, coe_one]))

theorem image_map_conj (g : adjointGroup .G2 K) (H : Subgroup (ModGL .G2 K)) :
    d.image (H.map (MulAut.conj (g : ModGL .G2 K)).toMonoidHom) =
      (d.image H).map (MulAut.conj (d.emb g)).toMonoidHom := by
  ext x
  simp only [d.mem_image, mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨k, ⟨m, hm, hmk⟩, rfl⟩
    have hmA : m ∈ adjointGroup .G2 K := by
      have := mul_mem (mul_mem (inv_mem g.2) k.2) g.2
      rwa [← hmk, show (g : ModGL .G2 K)⁻¹ * (g * m * (g : ModGL .G2 K)⁻¹) * g = m by group]
        at this
    refine ⟨d.emb ⟨m, hmA⟩, ⟨⟨m, hmA⟩, hm, rfl⟩, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by simpa using hmk)
  · rintro ⟨y, ⟨m, hm, rfl⟩, rfl⟩
    refine ⟨g * m * g⁻¹, ⟨m, hm, by simp⟩, ?_⟩
    simp [map_mul, map_inv]

@[expose] def preimage (E : Subgroup G) : Subgroup (ModGL .G2 K) :=
  (E.comap d.emb).map (adjointGroup .G2 K).subtype

theorem preimage_le (E : Subgroup G) : d.preimage E ≤ adjointGroup .G2 K := by
  rintro _ ⟨g, -, rfl⟩
  exact g.2

theorem mem_preimage {E : Subgroup G} {g : adjointGroup .G2 K} :
    (g : ModGL .G2 K) ∈ d.preimage E ↔ d.emb g ∈ E := by
  constructor
  · rintro ⟨g', hg', he⟩
    rwa [← Subtype.ext he]
  · intro h
    exact ⟨g, h, rfl⟩

theorem image_preimage {E : Subgroup G} (hE : E ≤ L) : d.image (d.preimage E) = E := by
  ext x
  rw [d.mem_image]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact d.mem_preimage.1 hg
  · intro hx
    obtain ⟨g, rfl⟩ := d.exists_emb_eq (hE hx)
    exact ⟨g, d.mem_preimage.2 hx, rfl⟩

theorem preimage_image {H : Subgroup (ModGL .G2 K)} (hH : H ≤ adjointGroup .G2 K) :
    d.preimage (d.image H) = H := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact d.emb_mem_image_iff.1 hg
  · intro hx
    exact (d.mem_preimage (g := ⟨x, hH hx⟩)).2 (d.emb_mem_image hx)

theorem isElementaryAbelian_image_iff {H : Subgroup (ModGL .G2 K)}
    (hH : H ≤ adjointGroup .G2 K) :
    CFSG.IsElementaryAbelian 2 (d.image H) ↔ CFSG.IsElementaryAbelian 2 H := by
  refine ⟨fun h => ?_, fun _ => d.isElementaryAbelian_image⟩
  refine isElementaryAbelian_of_forall (fun x hx y hy => ?_) fun x hx => ?_
  · have h1 := congrArg Subtype.val (mul_comm' (⟨_, d.emb_mem_image (g := ⟨x, hH hx⟩) hx⟩ :
      d.image H) ⟨_, d.emb_mem_image (g := ⟨y, hH hy⟩) hy⟩)
    simp only [Subgroup.coe_mul] at h1
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (d.emb_injective h1)
  · have h1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := d.image H) _
      (d.emb_mem_image (g := ⟨x, hH hx⟩) hx)
    rw [← map_pow, ← map_one d.emb] at h1
    have h2 := congrArg Subtype.val (d.emb_injective h1)
    rwa [Subgroup.coe_pow, Subgroup.coe_one, sq] at h2

theorem image_le_normalizer {H₁ H₂ : Subgroup (ModGL .G2 K)} (h₁ : H₁ ≤ adjointGroup .G2 K)
    (h₂ : H₂ ≤ adjointGroup .G2 K) (h : H₁ ≤ normalizer (H₂ : Set (ModGL .G2 K))) :
    d.image H₁ ≤ normalizer (d.image H₂ : Set G) := by
  have := d.image_mono (le_inf h₁ h)
  rw [d.image_inf_normalizer h₂] at this
  exact this.trans inf_le_right

section Subgroups


@[expose] def S : Subgroup G := d.image (Model.S K)

@[expose] def U : Subgroup G := d.image (Model.U K)

@[expose] def J : Subgroup G := d.image (Model.J K)

@[expose] def J₁ : Subgroup G := d.image (Model.J₁ K)

@[expose] def J₂ : Subgroup G := d.image (Model.J₂ K)

@[expose] def J₃ : Subgroup G := d.image (Model.J₃ K)

@[expose] def J₄ : Subgroup G := d.image (Model.J₄ K)

@[expose] def J₅ : Subgroup G := d.image (Model.J₅ K)

@[expose] def J₆ : Subgroup G := d.image (Model.J₆ K)

@[expose] def rootGroup (s : Fin Tag.G2.rank → ℤ) : Subgroup G :=
  d.image (rootSubgroup .G2 K s)

@[expose] def leviA : Subgroup G := d.image (Model.leviA K)

@[expose] def leviB : Subgroup G := d.image (Model.leviB K)

@[expose] def wa : G := d.emb ⟨Model.wa K, Model.wa_mem_adjointGroup K⟩

@[expose] def wb : G := d.emb ⟨Model.wb K, Model.wb_mem_adjointGroup K⟩

end Subgroups

section Radicals

variable
  [CharP K 2]

@[expose] def Y : Subgroup G := d.image (Model.Y K)

@[expose] def X : Subgroup G := d.image (Model.X K)

@[expose] def W : Subgroup G := d.image (Model.W K)

@[expose] def F : Subgroup G := d.image (Model.F K)

@[expose] def D : Subgroup G := d.image (Model.D K)

@[expose] def M : Subgroup G := d.image (Model.M K)

@[expose] def fieldAut [Finite K] : MulAut L :=
  d.equiv.trans ((Model.fieldAut K).trans d.equiv.symm)

end Radicals

theorem exists_of_lieModel
    {G : Type} [Group G] {L : Subgroup G} {f : ℕ}
    (h : LieModel L .G2 0 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ f ∧
      Nonempty (G2Data L K) := by
  have hce : ChevalleyExceptionalModel L .G2 2 f := by
    rcases h with ⟨hcl, -⟩ | ⟨-, -, hce⟩ | ⟨-, hree, -⟩ | ⟨-, hsz, -⟩
    · exact absurd hcl (by decide)
    · exact hce
    · exact absurd hree (by decide)
    · exact absurd hsz (by decide)
  obtain ⟨⟨-, hf, -⟩, hU⟩ := hce
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hU
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  exact ⟨K, inferInstance, inferInstance, inferInstance, hK, ⟨⟨e⟩⟩⟩

section Facts

variable
  [CharP K 2]

theorem inclusions : d.U ≤ d.Y ∧ d.Y ≤ d.X ∧ d.Y ≤ d.W ∧ d.X ≤ d.F ∧ d.W ≤ d.F ∧ d.F ≤ d.D ∧
    d.F ≤ d.M ∧ d.D ≤ d.S ∧ d.M ≤ d.S ∧ d.S ≤ L :=
  ⟨d.image_mono Model.U_le_Y, d.image_mono Model.Y_le_X, d.image_mono Model.Y_le_W,
    d.image_mono Model.X_le_F, d.image_mono Model.W_le_F, d.image_mono Model.F_le_D,
    d.image_mono Model.F_le_M, d.image_mono Model.D_le_S, d.image_mono Model.M_le_S,
    d.image_le _⟩

theorem yamada_defs : d.rootGroup g2b ⊔ d.U = d.Y ∧ d.rootGroup g2u ⊔ d.Y = d.X ∧
    d.rootGroup g2v ⊔ d.Y = d.W ∧ d.X ⊔ d.W = d.F ∧ d.rootGroup g2a ⊔ d.F = d.D ∧
    d.rootGroup g2r ⊔ d.F = d.M ∧ d.X ⊓ d.W = d.Y ∧ d.D ⊓ d.M = d.F ∧ d.D ⊔ d.M = d.S := by
  have hr := fun s => rootSubgroup_le_adjointGroup (K := K) (τ := .G2) s
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rootGroup, U, Y, ← d.image_sup (hr _) (Model.U_le_adjointGroup K),
      Model.rootSubgroup_b_sup_U]
  · rw [rootGroup, X, Y, ← d.image_sup (hr _) Model.Y_le_adjointGroup,
      Model.rootSubgroup_u_sup_Y]
  · rw [rootGroup, W, Y, ← d.image_sup (hr _) Model.Y_le_adjointGroup,
      Model.rootSubgroup_v_sup_Y]
  · rw [X, W, F, ← d.image_sup Model.X_le_adjointGroup Model.W_le_adjointGroup, Model.X_sup_W]
  · rw [rootGroup, D, F, ← d.image_sup (hr _) Model.F_le_adjointGroup,
      Model.rootSubgroup_a_sup_F]
  · rw [rootGroup, M, F, ← d.image_sup (hr _) Model.F_le_adjointGroup,
      Model.rootSubgroup_r_sup_F]
  · rw [X, W, Y, ← d.image_inf, Model.X_inf_W]
  · rw [D, M, F, ← d.image_inf, Model.D_inf_M]
  · rw [D, M, S, ← d.image_sup Model.D_le_adjointGroup Model.M_le_adjointGroup, Model.D_sup_M]

theorem S_le_normalizers : d.S ≤ normalizer (d.U : Set G) ∧ d.S ≤ normalizer (d.Y : Set G) ∧
    d.S ≤ normalizer (d.X : Set G) ∧ d.S ≤ normalizer (d.W : Set G) ∧
    d.S ≤ normalizer (d.F : Set G) ∧ d.S ≤ normalizer (d.D : Set G) ∧
    d.S ≤ normalizer (d.M : Set G) := by
  have hS := Model.S_le_adjointGroup K
  exact ⟨d.image_le_normalizer hS (Model.U_le_adjointGroup K) Model.S_le_normalizer_U,
    d.image_le_normalizer hS Model.Y_le_adjointGroup Model.S_le_normalizer_Y,
    d.image_le_normalizer hS Model.X_le_adjointGroup Model.S_le_normalizer_X,
    d.image_le_normalizer hS Model.W_le_adjointGroup Model.S_le_normalizer_W,
    d.image_le_normalizer hS Model.F_le_adjointGroup Model.S_le_normalizer_F,
    d.image_le_normalizer hS Model.D_le_adjointGroup Model.S_le_normalizer_D,
    d.image_le_normalizer hS Model.M_le_adjointGroup Model.S_le_normalizer_M⟩

theorem isElementaryAbelian : CFSG.IsElementaryAbelian 2 d.U ∧ CFSG.IsElementaryAbelian 2 d.Y ∧
    CFSG.IsElementaryAbelian 2 d.X ∧ CFSG.IsElementaryAbelian 2 d.W := by
  have := Model.U_isElementaryAbelian (K := K)
  have := Model.Y_isElementaryAbelian (K := K)
  have := Model.X_isElementaryAbelian (K := K)
  have := Model.W_isElementaryAbelian (K := K)
  exact ⟨d.isElementaryAbelian_image, d.isElementaryAbelian_image, d.isElementaryAbelian_image,
    d.isElementaryAbelian_image⟩

theorem cards [Finite K] : Nat.card d.U = Nat.card K ∧ Nat.card d.Y = Nat.card K ^ 2 ∧
    Nat.card d.X = Nat.card K ^ 3 ∧ Nat.card d.W = Nat.card K ^ 3 ∧
    Nat.card d.F = Nat.card K ^ 4 ∧ Nat.card d.D = Nat.card K ^ 5 ∧
    Nat.card d.M = Nat.card K ^ 5 ∧ Nat.card d.S = Nat.card K ^ 6 :=
  ⟨(d.card_image (Model.U_le_adjointGroup K)).trans Model.card_U,
    (d.card_image Model.Y_le_adjointGroup).trans Model.card_Y,
    (d.card_image Model.X_le_adjointGroup).trans Model.card_X,
    (d.card_image Model.W_le_adjointGroup).trans Model.card_W,
    (d.card_image Model.F_le_adjointGroup).trans Model.card_F,
    (d.card_image Model.D_le_adjointGroup).trans Model.card_D,
    (d.card_image Model.M_le_adjointGroup).trans Model.card_M,
    (d.card_image (Model.S_le_adjointGroup K)).trans Model.card_S⟩

end Facts

end G2Data

end CFSG.LocalAnalysis.EvenBN.G2

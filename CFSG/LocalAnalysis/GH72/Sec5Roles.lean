module

public import CFSG.LocalAnalysis.GH72.Sec5DBasic
public import CFSG.LocalAnalysis.GH72.Sec2
public import CFSG.LocalAnalysis.GH72.G3bNineteen
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorNontrivial

public section

namespace CFSG.GH72

open Subgroup
open scoped Pointwise

structure Sec5Roles (G : Type) [Group G] [Finite G] (A : Subgroup G) where
  S : Sylow 2 G
  S₁ : Subgroup G
  S₂ : Subgroup G
  z₁ : G
  z₂ : G
  sup_eq : S₁ ⊔ S₂ = S
  inf_eq : S₁ ⊓ S₂ = ⊥
  commute : S₂ ≤ centralizer (S₁ : Set G)
  dih₁ : IsDih S₁
  dih₂ : IsDih S₂
  fusion : HasProductFusion S₁ S₂
  hz₁ : z₁ ∈ S₁ ∧ orderOf z₁ = 2 ∧ S₁ ≤ C z₁
  hz₂ : z₂ ∈ S₂ ∧ orderOf z₂ = 2 ∧ S₂ ≤ C z₂
  hAS : A ≤ S
  hA : IsE16 A
  oddCore_eq_bot : CFSG.oddCore G = ⊥
  split : (A ⊓ S₁) ⊔ (A ⊓ S₂) = A ∧ IsKleinFour ↥(A ⊓ S₁) ∧ IsKleinFour ↥(A ⊓ S₂)
  z_mem : z₁ ∈ A ⊓ S₁ ∧ z₂ ∈ A ⊓ S₂
  normalizer_le : normalizer (A : Set G) ≤
    normalizer ((A ⊓ S₁ : Subgroup G) : Set G) ⊓ normalizer ((A ⊓ S₂ : Subgroup G) : Set G)
  conj₁ : ∀ x ∈ A ⊓ S₁, x ≠ 1 → ∃ n ∈ normalizer (A : Set G), n * z₁ * n⁻¹ = x
  conj₂ : ∀ y ∈ A ⊓ S₂, y ≠ 1 → ∃ n ∈ normalizer (A : Set G), n * z₂ * n⁻¹ = y
  isSylowOf_centralizer : CFSG.ABGLocalTools.IsSylowOf 2 A (centralizer (A : Set G))

namespace Sec5Roles

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} (ρ : Sec5Roles G A)

@[expose] def X : Subgroup G := A ⊓ ρ.S₁
@[expose] def Y : Subgroup G := A ⊓ ρ.S₂
@[expose] def M : Subgroup G := centralizer (ρ.X : Set G)
@[expose] def N : Subgroup G := centralizer (ρ.Y : Set G)
@[expose] def M₀ : Subgroup G := ⁅O2 ρ.M, O2 ρ.M⁆ ⊔ O ρ.M
@[expose] def N₀ : Subgroup G := ⁅O2 ρ.N, O2 ρ.N⁆ ⊔ O ρ.N
@[expose] def IsCoveringFirst (p : ℕ) (H : Subgroup G) : Prop :=
  Sec4Setting.IsPLocalA p A H ∧ Covers H ρ.M₀ (O ρ.M)
@[expose] def IsCoveringSecond (p : ℕ) (H : Subgroup G) : Prop :=
  Sec4Setting.IsPLocalA p A H ∧ Covers H ρ.N₀ (O ρ.N)
@[expose] def IsCovering (p : ℕ) (H : Subgroup G) : Prop :=
  Sec4Setting.IsPLocalA p A H ∧ Covers H ρ.M₀ (O ρ.M) ∧ Covers H ρ.N₀ (O ρ.N)

@[expose] def swap : Sec5Roles G A where
  S := ρ.S
  S₁ := ρ.S₂
  S₂ := ρ.S₁
  z₁ := ρ.z₂
  z₂ := ρ.z₁
  sup_eq := (sup_comm _ _).trans ρ.sup_eq
  inf_eq := (inf_comm _ _).trans ρ.inf_eq
  commute := le_centralizer_iff.mp ρ.commute
  dih₁ := ρ.dih₂
  dih₂ := ρ.dih₁
  fusion := ρ.fusion.swap
  hz₁ := ρ.hz₂
  hz₂ := ρ.hz₁
  hAS := ρ.hAS
  hA := ρ.hA
  oddCore_eq_bot := ρ.oddCore_eq_bot
  split := ⟨(sup_comm _ _).trans ρ.split.1, ρ.split.2.2, ρ.split.2.1⟩
  z_mem := ⟨ρ.z_mem.2, ρ.z_mem.1⟩
  normalizer_le := fun _ hn => ⟨(ρ.normalizer_le hn).2, (ρ.normalizer_le hn).1⟩
  conj₁ := ρ.conj₂
  conj₂ := ρ.conj₁
  isSylowOf_centralizer := ρ.isSylowOf_centralizer

theorem isCovering_swap {p : ℕ} {H : Subgroup G} : ρ.swap.IsCovering p H ↔ ρ.IsCovering p H :=
  ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₃, h₂⟩, fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₃, h₂⟩⟩

theorem X_le_A : ρ.X ≤ A := inf_le_left
theorem Y_le_A : ρ.Y ≤ A := inf_le_left
theorem X_le_S₁ : ρ.X ≤ ρ.S₁ := inf_le_right
theorem Y_le_S₂ : ρ.Y ≤ ρ.S₂ := inf_le_right

theorem X_sup_Y : ρ.X ⊔ ρ.Y = A := ρ.split.1

theorem X_inf_Y : ρ.X ⊓ ρ.Y = ⊥ := by
  rw [eq_bot_iff, ← ρ.inf_eq]
  exact inf_le_inf ρ.X_le_S₁ ρ.Y_le_S₂

theorem isKleinFour_X : IsKleinFour ρ.X := ρ.split.2.1
theorem isKleinFour_Y : IsKleinFour ρ.Y := ρ.split.2.2

theorem card_X : Nat.card ρ.X = 4 := @IsKleinFour.card_four _ _ ρ.isKleinFour_X
theorem card_Y : Nat.card ρ.Y = 4 := @IsKleinFour.card_four _ _ ρ.isKleinFour_Y

theorem z₁_mem_X : ρ.z₁ ∈ ρ.X := ρ.z_mem.1
theorem z₂_mem_Y : ρ.z₂ ∈ ρ.Y := ρ.z_mem.2

theorem z₁_ne_one : ρ.z₁ ≠ 1 := fun h => by
  have h2 := ρ.hz₁.2.1
  rw [h, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem z₂_ne_one : ρ.z₂ ≠ 1 := ρ.swap.z₁_ne_one

include ρ in
theorem isPGroup_A : IsPGroup 2 A := G5d.isPGroup_of_isE16 ρ.hA

include ρ in
theorem comm {a b : G} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a :=
  G4b.comm_of_isE16 ρ.hA ha hb

theorem A_le_M : A ≤ ρ.M := fun _ ha =>
  mem_centralizer_iff.mpr fun _ hx => ρ.comm (ρ.X_le_A hx) ha

theorem A_le_N : A ≤ ρ.N := ρ.swap.A_le_M

theorem M_le_C {x : G} (hx : x ∈ ρ.X) : ρ.M ≤ C x :=
  centralizer_le (Set.singleton_subset_iff.mpr hx)

theorem M₀_le : ρ.M₀ ≤ ρ.M :=
  sup_le (commutator_le.mpr fun _ ha _ hb => ρ.M.mul_mem (ρ.M.mul_mem
    (ρ.M.mul_mem (map_subtype_le _ ha) (map_subtype_le _ hb))
    (ρ.M.inv_mem (map_subtype_le _ ha))) (ρ.M.inv_mem (map_subtype_le _ hb)))
    (map_subtype_le _)

theorem N₀_le : ρ.N₀ ≤ ρ.N := ρ.swap.M₀_le

theorem O_M_le_M₀ : O ρ.M ≤ ρ.M₀ := le_sup_right

theorem O_N_le_N₀ : O ρ.N ≤ ρ.N₀ := le_sup_right

theorem M₀_le_normalizer_O_M : ρ.M₀ ≤ normalizer (O ρ.M : Set G) :=
  ρ.M₀_le.trans (le_normalizer_O _)

theorem N₀_le_normalizer_O_N : ρ.N₀ ≤ normalizer (O ρ.N : Set G) := ρ.swap.M₀_le_normalizer_O_M

theorem M_le_normalizer_X : ρ.M ≤ normalizer (ρ.X : Set G) :=
  centralizer_le_normalizer _

theorem N_le_normalizer_Y : ρ.N ≤ normalizer (ρ.Y : Set G) := ρ.swap.M_le_normalizer_X

theorem normalizer_X_le_normalizer_M : normalizer (ρ.X : Set G) ≤ normalizer (ρ.M : Set G) :=
  fun _ hn => G4b.mem_normalizer_centralizer hn

theorem normalizer_X_le_normalizer_M₀ : normalizer (ρ.X : Set G) ≤ normalizer (ρ.M₀ : Set G) :=
  fun _ hn => G4b.mem_normalizer_centralizer_core hn

theorem normalizer_Y_le_normalizer_N₀ : normalizer (ρ.Y : Set G) ≤ normalizer (ρ.N₀ : Set G) :=
  ρ.swap.normalizer_X_le_normalizer_M₀

theorem normalizer_X_le_normalizer_O_M :
    normalizer (ρ.X : Set G) ≤ normalizer (O ρ.M : Set G) := fun _ hn =>
  ProperTwoGeneratedCore.LocalCriterionDenominator.normalizer_normalizes_oddCore_image _
    (ρ.normalizer_X_le_normalizer_M hn)

theorem normalizer_le_normalizer_X : normalizer (A : Set G) ≤ normalizer (ρ.X : Set G) :=
  fun _ hn => (ρ.normalizer_le hn).1

theorem normalizer_le_normalizer_Y : normalizer (A : Set G) ≤ normalizer (ρ.Y : Set G) :=
  ρ.swap.normalizer_le_normalizer_X

theorem normalizer_le_normalizer_M₀ : normalizer (A : Set G) ≤ normalizer (ρ.M₀ : Set G) :=
  ρ.normalizer_le_normalizer_X.trans ρ.normalizer_X_le_normalizer_M₀

theorem normalizer_le_normalizer_N₀ : normalizer (A : Set G) ≤ normalizer (ρ.N₀ : Set G) :=
  ρ.swap.normalizer_le_normalizer_M₀

theorem normalizer_le_normalizer_O_M : normalizer (A : Set G) ≤ normalizer (O ρ.M : Set G) :=
  ρ.normalizer_le_normalizer_X.trans ρ.normalizer_X_le_normalizer_O_M

theorem normalizer_le_normalizer_O_N : normalizer (A : Set G) ≤ normalizer (O ρ.N : Set G) :=
  ρ.swap.normalizer_le_normalizer_O_M

include ρ in
theorem ne_top_of_isPLocal {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {H : Subgroup G}
    (hH : CFSG.IsPLocal p H) : H ≠ ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨R, hR1, hRp, rfl⟩ := hH
  intro htop
  have hRn : R.Normal := normalizer_eq_top_iff.mp htop
  have hodd : Odd (Nat.card R) := by
    obtain ⟨n, hn⟩ := hRp.exists_card_eq
    rw [hn]
    exact (hp.odd_of_ne_two hp2).pow
  have hle := ABGLocalTools.le_oddCore_of_normal hRn hodd
  rw [ρ.oddCore_eq_bot, le_bot_iff] at hle
  exact hR1 hle

theorem C_ne_top_of_mem_X {x : G} (hx : x ∈ ρ.X) (hx1 : x ≠ 1) : C x ≠ ⊤ := by
  intro htop
  obtain ⟨x', hx', hx'z⟩ := exists_mem_not_mem_zpowers_of_isKleinFour ρ.isKleinFour_X hx hx1
  have hx'1 : x' ≠ 1 := fun h => hx'z (h ▸ one_mem _)
  obtain ⟨g, hg⟩ := isConj_iff.mp (ρ.fusion.conj₁ x hx.2 x' hx'.2
    (G4b.orderOf_eq_two_of_isE16 ρ.hA hx.1 hx1) (G4b.orderOf_eq_two_of_isE16 ρ.hA hx'.1 hx'1))
  have hgx : g ∈ C x := by
    rw [htop]
    exact mem_top g
  rw [mem_centralizer_singleton_iff] at hgx
  apply hx'z
  rw [← hg, hgx, mul_inv_cancel_right]
  exact mem_zpowers x

theorem C_ne_top_of_mem_Y {y : G} (hy : y ∈ ρ.Y) (hy1 : y ≠ 1) : C y ≠ ⊤ :=
  ρ.swap.C_ne_top_of_mem_X hy hy1

end Sec5Roles

@[expose] def Sec4Setting.sec5Roles {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G)
    {A : Subgroup G} (hAS : A ≤ 𝔖.S) (hA : IsE16 A) : Sec5Roles G A where
  S := 𝔖.S
  S₁ := 𝔖.S₁
  S₂ := 𝔖.S₂
  z₁ := 𝔖.z₁
  z₂ := 𝔖.z₂
  sup_eq := 𝔖.decomp.sup_eq
  inf_eq := 𝔖.decomp.inf_eq
  commute := 𝔖.decomp.commute
  dih₁ := 𝔖.decomp.dih₁
  dih₂ := isDih_of_isDihNonab 𝔖.decomp.dih₂
  fusion := 𝔖.fusion
  hz₁ := 𝔖.hz₁
  hz₂ := 𝔖.hz₂
  hAS := hAS
  hA := hA
  oddCore_eq_bot := 𝔖.mc.hyp.1
  split := ⟨G4b.X_sup_Y 𝔖 hAS hA, G4b.isKleinFour_X 𝔖 hAS hA, G4b.isKleinFour_Y 𝔖 hAS hA⟩
  z_mem := ⟨G4b.z₁_mem_X 𝔖 hAS hA, G4b.z₂_mem_Y 𝔖 hAS hA⟩
  normalizer_le := fun _ hn => ⟨G4b.normalizer_le_normalizer_X 𝔖 hAS hA hn,
    G4b.normalizer_le_normalizer_Y 𝔖 hAS hA hn⟩
  conj₁ := fun _ hx hx1 => G4b.exists_mem_normalizer_conj_eq_of_mem_X 𝔖 hAS hA hx hx1
  conj₂ := fun _ hy hy1 => G4b.exists_mem_normalizer_conj_eq_of_mem_Y 𝔖 hAS hA hy hy1
  isSylowOf_centralizer := 𝔖.decomp.isSylowOf_centralizer_e16 hAS hA

namespace Sec4Setting

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G}
  (hAS : A ≤ 𝔖.S) (hA : IsE16 A)

theorem sec5Roles_isCovering {p : ℕ} {H : Subgroup G} :
    (𝔖.sec5Roles hAS hA).IsCovering p H ↔ 𝔖.IsCovering p A H := Iff.rfl

end Sec4Setting

structure Sec5KConfig {G : Type} [Group G] [Finite G] {A : Subgroup G} (ρ : Sec5Roles G A)
    (p : ℕ) where
  hp : p.Prime
  hp2 : p ≠ 2
  P : Subgroup G
  hP : IsMaxInvIn p A ⊤ P
  K : Subgroup G
  hK : CFSG.IsPLocal p K ∧ A ≤ K ∧ Covers K ρ.N₀ (O ρ.N) ∧
    IsMaxInvIn p A K (P ⊓ K) ∧ K = normalizer ((P ⊓ K ⊓ O K : Subgroup G) : Set G) ∧
    ρ.X ≤ centralizer ((P ⊓ K ⊓ O K : Subgroup G) : Set G)
  K₁ : Subgroup G
  hK₁ : (P ⊓ K) ⊔ A ≤ K₁ ∧ K₁ ≤ K ∧ Covers K₁ ρ.N₀ (O ρ.N) ∧
    P ⊓ K ⊓ O K₁ = P ⊓ K ⊓ O K
  hUV : ∃ u : G, P ⊓ centralizer (ρ.X : Set G) ⊓ K = (P ⊓ K ⊓ O K) ⊔ zpowers u
  hKmax : ∀ K' T : Subgroup G, CFSG.IsPLocal p K' → A ≤ K' →
    Covers K' ρ.N₀ (O ρ.N) → T ≤ K' → IsPGroup p T → A ≤ normalizer (T : Set G) →
    Nat.card T ≤ Nat.card (P ⊓ K : Subgroup G)
  hK₁q : ⁅K₁, ρ.Y⁆ ≤ O K₁ ∧
    ∃ W : Subgroup G, W ≤ K₁ ⊓ ρ.N₀ ∧ ρ.X ≤ W ∧ Covers W ρ.N₀ (O ρ.N) ∧
      K₁ = W ⊔ (P ⊓ K) ⊔ ρ.Y ⊔ O K₁ ∧ ((W ⊔ O K₁).subgroupOf K₁).Normal ∧
      O K₁ ⊓ W = W ⊓ O ρ.N ∧
      (IsL2OrA7 (bar K₁ W) 5 ∨ (bar K₁ W = bar K₁ ρ.X ∧ IsKleinFour (bar K₁ W)))

namespace Sec5KConfig

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {ρ : Sec5Roles G A} {p : ℕ}
  (𝔨 : Sec5KConfig ρ p)

@[expose] def Pstar : Subgroup G := 𝔨.P ⊓ 𝔨.K
@[expose] def V : Subgroup G := 𝔨.P ⊓ 𝔨.K ⊓ O 𝔨.K
@[expose] def R : Subgroup G := 𝔨.P ⊓ centralizer (ρ.X : Set G)
@[expose] def U : Subgroup G := 𝔨.R ⊓ 𝔨.K

end Sec5KConfig

structure Sec5ConfigR {G : Type} [Group G] [Finite G] {A : Subgroup G} (ρ : Sec5Roles G A)
    (p : ℕ) extends Sec5KConfig ρ p where
  x₀ : G
  hx₀ : x₀ ∈ ρ.X ∧ x₀ ≠ 1 ∧ Sec4Setting.PConstrainedWrt p A (C x₀) ρ.Y
  hno : ¬ ∃ H, ρ.IsCovering p H
  H₀ : Subgroup G
  hH₀ : P ⊔ A ≤ H₀ ∧ H₀ ≤ normalizer (CFSG.ambientMaxCardZJ P : Set G) ∧
    Covers H₀ ρ.M₀ (O ρ.M)
  hH₁ : ¬ ρ.Y ≤ centralizer ((P ⊓ O H₀ : Subgroup G) : Set G) ∧
    Covers (H₀ ⊓ normalizer ((P ⊓ O H₀ : Subgroup G) : Set G)) ρ.M₀ (O ρ.M) ∧
    ⁅H₀ ⊓ normalizer ((P ⊓ O H₀ : Subgroup G) : Set G), ρ.X⁆ ≤
      O (H₀ ⊓ normalizer ((P ⊓ O H₀ : Subgroup G) : Set G)) ∧
    ∃ W : Subgroup G, W ≤ H₀ ⊓ normalizer ((P ⊓ O H₀ : Subgroup G) : Set G) ⊓ ρ.M₀ ∧
      ρ.Y ≤ W ∧ Covers W ρ.M₀ (O ρ.M) ∧
      ((W ⊔ O (H₀ ⊓ normalizer ((P ⊓ O H₀ : Subgroup G) : Set G))).subgroupOf
        (H₀ ⊓ normalizer ((P ⊓ O H₀ : Subgroup G) : Set G))).Normal ∧
      O (H₀ ⊓ normalizer ((P ⊓ O H₀ : Subgroup G) : Set G)) ⊓ W = W ⊓ O ρ.M ∧
      IsL2OrA7 (bar (H₀ ⊓ normalizer ((P ⊓ O H₀ : Subgroup G) : Set G)) W) 5

@[expose] def Sec5ConfigR.Q {G : Type} [Group G] [Finite G] {A : Subgroup G} {ρ : Sec5Roles G A}
    {p : ℕ} (𝔠 : Sec5ConfigR ρ p) : Subgroup G := 𝔠.P ⊓ O 𝔠.H₀

structure Sec5ConfigTR {G : Type} [Group G] [Finite G] {A : Subgroup G} {ρ : Sec5Roles G A}
    {p : ℕ} (𝔠 : Sec5ConfigR ρ p) where
  t : ℕ
  ht : t.Prime ∧ t ≠ 2 ∧ t ≠ p
  x₁ : G
  hx₁ : x₁ ∈ ρ.X ∧ x₁ ≠ 1 ∧ 𝔠.P ≤ C x₁
  Tstar : Subgroup G
  hTstar : IsPGroup t Tstar ∧ A ≤ normalizer (Tstar : Set G) ∧
    Tstar ≤ centralizer ((𝔠.V ⊔ ρ.Y ⊔ zpowers x₁ : Subgroup G) : Set G) ∧
    ⁅Tstar, ρ.X⁆ = Tstar ∧ 𝔠.P ⊓ centralizer (Tstar : Set G) = 𝔠.V
  T : Subgroup G
  hT : Tstar ≤ T ∧ CFSG.ABGLocalTools.IsSylowOf t T (O (C x₁)) ∧ A ≤ normalizer (T : Set G) ∧
    ((T : Set G) * (𝔠.Q : Set G) = (𝔠.Q : Set G) * (T : Set G)) ∧
    ((T : Set G) * (𝔠.P : Set G) = (𝔠.P : Set G) * (T : Set G))
  hXP : 𝔠.P ≤ centralizer (ρ.X : Set G)
  hQ : CFSG.ABGLocalTools.IsSylowOf p 𝔠.Q (O (C x₁))

end CFSG.GH72

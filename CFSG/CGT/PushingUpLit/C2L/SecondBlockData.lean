module

public import CFSG.CGT.PushingUpLit.C2L.Gomi0
public import CFSG.Timmesfeld.RankOne.Defs
import CFSG.RankThree.PartOne.K1214.Basic

public section

namespace CFSG.CGT.PushingUpLit.C2L

open CFSG CFSG.ABGLocalTools CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2KSW
open scoped commutatorElement

abbrev zc {G : Type} [Group G] (Q : Subgroup G) : Subgroup G :=
  Q ⊓ Subgroup.centralizer (Q : Set G)

structure SecondBlockInput (G : Type) [Group G] [Finite G] (L M T : Subgroup G) (n : ℕ)
    (D D₂ : Subgroup G) (a : G) : Prop where
  D_def : D = Dc L T
  D_eq : oTwoIn (L ⊔ T) = D
  E_le : Ec L T ≤ D
  card_T_D : Nat.card T = 2 ^ n * Nat.card D
  T_le : T ≤ Rl L T ⊔ D
  ne_M : ¬ Subgroup.normalizer (D₂ : Set G) ≤ M
  D_dec : ∀ d ∈ D, ∃ v ∈ blockU L, ∃ e ∈ Ec L T, d = v * e
  card_D : Nat.card D = 2 ^ n * Nat.card (zc T)
  D₂_le : D₂ ≤ T
  T_le_N : T ≤ Subgroup.normalizer (D₂ : Set G)
  D_elem : CFSG.Open.IsElemAbelian 2 D
  D₂_elem : CFSG.Open.IsElemAbelian 2 D₂
  sup_eq : D ⊔ D₂ = T
  D₂_eq : D₂ = (zc T).map (MulAut.conj a).toMonoidHom ⊔ zc T
  relIndex_X : (zc T ⊓ (zc T).map (MulAut.conj a).toMonoidHom).relIndex (zc T) =
    D₂.relIndex T
  ti : ∀ S₁ S₂ : Subgroup G, IsSylowOf 2 S₁ (Subgroup.normalizer (D₂ : Set G)) →
    IsSylowOf 2 S₂ (Subgroup.normalizer (D₂ : Set G)) → S₁ ≠ S₂ → S₁ ⊓ S₂ ≤ D₂
  gomiH : GomiH D₂
  a_mem : a ∈ Subgroup.normalizer (D₂ : Set G)
  a_not : a ∉ Subgroup.normalizer (T : Set G)

structure BlockTwoFacts (G : Type) [Group G] (N D T L₂ : Subgroup G) (n : ℕ) : Prop where
  D_le : D ≤ L₂
  T_le : T ≤ L₂
  le_N : L₂ ≤ N
  normal : ∀ g ∈ N, ∀ x ∈ L₂, g * x * g⁻¹ ∈ L₂
  quot : ∃ φ : ↥L₂ →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
    Function.Surjective φ ∧ φ.ker = D.subgroupOf L₂ ∧
    (T.subgroupOf L₂).map φ = CFSG.Timmesfeld.upperUnipotent (GaloisField 2 n)
  gen : ∀ a ∈ N, a ∉ Subgroup.normalizer (T : Set G) →
    L₂ = T ⊔ T.map (MulAut.conj a).toMonoidHom

private theorem mem_normalizer_of_commute {G : Type} [Group G] [Finite G] {S : Subgroup G}
    {x : G} (h : ∀ z ∈ S, x * z = z * x) : x ∈ Subgroup.normalizer (S : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  have : x * z * x⁻¹ = z := by rw [h z hz]; group
  rwa [this]

namespace SecondBlockInput

variable {G : Type} [Group G] [Finite G] {L M T D D₂ : Subgroup G} {n : ℕ} {a : G}
  (h : SecondBlockInput G L M T n D D₂ a)
include h

theorem D₂_comm : ∀ x ∈ D₂, ∀ y ∈ D₂, x * y = y * x :=
  fun x hx y hy => congrArg Subtype.val (h.D₂_elem.1.is_comm.comm (⟨x, hx⟩ : D₂) ⟨y, hy⟩)

theorem zc_le_D₂ : zc T ≤ D₂ := h.D₂_eq ▸ le_sup_right

theorem X₂_le_D₂ : (zc T).map (MulAut.conj a).toMonoidHom ≤ D₂ := h.D₂_eq ▸ le_sup_left

theorem card_D₂_mul : Nat.card D₂ * Nat.card ↥(zc T ⊓ (zc T).map (MulAut.conj a).toMonoidHom) =
    Nat.card (zc T) * Nat.card (zc T) := by
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (A := (zc T).map (MulAut.conj a).toMonoidHom) (B := zc T)
    (fun _ hx => mem_normalizer_of_commute fun _ hz =>
      h.D₂_comm _ (h.zc_le_D₂ hx) _ (h.X₂_le_D₂ hz))
  have hc : Nat.card ((zc T).map (MulAut.conj a).toMonoidHom) = Nat.card (zc T) :=
    Subgroup.card_map_of_injective (MulAut.conj a).injective
  rw [← h.D₂_eq, hc, inf_comm] at hprod
  exact hprod

theorem card_T_D₂ : Nat.card T = 2 ^ n * Nat.card D₂ := by
  set X := zc T with hX
  set X₂ := X.map (MulAut.conj a).toMonoidHom with hX₂
  set k := D₂.relIndex T with hk
  have hz : 0 < Nat.card ↥(X ⊓ X₂) := Nat.card_pos
  have hx : 0 < Nat.card X := Nat.card_pos
  have h1 : k * Nat.card ↥(X ⊓ X₂) = Nat.card X := by
    have := Subgroup.relIndex_mul_card (H := X ⊓ X₂) (K := X)
    rw [inf_of_le_left (inf_le_left : X ⊓ X₂ ≤ X), h.relIndex_X] at this
    exact this
  have h2 : k * Nat.card D₂ = Nat.card T := by
    have := Subgroup.relIndex_mul_card (H := D₂) (K := T)
    rwa [inf_of_le_left h.D₂_le] at this
  have h3 := h.card_D₂_mul
  have h4 : Nat.card D₂ = Nat.card X * k := by
    apply Nat.eq_of_mul_eq_mul_right hz
    calc Nat.card D₂ * Nat.card ↥(X ⊓ X₂) = Nat.card X * Nat.card X := h3
      _ = Nat.card X * (k * Nat.card ↥(X ⊓ X₂)) := by rw [h1]
      _ = Nat.card X * k * Nat.card ↥(X ⊓ X₂) := by ring
  have h5 : Nat.card T = 2 ^ n * (2 ^ n * Nat.card X) := by
    rw [h.card_T_D, h.card_D]
  have h6 : k * k = 2 ^ n * 2 ^ n := by
    apply Nat.eq_of_mul_eq_mul_left hx
    calc Nat.card X * (k * k) = k * Nat.card D₂ := by rw [h4]; ring
      _ = Nat.card T := h2
      _ = Nat.card X * (2 ^ n * 2 ^ n) := by rw [h5]; ring
  have h7 : k = 2 ^ n := by
    have := (Nat.mul_self_inj (m := k) (n := 2 ^ n)).1 h6
    exact this
  rw [← h2, h7]

theorem card_D₂ : Nat.card D₂ =
    2 ^ (2 * n) * Nat.card ↥(zc T ⊓ (zc T).map (MulAut.conj a).toMonoidHom) := by
  set X := zc T with hX
  set X₂ := X.map (MulAut.conj a).toMonoidHom with hX₂
  have hz : 0 < Nat.card ↥(X ⊓ X₂) := Nat.card_pos
  have hk : D₂.relIndex T = 2 ^ n := by
    have h2 : D₂.relIndex T * Nat.card D₂ = Nat.card T := by
      have := Subgroup.relIndex_mul_card (H := D₂) (K := T)
      rwa [inf_of_le_left h.D₂_le] at this
    have h3 := h.card_T_D₂
    have hpos : 0 < Nat.card D₂ := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h2, h3]
  have h1 : 2 ^ n * Nat.card ↥(X ⊓ X₂) = Nat.card X := by
    have := Subgroup.relIndex_mul_card (H := X ⊓ X₂) (K := X)
    rw [inf_of_le_left (inf_le_left : X ⊓ X₂ ≤ X), h.relIndex_X, hk] at this
    exact this
  have h3 := h.card_D₂_mul
  apply Nat.eq_of_mul_eq_mul_right hz
  calc Nat.card D₂ * Nat.card ↥(X ⊓ X₂) = Nat.card X * Nat.card X := h3
    _ = (2 ^ n * Nat.card ↥(X ⊓ X₂)) * (2 ^ n * Nat.card ↥(X ⊓ X₂)) := by rw [h1]
    _ = 2 ^ (2 * n) * Nat.card ↥(X ⊓ X₂) * Nat.card ↥(X ⊓ X₂) := by ring

theorem exists_zc_not_mem (hn : 1 ≤ n) :
    ∃ x ∈ zc T, x ∉ (zc T).map (MulAut.conj a).toMonoidHom := by
  by_contra hcon
  set X := zc T with hX
  set X₂ := X.map (MulAut.conj a).toMonoidHom with hX₂
  have hXX₂ : X ⊓ X₂ = X := inf_of_le_left fun x hx => by_contra fun hx2 => hcon ⟨x, hx, hx2⟩
  have h1 : (X ⊓ X₂).relIndex X = 1 := by rw [hXX₂]; exact Subgroup.relIndex_self (H := X)
  rw [h.relIndex_X] at h1
  have h2 : D₂.relIndex T * Nat.card D₂ = Nat.card T := by
    have := Subgroup.relIndex_mul_card (H := D₂) (K := T)
    rwa [inf_of_le_left h.D₂_le] at this
  rw [h1, one_mul, h.card_T_D₂] at h2
  have hpos : 0 < Nat.card D₂ := Nat.card_pos
  have h3 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  nlinarith

theorem quot_elem : ∀ x ∈ T, ∀ y ∈ T, x * x ∈ D₂ ∧ ⁅x, y⁆ ∈ D₂ := by
  have hDT : D ≤ T := h.sup_eq ▸ le_sup_left
  have hDN : D ≤ Subgroup.normalizer (D₂ : Set G) := hDT.trans h.T_le_N
  have hdec : ∀ x ∈ T, ∃ e ∈ D₂, ∃ d ∈ D, e * d = x := by
    intro x hx
    have hx' : x ∈ D₂ ⊔ D := by
      rw [sup_comm, h.sup_eq]
      exact hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left D₂ D hDN] at hx'
    exact Set.mem_mul.1 hx'
  have hconj : ∀ d ∈ D, ∀ e ∈ D₂, d * e * d⁻¹ ∈ D₂ := fun d hd e he =>
    (Subgroup.mem_normalizer_iff.1 (hDN hd) e).1 he
  have hDcomm : ∀ d₁ ∈ D, ∀ d₂ ∈ D, d₁ * d₂ = d₂ * d₁ := fun d₁ hd₁ d₂ hd₂ =>
    congrArg Subtype.val (h.D_elem.1.is_comm.comm (⟨d₁, hd₁⟩ : D) ⟨d₂, hd₂⟩)
  have hDsq : ∀ d ∈ D, d * d = 1 := fun d hd => by
    have := h.D_elem.2 d hd
    rwa [pow_two] at this
  intro x hx y hy
  obtain ⟨e₁, he₁, d₁, hd₁, rfl⟩ := hdec x hx
  obtain ⟨e₂, he₂, d₂, hd₂, rfl⟩ := hdec y hy
  refine ⟨?_, ?_⟩
  · have e : e₁ * d₁ * (e₁ * d₁) = e₁ * (d₁ * e₁ * d₁⁻¹) * (d₁ * d₁) := by group
    rw [e, hDsq d₁ hd₁, mul_one]
    exact D₂.mul_mem he₁ (hconj d₁ hd₁ e₁ he₁)
  · have key : d₁ * d₂ * d₁⁻¹ = d₂ := by rw [hDcomm d₁ hd₁ d₂ hd₂]; group
    have e : ⁅e₁ * d₁, e₂ * d₂⁆ =
        e₁ * (d₁ * e₂ * d₁⁻¹) * (d₂ * e₁⁻¹ * d₂⁻¹) * e₂⁻¹ :=
      calc ⁅e₁ * d₁, e₂ * d₂⁆
          = e₁ * ((d₁ * e₂ * d₁⁻¹) * (d₁ * d₂ * d₁⁻¹)) * e₁⁻¹ * d₂⁻¹ * e₂⁻¹ := by
            simp only [commutatorElement_def]
            group
        _ = e₁ * ((d₁ * e₂ * d₁⁻¹) * d₂) * e₁⁻¹ * d₂⁻¹ * e₂⁻¹ := by rw [key]
        _ = e₁ * (d₁ * e₂ * d₁⁻¹) * (d₂ * e₁⁻¹ * d₂⁻¹) * e₂⁻¹ := by group
    rw [e]
    exact D₂.mul_mem (D₂.mul_mem (D₂.mul_mem he₁ (hconj d₁ hd₁ e₂ he₂))
      (hconj d₂ hd₂ e₁⁻¹ (D₂.inv_mem he₁))) (D₂.inv_mem he₂)

end SecondBlockInput

end CFSG.CGT.PushingUpLit.C2L

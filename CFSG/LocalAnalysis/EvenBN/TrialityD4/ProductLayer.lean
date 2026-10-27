module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductToolbox
public import CFSG.LocalAnalysis.EvenBN.Common.Diagonal
public import CFSG.LocalAnalysis.EvenBN.Common.RadicalRank
public import CFSG.LieType.Steinberg.CentralExt.RankOne
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import CFSG.Monster.B.TwoA.Sp8.A8

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.LocalAnalysis.EvenBN.Common
open CFSG.ABGLocalTools (IsSylowOf)
open scoped MatrixGroups Pointwise

section Defs

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {q : ℕ}

@[expose] noncomputable def eOne (d : TrialityD4Data L q) (t : G) (K : Subgroup G) : Subgroup G :=
  yamadaY₂ d t ⊓ K

@[expose] noncomputable def qThree (d : TrialityD4Data L q) (t : G) (K : Subgroup G) : Subgroup G :=
  prodX d t ⊓ K

@[expose] noncomputable def kThree (d : TrialityD4Data L q) (t : G) (K : Subgroup G) : Subgroup G :=
  oTwoPrimeRes (K ⊓ normalizer ((eOne d t K : Subgroup G) : Set G))

@[expose] noncomputable def nThree (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  oTwoPrimeRes (jZeroLayer d ⊓ normalizer ((yamadaY₂ d t : Subgroup G) : Set G))

@[expose] noncomputable def nTwo (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  nThree d t ⊔ yamadaM₆ d t

end Defs

namespace ProductLayerAux

section Odd

variable {G : Type*} [Group G]

theorem eq_one_of_pow_eq_one_of_mem_odd {B : Subgroup G} (hB : Odd (Nat.card B)) {x : G}
    (hx : x ∈ B) {k : ℕ} (hk : x ^ 2 ^ k = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf x ∣ Nat.card B := by
    have := orderOf_dvd_natCard (⟨x, hx⟩ : B)
    rwa [Subgroup.orderOf_mk] at this
  have h3 : Nat.Coprime (2 ^ k) (Nat.card B) := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hB)
  exact orderOf_eq_one_iff.1 ((h3.coprime_dvd_left h1).eq_one_of_dvd h2)

theorem inf_eq_bot_of_isPGroup_of_odd {A B : Subgroup G} (hA : IsPGroup 2 A)
    (hB : Odd (Nat.card B)) : A ⊓ B = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨k, hk⟩ := hA ⟨x, hx.1⟩
  have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
  exact mem_bot.2 (eq_one_of_pow_eq_one_of_mem_odd hB hx.2 hk')

end Odd

section SylowProd

variable {G : Type*} [Group G] [Finite G]

theorem commute_of_commutator_eq_bot {K K' : Subgroup G} (hcomm : ⁅K, K'⁆ = ⊥) :
    ∀ a ∈ K, ∀ b ∈ K', a * b = b * a := by
  intro a ha b hb
  have := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm ha
  exact (mem_centralizer_iff.1 this b hb).symm

theorem sup_le_normalizer_left_of_commutator_eq_bot {K K' : Subgroup G} (hcomm : ⁅K, K'⁆ = ⊥) :
    K ⊔ K' ≤ normalizer (K : Set G) := by
  refine sup_le le_normalizer fun y hy => ?_
  refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun a ha => ?_)
  exact (commute_of_commutator_eq_bot hcomm a ha y hy)

theorem sup_le_normalizer_right_of_commutator_eq_bot {K K' : Subgroup G} (hcomm : ⁅K, K'⁆ = ⊥) :
    K ⊔ K' ≤ normalizer (K' : Set G) := by
  refine sup_le (fun y hy => ?_) le_normalizer
  refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun b hb => ?_)
  exact (commute_of_commutator_eq_bot hcomm y hy b hb).symm

theorem isSylowOf_prod {K K' X : Subgroup G} (hcomm : ⁅K, K'⁆ = ⊥)
    (hodd : Odd (Nat.card (K ⊓ K' : Subgroup G))) (hX : IsSylowOf 2 X (K ⊔ K')) :
    IsSylowOf 2 (X ⊓ K) K ∧ IsSylowOf 2 (X ⊓ K') K' ∧ X = (X ⊓ K) ⊔ (X ⊓ K') ∧
      (X ⊓ K) ⊓ (X ⊓ K') = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcK := commute_of_commutator_eq_bot hcomm
  have hA : IsSylowOf 2 (X ⊓ K) K :=
    hX.inf_of_le_normalizer le_sup_left (sup_le_normalizer_left_of_commutator_eq_bot hcomm)
  have hB : IsSylowOf 2 (X ⊓ K') K' :=
    hX.inf_of_le_normalizer le_sup_right (sup_le_normalizer_right_of_commutator_eq_bot hcomm)
  have hinf : (X ⊓ K) ⊓ (X ⊓ K') = ⊥ := by
    have h1 : (X ⊓ K) ⊓ (X ⊓ K') ≤ K ⊓ K' := inf_le_inf inf_le_right inf_le_right
    have h2 : IsPGroup 2 ↥((X ⊓ K) ⊓ (X ⊓ K')) :=
      hX.isPGroup.to_le (inf_le_left.trans inf_le_left)
    have := inf_eq_bot_of_isPGroup_of_odd h2 hodd
    rwa [inf_eq_left.2 h1] at this
  refine ⟨hA, hB, ?_, hinf⟩
  have hAB : ∀ a ∈ X ⊓ K, ∀ b ∈ X ⊓ K', a * b = b * a := fun a ha b hb => hcK a ha.2 b hb.2
  obtain ⟨h1, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (X ⊓ K) (X ⊓ K') hAB
  obtain ⟨h2, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute K K' hcK
  rw [hinf, Subgroup.card_bot, mul_one] at h1
  refine (eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left) ?_).symm
  rw [h1, hX.card_eq, hA.card_eq, hB.card_eq]
  have hKpos : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hK'pos : Nat.card K' ≠ 0 := Nat.card_pos.ne'
  have hEpos : Nat.card (K ⊔ K' : Subgroup G) ≠ 0 := Nat.card_pos.ne'
  have h3 : (Nat.card (K ⊔ K' : Subgroup G)).factorization 2 =
      (Nat.card K).factorization 2 + (Nat.card K').factorization 2 := by
    have e := congrArg (fun n => n.factorization 2) h2
    simp only [Nat.factorization_mul hEpos Nat.card_pos.ne', Nat.factorization_mul hKpos hK'pos,
      Finsupp.add_apply] at e
    have : (Nat.card (K ⊓ K' : Subgroup G)).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hodd.not_two_dvd_nat
    omega
  rw [h3, pow_add]

end SylowProd

section Swap

variable {G : Type*} [Group G]

theorem invol_conj_mul {t : G} (ht : t * t = 1) (a b : G) :
    t * (a * b) * t = (t * a * t) * (t * b * t) := by
  rw [show (t * a * t) * (t * b * t) = t * a * (t * t) * b * t by group, ht]
  group

theorem invol_conj_invol {t : G} (ht : t * t = 1) (a : G) : t * (t * a * t) * t = a := by
  rw [show t * (t * a * t) * t = (t * t) * a * (t * t) by group, ht]
  group

theorem invol_conj_inv {t : G} (ht : t * t = 1) (a : G) : t * a⁻¹ * t = (t * a * t)⁻¹ := by
  rw [show (t * a * t)⁻¹ = t⁻¹ * a⁻¹ * t⁻¹ by group, inv_eq_of_mul_eq_one_right ht]

theorem mem_conjG_iff {A : Subgroup G} {t x : G} (ht : t * t = 1) :
    x ∈ Aᵍ[t] ↔ t * x * t ∈ A := by
  rw [Common.mem_map_conj_inv_iff, inv_eq_of_mul_eq_one_right ht]

theorem conj_mem_conjG {A : Subgroup G} {t a : G} (ht : t * t = 1) (ha : a ∈ A) :
    t * a * t ∈ Aᵍ[t] := by
  rw [mem_conjG_iff ht, show t * (t * a * t) * t = (t * t) * a * (t * t) by group, ht, one_mul,
    mul_one]
  exact ha

theorem exists_eq_mul_conj_of_mem_centralizer [Finite G] {A : Subgroup G} {t : G} (ht : t * t = 1)
    (hcomm : ⁅A, Aᵍ[t]⁆ = ⊥) (hinf : A ⊓ Aᵍ[t] = ⊥) {x : G} (hx : x ∈ A ⊔ Aᵍ[t])
    (hxt : t * x = x * t) : ∃ a ∈ A, x = a * (t * a * t) := by
  have hc := commute_of_commutator_eq_bot hcomm
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A Aᵍ[t] hc
  have hx' : x ∈ ((A ⊔ Aᵍ[t] : Subgroup G) : Set G) := hx
  rw [hset] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  have hb' : t * b * t ∈ A := (mem_conjG_iff ht).1 hb
  have hta : t * a * t ∈ Aᵍ[t] := conj_mem_conjG ht ha
  have h1 : t * (a * b) * t = (t * a * t) * (t * b * t) := by
    rw [show (t * a * t) * (t * b * t) = t * a * (t * t) * b * t by group, ht]
    group
  have h2 : t * (a * b) * t = a * b := by
    calc t * (a * b) * t = (t * (a * b)) * t := rfl
      _ = ((a * b) * t) * t := by rw [hxt]
      _ = a * b := by rw [mul_assoc, ht, mul_one]
  have h3 : (t * a * t) * (t * b * t) = (t * b * t) * (t * a * t) := (hc _ hb' _ hta).symm
  have h4 : (t * b * t)⁻¹ * a = (t * a * t) * b⁻¹ := by
    calc (t * b * t)⁻¹ * a = (t * b * t)⁻¹ * (a * b) * b⁻¹ := by group
      _ = (t * b * t)⁻¹ * ((t * b * t) * (t * a * t)) * b⁻¹ := by rw [← h2, h1, h3]
      _ = (t * a * t) * b⁻¹ := by group
  have h5 : (t * b * t)⁻¹ * a ∈ A ⊓ Aᵍ[t] :=
    mem_inf.2 ⟨mul_mem (inv_mem hb') ha, h4 ▸ mul_mem hta (inv_mem hb)⟩
  rw [hinf, mem_bot] at h5
  have h6 : a = t * b * t := by
    calc a = (t * b * t) * ((t * b * t)⁻¹ * a) := by group
      _ = t * b * t := by rw [h5, mul_one]
  have h7 : b = t * a * t := by
    rw [h6, show t * (t * b * t) * t = (t * t) * b * (t * t) by group, ht, one_mul, mul_one]
  exact ⟨a, ha, by rw [h7]⟩

end Swap

section HeisAux

variable {G : Type*} [Group G] [Finite G] {Q : Subgroup G} {k : ℕ}

theorem heis_commutator_mem (hQ : HeisLike Q k) {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) :
    x * y * x⁻¹ * y⁻¹ ∈ Q ⊓ centralizer (Q : Set G) := by
  set Z : Subgroup G := Q ⊓ centralizer (Q : Set G) with hZ
  have hxx : x * x ∈ Z := hQ.mul_self_mem x hx
  have hyy : y * y ∈ Z := hQ.mul_self_mem y hy
  have hxy : (x * y) * (x * y) ∈ Z := hQ.mul_self_mem _ (mul_mem hx hy)
  have hc1 : y⁻¹ * (x * x)⁻¹ = (x * x)⁻¹ * y⁻¹ := by
    have := mem_centralizer_iff.1 (inv_mem hxx).2 y⁻¹ (inv_mem hy)
    exact this
  have e : x * y * x⁻¹ * y⁻¹ = ((x * y) * (x * y)) * (x * x)⁻¹ * (y * y)⁻¹ := by
    calc x * y * x⁻¹ * y⁻¹ = ((x * y) * (x * y)) * (y⁻¹ * (x * x)⁻¹ * y⁻¹) := by group
      _ = ((x * y) * (x * y)) * ((x * x)⁻¹ * y⁻¹ * y⁻¹) := by rw [hc1]
      _ = ((x * y) * (x * y)) * (x * x)⁻¹ * (y * y)⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem hxy (inv_mem hxx)) (inv_mem hyy)

theorem heis_k_pos (hQ : HeisLike Q k) : 0 < k := by
  rw [← hQ.card_center]
  exact Nat.card_pos

theorem heis_card_centralizer_ge (hQ : HeisLike Q k) {a : G} (ha : a ∈ Q) :
    k ^ 2 ≤ Nat.card (Q ⊓ centralizer ({a} : Set G) : Subgroup G) := by
  have hDZ : ⁅Q, Q⁆ ≤ Q ⊓ centralizer (Q : Set G) := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    exact heis_commutator_mem hQ hx hy
  have h := Common.card_le_card_inf_centralizer_mul_card hDZ inf_le_right le_rfl ha
  rw [hQ.card_eq, hQ.card_center] at h
  have hk := heis_k_pos hQ
  have h' : k ^ 2 * k ≤ Nat.card (Q ⊓ centralizer ({a} : Set G) : Subgroup G) * k := by
    calc k ^ 2 * k = k ^ 3 := by ring
      _ ≤ _ := h
  exact Nat.le_of_mul_le_mul_right h' hk

theorem heis_card_centralizer_le (hQ : HeisLike Q k) {a : G} (ha : a ∈ Q)
    (haZ : a ∉ centralizer (Q : Set G)) :
    Nat.card (Q ⊓ centralizer ({a} : Set G) : Subgroup G) ≤ k ^ 2 := by
  have hk := heis_k_pos hQ
  obtain ⟨b, hb, hab⟩ : ∃ b ∈ Q, b * a ≠ a * b := by
    by_contra hcon
    push Not at hcon
    exact haZ (mem_centralizer_iff.2 hcon)
  set Ca : Subgroup G := Q ⊓ centralizer ({a} : Set G) with hCa
  set Cb : Subgroup G := Q ⊓ centralizer ({b} : Set G) with hCb
  have hbge := heis_card_centralizer_ge hQ hb
  have hinf : Ca ⊓ Cb ≤ Q ⊓ centralizer (Q : Set G) := by
    intro c hc
    refine ⟨hc.1.1, ?_⟩
    have h1 : c * a = a * c := mem_centralizer_singleton_iff.1 hc.1.2
    have h2 : c * b = b * c := mem_centralizer_singleton_iff.1 hc.2.2
    exact (hQ.mem_center a ha b hb (fun h => hab h.symm) c hc.1.1 h1 h2).2
  have hcardinf : Nat.card (Ca ⊓ Cb : Subgroup G) ≤ k := by
    rw [← hQ.card_center]
    exact Subgroup.card_le_of_le hinf
  have h1 := ncard_mul_mul_card_inf Ca Cb
  have h2 : ((Ca : Set G) * (Cb : Set G)).ncard ≤ k ^ 3 := by
    rw [← hQ.card_eq, ← Nat.card_coe_set_eq]
    refine (Set.ncard_le_ncard ?_ (Set.toFinite _)).trans_eq (Nat.card_coe_set_eq (Q : Set G)).symm
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact mul_mem hx.1 hy.1
  have h3 : Nat.card Ca * k ^ 2 ≤ k ^ 3 * k := by
    calc Nat.card Ca * k ^ 2 ≤ Nat.card Ca * Nat.card Cb := Nat.mul_le_mul_left _ hbge
      _ = ((Ca : Set G) * (Cb : Set G)).ncard * Nat.card (Ca ⊓ Cb : Subgroup G) := h1.symm
      _ ≤ k ^ 3 * k := Nat.mul_le_mul h2 hcardinf
  have h4 : Nat.card Ca * k ^ 2 ≤ k ^ 2 * k ^ 2 := by
    calc Nat.card Ca * k ^ 2 ≤ k ^ 3 * k := h3
      _ = k ^ 2 * k ^ 2 := by ring
  exact Nat.le_of_mul_le_mul_right h4 (by positivity)

theorem heis_card_le_of_abelian (hQ : HeisLike Q k) {B : Subgroup G} (hBQ : B ≤ Q)
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) : Nat.card B ≤ k ^ 2 := by
  by_cases hcen : ∀ x ∈ B, x ∈ centralizer (Q : Set G)
  · have : B ≤ Q ⊓ centralizer (Q : Set G) := fun x hx => ⟨hBQ hx, hcen x hx⟩
    calc Nat.card B ≤ Nat.card (Q ⊓ centralizer (Q : Set G) : Subgroup G) :=
          Subgroup.card_le_of_le this
      _ = k := hQ.card_center
      _ ≤ k ^ 2 := by
        have := heis_k_pos hQ
        nlinarith
  · push Not at hcen
    obtain ⟨a, ha, haZ⟩ := hcen
    have hle : B ≤ Q ⊓ centralizer ({a} : Set G) := fun x hx =>
      ⟨hBQ hx, mem_centralizer_singleton_iff.2 (hB a ha x hx).symm⟩
    exact (Subgroup.card_le_of_le hle).trans (heis_card_centralizer_le hQ (hBQ ha) haZ)

theorem heis_center_le_of_abelian_of_card_eq (hQ : HeisLike Q k) {B : Subgroup G}
    (hBQ : B ≤ Q) (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hcard : Nat.card B = k ^ 2) :
    Q ⊓ centralizer (Q : Set G) ≤ B := by
  have hBZ : ∀ x ∈ B ⊔ (Q ⊓ centralizer (Q : Set G)), ∀ y ∈ B ⊔ (Q ⊓ centralizer (Q : Set G)),
      x * y = y * x := by
    have hcc : ∀ a ∈ B, ∀ z ∈ Q ⊓ centralizer (Q : Set G), a * z = z * a :=
      fun a ha z hz => mem_centralizer_iff.1 hz.2 a (hBQ ha)
    obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute B
      (Q ⊓ centralizer (Q : Set G)) hcc
    intro x hx y hy
    have hx' : x ∈ ((B ⊔ (Q ⊓ centralizer (Q : Set G)) : Subgroup G) : Set G) := hx
    have hy' : y ∈ ((B ⊔ (Q ⊓ centralizer (Q : Set G)) : Subgroup G) : Set G) := hy
    rw [hset] at hx' hy'
    obtain ⟨b₁, hb₁, z₁, hz₁, rfl⟩ := hx'
    obtain ⟨b₂, hb₂, z₂, hz₂, rfl⟩ := hy'
    have hz₁b₂ : z₁ * b₂ = b₂ * z₁ := (mem_centralizer_iff.1 hz₁.2 b₂ (hBQ hb₂)).symm
    have hz₂b₁ : z₂ * b₁ = b₁ * z₂ := (mem_centralizer_iff.1 hz₂.2 b₁ (hBQ hb₁)).symm
    have hz₁z₂ : z₁ * z₂ = z₂ * z₁ := mem_centralizer_iff.1 hz₂.2 z₁ hz₁.1
    calc b₁ * z₁ * (b₂ * z₂) = (b₁ * b₂) * (z₁ * z₂) := by
          rw [show b₁ * z₁ * (b₂ * z₂) = b₁ * (z₁ * b₂) * z₂ by group, hz₁b₂]
          group
      _ = (b₂ * b₁) * (z₂ * z₁) := by rw [hB b₁ hb₁ b₂ hb₂, hz₁z₂]
      _ = b₂ * z₂ * (b₁ * z₁) := by
          rw [show b₂ * z₂ * (b₁ * z₁) = b₂ * (z₂ * b₁) * z₁ by group, hz₂b₁]
          group
  have hle : B ⊔ (Q ⊓ centralizer (Q : Set G)) ≤ Q := sup_le hBQ inf_le_left
  have h1 := heis_card_le_of_abelian hQ hle hBZ
  have h2 : B ⊔ (Q ⊓ centralizer (Q : Set G)) = B :=
    (eq_of_le_of_card_ge le_sup_left (hcard ▸ h1)).symm
  exact le_sup_right.trans h2.le

theorem heis_normal_subgroupOf_of_center_le (hQ : HeisLike Q k) {B : Subgroup G}
    (hBQ : B ≤ Q) (hZB : Q ⊓ centralizer (Q : Set G) ≤ B) : (B.subgroupOf Q).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_subgroupOf] at hn ⊢
  have hc := heis_commutator_mem hQ g.2 (hBQ hn)
  have e : (g : G) * n * (g : G)⁻¹ = ((g : G) * n * (g : G)⁻¹ * (n : G)⁻¹) * n := by group
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [e]
  exact mul_mem (hZB hc) hn

end HeisAux

section AbstractLayer

variable {Y : Type*} [Group Y] [Finite Y]

theorem exists_component_lift {N : Subgroup Y} [N.Normal]
    (hNO : ∀ a ∈ CFSG.oddCore Y, ∀ n ∈ N, a * n = n * a)
    {C : Subgroup (Y ⧸ CFSG.oddCore Y)} (hC : CFSG.IsComponent C)
    (hCN : C ≤ N.map (QuotientGroup.mk' (CFSG.oddCore Y))) :
    ∃ K : Subgroup Y, CFSG.IsComponent K ∧ K ≤ N ∧
      K.map (QuotientGroup.mk' (CFSG.oddCore Y)) = C := by
  classical
  set π := QuotientGroup.mk' (CFSG.oddCore Y) with hπ
  set Nt := N ⊓ C.comap π with hNt
  let φ : Nt →* C := (π.domRestrict Nt).codRestrict C fun x => (mem_comap.1 x.2.2)
  have hφ : ∀ x : Nt, (φ x : Y ⧸ CFSG.oddCore Y) = π x := fun _ => rfl
  have hφs : Function.Surjective φ := by
    intro c
    obtain ⟨n, hn, hnc⟩ := hCN c.2
    refine ⟨⟨n, hn, (show π n ∈ C by rw [hnc]; exact c.2)⟩, Subtype.ext ?_⟩
    rw [hφ]
    exact hnc
  have hker : φ.ker ≤ center Nt := by
    intro x hx
    have h1 : (x : Y) ∈ CFSG.oddCore Y := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
      rw [hφ, OneMemClass.coe_one, hπ, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at this
      exact this
    exact mem_center_iff.2 fun y => Subtype.ext (hNO _ h1 _ y.2.1).symm
  obtain ⟨-, -, hsurj⟩ := CFSG.LocalCores.central_extension_derived_of_surjective φ hφs hker
    hC.1.1
  have hq := CFSG.LocalCores.quasisimple_central_extension_derived_of_surjective φ hφs hker hC.1
  set C₁ := (commutator Nt).map Nt.subtype with hC₁
  have hC₁c : CFSG.IsComponent C₁ := by
    refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((commutator Nt).equivMapOfInjective Nt.subtype Nt.subtype_injective) hq, ?_⟩
    have hNts : Nt.IsSubnormal := (Normal.isSubnormal ‹N.Normal›).inf (hC.2.comap π)
    have hle : C₁ ≤ Nt := map_subtype_le _
    refine IsSubnormal.step C₁ Nt hle hNts ?_
    have : (commutator Nt).Normal := inferInstance
    have e : C₁.subgroupOf Nt = commutator Nt :=
      comap_map_eq_self_of_injective Nt.subtype_injective _
    rw [e]
    exact this
  refine ⟨C₁, hC₁c, (map_subtype_le _).trans inf_le_left, ?_⟩
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    have hyNt : y ∈ Nt := map_subtype_le _ hy
    exact mem_comap.1 hyNt.2
  · intro c hc
    obtain ⟨x, hx⟩ := hsurj ⟨c, hc⟩
    exact ⟨((x : Nt) : Y), ⟨x, x.2, rfl⟩, congrArg Subtype.val hx⟩

theorem map_conj_map {Z : Type*} [Group Z] (π : Y →* Z) (A : Subgroup Y) (g : Y) :
    (A.map (MulAut.conj g).toMonoidHom).map π =
      (A.map π).map (MulAut.conj (π g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem center_map_conj_eq_bot {A : Subgroup Y} (g : Y) (hA : center A = ⊥) :
    center (A.map (MulAut.conj g).toMonoidHom) = ⊥ := by
  have e := map_center_eq (A.equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective)
  rw [hA, Subgroup.map_bot] at e
  exact e.symm

theorem eq_one_of_mem_center_sup {A B : Subgroup Y} (hAB : ⁅A, B⁆ = ⊥) (hA : center A = ⊥)
    (hB : center B = ⊥) {w : Y} (hw : w ∈ A ⊔ B) (hwc : ∀ x ∈ A ⊔ B, w * x = x * w) : w = 1 := by
  have hc := commute_of_commutator_eq_bot hAB
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hc
  have hw' : w ∈ ((A ⊔ B : Subgroup Y) : Set Y) := hw
  rw [hset] at hw'
  obtain ⟨a, ha, b, hb, rfl⟩ := hw'
  have ha1 : a = 1 := by
    have h1 : (⟨a, ha⟩ : A) ∈ center A := by
      rw [mem_center_iff]
      intro g
      have h2 : a * b * g = g * (a * b) := hwc g (mem_sup_left g.2)
      have h3 : (g : Y) * b = b * g := hc g g.2 b hb
      apply Subtype.ext
      change (g : Y) * a = a * g
      have e1 : (a * g) * b = (g * a) * b := by
        calc (a * g) * b = a * (g * b) := by rw [mul_assoc]
          _ = a * (b * g) := by rw [h3]
          _ = (a * b) * g := by rw [mul_assoc]
          _ = g * (a * b) := h2
          _ = (g * a) * b := by rw [mul_assoc]
      exact (mul_right_cancel e1).symm
    rw [hA, mem_bot] at h1
    exact congrArg Subtype.val h1
  have hb1 : b = 1 := by
    have h1 : (⟨b, hb⟩ : B) ∈ center B := by
      rw [mem_center_iff]
      intro g
      have h2 : a * b * g = g * (a * b) := hwc g (mem_sup_right g.2)
      have h3 : a * (g : Y) = g * a := hc a ha g g.2
      apply Subtype.ext
      change (g : Y) * b = b * g
      have e1 : a * (b * g) = a * (g * b) := by
        calc a * (b * g) = (a * b) * g := by rw [mul_assoc]
          _ = g * (a * b) := h2
          _ = (g * a) * b := by rw [mul_assoc]
          _ = (a * g) * b := by rw [h3]
          _ = a * (g * b) := by rw [mul_assoc]
      exact (mul_left_cancel e1).symm
    rw [hB, mem_bot] at h1
    exact congrArg Subtype.val h1
  rw [ha1, hb1]
  exact one_mul 1

theorem layer_decomposition {s : Y} (hs : s * s = 1)
    {Kc : Subgroup (Y ⧸ CFSG.oddCore Y)} (hKc : CFSG.IsComponent Kc) (hZ : center Kc = ⊥)
    (hEO : ∀ a ∈ CFSG.oddCore Y, ∀ e ∈ CFSG.layer Y, a * e = e * a)
    (hEmap : (CFSG.layer Y).map (QuotientGroup.mk' (CFSG.oddCore Y)) =
      Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore Y) s)).toMonoidHom)
    (hne : Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore Y) s)).toMonoidHom ≠ Kc)
    (hcomm : ⁅Kc, Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore Y) s)).toMonoidHom⁆ = ⊥) :
    (∃ K : Subgroup Y, CFSG.IsComponent K ∧ K ≤ CFSG.layer Y ∧
      K.map (MulAut.conj s⁻¹).toMonoidHom ≠ K ∧
      ⁅K, K.map (MulAut.conj s⁻¹).toMonoidHom⁆ = ⊥ ∧
      CFSG.layer Y = K ⊔ K.map (MulAut.conj s⁻¹).toMonoidHom) ∧
    (∀ z ∈ CFSG.layer Y, (∀ e ∈ CFSG.layer Y, z * e = e * z) → z ∈ CFSG.oddCore Y) := by
  classical
  set O := CFSG.oddCore Y with hO
  set π := QuotientGroup.mk' O with hπ
  set sb := π s with hsb
  set Kc' := Kc.map (MulAut.conj sb).toMonoidHom with hKc'
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hsb2 : sb * sb = 1 := by rw [hsb, ← map_mul, hs, map_one]
  have hsbi : sb⁻¹ = sb := inv_eq_of_mul_eq_one_right hsb2
  have hEnorm : (CFSG.layer Y).Normal := by
    have := CFSG.LocalCores.layer_characteristic (G := Y)
    exact normal_of_characteristic _
  have hKc'c : CFSG.IsComponent Kc' := CFSG.LocalCores.isComponent_map_mulEquiv _ hKc
  have hZ' : center Kc' = ⊥ := center_map_conj_eq_bot sb hZ
  have hcenter : ∀ z ∈ CFSG.layer Y, (∀ e ∈ CFSG.layer Y, z * e = e * z) → z ∈ O := by
    intro z hz hzc
    have hzπ : π z ∈ Kc ⊔ Kc' := hEmap ▸ ⟨z, hz, rfl⟩
    have h1 : π z = 1 := by
      refine eq_one_of_mem_center_sup hcomm hZ hZ' hzπ fun x hx => ?_
      rw [← hEmap] at hx
      obtain ⟨e, he, rfl⟩ := hx
      rw [← map_mul, ← map_mul, hzc e he]
    exact (QuotientGroup.eq_one_iff _).1 h1
  refine ⟨?_, hcenter⟩
  haveI := hEnorm
  obtain ⟨K, hK, hKE, hKπ⟩ := exists_component_lift (N := CFSG.layer Y) hEO hKc
    (hEmap ▸ le_sup_left)
  have hKs : CFSG.IsComponent (K.map (MulAut.conj s⁻¹).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv _ hK
  have hKsπ : (K.map (MulAut.conj s⁻¹).toMonoidHom).map π = Kc' := by
    rw [map_conj_map, hKπ, map_inv, hsbi]
  have hKsE : K.map (MulAut.conj s⁻¹).toMonoidHom ≤ CFSG.layer Y := by
    rintro _ ⟨k, hk, rfl⟩
    exact hEnorm.conj_mem k (hKE hk) s⁻¹
  have hne' : K.map (MulAut.conj s⁻¹).toMonoidHom ≠ K := by
    intro h
    apply hne
    rw [← hKsπ, h, hKπ]
  have hcomm' : ⁅K, K.map (MulAut.conj s⁻¹).toMonoidHom⁆ = ⊥ := by
    have hle : ⁅K, K.map (MulAut.conj s⁻¹).toMonoidHom⁆ ≤ O := by
      have h1 : (⁅K, K.map (MulAut.conj s⁻¹).toMonoidHom⁆).map π = ⊥ := by
        rw [Subgroup.map_commutator, hKπ, hKsπ]
        exact hcomm
      rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at h1
      exact h1
    have hdouble : ⁅⁅K, K.map (MulAut.conj s⁻¹).toMonoidHom⁆, K⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [mem_centralizer_iff]
      intro k hk
      exact (hEO x (hle hx) k (hKE hk)).symm
    exact CFSG.LocalCores.perfect_double_commutator hK.1.1 hdouble
  refine ⟨K, hK, hKE, hne', hcomm', ?_⟩
  apply le_antisymm _ (sup_le hKE hKsE)
  set B := K ⊔ K.map (MulAut.conj s⁻¹).toMonoidHom with hB
  have hBE : B ≤ CFSG.layer Y := sup_le hKE hKsE
  have hπB : B.map π = Kc ⊔ Kc' := by rw [hB, Subgroup.map_sup, hKπ, hKsπ]
  have hdec : ∀ e ∈ CFSG.layer Y, ∃ b ∈ B, b⁻¹ * e ∈ O := by
    intro e he
    have : π e ∈ B.map π := by rw [hπB, ← hEmap]; exact ⟨e, he, rfl⟩
    obtain ⟨b, hb, hbe⟩ := this
    refine ⟨b, hb, ?_⟩
    have h1 : π (b⁻¹ * e) = 1 := by rw [map_mul, map_inv, hbe, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hcomm_le : ⁅CFSG.layer Y, CFSG.layer Y⁆ ≤ B := by
    rw [Subgroup.commutator_le]
    intro e₁ he₁ e₂ he₂
    obtain ⟨b₁, hb₁, hz₁⟩ := hdec e₁ he₁
    obtain ⟨b₂, hb₂, hz₂⟩ := hdec e₂ he₂
    have he₁' : e₁ = b₁ * (b₁⁻¹ * e₁) := by group
    have he₂' : e₂ = b₂ * (b₂⁻¹ * e₂) := by group
    have hzE₁ : b₁⁻¹ * e₁ ∈ CFSG.layer Y := mul_mem (inv_mem (hBE hb₁)) he₁
    have hzE₂ : b₂⁻¹ * e₂ ∈ CFSG.layer Y := mul_mem (inv_mem (hBE hb₂)) he₂
    have c1 : (b₁⁻¹ * e₁) * b₂ = b₂ * (b₁⁻¹ * e₁) := hEO _ hz₁ b₂ (hBE hb₂)
    have c2 : (b₁⁻¹ * e₁) * (b₂⁻¹ * e₂) = (b₂⁻¹ * e₂) * (b₁⁻¹ * e₁) := hEO _ hz₁ _ hzE₂
    have c3 : (b₂⁻¹ * e₂) * b₁ = b₁ * (b₂⁻¹ * e₂) := hEO _ hz₂ b₁ (hBE hb₁)
    rw [he₁', he₂']
    rw [commutatorElement_mul_mul_of_commute' c1 c2 c3]
    exact Subgroup.commutator_mem_commutator hb₁ hb₂ |> fun h => (Subgroup.commutator_le_self B) h
  calc CFSG.layer Y = ⁅CFSG.layer Y, CFSG.layer Y⁆ := (CFSG.LocalCores.layer_perfect (G := Y)).symm
    _ ≤ B := hcomm_le

end AbstractLayer

section LayerG

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem exists_layerComponent (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) :
    ∃ K : Subgroup G, IsLayerComponent d t K ∧
      ∀ z ∈ jZeroLayer d, (∀ e ∈ jZeroLayer d, z * e = e * z) →
        z ∈ (CFSG.oddCore (jZeroCentralizer d)).map (jZeroCentralizer d).subtype := by
  obtain ⟨Kc, hKc, hZ, -, -, hEO, hEmap, -, hcase⟩ := hp.layer
  rcases hcase with ⟨heq, hlie⟩ | ⟨hne, hcomm⟩
  · exact absurd ⟨Kc, hKc, heq, hlie⟩ hp.not_field
  · set H := jZeroCentralizer d with hH
    have htH : t ∈ H := h.t_mem_centralizer_J₀ d
    set s : H := ⟨t, htH⟩ with hs
    have hs2 : s * s = 1 := Subtype.ext h.t_mul_t
    obtain ⟨⟨K₁, hK₁, hK₁E, hK₁ne, hK₁c, hK₁lay⟩, hcenter⟩ :=
      layer_decomposition (Y := H) hs2 hKc hZ hEO hEmap hne hcomm
    have hconj : ∀ A : Subgroup H, (A.map (MulAut.conj s⁻¹).toMonoidHom).map H.subtype =
        (A.map H.subtype)ᵍ[t] := by
      intro A
      rw [map_conj_map]
      rfl
    refine ⟨K₁.map H.subtype, ⟨map_subtype_le _, ?_, ?_, ?_, ?_⟩, ?_⟩
    · have : (K₁.map H.subtype).subgroupOf H = K₁ :=
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
      rw [this]
      exact hK₁
    · intro heq
      apply hK₁ne
      apply Subgroup.map_injective H.subtype_injective
      rw [hconj]
      exact heq
    · rw [← hconj, ← Subgroup.map_commutator, hK₁c, Subgroup.map_bot]
    · rw [← hconj, ← Subgroup.map_sup]
      change CFSG.inSubgroup CFSG.layer H = _
      unfold CFSG.inSubgroup
      rw [hK₁lay]
    · intro z hz hzc
      obtain ⟨z₀, hz₀, rfl⟩ := hz
      refine ⟨z₀, hcenter z₀ hz₀ fun e he => Subtype.ext ?_, rfl⟩
      exact hzc _ ⟨e, he, rfl⟩

end LayerG

section LayerComponent

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem odd_card_zc_jZeroLayer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) : Odd (Nat.card (zc (jZeroLayer d))) := by
  obtain ⟨-, -, hcen⟩ := exists_layerComponent h d hp
  refine Odd.of_dvd_nat (Setup.odd_card_oddCore_map (jZeroCentralizer d)) ?_
  refine Subgroup.card_dvd_of_le fun z hz => hcen z hz.1 fun e he => ?_
  exact (mem_centralizer_iff.1 hz.2 e he).symm

theorem isLayerComponent_isQuasisimple {d : TrialityD4Data L (2 ^ f)} {K : Subgroup G}
    (hK : IsLayerComponent d t K) : CFSG.IsQuasisimple ↥K :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hK.le) hK.isComponent.1

theorem isLayerComponent_perfect {d : TrialityD4Data L (2 ^ f)} {K : Subgroup G}
    (hK : IsLayerComponent d t K) : ⁅K, K⁆ = K :=
  (isPerfect_subgroup_iff_commutator_eq K).1 (isLayerComponent_isQuasisimple hK).1

end LayerComponent

section DiagGeneric

variable {G : Type*} [Group G] [Finite G]

theorem commutator_sup_le_of_commute {A T : Subgroup G} (hAT : ∀ a ∈ A, ∀ c ∈ T, a * c = c * a)
    (hT : ∀ c ∈ T, ∀ d ∈ T, c * d = d * c) : ⁅A ⊔ T, A ⊔ T⁆ ≤ ⁅A, A⁆ := by
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A T hAT
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hx' : x ∈ ((A ⊔ T : Subgroup G) : Set G) := hx
  have hy' : y ∈ ((A ⊔ T : Subgroup G) : Set G) := hy
  rw [hset] at hx' hy'
  obtain ⟨a, ha, c, hc, rfl⟩ := hx'
  obtain ⟨b, hb, d, hd, rfl⟩ := hy'
  rw [commutatorElement_mul_mul_of_commute' (hAT b hb c hc).symm (hT c hc d hd)
    (hAT a ha d hd).symm]
  exact Subgroup.commutator_mem_commutator ha hb

theorem le_commutator_of_perfect_of_le_sup {P A T : Subgroup G} (hP : ⁅P, P⁆ = P)
    (hPAT : P ≤ A ⊔ T) (hAT : ∀ a ∈ A, ∀ c ∈ T, a * c = c * a)
    (hT : ∀ c ∈ T, ∀ d ∈ T, c * d = d * c) : P ≤ ⁅A, A⁆ := by
  calc P = ⁅P, P⁆ := hP.symm
    _ ≤ ⁅A ⊔ T, A ⊔ T⁆ := Subgroup.commutator_mono hPAT hPAT
    _ ≤ ⁅A, A⁆ := commutator_sup_le_of_commute hAT hT

theorem exists_diag_mul_of_commute {K : Subgroup G} {t : G} (ht : t * t = 1)
    (hcomm : ⁅K, Kᵍ[t]⁆ = ⊥) {c : G} (hc : c ∈ K ⊔ Kᵍ[t]) (hct : t * c = c * t) :
    ∃ k ∈ K, ∃ z ∈ K ⊓ Kᵍ[t], c = (k * (t * k * t)) * z := by
  have hcc := commute_of_commutator_eq_bot hcomm
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute K Kᵍ[t] hcc
  have hc' : c ∈ ((K ⊔ Kᵍ[t] : Subgroup G) : Set G) := hc
  rw [hset] at hc'
  obtain ⟨k, hk, k', hk', rfl⟩ := hc'
  have hk'' : t * k' * t ∈ K := (mem_conjG_iff ht).1 hk'
  have hk₁ : t * k * t ∈ Kᵍ[t] := conj_mem_conjG ht hk
  have e1 : t * (k * k') * t = (t * k * t) * (t * k' * t) := by
    rw [show (t * k * t) * (t * k' * t) = t * k * (t * t) * k' * t by group, ht]
    group
  have e2 : t * (k * k') * t = k * k' := by
    calc t * (k * k') * t = ((t * (k * k')) * t) := rfl
      _ = ((k * k') * t) * t := by rw [hct]
      _ = k * k' := by rw [mul_assoc, ht, mul_one]
  have e3 : (t * k * t) * (t * k' * t) = (t * k' * t) * (t * k * t) := (hcc _ hk'' _ hk₁).symm
  have e4 : (t * k' * t)⁻¹ * k = (t * k * t) * k'⁻¹ := by
    calc (t * k' * t)⁻¹ * k = (t * k' * t)⁻¹ * (k * k') * k'⁻¹ := by group
      _ = (t * k' * t)⁻¹ * ((t * k' * t) * (t * k * t)) * k'⁻¹ := by rw [← e2, e1, e3]
      _ = (t * k * t) * k'⁻¹ := by group
  have hz₀ : (t * k' * t)⁻¹ * k ∈ Kᵍ[t] := by rw [e4]; exact mul_mem hk₁ (inv_mem hk')
  have hzKt : (t * k * t)⁻¹ * k' ∈ Kᵍ[t] := mul_mem (inv_mem hk₁) hk'
  have hzK : (t * k * t)⁻¹ * k' ∈ K := by
    have h1 : t * ((t * k * t)⁻¹ * k') * t = ((t * k' * t)⁻¹ * k)⁻¹ := by
      rw [invol_conj_mul ht, ← invol_conj_inv ht, invol_conj_invol ht]
      group
    have h2 : t * ((t * k * t)⁻¹ * k') * t ∈ Kᵍ[t] := by rw [h1]; exact inv_mem hz₀
    have h3 := (mem_conjG_iff ht).1 h2
    rwa [invol_conj_invol ht] at h3
  refine ⟨k, hk, (t * k * t)⁻¹ * k', mem_inf.2 ⟨hzK, hzKt⟩, ?_⟩
  group

end DiagGeneric

section DiagRange

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem odd_card_inf_conj (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    Odd (Nat.card (K ⊓ Kᵍ[t] : Subgroup G)) := by
  refine Odd.of_dvd_nat (odd_card_zc_jZeroLayer h d hp) (Subgroup.card_dvd_of_le ?_)
  rw [hK.layer_eq]
  exact Common.inf_le_center_sup hK.comm

theorem diag_range_perfect {K : Subgroup G} (hK : ⁅K, K⁆ = K) (hcomm : ⁅K, Kᵍ[t]⁆ = ⊥) :
    ⁅(diagonalHom K t hcomm).range, (diagonalHom K t hcomm).range⁆ =
      (diagonalHom K t hcomm).range := by
  set Δ := diagonalHom K t hcomm
  have hperf : Group.IsPerfect K := (isPerfect_subgroup_iff_commutator_eq K).2 hK
  calc ⁅Δ.range, Δ.range⁆ = ⁅(⊤ : Subgroup K).map Δ, (⊤ : Subgroup K).map Δ⁆ := by
        rw [← MonoidHom.range_eq_map]
    _ = Subgroup.map Δ ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ := (Subgroup.map_commutator _ _ _).symm
    _ = Subgroup.map Δ (commutator K) := by rw [_root_.commutator_def]
    _ = Δ.range := by rw [hperf.commutator_eq_top, ← MonoidHom.range_eq_map]

theorem diag_range_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    (diagonalHom K t hK.comm).range = d.leviJ₀.map L.subtype := by
  set Δ := diagonalHom K t hK.comm with hΔ
  have hKE : K ≤ jZeroLayer d := hK.layer_eq ▸ le_sup_left
  have hKtE : Kᵍ[t] ≤ jZeroLayer d := hK.layer_eq ▸ le_sup_right
  have hrE : Δ.range ≤ jZeroLayer d := by
    rintro _ ⟨a, rfl⟩
    exact mul_mem (hKE a.2) (hKtE (Common.conj_mem_map_conj_inv t a.2))
  have hperf := diag_range_perfect (isLayerComponent_perfect hK) hK.comm
  apply le_antisymm
  ·
    have hC : Δ.range ≤ centralizer ({t} : Set G) := Common.range_diagonalHom_le hK.comm h.t_mul_t
    have hmem : Δ.range ≤ (centralizer (d.J₀ : Set L)).map L.subtype ⊔ zpowers t := by
      rw [← h.centralizer_J₀_inf_centralizer_eq d]
      exact le_inf (hrE.trans (Setup.jZeroLayer_le_centralizer_J₀ d)) hC
    have hAT : ∀ a ∈ (centralizer (d.J₀ : Set L)).map L.subtype, ∀ c ∈ zpowers t,
        a * c = c * a := by
      intro a ha c hc
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
      have haL : a ∈ L := map_subtype_le _ ha
      exact (Commute.zpow_right (mem_centralizer_iff.1 h.htL a haL : Commute a t) k).eq
    have hT : ∀ c ∈ zpowers t, ∀ e ∈ zpowers t, c * e = e * c := by
      intro c hc e he
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 he
      exact (Commute.zpow_zpow_self t k m).eq
    have := le_commutator_of_perfect_of_le_sup hperf hmem hAT hT
    rwa [← Subgroup.map_commutator, d.commutator_centralizer_J₀] at this
  ·
    have hK₀perf : ⁅d.leviJ₀.map L.subtype, d.leviJ₀.map L.subtype⁆ = d.leviJ₀.map L.subtype :=
      Subgroup.isPerfect_iff.1 (Setup.isQuasisimple_leviJ₀_map d).1
    have hK₀E : d.leviJ₀.map L.subtype ≤ jZeroLayer d := Setup.leviJ₀_map_le_jZeroLayer h d hp.layer
    have hK₀C := (Setup.leviJ₀_map_le_centralizer_J₀_inf_centralizer h d).trans inf_le_right
    have hmem : d.leviJ₀.map L.subtype ≤ Δ.range ⊔ (K ⊓ Kᵍ[t]) := by
      intro c hc
      obtain ⟨k, hk, z, hz, rfl⟩ := exists_diag_mul_of_commute h.t_mul_t hK.comm
        (hK.layer_eq ▸ hK₀E hc) (mem_centralizer_singleton_iff.1 (hK₀C hc)).symm
      refine mul_mem (mem_sup_left ⟨⟨k, hk⟩, ?_⟩) (mem_sup_right hz)
      exact Common.diagonalHom_apply_of_mul_self hK.comm h.t_mul_t ⟨k, hk⟩
    have hz := fun {z : G} (hz : z ∈ K ⊓ Kᵍ[t]) => hK.layer_eq ▸ Common.inf_le_center_sup hK.comm hz
    have hAT : ∀ a ∈ Δ.range, ∀ c ∈ K ⊓ Kᵍ[t], a * c = c * a := fun a ha c hc =>
      mem_centralizer_iff.1 (hz hc).2 a (hrE ha)
    have hT : ∀ c ∈ K ⊓ Kᵍ[t], ∀ e ∈ K ⊓ Kᵍ[t], c * e = e * c := fun c hc e he =>
      mem_centralizer_iff.1 (hz he).2 c (hz hc).1
    exact (le_commutator_of_perfect_of_le_sup hK₀perf hmem hAT hT).trans hperf.le

end DiagRange

section LieModelQuot

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem diag_surjective (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    ∃ D : ↥K →* ↥(d.leviJ₀.map L.subtype), Function.Surjective D ∧ D.ker ≤ center ↥K ∧
      ∀ x : K, ((D x : ↥(d.leviJ₀.map L.subtype)) : G) = x * (t * x * t) := by
  set Δ := diagonalHom K t hK.comm with hΔ
  have hrange := diag_range_eq h d hp hK
  let D : ↥K →* ↥(d.leviJ₀.map L.subtype) :=
    Δ.codRestrict _ (fun x => by rw [← hrange]; exact ⟨x, rfl⟩)
  refine ⟨D, ?_, ?_, ?_⟩
  · intro y
    have : (y : G) ∈ Δ.range := by rw [hrange]; exact y.2
    obtain ⟨x, hx⟩ := this
    exact ⟨x, Subtype.ext hx⟩
  · intro x hx
    apply Common.ker_diagonalHom_le_center hK.comm
    rw [MonoidHom.mem_ker] at hx ⊢
    exact congrArg Subtype.val hx
  · intro x
    exact Common.diagonalHom_apply_of_mul_self hK.comm h.t_mul_t x

theorem lieModel_layerComponent (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    LieModel (↥K ⧸ center ↥K) .PSL 3 2 f := by
  obtain ⟨D, hD, hker, -⟩ := diag_surjective h d hp hK
  obtain ⟨e⟩ := CFSG.LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective
    (isLayerComponent_isQuasisimple hK) D hD hker
  exact (Setup.lieModel_leviJ₀_map d (by have := hp.two_le; omega : 1 ≤ f)).of_mulEquiv e.symm

end LieModelQuot

section XSection

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

set_option hygiene false in
local macro "layer_ctx_PL" : tactic => `(tactic| (
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  have h5101 := h.yamada_5_10_1 d hlay
  have h5102 := h.yamada_5_10_2 d hlay
  have h59e := h.yamadaY₂_eq d hlay
  have h520 := h.yamada_5_20 d hlay
  have h5221 := h.yamada_5_22_1 d hlay
  have h521 := h.yamada_5_21 d hlay))

theorem yamadaY₂_le_yamadaW₃' (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaY₂ d t ≤ yamadaW₃ d t :=
  (le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t).trans (h.yamadaW₂_le_yamadaW₃ d hlay)

theorem yamadaD₅_eq_sup_conj (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaD₅ d t = yamadaW₃ d t ⊔ (yamadaW₃ d t).map (MulAut.conj (uG d)).toMonoidHom ∧
      yamadaW₃ d t ⊓ (yamadaW₃ d t).map (MulAut.conj (uG d)).toMonoidHom = yamadaV₁ d t := by
  layer_ctx_PL
  have := h.yamada_5_25 d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221 h521
  exact ⟨this.2.2.2.1, this.2.2.2.2.1⟩

theorem uG_mem_normalizer_J₀ (d : TrialityD4Data L (2 ^ f)) :
    uG d ∈ normalizer ((d.J₀.map L.subtype : Subgroup G) : Set G) :=
  Setup.coe_mem_normalizer_map d.u_mem_normalizer_J₀

theorem map_conj_uG_le_centralizer_J₀ (d : TrialityD4Data L (2 ^ f)) {A : Subgroup G}
    (hA : A ≤ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)) :
    A.map (MulAut.conj (uG d)).toMonoidHom ≤
      centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) := by
  have h1 := Setup.map_conj_eq_self_D4
    (K := centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))
    (mem_normalizer_centralizer_D4 (uG_mem_normalizer_J₀ d))
  rw [← h1]
  exact Subgroup.map_mono hA

theorem yamadaY₂_le_prodX (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) : yamadaY₂ d t ≤ prodX d t :=
  le_inf ((yamadaY₂_le_yamadaW₃' h d hp.layer).trans (h.yamadaW₃_le_yamadaD₅_PA d hp.layer))
    (h.yamadaY₂_le_centralizer_J₀_D3 d hp.layer)

theorem yamadaY₂_conj_le_prodX (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) : (yamadaY₂ d t).map (MulAut.conj (uG d)).toMonoidHom ≤ prodX d t := by
  refine le_inf ?_ (map_conj_uG_le_centralizer_J₀ d (h.yamadaY₂_le_centralizer_J₀_D3 d hp.layer))
  rw [(yamadaD₅_eq_sup_conj h d hp.layer).1]
  exact le_sup_of_le_right (Subgroup.map_mono (yamadaY₂_le_yamadaW₃' h d hp.layer))

theorem prodX_eq_sup (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    prodX d t = yamadaY₂ d t ⊔ (yamadaY₂ d t).map (MulAut.conj (uG d)).toMonoidHom := by
  have hlay := hp.layer
  obtain ⟨-, hX6⟩ : True ∧ Nat.card (prodX d t) = (2 ^ f) ^ 6 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h12⟩ := T5_J₀ h d hp
    exact ⟨trivial, h12⟩
  have hV₁ := (h.yamada_5_6_2 d hlay).2.1
  have hY₂ := (h.yamada_5_9_2 d hlay).2.1
  have hle : (yamadaY₂ d t ⊔ (yamadaY₂ d t).map (MulAut.conj (uG d)).toMonoidHom) ≤ prodX d t :=
    sup_le (yamadaY₂_le_prodX h d hp) (yamadaY₂_conj_le_prodX h d hp)
  refine (eq_of_le_of_card_ge hle ?_).symm
  set A := yamadaY₂ d t with hA
  set B := A.map (MulAut.conj (uG d)).toMonoidHom with hB
  have hinf : A ⊓ B ≤ yamadaV₁ d t := by
    rw [← (yamadaD₅_eq_sup_conj h d hlay).2]
    exact inf_le_inf (yamadaY₂_le_yamadaW₃' h d hlay)
      (Subgroup.map_mono (yamadaY₂_le_yamadaW₃' h d hlay))
  have hcardB : Nat.card B = (2 ^ f) ^ 4 := by
    rw [hB, Subgroup.card_map_of_injective (MulAut.conj (uG d)).injective, hY₂]
  have hcardinf : Nat.card (A ⊓ B : Subgroup G) ≤ (2 ^ f) ^ 2 := by
    rw [← hV₁]
    exact Subgroup.card_le_of_le hinf
  have h1 := ncard_mul_mul_card_inf A B
  rw [hY₂, hcardB] at h1
  have h2 : ((A : Set G) * (B : Set G)).ncard ≤ Nat.card (A ⊔ B : Subgroup G) := by
    rw [← Nat.card_coe_set_eq]
    refine (Set.ncard_le_ncard ?_ (Set.toFinite _)).trans_eq (Nat.card_coe_set_eq _)
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact mul_mem (mem_sup_left ha) (mem_sup_right hb)
  have hpos : 0 < (2 ^ f) ^ 2 := by positivity
  have h3 : (2 ^ f) ^ 6 * (2 ^ f) ^ 2 ≤ ((A : Set G) * (B : Set G)).ncard * (2 ^ f) ^ 2 := by
    calc (2 ^ f) ^ 6 * (2 ^ f) ^ 2 = (2 ^ f) ^ 4 * (2 ^ f) ^ 4 := by ring
      _ = ((A : Set G) * (B : Set G)).ncard * Nat.card (A ⊓ B : Subgroup G) := h1.symm
      _ ≤ _ := Nat.mul_le_mul_left _ hcardinf
  have h4 : (2 ^ f) ^ 6 ≤ ((A : Set G) * (B : Set G)).ncard := Nat.le_of_mul_le_mul_right h3 hpos
  rw [hX6]
  exact h4.trans h2

theorem map_conj_le_of_mem_normalizer {A B : Subgroup G} (hA : A ≤ B) {g : G}
    (hg : g ∈ normalizer (B : Set G)) : A.map (MulAut.conj g).toMonoidHom ≤ B := by
  rw [← Setup.map_conj_eq_self_D4 hg]
  exact Subgroup.map_mono hA

theorem prodX_le_jZeroLayer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) : prodX d t ≤ jZeroLayer d := by
  have hY₂E : yamadaY₂ d t ≤ jZeroLayer d := by
    rw [h.yamadaY₂_eq d hp.layer]
    exact inf_le_left
  rw [prodX_eq_sup h d hp]
  exact sup_le hY₂E (map_conj_le_of_mem_normalizer hY₂E
    (Setup.normalizer_le_normalizer_jZeroLayer d (uG_mem_normalizer_J₀ d)))

theorem card_prodX (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    Nat.card (prodX d t) = (2 ^ f) ^ 6 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h12⟩ := T5_J₀ h d hp
  exact h12

theorem isPGroup_prodX (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    IsPGroup 2 (prodX d t) :=
  IsPGroup.of_card (n := f * 6) (by rw [card_prodX h d hp, ← pow_mul])

theorem t_mem_normalizer_prodX (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    t ∈ normalizer (prodX d t : Set G) :=
  mem_normalizer_inf_D4 (h.t_mem_normalizer_yamadaD₅_C9 d) (mem_normalizer_centralizer_D4
    (Subgroup.centralizer_le_normalizer _ (h.t_mem_centralizer_J₀ d)))

theorem sylowJ₀_map_le_prodX (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : d.sylowJ₀.map L.subtype ≤ prodX d t := by
  layer_ctx_PL
  have hD₁C₅ : yamadaD₁ d t ≤ yamadaC₅ d t :=
    (h.yamadaD₁_le_yamadaC₁ d).trans (yamadaC₁_le_yamadaC₅ d t)
  have hDD₅ : d.D.map L.subtype ≤ yamadaD₅ d t := le_inf ((D_le_yamadaD₁ d t).trans hD₁C₅)
    fun δ hδ => mem_centralizer_iff.2 fun v hv =>
      (Setup.mul_comm_of_mem_S_of_mem_yamadaV₁ d h593 (Subgroup.map_mono d.D_le_S hδ) hv).symm
  exact le_inf ((Setup.sylowJ₀_map_le_D_map d).trans hDD₅) (Setup.sylowJ₀_map_le_centralizer_J₀ d)

theorem prodX_sylow (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    IsSylowOf 2 (prodX d t) (jZeroLayer d) ∧
      prodX d t ⊓ centralizer ({t} : Set G) = d.sylowJ₀.map L.subtype ∧
      SylowShape (prodX d t) (d.sylowJ₀.map L.subtype) (2 ^ f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hlay := hp.layer
  have htX := t_mem_normalizer_prodX h d
  have hXp := isPGroup_prodX h d hp
  have hz : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [h.card_zpowers_t, pow_one])
  have hXH : prodX d t ≤ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) := inf_le_right
  have htH : t ∈ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) :=
    h.t_mem_centralizer_J₀ d
  obtain ⟨T, hT, htT, hQT⟩ := Setup.exists_isSylowOf_jZeroLayer d (Q := zpowers t ⊔ prodX d t)
    (sup_le ((zpowers_le).2 htH) hXH)
    (IsPGroup.to_sup_of_normal_right' hz hXp ((zpowers_le).2 htX)) (mem_sup_left (mem_zpowers t))
  have hXT : prodX d t ≤ T :=
    fun x hx => hQT ⟨mem_sup_right hx, prodX_le_jZeroLayer h d hp hx⟩
  have hPT : d.sylowJ₀.map L.subtype ≤ T := (sylowJ₀_map_le_prodX h d hlay).trans hXT
  obtain ⟨hCt, hsh⟩ := h.sylowShape_of_isSylowOf_jZeroLayer d hlay hT htT hPT
  have hXeq : prodX d t = T := by
    refine eq_of_le_of_card_ge hXT ?_
    rw [hsh.card_eq, card_prodX h d hp]
  rw [hXeq]
  exact ⟨hT, hCt, hsh⟩

theorem heisLike_sylowJ₀_map (d : TrialityD4Data L (2 ^ f)) :
    HeisLike (d.sylowJ₀.map L.subtype) (2 ^ f) :=
  (HeisLike.map_iff L.subtype fun x _ hx => Subtype.ext hx).2 d.heisLike_sylowJ₀

end XSection

section QThree

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem conjG_eq_map_conj {t : G} (ht : t * t = 1) (A : Subgroup G) :
    Aᵍ[t] = A.map (MulAut.conj t).toMonoidHom := by
  rw [show t⁻¹ = t from inv_eq_of_mul_eq_one_right ht]

theorem conjG_inf (t : G) (A B : Subgroup G) : (A ⊓ B)ᵍ[t] = Aᵍ[t] ⊓ Bᵍ[t] :=
  Subgroup.map_inf_eq _ _ _ (MulAut.conj t⁻¹).injective

theorem conjG_eq_self_of_mem_normalizer {t : G} {A : Subgroup G}
    (htA : t ∈ normalizer (A : Set G)) : Aᵍ[t] = A :=
  Setup.map_conj_eq_self_D4 (inv_mem htA)

theorem qThree_decomp (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    prodX d t = qThree d t K ⊔ (qThree d t K)ᵍ[t] ∧ qThree d t K ⊓ (qThree d t K)ᵍ[t] = ⊥ ∧
      ⁅qThree d t K, (qThree d t K)ᵍ[t]⁆ = ⊥ ∧ IsSylowOf 2 (qThree d t K) K ∧
      Nat.card (qThree d t K) = (2 ^ f) ^ 3 := by
  have hsyl := (prodX_sylow h d hp).1
  rw [hK.layer_eq] at hsyl
  obtain ⟨hA, -, hsup, hinf⟩ := isSylowOf_prod hK.comm (odd_card_inf_conj h d hp hK) hsyl
  have hXt : (prodX d t)ᵍ[t] = prodX d t :=
    conjG_eq_self_of_mem_normalizer (t_mem_normalizer_prodX h d)
  have hQt : (qThree d t K)ᵍ[t] = prodX d t ⊓ Kᵍ[t] := by
    unfold qThree
    rw [conjG_inf, hXt]
  have hsup' : prodX d t = qThree d t K ⊔ (qThree d t K)ᵍ[t] := by
    rw [hQt]
    exact hsup
  have hinf' : qThree d t K ⊓ (qThree d t K)ᵍ[t] = ⊥ := by rw [hQt]; exact hinf
  have hcomm' : ⁅qThree d t K, (qThree d t K)ᵍ[t]⁆ = ⊥ := by
    refine le_bot_iff.1 ?_
    rw [← hK.comm]
    exact Subgroup.commutator_mono inf_le_right
      (by rw [hQt]; exact inf_le_inf_left _ le_rfl |>.trans (inf_le_right))
  refine ⟨hsup', hinf', hcomm', hA, ?_⟩
  obtain ⟨hc, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (qThree d t K)
    (qThree d t K)ᵍ[t] (commute_of_commutator_eq_bot hcomm')
  rw [← hsup', hinf', Subgroup.card_bot, mul_one, card_prodX h d hp,
    Subgroup.card_map_of_injective (MulAut.conj t⁻¹).injective] at hc
  have h2 : (Nat.card (qThree d t K)) ^ 2 = ((2 ^ f) ^ 3) ^ 2 := by
    rw [sq, ← hc]
    ring
  exact (Nat.pow_left_injective (by norm_num : 2 ≠ 0)) h2

end QThree

section ProjFst

variable {G : Type*} [Group G]

def projFst (A B Y : Subgroup G) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : Subgroup G where
  carrier := {a | a ∈ A ∧ ∃ b ∈ B, a * b ∈ Y}
  one_mem' := ⟨one_mem _, 1, one_mem _, by simpa using one_mem Y⟩
  mul_mem' := by
    rintro a a' ⟨ha, b, hb, hY⟩ ⟨ha', b', hb', hY'⟩
    refine ⟨mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
    have e : a * a' * (b * b') = (a * b) * (a' * b') := by
      calc a * a' * (b * b') = a * (a' * b) * b' := by group
        _ = a * (b * a') * b' := by rw [hAB a' ha' b hb]
        _ = (a * b) * (a' * b') := by group
    rw [e]
    exact mul_mem hY hY'
  inv_mem' := by
    rintro a ⟨ha, b, hb, hY⟩
    refine ⟨inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
    have e : a⁻¹ * b⁻¹ = (a * b)⁻¹ := by
      calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := by group
        _ = (a * b)⁻¹ := by rw [hAB a ha b hb]
    rw [e]
    exact inv_mem hY

end ProjFst

section SubProd

variable {G : Type*} [Group G] [Finite G]

theorem sub_prod_eq {A Y : Subgroup G} {t : G} {k : ℕ} (ht : t * t = 1) (hA : HeisLike A k)
    (hcomm : ⁅A, Aᵍ[t]⁆ = ⊥) (hinf : A ⊓ Aᵍ[t] = ⊥) (hYX : Y ≤ A ⊔ Aᵍ[t])
    (hYt : t ∈ normalizer (Y : Set G)) (hYab : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x)
    (hcard : Nat.card Y = k ^ 4) :
    ∃ B₁ : Subgroup G, B₁ ≤ A ∧ Y = B₁ ⊔ B₁ᵍ[t] ∧ Nat.card B₁ = k ^ 2 := by
  have hc := commute_of_commutator_eq_bot hcomm
  set B₁ := projFst A Aᵍ[t] Y hc with hB₁
  have hB₁A : B₁ ≤ A := fun x hx => hx.1
  have hB₁ab : ∀ x ∈ B₁, ∀ y ∈ B₁, x * y = y * x := by
    rintro x ⟨hxA, b, hb, hxY⟩ y ⟨hyA, b', hb', hyY⟩
    have h1 := hYab _ hxY _ hyY
    have e1 : (x * b) * (y * b') = (x * y) * (b * b') := by
      calc (x * b) * (y * b') = x * (b * y) * b' := by group
        _ = x * (y * b) * b' := by rw [hc y hyA b hb]
        _ = (x * y) * (b * b') := by group
    have e2 : (y * b') * (x * b) = (y * x) * (b' * b) := by
      calc (y * b') * (x * b) = y * (b' * x) * b := by group
        _ = y * (x * b') * b := by rw [hc x hxA b' hb']
        _ = (y * x) * (b' * b) := by group
    rw [e1, e2] at h1
    have h2 : (y * x)⁻¹ * (x * y) = (b' * b) * (b * b')⁻¹ := by
      calc (y * x)⁻¹ * (x * y) = (y * x)⁻¹ * ((x * y) * (b * b')) * (b * b')⁻¹ := by group
        _ = (y * x)⁻¹ * ((y * x) * (b' * b)) * (b * b')⁻¹ := by rw [h1]
        _ = (b' * b) * (b * b')⁻¹ := by group
    have h3 : (y * x)⁻¹ * (x * y) ∈ A ⊓ Aᵍ[t] :=
      mem_inf.2 ⟨mul_mem (inv_mem (mul_mem hyA hxA)) (mul_mem hxA hyA),
        h2 ▸ mul_mem (mul_mem hb' hb) (inv_mem (mul_mem hb hb'))⟩
    rw [hinf, mem_bot] at h3
    have h4 : x * y = y * x := by
      calc x * y = (y * x) * ((y * x)⁻¹ * (x * y)) := by group
        _ = y * x := by rw [h3, mul_one]
    exact h4
  have hcardB₁ : Nat.card B₁ ≤ k ^ 2 := heis_card_le_of_abelian hA hB₁A hB₁ab
  have hYtc : ∀ y ∈ Y, t * y * t ∈ Y := by
    intro y hy
    have := (mem_normalizer_iff.1 hYt y).1 hy
    rwa [inv_eq_of_mul_eq_one_right ht] at this
  have hYle : Y ≤ B₁ ⊔ B₁ᵍ[t] := by
    intro y hy
    have hy' : y ∈ ((A ⊔ Aᵍ[t] : Subgroup G) : Set G) := hYX hy
    obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A Aᵍ[t] hc
    rw [hset] at hy'
    obtain ⟨a, ha, b, hb, rfl⟩ := hy'
    refine mul_mem (mem_sup_left ⟨ha, b, hb, hy⟩) (mem_sup_right ?_)
    rw [mem_conjG_iff ht]
    refine ⟨(mem_conjG_iff ht).1 hb, t * a * t, conj_mem_conjG ht ha, ?_⟩
    have h5 : (t * b * t) * (t * a * t) = (t * a * t) * (t * b * t) :=
      hc _ ((mem_conjG_iff ht).1 hb) _ (conj_mem_conjG ht ha)
    rw [h5, ← invol_conj_mul ht]
    exact hYtc _ hy
  have hcommB : ⁅B₁, B₁ᵍ[t]⁆ = ⊥ :=
    le_bot_iff.1 (hcomm ▸ Subgroup.commutator_mono hB₁A (Subgroup.map_mono hB₁A))
  have hinfB : B₁ ⊓ B₁ᵍ[t] = ⊥ :=
    le_bot_iff.1 (hinf ▸ inf_le_inf hB₁A (Subgroup.map_mono hB₁A))
  have hcardsup : Nat.card (B₁ ⊔ B₁ᵍ[t] : Subgroup G) = Nat.card B₁ * Nat.card B₁ := by
    obtain ⟨hc', -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute B₁ B₁ᵍ[t]
      (commute_of_commutator_eq_bot hcommB)
    rw [hinfB, Subgroup.card_bot, mul_one] at hc'
    rw [hc', Subgroup.card_map_of_injective (MulAut.conj t⁻¹).injective]
  have hYeq : Y = B₁ ⊔ B₁ᵍ[t] := by
    refine eq_of_le_of_card_ge hYle ?_
    rw [hcardsup, hcard]
    calc Nat.card B₁ * Nat.card B₁ ≤ k ^ 2 * k ^ 2 := Nat.mul_le_mul hcardB₁ hcardB₁
      _ = k ^ 4 := by ring
  refine ⟨B₁, hB₁A, hYeq, ?_⟩
  have h6 : Nat.card B₁ * Nat.card B₁ = k ^ 2 * k ^ 2 := by
    rw [← hcardsup, ← hYeq, hcard]
    ring
  exact Nat.mul_self_inj.1 h6

end SubProd

section EOne

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem heisLike_qThree (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) : HeisLike (qThree d t K) (2 ^ f) := by
  obtain ⟨hsup, hinf, hcomm, -, -⟩ := qThree_decomp h d hp hK
  obtain ⟨-, hCt, -⟩ := prodX_sylow h d hp
  refine heisLike_of_swap_diag h.t_mul_t (A := qThree d t K) (B := (qThree d t K)ᵍ[t])
    (conjG_eq_map_conj h.t_mul_t _) (commute_of_commutator_eq_bot hcomm) hinf ?_
  rw [← hsup, hCt]
  exact heisLike_sylowJ₀_map d

theorem yamadaY₂_mul_self (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {y : G} (hy : y ∈ yamadaY₂ d t) : y * y = 1 := by
  have hV := (h.yamada_5_6_2 d hlay).1
  have hy' : y ∈ ((yamadaY₂ d t : Subgroup G) : Set G) := hy
  rw [h.coe_yamadaY₂ d hlay] at hy'
  obtain ⟨a, ha, b, hb, rfl⟩ := hy'
  obtain ⟨c, hc, rfl⟩ := hb
  have ha2 : a * a = 1 := by rw [← sq]; exact hV.2 a ha
  have hc2 : c * c = 1 := by rw [← sq]; exact hV.2 c hc
  have hb2 : (MulAut.conj ((d.v : L) : G)).toMonoidHom c *
      (MulAut.conj ((d.v : L) : G)).toMonoidHom c = 1 := by
    rw [← map_mul, hc2, map_one]
  have hab : a * (MulAut.conj ((d.v : L) : G)).toMonoidHom c =
      (MulAut.conj ((d.v : L) : G)).toMonoidHom c * a :=
    h.mul_comm_of_mem_yamadaY₂ d hlay (mem_sup_left ha)
      (Setup.yamadaV₁_conj_le_yamadaY₂ d ⟨c, hc, rfl⟩)
  change a * (MulAut.conj ((d.v : L) : G)).toMonoidHom c *
    (a * (MulAut.conj ((d.v : L) : G)).toMonoidHom c) = 1
  set b := (MulAut.conj ((d.v : L) : G)).toMonoidHom c with hb
  calc a * b * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [← hab]
    _ = (a * a) * (b * b) := by group
    _ = 1 := by rw [ha2, hb2, one_mul]

theorem eOne_decomp (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    yamadaY₂ d t = eOne d t K ⊔ (eOne d t K)ᵍ[t] ∧ eOne d t K ⊓ (eOne d t K)ᵍ[t] = ⊥ ∧
      Nat.card (eOne d t K) = (2 ^ f) ^ 2 ∧ eOne d t K ≤ qThree d t K ∧
      IsElemAbelian 2 (eOne d t K) := by
  have hlay := hp.layer
  obtain ⟨hsup, hinf, hcomm, -, -⟩ := qThree_decomp h d hp hK
  have hHeis := heisLike_qThree h d hp hK
  have hYX : yamadaY₂ d t ≤ qThree d t K ⊔ (qThree d t K)ᵍ[t] := hsup ▸ yamadaY₂_le_prodX h d hp
  obtain ⟨B₁, hB₁A, hY, hcardB⟩ := sub_prod_eq h.t_mul_t hHeis hcomm hinf hYX
    (h.t_mem_normalizer_yamadaY₂_D1 d) (fun x hx y hy => h.mul_comm_of_mem_yamadaY₂ d hlay hx hy)
    (h.yamada_5_9_2 d hlay).2.1
  have hAK : qThree d t K ≤ K := inf_le_right
  have hAX : qThree d t K ≤ prodX d t := inf_le_left
  have hcc := commute_of_commutator_eq_bot hcomm
  have hE : eOne d t K = B₁ := by
    apply le_antisymm
    · rintro x ⟨hxY, hxK⟩
      have hxY' : x ∈ ((B₁ ⊔ B₁ᵍ[t] : Subgroup G) : Set G) := hY ▸ hxY
      have hcB := commute_of_commutator_eq_bot
        (le_bot_iff.1 (hcomm ▸ Subgroup.commutator_mono hB₁A (Subgroup.map_mono hB₁A)) :
          ⁅B₁, B₁ᵍ[t]⁆ = ⊥)
      obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute B₁ B₁ᵍ[t] hcB
      rw [hset] at hxY'
      obtain ⟨a, ha, b, hb, rfl⟩ := hxY'
      have hbA : b ∈ qThree d t K := by
        refine ⟨?_, ?_⟩
        · exact hsup ▸ mem_sup_right (Subgroup.map_mono hB₁A hb)
        · have := mul_mem (inv_mem (hAK (hB₁A ha))) hxK
          rwa [inv_mul_cancel_left] at this
      have hb1 : b = 1 := by
        have : b ∈ qThree d t K ⊓ (qThree d t K)ᵍ[t] := ⟨hbA, Subgroup.map_mono hB₁A hb⟩
        rw [hinf, mem_bot] at this
        exact this
      rw [hb1]
      simpa using ha
    · intro x hx
      exact ⟨hY ▸ mem_sup_left hx, hAK (hB₁A hx)⟩
  rw [hE]
  refine ⟨hY, ?_, hcardB, hB₁A, ?_⟩
  · exact le_bot_iff.1 (hinf ▸ inf_le_inf hB₁A (Subgroup.map_mono hB₁A))
  · have hBY : B₁ ≤ yamadaY₂ d t := hY ▸ le_sup_left
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
    · exact h.mul_comm_of_mem_yamadaY₂ d hlay (hBY a.2) (hBY b.2)
    · rw [sq]
      exact yamadaY₂_mul_self h d hlay (hBY hy)

theorem eOne_normal (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    zc (qThree d t K) ≤ eOne d t K ∧ ((eOne d t K).subgroupOf (qThree d t K)).Normal := by
  obtain ⟨-, -, hcard, hle, hel⟩ := eOne_decomp h d hp hK
  have hHeis := heisLike_qThree h d hp hK
  have hZ : zc (qThree d t K) ≤ eOne d t K :=
    heis_center_le_of_abelian_of_card_eq hHeis hle
      (fun x hx y hy => hel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩ |> congrArg Subtype.val) hcard
  exact ⟨hZ, heis_normal_subgroupOf_of_center_le hHeis hle hZ⟩

end EOne

section AlphaOne

open Matrix

namespace AlphaOne

section SL3

variable {F : Type} [Field F]

@[expose] def parab : Subgroup SL(3, F) where
  carrier := {g | g 2 0 = 0 ∧ g 2 1 = 0}
  mul_mem' := by
    rintro a b ⟨ha0, ha1⟩ ⟨hb0, hb1⟩
    simp [mul_apply, Fin.sum_univ_three, ha0, ha1, hb0, hb1]
  one_mem' := by simp
  inv_mem' := by
    rintro a ⟨ha0, ha1⟩
    simp [adjugate_fin_three, ha0, ha1]

@[expose] def rad : Subgroup SL(3, F) where
  carrier := {g | g 0 0 = 1 ∧ g 0 1 = 0 ∧ g 1 0 = 0 ∧ g 1 1 = 1 ∧ g 2 0 = 0 ∧ g 2 1 = 0 ∧
    g 2 2 = 1}
  mul_mem' := by
    rintro a b ⟨a00, a01, a10, a11, a20, a21, a22⟩ ⟨b00, b01, b10, b11, b20, b21, b22⟩
    simp [mul_apply, Fin.sum_univ_three, a00, a01, a10, a11, a20, a21, a22, b00, b01, b10, b11,
      b20, b21, b22]
  one_mem' := by simp [one_apply]
  inv_mem' := by
    rintro a ⟨a00, a01, a10, a11, a20, a21, a22⟩
    simp [adjugate_fin_three, a00, a01, a10, a11, a20, a21, a22]

theorem mem_parab {g : SL(3, F)} : g ∈ parab ↔ g 2 0 = 0 ∧ g 2 1 = 0 :=
  Iff.rfl

@[expose] def slMk (M : Matrix (Fin 3) (Fin 3) F) (h : M.det = 1) : SL(3, F) :=
  ⟨M, h⟩

theorem coe_slMk (M : Matrix (Fin 3) (Fin 3) F) (h : M.det = 1) :
    ((slMk M h : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = M :=
  rfl

theorem det_parab {g : SL(3, F)} (hg : g ∈ parab) :
    g 0 0 * g 1 1 * g 2 2 - g 0 1 * g 1 0 * g 2 2 = 1 := by
  obtain ⟨g20, g21⟩ := hg
  have h := g.2
  rw [det_fin_three, g20, g21] at h
  linear_combination h

theorem conj_mem_rad {g y : SL(3, F)} (hg : g ∈ parab) (hy : y ∈ rad) : g * y * g⁻¹ ∈ rad := by
  have hdet := det_parab hg
  obtain ⟨g20, g21⟩ := hg
  obtain ⟨y00, y01, y10, y11, y20, y21, y22⟩ := hy
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [adjugate_fin_three, mul_apply, Fin.sum_univ_three, g20, g21, y00, y01, y10, y11, y20,
      y21, y22] <;>
    first | linear_combination hdet | linear_combination

theorem parab_le_normalizer_rad :
    parab ≤ normalizer ((rad : Subgroup SL(3, F)) : Set SL(3, F)) := by
  intro g hg
  refine mem_normalizer_iff.2 fun y => ⟨conj_mem_rad hg, fun h => ?_⟩
  have := conj_mem_rad (inv_mem hg) h
  rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at this

theorem slTrans_02_mem_rad (c : F) : slTrans (show (0 : Fin 3) ≠ 2 by decide) c ∈ rad := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [coe_slTrans, transvection, single_apply, one_apply]

theorem slTrans_12_mem_rad (c : F) : slTrans (show (1 : Fin 3) ≠ 2 by decide) c ∈ rad := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [coe_slTrans, transvection, single_apply, one_apply]

theorem normalizer_rad_le_parab :
    normalizer ((rad : Subgroup SL(3, F)) : Set SL(3, F)) ≤ parab := by
  intro g hg
  have key : ∀ y ∈ rad, ∃ z ∈ rad, z * g = g * y := fun y hy =>
    ⟨g * y * g⁻¹, (mem_normalizer_iff.1 hg y).1 hy, by group⟩
  obtain ⟨z, ⟨-, -, -, -, z20, z21, z22⟩, hz⟩ := key _ (slTrans_02_mem_rad (1 : F))
  obtain ⟨z', ⟨-, -, -, -, z'20, z'21, z'22⟩, hz'⟩ := key _ (slTrans_12_mem_rad (1 : F))
  have e := congrArg (fun m : SL(3, F) => m 2 2) hz
  have e' := congrArg (fun m : SL(3, F) => m 2 2) hz'
  simp [mul_apply, Fin.sum_univ_three, z20, z21, z22, z'20, z'21, z'22, coe_slTrans,
    transvection, single_apply, one_apply] at e e'
  exact ⟨e, e'⟩

theorem normalizer_rad : normalizer ((rad : Subgroup SL(3, F)) : Set SL(3, F)) = parab :=
  le_antisymm normalizer_rad_le_parab parab_le_normalizer_rad

theorem mul_inv_mem_parab {k k' : SL(3, F)} (h0 : k 2 0 = k' 2 0) (h1 : k 2 1 = k' 2 1)
    (h2 : k 2 2 = k' 2 2) : k * k'⁻¹ ∈ parab := by
  have e : ∀ j, (k * k'⁻¹) 2 j = (k' * k'⁻¹) 2 j := by
    intro j
    simp only [Matrix.SpecialLinearGroup.coe_mul, mul_apply, Fin.sum_univ_three, h0, h1, h2]
  rw [mul_inv_cancel] at e
  exact ⟨by rw [e 0]; simp, by rw [e 1]; simp⟩

theorem exists_parab_row {g : SL(3, F)} (hg : g ∉ parab) :
    ∃ p : SL(3, F), p ∈ parab ∧ (g * p) 2 0 = 1 ∧ (g * p) 2 1 = 0 ∧ (g * p) 2 2 = 0 := by
  by_cases h0 : g 2 0 = 0
  · have h1 : g 2 1 ≠ 0 := fun h1 => hg ⟨h0, h1⟩
    refine ⟨slMk !![0, -g 2 1, 0; (g 2 1)⁻¹, 0, -(g 2 2 * (g 2 1)⁻¹); 0, 0, 1] ?_, ⟨?_, ?_⟩, ?_,
      ?_, ?_⟩
    · rw [det_fin_three]
      simp [h1]
    all_goals simp [coe_slMk, mul_apply, Fin.sum_univ_three, h0, h1]
    field_simp
    ring
  · refine ⟨slMk !![(g 2 0)⁻¹, -g 2 1, -(g 2 2 * (g 2 0)⁻¹); 0, g 2 0, 0; 0, 0, 1] ?_, ⟨?_, ?_⟩,
      ?_, ?_, ?_⟩
    · rw [det_fin_three]
      simp [h0]
    all_goals simp [coe_slMk, mul_apply, Fin.sum_univ_three, h0]
    all_goals field_simp
    all_goals ring

theorem isCoatom_parab : IsCoatom (parab : Subgroup SL(3, F)) := by
  refine ⟨fun h => ?_, fun M hM => ?_⟩
  · have h1 : slTrans (show (2 : Fin 3) ≠ 0 by decide) (1 : F) ∈ parab := h ▸ mem_top _
    simp [mem_parab, coe_slTrans, transvection, single_apply, one_apply] at h1
  · obtain ⟨g, hgM, hgP⟩ := SetLike.exists_of_lt hM
    obtain ⟨p, hp, hp0, hp1, hp2⟩ := exists_parab_row hgP
    rw [eq_top_iff]
    intro h _
    by_cases hh : h ∈ parab
    · exact hM.le hh
    obtain ⟨p', hp', hp'0, hp'1, hp'2⟩ := exists_parab_row hh
    have h1 : h * p' * (g * p)⁻¹ ∈ M :=
      hM.le (mul_inv_mem_parab (by rw [hp'0, hp0]) (by rw [hp'1, hp1]) (by rw [hp'2, hp2]))
    have h2 : h * p' ∈ M := by
      have := mul_mem h1 (mul_mem hgM (hM.le hp))
      rwa [inv_mul_cancel_right] at this
    have := mul_mem h2 (inv_mem (hM.le hp'))
    rwa [mul_inv_cancel_right] at this

theorem pow_apply_two_two {g : SL(3, F)} (hg : g ∈ parab) (n : ℕ) : (g ^ n) 2 2 = g 2 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨h0, h1⟩ := pow_mem hg n
    rw [pow_succ, pow_succ, ← ih]
    simp only [Matrix.SpecialLinearGroup.coe_mul, mul_apply, Fin.sum_univ_three, h0, h1, zero_mul,
      zero_add]

theorem exists_rad_mul_block {g : SL(3, F)} (hg : g ∈ parab) (h22 : g 2 2 = 1) :
    ∃ y ∈ rad, ∃ a : SL(3, F), a 0 2 = 0 ∧ a 1 2 = 0 ∧ a 2 0 = 0 ∧ a 2 1 = 0 ∧ a 2 2 = 1 ∧
      g = y * a := by
  have hdet := det_parab hg
  obtain ⟨g20, g21⟩ := hg
  rw [h22] at hdet
  refine ⟨slMk !![1, 0, g 0 2; 0, 1, g 1 2; 0, 0, 1] (by simp [det_fin_three]), ?_,
    slMk !![g 0 0, g 0 1, 0; g 1 0, g 1 1, 0; 0, 0, 1] ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [coe_slMk]
  · rw [det_fin_three]
    simp
    linear_combination hdet
  all_goals try simp [coe_slMk]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_slMk, mul_apply, Fin.sum_univ_three, g20, g21, h22]

theorem block_eq_of_ne_zero {a : SL(3, F)} (h02 : a 0 2 = 0) (h12 : a 1 2 = 0) (h20 : a 2 0 = 0)
    (h21 : a 2 1 = 0) (h22 : a 2 2 = 1) (hc : a 1 0 ≠ 0) :
    a = slTrans (show (0 : Fin 3) ≠ 1 by decide) ((a 0 0 - 1) / a 1 0) *
      slTrans (show (1 : Fin 3) ≠ 0 by decide) (a 1 0) *
      slTrans (show (0 : Fin 3) ≠ 1 by decide) ((a 1 1 - 1) / a 1 0) := by
  have hdet : a 0 0 * a 1 1 - a 0 1 * a 1 0 = 1 := by
    have h := a.2
    rw [det_fin_three, h02, h12, h20, h21, h22] at h
    linear_combination h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_slTrans, transvection, mul_apply, Fin.sum_univ_three, one_apply, single_apply, h02,
      h12, h20, h21, h22, hc]
  all_goals field_simp
  all_goals first | linear_combination hdet | linear_combination -hdet | linear_combination

theorem eq_one_of_pow_two_pow_eq_one {K : Type*} [Field K] [CharP K 2] {c : K} {k : ℕ}
    (h : c ^ 2 ^ k = 1) : c = 1 := by
  have h' : (c - 1) ^ 2 ^ k = 0 := by rw [sub_pow_char_pow, h, one_pow, sub_self]
  exact sub_eq_zero.1 ((pow_eq_zero_iff (pow_ne_zero _ two_ne_zero)).1 h')

theorem eq_slTrans_mul_of_mem_rad {y : SL(3, F)} (hy : y ∈ rad) :
    y = slTrans (show (1 : Fin 3) ≠ 2 by decide) (y 1 2) *
      slTrans (show (0 : Fin 3) ≠ 2 by decide) (y 0 2) := by
  obtain ⟨y00, y01, y10, y11, y20, y21, y22⟩ := hy
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_slTrans, transvection, mul_apply, Fin.sum_univ_three, one_apply, single_apply, y00,
      y01, y10, y11, y20, y21, y22]

theorem slTrans_mul_slTrans {i j : Fin 3} (hij : i ≠ j) (c c' : F) :
    slTrans hij c * slTrans hij c' = slTrans hij (c + c') :=
  Subtype.ext (transvection_mul_transvection_same i j hij c c')

end SL3

section Levi

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem map_rad_a2Hom : (rad : Subgroup SL(3, d.Γ₀)).map d.a2Hom = d.Y := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    rw [eq_slTrans_mul_of_mem_rad hy, map_mul, d.a2Hom_transvection, d.a2Hom_transvection,
      d.a2_12, d.a2_02]
    exact mul_mem (d.x₅_mem_Y _) (d.x₆_mem_Y _)
  · show d.U₅ ⊔ d.V ≤ _
    refine sup_le ?_ ?_
    · rintro _ ⟨c, rfl⟩
      exact ⟨_, slTrans_12_mem_rad c, by rw [d.a2Hom_transvection, d.a2_12]⟩
    · rintro _ ⟨c, rfl⟩
      exact ⟨_, slTrans_02_mem_rad c, by rw [d.a2Hom_transvection, d.a2_02]⟩

theorem a2Hom_mem_leviLong_of_block {a : SL(3, d.Γ₀)} (h02 : a 0 2 = 0) (h12 : a 1 2 = 0)
    (h20 : a 2 0 = 0) (h21 : a 2 1 = 0) (h22 : a 2 2 = 1) : d.a2Hom a ∈ d.leviLong := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have hx₁₀ : ∀ c, d.a2Hom (slTrans h10 c) ∈ d.leviLong := fun c => by
    rw [d.a2Hom_transvection, d.a2_10, d.negRoot_x₂]
    exact mul_mem (mul_mem d.v_mem_leviLong (d.x₂_mem_leviLong c)) d.v_mem_leviLong
  have hx₀₁ : ∀ c, d.a2Hom (slTrans h01 c) ∈ d.leviLong := fun c => by
    rw [d.a2Hom_transvection, d.a2_01]
    exact d.x₂_mem_leviLong c
  have key : ∀ b : SL(3, d.Γ₀), b 0 2 = 0 → b 1 2 = 0 → b 2 0 = 0 → b 2 1 = 0 → b 2 2 = 1 →
      b 1 0 ≠ 0 → d.a2Hom b ∈ d.leviLong := by
    intro b b02 b12 b20 b21 b22 hc
    rw [block_eq_of_ne_zero b02 b12 b20 b21 b22 hc, map_mul, map_mul]
    exact mul_mem (mul_mem (hx₀₁ _) (hx₁₀ _)) (hx₀₁ _)
  by_cases hc : a 1 0 = 0
  · have ha00 : a 0 0 ≠ 0 := by
      intro h00
      have h := a.2
      rw [det_fin_three, h00, hc, h20, h21] at h
      simp at h
    have e : a = slTrans h10 (-1) * (slTrans h10 1 * a) := by
      rw [← mul_assoc, slTrans_mul_slTrans, neg_add_cancel]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [coe_slTrans, transvection]
    rw [e, map_mul]
    refine mul_mem (hx₁₀ _) (key _ ?_ ?_ ?_ ?_ ?_ ?_) <;>
      simp [coe_slTrans, transvection, mul_apply, Fin.sum_univ_three, one_apply, single_apply, h02,
        h12, h20, h21, h22, hc, ha00]
  · exact key a h02 h12 h20 h21 h22 hc

end Levi

section InG

variable {G : Type} [Group G] {L : Subgroup G} {q : ℕ}

theorem injective_a2G (d : TrialityD4Data L q) : Function.Injective (L.subtype.comp d.a2Hom) :=
  L.subtype_injective.comp d.a2Hom_injective

theorem range_a2G (d : TrialityD4Data L q) :
    (L.subtype.comp d.a2Hom).range = d.leviJ₀.map L.subtype := by
  rw [MonoidHom.range_comp, d.range_a2Hom]

theorem map_rad_a2G (d : TrialityD4Data L q) :
    (rad : Subgroup SL(3, d.Γ₀)).map (L.subtype.comp d.a2Hom) = d.Y.map L.subtype := by
  rw [← Subgroup.map_map, map_rad_a2Hom d]

theorem comap_normalizer_Y_map (d : TrialityD4Data L q) :
    (normalizer ((d.Y.map L.subtype : Subgroup G) : Set G)).comap (L.subtype.comp d.a2Hom) =
      parab := by
  rw [← map_rad_a2G d, comap_normalizer_eq_of_le_range (map_le_range _ _),
    comap_map_eq_self_of_injective (injective_a2G d), normalizer_rad]

end InG

end AlphaOne

open AlphaOne

variable {G : Type} [Group G] {L : Subgroup G} {q : ℕ}

theorem a2Hom_mem_normalizer_Y_iff (d : TrialityD4Data L q) (k : SL(3, d.Γ₀)) :
    L.subtype (d.a2Hom k) ∈ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) ↔
      (k : Matrix (Fin 3) (Fin 3) d.Γ₀) 2 0 = 0 ∧ (k : Matrix (Fin 3) (Fin 3) d.Γ₀) 2 1 = 0 := by
  rw [← mem_parab, ← comap_normalizer_Y_map d]
  rfl

theorem isCoatom_normalizer_Y (d : TrialityD4Data L q) :
    IsCoatom ((normalizer ((d.Y.map L.subtype : Subgroup G) : Set G)).subgroupOf
      (d.leviJ₀.map L.subtype)) := by
  let e : SL(3, d.Γ₀) ≃* d.leviJ₀.map L.subtype :=
    (MonoidHom.ofInjective (injective_a2G d)).trans (MulEquiv.subgroupCongr (range_a2G d))
  have he : ∀ k, (e k : G) = L.subtype (d.a2Hom k) := fun _ => rfl
  have h : (normalizer ((d.Y.map L.subtype : Subgroup G) : Set G)).subgroupOf
      (d.leviJ₀.map L.subtype) = MulEquiv.mapSubgroup e parab := by
    ext x
    have hx : (x : G) = L.subtype (d.a2Hom (e.symm x)) := by rw [← he, MulEquiv.apply_symm_apply]
    rw [MulEquiv.coe_mapSubgroup, mem_map_equiv, mem_subgroupOf, hx, a2Hom_mem_normalizer_Y_iff d,
      mem_parab]
  rw [h, OrderIso.isCoatom_iff]
  exact isCoatom_parab

theorem mem_Y_sup_leviLong_of_two_element (d : TrialityD4Data L q) {g : G}
    (hgK : g ∈ d.leviJ₀.map L.subtype)
    (hgN : g ∈ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G))
    {k : ℕ} (hk : g ^ 2 ^ k = 1) :
    g ∈ d.Y.map L.subtype ⊔ d.leviLong.map L.subtype := by
  rw [← range_a2G d] at hgK
  obtain ⟨m, rfl⟩ := hgK
  have hm : m ∈ parab := by
    rw [← comap_normalizer_Y_map d]
    exact hgN
  have hmk : m ^ 2 ^ k = 1 := injective_a2G d (by rw [map_pow, hk, map_one])
  have h22 : (m : Matrix (Fin 3) (Fin 3) d.Γ₀) 2 2 = 1 := by
    have h := pow_apply_two_two hm (2 ^ k)
    rw [hmk] at h
    have h' : (m 2 2) ^ 2 ^ k = 1 := by rw [← h]; simp
    have hΓ : ((m 2 2 : d.Γ₀) : d.Γ) ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val h'
    exact Subtype.ext (by simpa using eq_one_of_pow_two_pow_eq_one hΓ)
  obtain ⟨y, hy, a, a02, a12, a20, a21, a22, rfl⟩ := exists_rad_mul_block hm h22
  rw [map_mul]
  refine mul_mem (mem_sup_left ?_) (mem_sup_right ?_)
  · rw [← map_rad_a2G d]
    exact ⟨y, hy, rfl⟩
  · exact ⟨_, a2Hom_mem_leviLong_of_block d a02 a12 a20 a21 a22, rfl⟩

end AlphaOne

section Coatom

theorem isCoatom_comap_of_surjective {C D : Type*} [Group C] [Group D] (π : C →* D)
    (hπ : Function.Surjective π) {B : Subgroup D} (hB : IsCoatom B) : IsCoatom (B.comap π) := by
  refine ⟨?_, fun M hM => ?_⟩
  · intro htop
    apply hB.1
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := hπ y
    have : x ∈ B.comap π := htop ▸ mem_top x
    exact this
  · have hker : π.ker ≤ M := fun x hx =>
      hM.le (by rw [mem_comap, MonoidHom.mem_ker.1 hx]; exact one_mem B)
    have hBM : B ≤ M.map π := by
      intro y hy
      obtain ⟨x, rfl⟩ := hπ y
      exact ⟨x, hM.le hy, rfl⟩
    have hne : B ≠ M.map π := by
      intro heq
      have : M ≤ B.comap π := fun x hx => by
        rw [mem_comap, heq]
        exact ⟨x, hx, rfl⟩
      exact absurd hM (not_lt_of_ge this)
    have htop := hB.2 (M.map π) (lt_of_le_of_ne hBM hne)
    rw [eq_top_iff]
    intro x _
    obtain ⟨m, hm, hmx⟩ : π x ∈ M.map π := htop ▸ mem_top _
    have hmem : m⁻¹ * x ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hmx, inv_mul_cancel]
    have := mul_mem hm (hker hmem)
    rwa [mul_inv_cancel_left] at this

end Coatom

section DiagE

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem odd_card_ker_diag (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    Odd (Nat.card ((diagonalHom K t hK.comm).ker.map K.subtype)) := by
  rw [Subgroup.card_map_of_injective K.subtype_injective]
  exact Common.odd_card_ker_diagonalHom_of_le hK.comm (M := K ⊓ Kᵍ[t]) le_rfl
    (odd_card_inf_conj h d hp hK)

theorem eq_one_of_mem_ker_diag_of_sq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) {z : K}
    (hz : z ∈ (diagonalHom K t hK.comm).ker) (hz2 : z * z = 1) : z = 1 := by
  have h1 : (z : G) = 1 := by
    refine eq_one_of_pow_eq_one_of_mem_odd (odd_card_ker_diag h d hp hK) ⟨z, hz, rfl⟩ (k := 1) ?_
    have := congrArg Subtype.val hz2
    simpa [sq] using this
  exact Subtype.ext h1

end DiagE

section DiagE2

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem eOne_comm (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) {K : Subgroup G}
    (hK : IsLayerComponent d t K) : ⁅eOne d t K, (eOne d t K)ᵍ[t]⁆ = ⊥ :=
  le_bot_iff.1 (hK.comm ▸ Subgroup.commutator_mono inf_le_right (Subgroup.map_mono inf_le_right))

theorem diag_eOne (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    (∀ e ∈ eOne d t K, e * (t * e * t) ∈ d.Y.map L.subtype) ∧
      ∀ y ∈ d.Y.map L.subtype, ∃ e ∈ eOne d t K, y = e * (t * e * t) := by
  have hlay := hp.layer
  obtain ⟨hdec, hinf, -, -, -⟩ := eOne_decomp h d hp hK
  have hY := (h.yamada_5_9_2 d hlay).2.2.2.2
  constructor
  · intro e he
    rw [← hY]
    refine ⟨?_, ?_⟩
    · rw [hdec]
      exact mul_mem (mem_sup_left he) (mem_sup_right (conj_mem_conjG h.t_mul_t he))
    · have := Common.range_diagonalHom_le hK.comm h.t_mul_t
        ⟨⟨e, he.2⟩, rfl⟩
      simpa [Common.diagonalHom_apply_of_mul_self hK.comm h.t_mul_t] using this
  · intro y hy
    have hyY₂ : y ∈ yamadaY₂ d t := by
      rw [← hY] at hy
      exact hy.1
    have hyt : t * y = y * t := by
      rw [← hY] at hy
      exact mem_centralizer_singleton_iff.1 hy.2 |>.symm
    obtain ⟨e, he, rfl⟩ := exists_eq_mul_conj_of_mem_centralizer h.t_mul_t (eOne_comm h d hK) hinf
      (hdec ▸ hyY₂) hyt
    exact ⟨e, he, rfl⟩

end DiagE2

section NormE

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem mem_normalizer_eOne_iff (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) {k : G} (hk : k ∈ K) :
    k ∈ normalizer ((eOne d t K : Subgroup G) : Set G) ↔
      k * (t * k * t) ∈ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) := by
  obtain ⟨hiY, hYi⟩ := diag_eOne h d hp hK
  obtain ⟨-, -, -, -, hel⟩ := eOne_decomp h d hp hK
  set Δ := diagonalHom K t hK.comm with hΔ
  have hΔval : ∀ x : K, Δ x = (x : G) * (t * x * t) :=
    fun x => Common.diagonalHom_apply_of_mul_self hK.comm h.t_mul_t x
  have hsq : ∀ e ∈ eOne d t K, e * e = 1 := fun e he => by rw [← sq]; exact hel.2 e he
  have hconj : ∀ e ∈ eOne d t K, (k * e * k⁻¹) * (t * (k * e * k⁻¹) * t) =
      (k * (t * k * t)) * (e * (t * e * t)) * (k * (t * k * t))⁻¹ := by
    intro e he
    have hh : Δ (⟨k, hk⟩ * ⟨e, he.2⟩ * (⟨k, hk⟩ : K)⁻¹) =
        Δ ⟨k, hk⟩ * Δ ⟨e, he.2⟩ * (Δ ⟨k, hk⟩)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [hΔval (⟨k, hk⟩ * ⟨e, he.2⟩ * (⟨k, hk⟩ : K)⁻¹), hΔval ⟨k, hk⟩, hΔval ⟨e, he.2⟩] at hh
    simpa using hh
  constructor
  · intro hkN
    refine mem_normalizer_fintype fun y hy => ?_
    obtain ⟨e, he, rfl⟩ := hYi y hy
    have hke : k * e * k⁻¹ ∈ eOne d t K := (mem_normalizer_iff.1 hkN e).1 he
    rw [← hconj e he]
    exact hiY _ hke
  · intro hkN
    refine mem_normalizer_fintype fun e he => ?_
    have hxK : k * e * k⁻¹ ∈ K := mul_mem (mul_mem hk he.2) (inv_mem hk)
    have hxY : (k * e * k⁻¹) * (t * (k * e * k⁻¹) * t) ∈ d.Y.map L.subtype := by
      rw [hconj e he]
      exact (mem_normalizer_iff.1 hkN _).1 (hiY e he)
    obtain ⟨e', he', he'eq⟩ := hYi _ hxY
    set z : K := (⟨e', he'.2⟩ : K)⁻¹ * ⟨k * e * k⁻¹, hxK⟩ with hz
    have hzker : z ∈ Δ.ker := by
      rw [MonoidHom.mem_ker, hz, map_mul, map_inv, hΔval ⟨e', he'.2⟩, hΔval ⟨k * e * k⁻¹, hxK⟩]
      simp only
      rw [← he'eq, inv_mul_cancel]
    have hzc := (mem_center_iff.1 (Common.ker_diagonalHom_le_center hK.comm hzker))
    have hE'2 : (⟨e', he'.2⟩ : K) * ⟨e', he'.2⟩ = 1 := Subtype.ext (by simpa using hsq e' he')
    have hX2 : (⟨k * e * k⁻¹, hxK⟩ : K) * ⟨k * e * k⁻¹, hxK⟩ = 1 := by
      refine Subtype.ext ?_
      change (k * e * k⁻¹) * (k * e * k⁻¹) = 1
      calc (k * e * k⁻¹) * (k * e * k⁻¹) = k * (e * e) * k⁻¹ := by group
        _ = 1 := by rw [hsq e he]; group
    have hc' : (⟨k * e * k⁻¹, hxK⟩ : K) * ((⟨e', he'.2⟩ : K)⁻¹ * ⟨k * e * k⁻¹, hxK⟩) =
        ((⟨e', he'.2⟩ : K)⁻¹ * ⟨k * e * k⁻¹, hxK⟩) * ⟨k * e * k⁻¹, hxK⟩ := hzc _
    have hz2 : z * z = 1 := by
      calc z * z = ((⟨e', he'.2⟩ : K)⁻¹ * ⟨k * e * k⁻¹, hxK⟩) *
            ((⟨e', he'.2⟩ : K)⁻¹ * ⟨k * e * k⁻¹, hxK⟩) := rfl
        _ = (⟨e', he'.2⟩ : K)⁻¹ * (⟨k * e * k⁻¹, hxK⟩ * ((⟨e', he'.2⟩ : K)⁻¹ *
            ⟨k * e * k⁻¹, hxK⟩)) := by group
        _ = (⟨e', he'.2⟩ : K)⁻¹ * (((⟨e', he'.2⟩ : K)⁻¹ * ⟨k * e * k⁻¹, hxK⟩) *
            ⟨k * e * k⁻¹, hxK⟩) := by rw [hc']
        _ = ((⟨e', he'.2⟩ : K) * ⟨e', he'.2⟩)⁻¹ * (⟨k * e * k⁻¹, hxK⟩ * ⟨k * e * k⁻¹, hxK⟩) := by
            group
        _ = 1 := by rw [hE'2, hX2]; simp
    have hz1 := eq_one_of_mem_ker_diag_of_sq h d hp hK hzker hz2
    have hxe : (⟨k * e * k⁻¹, hxK⟩ : K) = ⟨e', he'.2⟩ :=
      (inv_injective (mul_eq_one_iff_eq_inv.1 hz1)).symm
    have hxe' : k * e * k⁻¹ = e' := congrArg Subtype.val hxe
    rw [hxe']
    exact he'

end NormE

section CoatomE

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem isCoatom_normalizer_eOne (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    IsCoatom ((normalizer ((eOne d t K : Subgroup G) : Set G)).subgroupOf K) := by
  obtain ⟨D, hD, -, hDval⟩ := diag_surjective h d hp hK
  have hcoatom := isCoatom_normalizer_Y d
  have := isCoatom_comap_of_surjective D hD hcoatom
  convert this using 1
  ext k
  rw [mem_subgroupOf, mem_comap, mem_subgroupOf, hDval k]
  exact mem_normalizer_eOne_iff h d hp hK k.2

end CoatomE

section ZcProd

variable {G : Type*} [Group G] [Finite G]

theorem zc_sup_eq {A B : Subgroup G} (hcomm : ⁅A, B⁆ = ⊥) :
    zc (A ⊔ B) = zc A ⊔ zc B := by
  have hc := commute_of_commutator_eq_bot hcomm
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hc
  apply le_antisymm
  · intro w hw
    have hw' : w ∈ ((A ⊔ B : Subgroup G) : Set G) := hw.1
    rw [hset] at hw'
    obtain ⟨a, ha, b, hb, rfl⟩ := hw'
    have hwc := fun x (hx : x ∈ A ⊔ B) => mem_centralizer_iff.1 hw.2 x hx
    have haz : a ∈ zc A := by
      refine ⟨ha, mem_centralizer_iff.2 fun x hx => ?_⟩
      have h1 := hwc x (mem_sup_left hx)
      have h2 : x * b = b * x := hc x hx b hb
      have e1 : (x * a) * b = (a * x) * b := by
        calc (x * a) * b = x * (a * b) := by rw [mul_assoc]
          _ = (a * b) * x := h1
          _ = a * (x * b) := by rw [mul_assoc, ← h2]
          _ = (a * x) * b := by rw [mul_assoc]
      exact mul_right_cancel e1
    have hbz : b ∈ zc B := by
      refine ⟨hb, mem_centralizer_iff.2 fun x hx => ?_⟩
      have h1 := hwc x (mem_sup_right hx)
      have h2 : a * x = x * a := hc a ha x hx
      have e1 : a * (x * b) = a * (b * x) := by
        calc a * (x * b) = (a * x) * b := by rw [mul_assoc]
          _ = (x * a) * b := by rw [h2]
          _ = x * (a * b) := by rw [mul_assoc]
          _ = (a * b) * x := h1
          _ = a * (b * x) := by rw [mul_assoc]
      exact mul_left_cancel e1
    exact mul_mem_sup haz hbz
  · refine sup_le (fun z hz => ?_) (fun z hz => ?_)
    · refine ⟨mem_sup_left hz.1, mem_centralizer_iff.2 fun x hx => ?_⟩
      have hx' : x ∈ ((A ⊔ B : Subgroup G) : Set G) := hx
      rw [hset] at hx'
      obtain ⟨a, ha, b, hb, rfl⟩ := hx'
      have h1 : a * z = z * a := mem_centralizer_iff.1 hz.2 a ha
      have h2 : z * b = b * z := (hc z hz.1 b hb)
      calc a * b * z = a * (b * z) := by rw [mul_assoc]
        _ = a * (z * b) := by rw [h2]
        _ = (a * z) * b := by rw [mul_assoc]
        _ = (z * a) * b := by rw [h1]
        _ = z * (a * b) := by rw [mul_assoc]
    · refine ⟨mem_sup_right hz.1, mem_centralizer_iff.2 fun x hx => ?_⟩
      have hx' : x ∈ ((A ⊔ B : Subgroup G) : Set G) := hx
      rw [hset] at hx'
      obtain ⟨a, ha, b, hb, rfl⟩ := hx'
      have h1 : b * z = z * b := mem_centralizer_iff.1 hz.2 b hb
      have h2 : a * z = z * a := (hc a ha z hz.1)
      calc a * b * z = a * (b * z) := by rw [mul_assoc]
        _ = a * (z * b) := by rw [h1]
        _ = (a * z) * b := by rw [mul_assoc]
        _ = (z * a) * b := by rw [h2]
        _ = z * (a * b) := by rw [mul_assoc]

theorem zc_map_conj (A : Subgroup G) (g : G) :
    zc (A.map (MulAut.conj g).toMonoidHom) = (zc A).map (MulAut.conj g).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, hx⟩
    refine ⟨a, ⟨ha, mem_centralizer_iff.2 fun a' ha' => ?_⟩, rfl⟩
    have h1 := mem_centralizer_iff.1 hx ((MulAut.conj g).toMonoidHom a') ⟨a', ha', rfl⟩
    have h2 : (MulAut.conj g) (a' * a) = (MulAut.conj g) (a * a') := by
      rw [map_mul, map_mul]
      exact h1
    exact (MulAut.conj g).injective h2
  · rintro ⟨a, ⟨ha, hac⟩, rfl⟩
    refine ⟨⟨a, ha, rfl⟩, mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨a', ha', rfl⟩
    have h1 := mem_centralizer_iff.1 hac a' ha'
    have h2 := congrArg (MulAut.conj g) h1
    rw [map_mul, map_mul] at h2
    exact h2

end ZcProd

section A4One

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem yamadaD₁_le_yamadaD₅ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    yamadaD₁ d t ≤ yamadaD₅ d t :=
  le_inf ((h.yamadaD₁_le_yamadaC₁ d).trans (yamadaC₁_le_yamadaC₅ d t))
    fun x hx => mem_centralizer_iff.2 fun v hv => (mem_centralizer_iff.1 hv.2 x hx).symm

theorem yamadaV₁_eq_zc_prodX (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) : yamadaV₁ d t = zc (prodX d t) := by
  have hQX : yamadaD₁ d t ⊓ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ≤
      prodX d t := inf_le_inf_right _ (yamadaD₁_le_yamadaD₅ h d)
  exact (h.yamada_5_6_3 d hp.layer (prodX d t) (prodX_sylow h d hp).1
    (t_mem_normalizer_prodX h d) hQX).1

theorem yamadaV₁_eq_zc_sup (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    yamadaV₁ d t = zc (qThree d t K) ⊔ (zc (qThree d t K))ᵍ[t] := by
  obtain ⟨hsup, -, hcomm, -, -⟩ := qThree_decomp h d hp hK
  rw [yamadaV₁_eq_zc_prodX h d hp, hsup, zc_sup_eq hcomm, zc_map_conj]

end A4One

section A4Two

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem zc_qThree_le (d : TrialityD4Data L (2 ^ f)) {K : Subgroup G} :
    zc (qThree d t K) ≤ K := (inf_le_left : zc (qThree d t K) ≤ qThree d t K).trans inf_le_right

theorem card_zc_qThree (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) : Nat.card (zc (qThree d t K)) = 2 ^ f :=
  (heisLike_qThree h d hp hK).card_center

theorem zc_inf_conj (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    zc (qThree d t K) ⊓ (zc (qThree d t K))ᵍ[t] = ⊥ := by
  obtain ⟨-, hinf, -, -, -⟩ := qThree_decomp h d hp hK
  have hZ : zc (qThree d t K) ≤ qThree d t K := inf_le_left
  exact le_bot_iff.1 (hinf ▸ inf_le_inf hZ (Subgroup.map_mono hZ))

theorem zc_qThree_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    zc (qThree d t K) = eOne d t K ⊓ yamadaV₁ d t := by
  obtain ⟨hsup, hinf, hcomm, -, -⟩ := qThree_decomp h d hp hK
  have hV := yamadaV₁_eq_zc_sup h d hp hK
  have hZ : zc (qThree d t K) ≤ qThree d t K := inf_le_left
  apply le_antisymm
  · refine le_inf (eOne_normal h d hp hK).1 ?_
    rw [hV]
    exact le_sup_left
  · rintro x ⟨hxE, hxV⟩
    rw [hV] at hxV
    have hZcomm : ⁅zc (qThree d t K), (zc (qThree d t K))ᵍ[t]⁆ = ⊥ :=
      le_bot_iff.1 (hcomm ▸ Subgroup.commutator_mono hZ (Subgroup.map_mono hZ))
    obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (zc (qThree d t K))
      (zc (qThree d t K))ᵍ[t] (commute_of_commutator_eq_bot hZcomm)
    have hx' : x ∈ ((zc (qThree d t K) ⊔ (zc (qThree d t K))ᵍ[t] : Subgroup G) : Set G) := hxV
    rw [hset] at hx'
    obtain ⟨z, hz, z', hz', rfl⟩ := hx'
    have hzK : z ∈ K := zc_qThree_le d hz
    have hxK : z * z' ∈ K := hxE.2
    have hz'K : z' ∈ K := by
      have := mul_mem (inv_mem hzK) hxK
      rwa [inv_mul_cancel_left] at this
    have hz'X : z' ∈ prodX d t := by
      have : z' ∈ (qThree d t K)ᵍ[t] := Subgroup.map_mono hZ hz'
      exact (hsup ▸ (mem_sup_right this))
    have hz'Q : z' ∈ qThree d t K ⊓ (qThree d t K)ᵍ[t] :=
      ⟨⟨hz'X, hz'K⟩, Subgroup.map_mono hZ hz'⟩
    rw [hinf, mem_bot] at hz'Q
    rw [hz'Q]
    simpa using hz

end A4Two

section A4Comp

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem layer_le_normalizer_K {d : TrialityD4Data L (2 ^ f)} {K : Subgroup G}
    (hK : IsLayerComponent d t K) : jZeroLayer d ≤ normalizer (K : Set G) := by
  rw [hK.layer_eq]
  exact sup_le_normalizer_left_of_commutator_eq_bot hK.comm

theorem layer_le_normalizer_Kt {d : TrialityD4Data L (2 ^ f)} {K : Subgroup G}
    (hK : IsLayerComponent d t K) : jZeroLayer d ≤ normalizer (Kᵍ[t] : Set G) := by
  rw [hK.layer_eq]
  exact sup_le_normalizer_right_of_commutator_eq_bot hK.comm

theorem isComponent_subgroupOf_layer {d : TrialityD4Data L (2 ^ f)} {S : Subgroup G}
    (hS : S ≤ jZeroLayer d) (hSn : jZeroLayer d ≤ normalizer (S : Set G))
    (hq : CFSG.IsQuasisimple ↥S) : CFSG.IsComponent (S.subgroupOf (jZeroLayer d)) :=
  ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hS).symm hq,
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hS).2 hSn).isSubnormal⟩

theorem eq_of_subgroupOf_eq {E A B : Subgroup G} (hA : A ≤ E) (hB : B ≤ E)
    (h : A.subgroupOf E = B.subgroupOf E) : A = B := by
  have := Subgroup.subgroupOf_inj.1 h
  rwa [inf_eq_left.2 hA, inf_eq_left.2 hB] at this

theorem conj_u_eq_or (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    Kᵍ[uG d] = K ∨ Kᵍ[uG d] = Kᵍ[t] := by
  have huE : uG d ∈ normalizer ((jZeroLayer d : Subgroup G) : Set G) :=
    Setup.normalizer_le_normalizer_jZeroLayer d (uG_mem_normalizer_J₀ d)
  have hKE : K ≤ jZeroLayer d := by rw [hK.layer_eq]; exact le_sup_left
  have hKtE : Kᵍ[t] ≤ jZeroLayer d := by rw [hK.layer_eq]; exact le_sup_right
  have hK'E : Kᵍ[uG d] ≤ jZeroLayer d := map_conj_le_of_mem_normalizer hKE (inv_mem huE)
  have hq : CFSG.IsQuasisimple ↥K := isLayerComponent_isQuasisimple hK
  have hq' : CFSG.IsQuasisimple ↥(Kᵍ[uG d]) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (K.equivMapOfInjective _ (MulAut.conj (uG d)⁻¹).injective) hq
  have hqt : CFSG.IsQuasisimple ↥(Kᵍ[t]) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (K.equivMapOfInjective _ (MulAut.conj t⁻¹).injective) hq
  have hK'n : jZeroLayer d ≤ normalizer (Kᵍ[uG d] : Set G) := by
    intro e he
    refine mem_normalizer_fintype fun x hx => ?_
    obtain ⟨k, hk, rfl⟩ := hx
    have hue : uG d * e * (uG d)⁻¹ ∈ jZeroLayer d := (mem_normalizer_iff.1 huE e).1 he
    have hk' : (uG d * e * (uG d)⁻¹) * k * (uG d * e * (uG d)⁻¹)⁻¹ ∈ K :=
      (mem_normalizer_iff.1 (layer_le_normalizer_K hK hue) k).1 hk
    refine ⟨_, hk', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hKc := isComponent_subgroupOf_layer hKE (layer_le_normalizer_K hK) hq
  have hKtc := isComponent_subgroupOf_layer hKtE (layer_le_normalizer_Kt hK) hqt
  have hK'c := isComponent_subgroupOf_layer hK'E hK'n hq'
  have hmapc : ∀ A B : Subgroup G, A ≤ jZeroLayer d → B ≤ jZeroLayer d →
      ⁅A.subgroupOf (jZeroLayer d), B.subgroupOf (jZeroLayer d)⁆ = ⊥ → ⁅A, B⁆ = ⊥ := by
    intro A B hA hB hAB
    have := congrArg (Subgroup.map (jZeroLayer d).subtype) hAB
    rwa [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 hA, inf_eq_left.2 hB, Subgroup.map_bot] at this
  rcases CFSG.LocalCores.distinct_components_commute hK'c hKc with h1 | h1
  · exact Or.inl (eq_of_subgroupOf_eq hK'E hKE h1)
  · rcases CFSG.LocalCores.distinct_components_commute hK'c hKtc with h2 | h2
    · exact Or.inr (eq_of_subgroupOf_eq hK'E hKtE h2)
    · exfalso
      have c1 := hmapc _ _ hK'E hKE h1
      have c2 := hmapc _ _ hK'E hKtE h2
      have h3 : jZeroLayer d ≤ centralizer (Kᵍ[uG d] : Set G) := by
        rw [hK.layer_eq]
        exact sup_le
          (Subgroup.le_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 c1))
          (Subgroup.le_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 c2))
      have h4 : ⁅Kᵍ[uG d], Kᵍ[uG d]⁆ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hK'E.trans h3)
      have h5 : ⁅Kᵍ[uG d], Kᵍ[uG d]⁆ = Kᵍ[uG d] :=
        (isPerfect_subgroup_iff_commutator_eq _).1 hq'.1
      have hnt : Nontrivial ↥(Kᵍ[uG d]) := CFSG.LocalCores.isQuasisimple_nontrivial hq'
      exact (Subgroup.nontrivial_iff_ne_bot _).1 hnt (h5.symm.trans h4)

end A4Comp

section A4Final

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem map_conj_map_conj_comm {g h : G} (hgh : g * h = h * g) (A : Subgroup G) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      (A.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc h * (g * x * g⁻¹) * h⁻¹ = (h * g) * x * (h * g)⁻¹ := by group
    _ = (g * h) * x * (g * h)⁻¹ := by rw [hgh]
    _ = g * (h * x * h⁻¹) * g⁻¹ := by group

theorem uG_mul_self (d : TrialityD4Data L (2 ^ f)) : uG d * uG d = 1 := by
  have := congrArg Subtype.val d.u_mul_self
  simpa using this

theorem uG_mul_t (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) : uG d * t = t * uG d :=
  mem_centralizer_iff.1 h.htL _ d.u.2

theorem conj_u_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) : Kᵍ[uG d] = K := by
  rcases conj_u_eq_or h d hp hK with h1 | h1
  · exact h1
  · exfalso
    have hu := S5_u_centralizes_V₁ h d hp.layer
    have hZV : zc (qThree d t K) ≤ yamadaV₁ d t := by
      rw [zc_qThree_eq h d hp hK]
      exact inf_le_right
    have hZ : zc (qThree d t K) ≤ Kᵍ[uG d] := by
      intro z hz
      rw [Common.mem_map_conj_inv_iff]
      have hc : z * uG d = uG d * z := mem_centralizer_iff.1 hu z (hZV hz)
      rw [← hc, mul_inv_cancel_right]
      exact zc_qThree_le d hz
    rw [h1] at hZ
    have hZ2 : zc (qThree d t K) ≤ K ⊓ Kᵍ[t] := le_inf (zc_qThree_le d) hZ
    have hZp : IsPGroup 2 (zc (qThree d t K)) :=
      (isPGroup_prodX h d hp).to_le ((inf_le_left : zc (qThree d t K) ≤ qThree d t K).trans
        inf_le_left)
    have hbot := inf_eq_bot_of_isPGroup_of_odd hZp (odd_card_inf_conj h d hp hK)
    rw [inf_eq_left.2 hZ2] at hbot
    have hc := card_zc_qThree h d hp hK
    rw [hbot, Subgroup.card_bot] at hc
    have hf : 1 ≤ f := by have := hp.two_le; omega
    have : 2 ^ 1 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega

end A4Final

section A4Three

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem qThree_eq_eOne_sup_conj (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    qThree d t K = eOne d t K ⊔ (eOne d t K)ᵍ[uG d] := by
  obtain ⟨hdec, -, -, hle, -⟩ := eOne_decomp h d hp hK
  obtain ⟨hsup, hinf, hcomm, -, -⟩ := qThree_decomp h d hp hK
  have hKu := conj_u_eq h d hp hK
  have hXeq := prodX_eq_sup h d hp
  have hu2 := uG_mul_self d
  have hE₁K : eOne d t K ≤ K := inf_le_right
  have hE₁X : eOne d t K ≤ prodX d t := hle.trans inf_le_left
  have huX : (eOne d t K)ᵍ[uG d] ≤ prodX d t := by
    rw [conjG_eq_map_conj hu2, hXeq]
    refine le_sup_of_le_right (Subgroup.map_mono ?_)
    rw [hdec]
    exact le_sup_left
  set M := eOne d t K ⊔ (eOne d t K)ᵍ[uG d] with hM
  have hMK : M ≤ K := sup_le hE₁K ((Subgroup.map_mono hE₁K).trans hKu.le)
  have hMX : M ≤ prodX d t := sup_le hE₁X huX
  have hMQ : M ≤ qThree d t K := le_inf hMX hMK
  apply le_antisymm _ hMQ
  have hut : (uG d)⁻¹ * t⁻¹ = t⁻¹ * (uG d)⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, uG_mul_t h d]
  have hMt : Mᵍ[t] = (eOne d t K)ᵍ[t] ⊔ ((eOne d t K)ᵍ[t])ᵍ[uG d] := by
    rw [hM, Subgroup.map_sup]
    congr 1
    exact map_conj_map_conj_comm hut _
  have hXMt : prodX d t = M ⊔ Mᵍ[t] := by
    have hXeq' : prodX d t = (eOne d t K ⊔ (eOne d t K)ᵍ[t]) ⊔
        ((eOne d t K)ᵍ[uG d] ⊔ ((eOne d t K)ᵍ[t])ᵍ[uG d]) := by
      rw [hXeq, ← conjG_eq_map_conj hu2, hdec, Subgroup.map_sup]
    rw [hXeq', hMt, hM]
    ac_rfl
  intro x hx
  have hMtK : Mᵍ[t] ≤ Kᵍ[t] := Subgroup.map_mono hMK
  have hcMMt : ∀ a ∈ M, ∀ b ∈ Mᵍ[t], a * b = b * a :=
    commute_of_commutator_eq_bot
      (le_bot_iff.1 (hK.comm ▸ Subgroup.commutator_mono hMK hMtK))
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute M Mᵍ[t] hcMMt
  have hx' : x ∈ ((M ⊔ Mᵍ[t] : Subgroup G) : Set G) := by
    rw [← hXMt]
    exact hx.1
  rw [hset] at hx'
  obtain ⟨m, hm, m', hm', rfl⟩ := hx'
  have hm'K : m' ∈ K := by
    have := mul_mem (inv_mem (hMK hm)) hx.2
    rwa [inv_mul_cancel_left] at this
  have hm'X : m' ∈ prodX d t := hXMt ▸ mem_sup_right hm'
  have hm'Q : m' ∈ qThree d t K ⊓ (qThree d t K)ᵍ[t] :=
    ⟨⟨hm'X, hm'K⟩, Subgroup.map_mono hMQ hm'⟩
  rw [hinf, mem_bot] at hm'Q
  rw [hm'Q]
  simpa using hm

end A4Three

section OddPower

variable {G : Type*} [Group G]

theorem exists_pow_eq_of_odd (B : Subgroup G) (hB : Odd (Nat.card B)) {g : G} {k : ℕ}
    (hg : g ^ 2 ^ k = 1) : ∃ N : ℕ, g ^ N = g ∧ ∀ x ∈ B, x ^ N = 1 := by
  have hfin : Finite B := Nat.finite_of_card_ne_zero hB.pos.ne'
  have hcop : Nat.Coprime (Nat.card B) (orderOf g) := by
    have h1 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hg
    exact (Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hB)).coprime_dvd_right h1
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨Nat.card B * m, by rw [pow_mul]; exact hm, fun x hx => ?_⟩
  have h1 : (⟨x, hx⟩ : B) ^ Nat.card B = 1 := pow_card_eq_one'
  have h2 : x ^ Nat.card B = 1 := congrArg Subtype.val h1
  rw [pow_mul, h2, one_pow]

theorem mem_of_mul_of_odd {M B : Subgroup G} (hB : Odd (Nat.card B)) {m z p : G} (hm : m ∈ M)
    (hz : z ∈ B) (hc : Commute m z) (hp : p = m * z) {k : ℕ} (hk : p ^ 2 ^ k = 1) : p ∈ M := by
  obtain ⟨N, hN, hB'⟩ := exists_pow_eq_of_odd B hB hk
  have : p = m ^ N := by
    calc p = p ^ N := hN.symm
      _ = (m * z) ^ N := by rw [hp]
      _ = m ^ N := by rw [hc.mul_pow, hB' z hz, mul_one]
  rw [this]
  exact pow_mem hm N

theorem exists_two_parts {B : Subgroup G} (hB : Odd (Nat.card B)) {a b : G} (hab : Commute a b)
    {k : ℕ} (hg : (a * b) ^ 2 ^ k = 1) (ha : a ^ 2 ^ k ∈ B) :
    ∃ N : ℕ, a * b = a ^ N * b ^ N ∧ (a ^ N) ^ 2 ^ k = 1 ∧ (b ^ N) ^ 2 ^ k = 1 := by
  obtain ⟨N, hN, hB'⟩ := exists_pow_eq_of_odd B hB hg
  have hb : b ^ 2 ^ k ∈ B := by
    have h1 : a ^ 2 ^ k * b ^ 2 ^ k = 1 := by rw [← hab.mul_pow]; exact hg
    rw [eq_inv_of_mul_eq_one_right h1]
    exact inv_mem ha
  refine ⟨N, ?_, ?_, ?_⟩
  · rw [← hab.mul_pow, hN]
  · rw [← pow_mul, mul_comm, pow_mul, hB' _ ha]
  · rw [← pow_mul, mul_comm, pow_mul, hB' _ hb]

end OddPower

section OTwo

variable {G : Type*} [Group G]

theorem oTwoPrimeRes_le_self (X : Subgroup G) : oTwoPrimeRes X ≤ X :=
  (Subgroup.closure_le _).2 fun _ hx => hx.1

theorem mem_oTwoPrimeRes {X : Subgroup G} {x : G} (hx : x ∈ X) (hk : ∃ k : ℕ, x ^ 2 ^ k = 1) :
    x ∈ oTwoPrimeRes X :=
  Subgroup.subset_closure ⟨hx, hk⟩

theorem oTwoPrimeRes_le_of {X M : Subgroup G} (h : ∀ x ∈ X, (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ M) :
    oTwoPrimeRes X ≤ M :=
  (Subgroup.closure_le _).2 fun _ hx => h _ hx.1 hx.2

end OTwo

section Sl2Gen

open CFSG.LieType.Steinberg CFSG.LieType.CentralExt Matrix

@[expose] def sl2RelsAux (F : Type*) [Field F] : RankOneRels (SpecialLinearGroup (Fin 2) F) F where
  x := sl2Upper
  y := sl2Lower
  x_add a b := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper, coe_sl2Upper, coe_sl2Upper]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]
  y_add a b := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Lower, coe_sl2Lower, coe_sl2Lower]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]
  conj_x t ht a := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_sl2Upper,
      coe_sl2Lower]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two] <;> field_simp <;> ring

theorem sl2RelsAux_x {F : Type*} [Field F] (a : F) : (sl2RelsAux F).x a = sl2Upper a :=
  rfl

theorem sl2RelsAux_y {F : Type*} [Field F] (a : F) : (sl2RelsAux F).y a = sl2Lower a :=
  rfl

theorem sl2RelsAux_sub (F : Type) [Field F] : (sl2RelsAux F).sub = ⊤ := by
  rw [eq_top_iff,
    ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field (ι := Fin 2)
      (K := F), Subgroup.closure_le]
  rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
  rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk]
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · have : Matrix.SpecialLinearGroup.transvection hij c = sl2Upper c := by
      refine Matrix.SpecialLinearGroup.ext _ _ fun a b => ?_
      fin_cases a <;> fin_cases b <;>
        simp [Matrix.SpecialLinearGroup.transvection_coe, coe_sl2Upper, Matrix.single_apply]
    rw [this]
    exact (sl2RelsAux F).x_mem_sub c
  · have : Matrix.SpecialLinearGroup.transvection hij c = sl2Lower c := by
      refine Matrix.SpecialLinearGroup.ext _ _ fun a b => ?_
      fin_cases a <;> fin_cases b <;>
        simp [Matrix.SpecialLinearGroup.transvection_coe, coe_sl2Lower, Matrix.single_apply]
    rw [this]
    exact (sl2RelsAux F).y_mem_sub c
  · exact absurd rfl hij

theorem exists_sl2_section {F : Type} [Field F] [Finite F] [CharP F 2] {E : Type*} [Group E]
    [Finite E] {π : E →* SpecialLinearGroup (Fin 2) F} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hC : ¬ 2 ∣ Nat.card π.ker) :
    ∃ σ : SpecialLinearGroup (Fin 2) F →* E, ∀ g, π (σ g) = g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hi : ∀ a t, t ≠ 0 → (sl2RelsAux F).x a * (sl2RelsAux F).h t = 1 → a = 0 ∧ t = 1 := by
    intro a t ht h
    have h' := congrArg (fun M : SpecialLinearGroup (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F)) h
    have hh : (((sl2RelsAux F).h t : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        !![t, 0; 0, t⁻¹] := by
      rw [RankOneRels.h_def, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv]
      rw [RankOneRels.w_def, RankOneRels.w_def]
      simp only [sl2RelsAux_x, sl2RelsAux_y, Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper,
        coe_sl2Lower, Matrix.SpecialLinearGroup.coe_inv]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two, ht]
    simp only [Matrix.SpecialLinearGroup.coe_mul, sl2RelsAux_x, coe_sl2Upper, hh,
      Matrix.SpecialLinearGroup.coe_one] at h'
    have h00 := congrFun (congrFun h' 0) 0
    have h01 := congrFun (congrFun h' 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
    subst h00
    simpa using h01
  have hii : ∀ a b t, t ≠ 0 →
      (sl2RelsAux F).x a * (sl2RelsAux F).w 1 * (sl2RelsAux F).x b * (sl2RelsAux F).h t ≠ 1 := by
    intro a b t ht h
    have hh : (((sl2RelsAux F).h t : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        !![t, 0; 0, t⁻¹] := by
      rw [RankOneRels.h_def, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv]
      rw [RankOneRels.w_def, RankOneRels.w_def]
      simp only [sl2RelsAux_x, sl2RelsAux_y, Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper,
        coe_sl2Lower, Matrix.SpecialLinearGroup.coe_inv]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two, ht]
    have hw : (((sl2RelsAux F).w 1 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        !![0, 1; -1, 0] := by
      rw [RankOneRels.w_def]
      simp only [sl2RelsAux_x, sl2RelsAux_y, Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper,
        coe_sl2Lower]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    have h' := congrArg (fun M : SpecialLinearGroup (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F)) h
    simp only [Matrix.SpecialLinearGroup.coe_mul, sl2RelsAux_x, coe_sl2Upper, hh, hw,
      Matrix.SpecialLinearGroup.coe_one] at h'
    have h10 := congrFun (congrFun h' 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h10
    exact ht h10
  obtain ⟨φ, hφ⟩ := (sl2RelsAux F).exists_lift_of_separated hπ hcen hC hi hii
  let e : SpecialLinearGroup (Fin 2) F ≃* (sl2RelsAux F).sub :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr (sl2RelsAux_sub F).symm)
  exact ⟨φ.comp e.toMonoidHom, fun g => hφ (e g)⟩

theorem exists_lift_sl2 {F : Type} [Field F] [Finite F] [CharP F 2] {K : Type*} [Group K]
    [Finite K] {G : Type*} [Group G] (Δ : K →* G) (hcen : Δ.ker ≤ Subgroup.center K)
    (hodd : Odd (Nat.card Δ.ker)) (ψ : SpecialLinearGroup (Fin 2) F →* G)
    (hψ : Function.Injective ψ) (hψΔ : ψ.range ≤ Δ.range) :
    ∃ σ : SpecialLinearGroup (Fin 2) F →* K, ∀ g, Δ (σ g) = ψ g := by
  let E : Subgroup K := ψ.range.comap Δ
  let e : SpecialLinearGroup (Fin 2) F ≃* ψ.range := MonoidHom.ofInjective hψ
  let π : E →* SpecialLinearGroup (Fin 2) F :=
    e.symm.toMonoidHom.comp ((Δ.comp E.subtype).codRestrict ψ.range (fun x => x.2))
  have hπ : ∀ x : E, ψ (π x) = Δ x := fun x => by
    have h1 : e (π x) = ⟨Δ x, x.2⟩ := e.apply_symm_apply _
    exact congrArg Subtype.val h1
  have hsurj : Function.Surjective π := by
    intro g
    obtain ⟨k, hk⟩ := hψΔ ⟨g, rfl⟩
    refine ⟨⟨k, ⟨g, hk.symm⟩⟩, hψ ?_⟩
    rw [hπ]
    exact hk
  have hker : π.ker ≤ Subgroup.center E := by
    intro x hx
    have hx1 : Δ x = 1 := by
      rw [← hπ, MonoidHom.mem_ker.1 hx, map_one]
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hcen (MonoidHom.mem_ker.2 hx1)) y)
  have hC : ¬ 2 ∣ Nat.card π.ker := by
    let ι : π.ker →* Δ.ker :=
      { toFun := fun x => ⟨(x : E), by
          rw [MonoidHom.mem_ker, ← hπ (x : E), MonoidHom.mem_ker.1 x.2, map_one]⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hι : Function.Injective ι := fun x y hxy =>
      Subtype.ext (Subtype.ext (congrArg (fun z : Δ.ker => ((z : K))) hxy))
    have hodd' : Odd (Nat.card π.ker) := Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_injective ι hι)
    rintro ⟨c, hc⟩
    have := Nat.odd_iff.1 hodd'
    omega
  obtain ⟨σ, hσ⟩ := exists_sl2_section hsurj hker hC
  exact ⟨E.subtype.comp σ, fun g => by
    have := hπ (σ g)
    rw [hσ] at this
    exact this.symm⟩

theorem sl2_center_eq_bot {F : Type} [Field F] [CharP F 2] : Subgroup.center SL(2, F) = ⊥ := by
  refine eq_bot_iff.mpr fun A hA => ?_
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h5 : (r - 1) ^ 2 = 0 := by linear_combination hr + (1 - r) * h2
  have hr1 : r = 1 := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h5)
  subst hr1
  rw [Subgroup.mem_bot]
  ext i j
  have := congrFun (congrFun hrA i) j
  simpa [Matrix.scalar_apply, Matrix.one_apply] using this.symm

theorem sl2_isSimple {F : Type} [Field F] [CharP F 2] (h4 : 4 ≤ Nat.card F) :
    IsSimpleGroup SL(2, F) := by
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have e : SL(2, F) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq sl2_center_eq_bot.symm)
  exact e.isSimpleGroup

theorem sl2_closure_involutions {F : Type} [Field F] [CharP F 2] :
    Subgroup.closure {g : SpecialLinearGroup (Fin 2) F | g * g = 1} = ⊤ := by
  rw [eq_top_iff,
    ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field (ι := Fin 2)
      (K := F), Subgroup.closure_le]
  rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
  apply Subgroup.subset_closure
  show Matrix.SpecialLinearGroup.transvection hij c * Matrix.SpecialLinearGroup.transvection hij c
    = 1
  rw [← Matrix.SpecialLinearGroup.transvection_add, CharTwo.add_self_eq_zero,
    Matrix.SpecialLinearGroup.transvection_coeff_zero]

theorem sl2_closure_lower_upper {F : Type} [Field F] :
    Subgroup.closure ({g : SpecialLinearGroup (Fin 2) F | ∃ a : F, g = sl2Lower a} ∪
      {g : SpecialLinearGroup (Fin 2) F | ∃ a : F, g = sl2Upper a}) = ⊤ := by
  have h := sl2RelsAux_sub F
  rw [RankOneRels.sub] at h
  convert h using 2
  ext g
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_range, sl2RelsAux_x, sl2RelsAux_y]
  constructor
  · rintro (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact Or.inr ⟨a, rfl⟩
    · exact Or.inl ⟨a, rfl⟩
  · rintro (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact Or.inr ⟨a, rfl⟩
    · exact Or.inl ⟨a, rfl⟩

end Sl2Gen

section Psi

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

@[expose] noncomputable def psiHom (d : TrialityD4Data L (2 ^ f)) :
    SL(2, d.Γ₀) →* G :=
  L.subtype.comp (d.leviLong.subtype.comp d.leviLongEquiv.symm.toMonoidHom)

theorem psiHom_injective (d : TrialityD4Data L (2 ^ f)) : Function.Injective (psiHom d) :=
  L.subtype_injective.comp (d.leviLong.subtype_injective.comp d.leviLongEquiv.symm.injective)

theorem psiHom_equiv (d : TrialityD4Data L (2 ^ f)) (g : d.leviLong) :
    psiHom d (d.leviLongEquiv g) = ((g : L) : G) := by
  simp [psiHom]

theorem psiHom_slX₂ (d : TrialityD4Data L (2 ^ f)) (a : d.Γ₀) :
    psiHom d (d.slX₂ a) = ((d.x₂ a : L) : G) := by
  have h := psiHom_equiv d ⟨d.x₂ a, d.x₂_mem_leviLong a⟩
  rwa [d.leviLongEquiv_apply, d.leviLongRep_x₂] at h

theorem psiHom_slV (d : TrialityD4Data L (2 ^ f)) : psiHom d d.slV = vG d := by
  have h := psiHom_equiv d ⟨d.v, d.v_mem_leviLong⟩
  rwa [d.leviLongEquiv_apply, d.leviLongRep_v] at h

theorem range_psiHom (d : TrialityD4Data L (2 ^ f)) :
    (psiHom d).range = d.leviLong.map L.subtype := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨_, (d.leviLongEquiv.symm g).2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨d.leviLongEquiv ⟨y, hy⟩, psiHom_equiv d ⟨y, hy⟩⟩

theorem range_psiHom_le (d : TrialityD4Data L (2 ^ f)) :
    (psiHom d).range ≤ d.leviJ₀.map L.subtype := by
  rw [range_psiHom]
  exact map_mono d.leviLong_le_leviJ₀

theorem map_leviLong_le_normalizer_Y (d : TrialityD4Data L (2 ^ f)) :
    d.leviLong.map L.subtype ≤ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) := by
  rintro _ ⟨l, hl, rfl⟩
  refine mem_normalizer_fintype fun y hy => ?_
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  exact ⟨l * y₀ * l⁻¹, (mem_normalizer_iff.1 (d.leviLong_le_normalizer_Y hl) y₀).1 hy₀, by simp⟩

theorem Y_le_M (d : TrialityD4Data L (2 ^ f)) : d.Y ≤ d.M :=
  d.Y_le_W.trans (d.W_le_F.trans d.F_le_M)

theorem Y_inf_leviLong_map (d : TrialityD4Data L (2 ^ f)) :
    d.Y.map L.subtype ⊓ d.leviLong.map L.subtype = ⊥ := by
  have h0 : d.Y ⊓ d.leviLong = ⊥ :=
    le_bot_iff.1 ((inf_le_inf_right _ (Y_le_M d)).trans d.M_inf_leviLong.le)
  rw [← Subgroup.map_inf_eq _ _ L.subtype L.subtype_injective, h0, Subgroup.map_bot]

theorem Y_map_comm (d : TrialityD4Data L (2 ^ f)) {a b : G} (ha : a ∈ d.Y.map L.subtype)
    (hb : b ∈ d.Y.map L.subtype) : a * b = b * a := by
  obtain ⟨a₀, ha₀, rfl⟩ := ha
  obtain ⟨b₀, hb₀, rfl⟩ := hb
  have := mem_centralizer_iff.1 (d.M_le_centralizer_Y (Y_le_M d ha₀)) b₀ hb₀
  exact congrArg L.subtype this.symm

theorem eq_one_of_psiHom_comm (d : TrialityD4Data L (2 ^ f)) {x : SL(2, d.Γ₀)}
    (hx : ∀ y ∈ d.Y.map L.subtype, psiHom d x * y = y * psiHom d x) : x = 1 := by
  apply psiHom_injective d
  rw [map_one]
  obtain ⟨g, hg⟩ : ∃ g : d.leviLong, psiHom d x = ((g : L) : G) :=
    ⟨d.leviLongEquiv.symm x, by simp [psiHom]⟩
  have hg1 : (g : L) = 1 := by
    refine d.eq_one_of_mem_leviLong_of_conj_yv g.2 fun w => ?_
    have h1 := hx (L.subtype (d.yv w)) ⟨d.yv w, d.yv_mem_Y w, rfl⟩
    rw [hg] at h1
    have h2 : (g : L) * d.yv w = d.yv w * (g : L) := Subtype.ext h1
    rw [h2]
    group
  rw [hg, hg1]
  rfl

open scoped Matrix in
theorem yv_eq_one_of_comm (d : TrialityD4Data L (2 ^ f)) {w : Fin 2 → d.Γ₀}
    (h1 : d.x₂ 1 * d.yv w = d.yv w * d.x₂ 1) (h2 : d.v * d.yv w = d.yv w * d.v) :
    d.yv w = 1 := by
  have e1 : d.yv ((d.slX₂ 1 : Matrix (Fin 2) (Fin 2) d.Γ₀) *ᵥ w) = d.yv w := by
    rw [← d.x₂_conj_yv, h1]
    group
  have e2 : d.yv ((d.slV : Matrix (Fin 2) (Fin 2) d.Γ₀) *ᵥ w) = d.yv w := by
    rw [← d.v_conj_yv, h2]
    group
  have f1 := congrFun (d.yv_injective e1) 1
  have f2 := congrFun (d.yv_injective e2) 0
  simp [TrialityD4Data.slX₂, TrialityD4Data.slV, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two] at f1 f2
  have hw0 : w 0 = 0 := f1
  have hw1 : w 1 = 0 := by rw [f2]; exact hw0
  have : w = 0 := by
    funext i
    fin_cases i
    · exact hw0
    · exact hw1
  rw [this]
  simp [TrialityD4Data.yv, d.x₅_zero, d.x₆_zero]

end Psi

section Sigma

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem exists_sigma (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    ∃ σ : SL(2, d.Γ₀) →* ↥K, ∀ g, diagonalHom K t hK.comm (σ g) = psiHom d g := by
  have hodd : Odd (Nat.card (diagonalHom K t hK.comm).ker) := by
    have := odd_card_ker_diag h d hp hK
    rwa [Subgroup.card_map_of_injective K.subtype_injective] at this
  refine exists_lift_sl2 (diagonalHom K t hK.comm) (Common.ker_diagonalHom_le_center hK.comm) hodd
    (psiHom d) (psiHom_injective d) ?_
  rw [diag_range_eq h d hp hK]
  exact range_psiHom_le d

@[expose] noncomputable def sigHom (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    SL(2, d.Γ₀) →* ↥K :=
  Classical.choose (exists_sigma h d hp hK)

theorem sigHom_spec (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) (g : SL(2, d.Γ₀)) :
    diagonalHom K t hK.comm (sigHom h d hp hK g) = psiHom d g :=
  Classical.choose_spec (exists_sigma h d hp hK) g

@[expose] noncomputable def sigG (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    SL(2, d.Γ₀) →* G :=
  K.subtype.comp (sigHom h d hp hK)

theorem sigG_mem (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) (g : SL(2, d.Γ₀)) :
    sigG h d hp hK g ∈ K :=
  (sigHom h d hp hK g).2

theorem sigG_diag (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) (g : SL(2, d.Γ₀)) :
    sigG h d hp hK g * (t * sigG h d hp hK g * t) = psiHom d g := by
  have := sigHom_spec h d hp hK g
  rw [Common.diagonalHom_apply_of_mul_self hK.comm h.t_mul_t] at this
  exact this

theorem sigG_mul_self (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) {g : SL(2, d.Γ₀)} (hg : g * g = 1) :
    sigG h d hp hK g * sigG h d hp hK g = 1 := by
  rw [← map_mul, hg, map_one]

theorem psiHom_mem_leviLong (d : TrialityD4Data L (2 ^ f)) (g : SL(2, d.Γ₀)) :
    psiHom d g ∈ d.leviLong.map L.subtype := by
  rw [← range_psiHom]
  exact ⟨g, rfl⟩

theorem sigG_mem_normalizer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) (g : SL(2, d.Γ₀)) :
    sigG h d hp hK g ∈ normalizer ((eOne d t K : Subgroup G) : Set G) := by
  rw [mem_normalizer_eOne_iff h d hp hK (sigG_mem h d hp hK g), sigG_diag]
  exact map_leviLong_le_normalizer_Y d (psiHom_mem_leviLong d g)

theorem range_sigG_le_normalizer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    (sigG h d hp hK).range ≤ normalizer ((eOne d t K : Subgroup G) : Set G) := by
  rintro _ ⟨g, rfl⟩
  exact sigG_mem_normalizer h d hp hK g

theorem eq_one_of_sigG_mem_eOne (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) {g : SL(2, d.Γ₀)}
    (hg : sigG h d hp hK g ∈ eOne d t K) : g = 1 := by
  have h1 := (diag_eOne h d hp hK).1 _ hg
  rw [sigG_diag] at h1
  have h2 : psiHom d g ∈ d.Y.map L.subtype ⊓ d.leviLong.map L.subtype :=
    ⟨h1, psiHom_mem_leviLong d g⟩
  rw [Y_inf_leviLong_map, mem_bot] at h2
  exact psiHom_injective d (by rw [h2, map_one])

end Sigma

section KThreeStruct

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem eOne_le_inf_normalizer (d : TrialityD4Data L (2 ^ f)) (K : Subgroup G) :
    eOne d t K ≤ K ⊓ normalizer ((eOne d t K : Subgroup G) : Set G) :=
  le_inf inf_le_right le_normalizer

theorem eOne_le_kThree (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) : eOne d t K ≤ kThree d t K := by
  obtain ⟨-, -, -, -, hel⟩ := eOne_decomp h d hp hK
  intro x hx
  refine mem_oTwoPrimeRes (eOne_le_inf_normalizer d K hx) ⟨1, ?_⟩
  rw [pow_one]
  exact hel.2 x hx

theorem kThree_le (d : TrialityD4Data L (2 ^ f)) (K : Subgroup G) :
    kThree d t K ≤ K ⊓ normalizer ((eOne d t K : Subgroup G) : Set G) :=
  oTwoPrimeRes_le_self _

theorem kThree_le_K (d : TrialityD4Data L (2 ^ f)) (K : Subgroup G) : kThree d t K ≤ K :=
  (kThree_le d K).trans inf_le_left

theorem kThree_le_normalizer (d : TrialityD4Data L (2 ^ f)) (K : Subgroup G) :
    kThree d t K ≤ normalizer ((eOne d t K : Subgroup G) : Set G) :=
  (kThree_le d K).trans inf_le_right

theorem range_sigG_le_kThree (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    (sigG h d hp hK).range ≤ kThree d t K := by
  have hS : (sigG h d hp hK).range =
      Subgroup.map (sigG h d hp hK) (Subgroup.closure {g : SL(2, d.Γ₀) | g * g = 1}) := by
    rw [sl2_closure_involutions, MonoidHom.range_eq_map]
  rw [hS, MonoidHom.map_closure]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨g, hg, rfl⟩
  refine mem_oTwoPrimeRes ⟨sigG_mem h d hp hK g, sigG_mem_normalizer h d hp hK g⟩ ⟨1, ?_⟩
  rw [pow_one, sq]
  exact sigG_mul_self h d hp hK hg

theorem kThree_le_sup (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    kThree d t K ≤ eOne d t K ⊔ (sigG h d hp hK).range := by
  refine oTwoPrimeRes_le_of fun p ⟨hpK, hpN⟩ ⟨k, hk⟩ => ?_
  set Δ := diagonalHom K t hK.comm with hΔ
  have hΔval : ∀ x : K, Δ x = (x : G) * (t * x * t) :=
    fun x => Common.diagonalHom_apply_of_mul_self hK.comm h.t_mul_t x
  have hN : p * (t * p * t) ∈ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) :=
    (mem_normalizer_eOne_iff h d hp hK hpK).1 hpN
  have hK₀ : p * (t * p * t) ∈ d.leviJ₀.map L.subtype := by
    rw [← diag_range_eq h d hp hK]
    exact ⟨⟨p, hpK⟩, hΔval _⟩
  have hk' : (p * (t * p * t)) ^ 2 ^ k = 1 := by
    have h1 : (⟨p, hpK⟩ : K) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    have := congrArg Δ h1
    rw [map_pow, map_one, hΔval] at this
    exact this
  have hmem := mem_Y_sup_leviLong_of_two_element d hK₀ hN hk'
  have hLE : d.leviLong.map L.subtype ≤ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) :=
    map_leviLong_le_normalizer_Y d
  have hmem' : p * (t * p * t) ∈
      (((d.Y.map L.subtype ⊔ d.leviLong.map L.subtype : Subgroup G)) : Set G) := hmem
  rw [coe_mul_of_right_le_normalizer_left _ _ hLE] at hmem'
  obtain ⟨y', hy', l', hl', hyl⟩ := hmem'
  obtain ⟨e, he, hye⟩ := (diag_eOne h d hp hK).2 y' hy'
  obtain ⟨x, hx⟩ : l' ∈ (psiHom d).range := by
    rw [range_psiHom]
    exact hl'
  set ε : K := ⟨e, he.2⟩ with hε
  set m : K := ε * sigHom h d hp hK x with hm
  have hΔm : Δ m = Δ ⟨p, hpK⟩ := by
    rw [hm, map_mul, hΔval ε, sigHom_spec h d hp hK x, hx, hΔval ⟨p, hpK⟩]
    have : e * (t * e * t) * l' = p * (t * p * t) := by rw [← hye]; exact hyl
    exact this
  set z : K := m⁻¹ * ⟨p, hpK⟩ with hz
  have hzker : z ∈ Δ.ker := by
    rw [MonoidHom.mem_ker, hz, map_mul, map_inv, hΔm, inv_mul_cancel]
  have hpmz : p = (e * sigG h d hp hK x) * (z : G) := by
    have : (⟨p, hpK⟩ : K) = m * z := by rw [hz]; group
    exact congrArg Subtype.val this
  have hzB : (z : G) ∈ Δ.ker.map K.subtype := ⟨z, hzker, rfl⟩
  have hcomm : Commute (e * sigG h d hp hK x) (z : G) := by
    have hzc := Common.ker_diagonalHom_le_center hK.comm hzker
    have := Subgroup.mem_center_iff.1 hzc m
    exact congrArg Subtype.val this
  exact mem_of_mul_of_odd (odd_card_ker_diag h d hp hK)
    (mul_mem (mem_sup_left he) (mem_sup_right ⟨x, rfl⟩)) hzB hcomm hpmz hk

end KThreeStruct

section KThreeEq

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem kThree_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    kThree d t K = eOne d t K ⊔ (sigG h d hp hK).range :=
  le_antisymm (kThree_le_sup h d hp hK)
    (sup_le (eOne_le_kThree h d hp hK) (range_sigG_le_kThree h d hp hK))

theorem exists_decomp_kThree (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) {x : G}
    (hx : x ∈ kThree d t K) :
    ∃ e ∈ eOne d t K, ∃ g : SL(2, d.Γ₀), x = e * sigG h d hp hK g := by
  rw [kThree_eq h d hp hK, ← SetLike.mem_coe,
    coe_mul_of_right_le_normalizer_left _ _ (range_sigG_le_normalizer h d hp hK)] at hx
  obtain ⟨e, he, s, ⟨g, rfl⟩, rfl⟩ := hx
  exact ⟨e, he, g, rfl⟩

theorem exists_phi (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    ∃ φ : ↥(kThree d t K) →* SL(2, d.Γ₀), Function.Surjective φ ∧
      φ.ker = (eOne d t K).subgroupOf (kThree d t K) := by
  set E₁' : Subgroup ↥(kThree d t K) := (eOne d t K).subgroupOf (kThree d t K) with hE₁'
  have hnorm : E₁'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer
    (eOne_le_kThree h d hp hK)).2 (kThree_le_normalizer d K)
  let σ₃ : SL(2, d.Γ₀) →* ↥(kThree d t K) :=
    (sigG h d hp hK).codRestrict _ (fun g => range_sigG_le_kThree h d hp hK ⟨g, rfl⟩)
  let θ : SL(2, d.Γ₀) →* ↥(kThree d t K) ⧸ E₁' := (QuotientGroup.mk' E₁').comp σ₃
  have hinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have : σ₃ g ∈ E₁' := (QuotientGroup.eq_one_iff _).1 hg
    exact eq_one_of_sigG_mem_eOne h d hp hK this
  have hsurj : Function.Surjective θ := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨e, he, g, rfl⟩ := exists_decomp_kThree h d hp hK hx
    refine ⟨g, ?_⟩
    show (QuotientGroup.mk (σ₃ g) : ↥(kThree d t K) ⧸ E₁') =
      QuotientGroup.mk ⟨e * sigG h d hp hK g, hx⟩
    rw [QuotientGroup.eq]
    have hσ := sigG_mem_normalizer h d hp hK g
    have h1 : (sigG h d hp hK g)⁻¹ * e * (sigG h d hp hK g)⁻¹⁻¹ ∈ eOne d t K :=
      (mem_normalizer_iff.1 (inv_mem hσ) e).1 he
    change (sigG h d hp hK g)⁻¹ * (e * sigG h d hp hK g) ∈ eOne d t K
    simpa [mul_assoc] using h1
  let e := MulEquiv.ofBijective θ ⟨hinj, hsurj⟩
  refine ⟨e.symm.toMonoidHom.comp (QuotientGroup.mk' E₁'), ?_, ?_⟩
  · exact e.symm.surjective.comp (QuotientGroup.mk'_surjective E₁')
  · rw [MonoidHom.ker_comp_of_injective _ _ e.symm.injective, QuotientGroup.ker_mk']

theorem kThree_inf_zc (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) : kThree d t K ⊓ zc K = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hz3, hzK, hzc⟩
  obtain ⟨e, he, g, rfl⟩ := exists_decomp_kThree h d hp hK hz3
  set Δ := diagonalHom K t hK.comm with hΔ
  have hΔval : ∀ x : K, Δ x = (x : G) * (t * x * t) :=
    fun x => Common.diagonalHom_apply_of_mul_self hK.comm h.t_mul_t x
  have heK : e ∈ K := he.2
  set zK : K := ⟨e * sigG h d hp hK g, hzK⟩ with hzK'
  have hcommΔ : ∀ k : K, Δ zK * Δ k = Δ k * Δ zK := by
    intro k
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_iff.1 hzc k k.2).symm
  have hΔz : Δ zK = (e * (t * e * t)) * psiHom d g := by
    have : zK = ⟨e, heK⟩ * sigHom h d hp hK g := rfl
    rw [this, map_mul, hΔval, sigHom_spec]
  have hΔe : e * (t * e * t) ∈ d.Y.map L.subtype := (diag_eOne h d hp hK).1 e he
  have hg : g = 1 := by
    apply eq_one_of_psiHom_comm d
    intro y hy
    obtain ⟨ε, hε, hye⟩ := (diag_eOne h d hp hK).2 y hy
    have hy' : y = Δ ⟨ε, hε.2⟩ := by rw [hΔval]; exact hye
    have hψg : psiHom d g = (e * (t * e * t))⁻¹ * Δ zK := by rw [hΔz]; group
    have hc := hcommΔ ⟨ε, hε.2⟩
    rw [← hy'] at hc
    have hYc := Y_map_comm d (inv_mem hΔe) hy
    rw [hψg]
    calc (e * (t * e * t))⁻¹ * Δ zK * y = (e * (t * e * t))⁻¹ * (Δ zK * y) := by group
      _ = (e * (t * e * t))⁻¹ * (y * Δ zK) := by rw [hc]
      _ = ((e * (t * e * t))⁻¹ * y) * Δ zK := by group
      _ = (y * (e * (t * e * t))⁻¹) * Δ zK := by rw [hYc]
      _ = y * ((e * (t * e * t))⁻¹ * Δ zK) := by group
  subst hg
  have hzΔ : Δ zK = e * (t * e * t) := by rw [hΔz, map_one, mul_one]
  obtain ⟨y₀, hy₀, hy₀e⟩ := hΔe
  obtain ⟨w, rfl⟩ : y₀ ∈ Set.range d.yv := by rw [d.range_yv]; exact hy₀
  have hcomm1 := hcommΔ (sigHom h d hp hK (d.slX₂ 1))
  have hcomm2 := hcommΔ (sigHom h d hp hK d.slV)
  rw [sigHom_spec, psiHom_slX₂, hzΔ, ← hy₀e] at hcomm1
  rw [sigHom_spec, psiHom_slV, hzΔ, ← hy₀e] at hcomm2
  have hyv : d.yv w = 1 := by
    refine yv_eq_one_of_comm d ?_ ?_
    · exact L.subtype_injective (by simpa using hcomm1.symm)
    · exact L.subtype_injective (by simpa using hcomm2.symm)
  have hΔ1 : Δ zK = 1 := by
    rw [hzΔ, ← hy₀e, hyv]
    simp
  have hzker : zK ∈ Δ.ker := hΔ1
  have hzsq : zK * zK = 1 := by
    obtain ⟨-, -, -, -, hel⟩ := eOne_decomp h d hp hK
    refine Subtype.ext ?_
    have : e * e = 1 := by rw [← sq]; exact hel.2 e he
    simpa [hzK', mul_one] using this
  have hz1 : zK = 1 := eq_one_of_mem_ker_diag_of_sq h d hp hK hzker hzsq
  have : e * sigG h d hp hK 1 = 1 := by
    have := congrArg Subtype.val hz1
    simpa [hzK'] using this
  rw [this]
  exact one_mem _

theorem kThree_inf_conj (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    kThree d t K ⊓ (kThree d t K)ᵍ[t] = ⊥ := by
  refine le_bot_iff.1 (le_trans ?_ (kThree_inf_zc h d hp hK).le)
  refine le_inf inf_le_left fun x ⟨hx3, hx3t⟩ => ?_
  have hxK : x ∈ K := kThree_le_K d K hx3
  have hxKt : x ∈ Kᵍ[t] := Subgroup.map_mono (kThree_le_K d K) hx3t
  exact ⟨hxK, mem_centralizer_iff.2 fun k hk => commute_of_commutator_eq_bot hK.comm k hk x hxKt⟩

theorem kThree_comm (d : TrialityD4Data L (2 ^ f)) {K : Subgroup G}
    (hK : IsLayerComponent d t K) : ⁅kThree d t K, (kThree d t K)ᵍ[t]⁆ = ⊥ :=
  le_bot_iff.1 (hK.comm ▸ Subgroup.commutator_mono (kThree_le_K d K)
    (Subgroup.map_mono (kThree_le_K d K)))

end KThreeEq

section NormalTwo

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem not_isPGroup_sl2 (d : TrialityD4Data L (2 ^ f)) :
    ¬ IsPGroup 2 (SL(2, d.Γ₀)) := by
  intro hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP
  rw [d.card_SL_Γ₀] at hn
  have h3 : 3 ∣ (2 ^ f) ^ 2 - 1 := by
    have h1 : (2 ^ f) ^ 2 = 4 ^ f := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [h1]
    simpa using Nat.sub_one_dvd_pow_sub_one 4 f
  have h4 : 3 ∣ 2 ^ n := by
    rw [← hn]
    exact Dvd.dvd.mul_left h3 _
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h4
  omega

theorem le_ker_of_normal_isPGroup (d : TrialityD4Data L (2 ^ f)) (hf : 2 ≤ f) {X : Type*}
    [Group X] [Finite X] (φ : X →* SL(2, d.Γ₀)) (hφ : Function.Surjective φ) {T : Subgroup X}
    (hT : T.Normal) (hTp : IsPGroup 2 T) : T ≤ φ.ker := by
  have hq : 4 ≤ Nat.card d.Γ₀ := by
    rw [d.card_Γ₀]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hsimple : IsSimpleGroup SL(2, d.Γ₀) := sl2_isSimple hq
  have hnormal : (T.map φ).Normal := hT.map φ hφ
  haveI := hnormal
  rcases hsimple.eq_bot_or_eq_top_of_normal (T.map φ) with h0 | h1
  · intro x hx
    have : φ x ∈ T.map φ := ⟨x, hx, rfl⟩
    rw [h0, mem_bot] at this
    exact this
  · exfalso
    apply not_isPGroup_sl2 d
    have h2 : IsPGroup 2 (T.map φ) :=
      IsPGroup.of_surjective hTp (φ.subgroupMap T) (φ.subgroupMap_surjective T)
    rw [h1] at h2
    exact h2.of_equiv Subgroup.topEquiv

theorem pCoreOf_kThree (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    pCoreOf 2 (kThree d t K) = eOne d t K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · obtain ⟨φ, hφ, hker⟩ := exists_phi h d hp hK
    have hchar : (CFSG.pCore 2 ↥(kThree d t K)).Characteristic :=
      CFSG.LieType.BorelTits.pCore_characteristic (G := ↥(kThree d t K)) 2
    have hle := le_ker_of_normal_isPGroup d hp.two_le φ hφ
      (T := CFSG.pCore 2 ↥(kThree d t K)) inferInstance
      (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥(kThree d t K)) 2)
    rintro _ ⟨y, hy, rfl⟩
    have := hle hy
    rw [hker] at this
    exact this
  · obtain ⟨-, -, hcard, -, -⟩ := eOne_decomp h d hp hK
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (eOne_le_kThree h d hp hK)
      (kThree_le_normalizer d K) (IsPGroup.of_card (n := f * 2) (by rw [hcard, ← pow_mul]))

end NormalTwo

section InvolAux

variable {G : Type*} [Group G]

theorem invol_conj_pow {t : G} (ht : t * t = 1) (x : G) (n : ℕ) :
    (t * x * t) ^ n = t * x ^ n * t := by
  have h1 : t * x * t = (MulAut.conj t) x := by
    simp [MulAut.conj_apply, inv_eq_of_mul_eq_one_right ht]
  have h2 : t * x ^ n * t = (MulAut.conj t) (x ^ n) := by
    simp [MulAut.conj_apply, inv_eq_of_mul_eq_one_right ht]
  rw [h1, h2, map_pow]

theorem invol_conj_conj {t : G} (ht : t * t = 1) (a x : G) :
    t * (a * x * a⁻¹) * t = (t * a * t) * (t * x * t) * (t * a * t)⁻¹ := by
  rw [invol_conj_mul ht, invol_conj_mul ht, invol_conj_inv ht]

@[expose] def conjTo {t : G} (ht : t * t = 1) (A : Subgroup G) : ↥(Aᵍ[t]) →* ↥A :=
  MonoidHom.mk' (fun x => ⟨t * x * t, (mem_conjG_iff ht).1 x.2⟩) fun x y =>
    Subtype.ext (by simp only [Subgroup.coe_mul]; exact invol_conj_mul ht x y)

theorem coe_conjTo {t : G} (ht : t * t = 1) (A : Subgroup G) (x : ↥(Aᵍ[t])) :
    ((conjTo ht A x : ↥A) : G) = t * x * t :=
  rfl

theorem conjTo_surjective {t : G} (ht : t * t = 1) (A : Subgroup G) :
    Function.Surjective (conjTo ht A) := by
  intro a
  refine ⟨⟨t * a * t, conj_mem_conjG ht a.2⟩, Subtype.ext ?_⟩
  rw [coe_conjTo]
  exact invol_conj_invol ht a

end InvolAux

section NThreeEq

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem eOne_conj_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (K : Subgroup G) :
    (eOne d t K)ᵍ[t] = yamadaY₂ d t ⊓ Kᵍ[t] := by
  unfold eOne
  rw [conjG_inf, conjG_eq_self_of_mem_normalizer (h.t_mem_normalizer_yamadaY₂_D1 d)]

theorem inf_normalizer_le (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    K ⊓ normalizer ((eOne d t K : Subgroup G) : Set G) ≤
      jZeroLayer d ⊓ normalizer ((yamadaY₂ d t : Subgroup G) : Set G) := by
  obtain ⟨hdec, -, -, -, -⟩ := eOne_decomp h d hp hK
  rintro p ⟨hpK, hpN⟩
  refine ⟨hK.layer_eq ▸ mem_sup_left hpK, ?_⟩
  rw [hdec]
  refine Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hpN, ?_⟩
  refine mem_normalizer_fintype fun y hy => ?_
  have hyKt : y ∈ Kᵍ[t] := Subgroup.map_mono inf_le_right hy
  have : p * y * p⁻¹ = y := by
    rw [commute_of_commutator_eq_bot hK.comm p hpK y hyKt]
    group
  rw [this]
  exact hy

theorem mem_normalizer_of_mul (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    {K : Subgroup G} (hK : IsLayerComponent d t K) {a b' : G} (ha : a ∈ K) (hb : b' ∈ Kᵍ[t])
    (hg : a * b' ∈ normalizer ((yamadaY₂ d t : Subgroup G) : Set G)) :
    a ∈ normalizer ((eOne d t K : Subgroup G) : Set G) ∧
      b' ∈ normalizer (((eOne d t K)ᵍ[t] : Subgroup G) : Set G) := by
  have hc := commute_of_commutator_eq_bot hK.comm
  refine ⟨mem_normalizer_fintype fun x hx => ?_, mem_normalizer_fintype fun x hx => ?_⟩
  · have hxY : x ∈ yamadaY₂ d t := hx.1
    have hxK : x ∈ K := hx.2
    have h1 : (a * b') * x * (a * b')⁻¹ ∈ yamadaY₂ d t := (mem_normalizer_iff.1 hg x).1 hxY
    have h2 : (a * b') * x * (a * b')⁻¹ = a * x * a⁻¹ := by
      have hbx : x * b' = b' * x := hc x hxK b' hb
      calc (a * b') * x * (a * b')⁻¹ = a * (b' * x) * b'⁻¹ * a⁻¹ := by group
        _ = a * (x * b') * b'⁻¹ * a⁻¹ := by rw [hbx]
        _ = a * x * a⁻¹ := by group
    rw [h2] at h1
    have h3 : a * x * a⁻¹ ∈ K := mul_mem (mul_mem ha hxK) (inv_mem ha)
    exact Subgroup.mem_inf.2 ⟨h1, h3⟩
  · rw [eOne_conj_eq h d K] at hx ⊢
    have hxY : x ∈ yamadaY₂ d t := hx.1
    have hxKt : x ∈ Kᵍ[t] := hx.2
    have hy : b' * x * b'⁻¹ ∈ Kᵍ[t] := mul_mem (mul_mem hb hxKt) (inv_mem hb)
    have h1 : (a * b') * x * (a * b')⁻¹ ∈ yamadaY₂ d t := (mem_normalizer_iff.1 hg x).1 hxY
    have h2 : (a * b') * x * (a * b')⁻¹ = b' * x * b'⁻¹ := by
      have hab : a * (b' * x * b'⁻¹) = (b' * x * b'⁻¹) * a := hc a ha _ hy
      calc (a * b') * x * (a * b')⁻¹ = a * (b' * x * b'⁻¹) * a⁻¹ := by group
        _ = (b' * x * b'⁻¹) * a * a⁻¹ := by rw [hab]
        _ = b' * x * b'⁻¹ := by group
    rw [h2] at h1
    exact Subgroup.mem_inf.2 ⟨h1, hy⟩

theorem kThree_le_nThree (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) : kThree d t K ≤ nThree d t := by
  refine oTwoPrimeRes_le_of fun p hpmem hk => ?_
  exact mem_oTwoPrimeRes (inf_normalizer_le h d hp hK hpmem) hk

theorem kThree_conj_le_nThree (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    (kThree d t K)ᵍ[t] ≤ nThree d t := by
  have ht := h.t_mem_normalizer_yamadaY₂_D1 d
  unfold kThree oTwoPrimeRes
  rw [MonoidHom.map_closure]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨p, ⟨hpmem, ⟨k, hk⟩⟩, rfl⟩
  obtain ⟨hpE, hpN⟩ := inf_normalizer_le h d hp hK hpmem
  have hpKt : (MulAut.conj t⁻¹).toMonoidHom p ∈ Kᵍ[t] := ⟨p, hpmem.1, rfl⟩
  have h1 : (MulAut.conj t⁻¹).toMonoidHom p ∈ jZeroLayer d := by
    rw [hK.layer_eq]
    exact mem_sup_right hpKt
  have h2 : (MulAut.conj t⁻¹).toMonoidHom p ∈
      normalizer ((yamadaY₂ d t : Subgroup G) : Set G) := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact mul_mem (mul_mem (inv_mem ht) hpN) (by simpa using ht)
  refine mem_oTwoPrimeRes (Subgroup.mem_inf.2 ⟨h1, h2⟩) ⟨k, ?_⟩
  · rw [← map_pow, hk, map_one]

theorem nThree_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    nThree d t = kThree d t K ⊔ (kThree d t K)ᵍ[t] := by
  refine le_antisymm ?_ (sup_le (kThree_le_nThree h d hp hK) (kThree_conj_le_nThree h d hp hK))
  have ht := h.t_mul_t
  refine oTwoPrimeRes_le_of fun g ⟨hgE, hgN⟩ ⟨k, hk⟩ => ?_
  have hc := commute_of_commutator_eq_bot hK.comm
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute K Kᵍ[t] hc
  have hg' : g ∈ ((K ⊔ Kᵍ[t] : Subgroup G) : Set G) := by
    rw [← hK.layer_eq]
    exact hgE
  rw [hset] at hg'
  obtain ⟨a, ha, b', hb, hgeq⟩ := hg'
  have ha : a ∈ K := ha
  have hb : b' ∈ Kᵍ[t] := hb
  have hgeq' : a * b' = g := hgeq
  subst hgeq'
  obtain ⟨haN, hbN⟩ := mem_normalizer_of_mul h d hK ha hb hgN
  have hab : Commute a b' := hc a ha b' hb
  have hab' : a ^ 2 ^ k ∈ K ⊓ Kᵍ[t] := by
    have h1 : a ^ 2 ^ k * b' ^ 2 ^ k = 1 := by rw [← hab.mul_pow]; exact hk
    have h2 : a ^ 2 ^ k ∈ Kᵍ[t] := by
      rw [eq_inv_of_mul_eq_one_left h1]
      exact inv_mem (pow_mem hb _)
    exact Subgroup.mem_inf.2 ⟨pow_mem ha _, h2⟩
  obtain ⟨N, hN, hNa, hNb⟩ := exists_two_parts (odd_card_inf_conj h d hp hK) hab hk hab'
  rw [hN]
  refine mul_mem (mem_sup_left ?_) (mem_sup_right ?_)
  · exact mem_oTwoPrimeRes (Subgroup.mem_inf.2 ⟨pow_mem ha N, pow_mem haN N⟩) ⟨k, hNa⟩
  · rw [mem_conjG_iff ht]
    have hβK : t * b' * t ∈ K := (mem_conjG_iff ht).1 hb
    have hβN : t * b' * t ∈ normalizer ((eOne d t K : Subgroup G) : Set G) := by
      refine mem_normalizer_fintype fun x hx => ?_
      have hx' : t * x * t ∈ (eOne d t K)ᵍ[t] := conj_mem_conjG ht hx
      have h1 := (mem_normalizer_iff.1 hbN _).1 hx'
      rw [mem_conjG_iff ht] at h1
      have h2 := invol_conj_conj ht b' (t * x * t)
      rw [invol_conj_invol ht] at h2
      rw [h2] at h1
      exact h1
    have h1 : t * b' ^ N * t ∈ K := by
      rw [← invol_conj_pow ht]
      exact pow_mem hβK N
    have h2 : t * b' ^ N * t ∈ normalizer ((eOne d t K : Subgroup G) : Set G) := by
      rw [← invol_conj_pow ht]
      exact pow_mem hβN N
    refine mem_oTwoPrimeRes (Subgroup.mem_inf.2 ⟨h1, h2⟩) ⟨k, ?_⟩
    rw [invol_conj_pow ht, hNb, mul_one, ht]

end NThreeEq

section Rho

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem exists_rho (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    ∃ ρ : ↥(nThree d t) →* SL(2, d.Γ₀) × SL(2, d.Γ₀), Function.Surjective ρ ∧
      ρ.ker = (yamadaY₂ d t).subgroupOf (nThree d t) := by
  have ht := h.t_mul_t
  obtain ⟨φ, hφs, hφk⟩ := exists_phi h d hp hK
  obtain ⟨hdec, -, -, -, -⟩ := eOne_decomp h d hp hK
  have hcomm : ∀ (m : ↥(kThree d t K)) (n : ↥((kThree d t K)ᵍ[t])),
      Commute ((kThree d t K).subtype m) (((kThree d t K)ᵍ[t]).subtype n) := fun m n =>
    commute_of_commutator_eq_bot (kThree_comm d hK) m m.2 n n.2
  let Θ : ↥(kThree d t K) × ↥((kThree d t K)ᵍ[t]) →* G :=
    MonoidHom.noncommCoprod (kThree d t K).subtype ((kThree d t K)ᵍ[t]).subtype hcomm
  have hΘapply : ∀ x : ↥(kThree d t K) × ↥((kThree d t K)ᵍ[t]), Θ x = (x.1 : G) * (x.2 : G) :=
    fun x => MonoidHom.noncommCoprod_apply _ _ _ x
  have hΘinj : Function.Injective Θ := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨(kThree d t K).subtype_injective, ((kThree d t K)ᵍ[t]).subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
    exact kThree_inf_conj h d hp hK
  have hΘrange : Θ.range = nThree d t := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
    exact (nThree_eq h d hp hK).symm
  let eΘ : ↥(kThree d t K) × ↥((kThree d t K)ᵍ[t]) ≃* ↥(nThree d t) :=
    (MonoidHom.ofInjective hΘinj).trans (MulEquiv.subgroupCongr hΘrange)
  have heΘ : ∀ x : ↥(kThree d t K) × ↥((kThree d t K)ᵍ[t]),
      ((eΘ x : ↥(nThree d t)) : G) = (x.1 : G) * (x.2 : G) :=
    fun x => hΘapply x
  let φt : ↥((kThree d t K)ᵍ[t]) →* SL(2, d.Γ₀) := φ.comp (conjTo ht (kThree d t K))
  have hφtk : ∀ b : ↥((kThree d t K)ᵍ[t]), φt b = 1 ↔ (b : G) ∈ (eOne d t K)ᵍ[t] := by
    intro b
    have : φt b = 1 ↔ conjTo ht (kThree d t K) b ∈ φ.ker := by rw [MonoidHom.mem_ker]; rfl
    rw [this, hφk, mem_subgroupOf, coe_conjTo, mem_conjG_iff ht]
  have hφak : ∀ a : ↥(kThree d t K), φ a = 1 ↔ (a : G) ∈ eOne d t K := by
    intro a
    rw [← MonoidHom.mem_ker, hφk, mem_subgroupOf]
  let Ψ : ↥(kThree d t K) × ↥((kThree d t K)ᵍ[t]) →* SL(2, d.Γ₀) × SL(2, d.Γ₀) := φ.prodMap φt
  let ρ : ↥(nThree d t) →* SL(2, d.Γ₀) × SL(2, d.Γ₀) := Ψ.comp eΘ.symm.toMonoidHom
  refine ⟨ρ, ?_, ?_⟩
  · have hφts : Function.Surjective φt := hφs.comp (conjTo_surjective ht (kThree d t K))
    exact (hφs.prodMap hφts).comp eΘ.symm.surjective
  · ext x
    obtain ⟨⟨a, b⟩, rfl⟩ := eΘ.surjective x
    have hρ : ρ (eΘ (a, b)) = (φ a, φt b) := by
      change (φ.prodMap φt) (eΘ.symm (eΘ (a, b))) = _
      rw [MulEquiv.symm_apply_apply]
      rfl
    rw [MonoidHom.mem_ker, hρ, Prod.mk_eq_one, hφak, hφtk, mem_subgroupOf, heΘ]
    constructor
    · rintro ⟨ha, hb⟩
      rw [hdec]
      exact mul_mem (mem_sup_left ha) (mem_sup_right hb)
    · intro hx
      have hcE := commute_of_commutator_eq_bot (eOne_comm h d hK)
      obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (eOne d t K)
        (eOne d t K)ᵍ[t] hcE
      rw [hdec, ← SetLike.mem_coe, hset] at hx
      obtain ⟨e, he, e', he', hee⟩ := hx
      have he : e ∈ eOne d t K := he
      have he' : e' ∈ (eOne d t K)ᵍ[t] := he'
      have hee' : e * e' = (a : G) * (b : G) := hee
      have h1 : Θ (⟨e, eOne_le_kThree h d hp hK he⟩,
          ⟨e', Subgroup.map_mono (eOne_le_kThree h d hp hK) he'⟩) = Θ (a, b) := by
        rw [hΘapply, hΘapply]
        exact hee'
      have h2 := hΘinj h1
      have h3 : e = (a : G) := congrArg (fun p => ((p.1 : (kThree d t K)) : G)) h2
      have h4 : e' = (b : G) := congrArg (fun p => ((p.2 : ↥((kThree d t K)ᵍ[t])) : G)) h2
      exact ⟨h3 ▸ he, h4 ▸ he'⟩

theorem le_Y₂_of_normal_isPGroup (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K)
    {T : Subgroup ↥(nThree d t)} (hT : T.Normal) (hTp : IsPGroup 2 T) :
    T ≤ (yamadaY₂ d t).subgroupOf (nThree d t) := by
  obtain ⟨ρ, hρs, hρk⟩ := exists_rho h d hp hK
  have h1 := le_ker_of_normal_isPGroup d hp.two_le ((MonoidHom.fst _ _).comp ρ)
    (Prod.fst_surjective.comp hρs) hT hTp
  have h2 := le_ker_of_normal_isPGroup d hp.two_le ((MonoidHom.snd _ _).comp ρ)
    (Prod.snd_surjective.comp hρs) hT hTp
  rw [← hρk]
  intro x hx
  have a1 := h1 hx
  have a2 := h2 hx
  rw [MonoidHom.mem_ker] at a1 a2 ⊢
  exact Prod.ext a1 a2

end Rho

section QThreeDiag

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem delta_mem_sylowJ₀ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) {q : G}
    (hq : q ∈ qThree d t K) : q * (t * q * t) ∈ d.sylowJ₀.map L.subtype := by
  obtain ⟨hdec, -, -, -, -⟩ := qThree_decomp h d hp hK
  rw [← (prodX_sylow h d hp).2.1]
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [hdec]
    exact mul_mem (mem_sup_left hq) (mem_sup_right (conj_mem_conjG h.t_mul_t hq))
  · have := Common.range_diagonalHom_le hK.comm h.t_mul_t ⟨⟨q, hq.2⟩, rfl⟩
    simpa [Common.diagonalHom_apply_of_mul_self hK.comm h.t_mul_t] using this

theorem exists_qThree_diag (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) {x : G}
    (hx : x ∈ d.sylowJ₀.map L.subtype) : ∃ q ∈ qThree d t K, x = q * (t * q * t) := by
  obtain ⟨hdec, hinf, hcomm, -, -⟩ := qThree_decomp h d hp hK
  have hx' : x ∈ prodX d t ⊓ centralizer ({t} : Set G) := by
    rw [(prodX_sylow h d hp).2.1]
    exact hx
  have hxt : t * x = x * t := (mem_centralizer_singleton_iff.1 hx'.2).symm
  exact exists_eq_mul_conj_of_mem_centralizer h.t_mul_t hcomm hinf (hdec ▸ hx'.1) hxt

theorem mem_of_diag_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) {M : Subgroup G} {q u : G} (hq : q ∈ M)
    (hqK : q ∈ K) (huK : u ∈ K) (hdiag : u * (t * u * t) = q * (t * q * t)) {k : ℕ}
    (hk : u ^ 2 ^ k = 1) : u ∈ M := by
  set Δ := diagonalHom K t hK.comm with hΔ
  have hΔval : ∀ x : K, Δ x = (x : G) * (t * x * t) :=
    fun x => Common.diagonalHom_apply_of_mul_self hK.comm h.t_mul_t x
  set qK : K := ⟨q, hqK⟩
  set uK : K := ⟨u, huK⟩
  have hzker : qK⁻¹ * uK ∈ Δ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hΔval, hΔval]
    change (q * (t * q * t))⁻¹ * (u * (t * u * t)) = 1
    rw [hdiag, inv_mul_cancel]
  have hpmz : u = q * ((qK⁻¹ * uK : K) : G) := by
    have : uK = qK * (qK⁻¹ * uK) := by group
    exact congrArg Subtype.val this
  have hzB : ((qK⁻¹ * uK : K) : G) ∈ Δ.ker.map K.subtype := ⟨_, hzker, rfl⟩
  have hcomm : Commute q ((qK⁻¹ * uK : K) : G) := by
    have hzc := Common.ker_diagonalHom_le_center hK.comm hzker
    have := Subgroup.mem_center_iff.1 hzc qK
    exact congrArg Subtype.val this
  exact mem_of_mul_of_odd (odd_card_ker_diag h d hp hK) hq hzB hcomm hpmz hk

theorem slX₂_mul_self (d : TrialityD4Data L (2 ^ f)) (a : d.Γ₀) : d.slX₂ a * d.slX₂ a = 1 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;>
    simp [TrialityD4Data.slX₂, Matrix.mul_apply, Fin.sum_univ_two, d.add_self_Γ₀ a]

theorem sigG_slX₂_mem_qThree (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) (a : d.Γ₀) :
    sigG h d hp hK (d.slX₂ a) ∈ qThree d t K := by
  have hx : ((d.x₂ a : L) : G) ∈ d.sylowJ₀.map L.subtype := by
    refine ⟨d.x₂ a, d.mem_sylowJ₀_iff.2 ⟨a, 0, 0, ?_⟩, rfl⟩
    rw [d.x₅_zero, d.x₆_zero, mul_one, mul_one]
  obtain ⟨q, hq, hqe⟩ := exists_qThree_diag h d hp hK hx
  refine mem_of_diag_eq h d hp hK hq hq.2 (sigG_mem h d hp hK _) ?_ (k := 1) ?_
  · rw [sigG_diag, psiHom_slX₂, hqe]
  · rw [pow_one, sq]
    exact sigG_mul_self h d hp hK (slX₂_mul_self d a)

theorem qThree_le_kThree (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) : qThree d t K ≤ kThree d t K := by
  obtain ⟨-, -, -, hle, -⟩ := eOne_decomp h d hp hK
  have hQp : IsPGroup 2 (qThree d t K) := (isPGroup_prodX h d hp).to_le inf_le_left
  have hnorm : qThree d t K ≤ normalizer ((eOne d t K : Subgroup G) : Set G) := by
    haveI := (eOne_normal h d hp hK).2
    exact Subgroup.le_normalizer_of_normal_subgroupOf hle
  intro q hq
  refine mem_oTwoPrimeRes (Subgroup.mem_inf.2 ⟨hq.2, hnorm hq⟩) ?_
  obtain ⟨k, hk⟩ := hQp ⟨q, hq⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

end QThreeDiag

section VOne

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem Y_inf_leviLong (d : TrialityD4Data L (2 ^ f)) : d.Y ⊓ d.leviLong = ⊥ :=
  le_bot_iff.1 ((inf_le_inf_right _ (Y_le_M d)).trans d.M_inf_leviLong.le)

theorem vG_mul_t (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) : vG d * t = t * vG d :=
  mem_centralizer_iff.1 h.htL _ d.v.2

theorem slV_mul_self (d : TrialityD4Data L (2 ^ f)) : d.slV * d.slV = 1 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;>
    simp [TrialityD4Data.slV, Matrix.mul_apply, Fin.sum_univ_two]

theorem slV_mul_slX₂_mul_slV (d : TrialityD4Data L (2 ^ f)) (a : d.Γ₀) :
    d.slV * d.slX₂ a * d.slV = CFSG.LieType.Steinberg.sl2Upper a := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, CFSG.LieType.Steinberg.coe_sl2Upper]
  fin_cases i <;> fin_cases j <;>
    simp [TrialityD4Data.slV, TrialityD4Data.slX₂, Matrix.mul_apply, Fin.sum_univ_two]

theorem vG_eq_v₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    vG d = sigG h d hp hK d.slV * (t⁻¹ * sigG h d hp hK d.slV * t) := by
  rw [inv_eq_of_mul_eq_one_right h.t_mul_t, sigG_diag, psiHom_slV]

theorem v₁_mem_kThree (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) : sigG h d hp hK d.slV ∈ kThree d t K :=
  range_sigG_le_kThree h d hp hK ⟨_, rfl⟩

theorem psiHom_mem_nThree (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) (g : SL(2, d.Γ₀)) :
    psiHom d g ∈ nThree d t := by
  rw [← sigG_diag h d hp hK g, nThree_eq h d hp hK]
  have hσ : sigG h d hp hK g ∈ kThree d t K :=
    range_sigG_le_kThree h d hp hK ⟨g, rfl⟩
  exact mul_mem (mem_sup_left hσ) (mem_sup_right (conj_mem_conjG h.t_mul_t hσ))

theorem leviLong_map_le_nThree (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    d.leviLong.map L.subtype ≤ nThree d t := by
  rw [← range_psiHom]
  rintro _ ⟨g, rfl⟩
  exact psiHom_mem_nThree h d hp hK g

theorem vG_mem_nThree (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) : vG d ∈ nThree d t := by
  rw [← psiHom_slV]
  exact psiHom_mem_nThree h d hp hK _

theorem eq_slX₂_of_psiHom_mem (d : TrialityD4Data L (2 ^ f)) {g : SL(2, d.Γ₀)}
    (hg : psiHom d g ∈ d.sylowJ₀.map L.subtype) : ∃ a, g = d.slX₂ a := by
  obtain ⟨y₀, hy₀, hy₀g⟩ := hg
  obtain ⟨a, b, c, hy⟩ := d.mem_sylowJ₀_iff.1 hy₀
  have hℓ : y₀ = ((d.leviLongEquiv.symm g : d.leviLong) : L) :=
    L.subtype_injective (by rw [hy₀g]; simp [psiHom])
  set ℓ : L := ((d.leviLongEquiv.symm g : d.leviLong) : L) with hℓdef
  have hℓmem : ℓ ∈ d.leviLong := (d.leviLongEquiv.symm g).2
  have hyY : d.x₅ b * d.x₆ c ∈ d.Y := mul_mem (d.x₅_mem_Y b) (d.x₆_mem_Y c)
  have hyL : d.x₅ b * d.x₆ c ∈ d.leviLong := by
    have h1 : d.x₅ b * d.x₆ c = (d.x₂ a)⁻¹ * ℓ := by
      rw [← hℓ, ← hy]
      group
    rw [h1]
    exact mul_mem (inv_mem (d.x₂_mem_leviLong a)) hℓmem
  have hy1 : d.x₅ b * d.x₆ c = 1 := by
    have : d.x₅ b * d.x₆ c ∈ d.Y ⊓ d.leviLong := ⟨hyY, hyL⟩
    rw [Y_inf_leviLong d, mem_bot] at this
    exact this
  have hℓx : ℓ = d.x₂ a := by
    rw [← hℓ, ← hy]
    have : d.x₂ a * d.x₅ b * d.x₆ c = d.x₂ a * (d.x₅ b * d.x₆ c) := by group
    rw [this, hy1, mul_one]
  refine ⟨a, ?_⟩
  apply psiHom_injective d
  rw [psiHom_slX₂]
  have : psiHom d g = ((ℓ : L) : G) := by simp [psiHom, hℓdef]
  rw [this, hℓx]

theorem v₁_not_mem_normalizer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    sigG h d hp hK d.slV ∉ normalizer ((qThree d t K : Subgroup G) : Set G) := by
  intro hv
  have hu := sigG_slX₂_mem_qThree h d hp hK 1
  have h1 : sigG h d hp hK d.slV * sigG h d hp hK (d.slX₂ 1) * (sigG h d hp hK d.slV)⁻¹ ∈
      qThree d t K := (mem_normalizer_iff.1 hv _).1 hu
  have h2 := delta_mem_sylowJ₀ h d hp hK h1
  set Δ := diagonalHom K t hK.comm with hΔ
  have h3 : sigG h d hp hK d.slV * sigG h d hp hK (d.slX₂ 1) * (sigG h d hp hK d.slV)⁻¹ *
      (t * (sigG h d hp hK d.slV * sigG h d hp hK (d.slX₂ 1) * (sigG h d hp hK d.slV)⁻¹) * t) =
      psiHom d (d.slV * d.slX₂ 1 * d.slV⁻¹) := by
    have := Common.diagonalHom_apply_of_mul_self hK.comm h.t_mul_t
      (sigHom h d hp hK d.slV * sigHom h d hp hK (d.slX₂ 1) * (sigHom h d hp hK d.slV)⁻¹)
    rw [map_mul, map_mul, map_inv, sigHom_spec, sigHom_spec] at this
    rw [map_mul, map_mul, map_inv]
    exact this.symm
  rw [h3] at h2
  obtain ⟨a, ha⟩ := eq_slX₂_of_psiHom_mem d h2
  have hinv : d.slV⁻¹ = d.slV := inv_eq_of_mul_eq_one_right (slV_mul_self d)
  rw [hinv, slV_mul_slX₂_mul_slV] at ha
  have := congrArg (fun m : SL(2, d.Γ₀) => (m : Matrix (Fin 2) (Fin 2) d.Γ₀) 0 1) ha
  simp [CFSG.LieType.Steinberg.coe_sl2Upper, TrialityD4Data.slX₂] at this

end VOne

section NThreeGen

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem yamadaY₂_le_nThree (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    yamadaY₂ d t ≤ nThree d t := by
  obtain ⟨hdec, -, -, -, -⟩ := eOne_decomp h d hp hK
  rw [hdec, nThree_eq h d hp hK]
  exact sup_le_sup (eOne_le_kThree h d hp hK) (Subgroup.map_mono (eOne_le_kThree h d hp hK))

theorem prodX_le_nThree (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    prodX d t ≤ nThree d t := by
  obtain ⟨hsup, -, -, -, -⟩ := qThree_decomp h d hp hK
  rw [hsup, nThree_eq h d hp hK]
  exact sup_le_sup (qThree_le_kThree h d hp hK) (Subgroup.map_mono (qThree_le_kThree h d hp hK))

theorem prodX_conj_v_le_nThree (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    (prodX d t).map (MulAut.conj (vG d)).toMonoidHom ≤ nThree d t :=
  map_conj_le_of_mem_normalizer (prodX_le_nThree h d hp hK)
    (le_normalizer (vG_mem_nThree h d hp hK))

theorem conj_t_prodX_sup (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    (prodX d t ⊔ (prodX d t).map (MulAut.conj (vG d)).toMonoidHom)ᵍ[t] =
      prodX d t ⊔ (prodX d t).map (MulAut.conj (vG d)).toMonoidHom := by
  have hX : (prodX d t)ᵍ[t] = prodX d t :=
    conjG_eq_self_of_mem_normalizer (t_mem_normalizer_prodX h d)
  have hcomm : vG d * t⁻¹ = t⁻¹ * vG d :=
    (Commute.inv_right (show Commute (vG d) t from vG_mul_t h d)).eq
  rw [Subgroup.map_sup, hX]
  congr 1
  calc ((prodX d t).map (MulAut.conj (vG d)).toMonoidHom).map (MulAut.conj t⁻¹).toMonoidHom
      = ((prodX d t).map (MulAut.conj t⁻¹).toMonoidHom).map (MulAut.conj (vG d)).toMonoidHom :=
        map_conj_map_conj_comm hcomm _
    _ = (prodX d t).map (MulAut.conj (vG d)).toMonoidHom := by rw [hX]

theorem nThree_eq_prodX_sup (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    nThree d t = prodX d t ⊔ (prodX d t).map (MulAut.conj (vG d)).toMonoidHom := by
  apply le_antisymm
  · have hK3W : kThree d t K ≤ prodX d t ⊔ (prodX d t).map (MulAut.conj (vG d)).toMonoidHom := by
      obtain ⟨-, -, -, hle, -⟩ := eOne_decomp h d hp hK
      have hQX : qThree d t K ≤ prodX d t := inf_le_left
      rw [kThree_eq h d hp hK]
      refine sup_le (hle.trans (hQX.trans le_sup_left)) ?_
      have hS : (sigG h d hp hK).range =
          Subgroup.map (sigG h d hp hK) (Subgroup.closure
            ({g : SL(2, d.Γ₀) | ∃ a : d.Γ₀, g = CFSG.LieType.Steinberg.sl2Lower a} ∪
             {g : SL(2, d.Γ₀) | ∃ a : d.Γ₀, g = CFSG.LieType.Steinberg.sl2Upper a})) := by
        rw [sl2_closure_lower_upper, MonoidHom.range_eq_map]
      rw [hS, MonoidHom.map_closure]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨g, hg, rfl⟩
      rcases hg with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · exact (hQX.trans le_sup_left) (sigG_slX₂_mem_qThree h d hp hK a)
      ·
        have hu := sigG_slX₂_mem_qThree h d hp hK a
        set u := sigG h d hp hK (d.slX₂ a) with hudef
        set v₁ := sigG h d hp hK d.slV with hv₁
        have hv₁sq : v₁ * v₁ = 1 := sigG_mul_self h d hp hK (slV_mul_self d)
        have hv₁inv : v₁⁻¹ = v₁ := inv_eq_of_mul_eq_one_right hv₁sq
        have hw : t⁻¹ * v₁ * t ∈ Kᵍ[t] :=
          Common.conj_mem_map_conj_inv t (kThree_le_K d K (v₁_mem_kThree h d hp hK))
        have hc : u * (t⁻¹ * v₁ * t) = (t⁻¹ * v₁ * t) * u :=
          commute_of_commutator_eq_bot hK.comm u hu.2 _ hw
        have hwu : (t⁻¹ * v₁ * t) * u * (t⁻¹ * v₁ * t)⁻¹ = u := by
          rw [← hc]
          group
        have hup : sigG h d hp hK (CFSG.LieType.Steinberg.sl2Upper a) = v₁ * u * v₁ := by
          rw [← slV_mul_slX₂_mul_slV d a, map_mul, map_mul]
        have hvu : vG d * u * (vG d)⁻¹ = v₁ * u * v₁ := by
          calc vG d * u * (vG d)⁻¹ = (v₁ * (t⁻¹ * v₁ * t)) * u * (v₁ * (t⁻¹ * v₁ * t))⁻¹ := by
                rw [← vG_eq_v₁ h d hp hK]
            _ = v₁ * ((t⁻¹ * v₁ * t) * u * (t⁻¹ * v₁ * t)⁻¹) * v₁⁻¹ := by group
            _ = v₁ * u * v₁ := by rw [hwu, hv₁inv]
        rw [hup, ← hvu]
        exact mem_sup_right ⟨u, hu.1, rfl⟩
    rw [nThree_eq h d hp hK]
    refine sup_le hK3W ?_
    have := Subgroup.map_mono (f := (MulAut.conj t⁻¹).toMonoidHom) hK3W
    rwa [conj_t_prodX_sup h d] at this
  · exact sup_le (prodX_le_nThree h d hp hK) (prodX_conj_v_le_nThree h d hp hK)

theorem nThree_le_normalizer_M₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    nThree d t ≤ normalizer ((yamadaM₆ d t : Subgroup G) : Set G) := by
  rw [nThree_eq_prodX_sup h d hp hK]
  have hlay := hp.layer
  have hv := h.v_mem_normalizer_yamadaM₆_PA d hlay
  have hX : prodX d t ≤ normalizer ((yamadaM₆ d t : Subgroup G) : Set G) :=
    (inf_le_left.trans (yamadaD₅_le_yamadaP d t)).trans (h.yamadaP_le_normalizer_yamadaM₆ d hlay)
  refine sup_le hX ?_
  rintro _ ⟨x, hx, rfl⟩
  exact mul_mem (mul_mem hv (hX hx)) (inv_mem hv)

end NThreeGen

section NTwo

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem yamadaY₂_le_yamadaM₆' (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaY₂ d t ≤ yamadaM₆ d t :=
  (yamadaY₂_le_yamadaW₃' h d hlay).trans
    ((h.yamadaW₃_le_yamadaF₄_R5 d hlay).trans (h.yamadaF₄_le_yamadaM₆_PA d hlay))

theorem isPGroup_yamadaM₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) : IsPGroup 2 (yamadaM₆ d t) := by
  obtain ⟨-, -, -, -, -, -, -, -, hM6, -, -⟩ := T4_series_free h d hp
  exact IsPGroup.of_card (n := f * 22) (by rw [hM6, ← pow_mul])

theorem nThree_inf_M₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    nThree d t ⊓ yamadaM₆ d t = yamadaY₂ d t := by
  apply le_antisymm
  · rintro x ⟨hxN, hxM⟩
    have hN3 := nThree_le_normalizer_M₆ h d hp hK
    have hT : ((yamadaM₆ d t).subgroupOf (nThree d t)).Normal :=
      ⟨fun x hx g => by
        rw [mem_subgroupOf] at hx ⊢
        exact (mem_normalizer_iff.1 (hN3 g.2) x).1 hx⟩
    have hTp : IsPGroup 2 ((yamadaM₆ d t).subgroupOf (nThree d t)) :=
      (isPGroup_yamadaM₆ h d hp).comap_subtype
    exact le_Y₂_of_normal_isPGroup h d hp hK hT hTp (show (⟨x, hxN⟩ : nThree d t) ∈ _ from hxM)
  · exact le_inf (yamadaY₂_le_nThree h d hp hK) (yamadaY₂_le_yamadaM₆' h d hp.layer)

theorem pCoreOf_nTwo (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) : pCoreOf 2 (nTwo d t) = yamadaM₆ d t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN3 := nThree_le_normalizer_M₆ h d hp hK
  have hM6p := isPGroup_yamadaM₆ h d hp
  have hnorm : nTwo d t ≤ normalizer ((yamadaM₆ d t : Subgroup G) : Set G) :=
    sup_le hN3 le_normalizer
  apply le_antisymm
  · intro x hx
    set R := pCoreOf 2 (nTwo d t) with hR
    have hRN : R ≤ nTwo d t := CFSG.LieType.BorelTits.pCoreOf_le 2 _
    have hRp : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
    have hnR : nTwo d t ≤ normalizer (R : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
    have hxN : x ∈ ((nThree d t ⊔ yamadaM₆ d t : Subgroup G) : Set G) := hRN hx
    rw [coe_mul_of_left_le_normalizer_right _ _ hN3] at hxN
    obtain ⟨n, hn, m, hm, hnm⟩ := hxN
    have hn : n ∈ nThree d t := hn
    have hm : m ∈ yamadaM₆ d t := hm
    have hnm' : n * m = x := hnm
    have hn' : n ∈ R ⊔ yamadaM₆ d t := by
      have : n = x * m⁻¹ := by rw [← hnm']; group
      rw [this]
      exact mul_mem (mem_sup_left hx) (inv_mem (mem_sup_right hm))
    have hM6R : yamadaM₆ d t ≤ normalizer (R : Set G) := le_sup_right.trans hnR
    have hS2 : IsPGroup 2 (R ⊔ yamadaM₆ d t : Subgroup G) :=
      hRp.to_sup_of_normal_left' hM6p hM6R
    have hNS : nThree d t ≤ normalizer ((R ⊔ yamadaM₆ d t : Subgroup G) : Set G) := by
      intro g hg
      exact Subgroup.inf_normalizer_le_normalizer_sup _ _
        ⟨hnR (show g ∈ nTwo d t from mem_sup_left hg), hN3 hg⟩
    have hT : ((R ⊔ yamadaM₆ d t).subgroupOf (nThree d t)).Normal :=
      ⟨fun x hx g => by
        rw [mem_subgroupOf] at hx ⊢
        exact (mem_normalizer_iff.1 (hNS g.2) x).1 hx⟩
    have hTp : IsPGroup 2 ((R ⊔ yamadaM₆ d t).subgroupOf (nThree d t)) := hS2.comap_subtype
    have hnY : n ∈ yamadaY₂ d t :=
      le_Y₂_of_normal_isPGroup h d hp hK hT hTp (show (⟨n, hn⟩ : nThree d t) ∈ _ from hn')
    rw [← hnm']
    exact mul_mem (yamadaY₂_le_yamadaM₆' h d hp.layer hnY) hm
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right hnorm hM6p

theorem card_kThree (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    Nat.card (kThree d t K) = (2 ^ f) ^ 2 * ((2 ^ f) * ((2 ^ f) ^ 2 - 1)) := by
  obtain ⟨φ, hφs, hφk⟩ := exists_phi h d hp hK
  obtain ⟨-, -, hcard, -, -⟩ := eOne_decomp h d hp hK
  have h1 := Subgroup.card_ker_mul_card_of_surjective hφs
  rw [hφk, d.card_SL_Γ₀] at h1
  have h2 : Nat.card ((eOne d t K).subgroupOf (kThree d t K)) = Nat.card (eOne d t K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (eOne_le_kThree h d hp hK)).toEquiv
  rw [h2, hcard] at h1
  exact h1.symm

theorem card_nThree (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    Nat.card (nThree d t) = Nat.card (kThree d t K) ^ 2 := by
  obtain ⟨h1, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (kThree d t K)
    (kThree d t K)ᵍ[t] (commute_of_commutator_eq_bot (kThree_comm d hK))
  rw [kThree_inf_conj h d hp hK, Subgroup.card_bot, mul_one,
    Subgroup.card_map_of_injective (MulAut.conj t⁻¹).injective] at h1
  rw [nThree_eq h d hp hK, h1, sq]

theorem yamadaP_eq_sup (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    yamadaP d t = yamadaM₆ d t ⊔ prodX d t := by
  have hlay := hp.layer
  obtain ⟨-, -, -, -, -, -, -, -, hM6, hP, -⟩ := T4_series_free h d hp
  obtain ⟨-, -, -, -, -, -, -, -, -, hMC, -, hX6⟩ := T5_J₀ h d hp
  have hY₂card := (h.yamada_5_9_2 d hlay).2.1
  have hXP : prodX d t ≤ yamadaP d t := inf_le_left.trans (yamadaD₅_le_yamadaP d t)
  have hle : yamadaM₆ d t ⊔ prodX d t ≤ yamadaP d t :=
    sup_le (yamadaM₆_le_yamadaP d t) hXP
  have hXN : prodX d t ≤ normalizer ((yamadaM₆ d t : Subgroup G) : Set G) :=
    hXP.trans (h.yamadaP_le_normalizer_yamadaM₆ d hlay)
  have hset := coe_mul_of_right_le_normalizer_left (yamadaM₆ d t) (prodX d t) hXN
  have hinf : yamadaM₆ d t ⊓ prodX d t = yamadaY₂ d t :=
    le_antisymm
      (le_trans (inf_le_inf_left _ (inf_le_right : prodX d t ≤ jZeroCentralizer d)) hMC.le)
      (le_inf (yamadaY₂_le_yamadaM₆' h d hlay) (yamadaY₂_le_prodX h d hp))
  have h1 := ncard_mul_mul_card_inf (yamadaM₆ d t) (prodX d t)
  rw [hinf, hY₂card, hM6, card_prodX h d hp] at h1
  have h2 : Nat.card (yamadaM₆ d t ⊔ prodX d t : Subgroup G) =
      (((yamadaM₆ d t : Set G) * (prodX d t : Set G))).ncard := by
    rw [← hset]
    exact Nat.card_coe_set_eq _
  have hpos : 0 < (2 ^ f) ^ 4 := by positivity
  have h3 : ((yamadaM₆ d t : Set G) * (prodX d t : Set G)).ncard = (2 ^ f) ^ 24 := by
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [h1]
    ring
  refine (eq_of_le_of_card_ge hle ?_).symm
  rw [hP, h2, h3]

theorem isSylowOf_yamadaP_nTwo (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    IsSylowOf 2 (yamadaP d t) (nTwo d t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hlay := hp.layer
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  obtain ⟨-, -, -, -, -, -, -, -, hM6, hP, -⟩ := T4_series_free h d hp
  have hY₂card := (h.yamada_5_9_2 d hlay).2.1
  have hPeq := yamadaP_eq_sup h d hp
  have hle : yamadaP d t ≤ nTwo d t := by
    rw [hPeq]
    exact sup_le le_sup_right ((prodX_le_nThree h d hp hK).trans le_sup_left)
  have hP2 : IsPGroup 2 (yamadaP d t) := IsPGroup.of_card (n := f * 24) (by rw [hP, ← pow_mul])
  refine ⟨hle, hP2, ?_⟩
  have hN3 := nThree_le_normalizer_M₆ h d hp hK
  have hset := coe_mul_of_left_le_normalizer_right (nThree d t) (yamadaM₆ d t) hN3
  have h1 := ncard_mul_mul_card_inf (nThree d t) (yamadaM₆ d t)
  rw [nThree_inf_M₆ h d hp hK, hY₂card, hM6, card_nThree h d hp hK, card_kThree h d hp hK] at h1
  have h2 : Nat.card (nTwo d t) = (((nThree d t : Set G) * (yamadaM₆ d t : Set G))).ncard := by
    rw [← hset]
    exact Nat.card_coe_set_eq _
  have hpos : 0 < (2 ^ f) ^ 4 := by positivity
  have h3 : Nat.card (nTwo d t) = (2 ^ f) ^ 24 * ((2 ^ f) ^ 2 - 1) ^ 2 := by
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [h2, h1]
    ring
  have h4 := Subgroup.relIndex_mul_card (yamadaP d t) (nTwo d t)
  rw [inf_of_le_left hle, hP, h3] at h4
  have hpos' : 0 < (2 ^ f) ^ 24 := by positivity
  have h5 : (yamadaP d t).relIndex (nTwo d t) = ((2 ^ f) ^ 2 - 1) ^ 2 := by
    refine Nat.eq_of_mul_eq_mul_right hpos' ?_
    rw [h4]
    ring
  rw [h5]
  have hf : 1 ≤ f := by have := hp.two_le; omega
  have hev : Even ((2 ^ f) ^ 2) := by
    rw [← pow_mul]
    exact (Nat.even_pow.2 ⟨even_two, by omega⟩)
  have hodd : Odd ((2 ^ f) ^ 2 - 1) := by
    refine Nat.Even.sub_odd ?_ hev odd_one
    exact Nat.one_le_pow _ _ (by positivity)
  have hodd2 : Odd (((2 ^ f) ^ 2 - 1) ^ 2) := hodd.pow
  rintro ⟨c, hc⟩
  have := Nat.odd_iff.1 hodd2
  omega

end NTwo

end ProductLayerAux

section Statements

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem A1_components (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    ∃ K : Subgroup G, IsLayerComponent d t K ∧ Odd (Nat.card (zc (jZeroLayer d))) ∧
      LieModel (↥K ⧸ Subgroup.center ↥K) .PSL 3 2 f := by
  obtain ⟨K, hK, -⟩ := ProductLayerAux.exists_layerComponent h d hp
  exact ⟨K, hK, ProductLayerAux.odd_card_zc_jZeroLayer h d hp,
    ProductLayerAux.lieModel_layerComponent h d hp hK⟩

theorem A2_sylow (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    (prodX d t = yamadaY₂ d t ⊔ (yamadaY₂ d t).map (MulAut.conj (uG d)).toMonoidHom ∧
      IsSylowOf 2 (prodX d t) (jZeroLayer d) ∧ Nat.card (prodX d t) = (2 ^ f) ^ 6) ∧
    (prodX d t = qThree d t K ⊔ (qThree d t K)ᵍ[t] ∧ qThree d t K ⊓ (qThree d t K)ᵍ[t] = ⊥ ∧
      ⁅qThree d t K, (qThree d t K)ᵍ[t]⁆ = ⊥ ∧ IsSylowOf 2 (qThree d t K) K ∧
      Nat.card (qThree d t K) = (2 ^ f) ^ 3) ∧
    (yamadaY₂ d t = eOne d t K ⊔ (eOne d t K)ᵍ[t] ∧ eOne d t K ⊓ (eOne d t K)ᵍ[t] = ⊥ ∧
      IsElemAbelian 2 (eOne d t K) ∧ Nat.card (eOne d t K) = (2 ^ f) ^ 2 ∧
      eOne d t K ≤ qThree d t K ∧ ((eOne d t K).subgroupOf (qThree d t K)).Normal ∧
      IsCoatom ((normalizer ((eOne d t K : Subgroup G) : Set G)).subgroupOf K)) := by
  refine ⟨⟨ProductLayerAux.prodX_eq_sup h d hp, (ProductLayerAux.prodX_sylow h d hp).1,
    ProductLayerAux.card_prodX h d hp⟩, ProductLayerAux.qThree_decomp h d hp hK, ?_⟩
  obtain ⟨hdec, hinf, hcard, hle, hel⟩ := ProductLayerAux.eOne_decomp h d hp hK
  exact ⟨hdec, hinf, hel, hcard, hle, (ProductLayerAux.eOne_normal h d hp hK).2,
    ProductLayerAux.isCoatom_normalizer_eOne h d hp hK⟩

theorem A3_structure (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    (eOne d t K ≤ kThree d t K ∧ pCoreOf 2 (kThree d t K) = eOne d t K ∧
      IsQuotientIso (kThree d t K) (eOne d t K) (SL(2, d.Γ₀)) ∧ kThree d t K ⊓ zc K = ⊥ ∧
      nThree d t = kThree d t K ⊔ (kThree d t K)ᵍ[t] ∧
      kThree d t K ⊓ (kThree d t K)ᵍ[t] = ⊥ ∧ ⁅kThree d t K, (kThree d t K)ᵍ[t]⁆ = ⊥ ∧
      IsQuotientIso (nThree d t) (yamadaY₂ d t) (SL(2, d.Γ₀) × SL(2, d.Γ₀))) ∧
    (nThree d t = prodX d t ⊔ (prodX d t).map (MulAut.conj (vG d)).toMonoidHom ∧
      d.leviLong.map L.subtype ≤ nThree d t ∧
      nThree d t ≤ normalizer ((yamadaM₆ d t : Subgroup G) : Set G) ∧
      ∃ v₁ ∈ kThree d t K, vG d = v₁ * (t⁻¹ * v₁ * t) ∧
        v₁ ∉ normalizer ((qThree d t K : Subgroup G) : Set G)) ∧
    (nThree d t ⊓ yamadaM₆ d t = yamadaY₂ d t ∧ pCoreOf 2 (nTwo d t) = yamadaM₆ d t ∧
      yamadaP d t = yamadaM₆ d t ⊔ prodX d t ∧ IsSylowOf 2 (yamadaP d t) (nTwo d t) ∧
      yamadaM₆ d t ⊓ centralizer ((jZeroG d : Subgroup G) : Set G) = yamadaY₂ d t) := by
  refine ⟨⟨ProductLayerAux.eOne_le_kThree h d hp hK, ProductLayerAux.pCoreOf_kThree h d hp hK,
    ProductLayerAux.exists_phi h d hp hK, ProductLayerAux.kThree_inf_zc h d hp hK,
    ProductLayerAux.nThree_eq h d hp hK, ProductLayerAux.kThree_inf_conj h d hp hK,
    ProductLayerAux.kThree_comm d hK, ProductLayerAux.exists_rho h d hp hK⟩,
    ⟨ProductLayerAux.nThree_eq_prodX_sup h d hp hK,
      ProductLayerAux.leviLong_map_le_nThree h d hp hK,
      ProductLayerAux.nThree_le_normalizer_M₆ h d hp hK, ProductLayerAux.sigG h d hp hK d.slV,
      ProductLayerAux.v₁_mem_kThree h d hp hK, ProductLayerAux.vG_eq_v₁ h d hp hK,
      ProductLayerAux.v₁_not_mem_normalizer h d hp hK⟩,
    ProductLayerAux.nThree_inf_M₆ h d hp hK, ProductLayerAux.pCoreOf_nTwo h d hp hK,
    ProductLayerAux.yamadaP_eq_sup h d hp, ProductLayerAux.isSylowOf_yamadaP_nTwo h d hp hK, ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hMC, -, -⟩ := T5_J₀ h d hp
  exact hMC

theorem A4_u_component (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    (zc (qThree d t K) = eOne d t K ⊓ yamadaV₁ d t ∧
      Nat.card (zc (qThree d t K)) = 2 ^ f ∧
      yamadaV₁ d t = zc (qThree d t K) ⊔ (zc (qThree d t K))ᵍ[t] ∧
      zc (qThree d t K) ⊓ (zc (qThree d t K))ᵍ[t] = ⊥) ∧
    Kᵍ[uG d] = K ∧ qThree d t K = eOne d t K ⊔ (eOne d t K)ᵍ[uG d] :=
  ⟨⟨ProductLayerAux.zc_qThree_eq h d hp hK, ProductLayerAux.card_zc_qThree h d hp hK,
    ProductLayerAux.yamadaV₁_eq_zc_sup h d hp hK, ProductLayerAux.zc_inf_conj h d hp hK⟩,
    ProductLayerAux.conj_u_eq h d hp hK, ProductLayerAux.qThree_eq_eOne_sup_conj h d hp hK⟩

end Statements

end CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase

module

public import CFSG.LocalAnalysis.EvenBN.G2.ProductDefs
import CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductN2
import CFSG.LocalAnalysis.EvenBN.Common.FongSeitzFourB
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Sporadic.Schreier.J4SOrder
public import CFSG.Sporadic.Th.Max3.Quotient
public import Certificates.Certificate10091Base

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure (BarM barMap barSub)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialLayer (ExactClosure)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialCases (FieldAlternative ProductAlternative)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (centerMod centralizerMod IsQuotientIso zc)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
open scoped commutatorElement Pointwise MatrixGroups

namespace CFSG.LocalAnalysis.EvenBN.G2.ProductN2Aux

open CFSG.LocalAnalysis.EvenBN.TrialityD4 (mem_normalizer_inf_D4 mem_normalizer_centralizer_D4)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (map_conj_inv_map_conj_inv centerMod
  centralizerMod)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN2Aux

section Generic

variable {Q : Type*} [Group Q]

theorem sup_inf_of_card_le {B₁ B₂ T : Subgroup Q} [Finite Q] {n : ℕ}
    (hcomm : ∀ a ∈ B₁, ∀ b ∈ B₂, a * b = b * a) (hinf : B₁ ⊓ B₂ = ⊥) (hT : T ≤ B₁ ⊔ B₂)
    (hT2 : IsPGroup 2 T) (h₁ : ∀ S : Subgroup Q, S ≤ B₁ → IsPGroup 2 S → Nat.card S ≤ n)
    (h₂ : ∀ S : Subgroup Q, S ≤ B₂ → IsPGroup 2 S → Nat.card S ≤ n)
    (hcard : Nat.card T = n * n) : T = (T ⊓ B₁) ⊔ (T ⊓ B₂) := by
  classical
  have hB₁N : B₁ ≤ normalizer (B₂ : Set Q) := le_normalizer_of_commute hcomm le_rfl le_rfl
  have hcomm' : ∀ a ∈ B₂, ∀ b ∈ B₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  let T₁ : Subgroup Q :=
    { carrier := {a | a ∈ B₁ ∧ ∃ b ∈ B₂, a * b ∈ T}
      mul_mem' := by
        rintro a a' ⟨ha, b, hb, hab⟩ ⟨ha', b', hb', hab'⟩
        refine ⟨mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
        have e : a * a' * (b * b') = (a * b) * (a' * b') := by
          calc a * a' * (b * b') = a * (a' * b) * b' := by group
            _ = a * (b * a') * b' := by rw [hcomm a' ha' b hb]
            _ = (a * b) * (a' * b') := by group
        rw [e]
        exact mul_mem hab hab'
      one_mem' := ⟨one_mem _, 1, one_mem _, by simpa using one_mem T⟩
      inv_mem' := by
        rintro a ⟨ha, b, hb, hab⟩
        refine ⟨inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
        have e : a⁻¹ * b⁻¹ = (a * b)⁻¹ := by
          rw [mul_inv_rev, hcomm a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)]
        rw [e]
        exact inv_mem hab }
  let T₂ : Subgroup Q :=
    { carrier := {b | b ∈ B₂ ∧ ∃ a ∈ B₁, a * b ∈ T}
      mul_mem' := by
        rintro b b' ⟨hb, a, ha, hab⟩ ⟨hb', a', ha', hab'⟩
        refine ⟨mul_mem hb hb', a * a', mul_mem ha ha', ?_⟩
        have e : a * a' * (b * b') = (a * b) * (a' * b') := by
          calc a * a' * (b * b') = a * (a' * b) * b' := by group
            _ = a * (b * a') * b' := by rw [hcomm a' ha' b hb]
            _ = (a * b) * (a' * b') := by group
        rw [e]
        exact mul_mem hab hab'
      one_mem' := ⟨one_mem _, 1, one_mem _, by simpa using one_mem T⟩
      inv_mem' := by
        rintro b ⟨hb, a, ha, hab⟩
        refine ⟨inv_mem hb, a⁻¹, inv_mem ha, ?_⟩
        have e : a⁻¹ * b⁻¹ = (a * b)⁻¹ := by
          rw [mul_inv_rev, hcomm a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)]
        rw [e]
        exact inv_mem hab }
  have hT₁B : T₁ ≤ B₁ := fun a ha => ha.1
  have hT₂B : T₂ ≤ B₂ := fun b hb => hb.1
  have hpow : ∀ {a b : Q}, a ∈ B₁ → b ∈ B₂ → a * b ∈ T →
      ∃ k : ℕ, a ^ 2 ^ k = 1 ∧ b ^ 2 ^ k = 1 := by
    intro a b ha hb hab
    obtain ⟨k, hk⟩ := hT2 ⟨a * b, hab⟩
    have hk' : (a * b) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hc : Commute a b := hcomm a ha b hb
    rw [hc.mul_pow] at hk'
    have h1 : a ^ 2 ^ k ∈ B₁ ⊓ B₂ := mem_inf.2 ⟨pow_mem ha _, by
      have : a ^ 2 ^ k = (b ^ 2 ^ k)⁻¹ := eq_inv_of_mul_eq_one_left hk'
      rw [this]
      exact inv_mem (pow_mem hb _)⟩
    rw [hinf, mem_bot] at h1
    refine ⟨k, h1, ?_⟩
    rw [h1, one_mul] at hk'
    exact hk'
  have hT₁2 : IsPGroup 2 T₁ := fun a => by
    obtain ⟨ha, b, hb, hab⟩ := a.2
    obtain ⟨k, hk, -⟩ := hpow ha hb hab
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hT₂2 : IsPGroup 2 T₂ := fun b => by
    obtain ⟨hb, a, ha, hab⟩ := b.2
    obtain ⟨k, -, hk⟩ := hpow ha hb hab
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hc₁ := h₁ T₁ hT₁B hT₁2
  have hc₂ := h₂ T₂ hT₂B hT₂2
  have hTle : T ≤ T₁ ⊔ T₂ := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Common.exists_mul_of_le_normalizer' hB₁N x (hT hx)
    exact mul_mem_sup ⟨ha, b, hb, hx⟩ ⟨hb, a, ha, hx⟩
  have hinf' : T₁ ⊓ T₂ = ⊥ := eq_bot_iff.2 fun x hx =>
    hinf.le ⟨hT₁B (mem_inf.1 hx).1, hT₂B (mem_inf.1 hx).2⟩
  have hcard' : Nat.card ↥(T₁ ⊔ T₂) = Nat.card T₁ * Nat.card T₂ :=
    card_sup_eq_mul_of_commute (fun a ha b hb => hcomm a (hT₁B ha) b (hT₂B hb)) hinf'
  have hTeq : T = T₁ ⊔ T₂ := by
    refine Subgroup.eq_of_le_of_card_ge hTle ?_
    rw [hcard', hcard]
    exact Nat.mul_le_mul hc₁ hc₂
  have hT₁T : T₁ ≤ T := hTeq ▸ le_sup_left
  have hT₂T : T₂ ≤ T := hTeq ▸ le_sup_right
  have e₁ : T ⊓ B₁ = T₁ := le_antisymm (fun x hx => ⟨hx.2, 1, one_mem _, by simpa using hx.1⟩)
    (le_inf hT₁T hT₁B)
  have e₂ : T ⊓ B₂ = T₂ := le_antisymm (fun x hx => ⟨hx.2, 1, one_mem _, by simpa using hx.1⟩)
    (le_inf hT₂T hT₂B)
  rw [e₁, e₂]
  exact hTeq

theorem mem_normalizer_map_conj {E : Subgroup Q} {a : Q} (g : Q)
    (ha : a ∈ normalizer (E : Set Q)) :
    g⁻¹ * a * g ∈ normalizer ((Eᵍ[g] : Subgroup Q) : Set Q) := by
  rw [mem_normalizer_iff]
  intro x
  rw [Common.mem_map_conj_inv_iff, Common.mem_map_conj_inv_iff]
  have e : g * (g⁻¹ * a * g * x * (g⁻¹ * a * g)⁻¹) * g⁻¹ = a * (g * x * g⁻¹) * a⁻¹ := by group
  rw [e]
  exact mem_normalizer_iff.1 ha _

theorem isPGroup_two_of_mul_self' {E : Subgroup Q} (hE : ∀ x ∈ E, x * x = 1) :
    IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa [sq] using hE x x.2)⟩

theorem map_conj_le_of_mem_normalizer {X Y : Subgroup Q} {g : Q}
    (hg : g ∈ normalizer (Y : Set Q)) (hXY : X ≤ Y) : X.map (MulAut.conj g).toMonoidHom ≤ Y := by
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_normalizer_iff.1 hg x).1 (hXY hx)

theorem mem_map_conj_iff {K : Subgroup Q} {s x : Q} :
    x ∈ K.map (MulAut.conj s).toMonoidHom ↔ s⁻¹ * x * s ∈ K := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem mem_normalizer_sup_aux {A B : Subgroup Q} {g : Q} (hA : g ∈ normalizer (A : Set Q))
    (hB : g ∈ normalizer (B : Set Q)) : g ∈ normalizer ((A ⊔ B : Subgroup Q) : Set Q) := by
  rw [mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem mem_normalizer_commutator_aux {A B : Subgroup Q} {g : Q}
    (hA : g ∈ normalizer (A : Set Q)) (hB : g ∈ normalizer (B : Set Q)) :
    g ∈ normalizer ((⁅A, B⁆ : Subgroup Q) : Set Q) := by
  rw [mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_commutator, hA, hB]

theorem eq_bot_of_normal_two {B S : Subgroup Q} (hB : IsSimpleGroup B) (hnot : ¬ IsPGroup 2 B)
    (hSB : S ≤ B) (hn : B ≤ normalizer (S : Set Q)) (hS2 : IsPGroup 2 S) : S = ⊥ := by
  haveI : (S.subgroupOf B).Normal := (normal_subgroupOf_iff_le_normalizer hSB).2 hn
  rcases hB.eq_bot_or_eq_top_of_normal (S.subgroupOf B) with h | h
  · rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hSB hx⟩ : B) ∈ S.subgroupOf B := mem_subgroupOf.2 hx
    rw [h, mem_bot] at h1
    exact (mem_bot.2 (congrArg Subtype.val h1))
  · exfalso
    apply hnot
    have hBS : B ≤ S := by
      intro x hx
      have : (⟨x, hx⟩ : B) ∈ S.subgroupOf B := by rw [h]; exact mem_top _
      exact mem_subgroupOf.1 this
    exact hS2.to_le hBS

end Generic

section SL2

variable {Q : Type*} [Group Q] {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

theorem card_le_of_isPGroup_sl2 {X : Subgroup Q} (ψ : X ≃* SL(2, K)) (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {S : Subgroup Q} (hSX : S ≤ X) (hS : IsPGroup 2 S) :
    Nat.card S ≤ Nat.card K := by
  haveI := Fintype.ofFinite K
  have hS' : IsPGroup 2 (S.subgroupOf X) := hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSX).symm
  have h := Common.card_le_of_isPGroup_SL2 (K := K) hf (by rw [← Nat.card_eq_fintype_card, hK])
    (hS'.map ψ.toMonoidHom)
  rw [Subgroup.card_map_of_injective ψ.injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSX).toEquiv] at h
  rw [hK]
  exact h

theorem not_isPGroup_sl2 {X : Subgroup Q} (ψ : X ≃* SL(2, K)) (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) : ¬ IsPGroup 2 X := by
  intro hX
  have h := card_le_of_isPGroup_sl2 ψ (by omega) hK le_rfl hX
  have h1 : Nat.card X = Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [Nat.card_congr ψ.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  rw [h1] at h
  have h2 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h5 : 3 ≤ Nat.card K ^ 2 - 1 := by
    have : 16 ≤ Nat.card K ^ 2 := by nlinarith
    omega
  have h3 : Nat.card K * 3 ≤ Nat.card K * (Nat.card K ^ 2 - 1) := Nat.mul_le_mul_left _ h5
  omega

theorem isSimpleGroup_sl2 {X : Subgroup Q} (ψ : X ≃* SL(2, K)) (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) : IsSimpleGroup X := by
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have := Common.sl2_isSimpleGroup_of_charTwo h4
  exact ψ.isSimpleGroup

theorem commutator_eq_self_sl2 {X : Subgroup Q} (ψ : X ≃* SL(2, K)) (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) : ⁅X, X⁆ = X := by
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have := CFSG.LinearGroups.special_linear_dimension_two_perfect (Common.exists_finset_card_four h4)
  have : Group.IsPerfect X := Group.IsPerfect.ofSurjective (f := ψ.symm.toMonoidHom)
    ψ.symm.surjective
  exact Subgroup.isPerfect_iff.1 this

end SL2

section Hat

variable {Q : Type*} [Group Q]

structure Hat73 (K : Type) [Field K] (f : ℕ) (t s : Q) (E B P F : Subgroup Q) : Prop where
  t_sq : t * t = 1
  E_comm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x
  E_sq : ∀ x ∈ E, x * x = 1
  E_t : Eᵍ[t] = E
  B_E : B ≤ normalizer (E : Set Q)
  B_comm : ∀ a ∈ B, ∀ b ∈ Bᵍ[t], a * b = b * a
  BB_inf : (B ⊔ Bᵍ[t]) ⊓ E = ⊥
  B_inf : B ⊓ Bᵍ[t] = ⊥
  sl2 : Nonempty (↥B ≃* SL(2, K))
  card_K : Nat.card K = 2 ^ f
  two_le : 2 ≤ f
  s_E : s ∈ normalizer (E : Set Q)
  s_B : s ∈ normalizer (B : Set Q)
  s_B' : s ∈ normalizer ((Bᵍ[t] : Subgroup Q) : Set Q)
  P_E : E ≤ P
  P_two : IsPGroup 2 P
  P_le : P ≤ (B ⊔ Bᵍ[t]) ⊔ E
  P_t : Pᵍ[t] = P
  P_card : Nat.card P = Nat.card K ^ 2 * Nat.card E
  N_gen : (B ⊔ Bᵍ[t]) ⊔ E = P ⊔ P.map (MulAut.conj s).toMonoidHom
  F_eq : F = P ⊓ centralizer (P : Set Q)
  E_F : E = F ⊔ F.map (MulAut.conj s).toMonoidHom
  F_inf : F ⊓ F.map (MulAut.conj s).toMonoidHom = ⊥
  Z_bot : E ⊓ centralizer ((B ⊔ Bᵍ[t] : Subgroup Q) : Set Q) = ⊥
  card_E : Nat.card E = Nat.card K ^ 4
  cent_E : ∀ x ∈ (B ⊔ Bᵍ[t]) ⊔ E, (∀ e ∈ E, x * e = e * x) → x ∈ E

namespace Hat73

variable {K : Type} [Field K] {f : ℕ} {t s : Q} {E B P F : Subgroup Q}
  (D : Hat73 K f t s E B P F)
include D

theorem B'_E : Bᵍ[t] ≤ normalizer (E : Set Q) := by
  rintro _ ⟨a, ha, rfl⟩
  have := mem_normalizer_map_conj t (D.B_E ha)
  rw [D.E_t] at this
  simpa using this

theorem four_le_card : 4 ≤ Nat.card K := by
  rw [D.card_K]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) D.two_le

theorem E_ne : E ≠ ⊥ := by
  intro h
  have h1 := D.card_E
  rw [h, Subgroup.card_bot] at h1
  have h2 : 1 < Nat.card K ^ 4 :=
    Nat.one_lt_pow (by norm_num) (by have := D.four_le_card; omega)
  omega

variable [Finite Q] [Finite K] [CharP K 2]

theorem sl2' : Nonempty (↥(Bᵍ[t]) ≃* SL(2, K)) := by
  obtain ⟨ψ⟩ := D.sl2
  exact ⟨(Subgroup.equivMapOfInjective B (MulAut.conj t⁻¹).toMonoidHom
    (fun a b hab => (MulAut.conj t⁻¹).injective hab)).symm.trans ψ⟩

theorem B_N_B' : B ≤ normalizer ((Bᵍ[t] : Subgroup Q) : Set Q) :=
  le_normalizer_of_commute D.B_comm le_rfl le_rfl

theorem B'_N_B : Bᵍ[t] ≤ normalizer (B : Set Q) :=
  le_normalizer_of_commute (fun a ha b hb => (D.B_comm b hb a ha).symm) le_rfl le_rfl

theorem BB_N_E : B ⊔ Bᵍ[t] ≤ normalizer (E : Set Q) := sup_le D.B_E D.B'_E

theorem card_le_B {S : Subgroup Q} (hS : S ≤ B) (hS2 : IsPGroup 2 S) : Nat.card S ≤ Nat.card K := by
  obtain ⟨ψ⟩ := D.sl2
  exact card_le_of_isPGroup_sl2 ψ (by have := D.two_le; omega) D.card_K hS hS2

theorem card_le_B' {S : Subgroup Q} (hS : S ≤ Bᵍ[t]) (hS2 : IsPGroup 2 S) :
    Nat.card S ≤ Nat.card K := by
  obtain ⟨ψ⟩ := D.sl2'
  exact card_le_of_isPGroup_sl2 ψ (by have := D.two_le; omega) D.card_K hS hS2

theorem P_eq : P = ((P ⊓ B) ⊔ (P ⊓ Bᵍ[t])) ⊔ E := by
  have hT : P = (P ⊓ (B ⊔ Bᵍ[t])) ⊔ E := by
    refine le_antisymm (fun x hx => ?_) (sup_le inf_le_left D.P_E)
    obtain ⟨y, hy, e, he, rfl⟩ := Common.exists_mul_of_le_normalizer' D.BB_N_E x (D.P_le hx)
    have hyP : y ∈ P := by
      have := mul_mem hx (inv_mem (D.P_E he))
      rwa [mul_inv_cancel_right] at this
    exact mul_mem_sup (mem_inf.2 ⟨hyP, hy⟩) he
  have hcard : Nat.card ↥(P ⊓ (B ⊔ Bᵍ[t])) = Nat.card K * Nat.card K := by
    have h1 := Common.card_sup_mul_card_inf_eq (A := E) (B := P ⊓ (B ⊔ Bᵍ[t]))
      (inf_le_right.trans D.BB_N_E)
    have h2 : E ⊓ (P ⊓ (B ⊔ Bᵍ[t])) = ⊥ := eq_bot_iff.2 fun x hx =>
      D.BB_inf.le ⟨(mem_inf.1 (mem_inf.1 hx).2).2, (mem_inf.1 hx).1⟩
    rw [h2, Subgroup.card_bot, mul_one, sup_comm, ← hT, D.P_card] at h1
    have hq : 0 < Nat.card E := Nat.card_pos
    have h3 : Nat.card E * Nat.card ↥(P ⊓ (B ⊔ Bᵍ[t])) =
        Nat.card E * (Nat.card K * Nat.card K) := by
      rw [← h1]
      ring
    exact Nat.eq_of_mul_eq_mul_left hq h3
  have hdec := sup_inf_of_card_le D.B_comm D.B_inf (inf_le_right : P ⊓ (B ⊔ Bᵍ[t]) ≤ _)
    (D.P_two.to_le inf_le_left) (fun S hS hS2 => D.card_le_B hS hS2)
    (fun S hS hS2 => D.card_le_B' hS hS2) hcard
  have e₁ : (P ⊓ (B ⊔ Bᵍ[t])) ⊓ B = P ⊓ B := by
    rw [inf_assoc, inf_of_le_right (le_sup_left : B ≤ B ⊔ Bᵍ[t])]
  have e₂ : (P ⊓ (B ⊔ Bᵍ[t])) ⊓ Bᵍ[t] = P ⊓ Bᵍ[t] := by
    rw [inf_assoc, inf_of_le_right (le_sup_right : Bᵍ[t] ≤ B ⊔ Bᵍ[t])]
  rw [e₁, e₂] at hdec
  rw [← hdec]
  exact hT

theorem U_conj : (P ⊓ B)ᵍ[t] = P ⊓ Bᵍ[t] := by
  rw [Subgroup.map_inf _ _ _ (fun a b hab => (MulAut.conj t⁻¹).injective hab), D.P_t]

theorem Z₂_eq : E ⊓ centralizer ((P ⊓ Bᵍ[t] : Subgroup Q) : Set Q) =
    (E ⊓ centralizer ((P ⊓ B : Subgroup Q) : Set Q))ᵍ[t] := by
  have h := map_inf_centralizer_aux (MulAut.conj t⁻¹) E (P ⊓ B)
  rw [D.E_t, D.U_conj] at h
  exact h.symm

theorem F_eq' : F = (E ⊓ centralizer ((P ⊓ B : Subgroup Q) : Set Q)) ⊓
    (E ⊓ centralizer ((P ⊓ Bᵍ[t] : Subgroup Q) : Set Q)) := by
  have hFE : F ≤ E := by
    intro x hx
    rw [D.F_eq] at hx
    obtain ⟨hxP, hxC⟩ := mem_inf.1 hx
    exact D.cent_E x (D.P_le hxP) fun e he => (mem_centralizer_iff.1 hxC e (D.P_E he)).symm
  refine le_antisymm (le_inf (le_inf hFE ?_) (le_inf hFE ?_)) ?_
  · rw [D.F_eq]
    exact (inf_le_right.trans (centralizer_le (SetLike.coe_subset_coe.2
      (inf_le_left : P ⊓ B ≤ P))))
  · rw [D.F_eq]
    exact (inf_le_right.trans (centralizer_le (SetLike.coe_subset_coe.2
      (inf_le_left : P ⊓ Bᵍ[t] ≤ P))))
  · intro x hx
    obtain ⟨⟨hxE, hx1⟩, -, hx2⟩ := (⟨mem_inf.1 (mem_inf.1 hx).1, mem_inf.1 (mem_inf.1 hx).2⟩ :
      (x ∈ E ∧ x ∈ centralizer ((P ⊓ B : Subgroup Q) : Set Q)) ∧
        (x ∈ E ∧ x ∈ centralizer ((P ⊓ Bᵍ[t] : Subgroup Q) : Set Q)))
    rw [D.F_eq]
    refine mem_inf.2 ⟨D.P_E hxE, mem_centralizer_iff.2 fun h hh => ?_⟩
    have hP : P ≤ centralizer ({x} : Set Q) := by
      rw [D.P_eq]
      refine sup_le (sup_le ?_ ?_) ?_
      · intro y hy
        exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hx1 y hy)
      · intro y hy
        exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hx2 y hy)
      · intro y hy
        exact mem_centralizer_singleton_iff.2 (D.E_comm x hxE y hy).symm
    exact (mem_centralizer_singleton_iff.1 (hP hh))

theorem B_gen : B = (P ⊓ B) ⊔ (P ⊓ B).map (MulAut.conj s).toMonoidHom := by
  have hsE : E.map (MulAut.conj s).toMonoidHom = E := mem_normalizer_iff_map_conj_eq.1 D.s_E
  have hU₁B : P ⊓ B ≤ B := inf_le_right
  have hU₂B : P ⊓ Bᵍ[t] ≤ Bᵍ[t] := inf_le_right
  have hX₁B : (P ⊓ B) ⊔ (P ⊓ B).map (MulAut.conj s).toMonoidHom ≤ B :=
    sup_le hU₁B (map_conj_le_of_mem_normalizer D.s_B hU₁B)
  have hX₂B : (P ⊓ Bᵍ[t]) ⊔ (P ⊓ Bᵍ[t]).map (MulAut.conj s).toMonoidHom ≤ Bᵍ[t] :=
    sup_le hU₂B (map_conj_le_of_mem_normalizer D.s_B' hU₂B)
  set X₁ := (P ⊓ B) ⊔ (P ⊓ B).map (MulAut.conj s).toMonoidHom with hX₁
  set X₂ := (P ⊓ Bᵍ[t]) ⊔ (P ⊓ Bᵍ[t]).map (MulAut.conj s).toMonoidHom with hX₂
  have hXE : X₁ ⊔ X₂ ≤ normalizer (E : Set Q) := sup_le (hX₁B.trans D.B_E) (hX₂B.trans D.B'_E)
  have hX₁N : X₁ ≤ normalizer (X₂ : Set Q) :=
    le_normalizer_of_commute D.B_comm hX₁B hX₂B
  have hP : P ≤ (X₁ ⊔ X₂) ⊔ E := by
    rw [D.P_eq]
    exact sup_le (sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left))
      (le_sup_left.trans (le_sup_right.trans le_sup_left))) le_sup_right
  have hPs : P.map (MulAut.conj s).toMonoidHom ≤ (X₁ ⊔ X₂) ⊔ E := by
    rw [D.P_eq]
    simp only [Subgroup.map_sup, hsE]
    exact sup_le (sup_le (le_sup_right.trans (le_sup_left.trans le_sup_left))
      (le_sup_right.trans (le_sup_right.trans le_sup_left))) le_sup_right
  refine le_antisymm (fun b hb => ?_) hX₁B
  have hbN : b ∈ (X₁ ⊔ X₂) ⊔ E := by
    have : b ∈ (B ⊔ Bᵍ[t]) ⊔ E := mem_sup_left (mem_sup_left hb)
    rw [D.N_gen] at this
    exact sup_le hP hPs this
  obtain ⟨y, hy, e, he, rfl⟩ := Common.exists_mul_of_le_normalizer' hXE b hbN
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Common.exists_mul_of_le_normalizer' hX₁N y hy
  have ha : x₁⁻¹ * (x₁ * x₂ * e) ∈ B := mul_mem (inv_mem (hX₁B hx₁)) hb
  have h1 : x₂⁻¹ * (x₁⁻¹ * (x₁ * x₂ * e)) ∈ (B ⊔ Bᵍ[t]) ⊓ E := by
    refine mem_inf.2 ⟨mul_mem (inv_mem (mem_sup_right (hX₂B hx₂))) (mem_sup_left ha), ?_⟩
    have e1 : x₂⁻¹ * (x₁⁻¹ * (x₁ * x₂ * e)) = e := by group
    rw [e1]
    exact he
  rw [D.BB_inf, mem_bot] at h1
  have h2 : x₂ = x₁⁻¹ * (x₁ * x₂ * e) := inv_mul_eq_one.1 h1
  have h3 : x₁⁻¹ * (x₁ * x₂ * e) ∈ B ⊓ Bᵍ[t] := mem_inf.2 ⟨ha, h2 ▸ hX₂B hx₂⟩
  rw [D.B_inf, mem_bot] at h3
  have h4 : x₁ = x₁ * x₂ * e := inv_mul_eq_one.1 h3
  rw [← h4]
  exact hx₁

theorem F_le_Z₁ : F ≤ E ⊓ centralizer ((P ⊓ B : Subgroup Q) : Set Q) := by
  rw [D.F_eq']
  exact inf_le_left

theorem F_le_Z₂ : F ≤ E ⊓ centralizer ((P ⊓ Bᵍ[t] : Subgroup Q) : Set Q) := by
  rw [D.F_eq']
  exact inf_le_right

theorem V₁_ne_bot : E ⊓ centralizer (B : Set Q) ≠ ⊥ := by
  have hZ₂t : E ⊓ centralizer ((P ⊓ Bᵍ[t] : Subgroup Q) : Set Q) =
      (E ⊓ centralizer ((P ⊓ B : Subgroup Q) : Set Q))ᵍ[t] := D.Z₂_eq
  have hZ₁t : (E ⊓ centralizer ((P ⊓ Bᵍ[t] : Subgroup Q) : Set Q))ᵍ[t] =
      E ⊓ centralizer ((P ⊓ B : Subgroup Q) : Set Q) := by
    rw [hZ₂t, map_conj_inv_map_conj_inv D.t_sq]
  have hnormFs : F ≤ normalizer ((F.map (MulAut.conj s).toMonoidHom : Subgroup Q) : Set Q) := by
    have hFE : F ≤ E := D.F_le_Z₁.trans inf_le_left
    have hFsE : F.map (MulAut.conj s).toMonoidHom ≤ E :=
      map_conj_le_of_mem_normalizer D.s_E hFE
    exact le_normalizer_of_commute D.E_comm hFE hFsE
  have hA : (E ⊓ centralizer ((P ⊓ B : Subgroup Q) : Set Q)) ⊓
      F.map (MulAut.conj s).toMonoidHom ≠ ⊥ := by
    intro hbot
    have hZ₁F : E ⊓ centralizer ((P ⊓ B : Subgroup Q) : Set Q) ≤ F := by
      intro z hz
      have hzE : z ∈ F ⊔ F.map (MulAut.conj s).toMonoidHom := D.E_F ▸ hz.1
      obtain ⟨f₀, hf₀, f₁, hf₁, rfl⟩ := Common.exists_mul_of_le_normalizer' hnormFs z hzE
      have h1 : f₁ ∈ (E ⊓ centralizer ((P ⊓ B : Subgroup Q) : Set Q)) ⊓
          F.map (MulAut.conj s).toMonoidHom := by
        refine mem_inf.2 ⟨?_, hf₁⟩
        have := mul_mem (inv_mem (D.F_le_Z₁ hf₀)) hz
        rwa [inv_mul_cancel_left] at this
      rw [hbot, mem_bot] at h1
      rw [h1, mul_one]
      exact hf₀
    have hZ₁Z₂ : E ⊓ centralizer ((P ⊓ B : Subgroup Q) : Set Q) ≤
        E ⊓ centralizer ((P ⊓ Bᵍ[t] : Subgroup Q) : Set Q) := fun z hz => D.F_le_Z₂ (hZ₁F hz)
    have hZ₂Z₁ : E ⊓ centralizer ((P ⊓ Bᵍ[t] : Subgroup Q) : Set Q) ≤
        E ⊓ centralizer ((P ⊓ B : Subgroup Q) : Set Q) := by
      have := Subgroup.map_mono (f := (MulAut.conj t⁻¹).toMonoidHom) hZ₁Z₂
      rwa [← hZ₂t, hZ₁t] at this
    have hZ₂F : E ⊓ centralizer ((P ⊓ Bᵍ[t] : Subgroup Q) : Set Q) ≤ F := hZ₂Z₁.trans hZ₁F
    have hU₂s : (P ⊓ Bᵍ[t]).map (MulAut.conj s).toMonoidHom ≤ Bᵍ[t] :=
      map_conj_le_of_mem_normalizer D.s_B' inf_le_right
    have hP2 : IsPGroup 2 (P ⊓ B : Subgroup Q) := D.P_two.to_le inf_le_left
    have hP2' : IsPGroup 2 (P ⊓ Bᵍ[t] : Subgroup Q) := D.P_two.to_le inf_le_left
    have hR2 : IsPGroup 2 ((P ⊓ B) ⊔ (P ⊓ Bᵍ[t]).map (MulAut.conj s).toMonoidHom : Subgroup Q) :=
      IsPGroup.to_sup_of_normal_right' hP2 (hP2'.map _)
        (le_normalizer_of_commute D.B_comm inf_le_right hU₂s)
    have hRE : (P ⊓ B) ⊔ (P ⊓ Bᵍ[t]).map (MulAut.conj s).toMonoidHom ≤ normalizer (E : Set Q) :=
      sup_le (inf_le_right.trans D.B_E) (hU₂s.trans D.B'_E)
    refine Common.inf_centralizer_ne_bot_of_isPGroup hR2 (isPGroup_two_of_mul_self' D.E_sq)
      D.E_ne hRE (eq_bot_iff.2 fun x hx => ?_)
    obtain ⟨hxE, hxR⟩ := mem_inf.1 hx
    have hx1 : x ∈ E ⊓ centralizer ((P ⊓ B : Subgroup Q) : Set Q) :=
      ⟨hxE, centralizer_le (SetLike.coe_subset_coe.2 le_sup_left) hxR⟩
    have hsx : s⁻¹ * x * s ∈ E := by
      have := (mem_normalizer_iff.1 (inv_mem D.s_E) x).1 hxE
      simpa using this
    have hx2 : s⁻¹ * x * s ∈ E ⊓ centralizer ((P ⊓ Bᵍ[t] : Subgroup Q) : Set Q) := by
      refine ⟨hsx, mem_centralizer_iff.2 fun u hu => ?_⟩
      have hc := mem_centralizer_iff.1 hxR (s * u * s⁻¹) (mem_sup_right ⟨u, hu, rfl⟩)
      calc u * (s⁻¹ * x * s) = s⁻¹ * (s * u * s⁻¹ * x) * s := by group
        _ = s⁻¹ * (x * (s * u * s⁻¹)) * s := by rw [hc]
        _ = s⁻¹ * x * s * u := by group
    have hx3 : x ∈ F ⊓ F.map (MulAut.conj s).toMonoidHom :=
      ⟨hZ₁F hx1, mem_map_conj_iff.2 (hZ₂F hx2)⟩
    rw [D.F_inf] at hx3
    exact hx3
  have hB : (E ⊓ centralizer ((P ⊓ B : Subgroup Q) : Set Q)) ⊓
      F.map (MulAut.conj s).toMonoidHom ≤ E ⊓ centralizer (B : Set Q) := by
    intro x hx
    obtain ⟨hxZ₁, hxFs⟩ := mem_inf.1 hx
    refine mem_inf.2 ⟨hxZ₁.1, ?_⟩
    have hxU : (P ⊓ B) ≤ centralizer ({x} : Set Q) := fun u hu =>
      mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hxZ₁.2 u hu)
    have hxUs : (P ⊓ B).map (MulAut.conj s).toMonoidHom ≤ centralizer ({x} : Set Q) := by
      rintro _ ⟨u, hu, rfl⟩
      have hf : s⁻¹ * x * s ∈ F := mem_map_conj_iff.1 hxFs
      have hfc := mem_centralizer_iff.1 (D.F_le_Z₁ hf).2 u hu
      refine mem_centralizer_singleton_iff.2 ?_
      show s * u * s⁻¹ * x = x * (s * u * s⁻¹)
      calc s * u * s⁻¹ * x = s * (u * (s⁻¹ * x * s)) * s⁻¹ := by group
        _ = s * ((s⁻¹ * x * s) * u) * s⁻¹ := by rw [hfc]
        _ = x * (s * u * s⁻¹) := by group
    have hBx : B ≤ centralizer ({x} : Set Q) := D.B_gen.le.trans (sup_le hxU hxUs)
    exact mem_centralizer_iff.2 fun b hb => mem_centralizer_singleton_iff.1 (hBx hb)
  intro h
  apply hA
  rw [eq_bot_iff]
  exact hB.trans h.le

theorem V_inf : (E ⊓ centralizer (B : Set Q)) ⊓ (E ⊓ centralizer ((Bᵍ[t] : Subgroup Q) : Set Q)) =
    ⊥ := by
  refine eq_bot_iff.2 fun x hx => D.Z_bot.le ?_
  obtain ⟨⟨hxE, hx1⟩, -, hx2⟩ := (⟨mem_inf.1 (mem_inf.1 hx).1, mem_inf.1 (mem_inf.1 hx).2⟩ :
    (x ∈ E ∧ x ∈ centralizer (B : Set Q)) ∧
      (x ∈ E ∧ x ∈ centralizer ((Bᵍ[t] : Subgroup Q) : Set Q)))
  refine mem_inf.2 ⟨hxE, ?_⟩
  rw [centralizer_sup_aux]
  exact mem_inf.2 ⟨hx1, hx2⟩

theorem V₂_eq : E ⊓ centralizer ((Bᵍ[t] : Subgroup Q) : Set Q) =
    (E ⊓ centralizer (B : Set Q))ᵍ[t] := by
  have h := map_inf_centralizer_aux (MulAut.conj t⁻¹) E B
  rw [D.E_t] at h
  exact h.symm

theorem V₂_t :
    (E ⊓ centralizer ((Bᵍ[t] : Subgroup Q) : Set Q))ᵍ[t] = E ⊓ centralizer (B : Set Q) := by
  rw [D.V₂_eq, map_conj_inv_map_conj_inv D.t_sq]

theorem B'_N_V₁ : Bᵍ[t] ≤ normalizer ((E ⊓ centralizer (B : Set Q) : Subgroup Q) : Set Q) :=
  fun g hg => mem_normalizer_inf_D4 (D.B'_E hg) (mem_normalizer_centralizer_D4 (D.B'_N_B hg))

theorem B_N_V₂ : B ≤ normalizer ((E ⊓ centralizer ((Bᵍ[t] : Subgroup Q) : Set Q) : Subgroup Q) :
    Set Q) :=
  fun g hg => mem_normalizer_inf_D4 (D.B_E hg) (mem_normalizer_centralizer_D4 (D.B_N_B' hg))

theorem V₂_ne_bot : E ⊓ centralizer ((Bᵍ[t] : Subgroup Q) : Set Q) ≠ ⊥ := by
  intro h
  apply D.V₁_ne_bot
  rw [← D.V₂_t, h, Subgroup.map_bot]

theorem V_card : Nat.card (E ⊓ centralizer (B : Set Q) : Subgroup Q) = Nat.card K ^ 2 ∧
    Nat.card (E ⊓ centralizer ((Bᵍ[t] : Subgroup Q) : Set Q) : Subgroup Q) = Nat.card K ^ 2 ∧
    (E ⊓ centralizer (B : Set Q)) ⊔ (E ⊓ centralizer ((Bᵍ[t] : Subgroup Q) : Set Q)) = E := by
  obtain ⟨ψ⟩ := D.sl2
  obtain ⟨ψ'⟩ := D.sl2'
  have hV₁E : E ⊓ centralizer (B : Set Q) ≤ E := inf_le_left
  have hV₂E : E ⊓ centralizer ((Bᵍ[t] : Subgroup Q) : Set Q) ≤ E := inf_le_left
  have h1 : Nat.card K ^ 2 ≤ Nat.card (E ⊓ centralizer (B : Set Q) : Subgroup Q) := by
    refine Common.sl2_card_sq_le_of_not_le_centralizer ψ' D.card_K D.two_le
      (fun v hv => D.E_sq v (hV₁E hv)) D.B'_N_V₁ fun hle => D.V₁_ne_bot ?_
    refine eq_bot_iff.2 fun x hx => ?_
    have hx' : x ∈ (E ⊓ centralizer (B : Set Q)) ⊓
        (E ⊓ centralizer ((Bᵍ[t] : Subgroup Q) : Set Q)) := by
      refine ⟨hx, hx.1, ?_⟩
      exact mem_centralizer_iff.2 fun b hb =>
        (mem_centralizer_iff.1 (hle hb) x hx).symm
    rw [D.V_inf] at hx'
    exact hx'
  have h2 : Nat.card K ^ 2 ≤ Nat.card (E ⊓ centralizer ((Bᵍ[t] : Subgroup Q) : Set Q) :
      Subgroup Q) := by
    refine Common.sl2_card_sq_le_of_not_le_centralizer ψ D.card_K D.two_le
      (fun v hv => D.E_sq v (hV₂E hv)) D.B_N_V₂ fun hle => D.V₂_ne_bot ?_
    refine eq_bot_iff.2 fun x hx => ?_
    have hx' : x ∈ (E ⊓ centralizer (B : Set Q)) ⊓
        (E ⊓ centralizer ((Bᵍ[t] : Subgroup Q) : Set Q)) := by
      refine ⟨⟨hx.1, ?_⟩, hx⟩
      exact mem_centralizer_iff.2 fun b hb =>
        (mem_centralizer_iff.1 (hle hb) x hx).symm
    rw [D.V_inf] at hx'
    exact hx'
  have hcomm : ∀ a ∈ E ⊓ centralizer (B : Set Q), ∀ b ∈ E ⊓ centralizer ((Bᵍ[t] : Subgroup Q) :
      Set Q), a * b = b * a := fun a ha b hb => D.E_comm a ha.1 b hb.1
  have hcard := card_sup_eq_mul_of_commute hcomm D.V_inf
  have hle : Nat.card ↥((E ⊓ centralizer (B : Set Q)) ⊔
      (E ⊓ centralizer ((Bᵍ[t] : Subgroup Q) : Set Q))) ≤ Nat.card E :=
    Subgroup.card_le_of_le (sup_le hV₁E hV₂E)
  rw [hcard, D.card_E] at hle
  have h3 : Nat.card K ^ 2 * Nat.card K ^ 2 ≤
      Nat.card (E ⊓ centralizer (B : Set Q) : Subgroup Q) *
        Nat.card (E ⊓ centralizer ((Bᵍ[t] : Subgroup Q) : Set Q) : Subgroup Q) :=
    Nat.mul_le_mul h1 h2
  have e4 : Nat.card K ^ 4 = Nat.card K ^ 2 * Nat.card K ^ 2 := by ring
  rw [e4] at hle
  have hq : 0 < Nat.card K ^ 2 := by have := D.four_le_card; positivity
  have hc1 : Nat.card (E ⊓ centralizer (B : Set Q) : Subgroup Q) = Nat.card K ^ 2 := by
    by_contra hne
    have hlt : Nat.card K ^ 2 < Nat.card (E ⊓ centralizer (B : Set Q) : Subgroup Q) :=
      lt_of_le_of_ne h1 (Ne.symm hne)
    have := Nat.mul_lt_mul_of_lt_of_le hlt h2 (lt_of_lt_of_le hq h2)
    omega
  have hc2 : Nat.card (E ⊓ centralizer ((Bᵍ[t] : Subgroup Q) : Set Q) : Subgroup Q) =
      Nat.card K ^ 2 := by
    rw [hc1] at hle h3
    exact le_antisymm (Nat.le_of_mul_le_mul_left hle hq) h2
  refine ⟨hc1, hc2, ?_⟩
  refine Subgroup.eq_of_le_of_card_ge (sup_le hV₁E hV₂E) ?_
  rw [D.card_E, hcard, hc1, hc2, e4]

theorem core {R : Subgroup Q} (hR : R ≤ B ⊔ E) (hR2 : IsPGroup 2 R)
    (hB : B ≤ normalizer (R : Set Q)) : R ≤ E := by
  obtain ⟨ψ⟩ := D.sl2
  have hsimple := isSimpleGroup_sl2 ψ D.two_le D.card_K
  have hnot := not_isPGroup_sl2 ψ D.two_le D.card_K
  have hRN : R ≤ normalizer (E : Set Q) := hR.trans (sup_le D.B_E Subgroup.le_normalizer)
  have hRE2 : IsPGroup 2 (R ⊔ E : Subgroup Q) :=
    IsPGroup.to_sup_of_normal_right' hR2 (isPGroup_two_of_mul_self' D.E_sq) hRN
  intro r hr
  obtain ⟨a, ha, e, he, rfl⟩ := Common.exists_mul_of_le_normalizer' D.B_E r (hR hr)
  have haRE : a ∈ (R ⊔ E) ⊓ B := by
    refine mem_inf.2 ⟨?_, ha⟩
    have : a = (a * e) * e⁻¹ := by group
    rw [this]
    exact mul_mem (mem_sup_left hr) (inv_mem (mem_sup_right he))
  have hn : B ≤ normalizer ((((R ⊔ E) ⊓ B : Subgroup Q)) : Set Q) := fun g hg =>
    mem_normalizer_inf_D4 (mem_normalizer_sup_aux (hB hg) (D.B_E hg)) (Subgroup.le_normalizer hg)
  have hbot : (R ⊔ E) ⊓ B = ⊥ :=
    eq_bot_of_normal_two hsimple hnot inf_le_right hn (hRE2.to_le inf_le_left)
  rw [hbot, mem_bot] at haRE
  rw [haRE, one_mul]
  exact he

theorem center_Lam : (B ⊔ E) ⊓ centralizer ((B ⊔ E : Subgroup Q) : Set Q) = zOf E B :=
  center_sup_of D.E_comm D.cent_E

theorem center_Lam' : (Bᵍ[t] ⊔ E) ⊓ centralizer ((Bᵍ[t] ⊔ E : Subgroup Q) : Set Q) =
    zOf E (Bᵍ[t]) :=
  center_sup_of (A := Bᵍ[t]) (A' := B) D.E_comm (by rw [sup_comm (Bᵍ[t]) B]; exact D.cent_E)

theorem H₂_eq : (hOf t B E)ᵍ[t] = Bᵍ[t] ⊔ zOf E B := by
  rw [Subgroup.map_sup]
  congr 1
  exact D.V₂_t

theorem H_comm : ∀ a ∈ hOf t B E, ∀ b ∈ (hOf t B E)ᵍ[t], a * b = b * a := by
  intro a ha b hb
  rw [D.H₂_eq] at hb
  have hle : hOf t B E ≤ centralizer (((Bᵍ[t] ⊔ zOf E B : Subgroup Q)) : Set Q) := by
    rw [centralizer_sup_aux]
    refine le_inf (sup_le ?_ ?_) (sup_le ?_ ?_)
    · intro x hx
      exact mem_centralizer_iff.2 fun h hh => (D.B_comm x hx h hh).symm
    · exact inf_le_right
    · intro x hx
      exact mem_centralizer_iff.2 fun h hh => (mem_centralizer_iff.1 hh.2 x hx).symm
    · intro x hx
      exact mem_centralizer_iff.2 fun h hh => D.E_comm h hh.1 x hx.1
  exact (mem_centralizer_iff.1 (hle ha) b hb).symm

theorem E_eq_sup : E = zOf E B ⊔ zOf E (Bᵍ[t]) := D.V_card.2.2.symm

theorem prod_decomp :
    (B ⊔ Bᵍ[t]) ⊔ E = hOf t B E ⊔ (hOf t B E)ᵍ[t] ∧
    hOf t B E ⊓ (hOf t B E)ᵍ[t] = ⊥ ∧ ⁅hOf t B E, (hOf t B E)ᵍ[t]⁆ = ⊥ := by
  have hM := D.E_eq_sup
  refine ⟨?_, ?_, ?_⟩
  · rw [D.H₂_eq]
    calc (B ⊔ Bᵍ[t]) ⊔ E = (B ⊔ Bᵍ[t]) ⊔ (zOf E B ⊔ zOf E (Bᵍ[t])) := by rw [← hM]
      _ = (B ⊔ zOf E (Bᵍ[t])) ⊔ (Bᵍ[t] ⊔ zOf E B) := by
        rw [sup_comm (zOf E B)]
        exact sup_sup_sup_comm _ _ _ _
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    rw [D.H₂_eq] at hx2
    have hn1 : B ≤ normalizer ((zOf E (Bᵍ[t]) : Subgroup Q) : Set Q) := D.B_N_V₂
    have hn2 : Bᵍ[t] ≤ normalizer ((zOf E B : Subgroup Q) : Set Q) := D.B'_N_V₁
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right B _ hn1] at hx1
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right (Bᵍ[t]) _ hn2] at hx2
    obtain ⟨a, ha, z₂, hz₂, rfl⟩ := hx1
    obtain ⟨a', ha', z₁, hz₁, hxx⟩ := hx2
    have hxx' : a' * z₁ = a * z₂ := hxx
    have hm : a'⁻¹ * a = z₁ * z₂⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * z₂) * z₂⁻¹ := by group
        _ = a'⁻¹ * (a' * z₁) * z₂⁻¹ := by rw [hxx']
        _ = z₁ * z₂⁻¹ := by group
    have hmem : a'⁻¹ * a ∈ (B ⊔ Bᵍ[t]) ⊓ E := Subgroup.mem_inf.2
      ⟨mul_mem (inv_mem (mem_sup_right ha')) (mem_sup_left ha), by
        rw [hm]
        exact mul_mem (hz₁.1) (inv_mem hz₂.1)⟩
    rw [D.BB_inf, Subgroup.mem_bot] at hmem
    have haa : a = a' := by
      have := congrArg (a' * ·) hmem
      simpa using this
    have ha1 : a = 1 := by
      have : a ∈ B ⊓ Bᵍ[t] := Subgroup.mem_inf.2 ⟨ha, haa ▸ ha'⟩
      rw [D.B_inf, Subgroup.mem_bot] at this
      exact this
    have hz : a * z₂ ∈ zOf E B ⊓ zOf E (Bᵍ[t]) := by
      rw [ha1, one_mul]
      refine Subgroup.mem_inf.2 ⟨?_, hz₂⟩
      have : z₁ = z₂ := by
        rw [ha1, one_mul] at hxx'
        rw [haa] at ha1
        rw [ha1, one_mul] at hxx'
        exact hxx'
      exact this ▸ hz₁
    rw [D.V_inf, Subgroup.mem_bot] at hz
    show a * z₂ = 1
    exact hz
  · rw [commutator_eq_bot_iff_le_centralizer]
    intro a ha
    exact mem_centralizer_iff.2 fun b hb => (D.H_comm a ha b hb).symm

theorem not_le_centralizer_V₂ :
    ¬ B ≤ centralizer ((zOf E (Bᵍ[t]) : Subgroup Q) : Set Q) := by
  intro hle
  apply D.V₂_ne_bot
  refine eq_bot_iff.2 fun x hx => ?_
  have hx' : x ∈ (E ⊓ centralizer (B : Set Q)) ⊓
      (E ⊓ centralizer ((Bᵍ[t] : Subgroup Q) : Set Q)) :=
    ⟨⟨hx.1, mem_centralizer_iff.2 fun b hb => (mem_centralizer_iff.1 (hle hb) x hx).symm⟩, hx⟩
  rw [D.V_inf] at hx'
  exact hx'

theorem H_perfect : ⁅hOf t B E, hOf t B E⁆ = hOf t B E := by
  obtain ⟨ψ⟩ := D.sl2
  have hBB : ⁅B, B⁆ = B := commutator_eq_self_sl2 ψ D.two_le D.card_K
  set H := hOf t B E with hH
  have hBH : B ≤ H := le_sup_left
  refine le_antisymm (comm_le_self H) (sup_le ?_ ?_)
  · calc B = ⁅B, B⁆ := hBB.symm
      _ ≤ ⁅H, H⁆ := commutator_mono hBH hBH
  · have hn : B ≤ normalizer ((⁅H, H⁆ ⊓ zOf E (Bᵍ[t]) : Subgroup Q) : Set Q) := fun g hg =>
      mem_normalizer_inf_D4 (mem_normalizer_commutator_aux (Subgroup.le_normalizer (hBH hg))
        (Subgroup.le_normalizer (hBH hg))) (D.B_N_V₂ hg)
    obtain ⟨a, ha, hnc⟩ : ∃ a ∈ B, a ∉ centralizer ((zOf E (Bᵍ[t]) : Subgroup Q) : Set Q) := by
      by_contra hcon
      push Not at hcon
      exact D.not_le_centralizer_V₂ hcon
    obtain ⟨v, hv, hvne⟩ : ∃ v ∈ zOf E (Bᵍ[t]), ¬ v * a = a * v := by
      by_contra hcon
      push Not at hcon
      exact hnc (mem_centralizer_iff.2 hcon)
    have hc1 : a * v * a⁻¹ * v⁻¹ ∈ ⁅H, H⁆ ⊓ zOf E (Bᵍ[t]) := by
      refine mem_inf.2 ⟨?_, ?_⟩
      · rw [← commutatorElement_def]
        exact commutator_mem_commutator (hBH ha) (mem_sup_right hv)
      · exact mul_mem ((mem_normalizer_iff.1 (D.B_N_V₂ ha) v).1 hv) (inv_mem hv)
    have hne : ¬ (⁅H, H⁆ ⊓ zOf E (Bᵍ[t])) = ⊥ := by
      intro hbot
      rw [hbot, mem_bot] at hc1
      apply hvne
      have : a * v = v * a := by
        have h1 : a * v * a⁻¹ = v := mul_inv_eq_one.1 hc1 |> fun h => by
          simpa using congrArg (· * v) h
        calc a * v = a * v * a⁻¹ * a := by group
          _ = v * a := by rw [h1]
      exact this.symm
    have hcard : Nat.card (zOf E (Bᵍ[t])) = 2 ^ (2 * f) := by
      rw [D.V_card.2.1, D.card_K, ← pow_mul, mul_comm]
    rcases Common.sl2_eq_bot_or_eq_of_card_le (X := B) (A := zOf E (Bᵍ[t]))
      (V₀ := ⁅H, H⁆ ⊓ zOf E (Bᵍ[t])) (m := f) (a := 2 * f) ψ D.card_K D.two_le
      (fun x hx y hy => D.E_comm x hx.1 y hy.1) hcard le_rfl D.B_N_V₂ hn inf_le_right
      D.not_le_centralizer_V₂ with h | h
    · exact absurd h hne
    · exact inf_eq_right.1 h

theorem Lam_comm : ⁅B ⊔ E, B ⊔ E⁆ = hOf t B E := by
  have hM := D.E_eq_sup
  set H := hOf t B E with hH
  set Z₁ := zOf E B with hZ₁
  have hZ₁E : Z₁ ≤ E := inf_le_left
  have hZ₂E : zOf E (Bᵍ[t]) ≤ E := inf_le_left
  have hHK : H ≤ B ⊔ E := sup_le le_sup_left (hZ₂E.trans le_sup_right)
  refine le_antisymm ?_ (D.H_perfect.symm.le.trans (commutator_mono hHK hHK))
  have hKH : B ⊔ E = H ⊔ Z₁ := by
    apply le_antisymm
    · refine sup_le (le_sup_left.trans le_sup_left) ?_
      refine hM.le.trans (sup_le le_sup_right ?_)
      exact (le_sup_right : zOf E (Bᵍ[t]) ≤ H).trans le_sup_left
    · exact sup_le hHK (hZ₁E.trans le_sup_right)
  have hZ₁c : ∀ z ∈ Z₁, ∀ h ∈ H, z * h = h * z := by
    intro z hz h hh
    have hle : H ≤ centralizer (Z₁ : Set Q) := by
      refine sup_le ?_ ?_
      · intro a ha
        exact mem_centralizer_iff.2 fun z hz => (mem_centralizer_iff.1 hz.2 a ha).symm
      · intro a ha
        exact mem_centralizer_iff.2 fun z hz => D.E_comm z hz.1 a ha.1
    exact mem_centralizer_iff.1 (hle hh) z hz
  have hnorm : H ≤ normalizer (Z₁ : Set Q) :=
    le_normalizer_of_commute (A := H) (A' := Z₁) (fun h hh z hz => (hZ₁c z hz h hh).symm)
      le_rfl le_rfl
  rw [hKH, commutator_le]
  intro g₁ hg₁ g₂ hg₂
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right H Z₁ hnorm] at hg₁ hg₂
  obtain ⟨h, hh, z, hz, rfl⟩ := hg₁
  obtain ⟨h', hh', z', hz', rfl⟩ := hg₂
  have e1 : ⁅h * z, h' * z'⁆ = ⁅h, h'⁆ :=
    comm_mul_of_central (hZ₁c z hz h' hh') (D.E_comm z (hZ₁E hz) z' (hZ₁E hz'))
      (hZ₁c z' hz' h hh)
  show ⁅h * z, h' * z'⁆ ∈ H
  rw [e1]
  exact comm_le_self H (Subgroup.commutator_mem_commutator hh hh')

theorem pcore :
    zOf E (Bᵍ[t]) ≤ hOf t B E ∧ IsPGroup 2 (zOf E (Bᵍ[t])) ∧
    hOf t B E ≤ normalizer ((zOf E (Bᵍ[t]) : Subgroup Q) : Set Q) ∧
    ∀ R : Subgroup Q, R ≤ hOf t B E → hOf t B E ≤ normalizer (R : Set Q) → IsPGroup 2 R →
      R ≤ zOf E (Bᵍ[t]) := by
  refine ⟨le_sup_right, (isPGroup_two_of_mul_self' D.E_sq).to_le inf_le_left,
    sup_le D.B_N_V₂ Subgroup.le_normalizer, ?_⟩
  intro R hRH hHN hR2
  have hAN : B ≤ normalizer (R : Set Q) := (le_sup_left : B ≤ hOf t B E).trans hHN
  have hRK : R ≤ B ⊔ E := hRH.trans (sup_le le_sup_left (inf_le_left.trans le_sup_right))
  have hRM : R ≤ E := D.core hRK hR2 hAN
  intro r hr
  have hrH := hRH hr
  have hn : B ≤ normalizer ((zOf E (Bᵍ[t]) : Subgroup Q) : Set Q) := D.B_N_V₂
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right B _ hn] at hrH
  obtain ⟨a, ha, z, hz, rfl⟩ := hrH
  have haM : a ∈ E := by
    have := mul_mem (hRM hr) (inv_mem hz.1)
    simpa using this
  have h1 : a ∈ (B ⊔ Bᵍ[t]) ⊓ E := Subgroup.mem_inf.2 ⟨mem_sup_left ha, haM⟩
  rw [D.BB_inf, Subgroup.mem_bot] at h1
  show a * z ∈ zOf E (Bᵍ[t])
  rw [h1, one_mul]
  exact hz

theorem Z₁_eq : E ⊓ centralizer ((P ⊓ B : Subgroup Q) : Set Q) = F ⊔ zOf E B := by
  refine le_antisymm (fun x hx => ?_) (sup_le D.F_le_Z₁ ?_)
  · have hxE : x ∈ zOf E B ⊔ zOf E (Bᵍ[t]) := D.E_eq_sup ▸ hx.1
    have hn : zOf E B ≤ normalizer ((zOf E (Bᵍ[t]) : Subgroup Q) : Set Q) :=
      le_normalizer_of_commute (A := zOf E B) (A' := zOf E (Bᵍ[t]))
        (fun a ha b hb => D.E_comm a ha.1 b hb.1) le_rfl le_rfl
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Common.exists_mul_of_le_normalizer' hn x hxE
    have hV₁Z : zOf E B ≤ E ⊓ centralizer ((P ⊓ B : Subgroup Q) : Set Q) :=
      inf_le_inf_left _ (centralizer_le (SetLike.coe_subset_coe.2 inf_le_right))
    have hV₂Z : zOf E (Bᵍ[t]) ≤ E ⊓ centralizer ((P ⊓ Bᵍ[t] : Subgroup Q) : Set Q) :=
      inf_le_inf_left _ (centralizer_le (SetLike.coe_subset_coe.2 inf_le_right))
    have hv₂F : v₂ ∈ F := by
      rw [D.F_eq']
      refine mem_inf.2 ⟨?_, hV₂Z hv₂⟩
      have := mul_mem (inv_mem (hV₁Z hv₁)) hx
      rwa [inv_mul_cancel_left] at this
    exact mul_mem (mem_sup_right hv₁) (mem_sup_left hv₂F)
  · exact inf_le_inf_left _ (centralizer_le (SetLike.coe_subset_coe.2 inf_le_right))

theorem P_inf_eq : P ⊓ (B ⊔ E) = (P ⊓ B) ⊔ E := by
  refine le_antisymm (fun x hx => ?_) (sup_le (inf_le_inf_left _ le_sup_left)
    (le_inf D.P_E le_sup_right))
  obtain ⟨hxP, hxBE⟩ := mem_inf.1 hx
  obtain ⟨a, ha, e, he, rfl⟩ := Common.exists_mul_of_le_normalizer' D.B_E x hxBE
  have haP : a ∈ P := by
    have := mul_mem hxP (inv_mem (D.P_E he))
    rwa [mul_inv_cancel_right] at this
  exact mul_mem_sup (mem_inf.2 ⟨haP, ha⟩) he

theorem center_Pt : (P ⊓ (B ⊔ E)) ⊓ centralizer ((P ⊓ (B ⊔ E) : Subgroup Q) : Set Q) =
    F ⊔ zOf E B := by
  rw [← D.Z₁_eq]
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨hxP, hxC⟩ := mem_inf.1 hx
    have hxN : x ∈ (B ⊔ Bᵍ[t]) ⊔ E :=
      (sup_le (le_sup_left.trans le_sup_left) le_sup_right : B ⊔ E ≤ (B ⊔ Bᵍ[t]) ⊔ E)
        (mem_inf.1 hxP).2
    have hxE : x ∈ E := D.cent_E x hxN fun e he =>
      (mem_centralizer_iff.1 hxC e (mem_inf.2 ⟨D.P_E he, mem_sup_right he⟩)).symm
    refine mem_inf.2 ⟨hxE, mem_centralizer_iff.2 fun u hu => ?_⟩
    exact mem_centralizer_iff.1 hxC u (mem_inf.2 ⟨hu.1, mem_sup_left hu.2⟩)
  · obtain ⟨hxE, hxC⟩ := mem_inf.1 hx
    refine mem_inf.2 ⟨mem_inf.2 ⟨D.P_E hxE, mem_sup_right hxE⟩,
      mem_centralizer_iff.2 fun h hh => ?_⟩
    have hP : (P ⊓ (B ⊔ E) : Subgroup Q) ≤ centralizer ({x} : Set Q) := by
      rw [D.P_inf_eq]
      refine sup_le (fun y hy => ?_) fun y hy => ?_
      · exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hxC y hy)
      · exact mem_centralizer_singleton_iff.2 (D.E_comm x hxE y hy).symm
    exact mem_centralizer_singleton_iff.1 (hP hh)

end Hat73

end Hat

end CFSG.LocalAnalysis.EvenBN.G2.ProductN2Aux

namespace CFSG.LocalAnalysis.EvenBN.G2.ProductN2Aux

open CFSG.LocalAnalysis.EvenBN.TrialityD4 (mem_normalizer_inf_D4 mem_normalizer_centralizer_D4)

section GFactor

variable {G : Type} [Group G] [Finite G] {X N Λ : Subgroup G} {t : G} {K : Type} [Field K]

theorem le_normalizer_of_isFactor (hΛ : IsFactor X N Λ t K) : N ≤ normalizer (Λ : Set G) := by
  rw [← hΛ.sup]
  refine sup_le Subgroup.le_normalizer fun y hy => mem_normalizer_fintype fun x hx => ?_
  have hc : y * x * y⁻¹ * x⁻¹ ∈ X := by
    have h1 : ⁅x, y⁆ ∈ X := hΛ.comm (commutator_mem_commutator hx hy)
    have h2 := inv_mem h1
    rwa [commutatorElement_inv] at h2
  have e : y * x * y⁻¹ = (y * x * y⁻¹ * x⁻¹) * x := by group
  rw [SetLike.mem_coe, e]
  exact mul_mem (hΛ.X_le hc) hx

theorem le_normalizer_map_of_isFactor (hΛ : IsFactor X N Λ t K) :
    N ≤ normalizer ((Λᵍ[t] : Subgroup G) : Set G) := by
  rw [← hΛ.sup]
  refine sup_le (fun x hx => mem_normalizer_fintype fun y hy => ?_) Subgroup.le_normalizer
  have hc : x * y * x⁻¹ * y⁻¹ ∈ X := hΛ.comm (commutator_mem_commutator hx hy)
  have e : x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y := by group
  rw [SetLike.mem_coe, e]
  exact mul_mem (hΛ.inf.ge.trans inf_le_right hc) hy

end GFactor

section BarConj

open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN2Aux

variable {G : Type} [Group G] [Finite G] {W : Subgroup G}

theorem bar_map_conjT {X : Subgroup G} {t : G} (ht : t ∈ normalizer (W : Set G))
    (hX : X ≤ normalizer (W : Set G)) :
    bar W (Xᵍ[t]) = (bar W X)ᵍ[proj W ⟨t, ht⟩] := by
  have h := bar_map_conj (inv_mem ht) hX
  have e : proj W ⟨t⁻¹, inv_mem ht⟩ = (proj W ⟨t, ht⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  rw [e] at h
  exact h

theorem lift_map_conjT {t : G} (ht : t ∈ normalizer (W : Set G)) (Y : Subgroup (Bar W)) :
    (lift Y : Subgroup G)ᵍ[t] = lift (Yᵍ[proj W ⟨t, ht⟩]) := by
  have hN : (lift Y : Subgroup G) ≤ normalizer (W : Set G) := lift_le_normalizer Y
  have h1 : bar W ((lift Y : Subgroup G)ᵍ[t]) = Yᵍ[proj W ⟨t, ht⟩] := by
    rw [bar_map_conjT ht hN, bar_lift]
  have hW1 : W ≤ (lift Y : Subgroup G)ᵍ[t] := by
    have := Subgroup.map_mono (f := (MulAut.conj t⁻¹).toMonoidHom) (le_lift (A := W) Y)
    rwa [conjT_eq_self_of_mem_normalizer ht] at this
  have hN1 : (lift Y : Subgroup G)ᵍ[t] ≤ normalizer (W : Set G) :=
    map_conj_le_normalizer (inv_mem ht) hN
  rw [← h1, lift_bar hW1 hN1]

end BarConj

section Ctx

variable {G : Type} [Group G]

structure Ctx (K : Type) [Field K] (f : ℕ) (t wb : G) (W Y M N P F₅ A Λ : Subgroup G) :
    Prop where
  t_sq : t * t = 1
  Y_W : Y ≤ W
  W_M : W ≤ M
  W_F : W ≤ F₅
  F_M : F₅ ≤ M
  M_P : M ≤ P
  P_N : P ≤ N
  P_two : IsPGroup 2 P
  N_W : N ≤ normalizer (W : Set G)
  N_M : N ≤ normalizer (M : Set G)
  N_Y : N ≤ normalizer (Y : Set G)
  t_W : t ∈ normalizer (W : Set G)
  t_M : t ∈ normalizer (M : Set G)
  t_Y : t ∈ normalizer (Y : Set G)
  P_t : Pᵍ[t] = P
  A_N : A ≤ N
  A_inf : A ⊓ M = ⊥
  N_eq : N = A ⊔ M
  A_t : Aᵍ[t] = A
  wb_A : wb ∈ A
  fac : IsFactor M N Λ t K
  cen_Y : centerMod Y N = W
  cen_W : centerMod W N = W
  cen_P : centerMod W P = F₅
  cent_M : N ⊓ centralizerMod W M = M
  N_gen : N = P ⊔ P.map (MulAut.conj wb).toMonoidHom
  M_F : M = F₅ ⊔ F₅.map (MulAut.conj wb).toMonoidHom
  F_inf : F₅ ⊓ F₅.map (MulAut.conj wb).toMonoidHom = W
  M_sq : ∀ x ∈ M, x * x ∈ Y
  M_comm : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ Y
  F_P : ∀ x ∈ F₅, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Y
  card_K : Nat.card K = 2 ^ f
  two_le : 2 ≤ f
  card_M : Nat.card M = Nat.card K ^ 10
  card_W : Nat.card W = Nat.card K ^ 6
  card_P : Nat.card P = Nat.card K ^ 12

end Ctx

namespace Ctx

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] {f : ℕ} {t wb : G}
  {W Y M N P F₅ A Λ : Subgroup G} (C : Ctx K f t wb W Y M N P F₅ A Λ)
include C

theorem M_Λ : M ≤ Λ := C.fac.X_le

theorem Λ_N : Λ ≤ N := C.fac.le

theorem M_Λ' : M ≤ Λᵍ[t] := C.fac.inf.ge.trans inf_le_right

theorem Λ'_N : Λᵍ[t] ≤ N := by
  rw [← C.fac.sup]
  exact le_sup_right

theorem A_NM : A ≤ normalizer (M : Set G) := C.A_N.trans C.N_M

theorem Λ_eq : Λ = (Λ ⊓ A) ⊔ M := by
  refine le_antisymm (fun x hx => ?_) (sup_le inf_le_left C.M_Λ)
  have hxN : x ∈ A ⊔ M := C.N_eq ▸ C.Λ_N hx
  obtain ⟨a, ha, m, hm, rfl⟩ := Common.exists_mul_of_le_normalizer' C.A_NM x hxN
  have haΛ : a ∈ Λ := by
    have := mul_mem hx (inv_mem (C.M_Λ hm))
    rwa [mul_inv_cancel_right] at this
  exact mul_mem_sup (mem_inf.2 ⟨haΛ, ha⟩) hm

theorem Λ'_eq : Λᵍ[t] = (Λᵍ[t] ⊓ A) ⊔ M := by
  refine le_antisymm (fun x hx => ?_) (sup_le inf_le_left C.M_Λ')
  have hxN : x ∈ A ⊔ M := C.N_eq ▸ C.Λ'_N hx
  obtain ⟨a, ha, m, hm, rfl⟩ := Common.exists_mul_of_le_normalizer' C.A_NM x hxN
  have haΛ : a ∈ Λᵍ[t] := by
    have := mul_mem hx (inv_mem (C.M_Λ' hm))
    rwa [mul_inv_cancel_right] at this
  exact mul_mem_sup (mem_inf.2 ⟨haΛ, ha⟩) hm

theorem A₂_t : (Λ ⊓ A)ᵍ[t] = Λᵍ[t] ⊓ A := by
  rw [Subgroup.map_inf _ _ _ (fun a b hab => (MulAut.conj t⁻¹).injective hab), C.A_t]

theorem N_eq' : N = ((Λ ⊓ A) ⊔ (Λᵍ[t] ⊓ A)) ⊔ M := by
  refine le_antisymm ?_ (sup_le (sup_le (inf_le_left.trans C.Λ_N) (inf_le_left.trans C.Λ'_N))
    (C.fac.X_le.trans C.Λ_N))
  rw [← C.fac.sup]
  exact sup_le (C.Λ_eq.le.trans (sup_le_sup_right le_sup_left M))
    (C.Λ'_eq.le.trans (sup_le_sup_right le_sup_right M))

theorem A₂_comm : ∀ x ∈ Λ ⊓ A, ∀ y ∈ Λᵍ[t] ⊓ A, x * y = y * x := by
  intro x hx y hy
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ M := C.fac.comm (commutator_mem_commutator hx.1 hy.1)
  have h2 : x * y * x⁻¹ * y⁻¹ ∈ A :=
    mul_mem (mul_mem (mul_mem hx.2 hy.2) (inv_mem hx.2)) (inv_mem hy.2)
  have h3 : x * y * x⁻¹ * y⁻¹ ∈ A ⊓ M := ⟨h2, h1⟩
  rw [C.A_inf, mem_bot] at h3
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [h3, one_mul]

theorem AA_inf : ((Λ ⊓ A) ⊔ (Λᵍ[t] ⊓ A)) ⊓ M = ⊥ := by
  have hle : (Λ ⊓ A) ⊔ (Λᵍ[t] ⊓ A) ≤ A := sup_le inf_le_right inf_le_right
  exact eq_bot_iff.2 fun x hx => C.A_inf.le ⟨hle hx.1, hx.2⟩

theorem sl2 : Nonempty (↥(Λ ⊓ A) ≃* SL(2, K)) := by
  obtain ⟨φ, hφs, hφk⟩ := C.fac.quot
  let ψ : ↥(Λ ⊓ A) →* SL(2, K) := φ.comp (Subgroup.inclusion inf_le_left)
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : Subgroup.inclusion inf_le_left x ∈ φ.ker := hx
    rw [hφk, mem_subgroupOf] at h1
    have h2 : (x : G) ∈ A ⊓ M := ⟨x.2.2, h1⟩
    rw [C.A_inf, mem_bot] at h2
    exact Subtype.ext h2
  have hsurj : Function.Surjective ψ := by
    intro g
    obtain ⟨l, hl⟩ := hφs g
    have hl' : (l : G) ∈ (Λ ⊓ A) ⊔ M := C.Λ_eq ▸ l.2
    have hn : Λ ⊓ A ≤ normalizer (M : Set G) := inf_le_right.trans C.A_NM
    obtain ⟨a, ha, m, hm, hlam⟩ := Common.exists_mul_of_le_normalizer' hn l hl'
    refine ⟨⟨a, ha⟩, ?_⟩
    have hm' : (⟨m, C.M_Λ hm⟩ : ↥Λ) ∈ φ.ker := by
      rw [hφk, mem_subgroupOf]
      exact hm
    have e : l = Subgroup.inclusion inf_le_left ⟨a, ha⟩ * ⟨m, C.M_Λ hm⟩ := Subtype.ext hlam
    rw [← hl, e, map_mul, MonoidHom.mem_ker.1 hm', mul_one]
    rfl
  exact ⟨MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩⟩

end Ctx

section HatOf

open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (commutator_mem_iff_proj)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN2Aux (isQuotientIso_bar_of_inf
  mem_bar_iff_exists bar_sup bar_inf bar_commutator bar_map_conj lift_sup lift_inf
  bar_centerMod centerMod_eq_lift relIndex_eq_card_bar bar_self lift_bar_eq_sup eq_of_bar_eq)

variable {G : Type} [Group G] [Finite G]

theorem nonempty_mulEquiv_bar {W X : Subgroup G} (hXN : X ≤ normalizer (W : Set G))
    (hinf : X ⊓ W = ⊥) : Nonempty (↥X ≃* ↥(bar W X)) := by
  obtain ⟨φ, hφs, hφk⟩ := isQuotientIso_bar_of_inf hXN hinf
  refine ⟨MulEquiv.ofBijective φ ⟨?_, hφs⟩⟩
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : x ∈ φ.ker := hx
  rw [hφk] at h1
  have h2 := mem_subgroupOf.1 h1
  exact Subtype.ext (mem_bot.1 h2)

theorem proj_comm_of_commutator_mem {W X : Subgroup G} (hXN : X ≤ normalizer (W : Set G))
    (h : ∀ a ∈ X, ∀ b ∈ X, a * b * a⁻¹ * b⁻¹ ∈ W) :
    ∀ x ∈ bar W X, ∀ y ∈ bar W X, x * y = y * x := by
  intro x hx y hy
  obtain ⟨a, ha, rfl⟩ := mem_bar_iff_exists.1 hx
  obtain ⟨b, hb, rfl⟩ := mem_bar_iff_exists.1 hy
  exact ((commutator_mem_iff_proj (N := W) a.2 b.2).2 (h a ha b hb)).symm

end HatOf

namespace Ctx

section HatCtx

open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (commutator_mem_iff_proj)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN2Aux (isQuotientIso_bar_of_inf
  mem_bar_iff_exists bar_sup bar_inf bar_commutator bar_map_conj lift_sup lift_inf
  bar_centerMod centerMod_eq_lift relIndex_eq_card_bar bar_self lift_bar_eq_sup eq_of_bar_eq
  conjT_eq_self_of_mem_normalizer map_conj_le_normalizer proj_mem_normalizer_bar)

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] {f : ℕ} {t wb : G}
  {W Y M N P F₅ A Λ : Subgroup G} (C : Ctx K f t wb W Y M N P F₅ A Λ)
include C

theorem M_W' : M ≤ normalizer (W : Set G) := C.M_P.trans (C.P_N.trans C.N_W)

theorem P_W' : P ≤ normalizer (W : Set G) := C.P_N.trans C.N_W

theorem F_W' : F₅ ≤ normalizer (W : Set G) := C.F_M.trans C.M_W'

theorem A₂_W' : Λ ⊓ A ≤ normalizer (W : Set G) := inf_le_right.trans (C.A_N.trans C.N_W)

theorem A₂'_W' : Λᵍ[t] ⊓ A ≤ normalizer (W : Set G) :=
  inf_le_right.trans (C.A_N.trans C.N_W)

theorem wb_W : wb ∈ normalizer (W : Set G) := C.N_W (C.A_N C.wb_A)

theorem bar_Λ : bar W Λ = bar W (Λ ⊓ A) ⊔ bar W M := by
  conv_lhs => rw [C.Λ_eq]
  exact bar_sup (inf_le_left.trans (C.Λ_N.trans C.N_W)) C.M_W'

theorem bar_Λ' : bar W (Λᵍ[t]) = bar W (Λᵍ[t] ⊓ A) ⊔ bar W M := by
  conv_lhs => rw [C.Λ'_eq]
  exact bar_sup C.A₂'_W' C.M_W'

theorem bar_N : bar W N = (bar W (Λ ⊓ A) ⊔ bar W (Λᵍ[t] ⊓ A)) ⊔ bar W M := by
  conv_lhs => rw [C.N_eq']
  rw [bar_sup (sup_le C.A₂_W' C.A₂'_W') C.M_W', bar_sup C.A₂_W' C.A₂'_W']

theorem bar_A₂_t : (bar W (Λ ⊓ A))ᵍ[proj W ⟨t, C.t_W⟩] = bar W (Λᵍ[t] ⊓ A) := by
  rw [← bar_map_conjT C.t_W C.A₂_W', C.A₂_t]

theorem E_comm' : ∀ x ∈ bar W M, ∀ y ∈ bar W M, x * y = y * x :=
  proj_comm_of_commutator_mem C.M_W' fun a ha b hb => C.Y_W (C.M_comm a ha b hb)

theorem E_sq' : ∀ x ∈ bar W M, x * x = 1 := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := mem_bar_iff_exists.1 hx
  rw [← map_mul, proj_eq_one_iff]
  exact C.Y_W (C.M_sq a ha)

theorem E_t' : (bar W M)ᵍ[proj W ⟨t, C.t_W⟩] = bar W M := by
  rw [← bar_map_conjT C.t_W C.M_W', conjT_eq_self_of_mem_normalizer C.t_M]

theorem B_E' : bar W (Λ ⊓ A) ≤ normalizer (bar W M : Set (Bar W)) :=
  bar_le_normalizer_bar C.W_M (inf_le_right.trans C.A_NM)

theorem B_comm' : ∀ a ∈ bar W (Λ ⊓ A), ∀ b ∈ (bar W (Λ ⊓ A))ᵍ[proj W ⟨t, C.t_W⟩],
    a * b = b * a := by
  intro a ha b hb
  rw [C.bar_A₂_t] at hb
  obtain ⟨x, hx, rfl⟩ := mem_bar_iff_exists.1 ha
  obtain ⟨y, hy, rfl⟩ := mem_bar_iff_exists.1 hb
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (C.A₂_comm _ hx _ hy)

theorem BB_inf' : (bar W (Λ ⊓ A) ⊔ (bar W (Λ ⊓ A))ᵍ[proj W ⟨t, C.t_W⟩]) ⊓ bar W M = ⊥ := by
  rw [C.bar_A₂_t, ← bar_sup C.A₂_W' C.A₂'_W', inf_comm, ← bar_inf C.W_M]
  have h : M ⊓ ((Λ ⊓ A) ⊔ (Λᵍ[t] ⊓ A)) = ⊥ := by rw [inf_comm]; exact C.AA_inf
  rw [h]
  exact eq_bot_iff.2 ((bar_mono bot_le).trans (bar_self W).le)

theorem B_inf' : bar W (Λ ⊓ A) ⊓ (bar W (Λ ⊓ A))ᵍ[proj W ⟨t, C.t_W⟩] = ⊥ := by
  rw [C.bar_A₂_t]
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
  obtain ⟨a, ha, rfl⟩ := mem_bar_iff_exists.1 hx1
  obtain ⟨b, hb, hab⟩ := mem_bar_iff_exists.1 hx2
  have hw : (b : G)⁻¹ * a ∈ W := proj_eq_proj_iff.1 hab
  have hbΛ : (b : G) ∈ Λ := by
    have : (b : G) = a * ((a : G)⁻¹ * b) := by group
    rw [this]
    refine mul_mem ha.1 (C.M_Λ (C.W_M ?_))
    have := inv_mem hw
    rwa [mul_inv_rev, inv_inv] at this
  have hbM : (b : G) ∈ Λ ⊓ Λᵍ[t] := ⟨hbΛ, hb.1⟩
  rw [C.fac.inf] at hbM
  have hb1 : (b : G) ∈ A ⊓ M := ⟨hb.2, hbM⟩
  rw [C.A_inf, mem_bot] at hb1
  have : b = 1 := Subtype.ext hb1
  rw [← hab, this, map_one]
  exact one_mem _

theorem sl2_bar : Nonempty (↥(bar W (Λ ⊓ A)) ≃* SL(2, K)) := by
  obtain ⟨e⟩ := C.sl2
  have hinf : (Λ ⊓ A) ⊓ W = ⊥ := by
    refine eq_bot_iff.2 fun x hx => C.A_inf.le ⟨hx.1.2, C.W_M hx.2⟩
  obtain ⟨e'⟩ := nonempty_mulEquiv_bar C.A₂_W' hinf
  exact ⟨e'.symm.trans e⟩

theorem s_E' : proj W ⟨wb, C.wb_W⟩ ∈ normalizer (bar W M : Set (Bar W)) := by
  have h := proj_mem_normalizer_bar (W := W) (Y := M) C.W_M C.wb_W (C.A_NM C.wb_A)
  exact h

theorem wb_N_A₂ : wb ∈ normalizer (((Λ ⊓ A) ⊔ W : Subgroup G) : Set G) :=
  mem_normalizer_sup_aux (mem_normalizer_inf_D4
    (le_normalizer_of_isFactor C.fac (C.A_N C.wb_A)) (Subgroup.le_normalizer C.wb_A)) C.wb_W

theorem wb_N_A₂' : wb ∈ normalizer (((Λᵍ[t] ⊓ A) ⊔ W : Subgroup G) : Set G) :=
  mem_normalizer_sup_aux (mem_normalizer_inf_D4
    (le_normalizer_map_of_isFactor C.fac (C.A_N C.wb_A)) (Subgroup.le_normalizer C.wb_A)) C.wb_W

theorem bar_eq_bar_sup (X : Subgroup G) (hX : X ≤ normalizer (W : Set G)) :
    bar W X = bar W (X ⊔ W) := by
  rw [bar_sup hX Subgroup.le_normalizer, bar_self, sup_bot_eq]

theorem s_B' : proj W ⟨wb, C.wb_W⟩ ∈ normalizer (bar W (Λ ⊓ A) : Set (Bar W)) := by
  rw [C.bar_eq_bar_sup _ C.A₂_W']
  exact proj_mem_normalizer_bar le_sup_right C.wb_W C.wb_N_A₂

theorem s_B'' : proj W ⟨wb, C.wb_W⟩ ∈ normalizer (bar W (Λᵍ[t] ⊓ A) : Set (Bar W)) := by
  rw [C.bar_eq_bar_sup _ C.A₂'_W']
  exact proj_mem_normalizer_bar le_sup_right C.wb_W C.wb_N_A₂'

theorem W_P : W ≤ P := C.W_M.trans C.M_P

theorem card_bar_P : Nat.card (bar W P) = Nat.card K ^ 6 := by
  have h1 := card_bar_mul C.W_P C.P_W'
  rw [C.card_W, C.card_P] at h1
  have hq0 : 0 < Nat.card K := by rw [C.card_K]; positivity
  have hq : 0 < Nat.card K ^ 6 := pow_pos hq0 6
  exact Nat.eq_of_mul_eq_mul_right hq (by rw [h1]; ring)

theorem card_bar_M : Nat.card (bar W M) = Nat.card K ^ 4 := by
  have h1 := card_bar_mul C.W_M C.M_W'
  rw [C.card_W, C.card_M] at h1
  have hq0 : 0 < Nat.card K := by rw [C.card_K]; positivity
  have hq : 0 < Nat.card K ^ 6 := pow_pos hq0 6
  exact Nat.eq_of_mul_eq_mul_right hq (by rw [h1]; ring)

theorem P_t' : (bar W P)ᵍ[proj W ⟨t, C.t_W⟩] = bar W P := by
  rw [← bar_map_conjT C.t_W C.P_W', C.P_t]

theorem bar_N_gen : bar W N = bar W P ⊔ (bar W P).map
    (MulAut.conj (proj W ⟨wb, C.wb_W⟩)).toMonoidHom := by
  conv_lhs => rw [C.N_gen]
  rw [bar_sup C.P_W' (map_conj_le_normalizer C.wb_W C.P_W'), bar_map_conj C.wb_W C.P_W']

theorem F_eq'' : bar W F₅ = bar W P ⊓ centralizer (bar W P : Set (Bar W)) := by
  rw [← bar_centerMod, C.cen_P]

theorem E_F' : bar W M = bar W F₅ ⊔ (bar W F₅).map
    (MulAut.conj (proj W ⟨wb, C.wb_W⟩)).toMonoidHom := by
  conv_lhs => rw [C.M_F]
  rw [bar_sup C.F_W' (map_conj_le_normalizer C.wb_W C.F_W'), bar_map_conj C.wb_W C.F_W']

theorem F_inf' : bar W F₅ ⊓ (bar W F₅).map
    (MulAut.conj (proj W ⟨wb, C.wb_W⟩)).toMonoidHom = ⊥ := by
  rw [← bar_map_conj C.wb_W C.F_W', ← bar_inf C.W_F, C.F_inf, bar_self]

theorem Z_bot' : bar W M ⊓ centralizer
    ((bar W (Λ ⊓ A) ⊔ (bar W (Λ ⊓ A))ᵍ[proj W ⟨t, C.t_W⟩] : Subgroup (Bar W)) : Set (Bar W)) =
      ⊥ := by
  have hZ : bar W N ⊓ centralizer ((bar W N : Subgroup (Bar W)) : Set (Bar W)) = ⊥ := by
    have h := bar_centerMod (W := W) N
    rw [C.cen_W, bar_self] at h
    exact h.symm
  refine eq_bot_iff.2 fun x hx => hZ.le ⟨bar_mono (C.M_P.trans C.P_N) hx.1, ?_⟩
  have hBN : bar W (Λ ⊓ A) ⊔ (bar W (Λ ⊓ A))ᵍ[proj W ⟨t, C.t_W⟩] ≤
      centralizer ({x} : Set (Bar W)) := fun y hy =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hx.2 y hy)
  have hE : bar W M ≤ centralizer ({x} : Set (Bar W)) := fun y hy =>
    mem_centralizer_singleton_iff.2 (C.E_comm' y hy x hx.1)
  have hN : bar W N ≤ centralizer ({x} : Set (Bar W)) := by
    rw [C.bar_N, ← C.bar_A₂_t]
    exact sup_le hBN hE
  exact mem_centralizer_iff.2 fun y hy => mem_centralizer_singleton_iff.1 (hN hy)

theorem cent_E' : ∀ x ∈ (bar W (Λ ⊓ A) ⊔ (bar W (Λ ⊓ A))ᵍ[proj W ⟨t, C.t_W⟩]) ⊔ bar W M,
    (∀ e ∈ bar W M, x * e = e * x) → x ∈ bar W M := by
  intro x hx hc
  have h := congrArg (bar W) C.cent_M
  rw [bar_inf (C.W_M.trans (C.M_P.trans C.P_N))] at h
  have hb : bar W (centralizerMod W M) = centralizer (bar W M : Set (Bar W)) := by
    unfold centralizerMod
    rw [bar_lift]
  rw [hb] at h
  rw [← h]
  refine ⟨?_, mem_centralizer_iff.2 fun e he => (hc e he).symm⟩
  rw [C.bar_N, ← C.bar_A₂_t]
  exact hx

theorem hat73 : Hat73 K f (proj W ⟨t, C.t_W⟩) (proj W ⟨wb, C.wb_W⟩) (bar W M)
    (bar W (Λ ⊓ A)) (bar W P) (bar W F₅) where
  t_sq := by
    rw [← map_mul]
    have : (⟨t, C.t_W⟩ * ⟨t, C.t_W⟩ : normalizer (W : Set G)) = 1 := Subtype.ext C.t_sq
    rw [this, map_one]
  E_comm := C.E_comm'
  E_sq := C.E_sq'
  E_t := C.E_t'
  B_E := C.B_E'
  B_comm := C.B_comm'
  BB_inf := C.BB_inf'
  B_inf := C.B_inf'
  sl2 := C.sl2_bar
  card_K := C.card_K
  two_le := C.two_le
  s_E := C.s_E'
  s_B := C.s_B'
  s_B' := by rw [C.bar_A₂_t]; exact C.s_B''
  P_E := bar_mono C.M_P
  P_two := isPGroup_bar C.P_two
  P_le := by rw [C.bar_A₂_t, ← C.bar_N]; exact bar_mono C.P_N
  P_t := C.P_t'
  P_card := by rw [C.card_bar_P, C.card_bar_M]; ring
  N_gen := by rw [C.bar_A₂_t, ← C.bar_N]; exact C.bar_N_gen
  F_eq := C.F_eq''
  E_F := C.E_F'
  F_inf := C.F_inf'
  Z_bot := C.Z_bot'
  card_E := C.card_bar_M
  cent_E := C.cent_E'

end HatCtx

end Ctx

section DerivedLift

open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN2Aux (bar_sup bar_commutator bar_self
  comm_le_self)

variable {G : Type} [Group G] [Finite G] {W : Subgroup G}

theorem derivedMod_lift (Y : Subgroup (Bar W)) : derivedMod W (lift Y : Subgroup G) =
    lift ⁅Y, Y⁆ := by
  have hN : (lift Y : Subgroup G) ≤ normalizer (W : Set G) := lift_le_normalizer Y
  have hc : ⁅(lift Y : Subgroup G), (lift Y : Subgroup G)⁆ ≤ normalizer (W : Set G) :=
    (comm_le_self _).trans hN
  have hWd : W ≤ derivedMod W (lift Y : Subgroup G) := le_sup_right
  have hdN : derivedMod W (lift Y : Subgroup G) ≤ normalizer (W : Set G) :=
    sup_le hc Subgroup.le_normalizer
  have h : bar W (derivedMod W (lift Y : Subgroup G)) = ⁅Y, Y⁆ := by
    unfold derivedMod
    rw [bar_sup hc Subgroup.le_normalizer, bar_commutator hN hN, bar_lift, bar_self, sup_bot_eq]
  rw [← h, lift_bar hWd hdN]

end DerivedLift

section ThreeSubgroup

open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN2Aux (comm_le_self
  le_normalizer_of_commute comm_mul_of_central)

variable {Q : Type*} [Group Q]

theorem three_subgroup_step {Λ Z W N Lt : Subgroup Q} (hΛN : Λ ≤ N)
    (hW : ∀ w ∈ W, ∀ n ∈ N, w * n = n * w) (hZW : ⁅Λ, Z⁆ ≤ W) (hΛ : Λ = ⁅Λ, Λ⁆ ⊔ Z)
    (hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hLt : ⁅⁅Λ, Λ⁆, Lt⁆ ≤ W) :
    ⁅Λ, Z⁆ = ⊥ ∧ ⁅⁅Λ, Λ⁆, ⁅Λ, Λ⁆⁆ = ⁅Λ, Λ⁆ ∧ ⁅⁅Λ, Λ⁆, Lt⁆ = ⊥ := by
  have hWN : ∀ L : Subgroup Q, L ≤ N → ⁅W, L⁆ = ⊥ := fun L hL => by
    rw [commutator_eq_bot_iff_le_centralizer]
    exact fun w hw => mem_centralizer_iff.2 fun l hl => (hW w hw l (hL hl)).symm
  have hD : ⁅Λ, Λ⁆ ≤ Λ := comm_le_self Λ
  have h1 : ⁅⁅Λ, Λ⁆, Z⁆ = ⊥ := by
    refine commutator_commutator_eq_bot_of_rotate (H₁ := Λ) (H₂ := Λ) (H₃ := Z) ?_ ?_
    · exact eq_bot_iff.2 ((commutator_mono hZW le_rfl).trans (hWN Λ hΛN).le)
    · rw [commutator_comm Z Λ]
      exact eq_bot_iff.2 ((commutator_mono hZW le_rfl).trans (hWN Λ hΛN).le)
  have h2 : ⁅Λ, Z⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    rw [hΛ]
    refine sup_le ?_ ?_
    · exact commutator_eq_bot_iff_le_centralizer.1 h1
    · exact fun a ha => mem_centralizer_iff.2 fun b hb => hZ a ha b hb |>.symm
  have hZc : ∀ z ∈ Z, ∀ g ∈ Λ, z * g = g * z := fun z hz g hg => by
    have := (commutator_eq_bot_iff_le_centralizer.1 h2) hg
    exact mem_centralizer_iff.1 this z hz
  have h3 : ⁅⁅Λ, Λ⁆, ⁅Λ, Λ⁆⁆ = ⁅Λ, Λ⁆ := by
    refine le_antisymm (commutator_mono hD hD) ?_
    have hn : ⁅Λ, Λ⁆ ≤ normalizer (Z : Set Q) :=
      le_normalizer_of_commute (A := ⁅Λ, Λ⁆) (A' := Z) (fun a ha b hb => (hZc b hb a (hD ha)).symm)
        le_rfl le_rfl
    rw [commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have hg₁' : g₁ ∈ ⁅Λ, Λ⁆ ⊔ Z := hΛ.le hg₁
    have hg₂' : g₂ ∈ ⁅Λ, Λ⁆ ⊔ Z := hΛ.le hg₂
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hn] at hg₁' hg₂'
    obtain ⟨d₁, hd₁, z₁, hz₁, rfl⟩ := hg₁'
    obtain ⟨d₂, hd₂, z₂, hz₂, rfl⟩ := hg₂'
    have e : ⁅d₁ * z₁, d₂ * z₂⁆ = ⁅d₁, d₂⁆ :=
      comm_mul_of_central (hZc z₁ hz₁ d₂ (hD hd₂)) (hZ z₁ hz₁ z₂ hz₂) (hZc z₂ hz₂ d₁ (hD hd₁))
    rw [e]
    exact commutator_mem_commutator hd₁ hd₂
  refine ⟨h2, h3, ?_⟩
  have h4 : ⁅⁅⁅Λ, Λ⁆, ⁅Λ, Λ⁆⁆, Lt⁆ = ⊥ := by
    refine commutator_commutator_eq_bot_of_rotate (H₁ := ⁅Λ, Λ⁆) (H₂ := ⁅Λ, Λ⁆) (H₃ := Lt) ?_ ?_
    · exact eq_bot_iff.2 ((commutator_mono hLt le_rfl).trans (hWN _ (hD.trans hΛN)).le)
    · rw [commutator_comm Lt]
      exact eq_bot_iff.2 ((commutator_mono hLt le_rfl).trans (hWN _ (hD.trans hΛN)).le)
  rwa [h3] at h4

end ThreeSubgroup

namespace Ctx

section Final

open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (mem_centerMod_iff commutator_mem_iff_proj)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN2Aux (mem_bar_iff_exists bar_sup
  bar_inf bar_commutator bar_map_conj lift_sup lift_inf bar_centerMod centerMod_eq_lift
  relIndex_eq_card_bar bar_self lift_bar_eq_sup eq_of_bar_eq conjT_eq_self_of_mem_normalizer
  map_conj_le_normalizer le_of_bar_eq_bot lift_bot comm_le_self isPGroup_lift_of zOf hOf
  mem_normalizer_lift)

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
  {t wb : G} {W Y M N P F₅ A Λ : Subgroup G} (C : Ctx K f t wb W Y M N P F₅ A Λ)
include C

theorem W_N : W ≤ N := C.W_M.trans (C.M_P.trans C.P_N)

theorem W_Λ : W ≤ Λ := C.W_M.trans C.M_Λ

theorem bar_N' : (bar W (Λ ⊓ A) ⊔ (bar W (Λ ⊓ A))ᵍ[proj W ⟨t, C.t_W⟩]) ⊔ bar W M = bar W N := by
  rw [C.bar_N, C.bar_A₂_t]

theorem yamada73 :
    ((W.relIndex (centerMod W Λ) = Nat.card K ^ 2 ∧
      centerMod W Λ ⊔ centerMod W (Λᵍ[t]) = M ∧
      centerMod W Λ ⊓ centerMod W (Λᵍ[t]) = W) ∧
    (derivedMod W Λ ⊔ (derivedMod W Λ)ᵍ[t] = N ∧
      derivedMod W Λ ⊓ (derivedMod W Λ)ᵍ[t] = W ∧
      ⁅derivedMod W Λ, (derivedMod W Λ)ᵍ[t]⁆ ≤ W ∧
      derivedMod W (derivedMod W Λ) = derivedMod W Λ) ∧
    (derivedMod W Λ = (Λ ⊓ A) ⊔ centerMod W (Λᵍ[t]) ∧
      centerMod W (Λᵍ[t]) = pCoreOf 2 (derivedMod W Λ)) ∧
    centerMod W (P ⊓ Λ) = F₅ ⊔ centerMod W Λ) := by
  have D := C.hat73
  set t' := proj W ⟨t, C.t_W⟩ with ht'
  have hΛN : Λ ≤ normalizer (W : Set G) := C.Λ_N.trans C.N_W
  have hbarΛ : bar W Λ = bar W (Λ ⊓ A) ⊔ bar W M := C.bar_Λ
  have hbarΛ' : bar W (Λᵍ[t]) = (bar W (Λ ⊓ A))ᵍ[t'] ⊔ bar W M := by
    rw [C.bar_Λ', C.bar_A₂_t]
  have hZ₁ : centerMod W Λ = lift (zOf (bar W M) (bar W (Λ ⊓ A))) := by
    rw [centerMod_eq_lift, hbarΛ, D.center_Lam]
  have hZ₂ : centerMod W (Λᵍ[t]) = lift (zOf (bar W M) ((bar W (Λ ⊓ A))ᵍ[t'])) := by
    rw [centerMod_eq_lift, hbarΛ', D.center_Lam']
  have hD : derivedMod W Λ = lift (hOf t' (bar W (Λ ⊓ A)) (bar W M)) := by
    have e : derivedMod W Λ = derivedMod W (lift (bar W Λ) : Subgroup G) := by
      rw [lift_bar C.W_Λ hΛN]
    rw [e, derivedMod_lift, hbarΛ, D.Lam_comm]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [hZ₁, relIndex_eq_card_bar (le_lift _) (lift_le_normalizer _), bar_lift]
    exact D.V_card.1
  · rw [hZ₁, hZ₂, ← lift_sup, ← D.E_eq_sup, lift_bar C.W_M C.M_W']
  · rw [hZ₁, hZ₂, ← lift_inf, D.V_inf, lift_bot]
  · rw [hD, lift_map_conjT C.t_W, ← lift_sup, ← D.prod_decomp.1, C.bar_N', lift_bar C.W_N C.N_W]
  · rw [hD, lift_map_conjT C.t_W, ← lift_inf, D.prod_decomp.2.1, lift_bot]
  · have hX : (lift (hOf t' (bar W (Λ ⊓ A)) (bar W M)) : Subgroup G) ≤ normalizer (W : Set G) :=
      lift_le_normalizer _
    have hY : (lift ((hOf t' (bar W (Λ ⊓ A)) (bar W M))ᵍ[t']) : Subgroup G) ≤
        normalizer (W : Set G) := lift_le_normalizer _
    rw [hD, lift_map_conjT C.t_W]
    refine le_of_bar_eq_bot ((commutator_mono hX hY).trans (comm_le_self _)) ?_
    rw [bar_commutator hX hY, bar_lift, bar_lift]
    exact D.prod_decomp.2.2
  · rw [hD, derivedMod_lift, D.H_perfect]
  · rw [hD, hZ₂, hOf, lift_sup, lift_bar_eq_sup C.A₂_W', sup_assoc, sup_eq_right.2 (le_lift _)]
  · have hW2 : IsPGroup 2 W := C.P_two.to_le C.W_P
    obtain ⟨hZH, hZ2, hHn, hmax⟩ := D.pcore
    have hkN : (lift (hOf t' (bar W (Λ ⊓ A)) (bar W M)) : Subgroup G) ≤ normalizer (W : Set G) :=
      lift_le_normalizer _
    have hWk : W ≤ (lift (hOf t' (bar W (Λ ⊓ A)) (bar W M)) : Subgroup G) := le_lift _
    rw [hD, hZ₂]
    refine le_antisymm ?_ ?_
    · have hl : lift (zOf (bar W M) ((bar W (Λ ⊓ A))ᵍ[t'])) ≤
          (lift (hOf t' (bar W (Λ ⊓ A)) (bar W M)) : Subgroup G) := lift_mono hZH
      have hn : (lift (hOf t' (bar W (Λ ⊓ A)) (bar W M)) : Subgroup G) ≤
          normalizer ((lift (zOf (bar W M) ((bar W (Λ ⊓ A))ᵍ[t'])) : Subgroup G) : Set G) := by
        intro k hk
        have hkH : proj W ⟨k, hkN hk⟩ ∈ hOf t' (bar W (Λ ⊓ A)) (bar W M) :=
          proj_mem_of_mem_lift hk
        exact mem_normalizer_lift (hkN hk) (hHn hkH)
      exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hl hn (isPGroup_lift_of hW2 hZ2)
    · have hRk : pCoreOf 2 (lift (hOf t' (bar W (Λ ⊓ A)) (bar W M)) : Subgroup G) ≤
          lift (hOf t' (bar W (Λ ⊓ A)) (bar W M)) := LieType.BorelTits.pCoreOf_le 2 _
      have hR2 : IsPGroup 2 (pCoreOf 2 (lift (hOf t' (bar W (Λ ⊓ A)) (bar W M)) : Subgroup G)) :=
        LieType.BorelTits.pCoreOf_isPGroup 2 _
      have hRn : (lift (hOf t' (bar W (Λ ⊓ A)) (bar W M)) : Subgroup G) ≤
          normalizer ((pCoreOf 2 (lift (hOf t' (bar W (Λ ⊓ A)) (bar W M)) : Subgroup G) :
            Subgroup G) : Set G) := LieType.BorelTits.le_normalizer_pCoreOf 2 _
      have hWR : W ≤ pCoreOf 2 (lift (hOf t' (bar W (Λ ⊓ A)) (bar W M)) : Subgroup G) :=
        LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hWk hkN hW2
      have hRN : pCoreOf 2 (lift (hOf t' (bar W (Λ ⊓ A)) (bar W M)) : Subgroup G) ≤
          normalizer (W : Set G) := hRk.trans hkN
      have h1 : bar W (pCoreOf 2 (lift (hOf t' (bar W (Λ ⊓ A)) (bar W M)) : Subgroup G)) ≤
          zOf (bar W M) ((bar W (Λ ⊓ A))ᵍ[t']) := by
        refine hmax _ ?_ ?_ (isPGroup_bar hR2)
        · have := bar_mono (A := W) hRk
          rwa [bar_lift] at this
        · have := bar_le_normalizer_bar hWR hRn
          rwa [bar_lift] at this
      calc pCoreOf 2 (lift (hOf t' (bar W (Λ ⊓ A)) (bar W M)) : Subgroup G) =
            lift (bar W (pCoreOf 2 (lift (hOf t' (bar W (Λ ⊓ A)) (bar W M)) : Subgroup G))) :=
          (lift_bar hWR hRN).symm
        _ ≤ _ := lift_mono h1
  · have hbarPΛ : bar W (P ⊓ Λ) = bar W P ⊓ (bar W (Λ ⊓ A) ⊔ bar W M) := by
      rw [bar_inf C.W_P, hbarΛ]
    rw [centerMod_eq_lift, hbarPΛ, D.center_Pt, lift_sup, lift_bar C.W_F C.F_W', ← hZ₁]

theorem Y_Λ : Y ≤ Λ := C.Y_W.trans C.W_Λ

theorem ZH_le_M : centerMod W Λ ≤ M := le_sup_left.trans C.yamada73.1.2.1.le

theorem ZH_le_Λ : centerMod W Λ ≤ Λ := C.ZH_le_M.trans C.M_Λ

theorem W_le_ZH : W ≤ centerMod W Λ := by
  rw [centerMod_eq_lift]
  exact le_lift _

theorem Λ_dec : Λ = ⁅Λ, Λ⁆ ⊔ centerMod W Λ := by
  obtain ⟨⟨-, h3b, -⟩, -, ⟨h3d, -⟩, -⟩ := C.yamada73
  have hdW : derivedMod W Λ ≤ ⁅Λ, Λ⁆ ⊔ centerMod W Λ := sup_le_sup_left C.W_le_ZH _
  refine le_antisymm ?_ (sup_le (comm_le_self Λ) C.ZH_le_Λ)
  calc Λ = (Λ ⊓ A) ⊔ M := C.Λ_eq
    _ ≤ ⁅Λ, Λ⁆ ⊔ centerMod W Λ := by
      refine sup_le ?_ ?_
      · exact (le_sup_left.trans h3d.symm.le).trans hdW
      · refine h3b.symm.le.trans (sup_le le_sup_right ?_)
        exact (le_sup_right.trans h3d.symm.le).trans hdW

theorem comm_ZH_le : ⁅Λ, centerMod W Λ⁆ ≤ W := by
  have hΛN : Λ ≤ normalizer (W : Set G) := C.Λ_N.trans C.N_W
  refine commutator_le.2 fun a ha z hz => ?_
  have e : a * z * a⁻¹ * z⁻¹ = (z * a * z⁻¹ * a⁻¹)⁻¹ := by group
  rw [commutatorElement_def, e]
  exact inv_mem (((mem_centerMod_iff C.W_Λ).1 hz).2.2 a ha (hΛN ha))

theorem comm_comm_le : ⁅⁅Λ, Λ⁆, (⁅Λ, Λ⁆)ᵍ[t]⁆ ≤ W := by
  obtain ⟨-, ⟨-, -, h3c3, -⟩, -, -⟩ := C.yamada73
  have h1 : ⁅Λ, Λ⁆ ≤ derivedMod W Λ := le_sup_left
  exact (commutator_mono h1 (Subgroup.map_mono h1)).trans h3c3

theorem hat74 : ⁅bar Y Λ, bar Y (centerMod W Λ)⁆ = ⊥ ∧
    ⁅⁅bar Y Λ, bar Y Λ⁆, ⁅bar Y Λ, bar Y Λ⁆⁆ = ⁅bar Y Λ, bar Y Λ⁆ ∧
    ⁅⁅bar Y Λ, bar Y Λ⁆, (⁅bar Y Λ, bar Y Λ⁆)ᵍ[proj Y ⟨t, C.t_Y⟩]⁆ = ⊥ := by
  have hΛY : Λ ≤ normalizer (Y : Set G) := C.Λ_N.trans C.N_Y
  have hZHY : centerMod W Λ ≤ normalizer (Y : Set G) := C.ZH_le_Λ.trans hΛY
  have hDΛ : ⁅Λ, Λ⁆ ≤ normalizer (Y : Set G) := (comm_le_self Λ).trans hΛY
  have hW' : ∀ w ∈ bar Y W, ∀ n ∈ bar Y N, w * n = n * w := by
    have h := bar_centerMod (W := Y) N
    rw [C.cen_Y] at h
    intro w hw n hn
    have hw' : w ∈ bar Y N ⊓ centralizer (bar Y N : Set (Bar Y)) := h ▸ hw
    exact (mem_centralizer_iff.1 hw'.2 n hn).symm
  have hZW' : ⁅bar Y Λ, bar Y (centerMod W Λ)⁆ ≤ bar Y W := by
    rw [← bar_commutator hΛY hZHY]
    exact bar_mono C.comm_ZH_le
  have hΛ' : bar Y Λ = ⁅bar Y Λ, bar Y Λ⁆ ⊔ bar Y (centerMod W Λ) := by
    rw [← bar_commutator hΛY hΛY, ← bar_sup hDΛ hZHY, ← C.Λ_dec]
  have hZab : ∀ a ∈ bar Y (centerMod W Λ), ∀ b ∈ bar Y (centerMod W Λ), a * b = b * a :=
    fun a ha b hb => proj_comm_of_commutator_mem (X := M) (C.M_P.trans (C.P_N.trans C.N_Y))
      (fun x hx y hy => C.M_comm x hx y hy) a (bar_mono C.ZH_le_M ha) b (bar_mono C.ZH_le_M hb)
  have hLt : ⁅⁅bar Y Λ, bar Y Λ⁆, (⁅bar Y Λ, bar Y Λ⁆)ᵍ[proj Y ⟨t, C.t_Y⟩]⁆ ≤ bar Y W := by
    rw [← bar_commutator hΛY hΛY, ← bar_map_conjT C.t_Y hDΛ,
      ← bar_commutator hDΛ (map_conj_le_normalizer (inv_mem C.t_Y) hDΛ)]
    exact bar_mono C.comm_comm_le
  exact three_subgroup_step (Λ := bar Y Λ) (Z := bar Y (centerMod W Λ))
    (W := bar Y W) (N := bar Y N) (Lt := (⁅bar Y Λ, bar Y Λ⁆)ᵍ[proj Y ⟨t, C.t_Y⟩])
    (bar_mono C.Λ_N) hW' hZW' hΛ' hZab hLt

theorem center_Y_eq : centerMod Y Λ = centerMod W Λ := by
  have hΛY : Λ ≤ normalizer (Y : Set G) := C.Λ_N.trans C.N_Y
  have hΛN : Λ ≤ normalizer (W : Set G) := C.Λ_N.trans C.N_W
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · have hx' := (mem_centerMod_iff C.Y_Λ).1 hx
    rw [mem_centerMod_iff C.W_Λ]
    exact ⟨hx'.1, hΛN hx'.1, fun a ha _ => C.Y_W (hx'.2.2 a ha (hΛY ha))⟩
  · have hx' := (mem_centerMod_iff C.W_Λ).1 hx
    rw [mem_centerMod_iff C.Y_Λ]
    refine ⟨hx'.1, hΛY hx'.1, fun a ha haY => ?_⟩
    have hle := commutator_eq_bot_iff_le_centralizer.1 C.hat74.1
    have hmem := hle (proj_mem_bar (x := ⟨a, haY⟩) ha)
    have hc := mem_centralizer_iff.1 hmem (proj Y ⟨x, hΛY hx'.1⟩)
      (proj_mem_bar (x := ⟨x, hΛY hx'.1⟩) hx)
    exact (commutator_mem_iff_proj (N := Y) (hΛY hx'.1) haY).1 hc.symm

theorem yamada74 :
    (centerMod Y Λ = centerMod W Λ ∧ centerMod Y (P ⊓ Λ) = centerMod W (P ⊓ Λ)) ∧
    (derivedMod Y (derivedMod Y Λ) = derivedMod Y Λ ∧
      ⁅derivedMod Y Λ, (derivedMod Y Λ)ᵍ[t]⁆ ≤ Y) := by
  have hΛY : Λ ≤ normalizer (Y : Set G) := C.Λ_N.trans C.N_Y
  have hΛN : Λ ≤ normalizer (W : Set G) := C.Λ_N.trans C.N_W
  have hd : ∀ X : Subgroup G, X ≤ normalizer (Y : Set G) →
      bar Y (derivedMod Y X) = ⁅bar Y X, bar Y X⁆ := by
    intro X hX
    unfold derivedMod
    rw [bar_sup ((comm_le_self X).trans hX) Subgroup.le_normalizer, bar_commutator hX hX,
      bar_self, sup_bot_eq]
  have hdN : ∀ X : Subgroup G, X ≤ normalizer (Y : Set G) →
      derivedMod Y X ≤ normalizer (Y : Set G) :=
    fun X hX => sup_le ((comm_le_self X).trans hX) Subgroup.le_normalizer
  refine ⟨⟨C.center_Y_eq, ?_⟩, ?_, ?_⟩
  · have hYPΛ : Y ≤ P ⊓ Λ := le_inf (C.Y_W.trans (C.W_P)) C.Y_Λ
    have hYW : Y ≤ P ⊓ Λ := hYPΛ
    refine le_antisymm (fun x hx => ?_) ?_
    · have hx' := (mem_centerMod_iff hYPΛ).1 hx
      rw [mem_centerMod_iff (C.W_P.trans le_rfl |> fun h => le_inf h C.W_Λ)]
      exact ⟨hx'.1, hΛN hx'.1.2, fun a ha _ => C.Y_W (hx'.2.2 a ha (hΛY ha.2))⟩
    · rw [C.yamada73.2.2.2]
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · rw [mem_centerMod_iff hYPΛ]
        exact ⟨mem_inf.2 ⟨C.F_M.trans C.M_P hx, C.M_Λ (C.F_M hx)⟩,
          hΛY (C.M_Λ (C.F_M hx)), fun a ha _ => C.F_P x hx a ha.1⟩
      · have hx' : x ∈ centerMod Y Λ := C.center_Y_eq.symm ▸ hx
        rw [mem_centerMod_iff hYPΛ]
        exact ⟨mem_inf.2 ⟨C.M_P (C.ZH_le_M hx), C.ZH_le_Λ hx⟩, hΛY (C.ZH_le_Λ hx),
          fun a ha _ => ((mem_centerMod_iff C.Y_Λ).1 hx').2.2 a ha.2 (hΛY ha.2)⟩
  · refine eq_of_bar_eq le_sup_right (hdN _ (hdN Λ hΛY)) le_sup_right (hdN Λ hΛY) ?_
    rw [hd _ (hdN Λ hΛY), hd Λ hΛY]
    exact C.hat74.2.1
  · have hdΛ := hdN Λ hΛY
    have hdΛt : (derivedMod Y Λ)ᵍ[t] ≤ normalizer (Y : Set G) :=
      map_conj_le_normalizer (inv_mem C.t_Y) hdΛ
    refine le_of_bar_eq_bot ((commutator_mono hdΛ hdΛt).trans (comm_le_self _)) ?_
    rw [bar_commutator hdΛ hdΛt, bar_map_conjT C.t_Y hdΛ, hd Λ hΛY]
    exact C.hat74.2.2

end Final

end Ctx

end CFSG.LocalAnalysis.EvenBN.G2.ProductN2Aux

namespace CFSG.LocalAnalysis.EvenBN.G2.ProductN2Aux

open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN2Aux
  (conjT_eq_self_of_mem_normalizer)

section Instance

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem ctx_of (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f)
    {Λ₂ : Subgroup G} (hΛ : IsFactor (yamadaM₆ d t) (yamadaN₂ d t) Λ₂ t K) :
    Ctx K f t d.wb (yamadaW₃ d t) (yamadaY₂ d t) (yamadaM₆ d t) (yamadaN₂ d t)
      (yamadaP d t) (yamadaF₅ d t) hp.Astar Λ₂ := by
  obtain ⟨α, hex, -⟩ := hp.exact₂
  have hD := hQ.doubling
  obtain ⟨hcen_a, hcen_b, hcen_c, hcen_d, hcen_e, -⟩ :=
    h.yamadaN₂_centers hW d hK hQ hp.sylow₂ hex
  obtain ⟨-, hN_gen⟩ := h.yamadaP_inf_map_conj_wb hW d hK hQ hp.sylow₂ hex
  obtain ⟨hY_W, -, hWX, -⟩ := h.yamada_5_46_1 hW d hK hQ
  obtain ⟨hM_F, -, hF_inf⟩ := h.yamada_5_44_2 hW d hK hQ
  obtain ⟨⟨-, ht_M, -⟩, -⟩ := h.yamada_5_44_1 hW d hK hQ
  obtain ⟨⟨-, htP, -⟩, -⟩ := h.yamada_5_51 hW d hK hQ
  obtain ⟨-, ⟨hsq, hcomm⟩⟩ := h.yamada_5_55_1 hW d hK hQ
  obtain ⟨-, hVN, -, -, -, hV₃eq, hWc⟩ := h.yamadaW₃_facts hW d hK hD
  have hKN : yamadaK₂ d ≤ normalizer (yamadaM₆ d t : Set G) :=
    (commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb) :
        yamadaK₂ d ≤ L ⊓ normalizer (d.Y : Set G)).trans
      (h.normalizer_L_le_yamadaD₇_M₆ hW d hK hQ).2
  have hNM : yamadaN₂ d t ≤ normalizer (yamadaM₆ d t : Set G) := yamadaN₂_le_normalizer d t hKN
  have hY : t ∈ normalizer (yamadaY₂ d t : Set G) := by
    have := mem_normalizer_commutator_aux ht_M ht_M
    rwa [hcomm] at this
  have h2f : 2 ≤ f := h.two_le
  exact
  { t_sq := h.t_mul_t
    Y_W := hY_W
    W_M := h.yamadaW₃_le_yamadaM₆ hW d hK hQ
    W_F := le_sup_left.trans hWX.le
    F_M := h.yamadaF₅_le_yamadaM₆ hW d hK hQ
    M_P := h.yamadaM₆_le_yamadaP hW d hK hQ
    P_N := hp.sylow₂.le
    P_two := hp.sylow₂.isPGroup
    N_W := hcen_a
    N_M := hNM
    N_Y := fun g hg => by
      have := mem_normalizer_commutator_aux (hNM hg) (hNM hg)
      rwa [hcomm] at this
    t_W := hVN (hV₃eq.le (mem_sup_right (mem_zpowers t)))
    t_M := ht_M
    t_Y := hY
    P_t := conjT_eq_self_of_mem_normalizer htP
    A_N := hp.Astar_spec.le_cen.trans inf_le_left
    A_inf := hp.Astar_spec.inf_eq
    N_eq := hp.Astar_spec.sup_eq
    A_t := hp.Astar_spec.conj_eq
    wb_A := hp.Astar_spec.levi_le d.wb_mem_leviB
    fac := hΛ
    cen_Y := hcen_b
    cen_W := hcen_c
    cen_P := hcen_d
    cent_M := hcen_e
    N_gen := hN_gen
    M_F := hM_F
    F_inf := hF_inf
    M_sq := fun x hx => by
      rw [← hsq]
      exact subset_closure ⟨x, hx, (sq x).symm⟩
    M_comm := fun x hx y hy => by
      have := commutator_mem_commutator hx hy
      rw [hcomm, commutatorElement_def] at this
      exact this
    F_P := fun x hx y hy => h.commutator_yamadaF₅_yamadaP_le hW d hK hQ x hx y hy
    card_K := hK
    two_le := h2f
    card_M := Setup.Q44.card_M₆ hW h d hK hQ
    card_W := hWc
    card_P := h.card_yamadaP hW d hK hQ }

end Instance

end CFSG.LocalAnalysis.EvenBN.G2.ProductN2Aux

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem yamada_7_3 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f) {Λ₂ : Subgroup G}
    (hΛ : IsFactor (yamadaM₆ d t) (yamadaN₂ d t) Λ₂ t K) :
    ((yamadaW₃ d t).relIndex (centerMod (yamadaW₃ d t) Λ₂) = Nat.card K ^ 2 ∧
      centerMod (yamadaW₃ d t) Λ₂ ⊔ centerMod (yamadaW₃ d t) (Λ₂ᵍ[t]) = yamadaM₆ d t ∧
      centerMod (yamadaW₃ d t) Λ₂ ⊓ centerMod (yamadaW₃ d t) (Λ₂ᵍ[t]) = yamadaW₃ d t) ∧
    (derivedMod (yamadaW₃ d t) Λ₂ ⊔ (derivedMod (yamadaW₃ d t) Λ₂)ᵍ[t] = yamadaN₂ d t ∧
      derivedMod (yamadaW₃ d t) Λ₂ ⊓ (derivedMod (yamadaW₃ d t) Λ₂)ᵍ[t] = yamadaW₃ d t ∧
      ⁅derivedMod (yamadaW₃ d t) Λ₂, (derivedMod (yamadaW₃ d t) Λ₂)ᵍ[t]⁆ ≤ yamadaW₃ d t ∧
      derivedMod (yamadaW₃ d t) (derivedMod (yamadaW₃ d t) Λ₂) =
        derivedMod (yamadaW₃ d t) Λ₂) ∧
    (derivedMod (yamadaW₃ d t) Λ₂ =
        leviFactor₂ hp.Astar Λ₂ ⊔ centerMod (yamadaW₃ d t) (Λ₂ᵍ[t]) ∧
      centerMod (yamadaW₃ d t) (Λ₂ᵍ[t]) = pCoreOf 2 (derivedMod (yamadaW₃ d t) Λ₂)) ∧
    centerMod (yamadaW₃ d t) (yamadaP d t ⊓ Λ₂) =
      yamadaF₅ d t ⊔ centerMod (yamadaW₃ d t) Λ₂ :=
  (ProductN2Aux.ctx_of hW h d hK hQ hp hΛ).yamada73

theorem yamada_7_4 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f) {Λ₂ : Subgroup G}
    (hΛ : IsFactor (yamadaM₆ d t) (yamadaN₂ d t) Λ₂ t K) :
    (centerMod (yamadaY₂ d t) Λ₂ = centerMod (yamadaW₃ d t) Λ₂ ∧
      centerMod (yamadaY₂ d t) (yamadaP d t ⊓ Λ₂) =
        centerMod (yamadaW₃ d t) (yamadaP d t ⊓ Λ₂)) ∧
    (derivedMod (yamadaY₂ d t) (derivedMod (yamadaY₂ d t) Λ₂) = derivedMod (yamadaY₂ d t) Λ₂ ∧
      ⁅derivedMod (yamadaY₂ d t) Λ₂, (derivedMod (yamadaY₂ d t) Λ₂)ᵍ[t]⁆ ≤ yamadaY₂ d t) :=
  (ProductN2Aux.ctx_of hW h d hK hQ hp hΛ).yamada74

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2

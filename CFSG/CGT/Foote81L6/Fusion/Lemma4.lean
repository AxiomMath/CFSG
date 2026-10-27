module

public import CFSG.CGT.Foote81L6.Fusion.CentralizerS
public import CFSG.CGT.Foote81L6.T0Sylow
public import CFSG.CGT.Foote81L6.Fusion.FourthPower

public section

namespace CFSG.CGT.Foote81L6

open Subgroup

private theorem exists_conj_mem_of_le_sylow {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)
    {N P : Subgroup G} (hTN : (T : Subgroup G) ≤ N) (hPN : P ≤ N) (hP : IsPGroup 2 P) :
    ∃ c ∈ N, ∀ x ∈ P, c * x * c⁻¹ ∈ (T : Subgroup G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsPGroup 2 (P.subgroupOf N) := hP.comap_subtype
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq N Q (T.subtype hTN)
  refine ⟨c, c.2, fun x hx => ?_⟩
  have hxQ : (⟨x, hPN hx⟩ : N) ∈ (Q : Subgroup N) :=
    hQ (show (⟨x, hPN hx⟩ : N) ∈ P.subgroupOf N from hx)
  have hmem : c * ⟨x, hPN hx⟩ * c⁻¹ ∈ ((c • Q : Sylow 2 N) : Subgroup N) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨_, hxQ, rfl⟩
  rw [hc, Sylow.coe_subtype, mem_subgroupOf] at hmem
  simpa using hmem

namespace FooteCore

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {m n : ℕ}

theorem lemma4_one_large (D : FooteCore G (T : Subgroup G) m n)
    (hL3b : ∀ y ∈ D.Zab, IsConj D.b y → y = D.b) (hab : ¬ IsConj D.a (D.a * D.b)) (hn : 4 ≤ n)
    (g : G) (hgT : g * D.a * g⁻¹ ∈ (T : Subgroup G)) : g * D.a * g⁻¹ ∈ D.T₁ := by
  have hTC : (T : Subgroup G) ≤ centralizer ({D.a} : Set G) := fun y hy =>
    mem_centralizer_singleton_iff.2 (D.a_comm_T hy)
  by_contra h1
  by_cases h0 : g * D.a * g⁻¹ ∈ D.T₀
  · exact hab (D.isConj_mul_b_of_mem_T₀_of_four_le hn hL3b le_rfl (T.subtype hTC)
      (Sylow.coe_subtype T hTC) D.a_mul_a h0 h1)
  · exact hab (D.isConj_mul_b_of_not_mem_T₀ hL3b le_rfl (T.subtype hTC)
      (Sylow.coe_subtype T hTC) D.a_mul_a hgT h0)

theorem lemma4_two_three (D : FooteCore G (T : Subgroup G) 2 n)
    (hL3b : ∀ y ∈ D.Zab, IsConj D.b y → y = D.b)
    (hL32 : ∀ {a₁ : G}, a₁ ∈ D.A → a₁ ≠ 1 → a₁ ≠ D.a → ¬ IsConj a₁ (a₁ * D.b))
    (hcen : D.a ∈ center G) {a₁ : G} (ha₁ : a₁ ∈ D.A) (ha₁1 : a₁ ≠ 1) (ha₁a : a₁ ≠ D.a)
    (hn : n = 3) {g : G} (hg₀ : g * a₁ * g⁻¹ ∈ D.T₀) (hg₁ : g * a₁ * g⁻¹ ∉ D.T₁) : False := by
  subst hn
  have hcen' : ∀ y : G, y * D.a * y⁻¹ = D.a := fun y => by
    rw [mem_center_iff.1 hcen y, mul_inv_cancel_right]
  have hu2 : g * a₁ * g⁻¹ * (g * a₁ * g⁻¹) = 1 := by
    rw [show g * a₁ * g⁻¹ * (g * a₁ * g⁻¹) = g * (a₁ * a₁) * g⁻¹ by group, D.mul_self_of_two ha₁,
      mul_one, mul_inv_cancel]
  obtain ⟨a', ha', -, β, hβ, hβu⟩ := D.exists_conj_mul_s hg₀ hg₁ hu2
  obtain ⟨q', hq'T, hq's, hq'4⟩ := D.exists_pow_four_eq_b_comm_s
  have hβT : β ∈ (T : Subgroup G) := D.B_le_T (D.B₀_le_B hβ)
  have hqT : β * q' * β⁻¹ ∈ (T : Subgroup G) := mul_mem (mul_mem hβT hq'T) (inv_mem hβT)
  have hq4 : (β * q' * β⁻¹) ^ 4 = D.b := by
    rw [conj_pow, hq'4, D.b_comm_T hβT, mul_inv_cancel_right]
  have hqu : β * q' * β⁻¹ * (g * a₁ * g⁻¹) * (β * q' * β⁻¹)⁻¹ = g * a₁ * g⁻¹ ∨
      β * q' * β⁻¹ * (g * a₁ * g⁻¹) * (β * q' * β⁻¹)⁻¹ = D.a * (g * a₁ * g⁻¹) := by
    have hs' : q' * D.s * q'⁻¹ = D.s := by rw [hq's, mul_inv_cancel_right]
    have e : β * q' * β⁻¹ * (β * (a' * D.s) * β⁻¹) * (β * q' * β⁻¹)⁻¹ =
        β * ((q' * a' * q'⁻¹) * (q' * D.s * q'⁻¹)) * β⁻¹ := by group
    rw [← hβu, e, hs']
    rcases D.conj_A_of_two hq'T ha' with h | h
    · left
      rw [h]
    · right
      rw [h, show β * (D.a * a' * D.s) * β⁻¹ = (β * D.a * β⁻¹) * (β * (a' * D.s) * β⁻¹) by group,
        hcen']
  set V : Subgroup G := zpowers D.a ⊔ zpowers a₁ with hV
  have hVA : V ≤ D.A := sup_le (zpowers_le.2 D.a_mem) (zpowers_le.2 ha₁)
  haveI : Finite D.A := D.finite_A
  haveI : Finite V := Finite.of_injective _ (inclusion_injective hVA)
  have hnorm : ∀ x : G, (x * a₁ * x⁻¹ = a₁ ∨ x * a₁ * x⁻¹ = D.a * a₁) →
      x ∈ normalizer (V : Set G) := by
    intro x hxa₁
    apply TStruct.mem_normalizer_of_forall_conj_mem
    have hle : V.map (MulAut.conj x).toMonoidHom ≤ V := by
      rw [hV, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
      · show x * D.a * x⁻¹ ∈ V
        rw [hcen']
        exact mem_sup_left (mem_zpowers _)
      · show x * a₁ * x⁻¹ ∈ V
        rcases hxa₁ with h | h <;> rw [h]
        · exact mem_sup_right (mem_zpowers _)
        · exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))
    intro v hv
    exact hle ⟨v, hv, rfl⟩
  have hTN : (T : Subgroup G) ≤ normalizer (V : Set G) := fun τ hτ =>
    hnorm τ (D.conj_A_of_two hτ ha₁)
  have hqN : g⁻¹ * (β * q' * β⁻¹) * g ∈ normalizer (V : Set G) := by
    apply hnorm
    have e : g⁻¹ * (β * q' * β⁻¹) * g * a₁ * (g⁻¹ * (β * q' * β⁻¹) * g)⁻¹ =
        g⁻¹ * (β * q' * β⁻¹ * (g * a₁ * g⁻¹) * (β * q' * β⁻¹)⁻¹) * g := by group
    rcases hqu with h | h
    · left
      rw [e, h]
      group
    · right
      rw [e, h, show g⁻¹ * (D.a * (g * a₁ * g⁻¹)) * g = (g⁻¹ * D.a * g⁻¹⁻¹) * a₁ by group, hcen']
  have hP : IsPGroup 2 (zpowers (g⁻¹ * (β * q' * β⁻¹) * g)) :=
    (D.isPGroup_T.map (MulAut.conj g⁻¹).toMonoidHom).to_le (zpowers_le.2
      ⟨β * q' * β⁻¹, hqT, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩)
  obtain ⟨c, hcN, hc⟩ := exists_conj_mem_of_le_sylow T hTN (zpowers_le.2 hqN) hP
  have hkq : c * g⁻¹ * (β * q' * β⁻¹) * (c * g⁻¹)⁻¹ ∈ (T : Subgroup G) := by
    have := hc _ (mem_zpowers _)
    rwa [show c * (g⁻¹ * (β * q' * β⁻¹) * g) * c⁻¹ =
      c * g⁻¹ * (β * q' * β⁻¹) * (c * g⁻¹)⁻¹ by group] at this
  have hkb := D.conj_b_of_pow_four hL3b hkq hq4
  have ha₁'V : c * a₁ * c⁻¹ ∈ V := (mem_normalizer_iff.1 hcN a₁).1 (mem_sup_right (mem_zpowers _))
  have ha₁'1 : c * a₁ * c⁻¹ ≠ 1 := fun h => ha₁1 (by
    have := congrArg (fun y => c⁻¹ * y * c) h
    simpa [mul_assoc] using this)
  have ha₁'a : c * a₁ * c⁻¹ ≠ D.a := fun h => ha₁a (by
    have h2 : c * a₁ * c⁻¹ = c * D.a * c⁻¹ := by rw [h, hcen']
    simpa [mul_assoc] using congrArg (fun y => c⁻¹ * y * c) h2)
  apply hL32 (hVA ha₁'V) ha₁'1 ha₁'a
  have hub : IsConj (g * a₁ * g⁻¹) (g * a₁ * g⁻¹ * D.b) := by
    rw [← hβu]
    exact D.isConj_conj_mul_s_mul_b ha' hβ
  have hk1 : c * g⁻¹ * (g * a₁ * g⁻¹) * (c * g⁻¹)⁻¹ = c * a₁ * c⁻¹ := by group
  have hk2 : c * g⁻¹ * (g * a₁ * g⁻¹ * D.b) * (c * g⁻¹)⁻¹ = c * a₁ * c⁻¹ * D.b := by
    rw [show c * g⁻¹ * (g * a₁ * g⁻¹ * D.b) * (c * g⁻¹)⁻¹ =
      (c * g⁻¹ * (g * a₁ * g⁻¹) * (c * g⁻¹)⁻¹) * (c * g⁻¹ * D.b * (c * g⁻¹)⁻¹) by group, hk1, hkb]
  exact ((isConj_iff.2 ⟨c * g⁻¹, hk1⟩).symm.trans hub).trans (isConj_iff.2 ⟨c * g⁻¹, hk2⟩)

theorem lemma4_two (D : FooteCore G (T : Subgroup G) 2 n)
    (hL3b : ∀ y ∈ D.Zab, IsConj D.b y → y = D.b)
    (hL32 : ∀ {a₁ : G}, a₁ ∈ D.A → a₁ ≠ 1 → a₁ ≠ D.a → ¬ IsConj a₁ (a₁ * D.b))
    (hcen : D.a ∈ center G) {a₁ : G} (ha₁ : a₁ ∈ D.A) (ha₁1 : a₁ ≠ 1) (ha₁a : a₁ ≠ D.a)
    (g : G) (hgT : g * a₁ * g⁻¹ ∈ (T : Subgroup G)) : g * a₁ * g⁻¹ ∈ D.T₁ := by
  obtain ⟨SK, hSK⟩ := D.sylow_centralizer_A hcen ha₁ ha₁1 ha₁a
  have ha₁2 : a₁ * a₁ = 1 := D.mul_self_of_two ha₁
  by_contra h1
  by_cases h0 : g * a₁ * g⁻¹ ∈ D.T₀
  · rcases (show n = 3 ∨ 4 ≤ n by have := D.three_le_n; omega) with hn | hn
    · exact D.lemma4_two_three hL3b hL32 hcen ha₁ ha₁1 ha₁a hn h0 h1
    · exact hL32 ha₁ ha₁1 ha₁a
        (D.isConj_mul_b_of_mem_T₀_of_four_le hn hL3b D.T₀_le_T SK hSK ha₁2 h0 h1)
  · exact hL32 ha₁ ha₁1 ha₁a (D.isConj_mul_b_of_not_mem_T₀ hL3b D.T₀_le_T SK hSK ha₁2 hgT h0)

end FooteCore

end CFSG.CGT.Foote81L6

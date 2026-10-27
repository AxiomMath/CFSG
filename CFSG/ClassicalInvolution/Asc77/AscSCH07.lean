module

public import CFSG.ClassicalInvolution.Asc77.AscSCH06

public section

namespace CFSG.ClassicalInvolution.Asc77.SCH

open scoped commutatorElement

theorem card_sup_eq_mul {G : Type*} [Group G] {R V : Subgroup G}
    (hVR : V ≤ Subgroup.normalizer (R : Set G)) (hRV : R ⊓ V = ⊥) :
    Nat.card (R ⊔ V : Subgroup G) = Nat.card R * Nat.card V := by
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left R V hVR
  let φ : R × V → (R ⊔ V : Subgroup G) := fun x =>
    ⟨x.1 * x.2, mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun x y hxy => ?_, fun z => ?_⟩
    · have h1 : (x.1 : G) * x.2 = y.1 * y.2 := congrArg Subtype.val hxy
      have h2 : ((y.1 : G))⁻¹ * x.1 = y.2 * (x.2 : G)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h1, mul_inv_cancel_right]
      have h3 : ((y.1 : G))⁻¹ * x.1 ∈ R ⊓ V :=
        Subgroup.mem_inf.2 ⟨R.mul_mem (R.inv_mem y.1.2) x.1.2,
          h2 ▸ V.mul_mem y.2.2 (V.inv_mem x.2.2)⟩
      rw [hRV, Subgroup.mem_bot, inv_mul_eq_one] at h3
      have h4 : (x.2 : G) = y.2 := by
        rw [← h3] at h1
        exact mul_left_cancel h1
      exact Prod.ext (Subtype.ext h3.symm) (Subtype.ext h4)
    · have hz : (z : G) ∈ ((R ⊔ V : Subgroup G) : Set G) := z.2
      rw [hset] at hz
      obtain ⟨x, hx, v, hv, hxv⟩ := hz
      exact ⟨(⟨x, hx⟩, ⟨v, hv⟩), Subtype.ext hxv⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective φ hφ)).symm

variable {E J : Type*} [Group E] [Group J]

theorem ker_eq_bot_of_blocks {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) [Finite E] [Group.IsPerfect E]
    (π : E →* J) (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (hCp : IsPGroup p π.ker) {G₁ : Type*} [Group G₁] [Finite G₁] (ι₁ ι₂ : G₁ →* J)
    (hι₁ : Function.Injective ι₁) (hι₂ : Function.Injective ι₂)
    (hcomm : ∀ a b, ι₁ a * ι₂ b = ι₂ b * ι₁ a) (hdisj : ∀ a b, ι₁ a = ι₂ b → ι₁ a = 1)
    (w : J) (hw₁ : ∀ a, w * ι₁ a * w⁻¹ = ι₂ a) (hw₂ : ∀ a, w * ι₂ a * w⁻¹ = ι₁ a)
    (t : G₁) (hord : (Nat.card J).factorization p ≤
      2 * (Nat.card (Subgroup.zpowers t)).factorization p) :
    π.ker = ⊥ := by
  classical
  have hJ : Finite J := Finite.of_surjective π hπ
  set A₁ : Subgroup J := (Subgroup.zpowers t).map ι₁ with hA₁
  set A₂ : Subgroup J := (Subgroup.zpowers t).map ι₂ with hA₂
  have hc1 : Nat.card A₁ = Nat.card (Subgroup.zpowers t) :=
    Subgroup.card_map_of_injective hι₁
  have hc2 : Nat.card A₂ = Nat.card (Subgroup.zpowers t) :=
    Subgroup.card_map_of_injective hι₂
  have hnorm : A₂ ≤ Subgroup.normalizer (A₁ : Set J) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rintro _ ⟨b, -, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, -, rfl⟩
    exact hcomm a b
  have hinf : A₁ ⊓ A₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨a, -, rfl⟩, ⟨b, -, hb⟩⟩
    exact Subgroup.mem_bot.2 (hdisj a b hb.symm)
  have hsup : Nat.card (A₁ ⊔ A₂ : Subgroup J) = Nat.card (Subgroup.zpowers t) ^ 2 := by
    rw [card_sup_eq_mul hnorm hinf, hc1, hc2, sq]
  set x₁ : J := ι₁ t
  set x₂ : J := ι₂ t
  have hle : A₁ ⊔ A₂ ≤ Subgroup.closure ({x₁, x₂} : Set J) := by
    refine sup_le ?_ ?_
    · rw [hA₁, MonoidHom.map_zpowers, Subgroup.zpowers_le]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    · rw [hA₂, MonoidHom.map_zpowers, Subgroup.zpowers_le]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hdvd := Subgroup.card_dvd_of_le hle
  have hfac := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 hdvd p
  rw [hsup, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hfac
  exact ker_eq_bot_of_swap hp2 π hπ hC hCp x₁ x₂ w (hcomm t t) (hw₁ t) (hw₂ t)
    (hord.trans hfac)

end CFSG.ClassicalInvolution.Asc77.SCH

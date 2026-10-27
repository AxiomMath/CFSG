module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.KC.M12Sig

theorem coset_conj_apply_aut {G : Type*} [Group G] (β : MulAut G) (f : G) :
    MulAut.conj (β f) = β * MulAut.conj f * β⁻¹ := by
  ext x
  simp [MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_apply]

theorem le_range_conj_of_fixed {G : Type*} [Group G] [Finite G]
    (hinj : Function.Injective (MulAut.conj : G →* MulAut G))
    (hidx : (MulAut.conj : G →* MulAut G).range.index = 2)
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {A : Subgroup G} (hA : IsPGroup p A)
    (hinner : ∀ α : MulAut G, (∀ f ∈ A, α f = f) → α ∈ (MulAut.conj : G →* MulAut G).range)
    {X : Subgroup (MulAut G)} (hX : IsPGroup 2 X)
    (hXA : A.map (MulAut.conj : G →* MulAut G) ≤ Subgroup.normalizer (X : Set (MulAut G))) :
    X ≤ (MulAut.conj : G →* MulAut G).range := by
  classical
  set I := (MulAut.conj : G →* MulAut G).range with hI
  have : Finite (MulAut G) := Finite.of_injective (fun σ : MulAut G => (σ : G → G))
    (fun a b h => MulEquiv.ext (congrFun h))
  intro α hαX
  by_contra hαI
  have hcI : ∀ f : A, MulAut.conj (f : G) ∈ I := fun f => ⟨f, rfl⟩
  have hcN : ∀ f : A, MulAut.conj (f : G) ∈ Subgroup.normalizer (X : Set (MulAut G)) :=
    fun f => hXA (Subgroup.mem_map_of_mem _ f.2)
  let T := {σ : MulAut G // σ ∈ X ∧ σ ∉ I}
  let act : A → T → T := fun f σ =>
    ⟨MulAut.conj (f : G) * σ.1 * (MulAut.conj (f : G))⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hcN f) σ.1).mp σ.2.1,
      fun h => σ.2.2 (by
        have := I.mul_mem (I.mul_mem (I.inv_mem (hcI f)) h) (hcI f)
        simpa [mul_assoc] using this)⟩
  let : MulAction A T :=
    { smul := act
      one_smul := fun σ => Subtype.ext (by
        change MulAut.conj ((1 : A) : G) * σ.1 * (MulAut.conj ((1 : A) : G))⁻¹ = σ.1
        simp)
      mul_smul := fun f g σ => Subtype.ext (by
        change MulAut.conj ((f * g : A) : G) * σ.1 * (MulAut.conj ((f * g : A) : G))⁻¹ =
          MulAut.conj (f : G) * (MulAut.conj (g : G) * σ.1 * (MulAut.conj (g : G))⁻¹) *
            (MulAut.conj (f : G))⁻¹
        simp [mul_assoc]) }
  have hT : Nat.card T = Nat.card (X ⊓ I : Subgroup (MulAut G)) := by
    refine Nat.card_congr
      { toFun := fun σ => ⟨α⁻¹ * σ.1, Subgroup.mem_inf.mpr ⟨X.mul_mem (X.inv_mem hαX) σ.2.1,
          (Subgroup.mul_mem_iff_of_index_two hidx).mpr
            (iff_of_false (fun h => hαI (inv_mem_iff.mp h)) σ.2.2)⟩⟩
        invFun := fun τ => ⟨α * τ.1, X.mul_mem hαX (Subgroup.mem_inf.mp τ.2).1,
          fun h => hαI (((Subgroup.mul_mem_iff_of_index_two hidx).mp h).mpr
            (Subgroup.mem_inf.mp τ.2).2)⟩
        left_inv := fun σ => Subtype.ext (by simp)
        right_inv := fun τ => Subtype.ext (by simp) }
  have h2 : IsPGroup 2 (X ⊓ I : Subgroup (MulAut G)) := hX.to_le inf_le_left
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  have hmod := hA.card_modEq_card_fixedPoints T
  have hne : Nat.card (MulAction.fixedPoints A T) ≠ 0 := by
    intro h0
    rw [h0, hT, hn] at hmod
    have hdvd : p ∣ 2 ^ n := Nat.modEq_zero_iff_dvd.mp hmod
    exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
      ((Fact.out : p.Prime).dvd_of_dvd_pow hdvd))
  obtain ⟨⟨β, hβ⟩⟩ := (Nat.card_ne_zero.mp hne).1
  rw [MulAction.mem_fixedPoints] at hβ
  have hfix : ∀ f ∈ A, β.1 f = f := by
    intro f hf
    have h1 : MulAut.conj f * β.1 * (MulAut.conj f)⁻¹ = β.1 :=
      congrArg Subtype.val (hβ ⟨f, hf⟩)
    have h2 : MulAut.conj f * β.1 = β.1 * MulAut.conj f := mul_inv_eq_iff_eq_mul.mp h1
    apply hinj
    rw [coset_conj_apply_aut, mul_inv_eq_iff_eq_mul, h2]
  exact β.2.2 (hinner β.1 hfix)

end CFSG.KC.M12Sig

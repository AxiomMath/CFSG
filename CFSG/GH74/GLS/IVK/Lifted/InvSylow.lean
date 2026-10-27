module

public import CFSG.GH74.GLS.IVK.Lifted.QuatAut
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup

section InvSylow

variable {Q : Type} [Group Q] [Finite Q]

theorem exists_invariant_sylow_containing (φ : MulAut Q) (hφ : φ * φ = 1) (r : Q)
    (hr4 : orderOf r = 4) (hrφ : φ r = r) :
    ∃ P₁ : Sylow 2 Q, r ∈ (P₁ : Subgroup Q) ∧ ∀ x ∈ (P₁ : Subgroup Q), φ x ∈ (P₁ : Subgroup Q) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A : Subgroup Q := Subgroup.zpowers r with hAdef
  have hA : IsPGroup 2 ↥A := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [hAdef, Nat.card_zpowers, hr4]
    norm_num
  have hmod := hA.card_modEq_card_fixedPoints (Sylow 2 Q)
  have hone := card_sylow_modEq_one 2 Q
  have hTodd : Odd (Nat.card (MulAction.fixedPoints ↥A (Sylow 2 Q))) := by
    have h3 : 1 ≡ Nat.card (MulAction.fixedPoints ↥A (Sylow 2 Q)) [MOD 2] := hone.symm.trans hmod
    exact Nat.odd_iff.2 (by simpa [Nat.ModEq] using h3.symm)
  have hφφ : ∀ x : Q, φ (φ x) = x := fun x => by
    simpa using congrArg (fun ψ : MulAut Q => ψ x) hφ
  let mp : Sylow 2 Q → Sylow 2 Q := fun S => S.mapSurjective (f := φ.toMonoidHom) φ.surjective
  have hmp : ∀ S : Sylow 2 Q,
      ((mp S : Sylow 2 Q) : Subgroup Q) = (S : Subgroup Q).map φ.toMonoidHom :=
    fun S => Sylow.coe_mapSurjective _ S
  have hmp2 : ∀ S : Sylow 2 Q, mp (mp S) = S := by
    intro S
    apply Sylow.ext
    rw [hmp, hmp, Subgroup.map_map]
    have : φ.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id Q := by
      ext x
      exact hφφ x
    rw [this, Subgroup.map_id]
  have hfix : ∀ S : Sylow 2 Q,
      S ∈ MulAction.fixedPoints ↥A (Sylow 2 Q) ↔ r ∈ (S : Subgroup Q) := by
    intro S
    rw [hA.sylow_mem_fixedPoints_iff, hAdef, Subgroup.zpowers_le]
  have hmem : ∀ S : Sylow 2 Q, r ∈ (S : Subgroup Q) → r ∈ ((mp S : Sylow 2 Q) : Subgroup Q) := by
    intro S hS
    rw [hmp]
    exact Subgroup.mem_map.2 ⟨r, hS, hrφ⟩
  let τ : Equiv.Perm (MulAction.fixedPoints ↥A (Sylow 2 Q)) :=
    { toFun := fun S => ⟨mp S.1, (hfix _).2 (hmem S.1 ((hfix S.1).1 S.2))⟩
      invFun := fun S => ⟨mp S.1, (hfix _).2 (hmem S.1 ((hfix S.1).1 S.2))⟩
      left_inv := fun S => Subtype.ext (hmp2 S.1)
      right_inv := fun S => Subtype.ext (hmp2 S.1) }
  have : Fintype (MulAction.fixedPoints ↥A (Sylow 2 Q)) := Fintype.ofFinite _
  have hnd : ¬ 2 ∣ Fintype.card (MulAction.fixedPoints ↥A (Sylow 2 Q)) := by
    intro hd
    have : Odd (Fintype.card (MulAction.fixedPoints ↥A (Sylow 2 Q))) := by
      rw [← Nat.card_eq_fintype_card]
      exact hTodd
    exact (Nat.not_even_iff_odd.2 this) (even_iff_two_dvd.2 hd)
  have hτ : τ ^ 2 ^ 1 = 1 := by
    apply Equiv.ext
    intro S
    exact Subtype.ext (hmp2 S.1)
  obtain ⟨S, hS⟩ := Equiv.Perm.exists_fixed_point_of_prime hnd hτ
  refine ⟨S.1, (hfix S.1).1 S.2, ?_⟩
  intro x hx
  have h1 : mp S.1 = S.1 := congrArg Subtype.val hS
  have h2 : φ x ∈ ((mp S.1 : Sylow 2 Q) : Subgroup Q) := by
    rw [hmp]
    exact Subgroup.mem_map.2 ⟨x, hx, rfl⟩
  rwa [h1] at h2

theorem exists_fixed_order_four (φ : MulAut Q) (hφ : φ * φ = 1) (r : Q) (hr4 : orderOf r = 4)
    (hrφ : φ r = r) (P : Sylow 2 Q) (hPφ : ∀ p ∈ (P : Subgroup Q), φ p ∈ (P : Subgroup Q))
    (n : ℕ) (hn : 2 ≤ n) (e : QuaternionGroup (2 ^ n) ≃* ↥(P : Subgroup Q)) :
    ∃ y ∈ (P : Subgroup Q), orderOf y = 4 ∧ φ y = y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hφφ : ∀ x : Q, φ (φ x) = x := fun x => by
    simpa using congrArg (fun ψ : MulAut Q => ψ x) hφ
  obtain ⟨P₁, hrP₁, hP₁φ⟩ := exists_invariant_sylow_containing φ hφ r hr4 hrφ
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q P₁ P
  have hconj : ∀ x : Q, x ∈ (P : Subgroup Q) ↔ g⁻¹ * x * g ∈ (P₁ : Subgroup Q) := by
    intro x
    have h := congrArg (fun S : Sylow 2 Q => (S : Subgroup Q)) hg
    simp only [Sylow.coe_subgroup_smul] at h
    rw [← h, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def]
  set u : Q := g⁻¹ * φ g with hu
  have hφu : φ u = (φ g)⁻¹ * g := by rw [hu, map_mul, map_inv, hφφ]
  have huφu : u * φ u = 1 := by rw [hφu, hu]; group
  have huN : u ∈ normalizer ((P₁ : Subgroup Q) : Set Q) := by
    apply Subgroup.mem_normalizer_fintype
    intro x hx
    have hx' : x ∈ (P₁ : Subgroup Q) := hx
    have h1 : φ x ∈ (P₁ : Subgroup Q) := hP₁φ x hx'
    have h2 : g * φ x * g⁻¹ ∈ (P : Subgroup Q) := by
      rw [hconj]
      simpa [mul_assoc] using h1
    have h3 := hPφ _ h2
    rw [hconj] at h3
    have h4 : g⁻¹ * φ (g * φ x * g⁻¹) * g = u * x * u⁻¹ := by
      rw [map_mul, map_mul, map_inv, hφφ, hu]
      group
    rw [h4] at h3
    exact h3
  have hmapP : (P₁ : Subgroup Q).map (MulAut.conj g).toMonoidHom = (P : Subgroup Q) := by
    ext x
    rw [Subgroup.mem_map, hconj]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hy
    · intro hx
      exact ⟨g⁻¹ * x * g, hx, by simp [MulAut.conj_apply, mul_assoc]⟩
  let cP : ↥(P₁ : Subgroup Q) ≃* ↥(P : Subgroup Q) :=
    (Subgroup.equivMapOfInjective (P₁ : Subgroup Q) (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hmapP)
  let e₁ : QuaternionGroup (2 ^ n) ≃* ↥(P₁ : Subgroup Q) := e.trans cP.symm
  obtain ⟨π, hπconj, hπiff⟩ := QuatAut.exists_parity_hom n hn e₁
  let N₁ : Subgroup Q := normalizer ((P₁ : Subgroup Q) : Set Q)
  let ρ : ↥N₁ →* MulAut ↥(P₁ : Subgroup Q) := (P₁ : Subgroup Q).normalizerMonoidHom
  let Θ : ↥N₁ →* Multiplicative (ZMod 2) := π.comp ρ
  have hΘ : ∀ w : ↥N₁, Θ w = 1 := by
    have hP₁N : (P₁ : Subgroup Q) ≤ N₁ := Subgroup.le_normalizer
    have hle : (P₁ : Subgroup Q).subgroupOf N₁ ≤ Θ.ker := by
      intro w hw
      rw [MonoidHom.mem_ker]
      have hwP : (w : Q) ∈ (P₁ : Subgroup Q) := hw
      have hρw : ρ w = MulAut.conj (⟨(w : Q), hwP⟩ : ↥(P₁ : Subgroup Q)) := by
        apply MulEquiv.ext
        intro x
        rfl
      show π (ρ w) = 1
      rw [hρw]
      exact hπconj _
    have h1 : Θ.ker.index ∣ ((P₁ : Subgroup Q).subgroupOf N₁).index :=
      Subgroup.index_dvd_of_le hle
    have h2 : ((P₁ : Subgroup Q).subgroupOf N₁).index ∣ (P₁ : Subgroup Q).index :=
      Dvd.intro _ (Subgroup.relIndex_mul_index hP₁N)
    have h3 : Θ.ker.index ∣ 2 := by
      rw [Subgroup.index_ker]
      have := Subgroup.card_subgroup_dvd_card Θ.range
      have hc : Nat.card (Multiplicative (ZMod 2)) = 2 := by simp
      rwa [hc] at this
    have hodd : ¬ 2 ∣ (P₁ : Subgroup Q).index := Sylow.not_dvd_index P₁
    have hone : Θ.ker.index = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 h3 with h | h
      · exact h
      · exfalso
        apply hodd
        have h4 := h1.trans h2
        rwa [h] at h4
    have htop : Θ.ker = ⊤ := Subgroup.index_eq_one.1 hone
    intro w
    have : w ∈ Θ.ker := by rw [htop]; exact Subgroup.mem_top w
    exact this
  let φ₁ : MulAut ↥(P₁ : Subgroup Q) :=
    { toFun := fun x => ⟨φ x, hP₁φ x x.2⟩
      invFun := fun x => ⟨φ x, hP₁φ x x.2⟩
      left_inv := fun x => Subtype.ext (hφφ x)
      right_inv := fun x => Subtype.ext (hφφ x)
      map_mul' := fun x y => Subtype.ext (map_mul φ (x : Q) (y : Q)) }
  have hφ₁2 : φ₁ * φ₁ = 1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    exact hφφ x
  let ρu : MulAut ↥(P₁ : Subgroup Q) := ρ ⟨u, huN⟩
  let φ₂ : MulAut ↥(P₁ : Subgroup Q) := ρu * φ₁
  have hφ₂val : ∀ x : ↥(P₁ : Subgroup Q), ((φ₂ x : ↥(P₁ : Subgroup Q)) : Q) = u * φ x * u⁻¹ :=
    fun x => rfl
  have hφ₂2 : φ₂ * φ₂ = 1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    show ((φ₂ (φ₂ x) : ↥(P₁ : Subgroup Q)) : Q) = x
    rw [hφ₂val, hφ₂val, map_mul, map_mul, map_inv, hφφ]
    calc u * (φ u * (x : Q) * (φ u)⁻¹) * u⁻¹ = (u * φ u) * (x : Q) * (u * φ u)⁻¹ := by group
      _ = x := by rw [huφu]; group
  have hπφ₂ : π φ₂ = 1 := by
    have h1 : π φ₂ = π ρu * π φ₁ := map_mul π ρu φ₁
    have h2 : π ρu = 1 := hΘ ⟨u, huN⟩
    have h3 : π φ₁ = 1 := by
      refine (hπiff φ₁ hφ₁2).1 ⟨⟨r, hrP₁⟩, ?_, Subtype.ext hrφ⟩
      rw [← Subgroup.orderOf_coe]
      exact hr4
    rw [h1, h2, h3, one_mul]
  obtain ⟨y', hy'4, hy'φ⟩ := (hπiff φ₂ hφ₂2).2 hπφ₂
  refine ⟨g * (y' : Q) * g⁻¹, ?_, ?_, ?_⟩
  · rw [hconj]
    simp [mul_assoc]
  · have h1 : orderOf (g * (y' : Q) * g⁻¹) = orderOf (y' : Q) := by
      have := MulEquiv.orderOf_eq (MulAut.conj g) (y' : Q)
      simpa [MulAut.conj_apply] using this
    rw [h1, Subgroup.orderOf_coe]
    exact hy'4
  · have h1 : u * φ (y' : Q) * u⁻¹ = (y' : Q) :=
      congrArg (fun z : ↥(P₁ : Subgroup Q) => (z : Q)) hy'φ
    have h2 : φ (g * (y' : Q) * g⁻¹) = g * (u * φ (y' : Q) * u⁻¹) * g⁻¹ := by
      rw [map_mul, map_mul, map_inv, hu]
      group
    rw [h2, h1]

end InvSylow

end CFSG.GH74.GLS.IVK.Lifted

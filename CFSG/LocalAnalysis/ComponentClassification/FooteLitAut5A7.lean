module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAut5A7Base
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFoote47Central
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Alt7

public section

namespace CFSG.ComponentClassification.FooteLit.Aut5A7

open CFSG Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.Foote5
open CFSG.ClassicalInvolution.Hat2A7 (A7)

theorem mulAut_conj_conj5 {Y : Type*} [Group Y] (α : MulAut Y) (s : Y) :
    α * MulAut.conj s * α⁻¹ = MulAut.conj (α s) := by
  ext g
  simp [MulAut.mul_apply, MulAut.conj_apply]

theorem innAut5_normal (Y : Type) [Group Y] : (innAut5 Y).Normal :=
  ⟨fun _ ⟨s, hs⟩ g => ⟨g s, by rw [← hs, mulAut_conj_conj5]⟩⟩

theorem cycleType_of_even_involution {π : Perm (Fin 7)} (h2 : π * π = 1) (h1 : π ≠ 1)
    (heven : Perm.sign π = 1) : π.cycleType = {2, 2} := by
  have hpow : π ^ 2 = 1 := by rw [sq]; exact h2
  have htypes : ∀ n, n ∈ cycleType π → n = 2 := pow_prime_eq_one_iff.mp hpow
  rw [← Multiset.eq_replicate_card] at htypes
  have hsupport := π.support.card_le_univ
  rw [← sum_cycleType, htypes, Multiset.sum_replicate, smul_eq_mul] at hsupport
  norm_num at hsupport
  have hcard : Multiset.card π.cycleType ≤ 3 := by omega
  rw [sign_of_cycleType, htypes] at heven
  simp only [Multiset.sum_replicate, smul_eq_mul, Multiset.card_replicate] at heven
  interval_cases h : Multiset.card π.cycleType
  · exact absurd (card_cycleType_eq_zero.mp h) h1
  · exact absurd heven (by decide)
  · rw [htypes]
    rfl
  · exact absurd heven (by decide)

theorem conj_involution_a7 (x y : A7) (hx : orderOf x = 2) (hy : orderOf y = 2) :
    ∃ g : A7, g⁻¹ * x * g = y := by
  have hinv : ∀ z : A7, orderOf z = 2 → ((z : Perm (Fin 7))).cycleType = {2, 2} := fun z hz => by
    have h2 : (z : Perm (Fin 7)) * z = 1 := by
      have := pow_orderOf_eq_one z
      rw [hz, sq] at this
      exact congrArg Subtype.val this
    have h1 : (z : Perm (Fin 7)) ≠ 1 := fun h => by
      have : z = 1 := Subtype.ext h
      rw [this, orderOf_one] at hz
      exact absurd hz (by norm_num)
    exact cycleType_of_even_involution h2 h1 (mem_alternatingGroup.mp z.2)
  have hcPerm : IsConj (x : Perm (Fin 7)) (y : Perm (Fin 7)) :=
    isConj_iff_cycleType_eq.mpr ((hinv x hx).trans (hinv y hy).symm)
  have hsupp : (x : Perm (Fin 7)).support.card + 2 ≤ Fintype.card (Fin 7) := by
    rw [← sum_cycleType, hinv x hx]
    decide
  obtain ⟨c, hc⟩ := isConj_iff.mp (alternatingGroup.isConj_of hcPerm hsupp)
  exact ⟨c⁻¹, by rw [inv_inv, hc]⟩

variable (R : Sylow 2 A7)

theorem card_sylow : Nat.card (R : Subgroup A7) = 8 := by
  obtain ⟨ρ⟩ := AutL2Facts.sylow_two_dihedral_a7 (MulEquiv.refl A7) R
  rw [Nat.card_congr ρ.toEquiv, DihedralGroup.nat_card]

theorem normalizer_sylow :
    normalizer ((R : Subgroup A7) : Set A7) = R :=
  CFSG.QuasithinUnique.L246.C123.normalizer_eq_of_card_eight (card_sylow R)

theorem sylow_noncomm : ∃ a ∈ (R : Subgroup A7), ∃ b ∈ (R : Subgroup A7), a * b ≠ b * a := by
  obtain ⟨ρ⟩ := AutL2Facts.sylow_two_dihedral_a7 (MulEquiv.refl A7) R
  have hne : DihedralGroup.r (1 : ZMod 4) * DihedralGroup.sr 0 ≠
      DihedralGroup.sr 0 * DihedralGroup.r 1 := by decide
  refine ⟨ρ.symm (DihedralGroup.r 1), (ρ.symm _).2, ρ.symm (DihedralGroup.sr 0), (ρ.symm _).2,
    fun h => hne (ρ.symm.injective (Subtype.ext ?_))⟩
  rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
  exact h

theorem card_center_le :
    Nat.card ↥((R : Subgroup A7) ⊓ centralizer ((R : Subgroup A7) : Set A7)) ≤ 2 := by
  obtain ⟨ρ⟩ := AutL2Facts.sylow_two_dihedral_a7 (MulEquiv.refl A7) R
  let f : ↥((R : Subgroup A7) ⊓ centralizer ((R : Subgroup A7) : Set A7)) →
      center (DihedralGroup 4) := fun z => ⟨ρ ⟨z, z.2.1⟩, by
    rw [mem_center_iff]
    intro w
    obtain ⟨w', rfl⟩ := ρ.surjective w
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_iff.mp z.2.2 w' w'.2)⟩
  have hf : Function.Injective f := fun a b h => by
    have h1 := ρ.injective (congrArg Subtype.val h)
    exact Subtype.ext (by simpa using congrArg Subtype.val h1)
  calc Nat.card ↥((R : Subgroup A7) ⊓ centralizer ((R : Subgroup A7) : Set A7))
      ≤ Nat.card (center (DihedralGroup 4)) := Nat.card_le_card_of_injective f hf
    _ = 2 := AutL2Facts.card_center_dihedral (by norm_num) (by decide)

theorem autPerm_eq_of_normalizes {τ : Perm (Fin 7)}
    (hτ : Perm.sign τ = -1) (hτ2 : τ * τ = 1)
    (hτR : ∀ r ∈ (R : Subgroup A7), (r : Perm (Fin 7)) * τ = τ * (r : Perm (Fin 7)))
    {β : MulAut A7} (hβ : ∀ r ∈ (R : Subgroup A7), β r ∈ (R : Subgroup A7)) :
    ∃ r₀ ∈ (R : Subgroup A7), autPerm β = r₀ ∨ autPerm β = r₀ * τ := by
  have hmem : ∀ σ : A7, (∀ r ∈ (R : Subgroup A7),
      (σ : Perm (Fin 7)) * r * (σ : Perm (Fin 7))⁻¹ = autPerm β * r * (autPerm β)⁻¹) →
      σ ∈ (R : Subgroup A7) := fun σ hσ => by
    rw [← normalizer_sylow R]
    refine CFSG.QuasithinUnique.L246.C123.mem_normalizer_of_conj_le fun k hk => ?_
    have h1 : ((σ * k * σ⁻¹ : A7) : Perm (Fin 7)) = ((β k : A7) : Perm (Fin 7)) := by
      rw [coe_apply, ← hσ k hk]
      rfl
    rw [Subtype.ext h1]
    exact hβ k hk
  rcases Int.units_eq_one_or (Perm.sign (autPerm β)) with hs | hs
  · exact ⟨⟨autPerm β, hs⟩, hmem _ fun r _ => rfl, Or.inl rfl⟩
  · have hs' : Perm.sign (autPerm β * τ) = 1 := by
      rw [Perm.sign_mul, hs, hτ]
      rfl
    refine ⟨⟨autPerm β * τ, hs'⟩, hmem _ fun r hr => ?_, Or.inr ?_⟩
    · change autPerm β * τ * r * (autPerm β * τ)⁻¹ = _
      have h1 := hτR r hr
      calc autPerm β * τ * r * (autPerm β * τ)⁻¹ = autPerm β * (τ * r) * τ⁻¹ * (autPerm β)⁻¹ := by
            group
        _ = autPerm β * (r * τ) * τ⁻¹ * (autPerm β)⁻¹ := by rw [h1]
        _ = autPerm β * r * (autPerm β)⁻¹ := by group
    · change autPerm β = autPerm β * τ * τ
      rw [mul_assoc, hτ2, mul_one]

theorem commute_of_fix (α : MulAut A7) (r : A7) (h : α r = r) :
    (r : Perm (Fin 7)) * autPerm α = autPerm α * (r : Perm (Fin 7)) := by
  have h1 := congrArg Subtype.val h
  rw [coe_apply] at h1
  calc (r : Perm (Fin 7)) * autPerm α = autPerm α * r * (autPerm α)⁻¹ * autPerm α := by
        rw [h1]
    _ = autPerm α * (r : Perm (Fin 7)) := by group

theorem commutator_mem_a7 (α β : MulAut A7) : α * β * α⁻¹ * β⁻¹ ∈ innAut5 A7 := by
  rw [mem_innAut5_iff]
  simp only [map_mul, map_inv]
  rw [mul_comm (Perm.sign (autPerm α)) (Perm.sign (autPerm β))]
  group

theorem exists_center_of_inner (α : MulAut A7) (hα : α ∈ innAut5 A7) {k : ℕ}
    (hk : α ^ 2 ^ k = 1) (hfix : ∀ r ∈ (R : Subgroup A7), α r = r) :
    ∃ c ∈ (R : Subgroup A7), (∀ r ∈ (R : Subgroup A7), c * r = r * c) ∧
      α = MulAut.conj c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, rfl⟩ := hα
  have hs : s ^ 2 ^ k = 1 := conj_injective (by rw [map_pow, hk, map_one])
  have hsR : ∀ r ∈ (R : Subgroup A7), s * r = r * s := fun r hr => by
    have h1 := hfix r hr
    rw [MulAut.conj_apply] at h1
    calc s * r = s * r * s⁻¹ * s := by group
      _ = r * s := by rw [h1]
  exact ⟨s, mem_sylow_of_commute R hs hsR, fun r hr => hsR r hr, rfl⟩

theorem centralizer_sylow_a7 (P : Subgroup (MulAut A7))
    (_hP : IsPGroup 2 P) (hPR : ∀ α ∈ P, ∀ r ∈ (R : Subgroup A7), α r = r) :
    (∀ α ∈ P, α * α = 1) ∧ Nat.card P ≤ 4 := by
  have hP2 : ∀ α ∈ P, α * α = 1 := fun α hα => autPerm.injective (by
    rw [map_mul, map_one]
    exact mul_self_of_commute_sylow R fun r hr => commute_of_fix α r (hPR α hα r hr))
  refine ⟨hP2, ?_⟩
  set f : ↥P →* ℤˣ := Perm.sign.comp (autPerm.toMonoidHom.comp P.subtype) with hf
  have hker : Nat.card f.ker ≤ 2 := by
    have hmap : ∀ α : ↥f.ker, ∃ c ∈ (R : Subgroup A7),
        (∀ r ∈ (R : Subgroup A7), c * r = r * c) ∧ (α : MulAut A7) = MulAut.conj c :=
      fun α => by
        have hα : ((α : ↥P) : MulAut A7) ∈ innAut5 A7 := by
          rw [mem_innAut5_iff]
          exact α.2
        exact exists_center_of_inner R _ hα (k := 1)
          (by rw [pow_one, sq]; exact hP2 _ (α : ↥P).2)
          (hPR _ (α : ↥P).2)
    choose c hcR hcZ hcα using hmap
    refine le_trans (Nat.card_le_card_of_injective
      (fun α => (⟨c α, hcR α, mem_centralizer_iff.mpr fun r hr => (hcZ α r hr).symm⟩ :
        ↥((R : Subgroup A7) ⊓ centralizer ((R : Subgroup A7) : Set A7)))) ?_) (card_center_le R)
    intro α β h
    have h1 : c α = c β := congrArg Subtype.val h
    apply Subtype.ext
    apply Subtype.ext
    rw [hcα α, hcα β, h1]
  have hrange : Nat.card f.range ≤ 2 := by
    calc Nat.card f.range ≤ Nat.card ℤˣ := Nat.card_le_card_of_injective _ Subtype.val_injective
      _ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
  calc Nat.card P = Nat.card (↥P ⧸ f.ker) * Nat.card f.ker :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup _
    _ = Nat.card f.range * Nat.card f.ker := by
        rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    _ ≤ 2 * 2 := Nat.mul_le_mul hrange hker
    _ = 4 := by norm_num

end CFSG.ComponentClassification.FooteLit.Aut5A7


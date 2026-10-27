module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingFixedSupport
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem support_of_isPComponent_fixed_conj {m : ℕ} {τ : Perm (Fin m)} (hτ2 : orderOf τ = 2)
    {P : Subgroup (alternatingGroup (Fin m))}
    (hPF : P ≤ fixedSubgroup (MulAut.conjNormal (H := alternatingGroup (Fin m)) τ))
    (hP : IsPComponent 2
      (P.subgroupOf (fixedSubgroup (MulAut.conjNormal (H := alternatingGroup (Fin m)) τ)))) :
    ∀ x ∈ P, ∀ ω : Fin m, τ ω ≠ ω → (x : Perm (Fin m)) ω = ω := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set c := (MulAut.conjNormal (H := alternatingGroup (Fin m)) :
    Perm (Fin m) →* MulAut (alternatingGroup (Fin m))) with hcdef
  have hcapp : ∀ x : alternatingGroup (Fin m), ((c τ x : alternatingGroup (Fin m)) :
      Perm (Fin m)) = τ * x * τ⁻¹ := fun x => rfl
  set Q : Subgroup (Perm (Fin m)) := zpowers τ with hQdef
  have hQ : IsPGroup 2 Q := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hτ2, pow_one])
  set N := normalizer (Q : Set (Perm (Fin m))) with hNdef
  set F := fixedSubgroup (c τ) with hFdef
  have hmemF : ∀ x : alternatingGroup (Fin m), x ∈ F ↔ τ * (x : Perm (Fin m)) = x * τ := by
    intro x
    change c τ x = x ↔ _
    constructor
    · intro hx
      have h1 := congrArg Subtype.val hx
      rw [hcapp] at h1
      calc τ * (x : Perm (Fin m)) = τ * x * τ⁻¹ * τ := by group
        _ = x * τ := by rw [h1]
    · intro hx
      apply Subtype.ext
      rw [hcapp, hx]
      group
  have hcN : ∀ g : Perm (Fin m), τ * g = g * τ → g ∈ N := by
    intro g hg
    apply Subgroup.centralizer_le_normalizer
    rw [hQdef, ← Subgroup.zpowers_le, Subgroup.zpowers_le, mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
    exact (Commute.zpow_left (show Commute τ g from hg) k).eq
  let ι : F →* N := ((alternatingGroup (Fin m)).subtype.comp F.subtype).codRestrict N
    fun x => hcN _ ((hmemF x.1).mp x.2)
  have hι : Function.Injective ι := by
    intro x y hxy
    have h1 : ((x : alternatingGroup (Fin m)) : Perm (Fin m)) =
        ((y : alternatingGroup (Fin m)) : Perm (Fin m)) :=
      congrArg (fun z : N => (z : Perm (Fin m))) hxy
    exact Subtype.ext (Subtype.ext h1)
  set R : Subgroup N := (alternatingGroup (Fin m)).subgroupOf N with hRdef
  have hR : R.Normal := inferInstance
  have hrange : ι.range = R := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact (x : alternatingGroup (Fin m)).2
    · intro y hy
      have hyA : (y : Perm (Fin m)) ∈ alternatingGroup (Fin m) := hy
      have hyτ : (y : Perm (Fin m)) * τ * (y : Perm (Fin m))⁻¹ ∈ Q :=
        (mem_normalizer_iff.mp y.2 τ).mp (mem_zpowers τ)
      have hyτ' : (y : Perm (Fin m)) * τ * (y : Perm (Fin m))⁻¹ = τ := by
        have hord : orderOf ((y : Perm (Fin m)) * τ * (y : Perm (Fin m))⁻¹) = 2 := by
          rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hτ2]
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hyτ
        rw [← hk] at hord ⊢
        rcases Int.emod_two_eq_zero_or_one k with hk2 | hk2
        · rw [← zpow_mod_orderOf, hτ2, show ((2 : ℕ) : ℤ) = 2 from rfl, hk2, zpow_zero,
            orderOf_one] at hord
          omega
        · rw [← zpow_mod_orderOf, hτ2, show ((2 : ℕ) : ℤ) = 2 from rfl, hk2, zpow_one]
      have hcomm : τ * (y : Perm (Fin m)) = (y : Perm (Fin m)) * τ := by
        calc τ * (y : Perm (Fin m)) = (y : Perm (Fin m)) * τ * (y : Perm (Fin m))⁻¹ * y := by
              rw [hyτ']
          _ = (y : Perm (Fin m)) * τ := by group
      exact ⟨⟨⟨y, hyA⟩, (hmemF ⟨y, hyA⟩).mpr hcomm⟩, Subtype.ext rfl⟩
  let e₁ : F ≃* R := (MonoidHom.ofInjective hι).trans (MulEquiv.subgroupCongr hrange)
  set L₀ := P.subgroupOf F with hL₀def
  have hL₁ : IsPComponent 2 (L₀.map e₁.toMonoidHom) :=
    LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 e₁ hP
  have hL := CatalogueBAlternating.pComponent_of_normal_subgroup 2 R (L₀.map e₁.toMonoidHom) hL₁
  set L := (L₀.map e₁.toMonoidHom).map R.subtype with hLdef
  have hsupp := CatalogueBAlternating.normalizer_pComponent_fixedSupport 2 Q hQ L hL
  intro x hx ω hω
  have hxF : x ∈ F := hPF hx
  have hxL : ι ⟨x, hxF⟩ ∈ L := by
    refine ⟨e₁ ⟨x, hxF⟩, ⟨⟨x, hxF⟩, hx, rfl⟩, ?_⟩
    rfl
  have hωQ : ω ∉ MulAction.fixedPoints Q (Fin m) := by
    intro h
    exact hω (h ⟨τ, mem_zpowers τ⟩)
  exact hsupp ⟨ι ⟨x, hxF⟩, hxL⟩ ω hωQ

theorem exists_double_transposition {m : ℕ} {τ : Perm (Fin m)} (hτ : τ * τ = 1)
    (h4 : 4 ≤ τ.support.card) :
    ∃ σ : Perm (Fin m), σ ∈ alternatingGroup (Fin m) ∧ σ * τ = τ * σ ∧ σ ≠ 1 ∧
      σ * σ = 1 ∧ (∀ ω, τ ω = ω → σ ω = ω) ∧ σ.support.card = 4 := by
  classical
  have hττ : ∀ x, τ (τ x) = x := fun x => by rw [← Perm.mul_apply, hτ, Perm.one_apply]
  obtain ⟨a, ha⟩ : τ.support.Nonempty := Finset.card_pos.mp (by omega)
  have ha' : τ a ≠ a := Perm.mem_support.mp ha
  obtain ⟨b, hb⟩ : (τ.support \ {a, τ a}).Nonempty := by
    apply Finset.card_pos.mp
    have h1 : ({a, τ a} : Finset (Fin m)).card ≤ 2 := Finset.card_le_two
    have h2 := Finset.le_card_sdiff ({a, τ a} : Finset (Fin m)) τ.support
    omega
  rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hb
  obtain ⟨hbs, hba, hbτa⟩ := hb
  have hb' : τ b ≠ b := Perm.mem_support.mp hbs
  have hτba : τ b ≠ a := fun h => hbτa (by rw [← h, hττ])
  have hτbτa : τ b ≠ τ a := fun h => hba (τ.injective h)
  set s₁ := swap a (τ a) with hs₁
  set s₂ := swap b (τ b) with hs₂
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  have hcomm : ∀ x, swap x (τ x) * τ = τ * swap x (τ x) := by
    intro x
    rw [Equiv.swap_mul_eq_mul_swap, hτinv, hττ, swap_comm]
  have hdisj : Perm.Disjoint s₁ s₂ := by
    intro y
    by_cases hya : y = a
    · right
      rw [hs₂, swap_apply_of_ne_of_ne (by rw [hya]; exact Ne.symm hba)
        (by rw [hya]; exact Ne.symm hτba)]
    · by_cases hyτa : y = τ a
      · right
        rw [hs₂, swap_apply_of_ne_of_ne (by rw [hyτa]; exact Ne.symm hbτa)
          (by rw [hyτa]; exact Ne.symm hτbτa)]
      · left
        exact swap_apply_of_ne_of_ne hya hyτa
  refine ⟨s₁ * s₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (Ne.symm ha'),
      Perm.sign_swap (Ne.symm hb')]
    decide
  · rw [mul_assoc, hcomm b, ← mul_assoc, hcomm a, mul_assoc]
  · intro h
    have h1 := congrArg (fun p : Perm (Fin m) => p a) h
    simp only [Perm.mul_apply, Perm.one_apply] at h1
    rw [hs₂, swap_apply_of_ne_of_ne (Ne.symm hba) (Ne.symm hτba), hs₁, swap_apply_left] at h1
    exact ha' h1
  · calc s₁ * s₂ * (s₁ * s₂) = s₁ * (s₂ * s₁) * s₂ := by simp only [mul_assoc]
      _ = s₁ * (s₁ * s₂) * s₂ := by rw [← hdisj.commute.eq]
      _ = (s₁ * s₁) * (s₂ * s₂) := by simp only [mul_assoc]
      _ = 1 := by rw [hs₁, hs₂, swap_mul_self, swap_mul_self, one_mul]
  · intro ω hω
    have hωa : ω ≠ a := fun h => ha' (h ▸ hω)
    have hωτa : ω ≠ τ a := fun h => ha' (by rw [h, hττ] at hω; exact hω.symm)
    have hωb : ω ≠ b := fun h => hb' (h ▸ hω)
    have hωτb : ω ≠ τ b := fun h => hb' (by rw [h, hττ] at hω; exact hω.symm)
    rw [Perm.mul_apply, hs₂, swap_apply_of_ne_of_ne hωb hωτb, hs₁,
      swap_apply_of_ne_of_ne hωa hωτa]
  · rw [hdisj.card_support_mul, hs₁, hs₂, Perm.card_support_swap (Ne.symm ha'),
      Perm.card_support_swap (Ne.symm hb')]

end CFSG.ComponentClassification.SolMax

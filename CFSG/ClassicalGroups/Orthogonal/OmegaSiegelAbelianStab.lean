module

public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelMinusThreePoint

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaSiegel

open CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.GF2n.Smith81
open CFSG.RankThree.OrthogonalInvolutions QuadraticMap Module

section Levi

variable {K : Type*} [Field K] {N : Type*} [AddCommGroup N] [Module K N] {Q : QuadraticForm K N}

private def LeviDec (P : HypPair Q) (g h : N ≃ₗ[K] N) : Prop :=
  h ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ h P.e = P.e ∧ h P.f = P.f ∧
    ∃ s ∈ rootGroup Q P.e, g = s * h

private theorem LeviDec.unique {P : HypPair Q} {g h₁ h₂ : N ≃ₗ[K] N} (h1 : LeviDec P g h₁)
    (h2 : LeviDec P g h₂) : h₁ = h₂ := by
  obtain ⟨-, -, hf1, s₁, hs₁, hg1⟩ := h1
  obtain ⟨-, -, hf2, s₂, hs₂, hg2⟩ := h2
  have hmem : s₂⁻¹ * s₁ ∈ rootGroup Q P.e := mul_mem (inv_mem hs₂) hs₁
  have heq : s₂⁻¹ * s₁ = h₂ * h₁⁻¹ := by
    have h12 : s₁ * h₁ = s₂ * h₂ := hg1.symm.trans hg2
    calc s₂⁻¹ * s₁ = s₂⁻¹ * (s₁ * h₁) * h₁⁻¹ := by group
      _ = h₂ * h₁⁻¹ := by rw [h12]; group
  have hf1' : h₁⁻¹ P.f = P.f := by
    conv_lhs => rw [← hf1]
    exact LinearEquiv.inv_apply_apply' h₁ P.f
  have hfix : (s₂⁻¹ * s₁) P.f = P.f := by
    rw [heq, LinearEquiv.mul_apply, hf1', hf2]
  have h1 := eq_one_of_mem_rootGroup_of_apply_eq P.Q_e
    (by rw [P.polar_ef]; exact one_ne_zero) hmem hfix
  have hss : s₁ = s₂ := by
    simpa using congrArg (s₂ * ·) h1
  rw [hss] at hg1
  exact mul_left_cancel (hg1.symm.trans hg2)

private theorem LeviDec.eq_one_iff {P : HypPair Q} {g h : N ≃ₗ[K] N} (hg : LeviDec P g h) :
    h = 1 ↔ g ∈ rootGroup Q P.e := by
  constructor
  · rintro rfl
    obtain ⟨-, -, -, s, hs, rfl⟩ := hg
    rwa [mul_one]
  · intro hmem
    exact hg.unique ⟨one_mem _, rfl, rfl, g, hmem, (mul_one g).symm⟩

private theorem LeviDec.apply_eq_of_commute (hnd : (polarBilin Q).Nondegenerate) {P : HypPair Q}
    {g h a : N ≃ₗ[K] N} (hg : LeviDec P g h) {x : N} (hx1 : polar Q P.e x = 0)
    (hx2 : polar Q P.f x = 0) (hax : eichler Q P.e x = a) (hcomm : g * a = a * g) : h x = x := by
  obtain ⟨hO, he, hf, s, hs, rfl⟩ := hg
  subst hax
  have hhx1 : polar Q P.e (h x) = 0 := by
    have := polar_map_of_mem hO P.e x
    rwa [he, hx1] at this
  have hhx2 : polar Q P.f (h x) = polar Q P.f x := by
    have := polar_map_of_mem hO P.f x
    rwa [hf] at this
  have hconj : h * eichler Q P.e x * h⁻¹ = eichler Q P.e (h x) := by
    rw [eichler_conj hO, he]
  have hkey : eichler Q P.e x = eichler Q P.e (h x) := by
    calc eichler Q P.e x = s * h * eichler Q P.e x * (s * h)⁻¹ := by
          rw [hcomm, mul_inv_cancel_right]
      _ = s * (h * eichler Q P.e x * h⁻¹) * s⁻¹ := by group
      _ = eichler Q P.e (h x) := by
          rw [hconj, rootGroup_commute hs (eichler_mem_rootGroup hhx1), mul_inv_cancel_right]
  obtain ⟨c, hc⟩ := (eichler_eq_eichler_iff hnd P.Q_e P.e_ne_zero hx1 hhx1).mp hkey
  have hc0 : c = 0 := by
    have := congrArg (polar Q P.f) hc
    rw [polar_add_right, polar_smul_right_eq, hhx2, hx2, P.polar_fe] at this
    simpa using this.symm
  rw [hc, hc0, zero_smul, add_zero]

private theorem natCard_ker_le [Finite N] (hnd : (polarBilin Q).Nondegenerate) {P : HypPair Q}
    {A : Subgroup (N ≃ₗ[K] N)} (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {ψ : ↥A →* (N ≃ₗ[K] N)} (hψ : ∀ g : A, LeviDec P g (ψ g)) :
    Nat.card ψ.ker ≤
      Nat.card {x : N // polar Q P.e x = 0 ∧ polar Q P.f x = 0 ∧ ∀ b ∈ ψ.range, b x = x} := by
  have hex : ∀ a : ψ.ker, ∃ x : N, polar Q P.e x = 0 ∧ polar Q P.f x = 0 ∧
      eichler Q P.e x = ((a : ↥A) : N ≃ₗ[K] N) := by
    rintro ⟨a, ha⟩
    obtain ⟨y, hy, hya⟩ := mem_rootGroup.mp ((hψ a).eq_one_iff.mp (MonoidHom.mem_ker.mp ha))
    refine ⟨y + (-polar Q y P.f) • P.e, ?_, ?_, ?_⟩
    · rw [polar_add_right, hy, polar_smul_right_eq, P.polar_ee]
      ring
    · rw [polar_add_right, polar_smul_right_eq, P.polar_fe, polar_comm Q P.f y]
      ring
    · rw [eichler_add_smul_self P.Q_e, hya]
  choose x hx1 hx2 hxa using hex
  have hfix : ∀ (a : ψ.ker), ∀ b ∈ ψ.range, b (x a) = x a := by
    intro a b hb
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hb
    exact (hψ g).apply_eq_of_commute hnd (hx1 a) (hx2 a) (hxa a) (hAc _ g.2 _ a.1.2)
  refine Nat.card_le_card_of_injective (fun a => ⟨x a, hx1 a, hx2 a, hfix a⟩) fun a₁ a₂ h => ?_
  have h' : x a₁ = x a₂ := congrArg Subtype.val h
  exact Subtype.ext (Subtype.ext (by rw [← hxa a₁, ← hxa a₂, h']))

end Levi

section Quadratic

open CFSG.HardMathSupport.Kantor79 CFSG.ClassicalGroups.Orthogonal.SiegelRT1

variable {K' : Type*} [Field K'] [CharP K' 2] [Finite K'] {N : Type*} [AddCommGroup N]
  [Module K' N] [FiniteDimensional K' N] {QN : QuadraticForm K' N} {K : Type*} [Field K]
  [CharP K 2] [Finite K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Qf : QuadraticForm K V} {ρ : ↥(elementaryGroup QN) →* (V ≃ₗ[K] V)}

theorem OmegaSetting.rhoE_apply_sub_eq (hs : OmegaSetting QN Qf ρ)
    (htop : commutatorSpace ρ.range = ⊤) (hfix : ∀ x : V, (∀ g, ρ g x = x) → x = 0)
    (hK : 2 < Nat.card K') {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v)
    (h8 : finrank K V = 8) {a w w' : N} (ha : QN a = 0) (ha0 : a ≠ 0) (haw : polar QN a w = 0)
    (haw' : polar QN a w' = 0) (x : V) :
    rhoE ρ a w (rhoE ρ a w' x - x) = rhoE ρ a w' x - x := by
  have hle : movedSpace (rhoE ρ a w') ≤
      ⨆ (y : N) (_ : polar QN a y = 0), movedSpace (rhoE ρ a y) :=
    le_iSup₂_of_le (f := fun y (_ : polar QN a y = 0) => movedSpace (rhoE ρ a y)) w' haw' le_rfl
  exact (hs.forall_rhoE_apply_eq_iff_mem_iSup htop hfix hK hF h8 ha ha0 _).mpr
    (hle (sub_mem_movedSpace _ x)) w haw

end Quadratic

end CFSG.ClassicalGroups.Orthogonal.OmegaSiegel

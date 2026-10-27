module

public import CFSG.LieType.SemisimpleCentralizers.HeldLangCoverLift

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldLang

open CFSG.Open

variable {Cov L X : Type} [Group Cov] [Group L] [Group X]

theorem card_eq_mul_card_ker {G : Type} [Group G] (q : G →* X) (hq : Function.Surjective q) :
    Nat.card G = Nat.card X * Nat.card q.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup q.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q hq).toEquiv]

theorem exists_fixed_elemAbelian_of_cover [Finite Cov] [Finite L]
    (qC : Cov →* X) (qL : L →* X) (hC : Function.Surjective qC) (hL : Function.Surjective qL)
    (hcC : qC.ker ≤ Subgroup.center Cov) (hcL : qL.ker ≤ Subgroup.center L)
    (hperfC : Group.IsPerfect Cov) (hperfL : Group.IsPerfect L)
    (hsec : ∀ (E : Type) [Group E] [Finite E] (π : E →* Cov), Function.Surjective π →
      π.ker ≤ Subgroup.center E → ∃ s : Cov →* E, ∀ g, π (s g) = g)
    (hker : Nat.card qC.ker ≤ Nat.card qL.ker)
    (β : MulAut L) (τ : MulAut Cov) (βb τb ψ : MulAut X)
    (hβ : ∀ x, qL (β x) = βb (qL x)) (hτ : ∀ x, qC (τ x) = τb (qC x))
    (hψ : ψ * βb * ψ⁻¹ = τb) {m : ℕ} (E : Subgroup Cov)
    (hE : E ≤ MonoidHom.eqLocus τ.toMonoidHom (MonoidHom.id _)) (hEab : IsElemAbelian 3 E)
    (hEcard : Nat.card E = 3 ^ m) :
    ∃ E' : Subgroup L, E' ≤ MonoidHom.eqLocus β.toMonoidHom (MonoidHom.id _) ∧ IsElemAbelian 3 E' ∧
      Nat.card E' = 3 ^ m := by
  haveI := hperfC
  haveI := hperfL
  obtain ⟨φ, hφ, hφs⟩ := exists_surjective_lift qC qL hC hL hcL hperfL hsec
  have hle : Nat.card Cov ≤ Nat.card L := by
    rw [card_eq_mul_card_ker qC hC, card_eq_mul_card_ker qL hL]
    exact Nat.mul_le_mul_left _ hker
  let Φ : Cov ≃* L := MulEquiv.ofBijective φ (hφs.bijective_of_nat_card_le hle)
  have hΦ : ∀ x, qL (Φ x) = qC x := hφ
  obtain ⟨ψ', hψ'⟩ := exists_automorphism_lift qC hC hcC hperfC hsec ψ
  let β' : MulAut Cov := Φ.trans (β.trans Φ.symm)
  have hβ'x : ∀ x, β' x = Φ.symm (β (Φ x)) := fun x => rfl
  have hβ' : ∀ x, qC (β' x) = βb (qC x) := fun x => by
    rw [← hΦ, hβ'x, Φ.apply_symm_apply, hβ, hΦ]
  have hψ'inv : ∀ y, qC (ψ'⁻¹ y) = ψ⁻¹ (qC y) := fun y => by
    have h1 : qC y = ψ (qC (ψ'⁻¹ y)) := by
      conv_lhs => rw [← ψ'.apply_symm_apply y]
      exact hψ' _
    rw [h1]
    exact (ψ.symm_apply_apply _).symm
  have hkey : (ψ' * β' * ψ'⁻¹).toMonoidHom = τ.toMonoidHom := by
    refine eq_of_central_displacement _ _ fun x => hcC ?_
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    show (qC (τ x))⁻¹ * qC (ψ' (β' (ψ'⁻¹ x))) = 1
    rw [hψ', hβ', hψ'inv, hτ]
    have h2 : ψ (βb (ψ⁻¹ (qC x))) = τb (qC x) := by
      rw [← hψ]
      rfl
    rw [h2, inv_mul_cancel]
  have hkey' : ∀ y, ψ' (β' (ψ'⁻¹ y)) = τ y := fun y => congrArg (fun f : Cov →* Cov => f y) hkey
  refine ⟨(E.map ψ'⁻¹.toMonoidHom).map Φ.toMonoidHom, ?_,
    isElemAbelian_map_of_injective _ (isElemAbelian_map_of_injective _ hEab), ?_⟩
  · rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
    show β (Φ (ψ'⁻¹ e)) = Φ (ψ'⁻¹ e)
    have h1 : β' (ψ'⁻¹ e) = ψ'⁻¹ e := by
      have h2 : ψ' (β' (ψ'⁻¹ e)) = e := by rw [hkey' e]; exact hE he
      calc β' (ψ'⁻¹ e) = ψ'⁻¹ (ψ' (β' (ψ'⁻¹ e))) := (ψ'.symm_apply_apply _).symm
        _ = ψ'⁻¹ e := by rw [h2]
    have h3 : β (Φ (ψ'⁻¹ e)) = Φ (β' (ψ'⁻¹ e)) := by
      rw [hβ'x, Φ.apply_symm_apply]
    rw [h3, h1]
  · rw [Subgroup.card_map_of_injective (f := Φ.toMonoidHom) Φ.injective,
      Subgroup.card_map_of_injective (f := ψ'⁻¹.toMonoidHom) ψ'⁻¹.injective, hEcard]

end CFSG.LieType.SemisimpleCentralizers.HeldLang

module

public import CFSG.LargeExtraspecial.AS35TFOdd
public import CFSG.LargeExtraspecial.S12Five

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace Setting

namespace AS35T

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem pow_apply_eq_of_apply_eq {σ : S.O} {v : S.Qt} (h : (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (j : ℕ) : ((σ ^ j : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ]
    change ((σ ^ j : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v
    rw [h, ih]

theorem fiveEight (hS : S.SixHyp) {g : G} (ht : g * S.z * g⁻¹ ∈ S.DSet)
    (htM : g * S.z * g⁻¹ ∈ S.M) (X : Subgroup S.O) (hXM : X ≤ S.Mbar)
    (hXt : ∀ x ∈ X, x * S.ρ ⟨_, htM⟩ = S.ρ ⟨_, htM⟩ * x)
    (hXP : ∀ p ∈ ((S.Qa g ⊓ S.M).subgroupOf S.M).map S.ρ, ∀ x ∈ X, p * x * p⁻¹ ∈ X)
    (hOE : CFSG.oddCore X ⊔ CFSG.layer X = ⊤) : Nat.card X ≤ 3 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set τ : S.O := S.ρ ⟨_, htM⟩ with hτ
  set τL : S.Qt ≃ₗ[ZMod 2] S.Qt := (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) with hτL
  set P := ((S.Qa g ⊓ S.M).subgroupOf S.M).map S.ρ with hP
  have hP2 : IsPGroup 2 P := (AS35T.isExtraspecialPGroup_pbar hS ht).1
  set R : Subgroup X := P.subgroupOf X with hR
  have hRn : R.Normal := by
    refine ⟨fun r hr a => ?_⟩
    rw [hR, mem_subgroupOf] at hr ⊢
    exact AS35T.conj_mem_pbar_of_commute hS ht htM (hXM a.2) (hXt a a.2) hr
  have hR2 : IsPGroup 2 R := hP2.comap_of_injective X.subtype X.subtype_injective
  have hRsol : Group.IsSolvable R := by
    have := hR2.isNilpotent
    infer_instance
  have hOR : CFSG.oddCore X ⊓ R = ⊥ := by
    have h1 : IsPGroup 2 (CFSG.oddCore X ⊓ R : Subgroup X) := hR2.to_le inf_le_right
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h1
    have h2 : Nat.card (CFSG.oddCore X ⊓ R : Subgroup X) ∣ Nat.card (CFSG.oddCore X) :=
      Subgroup.card_dvd_of_le inf_le_left
    have h3 := CFSG.ABGLocalTools.odd_card_oddCore (H := X)
    rw [hk] at h2
    have hk0 : k = 0 := by
      by_contra hk0
      exact (Nat.not_even_iff_odd.mpr h3) (even_iff_two_dvd.mpr ((dvd_pow_self 2 hk0).trans h2))
    rw [hk0, pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq _ hk
  have hRcomm : ∀ a : X, ∀ r ∈ R, a * r = r * a := by
    have hO : CFSG.oddCore X ≤ centralizer (R : Set X) := by
      rw [← commutator_eq_bot_iff_le_centralizer, eq_bot_iff, ← hOR]
      exact Subgroup.commutator_le_inf _ _
    have hE : CFSG.layer X ≤ centralizer (R : Set X) := by
      rw [← commutator_eq_bot_iff_le_centralizer]
      exact (CFSG.LocalCores.component_solvable_centralizer hRsol hRn.isSubnormal).2
    intro a r hr
    have ha : a ∈ centralizer (R : Set X) := by
      have h1 : (⊤ : Subgroup X) ≤ centralizer (R : Set X) := hOE ▸ sup_le hO hE
      exact h1 (mem_top a)
    exact (mem_centralizer_iff.mp ha r hr).symm
  have hB : ∀ σ ∈ X, ∀ m : ℕ, Odd m → σ ^ m = 1 → ∀ p ∈ P, σ * p = p * σ := by
    intro σ hσ m hm hσm p hp
    have hcX : σ * p * σ⁻¹ * p⁻¹ ∈ X := by
      rw [show σ * p * σ⁻¹ * p⁻¹ = σ * (p * σ⁻¹ * p⁻¹) by group]
      exact X.mul_mem hσ (hXP p hp _ (X.inv_mem hσ))
    have hcP : σ * p * σ⁻¹ * p⁻¹ ∈ P :=
      P.mul_mem (AS35T.conj_mem_pbar_of_commute hS ht htM (hXM hσ) (hXt σ hσ) hp) (P.inv_mem hp)
    have hcomm := hRcomm ⟨σ, hσ⟩ ⟨_, hcX⟩ (mem_subgroupOf.mpr hcP)
    obtain ⟨b, hb⟩ := hP2 ⟨_, hcP⟩
    exact AS35T.commute_of_pow_odd_of_comm_pow_two hm hσm (congrArg Subtype.val hcomm)
      (congrArg Subtype.val hb)
  have hD : ∀ σ ∈ X, (∀ v ∈ commSpace τL, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) →
      ∃ e : ℕ, σ ^ 2 ^ e = 1 := by
    intro σ hσ hfix
    obtain ⟨e, n', hn', hσn⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos σ).ne' 2 (by norm_num)
    have hodd : Odd n' := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hn')
    refine ⟨e, ?_⟩
    have h1 : (σ ^ 2 ^ e) ^ n' = 1 := by rw [← pow_mul, ← hσn, pow_orderOf_eq_one]
    have hσX : σ ^ 2 ^ e ∈ X := X.pow_mem hσ _
    exact AS35T.eq_one_of_odd_of_commute_pbar hS ht htM (hXM hσX) (hXt _ hσX) hodd h1
      (hB _ hσX n' hodd h1) (fun v hv => AS35T.pow_apply_eq_of_apply_eq (hfix v hv) _)
  have hmaps : ∀ σ : X, ∀ v ∈ commSpace τL, ((σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ commSpace τL :=
    fun σ v hv => apply_mem_commSpace_of_commute (hXt σ σ.2) hv
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : X →* Equiv.Perm (commSpace τL), ∀ σ : X, ∀ v : commSpace τL,
      ((Φ σ v : commSpace τL) : S.Qt) = ((σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
    let f : X → Equiv.Perm (commSpace τL) := fun σ =>
      { toFun := fun v => ⟨((σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v, hmaps σ v v.2⟩
        invFun := fun v => ⟨(((σ⁻¹ : X) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v, hmaps σ⁻¹ v v.2⟩
        left_inv := fun v => Subtype.ext (by
          change (((σ⁻¹ * σ : X) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v
          rw [inv_mul_cancel]
          rfl)
        right_inv := fun v => Subtype.ext (by
          change (((σ * σ⁻¹ : X) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v
          rw [mul_inv_cancel]
          rfl) }
    exact ⟨{ toFun := f
             map_one' := Equiv.ext fun v => Subtype.ext rfl
             map_mul' := fun σ₁ σ₂ => Equiv.ext fun v => Subtype.ext rfl }, fun _ _ => rfl⟩
  have hker : ∀ σ : X, σ ∈ Φ.ker →
      ∀ v ∈ commSpace τL, ((σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
    intro σ hσ v hv
    have h1 := congrArg (fun π : Equiv.Perm (commSpace τL) => ((π ⟨v, hv⟩ : commSpace τL) : S.Qt))
      (MonoidHom.mem_ker.mp hσ)
    simp only [Equiv.Perm.coe_one, id_eq] at h1
    rw [hΦ] at h1
    exact h1
  have hK2 : IsPGroup 2 Φ.ker := by
    intro κ
    have hκ : (κ : X) ∈ Φ.ker := κ.2
    have hκX : ((κ : X) : S.O) ∈ X := (κ : X).2
    have h3 := hker (κ : X) hκ
    have h4 := hD ((κ : X) : S.O) hκX
    exact (h4 h3).imp fun e he => Subtype.ext (Subtype.ext (by simpa using he))
  have hcard4 : Nat.card (commSpace τL) = 4 := by
    have hdim : finrank (ZMod 2) (commSpace (S.rhoL htM)) = 2 :=
      (S.fiveOne_two hS.sixFour hS.weak ht htM).1.2.2.2.1
    change Nat.card (commSpace (S.rhoL htM)) = 4
    rw [S.card_submodule, hdim]
    norm_num
  have hPermSol : Group.IsSolvable (Equiv.Perm (commSpace τL)) := by
    apply CFSG.GroupTheory.groups_order_below_sixty_solvable
    rw [Nat.card_perm, hcard4]
    decide
  obtain ⟨n, hn⟩ := (Group.isSolvable_def _).mp hPermSol
  have hEder : ∀ j, CFSG.layer X ≤ derivedSeries X j := by
    intro j
    induction j with
    | zero =>
      rw [derivedSeries_zero]
      exact le_top
    | succ j ih =>
      rw [derivedSeries_succ, ← CFSG.LocalCores.layer_perfect]
      exact commutator_mono ih ih
  have hEK : CFSG.layer X ≤ Φ.ker := by
    rw [← Subgroup.map_eq_bot_iff, eq_bot_iff]
    calc (CFSG.layer X).map Φ ≤ (derivedSeries X n).map Φ := map_mono (hEder n)
      _ ≤ derivedSeries _ n := map_derivedSeries_le_derivedSeries Φ n
      _ = ⊥ := hn
  have hE : CFSG.layer X = ⊥ := by
    have hE2 : IsPGroup 2 (CFSG.layer X) := hK2.to_le hEK
    have := hE2.isNilpotent
    have : Group.IsPerfect (CFSG.layer X) := CFSG.LocalCores.layer_isPerfect
    by_contra hne
    have : Nontrivial (CFSG.layer X) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable (CFSG.layer X) inferInstance
  have hXodd : Odd (Nat.card X) := by
    have h1 : CFSG.oddCore X = ⊤ := by rw [← hOE, hE, sup_bot_eq]
    have h2 := CFSG.ABGLocalTools.odd_card_oddCore (H := X)
    rwa [h1, Subgroup.card_top] at h2
  have hKbot : Φ.ker = ⊥ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hK2
    have h1 : Nat.card Φ.ker ∣ Nat.card X := Subgroup.card_subgroup_dvd_card _
    rw [hk] at h1
    have hk0 : k = 0 := by
      by_contra hk0
      exact (Nat.not_even_iff_odd.mpr hXodd) (even_iff_two_dvd.mpr ((dvd_pow_self 2 hk0).trans h1))
    rw [hk0, pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq _ hk
  have hinj : Function.Injective Φ := (MonoidHom.ker_eq_bot_iff Φ).mp hKbot
  have hdvd := Subgroup.card_dvd_of_injective Φ hinj
  rw [Nat.card_perm, hcard4, show Nat.factorial 4 = 3 * 2 ^ 3 by decide] at hdvd
  have hc : Nat.Coprime (Nat.card X) (2 ^ 3) := (Nat.coprime_two_right.mpr hXodd).pow_right 3
  exact Nat.le_of_dvd (by norm_num) (hc.dvd_of_dvd_mul_right hdvd)

end AS35T

end Setting

end CFSG.LargeExtraspecial

module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6TwoFactorGroup
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBXSp6TwoFactorCore
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBXSp6TensorModule

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.ChevTwoFactor

open Subgroup CFSG.ProperTwoGeneratedCore.PairedTensor
open CFSG.LocalAnalysis.ComponentInitial.SteinbergBX.TensorModel
open CFSG.LocalAnalysis.ComponentInitial.SteinbergBX.TensorModule (commutator_S)

instance isPerfect_S : Group.IsPerfect S := ⟨commutator_S⟩

section Character

variable {Y : Type*} [Group Y] [Finite Y] (D : Subgroup Y) [D.Normal] (Ψ : D ≃* K)

theorem exists_layer_character (hCD : centralizer (D : Set Y) = ⊥) {a : Y} (ha : a * a = 1)
    (hΨa : ∀ (d : Y) (hd : d ∈ D) (hda : a⁻¹ * d * a ∈ D), Ψ ⟨_, hda⟩ = (Ψ ⟨d, hd⟩).swap)
    {J : Subgroup Y} (hJ : ∀ j ∈ J, ∃ g : S, j = (Ψ.symm (g, g) : Y))
    (hJC : J ≤ centralizer ({a} : Set Y)) (hCa : zpowers a ⊔ J = centralizer ({a} : Set Y)) :
    ∃ χ : Y →* Multiplicative (ZMod 2), χ a = Multiplicative.ofAdd 1 ∧ χ.ker = D := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  refine SteinbergBX.TwoFactor.exists_swap_character D Ψ hCD (fun d => ?_) (fun y hy => ?_)
  · have hda : a⁻¹ * (d : Y) * a ∈ D := by
      have := (inferInstance : D.Normal).conj_mem _ d.2 a⁻¹
      rwa [inv_inv] at this
    have h1 := hΨa d d.2 hda
    have h2 : MulAut.conjNormal a d = ⟨_, hda⟩ := Subtype.ext (by
      rw [MulAut.conjNormal_apply]
      change a * (d : Y) * a⁻¹ = a⁻¹ * d * a
      rw [hainv])
    rw [h2, h1]
  · have hyC : y ∈ centralizer ({a} : Set Y) := mem_centralizer_singleton_iff.2 hy
    have hle : zpowers a ≤ normalizer (J : Set Y) := by
      rw [zpowers_le, mem_normalizer_iff]
      intro j
      constructor
      · intro hj
        have hc : j * a = a * j := mem_centralizer_singleton_iff.1 (hJC hj)
        rwa [show a * j * a⁻¹ = j by rw [← hc, mul_inv_cancel_right]]
      · intro hj
        have hc : a * j * a⁻¹ * a = a * (a * j * a⁻¹) := mem_centralizer_singleton_iff.1 (hJC hj)
        have h2 : j = a * j * a⁻¹ := by
          apply mul_left_cancel (a := a)
          calc a * j = a * j * a⁻¹ * a := by group
            _ = a * (a * j * a⁻¹) := hc
        rwa [h2]
    rw [← hCa, ← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hle] at hyC
    obtain ⟨x, hx, j, hj, rfl⟩ := hyC
    obtain ⟨g, rfl⟩ := hJ j hj
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    refine ⟨g, ?_⟩
    have ha2 : a ^ (2 : ℤ) = 1 := by rw [zpow_two, ha]
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
    · left
      show a ^ k * _ = _
      rw [hm, zpow_mul, ha2, one_zpow, one_mul]
    · right
      show a ^ k * _ = _
      rw [hm, zpow_add, zpow_mul, ha2, one_zpow, one_mul, zpow_one]

end Character

section Lift

variable {F : Type*} [Group F] [Finite F] {R : Subgroup F} {Y : Type*} [Group Y]

theorem exists_layer_mulEquiv_Q (θ : F →* Y) (hθker : θ.ker = R)
    (hRodd : Nat.Coprime 2 (Nat.card R)) {Q : Subgroup F} (hQperf : ⁅Q, Q⁆ = Q)
    {D : Subgroup Y} (hQD : Q.map θ = D) (hZ : Q ⊓ R ≤ (center Q).map Q.subtype)
    (Ψ : D ≃* K) :
    ∃ η : Q ≃* K, ∀ (q : Q) (hq : θ q ∈ D), η q = Ψ ⟨θ q, hq⟩ := by
  classical
  have : Group.IsPerfect Q := Subgroup.isPerfect_iff.2 hQperf
  have hmem : ∀ q : Q, θ q ∈ D := fun q => hQD ▸ mem_map_of_mem θ q.2
  let θQ : Q →* D := (θ.comp Q.subtype).codRestrict D hmem
  let η₀ : Q →* K := Ψ.toMonoidHom.comp θQ
  have hη₀ : ∀ q : Q, η₀ q = Ψ ⟨θ q, hmem q⟩ := fun q => rfl
  have hsurj : Function.Surjective η₀ := by
    intro k
    obtain ⟨y, hy⟩ := Ψ.surjective k
    obtain ⟨q, hq, hqy⟩ : (y : Y) ∈ Q.map θ := hQD ▸ y.2
    exact ⟨⟨q, hq⟩, by rw [hη₀, ← hy]; congr 1; exact Subtype.ext hqy⟩
  have hkerR : ∀ q : Q, q ∈ η₀.ker ↔ (q : F) ∈ R := fun q => by
    rw [MonoidHom.mem_ker, hη₀, MulEquiv.map_eq_one_iff, ← hθker, MonoidHom.mem_ker]
    exact Subtype.ext_iff
  have hker : η₀.ker ≤ center Q := fun q hq => by
    obtain ⟨c, hc, hcq⟩ := hZ (mem_inf.2 ⟨q.2, (hkerR q).1 hq⟩)
    rw [show q = c from Subtype.ext hcq.symm]
    exact hc
  have hodd : Odd (Nat.card η₀.ker) := by
    have hdvd : Nat.card η₀.ker ∣ Nat.card R := by
      have hle : η₀.ker.map Q.subtype ≤ R := by
        rintro _ ⟨q, hq, rfl⟩
        exact (hkerR q).1 hq
      have h1 := Subgroup.card_dvd_of_le hle
      rwa [Subgroup.card_map_of_injective Q.subtype_injective] at h1
    rw [Nat.odd_iff]
    have h2 : ¬ 2 ∣ Nat.card η₀.ker := fun h =>
      Nat.Prime.coprime_iff_not_dvd Nat.prime_two |>.1 hRodd (h.trans hdvd)
    omega
  have hcov : ∀ E : Subgroup Q, Group.IsPerfect E → ∀ f : E →* S, Function.Surjective f →
      f.ker ≤ center E → Odd (Nat.card f.ker) → f.ker = ⊥ := fun E hE f hf hfk hfo => by
    have := hE
    exact ker_eq_bot_of_perfect_odd_cover f hf hfk hfo
  have hbot := SteinbergBX.TwoFactor.ker_eq_bot_of_perfect_central_prod η₀ hsurj hker hodd hcov hcov
  have hinj : Function.Injective η₀ := (MonoidHom.ker_eq_bot_iff _).1 hbot
  exact ⟨MulEquiv.ofBijective η₀ ⟨hinj, hsurj⟩, fun q hq => rfl⟩

end Lift

end CFSG.LocalAnalysis.ComponentInitial.ChevTwoFactor

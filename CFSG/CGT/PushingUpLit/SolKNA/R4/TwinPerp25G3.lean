module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25G1
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25SixLift
public import CFSG.ClassicalInvolution.Asc77.AscE186CentB
public import CFSG.ClassicalInvolution.Q3.TL3T16

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516.Four

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Disconnected.AschTight

variable {X : Type} [Group X] [Finite X]

theorem exists_pow_involution {x : X} (hx1 : x ≠ 1) (hk : ∃ k : ℕ, orderOf x = 2 ^ k) :
    ∃ m : ℕ, (x ^ m) * (x ^ m) = 1 ∧ x ^ m ≠ 1 := by
  obtain ⟨k, hk⟩ := hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hx1 (orderOf_eq_one_iff.mp (by simpa using hk))
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  refine ⟨2 ^ j, ?_, ?_⟩
  · rw [← pow_add, ← two_mul, ← pow_succ', ← hk]
    exact pow_orderOf_eq_one x
  · intro h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hk] at h1
    have h2 := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h1
    omega

theorem false_of_twinE4 {K : Subgroup X} {t : X} (hΩ : HypOmegaGen (CoreAssembly.conjClass K))
    (hu : IsUniqueInvolution K t)
    (hq : ∀ P : Subgroup X, IsSylow2In P K → Nonempty (↥P ≃* QuaternionGroup 2))
    (hEC : OddEC t) (hTD : NoCentFour K t)
    {Q : Type} [Group Q] (f : X →* Q) (hf : Function.Surjective f) (hN2 : IsPGroup 2 f.ker)
    (htN : t ∉ f.ker)
    (hoddQ : ∀ w : Q, orderOf w = 2 → Balance.oddCoreIn (Subgroup.centralizer ({w} : Set Q)) = ⊥)
    (hM2 : ∀ w : Q, orderOf w = 2 → ¬ IsPGroup 2 (Subgroup.centralizer ({w} : Set Q))) : False := by
  classical
  haveI : Finite Q := Finite.of_surjective f hf
  obtain ⟨P, hP, -⟩ := IsSylow2In.exists_ge (IsPGroup.of_bot (G := X)) (bot_le : (⊥ : Subgroup X) ≤ K)
  obtain ⟨e⟩ := hq P hP
  have hP8 : Nat.card P = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  obtain ⟨k, hkP, hk4⟩ := exists_orderOf_four_of_uniqueInvolution hu hP.1 hP.2.1 (by omega)
  have hR : P ∈ RSet (CoreAssembly.conjClass K) :=
    mem_RSet_of_isSylow2In (CoreAssembly.mem_conjClass_self K) hP
  have hPN : P ⊓ f.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hN2) ⟨x, hx.2⟩
    have hj' : orderOf x = 2 ^ j := by rwa [Subgroup.orderOf_mk] at hj
    obtain ⟨m, hm2, hm1⟩ := exists_pow_involution hx1 ⟨j, hj'⟩
    have hmK : x ^ m ∈ K := K.pow_mem (hP.1 hx.1) m
    have hmN : x ^ m ∈ f.ker := f.ker.pow_mem hx.2 m
    rcases hu.unique _ hmK hm2 with h | h
    · exact hm1 h
    · rw [h] at hmN
      exact htN hmN
  have hcomm := comm613Gen_normal hΩ hR (inferInstance : f.ker.Normal) hPN
  rw [AscE186.oddCoreOf_eq_bot_of_isPGroup hN2, le_bot_iff] at hcomm
  have hPcent : P ≤ Subgroup.centralizer (f.ker : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hcentC : ∀ a : X, f a * f t = f t * f a → a * t = t * a := by
    intro a ha
    have hn : t⁻¹ * (a * t * a⁻¹) ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv]
      have : f a * f t * (f a)⁻¹ = f t := by rw [ha]; group
      rw [this]
      group
    have hkc : (t⁻¹ * (a * t * a⁻¹)) * k = k * (t⁻¹ * (a * t * a⁻¹)) :=
      (Subgroup.mem_centralizer_iff.mp (hPcent hkP)) _ hn
    have htk : k * t = t * k := TC.Thin.isUniqueInvolution_comm hu (hP.1 hkP)
    by_contra hne
    have hne' : a * t * a⁻¹ ≠ t := fun h => hne (by
      calc a * t = (a * t * a⁻¹) * a := by group
        _ = t * a := by rw [h])
    refine hTD a hne' k (hP.1 hkP) hk4 ?_
    have e1 : a * t * a⁻¹ = t * (t⁻¹ * (a * t * a⁻¹)) := by group
    rw [e1]
    calc t * (t⁻¹ * (a * t * a⁻¹)) * k = t * ((t⁻¹ * (a * t * a⁻¹)) * k) := by rw [mul_assoc]
      _ = t * (k * (t⁻¹ * (a * t * a⁻¹))) := by rw [hkc]
      _ = (t * k) * (t⁻¹ * (a * t * a⁻¹)) := by rw [← mul_assoc]
      _ = (k * t) * (t⁻¹ * (a * t * a⁻¹)) := by rw [htk]
      _ = k * (t * (t⁻¹ * (a * t * a⁻¹))) := by rw [mul_assoc]
  have hCQ : ∀ q ∈ Subgroup.centralizer ({f t} : Set Q),
      ∃ a ∈ Subgroup.centralizer ({t} : Set X), f a = q := by
    intro q hq'
    obtain ⟨a, rfl⟩ := hf q
    exact ⟨a, Subgroup.mem_centralizer_singleton_iff.mpr
      (hcentC a (Subgroup.mem_centralizer_singleton_iff.mp hq')), rfl⟩
  obtain ⟨N', hN'C, hN'odd, hN'norm, hN'all⟩ := hEC
  have hft : orderOf (f t) = 2 := orderOf_eq_prime (by rw [sq, ← map_mul, hu.sq, map_one])
    (fun h => htN (MonoidHom.mem_ker.mpr h))
  have hNq_le : N'.map f ≤ Subgroup.centralizer ({f t} : Set Q) := by
    rintro _ ⟨m, hm, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp (hN'C hm)]
  have hkey : ∀ q ∈ Subgroup.centralizer ({f t} : Set Q), ∀ y ∈ N'.map f,
      q * y * q⁻¹ ∈ N'.map f := by
    intro q hq' y hy
    obtain ⟨a, ha, rfl⟩ := hCQ q hq'
    obtain ⟨m, hm, rfl⟩ := hy
    exact ⟨a * m * a⁻¹, hN'norm a ha m hm, by simp⟩
  have hNq_norm : Subgroup.centralizer ({f t} : Set Q) ≤
      Subgroup.normalizer ((N'.map f : Subgroup Q) : Set Q) := by
    intro q hq'
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hkey q hq' y hy, fun hy => ?_⟩
    have := hkey q⁻¹ (Subgroup.inv_mem _ hq') _ hy
    simpa [mul_assoc] using this
  have hNq_odd : Odd (Nat.card (N'.map f)) := hN'odd.of_dvd_nat (Subgroup.card_map_dvd _ _)
  have hNq_bot : N'.map f = ⊥ := by
    have := Balance.le_oddCoreIn_of_normalizes hNq_le hNq_norm hNq_odd
    rw [hoddQ (f t) hft, le_bot_iff] at this
    exact this
  have hN'triv : ∀ m ∈ N', m = 1 := by
    intro m hm
    have h1 : f m = 1 := by
      have : f m ∈ N'.map f := ⟨m, hm, rfl⟩
      rw [hNq_bot, Subgroup.mem_bot] at this
      exact this
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hN2) ⟨m, MonoidHom.mem_ker.mpr h1⟩
    have hj' : orderOf m = 2 ^ j := by rwa [Subgroup.orderOf_mk] at hj
    have hmodd : Odd (orderOf m) := hN'odd.of_dvd_nat (Subgroup.orderOf_dvd_natCard N' hm)
    have hj0 : j = 0 := by
      by_contra hj0
      have : Even (orderOf m) := by
        rw [hj']
        exact Nat.even_pow.mpr ⟨even_two, hj0⟩
      exact (Nat.not_even_iff_odd.mpr hmodd) this
    rw [hj0, pow_zero] at hj'
    exact orderOf_eq_one_iff.mp hj'
  have h2 : ∀ g : X, g * t = t * g → ∃ k : ℕ, g ^ 2 ^ k = 1 := by
    intro g hg
    exact exists_pow_two_pow_eq_one (C := Subgroup.centralizer ({t} : Set X))
      (fun g hg ho => hN'triv g (hN'all g hg ho)) (Subgroup.mem_centralizer_singleton_iff.mpr hg)
  have hCt2 : IsPGroup 2 (Subgroup.centralizer ({t} : Set X)) := isPGroup_centralizer_of_two_power h2
  have hCQ2 : IsPGroup 2 (Subgroup.centralizer ({f t} : Set Q)) := by
    have heq : Subgroup.centralizer ({f t} : Set Q) = (Subgroup.centralizer ({t} : Set X)).map f := by
      refine le_antisymm (fun q hq' => ?_) ?_
      · obtain ⟨a, ha, rfl⟩ := hCQ q hq'
        exact ⟨a, ha, rfl⟩
      · rintro _ ⟨a, ha, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
          Subgroup.mem_centralizer_singleton_iff.mp ha]
    rw [heq]
    exact hCt2.map f
  exact hM2 (f t) hft hCQ2

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516.Four

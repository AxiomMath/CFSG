module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4BypassCore
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4BypassKer
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4WeylCases
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutStage

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.GH74.GLS.Stage2.OddAut
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem d4_hker_of_abelian {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f))
    {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hz3 : z ^ 3 = 1)
    (e : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hab : ∀ N₀ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      N₀ ≤ fixSub (MulAut.conj z) →
      (∀ f ∈ fixSub (MulAut.conj z), ∀ x ∈ N₀, f * x * f⁻¹ ∈ N₀) →
      (∀ x ∈ N₀, ∀ y ∈ N₀, x * y = y * x) → (∀ c ∈ N₀, e c = c) → N₀ ≤ Subgroup.zpowers z)
    (U₀ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hU : U₀ ≤ fixSub (MulAut.conj z)) (hUp : IsPGroup p U₀)
    (hcard : (p ^ f) ^ 3 ≤ Nat.card U₀) :
    ∀ ζ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), Odd (orderOf ζ) →
      Nat.Coprime (orderOf ζ) 3 → ζ * MulAut.conj z = MulAut.conj z * ζ → ζ * e = e * ζ →
      (∀ c ∈ fixSub (MulAut.conj z), ζ c = c) → ζ = 1 := by
  classical
  intro ζ hodd hcop hcomm hcomme hfix
  have hcen : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hinj : Function.Injective (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    mulAut_conj_injective_of_center_bot hcen
  refine d4PtKer_of_inner_trivial hp hp2 hf K hK σ hσ (MulAut.conj z) e ?_ U₀ hU hUp hcard ζ
    hodd hcop hcomm hcomme hfix
  rintro _ ⟨c₀, rfl⟩ hodd' hcop' hcomm' hcomme' hfix'
  have hc₀z : c₀ * z = z * c₀ := by
    apply hinj
    rw [map_mul, map_mul]
    exact hcomm'
  have hc₀F : c₀ ∈ fixSub (MulAut.conj z) := by
    rw [mem_fixSub, MulAut.conj_apply]
    rw [mul_inv_eq_iff_eq_mul]
    exact hc₀z.symm
  have hec₀ : e c₀ = c₀ := by
    apply hinj
    rw [← mulAut_conj_conj e c₀]
    calc e * MulAut.conj c₀ * e⁻¹ = MulAut.conj c₀ * e * e⁻¹ := by rw [hcomme']
      _ = MulAut.conj c₀ := mul_inv_cancel_right _ _
  have hcF : ∀ x ∈ fixSub (MulAut.conj z), c₀ * x = x * c₀ := by
    intro x hx
    have := hfix' x hx
    rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at this
    exact this
  have hN₀z : Subgroup.zpowers c₀ ≤ Subgroup.zpowers z := by
    refine hab (Subgroup.zpowers c₀) (Subgroup.zpowers_le.2 hc₀F) ?_ ?_ ?_
    · intro f hf x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      have h : c₀ ^ k * f = f * c₀ ^ k :=
        (Commute.zpow_left (show Commute c₀ f from hcF f hf) k).eq
      have h' : f * c₀ ^ k * f⁻¹ = c₀ ^ k := by
        rw [← h]
        group
      rw [h']
      exact Subgroup.zpow_mem_zpowers c₀ k
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      exact (Commute.zpow_zpow_self c₀ i j).eq
    · rintro _ ⟨i, rfl⟩
      have hec : ∀ k : ℤ, e (c₀ ^ k) = c₀ ^ k := fun k => by rw [map_zpow, hec₀]
      exact hec i
  have hmem := hN₀z (Subgroup.mem_zpowers c₀)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hz3' : (MulAut.conj z : MulAut _) ^ 3 = 1 := by
    rw [← map_pow, hz3, map_one]
  have hcube : (MulAut.conj (z ^ k) : MulAut _) ^ 3 = 1 := by
    rw [map_zpow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3', one_zpow]
  have hdvd : orderOf (MulAut.conj (z ^ k) : MulAut _) ∣ 3 := orderOf_dvd_of_pow_eq_one hcube
  have h1 : orderOf (MulAut.conj (z ^ k) : MulAut _) = 1 :=
    Nat.Coprime.eq_one_of_dvd hcop' hdvd
  exact orderOf_eq_one_iff.1 h1

end CFSG.GH74.GLS.Stage2.Bender.Thm1

module

public import CFSG.ClassicalInvolution.Asc77.AscR10Fix
public import CFSG.ClassicalInvolution.Asc77.AscT3XSec

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
open scoped MatrixGroups commutatorElement

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}



theorem Std20.r_false_of_le_inf_centralizer (d : Std20 p f K K' J S R R' W V z t) {g u₁ : G}
    (hI₁ : IsUniqueInvolution (conjSub g K) u₁) (hu₁ : u₁ ≠ z) {R₀ : Subgroup G}
    (hR2 : IsPGroup 2 R₀) (hRnc : ∃ x ∈ R₀, ∃ y ∈ R₀, x * y ≠ y * x) (hR8 : 2 < Nat.card R₀)
    (hRK : R₀ ≤ K) (hRz : R₀ ≤ Subgroup.centralizer ({u₁} : Set G)) : False := by
  have hΩ := d.hyp
  have hI := d.viol.hzK
  have hJ₁ : conjSub g K ∈ CoreAssembly.conjClass K := ⟨g, rfl⟩
  have hJ₂ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hJne : conjSub g K ≠ K := fun h => hu₁ (by
    have hm := hI₁.mem
    rw [h] at hm
    exact (hI.unique _ hm hI₁.sq).resolve_left hI₁.ne_one)
  have htwin : K ∉ twinSet (CoreAssembly.conjClass K) (conjSub g K) := by
    rintro ⟨-, w, hw₁, hw₂⟩
    exact hu₁ ((hI₁.eq hw₁).trans (hI.eq hw₂).symm)
  obtain ⟨V₀, hV, hRV⟩ := IsSylow2In.exists_ge hR2 (le_inf hRK hRz)
  have hzV : z ∈ V₀ := hRV (mem_of_le_member hI hRK hR2 (by omega))
  have hcard : Nat.card R₀ ≤ Nat.card V₀ := Subgroup.card_le_of_le hRV
  rcases Asc77.l6_2 p f d.branch.odd d.branch.five G _ hΩ _ hJ₁ _ hI₁ _ hJ₂ htwin _
    hI V₀ hV hzV with ⟨hV1, -⟩ | ⟨hV1, -⟩ | ⟨hV3, -⟩ | ⟨hV4, hVc⟩
  · rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [_root_.sq]; exact hI.sq)
      hI.ne_one] at hcard
    omega
  · rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [_root_.sq]; exact hI.sq)
      hI.ne_one] at hcard
    omega
  · obtain ⟨-, -, -, hcyc, -⟩ := hV3
    obtain ⟨x, hx, y, hy, hxy⟩ := hRnc
    exact hxy (commute_of_isCyclic hcyc (hRV hx) (hRV hy))
  · have hVJ₂ : V₀ ≤ K := hV.1.trans inf_le_left
    have hVN : V₀ ≤ Subgroup.normalizer (conjSub g K : Set G) :=
      le_normalizer_of_commutator_le (hVc.trans (oddCoreOf_le_self _))
    have hnbr : K ∈ omegaNbr (CoreAssembly.conjClass K) (conjSub g K) :=
      ⟨hJ₂, hJne.symm, V₀, hV4, hVJ₂, hVN⟩
    have h1 := omegaNbr_conj hΩ.conjInvariant hnbr g⁻¹
    rw [conjSub_inv_conjSub] at h1
    have h2 := d.late_nbr _ h1
    have h3 := twinSet_conj hΩ.conjInvariant h2 g
    rw [conjSub_conjSub_inv] at h3
    exact htwin h3


theorem Std20.r_conj_of_centralizes (d : Std20 p f K K' J S R R' W V z t) {a : G}
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    {t' : ↥(Subgroup.centralizer ({a} : Set G))} (ht2 : t' * t' = 1)
    (ht : ∃ g : G, (t' : G) = g * z * g⁻¹)
    {Q : Subgroup ↥(Subgroup.centralizer ({a} : Set G))} (hQ2 : IsPGroup 2 Q)
    (hQK : Q ≤ perfectCoreIn K a) (hQnc : ∃ x ∈ Q, ∃ y ∈ Q, x * y ≠ y * x)
    (hfix : ∀ q ∈ Q, t'⁻¹ * (q * t' * q⁻¹) ∈
      classicalInvolutionOddCore ↥(Subgroup.centralizer ({a} : Set G))) :
    ∃ o ∈ classicalInvolutionOddCore ↥(Subgroup.centralizer ({a} : Set G)),
      t' = o * ⟨z, hzA⟩ * o⁻¹ := by
  obtain ⟨v, hvN, hv⟩ := R10.r_exists_conj_centralizes_of_odd
    (CFSG.ComponentClassification.OddCore.odd_card _) hQ2 ht2 hfix
  set t'' : ↥(Subgroup.centralizer ({a} : Set G)) := v * t' * v⁻¹ with ht''
  by_cases hzz : (t'' : G) = z
  · refine ⟨v⁻¹, Subgroup.inv_mem _ hvN, ?_⟩
    have h1 : t'' = ⟨z, hzA⟩ := Subtype.ext hzz
    rw [← h1, ht'']
    group
  · exfalso
    obtain ⟨g, hg⟩ := ht
    set g'' : G := (v : G) * g with hg''
    have hu : (t'' : G) = g'' * z * g''⁻¹ := by
      rw [ht'', Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hg, hg'']
      group
    have hI₁ : IsUniqueInvolution (conjSub g'' K) (t'' : G) := by
      have := d.viol.hzK.conj g''
      rwa [← hu] at this
    have hmapK : (perfectCoreIn K a).map (Subgroup.centralizer ({a} : Set G)).subtype ≤ K := by
      have h1 := map_conjSub_perfectCore (K := K) (a := a) 1
      rw [conjSub_one, Subgroup.coe_one, conjSub_one] at h1
      rw [h1]
      exact (perfectResidualOf_le _).trans inf_le_left
    have hcard : Nat.card ↥(Q.map (Subgroup.centralizer ({a} : Set G)).subtype) = Nat.card Q :=
      (Nat.card_congr (Subgroup.equivMapOfInjective Q _
        (Subgroup.centralizer ({a} : Set G)).subtype_injective).toEquiv).symm
    refine d.r_false_of_le_inf_centralizer hI₁ hzz
      (hQ2.map (Subgroup.centralizer ({a} : Set G)).subtype) ?_ ?_ ?_ ?_
    · obtain ⟨x, hx, y, hy, hxy⟩ := hQnc
      exact ⟨x, Subgroup.mem_map_of_mem _ hx, y, Subgroup.mem_map_of_mem _ hy,
        fun h => hxy (Subtype.ext h)⟩
    · rw [hcard]
      exact two_lt_card_of_noncomm hQnc
    · exact (Subgroup.map_mono hQK).trans hmapK
    · rintro _ ⟨q, hq, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (hv q hq)


theorem Std20.r_nbr_twin (d : Std20 p f K K' J S R R' W V z t) {a : G} {e₀ : ℕ}
    (h5 : 5 ≤ p ^ e₀) (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hL : IsClassicalMember p e₀ (perfectCoreIn K a) ⟨z, hzA⟩) :
    ∀ M₁ ∈ conjFamily (perfectCoreIn K a), ∀ M₂ ∈ omegaNbr (conjFamily (perfectCoreIn K a)) M₁,
      M₂ ∈ twinSet (conjFamily (perfectCoreIn K a)) M₁ := by
  have hzKa : z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)) :=
    Subgroup.mem_subgroupOf.mp hL.mem
  rintro _ ⟨c₁, rfl⟩ M₂ ⟨hM₂, hne, R₀, hR, hRle, hRN⟩
  obtain ⟨c₂, rfl⟩ := hM₂
  by_cases htwin : conjSub (c₂ : G) K ∈ twinSet (CoreAssembly.conjClass K) (conjSub (c₁ : G) K)
  · obtain ⟨-, w, hw₁, hw₂⟩ := htwin
    have e₁ := (d.viol.hzK.conj (c₁ : G)).eq hw₁
    have e₂ := (d.viol.hzK.conj (c₂ : G)).eq hw₂
    have e : c₁ * ⟨z, hzA⟩ * c₁⁻¹ = c₂ * ⟨z, hzA⟩ * c₂⁻¹ := Subtype.ext (e₁.trans e₂.symm)
    refine ⟨⟨c₂, rfl⟩, c₁ * ⟨z, hzA⟩ * c₁⁻¹, d.x_isUniqueInvolution_conjSub hzA hzKa c₁, ?_⟩
    rw [e]
    exact d.x_isUniqueInvolution_conjSub hzA hzKa c₂
  · exfalso
    obtain ⟨⟨x, hx, y, hy, hxy⟩, h8⟩ := exists_ne_comm_of_mem_rSet d.branch.odd h5 hL hR
    have hR2 := isPGroup_of_mem_rSet hR
    have hne' : conjSub (c₁ : G) (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) ≠
        conjSub (c₂ : G) (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) := by
      intro h
      apply hne
      apply Subgroup.map_injective (Subgroup.centralizer ({a} : Set G)).subtype_injective
      rw [map_conjSub_perfectCore, map_conjSub_perfectCore, h]
    refine d.x_false_of_le_normalizer hzKa c₁.2 c₂.2 hne' htwin
      (hR2.map (Subgroup.centralizer ({a} : Set G)).subtype)
      ⟨(x : G), Subgroup.mem_map_of_mem _ hx, (y : G), Subgroup.mem_map_of_mem _ hy,
        fun h => hxy (Subtype.ext h)⟩ ?_ ?_ ?_
    · rw [← Nat.card_congr (Subgroup.equivMapOfInjective R₀ _
        (Subgroup.centralizer ({a} : Set G)).subtype_injective).toEquiv]
      omega
    · rw [← map_conjSub_perfectCore]
      exact Subgroup.map_mono hRle
    · rw [← map_conjSub_perfectCore]
      exact (Subgroup.map_mono hRN).trans (Subgroup.le_normalizer_map _)

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII

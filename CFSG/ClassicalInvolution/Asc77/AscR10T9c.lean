module

public import CFSG.ClassicalInvolution.Asc77.AscR10T9b
public import CFSG.ClassicalInvolution.Asc77.AscR10Lz
public import CFSG.ClassicalInvolution.Uniform.UHypOmegaGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ClassicalInvolution.Asc77.T3CII.T3R CFSG.ClassicalInvolution.Asc77.AscL62
open scoped MatrixGroups commutatorElement

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}



open CFSG.ClassicalInvolution.Uniform

theorem Std20.t9_false_of_le_normalizer (d : Std20 p f K K' J S R R' W V z t) {a : G}
    (hzKa : z ∈ (K ⊓ Subgroup.centralizer ({a} : Set G))) {c₁ c₂ : G}
    (hc₁ : c₁ ∈ Subgroup.centralizer ({a} : Set G))
    (hc₂ : c₂ ∈ Subgroup.centralizer ({a} : Set G))
    (hne : conjSub c₁ ((K ⊓ Subgroup.centralizer ({a} : Set G))) ≠
      conjSub c₂ ((K ⊓ Subgroup.centralizer ({a} : Set G))))
    (htwin : conjSub c₂ K ∉ twinSet (CoreAssembly.conjClass K) (conjSub c₁ K))
    {R₀ : Subgroup G} (hR2 : IsPGroup 2 R₀) (hRnc : ∃ x ∈ R₀, ∃ y ∈ R₀, x * y ≠ y * x)
    (hR8 : 2 < Nat.card R₀)
    (hRle : R₀ ≤ conjSub c₂ ((K ⊓ Subgroup.centralizer ({a} : Set G))))
    (hRN : R₀ ≤ Subgroup.normalizer
      ((conjSub c₁ ((K ⊓ Subgroup.centralizer ({a} : Set G))) : Subgroup G) :
        Set G)) : False := by
  have hI := d.viol.hzK
  have hΩ := d.hyp
  have hKaK : (K ⊓ Subgroup.centralizer ({a} : Set G)) ≤ K := inf_le_left
  have hJ₁ : conjSub c₁ K ∈ CoreAssembly.conjClass K := ⟨c₁, rfl⟩
  have hJ₂ : conjSub c₂ K ∈ CoreAssembly.conjClass K := ⟨c₂, rfl⟩
  have hI₁ := hI.conj c₁
  have hI₂ := hI.conj c₂
  have hJne : conjSub c₁ K ≠ conjSub c₂ K := fun h => hne (conjSub_cross_eq hc₁ hc₂ h)
  have hRz : R₀ ≤ Subgroup.centralizer ({c₁ * z * c₁⁻¹} : Set G) := by
    intro x hx
    have h1 : x * (c₁ * z * c₁⁻¹) * x⁻¹ ∈
        conjSub c₁ ((K ⊓ Subgroup.centralizer ({a} : Set G))) :=
      (Subgroup.mem_normalizer_iff.mp (hRN hx) _).mp (conj_mem_conjSub hzKa)
    have h2 : x * (c₁ * z * c₁⁻¹) * x⁻¹ ∈ conjSub c₁ K := Subgroup.map_mono hKaK h1
    have h3 : x * (c₁ * z * c₁⁻¹) * x⁻¹ * (x * (c₁ * z * c₁⁻¹) * x⁻¹) = 1 := by
      calc x * (c₁ * z * c₁⁻¹) * x⁻¹ * (x * (c₁ * z * c₁⁻¹) * x⁻¹) =
          x * ((c₁ * z * c₁⁻¹) * (c₁ * z * c₁⁻¹)) * x⁻¹ := by group
        _ = 1 := by rw [hI₁.sq]; group
    rcases hI₁.unique _ h2 h3 with h | h
    · exfalso
      apply hI₁.ne_one
      calc c₁ * z * c₁⁻¹ = x⁻¹ * (x * (c₁ * z * c₁⁻¹) * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc x * (c₁ * z * c₁⁻¹) = x * (c₁ * z * c₁⁻¹) * x⁻¹ * x := by group
        _ = c₁ * z * c₁⁻¹ * x := by rw [h]
  have hRJ₂ : R₀ ≤ conjSub c₂ K := hRle.trans (Subgroup.map_mono hKaK)
  obtain ⟨V₀, hV, hRV⟩ := IsSylow2In.exists_ge hR2 (le_inf hRJ₂ hRz)
  have hz₂V : c₂ * z * c₂⁻¹ ∈ V₀ := hRV (mem_of_le_member hI₂ hRJ₂ hR2 (by omega))
  have hcard : Nat.card R₀ ≤ Nat.card V₀ := Subgroup.card_le_of_le hRV
  rcases Asc77.l6_2 p f d.branch.odd d.branch.five G _ hΩ _ hJ₁ _ hI₁ _ hJ₂ htwin _
    hI₂ V₀ hV hz₂V with ⟨hV1, -⟩ | ⟨hV1, -⟩ | ⟨hV3, -⟩ | ⟨hV4, hVc⟩
  · rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [_root_.sq]; exact hI₂.sq)
      hI₂.ne_one] at hcard
    omega
  · rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [_root_.sq]; exact hI₂.sq)
      hI₂.ne_one] at hcard
    omega
  · obtain ⟨-, -, -, hcyc, -⟩ := hV3
    obtain ⟨x, hx, y, hy, hxy⟩ := hRnc
    exact hxy (commute_of_isCyclic hcyc (hRV hx) (hRV hy))
  · have hVJ₂ : V₀ ≤ conjSub c₂ K := hV.1.trans inf_le_left
    have hVN : V₀ ≤ Subgroup.normalizer (conjSub c₁ K : Set G) :=
      le_normalizer_of_commutator_le (hVc.trans (oddCoreOf_le_self _))
    have hnbr : conjSub c₂ K ∈ omegaNbr (CoreAssembly.conjClass K) (conjSub c₁ K) :=
      ⟨hJ₂, hJne.symm, V₀, hV4, hVJ₂, hVN⟩
    have h1 := omegaNbr_conj hΩ.conjInvariant hnbr c₁⁻¹
    rw [conjSub_inv_conjSub] at h1
    have h2 := d.late_nbr _ h1
    have h3 := twinSet_conj hΩ.conjInvariant h2 c₁
    rw [conjSub_conjSub_inv] at h3
    exact htwin h3


theorem exists_ne_comm_of_mem_rSetGen {Ω' : Set (Subgroup G)} (hΩ : HypOmegaGen Ω')
    {R₁ : Subgroup G}
    (hR : R₁ ∈ RSet Ω') : (∃ x ∈ R₁, ∃ y ∈ R₁, x * y ≠ y * x) ∧ 8 ≤ Nat.card R₁ := by
  have hq := Sec6Gen.isQuatSub_of_mem_RSet hΩ hR
  exact ⟨hq.exists_not_commute, hq.eight_le⟩


theorem Std20.t9_nbr_twin (d : Std20 p f K K' J S R R' W V z t) {a : G}
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hΩ : HypOmegaModU (.sl2 3 1) (conjFamily (crossIn K a)))
    (hL : IsClassicalMemberU (.sl2 3 1) (crossIn K a) ⟨z, hzA⟩) :
    ∀ M₁ ∈ conjFamily (crossIn K a), ∀ M₂ ∈ omegaNbr (conjFamily (crossIn K a)) M₁,
      M₂ ∈ twinSet (conjFamily (crossIn K a)) M₁ := by
  have hzKa : z ∈ K ⊓ Subgroup.centralizer ({a} : Set G) := Subgroup.mem_subgroupOf.mp hL.mem
  have hΩg : HypOmegaGen (conjFamily (crossIn K a)) :=
    hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΩ
  rintro _ ⟨c₁, rfl⟩ M₂ ⟨hM₂, hne, R₀, hR, hRle, hRN⟩
  obtain ⟨c₂, rfl⟩ := hM₂
  by_cases htwin : conjSub (c₂ : G) K ∈ twinSet (CoreAssembly.conjClass K) (conjSub (c₁ : G) K)
  · obtain ⟨-, w, hw₁, hw₂⟩ := htwin
    have e₁ := (d.viol.hzK.conj (c₁ : G)).eq hw₁
    have e₂ := (d.viol.hzK.conj (c₂ : G)).eq hw₂
    have e : c₁ * ⟨z, hzA⟩ * c₁⁻¹ = c₂ * ⟨z, hzA⟩ * c₂⁻¹ := Subtype.ext (e₁.trans e₂.symm)
    refine ⟨⟨c₂, rfl⟩, c₁ * ⟨z, hzA⟩ * c₁⁻¹, d.t9_isUniqueInvolution_conjSub hzA hzKa c₁, ?_⟩
    rw [e]
    exact d.t9_isUniqueInvolution_conjSub hzA hzKa c₂
  · exfalso
    obtain ⟨⟨x, hx, y, hy, hxy⟩, h8⟩ := exists_ne_comm_of_mem_rSetGen hΩg hR
    have hR2 := isPGroup_of_mem_rSet hR
    have hne' : conjSub (c₁ : G) (K ⊓ Subgroup.centralizer ({a} : Set G)) ≠
        conjSub (c₂ : G) (K ⊓ Subgroup.centralizer ({a} : Set G)) := by
      intro h
      apply hne
      apply Subgroup.map_injective (Subgroup.centralizer ({a} : Set G)).subtype_injective
      rw [map_conjSub_crossIn, map_conjSub_crossIn, h]
    refine d.t9_false_of_le_normalizer hzKa c₁.2 c₂.2 hne' htwin
      (hR2.map (Subgroup.centralizer ({a} : Set G)).subtype)
      ⟨(x : G), Subgroup.mem_map_of_mem _ hx, (y : G), Subgroup.mem_map_of_mem _ hy,
        fun h => hxy (Subtype.ext h)⟩ ?_ ?_ ?_
    · rw [← Nat.card_congr (Subgroup.equivMapOfInjective R₀ _
        (Subgroup.centralizer ({a} : Set G)).subtype_injective).toEquiv]
      omega
    · rw [← map_conjSub_crossIn]
      exact Subgroup.map_mono hRle
    · rw [← map_conjSub_crossIn]
      exact (Subgroup.map_mono hRN).trans (Subgroup.le_normalizer_map _)

theorem Std20.t9_conj_of_centralizes (d : Std20 p f K K' J S R R' W V z t) {a : G}
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    {t' : ↥(Subgroup.centralizer ({a} : Set G))} (ht2 : t' * t' = 1)
    (ht : ∃ g : G, (t' : G) = g * z * g⁻¹)
    {Q : Subgroup ↥(Subgroup.centralizer ({a} : Set G))} (hQ2 : IsPGroup 2 Q)
    (hQK : Q ≤ crossIn K a) (hQnc : ∃ x ∈ Q, ∃ y ∈ Q, x * y ≠ y * x)
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
    have hmapK : (crossIn K a).map (Subgroup.centralizer ({a} : Set G)).subtype ≤ K := by
      rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_subgroupOf.mp hx).1
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



end Std

end CFSG.ClassicalInvolution.Asc77.T3CII

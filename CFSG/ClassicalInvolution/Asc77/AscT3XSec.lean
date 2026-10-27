module

public import CFSG.ClassicalInvolution.Asc77.AscT3XHyp
public import CFSG.ClassicalInvolution.AschTight.S19CTop
public import CFSG.ClassicalInvolution.Asc77.AscIH8Small
public import CFSG.ClassicalInvolution.Asc77.AscIHSectL
public import CFSG.ClassicalInvolution.Asc77.AscT3CLateHexC

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


theorem Std20.x_isUniqueInvolution_conjSub (d : Std20 p f K K' J S R R' W V z t) {a : G}
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hzKa : z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)))
    (c : ↥(Subgroup.centralizer ({a} : Set G))) :
    IsUniqueInvolution (conjSub c (perfectCoreIn K a)) (c * ⟨z, hzA⟩ * c⁻¹) := by
  have hI := d.viol.hzK.conj (c : G)
  refine ⟨conj_mem_conjSub (Subgroup.mem_subgroupOf.mpr hzKa),
    fun h => hI.ne_one (congrArg Subtype.val h), Subtype.ext hI.sq, fun y hy hy2 => ?_⟩
  rcases hI.unique _ (le_conjSub_of_mem c hy) (congrArg Subtype.val hy2) with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem Std20.x_isUniqueInvolution_secImg (d : Std20 p f K K' J S R R' W V z t) {a : G}
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hzKa : z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)))
    (c : ↥(Subgroup.centralizer ({a} : Set G))) :
    IsUniqueInvolution (secImg (conjGen (perfectCoreIn K a)) (conjSub c (perfectCoreIn K a)))
      (QuotientGroup.mk' _ ⟨c * ⟨z, hzA⟩ * c⁻¹, le_conjGen ⟨c, rfl⟩
        (d.x_isUniqueInvolution_conjSub hzA hzKa c).mem⟩) :=
  isUniqueInvolution_map_mk (CFSG.ComponentClassification.OddCore.odd_card _)
    (isUniqueInvolution_subgroupOf (d.x_isUniqueInvolution_conjSub hzA hzKa c)
      (le_conjGen ⟨c, rfl⟩))

theorem Std20.x_top_not_mem (d : Std20 p f K K' J S R R' W V z t) {a : G}
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hzKa : z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)))
    (c : ↥(Subgroup.centralizer ({a} : Set G))) (hne : (c : G) * z * (c : G)⁻¹ ≠ z)
    (hcomm : (c : G) * z * (c : G)⁻¹ * z = z * ((c : G) * z * (c : G)⁻¹)) :
    (⊤ : Subgroup (↥(conjGen (perfectCoreIn K a)) ⧸
      classicalInvolutionOddCore ↥(conjGen (perfectCoreIn K a)))) ∉
      oddQuotientFamily (restrictFamily (conjFamily (perfectCoreIn K a))
        (conjGen (perfectCoreIn K a))) := by
  intro hTop
  obtain ⟨e, hdT⟩ := (mem_secFamily_iff _ _).mp hTop
  have hU := d.x_isUniqueInvolution_secImg hzA hzKa e
  rw [← hdT] at hU
  have h1 := d.x_isUniqueInvolution_secImg hzA hzKa 1
  have hc := d.x_isUniqueInvolution_secImg hzA hzKa c
  have e1 := (hU.unique _ (Subgroup.mem_top _) h1.sq).resolve_left h1.ne_one
  have ec := (hU.unique _ (Subgroup.mem_top _) hc.sq).resolve_left hc.ne_one
  have e' := e1.trans ec.symm
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at e'
  have hI := d.viol.hzK
  refine S19C.false_of_inv_mul_mem_odd (CFSG.ComponentClassification.OddCore.odd_card _) e' ?_ ?_
    ?_ ?_
  · apply Subtype.ext
    apply Subtype.ext
    simp [hI.sq]
  · apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
    calc (c : G) * z * (c : G)⁻¹ * ((c : G) * z * (c : G)⁻¹) = (c : G) * (z * z) * (c : G)⁻¹ := by
          group
      _ = 1 := by rw [hI.sq]; group
  · apply Subtype.ext
    apply Subtype.ext
    simpa using hcomm.symm
  · intro h
    apply hne
    have h' := congrArg (fun x : ↥(conjGen (perfectCoreIn K a)) =>
      ((x : ↥(Subgroup.centralizer ({a} : Set G))) : G)) h
    simpa using h'.symm

theorem Std20.x_false_of_le_normalizer (d : Std20 p f K K' J S R R' W V z t) {a : G}
    (hzKa : z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) {c₁ c₂ : G}
    (hc₁ : c₁ ∈ Subgroup.centralizer ({a} : Set G))
    (hc₂ : c₂ ∈ Subgroup.centralizer ({a} : Set G))
    (hne : conjSub c₁ (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) ≠
      conjSub c₂ (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))))
    (htwin : conjSub c₂ K ∉ twinSet (CoreAssembly.conjClass K) (conjSub c₁ K))
    {R₀ : Subgroup G} (hR2 : IsPGroup 2 R₀) (hRnc : ∃ x ∈ R₀, ∃ y ∈ R₀, x * y ≠ y * x)
    (hR8 : 2 < Nat.card R₀)
    (hRle : R₀ ≤ conjSub c₂ (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))))
    (hRN : R₀ ≤ Subgroup.normalizer
      ((conjSub c₁ (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) : Subgroup G) :
        Set G)) : False := by
  have hI := d.viol.hzK
  have hΩ := d.hyp
  have hKaK : perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)) ≤ K :=
    (perfectResidualOf_le _).trans inf_le_left
  have hJ₁ : conjSub c₁ K ∈ CoreAssembly.conjClass K := ⟨c₁, rfl⟩
  have hJ₂ : conjSub c₂ K ∈ CoreAssembly.conjClass K := ⟨c₂, rfl⟩
  have hI₁ := hI.conj c₁
  have hI₂ := hI.conj c₂
  have hJne : conjSub c₁ K ≠ conjSub c₂ K := fun h => hne (conjSub_perfectCore_eq hc₁ hc₂ h)
  have hRz : R₀ ≤ Subgroup.centralizer ({c₁ * z * c₁⁻¹} : Set G) := by
    intro x hx
    have h1 : x * (c₁ * z * c₁⁻¹) * x⁻¹ ∈
        conjSub c₁ (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) :=
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

theorem Std20.x_dEdgeless_or_swap (d : Std20 p f K K' J S R R' W V z t) {a : G} {e₀ : ℕ}
    (h5 : 5 ≤ p ^ e₀) (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hL : IsClassicalMember p e₀ (perfectCoreIn K a) ⟨z, hzA⟩) :
    Disconnected.DEdgeless (conjFamily (perfectCoreIn K a)) ∨
      ∃ c : G, c * a = a * c ∧ c * z = z * c ∧ conjSub c K = K' := by
  by_cases hsw : ∃ c : G, c * a = a * c ∧ c * z = z * c ∧ conjSub c K = K'
  · exact Or.inr hsw
  left
  push Not at hsw
  have hzKa : z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)) :=
    Subgroup.mem_subgroupOf.mp hL.mem
  have key : ∀ M₁ ∈ conjFamily (perfectCoreIn K a), ∀ M₂ ∈ conjFamily (perfectCoreIn K a),
      M₂ ∉ omegaNbr (conjFamily (perfectCoreIn K a)) M₁ := by
    rintro _ ⟨c₁, rfl⟩ _ ⟨c₂, rfl⟩ ⟨-, hne, R₀, hR, hRle, hRN⟩
    obtain ⟨⟨x, hx, y, hy, hxy⟩, h8⟩ := exists_ne_comm_of_mem_rSet d.branch.odd h5 hL hR
    have hR2 := isPGroup_of_mem_rSet hR
    have hne' : conjSub (c₁ : G) (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) ≠
        conjSub (c₂ : G) (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) := by
      intro h
      apply hne
      apply Subgroup.map_injective (Subgroup.centralizer ({a} : Set G)).subtype_injective
      rw [map_conjSub_perfectCore, map_conjSub_perfectCore, h]
    have htw : conjSub (c₂ : G) K ∉ twinSet (CoreAssembly.conjClass K) (conjSub (c₁ : G) K) := by
      rintro ⟨-, w, hw₁, hw₂⟩
      have e₁ := (d.viol.hzK.conj (c₁ : G)).eq hw₁
      have e₂ := (d.viol.hzK.conj (c₂ : G)).eq hw₂
      have hcz : (c₁ : G)⁻¹ * (c₂ : G) ∈ Subgroup.centralizer ({z} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h12 : (c₁ : G) * z * (c₁ : G)⁻¹ = (c₂ : G) * z * (c₂ : G)⁻¹ := e₁.trans e₂.symm
        calc (c₁ : G)⁻¹ * (c₂ : G) * z =
              (c₁ : G)⁻¹ * ((c₂ : G) * z * (c₂ : G)⁻¹) * (c₂ : G) := by group
          _ = (c₁ : G)⁻¹ * ((c₁ : G) * z * (c₁ : G)⁻¹) * (c₂ : G) := by rw [h12]
          _ = z * ((c₁ : G)⁻¹ * (c₂ : G)) := by group
      have hca : (c₁ : G)⁻¹ * (c₂ : G) ∈ Subgroup.centralizer ({a} : Set G) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ c₁.2) c₂.2
      have hc2 : conjSub (c₂ : G) K = conjSub (c₁ : G) (conjSub ((c₁ : G)⁻¹ * (c₂ : G)) K) := by
        rw [← conjSub_mul, mul_inv_cancel_left]
      rcases d.late_conj_K hcz with h | h
      · apply hne'
        rw [conjSub_perfectCore_eq c₁.2 c₂.2 (by rw [hc2, h])]
      · apply hsw ((c₁ : G)⁻¹ * (c₂ : G))
        · exact Subgroup.mem_centralizer_singleton_iff.mp hca
        · exact Subgroup.mem_centralizer_singleton_iff.mp hcz
        · exact h
    refine d.x_false_of_le_normalizer hzKa c₁.2 c₂.2 hne' htw
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
  intro M₁ hM₁ M₂ hM₂ hadj
  rcases hadj with h | h
  · exact key M₁ hM₁ M₂ hM₂ h
  · exact key M₂ hM₂ M₁ hM₁ h

theorem Std20.x_not_dEdgeless_of_swap (d : Std20 p f K K' J S R R' W V z t) {a : G}
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G)) {e₀ : ℕ}
    (hL : IsClassicalMember p e₀ (perfectCoreIn K a) ⟨z, hzA⟩) {c : G} (hca : c * a = a * c)
    (hcz : c * z = z * c) (hcK : conjSub c K = K') :
    ¬ Disconnected.DEdgeless (conjFamily (perfectCoreIn K a)) := by
  intro hDE
  have hΩ₀ := d.x_hypOmegaMod_conjFamily hzA hL
  have hcA : c ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hca
  set c' : ↥(Subgroup.centralizer ({a} : Set G)) := ⟨c, hcA⟩ with hc'
  have hM₁ : perfectCoreIn K a ∈ conjFamily (perfectCoreIn K a) := ⟨1, conjSub_one _⟩
  have hM₂ : conjSub c' (perfectCoreIn K a) ∈ conjFamily (perfectCoreIn K a) := ⟨c', rfl⟩
  have hzKa : z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)) :=
    Subgroup.mem_subgroupOf.mp hL.mem
  have hKaK : perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)) ≤ K :=
    (perfectResidualOf_le _).trans inf_le_left
  have hmap1 : (perfectCoreIn K a).map (Subgroup.centralizer ({a} : Set G)).subtype =
      perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)) := by
    have := map_conjSub_perfectCore (K := K) (a := a) 1
    simpa [conjSub_one] using this
  have hmap2 : (conjSub c' (perfectCoreIn K a)).map (Subgroup.centralizer ({a} : Set G)).subtype =
      conjSub c (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) :=
    map_conjSub_perfectCore c'
  have hne : conjSub c' (perfectCoreIn K a) ≠ perfectCoreIn K a := by
    intro h
    obtain ⟨P, hP, hP1, -⟩ := exists_mem_RSet_ge hM₁
      (isPGroup_two_bot' (G := ↥(Subgroup.centralizer ({a} : Set G)))) bot_le
    have h8 := hΩ₀.eight_le_of_mem_RSet d.branch.odd hP
    have hP2 : IsPGroup 2 P := hP1.2.1
    have hA2 : IsPGroup 2 (P.map (Subgroup.centralizer ({a} : Set G)).subtype) := hP2.map _
    have hcard : Nat.card ↥(P.map (Subgroup.centralizer ({a} : Set G)).subtype) = Nat.card P :=
      (Nat.card_congr (Subgroup.equivMapOfInjective P _
        (Subgroup.centralizer ({a} : Set G)).subtype_injective).toEquiv).symm
    have hPle : P ≤ perfectCoreIn K a := hP1.1
    have hAK : P.map (Subgroup.centralizer ({a} : Set G)).subtype ≤ K := by
      rw [← hmap1] at hKaK
      exact (Subgroup.map_mono hPle).trans hKaK
    have hAK' : P.map (Subgroup.centralizer ({a} : Set G)).subtype ≤ K' := by
      have h1 : (perfectCoreIn K a).map (Subgroup.centralizer ({a} : Set G)).subtype ≤
          conjSub c K := by
        calc (perfectCoreIn K a).map (Subgroup.centralizer ({a} : Set G)).subtype
            = (conjSub c' (perfectCoreIn K a)).map (Subgroup.centralizer ({a} : Set G)).subtype := by
              rw [h]
          _ = conjSub c (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) := hmap2
          _ ≤ conjSub c K := Subgroup.map_mono hKaK
      rw [hcK] at h1
      exact (Subgroup.map_mono hPle).trans h1
    exact d.ne (Sec6Gen.eq_of_le_of_le d.late_hΩ d.late_mem_K d.late_mem_K' hA2
      (by omega) hAK hAK').symm
  have hz2 : c' * ⟨z, hzA⟩ * c'⁻¹ = ⟨z, hzA⟩ := by
    apply Subtype.ext
    change c * z * c⁻¹ = z
    calc c * z * c⁻¹ = z * c * c⁻¹ := by rw [hcz]
      _ = z := by group
  have hu₂ := d.x_isUniqueInvolution_conjSub hzA hzKa c'
  rw [hz2] at hu₂
  have hu₁ : IsUniqueInvolution (perfectCoreIn K a) ⟨z, hzA⟩ := by
    have := d.x_isUniqueInvolution_conjSub hzA hzKa 1
    simpa [conjSub_one] using this
  exact hDE _ hM₁ _ hM₂ (Or.inl (twin_mem_omegaNbr hΩ₀ hM₁ hM₂ hne hu₁ hu₂))

theorem Std20.x_dEdgeless_iff (d : Std20 p f K K' J S R R' W V z t) {a : G} {e₀ : ℕ}
    (h5 : 5 ≤ p ^ e₀) (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hL : IsClassicalMember p e₀ (perfectCoreIn K a) ⟨z, hzA⟩) :
    Disconnected.DEdgeless (conjFamily (perfectCoreIn K a)) ↔
      ¬ ∃ c : G, c * a = a * c ∧ c * z = z * c ∧ conjSub c K = K' := by
  constructor
  · rintro hDE ⟨c, hca, hcz, hcK⟩
    exact d.x_not_dEdgeless_of_swap hzA hL hca hcz hcK hDE
  · intro hns
    rcases d.x_dEdgeless_or_swap h5 hzA hL with h | h
    · exact h
    · exact absurd h hns

section Typed


theorem Std20.x_sectionLieType_of_noSwap [IsSimpleGroup G]
    (d : Std20 p f K K' J S R R' W V z t) (c9 : Concl20_9 S K K' R R' z)
    (h8 : 8 < Nat.card R) (h9 : p ^ f ≠ 9) {b : G} (hb : FieldInv20 S K K' W z t b)
    (hNS : ∀ c : G, c * b = b * c → c * z = z * c → conjSub c K ≠ K') :
    ∃ e₀ : ℕ, f = 2 * e₀ ∧ 5 ≤ p ^ e₀ ∧ ∃ hzA : z ∈ Subgroup.centralizer ({b} : Set G),
      IsClassicalMember p e₀ (perfectCoreIn K b) ⟨z, hzA⟩ ∧
      (SectionLieType p e₀ (conjFamily (perfectCoreIn K b)) (conjGen (perfectCoreIn K b)) .PSL 3 ∨
        SectionLieType p e₀ (conjFamily (perfectCoreIn K b)) (conjGen (perfectCoreIn K b)) .PSU 3 ∨
        SectionLieType p e₀ (conjFamily (perfectCoreIn K b)) (conjGen (perfectCoreIn K b)) .G2 0 ∨
        SectionLieType p e₀ (conjFamily (perfectCoreIn K b)) (conjGen (perfectCoreIn K b))
          .trialityD4 0) := by
  obtain ⟨e₀, hfe, h5, hzA, hmem, hlt, hIH⟩ := d.x_sectionData c9 h8 h9 hb
  have hDE : Disconnected.DEdgeless (conjFamily (perfectCoreIn K b)) := by
    rcases d.x_dEdgeless_or_swap h5 hzA hmem with h | ⟨c, hcb, hcz, hcK⟩
    · exact h
    · exact absurd hcK (hNS c hcb hcz)
  obtain ⟨c, hcb, hczt⟩ := hb.fuse
  have hcA : c ∈ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcb
  have hzKa : z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({b} : Set G)) :=
    Subgroup.mem_subgroupOf.mp hmem.mem
  have hne : c * z * c⁻¹ ≠ z := by
    rw [hczt]
    exact d.late_ne_inv
  have hcomm : c * z * c⁻¹ * z = z * (c * z * c⁻¹) := by
    rw [hczt]
    exact d.late_zt_comm.symm
  have hTop := d.x_top_not_mem hzA hzKa ⟨c, hcA⟩ hne hcomm
  exact ⟨e₀, hfe, h5, hzA, hmem, sectionThm6 d.branch.odd h5 (ih8SmallEdge p) hIH hlt
    (d.x_hypOmegaMod_conjFamily hzA hmem) ⟨_, ⟨1, conjSub_one _⟩⟩ hDE hTop⟩

end Typed

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII

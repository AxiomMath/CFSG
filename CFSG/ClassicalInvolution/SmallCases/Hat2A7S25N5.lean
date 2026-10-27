module

public import Mathlib
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25N4
public import CFSG.ClassicalInvolution.Asc77.AscC25J25
public import CFSG.ClassicalInvolution.Q3.Induction

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S.N

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.C25V
  CFSG.ClassicalInvolution.Asc77.C25H CFSG.ClassicalInvolution.Asc77.C25J
  CFSG.ClassicalInvolution.Asc77.C25X CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.ClassicalInvolution.Asc77.C25I CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Asc77.T3
open CFSG.ClassicalInvolution.Hat2A7M.Asc77.T7F2 (Hyp25T)
open scoped MatrixGroups commutatorElement

section Omega

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}


theorem crossIn_omega5_conjFamily (hΩ : HypOmegaGen Ω) (hK : K ∈ Ω)
    (hI : IsUniqueInvolution K z) (a : G) :
    ∀ M₁ ∈ conjFamily (crossIn K a),
    ∀ M₂ ∈ conjFamily (crossIn K a), M₁ ≠ M₂ →
    ∀ u : ↥(Subgroup.centralizer ({a} : Set G)), IsUniqueInvolution M₁ u → ∀ v ∈ M₂,
      (¬ ∀ w ∈ M₂, v * w = w * v) → IsPGroup 2 (Subgroup.zpowers v) → v * u = u * v →
        v ∈ Subgroup.normalizer (M₁ : Set ↥(Subgroup.centralizer ({a} : Set G))) := by
  rintro _ ⟨c₁, rfl⟩ _ ⟨c₂, rfl⟩ hne u hu v hv hnc h2 hvu
  have hJne := conjSub_ne_of_ne_cross hne
  have hu' := crossIn_coe_eq_of_isUniqueInvolution hI c₁ hu
  have hvJ := le_conjSub_of_mem_cross c₂ hv
  have hnc' : ¬ ∀ w ∈ conjSub (c₂ : G) K, (v : G) * w = w * v := by
    intro h
    apply hnc
    intro w hw
    exact Subtype.ext (h _ (le_conjSub_of_mem_cross c₂ hw))
  have h2' : IsPGroup 2 (Subgroup.zpowers (v : G)) := by
    have := h2.map (Subgroup.centralizer ({a} : Set G)).subtype
    rwa [MonoidHom.map_zpowers] at this
  have hvz : (v : G) * ((c₁ : G) * z * (c₁ : G)⁻¹) = ((c₁ : G) * z * (c₁ : G)⁻¹) * v := by
    rw [← hu']
    exact congrArg Subtype.val hvu
  have hN := hΩ.omega5 _ (hΩ.conjInvariant c₁ K hK) _ (hΩ.conjInvariant c₂ K hK) hJne _
    (hI.conj (c₁ : G)) _ hvJ hnc' h2' hvz
  exact mem_normalizer_conjSub_of_cross c₁ v hN

theorem crossIn_omega4_conjFamily (hΩ : HypOmegaGen Ω) (hK : K ∈ Ω) (a : G) :
    ∀ M₁ ∈ conjFamily (crossIn K a), ∀ M₂ ∈ conjFamily (crossIn K a), M₁ ≠ M₂ →
      padicValNat 2 (Nat.card ↥(M₁ ⊓ M₂)) ≤ 1 ∧
        (padicValNat 2 (Nat.card ↥(M₁ ⊓ M₂)) = 1 → ⁅M₁, M₂⁆ ≤ oddCoreOf M₁ ⊓ oddCoreOf M₂) := by
  rintro _ ⟨c₁, rfl⟩ _ ⟨c₂, rfl⟩ hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJne := conjSub_ne_of_ne_cross hne
  obtain ⟨h4a, h4b⟩ := hΩ.omega4 _ (hΩ.conjInvariant c₁ K hK) _ (hΩ.conjInvariant c₂ K hK) hJne
  have hdvd : Nat.card ↥(conjSub c₁ (crossIn K a) ⊓ conjSub c₂ (crossIn K a)) ∣
      Nat.card ↥(conjSub (c₁ : G) K ⊓ conjSub (c₂ : G) K) := by
    rw [Nat.card_congr (Subgroup.equivMapOfInjective _ _
      (Subgroup.centralizer ({a} : Set G)).subtype_injective).toEquiv]
    apply Subgroup.card_dvd_of_le
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨le_conjSub_of_mem_cross c₁ hx.1, le_conjSub_of_mem_cross c₂ hx.2⟩
  have hval : padicValNat 2 (Nat.card ↥(conjSub c₁ (crossIn K a) ⊓
      conjSub c₂ (crossIn K a))) ≤
        padicValNat 2 (Nat.card ↥(conjSub (c₁ : G) K ⊓ conjSub (c₂ : G) K)) :=
    (padicValNat_dvd_iff_le Nat.card_pos.ne').mp (pow_padicValNat_dvd.trans hdvd)
  refine ⟨hval.trans h4a, fun h1 => ?_⟩
  have hc := h4b (le_antisymm h4a (h1 ▸ hval))
  refine le_inf (commutator_le_oddCoreOf_conjFamily_cross c₁ c₂ (hc.trans inf_le_left)) ?_
  rw [Subgroup.commutator_comm]
  refine commutator_le_oddCoreOf_conjFamily_cross c₂ c₁ ?_
  rw [Subgroup.commutator_comm]
  exact hc.trans inf_le_right

theorem crossIn_hypOmegaModU (hΩ : HypOmegaGen Ω) (hK : K ∈ Ω) (hI : IsUniqueInvolution K z)
    {b : G} (hzA : z ∈ Subgroup.centralizer ({b} : Set G))
    (hL : IsClassicalMemberU (.sl2 3 1) (crossIn K b) ⟨z, hzA⟩) :
    HypOmegaModU (.sl2 3 1) (conjFamily (crossIn K b)) where
  conjInvariant := by
    rintro n _ ⟨g, rfl⟩
    exact ⟨n * g, conjSub_mul _ _ _⟩
  classical := by
    rintro _ ⟨g, rfl⟩
    exact ⟨_, hL.conj g⟩
  omega4 := crossIn_omega4_conjFamily hΩ hK b
  omega5 := crossIn_omega5_conjFamily hΩ hK hI b

end Omega

section Nbr

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K K' : Subgroup G} {z : G}


theorem crossIn_false_of_le_normalizer (d : TwinCtx Ω K K' z) {a : G}
    (hzKa : z ∈ K ⊓ Subgroup.centralizer ({a} : Set G)) {c₁ c₂ : G}
    (hc₁ : c₁ ∈ Subgroup.centralizer ({a} : Set G))
    (hc₂ : c₂ ∈ Subgroup.centralizer ({a} : Set G))
    (hne : conjSub c₁ (K ⊓ Subgroup.centralizer ({a} : Set G)) ≠
      conjSub c₂ (K ⊓ Subgroup.centralizer ({a} : Set G)))
    (htwin : conjSub c₂ K ∉ twinSet Ω (conjSub c₁ K))
    {R₀ : Subgroup G} (hR2 : IsPGroup 2 R₀) (hRnc : ∃ x ∈ R₀, ∃ y ∈ R₀, x * y ≠ y * x)
    (hR8 : 2 < Nat.card R₀)
    (hRle : R₀ ≤ conjSub c₂ (K ⊓ Subgroup.centralizer ({a} : Set G)))
    (hRN : R₀ ≤ Subgroup.normalizer
      ((conjSub c₁ (K ⊓ Subgroup.centralizer ({a} : Set G)) : Subgroup G) : Set G)) :
    False := by
  have hI := d.hI
  have hΩ := d.hΩ
  have hKaK : (K ⊓ Subgroup.centralizer ({a} : Set G)) ≤ K := inf_le_left
  have hJ₁ : conjSub c₁ K ∈ Ω := hΩ.conjInvariant c₁ K d.hK
  have hJ₂ : conjSub c₂ K ∈ Ω := hΩ.conjInvariant c₂ K d.hK
  have hI₁ := hI.conj c₁
  have hI₂ := hI.conj c₂
  have hJne : conjSub c₁ K ≠ conjSub c₂ K := fun h => hne (conjSub_cross_eq hc₁ hc₂ h)
  have hRz : R₀ ≤ Subgroup.centralizer ({c₁ * z * c₁⁻¹} : Set G) := by
    intro x hx
    have h1 : x * (c₁ * z * c₁⁻¹) * x⁻¹ ∈
        conjSub c₁ (K ⊓ Subgroup.centralizer ({a} : Set G)) :=
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
  rcases Sec6Gen.l6_2Gen G _ hΩ _ hJ₁ _ hI₁ _ hJ₂ htwin _
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
    have hnbr : conjSub c₂ K ∈ omegaNbr Ω (conjSub c₁ K) :=
      ⟨hJ₂, hJne.symm, V₀, hV4, hVJ₂, hVN⟩
    have h1 := omegaNbr_conj hΩ.conjInvariant hnbr c₁⁻¹
    rw [conjSub_inv_conjSub] at h1
    have h2 := d.nbr h1
    have h3 := twinSet_conj hΩ.conjInvariant h2 c₁
    rw [conjSub_conjSub_inv] at h3
    exact htwin h3

theorem crossIn_nbr_twin (d : TwinCtx Ω K K' z) {a : G}
    (hzKa : z ∈ K ⊓ Subgroup.centralizer ({a} : Set G))
    (hΩ : HypOmegaModU (.sl2 3 1) (conjFamily (crossIn K a)))
    {c₁ c₂ : ↥(Subgroup.centralizer ({a} : Set G))}
    (h : conjSub c₂ (crossIn K a) ∈
      omegaNbr (conjFamily (crossIn K a)) (conjSub c₁ (crossIn K a))) :
    conjSub (c₂ : G) K ∈ twinSet Ω (conjSub (c₁ : G) K) := by
  by_contra htw
  have hΩg : HypOmegaGen (conjFamily (crossIn K a)) :=
    hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΩ
  obtain ⟨-, hne, R₀, hR, hRle, hRN⟩ := h
  obtain ⟨⟨x, hx, y, hy, hxy⟩, h8⟩ := exists_ne_comm_of_mem_rSetGen hΩg hR
  have hR2 := isPGroup_of_mem_rSet hR
  have hne' : conjSub (c₁ : G) (K ⊓ Subgroup.centralizer ({a} : Set G)) ≠
      conjSub (c₂ : G) (K ⊓ Subgroup.centralizer ({a} : Set G)) := by
    intro h
    apply hne
    apply Subgroup.map_injective (Subgroup.centralizer ({a} : Set G)).subtype_injective
    rw [map_conjSub_crossIn, map_conjSub_crossIn, h]
  refine crossIn_false_of_le_normalizer d hzKa c₁.2 c₂.2 hne' htw
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

theorem crossIn_nbr_eq (d : TwinCtx Ω K K' z) {a : G}
    (hzKa : z ∈ K ⊓ Subgroup.centralizer ({a} : Set G))
    (hΩ : HypOmegaModU (.sl2 3 1) (conjFamily (crossIn K a)))
    {w : ↥(Subgroup.centralizer ({a} : Set G))} (hw : conjSub (w : G) K = K')
    {c₁ c₂ : ↥(Subgroup.centralizer ({a} : Set G))}
    (h : conjSub c₂ (crossIn K a) ∈
      omegaNbr (conjFamily (crossIn K a)) (conjSub c₁ (crossIn K a))) :
    conjSub c₂ (crossIn K a) = conjSub (c₁ * w) (crossIn K a) := by
  have htw := crossIn_nbr_twin d hzKa hΩ h
  have h1 := twinSet_conj d.hΩ.conjInvariant htw (c₁ : G)⁻¹
  rw [conjSub_inv_conjSub, d.htw] at h1
  have e1 : conjSub ((c₁ : G)⁻¹) (conjSub (c₂ : G) K) = conjSub ((c₁ : G)⁻¹ * (c₂ : G)) K := by
    rw [conjSub_mul]
  rw [e1] at h1
  rcases h1 with h1 | h1
  · exfalso
    apply h.2.1
    apply crossIn_member_eq
    have h2 := congrArg (conjSub (c₁ : G)) h1
    rw [← conjSub_mul, mul_inv_cancel_left] at h2
    exact h2
  · apply crossIn_member_eq
    have h2 := congrArg (conjSub (c₁ : G)) h1
    rw [← conjSub_mul, mul_inv_cancel_left, ← hw, ← conjSub_mul] at h2
    exact h2

theorem crossIn_nbr_quot (d : TwinCtx Ω K K' z) {a : G}
    (hzKa : z ∈ K ⊓ Subgroup.centralizer ({a} : Set G))
    (hΛ : HypOmegaModU (.sl2 3 1) (conjFamily (crossIn K a)))
    {w : ↥(Subgroup.centralizer ({a} : Set G))} (hw : conjSub (w : G) K = K')
    (c₀ : ↥(Subgroup.centralizer ({a} : Set G)))
    {M : Subgroup (↥(conjGen (crossIn K a)) ⧸
      classicalInvolutionOddCore ↥(conjGen (crossIn K a)))}
    (hM : M ∈ omegaNbr (oddQuotientFamily (restrictFamily (conjFamily (crossIn K a))
      (conjGen (crossIn K a)))) (secImg (conjGen (crossIn K a))
        (conjSub c₀ (crossIn K a)))) :
    M = secImg (conjGen (crossIn K a)) (conjSub (c₀ * w) (crossIn K a)) := by
  obtain ⟨c, rfl⟩ := (mem_secFamily_iff (crossIn K a) M).mp hM.1
  set L := crossIn K a with hLdef
  set X := conjGen L with hX
  have hXn : X.Normal := conjGen_normal L
  have hN : Odd (Nat.card (classicalInvolutionOddCore ↥X)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥X
  have hΛ₁ : HypOmegaModU (.sl2 3 1) (restrictFamily (conjFamily L) X) :=
    hypOmegaModU_restrict hΛ X
  have hΛ₁g : HypOmegaGen (restrictFamily (conjFamily L) X) :=
    hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΛ₁
  have hΛ' : HypOmegaGen
      (quotFamily (restrictFamily (conjFamily L) X) (classicalInvolutionOddCore ↥X)) :=
    hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) (hypOmegaModU_oddQuotientFamily hΛ₁)
  have hK : (conjSub c₀ L).subgroupOf X ∈ restrictFamily (conjFamily L) X :=
    ⟨conjSub c₀ L, ⟨c₀, rfl⟩, le_conjGen ⟨c₀, rfl⟩, rfl⟩
  have hJ : (conjSub c L).subgroupOf X ∈ restrictFamily (conjFamily L) X :=
    ⟨conjSub c L, ⟨c, rfl⟩, le_conjGen ⟨c, rfl⟩, rfl⟩
  obtain ⟨n, hn, hnb⟩ := exists_conj_omegaNbr_gen hΛ₁g hΛ' hN hK hJ hM
  rw [conjSub_subgroupOf] at hnb
  have hnL : conjSub (n : ↥(Subgroup.centralizer ({a} : Set G))) (conjSub c₀ L) ≤ X :=
    le_conjGen ⟨(n : ↥(Subgroup.centralizer ({a} : Set G))) * c₀, conjSub_mul _ _ _⟩
  have hcL : conjSub c L ≤ X := le_conjGen ⟨c, rfl⟩
  have hnb' := omegaNbr_of_restrict hnL hcL hnb
  rw [← conjSub_mul] at hnb'
  have heq := crossIn_nbr_eq d hzKa hΛ hw hnb'
  rw [heq, mul_assoc, conjSub_mul]
  exact secImg_conjSub_odd L hn (le_conjGen ⟨c₀ * w, rfl⟩)

theorem crossIn_swap_ne (d : TwinCtx Ω K K' z) {a : G}
    (hΛ : HypOmegaModU (.sl2 3 1) (conjFamily (crossIn K a)))
    {c : ↥(Subgroup.centralizer ({a} : Set G))} (hcK : conjSub (c : G) K = K') :
    conjSub c (crossIn K a) ≠ crossIn K a := by
  have hΩg : HypOmegaGen (conjFamily (crossIn K a)) :=
    hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΛ
  have hM₁ : crossIn K a ∈ conjFamily (crossIn K a) := ⟨1, conjSub_one _⟩
  have hKaK : K ⊓ Subgroup.centralizer ({a} : Set G) ≤ K := inf_le_left
  have hmap1 : (crossIn K a).map (Subgroup.centralizer ({a} : Set G)).subtype =
      K ⊓ Subgroup.centralizer ({a} : Set G) := by
    simp
  have hmap2 : (conjSub c (crossIn K a)).map (Subgroup.centralizer ({a} : Set G)).subtype =
      conjSub (c : G) (K ⊓ Subgroup.centralizer ({a} : Set G)) := map_conjSub_crossIn c
  intro h
  obtain ⟨P, hP, hP1, -⟩ := exists_mem_RSet_ge hM₁
    (isPGroup_two_bot' (G := ↥(Subgroup.centralizer ({a} : Set G)))) bot_le
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩg hP
  have hP2 : IsPGroup 2 P := hP1.2.1
  have hA2 : IsPGroup 2 (P.map (Subgroup.centralizer ({a} : Set G)).subtype) := hP2.map _
  have hcard : Nat.card ↥(P.map (Subgroup.centralizer ({a} : Set G)).subtype) = Nat.card P :=
    (Nat.card_congr (Subgroup.equivMapOfInjective P _
      (Subgroup.centralizer ({a} : Set G)).subtype_injective).toEquiv).symm
  have hPle : P ≤ crossIn K a := hP1.1
  have hAK : P.map (Subgroup.centralizer ({a} : Set G)).subtype ≤ K := by
    rw [← hmap1] at hKaK
    exact (Subgroup.map_mono hPle).trans hKaK
  have hAK' : P.map (Subgroup.centralizer ({a} : Set G)).subtype ≤ K' := by
    have h1 : (crossIn K a).map (Subgroup.centralizer ({a} : Set G)).subtype ≤
        conjSub (c : G) K := by
      calc (crossIn K a).map (Subgroup.centralizer ({a} : Set G)).subtype
          = (conjSub c (crossIn K a)).map
              (Subgroup.centralizer ({a} : Set G)).subtype := by rw [h]
        _ = conjSub (c : G) (K ⊓ Subgroup.centralizer ({a} : Set G)) := hmap2
        _ ≤ conjSub (c : G) K := Subgroup.map_mono hKaK
    rw [hcK] at h1
    exact (Subgroup.map_mono hPle).trans h1
  exact d.ne (d.hΩ.eq_of_le_of_le d.hK d.hK' hA2 (by omega) hAK hAK').symm

end Nbr

section Twin

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


theorem crossIn_twinSect0 (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t') {a : G}
    (hF' : IsFAut R' a) (hat : a * t' = t' * a)
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hΛ : HypOmegaModU (.sl2 3 1) (conjFamily (crossIn K' a))) :
    ∃ (ht'a : t' ∈ Subgroup.centralizer ({a} : Set G))
      (hzX : (⟨z, hzA⟩ : ↥(Subgroup.centralizer ({a} : Set G))) ∈ conjGen (crossIn K' a))
      (a₀ b₀ : ↥(conjGen (crossIn K' a)) ⧸ classicalInvolutionOddCore ↥(conjGen (crossIn K' a))),
      TwinSect0 (oddQuotientFamily (restrictFamily (conjFamily (crossIn K' a))
        (conjGen (crossIn K' a))))
        (secImg (conjGen (crossIn K' a)) (crossIn K' a))
        (secImg (conjGen (crossIn K' a)) (conjSub (⟨t', ht'a⟩ :
          ↥(Subgroup.centralizer ({a} : Set G))) (crossIn K' a)))
        (QuotientGroup.mk ⟨⟨z, hzA⟩, hzX⟩) a₀ b₀ := by
  have ht'a : t' ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hat.symm
  refine ⟨ht'a, ?_⟩
  have d' := twinCtx'_of_hyp25 h
  have hzKa : z ∈ K' ⊓ Subgroup.centralizer ({a} : Set G) := ⟨h.hz'.mem, hzA⟩
  set w : ↥(Subgroup.centralizer ({a} : Set G)) := ⟨t', ht'a⟩ with hwdef
  have hw : conjSub (w : G) K' = K := conjSub_t'_K' h
  set L := crossIn K' a with hLdef
  set X := conjGen L with hX
  have hXn : X.Normal := conjGen_normal L
  have hLmem : L ∈ conjFamily L := ⟨1, conjSub_one L⟩
  have hL'mem : conjSub w L ∈ conjFamily L := ⟨w, rfl⟩
  have hLX : L ≤ X := le_conjGen hLmem
  have hL'X : conjSub w L ≤ X := le_conjGen hL'mem
  have hzw : w * ⟨z, hzA⟩ * w⁻¹ = (⟨z, hzA⟩ : ↥(Subgroup.centralizer ({a} : Set G))) := by
    apply Subtype.ext
    change t' * z * t'⁻¹ = z
    calc t' * z * t'⁻¹ = z * t' * t'⁻¹ := by rw [t'_comm_z h]
      _ = z := by group
  have hu₁ : IsUniqueInvolution L ⟨z, hzA⟩ := by
    have := crossIn_isUniqueInvolution_conjSub h.hz' hzA hzKa 1
    have e : (1 : ↥(Subgroup.centralizer ({a} : Set G))) * ⟨z, hzA⟩ * 1⁻¹ = ⟨z, hzA⟩ := by group
    rw [conjSub_one, e] at this
    exact this
  have hu₂ : IsUniqueInvolution (conjSub w L) ⟨z, hzA⟩ := by
    have := crossIn_isUniqueInvolution_conjSub h.hz' hzA hzKa w
    rwa [hzw] at this
  have hne : conjSub w L ≠ L := crossIn_swap_ne d' hΛ hw
  have hzX : (⟨z, hzA⟩ : ↥(Subgroup.centralizer ({a} : Set G))) ∈ X := hLX hu₁.mem
  set z₀ : ↥X ⧸ classicalInvolutionOddCore ↥X := QuotientGroup.mk ⟨⟨z, hzA⟩, hzX⟩ with hz₀
  have hz₀A : IsUniqueInvolution (secImg X L) z₀ := by
    have h1 := crossIn_isUniqueInvolution_secImg h.hz' hzA hzKa 1
    have e1 : (QuotientGroup.mk' _ ⟨1 * ⟨z, hzA⟩ * 1⁻¹, le_conjGen ⟨1, rfl⟩
        (crossIn_isUniqueInvolution_conjSub h.hz' hzA hzKa 1).mem⟩ :
          ↥X ⧸ classicalInvolutionOddCore ↥X) = z₀ := by
      apply congrArg QuotientGroup.mk
      apply Subtype.ext
      simp
    rw [e1, conjSub_one] at h1
    exact h1
  have hz₀A' : IsUniqueInvolution (secImg X (conjSub w L)) z₀ := by
    have h1 := crossIn_isUniqueInvolution_secImg h.hz' hzA hzKa w
    have e1 : (QuotientGroup.mk' _ ⟨w * ⟨z, hzA⟩ * w⁻¹, le_conjGen ⟨w, rfl⟩
        (crossIn_isUniqueInvolution_conjSub h.hz' hzA hzKa w).mem⟩ :
          ↥X ⧸ classicalInvolutionOddCore ↥X) = z₀ := by
      apply congrArg QuotientGroup.mk
      apply Subtype.ext
      exact hzw
    rw [e1] at h1
    exact h1
  have hΛ₁ : HypOmegaModU (.sl2 3 1) (restrictFamily (conjFamily L) X) :=
    hypOmegaModU_restrict hΛ X
  have hne_img : secImg X L ≠ secImg X (conjSub w L) := by
    intro heq
    have hX1 : IsUniqueInvolution (L.subgroupOf X) ⟨⟨z, hzA⟩, hzX⟩ :=
      S1911.isUniqueInvolution_subgroupOf hu₁ hLX
    have hX2 : IsUniqueInvolution ((conjSub w L).subgroupOf X) ⟨⟨z, hzA⟩, hzX⟩ :=
      S1911.isUniqueInvolution_subgroupOf hu₂ hL'X
    have hsub := eq_of_map_eq_of_twin_three hΛ₁ ⟨L, hLmem, hLX, rfl⟩
      ⟨conjSub w L, hL'mem, hL'X, rfl⟩ hX1 hX2 heq
    have e1 := Subgroup.map_subgroupOf_eq_of_le hLX
    have e2 := Subgroup.map_subgroupOf_eq_of_le hL'X
    rw [hsub] at e1
    exact hne (e2.symm.trans e1)
  obtain ⟨y, hyR', hy4, hya⟩ := exists_order_four_of_isFAut hF'
  have hyK' : y ∈ K' := h.hR'syl.1 hyR'
  have hyC : y ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hya
  have hyL : (⟨y, hyC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) ∈ L :=
    Subgroup.mem_subgroupOf.mpr ⟨hyK', hyC⟩
  have hyX : (⟨y, hyC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) ∈ X := hLX hyL
  have hysq : y * y = z := C25X.sq_eq_of_orderOf_four h.hz' hyK' hy4
  have hbL' : w * ⟨y, hyC⟩ * w⁻¹ ∈ conjSub w L := conj_mem_conjSub hyL
  have hbX : w * ⟨y, hyC⟩ * w⁻¹ ∈ X := hL'X hbL'
  refine ⟨hzX, QuotientGroup.mk ⟨⟨y, hyC⟩, hyX⟩, QuotientGroup.mk ⟨w * ⟨y, hyC⟩ * w⁻¹, hbX⟩,
    ⟨(mem_secFamily_iff L _).mpr ⟨1, by rw [conjSub_one]⟩, (mem_secFamily_iff L _).mpr ⟨w, rfl⟩,
      hne_img, hz₀A, hz₀A',
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hyL),
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hbL'), ?_, ?_, ?_, ?_⟩⟩
  · rw [← QuotientGroup.mk_mul]
    apply congrArg QuotientGroup.mk
    apply Subtype.ext
    apply Subtype.ext
    exact hysq
  · rw [← QuotientGroup.mk_mul]
    apply congrArg QuotientGroup.mk
    apply Subtype.ext
    have e : w * ⟨y, hyC⟩ * w⁻¹ * (w * ⟨y, hyC⟩ * w⁻¹) =
        w * (⟨y, hyC⟩ * ⟨y, hyC⟩) * w⁻¹ := by group
    have e2 : (⟨y, hyC⟩ * ⟨y, hyC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) = ⟨z, hzA⟩ :=
      Subtype.ext hysq
    change w * ⟨y, hyC⟩ * w⁻¹ * (w * ⟨y, hyC⟩ * w⁻¹) = ⟨z, hzA⟩
    rw [e, e2, hzw]
  · intro M hM hMn
    have := crossIn_nbr_quot d' hzKa hΛ hw 1 (M := M) (by rwa [conjSub_one])
    rwa [one_mul] at this
  · intro M hM hMn
    have := crossIn_nbr_quot d' hzKa hΛ hw w (M := M) hMn
    have hww : w * w = 1 := Subtype.ext h.ht'2
    rwa [hww, conjSub_one] at this

theorem crossIn_aEmpty (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t') {a : G}
    (hΛ : HypOmegaModU (.sl2 3 1) (conjFamily (crossIn K' a))) :
    ∀ M ∈ conjFamily (crossIn K' a), AEmpty (conjFamily (crossIn K' a)) M := by
  classical
  have hΩg : HypOmegaGen (conjFamily (crossIn K' a)) :=
    hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΛ
  rintro M ⟨c₁, rfl⟩ J hJstar hJnbr zK zJ hzK hzJ
  exfalso
  apply hJnbr
  obtain ⟨hJΛ, hJne, U, hU, hUJ, hUN⟩ := hJstar
  obtain ⟨c₂, rfl⟩ := hJΛ
  obtain ⟨R₀, hR₀, hUR₀, hUcyc, hUidx⟩ := hU
  obtain ⟨J₃, -, hR₀syl⟩ := exists_isSylow2In_of_mem_RSet hR₀
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩg hR₀
  obtain ⟨y, hyU, hy4⟩ := C25V.exists_orderOf_four_of_cyclic hUR₀ hUcyc hUidx h8 hR₀syl.2.1
  have hyJ := hUJ hyU
  have hyN := hUN hyU
  have hy4' : orderOf (y : G) = 4 := by rw [Subgroup.orderOf_coe, hy4]
  have hyK : (y : G) ∈ conjSub (c₂ : G) K' := le_conjSub_of_mem_cross c₂ hyJ
  have hyz : y * zK * y⁻¹ = zK := hzK.conj_eq (mem_normalizer_iff_conjSub_eq.mp hyN)
  have hzK' : (zK : G) = (c₁ : G) * z * (c₁ : G)⁻¹ :=
    crossIn_coe_eq_of_isUniqueInvolution h.hz' c₁ hzK
  have hzJ' : (zJ : G) = (c₂ : G) * z * (c₂ : G)⁻¹ :=
    crossIn_coe_eq_of_isUniqueInvolution h.hz' c₂ hzJ
  have hcomm : ((c₁ : G) * z * (c₁ : G)⁻¹) * (y : G) = (y : G) * ((c₁ : G) * z * (c₁ : G)⁻¹) := by
    rw [← hzK']
    have : (y : G) * (zK : G) * (y : G)⁻¹ = (zK : G) := by
      have := congrArg Subtype.val hyz
      simpa using this
    exact (mul_inv_eq_iff_eq_mul.mp this).symm
  have heq := eq_conj_z_of_commute_order_four h (c := (c₂ : G)) (g := (c₁ : G)) (y₀ := (y : G))
    hyK hy4' hcomm
  have hzz : zK = zJ := Subtype.ext (by rw [hzK', hzJ', heq])
  rw [← hzz] at hzJ
  have hJMem : conjSub c₂ (crossIn K' a) ∈ conjFamily (crossIn K' a) := ⟨c₂, rfl⟩
  have hMMem : conjSub c₁ (crossIn K' a) ∈ conjFamily (crossIn K' a) := ⟨c₁, rfl⟩
  exact CFSG.ClassicalInvolution.Q3.Q3CL.T3.twin_mem_omegaNbr hΩg hMMem hJMem hJne hzK hzJ

theorem crossIn_nc4_excl (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t') {a : G}
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G)) :
    ∀ {J₁ J₂ : Subgroup (↥(conjGen (crossIn K' a)) ⧸
        classicalInvolutionOddCore ↥(conjGen (crossIn K' a)))},
      J₁ ∈ oddQuotientFamily (restrictFamily (conjFamily (crossIn K' a))
        (conjGen (crossIn K' a))) →
      J₂ ∈ oddQuotientFamily (restrictFamily (conjFamily (crossIn K' a))
        (conjGen (crossIn K' a))) →
      ∀ {y z₂ : ↥(conjGen (crossIn K' a)) ⧸
        classicalInvolutionOddCore ↥(conjGen (crossIn K' a))},
        y ∈ J₁ → y * y * y * y = 1 → y * y ≠ 1 → z₂ ∈ J₂ → z₂ * z₂ = 1 → z₂ ≠ 1 →
        z₂ ≠ y * y → z₂ * y = y * z₂ → False := by
  have hzKa : z ∈ K' ⊓ Subgroup.centralizer ({a} : Set G) := ⟨h.hz'.mem, hzA⟩
  intro J₁ J₂ hJ₁ hJ₂ y z₂ hy hy4 hy2 hz₂ hz₂2 hz₂1 hne hcomm
  have hNC4 : ∀ c₁ c₂ y₁ : ↥(Subgroup.centralizer ({a} : Set G)),
      y₁ ∈ conjSub c₁ (crossIn K' a) → orderOf y₁ = 4 →
      y₁ * (c₂ * ⟨z, hzA⟩ * c₂⁻¹) = (c₂ * ⟨z, hzA⟩ * c₂⁻¹) * y₁ →
      c₂ * ⟨z, hzA⟩ * c₂⁻¹ = c₁ * ⟨z, hzA⟩ * c₁⁻¹ := by
    intro c₁ c₂ y₁ hy₁ hy₁4 hcomm
    have hy₁4' : orderOf (y₁ : G) = 4 := by rw [Subgroup.orderOf_coe]; exact hy₁4
    have hcomm' : ((c₂ : G) * z * (c₂ : G)⁻¹) * (y₁ : G) =
        (y₁ : G) * ((c₂ : G) * z * (c₂ : G)⁻¹) := (congrArg Subtype.val hcomm).symm
    have := eq_conj_z_of_commute_order_four h (c := (c₁ : G)) (g := (c₂ : G)) (y₀ := (y₁ : G))
      (le_conjSub_of_mem_cross c₁ hy₁) hy₁4' hcomm'
    exact Subtype.ext this
  exact nc4_excl_generic (crossIn K' a) ⟨z, hzA⟩
    (fun c => crossIn_isUniqueInvolution_conjSub h.hz' hzA hzKa c) hNC4 hJ₁ hJ₂ hy hy4 hy2 hz₂
    hz₂2 hz₂1 hne hcomm

end Twin

end CFSG.ClassicalInvolution.Hat2A7S.N

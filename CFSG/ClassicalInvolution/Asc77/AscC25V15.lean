module

public import CFSG.ClassicalInvolution.Asc77.AscC25V14
public import CFSG.ClassicalInvolution.AschTight.S19CTop
public import CFSG.ClassicalInvolution.Asc77.AscT7F2Ctx

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ClassicalInvolution.Asc77.T3
open scoped MatrixGroups commutatorElement

structure TwinCtx (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G]
    (Ω : Set (Subgroup G)) (K K' : Subgroup G) (z : G) : Prop where
  hp2 : p ≠ 2
  hq : 5 ≤ p ^ f
  hΩ : HypOmegaMod p f Ω
  hK : K ∈ Ω
  hK' : K' ∈ Ω
  hI : IsUniqueInvolution K z
  hI' : IsUniqueInvolution K' z
  ne : K' ≠ K
  htw : twinSet Ω K = {K, K'}
  hperp : KPerp Ω K = {K, K'}

namespace TwinCtx

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' : Subgroup G} {z : G}

theorem conj_K (d : TwinCtx p f Ω K K' z) {g : G} (hg : g * z = z * g) :
    conjSub g K = K ∨ conjSub g K = K' := by
  have hgz : g * z * g⁻¹ = z := by
    calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [hg]
      _ = z := by group
  have h1 : conjSub g K ∈ twinSet Ω K :=
    ⟨d.hΩ.conjInvariant g K d.hK, z, d.hI, hgz ▸ d.hI.conj g⟩
  rw [d.htw] at h1
  exact h1

theorem conj_K' (d : TwinCtx p f Ω K K' z) {g : G} (hg : g * z = z * g) :
    conjSub g K' = K ∨ conjSub g K' = K' := by
  have hgz : g * z * g⁻¹ = z := by
    calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [hg]
      _ = z := by group
  have h1 : conjSub g K' ∈ twinSet Ω K :=
    ⟨d.hΩ.conjInvariant g K' d.hK', z, d.hI, hgz ▸ d.hI'.conj g⟩
  rw [d.htw] at h1
  exact h1

theorem conj_iff (d : TwinCtx p f Ω K K' z) {g : G} (hg : g * z = z * g) :
    conjSub g K = K ↔ conjSub g K' = K' := by
  constructor
  · intro h
    rcases d.conj_K' hg with h' | h'
    · exact absurd (conjSub_injective g (h'.trans h.symm)) d.ne
    · exact h'
  · intro h
    rcases d.conj_K hg with h' | h'
    · exact h'
    · exact absurd (conjSub_injective g (h'.trans h.symm)) d.ne.symm

theorem nbr (d : TwinCtx p f Ω K K' z) {J : Subgroup G} (h : J ∈ omegaNbr Ω K) :
    J ∈ twinSet Ω K := by
  have h1 : J ∈ KPerp Ω K := Or.inr h
  rw [d.hperp] at h1
  rcases h1 with rfl | rfl
  · exact absurd rfl h.2.1
  · rw [d.htw]
    exact Or.inr rfl

theorem conj_normalizer (d : TwinCtx p f Ω K K' z) {y x : G} (hy : y * z = z * y)
    (hx : x * z = z * x) (hxK : conjSub x K = K) : conjSub (y * x * y⁻¹) K = K := by
  have hyi : y⁻¹ * z = z * y⁻¹ := by
    have h1 : y * z = z * y := hy
    calc y⁻¹ * z = y⁻¹ * (z * y) * y⁻¹ := by group
      _ = y⁻¹ * (y * z) * y⁻¹ := by rw [h1]
      _ = z * y⁻¹ := by group
  have hxK' : conjSub x K' = K' := (d.conj_iff hx).mp hxK
  have e1 : conjSub (y * x * y⁻¹) K = conjSub y (conjSub x (conjSub y⁻¹ K)) := by
    rw [conjSub_mul, conjSub_mul]
  rcases d.conj_K hyi with h | h
  · rw [e1, h, hxK]
    have h1 := congrArg (conjSub y) h
    rw [← conjSub_mul, mul_inv_cancel, conjSub_one] at h1
    exact h1.symm
  · rw [e1, h, hxK']
    have h1 := congrArg (conjSub y) h
    rw [← conjSub_mul, mul_inv_cancel, conjSub_one] at h1
    exact h1.symm

end TwinCtx

section FromHyp25

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


theorem twinCtx_of_hyp25 (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') :
    TwinCtx p f Ω K K' z where
  hp2 := h.hp
  hq := h.hs.stand.five
  hΩ := h.hΩ
  hK := h.hK
  hK' := h.hK'
  hI := h.hz
  hI' := h.hz'
  ne := h.hs.hne
  htw := h.hs.twinSet_eq
  hperp := h.hs.perp

theorem twinCtx'_of_hyp25 (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') :
    TwinCtx p f Ω K' K z where
  hp2 := h.hp
  hq := h.hs.stand.five
  hΩ := h.hΩ
  hK := h.hK'
  hK' := h.hK
  hI := h.hz'
  hI' := h.hz
  ne := h.hs.hne.symm
  htw := by
    rw [twinSet_eq_of_mem_twinSet h.hz h.hs.hK', h.hs.twinSet_eq, Set.pair_comm]
  hperp := by
    rw [h.hs.perp_of_twin h.hs.hK', Set.pair_comm]

end FromHyp25

section Sec

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' : Subgroup G} {z : G}


theorem fs_isUniqueInvolution_conjSub (hI : IsUniqueInvolution K z) {a : G}
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hzKa : z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)))
    (c : ↥(Subgroup.centralizer ({a} : Set G))) :
    IsUniqueInvolution (conjSub c (perfectCoreIn K a)) (c * ⟨z, hzA⟩ * c⁻¹) := by
  have hI' := hI.conj (c : G)
  refine ⟨conj_mem_conjSub (Subgroup.mem_subgroupOf.mpr hzKa),
    fun h => hI'.ne_one (congrArg Subtype.val h), Subtype.ext hI'.sq, fun y hy hy2 => ?_⟩
  rcases hI'.unique _ (le_conjSub_of_mem c hy) (congrArg Subtype.val hy2) with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem fs_isUniqueInvolution_secImg (hI : IsUniqueInvolution K z) {a : G}
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hzKa : z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)))
    (c : ↥(Subgroup.centralizer ({a} : Set G))) :
    IsUniqueInvolution (secImg (conjGen (perfectCoreIn K a)) (conjSub c (perfectCoreIn K a)))
      (QuotientGroup.mk' _ ⟨c * ⟨z, hzA⟩ * c⁻¹, le_conjGen ⟨c, rfl⟩
        (fs_isUniqueInvolution_conjSub hI hzA hzKa c).mem⟩) :=
  isUniqueInvolution_map_mk (CFSG.ComponentClassification.OddCore.odd_card _)
    (isUniqueInvolution_subgroupOf (fs_isUniqueInvolution_conjSub hI hzA hzKa c)
      (le_conjGen ⟨c, rfl⟩))

theorem fs_top_not_mem (hI : IsUniqueInvolution K z) {a : G}
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
  have hU := fs_isUniqueInvolution_secImg hI hzA hzKa e
  rw [← hdT] at hU
  have h1 := fs_isUniqueInvolution_secImg hI hzA hzKa 1
  have hc := fs_isUniqueInvolution_secImg hI hzA hzKa c
  have e1 := (hU.unique _ (Subgroup.mem_top _) h1.sq).resolve_left h1.ne_one
  have ec := (hU.unique _ (Subgroup.mem_top _) hc.sq).resolve_left hc.ne_one
  have e' := e1.trans ec.symm
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at e'
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

theorem fs_false_of_le_normalizer (d : TwinCtx p f Ω K K' z) {a : G}
    (hzKa : z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) {c₁ c₂ : G}
    (hc₁ : c₁ ∈ Subgroup.centralizer ({a} : Set G))
    (hc₂ : c₂ ∈ Subgroup.centralizer ({a} : Set G))
    (hne : conjSub c₁ (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) ≠
      conjSub c₂ (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))))
    (htwin : conjSub c₂ K ∉ twinSet Ω (conjSub c₁ K))
    {R₀ : Subgroup G} (hR2 : IsPGroup 2 R₀) (hRnc : ∃ x ∈ R₀, ∃ y ∈ R₀, x * y ≠ y * x)
    (hR8 : 2 < Nat.card R₀)
    (hRle : R₀ ≤ conjSub c₂ (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))))
    (hRN : R₀ ≤ Subgroup.normalizer
      ((conjSub c₁ (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) : Subgroup G) :
        Set G)) : False := by
  have hI := d.hI
  have hΩ := d.hΩ
  have hKaK : perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)) ≤ K :=
    (perfectResidualOf_le _).trans inf_le_left
  have hJ₁ : conjSub c₁ K ∈ Ω := hΩ.conjInvariant c₁ K d.hK
  have hJ₂ : conjSub c₂ K ∈ Ω := hΩ.conjInvariant c₂ K d.hK
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
  rcases Asc77.l6_2 p f d.hp2 d.hq G _ hΩ _ hJ₁ _ hI₁ _ hJ₂ htwin _
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

theorem fs_dEdgeless_or_swap (d : TwinCtx p f Ω K K' z) {a : G} {e₀ : ℕ}
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
    obtain ⟨⟨x, hx, y, hy, hxy⟩, h8⟩ := exists_ne_comm_of_mem_rSet d.hp2 h5 hL hR
    have hR2 := isPGroup_of_mem_rSet hR
    have hne' : conjSub (c₁ : G) (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) ≠
        conjSub (c₂ : G) (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) := by
      intro h
      apply hne
      apply Subgroup.map_injective (Subgroup.centralizer ({a} : Set G)).subtype_injective
      rw [map_conjSub_perfectCore, map_conjSub_perfectCore, h]
    have htw : conjSub (c₂ : G) K ∉ twinSet Ω (conjSub (c₁ : G) K) := by
      rintro ⟨-, w, hw₁, hw₂⟩
      have e₁ := (d.hI.conj (c₁ : G)).eq hw₁
      have e₂ := (d.hI.conj (c₂ : G)).eq hw₂
      have hcz : (c₁ : G)⁻¹ * (c₂ : G) ∈ Subgroup.centralizer ({z} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h12 : (c₁ : G) * z * (c₁ : G)⁻¹ = (c₂ : G) * z * (c₂ : G)⁻¹ := e₁.trans e₂.symm
        calc (c₁ : G)⁻¹ * (c₂ : G) * z =
              (c₁ : G)⁻¹ * ((c₂ : G) * z * (c₂ : G)⁻¹) * (c₂ : G) := by group
          _ = (c₁ : G)⁻¹ * ((c₁ : G) * z * (c₁ : G)⁻¹) * (c₂ : G) := by rw [h12]
          _ = z * ((c₁ : G)⁻¹ * (c₂ : G)) := by group
      have hcz' : (c₁ : G)⁻¹ * (c₂ : G) * z = z * ((c₁ : G)⁻¹ * (c₂ : G)) :=
        Subgroup.mem_centralizer_singleton_iff.mp hcz
      have hca : (c₁ : G)⁻¹ * (c₂ : G) ∈ Subgroup.centralizer ({a} : Set G) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ c₁.2) c₂.2
      have hc2 : conjSub (c₂ : G) K = conjSub (c₁ : G) (conjSub ((c₁ : G)⁻¹ * (c₂ : G)) K) := by
        rw [← conjSub_mul, mul_inv_cancel_left]
      rcases d.conj_K hcz' with h | h
      · apply hne'
        rw [conjSub_perfectCore_eq c₁.2 c₂.2 (by rw [hc2, h])]
      · apply hsw ((c₁ : G)⁻¹ * (c₂ : G))
        · exact Subgroup.mem_centralizer_singleton_iff.mp hca
        · exact hcz'
        · exact h
    refine fs_false_of_le_normalizer d hzKa c₁.2 c₂.2 hne' htw
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

theorem fs_not_dEdgeless_of_swap (d : TwinCtx p f Ω K K' z) {a : G}
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G)) {e₀ : ℕ}
    (hL : IsClassicalMember p e₀ (perfectCoreIn K a) ⟨z, hzA⟩) {c : G} (hca : c * a = a * c)
    (hcz : c * z = z * c) (hcK : conjSub c K = K') :
    ¬ Disconnected.DEdgeless (conjFamily (perfectCoreIn K a)) := by
  intro hDE
  have hΩ₀ := fs_hypOmegaMod_conjFamily d.hΩ d.hK d.hI hzA hL
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
    have h8 := hΩ₀.eight_le_of_mem_RSet d.hp2 hP
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
            = (conjSub c' (perfectCoreIn K a)).map
                (Subgroup.centralizer ({a} : Set G)).subtype := by rw [h]
          _ = conjSub c (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) := hmap2
          _ ≤ conjSub c K := Subgroup.map_mono hKaK
      rw [hcK] at h1
      exact (Subgroup.map_mono hPle).trans h1
    exact d.ne (d.hΩ.eq_of_le_of_le d.hK d.hK' hA2 (by omega) hAK hAK').symm
  have hz2 : c' * ⟨z, hzA⟩ * c'⁻¹ = ⟨z, hzA⟩ := by
    apply Subtype.ext
    change c * z * c⁻¹ = z
    calc c * z * c⁻¹ = z * c * c⁻¹ := by rw [hcz]
      _ = z := by group
  have hu₂ := fs_isUniqueInvolution_conjSub d.hI hzA hzKa c'
  rw [hz2] at hu₂
  have hu₁ : IsUniqueInvolution (perfectCoreIn K a) ⟨z, hzA⟩ := by
    have := fs_isUniqueInvolution_conjSub d.hI hzA hzKa 1
    simpa [conjSub_one] using this
  exact hDE _ hM₁ _ hM₂ (Or.inl (twin_mem_omegaNbr hΩ₀ hM₁ hM₂ hne hu₁ hu₂))

theorem fs_dEdgeless_iff (d : TwinCtx p f Ω K K' z) {a : G} {e₀ : ℕ}
    (h5 : 5 ≤ p ^ e₀) (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hL : IsClassicalMember p e₀ (perfectCoreIn K a) ⟨z, hzA⟩) :
    Disconnected.DEdgeless (conjFamily (perfectCoreIn K a)) ↔
      ¬ ∃ c : G, c * a = a * c ∧ c * z = z * c ∧ conjSub c K = K' := by
  constructor
  · rintro hDE ⟨c, hca, hcz, hcK⟩
    exact fs_not_dEdgeless_of_swap d hzA hL hca hcz hcK hDE
  · intro hns
    rcases fs_dEdgeless_or_swap d h5 hzA hL with h | h
    · exact h
    · exact absurd h hns

end Sec

end CFSG.ClassicalInvolution.Asc77.C25V

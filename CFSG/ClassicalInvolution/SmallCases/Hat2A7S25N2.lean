module

public import CFSG.ClassicalInvolution.Q3.Q3T7M00
public import CFSG.ClassicalInvolution.Asc77.AscC25V32
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7M2
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7M3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S.N

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.C25V
open CFSG.ClassicalInvolution.Asc77.T3
open CFSG.ClassicalInvolution.Hat2A7M.Asc77.T7F2 (Hyp25T)
open scoped MatrixGroups commutatorElement

structure TwinCtx {G : Type} [Group G] [Finite G]
    (Ω : Set (Subgroup G)) (K K' : Subgroup G) (z : G) : Prop where
  hΩ : HypOmegaGen Ω
  hK : K ∈ Ω
  hK' : K' ∈ Ω
  hI : IsUniqueInvolution K z
  hI' : IsUniqueInvolution K' z
  ne : K' ≠ K
  htw : twinSet Ω K = {K, K'}
  hperp : KPerp Ω K = {K, K'}

namespace TwinCtx

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' : Subgroup G} {z : G}

theorem conj_K (d : TwinCtx Ω K K' z) {g : G} (hg : g * z = z * g) :
    conjSub g K = K ∨ conjSub g K = K' := by
  have hgz : g * z * g⁻¹ = z := by
    calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [hg]
      _ = z := by group
  have h1 : conjSub g K ∈ twinSet Ω K :=
    ⟨d.hΩ.conjInvariant g K d.hK, z, d.hI, hgz ▸ d.hI.conj g⟩
  rw [d.htw] at h1
  exact h1

theorem conj_K' (d : TwinCtx Ω K K' z) {g : G} (hg : g * z = z * g) :
    conjSub g K' = K ∨ conjSub g K' = K' := by
  have hgz : g * z * g⁻¹ = z := by
    calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [hg]
      _ = z := by group
  have h1 : conjSub g K' ∈ twinSet Ω K :=
    ⟨d.hΩ.conjInvariant g K' d.hK', z, d.hI, hgz ▸ d.hI'.conj g⟩
  rw [d.htw] at h1
  exact h1

theorem conj_iff (d : TwinCtx Ω K K' z) {g : G} (hg : g * z = z * g) :
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

theorem nbr (d : TwinCtx Ω K K' z) {J : Subgroup G} (h : J ∈ omegaNbr Ω K) :
    J ∈ twinSet Ω K := by
  have h1 : J ∈ KPerp Ω K := Or.inr h
  rw [d.hperp] at h1
  rcases h1 with rfl | rfl
  · exact absurd rfl h.2.1
  · rw [d.htw]
    exact Or.inr rfl

theorem conj_normalizer (d : TwinCtx Ω K K' z) {y x : G} (hy : y * z = z * y)
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

section Hyp

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}

theorem twinCtx'_of_hyp25 (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t') :
    TwinCtx Ω K' K z where
  hΩ := h.hΩ
  hK := h.hK'
  hK' := h.hK
  hI := h.hz'
  hI' := h.hz
  ne := h.hs.hne.symm
  htw := by
    rw [twinSet_eq_of_mem_twinSet h.hz h.hs.hK', h.hs.twinSet_eq, Set.pair_comm]
  hperp := by
    have h1 := (CFSG.ClassicalInvolution.Q3.Q3T7M.l6_3 G Ω h.hΩ K h.hK K' h.hs.hK').1
    rw [← h1, h.hs.perp, Set.pair_comm]

theorem eq_conj_z_of_commute_order_four (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t')
    {c g y₀ : G} (hy₀ : y₀ ∈ conjSub c K') (hy4 : orderOf y₀ = 4)
    (hcomm : (g * z * g⁻¹) * y₀ = y₀ * (g * z * g⁻¹)) : g * z * g⁻¹ = c * z * c⁻¹ := by
  by_contra hne
  have hJ : conjSub c K' ∈ Ω := h.hΩ.conjInvariant c K' h.hK'
  have ha : IsUniqueInvolution (conjSub c K') (c * z * c⁻¹) := h.hz'.conj c
  exact Hat2A7M.Asc77.T7ER.not_commute_of_conj h.hs h.hyp.hW h.hyp.hE4 hJ ha hne hy₀ hy4 hcomm

end Hyp

section Sec

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)}
  {K K' : Subgroup G} {z : G}

theorem fs_omega5_conjFamily (hΩ : HypOmegaGen Ω) (hK : K ∈ Ω) (hI : IsUniqueInvolution K z)
    (a : G) :
    ∀ M₁ ∈ conjFamily (perfectCoreIn K a),
    ∀ M₂ ∈ conjFamily (perfectCoreIn K a), M₁ ≠ M₂ →
    ∀ u : ↥(Subgroup.centralizer ({a} : Set G)), IsUniqueInvolution M₁ u → ∀ v ∈ M₂,
      (¬ ∀ w ∈ M₂, v * w = w * v) → IsPGroup 2 (Subgroup.zpowers v) → v * u = u * v →
        v ∈ Subgroup.normalizer (M₁ : Set ↥(Subgroup.centralizer ({a} : Set G))) := by
  rintro _ ⟨c₁, rfl⟩ _ ⟨c₂, rfl⟩ hne u hu v hv hnc h2 hvu
  have hJne := conjSub_ne_of_ne hne
  have hu' := fs_coe_eq_of_isUniqueInvolution hI c₁ hu
  have hvJ := le_conjSub_of_mem c₂ hv
  have hnc' : ¬ ∀ w ∈ conjSub (c₂ : G) K, (v : G) * w = w * v := by
    intro h
    apply hnc
    intro w hw
    exact Subtype.ext (h _ (le_conjSub_of_mem c₂ hw))
  have h2' : IsPGroup 2 (Subgroup.zpowers (v : G)) := by
    have := h2.map (Subgroup.centralizer ({a} : Set G)).subtype
    rwa [MonoidHom.map_zpowers] at this
  have hvz : (v : G) * ((c₁ : G) * z * (c₁ : G)⁻¹) = ((c₁ : G) * z * (c₁ : G)⁻¹) * v := by
    rw [← hu']
    exact congrArg Subtype.val hvu
  have hN := hΩ.omega5 _ (hΩ.conjInvariant c₁ K hK) _ (hΩ.conjInvariant c₂ K hK) hJne _
    (hI.conj (c₁ : G)) _ hvJ hnc' h2' hvz
  exact mem_normalizer_conjSub_of c₁ v hN

theorem fs_omega4_conjFamily (hΩ : HypOmegaGen Ω) (hK : K ∈ Ω) (a : G) :
    ∀ M₁ ∈ conjFamily (perfectCoreIn K a), ∀ M₂ ∈ conjFamily (perfectCoreIn K a), M₁ ≠ M₂ →
      padicValNat 2 (Nat.card ↥(M₁ ⊓ M₂)) ≤ 1 ∧
        (padicValNat 2 (Nat.card ↥(M₁ ⊓ M₂)) = 1 → ⁅M₁, M₂⁆ ≤ oddCoreOf M₁ ⊓ oddCoreOf M₂) := by
  rintro _ ⟨c₁, rfl⟩ _ ⟨c₂, rfl⟩ hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJne := conjSub_ne_of_ne hne
  obtain ⟨h4a, h4b⟩ := hΩ.omega4 _ (hΩ.conjInvariant c₁ K hK) _ (hΩ.conjInvariant c₂ K hK) hJne
  have hdvd : Nat.card ↥(conjSub c₁ (perfectCoreIn K a) ⊓ conjSub c₂ (perfectCoreIn K a)) ∣
      Nat.card ↥(conjSub (c₁ : G) K ⊓ conjSub (c₂ : G) K) := by
    rw [Nat.card_congr (Subgroup.equivMapOfInjective _ _
      (Subgroup.centralizer ({a} : Set G)).subtype_injective).toEquiv]
    apply Subgroup.card_dvd_of_le
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨le_conjSub_of_mem c₁ hx.1, le_conjSub_of_mem c₂ hx.2⟩
  have hval : padicValNat 2 (Nat.card ↥(conjSub c₁ (perfectCoreIn K a) ⊓
      conjSub c₂ (perfectCoreIn K a))) ≤
        padicValNat 2 (Nat.card ↥(conjSub (c₁ : G) K ⊓ conjSub (c₂ : G) K)) :=
    (padicValNat_dvd_iff_le Nat.card_pos.ne').mp (pow_padicValNat_dvd.trans hdvd)
  refine ⟨hval.trans h4a, fun h1 => ?_⟩
  have hc := h4b (le_antisymm h4a (h1 ▸ hval))
  refine le_inf (commutator_le_oddCoreOf_conjFamily c₁ c₂ (hc.trans inf_le_left)) ?_
  rw [Subgroup.commutator_comm]
  refine commutator_le_oddCoreOf_conjFamily c₂ c₁ ?_
  rw [Subgroup.commutator_comm]
  exact hc.trans inf_le_right

theorem fs_hypOmegaMod_conjFamily (hΩ : HypOmegaGen Ω) (hK : K ∈ Ω)
    (hI : IsUniqueInvolution K z) {a : G} {e₀ : ℕ}
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hL : IsClassicalMember p e₀ (perfectCoreIn K a) ⟨z, hzA⟩) :
    HypOmegaMod p e₀ (conjFamily (perfectCoreIn K a)) where
  conjInvariant := by
    rintro n _ ⟨g, rfl⟩
    exact ⟨n * g, conjSub_mul _ _ _⟩
  classical := by
    rintro _ ⟨g, rfl⟩
    exact ⟨_, hL.conj g⟩
  omega4 := fs_omega4_conjFamily hΩ hK a
  omega5 := fs_omega5_conjFamily hΩ hK hI a

theorem fs_false_of_le_normalizer (d : TwinCtx Ω K K' z) {a : G}
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

theorem fs_nbr_twin (d : TwinCtx Ω K K' z) {a : G} {e₀ : ℕ} (hp : p ≠ 2) (h5 : 5 ≤ p ^ e₀)
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hL : IsClassicalMember p e₀ (perfectCoreIn K a) ⟨z, hzA⟩)
    {c₁ c₂ : ↥(Subgroup.centralizer ({a} : Set G))}
    (h : conjSub c₂ (perfectCoreIn K a) ∈
      omegaNbr (conjFamily (perfectCoreIn K a)) (conjSub c₁ (perfectCoreIn K a))) :
    conjSub (c₂ : G) K ∈ twinSet Ω (conjSub (c₁ : G) K) := by
  by_contra htw
  obtain ⟨-, hne, R₀, hR, hRle, hRN⟩ := h
  have hzKa : z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)) :=
    Subgroup.mem_subgroupOf.mp hL.mem
  obtain ⟨⟨x, hx, y, hy, hxy⟩, h8⟩ := exists_ne_comm_of_mem_rSet hp h5 hL hR
  have hR2 := isPGroup_of_mem_rSet hR
  have hne' : conjSub (c₁ : G) (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) ≠
      conjSub (c₂ : G) (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) := by
    intro h
    apply hne
    apply Subgroup.map_injective (Subgroup.centralizer ({a} : Set G)).subtype_injective
    rw [map_conjSub_perfectCore, map_conjSub_perfectCore, h]
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

theorem fs_nbr_eq (d : TwinCtx Ω K K' z) {a : G} {e₀ : ℕ} (hp : p ≠ 2) (h5 : 5 ≤ p ^ e₀)
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hL : IsClassicalMember p e₀ (perfectCoreIn K a) ⟨z, hzA⟩)
    {w : ↥(Subgroup.centralizer ({a} : Set G))} (hw : conjSub (w : G) K = K')
    {c₁ c₂ : ↥(Subgroup.centralizer ({a} : Set G))}
    (h : conjSub c₂ (perfectCoreIn K a) ∈
      omegaNbr (conjFamily (perfectCoreIn K a)) (conjSub c₁ (perfectCoreIn K a))) :
    conjSub c₂ (perfectCoreIn K a) = conjSub (c₁ * w) (perfectCoreIn K a) := by
  have htw := fs_nbr_twin d hp h5 hzA hL h
  have h1 := twinSet_conj d.hΩ.conjInvariant htw (c₁ : G)⁻¹
  rw [conjSub_inv_conjSub, d.htw] at h1
  have e1 : conjSub ((c₁ : G)⁻¹) (conjSub (c₂ : G) K) = conjSub ((c₁ : G)⁻¹ * (c₂ : G)) K := by
    rw [conjSub_mul]
  rw [e1] at h1
  rcases h1 with h1 | h1
  · exfalso
    apply h.2.1
    apply conjSub_member_eq
    have h2 := congrArg (conjSub (c₁ : G)) h1
    rw [← conjSub_mul, mul_inv_cancel_left] at h2
    exact h2
  · apply conjSub_member_eq
    have h2 := congrArg (conjSub (c₁ : G)) h1
    rw [← conjSub_mul, mul_inv_cancel_left, ← hw, ← conjSub_mul] at h2
    exact h2

theorem fs_nbr_quot (d : TwinCtx Ω K K' z) {a : G} {e₀ : ℕ} (hp : p ≠ 2) (h5 : 5 ≤ p ^ e₀)
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hL : IsClassicalMember p e₀ (perfectCoreIn K a) ⟨z, hzA⟩)
    (hΛ : HypOmegaMod p e₀ (conjFamily (perfectCoreIn K a)))
    {w : ↥(Subgroup.centralizer ({a} : Set G))} (hw : conjSub (w : G) K = K')
    (c₀ : ↥(Subgroup.centralizer ({a} : Set G)))
    {M : Subgroup (↥(conjGen (perfectCoreIn K a)) ⧸
      classicalInvolutionOddCore ↥(conjGen (perfectCoreIn K a)))}
    (hM : M ∈ omegaNbr (oddQuotientFamily (restrictFamily (conjFamily (perfectCoreIn K a))
      (conjGen (perfectCoreIn K a)))) (secImg (conjGen (perfectCoreIn K a))
        (conjSub c₀ (perfectCoreIn K a)))) :
    M = secImg (conjGen (perfectCoreIn K a)) (conjSub (c₀ * w) (perfectCoreIn K a)) := by
  obtain ⟨c, rfl⟩ := (mem_secFamily_iff (perfectCoreIn K a) M).mp hM.1
  set L := perfectCoreIn K a with hLdef
  set X := conjGen L with hX
  have hXn : X.Normal := conjGen_normal L
  have hN : Odd (Nat.card (classicalInvolutionOddCore ↥X)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥X
  have hΛ₁ : HypOmegaMod p e₀ (restrictFamily (conjFamily L) X) := hΛ.restrict X
  have hΛ' : HypOmegaMod p e₀
      (quotFamily (restrictFamily (conjFamily L) X) (classicalInvolutionOddCore ↥X)) :=
    oddQuotHyp p e₀ hp h5 ↥X _ hΛ₁ _ hN
  have hK : (conjSub c₀ L).subgroupOf X ∈ restrictFamily (conjFamily L) X :=
    ⟨conjSub c₀ L, ⟨c₀, rfl⟩, le_conjGen ⟨c₀, rfl⟩, rfl⟩
  have hJ : (conjSub c L).subgroupOf X ∈ restrictFamily (conjFamily L) X :=
    ⟨conjSub c L, ⟨c, rfl⟩, le_conjGen ⟨c, rfl⟩, rfl⟩
  obtain ⟨n, hn, hnb⟩ := exists_conj_omegaNbr hp h5 hΛ₁ hΛ' hN hK hJ hM
  rw [conjSub_subgroupOf] at hnb
  have hnL : conjSub (n : ↥(Subgroup.centralizer ({a} : Set G))) (conjSub c₀ L) ≤ X :=
    le_conjGen ⟨(n : ↥(Subgroup.centralizer ({a} : Set G))) * c₀, conjSub_mul _ _ _⟩
  have hcL : conjSub c L ≤ X := le_conjGen ⟨c, rfl⟩
  have hnb' := omegaNbr_of_restrict hnL hcL hnb
  rw [← conjSub_mul] at hnb'
  have heq := fs_nbr_eq d hp h5 hzA hL hw hnb'
  rw [heq, mul_assoc, conjSub_mul]
  exact secImg_conjSub_odd L hn (le_conjGen ⟨c₀ * w, rfl⟩)

theorem fs_swap_ne (d : TwinCtx Ω K K' z) {a : G} (hp : p ≠ 2)
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    {e₀ : ℕ} (hL : IsClassicalMember p e₀ (perfectCoreIn K a) ⟨z, hzA⟩)
    {c : ↥(Subgroup.centralizer ({a} : Set G))} (hcK : conjSub (c : G) K = K') :
    conjSub c (perfectCoreIn K a) ≠ perfectCoreIn K a := by
  have hΩ₀ := fs_hypOmegaMod_conjFamily d.hΩ d.hK d.hI hzA hL
  have hM₁ : perfectCoreIn K a ∈ conjFamily (perfectCoreIn K a) := ⟨1, conjSub_one _⟩
  have hzKa : z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)) :=
    Subgroup.mem_subgroupOf.mp hL.mem
  have hKaK : perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)) ≤ K :=
    (perfectResidualOf_le _).trans inf_le_left
  have hmap1 : (perfectCoreIn K a).map (Subgroup.centralizer ({a} : Set G)).subtype =
      perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)) := by
    have := map_conjSub_perfectCore (K := K) (a := a) 1
    simpa [conjSub_one] using this
  have hmap2 : (conjSub c (perfectCoreIn K a)).map (Subgroup.centralizer ({a} : Set G)).subtype =
      conjSub (c : G) (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) :=
    map_conjSub_perfectCore c
  intro h
  obtain ⟨P, hP, hP1, -⟩ := exists_mem_RSet_ge hM₁
    (isPGroup_two_bot' (G := ↥(Subgroup.centralizer ({a} : Set G)))) bot_le
  have h8 := hΩ₀.eight_le_of_mem_RSet hp hP
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
        conjSub (c : G) K := by
      calc (perfectCoreIn K a).map (Subgroup.centralizer ({a} : Set G)).subtype
          = (conjSub c (perfectCoreIn K a)).map
              (Subgroup.centralizer ({a} : Set G)).subtype := by rw [h]
        _ = conjSub (c : G) (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) := hmap2
        _ ≤ conjSub (c : G) K := Subgroup.map_mono hKaK
    rw [hcK] at h1
    exact (Subgroup.map_mono hPle).trans h1
  exact d.ne (d.hΩ.eq_of_le_of_le d.hK d.hK' hA2 (by omega) hAK hAK').symm

end Sec

section AE

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}

theorem aEmpty_conjFamily_perfectCore
    (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t') {a : G} {e₀ : ℕ} (hp' : p ≠ 2)
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hmem : IsClassicalMember p e₀ (perfectCoreIn K' a) ⟨z, hzA⟩) :
    ∀ M ∈ conjFamily (perfectCoreIn K' a), AEmpty (conjFamily (perfectCoreIn K' a)) M := by
  classical
  have hΛ : HypOmegaMod p e₀ (conjFamily (perfectCoreIn K' a)) :=
    fs_hypOmegaMod_conjFamily h.hΩ h.hK' h.hz' hzA hmem
  rintro M ⟨c₁, rfl⟩ J hJstar hJnbr zK zJ hzK hzJ
  exfalso
  apply hJnbr
  obtain ⟨hJΛ, hJne, U, hU, hUJ, hUN⟩ := hJstar
  obtain ⟨c₂, rfl⟩ := hJΛ
  obtain ⟨R₀, hR₀, hUR₀, hUcyc, hUidx⟩ := hU
  obtain ⟨J₃, -, hR₀syl⟩ := exists_isSylow2In_of_mem_RSet hR₀
  have h8 := hΛ.eight_le_of_mem_RSet hp' hR₀
  obtain ⟨y, hyU, hy4⟩ := exists_orderOf_four_of_cyclic hUR₀ hUcyc hUidx h8 hR₀syl.2.1
  have hyJ := hUJ hyU
  have hyN := hUN hyU
  have hy4' : orderOf (y : G) = 4 := by rw [Subgroup.orderOf_coe, hy4]
  have hyK : (y : G) ∈ conjSub (c₂ : G) K' := le_conjSub_of_mem c₂ hyJ
  have hyz : y * zK * y⁻¹ = zK := hzK.conj_eq (mem_normalizer_iff_conjSub_eq.mp hyN)
  have hzK' : (zK : G) = (c₁ : G) * z * (c₁ : G)⁻¹ := fs_coe_eq_of_isUniqueInvolution h.hz' c₁ hzK
  have hzJ' : (zJ : G) = (c₂ : G) * z * (c₂ : G)⁻¹ := fs_coe_eq_of_isUniqueInvolution h.hz' c₂ hzJ
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
  have hJMem : conjSub c₂ (perfectCoreIn K' a) ∈ conjFamily (perfectCoreIn K' a) := ⟨c₂, rfl⟩
  have hMMem : conjSub c₁ (perfectCoreIn K' a) ∈ conjFamily (perfectCoreIn K' a) := ⟨c₁, rfl⟩
  rcases mem_kPerp_of_twin hΛ hJMem hMMem hzJ hzK with hEq | hnbr
  · exact absurd hEq hJne
  · exact hnbr

end AE

end CFSG.ClassicalInvolution.Hat2A7S.N

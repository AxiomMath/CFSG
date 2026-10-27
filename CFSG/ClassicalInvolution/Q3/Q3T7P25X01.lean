module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25B00
public import CFSG.ClassicalInvolution.Q3.Q3T7LayerAEQ
public import CFSG.ClassicalInvolution.Q3.Q3T7F25M7
public import CFSG.ClassicalInvolution.Q3.Q3T7F25M6
public import CFSG.ClassicalInvolution.Q3.Q3T7P25A03

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

@[expose] def L6_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaModT Ω →
      ∀ K ∈ Ω, ∀ L ∈ twinSet Ω K,
        KPerp Ω K = KPerp Ω L ∧
          omegaStarNbr Ω K \ omegaNbr Ω K = omegaStarNbr Ω L \ omegaNbr Ω L
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ComponentClassification
open scoped commutatorElement
section Lie
variable {G : Type} [Group G]

theorem ih8_exists_noncomm [Finite G] {L : Subgroup G} {z : G} (hz : Generic.IsClassicalMember L z)
    :
    ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x :=
  hz.exists_noncomm
end Lie
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem omegaNbr_subset_kPerp_of_twin (hΩ : HypOmegaModT Ω)
    {K L : Subgroup G} (hL : L ∈ Ω) {z : G} (hzK : IsUniqueInvolution K z)
    (hzL : IsUniqueInvolution L z) : omegaNbr Ω K ⊆ KPerp Ω L := by
  rintro J ⟨hJ, hJK, R, hR, hRJ, hRN⟩
  by_cases hJL : J = L
  · exact Set.mem_insert_iff.mpr (Or.inl hJL)
  · refine Set.mem_insert_iff.mpr (Or.inr ⟨hJ, hJL, R, hR, hRJ, ?_⟩)
    obtain ⟨J', -, hRJ'⟩ := exists_isSylow2In_of_mem_RSet hR
    exact hΩ.le_normalizer_of_le_centralizer hL hJ (Ne.symm hJL) hzL hRJ hRJ'.2.1
      (by have := hΩ.eight_le_of_mem_RSet hR; omega) (le_centralizer_of_le_normalizer hzK hRN)

theorem omegaStarDiff_subset_of_twin (hΩ : HypOmegaModT Ω)
    {K L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ Ω) {z : G} (hzK : IsUniqueInvolution K z)
    (hzL : IsUniqueInvolution L z) :
    omegaStarNbr Ω K \ omegaNbr Ω K ⊆ omegaStarNbr Ω L \ omegaNbr Ω L := by
  rintro J ⟨⟨hJ, hJK, U, hU, hUJ, hUN⟩, hJnot⟩
  have hJL : J ≠ L := by
    rintro rfl
    by_cases hJK' : J = K
    · exact hJK hJK'
    · apply hJnot
      have := mem_kPerp_of_twin hΩ hL hK hzL hzK
      exact (Set.mem_insert_iff.mp this).resolve_left hJK'
  refine ⟨⟨hJ, hJL, U, hU, hUJ, ?_⟩, fun h => ?_⟩
  · have h4 := (hΩ.exists_data_of_mem_USet hU)
    obtain ⟨R, -, J', -, hRJ', hUR, -, -, h4⟩ := h4
    exact hΩ.le_normalizer_of_le_centralizer hL hJ (Ne.symm hJL) hzL hUJ
      (hRJ'.2.1.to_le hUR) (by omega) (le_centralizer_of_le_normalizer hzK hUN)
  · have := omegaNbr_subset_kPerp_of_twin hΩ hK hzL hzK h
    exact hJnot ((Set.mem_insert_iff.mp this).resolve_left hJK)

theorem l6_3 : L6_3 := by
  intro G _ _ Ω hΩ K hK L hL
  obtain ⟨hLΩ, z, hzK, hzL⟩ := hL
  have hKL := omegaNbr_subset_kPerp_of_twin hΩ hLΩ hzK hzL
  have hLK := omegaNbr_subset_kPerp_of_twin hΩ hK hzL hzK
  have hK' := mem_kPerp_of_twin hΩ hK hLΩ hzK hzL
  have hL' := mem_kPerp_of_twin hΩ hLΩ hK hzL hzK
  refine ⟨Set.Subset.antisymm ?_ ?_, Set.Subset.antisymm ?_ ?_⟩
  · exact Set.insert_subset hK' hKL
  · exact Set.insert_subset hL' hLK
  · exact omegaStarDiff_subset_of_twin hΩ hK hLΩ hzK hzL
  · exact omegaStarDiff_subset_of_twin hΩ hLΩ hK hzL hzK
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

@[expose] def C25_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ → ∀ A : Subgroup G, z ∈ A → A ≤ (S : Subgroup G) →
      (∀ s ∈ (S : Subgroup G), conjSub s A = A) →
      (∀ a ∈ A, a ≠ 1 → z ∈ zStarOf (Subgroup.centralizer ({a} : Set G))) → A = Subgroup.zpowers z

@[expose] def C25_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ →
      Nat.card ↥((S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)) ≤ 4 ∧
        (Nat.card ↥((S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)) = 4 →
          ∃ a : G, Subgroup.closure {a, z} =
              (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) ∧
            z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)) ∧
            z ∉ zStarOf (Subgroup.centralizer ({a * z} : Set G)))
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected
structure GenSection {X : Type} [Group X] (Φ : Set (Subgroup X)) :
    Prop where
  hyp : HypOmegaModT Φ
  oddCore : classicalInvolutionOddCore X = ⊥
  gen : omegaGen Φ = ⊤
  aEmpty : ∀ J ∈ Φ, AEmpty Φ J
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.AscE184Sect
section Quot
variable {Y : Type} [Group Y] [Finite Y] {Λ : Set (Subgroup Y)}
  {N : Subgroup Y} [N.Normal]

theorem map_ne_of_commutes_sylow (hΛ' : HypOmegaModT (quotFamily Λ N))
    (hN : Odd (Nat.card N)) {M₁ M₂ V₁ V₂ : Subgroup Y} (hM₁ : M₁ ∈ Λ)
    (hV₁ : IsSylow2In V₁ M₁) (hV₂ : IsSylow2In V₂ M₂) (hc : Commutes V₁ V₂) :
    M₁.map (QuotientGroup.mk' N) ≠ M₂.map (QuotientGroup.mk' N) := by
  intro heq
  set mk := QuotientGroup.mk' N with hmk
  have h1 : IsSylow2In (V₁.map mk) (M₁.map mk) := isSylow2In_map_mk hN hV₁
  have h2 : IsSylow2In (V₂.map mk) (M₁.map mk) := heq ▸ isSylow2In_map_mk hN hV₂
  have hc' : Commutes (V₁.map mk) (V₂.map mk) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hc x hx y hy]
  have hP : IsPGroup 2 ↥(V₁.map mk ⊔ V₂.map mk) :=
    h1.2.1.to_sup_of_normal_right' h2.2.1 (T7A.le_normalizer_of_commutes hc'.symm)
  have hsup : V₁.map mk ⊔ V₂.map mk ≤ M₁.map mk := sup_le h1.1 h2.1
  have hle : V₂.map mk ≤ V₁.map mk := by
    have := h1.eq_of_le hP hsup le_sup_left
    rw [← this]
    exact le_sup_right
  have heqV : V₁.map mk = V₂.map mk := h2.eq_of_le h1.2.1 h1.1 hle
  have hRset : V₁.map mk ∈ RSet (quotFamily Λ N) :=
    mem_RSet_of_isSylow2In (map_mem_quotFamily hM₁) h1
  obtain ⟨x, hx, y, hy, hxy⟩ := (hΛ'.isQuatSub_of_mem_RSet hRset).exists_not_commute
  exact hxy (hc' x hx y (heqV ▸ hy))
end Quot
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
section Basic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {z u e g : G}

theorem Hyp23Setting.perp_of_twin (h : Hyp23Setting Ω K K' z) {L : Subgroup G}
    (hL : L ∈ twinSet Ω K) : KPerp Ω L = {K, K'} := by
  have h1 := (l6_3 G Ω h.stand.modU K h.stand.mem L hL).1
  rw [← h1]
  exact h.perp
end Basic
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
    CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.Disconnected
section Lift
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {N : Subgroup G} [N.Normal]

theorem exists_conj_omegaNbr (hΩ : HypOmegaModT Ω)
    (hΩ' : HypOmegaModT (quotFamily Ω N)) (hN : Odd (Nat.card N)) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (h : J.map (QuotientGroup.mk' N) ∈
      omegaNbr (quotFamily Ω N) (K.map (QuotientGroup.mk' N))) :
    ∃ n ∈ N, J ∈ omegaNbr Ω (conjSub n K) := by
  obtain ⟨-, hne, Rb, hRb, hRbJ, hRbN⟩ := h
  obtain ⟨J₁, hJ₁, hRbsyl⟩ := exists_isSylow2In_of_mem_RSet hRb
  have hRb2 : IsPGroup 2 Rb := hRbsyl.2.1
  have h8 : 8 ≤ Nat.card Rb := hΩ'.eight_le_of_mem_RSet hRb
  have hJ₁eq : J₁ = J.map (QuotientGroup.mk' N) :=
    hΩ'.eq_of_le_of_le hJ₁ (map_mem_quotFamily hJ) hRb2 (by omega) hRbsyl.1 hRbJ
  rw [hJ₁eq] at hRbsyl
  obtain ⟨R₀, hR₀, hR₀J, -⟩ :=
    exists_mem_RSet_ge hJ (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G)) bot_le
  have hV₁ := isSylow2In_map_mk hN hR₀J
  obtain ⟨xb, hxbJ, hconj⟩ := exists_conjSub_eq_of_isSylow2In hV₁ hRbsyl
  obtain ⟨x, hxJ, hx⟩ := Subgroup.mem_map.mp hxbJ
  have hRΩ : conjSub x R₀ ∈ RSet Ω := RSet.conj hΩ.conjInvariant hR₀ x
  have hRJ : conjSub x R₀ ≤ J := by
    have := conjSub_mono (n := x) hR₀J.1
    rwa [conjSub_eq_self_of_mem hxJ] at this
  have hRmap : (conjSub x R₀).map (QuotientGroup.mk' N) = Rb := by
    rw [AscQuot.map_conjSub, hx]
    exact hconj
  have hR2 : IsPGroup 2 (conjSub x R₀) := isPGroup_conjSub x hR₀J.2.1
  obtain ⟨n, hn, hRn⟩ := Q3T7.exists_conj_normalizer3 hΩ hN hK hR2 (fun u hu =>
    hRbN (hRmap ▸ Subgroup.mem_map_of_mem _ hu))
  refine ⟨n, hn, hJ, ?_, conjSub x R₀, hRΩ, hRJ, hRn⟩
  intro hJK
  apply hne
  rw [hJK, AscQuot.map_conjSub, show QuotientGroup.mk' N n = 1 from
    (QuotientGroup.eq_one_iff _).mpr hn, conjSub_one]
end Lift
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7G2
open CFSG.ClassicalInvolution.Asc77.T7G2
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}
section Swap
variable (hyp : Asc77.Hyp25 Ω K K' W S R R' z t u₁ u₂)
include hyp

theorem not_normalizes_of_nonfused {t'' g : G} (hg : g * z * g⁻¹ = t'') (hne : z ≠ t'')
    (hnf : ¬ ∃ y : G, y * z * y⁻¹ = t'' * z) : conjSub z (conjSub g K) ≠ conjSub g K :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7G2.not_normalizes_of_nonfused hyp.toF hg hne hnf
end Swap
end T7G2
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7T
open CFSG.ClassicalInvolution.Asc77.T7T
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}

theorem exists_hyp25T (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) :
    ∃ t' : G, T7F2.Hyp25T Ω K K' W S R R' z t u₁ u₂ t' := by
  obtain ⟨t', hT⟩ := CFSG.ClassicalInvolution.T7F25.Asc77.T7T.exists_hyp25T hyp.toF
  exact ⟨t', hyp, hT.ht'S, hT.ht'2, hT.ht'R⟩
end T7T
end Asc77

end

section

namespace Asc77.T7H
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7H
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Asc77.AscE184Sect
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

@[expose] noncomputable def exactImg (Ω : Set (Subgroup G)) (c : G) (K : Subgroup G) :
    Subgroup (↥(ExactLayer.exactLayer Ω c) ⧸ classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω
        c)) :=
  ((ExactLayer.exactCore c K).subgroupOf (ExactLayer.exactLayer Ω c)).map
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω c)))

theorem exactImg_mem {K : Subgroup G} (hK : K ∈ ExactLayer.tqMembers Ω c) :
    exactImg Ω c K ∈ oddQuotientFamily (ExactLayer.exactPair Ω c) :=
  ⟨_, ⟨ExactLayer.exactCore c K, ExactLayer.exactCore_mem_exactFamily hK,
      ExactLayer.exactCore_le_exactLayer hK, rfl⟩, rfl⟩

theorem exists_exactImg_of_mem {M : Subgroup (↥(ExactLayer.exactLayer Ω c) ⧸
    classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω c))} (hM : M ∈ oddQuotientFamily
        (ExactLayer.exactPair Ω c)) :
    ∃ J ∈ ExactLayer.tqMembers Ω c, M = exactImg Ω c J := by
  obtain ⟨_, ⟨L, ⟨J, hJ, rfl⟩, hLY, rfl⟩, rfl⟩ := hM
  exact ⟨J, hJ, rfl⟩

theorem exactImg_conjSub_odd {K : Subgroup G} {n : ↥(ExactLayer.exactLayer Ω c)}
    (hn : n ∈ classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω c)) (hnc : (n : G) * c * (n :
        G)⁻¹ = c) :
    exactImg Ω c (conjSub (n : G) K) = exactImg Ω c K := by
  have h1 : ExactLayer.exactCore c (conjSub (n : G) K) = conjSub (n : G) (ExactLayer.exactCore c K)
      := by
    have := ExactLayer.exactCore_conjSub (n : G) c K
    rwa [hnc] at this
  unfold exactImg
  rw [h1, ← conjSub_subgroupOf, AscQuot.map_conjSub,
    show QuotientGroup.mk' (classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω c)) n = 1 from
      (QuotientGroup.eq_one_iff n).mpr hn, conjSub_one]

theorem mem_centralizer_of_mem_exactLayer {n : ↥(ExactLayer.exactLayer Ω c)} :
    (n : G) * c * (n : G)⁻¹ = c := by
  have h := Subgroup.mem_centralizer_singleton_iff.mp (ExactLayer.exactLayer_le_centralizer Ω c n.2)
  calc (n : G) * c * (n : G)⁻¹ = c * (n : G) * (n : G)⁻¹ := by rw [h]
    _ = c := by group

theorem exactImg_nbr_lift (hΩ : HypOmegaModT Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {K J : Subgroup G}
    (hK : K ∈ ExactLayer.tqMembers Ω c) (hJ : J ∈ ExactLayer.tqMembers Ω c)
    (h : exactImg Ω c J ∈ omegaNbr (oddQuotientFamily (ExactLayer.exactPair Ω c)) (exactImg Ω c K))
        :
    ∃ n : ↥(ExactLayer.exactLayer Ω c), n ∈ classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω c)
        ∧
      J ∈ omegaNbr Ω (conjSub (n : G) K) := by
  set Y := ExactLayer.exactLayer Ω c with hY
  set N₀ := classicalInvolutionOddCore ↥Y with hN₀
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hΛ : HypOmegaModT (ExactLayer.exactPair Ω c) := ExactLayer.hypOmegaMod_exactPair hΩ hc2
  have hΛ' : HypOmegaModT (quotFamily (ExactLayer.exactPair Ω c) N₀) :=
    T3CII.hypOmegaModU_oddQuotientFamily hΛ
  have hKY : (ExactLayer.exactCore c K).subgroupOf Y ∈ ExactLayer.exactPair Ω c :=
    ⟨ExactLayer.exactCore c K, ExactLayer.exactCore_mem_exactFamily hK,
        ExactLayer.exactCore_le_exactLayer hK, rfl⟩
  have hJY : (ExactLayer.exactCore c J).subgroupOf Y ∈ ExactLayer.exactPair Ω c :=
    ⟨ExactLayer.exactCore c J, ExactLayer.exactCore_mem_exactFamily hJ,
        ExactLayer.exactCore_le_exactLayer hJ, rfl⟩
  obtain ⟨n, hn, hnb⟩ := exists_conj_omegaNbr hΛ hΛ' hN₀odd hKY hJY h
  refine ⟨n, hn, ?_⟩
  have hnc : (n : G) * c * (n : G)⁻¹ = c := mem_centralizer_of_mem_exactLayer
  have hncent : (n : G) ∈ Subgroup.centralizer ({c} : Set G) :=
    ExactLayer.exactLayer_le_centralizer Ω c n.2
  rw [conjSub_subgroupOf] at hnb
  have hK'Y : conjSub (n : G) (ExactLayer.exactCore c K) ≤ Y := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have h1 : (n : G)⁻¹ * x * (n : G) ∈ Y := ExactLayer.exactCore_le_exactLayer hK hx
    have h2 := Y.mul_mem (Y.mul_mem n.2 h1) (Y.inv_mem n.2)
    simpa [mul_assoc] using h2
  have hJ'Y : ExactLayer.exactCore c J ≤ Y := ExactLayer.exactCore_le_exactLayer hJ
  have h3 : ExactLayer.exactCore c J ∈ omegaNbr (ExactLayer.exactFamily Ω c) (conjSub (n : G)
      (ExactLayer.exactCore c K)) :=
    omegaNbr_of_restrict hK'Y hJ'Y hnb
  have hK'' : conjSub (n : G) K ∈ ExactLayer.tqMembers Ω c :=
    ExactLayer.conjSub_mem_tqMembers hΩ.conjInvariant hncent hK
  have h4 : ExactLayer.exactCore c (conjSub (n : G) K) = conjSub (n : G) (ExactLayer.exactCore c K)
      := by
    have := ExactLayer.exactCore_conjSub (n : G) c K
    rwa [hnc] at this
  refine ExactLayer.mem_omegaNbr_of_exactFamily hΩ hc2 hK'' hJ ?_
  rw [h4]
  exact h3

theorem exactImg_nbr_eq (hΩ : HypOmegaModT Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {K K' : Subgroup G} (hK : K ∈ ExactLayer.tqMembers Ω c)
    (hperp : KPerp Ω K = {K, K'}) {J : Subgroup G} (hJ : J ∈ ExactLayer.tqMembers Ω c)
    (h : exactImg Ω c J ∈ omegaNbr (oddQuotientFamily (ExactLayer.exactPair Ω c)) (exactImg Ω c K))
        :
    exactImg Ω c J = exactImg Ω c K' := by
  obtain ⟨n, hn, hnb⟩ := exactImg_nbr_lift hΩ hc2 hK hJ h
  have hnc : (n : G) * c * (n : G)⁻¹ = c := mem_centralizer_of_mem_exactLayer
  have h1 := omegaNbr_conj hΩ.conjInvariant hnb (n : G)⁻¹
  rw [conjSub_inv_conjSub] at h1
  have h2 : conjSub (n : G)⁻¹ J ∈ KPerp Ω K := Set.mem_insert_of_mem _ h1
  rw [hperp] at h2
  have h3 : conjSub (n : G)⁻¹ J = K' := by
    rcases h2 with h2 | h2
    · exact absurd h2 h1.2.1
    · exact h2
  have h4 : J = conjSub (n : G) K' := by
    rw [← h3, conjSub_conjSub_inv]
  rw [h4]
  exact exactImg_conjSub_odd hn hnc
end Asc77.T7H

end

section

namespace Asc77.T7H
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7H
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Asc77.AscE184Sect
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem isUniqueInvolution_exactCore (hΩ : HypOmegaModT Ω)
    (hcpg : IsPGroup 2 (Subgroup.zpowers c)) {K : Subgroup G} (hK : K ∈ ExactLayer.tqMembers Ω c)
        {z : G}
    (hz : IsUniqueInvolution K z) : IsUniqueInvolution (ExactLayer.exactCore c K) z :=
  ExactLayer.isUniqueInvolution_exactCore' hΩ hcpg hK hz

@[expose] noncomputable def toBar (Ω : Set (Subgroup G)) (c x : G) (hx : x ∈ ExactLayer.exactLayer
    Ω c) :
    ↥(ExactLayer.exactLayer Ω c) ⧸ classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω c) :=
  QuotientGroup.mk' (classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω c)) ⟨x, hx⟩

theorem mem_exactImg {K : Subgroup G} {x : G} (hxK : x ∈ ExactLayer.exactCore c K)
    (hx : x ∈ ExactLayer.exactLayer Ω c) : toBar Ω c x hx ∈ exactImg Ω c K :=
  Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxK)

theorem exactImg_isUnique (hΩ : HypOmegaModT Ω)
    (hcpg : IsPGroup 2 (Subgroup.zpowers c)) {K : Subgroup G} (hK : K ∈ ExactLayer.tqMembers Ω c)
        {z : G}
    (hz : IsUniqueInvolution K z) (hzE : z ∈ ExactLayer.exactLayer Ω c) :
    IsUniqueInvolution (exactImg Ω c K) (toBar Ω c z hzE) := by
  have hz' := isUniqueInvolution_exactCore hΩ hcpg hK hz
  have h1 := isUniqueInvolution_subgroupOf hz' (ExactLayer.exactCore_le_exactLayer hK)
  exact isUniqueInvolution_map_mk_of_odd
    (odd_natCard_inf (CFSG.ComponentClassification.OddCore.odd_card ↥(ExactLayer.exactLayer Ω c))
        _) h1
end Asc77.T7H

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7T
open CFSG.ClassicalInvolution.Asc77.T7T
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' : Subgroup G} {z : G}

theorem twin_sq (hs : Hyp23Setting Ω K K' z) {x : G} (hx : x * z * x⁻¹ = z) :
    conjSub (x * x) K = K :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7T.twin_sq hs.toF hx

theorem c25_5_proved : C25_5 := by
    intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp
    exact CFSG.ClassicalInvolution.T7F25.Asc77.T7T.c25_5_proved G Ω K K' W S R R' z t u₁ u₂ hyp.toF
end T7T
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
    CFSG.ClassicalInvolution.Disconnected
variable (p : ℕ)
variable {p}
namespace T7L
open CFSG.ClassicalInvolution.Asc77.T7L
variable {f : ℕ} {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

noncomputable def toModelOfGen (hΦ : HypOmegaModT Φ) (D : OmegaLie 3 1 Φ) (hcard : D.card = 1)
    (hgen : omegaGen Φ = ⊤) (i : Fin D.card) :
    Ih8Model 3 1 Φ (D.tag i) (D.rank i) (D.exp i) where
  isFundTag := D.isFundTag i
  admissible := D.admissible i
  exp_eq := D.exp_eq i
  ψ := D.hom i
  ker_le_center := D.ker_le_center i
  surj := D.hom_surjective_of_gen hcard hgen i
  cls := D.cls i
  cls_sub := fun _ hR => hR.1
  mem_iff := fun _ => D.mem_iff_exists_cls hcard i
  cls_conj := fun _ hR g => D.cls_conj hΦ.conjInvariant i hR g
end T7L
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7T
open CFSG.ClassicalInvolution.Asc77.T7T
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ : G}

theorem perm_R_of_hyp (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {s : G}
    (hs : s ∈ (S : Subgroup G)) {X : Subgroup G} (hX : X = R ∨ X = R') :
    conjSub s X = R ∨ conjSub s X = R' := by
  have hΩ : HypOmegaModT Ω := hyp.std.setting.stand.modU
  have hXmem : X ∈ RSet Ω := by rcases hX with rfl | rfl; exacts [hyp.hR.1, hyp.hR'.1]
  have hXS : X ≤ (S : Subgroup G) := by rcases hX with rfl | rfl; exacts [hyp.hR.2.2, hyp.hR'.2.2]
  have hmem : conjSub s X ∈ RSet Ω := RSet.conj hΩ.conjInvariant hXmem s
  have hle : conjSub s X ≤ (S : Subgroup G) := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have h1 : s * (s⁻¹ * x * s) * s⁻¹ ∈ (S : Subgroup G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hs (hXS hx)) (Subgroup.inv_mem _ hs)
    simpa [mul_assoc] using h1
  exact hyp.hRS _ hmem hle

theorem conjSub_sup_of_hyp (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {s : G}
    (hs : s ∈ (S : Subgroup G)) : conjSub s (R ⊔ R') = R ⊔ R' := by
  have hne : R ≠ R' := T7ER.ne_of_hyp25 hyp
  rw [T7F2.conjSub_sup']
  rcases perm_R_of_hyp hyp hs (Or.inl rfl : R = R ∨ R = R') with h | h
  · have h' : conjSub s R' = R' := by
      rcases perm_R_of_hyp hyp hs (Or.inr rfl : R' = R ∨ R' = R') with h' | h'
      · exact absurd (conjSub_injective s (h.trans h'.symm)) hne
      · exact h'
    rw [h, h']
  · have h' : conjSub s R' = R := by
      rcases perm_R_of_hyp hyp hs (Or.inr rfl : R' = R ∨ R' = R') with h' | h'
      · exact h'
      · exact absurd (conjSub_injective s (h.trans h'.symm)) hne
    rw [h, h', sup_comm]

theorem conjSub_centralizer_of_hyp (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {s : G}
    (hs : s ∈ (S : Subgroup G)) :
    conjSub s ((S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)) =
      (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) := by
  rw [T7F2.conjSub_inf_centralizer, conjSub_eq_self_of_mem hs, conjSub_sup_of_hyp hyp hs]

theorem z_mem_centralizer_of_hyp (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) :
    z ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) := by
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hΩ : HypOmegaModT Ω := hs.stand.modU
  have hK : K ∈ Ω := hs.stand.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hΩ hK hyp.hR.1 hyp.hR.2.1
  have hR'syl : IsSylow2In R' K' :=
    T7C.isSylow2In_of_mem_RSet_of_le hΩ hK' hyp.hR'.1 hyp.hR'.2.1
  have h8 := (hΩ.isQuatSub_of_mem_RSet hyp.hR.1).eight_le
  have h8' := (hΩ.isQuatSub_of_mem_RSet hyp.hR'.1).eight_le
  have hzR : z ∈ R := mem_of_isUniqueInvolution_of_isPGroup hz hyp.hR.2.1 hRsyl.2.1 (by omega)
  have hzR' : z ∈ R' := mem_of_isUniqueInvolution_of_isPGroup hz' hyp.hR'.2.1 hR'syl.2.1 (by omega)
  have hle : R ⊔ R' ≤ Subgroup.centralizer ({z} : Set G) :=
    sup_le (hyp.hR.2.1.trans (AscP1Nine3.le_centralizer_of_uniqueInvolution hz))
      (hyp.hR'.2.1.trans (AscP1Nine3.le_centralizer_of_uniqueInvolution hz'))
  refine ⟨hyp.hR.2.2 hzR, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
  have := Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  exact this
end T7T
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
open scoped commutatorElement
namespace C25X
open CFSG.ClassicalInvolution.Asc77.C25X
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {z : G}

theorem layer_a_frame {S : Sylow 2 G} {R R' : Subgroup G} {t u₁ u₂ : G}
    (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (haR : ∀ x ∈ R, a * x = x * a) (haR' : ∀ x ∈ R', a * x = x * a) :
    ∃ (hzY : z ∈ ExactLayer.exactLayer Ω a) (hu₁Y : u₁ ∈ ExactLayer.exactLayer Ω a) (hu₂Y : u₂ ∈
        ExactLayer.exactLayer Ω a),
      K ∈ ExactLayer.tqMembers Ω a ∧ K' ∈ ExactLayer.tqMembers Ω a ∧
      GenSection (oddQuotientFamily (ExactLayer.exactPair Ω a)) ∧
      Nat.card (↥(ExactLayer.exactLayer Ω a) ⧸ classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω
          a)) < Nat.card G ∧
      TwinSect0 (oddQuotientFamily (ExactLayer.exactPair Ω a)) (T7H.exactImg Ω a K) (T7H.exactImg Ω
          a K')
        (T7H.toBar Ω a z hzY) (T7H.toBar Ω a u₁ hu₁Y) (T7H.toBar Ω a u₂ hu₂Y) := by
  classical
  obtain ⟨t', h⟩ := T7T.exists_hyp25T hyp
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hst := hs.stand
  have hΩ : HypOmegaModT Ω := hst.modU
  have hKΩ : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hzK : IsUniqueInvolution K z := hs.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  have hcpg : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_sq_eq_one ha2
  have hRsyl : IsSylow2In R K := h.hRsyl
  have hR'syl : IsSylow2In R' K' := h.hR'syl
  have hRc : R ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (haR x hx).symm
  have hR'c : R' ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (haR' x hx).symm
  have hK₂ : K ∈ ExactLayer.tqMembers Ω a :=
    (ExactLayer.mem_tqMembers_iff_exists_sylow hΩ hcpg).mpr ⟨hKΩ, R, hRsyl, hRc⟩
  have hK₂' : K' ∈ ExactLayer.tqMembers Ω a :=
    (ExactLayer.mem_tqMembers_iff_exists_sylow hΩ hcpg).mpr ⟨hK'Ω, R', hR'syl, hR'c⟩
  have hS₂ : IsSylow2In R (ExactLayer.exactCore a K) :=
    (ExactLayer.isSylow2In_exactCore_iff hΩ hcpg hKΩ hK₂.2).mpr ⟨hRsyl, hRc⟩
  have hS₂' : IsSylow2In R' (ExactLayer.exactCore a K') :=
    (ExactLayer.isSylow2In_exactCore_iff hΩ hcpg hK'Ω hK₂'.2).mpr ⟨hR'syl, hR'c⟩
  have hu₁R : u₁ ∈ R := hyp.hu₁.1
  have hu₂R' : u₂ ∈ R' := hyp.hu₂.1
  have hu₁sq : u₁ * u₁ = z := Asc77.C25X.sq_eq_of_orderOf_four hzK (hRsyl.1 hu₁R) hyp.hu₁.2.1
  have hu₂sq : u₂ * u₂ = z := Asc77.C25X.sq_eq_of_orderOf_four hzK' (hR'syl.1 hu₂R') hyp.hu₂.2.1
  set Y := ExactLayer.exactLayer Ω a with hY
  set N₀ := classicalInvolutionOddCore ↥Y with hN₀
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hΛ : HypOmegaModT (ExactLayer.exactPair Ω a) := ExactLayer.hypOmegaMod_exactPair hΩ hcpg
  have hΦ : HypOmegaModT (oddQuotientFamily (ExactLayer.exactPair Ω a)) :=
    T3CII.hypOmegaModU_oddQuotientFamily hΛ
  have hzc : z ∈ ExactLayer.exactCore a K := (T7H.isUniqueInvolution_exactCore hΩ hcpg hK₂ hzK).mem
  have hzY : z ∈ Y := ExactLayer.exactCore_le_exactLayer hK₂ hzc
  have hu₁c : u₁ ∈ ExactLayer.exactCore a K := hS₂.1 hu₁R
  have hu₂c : u₂ ∈ ExactLayer.exactCore a K' := hS₂'.1 hu₂R'
  have hu₁Y : u₁ ∈ Y := ExactLayer.exactCore_le_exactLayer hK₂ hu₁c
  have hu₂Y : u₂ ∈ Y := ExactLayer.exactCore_le_exactLayer hK₂' hu₂c
  have hperp' : KPerp Ω K' = {K', K} := by rw [hs.perp_of_twin hs.hK', Set.pair_comm]
  have hA : T7H.exactImg Ω a K ∈ oddQuotientFamily (ExactLayer.exactPair Ω a) := T7H.exactImg_mem
      hK₂
  have hA' : T7H.exactImg Ω a K' ∈ oddQuotientFamily (ExactLayer.exactPair Ω a) := T7H.exactImg_mem
      hK₂'
  have hzA := T7H.exactImg_isUnique hΩ hcpg hK₂ hzK hzY
  have hzA' := T7H.exactImg_isUnique hΩ hcpg hK₂' hzK' hzY
  have hne : T7H.exactImg Ω a K ≠ T7H.exactImg Ω a K' := by
    refine map_ne_of_commutes_sylow (N := N₀) hΦ hN₀odd
      (M₁ := (ExactLayer.exactCore a K).subgroupOf Y) (M₂ := (ExactLayer.exactCore a K').subgroupOf
          Y)
      (V₁ := R.subgroupOf Y) (V₂ := R'.subgroupOf Y)
      ⟨_, ExactLayer.exactCore_mem_exactFamily hK₂, ExactLayer.exactCore_le_exactLayer hK₂, rfl⟩
      (hS₂.subgroupOf (ExactLayer.exactCore_le_exactLayer hK₂))
      (hS₂'.subgroupOf (ExactLayer.exactCore_le_exactLayer hK₂')) ?_
    intro x hx y hy
    exact Subtype.ext (h.hcomm x (Subgroup.mem_subgroupOf.mp hx) y (Subgroup.mem_subgroupOf.mp hy))
  have hnbA : ∀ M ∈ oddQuotientFamily (ExactLayer.exactPair Ω a),
      M ∈ omegaNbr (oddQuotientFamily (ExactLayer.exactPair Ω a)) (T7H.exactImg Ω a K) →
        M = T7H.exactImg Ω a K' := by
    intro M hM hMn
    obtain ⟨J, hJ, rfl⟩ := T7H.exists_exactImg_of_mem hM
    exact T7H.exactImg_nbr_eq hΩ hcpg hK₂ hs.perp hJ hMn
  have hnbA' : ∀ M ∈ oddQuotientFamily (ExactLayer.exactPair Ω a),
      M ∈ omegaNbr (oddQuotientFamily (ExactLayer.exactPair Ω a)) (T7H.exactImg Ω a K') →
        M = T7H.exactImg Ω a K := by
    intro M hM hMn
    obtain ⟨J, hJ, rfl⟩ := T7H.exists_exactImg_of_mem hM
    exact T7H.exactImg_nbr_eq hΩ hcpg hK₂' hperp' hJ hMn
  have hgen : omegaGen (oddQuotientFamily (ExactLayer.exactPair Ω a)) = ⊤ :=
    omegaGen_quotFamily_eq_top (ExactLayer.exactPair Ω a) N₀
      (omegaGen_restrictFamily_eq_top (ExactLayer.exactFamily Ω a) Y (ExactLayer.exactLayer_eq_iSup
          Ω a).symm)
  have hAΩ : ∀ M ∈ Ω, AEmpty Ω M := hst.aEmpty
  have hAΛ : ∀ L ∈ ExactLayer.exactPair Ω a, AEmpty (ExactLayer.exactPair Ω a) L := by
    have h0 := aEmpty_exactPair hΩ hAΩ hcpg
    have e0 : centralizingMembers (ExactLayer.exactFamily Ω a) {a} = ExactLayer.exactFamily Ω a :=
      ExactLayer.centMembers_exactFamily Ω a
    rw [e0] at h0
    exact h0
  have hAΦ : ∀ L ∈ oddQuotientFamily (ExactLayer.exactPair Ω a),
      AEmpty (oddQuotientFamily (ExactLayer.exactPair Ω a)) L :=
    Q3T7.aEmpty_quotFamily3 hΛ (Q3T7P25.hyp_of_modU hΦ) hN₀odd hAΛ
  have hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G := by
    intro hsub
    obtain ⟨z₀, hz₀⟩ := hΩ.classical K hKΩ
    obtain ⟨x, -, y, -, hxy⟩ := ih8_exists_noncomm hz₀
    have hacen : a ∈ Subgroup.center G := hsub (Set.mem_singleton a)
    exact ha1 (T7B.eq_one_of_central ⟨x, y, hxy⟩
      (fun g' => Subgroup.mem_center_iff.mp hacen g'))
  have hlt : Nat.card (↥Y ⧸ N₀) < Nat.card G := by
    have h1 : Nat.card (↥Y ⧸ N₀) ≤ Nat.card ↥Y :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card N₀)
    have h2 : Nat.card ↥Y < Nat.card G := ExactLayer.card_exactLayer_lt hnc
    omega
  have haB : T7H.toBar Ω a u₁ hu₁Y ∈ T7H.exactImg Ω a K := T7H.mem_exactImg hu₁c hu₁Y
  have hbB : T7H.toBar Ω a u₂ hu₂Y ∈ T7H.exactImg Ω a K' := T7H.mem_exactImg hu₂c hu₂Y
  have haBsq : T7H.toBar Ω a u₁ hu₁Y * T7H.toBar Ω a u₁ hu₁Y = T7H.toBar Ω a z hzY := by
    have h1 : (⟨u₁, hu₁Y⟩ : ↥Y) * ⟨u₁, hu₁Y⟩ = ⟨z, hzY⟩ := Subtype.ext hu₁sq
    unfold T7H.toBar
    rw [← map_mul, h1]
  have hbBsq : T7H.toBar Ω a u₂ hu₂Y * T7H.toBar Ω a u₂ hu₂Y = T7H.toBar Ω a z hzY := by
    have h1 : (⟨u₂, hu₂Y⟩ : ↥Y) * ⟨u₂, hu₂Y⟩ = ⟨z, hzY⟩ := Subtype.ext hu₂sq
    unfold T7H.toBar
    rw [← map_mul, h1]
  exact ⟨hzY, hu₁Y, hu₂Y, hK₂, hK₂',
    ⟨hΦ, CFSG.ComponentClassification.OddCore.quotient_corefree ↥Y, hgen, hAΦ⟩, hlt,
    ⟨hA, hA', hne, hzA, hzA', haB, hbB, haBsq, hbBsq, hnbA, hnbA'⟩⟩
end C25X
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8

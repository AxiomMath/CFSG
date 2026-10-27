module

public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraComponents
public import CFSG.Quasithin.Background.A3Structure36AQuasi
import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase
public import CFSG.Quasithin.Background.A3Structure36ABasic
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Vol2.Ch1List
public import CFSG.Quasithin.Vol2.Ch1Rank

public section

namespace CFSG.QuasithinUnique.Vol2Native

open CFSG.Open
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_1_three lemma_1_2_2_b
  Lemma122A lemma_1_2_4_exists lemma_1_2_4_unique lemma_1_2_4_existsUnique lemma_1_2_4_normal
  lemma_1_2_4_list normal_conjClosure_of_pCoreOf_ne_bot

section Generic

variable {G : Type} [Group G]

theorem zpow_eq_one_or_self {z : G} (hz2 : z ^ 2 = 1) (k : ℤ) : z ^ k = 1 ∨ z ^ k = z := by
  have h2 : z ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact hz2
  obtain ⟨n, hn | hn⟩ := Int.even_or_odd' k
  · left
    rw [hn, zpow_mul, h2, one_zpow]
  · right
    rw [hn, zpow_add_one, zpow_mul, h2, one_zpow, one_mul]

theorem commutator_zpowers_le_centralizer_of_inverts {X V : Subgroup G} {z : G} (hz2 : z ^ 2 = 1)
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) (hzV : ∀ v ∈ V, z⁻¹ * v * z = v⁻¹) :
    ⁅X, Subgroup.zpowers z⁆ ≤ Subgroup.centralizer (V : Set G) := by
  have hzz : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hz2)
  refine Subgroup.commutator_le.mpr fun x hx g hg => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  rcases zpow_eq_one_or_self hz2 k with hk | hk
  · rw [hk, commutatorElement_one_right]
    exact Subgroup.one_mem _
  · rw [hk, Subgroup.mem_centralizer_iff]
    intro v hv
    have hu : x⁻¹ * v⁻¹ * x ∈ V :=
      (Subgroup.mem_normalizer_iff''.mp (hXV hx) v⁻¹).mp (V.inv_mem hv)
    have e1 : z⁻¹ * v * z = v⁻¹ := hzV v hv
    have e2 : z⁻¹ * (x⁻¹ * v⁻¹ * x) * z = (x⁻¹ * v⁻¹ * x)⁻¹ := hzV _ hu
    have h : z * (x⁻¹ * v⁻¹ * x) * z⁻¹ = x⁻¹ * v * x := by
      calc z * (x⁻¹ * v⁻¹ * x) * z⁻¹ = z⁻¹ * (x⁻¹ * v⁻¹ * x) * z := by rw [hzz]
        _ = (x⁻¹ * v⁻¹ * x)⁻¹ := e2
        _ = x⁻¹ * v * x := by group
    rw [commutatorElement_def]
    symm
    calc x * z * x⁻¹ * z⁻¹ * v
        = x * z * x⁻¹ * (z⁻¹ * v * z) * z⁻¹ := by group
      _ = x * z * x⁻¹ * v⁻¹ * z⁻¹ := by rw [e1]
      _ = x * (z * (x⁻¹ * v⁻¹ * x) * z⁻¹) * (z * x⁻¹ * z⁻¹) := by group
      _ = x * (x⁻¹ * v * x) * (z * x⁻¹ * z⁻¹) := by rw [h]
      _ = v * (x * z * x⁻¹ * z⁻¹) := by group

theorem commutator_zpowers_le_centralizer_of_centralizes {X V : Subgroup G} {z : G}
    (hz2 : z ^ 2 = 1) (hXV : X ≤ Subgroup.normalizer (V : Set G))
    (hzV : ∀ v ∈ V, z⁻¹ * v * z = v) :
    ⁅X, Subgroup.zpowers z⁆ ≤ Subgroup.centralizer (V : Set G) := by
  refine Subgroup.commutator_le.mpr fun x hx g hg => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  rcases zpow_eq_one_or_self hz2 k with hk | hk
  · rw [hk, commutatorElement_one_right]
    exact Subgroup.one_mem _
  · rw [hk, Subgroup.mem_centralizer_iff]
    intro v hv
    have hu : x⁻¹ * v * x ∈ V :=
      (Subgroup.mem_normalizer_iff''.mp (hXV hx) v).mp hv
    have e1 : z⁻¹ * v * z = v := hzV v hv
    have e2 : z⁻¹ * (x⁻¹ * v * x) * z = x⁻¹ * v * x := hzV _ hu
    have h : z * (x⁻¹ * v * x) * z⁻¹ = x⁻¹ * v * x := by
      calc z * (x⁻¹ * v * x) * z⁻¹ = z * (z⁻¹ * (x⁻¹ * v * x) * z) * z⁻¹ := by rw [e2]
        _ = x⁻¹ * v * x := by group
    rw [commutatorElement_def]
    symm
    calc x * z * x⁻¹ * z⁻¹ * v
        = x * z * x⁻¹ * (z⁻¹ * v * z) * z⁻¹ := by group
      _ = x * z * x⁻¹ * v * z⁻¹ := by rw [e1]
      _ = x * (z * (x⁻¹ * v * x) * z⁻¹) * (z * x⁻¹ * z⁻¹) := by group
      _ = x * (x⁻¹ * v * x) * (z * x⁻¹ * z⁻¹) := by rw [h]
      _ = v * (x * z * x⁻¹ * z⁻¹) := by group

theorem le_centralizer_symm {A B : Subgroup G} (h : A ≤ Subgroup.centralizer (B : Set G)) :
    B ≤ Subgroup.centralizer (A : Set G) := fun b hb =>
  Subgroup.mem_centralizer_iff.mpr fun _ ha => (Subgroup.mem_centralizer_iff.mp (h ha) b hb).symm

theorem le_normalizer_oddCoreOf (H : Subgroup G) [Finite G] :
    H ≤ Subgroup.normalizer (A37.oddCoreOf H : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact A37.conj_mem_oddCoreOf (Subgroup.le_normalizer hg) hx
  · intro hx
    have := A37.conj_mem_oddCoreOf (Subgroup.le_normalizer (H.inv_mem hg)) hx
    simpa [mul_assoc] using this

end Generic

section CComponent

variable {G : Type} [Group G] [Finite G]

theorem le_of_normal_of_perfect_le {N LQ B K : Subgroup G} (hLQ : LQ ∈ cComp N) (hBLQ : B ≤ LQ)
    (hBn : (B.subgroupOf LQ).Normal) (hKB : K ≤ B) (hK : K ≠ ⊥) (hKp : ⁅K, K⁆ = K) : LQ ≤ B := by
  have hP : ⁅perfectCore B, perfectCore B⁆ = perfectCore B := perfectCore_perfect B
  have hKP : K ≤ perfectCore B := le_perfectCore_of_perfect hKB hKp
  have hPne : perfectCore B ≠ ⊥ := fun h => hK (le_bot_iff.mp (h ▸ hKP))
  have hsub : IsSubnormal (perfectCore B) N :=
    A3.subnormal_trans (A3.subnormal_perfectCore (A3.subnormal_of_normal hBLQ hBn))
      (subnormal_of_mem_cComp hLQ)
  by_contra hnot
  have hlt : perfectCore B < LQ :=
    lt_of_le_of_ne ((perfectCore_le B).trans hBLQ) fun h => hnot (h ▸ perfectCore_le B)
  exact not_subnormal_of_mem_cComp hLQ hlt hPne hP hsub

theorem le_centralizer_of_mem_cComp {N LQ L V : Subgroup G} (hLQ : LQ ∈ cComp N) (hL : L ≤ LQ)
    (hL0 : L ≠ ⊥) (hLp : ⁅L, L⁆ = L) (hVN : N ≤ Subgroup.normalizer (V : Set G))
    (hLV : L ≤ Subgroup.centralizer (V : Set G)) : LQ ≤ Subgroup.centralizer (V : Set G) := by
  have hLQN : LQ ≤ N := le_of_mem_cComp hLQ
  have hBLQ : LQ ⊓ Subgroup.centralizer (V : Set G) ≤ LQ := inf_le_left
  have hBn : ((LQ ⊓ Subgroup.centralizer (V : Set G)).subgroupOf LQ).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hBLQ]
    exact CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf LQ LQ _
      Subgroup.le_normalizer
      ((hLQN.trans hVN).trans
        (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer V))
  exact (le_of_normal_of_perfect_le hLQ hBLQ hBn (le_inf hL hLV) hL0 hLp).trans inf_le_right

theorem fittingSubgroup_le_pCore_sup_oddCore (X : Type) [Group X] [Finite X] :
    CFSG.fittingSubgroup X ≤ CFSG.pCore 2 X ⊔ CFSG.oddCore X :=
  CFSG.WholeGroup.fittingSubgroup_le_pCore_two_sup_oddCore

theorem isQuasisimple_of_mem_cComp_of_centralizes {N LQ L : Subgroup G} (hLQ : LQ ∈ cComp N)
    (hL : L ≤ LQ) (hL0 : L ≠ ⊥) (hLp : ⁅L, L⁆ = L)
    (hL2 : L ≤ Subgroup.centralizer (pCoreOf 2 N : Set G))
    (hLo : L ≤ Subgroup.centralizer (A37.oddCoreOf N : Set G)) : CFSG.IsQuasisimple ↥LQ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 := le_centralizer_of_mem_cComp hLQ hL hL0 hLp
    (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 N) hL2
  have ho := le_centralizer_of_mem_cComp hLQ hL hL0 hLp (le_normalizer_oddCoreOf N) hLo
  have hjoin : pCoreOf 2 N ⊔ A37.oddCoreOf N ≤ Subgroup.centralizer (LQ : Set G) :=
    sup_le (le_centralizer_symm h2) (le_centralizer_symm ho)
  have hF : CFSG.fittingSubgroup ↥LQ ≤ Subgroup.center ↥LQ := by
    intro f hf
    have hf1 := fittingSubgroup_le_pCore_sup_oddCore ↥LQ hf
    have hf2 : ((f : ↥LQ) : G) ∈ (CFSG.pCore 2 ↥LQ ⊔ CFSG.oddCore ↥LQ).map LQ.subtype :=
      Subgroup.mem_map_of_mem LQ.subtype hf1
    rw [Subgroup.map_sup] at hf2
    have hP : (CFSG.pCore 2 ↥LQ).map LQ.subtype = pCoreOf 2 LQ := by
      rfl
    have hO : (CFSG.oddCore ↥LQ).map LQ.subtype = A37.oddCoreOf LQ := rfl
    rw [hP, hO] at hf2
    have hf3 : ((f : ↥LQ) : G) ∈ pCoreOf 2 N ⊔ A37.oddCoreOf N :=
      sup_le_sup (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hLQ))
        (A37.oddCoreOf_le_of_subnormal (subnormal_of_mem_cComp hLQ)) hf2
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hjoin hf3) (y : G) y.2)
  exact A36A.isQuasisimple_of_fitting_le_center (A36A.isPerfect_of_mem_cComp hLQ)
    (A36A.simple_quotient_of_mem_cComp hLQ).1 (A36A.simple_quotient_of_mem_cComp hLQ).2 hF

end CComponent

theorem mem_cComp_of_isComponentIn {G : Type} [Group G] [Finite G] {L H : Subgroup G}
    (hL : IsComponentIn L H) : L ∈ cComp H := by
  have h2 := map_subtype_mem_cComp (mem_cComp_top_of_isComponent hL.2)
  rwa [Subgroup.map_subgroupOf_eq_of_le hL.1] at h2

theorem exists_isComponentIn_of_gamma0_overgroup (h37 : A37ForSQTKCat) (h39 : A39ForSQTKCat)
    {G : Type} [Group G] [Finite G] {T M : Subgroup G} (h : UniqueSetting G T M)
    {H S X T' : Subgroup G} {z : G} (hH : IsGamma0 M H) (hS : IsSylowTwoOf S (H ⊓ M))
    (hT' : IsSylowTwoOf T' M) (hST' : S ≤ T') (hz : z ∈ T' ⊓ Subgroup.centralizer (T' : Set G))
    (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) (hX : IsGamma0 M X) (hSX : IsSylowTwoOf S X)
    (hSXM : IsSylowTwoOf S (X ⊓ M)) (hHX : H ≤ X) {L : Subgroup G} (hL : IsComponentIn L H) :
    ∃ LQ : Subgroup G, IsComponentIn LQ X ∧ L ≤ LQ := by
  have hK : LocalSQTK G := h.qtke.1
  have hSH : IsSylowTwoOf S H := hH.isSylowTwoOf_of_inf h hS
  have hLH : L ≤ H := hL.1
  have hLc : L ∈ cComp H := mem_cComp_of_isComponentIn hL
  have hLfam : L ∈ lFamily S := cComp_mem_of_le hLc le_sup_left (sup_le hLH hSH.le)
  have hXcore : pCoreOf 2 X ≠ ⊥ := hX.isGamma.1
  have hLX : L ≤ X := hLH.trans hHX
  obtain ⟨LQ, hLQ, hLLQ⟩ := lemma_1_2_4_exists hK h37 h39 hXcore hSX hLX hLfam
  obtain ⟨hcentre, -, -⟩ := hH.center_le_of_le_sylow h hS hT' hST'
  have hzS : z ∈ S ⊓ Subgroup.centralizer (S : Set G) := hcentre hz
  obtain ⟨-, hcomm, -, -⟩ := hH.component_normalized_commutator_not_le h hS hT' hST' hz hz1 hz2 hL
  obtain ⟨-, hinv⟩ := hX.centralizer_le_and_inverts_oddCoreIn h hSXM hT' hST' hz hz1 hz2
  have hV₂S : pCoreOf 2 X ≤ S := hSX.le_of_normalizes
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 X)
    (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X)
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 X)
  have hzV₂ : ∀ v ∈ pCoreOf 2 X, z⁻¹ * v * z = v := by
    intro v hv
    have hvz : v * z = z * v := Subgroup.mem_centralizer_iff.mp hzS.2 v (hV₂S hv)
    rw [mul_assoc, hvz, inv_mul_cancel_left]
  have hL2 : L ≤ Subgroup.centralizer (pCoreOf 2 X : Set G) := by
    calc L = ⁅L, Subgroup.zpowers z⁆ := hcomm.symm
      _ ≤ _ := commutator_zpowers_le_centralizer_of_centralizes hz2
        (hLX.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X))
        hzV₂
  have hLo : L ≤ Subgroup.centralizer (A37.oddCoreOf X : Set G) := by
    calc L = ⁅L, Subgroup.zpowers z⁆ := hcomm.symm
      _ ≤ _ := commutator_zpowers_le_centralizer_of_inverts hz2
        (hLX.trans (le_normalizer_oddCoreOf X)) hinv
  have hq : CFSG.IsQuasisimple ↥LQ :=
    isQuasisimple_of_mem_cComp_of_centralizes hLQ hLLQ (ne_bot_of_mem_cComp hLc)
      (perfect_of_mem_cComp hLc) hL2 hLo
  have hLQX : LQ ≤ X := le_of_mem_cComp hLQ
  refine ⟨LQ, ⟨hLQX, ?_, ?_⟩, hLLQ⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLQX).symm hq
  · have := A3.subnormal_comap X.subtype (subnormal_of_mem_cComp hLQ)
    rw [show X.comap X.subtype = ⊤ from Subgroup.subgroupOf_self X] at this
    exact A3.subnormal_top_iff.mp this

end CFSG.QuasithinUnique.Vol2Native

module

public import CFSG.ClassicalInvolution.Q3.Q3CLBasic
public import CFSG.ClassicalInvolution.Q3.Q3CPSix67
import CFSG.ClassicalInvolution.Q3.Q3T7M00

public section

namespace CFSG.ClassicalInvolution.A7Q.Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem omegaNbr_subset_kPerp_of_twin (hΩ : HypOmegaGen Ω) {K L : Subgroup G} (hL : L ∈ Ω)
    {z : G} (hzK : IsUniqueInvolution K z) (hzL : IsUniqueInvolution L z) :
    omegaNbr Ω K ⊆ KPerp Ω L :=
  CFSG.ClassicalInvolution.Q3.Q3T7M.omegaNbr_subset_kPerp_of_twin hΩ hL hzK hzL

theorem mem_kPerp_of_twin (hΩ : HypOmegaGen Ω) {K L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ Ω)
    {z : G} (hzK : IsUniqueInvolution K z) (hzL : IsUniqueInvolution L z) : K ∈ KPerp Ω L := by
  by_cases hKL : K = L
  · exact Set.mem_insert_iff.mpr (Or.inl hKL)
  · refine Set.mem_insert_iff.mpr (Or.inr ⟨hK, hKL, ?_⟩)
    obtain ⟨R, hR, hRK, -⟩ := exists_mem_RSet_ge hK (isPGroup_two_bot (G := G)) bot_le
    exact ⟨R, hR, hRK.1, fun x hx =>
      Sec6Gen.le_normalizer_of_twin hΩ hK hL hKL hzK hzL (hRK.1 hx)⟩

theorem kPerp_eq_of_twin (hΩ : HypOmegaGen Ω) {K L : Subgroup G} (hK : K ∈ Ω)
    (hL : L ∈ twinSet Ω K) : KPerp Ω K = KPerp Ω L := by
  obtain ⟨hLΩ, z, hzK, hzL⟩ := hL
  exact Set.Subset.antisymm
    (Set.insert_subset (mem_kPerp_of_twin hΩ hK hLΩ hzK hzL)
      (omegaNbr_subset_kPerp_of_twin hΩ hLΩ hzK hzL))
    (Set.insert_subset (mem_kPerp_of_twin hΩ hLΩ hK hzL hzK)
      (omegaNbr_subset_kPerp_of_twin hΩ hK hzL hzK))

theorem mem_omegaOfSet_of_mem_kPerp (hΩ : HypOmegaGen Ω) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ KPerp Ω K) (hJnot : J ∉ twinSet Ω K) : J ∈ omegaOfSet Ω (twinSet Ω K) := by
  have hJΩ : J ∈ Ω := by
    rcases Set.mem_insert_iff.mp hJ with h | h
    · exact h ▸ hK
    · exact h.1
  refine ⟨hJΩ, fun L hL => ?_⟩
  have hJL : J ∈ KPerp Ω L := kPerp_eq_of_twin hΩ hK hL ▸ hJ
  rcases Set.mem_insert_iff.mp hJL with h | h
  · exact absurd (h ▸ hL) hJnot
  · exact h

theorem exists_twinSylow (hΩ : HypOmegaGen Ω) {K K' J : Subgroup G} {z : G} (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K)
    (hJ : J ∈ omegaOfSet Ω (twinSet Ω K)) :
    ∃ (S : Sylow 2 G) (R R' T : Subgroup G), IsSylow2In R K ∧ IsSylow2In R' K' ∧
      IsSylow2In T J ∧ R ≤ (S : Subgroup G) ∧ R' ≤ (S : Subgroup G) ∧ T ≤ (S : Subgroup G) ∧
      Commutes R R' ∧ Commutes R T ∧ Commutes R' T := by
  have hK'Ω : K' ∈ Ω := hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'
  have hJΩ : J ∈ Ω := hJ.1
  obtain ⟨-, hJneK, T, hT, hTJ, hTN⟩ := hJ.2 K (mem_twinSet_self hK hz)
  have hJneK' : J ≠ K' := (hJ.2 K' hK').2.1
  have hTsyl : IsSylow2In T J := Q3.Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hT hTJ
  have hT2 : IsPGroup 2 ↥T := hTsyl.2.1
  have hT8 : 8 ≤ Nat.card T := Sec6Gen.eight_le_of_mem_RSet hΩ hT
  have hTc : T ≤ Subgroup.centralizer ({z} : Set G) := le_centralizer_of_le_normalizer hz hTN
  have hTN' : T ≤ Subgroup.normalizer (K' : Set G) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hK'Ω hJΩ hJneK'.symm hzK' hTJ hT2 (by omega) hTc
  obtain ⟨R, hRsyl, hRfix⟩ := exists_sylow_normalized hT2 hTN
  have hRset : R ∈ RSet Ω := mem_RSet_of_isSylow2In hK hRsyl
  have hTnR : T ≤ Subgroup.normalizer (R : Set G) := fun x hx =>
    mem_normalizer_iff_conjSub_eq.mpr (hRfix x hx)
  have hTR2 : IsPGroup 2 ↥(T ⊔ R) := hT2.to_sup_of_normal_right' hRsyl.2.1 hTnR
  have hKN : K ≤ Subgroup.normalizer (K' : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hK hK'Ω hne.symm hz hzK'
  have hPN : T ⊔ R ≤ Subgroup.normalizer (K' : Set G) := sup_le hTN' (hRsyl.1.trans hKN)
  obtain ⟨R', hR'syl, hR'fix⟩ := exists_sylow_normalized hTR2 hPN
  have hR'set : R' ∈ RSet Ω := mem_RSet_of_isSylow2In hK'Ω hR'syl
  have hPnR' : T ⊔ R ≤ Subgroup.normalizer (R' : Set G) := fun x hx =>
    mem_normalizer_iff_conjSub_eq.mpr (hR'fix x hx)
  have hQ2 : IsPGroup 2 ↥((T ⊔ R) ⊔ R') := hTR2.to_sup_of_normal_right' hR'syl.2.1 hPnR'
  obtain ⟨S, hS⟩ := hQ2.exists_le_sylow
  have hTS : T ≤ (S : Subgroup G) := le_sup_left.trans (le_sup_left.trans hS)
  have hRS : R ≤ (S : Subgroup G) := le_sup_right.trans (le_sup_left.trans hS)
  have hR'S : R' ≤ (S : Subgroup G) := le_sup_right.trans hS
  have hRR' : R ≠ R' := by
    intro h
    have := Sec6Gen.card_le_two_of_le_inf hΩ hK hK'Ω hne.symm hRsyl.2.1 hRsyl.1 (h ▸ hR'syl.1)
    have := Sec6Gen.eight_le_of_mem_RSet hΩ hRset
    omega
  have hRT : R ≠ T := by
    intro h
    have := Sec6Gen.card_le_two_of_le_inf hΩ hK hJΩ hJneK.symm hRsyl.2.1 hRsyl.1 (h ▸ hTsyl.1)
    have := Sec6Gen.eight_le_of_mem_RSet hΩ hRset
    omega
  have hR'T : R' ≠ T := by
    intro h
    have := Sec6Gen.card_le_two_of_le_inf hΩ hK'Ω hJΩ hJneK'.symm hR'syl.2.1 hR'syl.1
      (h ▸ hTsyl.1)
    have := Sec6Gen.eight_le_of_mem_RSet hΩ hR'set
    omega
  exact ⟨S, R, R', T, hRsyl, hR'syl, hTsyl, hRS, hR'S, hTS,
    Q3.Q3CP.l67Gen G Ω hΩ S R hRset R' hR'set hRS hR'S hRR',
    Q3.Q3CP.l67Gen G Ω hΩ S R hRset T hT hRS hTS hRT,
    Q3.Q3CP.l67Gen G Ω hΩ S R' hR'set T hT hR'S hTS hR'T⟩

theorem comm_zt (hΩ : HypOmegaGen Ω) {K K' J : Subgroup G} {z u t : G}
    (h : TwinFrameData Ω K K' z u J t) : z * t = t * z := by
  obtain ⟨-, -, R, hR, hRJ, hRN⟩ := h.hJ.2 K (mem_twinSet_self h.mem h.hz)
  have hRsyl : IsSylow2In R J := Q3.Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ h.hJ.1 hR hRJ
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hR
  have htR : t ∈ R := mem_of_isUniqueInvolution_of_isPGroup h.ht hRsyl.1 hRsyl.2.1 (by omega)
  exact (Subgroup.mem_centralizer_singleton_iff.mp
    (le_centralizer_of_le_normalizer h.hz hRN htR)).symm

theorem not_mem_of_orderOf_four (hΩ : HypOmegaGen Ω) {K K' : Subgroup G} (hK : K ∈ Ω)
    (hK' : K' ∈ Ω) (hne : K' ≠ K) {x : G} (hx4 : orderOf x = 4) (hxK : x ∈ K) : x ∉ K' := by
  intro hxK'
  have h2 : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hx4]; norm_num)
  have := Sec6Gen.card_le_two_of_le_inf hΩ hK hK' hne.symm h2 (Subgroup.zpowers_le.mpr hxK)
    (Subgroup.zpowers_le.mpr hxK')
  rw [Nat.card_zpowers, hx4] at this
  omega

end CFSG.ClassicalInvolution.A7Q.Gen

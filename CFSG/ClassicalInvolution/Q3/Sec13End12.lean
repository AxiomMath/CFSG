module

public import CFSG.ClassicalInvolution.Q3.Sec13End11
public import CFSG.ClassicalInvolution.Q3.Sec13End10
import CFSG.ClassicalInvolution.Q3.TL3T28

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

private theorem e12_four_le_card {H : Subgroup G} {a b : G} (ha : a ∈ H) (hb : b ∈ H)
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    4 ≤ Nat.card H := by
  have h1a : (1 : G) ≠ a := fun h => ha1 h.symm
  have h1b : (1 : G) ≠ b := fun h => hb1 h.symm
  have h1ab : (1 : G) ≠ a * b := fun h => hne (mul_left_cancel (h.symm.trans ha2.symm)).symm
  have hab_a : a ≠ a * b := fun h => hb1 (mul_left_cancel (h.symm.trans (mul_one a).symm))
  have hab_b : b ≠ a * b := fun h => ha1 (mul_right_cancel (h.symm.trans (one_mul b).symm))
  have hab1 : a * b ≠ 1 := fun h => h1ab h.symm
  let v : Fin 4 → G := ![1, a, b, a * b]
  have hv : ∀ k, v k ∈ H := by
    intro k
    fin_cases k
    exacts [H.one_mem, ha, hb, H.mul_mem ha hb]
  have hinj : Function.Injective v := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | rfl
      | exact absurd hij h1a
      | exact absurd hij h1b
      | exact absurd hij h1ab
      | exact absurd hij ha1
      | exact absurd hij hb1
      | exact absurd hij hab1
      | exact absurd hij hne
      | exact absurd hij hne.symm
      | exact absurd hij hab_a
      | exact absurd hij hab_a.symm
      | exact absurd hij hab_b
      | exact absurd hij hab_b.symm
  have hfin : Function.Injective (fun k : Fin 4 => (⟨v k, hv k⟩ : ↥H)) :=
    fun i j hij => hinj (congrArg Subtype.val hij)
  have := Nat.card_le_card_of_injective _ hfin
  simpa using this

private theorem e12_le_centralizer {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) {z : G} (hzW : z ∈ W) :
    W ≤ Subgroup.centralizer ({z} : Set G) := by
  obtain ⟨η, hη, rfl⟩ := hW
  intro w hw
  exact Subgroup.mem_centralizer_singleton_iff.mpr (TC.etaSpan_comm hΩ hη w hw z hzW)

private theorem e12_insert_eq {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) (X : Subgroup G) :
    insert X (omegaStarNbr Ω X) = (omegaStarNbr Ω X \ omegaNbr Ω X) ∪ KPerp Ω X := by
  ext Y
  simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_diff, KPerp]
  constructor
  · rintro (rfl | hY)
    · exact Or.inr (Or.inl rfl)
    · by_cases hn : Y ∈ omegaNbr Ω X
      · exact Or.inr (Or.inr hn)
      · exact Or.inl ⟨hY, hn⟩
  · rintro (⟨hY, -⟩ | (rfl | hY))
    · exact Or.inr hY
    · exact Or.inl rfl
    · exact Or.inr (Q3T6.Mu.omegaNbr_subset_omegaStarNbr hΩ X hY)

private theorem e12_conjSub_eGroup_le {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (g : G)
    {K : Subgroup G} : conjSub g (eGroup Ω K) ≤ eGroup Ω (conjSub g K) := by
  have hle : eGroup Ω K ≤ (eGroup Ω (conjSub g K)).comap (MulAut.conj g).toMonoidHom := by
    unfold eGroup
    refine (Subgroup.closure_le _).mpr ?_
    rintro u ⟨J, hJ, hu⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    apply Subgroup.subset_closure
    refine ⟨conjSub g J, ?_, hu.conj g⟩
    rcases hJ with hJ | hJ
    · rw [hJ]
      exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (omegaStarNbr_conj hΩ hJ g)
  exact Subgroup.map_le_iff_le_comap.mpr hle

namespace EndHyp

variable {Ω : Set (Subgroup G)} (h : EndHyp Ω)
include h

theorem eGroup_le_zGroup {K : Subgroup G} (hK : K ∈ Ω) : eGroup Ω K ≤ zGroup Ω := by
  unfold eGroup zGroup
  refine Subgroup.closure_mono ?_
  rintro u ⟨J, hJ, hu⟩
  rcases hJ with hJ | hJ
  · exact ⟨K, hK, by rw [← hJ]; exact hu⟩
  · exact ⟨J, hJ.1, hu⟩

theorem mem_eGroup_of_isUniqueInvolution {K : Subgroup G} {z : G}
    (hz : IsUniqueInvolution K z) : z ∈ eGroup Ω K :=
  Subgroup.subset_closure ⟨K, Set.mem_insert _ _, hz⟩

theorem mem_eGroup_of_mem_omegaStarNbr {K J : Subgroup G} (hJ : J ∈ omegaStarNbr Ω K) {u : G}
    (hu : IsUniqueInvolution J u) : u ∈ eGroup Ω K :=
  Subgroup.subset_closure ⟨J, Set.mem_insert_of_mem _ hJ, hu⟩

theorem eGroup_conj {K : Subgroup G} (hK : K ∈ Ω) (g : G) :
    eGroup Ω (conjSub g K) = conjSub g (eGroup Ω K) := by
  refine le_antisymm ?_ (e12_conjSub_eGroup_le h.thmD.hyp.conjInvariant g)
  have h' := e12_conjSub_eGroup_le h.thmD.hyp.conjInvariant g⁻¹ (K := conjSub g K)
  rw [conjSub_inv_conjSub] at h'
  calc eGroup Ω (conjSub g K) = conjSub g (conjSub g⁻¹ (eGroup Ω (conjSub g K))) :=
        (conjSub_conjSub_inv g _).symm
    _ ≤ conjSub g (eGroup Ω K) := conjSub_mono h'

theorem card_eGroup_eq {K L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ Ω) :
    Nat.card (eGroup Ω K) = Nat.card (eGroup Ω L) := by
  obtain ⟨g, rfl⟩ := h.thmD.trans K hK L hL
  rw [h.eGroup_conj hK g]
  exact (Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective).symm

theorem eGroup_eq_of_mem_twinSet {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ twinSet Ω K) :
    eGroup Ω J = eGroup Ω K := by
  obtain ⟨hperp, hdiff⟩ := CFSG.ClassicalInvolution.Q3.Q3T7M.l6_3 G Ω h.thmD.hyp K hK J hJ
  have hset : insert K (omegaStarNbr Ω K) = insert J (omegaStarNbr Ω J) := by
    rw [e12_insert_eq h.thmD.hyp K, e12_insert_eq h.thmD.hyp J, hperp, hdiff]
  unfold eGroup
  rw [hset]

theorem eGroup_eq_of_dstarAdj (h9 : Perp9 Ω) {K J : Subgroup G} (hK : K ∈ Ω)
    (hKJ : dstarAdj Ω K J) (h4 : Nat.card (eGroup Ω K) = 4) : eGroup Ω J = eGroup Ω K := by
  obtain ⟨hJ, hadj⟩ := hKJ
  by_cases hT : J ∈ twinSet Ω K
  · exact h.eGroup_eq_of_mem_twinSet hK hT
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hK
  obtain ⟨t, ht⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hJ
  have hJK : J ∈ omegaStarNbr Ω K := by
    rcases hadj with hadj | hadj
    · exact hadj
    · exact Q3T6.Mu.omegaStarNbr_symm h.thmD.hyp hJ hK hadj
  have hKJ' : K ∈ omegaStarNbr Ω J := Q3T6.Mu.omegaStarNbr_symm h.thmD.hyp hK hJ hJK
  have hzt : z ≠ t := by
    intro hzt
    apply hT
    exact ⟨hJ, z, hz, by rw [hzt]; exact ht⟩
  have hzK : z ∈ eGroup Ω K := h.mem_eGroup_of_isUniqueInvolution hz
  have htK : t ∈ eGroup Ω K := h.mem_eGroup_of_mem_omegaStarNbr hJK ht
  have hzJ : z ∈ eGroup Ω J := h.mem_eGroup_of_mem_omegaStarNbr hKJ' hz
  have htJ : t ∈ eGroup Ω J := h.mem_eGroup_of_isUniqueInvolution ht
  have hcard : 4 ≤ Nat.card (Subgroup.closure ({z, t} : Set G)) :=
    e12_four_le_card (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      hz.sq hz.ne_one ht.ne_one hzt
  have hsubK : Subgroup.closure ({z, t} : Set G) ≤ eGroup Ω K :=
    (Subgroup.closure_le _).mpr (Set.insert_subset hzK (Set.singleton_subset_iff.mpr htK))
  have hsubJ : Subgroup.closure ({z, t} : Set G) ≤ eGroup Ω J :=
    (Subgroup.closure_le _).mpr (Set.insert_subset hzJ (Set.singleton_subset_iff.mpr htJ))
  have hJcard : Nat.card (eGroup Ω J) = 4 := by
    have := h.card_eGroup_eq hK hJ
    omega
  have hEK := Subgroup.eq_of_le_of_card_ge hsubK (by omega)
  have hEJ := Subgroup.eq_of_le_of_card_ge hsubJ (by omega)
  exact hEJ.symm.trans hEK

theorem zGroup_eq_eGroup_of_card_eq_four (h9 : Perp9 Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (h4 : Nat.card (eGroup Ω K) = 4) : zGroup Ω = eGroup Ω K := by
  have key : ∀ L, Relation.ReflTransGen (dstarAdj Ω) K L →
      L ∈ Ω ∧ eGroup Ω L = eGroup Ω K := by
    intro L hL
    induction hL with
    | refl => exact ⟨hK, rfl⟩
    | @tail b c hb hbc ih =>
      obtain ⟨hbΩ, heb⟩ := ih
      have h4b : Nat.card (eGroup Ω b) = 4 := by
        rw [heb]
        exact h4
      exact ⟨hbc.1, (h.eGroup_eq_of_dstarAdj h9 hbΩ hbc h4b).trans heb⟩
  refine le_antisymm ?_ (h.eGroup_le_zGroup hK)
  unfold zGroup
  refine (Subgroup.closure_le _).mpr ?_
  rintro u ⟨L, hL, hu⟩
  obtain ⟨-, heq⟩ := key L (h.star K hK L hL)
  have hu' := h.mem_eGroup_of_isUniqueInvolution hu
  rw [heq] at hu'
  exact hu'

private theorem e12_le_oTwoCore {L : Subgroup G} (hL : L ∈ Ω) {u : G}
    (hu : IsUniqueInvolution L u) : L ≤ oTwoCore (Subgroup.centralizer ({u} : Set G)) :=
  TC.Thin.le_pCoreOf_centralizer h.thmD.hyp h.thmD.two hL hu

private theorem e12_exists_wSet_involution {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) :
    ∃ W ∈ WSet Ω, z ∈ W ∧ ∃ t ∈ W, t ∈ eGroup Ω K ∧ t ≠ 1 ∧ t ≠ z := by
  obtain ⟨W, hW, hzW, -, U, hU, hUW, hUO⟩ := h.exists_wSet_uSet_not_le hK hz
  have hUC : U ≤ Subgroup.centralizer ({z} : Set G) :=
    hUW.trans (e12_le_centralizer h.thmD.hyp hW hzW)
  obtain ⟨R, -, J, hJ, hRJ, hUR, hcyc, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet h.thmD.hyp hU
  have hU2 : IsPGroup 2 U := Sec6Gen.isPGroup_of_mem_USet h.thmD.hyp hU
  have hUJ : U ≤ J := hUR.trans hRJ.1
  have hJK : J ≠ K := by
    rintro rfl
    exact hUO (hUJ.trans (h.e12_le_oTwoCore hJ hz))
  have hUN : U ≤ Subgroup.normalizer (K : Set G) :=
    Sec6Gen.le_normalizer_of_le_centralizer h.thmD.hyp hK hJ hJK.symm hz hUJ hU2 (by omega) hUC
  have hJs : J ∈ omegaStarNbr Ω K := ⟨hJ, hJK, U, hU, hUJ, hUN⟩
  obtain ⟨t, ht⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hJ
  obtain ⟨w, hwU, hww⟩ :=
    CFSG.ClassicalInvolution.Asc77.T3.exists_sq_eq_of_cyclic ht hUJ hcyc hU2 h4
  refine ⟨W, hW, hzW, t, ?_, h.mem_eGroup_of_mem_omegaStarNbr hJs ht, ht.ne_one, ?_⟩
  · rw [← hww]
    exact W.mul_mem (hUW hwU) (hUW hwU)
  · intro htz
    apply hUO
    have hJO := h.e12_le_oTwoCore hJ ht
    rw [htz] at hJO
    exact hUJ.trans hJO

theorem eight_le_card_eGroup (h9 : Perp9 Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    8 ≤ Nat.card (eGroup Ω K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hK
  obtain ⟨W, hW, hzW, t, htW, htE, ht1, htz⟩ := h.e12_exists_wSet_involution hK hz
  have hzE : z ∈ eGroup Ω K := h.mem_eGroup_of_isUniqueInvolution hz
  have h4le : 4 ≤ Nat.card (eGroup Ω K) :=
    e12_four_le_card hzE htE hz.sq hz.ne_one ht1 htz.symm
  by_contra hlt
  have hP : IsPGroup 2 (eGroup Ω K) :=
    (CFSG.pCore_isPGroup (p := 2) (G := G)).to_le
      ((h.eGroup_le_zGroup hK).trans h.zGroup_le_pCore)
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have h4 : Nat.card (eGroup Ω K) = 4 := by
    have hn3 : n < 3 := by
      by_contra hc
      have h8 : 8 ≤ 2 ^ n :=
        calc (8 : ℕ) = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [hn] at hlt
      omega
    interval_cases n <;> norm_num only at hn <;> omega
  have hzt2 : 4 ≤ Nat.card (Subgroup.closure ({z, t} : Set G)) :=
    e12_four_le_card (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      hz.sq hz.ne_one ht1 htz.symm
  have hsubK : Subgroup.closure ({z, t} : Set G) ≤ eGroup Ω K :=
    (Subgroup.closure_le _).mpr (Set.insert_subset hzE (Set.singleton_subset_iff.mpr htE))
  have hEq : Subgroup.closure ({z, t} : Set G) = eGroup Ω K :=
    Subgroup.eq_of_le_of_card_ge hsubK (by omega)
  have hEW : eGroup Ω K ≤ W := by
    rw [← hEq]
    exact (Subgroup.closure_le _).mpr (Set.insert_subset hzW (Set.singleton_subset_iff.mpr htW))
  have hzeroD : zGroup Ω = eGroup Ω K := h.zGroup_eq_eGroup_of_card_eq_four h9 hK h4
  have hmem : ∀ L ∈ Ω, L ≤ Subgroup.normalizer (W : Set G) := by
    intro L hL
    obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hL
    have huD : u ∈ zGroup Ω := Subgroup.subset_closure ⟨L, hL, hu⟩
    rw [hzeroD] at huD
    exact (h.mem_dSet_iff.mp (h.mem_dSet_of_mem hW hL hu (hEW huD))).2
  have hnorm : W.Normal := by
    have htop : (⊤ : Subgroup G) ≤ Subgroup.normalizer (W : Set G) := by
      rw [← h.thmD.gen]
      exact pSpan_le hmem
    exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp htop)
  exact h.wSet_ne W (wSet_eq_singleton_of_normal h.thmD.hyp h.thmD.two h.thmD.trans
    h.thmD.gen (fun hs => h.not (Or.inl hs)) hW hnorm)

end EndHyp

end CFSG.ClassicalInvolution.Q3.Sec13

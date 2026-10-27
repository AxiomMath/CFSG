module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusLink
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitMaximalFamilyCharacter
import CFSG.RankThree.PartTwo.Census.Carrier.SpinDBridge
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverModel
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelMaximal
import CFSG.Timmesfeld.Orders.ClassicalOmega

public section

namespace CFSG.AGLEmbedding.LeviBlock

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
  (native_partialBorel_eq_fullBorel)
open scoped Pointwise

theorem exists_mulEquiv_plusElementary_of_idxD (hZ : OddCenterRest) {Y : Type} [Group Y]
    [Finite Y] {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) (hD : IsLieOf IdxD (↥L ⧸ Subgroup.center ↥L)) :
    ∃ (r : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), 4 ≤ r ∧
      Nonempty (↥L ≃* ↥(orthElementaryGroup (quadPlus r K))) := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hD
  cases d
  case D r q =>
    have hq2 : q.p = 2 := hd
    obtain ⟨⟨-, hf, hr⟩, K, hKf, hKfin, hK, ⟨e'⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hq2 e
    rw [hq2] at hK
    have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
    have hr4 : 4 ≤ r := hr
    refine ⟨r, K, hKf, hKfin, inferInstance, hr4, ?_⟩
    have hZ1 : Nat.card (Subgroup.center ↥L) = 1 := by
      rcases hZ Y L hL hodd (Or.inr (Or.inl ⟨⟨_, hv⟩, hd, ⟨e⟩⟩)) with h1 | ⟨-, ⟨e6⟩⟩
      · exact h1
      · exfalso
        have h360 : (Nat.card (StatedProj (StatedOmega (StatedQuadPlus r K))) : ℤ) = 360 := by
          rw [← Nat.card_congr e'.toEquiv, Nat.card_congr e6.toEquiv, nat_card_alternatingGroup]
          simp [Nat.factorial]
        rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadPlus hr4, hK]
          at h360
        have h12 : 4 ≤ q.exponent * (r * (r - 1)) :=
          (Nat.mul_le_mul hr4 (by omega : 3 ≤ r - 1)).trans' (by norm_num) |>.trans
            (Nat.le_mul_of_pos_left _ hf)
        have hdvd : (2 : ℤ) ^ 4 ∣ 360 := by
          rw [← h360]
          refine Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _
          push_cast
          rw [← pow_mul]
          exact pow_dvd_pow 2 h12
        norm_num at hdvd
    have hbot : Subgroup.center ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ1
    exact ⟨((QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq
      hbot.symm)).trans e').trans (statedProjOmegaPlusEquiv (K := K) (by omega))⟩
  all_goals exact hd.elim

variable {r : ℕ} {K : Type} [Field K]

theorem map_swapPair_flag_of_le {i : ℕ} (hi : i ≤ r - 1) (hr : 1 ≤ r) :
    (flag r K i).map (swapPair K (⟨r - 1, by omega⟩ : Fin r) :
      (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) = flag r K i := by
  rw [flag, Submodule.map_span]
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_ofPred_eq, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    refine ⟨j, hj, (swapPair_single_of_ne _ (fun h => ?_) Sum.inl_ne_inr).symm⟩
    have := congrArg Fin.val (Sum.inl_injective h)
    simp only at this
    omega
  · rintro ⟨j, hj, rfl⟩
    refine ⟨_, ⟨j, hj, rfl⟩, swapPair_single_of_ne _ (fun h => ?_) Sum.inl_ne_inr⟩
    have := congrArg Fin.val (Sum.inl_injective h)
    simp only at this
    omega

theorem conj_mem_orthElementaryGroup {g a : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K))
    (ha : a ∈ orthElementaryGroup (quadPlus r K)) :
    g * a * g⁻¹ ∈ orthElementaryGroup (quadPlus r K) := by
  have hn := (orthogonal_elementary_normality (quadPlus r K)).2
  have haO := orthElementaryGroup_le (quadPlus r K) ha
  have h := hn.conj_mem ⟨a, haO⟩ (Subgroup.mem_subgroupOf.2 ha) ⟨g, hg⟩
  rwa [Subgroup.mem_subgroupOf] at h

theorem swapPair_inv (i : Fin r) : (swapPair K i)⁻¹ = swapPair K i :=
  inv_eq_of_mul_eq_one_right (swapPair_mul_self i)

theorem conj_swapPair_mem_borel [Finite K] (hr : 3 ≤ r)
    {b : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)} (hb : b ∈ borel r K) :
    swapPair K (⟨r - 1, by omega⟩ : Fin r) * b * swapPair K (⟨r - 1, by omega⟩ : Fin r) ∈
      borel r K := by
  rw [← native_partialBorel_eq_fullBorel r K hr] at hb ⊢
  obtain ⟨hbE, hbF⟩ := mem_flagStab.1 hb
  have hE := conj_mem_orthElementaryGroup (swapIso K (⟨r - 1, by omega⟩ : Fin r)).2 hbE
  rw [coe_swapIso, swapPair_inv] at hE
  refine mem_flagStab.2 ⟨hE, fun i hi hir => ?_⟩
  have hσ := map_swapPair_flag_of_le (K := K) hir (by omega)
  rw [map_mul_linearEquiv, map_mul_linearEquiv, hσ, hbF i hi hir, hσ]

theorem swapPair_smul_flag_top [Finite K] (hr : 3 ≤ r) :
    swapPair K (⟨r - 1, by omega⟩ : Fin r) • flag r K r = Xstar r K (by omega) ∧
      swapPair K (⟨r - 1, by omega⟩ : Fin r) • Xstar r K (by omega) = flag r K r := by
  have h : swapPair K (⟨r - 1, by omega⟩ : Fin r) • flag r K r = Xstar r K (by omega) :=
    map_swapIso_flag_top (K := K) hr
  refine ⟨h, ?_⟩
  rw [← h, smul_smul, swapPair_mul_self, one_smul]

theorem nonempty_of_map_eq_plusNodeStab {Y : Type} [Group Y] {L P : Subgroup Y} (hPL : P ≤ L)
    (hne : P ≠ L) (hr : 3 ≤ r) (ψ : ↥L ≃* ↥(orthElementaryGroup (quadPlus r K)))
    {I : Set (Fin r)}
    (hI : ((P.subgroupOf L).map ψ.toMonoidHom).map (orthElementaryGroup (quadPlus r K)).subtype =
      plusNodeStab K hr I) : I.Nonempty := by
  by_contra hemp
  rw [Set.not_nonempty_iff_eq_empty] at hemp
  rw [hemp, plusNodeStab_empty] at hI
  apply hne
  refine le_antisymm hPL fun y hy => ?_
  have hmem : ((ψ ⟨y, hy⟩ : ↥(orthElementaryGroup (quadPlus r K))) :
      (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) ∈
        ((P.subgroupOf L).map ψ.toMonoidHom).map (orthElementaryGroup (quadPlus r K)).subtype := by
    rw [hI]
    exact (ψ ⟨y, hy⟩).2
  obtain ⟨_, ⟨z, hz, rfl⟩, hzy⟩ := hmem
  have hzy' : z = ⟨y, hy⟩ := ψ.injective (Subtype.ext hzy)
  rw [hzy'] at hz
  exact Subgroup.mem_subgroupOf.1 hz

theorem map_conj_swapPair_orthElementaryGroup (hr : 1 ≤ r) :
    (orthElementaryGroup (quadPlus r K)).map
      (MulAut.conj (swapPair K (⟨r - 1, by omega⟩ : Fin r))).toMonoidHom =
      orthElementaryGroup (quadPlus r K) := by
  have hc : ∀ g ∈ orthElementaryGroup (quadPlus r K), (MulAut.conj (swapPair K
      (⟨r - 1, by omega⟩ : Fin r))).toMonoidHom g ∈ orthElementaryGroup (quadPlus r K) :=
    fun g hg => conj_mem_orthElementaryGroup (swapIso K (⟨r - 1, by omega⟩ : Fin r)).2 hg
  refine le_antisymm (Subgroup.map_le_iff_le_comap.2 hc) fun g hg => ⟨_, hc g hg, ?_⟩
  change swapPair K _ * (swapPair K _ * g * (swapPair K _)⁻¹) * (swapPair K _)⁻¹ = g
  rw [swapPair_inv]
  simp only [← mul_assoc, swapPair_mul_self, one_mul]
  rw [mul_assoc, swapPair_mul_self, mul_one]

variable (K) in
@[expose] noncomputable def plusGraphConj (hr : 1 ≤ r) :
    ↥(orthElementaryGroup (quadPlus r K)) ≃* ↥(orthElementaryGroup (quadPlus r K)) :=
  ((MulAut.conj (swapPair K (⟨r - 1, by omega⟩ : Fin r))).subgroupMap _).trans
    (MulEquiv.subgroupCongr (map_conj_swapPair_orthElementaryGroup hr))

theorem coe_plusGraphConj (hr : 1 ≤ r) (g : ↥(orthElementaryGroup (quadPlus r K))) :
    ((plusGraphConj K hr g : ↥(orthElementaryGroup (quadPlus r K))) :
      (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) =
      swapPair K (⟨r - 1, by omega⟩ : Fin r) *
        (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) * swapPair K ⟨r - 1, by omega⟩ := by
  change swapPair K _ * _ * (swapPair K _)⁻¹ = _
  rw [swapPair_inv]

theorem exists_plusNodeStab_of_compParab [Finite K] [CharP K 2] (hr : 4 ≤ r) {Y : Type}
    [Group Y] [Finite Y] {L P : Subgroup Y} (hCP : CompParab L P)
    (φ : ↥L ≃* ↥(orthElementaryGroup (quadPlus r K))) :
    ∃ (ψ : ↥L ≃* ↥(orthElementaryGroup (quadPlus r K))) (I : Set (Fin r)), I.Nonempty ∧
      ((⟨r - 2, by omega⟩ : Fin r) ∈ I → (⟨r - 1, by omega⟩ : Fin r) ∈ I) ∧
      ((P.subgroupOf L).map ψ.toMonoidHom).map (orthElementaryGroup (quadPlus r K)).subtype =
        plusNodeStab K (by omega) I := by
  have hr3 : 3 ≤ r := by omega
  set E := orthElementaryGroup (quadPlus r K) with hE
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite ↥E := Finite.of_equiv _ φ.toEquiv
  obtain ⟨hPL, T, ⟨hTL, hT2, hTi⟩, hNP⟩ := hCP.parab
  set T₀ : Subgroup ↥L := T.subgroupOf L
  have hNT₀ : Subgroup.normalizer (T₀ : Set ↥L) ≤ P.subgroupOf L := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    refine hNP ⟨x.2, Subgroup.mem_normalizer_fintype fun s hs => ?_⟩
    have h1 : (⟨s, hTL hs⟩ : ↥L) ∈ T₀ := Subgroup.mem_subgroupOf.2 hs
    have h2 := (Subgroup.mem_normalizer_iff.1 hx ⟨s, hTL hs⟩).1 h1
    simpa [T₀, Subgroup.mem_subgroupOf] using h2
  have hT₁ : IsPGroup 2 (T₀.map φ.toMonoidHom) := (hT2.comap_subtype (K := L)).map _
  have hT₁i : ¬ 2 ∣ (T₀.map φ.toMonoidHom).index := by
    rw [show φ.toMonoidHom = (φ : ↥L →* ↥E) from rfl, Subgroup.index_map_equiv]
    exact hTi
  let S₁ : Sylow 2 ↥E := hT₁.toSylow hT₁i
  obtain ⟨⟨U, hU⟩, hN, -⟩ := orthogonal_geometry_split_Sylow_flag_normalizer (K := K) 2 hr3
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq ↥E U S₁
  let ψ₀ : ↥L ≃* ↥E := φ.trans (MulAut.conj x⁻¹)
  have hψT : T₀.map ψ₀.toMonoidHom = (posUnip r K).subgroupOf E := by
    have h1 : ((x • U : Sylow 2 ↥E) : Subgroup ↥E) = T₀.map φ.toMonoidHom := by rw [hx]; rfl
    rw [Sylow.coe_subgroup_smul, hU] at h1
    have h1' : T₀.map φ.toMonoidHom =
        ((posUnip r K).subgroupOf E).map (MulAut.conj x).toMonoidHom := by
      rw [← h1]
      rfl
    have h2 : T₀.map ψ₀.toMonoidHom =
        (T₀.map φ.toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    have : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom = MonoidHom.id _ := by
      refine MonoidHom.ext fun z => ?_
      change x⁻¹ * (x * z * x⁻¹) * x⁻¹⁻¹ = z
      group
    rw [h2, h1', Subgroup.map_map, this, Subgroup.map_id]
  set M₀ := ((P.subgroupOf L).map ψ₀.toMonoidHom).map E.subtype with hM₀
  have hB₀ : borel r K ≤ M₀ := by
    intro b hb
    have hbE : b ∈ E := borel_le hb
    have h1 : (⟨b, hbE⟩ : ↥E) ∈ (flagStab r K).subgroupOf E := by
      rw [Subgroup.mem_subgroupOf, native_partialBorel_eq_fullBorel r K hr3]
      exact hb
    rw [← hN, ← hψT, ← Subgroup.map_normalizer_eq_of_bijective _ ψ₀.bijective] at h1
    exact ⟨_, Subgroup.map_mono hNT₀ h1, rfl⟩
  have hM₀E : M₀ ≤ E := Subgroup.map_subtype_le _
  by_cases htw : weylElt r K ⟨r - 2, by omega⟩ ∉ M₀ ∧ weylElt r K ⟨r - 1, by omega⟩ ∈ M₀
  ·
    set ψ := ψ₀.trans (plusGraphConj K (by omega)) with hψ
    set M := ((P.subgroupOf L).map ψ.toMonoidHom).map E.subtype with hM
    have hmemM : ∀ g, g ∈ M ↔ swapPair K (⟨r - 1, by omega⟩ : Fin r) * g *
        swapPair K ⟨r - 1, by omega⟩ ∈ M₀ := by
      intro g
      constructor
      · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        refine ⟨_, ⟨z, hz, rfl⟩, ?_⟩
        change ((ψ₀ z : ↥E) : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) =
          swapPair K _ * ((plusGraphConj K (by omega) (ψ₀ z) : ↥E) :
            (Fin r ⊕ Fin r → K) ≃ₗ[K] _) * swapPair K _
        rw [coe_plusGraphConj]
        simp only [← mul_assoc, swapPair_mul_self, one_mul]
        rw [mul_assoc, swapPair_mul_self, mul_one]
      · rintro ⟨_, ⟨z, hz, rfl⟩, hzg⟩
        refine ⟨_, ⟨z, hz, rfl⟩, ?_⟩
        change ((plusGraphConj K (by omega) (ψ₀ z) : ↥E) : (Fin r ⊕ Fin r → K) ≃ₗ[K] _) = g
        change ((ψ₀ z : ↥E) : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) = _ at hzg
        rw [coe_plusGraphConj, hzg]
        simp only [← mul_assoc, swapPair_mul_self, one_mul]
        rw [mul_assoc, swapPair_mul_self, mul_one]
    have hBM : borel r K ≤ M := fun b hb => (hmemM b).2 (hB₀ (conj_swapPair_mem_borel hr3 hb))
    have hME : M ≤ E := Subgroup.map_subtype_le _
    have hM₀X : ∀ h ∈ M₀, h • Xstar r K (by omega) = Xstar r K (by omega) := by
      intro h hh
      rw [eq_plusNodeStab_of_borel_le hr3 hM₀E hB₀] at hh
      have := (mem_plusNodeStab.1 hh).2 ⟨r - 2, by omega⟩ htw.1
      simpa [plusNodeSpace, show ¬ r - 2 + 1 ≤ r - 2 by omega] using this
    have hnM : weylElt r K ⟨r - 1, by omega⟩ ∉ M := by
      intro hn
      have h := hM₀X _ ((hmemM _).1 hn)
      have hσ := swapPair_smul_flag_top (K := K) hr3
      rw [mul_smul, mul_smul, hσ.2, ← hσ.1] at h
      apply (weylElt_last_smul (K := K) hr3).1
      have h2 := congrArg (swapPair K (⟨r - 1, by omega⟩ : Fin r) • ·) h
      simpa only [smul_smul, ← mul_assoc, swapPair_mul_self, one_mul, one_smul] using h2
    refine ⟨ψ, {i | weylElt r K i ∉ M}, nonempty_of_map_eq_plusNodeStab hPL hCP.ne_top hr3 ψ
      (eq_plusNodeStab_of_borel_le hr3 hME hBM), fun _ => hnM,
      eq_plusNodeStab_of_borel_le hr3 hME hBM⟩
  · refine ⟨ψ₀, {i | weylElt r K i ∉ M₀}, nonempty_of_map_eq_plusNodeStab hPL hCP.ne_top hr3 ψ₀
      (eq_plusNodeStab_of_borel_le hr3 hM₀E hB₀), fun h2 => ?_,
      eq_plusNodeStab_of_borel_le hr3 hM₀E hB₀⟩
    by_contra h1
    exact htw ⟨h2, not_not.1 h1⟩

end CFSG.AGLEmbedding.LeviBlock

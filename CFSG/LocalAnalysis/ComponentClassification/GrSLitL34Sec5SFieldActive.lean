module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldCoreParts
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoAutCard
public import CFSG.GH74.KGroups.PSLN
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSol25

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

@[expose] def activeTwoComponents {G : Type} [Group G] (a : G) (Y : Subgroup G) :
    Set (Subgroup G) :=
  {J | J ≤ centralizer ({a} : Set G) ∧
    IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))) ∧ ¬ ⁅J, Y⁆ ≤ oddIn J}

@[expose] def L34ActiveImageBound : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t a : G), orderOf t = 2 → orderOf a = 2 → t * a = a * t →
    (∀ J : Subgroup G, GSUnbalancingTriple a t J →
      IsL2Type 5 (J ⧸ pPrimeCore 2 J) ∨ IsL2Type 7 (J ⧸ pPrimeCore 2 J) ∨
        IsL34Type (J ⧸ Open.fusionZStar J)) →
    ∀ Y : Subgroup G, Y ≤ oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({a} : Set G) →
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      padicValNat p ((oddIn (centralizer ({a} : Set G))).relIndex Y) ≤
        3 * (activeTwoComponents a Y).ncard

@[expose] def L34ActiveSupportCount : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t a : G), orderOf t = 2 → orderOf a = 2 → t * a = a * t →
    (∀ J : Subgroup G, GSUnbalancingTriple a t J →
      IsL2Type 5 (J ⧸ pPrimeCore 2 J) ∨ IsL2Type 7 (J ⧸ pPrimeCore 2 J) ∨
        IsL34Type (J ⧸ Open.fusionZStar J)) →
    ∀ Y : Subgroup G, Y ≤ oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({a} : Set G) →
      (activeTwoComponents a Y).ncard ≤
        pRank 2 ↥(centralizer ({t} : Set G) ⊓ centralizer ({a} : Set G))

theorem l34ActiveComponentBound_of_parts (h1 : L34ActiveImageBound)
    (h2 : L34ActiveSupportCount) : L34ActiveComponentBound :=
  fun G _ _ t a ht ha hta htypes Y hY p hp hp2 =>
    (h1 G t a ht ha hta htypes Y hY p hp hp2).trans
      (Nat.mul_le_mul_left 3 (h2 G t a ht ha hta htypes Y hY))

section AutOrders

variable {J : Type} [Group J]

theorem fusionZStar_eq_pPrimeCore_of_isSimpleGroup [Group.IsPerfect J]
    [IsSimpleGroup (J ⧸ pPrimeCore 2 J)] : Open.fusionZStar J = pPrimeCore 2 J := by
  have : Group.IsPerfect (J ⧸ pPrimeCore 2 J) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have hcen : center (J ⧸ pPrimeCore 2 J) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (J ⧸ pPrimeCore 2 J)) with h | h
    · exact h
    · exfalso
      have hc : ∀ x y : J ⧸ pPrimeCore 2 J, x * y = y * x := fun x y =>
        (mem_center_iff.mp (h ▸ mem_top y) x)
      have hcomm : commutator (J ⧸ pPrimeCore 2 J) = ⊥ := by
        rw [_root_.commutator_def, eq_bot_iff, commutator_le]
        intro x _ y _
        rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact hc x y
      rw [Group.IsPerfect.commutator_eq_top] at hcomm
      exact (top_ne_bot (α := Subgroup (J ⧸ pPrimeCore 2 J))) hcomm
  rw [GrS4.fusionZStar_eq_comap_pPrimeCore, hcen, MonoidHom.comap_bot, QuotientGroup.ker_mk']

theorem card_mulAut_fusionZStar_of_l2 [Group.IsPerfect J] {q : ℕ} [Fact q.Prime]
    (hL : IsL2Type q (J ⧸ pPrimeCore 2 J)) :
    Nat.card (MulAut (J ⧸ Open.fusionZStar J)) = q * (q ^ 2 - 1) := by
  have : IsSimpleGroup (J ⧸ pPrimeCore 2 J) :=
    CatLeafProof.X10Sp.isSimpleGroup_of_lieModel_psl (by norm_num) hL
  have hZ := fusionZStar_eq_pPrimeCore_of_isSimpleGroup (J := J)
  obtain ⟨e⟩ := GH74.KGroups.PSLN.psl_equiv_of_lieModel (F := GaloisField q 1) 2 q 1
    (by norm_num) (GaloisField.card q 1 (by norm_num)) hL
  let e' : J ⧸ Open.fusionZStar J ≃* AGLEmbedding.PSL2GF q 1 :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans e
  rw [Nat.card_congr (MulAut.congr e').toEquiv, AGLEmbedding.card_mulAut_psl2GF q 1 le_rfl]
  ring

theorem card_mulAut_fusionZStar_dvd [Group.IsPerfect J]
    (hJ : IsL2Type 5 (J ⧸ pPrimeCore 2 J) ∨ IsL2Type 7 (J ⧸ pPrimeCore 2 J) ∨
      IsL34Type (J ⧸ Open.fusionZStar J)) :
    Nat.card (MulAut (J ⧸ Open.fusionZStar J)) ∣ 2 ^ 8 * 945 := by
  rcases hJ with h5 | h7 | h34
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [card_mulAut_fusionZStar_of_l2 h5]
    norm_num
  · have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    rw [card_mulAut_fusionZStar_of_l2 h7]
    norm_num
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ :=
      LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel h34
    rw [Nat.card_congr (MulAut.congr e).toEquiv,
      RankThree.PartTwo.KFacts.L34.card_mulAut (by rw [hK]; norm_num)]
    norm_num

theorem padicValNat_le_three_of_dvd {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : n ∣ 2 ^ 8 * 945) :
    padicValNat p n ≤ 3 := by
  have : Fact p.Prime := ⟨hp⟩
  have hn0 : n ≠ 0 := fun h => by rw [h, zero_dvd_iff] at hn; norm_num at hn
  by_contra h
  push Not at h
  have h4 : p ^ 4 ∣ n := (padicValNat_dvd_iff_le hn0).mpr h
  have h4' : p ^ 4 ∣ 945 := by
    have h1 : p ^ 4 ∣ 2 ^ 8 * 945 := h4.trans hn
    have hcop : Nat.Coprime (p ^ 4) (2 ^ 8) := by
      refine Nat.Coprime.pow _ _ ?_
      exact (Nat.coprime_primes hp Nat.prime_two).mpr hp2
    exact hcop.dvd_of_dvd_mul_left h1
  have hle : p ^ 4 ≤ 945 := Nat.le_of_dvd (by norm_num) h4'
  have hp5 : p ≤ 5 := by
    by_contra hp6
    push Not at hp6
    have : 6 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left hp6 4
    omega
  interval_cases p
  · norm_num at hp
  · norm_num at hp
  · exact absurd rfl hp2
  · norm_num at h4'
  · norm_num at hp
  · norm_num at h4'

end AutOrders

theorem l34ActiveImageBound_holds : L34ActiveImageBound := by
  intro G _ _ t a ht ha hta htypes Y hY p hp hp2
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  set H := centralizer ({a} : Set G) with hH
  set A := activeTwoComponents a Y with hA
  have hAfin : A.Finite := Set.toFinite _
  set I := hAfin.toFinset with hI
  have hsol := GrS5.solomon_involutions solomonCommutingCoreInput ht ha hta
  have hYH : Y ≤ H := hY.trans inf_le_right
  have hYN : ∀ J ∈ A, Y ≤ normalizer (J : Set G) := fun J hJ =>
    hY.trans (hsol.2 J hJ.1 hJ.2.1).1
  have hmemI : ∀ J : ↥I, (J : Subgroup G) ∈ A := fun J => hAfin.mem_toFinset.mp J.2
  let Φ : ↥Y →* ∀ J : ↥I, MulAut (↥(J : Subgroup G) ⧸ Open.fusionZStar ↥(J : Subgroup G)) :=
    Pi.monoidHom fun J => (GSThmB.A10T.zStarAct (J : Subgroup G)).comp
      (Subgroup.inclusion (hYN J (hmemI J)))
  have hkerK : ∀ y : ↥Y, Φ y = 1 → ∀ J ∈ A, (y : G) ∈ coreActionKernel J := by
    intro y hy J hJ
    have h1 := congrFun hy ⟨J, hAfin.mem_toFinset.mpr hJ⟩
    exact (GSThmB.A10T.zStarAct_eq_one_iff hJ.1 hJ.2.1 _).mp h1
  set K₀ : Subgroup G := Φ.ker.map Y.subtype with hK₀
  have hK₀Y : K₀ ≤ Y := map_subtype_le _
  have hK₀H : K₀ ≤ H := hK₀Y.trans hYH
  have hYodd : Odd (Nat.card Y) := by
    have h1 : Nat.card Y ∣ Nat.card ↥(oddIn (centralizer ({t} : Set G))) :=
      Subgroup.card_dvd_of_le (hY.trans inf_le_left)
    refine Odd.of_dvd_nat ?_ h1
    rw [oddIn, card_map_of_injective (subtype_injective _)]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hK₀O : K₀ ≤ oddIn H := by
    set D : Subgroup ↥H := K₀.subgroupOf H with hD
    have hDodd : Odd (Nat.card D) := by
      rw [hD, Nat.card_congr (subgroupOfEquivOfLe hK₀H).toEquiv]
      exact hYodd.of_dvd_nat (Subgroup.card_dvd_of_le hK₀Y)
    have hDmem : ∀ d ∈ D, (d : G) ∈ K₀ := fun d hd => mem_subgroupOf.mp hd
    have hpull : ∀ x : ↥H, (x : G) ∈ oddIn H → x ∈ pPrimeCore 2 ↥H := fun x hx =>
      (mem_map_iff_mem H.subtype_injective).mp hx
    have hDle : D ≤ pPrimeCore 2 ↥H := by
      refine GrS5.le_pPrimeCore_of_commute hDodd ?_ ?_
      · intro m hm d hd
        apply hpull
        have h1 := hsol.1 (commutator_mem_commutator (mem_map_of_mem H.subtype hm)
          (Subgroup.mem_inf.mpr ⟨(hY (hK₀Y (hDmem d hd))).1, d.2⟩))
        simpa [commutatorElement_def] using h1
      · intro M hM m hm d hd
        apply hpull
        set M' : Subgroup G := M.map H.subtype with hM'
        have hM'H : M' ≤ H := map_subtype_le _
        have hM's : M'.subgroupOf H = M := comap_map_eq_self_of_injective H.subtype_injective _
        have hM'c : IsPComponent 2 (M'.subgroupOf H) := hM's ▸ hM
        have hmM' : (m : G) ∈ M' := mem_map_of_mem _ hm
        have hO : oddIn M' ≤ oddIn H := GSLit.map_pPrimeCore_le_of_isPComponent hM'H hM'c
        by_cases hact : M' ∈ A
        · obtain ⟨y, hy, hyd⟩ := hDmem d hd
          have hdK : (d : G) ∈ coreActionKernel M' := hyd ▸ hkerK y hy M' hact
          have h1 := GrS5.conj_mem_oddIn_of_mem_coreActionKernel hdK (m : G) hmM'
          have h2 := hO ((oddIn M').inv_mem h1)
          have e : ((m * d * m⁻¹ * d⁻¹ : ↥H) : G) =
              ((d : G) * m * (d : G)⁻¹ * (m : G)⁻¹)⁻¹ := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]
            group
          rw [e]
          exact h2
        · have hinact : ⁅M', Y⁆ ≤ oddIn M' := by
            by_contra hc
            exact hact ⟨hM'H, hM'c, hc⟩
          have h1 := hO (hinact (commutator_mem_commutator hmM' (hK₀Y (hDmem d hd))))
          simpa [commutatorElement_def] using h1
    intro x hx
    have hxD : (⟨x, hK₀H hx⟩ : ↥H) ∈ D := mem_subgroupOf.mpr hx
    exact ⟨_, hDle hxD, rfl⟩
  have hidx : (oddIn H).relIndex Y ∣ Nat.card ↥Φ.range := by
    have h1 : (oddIn H).relIndex Y ∣ K₀.relIndex Y := Subgroup.relIndex_dvd_of_le_left Y hK₀O
    have h2 : K₀.relIndex Y = Φ.ker.index := by
      rw [Subgroup.relIndex, Subgroup.subgroupOf, hK₀,
        comap_map_eq_self_of_injective Y.subtype_injective]
    rw [h2, Subgroup.index_ker] at h1
    exact h1
  have hdvdJ : ∀ J : ↥I, Nat.card (MulAut (↥(J : Subgroup G) ⧸
      Open.fusionZStar ↥(J : Subgroup G))) ∣ 2 ^ 8 * 945 := by
    intro J
    have hJ := hmemI J
    have : Group.IsPerfect ↥(J : Subgroup G) := by
      have h1 := ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hJ.2.1
      exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hJ.1).toMonoidHom)
        (subgroupOfEquivOfLe hJ.1).surjective
    have hT := GrS5.gsUnbalancingTriple_of_not_le solomonCommutingCoreInput ht ha hta hJ.1
      hJ.2.1 hY hJ.2.2
    exact card_mulAut_fusionZStar_dvd (htypes _ hT)
  have hprod : Nat.card ↥Φ.range ∣ (2 ^ 8 * 945) ^ I.card := by
    have h1 : Nat.card ↥Φ.range ∣ Nat.card (∀ J : ↥I, MulAut (↥(J : Subgroup G) ⧸
        Open.fusionZStar ↥(J : Subgroup G))) := Subgroup.card_subgroup_dvd_card _
    rw [Nat.card_pi] at h1
    refine h1.trans ?_
    calc ∏ J : ↥I, Nat.card (MulAut (↥(J : Subgroup G) ⧸ Open.fusionZStar ↥(J : Subgroup G)))
        ∣ ∏ _J : ↥I, (2 ^ 8 * 945) := Finset.prod_dvd_prod_of_dvd _ _ fun J _ => hdvdJ J
      _ = (2 ^ 8 * 945) ^ I.card := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  have hne : (2 ^ 8 * 945) ^ I.card ≠ 0 := pow_ne_zero _ (by norm_num)
  have hv1 : padicValNat p ((oddIn H).relIndex Y) ≤ padicValNat p ((2 ^ 8 * 945) ^ I.card) :=
    (padicValNat_dvd_iff_le hne).mp (pow_padicValNat_dvd.trans (hidx.trans hprod))
  rw [padicValNat.pow] at hv1
  have hv2 := padicValNat_le_three_of_dvd hp hp2 (dvd_refl (2 ^ 8 * 945))
  have hcard : A.ncard = I.card := Set.ncard_eq_toFinset_card A hAfin
  rw [hcard]
  nlinarith

end CFSG.ComponentClassification.GrSLit.L34Sec5S

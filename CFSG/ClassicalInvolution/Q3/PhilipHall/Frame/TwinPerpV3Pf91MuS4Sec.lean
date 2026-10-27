module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf11Twin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TightRefute
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf17Inst

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.Sec

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL

section Abstract

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem dComp_subset_pair (hΦ : HypOmegaGen Φ) {A B : Subgroup X} (hA : A ∈ Φ) (hB : B ∈ Φ)
    (hnb : ∀ M ∈ Φ, M ∈ omegaNbr Φ A → M = B) (hnb' : ∀ M ∈ Φ, M ∈ omegaNbr Φ B → M = A)
    {J : Subgroup X} (hJ : J ∈ dComp Φ A) : J = A ∨ J = B := by
  have key : ∀ J : Subgroup X, Relation.ReflTransGen
      (fun M N : Subgroup X => N ∈ Φ ∧ Disconnected.dAdj Φ M N) A J → J = A ∨ J = B := by
    intro J hJ'
    induction hJ' with
    | refl => exact Or.inl rfl
    | @tail b c _ hbc ih =>
      obtain ⟨hcΦ, hadj⟩ := hbc
      rcases ih with rfl | rfl
      · right
        rcases hadj with h | h
        · exact hnb c hcΦ h
        · exact hnb c hcΦ (Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΦ hcΦ hA h)
      · left
        rcases hadj with h | h
        · exact hnb' c hcΦ h
        · exact hnb' c hcΦ (Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΦ hcΦ hB h)
  exact key J hJ

end Abstract

section Sec


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem omegaStarNbr_cFam (hΩ : HypOmegaGen Ω) {K J : Subgroup G} (hJ2 : IsPGroup 2 J)
    (hKcore : K ∈ TwinADescent.coreFamily Ω c) (hJcore : J ∈ TwinADescent.coreFamily Ω c)
    (hKC : K ≤ Subgroup.centralizer ({c} : Set G)) (hJC : J ≤ Subgroup.centralizer ({c} : Set G))
    (h : J ∈ omegaStarNbr Ω K) :
    J.subgroupOf (Subgroup.centralizer ({c} : Set G)) ∈
      omegaStarNbr (cFam Ω c) (K.subgroupOf (Subgroup.centralizer ({c} : Set G))) := by
  obtain ⟨hJΩ, hne, U, hU, hUJ, hUN⟩ := h
  obtain ⟨R, hR, hUR, hcyc, hidx⟩ := id hU
  obtain ⟨J₁, hJ₁, hRJ₁⟩ := exists_isSylow2In_of_mem_RSet hR
  have hJ₁J : J₁ = J := Sec6Gen.eq_of_mem_USet hΩ hU hJ₁ hJΩ (hUR.trans hRJ₁.1) hUJ
  subst hJ₁J
  have hJR : J₁ = R := hRJ₁.2.2 J₁ le_rfl hJ2 hRJ₁.1
  subst hJR
  have hUC : U ≤ Subgroup.centralizer ({c} : Set G) := hUJ.trans hJC
  have hJself : IsSylow2In J₁ J₁ := ⟨le_rfl, hJ2, fun V' hV' _ hle => le_antisymm hV' hle⟩
  refine ⟨subgroupOf_mem_restrictFamily hJcore hJC, subgroupOf_ne_of_ne hKC hJC hne,
    U.subgroupOf (Subgroup.centralizer ({c} : Set G)),
    ⟨J₁.subgroupOf (Subgroup.centralizer ({c} : Set G)), mem_RSet_restrict hJcore hJC hJself,
      Subgroup.subgroupOf_mono _ hUR, ?_, ?_⟩,
    Subgroup.subgroupOf_mono _ hUJ, fun x hx => ?_⟩
  · exact (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hUC)).mpr hcyc
  · rw [← Subgroup.relIndex_map_map_of_injective _ _ (Subgroup.centralizer ({c} : Set G)).subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hUC, Subgroup.map_subgroupOf_eq_of_le hJC]
    exact hidx
  · exact (mem_normalizer_subgroupOf_iff hKC).mp (hUN (Subgroup.mem_subgroupOf.mp hx))

theorem coreAt_eq_of_isPGroup {J : Subgroup G} (hJ2 : IsPGroup 2 J)
    (hJC : J ≤ Subgroup.centralizer ({c} : Set G)) : TwinADescent.coreAt c J = J := by
  unfold TwinADescent.coreAt
  rw [inf_eq_left.mpr hJC]
  exact tightCore_eq_of_isPGroup hJ2

theorem omegaStarNbr_secImg (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {J J' : Subgroup G} (hJ : J ∈ tqMembers3 Ω c) (hJ' : J' ∈ tqMembers3 Ω c)
    (hJ2 : IsPGroup 2 J) (hJ'2 : IsPGroup 2 J')
    (hJC : J ≤ Subgroup.centralizer ({c} : Set G)) (hJ'C : J' ≤ Subgroup.centralizer ({c} : Set G))
    (h : J' ∈ omegaStarNbr Ω J) (hne : secImg Ω c J' ≠ secImg Ω c J) :
    secImg Ω c J' ∈ omegaStarNbr (TwinDisc.secFam Ω c) (secImg Ω c J) := by
  have hcJ : TwinADescent.coreAt c J = J := coreAt_eq_of_isPGroup hJ2 hJC
  have hcJ' : TwinADescent.coreAt c J' = J' := coreAt_eq_of_isPGroup hJ'2 hJ'C
  have hJcore : J ∈ TwinADescent.coreFamily Ω c := ⟨J, hJ, hcJ.symm⟩
  have hJ'core : J' ∈ TwinADescent.coreFamily Ω c := ⟨J', hJ', hcJ'.symm⟩
  have h1 := omegaStarNbr_cFam hΩ hJ'2 hJcore hJ'core hJC hJ'C h
  have hΛ1 : HypOmegaGen (cFam Ω c) := TwinADescent.hypOmegaGen_coreFamily hΩ hc2
  have hJX : J.subgroupOf (Subgroup.centralizer ({c} : Set G)) ≤ coreHull Ω c := by
    have := le_coreHull hJ
    rwa [hcJ] at this
  have hJ'X : J'.subgroupOf (Subgroup.centralizer ({c} : Set G)) ≤ coreHull Ω c := by
    have := le_coreHull hJ'
    rwa [hcJ'] at this
  have h2 := FrameAEmptyPf.omegaStarNbr_subgroupOf_gen hΛ1 hJX hJ'X h1
  have hne' : (((J'.subgroupOf (Subgroup.centralizer ({c} : Set G))).subgroupOf (coreHull Ω c)).map
      (T3.oddQuot ↥(coreHull Ω c))) ≠
      (((J.subgroupOf (Subgroup.centralizer ({c} : Set G))).subgroupOf (coreHull Ω c)).map
        (T3.oddQuot ↥(coreHull Ω c))) := by
    intro heq
    apply hne
    unfold secImg
    rw [hcJ, hcJ']
    exact heq
  have h3 := T3.omegaStarNbr_map_quot h2 hne'
  unfold secImg
  rw [hcJ, hcJ']
  exact h3

theorem secImg_ne_of_involution (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {J L : Subgroup G} (hJ : J ∈ tqMembers3 Ω c) (hL : L ∈ tqMembers3 Ω c) {zJ zL : G}
    (hzJ : IsUniqueInvolution J zJ) (hzL : IsUniqueInvolution L zL) (hne : zJ ≠ zL)
    (hcomm : zJ * zL = zL * zJ) : secImg Ω c J ≠ secImg Ω c L := by
  intro heq
  obtain ⟨htJ, hYJ, hUJ⟩ := isUniqueInvolution_secImg hΩ hc2 hJ hzJ
  obtain ⟨htL, hYL, hUL⟩ := isUniqueInvolution_secImg hΩ hc2 hL hzL
  rw [heq] at hUJ
  have h := hUJ.eq hUL
  rw [QuotientGroup.eq] at h
  set N := classicalInvolutionOddCore ↥(coreHull Ω c) with hN
  have hodd : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card ↥(coreHull Ω c)
  set a : ↥(coreHull Ω c) := ⟨⟨zJ, htJ⟩, hYJ⟩ with ha
  set b : ↥(coreHull Ω c) := ⟨⟨zL, htL⟩, hYL⟩ with hb
  have hzJ2 : zJ * zJ = 1 := hzJ.sq
  have hzL2 : zL * zL = 1 := hzL.sq
  have hn2 : (a⁻¹ * b) * (a⁻¹ * b) = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    show zJ⁻¹ * zL * (zJ⁻¹ * zL) = 1
    have hi : zJ⁻¹ = zJ := inv_eq_of_mul_eq_one_right hzJ2
    rw [hi]
    calc zJ * zL * (zJ * zL) = zJ * (zL * zJ) * zL := by group
      _ = zJ * (zJ * zL) * zL := by rw [hcomm]
      _ = (zJ * zJ) * (zL * zL) := by group
      _ = 1 := by rw [hzJ2, hzL2, one_mul]
  have hord : orderOf (⟨a⁻¹ * b, h⟩ : N) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    simpa [pow_two] using hn2
  have hdvd : orderOf (⟨a⁻¹ * b, h⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
  have h1 : orderOf (⟨a⁻¹ * b, h⟩ : N) = 1 := by
    have h2' : orderOf (⟨a⁻¹ * b, h⟩ : N) = 1 ∨ orderOf (⟨a⁻¹ * b, h⟩ : N) = 2 :=
      (Nat.dvd_prime Nat.prime_two).mp hord
    rcases h2' with h2' | h2'
    · exact h2'
    · rw [h2'] at hdvd
      exact absurd (even_iff_two_dvd.mpr hdvd) (Nat.not_even_iff_odd.mpr hodd)
  have h3 : (⟨a⁻¹ * b, h⟩ : N) = 1 := orderOf_eq_one_iff.mp h1
  have h4 : a⁻¹ * b = 1 := congrArg Subtype.val h3
  have h5 : a = b := inv_mul_eq_one.mp h4
  apply hne
  have := congrArg (fun x : ↥(coreHull Ω c) => ((x : ↥(Subgroup.centralizer ({c} : Set G))) : G)) h5
  exact this

end Sec

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.Sec

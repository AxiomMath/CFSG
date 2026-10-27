module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldActive
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldActiveSupport
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecDiag

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_involution_not_mem_zStarIn_of_isSimpleGroup {t : G} {J : Subgroup G}
    (ht : t * t = 1) (htN : t ∈ normalizer (J : Set G)) [Group.IsPerfect ↥J]
    [IsSimpleGroup (↥J ⧸ pPrimeCore 2 ↥J)] :
    ∃ x ∈ J ⊓ centralizer ({t} : Set G), x * x = 1 ∧ x ∉ zStarIn J := by
  have hZ : zStarIn J = oddIn J := by
    rw [zStarIn, oddIn, fusionZStar_eq_pPrimeCore_of_isSimpleGroup]
  have hev : Even (Nat.card J) := by
    rcases Nat.even_or_odd (Nat.card J) with h | h
    · exact h
    · exfalso
      have htop : pPrimeCore 2 ↥J = ⊤ := by
        refine eq_top_iff.mpr (le_sSup ⟨inferInstance, ?_⟩)
        rw [card_top]
        exact Nat.coprime_two_left.mpr h
      have : Subsingleton (↥J ⧸ pPrimeCore 2 ↥J) := by
        refine ⟨fun u v => ?_⟩
        induction u using QuotientGroup.induction_on
        induction v using QuotientGroup.induction_on
        rw [QuotientGroup.eq, htop]
        exact mem_top _
      exact not_nontrivial (↥J ⧸ pPrimeCore 2 ↥J) inferInstance
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : ∀ x ∈ J, t * x * t⁻¹ ∈ J := fun x hx => (mem_normalizer_iff.mp htN x).mp hx
  have hC := ClassicalInvolution.Balance.LocalBalance.even_card_inf_centralizer_of_even ht hK hev
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(J ⊓ centralizer ({t} : Set G))) 2
    (even_iff_two_dvd.mp hC)
  refine ⟨y, y.2, ?_, ?_⟩
  · have h := pow_orderOf_eq_one y
    rw [hy, pow_two] at h
    exact congrArg Subtype.val h
  · rw [hZ]
    intro hyO
    have hodd : Odd (Nat.card ↥(oddIn J)) := by
      rw [oddIn, card_map_of_injective (subtype_injective _)]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    have hdvd : orderOf (⟨y, hyO⟩ : ↥(oddIn J)) ∣ Nat.card ↥(oddIn J) := orderOf_dvd_natCard _
    rw [show orderOf (⟨y, hyO⟩ : ↥(oddIn J)) = 2 by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hy]] at hdvd
    exact absurd (even_iff_two_dvd.mpr hdvd) (Nat.not_even_iff_odd.mpr hodd)

theorem exists_involution_not_mem_zStarIn_of_l34
    {a t : G} {J : Subgroup G} (hT : GSUnbalancingTriple a t J)
    (hL : IsL34Type (J ⧸ Open.fusionZStar J)) :
    ∃ x ∈ J ⊓ centralizer ({t} : Set G), x * x = 1 ∧ x ∉ zStarIn J := by
  obtain ⟨hU, P, hP, htP⟩ := exists_unitary_invariant_sylow hT hL
  have hJ : ⁅J, J⁆ = J := by
    obtain ⟨-, -, -, hJa, hJc, -, -⟩ := hT
    exact UnbalancedCorr.commutator_eq_of_isPComponent hJa hJc
  obtain ⟨hinv, hcard8, -, -, -, -, ⟨D, hDle, hDinf, hDsup⟩, -⟩ :=
    L34Facts.l34UnitaryCentralizerFact G J P t hJ hL hU hP htP
  set C := P ⊓ zStarIn J ⊓ centralizer ({t} : Set G) with hCdef
  have hC4 : Nat.card C ≤ 4 := by
    refine card_le_four_of_le_inf_zStarIn hJ hL hP inf_le_left fun b hb => ?_
    obtain ⟨hbPZ, hbt⟩ := mem_inf.mp hb
    have h1 := hinv b hbPZ
    have h2 : t⁻¹ * b * t = b := by
      have := mem_centralizer_singleton_iff.mp hbt
      rw [mul_assoc, this, inv_mul_cancel_left]
    rw [h2] at h1
    have h3 : b * b⁻¹ = 1 := mul_inv_cancel b
    rwa [← h1] at h3
  have hDne : D ≠ ⊥ := by
    rintro rfl
    rw [sup_bot_eq] at hDsup
    rw [hDsup, hcard8] at hC4
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPp : IsPGroup 2 ↥P := by
    obtain ⟨Q, hQ⟩ := hP.2
    have h1 : IsPGroup 2 ↥(P.subgroupOf J) := hQ ▸ Q.isPGroup'
    exact h1.of_equiv (subgroupOfEquivOfLe hP.1)
  have hDp : IsPGroup 2 ↥D := hPp.to_le (hDle.trans inf_le_left)
  obtain ⟨k, hk⟩ := hDp.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hDne (card_eq_one.mp (by rw [hk, pow_zero]))
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥D) 2
    (by rw [hk]; exact dvd_pow_self 2 hk0)
  have hyP : (y : G) ∈ P ⊓ centralizer ({t} : Set G) := hDle y.2
  refine ⟨y, mem_inf.mpr ⟨hP.1 (mem_inf.mp hyP).1, (mem_inf.mp hyP).2⟩, ?_, ?_⟩
  · have h := pow_orderOf_eq_one y
    rw [hy, pow_two] at h
    exact congrArg Subtype.val h
  · intro hyZ
    have hyC : (y : G) ∈ C ⊓ D :=
      mem_inf.mpr ⟨mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp hyP).1, hyZ⟩, (mem_inf.mp hyP).2⟩, y.2⟩
    rw [hDinf, mem_bot] at hyC
    have h1 : y = 1 := Subtype.ext hyC
    rw [h1, orderOf_one] at hy
    exact absurd hy (by norm_num)

theorem exists_involution_not_mem_zStarIn_of_l2 {a t : G} {J : Subgroup G}
    (hT : GSUnbalancingTriple a t J) {q : ℕ} (hL : IsL2Type q (J ⧸ pPrimeCore 2 J)) :
    ∃ x ∈ J ⊓ centralizer ({t} : Set G), x * x = 1 ∧ x ∉ zStarIn J := by
  obtain ⟨-, hto, -, hJa, hJc, htJ, -⟩ := hT
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  have hset : {y | ∃ j ∈ J, ∃ d ∈ ({t} : Set G), y = j⁻¹ * d⁻¹ * j * d} =
      {y | ∃ j ∈ J, y = j⁻¹ * t⁻¹ * j * t} := by
    ext y
    simp
  have htJ' : closure {y | ∃ j ∈ J, ∃ d ∈ ({t} : Set G), y = j⁻¹ * d⁻¹ * j * d} = J := by
    rw [hset]
    exact htJ
  have htN : t ∈ normalizer (J : Set G) :=
    L34Facts.mem_normalizer_of_closure htJ' (Set.mem_singleton t)
  have : Group.IsPerfect ↥J := by
    have h1 := ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hJc
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hJa).toMonoidHom)
      (subgroupOfEquivOfLe hJa).surjective
  have : IsSimpleGroup (↥J ⧸ pPrimeCore 2 ↥J) :=
    CatLeafProof.X10Sp.isSimpleGroup_of_lieModel_psl (by norm_num) hL
  exact exists_involution_not_mem_zStarIn_of_isSimpleGroup ht2 htN

theorem exists_involution_not_mem_zStarIn
    {a t : G} {J : Subgroup G} (hT : GSUnbalancingTriple a t J)
    (hty : IsL2Type 5 (J ⧸ pPrimeCore 2 J) ∨ IsL2Type 7 (J ⧸ pPrimeCore 2 J) ∨
      IsL34Type (J ⧸ Open.fusionZStar J)) :
    ∃ x ∈ J ⊓ centralizer ({t} : Set G), x * x = 1 ∧ x ∉ zStarIn J := by
  rcases hty with h5 | h7 | h34
  · exact exists_involution_not_mem_zStarIn_of_l2 hT h5
  · exact exists_involution_not_mem_zStarIn_of_l2 hT h7
  · exact exists_involution_not_mem_zStarIn_of_l34 hT h34

theorem map_closure_le_centralizer {H J₀ : Subgroup G} {S : Finset (Subgroup G)}
    {x : Subgroup G → G} (hS : ∀ J ∈ S, J ≤ H ∧ IsPComponent 2 (J.subgroupOf H))
    (hxS : ∀ J ∈ S, x J ∈ J) (hJ₀ : J₀ ≤ H ∧ IsPComponent 2 (J₀.subgroupOf H)) (hJ₀S : J₀ ∉ S)
    {y : G} (hy : y ∈ J₀) :
    ((closure (x '' (S : Set (Subgroup G)))).subgroupOf H).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥H)) ≤
      centralizer {QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨y, hJ₀.1 hy⟩} := by
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥H) with hπ
  have hle : closure (x '' (S : Set (Subgroup G))) ≤
      ((centralizer {π ⟨y, hJ₀.1 hy⟩}).comap π).map H.subtype := by
    rw [closure_le]
    rintro _ ⟨J, hJ, rfl⟩
    have hJS := hS J hJ
    refine ⟨⟨x J, hJS.1 (hxS J hJ)⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_comap, mem_centralizer_singleton_iff]
    have hne : J.subgroupOf H ≠ J₀.subgroupOf H := by
      intro h
      rw [subgroupOf_inj, inf_of_le_left hJS.1, inf_of_le_left hJ₀.1] at h
      exact hJ₀S (h ▸ hJ)
    exact Sp4Rec.commute_map_of_ne hJS.2 hJ₀.2 hne (mem_subgroupOf.mpr (hxS J hJ))
      (mem_subgroupOf.mpr hy)
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨g', hg'c, hgg'⟩ := hle (mem_subgroupOf.mp hg)
  rw [show g' = g from Subtype.ext hgg'] at hg'c
  exact hg'c

theorem isElemTwo_map_closure {H : Subgroup G} (S : Finset (Subgroup G)) (x : Subgroup G → G)
    (hS : ∀ J ∈ S, J ≤ H ∧ IsPComponent 2 (J.subgroupOf H))
    (hx : ∀ J ∈ S, x J ∈ J ∧ x J * x J = 1 ∧ x J ∉ zStarIn J) :
    IsElemTwo (((closure (x '' (S : Set (Subgroup G)))).subgroupOf H).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥H))) ∧
      Nat.card ↥(((closure (x '' (S : Set (Subgroup G)))).subgroupOf H).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥H))) = 2 ^ S.card := by
  classical
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥H) with hπ
  induction S using Finset.induction_on with
  | empty =>
    have h0 : ((closure (x '' ((∅ : Finset (Subgroup G)) : Set (Subgroup G)))).subgroupOf
        H).map π = ⊥ := by
      rw [Finset.coe_empty, Set.image_empty, Subgroup.closure_empty, bot_subgroupOf,
        Subgroup.map_bot]
    rw [h0, Finset.card_empty, pow_zero, card_bot]
    refine ⟨⟨fun a ha b hb => ?_, fun a ha => ?_⟩, rfl⟩
    · rw [mem_bot.mp ha, mem_bot.mp hb]
    · rw [mem_bot.mp ha, one_mul]
  | insert J₀ S hJ₀S ih =>
    have hS' : ∀ J ∈ S, J ≤ H ∧ IsPComponent 2 (J.subgroupOf H) := fun J hJ =>
      hS J (Finset.mem_insert_of_mem hJ)
    have hx' : ∀ J ∈ S, x J ∈ J ∧ x J * x J = 1 ∧ x J ∉ zStarIn J := fun J hJ =>
      hx J (Finset.mem_insert_of_mem hJ)
    obtain ⟨ih1, ih2⟩ := ih hS' hx'
    have hJ₀ := hS J₀ (Finset.mem_insert_self _ _)
    obtain ⟨hx₀J, hx₀2, hx₀Z⟩ := hx J₀ (Finset.mem_insert_self _ _)
    set x₀ : ↥H := ⟨x J₀, hJ₀.1 hx₀J⟩ with hx₀
    set E := ((closure (x '' (S : Set (Subgroup G)))).subgroupOf H).map π with hE
    have hcl : closure (x '' (S : Set (Subgroup G))) ≤ H := by
      rw [closure_le]
      rintro _ ⟨J, hJ, rfl⟩
      exact (hS' J hJ).1 (hx' J hJ).1
    have heq : ((closure (x '' ((insert J₀ S : Finset (Subgroup G)) : Set (Subgroup G)))).subgroupOf
        H).map π = zpowers (π x₀) ⊔ E := by
      rw [Finset.coe_insert, Set.image_insert_eq, ← Set.singleton_union, Subgroup.closure_union,
        ← zpowers_eq_closure, subgroupOf_sup (zpowers_le.mpr (hJ₀.1 hx₀J)) hcl, Subgroup.map_sup]
      congr 1
      have h1 : zpowers (x J₀) = (zpowers x₀).map H.subtype := by
        rw [MonoidHom.map_zpowers]
        rfl
      rw [h1, Subgroup.subgroupOf, comap_map_eq_self_of_injective H.subtype_injective,
        MonoidHom.map_zpowers]
    rw [heq, Finset.card_insert_of_notMem hJ₀S]
    have hcomm : ∀ y ∈ E, π x₀ * y = y * π x₀ := fun y hy =>
      (mem_centralizer_singleton_iff.mp
        (map_closure_le_centralizer hS' (fun J hJ => (hx' J hJ).1) hJ₀ hJ₀S hx₀J hy)).symm
    have hnot : π x₀ ∉ E := by
      intro hmem
      apply hx₀Z
      apply GrS5.inf_coreActionKernel_le_zStarIn
      refine mem_inf.mpr ⟨hx₀J, mem_coreActionKernel.mpr ⟨le_normalizer hx₀J, fun j hj => ?_⟩⟩
      have hc := mem_centralizer_singleton_iff.mp
        (map_closure_le_centralizer hS' (fun J hJ => (hx' J hJ).1) hJ₀ hJ₀S hj hmem)
      rw [← hπ] at hc
      set j' : ↥H := ⟨j, hJ₀.1 hj⟩ with hj'
      have hO : j'⁻¹ * x₀⁻¹ * j' * x₀ ∈ pPrimeCore 2 ↥H := by
        rw [← QuotientGroup.eq_one_iff (N := pPrimeCore 2 ↥H)]
        have : (π (j'⁻¹ * x₀⁻¹ * j' * x₀) : ↥H ⧸ pPrimeCore 2 ↥H) = 1 := by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_assoc ((π j')⁻¹ * (π x₀)⁻¹),
            ← hc]
          group
        exact this
      have hmemJ : j⁻¹ * (x J₀)⁻¹ * j * x J₀ ∈ J₀ :=
        mul_mem (mul_mem (mul_mem (inv_mem hj) (inv_mem hx₀J)) hj) hx₀J
      exact GrS5.inf_oddIn_le_oddIn hJ₀.1 (mem_inf.mpr ⟨⟨_, hO, rfl⟩, hmemJ⟩)
    have hx2 : π x₀ * π x₀ = 1 := by
      rw [← map_mul, show x₀ * x₀ = 1 from Subtype.ext hx₀2, map_one]
    obtain ⟨h1, h2⟩ := GrS5.elemTwo_zpowers_sup hx2 ih1 hcomm hnot
    exact ⟨h1, by rw [h2, ih2, pow_succ]; ring⟩

theorem l34ActiveSupportCount_holds :
    L34ActiveSupportCount := by
  intro G _ _ t a ht ha hta htypes Y hY
  classical
  set H := centralizer ({a} : Set G) with hH
  set A := activeTwoComponents a Y with hA
  have hAfin : A.Finite := Set.toFinite _
  set S := hAfin.toFinset with hSdef
  have hmemS : ∀ J, J ∈ S ↔ J ∈ A := fun J => hAfin.mem_toFinset
  have hchoose : ∀ J : Subgroup G, ∃ y : G, J ∈ A →
      y ∈ J ⊓ centralizer ({t} : Set G) ∧ y * y = 1 ∧ y ∉ zStarIn J := by
    intro J
    by_cases hJ : J ∈ A
    · have hT := GrS5.gsUnbalancingTriple_of_not_le solomonCommutingCoreInput ht ha hta hJ.1
        hJ.2.1 hY hJ.2.2
      obtain ⟨y, hy, hy2, hyZ⟩ := exists_involution_not_mem_zStarIn hT (htypes _ hT)
      exact ⟨y, fun _ => ⟨hy, hy2, hyZ⟩⟩
    · exact ⟨1, fun h => absurd h hJ⟩
  choose x hx using hchoose
  have hS : ∀ J ∈ S, J ≤ H ∧ IsPComponent 2 (J.subgroupOf H) := fun J hJ =>
    ⟨((hmemS J).mp hJ).1, ((hmemS J).mp hJ).2.1⟩
  have hxS : ∀ J ∈ S, x J ∈ J ∧ x J * x J = 1 ∧ x J ∉ zStarIn J := fun J hJ => by
    obtain ⟨h1, h2, h3⟩ := hx J ((hmemS J).mp hJ)
    exact ⟨(mem_inf.mp h1).1, h2, h3⟩
  obtain ⟨hE, hEcard⟩ := isElemTwo_map_closure S x hS hxS
  set X := closure (x '' (S : Set (Subgroup G))) with hXdef
  have hXle : X ≤ centralizer ({t} : Set G) ⊓ H := by
    rw [closure_le]
    rintro _ ⟨J, hJ, rfl⟩
    exact mem_inf.mpr ⟨(mem_inf.mp (hx J ((hmemS J).mp hJ)).1).2, (hS J hJ).1 (hxS J hJ).1⟩
  have hXH : X ≤ H := hXle.trans inf_le_right
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥H) with hπ
  set f : ↥X →* ↥H ⧸ pPrimeCore 2 ↥H := π.comp (inclusion hXH) with hf
  have hrange : f.range = (X.subgroupOf H).map π := by
    rw [hf, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hker : Odd (Nat.card f.ker) := by
    have h1 : f.ker = (pPrimeCore 2 ↥H).comap (inclusion hXH) := by
      rw [hf, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    have h2 : Nat.card f.ker ∣ Nat.card ↥(pPrimeCore 2 ↥H) := by
      rw [h1]
      exact card_comap_dvd_of_injective _ _ (inclusion_injective hXH)
    exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat h2
  obtain ⟨E', hE'c, hE'2, hE'card⟩ := GH74.GLS.Stage1.Thm4.L96.exists_elemAbelian_of_odd_kernel f
    hker _ (le_of_eq hrange.symm) hE.1 (fun u hu => by rw [pow_two]; exact hE.2 u hu)
  set E'' : Subgroup G := E'.map X.subtype with hE''
  have hE''le : E'' ≤ centralizer ({t} : Set G) ⊓ H := (map_subtype_le _).trans hXle
  have hE''elem : IsElemTwo E'' := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
      exact congrArg Subtype.val (hE'c u hu v hv)
    · rintro _ ⟨u, hu, rfl⟩
      have := hE'2 u hu
      rw [pow_two] at this
      exact congrArg Subtype.val this
  have hE''card : Nat.card E'' = Nat.card E' := card_map_of_injective (subtype_injective _)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE''p : IsPGroup 2 ↥E'' := fun u => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, pow_two, Subgroup.coe_one]; exact hE''elem.2 u u.2)⟩
  obtain ⟨k, hk⟩ := hE''p.exists_card_eq
  have hrank := GrS4.le_pRank_of_isElemTwo hE''le hE''elem hk
  have hle : 2 ^ S.card ≤ 2 ^ k := by
    rw [← hk, hE''card, ← hEcard]
    exact hE'card
  have hSk : S.card ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
  rw [Set.ncard_eq_toFinset_card A hAfin]
  exact hSk.trans hrank

end CFSG.ComponentClassification.GrSLit.L34Sec5S

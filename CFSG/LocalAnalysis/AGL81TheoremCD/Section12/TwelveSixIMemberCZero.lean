module

public import CFSG.LocalAnalysis.AGLEmbedding.CZeroDefs
public import CFSG.Quasithin.Background.A3ComponentsBasic
import CFSG.LocalAnalysis.AGLEmbedding.CZeroLift
import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic
import CFSG.Quasithin.Background.GoldschmidtS146RAux
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81JOneSolvPrimes
import CFSG.HardMathSupport.Solomon.Proving.SU32Carrier

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12.CZeroUnique

open CFSG.Open CFSG.AGLEmbedding Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem not_isPGroup_of_isTwoPrimeComponent {I : Subgroup G}
    (h : IsTwoPrimeComponent I I) : ¬ IsPGroup 2 I := by
  intro hp
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htop : CFSG.pCore 2 ↥I = ⊤ := by
    refine le_antisymm le_top (le_sSup ⟨inferInstance, hp.of_equiv Subgroup.topEquiv.symm⟩)
  haveI : Subsingleton (↥I ⧸ CFSG.pCore 2 ↥I) := by
    rw [htop]
    exact QuotientGroup.subsingleton_quotient_top
  have hb : barM I I = ⊥ := Subsingleton.elim _ _
  have hq := h.component.2.2
  rw [hb] at hq
  haveI : Subsingleton ↥(⊥ : Subgroup (↥I ⧸ CFSG.pCore 2 ↥I)) := inferInstance
  haveI : Subsingleton (↥(⊥ : Subgroup (↥I ⧸ CFSG.pCore 2 ↥I)) ⧸
      Subgroup.center ↥(⊥ : Subgroup (↥I ⧸ CFSG.pCore 2 ↥I))) :=
    Function.Surjective.subsingleton (QuotientGroup.mk'_surjective _)
  haveI := hq.2
  exact not_subsingleton (↥(⊥ : Subgroup (↥I ⧸ CFSG.pCore 2 ↥I)) ⧸
    Subgroup.center ↥(⊥ : Subgroup (↥I ⧸ CFSG.pCore 2 ↥I))) inferInstance

theorem two_dvd_card_of_isSymThreeOrSUThreeTwo {K : Type} [Group K]
    (h : IsSymThreeOrSUThreeTwo K) : 2 ∣ Nat.card K := by
  rcases h with ⟨f⟩ | ⟨K', _, _, hK, ⟨f⟩⟩
  · rw [Nat.card_congr f.some.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI := CFSG.HardMathSupport.Solomon.Proving.charP_two_of_card_four K' hK
    have h2 := CFSG.SectionRank.OddCover.card_statedSU_three (K := K') (p := 2) (f := 1)
      (by rw [hK]; norm_num)
    rw [Nat.card_congr f.toEquiv, pow_one] at *
    rw [h2]
    norm_num

theorem map_subgroupOf_perfectCore {X : Subgroup G} {D : Type} [Group D] [Finite D]
    (ψ : ↥X →* D) (hψ : Function.Surjective ψ) :
    ((CFSG.Quasithin.perfectCore X).subgroupOf X).map ψ =
      CFSG.Quasithin.perfectCore (⊤ : Subgroup D) := by
  have h₁ : (CFSG.Quasithin.perfectCore (⊤ : Subgroup ↥X)).map X.subtype =
      CFSG.Quasithin.perfectCore X := by
    rw [CFSG.Quasithin.map_perfectCore, Subgroup.map_top, Subgroup.range_subtype]
  have hsub : (CFSG.Quasithin.perfectCore X).subgroupOf X =
      CFSG.Quasithin.perfectCore (⊤ : Subgroup ↥X) := by
    rw [← h₁, CZeroLift.subgroupOf_map_subtype']
  rw [hsub, CFSG.Quasithin.map_perfectCore, Subgroup.map_top_of_surjective ψ hψ]

namespace Aux

variable {X : Subgroup G} {D : Type} [Group D] [Finite D] {ψ : ↥X →* D}

omit [Finite D] in
private theorem isPGroup_of_map_eq_bot (hψ : Function.Surjective ψ)
    (hker : IsPGroup 2 ψ.ker) (hD : CFSG.pCore 2 D = ⊥) {I : Subgroup G} (hIX : I ≤ X)
    (hbot : (I.subgroupOf X).map ψ = ⊥) : IsPGroup 2 I := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpX : CFSG.pCore 2 ↥X = ψ.ker := CZeroLift.pCore_eq_ker ψ hψ hker hD
  have hIker : I ≤ pCoreOf 2 X := by
    intro i hi
    have hxI : (⟨i, hIX hi⟩ : ↥X) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      have hmem : ψ ⟨i, hIX hi⟩ ∈ (I.subgroupOf X).map ψ :=
        Subgroup.mem_map_of_mem ψ (Subgroup.mem_subgroupOf.mpr hi)
      rw [hbot] at hmem
      simpa using hmem
    rw [← hpX] at hxI
    exact Subgroup.mem_map.mpr ⟨⟨i, hIX hi⟩, hxI, rfl⟩
  exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).of_injective
    (Subgroup.inclusion hIker) (Subgroup.inclusion_injective hIker)

omit [Finite G] [Finite D] in
private theorem isSubnormal_map (hψ : Function.Surjective ψ) {I : Subgroup G} (hIX : I ≤ X)
    (hIs : IsSubnormal I X) : IsSubnormal ((I.subgroupOf X).map ψ) ⊤ := by
  have h1 := (CFSG.Open.IsSubnormal.of_mathlib
    ((CFSG.Open.IsSubnormal.iff_subgroupOf hIX).1 hIs)).map ψ
  rwa [Subgroup.map_top_of_surjective ψ hψ] at h1

end Aux

private theorem normal_perfectCore_top {D : Type} [Group D] [Finite D] :
    (CFSG.Quasithin.perfectCore (⊤ : Subgroup D)).Normal := by
  have hsurj : Function.Surjective ⇑(⊤ : Subgroup D).subtype :=
    fun d => ⟨⟨d, Subgroup.mem_top d⟩, rfl⟩
  have h := Subgroup.Normal.map (CFSG.Quasithin.perfectCore_normal (⊤ : Subgroup D))
    (⊤ : Subgroup D).subtype hsurj
  rwa [Subgroup.map_subgroupOf_eq_of_le (le_top :
    CFSG.Quasithin.perfectCore (⊤ : Subgroup D) ≤ ⊤)] at h

private theorem perfectCore_le_sup_of_map_eq_perfectCore {X : Subgroup G}
    {D : Type} [Group D] [Finite D] {ψ : ↥X →* D}
    (hψ : Function.Surjective ψ) (hker : IsPGroup 2 ψ.ker) (hD : CFSG.pCore 2 D = ⊥)
    {I : Subgroup G} (hIpc : I ≤ CFSG.Quasithin.perfectCore X)
    (hKC : (I.subgroupOf X).map ψ = CFSG.Quasithin.perfectCore (⊤ : Subgroup D)) :
    CFSG.Quasithin.perfectCore X ≤
      I ⊔ (pCoreOf 2 X ⊓ CFSG.Quasithin.perfectCore X) := by
  intro x hx
  have hxX : x ∈ X := CFSG.Quasithin.perfectCore_le X hx
  have hψxK : ψ ⟨x, hxX⟩ ∈ (I.subgroupOf X).map ψ := by
    have h1 : ψ ⟨x, hxX⟩ ∈
        ((CFSG.Quasithin.perfectCore X).subgroupOf X).map ψ :=
      Subgroup.mem_map_of_mem ψ (Subgroup.mem_subgroupOf.mpr hx)
    rw [map_subgroupOf_perfectCore ψ hψ] at h1
    rwa [← hKC] at h1
  obtain ⟨i, hiI, hψi⟩ := Subgroup.mem_map.mp hψxK
  have hiI' : (i : G) ∈ I := Subgroup.mem_subgroupOf.mp hiI
  have hkerx : (⟨x, hxX⟩ * i⁻¹ : ↥X) ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hψi, mul_inv_cancel]
  have hpcx : x * (i : G)⁻¹ ∈ pCoreOf 2 X := by
    have hmem : (⟨x, hxX⟩ * i⁻¹ : ↥X) ∈ CFSG.pCore 2 ↥X := by
      rwa [CZeroLift.pCore_eq_ker ψ hψ hker hD]
    exact Subgroup.mem_map.mpr ⟨⟨x, hxX⟩ * i⁻¹, hmem, rfl⟩
  have hpc : x * (i : G)⁻¹ ∈
      pCoreOf 2 X ⊓ CFSG.Quasithin.perfectCore X :=
    ⟨hpcx, (CFSG.Quasithin.perfectCore X).mul_mem hx
      ((CFSG.Quasithin.perfectCore X).inv_mem (hIpc hiI'))⟩
  have hxeq : x = (x * (i : G)⁻¹) * (i : G) := by group
  rw [hxeq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hpc) (Subgroup.mem_sup_left hiI')

private theorem isComponent_perfectCore_top {D : Type} [Group D] [Finite D]
    (hC : IsSimpleGroup ↥(CFSG.Quasithin.perfectCore (⊤ : Subgroup D))) :
    IsComponentOf (CFSG.Quasithin.perfectCore (⊤ : Subgroup D)) ⊤ := by
  haveI : IsSimpleGroup ↥(CFSG.Quasithin.perfectCore (⊤ : Subgroup D)) := hC
  have hCsub : IsSubnormal (CFSG.Quasithin.perfectCore (⊤ : Subgroup D)) ⊤ :=
    CFSG.Open.IsSubnormal.of_mathlib normal_perfectCore_top.isSubnormal
  have hcomm : commutator ↥(CFSG.Quasithin.perfectCore (⊤ : Subgroup D)) = ⊤ :=
    (Subgroup.isPerfect_iff.2
      (CFSG.Quasithin.perfectCore_perfect (⊤ : Subgroup D))).commutator_eq_top
  haveI : Group.IsPerfect ↥(CFSG.Quasithin.perfectCore (⊤ : Subgroup D)) :=
    Subgroup.isPerfect_iff.2 (CFSG.Quasithin.perfectCore_perfect (⊤ : Subgroup D))
  have hnc : ¬ IsMulCommutative ↥(CFSG.Quasithin.perfectCore (⊤ : Subgroup D)) :=
    Group.IsPerfect.not_isMulCommutative _
  have hZ : Subgroup.center ↥(CFSG.Quasithin.perfectCore (⊤ : Subgroup D)) = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnc
  refine ⟨le_top, hCsub, hcomm, ?_⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot).isSimpleGroup

theorem eq_perfectCore_of_isTwoPrimeComponent {X : Subgroup G} {D : Type} [Group D] [Finite D]
    {ψ : ↥X →* D} (hψ : Function.Surjective ψ) (hker : IsPGroup 2 ψ.ker)
    (hD : CFSG.pCore 2 D = ⊥)
    (hC : IsSimpleGroup ↥(CFSG.Quasithin.perfectCore (⊤ : Subgroup D)))
    {I : Subgroup G} (hI : IsCZeroMember X I) (hc : IsTwoPrimeComponent I I) :
    I = CFSG.Quasithin.perfectCore X := by
  have hIX : I ≤ X := hI.le
  have hIpc : I ≤ CFSG.Quasithin.perfectCore X :=
    CFSG.Quasithin.le_perfectCore_of_perfect hIX hc.perfect
  let K : Subgroup D := (I.subgroupOf X).map ψ
  let C : Subgroup D := CFSG.Quasithin.perfectCore (⊤ : Subgroup D)
  have hKle : K ≤ C := by
    rw [show K = (I.subgroupOf X).map ψ from rfl,
      show C = CFSG.Quasithin.perfectCore ⊤ from rfl, ← map_subgroupOf_perfectCore ψ hψ]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono X hIpc)
  have hKsub : IsSubnormal K ⊤ := Aux.isSubnormal_map hψ hIX hI.subnormal
  have hKsubC : IsSubnormal K C := by
    have := hKsub.inf_of_le (le_top : C ≤ ⊤)
    rwa [inf_eq_left.mpr hKle] at this
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hKsubC hC with hbot | htop
  · exact absurd (Aux.isPGroup_of_map_eq_bot hψ hker hD hIX hbot)
      (not_isPGroup_of_isTwoPrimeComponent hc)
  · have hLAN : CFSG.Quasithin.perfectCore X ≤
        I ⊔ (pCoreOf 2 X ⊓ CFSG.Quasithin.perfectCore X) :=
      perfectCore_le_sup_of_map_eq_perfectCore hψ hker hD hIpc
        (show (I.subgroupOf X).map ψ = CFSG.Quasithin.perfectCore (⊤ : Subgroup D) from htop)
    have hN2 : IsPGroup 2 ↥(pCoreOf 2 X ⊓ CFSG.Quasithin.perfectCore X) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).of_injective
        (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective inf_le_left)
    have hA : IsSubnormal I (CFSG.Quasithin.perfectCore X) := by
      have := hI.subnormal.inf_of_le (CFSG.Quasithin.perfectCore_le X)
      rwa [inf_eq_left.mpr hIpc] at this
    exact CFSG.Quasithin.GoldS146R.eq_of_subnormal_of_le_sup inf_le_right
      (CFSG.Quasithin.perfectCore_perfect X) hN2 hA hLAN

theorem false_of_symThree_member {X : Subgroup G} {D : Type} [Group D] [Finite D]
    {ψ : ↥X →* D} (hψ : Function.Surjective ψ) (hker : IsPGroup 2 ψ.ker)
    (hD : CFSG.pCore 2 D = ⊥)
    (hC : IsSimpleGroup ↥(CFSG.Quasithin.perfectCore (⊤ : Subgroup D)))
    (hodd : ¬ 2 ∣ (CFSG.Quasithin.perfectCore (⊤ : Subgroup D)).index)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (hrC : r ∣ Nat.card ↥(CFSG.Quasithin.perfectCore (⊤ : Subgroup D)))
    {I : Subgroup G} (hIX : I ≤ X) (hIs : IsSubnormal I X)
    (hb : IsSymThreeOrSUThreeTwo (↥I ⧸ CFSG.pCore 2 ↥I)) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K : Subgroup D := (I.subgroupOf X).map ψ
  let C : Subgroup D := CFSG.Quasithin.perfectCore (⊤ : Subgroup D)
  have hKsub : IsSubnormal K ⊤ := Aux.isSubnormal_map hψ hIX hIs
  have hKO : CFSG.pCore 2 ↥K = ⊥ := CZeroLift.pCore_eq_bot_of_isSubnormal hKsub hD
  obtain ⟨-, ⟨e⟩⟩ := CZeroLift.pCore_eq_and_equiv ψ hIX hker hKO
  have hbK : IsSymThreeOrSUThreeTwo ↥K := IsSymThreeOrSUThreeTwo.of_mulEquiv e hb
  have h2K : 2 ∣ Nat.card ↥K := two_dvd_card_of_isSymThreeOrSUThreeTwo hbK
  have hKsubC : IsSubnormal (K ⊓ C) C := by
    have := hKsub.inf_of_le (le_top : C ≤ ⊤)
    simpa only [inf_comm] using this
  rcases IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hKsubC hC with hbot | htop
  · have hCK : C ⊓ K = ⊥ := by rwa [inf_comm] at hbot
    have hrel : C.relIndex K = Nat.card ↥K := by
      rw [Subgroup.relIndex, Subgroup.subgroupOf_eq_bot.2 (disjoint_iff.mpr hCK),
        Subgroup.index_bot]
    haveI : C.Normal := normal_perfectCore_top
    refine hodd ?_
    have h2rel : 2 ∣ C.relIndex K := by rw [hrel]; exact h2K
    exact h2rel.trans (Subgroup.relIndex_dvd_index_of_normal C K)
  · have hCK : C ≤ K := inf_eq_right.mp htop
    have hrdvd : r ∣ Nat.card ↥K := hrC.trans (Subgroup.card_dvd_of_le hCK)
    rcases IsSymThreeOrSUThreeTwo.prime_eq_of_dvd_card hbK hr hrdvd with h | h
    · exact hr2 h
    · exact hr3 h

theorem cZero_eq_singleton_of_perfectCore {X : Subgroup G} {D : Type} [Group D] [Finite D]
    {ψ : ↥X →* D} (hψ : Function.Surjective ψ) (hker : IsPGroup 2 ψ.ker)
    (hD : CFSG.pCore 2 D = ⊥)
    (hC : IsSimpleGroup ↥(CFSG.Quasithin.perfectCore (⊤ : Subgroup D)))
    (hodd : ¬ 2 ∣ (CFSG.Quasithin.perfectCore (⊤ : Subgroup D)).index)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (hrC : r ∣ Nat.card ↥(CFSG.Quasithin.perfectCore (⊤ : Subgroup D))) :
    ∃ I : Subgroup G, cZero X = {I} ∧
      Nonempty (↥I ⧸ CFSG.pCore 2 ↥I ≃*
        ↥(CFSG.Quasithin.perfectCore (⊤ : Subgroup D))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup D := CFSG.Quasithin.perfectCore (⊤ : Subgroup D)
  have hCcomp : IsComponentOf C ⊤ := isComponent_perfectCore_top hC
  obtain ⟨I₀, hI₀cZ, hI₀map⟩ := CZeroLift.exists_cZero_of_component ψ hψ hker hD hCcomp
  have hCp : CFSG.pCore 2 ↥C = ⊥ :=
    CZeroLift.pCore_eq_bot_of_isSubnormal hCcomp.2.1 hD
  have hI₀eq : I₀ = CFSG.Quasithin.perfectCore X := by
    rcases hI₀cZ.shape with hc | ⟨-, hb⟩
    · exact eq_perfectCore_of_isTwoPrimeComponent hψ hker hD hC hI₀cZ hc
    · exact (false_of_symThree_member hψ hker hD hC hodd hr hr2 hr3 hrC hI₀cZ.le
        hI₀cZ.subnormal hb).elim
  have hset : cZero X = {I₀} := by
    ext I
    constructor
    · intro hI
      rw [Set.mem_singleton_iff]
      rcases hI.shape with hc | ⟨-, hb⟩
      · rw [eq_perfectCore_of_isTwoPrimeComponent hψ hker hD hC hI hc, ← hI₀eq]
      · exact (false_of_symThree_member hψ hker hD hC hodd hr hr2 hr3 hrC hI.le
          hI.subnormal hb).elim
    · intro hI
      rw [Set.mem_singleton_iff] at hI
      simpa [hI] using hI₀cZ
  obtain ⟨-, ⟨e⟩⟩ := CZeroLift.pCore_eq_and_equiv ψ hI₀cZ.le hker
    (by rw [hI₀map]; exact hCp)
  exact ⟨I₀, hset, ⟨e.trans (MulEquiv.subgroupCongr hI₀map)⟩⟩

private theorem false_of_isTwoPrimeComponent_mem_cZero_of_perfectCore_eq_bot
    {X : Subgroup G} {D : Type} [Group D] [Finite D] {ψ : ↥X →* D}
    (hψ : Function.Surjective ψ) (hker : IsPGroup 2 ψ.ker) (hD : CFSG.pCore 2 D = ⊥)
    (hpc : CFSG.Quasithin.perfectCore (⊤ : Subgroup D) = ⊥) {I : Subgroup G}
    (hI : I ∈ cZero X) (hc : IsTwoPrimeComponent I I) : False := by
  have hIpc : I ≤ CFSG.Quasithin.perfectCore X :=
    CFSG.Quasithin.le_perfectCore_of_perfect hI.le hc.perfect
  have hKbot : (I.subgroupOf X).map ψ = ⊥ := by
    have hKle : (I.subgroupOf X).map ψ ≤
        CFSG.Quasithin.perfectCore (⊤ : Subgroup D) := by
      rw [← map_subgroupOf_perfectCore ψ hψ]
      exact Subgroup.map_mono (Subgroup.subgroupOf_mono X hIpc)
    rwa [hpc, le_bot_iff] at hKle
  exact not_isPGroup_of_isTwoPrimeComponent hc
    (Aux.isPGroup_of_map_eq_bot hψ hker hD hI.le hKbot)

private theorem card_eq_six_of_mulEquiv_perm_three {D : Type} [Group D] [Finite D]
    (e : D ≃* Equiv.Perm (Fin 3)) : Nat.card D = 6 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num

private theorem card_eq_six_of_isSymThreeOrSUThreeTwo_of_le_perm_three
    {D : Type} [Group D] [Finite D] (e : D ≃* Equiv.Perm (Fin 3))
    {K : Subgroup D} (h : IsSymThreeOrSUThreeTwo ↥K) : Nat.card ↥K = 6 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDcard : Nat.card D = 6 := card_eq_six_of_mulEquiv_perm_three e
  rcases h with ⟨e3⟩ | ⟨K', hfield, hfin, hK4, ⟨eSU⟩⟩
  · rw [Nat.card_congr e3.some.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    norm_num
  · exfalso
    letI : Field K' := hfield
    letI : Finite K' := hfin
    have h216 : Nat.card ↥(StatedSU 3 2 K') = 216 := by
      haveI := CFSG.HardMathSupport.Solomon.Proving.charP_two_of_card_four K' hK4
      have h := CFSG.SectionRank.OddCover.card_statedSU_three (K := K') (p := 2) (f := 1)
        (by rw [hK4]; norm_num)
      rw [pow_one] at h
      norm_num at h ⊢
      exact h
    have hdvd : Nat.card ↥K ∣ Nat.card D := Subgroup.card_subgroup_dvd_card K
    rw [hDcard, Nat.card_congr eSU.toEquiv, h216] at hdvd
    norm_num at hdvd

private theorem eq_of_symThree_mem_cZero_of_perm_three {X : Subgroup G}
    {D : Type} [Group D] [Finite D] {ψ : ↥X →* D}
    (hψ : Function.Surjective ψ) (hker : IsPGroup 2 ψ.ker) (hD : CFSG.pCore 2 D = ⊥)
    (e : D ≃* Equiv.Perm (Fin 3)) {I : Subgroup G} (hI : I ∈ cZero X)
    (hpcI : pCoreOf 2 I = pCoreOf 2 X)
    (hb : IsSymThreeOrSUThreeTwo (↥I ⧸ CFSG.pCore 2 ↥I)) : I = X := by
  have hIX : I ≤ X := hI.le
  have hpX : CFSG.pCore 2 ↥X = ψ.ker := CZeroLift.pCore_eq_ker ψ hψ hker hD
  have hIpcore : pCoreOf 2 X ≤ I := by
    rw [← hpcI]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 I
  have hkerI : ψ.ker ≤ I.subgroupOf X := by
    intro u hu
    rw [Subgroup.mem_subgroupOf]
    have hu' : (u : G) ∈ pCoreOf 2 X := by
      rw [← hpX] at hu
      exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
    exact hIpcore hu'
  let K : Subgroup D := (I.subgroupOf X).map ψ
  have hKsub : IsSubnormal K ⊤ := Aux.isSubnormal_map hψ hIX hI.subnormal
  have hKO : CFSG.pCore 2 ↥K = ⊥ := CZeroLift.pCore_eq_bot_of_isSubnormal hKsub hD
  obtain ⟨-, ⟨eI⟩⟩ := CZeroLift.pCore_eq_and_equiv ψ hIX hker hKO
  have hbK : IsSymThreeOrSUThreeTwo ↥K := IsSymThreeOrSUThreeTwo.of_mulEquiv eI hb
  have hKcard : Nat.card ↥K = 6 := card_eq_six_of_isSymThreeOrSUThreeTwo_of_le_perm_three e hbK
  have hKtop : K = ⊤ :=
    Subgroup.eq_top_of_card_eq K (by rw [hKcard, card_eq_six_of_mulEquiv_perm_three e])
  refine le_antisymm hIX ?_
  intro x hx
  have hxK : ψ ⟨x, hx⟩ ∈ K := by
    rw [hKtop]
    exact Subgroup.mem_top _
  obtain ⟨i, hiI, hψi⟩ := Subgroup.mem_map.mp hxK
  have hiI' : (i : G) ∈ I := Subgroup.mem_subgroupOf.mp hiI
  have hkerx : (⟨x, hx⟩ * i⁻¹ : ↥X) ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hψi, mul_inv_cancel]
  have hxI : x * (i : G)⁻¹ ∈ I := by
    have := hkerI hkerx
    simpa using Subgroup.mem_subgroupOf.mp this
  have hxeq : x = (x * (i : G)⁻¹) * (i : G) := by group
  rw [hxeq]
  exact I.mul_mem hxI hiI'

theorem cZero_eq_singleton_of_perm_three {X : Subgroup G} {D : Type} [Group D] [Finite D]
    {ψ : ↥X →* D} (hψ : Function.Surjective ψ) (hker : IsPGroup 2 ψ.ker)
    (hD : CFSG.pCore 2 D = ⊥) (e : D ≃* Equiv.Perm (Fin 3)) :
    cZero X = {X} ∧
      Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* Equiv.Perm (Fin 3)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
  haveI : Group.IsSolvable D :=
    Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hpc : CFSG.Quasithin.perfectCore (⊤ : Subgroup D) = ⊥ := by
    refine (CFSG.Quasithin.isSolvable_iff_perfectCore_eq_bot (⊤ : Subgroup D)).mp ?_
    exact Group.isSolvable_of_isSolvable_injective (f := (⊤ : Subgroup D).subtype)
      (Subgroup.subtype_injective _)
  have hpX : CFSG.pCore 2 ↥X = ψ.ker := CZeroLift.pCore_eq_ker ψ hψ hker hD
  let eX : ↥X ⧸ CFSG.pCore 2 ↥X ≃* D :=
    (QuotientGroup.quotientMulEquivOfEq hpX).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  have hXmem : X ∈ cZero X := by
    have hshape : IsSymThreeOrSUThreeTwo (↥X ⧸ CFSG.pCore 2 ↥X) :=
      IsSymThreeOrSUThreeTwo.of_mulEquiv (eX.trans e).symm (Or.inl ⟨MulEquiv.refl _⟩)
    exact ⟨le_rfl, .refl X, Or.inr ⟨rfl, hshape⟩⟩
  have hIeq : ∀ I ∈ cZero X, I = X := by
    intro I hI
    rcases hI.shape with hc | ⟨hpcI, hb⟩
    · exact (false_of_isTwoPrimeComponent_mem_cZero_of_perfectCore_eq_bot hψ hker hD hpc
        hI hc).elim
    · exact eq_of_symThree_mem_cZero_of_perm_three hψ hker hD e hI hpcI hb
  have hset : cZero X = {X} := by
    ext I
    constructor
    · intro hI
      rw [Set.mem_singleton_iff]
      exact hIeq I hI
    · intro hI
      rw [Set.mem_singleton_iff] at hI
      simpa [hI] using hXmem
  exact ⟨hset, ⟨eX.trans e⟩⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12.CZeroUnique

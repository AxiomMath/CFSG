module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3Shadow
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1Struct3
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1Struct2
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1Struct4
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1L44c

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem isPGroup_three_of_normal_cyclic_sylow {Y : Type} [Group Y] [Finite Y]
    (hcore : primeComplementCore (G := Y) 3 = ⊥) {D : Subgroup Y} [D.Normal] {z : Y}
    (hz : z ∈ Subgroup.center Y) (hzo : orderOf z = 3) (hzD : z ∈ D)
    (hcyc : ∀ T : Sylow 3 D, IsCyclic ↥(T : Subgroup D)) : IsPGroup 3 D := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S⟩ : Nonempty (Sylow 3 D) := inferInstance
  set z' : D := ⟨z, hzD⟩ with hz'def
  have hz' : z' ∈ center D := mem_center_iff.mpr fun d => Subtype.ext (mem_center_iff.mp hz d)
  have hzo' : orderOf z' = 3 := by rw [← hzo, ← Subgroup.orderOf_coe]
  have hNC := r1s_normalizer_le_centralizer S (hcyc S) hz' hzo'
  have hcomp := MonoidHom.ker_transferSylow_isComplement' S hNC
  set K : Subgroup D := (MonoidHom.transferSylow S hNC).ker with hK
  have hKcop : Nat.Coprime 3 (Nat.card K) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (MonoidHom.not_dvd_card_ker_transferSylow S hNC)
  have hmem : ∀ d : D, Nat.Coprime 3 (orderOf d) → d ∈ K := by
    intro d hd
    rw [hK, MonoidHom.mem_ker]
    obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp S.isPGroup' (MonoidHom.transferSylow S hNC d)
    have h1 : orderOf (MonoidHom.transferSylow S hNC d) ∣ orderOf d := orderOf_map_dvd _ d
    rw [hj] at h1
    have : 3 ^ j = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left j hd) h1
    rw [this] at hj
    exact orderOf_eq_one_iff.mp hj
  have hKY : (K.map D.subtype).Normal := by
    refine ⟨fun m hm y => ?_⟩
    obtain ⟨k, hk, rfl⟩ := hm
    have hyD : y * (k : Y) * y⁻¹ ∈ D := ‹D.Normal›.conj_mem _ k.2 y
    refine ⟨⟨y * (k : Y) * y⁻¹, hyD⟩, hmem _ ?_, rfl⟩
    have h1 : orderOf (⟨y * (k : Y) * y⁻¹, hyD⟩ : D) = orderOf k := by
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe k]
      exact (MulAut.conj y).orderOf_eq (k : Y)
    rw [h1]
    exact hKcop.coprime_dvd_right (Subgroup.orderOf_dvd_natCard K hk)
  have hKbot : K.map D.subtype = ⊥ := by
    have hle := normal_coprime_le_primeComplementCore 3 (K.map D.subtype) hKY
      (by rwa [Subgroup.card_map_of_injective D.subtype_injective])
    rwa [hcore, le_bot_iff] at hle
  have hK1 : K = ⊥ := (Subgroup.map_eq_bot_iff_of_injective K D.subtype_injective).mp hKbot
  have hcard := hcomp.card_mul_card
  rw [hK1, Subgroup.card_bot, one_mul] at hcard
  obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
  exact IsPGroup.of_card (n := n) (by rw [← hcard, hn])

theorem m11_reducedCentralizer_sylow_cyclic (hS : Setting G) (hU0 : FullCoreLocal G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsM11Normal M x J)
    (T : Sylow 3 (reducedCentralizerOfJ x J)) :
    IsCyclic ↥(T : Subgroup (reducedCentralizerOfJ x J)) := by
  obtain ⟨S, -, hsh⟩ := exists_genericShadow3 hS hU0 hp rfl hM hgen
  have := r1sBar_normal hJ
  have := r1sBar_perfect hJ
  exact r1s_sylow_centralizer_cyclic hsh.rank_eq.le (r1s_reducedCentralizerOfJ_eq x J)
    (r1sBar_sylow_facts hKM hKA hJ) T

theorem m11_reducedCentralizer_isPGroup (hS : Setting G) (hU0 : FullCoreLocal G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsM11Normal M x J) :
    IsPGroup 3 (reducedCentralizerOfJ x J) := by
  obtain ⟨S, -, hsh⟩ := exists_genericShadow3 hS hU0 hp rfl hM hgen
  have := r1sBar_normal hJ
  have hDn : (reducedCentralizerOfJ x J).Normal := by
    rw [r1s_reducedCentralizerOfJ_eq]
    infer_instance
  refine isPGroup_three_of_normal_cyclic_sylow hsh.core_eq_bot hsh.mem_center hsh.orderOf_eq ?_
    (m11_reducedCentralizer_sylow_cyclic hS hU0 hKM hKA hp hM hgen hJ)
  rw [r1s_reducedCentralizerOfJ_eq]
  exact mem_centralizer_iff.mpr fun h _ => mem_center_iff.mp hsh.mem_center h

theorem m11_reducedCentralizer_isCyclic (hS : Setting G) (hU0 : FullCoreLocal G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsM11Normal M x J) :
    IsCyclic ↥(reducedCentralizerOfJ x J) := by
  have hDp := m11_reducedCentralizer_isPGroup hS hU0 hKM hKA hp hM hgen hJ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T⟩ : Nonempty (Sylow 3 (reducedCentralizerOfJ x J)) := inferInstance
  have hT : (T : Subgroup (reducedCentralizerOfJ x J)) = ⊤ :=
    (T.3 (hDp.of_equiv Subgroup.topEquiv.symm) le_top).symm
  have hc := m11_reducedCentralizer_sylow_cyclic hS hU0 hKM hKA hp hM hgen hJ T
  rw [hT] at hc
  exact isCyclic_of_surjective (Subgroup.topEquiv : (⊤ : Subgroup (reducedCentralizerOfJ x J)) ≃*
    reducedCentralizerOfJ x J) Subgroup.topEquiv.surjective

theorem m11_bar_inf_reducedCentralizer_eq_bot {M : Subgroup G} {x : G} {J : Subgroup G}
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hJ : IsM11Normal M x J) : r1sBar x J ⊓ reducedCentralizerOfJ x J = ⊥ := by
  have := r1sBar_perfect hJ
  exact r1s_inf_centralizer_eq_bot (r1s_reducedCentralizerOfJ_eq x J) fun T =>
    ⟨(r1sBar_sylow_facts hKM hKA hJ T).1.1, (r1sBar_sylow_facts hKM hKA hJ T).2.2⟩

theorem m11_inf_ne_bot (hS : Setting G) (hU0 : FullCoreLocal G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsM11Normal M x J)
    {U : Subgroup G} (hU : IsElemAbelian 3 U) (hUc : Nat.card U = 3 ^ 2)
    (_hUP : U ≤ (P : Subgroup G)) (hxU : x ∈ U) : U ⊓ J ≠ ⊥ := by
  intro hUJ
  have := r1sBar_normal hJ
  obtain ⟨e⟩ := r1sBar_nonempty_equiv hJ
  have hdec := l44_decomp (r1sBar x J) (hKM _ ⟨e⟩).1
  have := m11_reducedCentralizer_isCyclic hS hU0 hKM hKA hp hM hgen hJ
  have hcycQ : IsCyclic (GenericReduced 3 x ⧸ r1sBar x J) :=
    r1s_isCyclic_quotient (D := reducedCentralizerOfJ x J) hdec
  have := hU.1
  have hUC : U ≤ centralizer ({x} : Set G) := fun u hu => mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mul_comm' (⟨u, hu⟩ : U) ⟨x, hxU⟩))
  let g : ↥U →* GenericReduced 3 x ⧸ r1sBar x J :=
    (QuotientGroup.mk' (r1sBar x J)).comp
      ((QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3)).comp
        (Subgroup.inclusion hUC))
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 := (QuotientGroup.eq_one_iff _).mp hu
    have h2 : (u : G) ∈ J := r1s_mem_of_mk_mem hJ (hUC u.2) (hU.2 u u.2) h1
    have h3 : (u : G) ∈ U ⊓ J := ⟨u.2, h2⟩
    rw [hUJ, mem_bot] at h3
    exact Subtype.ext h3
  exact r1s_not_isCyclic_of_pow_three hU.2 hUc (isCyclic_of_injective g hinj)

end CFSG.LocalAnalysis.RankThreeTheoremC

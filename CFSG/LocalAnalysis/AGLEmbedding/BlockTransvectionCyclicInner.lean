module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockTransvectionCyclicLift
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFourAux
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {M S L : Subgroup G}

theorem mem_blockPL_of_conj (h86 : Asc81bEightSix) (hK : Open.IsKGroup ↥M)
    (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hZS : barM M L ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
      Subgroup.centralizer (barM M S : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    {l : ↥M ⧸ CFSG.pCore 2 ↥M} (hl : l ∈ barM M L)
    (hlS : ∀ s ∈ barM M S, ∃ s' ∈ barM M S, ∀ y ∈ barM M L,
      (l * s * l⁻¹) * y * (l * s * l⁻¹)⁻¹ = s' * y * s'⁻¹) :
    l ∈ barM M (Subgroup.normalizer (S : Set G) ⊓ L) := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Lb := barM M L
  set Sb := barM M S
  set LS := barM M (L ⊔ S)
  set C := Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M))
  set Z := Lb ⊓ C
  set D := C ⊓ LS
  have hSL : S ≤ Subgroup.normalizer (L : Set G) :=
    hL.toIsTwoPrimeComponent.le_normalizer (h86 G M S hK hA _ hL.component) hA.twoRadical.1
  have hrad := hA.twoCore_eq_pCoreOf_normalizer_sup hL.toIsTwoPrimeComponent hSL
  have hSM : S ≤ M := hA.twoRadical.1
  have hQS : pCoreOf 2 M ≤ S := hA.twoCore_le
  have hLM : L ≤ M := hL.le
  have hS2 : IsPGroup 2 S := hA.twoRadical.isPGroup
  have hSb2 : IsPGroup 2 Sb := hS2.comap_subtype.map _
  have hLbLS : Lb ≤ LS := barM_mono le_sup_left
  have hSbLS : Sb ≤ LS := barM_mono le_sup_right
  have hLsub : IsSubnormal Lb ⊤ := hL.component.2.1
  have hZodd : Nat.Coprime 2 (Nat.card Z) :=
    coprime_two_card_inf_centralizer (pCore_quotient_pCore_eq_bot' 2) hLsub
  have hZ2 : ∀ z ∈ Z, ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1 := by
    intro z hz k hzk
    have h1 : orderOf z ∣ Nat.card Z := Z.orderOf_dvd_natCard hz
    have h2 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hzk
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (hZodd.pow_left k) h2 h1)
  have hDZ : ∀ d ∈ D, ∃ k : ℕ, d ^ 2 ^ k ∈ Z := by
    rintro d ⟨hdC, hdLS⟩
    obtain ⟨m, hm, rfl⟩ := hdLS
    have hm' : (m : G) ∈ S ⊔ L := by
      rw [sup_comm]
      exact Subgroup.mem_subgroupOf.mp hm
    obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_sup_of_isPGroup hS2 hSL hm'
    refine ⟨k, ⟨?_, C.pow_mem hdC _⟩⟩
    rw [← map_pow]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (by simpa using hk))
  have hcomm : ∀ d ∈ D, ∀ z ∈ Z, d * z = z * d := fun d hd z hz =>
    (Subgroup.mem_centralizer_iff.mp hd.1 z hz.1).symm
  have hTS : pCoreOf 2 D ≤ Sb := by
    set T := pCoreOf 2 D
    set Xg : Subgroup G := (T.comap mk).map M.subtype
    have hLSM : L ⊔ S ≤ M := sup_le hLM hSM
    have hLSN : L ⊔ S ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hSL
    have hNC : Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
        Subgroup.normalizer (C : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer _)
    have hXN : L ⊔ S ≤ Subgroup.normalizer (Xg : Set G) := by
      intro g hg
      have hgLS : mk ⟨g, hLSM hg⟩ ∈ LS :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hg)
      have hgD : mk ⟨g, hLSM hg⟩ ∈ Subgroup.normalizer (D : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
        Subgroup.inf_normalizer_le_normalizer_inf
          ⟨hNC (barM_le_normalizer_barM hLSN hgLS), Subgroup.le_normalizer hgLS⟩
      exact Subgroup.le_normalizer_map M.subtype (Subgroup.mem_map_of_mem _
        (Subgroup.le_normalizer_comap mk (normalizer_localGroup_le_normalizer_pCoreOf 2 D hgD)))
    have hXLS : Xg ≤ L ⊔ S := by
      rintro _ ⟨m, hm, rfl⟩
      exact coe_mem_of_mk_mem_barM (hQS.trans le_sup_right) m
        (((pCoreOf_le 2 D).trans inf_le_right) hm)
    have hX2 : IsPGroup 2 Xg :=
      (IsPGroup.comap_of_ker_isPGroup (pCoreOf_isPGroup 2 D) mk
        (by rw [hmk, QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup)).map M.subtype
    have hXS : Xg ≤ S :=
      le_of_two_radical le_sup_right hrad hXLS hX2 fun g hg => hXN hg.1
    intro c hc
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M) c
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hXS ⟨m, hc, rfl⟩))
  have hconj : ∀ s ∈ Sb, l * s * l⁻¹ ∈ Sb := by
    intro s hs
    obtain ⟨s', hs', heq⟩ := hlS s hs
    have hdC : s'⁻¹ * (l * s * l⁻¹) ∈ C := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      calc y * (s'⁻¹ * (l * s * l⁻¹)) = s'⁻¹ * (s' * y * s'⁻¹) * (l * s * l⁻¹) := by group
        _ = s'⁻¹ * ((l * s * l⁻¹) * y * (l * s * l⁻¹)⁻¹) * (l * s * l⁻¹) := by
          rw [heq y hy]
        _ = s'⁻¹ * (l * s * l⁻¹) * y := by group
    have hdLS : s'⁻¹ * (l * s * l⁻¹) ∈ LS :=
      LS.mul_mem (LS.inv_mem (hSbLS hs'))
        (LS.mul_mem (LS.mul_mem (hLbLS hl) (hSbLS hs)) (LS.inv_mem (hLbLS hl)))
    obtain ⟨c, hc, z, hz, hdz⟩ := exists_mul_of_pow_mem_of_commute hcomm hDZ ⟨hdC, hdLS⟩
    have hu : s' * c ∈ Sb := Sb.mul_mem hs' (hTS hc)
    have htu : l * s * l⁻¹ = (s' * c) * z := by
      rw [mul_assoc s' c z, ← hdz, mul_inv_cancel_left]
    have hzu : Commute (s' * c) z := Subgroup.mem_centralizer_iff.mp (hZS hz) _ hu
    obtain ⟨k, hk⟩ := hSb2 ⟨s, hs⟩
    obtain ⟨j, hj⟩ := hSb2 ⟨s' * c, hu⟩
    have hsk : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have huj : (s' * c) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have htn : (l * s * l⁻¹) ^ 2 ^ (k + j) = 1 := by
      rw [conj_pow, pow_add, pow_mul, hsk, one_pow, mul_one, mul_inv_cancel]
    have hun : (s' * c) ^ 2 ^ (k + j) = 1 := by
      rw [pow_add, pow_mul', huj, one_pow]
    have hzn : z ^ 2 ^ (k + j) = 1 := by
      rw [htu, hzu.mul_pow, hun, one_mul] at htn
      exact htn
    rw [htu, hZ2 z hz _ hzn, mul_one]
    exact hu
  have hlN : l ∈ Subgroup.normalizer (Sb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hle : Sb.map (MulAut.conj l).toMonoidHom ≤ Sb := by
      rintro _ ⟨s, hs, rfl⟩
      exact hconj s hs
    exact Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj l).injective).ge
  have hK' : ((Subgroup.normalizer (Sb : Set (↥M ⧸ CFSG.pCore 2 ↥M))).comap mk).map M.subtype ≤
      Subgroup.normalizer (S : Set G) := by
    refine le_normalizer_of_forall_map_conj_le fun g hg => ?_
    obtain ⟨g', hg', rfl⟩ := hg
    rintro _ ⟨s, hs, rfl⟩
    have hsb : mk ⟨s, hSM hs⟩ ∈ Sb :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hs)
    have h1 : mk (g' * ⟨s, hSM hs⟩ * g'⁻¹) ∈ Sb := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hg' _).mp hsb
    have h2 := coe_mem_of_mk_mem_barM hQS _ h1
    simpa [MulAut.conj_apply] using h2
  obtain ⟨m, hmL, rfl⟩ := hl
  exact Subgroup.mem_map_of_mem _
    (Subgroup.mem_subgroupOf.mpr ⟨hK' ⟨m, hlN, rfl⟩, Subgroup.mem_subgroupOf.mp hmL⟩)

@[expose] def BlockTransvectionOddInner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G) (p : ℕ), Open.IsKGroup ↥M →
    Asc81bHyp M S → IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    NineThreeThree M S L → p.Prime → p ≠ 2 →
    PerfectCyclicSylow p (barM M (Subgroup.normalizer (S : Set G) ⊓ L)) →
    ∀ x ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
      (∃ k : ℕ, x ^ p ^ k = 1) →
      x ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))

@[expose] def BlockTransvectionCenter : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M →
    Asc81bHyp M S → IsWeakSBlock M S L → NineThreeThree M S L →
    barM M L ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥

theorem citedBlockTransvectionInner_of (h86 : Asc81bEightSix) (hOdd : BlockTransvectionOddInner)
    (hZ : BlockTransvectionCenter) : CitedBlockTransvectionInner := by
  intro G _ _ M S L p hK hA hL hX hS h3 hp hp2 hperf u huS huL ⟨k, hk⟩
  set q := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  set Lb := barM M L
  set Cb := Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M))
  have huN : q u ∈ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    mem_normalizer_barM u.2 huL
  have huSb : q u ∈ Subgroup.normalizer (barM M S : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    mem_normalizer_barM u.2 huS
  have hk' : q u ^ p ^ k = 1 := by rw [← map_pow, hk, map_one]
  have hLC := hOdd G M S L p hK hA hL hX hS h3 hp hp2 hperf (q u) huN ⟨k, hk'⟩
  have hLCn : Lb ≤ Subgroup.normalizer (Cb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    Subgroup.le_normalizer.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer _))
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right Lb Cb hLCn] at hLC
  obtain ⟨l, hl, c, hc, hlc⟩ := hLC
  have hconj : ∀ x ∈ Lb, q u * x * (q u)⁻¹ = l * x * l⁻¹ := by
    intro x hx
    have hcx : c * x * c⁻¹ = x := by
      have h := Subgroup.mem_centralizer_iff.mp hc x hx
      rw [← h, mul_inv_cancel_right]
    rw [← hlc]
    calc l * c * x * (l * c)⁻¹ = l * (c * x * c⁻¹) * l⁻¹ := by group
      _ = l * x * l⁻¹ := by rw [hcx]
  have hZS : Lb ⊓ Cb ≤ Subgroup.centralizer (barM M S : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rw [hZ G M S L hK hA hL h3]
    exact bot_le
  have hSLb : barM M S ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    h86 G M S hK hA _ hL.component
  refine ⟨l, mem_blockPL_of_conj h86 hK hA hL hZS hl fun s hs => ?_, hconj⟩
  refine ⟨q u * s * (q u)⁻¹, (Subgroup.mem_normalizer_iff.mp huSb s).mp hs, fun y hy => ?_⟩
  have hl' : l⁻¹ * y * l ∈ Lb := Lb.mul_mem (Lb.mul_mem (Lb.inv_mem hl) hy) hl
  have hsy : s * (l⁻¹ * y * l) * s⁻¹ ∈ Lb := (Subgroup.mem_normalizer_iff.mp (hSLb hs) _).mp hl'
  have h1 : (q u)⁻¹ * y * q u = l⁻¹ * y * l := by
    have := hconj ((q u)⁻¹ * y * q u) (by
      have hyN := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ huN) y).mp hy
      simpa using hyN)
    rw [show q u * ((q u)⁻¹ * y * q u) * (q u)⁻¹ = y by group] at this
    calc (q u)⁻¹ * y * q u = l⁻¹ * (l * ((q u)⁻¹ * y * q u) * l⁻¹) * l := by group
      _ = l⁻¹ * y * l := by rw [← this]
  calc (l * s * l⁻¹) * y * (l * s * l⁻¹)⁻¹ = l * (s * (l⁻¹ * y * l) * s⁻¹) * l⁻¹ := by group
    _ = q u * (s * (l⁻¹ * y * l) * s⁻¹) * (q u)⁻¹ := (hconj _ hsy).symm
    _ = q u * (s * ((q u)⁻¹ * y * q u) * s⁻¹) * (q u)⁻¹ := by rw [h1]
    _ = (q u * s * (q u)⁻¹) * y * (q u * s * (q u)⁻¹)⁻¹ := by group

end CFSG.AGLEmbedding

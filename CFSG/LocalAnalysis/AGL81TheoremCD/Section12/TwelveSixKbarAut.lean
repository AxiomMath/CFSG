module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K5Small
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourOneProof
import CFSG.GroupTheory.PCore.NormalPCoreOf
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup
import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.Blueprint (LieModel)
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.GroupTheory.AutAlternating
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} {d : ℕ}
  {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}

private noncomputable def pCoreQuotAut (Y : Type*) [Group Y] :
    MulAut Y →* MulAut (Y ⧸ CFSG.pCore 2 Y) where
  toFun φ := QuotientGroup.congr (CFSG.pCore 2 Y) (CFSG.pCore 2 Y) φ
    (Subgroup.characteristic_iff_map_eq.mp inferInstance φ)
  map_one' := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    rfl
  map_mul' φ ψ := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    rfl

private noncomputable def barConj (K : Subgroup G) :
    ↥(Subgroup.normalizer (K : Set G)) →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K) :=
  (pCoreQuotAut ↥K).comp K.normalizerMonoidHom

private theorem barConj_mk (K : Subgroup G)
    (y : ↥(Subgroup.normalizer (K : Set G))) (k : ↥K) :
    barConj K y (QuotientGroup.mk k) =
      QuotientGroup.mk (⟨(y : G) * k * (y : G)⁻¹, (y.2 k).mp k.2⟩ : ↥K) :=
  rfl

private theorem coe_mem_pCoreOf_iff {K : Subgroup G} (x : ↥K) :
    (x : G) ∈ pCoreOf 2 K ↔ x ∈ CFSG.pCore 2 ↥K := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    rwa [← Subtype.ext hyx]
  · intro hx
    exact ⟨x, hx, rfl⟩

private theorem le_normalizer_kSub (hKH : ((kSub p M H).subgroupOf H).Normal) :
    H ≤ Subgroup.normalizer (kSub p M H : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    (CFSG.LocalAnalysis.AGL81TheoremCD.Section14.kSub_le p M H)).mp hKH

noncomputable def kbarConj (hKH : ((kSub p M H).subgroupOf H).Normal) :
    ↥H →* MulAut (modTwoCore (kSub p M H)) :=
  (barConj (kSub p M H)).comp
    (Subgroup.inclusion (le_normalizer_kSub hKH))

theorem kbarConj_mk (hKH : ((kSub p M H).subgroupOf H).Normal) (y : ↥H)
    (k : ↥(kSub p M H)) :
    kbarConj hKH y (QuotientGroup.mk k) =
      QuotientGroup.mk
        (⟨(y : G) * k * (y : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp
            ((Subgroup.normal_subgroupOf_iff_le_normalizer
              (CFSG.LocalAnalysis.AGL81TheoremCD.Section14.kSub_le p M H)).mp hKH y.2)
            (k : G)).mp k.2⟩ :
          ↥(kSub p M H)) := by
  exact barConj_mk (kSub p M H) (Subgroup.inclusion _ y) k

private theorem mem_xSub_iff {p : ℕ} {M H : Subgroup G} {z : G} (hz : z ∈ H) :
    z ∈ xSub p M H ↔
      QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨z, hz⟩ ∈
        Subgroup.centralizer (kStar p M H : Set (StarGroup p H)) := by
  have hsub : ((xSub p M H).subgroupOf H) =
      (Subgroup.centralizer (kStar p M H)).comap
        (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) := by
    rw [xSub]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have h1 : (⟨z, hz⟩ : ↥H) ∈ (xSub p M H).subgroupOf H ↔ z ∈ xSub p M H :=
    Subgroup.mem_subgroupOf
  have h2 : (⟨z, hz⟩ : ↥H) ∈ (Subgroup.centralizer (kStar p M H)).comap
        (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) ↔ z ∈ xSub p M H := by
    rw [← hsub]
    exact h1
  rw [Subgroup.mem_comap] at h2
  exact h2.symm

private theorem commutator_mem_pCoreOf_of_mem_ker
    (hKH : ((kSub p M H).subgroupOf H).Normal) {y : ↥H}
    (hy : y ∈ (kbarConj hKH).ker) (k : ↥(kSub p M H)) :
    (y : G) * k * (y : G)⁻¹ * (k : G)⁻¹ ∈ pCoreOf 2 (kSub p M H) := by
  have hmem : (y : G) * k * (y : G)⁻¹ ∈ kSub p M H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_kSub hKH y.2) (k : G)).mp k.2
  have hfix : kbarConj hKH y (QuotientGroup.mk k) = QuotientGroup.mk k := by
    have hy1 : kbarConj hKH y = 1 := MonoidHom.mem_ker.mp hy
    rw [hy1]
    rfl
  have hq : (QuotientGroup.mk (⟨(y : G) * k * (y : G)⁻¹, hmem⟩ :
      ↥(kSub p M H)) : modTwoCore (kSub p M H)) = QuotientGroup.mk k := by
    change kbarConj hKH y (QuotientGroup.mk k) = QuotientGroup.mk k
    exact hfix
  have hdiv : (⟨(y : G) * k * (y : G)⁻¹, hmem⟩ : ↥(kSub p M H)) / k ∈
      CFSG.pCore 2 ↥(kSub p M H) :=
    QuotientGroup.eq_iff_div_mem.mp hq
  have hcoe := (coe_mem_pCoreOf_iff ((⟨(y : G) * k * (y : G)⁻¹, hmem⟩ :
    ↥(kSub p M H)) / k)).mpr hdiv
  simpa [div_eq_mul_inv] using hcoe

private theorem commutator_mem_primeComplementCore_of_mem_pCoreOf
    (h : TwelveCtx G M p Q H) (hKH : ((kSub p M H).subgroupOf H).Normal)
    {y : ↥H} {kH : ↥H}
    (hcommK : (y : G) * kH * (y : G)⁻¹ * (kH : G)⁻¹ ∈
      pCoreOf 2 (kSub p M H)) :
    (⁅y, kH⁆ : ↥H) ∈ primeComplementCore (G := ↥H) p := by
  have hKleH : kSub p M H ≤ H :=
    CFSG.LocalAnalysis.AGL81TheoremCD.Section14.kSub_le p M H
  have hcore_le : pCoreOf 2 (kSub p M H) ≤ pCoreOf 2 H :=
    CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hKleH (le_normalizer_kSub hKH)
  have hcommHcore : (y : G) * kH * (y : G)⁻¹ * (kH : G)⁻¹ ∈ pCoreOf 2 H :=
    hcore_le hcommK
  have hcommH : (y : G) * kH * (y : G)⁻¹ * (kH : G)⁻¹ ∈ H :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 H) hcommHcore
  have hcommP : (⟨(y : G) * kH * (y : G)⁻¹ * (kH : G)⁻¹, hcommH⟩ : ↥H) ∈
      CFSG.pCore 2 ↥H := by
    obtain ⟨u, hu, huc⟩ := Subgroup.mem_map.mp hcommHcore
    have hueq : u = ⟨(y : G) * kH * (y : G)⁻¹ * (kH : G)⁻¹, hcommH⟩ := Subtype.ext huc
    rwa [hueq] at hu
  have hcommPC : (⟨(y : G) * kH * (y : G)⁻¹ * (kH : G)⁻¹, hcommH⟩ : ↥H) ∈
      primeComplementCore (G := ↥H) p :=
    CFSG.AGLEmbedding.pCore_two_le_primeComplementCore h.p_prime h.p_odd hcommP
  rw [show (⁅y, kH⁆ : ↥H) =
    ⟨(y : G) * kH * (y : G)⁻¹ * (kH : G)⁻¹, hcommH⟩ from
      Subtype.ext (by simp [commutatorElement_def, mul_assoc])]
  exact hcommPC

theorem TwelveCtx.ker_kbarConj_le (h : TwelveCtx G M p Q H)
    (hKH : ((kSub p M H).subgroupOf H).Normal) :
    (kbarConj hKH).ker ≤ (xSub p M H).subgroupOf H := by
  intro y hy
  rw [Subgroup.mem_subgroupOf]
  rw [mem_xSub_iff y.2, Subgroup.mem_centralizer_iff]
  intro kbar hkbar
  change kbar ∈ ((kSub p M H).subgroupOf H).map
    (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) at hkbar
  rw [Subgroup.mem_map] at hkbar
  obtain ⟨kH, hkH, hkx⟩ := hkbar
  rw [← hkx]
  let k : ↥(kSub p M H) := ⟨kH, Subgroup.mem_subgroupOf.mp hkH⟩
  have hcommK := commutator_mem_pCoreOf_of_mem_ker hKH hy k
  have hcommPC : (⁅y, kH⁆ : ↥H) ∈ primeComplementCore (G := ↥H) p :=
    commutator_mem_primeComplementCore_of_mem_pCoreOf h hKH (by simpa [k] using hcommK)
  have hπ : ⁅QuotientGroup.mk' (primeComplementCore (G := ↥H) p) y,
      QuotientGroup.mk' (primeComplementCore (G := ↥H) p) kH⁆ = 1 := by
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr hcommPC
  exact (commutatorElement_eq_one_iff_mul_comm.mp hπ).symm

theorem TwelveCtx.xSub_inf_kSub_eq (h : TwelveCtx G M p Q H)
    (hKH : ((kSub p M H).subgroupOf H).Normal)
    (hK : IsTwoPrimeComponentIn (kSub p M H) H)
    (hZ : center (modTwoCore (kSub p M H)) = ⊥) :
    xSub p M H ⊓ kSub p M H = pCoreOf 2 (kSub p M H) := by
  have hXK := TwelveCtx.xSub_subgroupOf_kSub_eq h hKH hK
  rw [hZ, MonoidHom.comap_bot, QuotientGroup.ker_mk'] at hXK
  rw [← Subgroup.subgroupOf_map_subtype, hXK]
  rfl

theorem TwelveCtx.ker_kbarConj (h : TwelveCtx G M p Q H)
    (hKH : ((kSub p M H).subgroupOf H).Normal)
    (hK : IsTwoPrimeComponentIn (kSub p M H) H)
    (hZ : center (modTwoCore (kSub p M H)) = ⊥) :
    (kbarConj hKH).ker = (xSub p M H).subgroupOf H := by
  refine le_antisymm (TwelveCtx.ker_kbarConj_le h hKH) ?_
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  rw [MonoidHom.mem_ker]
  ext q
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  have hmem : (x : G) * k * (x : G)⁻¹ ∈ kSub p M H :=
    (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_kSub hKH x.2) (k : G)).mp k.2
  rw [kbarConj_mk hKH x k]
  have hconjX : (k : G) * (x : G) * (k : G)⁻¹ ∈ xSub p M H :=
    (Subgroup.mem_normalizer_iff.mp
      (xSub_normal_of_kSub_normal hKH
        (CFSG.LocalAnalysis.AGL81TheoremCD.Section14.kSub_le p M H k.2)) (x : G)).mp hx
  have hcommX : (x : G) * k * (x : G)⁻¹ * (k : G)⁻¹ ∈ xSub p M H := by
    have heq : (x : G) * k * (x : G)⁻¹ * (k : G)⁻¹ =
        (x : G) * ((k : G) * (x : G) * (k : G)⁻¹)⁻¹ := by group
    rw [heq]
    exact (xSub p M H).mul_mem hx ((xSub p M H).inv_mem hconjX)
  have hcommK : (x : G) * k * (x : G)⁻¹ * (k : G)⁻¹ ∈ kSub p M H := by
    have hconj : (x : G) * k * (x : G)⁻¹ ∈ kSub p M H :=
      (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_kSub hKH x.2) (k : G)).mp k.2
    exact (kSub p M H).mul_mem hconj ((kSub p M H).inv_mem k.2)
  have hcommInf : (x : G) * k * (x : G)⁻¹ * (k : G)⁻¹ ∈
      xSub p M H ⊓ kSub p M H := ⟨hcommX, hcommK⟩
  rw [TwelveCtx.xSub_inf_kSub_eq h hKH hK hZ] at hcommInf
  have hcommSub : (⟨(x : G) * k * (x : G)⁻¹ * (k : G)⁻¹, hcommK⟩ : ↥(kSub p M H)) ∈
      CFSG.pCore 2 ↥(kSub p M H) := (coe_mem_pCoreOf_iff _).mp hcommInf
  refine QuotientGroup.eq_iff_div_mem.mpr ?_
  have hdiv : (⟨(x : G) * k * (x : G)⁻¹, hmem⟩ : ↥(kSub p M H)) / k =
      (⟨(x : G) * k * (x : G)⁻¹ * (k : G)⁻¹, hcommK⟩ : ↥(kSub p M H)) := by
    refine Subtype.ext ?_
    simp [div_eq_mul_inv, mul_assoc]
  rw [hdiv]
  exact hcommSub

private theorem relIndex_sup_eq_card_modTwoCore (h : TwelveCtx G M p Q H)
    (hKH : ((kSub p M H).subgroupOf H).Normal)
    (hK : IsTwoPrimeComponentIn (kSub p M H) H)
    (hZ : center (modTwoCore (kSub p M H)) = ⊥) :
    ((xSub p M H).subgroupOf H).relIndex ((kSub p M H ⊔ xSub p M H).subgroupOf H) =
      Nat.card (modTwoCore (kSub p M H)) := by
  have hXleH : xSub p M H ≤ H := xSub_le_H p M H
  have hKleH : kSub p M H ≤ H :=
    CFSG.LocalAnalysis.AGL81TheoremCD.Section14.kSub_le p M H
  have hKXleH : kSub p M H ⊔ xSub p M H ≤ H := sup_le hKleH hXleH
  have hXleNK : xSub p M H ≤ Subgroup.normalizer (kSub p M H : Set G) :=
    hXleH.trans (le_normalizer_kSub hKH)
  have hsecond := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
    (H := xSub p M H) (K := kSub p M H) hXleNK).1
  have hsup : xSub p M H ⊔ kSub p M H = kSub p M H ⊔ xSub p M H := sup_comm ..
  have hrelH := Subgroup.relIndex_subgroupOf (G := G) (H := xSub p M H)
    (K := kSub p M H ⊔ xSub p M H) (L := H) hKXleH
  have hrelK := Subgroup.relIndex_subgroupOf (G := G)
    (H := pCoreOf 2 (kSub p M H))
    (K := kSub p M H) (L := kSub p M H) le_rfl
  calc ((xSub p M H).subgroupOf H).relIndex ((kSub p M H ⊔ xSub p M H).subgroupOf H)
      = (xSub p M H).relIndex (kSub p M H ⊔ xSub p M H) := hrelH
    _ = (xSub p M H).relIndex (xSub p M H ⊔ kSub p M H) := by rw [hsup]
    _ = (xSub p M H ⊓ kSub p M H).relIndex (kSub p M H) := hsecond
    _ = (pCoreOf 2 (kSub p M H)).relIndex (kSub p M H) := by
          rw [TwelveCtx.xSub_inf_kSub_eq h hKH hK hZ]
    _ = (CFSG.pCore 2 ↥(kSub p M H)).relIndex ⊤ := by
          simpa [pCoreOf] using hrelK.symm
    _ = (CFSG.pCore 2 ↥(kSub p M H)).index := Subgroup.relIndex_top_right _
    _ = Nat.card (modTwoCore (kSub p M H)) := by
          simpa [modTwoCore] using
            (Subgroup.index_eq_card (H := CFSG.pCore 2 ↥(kSub p M H)))

theorem TwelveCtx.index_sup_le_two (h : TwelveCtx G M p Q H)
    (hKH : ((kSub p M H).subgroupOf H).Normal)
    (hK : IsTwoPrimeComponentIn (kSub p M H) H)
    (hZ : center (modTwoCore (kSub p M H)) = ⊥)
    (hAut : Nat.card (MulAut (modTwoCore (kSub p M H))) ≤
      2 * Nat.card (modTwoCore (kSub p M H))) :
    ((kSub p M H ⊔ xSub p M H).subgroupOf H).index ≤ 2 := by
  let K := kSub p M H
  let X := xSub p M H
  let KH : Subgroup ↥H := K.subgroupOf H
  let XH : Subgroup ↥H := X.subgroupOf H
  let KXH : Subgroup ↥H := (K ⊔ X).subgroupOf H
  have hXHnormal : XH.Normal := xSub_subgroupOf_normal_of_kSub_normal hKH
  haveI : XH.Normal := hXHnormal
  have hker : (kbarConj hKH).ker = XH := TwelveCtx.ker_kbarConj h hKH hK hZ
  let φ : (↥H ⧸ XH) →* MulAut (modTwoCore K) :=
    QuotientGroup.lift XH (kbarConj hKH) (le_of_eq hker.symm)
  have hφinj : Function.Injective φ :=
    (QuotientGroup.injective_lift_iff (N := XH) (φ := kbarConj hKH)
      (le_of_eq hker.symm)).mpr hker.symm
  have hcard : XH.relIndex KXH = Nat.card (modTwoCore K) :=
    relIndex_sup_eq_card_modTwoCore h hKH hK hZ
  have hXleKX : XH ≤ KXH := Subgroup.subgroupOf_mono H le_sup_right
  have hindex : XH.index ≤ 2 * XH.relIndex KXH := by
    calc XH.index = Nat.card (↥H ⧸ XH) := Subgroup.index_eq_card (G := ↥H) (H := XH)
      _ ≤ Nat.card (MulAut (modTwoCore K)) := Nat.card_le_card_of_injective φ hφinj
      _ ≤ 2 * Nat.card (modTwoCore K) := hAut
      _ = 2 * XH.relIndex KXH := by rw [hcard]
  have hmul : XH.relIndex KXH * KXH.index = XH.index := Subgroup.relIndex_mul_index hXleKX
  haveI : Nonempty (modTwoCore K) := ⟨QuotientGroup.mk (1 : ↥K)⟩
  have hrelpos : 0 < XH.relIndex KXH := by
    rw [hcard]
    exact Nat.card_pos
  have hineq : XH.relIndex KXH * KXH.index ≤ XH.relIndex KXH * 2 := by
    rw [hmul]
    simpa [Nat.mul_comm] using hindex
  exact Nat.le_of_mul_le_mul_left hineq hrelpos

theorem card_mulAut_le_two_mul_of_kbarType {Y : Type} [Group Y] [Finite Y]
    (h : LieModel Y .PSp 2 3 1 ∨ Nonempty (Y ≃* alternatingGroup (Fin 9))) :
    Nat.card (MulAut Y) ≤ 2 * Nat.card Y := by
  rcases h with hpsp | hne
  · obtain ⟨ePSp⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.psp43_equiv_of_lieModel hpsp
    have hcard : Nat.card Y = 25920 := by
      rw [Nat.card_congr ePSp.toEquiv,
        CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.card_PSp43]
    calc Nat.card (MulAut Y) =
        Nat.card (MulAut CFSG.GH74.Exceptional.PSp43) :=
          Nat.card_congr (MulAut.congr ePSp).toEquiv
      _ ≤ 51840 :=
          CFSG.Quasithin.SimsF5.card_mulAut_of_mulEquiv_PSp43 (MulEquiv.refl _)
      _ = 2 * Nat.card Y := by rw [hcard]
  · obtain ⟨e⟩ := hne
    have hconj : Nat.card (MulAut (alternatingGroup (Fin 9))) =
        Nat.card (Equiv.Perm (Fin 9)) :=
      Nat.card_congr (MulEquiv.ofBijective
        (MulAut.conjNormal (H := alternatingGroup (Fin 9)))
        (aut_alternatingGroup_bijective_conj 9 (by norm_num) (by norm_num))).symm.toEquiv
    refine le_of_eq ?_
    calc Nat.card (MulAut Y) = Nat.card (MulAut (alternatingGroup (Fin 9))) :=
            Nat.card_congr (MulAut.congr e).toEquiv
      _ = Nat.card (Equiv.Perm (Fin 9)) := hconj
      _ = 2 * Nat.card (alternatingGroup (Fin 9)) :=
          (two_mul_nat_card_alternatingGroup (α := Fin 9)).symm
      _ = 2 * Nat.card Y := by rw [Nat.card_congr e.toEquiv]

theorem center_eq_bot_of_kbarType {Y : Type} [Group Y] [Finite Y]
    (h : LieModel Y .PSp 2 3 1 ∨ Nonempty (Y ≃* alternatingGroup (Fin 9))) :
    center Y = ⊥ := by
  rcases h with hpsp | hne
  · obtain ⟨ePSp⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.psp43_equiv_of_lieModel hpsp
    have hmap : (Subgroup.center Y).map (ePSp : Y →* CFSG.GH74.Exceptional.PSp43) = ⊥ := by
      rw [Subgroup.map_center_eq,
        CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.center_PSp43_eq_bot]
    exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center Y) ePSp.injective).mp hmap
  · obtain ⟨e⟩ := hne
    have hmap : (Subgroup.center Y).map (e : Y →* alternatingGroup (Fin 9)) = ⊥ := by
      rw [Subgroup.map_center_eq, alternatingGroup.center_eq_bot (by norm_num)]
    exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center Y) e.injective).mp hmap

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end

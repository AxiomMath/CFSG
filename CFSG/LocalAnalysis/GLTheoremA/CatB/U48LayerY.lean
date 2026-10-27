module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Blocks
public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U48

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB TauCeti
open CFSG.LocalAnalysis.GLTheoremA.CatB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48 (SU4 μ3)
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K card_K)

noncomputable section

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem restrictCent_mem (φ : ↥L →* SU4) {y : G} (hyL : y ∈ L) {z : SU4} (hz : φ ⟨y, hyL⟩ = z)
    (x : ↥(L ⊓ cx y)) :
    φ (Subgroup.inclusion (inf_le_left : L ⊓ cx y ≤ L) x) ∈
      Subgroup.centralizer ({z} : Set SU4) := by
  subst hz
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h : (x : G) * y = y * (x : G) := Subgroup.mem_centralizer_singleton_iff.1 x.2.2
  rw [← map_mul, ← map_mul]
  exact congrArg φ (Subtype.ext h)

@[expose] def restrictCent (φ : ↥L →* SU4) {y : G} (hyL : y ∈ L) {z : SU4}
    (hz : φ ⟨y, hyL⟩ = z) : ↥(L ⊓ cx y) →* ↥(Subgroup.centralizer ({z} : Set SU4)) :=
  (φ.comp (Subgroup.inclusion (inf_le_left : L ⊓ cx y ≤ L))).codRestrict _
    (restrictCent_mem φ hyL hz)

theorem restrictCent_surjective (φ : ↥L →* SU4) (hφ : Function.Surjective φ)
    (hker : ¬ 3 ∣ Nat.card φ.ker) {y : G} (hyL : y ∈ L) (hy3 : y ^ 3 = 1) {z : SU4}
    (hz : φ ⟨y, hyL⟩ = z) : Function.Surjective (restrictCent φ hyL hz) := by
  subst hz
  rintro ⟨c, hc⟩
  have hy3' : (⟨y, hyL⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
  have hcm : c * φ ⟨y, hyL⟩ = φ ⟨y, hyL⟩ * c := Subgroup.mem_centralizer_singleton_iff.1 hc
  obtain ⟨l, hlz, hlc⟩ := exists_mem_centralizer_lift Nat.prime_three φ hker hy3'
    (MonoidHom.mem_range.2 (hφ c)) hcm
  have hl : (l : G) ∈ L ⊓ cx y := by
    refine ⟨l.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have := congrArg Subtype.val hlz
    exact this
  exact ⟨⟨l, hl⟩, Subtype.ext hlc⟩

theorem restrictCent_ker (φ : ↥L →* SU4) (hker : ¬ 3 ∣ Nat.card φ.ker) {y : G} (hyL : y ∈ L)
    {z : SU4} (hz : φ ⟨y, hyL⟩ = z) : ¬ 3 ∣ Nat.card (restrictCent φ hyL hz).ker := by
  intro h3
  apply hker
  refine h3.trans ?_
  rw [← Subgroup.card_map_of_injective (K := (restrictCent φ hyL hz).ker)
    (Subgroup.subtype_injective _), ← Subgroup.card_map_of_injective (K := φ.ker)
    (Subgroup.subtype_injective _)]
  apply Subgroup.card_dvd_of_le
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨Subgroup.inclusion (inf_le_left : L ⊓ cx y ≤ L) x, ?_, rfl⟩
  have := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
  exact MonoidHom.mem_ker.2 this

def pp8 : PrimePower := ⟨2, 3, Nat.prime_two, by norm_num⟩

theorem valid_twistedA_two_eight : (LieTypeIndex.twistedA 2 pp8).Valid := by
  rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
    LieTypeIndex.isDuplicateRepresentative_iff]
  simp [pp8]

theorem catalogIs_u3eight_of_statedProj {X : Type} [Group X] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 64) (e : X ≃* StatedProj (StatedSU 3 (2 ^ 3) K)) :
    catalogIs X S9.isU3eight := by
  have hc2 : ValidLieTypeIndex.characteristic ⟨.twistedA 2 pp8, valid_twistedA_two_eight⟩ = 2 :=
    LieTypeIndex.characteristic_twistedA 2 pp8
  have hf2 : ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 pp8, valid_twistedA_two_eight⟩ = 3 :=
    LieTypeIndex.fieldExponent_twistedA 2 pp8
  have eq := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 pp8 valid_twistedA_two_eight
  have hq : ValidLieTypeIndex.characteristic ⟨.twistedA 2 pp8, valid_twistedA_two_eight⟩ ^
      ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 pp8, valid_twistedA_two_eight⟩ = 2 ^ 3 := by
    rw [hc2, hf2]
  rw [← hq] at e
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (GaloisField (ValidLieTypeIndex.characteristic
    ⟨.twistedA 2 pp8, valid_twistedA_two_eight⟩)
      (2 * ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 pp8, valid_twistedA_two_eight⟩)) :=
    Fintype.ofFinite _
  have hc : Fintype.card K = Fintype.card (GaloisField (ValidLieTypeIndex.characteristic
      ⟨.twistedA 2 pp8, valid_twistedA_two_eight⟩)
        (2 * ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 pp8, valid_twistedA_two_eight⟩)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card _ _ (by rw [hf2]; norm_num), hc2, hf2]
    norm_num
  refine ⟨.lie ⟨.twistedA 2 pp8, valid_twistedA_two_eight⟩, ?_, ⟨?_⟩⟩
  · show pp8.card = 8
    rw [PrimePower.card_def]
    norm_num [pp8]
  · exact (e.trans (CFSG.Open.StatedSUFieldChange.statedProjSUEquiv
      (FiniteField.ringEquivOfCardEq hc) 3 _)).trans eq.symm

theorem catalogIs_psimple_of_pquot {J : Subgroup G}
    (ε : PQuot 3 J ≃* CFSG.ClassicalInvolution.Phan.Su K 2 3 3) :
    catalogIs (PSimple 3 J) S9.isU3eight := by
  have hK : Nat.card K = 64 := by rw [card_K]; norm_num
  refine catalogIs_u3eight_of_statedProj hK ?_
  exact (QuotientGroup.congr _ _ ε (CFSG.LieType.Universal.Unitary.map_center_mulEquiv ε)).trans
    (CFSG.GH74.L5U5.centerQuotientEquivStatedProjSu (K := K) (p := 2) (f := 3) card_K (d := 3)
      le_rfl (by decide))

theorem layerY (φ : ↥L →* SU4) (hφ : Function.Surjective φ) (hker : ¬ 3 ∣ Nat.card φ.ker)
    {t : μ3} (ht : (t : Kˣ) ≠ 1) {y : G} (hyL : y ∈ L) (hy3 : y ^ 3 = 1)
    (hφy : φ ⟨y, hyL⟩ = yStd t) :
    ∃ J : Subgroup G, GLAPComponent 3 (L ⊓ cx y) J ∧ GLAPLayer 3 (L ⊓ cx y) = J ∧
      (J.subgroupOf L).map φ = Jblk ∧
        Nonempty (PQuot 3 J ≃* CFSG.ClassicalInvolution.Phan.Su K 2 3 3) := by
  obtain ⟨J, hJ, hJl, himg, ⟨ε⟩⟩ := layer_of_surj (restrictCent φ hyL hφy)
    (restrictCent_surjective φ hφ hker hyL hy3 hφy) (restrictCent_ker φ hker hyL hφy)
    (pPrimeCore_Cstd ht)
    (rho ht).ker (isQuasisimple_ker ht) (perfect_le_ker ht)
  refine ⟨J, hJ, hJl, ?_, ⟨ε.trans (kerEquiv ht)⟩⟩
  have hJle : J ≤ L ⊓ cx y := hJ.1
  rw [← map_ker_rho ht, ← himg]
  ext b
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hjX : (j : G) ∈ L ⊓ cx y := hJle (Subgroup.mem_subgroupOf.1 hj)
    refine ⟨restrictCent φ hyL hφy ⟨j.1, hjX⟩, ⟨⟨j.1, hjX⟩, ?_, rfl⟩, rfl⟩
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hj)
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨Subgroup.inclusion (inf_le_left : L ⊓ cx y ≤ L) x, ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hx)

end

end CFSG.LocalAnalysis.GLTheoremA.CatB.U48

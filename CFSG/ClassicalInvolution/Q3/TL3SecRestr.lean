module

public import CFSG.ClassicalInvolution.Q3.TL3SecOdd
public import CFSG.ClassicalInvolution.Q3.TL3TopRestrict
public import CFSG.ClassicalInvolution.AschTight.S19BEnd

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem TightDatum.ofSylow (hd : TightDatum R S t) (S' : Sylow 2 R) : TightDatum R S' t := by
  classical
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq R S S'
  refine ⟨?_, ?_, hd.order, hd.cent, hd.normal, hd.twoGroup⟩
  · obtain ⟨r, hr, ⟨e⟩⟩ := hd.quat
    exact ⟨r, hr, ⟨(Sylow.equiv S' S).trans e⟩⟩
  ·
    obtain ⟨s, hs, hst⟩ := hd.mem
    have hsR : (s : Y) = t := hst
    rw [← hg]
    refine ⟨g * s * g⁻¹, ?_, ?_⟩
    · rw [Sylow.coe_subgroup_smul]
      exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨s, hs, by
        simp [MulAut.smul_def, MulAut.conj_apply]⟩
    · show ((g : Y) * (s : Y) * (g : Y)⁻¹) = t
      rw [hsR]
      have hgt : (g : Y) * t = t * (g : Y) :=
        Subgroup.mem_centralizer_singleton_iff.mp (hd.cent g.2)
      calc (g : Y) * t * (g : Y)⁻¹ = t * (g : Y) * (g : Y)⁻¹ := by rw [hgt]
        _ = t := by group

theorem TightDatum.exists_sylow_le_centralizer (hd : TightDatum R S t) {B : Subgroup Y}
    (hB2 : IsPGroup 2 ↥B) (hBR : B ≤ centralizerModOdd ⊤ R) :
    ∃ S' : Sylow 2 R, (S' : Subgroup R).map R.subtype ≤ Subgroup.centralizer (B : Set Y) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : OddByQuat R ((S : Subgroup R).map R.subtype) t :=
    OddByQuat.of_quaternion S hd.quat hd.mem hd.order hd.cent hd.normal hd.twoGroup
  set H : Subgroup Y := R ⊓ Subgroup.centralizer (B : Set Y) with hH
  set φ : ↥H →* ↥R ⧸ classicalInvolutionOddCore ↥R :=
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥R)).comp
      (Subgroup.inclusion (inf_le_left : H ≤ R)) with hφ
  have hsurj : Function.Surjective φ := S19B.surjective_mk_inf_centralizer hB2 hBR
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥H))
  have hP2 : IsPGroup 2 ↥((P : Subgroup H).map H.subtype) := P.isPGroup'.map _
  have hPR : (P : Subgroup H).map H.subtype ≤ R :=
    (Subgroup.map_subtype_le _).trans inf_le_left
  have hcardQ : Nat.card (↥R ⧸ classicalInvolutionOddCore ↥R) =
      Nat.card ↥((S : Subgroup R).map R.subtype) :=
    (Nat.card_congr (Equiv.ofBijective _ hO.bijective_restrict)).symm
  have hPtop : (P : Subgroup H).map φ = ⊤ := by
    have h2 : IsPGroup 2 (↥R ⧸ classicalInvolutionOddCore ↥R) := hd.twoGroup
    have := (P.mapSurjective hsurj).is_maximal' (h2.to_subgroup ⊤) le_top
    rw [Sylow.coe_mapSurjective] at this
    exact this.symm
  have hle : Nat.card ↥((S : Subgroup R).map R.subtype) ≤
      Nat.card ↥((P : Subgroup H).map H.subtype) := by
    rw [← hcardQ, Subgroup.card_map_of_injective H.subtype_injective]
    calc Nat.card (↥R ⧸ classicalInvolutionOddCore ↥R)
        = Nat.card ↥((P : Subgroup H).map φ) := by rw [hPtop, Subgroup.card_top]
      _ ≤ Nat.card ↥(P : Subgroup H) :=
          Nat.card_le_card_of_surjective _ (φ.subgroupMap_surjective (P : Subgroup H))
  have hsyl := (isSylow2In_map_sylow R S).of_natCard_le hP2 hPR hle
  set P' : Subgroup Y := (P : Subgroup H).map H.subtype with hP'
  let S' : Sylow 2 ↥R :=
    { toSubgroup := P'.subgroupOf R
      isPGroup' := hP2.comap_subtype
      is_maximal' := by
        intro Q hQ hle'
        have hVQ : P' ≤ Q.map R.subtype := by
          rw [← Subgroup.map_subgroupOf_eq_of_le hPR]
          exact Subgroup.map_mono hle'
        have := hsyl.2.2 (Q.map R.subtype) (Subgroup.map_subtype_le _) (hQ.map _) hVQ
        rw [← Subgroup.comap_map_eq_self_of_injective R.subtype_injective Q, this]
        rfl }
  refine ⟨S', ?_⟩
  show (P'.subgroupOf R).map R.subtype ≤ _
  rw [Subgroup.map_subgroupOf_eq_of_le hPR]
  exact (Subgroup.map_subtype_le _).trans inf_le_right

theorem TightDatum.restrictCentralizer (hd : TightDatum R S t) {B : Subgroup Y}
    (hB2 : IsPGroup 2 ↥B) (hBR : B ≤ centralizerModOdd ⊤ R) :
    ∃ (ht : t ∈ Subgroup.centralizer (B : Set Y))
      (S'' : Sylow 2 ↥(R.subgroupOf (Subgroup.centralizer (B : Set Y)))),
      TightDatum (R.subgroupOf (Subgroup.centralizer (B : Set Y))) S'' ⟨t, ht⟩ ∧
        Nonempty ((S'' : Subgroup ↥(R.subgroupOf (Subgroup.centralizer (B : Set Y)))) ≃*
          (S : Subgroup R)) := by
  obtain ⟨S', hS'⟩ := hd.exists_sylow_le_centralizer hB2 hBR
  have hd' := hd.ofSylow S'
  obtain ⟨S'', hd'', ⟨e⟩⟩ := hd'.restrict hS'
  exact ⟨hS' hd'.mem, S'', hd'', ⟨e.trans (Sylow.equiv S' S)⟩⟩

theorem TightDatum.exists_cls_subnormalClosure (hd : TightDatum R S t)
    (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)) :
    ∃ (ht : t ∈ subnormalClosure (tightCore R))
      (S' : Sylow 2 ↥(R.subgroupOf (subnormalClosure (tightCore R)))),
      TightDatum (R.subgroupOf (subnormalClosure (tightCore R))) S' ⟨t, ht⟩ ∧
      TightSelfGen (R.subgroupOf (subnormalClosure (tightCore R))) ∧
      TightCls (↥(subnormalClosure (tightCore R)) ⧸
          classicalInvolutionOddCore ↥(subnormalClosure (tightCore R)))
        ((R.subgroupOf (subnormalClosure (tightCore R))).map
          (QuotientGroup.mk' (classicalInvolutionOddCore ↥(subnormalClosure (tightCore R)))))
        (TwistQ.sylowMap (classicalInvolutionOddCore ↥(subnormalClosure (tightCore R))) S')
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(subnormalClosure (tightCore R)))
          ⟨t, ht⟩) := by
  set H : Subgroup Y := subnormalClosure (tightCore R) with hH
  have hKH : tightCore R ≤ H := le_subnormalClosure _
  have hSK : (S : Subgroup R).map R.subtype ≤ tightCore R := hd.sylow_core.1
  have hSH : (S : Subgroup R).map R.subtype ≤ H := hSK.trans hKH
  obtain ⟨S', hd', ⟨eS⟩⟩ := hd.restrict hSH
  have hgen : TightSelfGen (R.subgroupOf H) := by
    unfold TightSelfGen
    rw [tightCore_subgroupOf hKH]
    exact iSup_conjSub_eq_top_of_subnormalClosure (subnormalClosure_subgroupOf_subnormalClosure _)
  obtain ⟨e⟩ := hq8
  exact ⟨hSH hd.mem, S', hd', hgen, OddQ.cls hd' hgen ⟨eS.trans e⟩⟩

end CFSG.ClassicalInvolution.Q3

module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.Construct
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.A7Radical
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.OddDescent
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.OddLift

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

theorem mem_normalizer_subgroupOf {B : Type*} [Group B] {Λ P : Subgroup B} (hPΛ : P ≤ Λ)
    (t : ↥Λ) : t ∈ Subgroup.normalizer ((P.subgroupOf Λ : Subgroup ↥Λ) : Set ↥Λ) ↔
      (t : B) ∈ Subgroup.normalizer (P : Set B) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h b
    constructor
    · intro hb
      exact (h ⟨b, hPΛ hb⟩).1 hb
    · intro hb
      have hbΛ : b ∈ Λ := by
        have h1 : (t : B)⁻¹ * ((t : B) * b * (t : B)⁻¹) * (t : B) ∈ Λ :=
          Λ.mul_mem (Λ.mul_mem (Λ.inv_mem t.2) (hPΛ hb)) t.2
        simpa [mul_assoc] using h1
      exact (h ⟨b, hbΛ⟩).2 hb
  · intro h q
    exact h q

theorem isTwoRadicalIn_top_subgroupOf {B : Type*} [Group B] {Λ P : Subgroup B}
    (hP : IsTwoRadicalIn Λ P) : IsTwoRadicalIn ⊤ (P.subgroupOf Λ) := by
  obtain ⟨hPΛ, hne, hP2, hmax⟩ := isTwoRadicalIn_iff.1 hP
  refine isTwoRadicalIn_iff.2 ⟨le_top, ?_, ?_, ?_⟩
  · intro h
    apply hne
    rw [← Subgroup.map_subgroupOf_eq_of_le hPΛ, h, Subgroup.map_bot]
  · exact hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPΛ).symm
  · intro T' hT' hT'2 hTn
    have hT'N : ∀ t ∈ T', (t : B) ∈ Subgroup.normalizer (P : Set B) := fun t ht =>
      (mem_normalizer_subgroupOf hPΛ t).1 (hT' ht).2
    set T : Subgroup B := T'.map Λ.subtype with hT
    have hTle : T ≤ Λ ⊓ Subgroup.normalizer (P : Set B) := by
      rintro _ ⟨t, ht, rfl⟩
      exact ⟨t.2, hT'N t ht⟩
    have hnormal : (T.subgroupOf (Λ ⊓ Subgroup.normalizer (P : Set B))).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hTle]
      rintro _ k ⟨t, ht, rfl⟩ hk
      have hk' : (⟨k, hk.1⟩ : ↥Λ) ∈ Subgroup.normalizer ((P.subgroupOf Λ : Subgroup ↥Λ) : Set ↥Λ) :=
        (mem_normalizer_subgroupOf hPΛ ⟨k, hk.1⟩).2 hk.2
      have := (Subgroup.normal_subgroupOf_iff hT').1 hTn t ⟨k, hk.1⟩ ht ⟨trivial, hk'⟩
      exact ⟨_, this, rfl⟩
    have hTP := hmax T hTle (hT'2.map _) hnormal
    intro t ht
    exact hTP ⟨t, ht, rfl⟩

theorem isQuasisimple_of_mulEquiv_aux {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (h : CFSG.Open.IsQuasisimple G) : CFSG.Open.IsQuasisimple G' :=
  h.of_mulEquiv e.symm

theorem a7PerfectSylow_top {B : Type} [Group B] [Finite B] (hq : CFSG.Open.IsQuasisimple B)
    (hodd : Odd (Nat.card (Subgroup.center B)))
    (e : B ⧸ Subgroup.center B ≃* alternatingGroup (Fin 7)) {P : Subgroup B}
    (hP : IsTwoRadicalIn ⊤ P) :
    ∃ H : Subgroup B, ⁅H, H⁆ = H ∧ P ≤ H ∧ ¬ 2 ∣ (P.subgroupOf H).index ∧
      Odd (Nat.card (Subgroup.center ↥H)) ∧ CFSG.Open.IsQuasisimple ↥H := by
  let φ : B →* A7 := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center B))
  have hker : φ.ker = Subgroup.center B := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff e e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hsurj : Function.Surjective φ :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hoddk : Odd (Nat.card φ.ker) := by rw [hker]; exact hodd
  have hA7 : IsSimpleGroup A7 := by
    have : IsSimpleGroup (B ⧸ Subgroup.center B) := hq.2
    exact e.symm.isSimpleGroup
  have hrad := isTwoRadicalIn_map_of_odd φ hker.le hoddk hsurj hP
  obtain ⟨Ht, hs, hnon, hle, hidx⟩ := a7Good_of_radical hA7 hrad
  exact exists_lift φ hker.le hoddk hsurj (isTwoRadicalIn_iff.1 hP).2.2.1 hs hnon hle hidx

theorem a7PerfectSylow : A7PerfectSylow := by
  intro B _ _ Λ hq hodd ⟨e⟩ P hP
  have hPΛ : P ≤ Λ := hP.1
  have hP2 : IsPGroup 2 ↥P := (isTwoRadicalIn_iff.1 hP).2.2.1
  obtain ⟨H', hperf, hle, hidx, hZ, hq'⟩ :=
    a7PerfectSylow_top hq hodd e (isTwoRadicalIn_top_subgroupOf hP)
  have hf : Function.Injective Λ.subtype := Λ.subtype_injective
  have hPeq : (P.subgroupOf Λ).map Λ.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPΛ
  have hPH : P ≤ H'.map Λ.subtype := hPeq ▸ Subgroup.map_mono hle
  have hidx' : ¬ 2 ∣ (P.subgroupOf (H'.map Λ.subtype)).index := by
    have h1 := Subgroup.relIndex_map_map_of_injective (P.subgroupOf Λ) H' hf
    rw [hPeq] at h1
    unfold Subgroup.relIndex at h1
    rw [h1]
    exact hidx
  have hequiv : ↥H' ≃* ↥(H'.map Λ.subtype) := Subgroup.equivMapOfInjective H' Λ.subtype hf
  refine ⟨H'.map Λ.subtype, Subgroup.map_subtype_le H', ?_, hPH, hidx', ?_, ?_, ?_⟩
  · rw [← Subgroup.map_commutator, hperf]
  · intro T hT hT2
    refine le_of_isPGroup_of_odd_index hPH hP2 ?_ hT hT2
    have hsub : P ≤ H'.map Λ.subtype ⊓ Subgroup.normalizer (P : Set B) :=
      le_inf hPH Subgroup.le_normalizer
    have h1 := Subgroup.relIndex_mul_relIndex (H := P)
      (K := H'.map Λ.subtype ⊓ Subgroup.normalizer (P : Set B)) (L := H'.map Λ.subtype) hsub
      inf_le_left
    intro h2
    apply hidx'
    have : (P.subgroupOf (H'.map Λ.subtype ⊓ Subgroup.normalizer (P : Set B))).index ∣
        (P.subgroupOf (H'.map Λ.subtype)).index := ⟨_, h1.symm⟩
    exact h2.trans this
  · rw [← Nat.card_congr (Subgroup.centerCongr hequiv).toEquiv]
    exact hZ
  · exact isQuasisimple_of_mulEquiv_aux hequiv hq'

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour

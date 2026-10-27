module

public import CFSG.ClassicalInvolution.Asc77.AscSixModCent
import CFSG.ClassicalInvolution.SmallOrth.PlusFourMain

public section

open scoped commutatorElement MatrixGroups Pointwise

namespace CFSG.ClassicalInvolution.Asc77.ExactD

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

structure TwinPair {G : Type} [Group G] (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G))
    (K K' : Subgroup G) (z : G) : Prop where
  odd : p ≠ 2
  five : 5 ≤ p ^ f
  hyp : HypOmegaMod p f Ω
  mem : K ∈ Ω
  mem' : K' ∈ Ω
  ne : K ≠ K'
  hz : IsUniqueInvolution K z
  hz' : IsUniqueInvolution K' z

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' : Subgroup G} {z : G}

theorem TwinPair.of_twinSet (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hK : K ∈ Ω) (hz : IsUniqueInvolution K z) (hK' : K' ∈ twinSet Ω K) (hne : K ≠ K') :
    TwinPair p f Ω K K' z := by
  obtain ⟨hK'Ω, z', hz'K, hz'K'⟩ := hK'
  have hzz : z' = z := hz'K.eq hz
  subst hzz
  exact ⟨hp, hq, hΩ, hK, hK'Ω, hne, hz, hz'K'⟩

theorem TwinPair.symm (d : TwinPair p f Ω K K' z) : TwinPair p f Ω K' K z :=
  ⟨d.odd, d.five, d.hyp, d.mem', d.mem, d.ne.symm, d.hz', d.hz⟩

@[expose] def oddProd (K K' : Subgroup G) : Subgroup G := oddCoreOf K ⊔ oddCoreOf K'

theorem oddProd_comm (K K' : Subgroup G) : oddProd K' K = oddProd K K' := sup_comm _ _

section Twin

namespace TwinPair

variable [Finite G] (d : TwinPair p f Ω K K' z)
include d

theorem comm_le : ⁅K, K'⁆ ≤ oddCoreOf K ⊓ oddCoreOf K' :=
  d.hyp.comm_le_oddCore_of_twin d.mem d.mem' d.ne d.hz d.hz'

theorem K_le : K ≤ Subgroup.normalizer (K' : Set G) :=
  d.hyp.le_normalizer_of_twin d.mem d.mem' d.ne d.hz d.hz'

theorem K'_le : K' ≤ Subgroup.normalizer (K : Set G) :=
  d.symm.K_le

theorem sup_le_normalizer_left : K ⊔ K' ≤ Subgroup.normalizer (K : Set G) :=
  sup_le Subgroup.le_normalizer d.K'_le

theorem sup_le_normalizer_right : K ⊔ K' ≤ Subgroup.normalizer (K' : Set G) :=
  sup_le d.K_le Subgroup.le_normalizer

theorem sup_le_normalizer_oddCore_left : K ⊔ K' ≤ Subgroup.normalizer (oddCoreOf K : Set G) :=
  fun _ hg => mem_normalizer_oddCore_of_mem_normalizer (d.sup_le_normalizer_left hg)

theorem sup_le_normalizer_oddCore_right : K ⊔ K' ≤ Subgroup.normalizer (oddCoreOf K' : Set G) :=
  fun _ hg => mem_normalizer_oddCore_of_mem_normalizer (d.sup_le_normalizer_right hg)

theorem sup_le_normalizer_oddProd : K ⊔ K' ≤ Subgroup.normalizer (oddProd K K' : Set G) :=
  fun _ hg => Subgroup.inf_normalizer_le_normalizer_sup (oddCoreOf K) (oddCoreOf K')
    ⟨d.sup_le_normalizer_oddCore_left hg, d.sup_le_normalizer_oddCore_right hg⟩

omit [Finite G] [Fact p.Prime] d in
theorem oddProd_le : oddProd K K' ≤ K ⊔ K' :=
  sup_le ((oddCoreOf_le_self K).trans le_sup_left) ((oddCoreOf_le_self K').trans le_sup_right)

theorem oddCoreOf_le_oddCoreOf_sup : oddCoreOf K ≤ oddCoreOf (K ⊔ K') :=
  Balance.le_oddCoreIn_of_normalizes ((oddCoreOf_le_self K).trans le_sup_left)
    d.sup_le_normalizer_oddCore_left (oddCoreOf_odd_natCard K)

theorem oddCoreOf_le_oddCoreOf_sup' : oddCoreOf K' ≤ oddCoreOf (K ⊔ K') :=
  Balance.le_oddCoreIn_of_normalizes ((oddCoreOf_le_self K').trans le_sup_right)
    d.sup_le_normalizer_oddCore_right (oddCoreOf_odd_natCard K')

theorem odd_oddProd : Odd (Nat.card (oddProd K K')) := by
  have hle : oddProd K K' ≤ oddCoreOf (K ⊔ K') :=
    sup_le d.oddCoreOf_le_oddCoreOf_sup d.oddCoreOf_le_oddCoreOf_sup'
  exact (oddCoreOf_odd_natCard (K ⊔ K')).of_dvd_nat (Subgroup.card_dvd_of_le hle)

omit [Finite G] in
theorem commutator_sup_eq : ⁅K ⊔ K', K ⊔ K'⁆ = K ⊔ K' := by
  have hK : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp (d.hyp.isPerfect d.mem)
  have hK' : ⁅K', K'⁆ = K' := Subgroup.isPerfect_iff.mp (d.hyp.isPerfect d.mem')
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    have hM := (K ⊔ K').mul_mem ((K ⊔ K').mul_mem ((K ⊔ K').mul_mem ha hb) ((K ⊔ K').inv_mem ha))
      ((K ⊔ K').inv_mem hb)
    simpa [commutatorElement_def] using hM
  · refine sup_le ?_ ?_
    · calc K = ⁅K, K⁆ := hK.symm
        _ ≤ ⁅K ⊔ K', K ⊔ K'⁆ := Subgroup.commutator_mono le_sup_left le_sup_left
    · calc K' = ⁅K', K'⁆ := hK'.symm
        _ ≤ ⁅K ⊔ K', K ⊔ K'⁆ := Subgroup.commutator_mono le_sup_right le_sup_right

end TwinPair

end Twin

theorem mem_center_of_commutators_central {S : Type*} [Group S] [Group.IsPerfect S] {s : S}
    (h : ∀ t : S, ⁅s, t⁆ ∈ Subgroup.center S) : s ∈ Subgroup.center S := by
  have h1 : (QuotientGroup.mk' (Subgroup.center S) s) ∈
      Subgroup.center (S ⧸ Subgroup.center S) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center S) y
    have e1 : s * t = ⁅s, t⁆ * (t * s) := by simp only [commutatorElement_def]; group
    have e2 : QuotientGroup.mk' (Subgroup.center S) ⁅s, t⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (h t)
    have h3 : QuotientGroup.mk' (Subgroup.center S) (s * t) =
        QuotientGroup.mk' (Subgroup.center S) (t * s) := by
      rw [e1, map_mul, e2, one_mul]
    calc QuotientGroup.mk' (Subgroup.center S) t * QuotientGroup.mk' (Subgroup.center S) s
        = QuotientGroup.mk' (Subgroup.center S) (t * s) := (map_mul _ _ _).symm
      _ = QuotientGroup.mk' (Subgroup.center S) (s * t) := h3.symm
      _ = QuotientGroup.mk' (Subgroup.center S) s * QuotientGroup.mk' (Subgroup.center S) t :=
        map_mul _ _ _
  rw [Group.IsPerfect.center_quotient_center_eq_bot S, Subgroup.mem_bot] at h1
  exact (QuotientGroup.eq_one_iff s).mp h1

section Chart

namespace TwinPair

variable [Finite G] (d : TwinPair p f Ω K K' z)
include d

omit [Finite G] in
theorem isQuasisimple_sl2 : CFSG.Open.IsQuasisimple SL(2, GaloisField p f) := by
  have hf : f ≠ 0 := by
    rintro rfl
    simpa using d.five
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [GaloisField.card p f hf]
    exact (by norm_num : 4 ≤ 5).trans d.five
  exact CFSG.ClassicalGroups.Orthogonal.Small.isQuasisimple_specialLinearGroup_two h4

theorem chart_z {φ : ↥K →* SL(2, GaloisField p f)}
    (hφk : ∀ x : ↥K, φ x = 1 ↔ x ∈ classicalInvolutionOddCore ↥K) :
    φ ⟨z, d.hz.mem⟩ = -1 := by
  have hodd := odd_natCard_galoisField d.odd d.five
  have hoddO := oddCoreOf_odd_natCard K
  have hz2 := isPGroup_zpowers_of_mul_self_eq_one d.hz.sq d.hz.ne_one
  have hzN : (⟨z, d.hz.mem⟩ : ↥K) ∉ classicalInvolutionOddCore ↥K := fun hN =>
    d.hz.ne_one
      (eq_one_of_isPGroup_of_mem_odd hoddO (mem_oddCoreOf_iff.mpr ⟨d.hz.mem, hN⟩) hz2)
  have h1 : φ ⟨z, d.hz.mem⟩ ≠ 1 := fun h => hzN ((hφk _).mp h)
  have h2 : φ ⟨z, d.hz.mem⟩ * φ ⟨z, d.hz.mem⟩ = 1 := by
    rw [← map_mul]
    have : (⟨z, d.hz.mem⟩ : ↥K) * ⟨z, d.hz.mem⟩ = 1 := Subtype.ext d.hz.sq
    rw [this, map_one]
  exact (sl2_orderOf_eq_two_iff hodd _).mp (orderOf_eq_prime (by rw [pow_two]; exact h2) h1)

theorem mem_oddCore_or_mul_of_chart_central {φ : ↥K →* SL(2, GaloisField p f)}
    (hφk : ∀ x : ↥K, φ x = 1 ↔ x ∈ classicalInvolutionOddCore ↥K) {w : G} (hw : w ∈ K)
    (hc : φ ⟨w, hw⟩ ∈ Subgroup.center SL(2, GaloisField p f)) :
    w ∈ oddCoreOf K ∨ w * z ∈ oddCoreOf K := by
  rcases (mem_center_sl2_iff _).mp hc with h | h
  · left
    exact mem_oddCoreOf_iff.mpr ⟨hw, (hφk _).mp h⟩
  · right
    have hwz : (⟨w * z, K.mul_mem hw d.hz.mem⟩ : ↥K) ∈ classicalInvolutionOddCore ↥K := by
      rw [← hφk, show (⟨w * z, K.mul_mem hw d.hz.mem⟩ : ↥K) = ⟨w, hw⟩ * ⟨z, d.hz.mem⟩ from rfl,
        map_mul, h, d.chart_z hφk]
      simp
    exact mem_oddCoreOf_iff.mpr ⟨K.mul_mem hw d.hz.mem, hwz⟩

omit [Finite G] in
theorem K_le_or_chart_central {φ : ↥K →* SL(2, GaloisField p f)} (hφs : Function.Surjective φ)
    (hφk : ∀ x : ↥K, φ x = 1 ↔ x ∈ classicalInvolutionOddCore ↥K) {T : Subgroup G}
    (hTK : T ≤ K) (hKT : K ≤ Subgroup.normalizer (T : Set G)) (hNT : oddCoreOf K ≤ T) :
    K ≤ T ∨ ∀ (t : G) (ht : t ∈ T), φ ⟨t, hTK ht⟩ ∈ Subgroup.center SL(2, GaloisField p f) := by
  classical
  have hQ := d.isQuasisimple_sl2
  have hT'n : (T.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hTK).mpr hKT
  have hHn : ((T.subgroupOf K).map φ).Normal := Subgroup.Normal.map hT'n φ hφs
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hQ
      ((T.subgroupOf K).map φ) with hle | htop
  · right
    intro t ht
    exact hle ⟨⟨t, hTK ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  · left
    intro k hk
    have hmem : φ ⟨k, hk⟩ ∈ (T.subgroupOf K).map φ := htop ▸ Subgroup.mem_top _
    obtain ⟨t₀, ht₀, ht₀φ⟩ := hmem
    have hker : t₀⁻¹ * ⟨k, hk⟩ ∈ classicalInvolutionOddCore ↥K := by
      rw [← hφk, map_mul, map_inv, ht₀φ]
      simp
    have hN : ((t₀⁻¹ * ⟨k, hk⟩ : ↥K) : G) ∈ oddCoreOf K :=
      mem_oddCoreOf_iff.mpr ⟨(t₀⁻¹ * ⟨k, hk⟩).2, hker⟩
    have h1 : (t₀ : G) ∈ T := Subgroup.mem_subgroupOf.mp ht₀
    have h2 : k = (t₀ : G) * ((t₀⁻¹ * ⟨k, hk⟩ : ↥K) : G) := by simp
    rw [h2]
    exact T.mul_mem h1 (hNT hN)

end TwinPair

end Chart

end CFSG.ClassicalInvolution.Asc77.ExactD

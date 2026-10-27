module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveLeCartanLift
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveLeCartanCoprime
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.AssemblyAll
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerComponentDvd
import CFSG.HardMathSupport.Malle.E27Lie.Cross.MapPerfect

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe

open CFSG.Open CFSG.AGLEmbedding CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.RichardWeiss.Coordinator CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree
  Subgroup
open scoped commutatorElement


theorem exists_component_of_perfect {A : Type} [Group A] [Finite A] {Y P : Subgroup A} {β : A}
    (hY : Open.IsQuasisimple ↥Y) {d : TauCeti.ValidLieTypeIndex} (hd : IsClassicalOrG2Index d.1)
    (e : ↥Y ⧸ center ↥Y ≃* (TauCeti.CFSGIndex.lie d).Group) (hPY : P ≤ Y)
    (hβ3 : orderOf β = 3) (hβY : β ∈ normalizer (Y : Set A))
    (hβP : β ∈ normalizer (P : Set A)) (hW : ParabComm.WCent P β)
    (hodd : ¬ 2 ∣ (wSup (↥P ⧸ CFSG.pCore 2 ↥P)).index)
    (hnc : ¬ ∀ y ∈ Y, β * y = y * β) {J : Subgroup A} (hJP : J ≤ P) (hJ : ⁅J, J⁆ = J)
    (hJ3 : 3 ∣ Nat.card J) :
    ∃ D : Subgroup A, Open.IsComponentOf D (Y ⊓ centralizer ({β} : Set A)) ∧
      3 ∣ Nat.card D := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨D, hDP, hDc, hDperf, hD3⟩ :=
    exists_perfect_le_centralizer_of_perfect hβ3 hβP hW hodd hJP hJ hJ3
  have hDY : D ≤ Y := hDP.trans hPY
  have hβ3' : β ^ 3 = 1 := by
    have h := pow_orderOf_eq_one β
    rwa [hβ3] at h
  set α : MulAut ↥Y := Y.normalizerMonoidHom ⟨β, hβY⟩ with hα
  have hαc : ∀ y : ↥Y, ((α y : ↥Y) : A) = β * (y : A) * β⁻¹ := fun y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe Y ⟨β, hβY⟩ y
  have hα3 : α ^ 3 = 1 := by
    rw [hα, ← map_pow]
    have : (⟨β, hβY⟩ : normalizer (Y : Set A)) ^ 3 = 1 := Subtype.ext hβ3'
    rw [this, map_one]
  set Dt : Subgroup ↥Y := D.subgroupOf Y with hDt
  have hDtfix : Dt ≤ fixSubgroup α := by
    intro x hx
    have hxD : (x : A) ∈ D := hx
    have hxc : β * (x : A) = (x : A) * β :=
      mem_centralizer_iff.1 (hDc hxD) β (Set.mem_singleton β)
    refine mem_fixSubgroup.2 (Subtype.ext ?_)
    rw [hαc, mul_inv_eq_iff_eq_mul]
    exact hxc
  have hDtperf : ⁅Dt, Dt⁆ = Dt := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [map_commutator, hDt, subgroupOf_map_subtype, inf_eq_left.2 hDY, hDperf]
  have hDt3 : 3 ∣ Nat.card Dt := by
    rwa [hDt, Nat.card_congr (subgroupOfEquivOfLe hDY).toEquiv]
  have hᾱ3 : centerQuotientAut ↥Y α ^ 3 = 1 := by
    rw [← map_pow, hα3, map_one]
  have hᾱ1 : centerQuotientAut ↥Y α ≠ 1 := by
    intro h1
    apply hnc
    have h := mem_centralizer_of_centerQuotientAut_eq_one hY.1 hβY h1
    exact fun y hy => (mem_centralizer_iff.1 h y hy).symm
  have hchar : d.1.characteristic = 2 := by
    obtain ⟨d', hv⟩ := d
    cases d' <;> first | exact hd.elim | simpa [IsClassicalOrG2Index] using hd
  have hnab : ∃ a b : ↥Y ⧸ center ↥Y, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥Y hY
  have hPIL := LieSemisimple.lieSemisimpleCent (↥Y ⧸ center ↥Y) hY.2 hnab d ⟨e⟩ 3 Nat.prime_three
    (by norm_num) (by rw [hchar]; norm_num) (centerQuotientAut ↥Y α) hᾱ3 hᾱ1
  set π : ↥Y →* ↥Y ⧸ center ↥Y := QuotientGroup.mk' (center ↥Y) with hπ
  have hDbfix : Dt.map π ≤ fixSubgroup (centerQuotientAut ↥Y α) := by
    rintro _ ⟨x, hx, rfl⟩
    have h := mem_fixSubgroup.1 (hDtfix hx)
    show π (α x) = π x
    rw [h]
  have hDbperf : ⁅Dt.map π, Dt.map π⁆ = Dt.map π := by
    rw [← map_commutator, hDtperf]
  have hlayer := hPIL (Dt.map π) hDbfix hDbperf
  have h3 : 3 ∣ Nat.card (Dt.map π) :=
    CFSG.HardMathSupport.Malle.E27Lie.three_dvd_card_map_of_perfect π
      (by rw [hπ, QuotientGroup.ker_mk']) hDtperf hDt3
  have h3L : 3 ∣ Nat.card (GLALayer (fixSubgroup (centerQuotientAut ↥Y α))) :=
    h3.trans (Subgroup.card_dvd_of_le hlayer)
  obtain ⟨Kb, hKb, hKb3⟩ := CFSG.exists_isComponentOf_dvd_card_of_dvd_card_glaLayer
    Nat.prime_three h3L
  obtain ⟨K, hK, hKmap⟩ := exists_isComponentOf_fixSubgroup_of_map α hKb
  have hK3 : 3 ∣ Nat.card K := by
    refine hKb3.trans ?_
    rw [← hKmap]
    exact Subgroup.card_map_dvd K π
  have hfixmap : (fixSubgroup α).map Y.subtype = Y ⊓ centralizer ({β} : Set A) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h := congrArg Subtype.val (mem_fixSubgroup.1 hy)
      rw [hαc, mul_inv_eq_iff_eq_mul] at h
      exact ⟨y.2, mem_centralizer_iff.2 fun g hg => by
        rw [Set.mem_singleton_iff] at hg
        subst hg
        exact h⟩
    · rintro ⟨hxY, hxc⟩
      refine ⟨⟨x, hxY⟩, mem_fixSubgroup.2 (Subtype.ext ?_), rfl⟩
      rw [hαc, mul_inv_eq_iff_eq_mul]
      exact mem_centralizer_iff.1 hxc β (Set.mem_singleton β)
  obtain ⟨hKF, hKsub, hKq⟩ := hK
  refine ⟨K.map Y.subtype, ?_, ?_⟩
  · rw [← hfixmap]
    exact ⟨Subgroup.map_mono hKF, hKsub.map Y.subtype,
      Open.IsQuasisimple.of_mulEquiv
        (Subgroup.equivMapOfInjective K Y.subtype Y.subtype_injective).symm hKq⟩
  · rwa [Subgroup.card_map_of_injective Y.subtype_injective]

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe

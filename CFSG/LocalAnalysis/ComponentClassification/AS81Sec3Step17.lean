module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step17
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3G24Fix
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2TorusConj
public import CFSG.LocalAnalysis.ComponentClassification.AS81Reduce
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionFitting
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionMoved
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Containment
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveComponents
public import CFSG.LocalAnalysis.ComponentClassification.BlockFixedFactorSylowReduction
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.FittingNilpotence
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.Blueprint.NativeSporadic

@[expose] def Step17G24Odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A A₁ R : Subgroup G) (g : G) (E F : Subgroup G) (x : G),
    Sec3Setting G A A₁ R g E F x → ∀ X ∈ oddNStar E,
      IsSylowOf 3 (X ⊓ A) (A ⊓ centralizer ((E ⊓ A : Subgroup G) : Set G)) ∧
      X = (X ⊓ A) ⊔ AS76b.oddCoreIn (centralizer (A : Set G))

section Model

@[expose] def G24Hyp : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 4 →
    ∀ H : Subgroup (ModGL .G2 K), H ≤ g2BCGroup K → 8 ≤ Nat.card H →
      ∀ α : MulAut ↥(adjointGroup .G2 K),
        (∀ z : ↥(adjointGroup .G2 K), (z : ModGL .G2 K) ∈ H → α z = z) →
          ∃ c : ↥(adjointGroup .G2 K),
            (c : ModGL .G2 K) ∈ g2ShortParabolicRadical K ⊔ g2TorusR K ∧ α = MulAut.conj c

end Model

section Reduction

namespace G2

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem g2D0Hr_le_centralizer (hK : Nat.card K = 4) :
    g2ShortParabolicRadical K ⊔ g2TorusR K ≤ centralizer (g2BCGroup K : Set (ModGL .G2 K)) :=
  sup_le g2ShortParabolicRadical_le_centralizer (g2TorusR_le_centralizer_g2BCGroup hK)

omit [Finite K] in
theorem g2D0Hr_le_adjointGroup :
    g2ShortParabolicRadical K ⊔ g2TorusR K ≤ adjointGroup .G2 K :=
  sup_le g2ShortParabolicRadical_le_adjointGroup g2TorusR_le_adjointGroup

theorem card_g2D0Hr (hK : Nat.card K = 4) :
    Nat.card (g2ShortParabolicRadical K ⊔ g2TorusR K : Subgroup (ModGL .G2 K)) = 2 ^ 10 * 3 := by
  have hN : g2TorusR K ≤ normalizer (g2ShortParabolicRadical K : Set (ModGL .G2 K)) :=
    (le_sup_right : g2TorusR K ≤ g2Para K).trans g2Para_le_normalizer
  have h := card_sup_mul_card_inf hN
  have hD : Nat.card (g2ShortParabolicRadical K) = 2 ^ 10 := by
    rw [card_g2ShortParabolicRadical, hK]
    norm_num
  have hT : Nat.card (g2TorusR K) = 3 := by
    rw [card_g2TorusR, hK]
  have hI : g2ShortParabolicRadical K ⊓ g2TorusR K = ⊥ :=
    disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard (by rw [hD, hT]; norm_num))
  rw [hI, card_bot, mul_one, hD, hT] at h
  exact h

end G2

namespace Sec3Model

theorem exists_mul_of_fix (hG : G24Hyp) {G : Type} [Group G] {A A₁ E F : Subgroup G} {x : G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f : ↥(adjointGroup .G2 K) →* G}
    (hK : Nat.card K = 4) (hM : Sec3Model G A A₁ E F x K f) {w : G}
    (hwN : w ∈ normalizer (A : Set G)) {B : Subgroup G} (hB : B ≤ E ⊓ A) (hB8 : 8 ≤ Nat.card B)
    (hwB : w ∈ centralizer (B : Set G)) :
    ∃ k ∈ centralizer (A : Set G), ∃ c ∈ ((g2ShortParabolicRadical K ⊔ g2TorusR K).subgroupOf
      (adjointGroup .G2 K)).map f, w = k * c := by
  set H : Subgroup (ModGL .G2 K) := (B.comap f).map (adjointGroup .G2 K).subtype with hH
  have hHZ : H ≤ g2BCGroup K := by
    rintro _ ⟨z, hz, rfl⟩
    have hfz : f z ∈ E ⊓ A := hB hz
    rw [← hM.E_eq] at hfz
    obtain ⟨z', hz', hz'e⟩ := hfz
    rw [hM.inj hz'e] at hz'
    exact hz'
  have hH8 : 8 ≤ Nat.card H := by
    rw [hH, card_map_of_injective (adjointGroup .G2 K).subtype_injective]
    have hBA : B ≤ f.range := hM.range_eq ▸ (hB.trans inf_le_right)
    have h1 : Nat.card ((B.comap f).map f) = Nat.card (B.comap f) := card_map_of_injective hM.inj
    rw [map_comap_eq, inf_eq_right.mpr hBA] at h1
    omega
  have hα : ∀ z : ↥(adjointGroup .G2 K), (z : ModGL .G2 K) ∈ H → hM.act ⟨w, hwN⟩ z = z := by
    intro z hz
    obtain ⟨z', hz', hz'e⟩ := hz
    have hzz : z' = z := Subtype.ext hz'e
    subst hzz
    apply hM.inj
    rw [Sec3Model.act_apply]
    have h1 := mem_centralizer_iff.mp hwB (f z') hz'
    change w * f z' * w⁻¹ = f z'
    rw [← h1, mul_inv_cancel_right]
  obtain ⟨g, hg, hαg⟩ := hG K hK H hHZ hH8 _ hα
  have hfgA : f g ∈ A := by
    rw [← hM.range_eq]
    exact ⟨g, rfl⟩
  refine ⟨w * (f g)⁻¹, ?_, f g, ⟨g, mem_subgroupOf.mpr hg, rfl⟩, by group⟩
  have h1 : hM.act ⟨f g, le_normalizer hfgA⟩ = hM.act ⟨w, hwN⟩ := by
    rw [hM.act_of_mem hfgA, hαg]
    congr 1
    exact hM.equivA.symm_apply_eq.mpr (Subtype.ext rfl)
  have h2 : hM.act (⟨w, hwN⟩ * ⟨f g, le_normalizer hfgA⟩⁻¹) = 1 := by
    rw [map_mul, map_inv, h1, mul_inv_cancel]
  exact (hM.isActionHom_act.eq_one_iff _).mp h2

end Sec3Model

theorem step17G24Odd_of (h4 : AS76b.Asc75Theorem4) (h34 : AS76b.Asc08Lemma34) (hG : G24Hyp) :
    Step17G24Odd := by
  intro G _ _ A A₁ R g E F x hS X hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hFr := hS.frame
  have hB := hS.base
  have hstd := hB.hyp.standard
  have hFs := (h34 G A hB.hyp31).2
  have hKn := not_normal_centralizer hstd hB.hyp.not_normal
  set K := centralizer (A : Set G) with hKdef
  set O := AS76b.oddCoreIn K with hOdef
  set C := A ⊓ centralizer ((E ⊓ A : Subgroup G) : Set G) with hCdef
  have hK := AS76b.tightlyEmbedded_centralizer hstd
  have hNK := AS76b.normalizer_centralizer_eq hstd
  have hRK : R ≤ K := hS.sylowR.le
  obtain ⟨⟨hXo, hEX⟩, hmax⟩ := id hX
  have hX2 : ¬ 2 ∣ Nat.card X := fun h => (Nat.not_even_iff_odd.mpr hXo) (even_iff_two_dvd.mpr h)
  have hRX : R ≤ normalizer (X : Set G) := hFr.R_le_E.trans hEX
  have hAK : ∀ z ∈ A, z ∈ K → z = 1 := by
    intro z hzA hzK
    have hz : (⟨z, hzA⟩ : A) ∈ center A := mem_center_iff.mpr fun a =>
      Subtype.ext (mem_centralizer_iff.mp hzK a a.2)
    rw [hS.center_eq, mem_bot] at hz
    exact congrArg Subtype.val hz
  have hcomm : ∀ c ∈ A, ∀ k ∈ K, c * k = k * c := fun c hc k hk => mem_centralizer_iff.mp hk c hc
  have hAN : A ≤ normalizer (K : Set G) := by
    rw [hNK]
    exact le_normalizer
  have hNO : normalizer (A : Set G) ≤ normalizer (O : Set G) := by
    rw [← hNK]
    exact AS76b.normalizer_le_normalizer_oddCoreIn K
  have hKO : K ≤ normalizer (O : Set G) := AS76b.le_normalizer_oddCoreIn K
  have hRK' : R ≤ normalizer (K : Set G) := hRK.trans le_normalizer
  have hEN : E ≤ normalizer (A : Set G) :=
    hFr.E_le.trans (sup_le (hS.le.trans le_normalizer) (hRK.trans (centralizer_le_normalizer _)))
  have hEO : E ≤ normalizer (O : Set G) := hEN.trans hNO
  have hXNA : X ≤ normalizer (A : Set G) := by
    refine le_of_forall_inf_centralizer_le
      (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.isElementaryAbelian_of_sq_eq_one
        hS.elemR.2) (by rw [hFr.cardR]; norm_num) hX2 hRX ?_
    intro r hr hr1 y hy
    rw [← hNK]
    exact RankTwoSporadic.mem_normalizer_of_commute_of_tightlyEmbedded hK (hRK hr) hr1
      (hS.elemR.2 r hr) (mem_centralizer_singleton_iff.mp hy.2)
  have hXO : X ≤ normalizer (O : Set G) := hXNA.trans hNO
  obtain ⟨Kf, _, _, _, hKf, f, hM⟩ := exists_sec3Model hS
  have hEA16 : Nat.card (E ⊓ A : Subgroup G) = 16 := by
    obtain ⟨hEA, -, -, -, h16, -⟩ := Sec3.frame_inf_A₁ hS
    rw [hEA]
    exact h16
  have hfC : ((g2ShortParabolicRadical Kf ⊔ g2TorusR Kf).subgroupOf
      (adjointGroup .G2 Kf)).map f ≤ C := by
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨by rw [← hM.range_eq]; exact ⟨c, rfl⟩, mem_centralizer_iff.mpr fun w hw => ?_⟩
    rw [← hM.E_eq] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    have h1 := mem_centralizer_iff.mp (G2.g2D0Hr_le_centralizer hKf (mem_subgroupOf.mp hc)) _
      (mem_subgroupOf.mp hz)
    rw [← map_mul, ← map_mul]
    exact congrArg f (Subtype.ext h1)
  have hXCK : X ≤ C ⊔ K := by
    have hEn : Nontrivial E := by
      rw [← Finite.one_lt_card_iff_nontrivial, hFr.cardE]
      norm_num
    refine le_of_forall_inf_centralizer_hyperplane_le
      (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.isElementaryAbelian_of_sq_eq_one
        hFr.elemE.2) hEn hX2 hEX ?_
    intro B hBE hB2 y hy
    have hyN := hXNA hy.1
    have hB8 : 8 ≤ Nat.card (B ⊓ A : Subgroup G) := by
      have h1 : B.relIndex (E ⊓ A) ≤ 2 := by
        rw [← hB2]
        exact relIndex_le_of_le_right inf_le_left (by rw [hB2]; norm_num)
      have h2 := relIndex_mul_card B (E ⊓ A)
      rw [show B ⊓ (E ⊓ A) = B ⊓ A by rw [← inf_assoc, inf_eq_left.mpr hBE], hEA16] at h2
      nlinarith
    obtain ⟨k, hk, c, hc, rfl⟩ := Sec3Model.exists_mul_of_fix hG hKf hM hyN
      (inf_le_inf_right A hBE) hB8
      (Subgroup.centralizer_le (show ((B ⊓ A : Subgroup G) : Set G) ⊆ B from fun z hz => hz.1)
        hy.2)
    exact mul_mem (mem_sup_right hk) (mem_sup_left (hfC hc))
  have hCK : ∀ w ∈ C ⊔ K, ∃ c ∈ C, ∃ k ∈ K, w = c * k := by
    intro w hw
    have hw' : w ∈ ((C ⊔ K : Subgroup G) : Set G) := hw
    rw [coe_mul_of_left_le_normalizer_right C K (inf_le_left.trans hAN), Set.mem_mul] at hw'
    obtain ⟨c, hc, k, hk, rfl⟩ := hw'
    exact ⟨c, hc, k, hk, rfl⟩
  have hOX : O ≤ X := by
    have hP : Odd (Nat.card (O ⊔ X : Subgroup G)) := by
      have h := card_sup_mul_card_inf hXO
      have h1 : Nat.card (O ⊔ X : Subgroup G) ∣ Nat.card O * Nat.card X := ⟨_, h.symm⟩
      exact ((AS76b.odd_card_oddCoreIn K).mul hXo).of_dvd_nat h1
    have hEOX : E ≤ normalizer ((O ⊔ X : Subgroup G) : Set G) := by
      intro e he
      refine AS76b.mem_normalizer_of_map_conj_le ?_
      rw [Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨o, ho, rfl⟩
        exact (mem_normalizer_iff.mp (hEO he) o).mp ho
      · rintro _ ⟨y, hy, rfl⟩
        exact (mem_normalizer_iff.mp (hEX he) y).mp hy
    exact le_sup_left.trans (hmax ⟨hP, hEOX⟩ le_sup_right)
  have hXKO : X ⊓ K ≤ O := by
    refine le_oddCoreIn_of_le_normalizer h4 hK hS.sylowR hS.elemR (by rw [hFr.cardR]; norm_num)
      hFs hKn inf_le_right ?_ (hXo.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
    intro r hr
    rw [mem_normalizer_iff]
    intro y
    exact and_congr (mem_normalizer_iff.mp (hRX hr) y) (mem_normalizer_iff.mp (hRK' hr) y)
  have hdec : ∀ w ∈ X, ∃ c ∈ X ⊓ A, ∃ k ∈ O, w = c * k := by
    intro w hw
    obtain ⟨c, hc, k, hk, rfl⟩ := hCK w (hXCK hw)
    have hko : Odd (orderOf k) := by
      have hwo : Odd (orderOf (c * k)) := hXo.of_dvd_nat (Subgroup.orderOf_dvd_natCard X hw)
      have hpow : (c * k) ^ orderOf (c * k) = 1 := pow_orderOf_eq_one _
      rw [(Commute.mul_pow (hcomm c hc.1 k hk) _)] at hpow
      have h1 : c ^ orderOf (c * k) = (k ^ orderOf (c * k))⁻¹ := eq_inv_of_mul_eq_one_left hpow
      have h2 := hAK _ (pow_mem hc.1 _) (by rw [h1]; exact inv_mem (pow_mem hk _))
      rw [h2, one_mul] at hpow
      exact hwo.of_dvd_nat (orderOf_dvd_of_pow_eq_one hpow)
    have hkr : ∀ r ∈ R, k⁻¹ * (r * k * r⁻¹) ∈ O := by
      intro r hr
      have h1 : r * (c * k) * r⁻¹ ∈ X := (mem_normalizer_iff.mp (hRX hr) _).mp hw
      have hrc : r * c * r⁻¹ = c := by
        rw [← (mem_centralizer_iff.mp (hRK hr) c hc.1), mul_inv_cancel_right]
      have h2 : (c * k)⁻¹ * (r * (c * k) * r⁻¹) = k⁻¹ * (r * k * r⁻¹) := by
        calc (c * k)⁻¹ * (r * (c * k) * r⁻¹) =
            k⁻¹ * c⁻¹ * ((r * c * r⁻¹) * (r * k * r⁻¹)) := by group
          _ = k⁻¹ * (r * k * r⁻¹) := by rw [hrc]; group
      have h3 : k⁻¹ * (r * k * r⁻¹) ∈ X := h2 ▸ mul_mem (inv_mem hw) h1
      have h4 : k⁻¹ * (r * k * r⁻¹) ∈ K :=
        mul_mem (inv_mem hk) ((mem_normalizer_iff.mp (hRK' hr) k).mp hk)
      exact hXKO ⟨h3, h4⟩
    have hkN : zpowers k ≤ normalizer (O : Set G) := (zpowers_le.mpr hk).trans hKO
    have hY : O ⊔ zpowers k ≤ O := by
      refine le_oddCoreIn_of_le_normalizer h4 hK hS.sylowR hS.elemR
        (by rw [hFr.cardR]; norm_num) hFs hKn
        (sup_le (Subgroup.map_subtype_le _) (zpowers_le.mpr hk)) ?_ ?_
      · intro r hr
        refine AS76b.mem_normalizer_of_map_conj_le ?_
        rw [Subgroup.map_sup]
        refine sup_le ?_ ?_
        · rintro _ ⟨o, ho, rfl⟩
          exact mem_sup_left ((mem_normalizer_iff.mp (hKO (hRK hr)) o).mp ho)
        · rw [MonoidHom.map_zpowers, zpowers_le]
          have e : r * k * r⁻¹ = k * (k⁻¹ * (r * k * r⁻¹)) := by group
          show r * k * r⁻¹ ∈ O ⊔ zpowers k
          rw [e]
          exact mul_mem (mem_sup_right (mem_zpowers k)) (mem_sup_left (hkr r hr))
      · have h := card_sup_mul_card_inf hkN
        have h1 : Nat.card (O ⊔ zpowers k : Subgroup G) ∣ Nat.card O * Nat.card (zpowers k) :=
          ⟨_, h.symm⟩
        rw [Nat.card_zpowers] at h1
        exact ((AS76b.odd_card_oddCoreIn K).mul hko).of_dvd_nat h1
    have hkO : k ∈ O := hY (mem_sup_right (mem_zpowers k))
    refine ⟨c, ⟨?_, hc.1⟩, k, hkO, rfl⟩
    have := mul_mem hw (inv_mem (hOX hkO))
    rwa [mul_inv_cancel_right] at this
  have hXeq : X = (X ⊓ A) ⊔ O := by
    refine le_antisymm (fun w hw => ?_) (sup_le inf_le_left hOX)
    obtain ⟨c, hc, k, hk, rfl⟩ := hdec w hw
    exact mul_mem (mem_sup_left hc) (mem_sup_right hk)
  have hXAC : X ⊓ A ≤ C := by
    intro w hw
    obtain ⟨c, hc, k, hk, rfl⟩ := hCK w (hXCK hw.1)
    have hcA : c ∈ A := (mem_inf.mp hc).1
    have hwA : c * k ∈ A := (mem_inf.mp hw).2
    have hkA : k ∈ A := by
      have := A.mul_mem (A.inv_mem hcA) hwA
      rwa [inv_mul_cancel_left] at this
    rw [hAK k hkA hk, mul_one]
    exact hc
  have hCeq : C = ((g2ShortParabolicRadical Kf ⊔ g2TorusR Kf).subgroupOf
      (adjointGroup .G2 Kf)).map f := by
    refine le_antisymm (fun a ha => ?_) hfC
    obtain ⟨k, hk, c, hc, hac⟩ :=
      Sec3Model.exists_mul_of_mem_normalizer hKf hM (le_normalizer ha.1) ha.2
    have hcA : c ∈ A := (hfC hc).1
    have hkA : k ∈ A := by
      have e : k = a * c⁻¹ := by rw [hac]; group
      rw [e]
      exact mul_mem ha.1 (inv_mem hcA)
    rw [hac, hAK k hkA hk, one_mul]
    exact hc
  have hCcard : Nat.card C = 2 ^ 10 * 3 := by
    rw [hCeq, card_map_of_injective hM.inj, ← G2.card_g2D0Hr hKf]
    exact Nat.card_congr (subgroupOfEquivOfLe G2.g2D0Hr_le_adjointGroup).toEquiv
  have hxZ : x ∈ centerIn A₁ := by rw [hS.center_A₁]; exact mem_zpowers x
  have hxA : x ∈ A := hS.le hxZ.1
  have hx1 : x ≠ 1 := fun h => by
    have := hS.order_x
    rw [h, orderOf_one] at this
    omega
  have hA₁x : A₁ ≤ centralizer ({x} : Set G) := fun a ha =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hxZ.2 a ha)
  have hRx : R ≤ centralizer ({x} : Set G) := fun r hr =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hRK hr) x hxA).symm
  have hEx : E ≤ centralizer ({x} : Set G) := hFr.E_le.trans (sup_le hA₁x hRx)
  have hXA3 : Nat.card (X ⊓ A : Subgroup G) = 3 := by
    have hdvd : Nat.card (X ⊓ A : Subgroup G) ∣ 2 ^ 10 * 3 :=
      hCcard ▸ Subgroup.card_dvd_of_le hXAC
    have hodd : Odd (Nat.card (X ⊓ A : Subgroup G)) :=
      hXo.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    have hcop : Nat.Coprime (Nat.card (X ⊓ A : Subgroup G)) (2 ^ 10) :=
      Nat.Coprime.pow_right 10 (Nat.coprime_two_right.mpr hodd)
    have h3 : Nat.card (X ⊓ A : Subgroup G) ∣ 3 := (Nat.Coprime.dvd_mul_left hcop).mp hdvd
    have hne1 : Nat.card (X ⊓ A : Subgroup G) ≠ 1 := by
      intro h1
      have hbot : X ⊓ A = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
      have hXO' : X ≤ O := by
        rw [hXeq, hbot, bot_sup_eq]
      have hxN : zpowers x ≤ normalizer (O : Set G) :=
        (zpowers_le.mpr (le_normalizer hxA)).trans hNO
      have hP : Odd (Nat.card (O ⊔ zpowers x : Subgroup G)) := by
        have h := card_sup_mul_card_inf hxN
        have h1 : Nat.card (O ⊔ zpowers x : Subgroup G) ∣ Nat.card O * Nat.card (zpowers x) :=
          ⟨_, h.symm⟩
        rw [Nat.card_zpowers, hS.order_x] at h1
        exact ((AS76b.odd_card_oddCoreIn K).mul (by decide : Odd 3)).of_dvd_nat h1
      have hEOx : E ≤ normalizer ((O ⊔ zpowers x : Subgroup G) : Set G) := by
        intro e he
        refine AS76b.mem_normalizer_of_map_conj_le ?_
        rw [Subgroup.map_sup]
        refine sup_le ?_ ?_
        · rintro _ ⟨o, ho, rfl⟩
          exact mem_sup_left ((mem_normalizer_iff.mp (hEO he) o).mp ho)
        · rw [MonoidHom.map_zpowers, zpowers_le]
          refine mem_sup_right ?_
          show e * x * e⁻¹ ∈ zpowers x
          rw [mem_centralizer_singleton_iff.mp (hEx he), mul_inv_cancel_right]
          exact mem_zpowers x
      have hle := hmax ⟨hP, hEOx⟩ (hXO'.trans le_sup_left)
      have hxX : x ∈ X ⊓ A := ⟨hle (mem_sup_right (mem_zpowers x)), hxA⟩
      rw [hbot, mem_bot] at hxX
      exact hx1 hxX
    rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
    · exact absurd h hne1
    · exact h
  refine ⟨?_, hXeq⟩
  rw [isSylowOf_iff]
  refine ⟨hXAC, IsPGroup.of_card (n := 1) (by rw [hXA3, pow_one]), ?_⟩
  have h := relIndex_mul_card (X ⊓ A) C
  rw [inf_eq_left.mpr hXAC, hXA3, hCcard] at h
  omega

theorem g24Hyp : G24Hyp := fun _ _ _ _ hK _ hHZ hH8 α hα => G2.eq_conj_of_fix hK hHZ hH8 α hα

theorem step17G24Odd (h4 : AS76b.Asc75Theorem4) (h34 : AS76b.Asc08Lemma34) : Step17G24Odd :=
  step17G24Odd_of h4 h34 g24Hyp

end Reduction

end CFSG.ComponentClassification.AS81

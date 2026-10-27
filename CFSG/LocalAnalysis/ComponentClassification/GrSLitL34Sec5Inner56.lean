module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inputs56X
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma551
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Sylow

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem derived_le_of_relIndex_le_two {H P : Subgroup G} (hidx : H.relIndex P ≤ 2) :
    ⁅P, P⁆ ≤ H := by
  refine commutator_le.mpr fun a ha b hb => ?_
  have hpos : H.relIndex P ≠ 0 := (H.subgroupOf P).index_ne_zero_of_finite
  rcases (show H.relIndex P = 1 ∨ H.relIndex P = 2 by omega) with h1 | h2
  · exact relIndex_eq_one.mp h1
      (P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb))
  · have h2' : (H.subgroupOf P).index = 2 := h2
    have key : ⁅(⟨a, ha⟩ : P), ⟨b, hb⟩⁆ ∈ H.subgroupOf P := by
      rw [commutatorElement_def, show (⟨a, ha⟩ : P) * ⟨b, hb⟩ * (⟨a, ha⟩ : P)⁻¹ *
          (⟨b, hb⟩ : P)⁻¹ = ((⟨a, ha⟩ : P) * ⟨b, hb⟩) * ((⟨a, ha⟩ : P)⁻¹ * (⟨b, hb⟩ : P)⁻¹) by
          group, mul_mem_iff_of_index_two h2', mul_mem_iff_of_index_two h2',
        mul_mem_iff_of_index_two h2', inv_mem_iff, inv_mem_iff]
    rw [mem_subgroupOf] at key
    simpa [commutatorElement_def] using key

theorem commute_of_mem_withKernel {S L : Subgroup G} (hS : IsPGroup 2 S) {w z : G}
    (hwS : w ∈ S) (hw : w ∈ withKernel L) (hzS : z ∈ S) (hz : z ∈ zStarIn L) :
    w * z = z * w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLN : L ≤ normalizer (coreActionKernel L : Set G) :=
    le_normalizer.trans (normalizer_le_normalizer_coreActionKernel L)
  have hw' : w ∈ ((L ⊔ coreActionKernel L : Subgroup G) : Set G) := hw
  rw [coe_mul_of_left_le_normalizer_right L (coreActionKernel L) hLN] at hw'
  obtain ⟨l, hl, c, hc, rfl⟩ := hw'
  have hzL : z ∈ L := by
    obtain ⟨z', -, rfl⟩ := hz
    exact z'.2
  have ha : l⁻¹ * z⁻¹ * l * z ∈ oddIn L :=
    (mem_coreActionKernel.mp (zStarIn_le_coreActionKernel L hz)).2 l hl
  have hb : z⁻¹ * c⁻¹ * z * c ∈ oddIn L := (mem_coreActionKernel.mp hc).2 z hzL
  have hcN : c⁻¹ ∈ normalizer (oddIn L : Set G) :=
    normalizer_le_normalizer_oddIn L (inv_mem (mem_coreActionKernel.mp hc).1)
  have ha' : c⁻¹ * (l⁻¹ * z⁻¹ * l * z) * c ∈ oddIn L := by
    have h := (mem_normalizer_iff.mp hcN _).mp ha
    rwa [inv_inv] at h
  have h1 : (l * c)⁻¹ * z⁻¹ * (l * c) * z ∈ oddIn L := by
    rw [show (l * c)⁻¹ * z⁻¹ * (l * c) * z =
      c⁻¹ * (l⁻¹ * z⁻¹ * l * z) * c * (z⁻¹ * c⁻¹ * z * c)⁻¹ by group]
    exact mul_mem ha' (inv_mem hb)
  have h2 : (l * c)⁻¹ * z⁻¹ * (l * c) * z ∈ S :=
    mul_mem (mul_mem (mul_mem (inv_mem hwS) (inv_mem hzS)) hwS) hzS
  have hSO : S ⊓ oddIn L = ⊥ := by
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    obtain ⟨k, hk⟩ := hS.exists_card_eq
    have hodd : Odd (Nat.card (oddIn L)) := by
      rw [oddIn, card_map_of_injective (subtype_injective _)]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    rw [hk]
    exact (Nat.coprime_two_left.mpr hodd).pow_left k
  have h3 : (l * c)⁻¹ * z⁻¹ * (l * c) * z = 1 := by
    have h4 : (l * c)⁻¹ * z⁻¹ * (l * c) * z ∈ S ⊓ oddIn L := mem_inf.mpr ⟨h2, h1⟩
    rw [hSO] at h4
    exact h4
  calc l * c * z = z * (l * c) * ((l * c)⁻¹ * z⁻¹ * (l * c) * z) := by group
    _ = z * (l * c) := by rw [h3, mul_one]

theorem exists_unbalanced_of_wGroup_eq_bot {L : Subgroup G} {t u : G}
    (hLt : L ≤ centralizer ({t} : Set G))
    (hLpt : IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set G))))
    (hX : ¬ oddIn L ≤ (center ↥L).map L.subtype) (hto : orderOf t = 2)
    (huN : u ∈ normalizer (L : Set G)) (hu : orderOf u = 2) (huK : u ∉ coreActionKernel L)
    (hut : u * t = t * u) (hW : wGroup (zpowers u ⊔ zpowers t) = ⊥) :
    ∃ u₁ ∈ ({u, u * t} : Set G),
      ¬ oddIn L ⊓ centralizer ({u₁} : Set G) ≤ oddIn (centralizer ({u₁} : Set G)) := by
  have hu2 : u * u = 1 := by rw [← pow_two, ← hu, pow_orderOf_eq_one]
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  have htL : t ∈ centralizer (L : Set G) := mem_centralizer_iff.mpr fun l hl =>
    mem_centralizer_singleton_iff.mp (hLt hl)
  have htK : t ∈ coreActionKernel L := mem_coreActionKernel_of_commute fun l hl =>
    (mem_centralizer_singleton_iff.mp (hLt hl)).symm
  have h1 : oddIn L ⊓ centralizer ({u} : Set G) ≠ ⊥ := by
    intro hbot
    have hinv := conj_eq_inv_of_inf_centralizer_eq_bot (normalizer_le_normalizer_oddIn L huN)
      hu2 hbot
    exact huK (mem_coreActionKernel_of_inverts hLt hLpt hX huN hinv)
  by_contra hall
  push Not at hall
  have hall₁ := hall u (Set.mem_insert u _)
  have hall₂ := hall (u * t) (Set.mem_insert_of_mem u rfl)
  have hunt : u ∉ zpowers t := by
    intro hm
    rcases (LocalB.mem_zpowers_iff_of_involution t u hto).mp hm with h | h
    · exact huK (h ▸ one_mem _)
    · exact huK (h ▸ htK)
  obtain ⟨hUTe, hUTc⟩ := elemTwo_zpowers_sup hu2 (isElemTwo_zpowers ht2)
    (fun y hy => by
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
      exact (Commute.zpow_right hut j).eq) hunt
  have hXt : oddIn L ≤ oddIn (centralizer ({t} : Set G)) :=
    GSLit.map_pPrimeCore_le_of_isPComponent hLt hLpt
  have hCX : oddIn L ⊓ centralizer ({u} : Set G) ≤
      ⨅ (b : G) (_ : b ∈ zpowers u ⊔ zpowers t) (_ : b ≠ 1),
        (pPrimeCore 2 (centralizer ({b} : Set G))).map (centralizer ({b} : Set G)).subtype := by
    intro x hx
    obtain ⟨hxX, hxu⟩ := mem_inf.mp hx
    simp only [mem_iInf]
    intro b hb hb1
    obtain ⟨a, h, hh, hbah⟩ := mem_zpowers_sup (fun y hy => by
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
      exact (Commute.zpow_right hut j).eq) hb
    have hua := (LocalB.mem_zpowers_iff_of_involution u (u ^ a) hu).mp (zpow_mem (mem_zpowers u) a)
    have hth := (LocalB.mem_zpowers_iff_of_involution t h hto).mp hh
    have hxt : x ∈ centralizer ({t} : Set G) :=
      mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp htL) x
        (map_subtype_le _ hxX))
    rcases hua with h1 | h1 <;> rcases hth with h2 | h2 <;> rw [hbah, h1, h2] at hb1 ⊢
    · exact absurd (one_mul (1 : G)) hb1
    · rw [one_mul]
      exact hXt hxX
    · rw [mul_one]
      exact hall₁ hx
    · have hxut : x ∈ oddIn L ⊓ centralizer ({u * t} : Set G) := by
        refine mem_inf.mpr ⟨hxX, mem_centralizer_singleton_iff.mpr ?_⟩
        have hxu' := mem_centralizer_singleton_iff.mp hxu
        have hxt' := mem_centralizer_singleton_iff.mp hxt
        calc x * (u * t) = (x * u) * t := by group
          _ = u * x * t := by rw [hxu']
          _ = u * (x * t) := by group
          _ = u * (t * x) := by rw [hxt']
          _ = u * t * x := by group
      exact hall₂ hxut
  have hΔW : (⨅ (b : G) (_ : b ∈ zpowers u ⊔ zpowers t) (_ : b ≠ 1),
      (pPrimeCore 2 (centralizer ({b} : Set G))).map (centralizer ({b} : Set G)).subtype) ≤
      wGroup (zpowers u ⊔ zpowers t) := by
    refine le_trans ?_ (le_iSup _ (zpowers u ⊔ zpowers t))
    refine le_trans ?_ (le_iSup _ le_rfl)
    refine le_trans ?_ (le_iSup _ (by rw [hUTc, Nat.card_zpowers, hto]))
    exact le_iSup (fun _ : ∀ b ∈ zpowers u ⊔ zpowers t, b * b = 1 => _) hUTe.2
  exact h1 (le_bot_iff.mp (hW ▸ hCX.trans hΔW))

theorem wGroup_eq_bot_of_inner (hGWb : GWTwoBalanced G) (hFour : L34CommutatorFourGroupFact)
    {L S : Subgroup G} {t w : G} (hLperf : ⁅L, L⁆ = L)
    (htype : IsL34Type (L ⧸ Open.fusionZStar L))
    (hSyl : IsSylowTwoIn S (normalizer (L : Set G))) (hto : orderOf t = 2)
    (hLt : L ≤ centralizer ({t} : Set G)) (hZS : ∀ s ∈ S, s * t = t * s)
    (hW8 : ∀ A : Subgroup G, IsEightGroup A → A ≤ L ⊔ zpowers t ∨ A ≤ coreActionKernel L →
      wGroup A = ⊥)
    (hwS : w ∈ S) (hw2 : w * w = 1) (hwW : w ∈ withKernel L) (hwLt : w ∉ L ⊔ zpowers t)
    (hidx : Nat.card S ≤ 2 * Nat.card ↥(S ⊓ centralizer ({w} : Set G))) :
    wGroup (zpowers w ⊔ zpowers t) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := IsSylowTwoIn.isPGroup hSyl
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  have htK : t ∈ coreActionKernel L := mem_coreActionKernel_of_commute fun l hl =>
    (mem_centralizer_singleton_iff.mp (hLt hl)).symm
  have hS₀ : IsSylowTwoIn (S ⊓ L) L := isSylowTwoIn_inf_of_isSubnormal hSyl le_normalizer
    (Subgroup.Normal.isSubnormal Subgroup.normal_in_normalizer)
  obtain ⟨Y, hYP, hYe, hY4, hYZ, hYc, -⟩ := hFour G L (S ⊓ L) hLperf htype hS₀
  have hidx₁ : (S ⊓ centralizer ({w} : Set G)).relIndex S ≤ 2 := by
    have h1 := relIndex_mul_card_of_le (inf_le_left : S ⊓ centralizer ({w} : Set G) ≤ S)
    have h2 : 0 < Nat.card ↥(S ⊓ centralizer ({w} : Set G)) := Nat.card_pos
    by_contra hgt
    push Not at hgt
    have : 3 * Nat.card ↥(S ⊓ centralizer ({w} : Set G)) ≤ Nat.card S := by
      rw [← h1]
      exact Nat.mul_le_mul_right _ hgt
    omega
  have hidx₂ : (S ⊓ centralizer ({w} : Set G) ⊓ L).relIndex (S ⊓ L) ≤ 2 :=
    (relIndex_inf_le_of_le (K := L) inf_le_left).trans hidx₁
  have hYw : Y ≤ centralizer ({w} : Set G) := by
    refine hYc.trans (sup_le ((derived_le_of_relIndex_le_two hidx₂).trans
      (inf_le_left.trans inf_le_right)) fun z hz => ?_)
    obtain ⟨hzSL, hzZ⟩ := mem_inf.mp hz
    exact mem_centralizer_singleton_iff.mpr
      (commute_of_mem_withKernel hS2 hwS hwW (mem_inf.mp hzSL).1 hzZ).symm
  have hYL : Y ≤ L := hYP.trans inf_le_right
  have htY : t ∉ Y := by
    intro h
    have htZ : t ∈ Y ⊓ zStarIn L :=
      mem_inf.mpr ⟨h, inf_coreActionKernel_le_zStarIn L (mem_inf.mpr ⟨hYL h, htK⟩)⟩
    rw [hYZ, mem_bot] at htZ
    rw [htZ, orderOf_one] at hto
    exact absurd hto (by norm_num)
  have htYc : ∀ y ∈ Y, t * y = y * t := fun y hy =>
    (mem_centralizer_singleton_iff.mp (hLt (hYL hy))).symm
  obtain ⟨hB, hBc⟩ := elemTwo_zpowers_sup ht2 hYe htYc htY
  have hWB : wGroup (zpowers t ⊔ Y) = ⊥ := hW8 _ ⟨hB, by rw [hBc, hY4]⟩
    (Or.inl (sup_le le_sup_right (hYL.trans le_sup_left)))
  obtain ⟨b, hbY, hb1⟩ : ∃ b ∈ Y, b ≠ 1 := by
    by_contra hne
    push Not at hne
    rw [(eq_bot_iff_forall Y).mpr hne, card_bot] at hY4
    omega
  have hb2 : b * b = 1 := hYe.2 b hbY
  have hbt : b * t = t * b := (htYc b hbY).symm
  have hbnt : b ∉ zpowers t := by
    intro hm
    rcases (LocalB.mem_zpowers_iff_of_involution t b hto).mp hm with h | h
    · exact hb1 h
    · exact htY (h ▸ hbY)
  obtain ⟨hD, hDc⟩ := elemTwo_zpowers_sup hb2 (isElemTwo_zpowers ht2)
    (fun y hy => by
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
      exact (Commute.zpow_right hbt j).eq) hbnt
  have hwt : w * t = t * w := hZS w hwS
  have hwb : w * b = b * w := (mem_centralizer_singleton_iff.mp (hYw hbY)).symm
  have hwD : ∀ y ∈ zpowers b ⊔ zpowers t, w * y = y * w := by
    have hle : zpowers b ⊔ zpowers t ≤ centralizer ({w} : Set G) := sup_le
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hwb.symm))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hwt.symm))
    exact fun y hy => (mem_centralizer_singleton_iff.mp (hle hy)).symm
  have hwnD : w ∉ zpowers b ⊔ zpowers t := fun h =>
    hwLt (sup_le (zpowers_le.mpr (mem_sup_left (hYL hbY))) le_sup_right h)
  obtain ⟨hA, hAc⟩ := elemTwo_zpowers_sup hw2 hD hwD hwnD
  have hBw : zpowers t ⊔ Y ≤ centralizer ({w} : Set G) :=
    sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hwt.symm)) hYw
  have hBb : zpowers t ⊔ Y ≤ centralizer ({b} : Set G) :=
    sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hbt.symm))
      fun y hy => mem_centralizer_singleton_iff.mpr (hYe.1 y hy b hbY)
  have hBt : zpowers t ⊔ Y ≤ centralizer ({t} : Set G) :=
    sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)) (hYL.trans hLt)
  have hcen : ∀ g : G, zpowers t ⊔ Y ≤ centralizer ({g} : Set G) →
      g ∈ centralizer ((zpowers t ⊔ Y : Subgroup G) : Set G) := fun g hg =>
    mem_centralizer_iff.mpr fun h hh => mem_centralizer_singleton_iff.mp (hg hh)
  have hAB : zpowers w ⊔ (zpowers b ⊔ zpowers t) ≤
      centralizer ((zpowers t ⊔ Y : Subgroup G) : Set G) :=
    sup_le (zpowers_le.mpr (hcen w hBw))
      (sup_le (zpowers_le.mpr (hcen b hBb)) (zpowers_le.mpr (hcen t hBt)))
  have hA8 : 8 ≤ Nat.card ↥(zpowers w ⊔ (zpowers b ⊔ zpowers t)) := by
    rw [hAc, hDc, Nat.card_zpowers, hto]
  have hB8 : 8 ≤ Nat.card ↥(zpowers t ⊔ Y) := by rw [hBc, hY4]
  have hWA := wGroup_eq_of_commute hGWb (hA.isAbelianTwoOfRank hA8) (hB.isAbelianTwoOfRank hB8)
    fun x hx y hy => ((mem_centralizer_iff.mp (hAB hx)) y hy).symm
  have hle : zpowers w ⊔ zpowers t ≤ zpowers w ⊔ (zpowers b ⊔ zpowers t) :=
    sup_le le_sup_left (le_sup_right.trans le_sup_right)
  exact le_bot_iff.mp (hWB ▸ hWA ▸ wGroup_mono hle)

theorem exists_unbalanced_of_mem_withKernel (h53 : L34Lemma53)
    (hFour : L34CommutatorFourGroupFact) (hSol : SolomonCommutingCoreInput) {L : Subgroup G}
    {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T)
    (hLt : L ≤ centralizer ({t} : Set G))
    (hLpt : IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set G))))
    (hZS : ∀ s ∈ S, s * t = t * s) {w : G} (hwS : w ∈ S) (hw : orderOf w = 2)
    (hwK : w ∉ coreActionKernel L) (hwW : w ∈ withKernel L)
    (hidx : Nat.card S ≤ 2 * Nat.card ↥(S ⊓ centralizer ({w} : Set G))) :
    ∃ w₁ ∈ ({w, w * t} : Set G),
      ¬ oddIn L ⊓ centralizer ({w₁} : Set G) ≤ oddIn (centralizer ({w₁} : Set G)) := by
  by_cases hwLt : w ∈ L ⊔ zpowers t
  · exact (h53 G L t S T hset w hwS hw hwK hwLt).2
  obtain ⟨hbase, hfam, -, hSyl, -, -, -⟩ := hset
  obtain ⟨⟨-, -, -, -, -, hto, -, -⟩, htype, -, hX, hW8⟩ := hfam
  have hGWb : GWTwoBalanced G := gwTwoBalanced_of_locallyTwoBalanced hSol hbase.2.2.2.2.2.1
  have hperf : ⁅L, L⁆ = L := GSThmB.commutator_eq_self_of_isPComponent hLt hLpt
  have hw2 : w * w = 1 := by rw [← pow_two, ← hw, pow_orderOf_eq_one]
  exact exists_unbalanced_of_wGroup_eq_bot hLt hLpt hX hto (hSyl.1 hwS) hw hwK (hZS w hwS)
    (wGroup_eq_bot_of_inner hGWb hFour hperf htype hSyl hto hLt hZS hW8 hwS hw2 hwW hwLt hidx)

end CFSG.ComponentClassification.GrSLit.GrS5

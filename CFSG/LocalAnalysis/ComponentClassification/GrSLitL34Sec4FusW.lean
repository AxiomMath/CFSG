module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4WInv
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InvCls
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4End46F
public import CFSG.ClassicalInvolution.Asc77.AscT3CoreInvol
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4End46T

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.ComponentClassification.GrSLit.L34Facts

variable {G : Type} [Group G] [Finite G]

theorem wGroup_facts_of_setting (hRank : L34CenterRankFact)
    (hSqC : L34SquareCenterFact) (hWit : L34OuterWitnessFact) (hConn : L34EightsConnectedFact)
    (hU : L34UnbalancingUnitaryStep) (hC : L34UnitaryCentralizerFact) {a x : G}
    {J S W : Subgroup G} (hset : L34Sec4Setting G a x J S) (hcent : ∀ s ∈ S, s * a = a * s)
    (haZ : a ∈ S ⊓ zStarIn J) (hexp : Monoid.exponent ↥(S ⊓ zStarIn J) = 4)
    (hnc : ¬ IsCyclic ↥(S ⊓ zStarIn J))
    (hWx : wGroup (S ⊓ J ⊓ centralizer ({x} : Set G)) = W)
    (hNJ : normalizer (J : Set G) ≤ normalizer (W : Set G)) :
    (∃ f ∈ S ⊓ zStarIn J, f * f = 1 ∧ f ≠ 1 ∧ f ≠ a ∧
      ∀ A : Subgroup G, A ≤ S → IsAbelianTwoOfRank 3 A →
        (∀ y ∈ A, ∀ v ∈ zpowers a ⊔ zpowers f, v * y = y * v) → wGroup A = W) ∧
    ∀ A : Subgroup G, A ≤ S → IsElemTwo A → Nat.card A = 16 → wGroup A = W := by
  obtain ⟨hbase, hU3, hL34, -, hS, -, -⟩ := id hset
  have hGW : GWTwoBalanced G :=
    gwTwoBalanced_of_locallyTwoBalanced solomonCommutingCoreInput hbase.2.2.2.2.2.1
  have hJ : ⁅J, J⁆ = J := GSThmB.commutator_eq_self_of_isPComponent hU3.2.2.2.1 hU3.2.2.2.2.1
  have hS2 : IsPGroup 2 S := isPGroup_of_isSylowTwoIn hS
  have ha2 : orderOf a = 2 := hU3.1
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha2
    exact absurd ha2 (by norm_num)
  have hzK : ∀ {z : G}, z ∈ zStarIn J → z ∈ coreActionKernel J := fun hz => by
    have h : zStarIn J = J ⊓ coreActionKernel J := GSThmB.map_fusionZStar_eq J
    rw [h] at hz
    exact (mem_inf.mp hz).2
  have hZab : ∀ u ∈ S ⊓ zStarIn J, ∀ v ∈ S ⊓ zStarIn J, u * v = v * u := fun u hu v hv =>
    mul_comm_of_mem_coreActionKernel hS2 (mem_inf.mp hu).1 (hzK (mem_inf.mp hu).2)
      (mem_inf.mp hv).1 (map_subtype_le _ (mem_inf.mp hv).2)
  have h4 : Nat.card ↥(omegaOne (S ⊓ zStarIn J)) ≤ 4 := by
    have h := hRank G J (S ⊓ J) hJ hL34 (isSylowTwoIn_inf hS)
    rwa [inf_assoc, inf_of_le_right (show zStarIn J ≤ J from map_subtype_le _)] at h
  obtain ⟨a₁, ha₁, a₂, ha₂, h11, h22, h1, h2, h12⟩ :=
    exists_two_involutions_of_not_isCyclic (hS2.to_le inf_le_left) hZab hnc
  obtain ⟨f, hfZ, hff, hf1, hfa⟩ : ∃ f ∈ S ⊓ zStarIn J, f * f = 1 ∧ f ≠ 1 ∧ f ≠ a := by
    by_cases h : a₁ = a
    · exact ⟨a₂, ha₂, h22, h2, fun h' => h12 (h.trans h'.symm)⟩
    · exact ⟨a₁, ha₁, h11, h1, h⟩
  have hfV : f ∉ zpowers a := fun h => (eq_one_or_eq_of_mem_zpowers haa h).elim hf1 hfa
  obtain ⟨hV₀, hV₀c⟩ := isElemTwo_sup_zpowers (isElemTwo_zpowers haa) hff hfV fun e he => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp he
    exact Commute.zpow_left (hZab a haZ f hfZ) k
  have hca : Nat.card (zpowers a) = 2 := by
    rw [Nat.card_zpowers]
    exact ha2
  have hV₀4 : Nat.card ↥(zpowers a ⊔ zpowers f) = 4 := by rw [hV₀c, hca]
  have hV₀Z : zpowers a ⊔ zpowers f ≤ S ⊓ zStarIn J :=
    sup_le (zpowers_le.mpr haZ) (zpowers_le.mpr hfZ)
  have hSf : ∀ s ∈ S, s * f * s⁻¹ = f ∨ s * f * s⁻¹ = a * f := by
    intro s hs
    by_cases h : s * f * s⁻¹ = f
    · exact Or.inl h
    · right
      have hsfZ : s * f * s⁻¹ ∈ S ⊓ zStarIn J :=
        mem_inf.mpr ⟨mul_mem (mul_mem hs (mem_inf.mp hfZ).1) (inv_mem hs),
          conj_mem_zStarIn (hS.1 hs) (mem_inf.mp hfZ).2⟩
      have hsff : s * f * s⁻¹ * (s * f * s⁻¹) = 1 := by
        rw [show s * f * s⁻¹ * (s * f * s⁻¹) = s * (f * f) * s⁻¹ by group, hff]
        group
      have hsf1 : s * f * s⁻¹ ≠ 1 := fun h' => hf1 (by
        calc f = s⁻¹ * (s * f * s⁻¹) * s := by group
          _ = 1 := by rw [h']; group)
      have hsfa : s * f * s⁻¹ ≠ a := fun h' => hfa (by
        calc f = s⁻¹ * (s * f * s⁻¹) * s := by group
          _ = s⁻¹ * a * s := by rw [h']
          _ = a := by rw [mul_assoc, ← hcent s hs, inv_mul_cancel_left])
      exact eq_mul_of_card_omegaOne_le_four h4 haZ hfZ hsfZ haa hff hsff ha1 hf1 hsf1
        (Ne.symm hfa) (Ne.symm hsfa) (Ne.symm h)
  have hT2 : ∀ A : Subgroup G, A ≤ S → IsAbelianTwoOfRank 3 A →
      (∀ y ∈ A, ∀ v ∈ zpowers a ⊔ zpowers f, v * y = y * v) → wGroup A = W :=
    fun A hAS hA hAV => wGroup_eq_of_centralizes hGW
      (fun E hEJ hE8 => wGroup_eq_of_eight_le hConn hU hC hset hexp hnc hWx hNJ hEJ hE8)
      (fun t htS htt htV => exists_eight_le_centralizer hSqC hWit hJ hL34 hS hnc hV₀Z hV₀ hV₀4
        htS htt htV) hV₀ hV₀4 hAS hA hAV
  exact ⟨⟨f, hfZ, hff, hf1, hfa, hT2⟩, fun A hAS hA h16 =>
    wGroup_eq_of_sixteen hGW hT2 hcent hff hSf hAS hA h16⟩

theorem exists_conj_of_sixteen {S W : Subgroup G} {a : G}
    (hSa : IsSylowTwoIn S (centralizer ({a} : Set G)))
    (h16 : ∀ A : Subgroup G, A ≤ S → IsElemTwo A → Nat.card A = 16 → wGroup A = W) {d : G}
    (hda : ∃ g : G, d = g⁻¹ * a * g) {B : Subgroup G}
    (hB : B ≤ S ⊓ centralizer ({d} : Set G)) (hBe : IsElemTwo B) (hB16 : Nat.card B = 16) :
    ∃ m ∈ normalizer (W : Set G), d = m⁻¹ * a * m := by
  obtain ⟨g, hg⟩ := hda
  obtain ⟨h, hh, hhS⟩ := exists_conj_eq_of_isSylowTwoIn hSa (isPGroup_of_isSylowTwoIn hSa) hg
  have hBh : B.map (MulAut.conj h⁻¹).toMonoidHom ≤ S := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 := hhS y (hB hy)
    simpa [MulAut.conj_apply] using h1
  have hW1 := h16 B (hB.trans inf_le_left) hBe hB16
  have hW2 := h16 _ hBh (hBe.map_conj h⁻¹)
    (by rw [card_map_of_injective (MulAut.conj h⁻¹).injective, hB16])
  refine ⟨h⁻¹, inv_mem (mem_normalizer_of_wGroup_eq hW1 hW2), ?_⟩
  rw [inv_inv, ← hh]
  group

end CFSG.ComponentClassification.GrSLit.GrS4

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.ComponentClassification.GrSLit.L34Facts

theorem l34Lemma46FusionStep_of_facts
    (hRank : L34CenterRankFact) (hSqC : L34SquareCenterFact) (hWit : L34OuterWitnessFact)
    (hConn : L34EightsConnectedFact) (hU : L34UnbalancingUnitaryStep)
    (hC : L34UnitaryCentralizerFact) : L34Lemma46FusionStep := by
  intro G _ _ a x J S A hset hcent hZ hrun hn3 hexp hnc W hW hWodd hWx hNJ hMO hNS hSyl b hbS
    hba hr
  obtain ⟨hbase, hU3, hL34, -, hS, haS, hxS⟩ := id hset
  have hJa : J ≤ centralizer ({a} : Set G) := hU3.2.2.2.1
  have hJ : ⁅J, J⁆ = J := GSThmB.commutator_eq_self_of_isPComponent hJa hU3.2.2.2.2.1
  have hS2 : IsPGroup 2 S := GrS4.isPGroup_of_isSylowTwoIn hS
  have hP : IsSylowTwoIn (S ⊓ J) J := GrS4.isSylowTwoIn_inf hS
  have ha2 : orderOf a = 2 := hU3.1
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have hZne : S ⊓ zStarIn J ≠ ⊥ := by
    intro h
    obtain ⟨z, hz, hzz⟩ := GrS4.exists_sq_ne_one_of_exponent_eq_four hexp
    rw [h, mem_bot] at hz
    rw [hz, one_mul] at hzz
    exact hzz rfl
  have haZ : a ∈ S ⊓ zStarIn J := hZ hZne
  obtain ⟨-, h16⟩ := GrS4.wGroup_facts_of_setting hRank hSqC hWit hConn hU hC hset hcent haZ
    hexp hnc hWx hNJ
  have hSa : IsSylowTwoIn S (centralizer ({a} : Set G)) :=
    GrS4.isSylowTwoIn_of_le_of_sylow hSyl fun s hs =>
      mem_centralizer_singleton_iff.mpr (hcent s hs)
  obtain ⟨g, hg⟩ := hba
  have hbb : b * b = 1 := by
    rw [hg, show g⁻¹ * a * g * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g by group, haa]
    group
  by_cases hbJ : b ∈ J
  swap
  ·
    obtain ⟨F, hF, hFe, hF8⟩ := exists_isElemTwo_of_three_le_pRank hr
    obtain ⟨E, hEF, hE8⟩ := exists_le_card_eight hFe.isPGroup hF8
    have hES : E ≤ S ⊓ J ⊓ centralizer ({b} : Set G) := hEF.trans hF
    have hbE : b ∉ E := fun h => hbJ (mem_inf.mp (mem_inf.mp (hES h)).1).2
    obtain ⟨hAe, hAc⟩ := GrS4.isElemTwo_sup_zpowers (hFe.mono hEF) hbb hbE fun e he =>
      mem_centralizer_singleton_iff.mp (mem_inf.mp (hES he)).2
    refine GrS4.exists_conj_of_sixteen hSa h16 ⟨g, hg⟩ (sup_le (fun e he => ?_)
      (zpowers_le.mpr (mem_inf.mpr ⟨hbS, mem_centralizer_singleton_iff.mpr rfl⟩))) hAe
      (by rw [hAc, hE8])
    exact mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp (hES he)).1).1, (mem_inf.mp (hES he)).2⟩
  have hx2 : x * x = 1 := by rw [← pow_two, ← hU3.2.1, pow_orderOf_eq_one]
  have hxU : IsL34Unitary J x := hU G a x J hU3 hL34
  have hxP : x ∈ normalizer ((S ⊓ J : Subgroup G) : Set G) :=
    GrS4.inf_mem_normalizer (le_normalizer hxS) (hS.1 hxS)
  have hZP : S ⊓ J ⊓ zStarIn J = S ⊓ zStarIn J := by
    rw [inf_assoc, inf_of_le_right (show zStarIn J ≤ J from map_subtype_le _)]
  obtain ⟨hinvZ, h8, -, -, -, hel, -, -⟩ := hC G J (S ⊓ J) x hJ hL34 hxU hP hxP
  set R : Subgroup G := S ⊓ J ⊓ centralizer ({x} : Set G) with hR
  have hRe : IsElemTwo R := hel (by rwa [hZP])
  have hxR : x ∉ R := fun h => hxU.2.2.1 (mem_sup_left (mem_inf.mp (mem_inf.mp h).1).2)
  obtain ⟨hBe, hBc⟩ := GrS4.isElemTwo_sup_zpowers hRe hx2 hxR fun e he =>
    mem_centralizer_singleton_iff.mp (mem_inf.mp he).2
  have hB16 : Nat.card ↥(R ⊔ zpowers x) = 16 := by rw [hBc, h8]
  have hBS : R ⊔ zpowers x ≤ S :=
    sup_le (inf_le_left.trans inf_le_left) (zpowers_le.mpr hxS)
  have hBd : ∀ d ∈ R, R ⊔ zpowers x ≤ S ⊓ centralizer ({d} : Set G) := fun d hd =>
    le_inf hBS (sup_le (fun e he => mem_centralizer_singleton_iff.mpr (hRe.1 e he d hd))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp (mem_inf.mp hd).2).symm)))
  have hZR : ∀ v ∈ S ⊓ zStarIn J, v * v = 1 → v ∈ R := fun v hv hvv => by
    have hvP : v ∈ S ⊓ J := mem_inf.mpr ⟨(mem_inf.mp hv).1, map_subtype_le _ (mem_inf.mp hv).2⟩
    have h1 := hinvZ v (by rw [hZP]; exact hv)
    refine mem_inf.mpr ⟨hvP, mem_centralizer_singleton_iff.mpr ?_⟩
    calc v * x = x * (x⁻¹ * v * x) := by group
      _ = x * v := by rw [h1, inv_eq_of_mul_eq_one_right hvv]
  have hbP : b ∈ S ⊓ J := mem_inf.mpr ⟨hbS, hbJ⟩
  by_cases hbZ : b ∈ zStarIn J
  · exact GrS4.exists_conj_of_sixteen hSa h16 ⟨g, hg⟩
      (hBd b (hZR b (mem_inf.mpr ⟨hbS, hbZ⟩) hbb)) hBe hB16
  obtain ⟨w, hwR, hwZ⟩ : ∃ w ∈ R, w ∉ zStarIn J := by
    by_contra hno
    push Not at hno
    have hRle : R ≤ omegaOne (S ⊓ zStarIn J) := fun r hr =>
      subset_closure ⟨mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hr).1).1, hno r hr⟩, hRe.2 r hr⟩
    have h1 := card_le_of_le hRle
    have h2 := hRank G J (S ⊓ J) hJ hL34 hP
    rw [hZP] at h2
    omega
  have hwP : w ∈ S ⊓ J := (mem_inf.mp hwR).1
  have hww : w * w = 1 := hRe.2 w hwR
  obtain ⟨j, hj⟩ := GrS4.exists_conj_jq_mem_center hL34 hbJ (mem_inf.mp hwP).2 hbb hww hbZ hwZ
  obtain ⟨z, hzP, hzJ, hzj⟩ := exists_mem_of_mem_center hP hj
  have hzZ : z ∈ S ⊓ zStarIn J :=
    mem_inf.mpr ⟨(mem_inf.mp hzP).1, (mem_zStarIn_iff hzJ).mpr (hzj ▸ hj)⟩
  set b' : G := (j : G)⁻¹ * b * j with hb'
  have hb'J : b' ∈ J := mul_mem (mul_mem (inv_mem j.2) hbJ) j.2
  have hwzP : w * z ∈ S ⊓ J := mul_mem hwP hzP
  have hjq : jq J ⟨b', hb'J⟩ = jq J ⟨w * z, (mem_inf.mp hwzP).2⟩ := by
    have e1 : (⟨w * z, (mem_inf.mp hwzP).2⟩ : J) = ⟨w, (mem_inf.mp hwP).2⟩ * ⟨z, hzJ⟩ := rfl
    have e2 : (⟨b', hb'J⟩ : J) = j⁻¹ * ⟨b, hbJ⟩ * j := rfl
    rw [e1, map_mul, hzj, e2, mul_inv_cancel_left]
  have hzK : z ∈ coreActionKernel J := by
    have h : zStarIn J = J ⊓ coreActionKernel J := GSThmB.map_fusionZStar_eq J
    have := (mem_inf.mp hzZ).2
    rw [h] at this
    exact (mem_inf.mp this).2
  have hwz : w * z = z * w := (GrS4.mul_comm_of_mem_coreActionKernel hS2 (mem_inf.mp hzP).1 hzK
    (mem_inf.mp hwP).1 (mem_inf.mp hwP).2).symm
  have hwzwz : w * z * (w * z) = 1 := by
    refine eq_one_of_jq_eq_one hP.1 (hS2.to_le inf_le_left) (mul_mem hwzP hwzP) ?_
    have e1 : (⟨w * z * (w * z), hP.1 (mul_mem hwzP hwzP)⟩ : J) =
        ⟨w * z, (mem_inf.mp hwzP).2⟩ * ⟨w * z, (mem_inf.mp hwzP).2⟩ := rfl
    have e2 : (⟨b', hb'J⟩ : J) * ⟨b', hb'J⟩ = 1 := Subtype.ext (by
      show (j : G)⁻¹ * b * j * ((j : G)⁻¹ * b * j) = 1
      rw [show (j : G)⁻¹ * b * j * ((j : G)⁻¹ * b * j) = (j : G)⁻¹ * (b * b) * j by group, hbb]
      group)
    rw [e1, map_mul, ← hjq, ← map_mul, e2, map_one]
  have hzz : z * z = 1 := by
    calc z * z = w * w * (z * z) := by rw [hww, one_mul]
      _ = w * z * (w * z) := by
          rw [mul_assoc w z, ← mul_assoc z w z, ← hwz]; group
      _ = 1 := hwzwz
  set d : G := w * z with hd
  have hdR : d ∈ R := mul_mem hwR (hZR z hzZ hzz)
  have hb'b' : b' * b' = 1 := by
    rw [hb', show (j : G)⁻¹ * b * j * ((j : G)⁻¹ * b * j) = (j : G)⁻¹ * (b * b) * j by group, hbb]
    group
  have hO : d * b' ∈ oddIn J := by
    have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hwzwz
    have h1 : jq J ⟨d * b', mul_mem (mem_inf.mp hwzP).2 hb'J⟩ = 1 := by
      have e1 : (⟨d * b', mul_mem (mem_inf.mp hwzP).2 hb'J⟩ : J) =
          (⟨d, (mem_inf.mp hwzP).2⟩ : J)⁻¹ * ⟨b', hb'J⟩ := Subtype.ext (by
        show d * b' = d⁻¹ * b'
        rw [hdi])
      rw [e1, map_mul, map_inv, hjq, inv_mul_cancel]
    exact (mem_oddIn_iff _).mpr h1
  obtain ⟨k, hk⟩ := CFSG.ClassicalInvolution.Asc77.T3Core.exists_conj_of_mul_mem_odd hwzwz hb'b'
    ((odd_card_map_pPrimeCore J).of_dvd_nat ((oddIn J).orderOf_dvd_natCard hO))
  set o : G := (d * b') ^ k with ho
  have hoJ : o ∈ J := map_subtype_le _ (pow_mem hO k)
  set m₀ : G := (j : G) * o with hm₀
  have hm₀J : m₀ ∈ J := mul_mem j.2 hoJ
  have hbd : b = m₀ * d * m₀⁻¹ := by
    rw [hm₀, show (j : G) * o * d * ((j : G) * o)⁻¹ = (j : G) * (o * d * o⁻¹) * (j : G)⁻¹ by
      group, hk, hb']
    group
  obtain ⟨m, hm, hdm⟩ := GrS4.exists_conj_of_sixteen hSa h16
    ⟨g * m₀, by rw [show d = m₀⁻¹ * b * m₀ by rw [hbd]; group, hg]; group⟩ (hBd d hdR) hBe hB16
  have hm₀M : m₀ ∈ normalizer (W : Set G) := hNJ (le_normalizer hm₀J)
  refine ⟨m * m₀⁻¹, mul_mem hm (inv_mem hm₀M), ?_⟩
  rw [hbd, hdm]
  group

end CFSG.ComponentClassification.GrSLit

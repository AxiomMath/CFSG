module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.Defs
import CFSG.GroupTheory.CentralizerSup

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.AGLEmbedding
open CFSG.AGLEmbeddingD2 (NoXBlockFor)

section Abstract

variable {X : Type} [Group X] [Finite X]

private theorem inv_mul_conj_mem_centralizer_fitting (hX : CFSG.pCore 2 X = ⊥)
    {T : Subgroup X} (hTO : CFSG.pPrimeCore 2 X ≤
      Subgroup.centralizer (T : Set X)) {c t : X} (ht : t ∈ T) :
    t⁻¹ * (c * t * c⁻¹) ∈ Subgroup.centralizer
      (CFSG.ComponentClassification.Fitting.subgroup X : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  have hfO : f ∈ CFSG.pPrimeCore 2 X := fitting_le_pPrimeCore_two hX hf
  have htf : t * f = f * t := (Subgroup.mem_centralizer_iff.mp (hTO hfO)) t ht
  have hcf : c⁻¹ * f * c ∈ CFSG.ComponentClassification.Fitting.subgroup X :=
    (CFSG.ComponentClassification.Fitting.normal X).conj_mem' f hf c
  have hcfO : c⁻¹ * f * c ∈ CFSG.pPrimeCore 2 X := fitting_le_pPrimeCore_two hX hcf
  have htc : t * (c⁻¹ * f * c) = (c⁻¹ * f * c) * t :=
    (Subgroup.mem_centralizer_iff.mp (hTO hcfO)) t ht
  have htinvt : Commute t⁻¹ f := (show Commute t f from htf).inv_left
  have huconj : (t⁻¹ * (c * t * c⁻¹)) * f * (t⁻¹ * (c * t * c⁻¹))⁻¹ = f := by
    calc
      (t⁻¹ * (c * t * c⁻¹)) * f * (t⁻¹ * (c * t * c⁻¹))⁻¹
          = t⁻¹ * (c * (t * (c⁻¹ * f * c) * t⁻¹) * c⁻¹) * t := by group
      _ = t⁻¹ * (c * ((c⁻¹ * f * c) * t * t⁻¹) * c⁻¹) * t := by rw [htc]
      _ = t⁻¹ * (c * (c⁻¹ * f * c) * c⁻¹) * t := by group
      _ = t⁻¹ * f * t := by group
      _ = f := by rw [htinvt.eq]; group
  exact (mul_inv_eq_iff_eq_mul.mp huconj).symm

omit [Finite X] in
private theorem inv_mul_conj_mem_centralizer_of_mem_block {T : Subgroup X}
    {𝓑 : Set (Subgroup X)} {B : Subgroup X} (hB : B ∈ 𝓑)
    (hTB : ∀ B ∈ 𝓑, T ≤ Subgroup.normalizer (B : Set X))
    {c : X} (hc : ∀ B ∈ 𝓑, c ∈ Subgroup.centralizer (B : Set X))
    {t : X} (ht : t ∈ T) :
    t⁻¹ * (c * t * c⁻¹) ∈ Subgroup.centralizer (B : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have hcB : c ∈ Subgroup.centralizer (B : Set X) := hc B hB
  have hce : e * c = c * e := Subgroup.mem_centralizer_iff.mp hcB e he
  have htN : t ∈ Subgroup.normalizer (B : Set X) := hTB B hB ht
  have hte : t * e * t⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp htN e).mp he
  have hcte_comm : (t * e * t⁻¹) * c = c * (t * e * t⁻¹) :=
    Subgroup.mem_centralizer_iff.mp hcB (t * e * t⁻¹) hte
  have hceinv : c⁻¹ * e * c = e := by
    rw [mul_assoc, hce]
    group
  have hcte : c * (t * e * t⁻¹) * c⁻¹ = t * e * t⁻¹ := by
    rw [← hcte_comm]; group
  have huconj : (t⁻¹ * (c * t * c⁻¹)) * e * (t⁻¹ * (c * t * c⁻¹))⁻¹ = e := by
    calc
      (t⁻¹ * (c * t * c⁻¹)) * e * (t⁻¹ * (c * t * c⁻¹))⁻¹
          = t⁻¹ * (c * (t * (c⁻¹ * e * c) * t⁻¹) * c⁻¹) * t := by group
      _ = t⁻¹ * (c * (t * e * t⁻¹) * c⁻¹) * t := by rw [hceinv]
      _ = t⁻¹ * (t * e * t⁻¹) * t := by rw [hcte]
      _ = e := by group
  exact (mul_inv_eq_iff_eq_mul.mp huconj).symm

omit [Finite X] in
private theorem inv_mul_conj_mem_centralizer_of_not_mem_block {T : Subgroup X}
    {𝓑 : Set (Subgroup X)} {E : Subgroup X}
    (hE : IsComponentOf E ⊤) (hEB : E ∉ 𝓑)
    (hTE : ∀ E : Subgroup X, IsComponentOf E ⊤ → E ∉ 𝓑 →
      T ≤ Subgroup.centralizer (E : Set X))
    {c : X} (hc : ∀ B ∈ 𝓑, c ∈ Subgroup.centralizer (B : Set X))
    {t : X} (ht : t ∈ T) :
    t⁻¹ * (c * t * c⁻¹) ∈ Subgroup.centralizer (E : Set X) := by
  let B : Subgroup X := E.map (MulAut.conj c⁻¹).toMonoidHom
  have hB : IsComponentOf B ⊤ :=
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj c⁻¹) E).mpr hE
  have hBnot : B ∉ 𝓑 := by
    intro hBmem
    have hcn : c ∈ Subgroup.normalizer (B : Set X) :=
      Subgroup.centralizer_le_normalizer _ (hc B hBmem)
    have hBmap : B.map (MulAut.conj c).toMonoidHom = B :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hcn
    have hcomp : (MulAut.conj c).toMonoidHom.comp (MulAut.conj c⁻¹).toMonoidHom =
        MonoidHom.id X := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
    have hEq : B = E := by
      have h1 : B.map (MulAut.conj c).toMonoidHom = E := by
        rw [show B = E.map (MulAut.conj c⁻¹).toMonoidHom from rfl, Subgroup.map_map, hcomp,
          Subgroup.map_id]
      rw [← hBmap, h1]
    exact hEB (hEq ▸ hBmem)
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have hbB : c⁻¹ * e * c ∈ B := by
    have := Subgroup.mem_map_of_mem (MulAut.conj c⁻¹).toMonoidHom (K := E) he
    simpa [B, MulAut.conj_apply] using this
  have htb : t * (c⁻¹ * e * c) = (c⁻¹ * e * c) * t :=
    (Subgroup.mem_centralizer_iff.mp ((hTE B hB hBnot) ht) (c⁻¹ * e * c) hbB).symm
  have hte_comm : e * t = t * e :=
    Subgroup.mem_centralizer_iff.mp (hTE E hE hEB ht) e he
  have huconj : (t⁻¹ * (c * t * c⁻¹)) * e * (t⁻¹ * (c * t * c⁻¹))⁻¹ = e := by
    calc
      (t⁻¹ * (c * t * c⁻¹)) * e * (t⁻¹ * (c * t * c⁻¹))⁻¹
          = t⁻¹ * (c * (t * (c⁻¹ * e * c) * t⁻¹) * c⁻¹) * t := by group
      _ = t⁻¹ * (c * ((c⁻¹ * e * c) * t * t⁻¹) * c⁻¹) * t := by rw [htb]
      _ = t⁻¹ * (c * (c⁻¹ * e * c) * c⁻¹) * t := by group
      _ = t⁻¹ * e * t := by group
      _ = e := by
        calc t⁻¹ * e * t = t⁻¹ * (e * t) := by group
          _ = t⁻¹ * (t * e) := by rw [hte_comm]
          _ = e := by group
  exact (mul_inv_eq_iff_eq_mul.mp huconj).symm

theorem inv_mul_conj_mem_centralizer_generalizedFitting (hX : CFSG.pCore 2 X = ⊥)
    {T : Subgroup X} {𝓑 : Set (Subgroup X)}
    (hTO : CFSG.pPrimeCore 2 X ≤ Subgroup.centralizer (T : Set X))
    (hTB : ∀ B ∈ 𝓑, T ≤ Subgroup.normalizer (B : Set X))
    (hTE : ∀ E : Subgroup X, IsComponentOf E ⊤ → E ∉ 𝓑 →
      T ≤ Subgroup.centralizer (E : Set X))
    {c : X} (hc : ∀ B ∈ 𝓑, c ∈ Subgroup.centralizer (B : Set X)) {t : X} (ht : t ∈ T) :
    t⁻¹ * (c * t * c⁻¹) ∈ Subgroup.centralizer
      (CFSG.ComponentClassification.GeneralizedFitting.subgroup X : Set X) := by
  let u := t⁻¹ * (c * t * c⁻¹)
  have hF : u ∈ Subgroup.centralizer
      (CFSG.ComponentClassification.Fitting.subgroup X : Set X) :=
    inv_mul_conj_mem_centralizer_fitting hX hTO ht
  have hL : u ∈ Subgroup.centralizer
      (CFSG.ComponentClassification.Layer.subgroup X : Set X) := by
    rw [CFSG.ComponentClassification.Layer.subgroup.eq_sSup, sSup_eq_iSup']
    refine Subgroup.zpowers_le.mp (CFSG.subgroup_le_centralizer_iSup_of_le_centralizer
      (P := Subgroup.zpowers u)
      (S := fun E : {E : Subgroup X // IsComponentOf E ⊤} => (E : Subgroup X)) ?_)
    intro E
    exact Subgroup.zpowers_le.mpr (by
      by_cases hEB : E.1 ∈ 𝓑
      · exact inv_mul_conj_mem_centralizer_of_mem_block hEB hTB hc ht
      · exact inv_mul_conj_mem_centralizer_of_not_mem_block E.2 hEB hTE hc ht)
  rw [CFSG.ComponentClassification.GeneralizedFitting.subgroup.eq_sup, CFSG.centralizer_sup_eq]
  exact ⟨hF, hL⟩

theorem eq_one_of_mem_centralizer_generalizedFitting (hX : CFSG.pCore 2 X = ⊥) {t u : X}
    (hu : u ∈ Subgroup.centralizer
      (CFSG.ComponentClassification.GeneralizedFitting.subgroup X : Set X))
    (ht : t ∈ Subgroup.centralizer (CFSG.pPrimeCore 2 X : Set X))
    (ht2 : IsPGroup 2 (Subgroup.zpowers t)) (htu : IsPGroup 2 (Subgroup.zpowers (t * u))) :
    u = 1 := by
  have huF : u ∈ CFSG.ComponentClassification.Fitting.subgroup X :=
    CFSG.ComponentClassification.GeneralizedFitting.centralizer_le_fitting X hu
  have huO : u ∈ CFSG.pPrimeCore 2 X := fitting_le_pPrimeCore_two hX huF
  have hcomm : Commute t u := (Subgroup.mem_centralizer_iff.mp ht u huO).symm
  obtain ⟨k, hk⟩ : ∃ k, orderOf t ∣ 2 ^ k := by
    obtain ⟨k, hk⟩ := isPGroup_iff_orderOf_dvd_pow.mp ht2 ⟨t, Subgroup.mem_zpowers t⟩
    exact ⟨k, Subgroup.orderOf_mk t (Subgroup.mem_zpowers t) ▸ hk⟩
  obtain ⟨l, hl⟩ : ∃ l, orderOf (t * u) ∣ 2 ^ l := by
    obtain ⟨l, hl⟩ := isPGroup_iff_orderOf_dvd_pow.mp htu
      ⟨t * u, Subgroup.mem_zpowers (t * u)⟩
    exact ⟨l, Subgroup.orderOf_mk (t * u) (Subgroup.mem_zpowers (t * u)) ▸ hl⟩
  have hcomm' : Commute t⁻¹ (t * u) := by
    have h1 : Commute t⁻¹ (u * t) :=
      hcomm.inv_left.mul_right (Commute.refl t).inv_left
    simpa [hcomm.eq] using h1
  have hu2 : orderOf u ∣ 2 ^ max k l := by
    have hprod : orderOf (t⁻¹ * (t * u)) ∣
        (orderOf t⁻¹).lcm (orderOf (t * u)) := hcomm'.orderOf_mul_dvd_lcm
    rw [show t⁻¹ * (t * u) = u by group] at hprod
    refine hprod.trans (Nat.lcm_dvd ?_ ?_)
    · rw [orderOf_inv]
      exact hk.trans (pow_dvd_pow 2 (le_max_left k l))
    · exact hl.trans (pow_dvd_pow 2 (le_max_right k l))
  have hcard : orderOf u ∣ Nat.card (CFSG.pPrimeCore 2 X) :=
    Subgroup.orderOf_dvd_natCard (CFSG.pPrimeCore 2 X) huO
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (CFSG.pPrimeCore_coprime_card.pow_left (max k l)) hu2 hcard)

theorem centralizer_sSup_le_centralizer_of_isPGroup (hX : CFSG.pCore 2 X = ⊥)
    {T : Subgroup X} (hT : IsPGroup 2 T) {𝓑 : Set (Subgroup X)}
    (hTO : CFSG.pPrimeCore 2 X ≤ Subgroup.centralizer (T : Set X))
    (hTB : ∀ B ∈ 𝓑, T ≤ Subgroup.normalizer (B : Set X))
    (hTE : ∀ E : Subgroup X, IsComponentOf E ⊤ → E ∉ 𝓑 →
      T ≤ Subgroup.centralizer (E : Set X)) :
    Subgroup.centralizer ((sSup 𝓑 : Subgroup X) : Set X) ≤
      Subgroup.centralizer (T : Set X) := by
  intro c hc
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have hcB : ∀ B ∈ 𝓑, c ∈ Subgroup.centralizer (B : Set X) := fun B hB =>
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (le_sSup hB)) hc
  have ht2 : IsPGroup 2 (Subgroup.zpowers t) := hT.to_le (Subgroup.zpowers_le.mpr ht)
  have hct2 : IsPGroup 2 (Subgroup.zpowers (t * (t⁻¹ * (c * t * c⁻¹)))) := by
    rw [show t * (t⁻¹ * (c * t * c⁻¹)) = c * t * c⁻¹ by group]
    refine (hT.map (MulAut.conj c).toMonoidHom).to_le (Subgroup.zpowers_le.mpr ?_)
    exact ⟨t, ht, rfl⟩
  have hu := eq_one_of_mem_centralizer_generalizedFitting hX
    (inv_mul_conj_mem_centralizer_generalizedFitting hX hTO hTB hTE hcB ht)
    (Subgroup.le_centralizer_iff.mp hTO ht) ht2 hct2
  have h1 : t = c * t * c⁻¹ := inv_mul_eq_one.mp hu
  calc t * c = c * t * c⁻¹ * c := by rw [← h1]
    _ = c * t := by group

end Abstract

variable {G : Type} [Group G] [Finite G]

private theorem subgroupOf_sSup_image {M : Subgroup G} {U : Set (Subgroup G)}
    (hU : ∀ A ∈ U, A ≤ M) :
    (sSup U).subgroupOf M = sSup (U.image fun A : Subgroup G => A.subgroupOf M) := by
  classical
  obtain ⟨s, rfl⟩ := (Set.toFinite U).exists_finset_coe
  induction s using Finset.induction_on with
  | empty => simp
  | insert A s _ ih =>
      rw [Finset.coe_insert, sSup_insert, Set.image_insert_eq, sSup_insert]
      rw [Subgroup.subgroupOf_sup (hU A (Finset.mem_insert_self A s))
        (sSup_le fun B hB => hU B (Finset.mem_insert_of_mem hB))]
      rw [ih fun B hB => hU B (Finset.mem_insert_of_mem hB)]

theorem barM_jSub_eq_sSup_image (M H : Subgroup G) :
    barM M (jSub M H) = sSup (barM M '' weakBlockSet M H) := by
  have hM : ∀ L ∈ weakBlockSet M H, L ≤ M := fun L hL => hL.le
  have h1 : (sSup (weakBlockSet M H)).subgroupOf M =
      sSup ((weakBlockSet M H).image fun A : Subgroup G => A.subgroupOf M) :=
    subgroupOf_sSup_image hM
  rw [jSub, barM, h1, (Subgroup.gc_map_comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M)))
    |>.l_sSup_eq_sSup_image, Set.image_image]
  rfl

theorem barM_twoCore_le_centralizer_of_not_mem_image {M H : Subgroup G}
    {E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hE : IsComponentOf E ⊤)
    (hEB : E ∉ barM M '' weakBlockSet M H) :
    barM M (pCoreOf 2 H) ≤ Subgroup.centralizer (E : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  obtain ⟨L, hL, hbar⟩ := exists_isTwoPrimeComponent hE
  have hLS : L ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := by
    by_contra h
    exact hEB ⟨L, ⟨hL, h⟩, hbar⟩
  have hLE : E ≤ Subgroup.normalizer (barM M (pCoreOf 2 H) : Set _) :=
    hbar ▸ barM_le_normalizer_barM hLS
  have hS : IsPGroup 2 (barM M (pCoreOf 2 H)) :=
    ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H).comap_of_injective
      M.subtype M.subtype_injective).map _
  have hcomm : ⁅E, barM M (pCoreOf 2 H)⁆ = ⊥ :=
    commutator_eq_bot_of_le_normalizer hE hS hLE
  rw [Subgroup.commutator_comm] at hcomm
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm

theorem centralizer_barM_jSub_le_centralizer_barM_twoCore {M H : Subgroup G}
    (h : TwoLocalPhaseThree M H) (hK : CFSG.Open.IsKGroup ↥M) (h84 : Asc81bEightFour)
    (h86 : Asc81bEightSix) (hD2 : NoXBlockFor G) :
    Subgroup.centralizer (barM M (jSub M H) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
      Subgroup.centralizer (barM M (pCoreOf 2 H) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  rw [barM_jSub_eq_sSup_image]
  refine centralizer_sSup_le_centralizer_of_isPGroup (pCore_quotient_pCore_eq_bot' 2) ?_
    (h.oddCore_le_centralizer hK h84 hD2) ?_
    (fun E hE hEB => barM_twoCore_le_centralizer_of_not_mem_image hE hEB)
  · exact ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H).comap_of_injective
      M.subtype M.subtype_injective).map _
  · rintro B ⟨L, hL, rfl⟩
    exact barM_le_normalizer_barM (h.weakSBlock_asc81bHyp hK h86 hL).1

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end

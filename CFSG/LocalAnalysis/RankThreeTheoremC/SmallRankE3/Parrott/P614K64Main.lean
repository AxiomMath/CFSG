module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K278Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K64Rep
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K64Fixed

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open Subgroup CFSG.Quasithin CFSG.HardMathSupport.Solomon
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
open P614K64


theorem kFact64iii_of_l34 : KFact278L34 → KFact64iii := by
  intro h A _ _ X Q B U Y S hK hrk hQ hZ hBQ hB hB9 hUQ hU hU9 hBU hwc hYX hYne hU1 hQ2
    hcent hcore hSmax hYS
  obtain ⟨K, hKX, hKn, hKp, hKlt, hKmax, hcov, ⟨e⟩, hSidx⟩ :=
    h A X Q B U Y hK hrk hQ hZ hBQ hB hB9 hUQ hU hU9 hBU hwc hYX hYne hU1 hQ2
  rw [hcore] at hKlt hKmax hcov hSidx
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O : Subgroup A := pCoreOf 2 X with hOdef
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hOX : O ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hXO : X ≤ normalizer (O : Set A) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hQX : Q ≤ X := by
    obtain ⟨Q', hQ'⟩ := hQ
    rw [← hQ']
    exact map_subtype_le _
  have hOS : O ≤ S := pCoreOf_le_of_maxInv hSmax (hBQ.trans hQX)
  have hSX : S ≤ X := hSmax.1.1
  have hS2 : IsPGroup 2 S := hSmax.1.2.1
  have hidx : O.relIndex S ≤ 2 := hSidx S hSmax.1 hYS
  have hKO : K ≤ normalizer (O : Set A) := hKX.trans hXO
  by_contra hfail
  have hK' : ∀ Z₀ : Subgroup A, Z₀ ≤ S → Z₀ ≠ ⊥ → (Z₀.subgroupOf S).Characteristic →
      ¬ K ≤ normalizer (Z₀ : Set A) := by
    intro Z₀ hZS hZ1 hZc hKZ
    apply hfail
    haveI := hZc
    have hSZ : S ≤ normalizer (Z₀ : Set A) :=
      (normal_subgroupOf_iff_le_normalizer hZS).mp inferInstance
    refine ⟨Z₀, hZS, hZ1, hZc, hcov.trans (sup_le (sup_le le_sup_left ?_) ?_)⟩
    · exact le_sup_of_le_right (le_inf hKX hKZ)
    · exact le_sup_of_le_right (le_inf hOX (hOS.trans hSZ))
  have hX1 : X ≠ ⊥ := fun hX => hYne (le_antisymm hYX (by rw [hX]; exact bot_le))
  have hO1 : O ≠ ⊥ := by
    intro hO
    apply hX1
    rw [eq_bot_iff]
    intro x hx
    have hxC : x ∈ centralizer (O : Set A) := by
      rw [hO]
      exact mem_centralizer_iff.mpr fun g hg => by
        rw [show g = 1 from mem_bot.mp hg, one_mul, mul_one]
    have := hcent ⟨hx, hxC⟩
    rwa [hO] at this
  have hS1 : S ≠ ⊥ := fun hS => hO1 (le_bot_iff.mp (hS ▸ hOS))
  have hKS : ¬ K ≤ normalizer (S : Set A) := by
    refine hK' S le_rfl hS1 ?_
    rw [subgroupOf_self]
    infer_instance
  set V : Subgroup A := omegaOneCenterOf O with hVdef
  have hV : IsElemAbelian 2 V := isElemAbelian_omegaOneCenterOf O
  have hVO : V ≤ O := CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le O
  have hXV : X ≤ normalizer (V : Set A) := le_normalizer_omegaOneCenterOf hXO
  have hOV : O ≤ centralizer (V : Set A) := le_centralizer_omegaOneCenterOf O
  have hKV : K ≤ normalizer (V : Set A) := hKX.trans hXV
  have hZSV : omegaOneCenterOf S ≤ V := omegaOneCenterOf_le_omegaOneCenterOf hOS hSX hcent
  have hZS1 : omegaOneCenterOf S ≠ ⊥ :=
    CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hS2 hS1
  have hZSc := CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf S
  have hZSle : omegaOneCenterOf S ≤ S := CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le S
  have hKC : ¬ K ≤ centralizer (V : Set A) := fun hKC =>
    hK' _ hZSle hZS1 hZSc (hKC.trans ((centralizer_le (SetLike.coe_subset_coe.mpr hZSV)).trans
      (centralizer_le_normalizer _)))
  have hSCV : S ⊓ centralizer (V : Set A) = O := by
    rcases eq_or_eq_of_relIndex_le_two (le_inf hOS hOV) inf_le_left hidx with h | h
    · exact h
    · exfalso
      have hSC : S ≤ centralizer (V : Set A) := h.ge.trans inf_le_right
      have hZeq : omegaOneCenterOf S = V :=
        le_antisymm hZSV (le_omegaOneCenterOf (hVO.trans hOS) hV hSC)
      exact hK' _ hZSle hZS1 hZSc (by rw [hZeq]; exact hKV)
  obtain ⟨A₀, hA₀, hA₀O⟩ := exists_offender hOS hXO hKX fun hKJ =>
    hK' _ (thompsonJ_le_self S) (CFSG.QuasithinUnique.Setup.thompsonJ_ne_bot hS2 hS1)
      (CFSG.QuasithinUnique.Setup.characteristic_thompsonJ S) hKJ
  obtain ⟨a, haA, haO⟩ := SetLike.not_le_iff_exists.mp hA₀O
  have haS : a ∈ S := hA₀.1 haA
  have haX : a ∈ X := hSX haS
  have haC : a ∉ centralizer (V : Set A) := fun h => haO (hSCV ▸ ⟨haS, h⟩)
  have ha2 : a * a = 1 := by
    have := hA₀.2.1.2 a haA
    rwa [pow_two] at this
  have ha2' : a * a ∈ centralizer (V : Set A) := by
    rw [ha2]
    exact one_mem _
  have haV : a ∈ normalizer (V : Set A) := hXV haX
  have haK : a ∈ normalizer (K : Set A) := hKn haX
  have hidxA : ∀ W : Subgroup A, O ≤ centralizer (W : Set A) →
      (A₀ ⊓ centralizer (W : Set A)).relIndex A₀ ≤ 2 := by
    intro W hOW
    haveI : (A₀ ⊓ O).IsFiniteRelIndex A₀ := isFiniteRelIndex_of_finiteIndex
    haveI : O.IsFiniteRelIndex S := isFiniteRelIndex_of_finiteIndex
    calc (A₀ ⊓ centralizer (W : Set A)).relIndex A₀ ≤ (A₀ ⊓ O).relIndex A₀ :=
          relIndex_le_of_le_left (inf_le_inf_left _ hOW) relIndex_ne_zero
      _ = O.relIndex A₀ := inf_relIndex_left A₀ O
      _ ≤ O.relIndex S := relIndex_le_of_le_right hA₀.1 relIndex_ne_zero
      _ ≤ 2 := hidx
  have hτ := isTransvection_convI hV haV haC
    (card_commV_le_two hA₀ haA hV (hVO.trans hOS) haV (hidxA V hOV))
  have hKC' : K ⊓ centralizer (V : Set A) = K ⊓ O := inf_centralizer_eq hKV hOV hKC hKmax
  have hτc : ∃ n ∈ autI hV K, convI hV ⟨a, haV⟩ * n ≠ n * convI hV ⟨a, haV⟩ := by
    by_contra hall
    push Not at hall
    refine hKS (le_normalizer_of_index_two hOS hidx haS haO hKO fun k hk => ?_)
    have hkV : k ∈ normalizer (V : Set A) := hKV hk
    have h1 := hall _ (convI_mem_autI hV hk hkV)
    have h2 : a * k * a⁻¹ * k⁻¹ ∈ K ⊓ centralizer (V : Set A) := by
      refine ⟨K.mul_mem ((mem_normalizer_iff.mp haK k).mp hk) (K.inv_mem hk), ?_⟩
      have h3 : convI hV (⟨a, haV⟩ * ⟨k, hkV⟩ * ⟨a, haV⟩⁻¹ * ⟨k, hkV⟩⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
        group
      exact (convI_eq_one_iff hV _).mp h3
    rw [hKC'] at h2
    have h4 := O.inv_mem h2.2
    have e4 : (a * k * a⁻¹ * k⁻¹)⁻¹ = k * a * k⁻¹ * a⁻¹ := by group
    rwa [e4] at h4
  by_cases hout : ∀ n ∈ autI hV K, (∀ m ∈ autI hV K,
      n * convI hV ⟨a, haV⟩ * m = m * (n * convI hV ⟨a, haV⟩)) → n * convI hV ⟨a, haV⟩ = 1
  · exact false_of_module hO2 hKO hKlt hKmax e hV hKV hOV hKC haV haK ha2' hτ hτc hout
  push Not at hout
  obtain ⟨n, hn, hnc, -⟩ := hout
  obtain ⟨g, hgK, rfl⟩ := (mem_autI hV).mp hn
  have hcV : (g : A) * a ∈ normalizer (V : Set A) := mul_mem g.2 haV
  have hcconv : convI hV ⟨(g : A) * a, hcV⟩ = convI hV g * convI hV ⟨a, haV⟩ := by
    rw [← map_mul]
    rfl
  obtain ⟨hs, hc, hi⟩ := autI_facts hO2 hKO hKlt hKmax e hV hKV hOV hKC
  haveI := hs
  have hz := center_eq_bot_of_l34 hc hi
  have hcK : ∀ k ∈ K, (g : A) * a * k * ((g : A) * a)⁻¹ * k⁻¹ ∈ centralizer (V : Set A) := by
    intro k hk
    have hkV : k ∈ normalizer (V : Set A) := hKV hk
    have h1 := hnc _ (convI_mem_autI hV hk hkV)
    have h3 : convI hV (⟨(g : A) * a, hcV⟩ * ⟨k, hkV⟩ * ⟨(g : A) * a, hcV⟩⁻¹ * ⟨k, hkV⟩⁻¹) =
        1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcconv, h1]
      group
    exact (convI_eq_one_iff hV _).mp h3
  have hc2 : (g : A) * a * ((g : A) * a) ∈ centralizer (V : Set A) := by
    have h1 := mul_self_eq_one_of_central (convI_mul_self hV haV ha2') hn hz hnc
    rw [← hcconv, ← map_mul] at h1
    exact (convI_eq_one_iff hV _).mp h1
  set c : A := (g : A) * a with hcdef
  set Uf : Subgroup A := V ⊓ centralizer ({c} : Set A) with hUfdef
  have hUe : IsElemAbelian 2 Uf := B2F.isElemAbelian_mono inf_le_left hV
  have hKU : K ≤ normalizer (Uf : Set A) := le_normalizer_fixed hKV hcK
  have hcU : c ∈ centralizer (Uf : Set A) :=
    mem_centralizer_iff.mpr fun u hu => mem_centralizer_singleton_iff.mp hu.2
  have hcUN : c ∈ normalizer (Uf : Set A) := centralizer_le_normalizer _ hcU
  have hk0U : (g : A)⁻¹ ∈ normalizer (Uf : Set A) := hKU (K.inv_mem hgK)
  have haeq : a = (g : A)⁻¹ * c := by
    rw [hcdef]
    group
  have haU : a ∈ normalizer (Uf : Set A) := by
    rw [haeq]
    exact mul_mem hk0U hcUN
  have hOU : O ≤ centralizer (Uf : Set A) :=
    hOV.trans (centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left))
  have hKCU : ¬ K ≤ centralizer (Uf : Set A) :=
    not_le_centralizer_fixed hV hKV hcV hcK hc2 hKp hKC
  have hKCU' := inf_centralizer_eq hKU hOU hKCU hKmax
  have haCU : a ∉ centralizer (Uf : Set A) := by
    intro haC'
    have hk0 : (g : A) ∈ K ⊓ centralizer (Uf : Set A) := by
      refine ⟨hgK, ?_⟩
      have e1 : (g : A) = c * a⁻¹ := by
        rw [hcdef]
        group
      rw [e1]
      exact Subgroup.mul_mem _ hcU (Subgroup.inv_mem _ haC')
    rw [hKCU'] at hk0
    have hg1 : convI hV g = 1 := (convI_eq_one_iff hV g).mpr (hOV hk0.2)
    obtain ⟨m, hm, hm'⟩ := hτc
    apply hm'
    have h1 := hnc m hm
    simp only [hg1, one_mul] at h1
    exact h1
  have hτU := isTransvection_convI hUe haU haCU
    (card_commV_le_two hA₀ haA hUe (inf_le_left.trans (hVO.trans hOS)) haU (hidxA Uf hOU))
  have hτUK : convI hUe ⟨a, haU⟩ ∈ autI hUe K := by
    have e1 : (⟨a, haU⟩ : normalizer (Uf : Set A)) = ⟨(g : A)⁻¹, hk0U⟩ * ⟨c, hcUN⟩ :=
      Subtype.ext haeq
    rw [e1, map_mul, (convI_eq_one_iff hUe ⟨c, hcUN⟩).mpr hcU, mul_one]
    exact convI_mem_autI hUe (K.inv_mem hgK) hk0U
  exact false_of_module_of_mem hO2 hKO hKlt hKmax e hUe hKU hOU hKCU haU haK
    (by rw [ha2]; exact one_mem _) hτU hτUK

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

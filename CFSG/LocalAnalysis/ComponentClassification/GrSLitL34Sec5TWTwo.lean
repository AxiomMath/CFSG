module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5TWOne
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWNonW
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real
  CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso CFSG.LieType.Multipliers.L34

variable {G : Type} [Group G] [Finite G]

theorem exists_fixed_conj_of_odd {T : Subgroup G} (hT : IsPGroup 2 T) {Ω : Set G}
    (hΩ : ∀ t ∈ T, ∀ y ∈ Ω, t * y * t⁻¹ ∈ Ω) (hodd : Odd (Nat.card Ω)) :
    ∃ y ∈ Ω, ∀ t ∈ T, t * y * t⁻¹ = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let act : MulAction T Ω :=
    { smul := fun t y => ⟨(t : G) * y * (t : G)⁻¹, hΩ t t.2 y y.2⟩
      one_smul := fun y => Subtype.ext (show ((1 : T) : G) * y * ((1 : T) : G)⁻¹ = y by
        rw [OneMemClass.coe_one, one_mul, inv_one, mul_one])
      mul_smul := fun t s y => Subtype.ext (show ((t * s : T) : G) * y * ((t * s : T) : G)⁻¹ =
          (t : G) * ((s : G) * y * (s : G)⁻¹) * (t : G)⁻¹ by
        rw [Subgroup.coe_mul]
        group) }
  have hmod := hT.card_modEq_card_fixedPoints Ω
  have hne : (MulAction.fixedPoints T Ω).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h] at hmod
    have h0 : Nat.card (∅ : Set Ω) = 0 := by simp
    rw [h0] at hmod
    have := Nat.odd_iff.mp hodd
    rw [Nat.ModEq] at hmod
    omega
  obtain ⟨⟨y, hy⟩, hfix⟩ := hne
  refine ⟨y, hy, fun t ht => ?_⟩
  have := hfix ⟨t, ht⟩
  exact congrArg Subtype.val this


theorem ncard_omegaOne_le {K T : Subgroup G} {hTN : T ≤ normalizer (K : Set G)}
    (D : WStd K T hTN) (hT2 : IsPGroup 2 T) :
    {z : G | z ∈ T ∧ z ∈ zStarIn K ∧ z * z = 1}.ncard ≤ 4 := by
  have hP2 : IsPGroup 2 ↥(T ⊓ K) := hT2.to_le inf_le_left
  have hzK : ∀ {z : G}, z ∈ zStarIn K → z ∈ K := fun hz =>
    (map_subtype_le _ : zStarIn K ≤ K) hz
  rw [← Nat.card_coe_set_eq]
  refine le_trans (Nat.card_le_card_of_injective
    (fun k => (⟨jq K ⟨k.1, hzK k.2.2.1⟩, ?_, ?_⟩ :
      {e : Jhat K // e ∈ D.q.ker ∧ e * e = 1})) fun u v huv => ?_) D.hQ.card_omega_ker_le
  · rw [D.hQ.ker]
    exact (mem_zStarIn_iff _).1 k.2.2.1
  · rw [← map_mul]
    have : (⟨k.1, hzK k.2.2.1⟩ : K) * ⟨k.1, hzK k.2.2.1⟩ = 1 := Subtype.ext k.2.2.2
    rw [this, map_one]
  · have h1 := congrArg Subtype.val huv
    exact Subtype.ext (eq_of_jq_eq (inf_le_right : T ⊓ K ≤ K) hP2
      (mem_inf.mpr ⟨u.2.1, hzK u.2.2.1⟩) (mem_inf.mpr ⟨v.2.1, hzK v.2.2.1⟩) h1)

theorem conj_eq_or_of_omegaOne {K T : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTN : T ≤ normalizer (K : Set G))
    (h4 : {z : G | z ∈ T ∧ z ∈ zStarIn K ∧ z * z = 1}.ncard ≤ 4) {a : G} (haT : a ∈ T)
    (haZ : a ∈ zStarIn K) (haa : a * a = 1) (ha1 : a ≠ 1) {e e' : G} (he : e ∈ T)
    (he' : e' ∈ T) : e * a * e⁻¹ = a ∨ e' * a * e'⁻¹ = a ∨ e * a * e⁻¹ = e' * a * e'⁻¹ := by
  by_contra hall
  push Not at hall
  obtain ⟨h1, h2, h3⟩ := hall
  set Ω₁ : Set G := {z : G | z ∈ T ∧ z ∈ zStarIn K ∧ z * z = 1} with hΩ₁
  set Ω : Set G := Ω₁ \ {1} with hΩ
  have hconj : ∀ t ∈ T, ∀ y ∈ Ω, t * y * t⁻¹ ∈ Ω := by
    intro t ht y hy
    obtain ⟨⟨hyT, hyZ, hyy⟩, hy1⟩ := hy
    refine ⟨⟨mul_mem (mul_mem ht hyT) (inv_mem ht), GrS4.conj_mem_zStarIn (hTN ht) hyZ, ?_⟩, ?_⟩
    · rw [show t * y * t⁻¹ * (t * y * t⁻¹) = t * (y * y) * t⁻¹ by group, hyy, mul_one,
        mul_inv_cancel]
    · intro h
      apply hy1
      have h' : t * y * t⁻¹ = 1 := h
      rw [Set.mem_singleton_iff]
      calc y = t⁻¹ * (t * y * t⁻¹) * t := by group
        _ = 1 := by rw [h', mul_one, inv_mul_cancel]
  have hmem : ∀ g ∈ T, g * a * g⁻¹ ∈ Ω := fun g hg =>
    hconj g hg a ⟨⟨haT, haZ, haa⟩, ha1⟩
  have haΩ : a ∈ Ω := by
    have := hmem 1 (one_mem _)
    rwa [one_mul, inv_one, mul_one] at this
  have hΩ3 : Ω.ncard ≤ 3 := by
    have h1Ω : (1 : G) ∈ Ω₁ := ⟨one_mem _, one_mem _, mul_one 1⟩
    rw [hΩ, Set.ncard_sdiff_singleton_of_mem h1Ω]
    omega
  have hsub : ({a, e * a * e⁻¹, e' * a * e'⁻¹} : Set G) ⊆ Ω := by
    intro y hy
    rcases hy with rfl | rfl | rfl
    · exact haΩ
    · exact hmem e he
    · exact hmem e' he'
  have h3card : ({a, e * a * e⁻¹, e' * a * e'⁻¹} : Set G).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨a, e * a * e⁻¹, e' * a * e'⁻¹, h1.symm, h2.symm, h3, rfl⟩
  have hfin : Ω.Finite := Set.toFinite Ω
  have heq : ({a, e * a * e⁻¹, e' * a * e'⁻¹} : Set G) = Ω :=
    Set.eq_of_subset_of_ncard_le hsub (by omega) hfin
  have hodd : Odd (Nat.card Ω) := by
    rw [Nat.card_coe_set_eq, ← heq, h3card]
    decide
  obtain ⟨y, hy, hfix⟩ := exists_fixed_conj_of_odd hT2 hconj hodd
  rw [← heq] at hy
  rcases hy with rfl | rfl | rfl
  · exact h1 (hfix e he)
  · apply h1
    have := hfix e⁻¹ (inv_mem he)
    rw [inv_inv] at this
    calc e * a * e⁻¹ = e⁻¹ * (e * a * e⁻¹) * e := this.symm
      _ = a := by group
  · apply h2
    have := hfix e'⁻¹ (inv_mem he')
    rw [inv_inv] at this
    calc e' * a * e'⁻¹ = e'⁻¹ * (e' * a * e'⁻¹) * e' := this.symm
      _ = a := by group


theorem wGroup_eq_of_le_normalizer_of_inf_zStarIn_ne_bot (hMax : MaximalTwoComponentInput)
    {a x : G} {J S W : Subgroup G} (hset : L34Sec4Setting G a x J S)
    (hcent : ∀ s ∈ S, s * a = a * s) (hZa : S ⊓ zStarIn J ≠ ⊥ → a ∈ S ⊓ zStarIn J)
    (hWB : ∀ B : Subgroup G, B ≤ S ⊓ withKernel J → IsAbelianTwoOfRank 3 B → wGroup B = W)
    (hNJ : normalizer (J : Set G) ≤ normalizer (W : Set G)) {K : Subgroup G}
    (hKM : K ≤ normalizer (W : Set G))
    (hKc : IsPComponent 2 (K.subgroupOf (normalizer (W : Set G))))
    (hKL : IsL34Type (K ⧸ Open.fusionZStar K))
    (hout : J ⊔ oddIn (normalizer (W : Set G)) = K ⊔ oddIn (normalizer (W : Set G)) ∨
      (conjugate K a ≠ K ∧ J ≤ K ⊔ conjugate K a ⊔ oddIn (normalizer (W : Set G))))
    {T : Subgroup G} (hT : IsSylowTwoIn T (normalizer (W : Set G))) (hST : S ≤ T)
    (hTN : T ≤ normalizer (K : Set G)) (hZK : T ⊓ zStarIn K ≠ ⊥) {F : Subgroup G}
    (hFT : F ≤ T) (hF : IsEightGroup F)
    (hns : ∃ t ∈ T, t * t = 1 ∧ (∀ e ∈ F, t * e = e * t) ∧ t ∉ F) : wGroup F = W := by
  have hGW : GWTwoBalanced G :=
    gwTwoBalanced_of_locallyTwoBalanced solomonCommutingCoreInput hset.1.2.2.2.2.2.1
  obtain ⟨hbase, hU3, hL34, hmax, hSyl, haS, -⟩ := id hset
  obtain ⟨hsimple, hnab, hK, -, hUo, -, -, -⟩ := hbase
  obtain ⟨ha2, -, -, hJa, hJc, -, -⟩ := hU3
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := by rintro rfl; simp at ha2
  have hJper : ⁅J, J⁆ = J := UnbalancedCorr.commutator_eq_of_isPComponent hJa hJc
  set M : Subgroup G := normalizer (W : Set G) with hM
  have hJM : J ≤ M := le_normalizer.trans hNJ
  have haM : a ∈ M := hNJ (hSyl.1 haS)
  have haT : a ∈ T := hST haS
  have hT2 : IsPGroup 2 T := GrS4.isPGroup_of_isSylowTwoIn hT
  have hKper : ⁅K, K⁆ = K := UnbalancedCorr.commutator_eq_of_isPComponent hKM hKc
  have hsup : J ⊔ oddIn M = K ⊔ oddIn M := by
    rcases hout with h | ⟨hne, -⟩
    · exact h
    · refine absurd ?_ hne
      ext y
      rw [UnbalancedLayer.mem_conjugate_iff]
      exact ((mem_normalizer_iff.mp (hTN haT)) y).symm
  have hJK := GrS4.le_of_sup_oddIn_eq hJM hKM hKc hJper hsup
  have hKJ := GrS4.eq_sup_oddIn_of_sup_eq hJK hKM hsup
  have hTKs := isSylowTwoIn_inf_of_isPComponent hT hKM hKc
  have hZJ : S ⊓ zStarIn J ≠ ⊥ := fun h =>
    hZK (inf_zStarIn_eq_bot_of_le hJK hKJ (GrS4.isSylowTwoIn_inf hSyl) hST hTKs h)
  have haJ : a ∈ J := (map_subtype_le _ : zStarIn J ≤ J) (mem_inf.mp (hZa hZJ)).2
  have haCK := mem_coreActionKernel_of_sup_eq hKM hKc hJM hJper
    (GrS4.not_odd_card_of_isPComponent hJa hJc) hsup haM hJa
  have haZK : a ∈ zStarIn K := mem_zStarIn_of_mem_coreActionKernel (hJK haJ) haCK
  have hgs : GSMaximalSetting G a J := ⟨hsimple, hnab, hK, hUo, ha2, hJa, hJc, hmax,
    GrS5.three_le_pRank_of_l34 hL34, Sol78.not_psp4_of_l34 hL34, Or.inl ⟨hL34, hset.1⟩⟩
  have hCaN := GrS4.centralizer_le_normalizer_of_gsMaximalSetting hMax hgs
  have hCS : T ⊓ centralizer ({a} : Set G) = S :=
    hSyl.eq_of_le (le_inf hST fun s hs => mem_centralizer_singleton_iff.mpr (hcent s hs))
      (inf_le_right.trans hCaN) (hT2.to_le inf_le_left)
  obtain ⟨DK⟩ := exists_wStd hKper hKL hTKs hTN
  have h4 := ncard_omegaOne_le DK hT2
  have hconj : ∀ {e : G}, e * a * e⁻¹ = a → e ∈ centralizer ({a} : Set G) := fun {e} h =>
    mem_centralizer_singleton_iff.mpr (by
      calc e * a = e * a * e⁻¹ * e := by group
        _ = a * e := by rw [h])
  obtain ⟨t, htT, htt, htF, htn⟩ := hns
  by_cases hEa : F ≤ centralizer ({a} : Set G) ∧ t ∈ centralizer ({a} : Set G)
  · have hFS : F ≤ S := hCS ▸ le_inf hFT hEa.1
    have htS : t ∈ S := hCS ▸ mem_inf.mpr ⟨htT, hEa.2⟩
    exact wGroup_eq_of_not_stronglyIsolated hset hcent hWB hFS hF ⟨t, htS, htt, htF, htn⟩
  obtain ⟨hE, hEc⟩ := GrS4.isElemTwo_sup_zpowers hF.1 htt htn fun e he => (htF e he).symm
  set E : Subgroup G := F ⊔ zpowers t with hEdef
  have hE16 : Nat.card E = 16 := by rw [hEc, hF.2]
  have hET : E ≤ T := sup_le hFT (zpowers_le.mpr htT)
  obtain ⟨f, hfE, hfC⟩ : ∃ f ∈ E, f ∉ centralizer ({a} : Set G) := by
    by_contra hall
    push Not at hall
    exact hEa ⟨fun e he => hall e (mem_sup_left he), hall t (mem_sup_right (mem_zpowers t))⟩
  set E₀ : Subgroup G := E ⊓ centralizer ({a} : Set G) with hE₀
  have hE₀e : IsElemTwo E₀ := hE.mono inf_le_left
  have hfE₀ : f ∉ E₀ := fun h => hfC (mem_inf.mp h).2
  obtain ⟨hE₀f, hE₀fc⟩ := GrS4.isElemTwo_sup_zpowers hE₀e (hE.2 f hfE) hfE₀
    fun e he => hE.1 e (mem_inf.mp he).1 f hfE
  have hEle : E ≤ E₀ ⊔ zpowers f := by
    intro e he
    by_cases heC : e ∈ centralizer ({a} : Set G)
    · exact mem_sup_left (mem_inf.mpr ⟨he, heC⟩)
    rcases conj_eq_or_of_omegaOne hT2 hTN h4 haT haZK haa ha1 (hET he) (hET hfE) with
      h | h | h
    · exact absurd (hconj h) heC
    · exact absurd (hconj h) hfC
    · have hfe : f⁻¹ * e ∈ E₀ := mem_inf.mpr ⟨mul_mem (inv_mem hfE) he, hconj (by
        calc f⁻¹ * e * a * (f⁻¹ * e)⁻¹ = f⁻¹ * (e * a * e⁻¹) * f := by group
          _ = a := by rw [h]; group)⟩
      have : e = f * (f⁻¹ * e) := by group
      rw [this]
      exact mul_mem (mem_sup_right (mem_zpowers f)) (mem_sup_left hfe)
  have hE₀8 : IsEightGroup E₀ := by
    refine ⟨hE₀e, ?_⟩
    have h1 : Nat.card ↥(E₀ ⊔ zpowers f) ≤ 16 :=
      hE16 ▸ Subgroup.card_le_of_le (sup_le inf_le_left (zpowers_le.mpr hfE))
    have h2 : 16 ≤ Nat.card ↥(E₀ ⊔ zpowers f) := hE16 ▸ Subgroup.card_le_of_le hEle
    omega
  have hE₀S : E₀ ≤ S := hCS ▸ inf_le_inf_right _ hET
  have haE₀ : a ∉ E₀ := fun h => hfC (mem_centralizer_singleton_iff.mpr
    (hE.1 f hfE a (mem_inf.mp h).1))
  have hWE₀ : wGroup E₀ = W := wGroup_eq_of_not_stronglyIsolated hset hcent hWB hE₀S hE₀8
    ⟨a, haS, haa, fun e he => (mem_centralizer_singleton_iff.mp (mem_inf.mp he).2).symm, haE₀⟩
  rw [← hWE₀]
  exact wGroup_eq_of_commute hGW (hF.1.isAbelianTwoOfRank hF.2.ge)
    (hE₀8.1.isAbelianTwoOfRank hE₀8.2.ge)
    (fun u hu v hv => hE.1 u (mem_sup_left hu) v (mem_inf.mp hv).1)

end CFSG.ComponentClassification.GrSLit.GrS5S

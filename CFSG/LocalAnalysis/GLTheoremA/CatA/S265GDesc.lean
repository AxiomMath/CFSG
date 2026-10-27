module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265GCos
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265GCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265GLev
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265GPar
public import CFSG.LieType.Chevalley.ParabolicSelfNormalizing
public import CFSG.RankThree.PartOne.KF.ParabolicNormalizes

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265G

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.EvenOddRadical
open CFSG.Timmesfeld.ExceptionalOrders CFSG.RankThree.PartOne.KFU

variable
  {K : Type} [Field K] [Finite K]

private theorem entrywise_mem_parabolic_iff {σ : K ≃+* K} (hσ : σ ^ 3 = 1)
    (J : Set (Fin Tag.F4.rank)) (c : adjointGroup .F4 K) :
    ((entrywiseAdjointAut .F4 σ c : adjointGroup .F4 K) : ModGL .F4 K) ∈
        parabolicSubgroup .F4 K J ↔ (c : ModGL .F4 K) ∈ parabolicSubgroup .F4 K J := by
  have hfw : ∀ c : adjointGroup .F4 K, (c : ModGL .F4 K) ∈ parabolicSubgroup .F4 K J →
      ((entrywiseAdjointAut .F4 σ c : adjointGroup .F4 K) : ModGL .F4 K) ∈
        parabolicSubgroup .F4 K J :=
    fun c hc => entrywise_mem_parabolic σ hc
  refine ⟨fun h => ?_, hfw c⟩
  have h3 := hfw _ (hfw _ h)
  rwa [entrywiseAdjointAut_apply_three hσ] at h3

theorem exists_fixed_two_subgroup {f : ℕ} (hf : Odd f) (hK : Nat.card K = 2 ^ f) {σ : K ≃+* K}
    (hσ : σ ^ 3 = 1) {A V : Subgroup (adjointGroup .F4 K)} (hA3 : IsPGroup 3 A)
    (hAσ : ∀ a ∈ A, entrywiseAdjointAut .F4 σ a = a) (hV : V ≠ ⊥) (hV2 : IsPGroup 2 V)
    (hVσ : V.map (entrywiseAdjointAut .F4 σ).toMonoidHom = V)
    (hAV : A ≤ Subgroup.normalizer (V : Set (adjointGroup .F4 K))) :
    ∃ U : Subgroup (adjointGroup .F4 K), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      (∀ u ∈ U, entrywiseAdjointAut .F4 σ u = u) ∧
        A ≤ Subgroup.normalizer (U : Set (adjointGroup .F4 K)) := by
  classical
  haveI : CharP K 2 := by
    haveI : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  haveI : Finite (ModGL .F4 K) := finite_modGL
  set φ : MulAut (adjointGroup .F4 K) := entrywiseAdjointAut .F4 σ with hφdef
  have hφ3 : ∀ x, φ (φ (φ x)) = x := entrywiseAdjointAut_apply_three hσ
  obtain ⟨P, S, hPtop, hSP, hAP, hPφ⟩ :=
    exists_stable_overgroup (holds_adjointGroup_tag .F4 K 2) φ hV hV2 hVσ hAV
  have hBC : borelGroup .F4 K ≤ adjointGroup .F4 K := borelGroup_le_adjointGroup' .F4
  have hUC : posUnipotent .F4 K ≤ adjointGroup .F4 K := le_sup_right.trans hBC
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index 2 hUC card_posUnipotent
  have hUc := IsPGroup.toSylow_coe hUp hUi
  obtain ⟨g, hg⟩ := exists_conj_le_of_normalizes (hUp.toSylow hUi) S
    ((borelGroup .F4 K).subgroupOf (adjointGroup .F4 K)) P
    (by rw [hUc]; exact borelGroup_subgroupOf_le_normalizer .F4) hSP
  set P₁ : Subgroup (adjointGroup .F4 K) := P.comap (MulAut.conj g).toMonoidHom with hP₁
  have hmemP₁ : ∀ c, c ∈ P₁ ↔ g * c * g⁻¹ ∈ P := fun c => Iff.rfl
  set A₁ : Subgroup (ModGL .F4 K) := P₁.map (adjointGroup .F4 K).subtype with hA₁
  have hBA : borelGroup .F4 K ≤ A₁ := fun b hb =>
    ⟨⟨b, hBC hb⟩, hg (show (⟨b, hBC hb⟩ : adjointGroup .F4 K) ∈
      (borelGroup .F4 K).subgroupOf (adjointGroup .F4 K) from hb), rfl⟩
  have hAC : A₁ ≤ adjointGroup .F4 K := Subgroup.map_subtype_le _
  set J : Set (Fin Tag.F4.rank) := {i | weylElt .F4 K i 1 ∈ A₁} with hJdef
  have hAJ : A₁ = parabolicSubgroup .F4 K J := (borel_overgroup_classification .F4 K).1 A₁ hBA hAC
  have hP₁J : ∀ c : adjointGroup .F4 K, c ∈ P₁ ↔ (c : ModGL .F4 K) ∈ parabolicSubgroup .F4 K J := by
    intro c
    rw [← hAJ]
    constructor
    · intro hc
      exact ⟨c, hc, rfl⟩
    · rintro ⟨c', hc', hcc⟩
      rwa [← Subtype.ext hcc]
  have hJ : J ≠ Set.univ := by
    intro hJu
    apply hPtop
    rw [eq_top_iff]
    intro z _
    have hz : g⁻¹ * z * g ∈ P₁ := by
      rw [hP₁J, hJu, (standard_parabolic_cells .F4 K).2.2.2.2.2.1]
      exact (g⁻¹ * z * g).2
    rw [hmemP₁] at hz
    simpa [mul_assoc] using hz
  have hA : ∀ a ∈ A, ((g⁻¹ * a * g : adjointGroup .F4 K) : ModGL .F4 K) ∈
      parabolicSubgroup .F4 K J := by
    intro a ha
    rw [← hP₁J, hmemP₁]
    simpa [mul_assoc] using hAP ha
  have hPφ' : ∀ z, φ z ∈ P ↔ z ∈ P := by
    intro z
    constructor
    · intro hz
      rw [← hPφ] at hz
      obtain ⟨w, hw, hwz⟩ := hz
      rwa [← φ.injective hwz]
    · intro hz
      rw [← hPφ]
      exact ⟨z, hz, rfl⟩
  have hP₁φ : ∀ c, φ c ∈ P₁ ↔ c ∈ P₁ := by
    intro c
    rw [hP₁J, hP₁J]
    exact entrywise_mem_parabolic_iff hσ J c
  set y : adjointGroup .F4 K := g⁻¹ * φ g with hydef
  have hyN : ∀ c, c ∈ P₁ ↔ y * c * y⁻¹ ∈ P₁ := by
    intro c
    obtain ⟨c', rfl⟩ := φ.surjective c
    rw [hP₁φ, hmemP₁, hmemP₁]
    have h : g * (y * φ c' * y⁻¹) * g⁻¹ = φ (g * c' * g⁻¹) := by
      rw [hydef]
      simp only [map_mul, map_inv]
      group
    rw [h, hPφ']
  have hy : ((g⁻¹ * φ g : adjointGroup .F4 K) : ModGL .F4 K) ∈ parabolicSubgroup .F4 K J := by
    rw [← adjointGroup_inf_normalizer_parabolicSubgroup J]
    refine Subgroup.mem_inf.2 ⟨(g⁻¹ * φ g).2, ?_⟩
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have hzC : z ∈ adjointGroup .F4 K := parabolicSubgroup_le_adjointGroup _ _ _ hz
      have h1 : (⟨z, hzC⟩ : adjointGroup .F4 K) ∈ P₁ := (hP₁J _).2 hz
      have h2 := (hP₁J _).1 ((hyN _).1 h1)
      simpa [hydef] using h2
    · intro hz
      have hzC' : (y : ModGL .F4 K) * z * (y : ModGL .F4 K)⁻¹ ∈ adjointGroup .F4 K :=
        parabolicSubgroup_le_adjointGroup _ _ _ (by simpa [hydef] using hz)
      have hzC : z ∈ adjointGroup .F4 K := by
        have h := mul_mem (mul_mem (inv_mem y.2) hzC') y.2
        simpa [mul_assoc] using h
      have h1 : y * (⟨z, hzC⟩ : adjointGroup .F4 K) * y⁻¹ ∈ P₁ := by
        rw [hP₁J]
        simpa [hydef] using hz
      exact (hP₁J _).1 ((hyN _).2 h1)
  have hodd : ∀ (J' : Set (Fin Tag.F4.rank)) (d : ℤ), 1 ≤ d → Odd (levelRoots .F4 J' d).ncard →
      ∀ g' : adjointGroup .F4 K,
        ((g'⁻¹ * φ g' : adjointGroup .F4 K) : ModGL .F4 K) ∈ parabolicSubgroup .F4 K J' →
        (∀ a ∈ A, ((g'⁻¹ * a * g' : adjointGroup .F4 K) : ModGL .F4 K) ∈
          parabolicSubgroup .F4 K J') →
        ∃ U : Subgroup (adjointGroup .F4 K), U ≠ ⊥ ∧ IsPGroup 2 U ∧
          (∀ u ∈ U, entrywiseAdjointAut .F4 σ u = u) ∧
            A ≤ Subgroup.normalizer (U : Set (adjointGroup .F4 K)) :=
    fun J' d hd hn g' hy' hA' => exists_fixed_of_odd_level hf hK hσ hd hn hAσ g' hy' hA'
  have hmono : ∀ J' : Set (Fin Tag.F4.rank), J ⊆ J' →
      parabolicSubgroup .F4 K J ≤ parabolicSubgroup .F4 K J' :=
    fun J' h => ((standard_parabolic_cells .F4 K).2.2.2.1 J J').2 h
  have hodd7 : Odd (levelRoots .F4 (maskSet .F4 7 : Set (Fin Tag.F4.rank)) 1).ncard := by
    rw [ncard_levelRoots_seven]
    decide
  rcases subset_or_eq_thirteen hJ with h7 | h14 | h11 | h13
  · exact hodd _ 1 le_rfl hodd7 g (hmono _ h7 hy) fun a ha => hmono _ h7 (hA a ha)
  · refine hodd _ 1 le_rfl ?_ g (hmono _ h14 hy) fun a ha => hmono _ h14 (hA a ha)
    rw [ncard_levelRoots_fourteen]
    decide
  · refine hodd _ 3 (by norm_num) ?_ g (hmono _ h11 hy) fun a ha => hmono _ h11 (hA a ha)
    rw [ncard_levelRoots_eleven]
    decide
  set P₂' : Subgroup (adjointGroup .F4 K) :=
    (parabolicSubgroup .F4 K (maskSet .F4 13 : Set (Fin Tag.F4.rank))).subgroupOf
      (adjointGroup .F4 K) with hP₂'
  set P₁' : Subgroup (adjointGroup .F4 K) :=
    (parabolicSubgroup .F4 K (maskSet .F4 5 : Set (Fin Tag.F4.rank))).subgroupOf
      (adjointGroup .F4 K) with hP₁'
  have h12 : P₁' ≤ P₂' := Subgroup.comap_mono parabolic_five_le_thirteen
  have hφP : ∀ (J' : Set (Fin Tag.F4.rank)) (x : adjointGroup .F4 K),
      x ∈ (parabolicSubgroup .F4 K J').subgroupOf (adjointGroup .F4 K) →
        φ.toMonoidHom x ∈ (parabolicSubgroup .F4 K J').subgroupOf (adjointGroup .F4 K) := by
    intro J' x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (entrywise_mem_parabolic_iff hσ J' x).2 hx
  have hyP : y ∈ P₂' := by
    rw [hP₂', Subgroup.mem_subgroupOf, ← h13]
    exact hy
  have hyy : y * φ.toMonoidHom y * φ.toMonoidHom (φ.toMonoidHom y) = 1 := by
    simp only [MulEquiv.coe_toMonoidHom, hydef, map_mul, map_inv, hφ3]
    group
  set A' : Subgroup (adjointGroup .F4 K) := A.map (MulAut.conj g⁻¹).toMonoidHom with hA'
  have hmemA' : ∀ a', a' ∈ A' ↔ g * a' * g⁻¹ ∈ A := by
    intro a'
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using ha
    · intro ha'
      refine ⟨g * a' * g⁻¹, ha', ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  have hA'3 : IsPGroup 3 A' := hA3.map _
  have hA'2 : A' ≤ P₂' := by
    intro a' ha'
    rw [hmemA'] at ha'
    rw [hP₂', Subgroup.mem_subgroupOf, ← h13]
    have h := hA _ ha'
    simpa [mul_assoc] using h
  have hA'y : ∀ a' ∈ A', y * φ.toMonoidHom a' * y⁻¹ = a' := by
    intro a' ha'
    rw [hmemA'] at ha'
    have hfix : φ (g * a' * g⁻¹) = g * a' * g⁻¹ := hAσ _ ha'
    simp only [map_mul, map_inv] at hfix
    simp only [MulEquiv.coe_toMonoidHom, hydef]
    have hφa : φ a' = (φ g)⁻¹ * (g * a' * g⁻¹) * φ g := by
      rw [← hfix]
      group
    rw [hφa]
    group
  have hq : Nat.card K % 3 = 2 := by
    rw [hK]
    exact two_pow_mod_three_of_odd hf
  obtain ⟨x, -, hxy, hxA⟩ := exists_twisted_fixed_coset h12 φ.toMonoidHom hφ3
    (hφP _) (hφP _) hyP hyy hA'3 hA'2 hA'y (not_three_dvd_index_five_thirteen hq)
  have h57 : parabolicSubgroup .F4 K (maskSet .F4 5 : Set (Fin Tag.F4.rank)) ≤
      parabolicSubgroup .F4 K (maskSet .F4 7 : Set (Fin Tag.F4.rank)) :=
    ((standard_parabolic_cells .F4 K).2.2.2.1 _ _).2 (Finset.coe_subset.2 (by decide))
  refine hodd _ 1 le_rfl hodd7 (g * x) (h57 ?_) fun a ha => h57 ?_
  · have h : (g * x)⁻¹ * φ (g * x) = x⁻¹ * y * φ.toMonoidHom x := by
      simp only [MulEquiv.coe_toMonoidHom, hydef, map_mul]
      group
    rw [h]
    exact hxy
  · have ha' : g⁻¹ * a * g ∈ A' := by
      rw [hmemA']
      simpa [mul_assoc] using ha
    have h : (g * x)⁻¹ * a * (g * x) = x⁻¹ * (g⁻¹ * a * g) * x := by group
    rw [h]
    exact hxA _ ha'

end CFSG.LocalAnalysis.GLTheoremA.S265G

end

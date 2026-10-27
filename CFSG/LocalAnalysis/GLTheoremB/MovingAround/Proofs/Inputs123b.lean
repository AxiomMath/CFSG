module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltFacts3
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113ClaimsL2
public import CFSG.GH74.GLS.IVK.Proofs2.C3Ivk102L
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma123c

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs123b

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut autBar barOf innerAut)
open scoped MatrixGroups

section L27

open CFSG.GH74.GLS.IVK CFSG.GorensteinWalter

variable {Y : Type} [Group Y]

theorem fixSub_eq_fixedSubgroup (σ : MulAut Y) :
    fixSub σ = CFSG.GH74.GLS.fixedSubgroup Y σ := by
  ext x
  exact Iff.rfl

theorem innAut_eq_innerAut : CFSG.GH74.GLS.IVK.innAut Y = innerAut Y := rfl

theorem mem_innerAut_of_fieldProj {F : Type} [Field F] [Finite F] (e : Y ≃* L2 F) {x : MulAut Y}
    (hx : fieldProj e x = 1) {n : ℕ} (hn : Odd n) (hxn : x ^ n = 1) : x ∈ innerAut Y := by
  obtain ⟨A, rfl⟩ := (mem_innDiagSub_iff e x).2 hx
  have hA : A ^ n = 1 := innDiagHom_injective e (by rw [map_pow, hxn, map_one])
  obtain ⟨s, hs⟩ := CFSG.RankThree.PartTwo.KFacts.exists_toPGL_eq_of_pow_odd hn hA
  rw [← innAut_eq_innerAut]
  exact (innDiagHom_mem_innAut_iff e A).2 ⟨s, hs⟩

theorem fixSub_equiv_psl2 (e : Y ≃* L2 (GaloisField 3 3)) {β : MulAut Y} (hβ3 : β ^ 3 = 1)
    (hβ : fieldProj e β ≠ 1) :
    Nat.card (fixedField (fieldProj e β)) = 3 ∧
      Nonempty (↥(fixSub β) ≃* PSL2 (fixedField (fieldProj e β))) := by
  set σ := fieldProj e β with hσ
  have hσ3 : σ ^ 3 = 1 := by rw [hσ, ← map_pow, hβ3, map_one]
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hβ
  refine ⟨?_, ?_⟩
  · have h := fixedField_card_pow σ
    rw [hord, Lemma113Claims.L2.card_gf27] at h
    exact Nat.pow_left_injective (by norm_num) h
  · obtain ⟨c, -, hc⟩ := exists_conj_fieldAutHom e β (by rw [hord]; exact hβ3)
    have h1 : c⁻¹ * β * c⁻¹⁻¹ = fieldAutHom e σ := by rw [inv_inv]; exact hc
    have hodd : Odd (orderOf σ) := by rw [hord]; decide
    exact ⟨(MulEquiv.subgroupCongr (fixSub_eq_fixedSubgroup β)).trans
      ((CFSG.GH74.GLS.IVK.Proofs2.fixedSubgroupEquivOfConj h1).trans
        ((fixedSubgroupEquivL2 e σ hodd).trans (L2.equivPSL _)))⟩

theorem le_normalizer_map_subtype {G : Type*} [Group G] {C : Subgroup G} {N : Subgroup ↥C}
    (hN : N.Normal) : C ≤ Subgroup.normalizer ((N.map C.subtype : Subgroup G) : Set G) := by
  have key : ∀ c : ↥C, ∀ x ∈ N.map C.subtype, (c : G) * x * (c : G)⁻¹ ∈ N.map C.subtype := by
    rintro c _ ⟨n, hn, rfl⟩
    exact ⟨c * n * c⁻¹, hN.conj_mem n hn c, by simp⟩
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key ⟨c, hc⟩ x, fun hx => ?_⟩
  have := key (⟨c, hc⟩ : ↥C)⁻¹ _ hx
  simpa [mul_assoc] using this

theorem fixSub_struct (e : Y ≃* L2 (GaloisField 3 3)) [Finite Y] {β : MulAut Y} (hβ3 : β ^ 3 = 1)
    (hβ : fieldProj e β ≠ 1) {y₀ : Y} (hy₀ : β y₀ = y₀) (hy₀1 : y₀ ≠ 1) (hy₀3 : y₀ ^ 3 = 1) :
    Nat.card (fixSub β) = 12 ∧ Subgroup.center ↥(fixSub β) = ⊥ ∧
      fixSub β ≤ pCoreOf 2 (fixSub β) ⊔ Subgroup.zpowers y₀ ∧ pCoreOf 2 (fixSub β) ≠ ⊥ := by
  obtain ⟨hF3, ⟨φ⟩⟩ := fixSub_equiv_psl2 e hβ3 hβ
  set F₀ := fixedField (fieldProj e β) with hF₀
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (fixSub β) = 12 := by
    rw [Nat.card_congr φ.toEquiv]
    exact CFSG.RankThree.PartTwo.KFacts.card_psl2_of_card_three hF3
  have hcen : Subgroup.center ↥(fixSub β) = ⊥ := by
    have h := Subgroup.map_center_eq φ
    rw [psl2_center_eq_bot] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).1 h
  set V₀ : Subgroup (PSL2 F₀) := CFSG.RankThree.PartTwo.KFacts.psl2FourGroup F₀ with hV₀
  set V₁ : Subgroup ↥(fixSub β) := V₀.map φ.symm.toMonoidHom with hV₁
  set V : Subgroup Y := V₁.map (fixSub β).subtype with hV
  have hV₁n : V₁.Normal :=
    (CFSG.RankThree.PartTwo.KFacts.psl2FourGroup_normal_of_card_three hF3).map _ φ.symm.surjective
  have hVle : V ≤ fixSub β := Subgroup.map_subtype_le _
  have hVn : fixSub β ≤ Subgroup.normalizer (V : Set Y) := le_normalizer_map_subtype hV₁n
  have hV2 : IsPGroup 2 ↥V :=
    (CFSG.RankThree.PartTwo.KFacts.isPGroup_psl2FourGroup.map φ.symm.toMonoidHom).map _
  have hVcard : Nat.card V = 4 := by
    rw [hV, Subgroup.card_map_of_injective (fixSub β).subtype_injective, hV₁,
      Subgroup.card_map_of_injective φ.symm.injective]
    exact CFSG.RankThree.PartTwo.KFacts.card_psl2FourGroup_of_card_three hF3
  have hVO : V ≤ pCoreOf 2 (fixSub β) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVle hVn hV2
  have hy₀C : y₀ ∈ fixSub β := hy₀
  have hord : orderOf y₀ = 3 := orderOf_eq_prime hy₀3 hy₀1
  set W : Subgroup Y := V ⊔ Subgroup.zpowers y₀ with hW
  have hWle : W ≤ fixSub β := sup_le hVle ((Subgroup.zpowers_le).2 hy₀C)
  haveI : Finite ↥(fixSub β) := inferInstance
  have h12 : 12 ∣ Nat.card W := by
    have h4 : 4 ∣ Nat.card W := hVcard ▸ Subgroup.card_dvd_of_le le_sup_left
    have h3 : 3 ∣ Nat.card W := by
      have := Subgroup.card_dvd_of_le (le_sup_right : Subgroup.zpowers y₀ ≤ W)
      rwa [Nat.card_zpowers, hord] at this
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4 h3
  have hWeq : W = fixSub β := by
    refine Subgroup.eq_of_le_of_card_ge hWle ?_
    rw [hcard]
    exact Nat.le_of_dvd (Nat.card_pos) h12
  refine ⟨hcard, hcen, ?_, ?_⟩
  · exact (le_of_eq hWeq.symm).trans (sup_le_sup_right hVO _)
  · intro h
    have : V = ⊥ := le_bot_iff.1 (h ▸ hVO)
    rw [this, Subgroup.card_bot] at hVcard
    norm_num at hVcard

theorem eq_top_of_two_twelve (e₀ : Y ≃* PSL(2, GaloisField 3 3))
    {H C₁ C₂ : Subgroup Y} (h₁ : C₁ ≤ H) (h₂ : C₂ ≤ H) (hc₁ : Nat.card C₁ = 12)
    (hc₂ : Nat.card C₂ = 12) (hne : C₁ ≠ C₂) : H = ⊤ := by
  haveI : Finite Y := Lemma113Claims.L2.finite_of_mulEquiv e₀
  have h12 : 12 ∣ Nat.card H := hc₁ ▸ Subgroup.card_dvd_of_le h₁
  have hne12 : Nat.card H ≠ 12 := by
    intro h
    apply hne
    have e1 : C₁ = H := Subgroup.eq_of_le_of_card_ge h₁ (by rw [h, hc₁])
    have e2 : C₂ = H := Subgroup.eq_of_le_of_card_ge h₂ (by rw [h, hc₂])
    rw [e1, e2]
  set H' : Subgroup PSL(2, GaloisField 3 3) := H.map e₀.toMonoidHom with hH'
  have hcH : Nat.card H' = Nat.card H := Subgroup.card_map_of_injective e₀.injective
  suffices hH'top : H' = ⊤ by
    have := congrArg (Subgroup.comap e₀.toMonoidHom) hH'top
    rwa [hH', Subgroup.comap_map_eq_self_of_injective e₀.injective, Subgroup.comap_top] at this
  have h12' : 12 ∣ Nat.card H' := hcH ▸ h12
  have hne12' : Nat.card H' ≠ 12 := hcH ▸ hne12
  have h2 : 2 ∣ Nat.card H' := dvd_trans (by norm_num) h12'
  have h3' : 3 ∣ Nat.card H' := dvd_trans (by norm_num) h12'
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases CFSG.Quasithin.F6.dicksonPSL2_holds 3 3 (by norm_num) H' with
    h | h | h | h | h | h | h | h | h
  · obtain ⟨-, m, -, hm⟩ := h
    rw [hm] at h2
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2) (by norm_num)
  · obtain ⟨-, h | h⟩ := h
    · norm_num at h
      exact absurd (dvd_trans h12' h) (by norm_num)
    · norm_num at h
      exact absurd (dvd_trans h12' h) (by norm_num)
  · obtain ⟨z, hz, ⟨f⟩⟩ := h
    have hc : Nat.card H' = 2 * z := by rw [Nat.card_congr f.toEquiv, DihedralGroup.nat_card]
    rw [hc] at h12'
    norm_num at hz
    rcases hz with hz | hz
    · exact absurd (dvd_trans h12' (Nat.mul_dvd_mul_left 2 hz)) (by norm_num)
    · exact absurd (dvd_trans h12' (Nat.mul_dvd_mul_left 2 hz)) (by norm_num)
  · obtain ⟨-, ⟨f⟩⟩ := h
    exfalso
    apply hne12'
    rw [Nat.card_congr f.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  · obtain ⟨h, -⟩ := h
    norm_num at h
  · obtain ⟨h, -⟩ := h
    norm_num at h
  · obtain ⟨m, t, P, -, -, hPc, -, hQc, -, ht⟩ := h
    have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup P
    rw [hQc, hPc] at hc
    rw [hc] at h2
    norm_num at ht
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h | h
    · exact absurd (dvd_trans h ht) (by norm_num)
    · exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h) (by norm_num)
  · obtain ⟨m, hm, ⟨f⟩⟩ := h
    rcases (Nat.dvd_prime Nat.prime_three).1 hm with rfl | rfl
    · exfalso
      apply hne12'
      rw [Nat.card_congr f.toEquiv]
      exact CFSG.RankThree.PartTwo.KFacts.card_psl2_of_card_three
        (by rw [GaloisField.card 3 1 (by norm_num)]; norm_num)
    · apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_congr f.toEquiv]
  · obtain ⟨m, hm, -⟩ := h
    rcases (Nat.dvd_prime Nat.prime_three).1 hm with h | h <;> omega

theorem mem_normalizer_iSup' {G : Type*} [Group G] {ι : Sort*} {U : ι → Subgroup G} {g : G}
    (h : ∀ i, g ∈ Subgroup.normalizer (U i : Set G)) :
    g ∈ Subgroup.normalizer ((⨆ i, U i : Subgroup G) : Set G) := by
  have key : ∀ g' : G, (∀ i, g' ∈ Subgroup.normalizer (U i : Set G)) →
      (⨆ i, U i) ≤ (⨆ i, U i).comap (MulAut.conj g').toMonoidHom := by
    intro g' hg'
    refine iSup_le fun i x hx => ?_
    show g' * x * g'⁻¹ ∈ ⨆ i, U i
    exact le_iSup U i ((Subgroup.mem_normalizer_iff.1 (hg' i) x).1 hx)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g h hx, fun hx => ?_⟩
  have := key g⁻¹ (fun i => inv_mem (h i)) hx
  simpa [mul_assoc] using this

theorem l27_top_le_iSup (Y : Type) [Group Y] (D : Type) [Group D]
    [Finite D] (ψ : D →* MulAut Y) (hψ : Function.Injective ψ) (hY : IsLTwoTwentySeven Y)
    (hDc : ∀ x y : D, x * y = y * x) (hD3 : ∀ x : D, x ^ 3 = 1) (hcard : 9 ≤ Nat.card D)
    (hout : ∃ d : D, ψ d ∉ innerAut Y) :
    (⊤ : Subgroup Y) ≤ ⨆ (d : D) (_ : d ≠ 1), pCoreOf 2 (fixSub (ψ d)) := by
  obtain ⟨e₀⟩ := hY
  haveI : Finite Y := Lemma113Claims.L2.finite_of_mulEquiv e₀
  set e : Y ≃* L2 (GaloisField 3 3) := Lemma113Claims.L2.toL2 e₀ with he
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) := Lemma113Claims.L2.conj_injective e₀
  set f : D →* (GaloisField 3 3 ≃+* GaloisField 3 3) := (fieldProj e).comp ψ with hf
  have hker : f.ker ≠ ⊥ := by
    intro hbot
    have h1 := CFSG.RankThree.PartTwo.KFacts.card_eq_card_ker_mul_card_range f
    have h2 : Nat.card f.range ≤ 3 := (Subgroup.card_le_card_group _).trans
      CFSG.RankThree.PartTwo.KFacts.card_ringAut_galoisField_three_three.le
    rw [hbot, Subgroup.card_bot, one_mul] at h1
    omega
  obtain ⟨⟨d₀, hd₀k⟩, hd₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hker
  have hd₀1' : d₀ ≠ 1 := fun h => hd₀1 (Subtype.ext h)
  have hψ₀3 : ψ d₀ ^ 3 = 1 := by rw [← map_pow, hD3, map_one]
  obtain ⟨y₀, hy₀⟩ : ψ d₀ ∈ innerAut Y :=
    mem_innerAut_of_fieldProj e (MonoidHom.mem_ker.1 hd₀k) (by decide) hψ₀3
  have hy₀3 : y₀ ^ 3 = 1 := hinj (by rw [map_pow, hy₀, hψ₀3, map_one])
  have hy₀1 : y₀ ≠ 1 := by
    rintro rfl
    apply hd₀1'
    apply hψ
    rw [map_one, ← hy₀, map_one]
  have hfix : ∀ d : D, ψ d y₀ = y₀ := by
    intro d
    apply hinj
    rw [Lemma113Claims.L2.conj_map_apply, hy₀, ← map_mul, ← map_inv, ← map_mul, hDc d d₀,
      mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨d₁, hd₁⟩ := hout
  have hout_fp : ∀ d : D, ψ d ∉ innerAut Y → ψ d ^ 3 = 1 ∧ fieldProj e (ψ d) ≠ 1 := by
    intro d hd
    have h3 : ψ d ^ 3 = 1 := by rw [← map_pow, hD3, map_one]
    exact ⟨h3, fun h => hd (mem_innerAut_of_fieldProj e h (by decide) h3)⟩
  have hd₂ : ψ (d₁ * d₀) ∉ innerAut Y := by
    intro h
    apply hd₁
    have : ψ d₁ = ψ (d₁ * d₀) * (ψ d₀)⁻¹ := by rw [map_mul]; group
    rw [this]
    exact mul_mem h (inv_mem ⟨y₀, hy₀⟩)
  obtain ⟨h₁3, h₁f⟩ := hout_fp d₁ hd₁
  obtain ⟨h₂3, h₂f⟩ := hout_fp (d₁ * d₀) hd₂
  obtain ⟨hc₁, hz₁, hle₁, hne₁⟩ := fixSub_struct e h₁3 h₁f (hfix d₁) hy₀1 hy₀3
  obtain ⟨hc₂, -, hle₂, -⟩ := fixSub_struct e h₂3 h₂f (hfix (d₁ * d₀)) hy₀1 hy₀3
  have hdist : fixSub (ψ d₁) ≠ fixSub (ψ (d₁ * d₀)) := by
    intro heq
    have hcen : (⟨y₀, hfix d₁⟩ : ↥(fixSub (ψ d₁))) ∈ Subgroup.center ↥(fixSub (ψ d₁)) := by
      rw [Subgroup.mem_center_iff]
      intro c
      apply Subtype.ext
      have hc1 : ψ d₁ (c : Y) = c := c.2
      have hc2 : ψ (d₁ * d₀) (c : Y) = c := by
        have : (c : Y) ∈ fixSub (ψ (d₁ * d₀)) := heq ▸ c.2
        exact this
      rw [map_mul, MulAut.mul_apply, ← hy₀, MulAut.conj_apply] at hc2
      have h3 : ψ d₁ (y₀ * c * y₀⁻¹) = y₀ * c * y₀⁻¹ := by
        rw [map_mul, map_mul, map_inv, hfix d₁, hc1]
      rw [h3] at hc2
      show (c : Y) * y₀ = y₀ * c
      calc (c : Y) * y₀ = y₀ * c * y₀⁻¹ * y₀ := by rw [hc2]
        _ = y₀ * c := by group
    rw [hz₁, Subgroup.mem_bot] at hcen
    exact hy₀1 (congrArg Subtype.val hcen)
  set X₀ : Subgroup Y := ⨆ (d : D) (_ : d ≠ 1), pCoreOf 2 (fixSub (ψ d)) with hX₀
  have hd₁1 : d₁ ≠ 1 := by
    rintro rfl
    exact hd₁ (by rw [map_one]; exact one_mem _)
  have hd₂1 : d₁ * d₀ ≠ 1 := by
    intro h
    exact hd₂ (by rw [h, map_one]; exact one_mem _)
  have hO_le : ∀ d : D, d ≠ 1 → pCoreOf 2 (fixSub (ψ d)) ≤ X₀ := fun d hd =>
    le_iSup_of_le d (le_iSup_of_le hd le_rfl)
  have hy₀N : y₀ ∈ Subgroup.normalizer (X₀ : Set Y) := by
    refine mem_normalizer_iSup' fun d => mem_normalizer_iSup' fun _ => ?_
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (hfix d)
  have hXtop : X₀ ⊔ Subgroup.zpowers y₀ = ⊤ := by
    refine eq_top_of_two_twelve e₀ (C₁ := fixSub (ψ d₁)) (C₂ := fixSub (ψ (d₁ * d₀)))
      (hle₁.trans (sup_le_sup_right (hO_le d₁ hd₁1) _))
      (hle₂.trans (sup_le_sup_right (hO_le _ hd₂1) _)) hc₁ hc₂ hdist
  have hnorm : X₀.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hXtop]
    exact sup_le Subgroup.le_normalizer ((Subgroup.zpowers_le).2 hy₀N)
  haveI : IsSimpleGroup PSL(2, GaloisField 3 3) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Lemma113Claims.L2.card_gf27]; norm_num)
  haveI : IsSimpleGroup Y := e₀.isSimpleGroup
  rcases hnorm.eq_bot_or_eq_top with h | h
  · exact absurd (le_bot_iff.1 (h ▸ hO_le d₁ hd₁1)) hne₁
  · exact h.ge

end L27

section Components

open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns (mem_gLAPPrimeCoreOf_iff gLAPPrimeCoreOf_le
  barX_eq_iff_cov isQuasisimple_barOf)

theorem quotientCenterAut'_conj {Q : Type*} [Group Q] (k : Q) :
    quotientCenterAut' Q (MulAut.conj k) = MulAut.conj (QuotientGroup.mk k : Q ⧸ Subgroup.center Q) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H y => rfl

theorem mem_innerAut_of_quotientCenterAut' {Q : Type*} [Group Q] (hperf : commutator Q = ⊤)
    {α : MulAut Q} (h : quotientCenterAut' Q α ∈ innerAut (Q ⧸ Subgroup.center Q)) :
    α ∈ innerAut Q := by
  obtain ⟨q, hq⟩ := h
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨k, quotientCenterAut'_injective hperf ?_⟩
  rw [quotientCenterAut'_conj]
  exact hq

variable {G : Type} [Group G] [Finite G]

theorem injective_quotientCenter_barAut {p : ℕ} {K B : Subgroup G}
    (hperf : commutator (barOf p K) = ⊤) (hBn : B ≤ Subgroup.normalizer (K : Set G))
    (hfaith : ∀ x ∈ B, x ∈ centBar p ⊤ K → x = 1) :
    Function.Injective ((quotientCenterAut' (barOf p K)).comp
      ((barAut p K).comp (Subgroup.inclusion hBn))) := by
  rw [injective_iff_map_eq_one]
  intro b hb
  have hβ : barAut p K ⟨(b : G), hBn b.2⟩ = 1 :=
    quotientCenterAut'_injective hperf (hb.trans (map_one _).symm)
  have hbc : (b : G) ∈ centBar p ⊤ K :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_map.2 ⟨⟨(b : G), hBn b.2⟩, MonoidHom.mem_ker.2 hβ, rfl⟩,
      Subgroup.mem_top _⟩
  exact Subtype.ext (hfaith _ b.2 hbc)

theorem input23_17_holds : Lemma123.Input23_17 := by
  intro G _ _ X K B hK hBX hBel hBn hfaith hrk hL27 hout
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  set H : Subgroup G := ⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1),
    GLAPPrimeCoreOf 3 (K ⊓ Subgroup.centralizer ({b} : Set G)) with hH
  have hHK : H ≤ K := iSup_le fun b => iSup_le fun _ => iSup_le fun _ =>
    (gLAPPrimeCoreOf_le 3 _).trans inf_le_left
  have hcore_le : ∀ b ∈ B, b ≠ 1 →
      GLAPPrimeCoreOf 3 (K ⊓ Subgroup.centralizer ({b} : Set G)) ≤ H := fun b hb hb1 =>
    le_iSup_of_le b (le_iSup_of_le hb (le_iSup_of_le hb1 le_rfl))
  suffices hcov : ∀ k ∈ K, ∃ h ∈ H, h⁻¹ * k ∈ GLAPPrimeCoreOf 3 K from
    ((barX_eq_iff_cov hp hK.2.1 hHK).2 hcov).ge
  obtain ⟨e27⟩ := hL27
  haveI hntQ : Nontrivial (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) :=
    e27.symm.injective.nontrivial
  haveI hntK : Nontrivial (barOf 3 K) :=
    (QuotientGroup.mk_surjective (s := Subgroup.center (barOf 3 K))).nontrivial
  have hq : CFSG.Open.IsQuasisimple (barOf 3 K) := isQuasisimple_barOf hp hK hntK
  have hO : GLAPPrimeCore 3 (barOf 3 K) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥K) (p := 3)
  have hperf : commutator (barOf 3 K) = ⊤ := hq.1
  have hZ3 : IsPGroup 3 ↥(Subgroup.center (barOf 3 K)) :=
    AltFacts2.isPGroup_center_of_core_eq_bot hp hO
  set ψ : ↥B →* MulAut (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) :=
    (quotientCenterAut' (barOf 3 K)).comp ((barAut 3 K).comp (Subgroup.inclusion hBn)) with hψdef
  have hψ : Function.Injective ψ := injective_quotientCenter_barAut hperf hBn hfaith
  have hcard9 : 9 ≤ Nat.card ↥B := by
    obtain ⟨E, hEB, -, hE⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank hrk
    have h9 := Subgroup.card_le_of_le hEB
    rw [hE] at h9
    simpa using h9
  have hDc : ∀ x y : ↥B, x * y = y * x := fun x y => hBel.1.is_comm.comm x y
  have hD3 : ∀ x : ↥B, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hBel.2 _ x.2)
  have hout' : ∃ d : ↥B, ψ d ∉ innerAut (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) := by
    by_contra hall
    push Not at hall
    apply hout
    rintro _ ⟨γ, hγ, rfl⟩
    have hγB : (γ : G) ∈ B := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hγ)).1
    have h1 := hall ⟨(γ : G), hγB⟩
    exact mem_innerAut_of_quotientCenterAut' hperf h1
  have hgen := l27_top_le_iSup (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) ↥B ψ hψ ⟨e27⟩ hDc hD3
    hcard9 hout'
  set M : Subgroup (barOf 3 K) := barX 3 K H with hM
  have hMtop : M.map (QuotientGroup.mk' (Subgroup.center (barOf 3 K))) = ⊤ := by
    refine eq_top_iff.2 (hgen.trans (iSup_le fun d => iSup_le fun hd => ?_))
    intro w hw
    have hdB : (d : G) ∈ B := d.2
    have hd1 : (d : G) ≠ 1 := fun h => hd (Subtype.ext h)
    have hdN : (d : G) ∈ Subgroup.normalizer (K : Set G) := hBn hdB
    have hd3 : (d : G) ^ 3 = 1 := hBel.2 _ hdB
    obtain ⟨y, hy, hyw⟩ := AltFacts2.exists_mem_pCoreOf_lift hZ3 (barAut 3 K ⟨(d : G), hdN⟩) hw
    obtain ⟨c, hcK, hcC, hcy⟩ := AltFacts2.lift_two_core hdN hd3 hy
    have hcH : c ∈ H := hcore_le _ hdB hd1 hcC
    refine Subgroup.mem_map.2 ⟨y, ?_, hyw⟩
    exact ⟨⟨c, hcK⟩, Subgroup.mem_subgroupOf.2 hcH, hcy⟩
  have hMeq : M = ⊤ := AltFacts2.eq_top_of_map_center_eq_top hperf hMtop
  intro k hk
  have hmem : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) ⟨k, hk⟩ : barOf 3 K) ∈ M := by
    rw [hMeq]; exact Subgroup.mem_top _
  obtain ⟨⟨h, hhK⟩, hhH, hhk⟩ := hmem
  refine ⟨h, Subgroup.mem_subgroupOf.1 hhH, ?_⟩
  have h1 : (⟨h, hhK⟩ : ↥K)⁻¹ * ⟨k, hk⟩ ∈ GLAPPrimeCore 3 ↥K := QuotientGroup.eq.1 hhk
  exact (mem_gLAPPrimeCoreOf_iff 3 K _).2 ⟨K.mul_mem (K.inv_mem hhK) hk, h1⟩

theorem comap_le_pPrimeCore' {p : ℕ} (hp : p.Prime) {Cg Y : Type*} [Group Cg] [Finite Cg] [Group Y]
    [Finite Y] (ρ : Cg →* Y) (hker : ∀ x : Cg, ρ x = 1 → ¬ p ∣ orderOf x)
    (Q : Subgroup Y) (hQ : ¬ p ∣ Nat.card Q)
    (hnorm : ∀ x : Cg, ρ x ∈ Subgroup.normalizer (Q : Set Y)) :
    Q.comap ρ ≤ CFSG.pPrimeCore p Cg := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hN : (Q.comap ρ).Normal := by
    refine ⟨fun r hr g => ?_⟩
    rw [Subgroup.mem_comap] at hr ⊢
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 (hnorm g) (ρ r)).1 hr
  have hcop : Nat.Coprime p (Nat.card (Q.comap ρ)) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hzord : orderOf (x : Cg) = p := by rw [Subgroup.orderOf_coe]; exact hx
    have hρz : ρ (x : Cg) ∈ Q := x.2
    have h2 : orderOf (ρ (x : Cg)) ∣ p := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow, ← hzord, pow_orderOf_eq_one, map_one]
    have h3 : orderOf (ρ (x : Cg)) ∣ Nat.card Q := by
      have := orderOf_dvd_natCard (⟨ρ (x : Cg), hρz⟩ : ↥Q)
      rwa [Subgroup.orderOf_mk] at this
    have h4 : orderOf (ρ (x : Cg)) = 1 := by
      rcases (Nat.dvd_prime hp).1 h2 with h | h
      · exact h
      · exact absurd (h ▸ h3) hQ
    exact hker (x : Cg) (orderOf_eq_one_iff.1 h4) (by rw [hzord])
  exact CFSG.le_pPrimeCore_of_normal_coprime hN hcop

theorem lift_core {p : ℕ} (hp : p.Prime) {K : Subgroup G} {d : G}
    (hdN : d ∈ Subgroup.normalizer (K : Set G)) (hdp : d ^ p = 1) {y : barOf p K}
    (hy : y ∈ GLAPPrimeCoreOf p (fixSub (barAut p K ⟨d, hdN⟩))) :
    ∃ (c : G) (hc : c ∈ K), c ∈ GLAPPrimeCoreOf p (K ⊓ Subgroup.centralizer ({d} : Set G)) ∧
      (QuotientGroup.mk' (GLAPPrimeCore p ↥K) ⟨c, hc⟩ : barOf p K) = y := by
  set α := barAut p K ⟨d, hdN⟩ with hα
  set C : Subgroup G := K ⊓ Subgroup.centralizer ({d} : Set G) with hC
  have hCK : C ≤ K := inf_le_left
  have hF : fixSub α = barX p K C := by
    rw [AltFacts2.fixSub_eq_fixedSub]
    exact AltFacts3.fixedSub_barAut_eq_p hp hdp hdN
  set Q : Subgroup (barOf p K) := GLAPPrimeCoreOf p (fixSub α) with hQ
  have hyF : y ∈ fixSub α := gLAPPrimeCoreOf_le p _ hy
  rw [hF] at hyF
  obtain ⟨c', hc'C, hc'y⟩ := Subgroup.mem_map.1 hyF
  let c₀ : ↥C := ⟨(c' : G), Subgroup.mem_subgroupOf.1 hc'C⟩
  let ρ : ↥C →* barOf p K := (QuotientGroup.mk' (GLAPPrimeCore p ↥K)).comp (Subgroup.inclusion hCK)
  have hker : ∀ x : ↥C, ρ x = 1 → ¬ p ∣ orderOf x := by
    intro x hx h3
    have h1 : (x : G) ∈ GLAPPrimeCoreOf p K :=
      (mem_gLAPPrimeCoreOf_iff p K _).2 ⟨hCK x.2, (QuotientGroup.eq_one_iff _).1 hx⟩
    have h2 : orderOf (⟨(x : G), h1⟩ : ↥(GLAPPrimeCoreOf p K)) ∣ Nat.card (GLAPPrimeCoreOf p K) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h2
    have h4 : orderOf x = orderOf (x : G) := (Subgroup.orderOf_coe x).symm
    have h5 : orderOf x ∣ Nat.card (GLAPPrimeCoreOf p K) := by rw [h4]; exact h2
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes
      (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.card_gLAPPrimeCoreOf_coprime p K)
      (dvd_refl p) (h3.trans h5))
  have hnorm : ∀ x : ↥C, ρ x ∈ Subgroup.normalizer (Q : Set (barOf p K)) := by
    intro x
    have hmem : ρ x ∈ fixSub α := by
      rw [hF]
      exact ⟨⟨(x : G), hCK x.2⟩, Subgroup.mem_subgroupOf.2 x.2, rfl⟩
    exact CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.le_normalizer_gLAPPrimeCoreOf p _ hmem
  have hQp : ¬ p ∣ Nat.card Q := by
    intro h
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes
      (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.card_gLAPPrimeCoreOf_coprime p _)
      (dvd_refl p) h)
  have hle := comap_le_pPrimeCore' hp ρ hker Q hQp hnorm
  have hc₀Q : c₀ ∈ Q.comap ρ := by
    have h1 : ρ c₀ = (QuotientGroup.mk' (GLAPPrimeCore p ↥K)) c' := rfl
    rw [Subgroup.mem_comap, h1, hc'y]
    exact hy
  have hc₀core : c₀ ∈ GLAPPrimeCore p ↥C := hle hc₀Q
  exact ⟨(c' : G), c'.2, (mem_gLAPPrimeCoreOf_iff p C _).2 ⟨c₀.2, hc₀core⟩, hc'y⟩

theorem autBar_eq_range {p : ℕ} {K B : Subgroup G} (hBn : B ≤ Subgroup.normalizer (K : Set G)) :
    autBar p B K = ((barAut p K).comp (Subgroup.inclusion hBn)).range := by
  ext α
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    have hγB : (γ : G) ∈ B := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hγ)).1
    exact ⟨⟨(γ : G), hγB⟩, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨Subgroup.inclusion hBn b, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨b.2, hBn b.2⟩), rfl⟩

theorem injective_barAut {p : ℕ} {K B : Subgroup G} (hBn : B ≤ Subgroup.normalizer (K : Set G))
    (hfaith : ∀ x ∈ B, x ∈ centBar p ⊤ K → x = 1) :
    Function.Injective ((barAut p K).comp (Subgroup.inclusion hBn)) := by
  rw [injective_iff_map_eq_one]
  intro b hb
  have hbc : (b : G) ∈ centBar p ⊤ K :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_map.2 ⟨⟨(b : G), hBn b.2⟩, MonoidHom.mem_ker.2 hb, rfl⟩,
      Subgroup.mem_top _⟩
  exact Subtype.ext (hfaith _ b.2 hbc)

theorem card_autBar {p : ℕ} {K B : Subgroup G} (hBn : B ≤ Subgroup.normalizer (K : Set G))
    (hfaith : ∀ x ∈ B, x ∈ centBar p ⊤ K → x = 1) : Nat.card (autBar p B K) = Nat.card B := by
  rw [autBar_eq_range hBn]
  exact (Nat.card_congr (MonoidHom.ofInjective (injective_barAut hBn hfaith)).toEquiv).symm

theorem exists_of_mem_autBar {p : ℕ} {K B : Subgroup G} (hBn : B ≤ Subgroup.normalizer (K : Set G))
    {α : MulAut (barOf p K)} (hα : α ∈ autBar p B K) (hα1 : α ≠ 1) :
    ∃ b ∈ B, ∃ hb : b ∈ Subgroup.normalizer (K : Set G), b ≠ 1 ∧ barAut p K ⟨b, hb⟩ = α := by
  rw [autBar_eq_range hBn] at hα
  obtain ⟨b, rfl⟩ := hα
  refine ⟨(b : G), b.2, hBn b.2, fun h => hα1 ?_, rfl⟩
  have hb1 : b = 1 := Subtype.ext h
  rw [hb1, map_one]

theorem barX_le_of_top_le {p : ℕ} (hp : p.Prime) {X K B : Subgroup G} (hK : GLAPComponent p X K)
    (hBel : IsElemAbelian p B) (hBn : B ≤ Subgroup.normalizer (K : Set G))
    (hgen : (⊤ : Subgroup (barOf p K)) ≤ ⨆ (α : MulAut (barOf p K)) (_ : α ∈ autBar p B K) (_ : α ≠ 1),
      GLAPPrimeCoreOf p (fixSub α)) :
    barX p X K ≤ barX p X (⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1),
      GLAPPrimeCoreOf p (K ⊓ Subgroup.centralizer ({b} : Set G))) := by
  set H : Subgroup G := ⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1),
    GLAPPrimeCoreOf p (K ⊓ Subgroup.centralizer ({b} : Set G)) with hH
  have hHK : H ≤ K := iSup_le fun b => iSup_le fun _ => iSup_le fun _ =>
    (gLAPPrimeCoreOf_le p _).trans inf_le_left
  have hcore_le : ∀ b ∈ B, b ≠ 1 →
      GLAPPrimeCoreOf p (K ⊓ Subgroup.centralizer ({b} : Set G)) ≤ H := fun b hb hb1 =>
    le_iSup_of_le b (le_iSup_of_le hb (le_iSup_of_le hb1 le_rfl))
  have htop : barX p K H = ⊤ := by
    refine eq_top_iff.2 (hgen.trans (iSup_le fun α => iSup_le fun hα => iSup_le fun hα1 => ?_))
    intro y hy
    obtain ⟨b, hbB, hbN, hb1, rfl⟩ := exists_of_mem_autBar hBn hα hα1
    obtain ⟨c, hcK, hcC, hcy⟩ := lift_core hp hbN (hBel.2 b hbB) hy
    exact ⟨⟨c, hcK⟩, Subgroup.mem_subgroupOf.2 (hcore_le b hbB hb1 hcC), hcy⟩
  have hcov := (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.barX_eq_top_iff p hHK).1 htop
  exact ((barX_eq_iff_cov hp hK.2.1 hHK).2 hcov).ge

@[expose] def Input23_24Q : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (s : TauCeti.SporadicName), CFSG.Open.IsQuasisimple Y →
    GLAPPrimeCore 3 Y = ⊥ →
    (s = TauCeti.SporadicName.M12 ∨ s = TauCeti.SporadicName.M22 ∨ s = TauCeti.SporadicName.J2) →
    IsSporType s (Y ⧸ Subgroup.center Y) →
    ∀ A : Subgroup (MulAut Y), IsElemAbelian 3 A → 9 ≤ Nat.card A →
      (¬ IsLocallyOTwoBalanced 3 2 A ∨ ¬ IsWeaklyLocallyOTwoBalanced 3 1 A) →
        (⊤ : Subgroup Y) ≤ ⨆ (α : MulAut Y) (_ : α ∈ A) (_ : α ≠ 1), GLAPPrimeCoreOf 3 (fixSub α)

theorem nine_le_card {B : Subgroup G} (hrk : 2 ≤ CFSG.Open.pRank 3 B) : 9 ≤ Nat.card B := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEB, -, hE⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank hrk
  have h9 := Subgroup.card_le_of_le hEB
  rw [hE] at h9
  simpa using h9

theorem input23_24_of_Q (h : Input23_24Q) : Lemma123.Input23_24 := by
  intro G _ _ X K B s hK hBX hBel hBn hfaith hrk hs hsp hbal
  have hp : Nat.Prime 3 := Nat.prime_three
  have hq : CFSG.Open.IsQuasisimple (barOf 3 K) :=
    CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hK
  have hO : GLAPPrimeCore 3 (barOf 3 K) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hA9 : 9 ≤ Nat.card (autBar 3 B K) := by
    rw [card_autBar hBn hfaith]
    exact nine_le_card hrk
  exact barX_le_of_top_le hp hK hBel hBn
    (h (barOf 3 K) s hq hO hs hsp _ (Lemma123.isElemAbelian_autBar hBel) hA9 hbal)

@[expose] def Input27_2Q : Prop :=
  ∀ (p q n : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore p Y = ⊥ →
    ∀ A : Subgroup (MulAut Y), IsElemAbelian p A → Nat.card A = p ^ 2 →
      ((IsLpType p (q ^ n) (Y ⧸ Subgroup.center Y) ∧ p ∣ q ^ n - 1 ∧
          Prop1116Design.HeisenbergImageL p (q ^ n) A) ∨
        (IsUpType p (q ^ n) (Y ⧸ Subgroup.center Y) ∧ p ∣ q ^ n + 1 ∧
          Prop1116Design.HeisenbergImageU p (q ^ n) A)) →
      ∀ W : Subgroup (MulAut Y), IsPGroup 2 ↥W → A ≤ Subgroup.normalizer (W : Set (MulAut Y)) →
        (∀ α ∈ A, α ≠ 1 → ∀ y ∈ GLAPPrimeCoreOf p (fixSub α),
          MulAut.conj y ∈ Subgroup.normalizer (W : Set (MulAut Y))) →
          W = ⊥

theorem barAut_mem_normalizer_map {p : ℕ} {K W : Subgroup G} {g : G}
    (hgK : g ∈ Subgroup.normalizer (K : Set G)) (hgW : g ∈ Subgroup.normalizer (W : Set G)) :
    barAut p K ⟨g, hgK⟩ ∈ Subgroup.normalizer
      (((W.subgroupOf (Subgroup.normalizer (K : Set G))).map (barAut p K) :
        Subgroup (MulAut (barOf p K))) : Set (MulAut (barOf p K))) := by
  set W' : Subgroup (MulAut (barOf p K)) :=
    (W.subgroupOf (Subgroup.normalizer (K : Set G))).map (barAut p K) with hW'
  have key : ∀ γ : ↥(Subgroup.normalizer (K : Set G)), (γ : G) ∈ Subgroup.normalizer (W : Set G) →
      ∀ x ∈ W', barAut p K γ * x * (barAut p K γ)⁻¹ ∈ W' := by
    rintro γ hγW _ ⟨δ, hδ, rfl⟩
    refine ⟨γ * δ * γ⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    have hδ' : (δ : G) ∈ W := Subgroup.mem_subgroupOf.1 hδ
    refine Subgroup.mem_subgroupOf.2 ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.1 hγW _).1 hδ'
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key ⟨g, hgK⟩ hgW x, fun hx => ?_⟩
  have h1 := key (⟨g, hgK⟩ : ↥(Subgroup.normalizer (K : Set G)))⁻¹ (inv_mem hgW) _ hx
  rw [map_inv, inv_inv] at h1
  simpa [mul_assoc] using h1

theorem input27_2_of_Q (h : Input27_2Q) : Lemma123.Input27_2 := by
  intro G _ _ p q n X K B W hp hp2 hq hq2 hqp hK hBX hBel hBcard hBn hfaith hHeis hW2 hWK hBW hJW
  have hqs : CFSG.Open.IsQuasisimple (barOf p K) :=
    CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hK
  have hO : GLAPPrimeCore p (barOf p K) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W' : Subgroup (MulAut (barOf p K)) :=
    (W.subgroupOf (Subgroup.normalizer (K : Set G))).map (barAut p K) with hW'
  have hW'2 : IsPGroup 2 ↥W' := by
    have h0 : IsPGroup 2 ↥(W.subgroupOf (Subgroup.normalizer (K : Set G))) :=
      hW2.comap_of_injective _ (Subgroup.normalizer (K : Set G)).subtype_injective
    exact h0.map _
  have hAW : autBar p B K ≤ Subgroup.normalizer (W' : Set (MulAut (barOf p K))) := by
    rw [autBar_eq_range hBn]
    rintro _ ⟨b, rfl⟩
    exact barAut_mem_normalizer_map (hBn b.2) (hBW b.2)
  have hJW' : ∀ α ∈ autBar p B K, α ≠ 1 → ∀ y ∈ GLAPPrimeCoreOf p (fixSub α),
      MulAut.conj y ∈ Subgroup.normalizer (W' : Set (MulAut (barOf p K))) := by
    intro α hα hα1 y hy
    obtain ⟨b, hbB, hbN, hb1, rfl⟩ := exists_of_mem_autBar hBn hα hα1
    obtain ⟨c, hcK, hcC, hcy⟩ := lift_core hp hbN (hBel.2 b hbB) hy
    have hcNW : c ∈ Subgroup.normalizer (W : Set G) := hJW b hbB hb1 hcC
    have hcNK : c ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hcK
    have hconj : MulAut.conj y = barAut p K ⟨c, hcNK⟩ := by
      rw [Lemma123.barAut_of_mem hcK hcNK, ← hcy]
      rfl
    rw [hconj]
    exact barAut_mem_normalizer_map hcNK hcNW
  have hcardA : Nat.card (autBar p B K) = p ^ 2 := by rw [card_autBar hBn hfaith, hBcard]
  have hbot := h p q n hp hp2 hq hq2 hqp (barOf p K) hqs hO (autBar p B K)
    (Lemma123.isElemAbelian_autBar hBel) hcardA hHeis W' hW'2 hAW hJW'
  intro w hw
  have hmem : barAut p K ⟨w, hWK hw⟩ ∈ W' :=
    ⟨⟨w, hWK hw⟩, Subgroup.mem_subgroupOf.2 hw, rfl⟩
  rw [hbot] at hmem
  exact hmem

noncomputable def toBarX (p : ℕ) {K C : Subgroup G} (hCK : C ≤ K) : ↥C →* ↥(barX p K C) :=
  ((QuotientGroup.mk' (GLAPPrimeCore p ↥K)).comp (Subgroup.inclusion hCK)).codRestrict (barX p K C)
    (fun x => ⟨⟨x, hCK x.2⟩, Subgroup.mem_subgroupOf.2 x.2, rfl⟩)

theorem toBarX_surjective (p : ℕ) {K C : Subgroup G} (hCK : C ≤ K) :
    Function.Surjective (toBarX p hCK) := by
  rintro ⟨_, ⟨⟨l, hlX⟩, hl, rfl⟩⟩
  exact ⟨⟨l, Subgroup.mem_subgroupOf.1 hl⟩, rfl⟩

theorem not_dvd_card_ker_toBarX {p : ℕ} (hp : p.Prime) {K C : Subgroup G} (hCK : C ≤ K) :
    ¬ p ∣ Nat.card (toBarX p hCK).ker := by
  intro h
  have hk : (toBarX p hCK).ker =
      ((QuotientGroup.mk' (GLAPPrimeCore p ↥K)).comp (Subgroup.inclusion hCK)).ker :=
    MonoidHom.ker_codRestrict _ _ _
  have h1 := Subgroup.card_dvd_of_le (hk ▸ AltFacts3.ker_inclusion_le_core p hCK)
  exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes
    (CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux p ↥C) (dvd_refl p)
    (h.trans h1))

theorem layer_fixSub_le {p : ℕ} (hp : p.Prime) {K : Subgroup G} {d : G}
    (hdN : d ∈ Subgroup.normalizer (K : Set G)) (hdp : d ^ p = 1) :
    GLAPLayer p (fixSub (barAut p K ⟨d, hdN⟩)) ≤
      barX p K (GLAPLayer p (K ⊓ Subgroup.centralizer ({d} : Set G))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set C : Subgroup G := K ⊓ Subgroup.centralizer ({d} : Set G) with hC
  have hCK : C ≤ K := inf_le_left
  have hF : fixSub (barAut p K ⟨d, hdN⟩) = barX p K C := by
    rw [AltFacts2.fixSub_eq_fixedSub]
    exact AltFacts3.fixedSub_barAut_eq_p hp hdp hdN
  rw [hF, CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPLayer_eq_map hp,
    CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPLayer_eq_map hp]
  set φ := toBarX p hCK with hφ
  have hφs : Function.Surjective φ := toBarX_surjective p hCK
  rw [← CFSG.ComponentClassification.UnbalancingLocal.Correspondence.map_pLayer_of_coprime_kernel φ hφs
    (not_dvd_card_ker_toBarX hp hCK), Subgroup.map_map]
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨⟨(x : G), hCK x.2⟩, Subgroup.mem_subgroupOf.2 ⟨x, hx, rfl⟩, rfl⟩

theorem exists_component_image {p : ℕ} (hp : p.Prime) {K : Subgroup G} {d : G}
    (hdN : d ∈ Subgroup.normalizer (K : Set G)) (hdp : d ^ p = 1) {J : Subgroup G}
    (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({d} : Set G)) J) :
    ∃ Q : Subgroup (barOf p K), GLAPComponent p (fixSub (barAut p K ⟨d, hdN⟩)) Q ∧
      Nonempty (barOf p J ≃* barOf p Q) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set C : Subgroup G := K ⊓ Subgroup.centralizer ({d} : Set G) with hC
  have hCK : C ≤ K := inf_le_left
  have hF : fixSub (barAut p K ⟨d, hdN⟩) = barX p K C := by
    rw [AltFacts2.fixSub_eq_fixedSub]
    exact AltFacts3.fixedSub_barAut_eq_p hp hdp hdN
  set φ := toBarX p hCK with hφ
  have hφs : Function.Surjective φ := toBarX_surjective p hCK
  obtain ⟨hJC, hL⟩ := (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent hp).1 hJ
  have hbij := CFSG.ComponentClassification.CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
    φ hφs (not_dvd_card_ker_toBarX hp hCK)
  set L : Subgroup ↥C := J.subgroupOf C with hLdef
  set M : Subgroup ↥(barX p K C) := L.map φ with hM
  have hMc : CFSG.IsPComponent p M := hbij.1.mapsTo hL
  obtain ⟨e, -⟩ := hbij.2.2 L hL
  set Q : Subgroup (barOf p K) := M.map (barX p K C).subtype with hQ
  have hQsub : Q.subgroupOf (barX p K C) = M :=
    Subgroup.comap_map_eq_self_of_injective (barX p K C).subtype_injective M
  refine ⟨Q, ?_, ?_⟩
  · rw [hF]
    refine (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent hp).2
      ⟨Subgroup.map_subtype_le _, ?_⟩
    rw [hQsub]
    exact hMc
  · have e1 : ↥J ⧸ CFSG.pPrimeCore p ↥J ≃* ↥L ⧸ CFSG.pPrimeCore p ↥L :=
      CFSG.ComponentClassification.UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr p
        (Subgroup.subgroupOfEquivOfLe hJC).symm
    have e2 : ↥M ⧸ CFSG.pPrimeCore p ↥M ≃* ↥Q ⧸ CFSG.pPrimeCore p ↥Q :=
      CFSG.ComponentClassification.UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr p
        (M.equivMapOfInjective _ (barX p K C).subtype_injective)
    exact ⟨(e1.trans e).trans e2⟩

theorem isAltType_center_congr {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y') {n : ℕ}
    (h : IsAltType n (Y' ⧸ Subgroup.center Y')) : IsAltType n (Y ⧸ Subgroup.center Y) := by
  obtain ⟨f⟩ := h
  exact ⟨(QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans f⟩

@[expose] def Input23_4Q : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    GLAPPrimeCore p Y = ⊥ → ∀ n : ℕ, 5 ≤ n → IsAltType n (Y ⧸ Subgroup.center Y) → ¬ p ∣ n →
    ∀ A : Subgroup (MulAut Y), IsElemAbelian p A → A ≠ ⊥ →
      ((⊤ : Subgroup Y) ≤ ⨆ (α : MulAut Y) (_ : α ∈ A) (_ : α ≠ 1),
          (GLAPPrimeCoreOf p (fixSub α) ⊔ GLAPLayer p (fixSub α)) ∨ Nat.card A < n) ∧
      (∀ α ∈ A, α ≠ 1 → ∀ J : Subgroup Y, GLAPComponent p (fixSub α) J →
        ∃ n' : ℕ, 5 ≤ n' ∧ n' < n ∧ n' % p = n % p ∧
          IsAltType n' (barOf p J ⧸ Subgroup.center (barOf p J)))

theorem input23_4_of_Q (h : Input23_4Q) : Lemma123.Input23_4 := by
  intro G _ _ p hp hp2 X K B hK hBX hBn hBel hBne hfaith n hn5 hn hpn
  haveI : Fact p.Prime := ⟨hp⟩
  have hqs : CFSG.Open.IsQuasisimple (barOf p K) :=
    CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hK
  have hO : GLAPPrimeCore p (barOf p K) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hAne : autBar p B K ≠ ⊥ := by
    intro h0
    apply hBne
    have h1 := card_autBar hBn hfaith
    rw [h0, Subgroup.card_bot] at h1
    exact Subgroup.eq_bot_of_card_eq _ h1.symm
  obtain ⟨h1, h2⟩ := h p hp hp2 (barOf p K) hqs hO n hn5 hn hpn (autBar p B K)
    (Lemma123.isElemAbelian_autBar hBel) hAne
  refine ⟨?_, ?_⟩
  · rcases h1 with hgen | hlt
    · left
      set H : Subgroup G := ⨆ (e : G) (_ : e ∈ B) (_ : e ≠ 1), Lemma123.Ke' p K e with hH
      have hKeK : ∀ e : G, Lemma123.Ke' p K e ≤ K := fun e =>
        sup_le ((gLAPPrimeCoreOf_le p _).trans inf_le_left)
          ((CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPLayer_le p _).trans inf_le_left)
      have hHK : H ≤ K := iSup_le fun e => iSup_le fun _ => iSup_le fun _ => hKeK e
      have hKe_le : ∀ e ∈ B, e ≠ 1 → Lemma123.Ke' p K e ≤ H := fun e he he1 =>
        le_iSup_of_le e (le_iSup_of_le he (le_iSup_of_le he1 le_rfl))
      have htop : barX p K H = ⊤ := by
        refine eq_top_iff.2 (hgen.trans (iSup_le fun α => iSup_le fun hα => iSup_le fun hα1 => ?_))
        obtain ⟨b, hbB, hbN, hb1, rfl⟩ := exists_of_mem_autBar hBn hα hα1
        have hbp : b ^ p = 1 := hBel.2 b hbB
        refine sup_le ?_ ?_
        · intro y hy
          obtain ⟨c, hcK, hcC, hcy⟩ := lift_core hp hbN hbp hy
          exact ⟨⟨c, hcK⟩, Subgroup.mem_subgroupOf.2 (hKe_le b hbB hb1 (Subgroup.mem_sup_left hcC)),
            hcy⟩
        · refine (layer_fixSub_le hp hbN hbp).trans (barX_mono ?_)
          exact le_sup_right.trans (hKe_le b hbB hb1)
      have hcov := (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.barX_eq_top_iff p hHK).1 htop
      exact ((barX_eq_iff_cov hp hK.2.1 hHK).2 hcov).ge
    · right
      rwa [card_autBar hBn hfaith] at hlt
  · intro e he he1 J hJ
    have heN : e ∈ Subgroup.normalizer (K : Set G) := hBn he
    have hep : e ^ p = 1 := hBel.2 e he
    obtain ⟨Q, hQ, ⟨eJ⟩⟩ := exists_component_image hp heN hep hJ
    have hα : barAut p K ⟨e, heN⟩ ∈ autBar p B K := by
      rw [autBar_eq_range hBn]
      exact ⟨⟨e, he⟩, rfl⟩
    have hα1 : barAut p K ⟨e, heN⟩ ≠ 1 := by
      intro h0
      apply he1
      have hinj := injective_barAut hBn hfaith
      have : ((barAut p K).comp (Subgroup.inclusion hBn)) ⟨e, he⟩ = 1 := h0
      exact congrArg Subtype.val (hinj (this.trans (map_one _).symm))
    obtain ⟨n', h5, hlt, hmod, hAlt⟩ := h2 _ hα hα1 Q hQ
    exact ⟨n', h5, hlt, hmod, isAltType_center_congr eJ hAlt⟩

theorem not_isLocallyOTwoBalanced_of_map {p : ℕ} {M M' : Type*} [Group M] [Group M'] [Finite M]
    [Finite M']
    (Φ : MulAut M →* MulAut M') (hΦ : Function.Injective Φ)
    (hinn : innerAut M' ≤ (innerAut M).map Φ) {A : Subgroup (MulAut M)} {A' : Subgroup (MulAut M')}
    (hAA : A.map Φ ≤ A') (hA : ¬ IsLocallyOTwoBalanced p 1 A) : ¬ IsLocallyOTwoBalanced p 1 A' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (MulAut M') :=
    Finite.of_injective (fun α : MulAut M' => (α : M' → M')) fun _ _ h => MulEquiv.ext (congrFun h)
  haveI : Finite (MulAut M) :=
    Finite.of_injective (fun α : MulAut M => (α : M → M)) fun _ _ h => MulEquiv.ext (congrFun h)
  intro hA'
  apply hA
  intro D hD H hH hDH
  obtain ⟨hDA, hDel, hDc⟩ := hD
  have hD' : CFSG.HardMathSupport.Solomon.Coordinator.IsEkIn p 1 A' (D.map Φ) :=
    ⟨(Subgroup.map_mono hDA).trans hAA, CFSG.SectionRank.isElemAbelian_map hDel Φ,
      by rw [Subgroup.card_map_of_injective hΦ, hDc]⟩
  have hH' : innerAut M' ≤ H.map Φ := hinn.trans (Subgroup.map_mono hH)
  have hDH' : D.map Φ ≤ Subgroup.normalizer ((H.map Φ : Subgroup (MulAut M')) : Set (MulAut M')) :=
    (Subgroup.map_mono hDH).trans (Subgroup.le_normalizer_map Φ)
  have h0 := hA' (D.map Φ) hD' (H.map Φ) hH' hDH'
  have hle : (localDeltaTwoIn H D).map Φ ≤ localDeltaTwoIn (H.map Φ) (D.map Φ) := by
    unfold localDeltaTwoIn
    refine le_iInf fun d' => le_iInf fun hd' => le_iInf fun hd'1 => ?_
    obtain ⟨d, hdD, rfl⟩ := hd'
    have hd1 : d ≠ 1 := by
      rintro rfl
      exact hd'1 (map_one Φ)
    set S : Subgroup (MulAut M) := H ⊓ Subgroup.centralizer ({d} : Set (MulAut M)) with hS
    have hSmap : S.map Φ = H.map Φ ⊓ Subgroup.centralizer ({Φ d} : Set (MulAut M')) := by
      apply le_antisymm
      · rintro _ ⟨x, ⟨hxH, hxd⟩, rfl⟩
        refine ⟨⟨x, hxH, rfl⟩, ?_⟩
        have hxd' : x ∈ Subgroup.centralizer ({d} : Set (MulAut M)) := hxd
        rw [Subgroup.mem_centralizer_singleton_iff] at hxd'
        show Φ x ∈ Subgroup.centralizer ({Φ d} : Set (MulAut M'))
        rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hxd']
      · rintro _ ⟨⟨x, hxH, rfl⟩, hxd⟩
        refine ⟨x, ⟨hxH, ?_⟩, rfl⟩
        have hxd' : Φ x ∈ Subgroup.centralizer ({Φ d} : Set (MulAut M')) := hxd
        rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul] at hxd'
        show x ∈ Subgroup.centralizer ({d} : Set (MulAut M))
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hΦ hxd'
    have h1 : (⨅ (e : MulAut M) (_ : e ∈ D) (_ : e ≠ 1),
        pCoreOf 2 (H ⊓ Subgroup.centralizer ({e} : Set (MulAut M)))).map Φ ≤
        (pCoreOf 2 S).map Φ :=
      Subgroup.map_mono ((iInf_le _ d).trans ((iInf_le _ hdD).trans (iInf_le _ hd1)))
    refine h1.trans ?_
    rw [← hSmap]
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (Subgroup.map_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 S)) ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 S).map Φ)
    exact (Subgroup.map_mono (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 S)).trans
      (Subgroup.le_normalizer_map Φ)
  rw [h0] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective _ hΦ).1 (le_bot_iff.1 hle)

@[expose] noncomputable def quotAut {Q : Type*} [Group Q] (N : Subgroup Q) [N.Normal]
    (hN : ∀ α : MulAut Q, N.map α.toMonoidHom = N) : MulAut Q →* MulAut (Q ⧸ N) where
  toFun α := QuotientGroup.congr N N α (hN α)
  map_one' := by
    apply MulEquiv.ext
    intro x
    refine QuotientGroup.induction_on x ?_
    intro y
    simp [QuotientGroup.congr]
  map_mul' := by
    intro a b
    apply MulEquiv.ext
    intro x
    refine QuotientGroup.induction_on x ?_
    intro y
    simp [QuotientGroup.congr]

theorem quotAut_mk {Q : Type*} [Group Q] (N : Subgroup Q) [N.Normal]
    (hN : ∀ α : MulAut Q, N.map α.toMonoidHom = N) (α : MulAut Q) (q : Q) :
    quotAut N hN α (QuotientGroup.mk q) = QuotientGroup.mk (α q) := rfl

@[expose] def Input18_3_eqv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 → ∀ (C K B : Subgroup G),
    GLAPComponent p C K → IsElemAbelian p B → B ≤ C →
    ∀ b ∈ B, b ≠ 1 → ∀ hbC : b ∈ C,
      (b ∉ Subgroup.normalizer (K : Set G) ∨ ∀ q ∈ barX p C K,
        QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨b, hbC⟩ * q =
          q * QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨b, hbC⟩) →
      ∀ J : Subgroup G, GLAPComponent p (C ⊓ Subgroup.centralizer ({b} : Set G)) J →
        barX p C J ≤ barX p C (⨆ y ∈ B, GLBConj y K) →
          ∃ π : barOf p K →* barOf p J, Function.Surjective π ∧
            π.ker ≤ Subgroup.center (barOf p K) ∧
            ∀ x ∈ B, ∀ hxK : x ∈ Subgroup.normalizer (K : Set G),
              ∃ hxJ : x ∈ Subgroup.normalizer (J : Set G),
                ∀ k : barOf p K, π (barAut p K ⟨x, hxK⟩ k) = barAut p J ⟨x, hxJ⟩ (π k)

@[expose] def InputDiagBalanceC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 → ∀ (C K B : Subgroup G),
    GLAPComponent p C K → IsElemAbelian p B → B ≤ C → ¬ IsCompLocallyOTwoBalanced p 1 B K →
    IsCyclic ↥(Subgroup.center (barOf p K)) →
    ∀ b ∈ B, b ≠ 1 → ∀ hbC : b ∈ C,
      (b ∉ Subgroup.normalizer (K : Set G) ∨ ∀ q ∈ barX p C K,
        QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨b, hbC⟩ * q =
          q * QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨b, hbC⟩) →
      ∀ J : Subgroup G, GLAPComponent p (C ⊓ Subgroup.centralizer ({b} : Set G)) J →
        barX p C J ≤ barX p C (⨆ y ∈ B, GLBConj y K) →
          ¬ IsCompLocallyOTwoBalanced p 1 B J ∧ ¬ IsLocallyOTwoBalancedWrtP p 1 (barOf p J)

@[expose] def InputCyclicCentre : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    GLAPPrimeCore p Y = ⊥ →
    ((∃ q : ℕ, q.Prime ∧ CFSG.Yardstones.Md0ec50421ce4.IsChevSimple q (Y ⧸ Subgroup.center Y)) ∨
      (∃ n : ℕ, 5 ≤ n ∧ IsAltType n (Y ⧸ Subgroup.center Y)) ∨
      (∃ s : TauCeti.SporadicName, IsSporType s (Y ⧸ Subgroup.center Y))) →
    ¬ IsLocallyOTwoBalancedWrtP p 1 Y → IsCyclic ↥(Subgroup.center Y)

theorem inputDiagBalanceC_of_eqv (h : Input18_3_eqv) : InputDiagBalanceC := by
  intro G _ _ p hp hp2 C K B hK hBel hBC hbal hcyc b hbB hb1 hbC hcase J hJ hJL
  obtain ⟨π, hπs, hπk, hπe⟩ := h G p hp hp2 C K B hK hBel hBC b hbB hb1 hbC hcase J hJ hJL
  have hqK : CFSG.Open.IsQuasisimple (barOf p K) :=
    CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hK
  have hperf : commutator (barOf p K) = ⊤ := hqK.1
  set N : Subgroup (barOf p K) := π.ker with hNdef
  have hN : ∀ α : MulAut (barOf p K), N.map α.toMonoidHom = N := by
    intro α
    haveI := hcyc
    have hZ : (Subgroup.center (barOf p K)).map α.toMonoidHom = Subgroup.center (barOf p K) :=
      Subgroup.map_center_eq α
    have h1 : N.map α.toMonoidHom ≤ Subgroup.center (barOf p K) := hZ ▸ Subgroup.map_mono hπk
    have hcard : Nat.card (N.map α.toMonoidHom) = Nat.card N :=
      Subgroup.card_map_of_injective α.injective
    have h2 : (N.map α.toMonoidHom).subgroupOf (Subgroup.center (barOf p K)) =
        N.subgroupOf (Subgroup.center (barOf p K)) := by
      rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe h1).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hπk).toEquiv, hcard]
    rw [Subgroup.subgroupOf_inj, inf_eq_left.2 h1, inf_eq_left.2 hπk] at h2
    exact h2
  set e : barOf p K ⧸ N ≃* barOf p J := QuotientGroup.quotientKerEquivOfSurjective π hπs with he
  have he_mk : ∀ k : barOf p K, e (QuotientGroup.mk k) = π k := fun k => rfl
  set Φ : MulAut (barOf p K) →* MulAut (barOf p J) :=
    (MulAut.congr e).toMonoidHom.comp (quotAut N hN) with hΦdef
  have hΦ : ∀ (α : MulAut (barOf p K)) (k : barOf p K), Φ α (π k) = π (α k) := by
    intro α k
    show e (quotAut N hN α (e.symm (π k))) = π (α k)
    have h1 : e.symm (π k) = QuotientGroup.mk k := by
      rw [MulEquiv.symm_apply_eq, he_mk]
    rw [h1, quotAut_mk, he_mk]
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro α hα
    apply quotientCenterAut'_injective hperf
    rw [map_one]
    apply MulEquiv.ext
    intro x
    refine QuotientGroup.induction_on x ?_
    intro y
    have h1 : π (α y) = π y := by
      rw [← hΦ, hα]
      rfl
    have h2 : y⁻¹ * α y ∈ Subgroup.center (barOf p K) :=
      hπk (by rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel])
    show (QuotientGroup.mk (α y) : barOf p K ⧸ Subgroup.center (barOf p K)) = QuotientGroup.mk y
    exact (QuotientGroup.eq.2 h2).symm
  have hext : ∀ β γ : MulAut (barOf p J), (∀ k : barOf p K, β (π k) = γ (π k)) → β = γ := by
    intro β γ hβγ
    apply MulEquiv.ext
    intro j
    obtain ⟨k, rfl⟩ := hπs j
    exact hβγ k
  have hinn : innerAut (barOf p J) ≤ (innerAut (barOf p K)).map Φ := by
    rintro _ ⟨j, rfl⟩
    obtain ⟨k, rfl⟩ := hπs j
    refine ⟨MulAut.conj k, ⟨k, rfl⟩, hext _ _ fun k' => ?_⟩
    rw [hΦ, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hAA : (autBar p B K).map Φ ≤ autBar p B J := by
    rintro _ ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩
    have hγB : (γ : G) ∈ B := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hγ)).1
    obtain ⟨hxJ, hxe⟩ := hπe (γ : G) hγB γ.2
    refine ⟨⟨(γ : G), hxJ⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hγB, hxJ⟩), ?_⟩
    refine hext _ _ fun k => ?_
    rw [hΦ]
    exact (hxe k).symm
  haveI : Finite (barOf p J) := inferInstance
  have h1 : ¬ IsCompLocallyOTwoBalanced p 1 B J :=
    not_isLocallyOTwoBalanced_of_map Φ hΦinj hinn hAA hbal
  exact ⟨h1, fun hw => h1 (hw _ (Lemma123.isElemAbelian_autBar hBel))⟩

theorem isCyclic_center_of_cex (hcc : InputCyclicCentre) {m p : ℕ} {B M E A : Subgroup G} {a : G}
    (h : Cex121 G m p B M E A a) {K : Subgroup G} (hK : GLAPComponent p (Cg a) K)
    (hbal : ¬ IsCompLocallyOTwoBalanced p 1 (E ⊓ A) K) :
    IsCyclic ↥(Subgroup.center (barOf p K)) := by
  have hp : p.Prime := h.standing.prime
  have hq : CFSG.Open.IsQuasisimple (barOf p K) :=
    CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hK
  have hO : GLAPPrimeCore p (barOf p K) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hbalP : ¬ IsLocallyOTwoBalancedWrtP p 1 (barOf p K) := fun hb =>
    hbal (hb _ (Lemma123.isElemAbelian_autBar (Lemma123.isElemAbelian_inter h.toSec11)))
  exact hcc p hp h.standing.ne_two (barOf p K) hq hO (Lemma123.type_trichotomy123 h hK) hbalP

end Components

section Corrected

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G}

open Lemma123 in
theorem layer_le_C {p : ℕ} (hp : p.Prime) {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (hSec : Sec11 G m p B M E A) (ha : a ∈ A) (ha1 : a ≠ 1)
    (hnotD : ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1)
    (hK : GLAPComponent p (Cg a) K) (hbal : ¬ IsCompLocallyOTwoBalanced p 1 (E ⊓ A) K)
    (hDiag : InputDiagBalanceC) (h115 : Prop115Statement)
    (hcyc : IsCyclic ↥(Subgroup.center (barOf p K)))
    {b : G} (hbA0 : b ∈ E ⊓ A) (hb1 : b ≠ 1) (hbC : b ∈ Cg a)
    (hbp : IsPGroup p (Subgroup.zpowers b))
    (hbad : b ∉ Subgroup.normalizer (K : Set G) ∨ ∀ q ∈ barX p (Cg a) K,
      QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) ⟨b, hbC⟩ * q =
        q * QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) ⟨b, hbC⟩)
    {L : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a))} (hL : IsSubnormal L ⊤)
    (hLK : L ≤ barX p (Cg a) (⨆ y ∈ E ⊓ A, GLBConj y K))
    {Q : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a))}
    (hQ : GLAPComponent p (L ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) ⟨b, hbC⟩} :
        Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) Q) :
    Q ≤ barX p (Cg a) M := by
  obtain ⟨P, hP, hPQ, -⟩ := l119_layer_piece hp hbC hbp hL hQ
  have hQL : Q ≤ L := hQ.1.trans inf_le_left
  have hPK : barX p (Cg a) P ≤ barX p (Cg a) (⨆ y ∈ E ⊓ A, GLBConj y K) := hPQ ▸ hQL.trans hLK
  obtain ⟨hb1', hb2'⟩ := hDiag G p hp hSec.standing.ne_two (Cg a) K (E ⊓ A) hK
    (isElemAbelian_inter hSec) (inter_le_cg' hSec ha) hbal hcyc b hbA0 hb1 hbC hbad P hP hPK
  have hJ : GLAPComponent p (Cg2 b a) P := by
    unfold Cg2
    rw [l119_cg2_eq]
    exact hP
  rcases h115 hSec ha ha1 hbA0 hb1 hJ hb2'
      (fun _ _ => not_isCompLocallyOTwoBalanced_mono (inf_le_right : E ⊓ A ≤ A) hb1') with hPM | ⟨A1, hA1, haA1⟩
  · rw [← hPQ]
    exact barX_mono hPM
  · exact absurd ⟨A1, hA1, haA1⟩ hnotD


open Lemma123 in
theorem no_bad_C {p : ℕ} {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (hp : p.Prime) (hSec : Sec11 G m p B M E A) (ha : a ∈ A) (ha1 : a ≠ 1)
    (hK : GLAPComponent p (Cg a) K) (hKM : ¬ K ≤ M)
    (hnotD : ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1)
    (hbal : ¬ IsCompLocallyOTwoBalanced p 1 (E ⊓ A) K)
    (h111 : Prop111Statement) (hI22 : Input22_3_2) (hDiag : InputDiagBalanceC)
    (h115 : Prop115Statement) (hcyc : IsCyclic ↥(Subgroup.center (barOf p K))) :
    ¬ ∃ z : ↥(Cg a), (z : G) ∈ E ⊓ A ∧ (z : G) ≠ 1 ∧
      ((z : G) ∉ Subgroup.normalizer (K : Set G) ∨
        ∀ q ∈ barX p (Cg a) K, QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z * q =
          q * QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  rintro ⟨z₀, hz₀A, hz₀1, hbad⟩
  obtain ⟨hDDp, -⟩ := hSec.pair
  obtain ⟨-, hDp, hrA0⟩ := hDDp
  obtain ⟨hSCs, -⟩ := hDp
  obtain ⟨hSCp, -⟩ := hSCs
  obtain ⟨-, hAel, -⟩ := hSCp
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hApow : ∀ x ∈ A, x ^ p = 1 := fun x hx => hAel.2 x hx
  have hACg : A ≤ Cg a := fun x hx => by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hAcomm a ha x hx
  set A0 : Subgroup G := E ⊓ A with hA0
  have hA0A : A0 ≤ A := inf_le_right
  have hA0C : A0 ≤ Cg a := hA0A.trans hACg
  have hA0el : IsElemAbelian p A0 := l119_isElemAbelian_of_le hA0A hAel
  have hrA0 : 2 ≤ CFSG.Open.pRank p A0 := hrA0
  set A0C : Subgroup ↥(Cg a) := A0.subgroupOf (Cg a) with hA0Cdef
  set Bbar : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) :=
    A0C.map (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a))) with hBbar
  set Kb : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) := barX p (Cg a) K with hKb
  set 𝓛 := Fam123 p (Cg a) K A0C with h𝓛def
  set Yb : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) := sSup 𝓛 with hYb
  have hKbc : IsComponentOf Kb ⊤ := l119_isComponent_barX hK
  have hKbmem : Kb ∈ 𝓛 := fam123_base p (Cg a) K A0C
  have h𝓛c : ∀ X ∈ 𝓛, IsComponentOf X ⊤ := fam123_comp hK A0C
  have hcomm𝓛 : ∀ X ∈ 𝓛, ∀ X' ∈ 𝓛, X ≠ X' → ∀ x ∈ X, ∀ y ∈ X', x * y = y * x := by
    rintro X ⟨w, -, rfl⟩ X' ⟨w', -, rfl⟩ hne x hx y hy
    exact l119_conj_comm hK hne hx hy
  have hYsub : IsSubnormal Yb ⊤ := l119_isSubnormal_sSup_components h𝓛c
  have hYcomp : ∀ X ∈ 𝓛, IsComponentOf X Yb := fun X hX => l119_isComponentOf_sSup h𝓛c hcomm𝓛 hX
  have hBcomm : ∀ z ∈ A0C, ∀ w ∈ A0C,
      QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z * QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) w =
        QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) w * QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z := by
    intro z hz w hw
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hAcomm _ (hA0A ((Subgroup.mem_subgroupOf).1 hz)) _ (hA0A ((Subgroup.mem_subgroupOf).1 hw))
  have hBnorm : Bbar ≤ Subgroup.normalizer ((Yb : Subgroup _) : Set _) := by
    rintro _ ⟨z, hz, rfl⟩
    exact bar_normalizes123 A0C hz
  have hA0Cel : IsElemAbelian p A0C := l119_isElemAbelian_subgroupOf hA0el (Cg a)
  have hBel : IsElemAbelian p Bbar :=
    CFSG.SectionRank.isElemAbelian_map hA0Cel _
  have hB_rank : 2 ≤ CFSG.Open.pRank p Bbar := le_trans hrA0 (l119_pRank_image_ge hp hA0C hA0el)
  have hKbe : (↥K ⧸ GLAPPrimeCore p ↥K) ≃* ↥Kb := quotEquivBarX hp hK.1 hK.2.1
  have hpY : p ∣ Nat.card ↥Yb :=
    dvd_trans (by rw [← Nat.card_congr hKbe.toEquiv]; exact p_dvd_card_barOf hp hK)
      (Subgroup.card_dvd_of_le (le_sSup hKbmem))
  have htrans : ∀ X ∈ 𝓛, ∀ X' ∈ 𝓛, ∃ b ∈ Bbar, GLBConj b X = X' := by
    rintro X ⟨w, hw, rfl⟩ X' ⟨w', hw', rfl⟩
    exact ⟨QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) (w⁻¹ * w'),
      Subgroup.mem_map_of_mem _ (A0C.mul_mem (A0C.inv_mem hw) hw'), l119_conj_trans w w'⟩
  have hz₀C : z₀ ∈ A0C := Subgroup.mem_subgroupOf.2 hz₀A
  have hb₀B : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀ ∈ Bbar :=
    Subgroup.mem_map_of_mem _ hz₀C
  have hz₀pow : z₀ ^ p = 1 := by
    apply Subtype.ext
    simpa using hApow _ hz₀A.2
  have hb₀1 : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀ ≠ 1 := by
    intro h
    apply hz₀1
    have h2 := l119_eq_one_of_pow_of_mem_core hp hz₀pow ((QuotientGroup.eq_one_iff _).1 h)
    simpa using congrArg Subtype.val h2
  have hJb₀ : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀ ∈ Subgroup.centralizer (Yb : Set _) ∨
      QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀ ∉ Subgroup.normalizer (Kb : Set _) := by
    rcases hbad with hN | hC
    · right
      intro hb
      exact hN (l119_mem_normalizer_of_bar hp hK z₀ hb)
    · left
      have hYc : Yb ≤ Subgroup.centralizer
          ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀} : Set _) := by
        refine sSup_le fun X hX => ?_
        obtain ⟨w, hw, rfl⟩ := hX
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [Set.mem_singleton_iff] at hg
        rw [hg]
        exact l119_centralizes_gLBConj (hBcomm z₀ hz₀C w hw) hC x hx
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have h2 := hYc hh
      rw [Subgroup.mem_centralizer_iff] at h2
      exact (h2 _ (Set.mem_singleton _)).symm
  have hLayer : ∀ b ∈ Bbar, b ≠ 1 → (b ∈ Subgroup.centralizer (Yb : Set _) ∨
      b ∉ Subgroup.normalizer (Kb : Set _)) →
      GLAPLayer p (Yb ⊓ Subgroup.centralizer ({b} : Set _)) ≤ barX p (Cg a) M := by
    intro b hb hb1 hJ
    have hbB := hb
    obtain ⟨z, hz, rfl⟩ := hb
    have hzA : (z : G) ∈ A0 := Subgroup.mem_subgroupOf.1 hz
    have hz1 : (z : G) ≠ 1 := by
      intro h
      apply hb1
      have hzeq : z = 1 := Subtype.ext h
      rw [hzeq, map_one]
    have hzpow : (z : G) ^ p = 1 := hApow _ hzA.2
    have hzC : (z : G) ∈ Cg a := z.2
    have hzp : IsPGroup p (Subgroup.zpowers (z : G)) := l119_isPGroup_zpowers hzpow
    have hzpow' : z ^ p = 1 := by
      apply Subtype.ext
      simpa using hzpow
    have hbord : orderOf (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z) = p := by
      apply orderOf_eq_prime
      · rw [← map_pow, hzpow', map_one]
      · exact hb1
    have hbad : (z : G) ∉ Subgroup.normalizer (K : Set G) ∨ ∀ q ∈ barX p (Cg a) K,
        QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) ⟨(z : G), hzC⟩ * q =
          q * QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) ⟨(z : G), hzC⟩ := by
      rcases hJ with hC | hN
      · right
        intro q hq
        exact ((Subgroup.mem_centralizer_iff.1 hC) q (le_sSup hKbmem hq)).symm
      · left
        intro hzN
        exact hN (mk_mem_normalizer_barX hK.1 hzN)
    have hYK : Yb ≤ barX p (Cg a) (⨆ y ∈ E ⊓ A, GLBConj y K) := by
      refine sSup_le fun X hX => ?_
      obtain ⟨w, hw, rfl⟩ := hX
      have hwA : (w : G) ∈ E ⊓ A := Subgroup.mem_subgroupOf.1 hw
      have h1 := l119_barX_gLBConj (p := p) (C := Cg a) (g := (w : G)) w.2 hK.1
      refine le_of_eq_of_le h1.symm (barX_mono ?_)
      exact le_iSup₂_of_le (w : G) hwA le_rfl
    unfold GLAPLayer
    refine sSup_le fun Q hQ => ?_
    exact layer_le_C hp hSec ha ha1 hnotD hK hbal hDiag h115 hcyc hzA hz1 hzC hzp hbad hYsub hYK hQ
  have hYM : Yb ≤ barX p (Cg a) M := by
    have hI22' := hI22 (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) p hp Bbar Yb Kb 𝓛 hBel hBnorm
      hKbmem hB_rank hpY rfl hYcomp hcomm𝓛 htrans
      ⟨QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀, hb₀B, hb₀1, hJb₀⟩
    rw [hI22']
    refine sSup_le ?_
    rintro Z ⟨b, hb, hb1, hJ, rfl⟩
    exact hLayer b hb hb1 hJ
  have hKM' : barX p (Cg a) K ≤ barX p (Cg a) M := le_trans (le_sSup hKbmem) hYM
  apply hKM
  intro k hk
  obtain ⟨m, hm, hmk⟩ := exists_of_barX_le hKM' hk (hK.1 hk)
  have hmM : m⁻¹ * k ∈ M := h111 hSec ha ha1 hmk
  have := M.mul_mem hm hmM
  simpa using this


open Lemma123 in
theorem prep123_C (h111 : Prop111Statement) (h122 : Lemma122_i_iiStatement)
    (h115 : Prop115Statement) (hI191 : Lemma136c.Input19_1_O2) (hI22 : Input22_3_2)
    (hDiag : InputDiagBalanceC) (hcc : InputCyclicCentre) (h : Cex121 G m p B M E A a) :
    ∃ (K D : Subgroup G) (r : ℕ), Prep123 G m p B M E A a K D r := by
  obtain ⟨K, D, r, P⟩ := prep123a h111 h122 hI191 h
  have hp : p.Prime := h.standing.prime
  have hSec : Sec11 G m p B M E A := h.toSec11
  have ha : a ∈ A := h.ha.1
  have ha1 : a ≠ 1 := h.ha.2
  have hnotD : ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1 := lemma122_ii_of_cex h
  have hbal1 : ¬ IsCompLocallyOTwoBalanced p 1 (E ⊓ A) K :=
    not_isCompLocallyOTwoBalanced_one hp P.hr P.hDA P.hbal
  have hno := no_bad_C hp hSec ha ha1 P.hK P.hKM hnotD hbal1 h111 hI22 hDiag h115
    (isCyclic_center_of_cex hcc h P.hK hbal1)
  have hACg : E ⊓ A ≤ Cg a := inter_le_cg h
  have hgood : ∀ x (hxA : x ∈ E ⊓ A), x ≠ 1 →
      x ∈ Subgroup.normalizer (K : Set G) ∧
        ¬ (∀ q ∈ barX p (Cg a) K, QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) ⟨x, hACg hxA⟩ * q =
          q * QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) ⟨x, hACg hxA⟩) := by
    intro x hxA hx1
    have h2 : ¬ (x ∉ Subgroup.normalizer (K : Set G) ∨
        ∀ q ∈ barX p (Cg a) K, QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) ⟨x, hACg hxA⟩ * q =
          q * QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) ⟨x, hACg hxA⟩) :=
      fun hc => hno ⟨⟨x, hACg hxA⟩, hxA, hx1, hc⟩
    refine ⟨?_, fun hall => h2 (Or.inr hall)⟩
    by_contra hN
    exact h2 (Or.inl hN)
  have hA0N : E ⊓ A ≤ Subgroup.normalizer (K : Set G) := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact Subgroup.one_mem _
    · exact (hgood x hx hx1).1
  refine ⟨K, D, r, ⟨P, hA0N, ?_⟩⟩
  intro x hx hc
  by_contra hx1
  obtain ⟨γ, hγ, hγx⟩ := Subgroup.mem_map.1 (Subgroup.mem_inf.1 hc).1
  have hbar : barAut p K ⟨x, hA0N hx⟩ = 1 := by
    have hxγ : (⟨x, hA0N hx⟩ : ↥(Subgroup.normalizer (K : Set G))) = γ := Subtype.ext hγx.symm
    rw [hxγ]
    exact MonoidHom.mem_ker.1 hγ
  obtain ⟨_, hnc⟩ := hgood x hx hx1
  exact hnc (l119_centralizes_of_barAut hp P.hK (hACg hx) (hA0N hx) hbar)


theorem lemma123_of_inputs_C
    (h112 : Prop112Statement) (h115 : Prop115Statement)
    (h117 : Prop117_cex_falseStatement) (h122 : Lemma122_i_iiStatement) (h1116 : Prop1116StrongStatement)
    (hI185 : Sec12a.Input18_5) (hI191 : Lemma136c.Input19_1_O2) (hI191img : Lemma123.Input19_1_O2_img)
    (hI22 : Input22_3_2) (hI183 : Input18_3_eqv) (hcc : InputCyclicCentre)
    (hI196 : Lemma123.Input19_6_4)
    (hI1917a : Lemma123.Input19_17_1c) (hI234Q : Input23_4Q) (hSchurAlt : Lemma123.InputSchurAlt')
    (hL27 : Prop1116.InputNotL27Pi)
    (hI1917s : Lemma123.Input19_17_2) (hI2324Q : Input23_24Q) (hSchurFi : Lemma123.InputSchurFi22)
    (hCore : CFSG.LieType.ChevTwo.Chev2CoreCent) (hKD : CFSG.LieType.ChevTwo.Chev2KDOut)
    (hI1916 : Lemma123.Input19_16_two)
    (hI7L : Input7_L34)
    (hI197 : Lemma123.Input19_7_3) (hI1918 : Lemma123.Input19_18) (hI272Q : Input27_2Q) :
    Lemma123Statement := by
  have hI2317 : Lemma123.Input23_17 := input23_17_holds
  have hI234 : Lemma123.Input23_4 := input23_4_of_Q hI234Q
  have hI2324 : Lemma123.Input23_24 := input23_24_of_Q hI2324Q
  have hI272 : Lemma123.Input27_2 := input27_2_of_Q hI272Q
  intro G _ _ m p B M E A a h
  obtain ⟨K, D, r, P⟩ := prep123_C (prop111_of_prop112 h112) h122 h115 hI191 hI22
    (inputDiagBalanceC_of_eqv hI183) hcc h
  have hp : p.Prime := h.standing.prime
  have hp2 : p ≠ 2 := h.standing.ne_two
  have hSec : Sec11 G m p B M E A := h.toSec11
  have ha : a ∈ A := h.ha.1
  have ha1 : a ≠ 1 := h.ha.2
  have hiv : Tof p M a ≤ Lstar p (Cg a) := Sec12a.tof_le_lstar_of_inputs h hp hp2 (h122 h).1 hI185
  have key : p = 3 ∧ IsLThreeFour (barOf p K ⧸ Subgroup.center (barOf p K)) ∧
      Nat.card (E ⊓ A : Subgroup G) = 9 ∧ InducesFaithfulInner p (E ⊓ A) K ∧
      ∃ u ∈ Tof p M a ⊓ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G),
        ∃ hu : u ∈ Subgroup.normalizer (K : Set G), IsUnitaryAut (barAut p K ⟨u, hu⟩) := by
    rcases Lemma123.type_trichotomy123 h P.hK with ⟨q, hq, hchev⟩ | ⟨n, hn5, hn⟩ | ⟨s, hs⟩
    · by_cases hqp : q = p
      · rw [hqp] at hchev
        exact (Lemma123.case_chevp h112 hI196 hI2317 P hchev).elim
      · by_cases hq2 : q = 2
        · rw [hq2] at hchev
          by_cases hr1 : r = 1
          · exact (Lemma123.case_chev2_one hI191img h122 (Lemma123.input19_20_1_of_chev2 hCore)
            (Lemma123.input7_12_2_of_chev2 hKD) P hr1 hchev).elim
          · exact Lemma123.case_chev2_ge2 h122 hI191img hI1916 hI7L P (by have := P.hr; omega) hchev
        · exact (Lemma123.case_chev_odd h112 h1116 hI191img h122 hI1918 hI197 hI272 P hq hq2 hqp hchev).elim
    · exact (Lemma123.case_alt h112 h115 h117 hI1917a hI234 hSchurAlt hL27 P hn5 hn).elim
    · exact (Lemma123.case_spor h112 h117 hI191img h122 hI1917s hI2324 hSchurFi P hs).elim
  obtain ⟨hp3, hL34, hcard9, hfaith, hu⟩ := key
  subst hp3
  refine ⟨rfl, K, P.hK, ⟨hL34, ?_⟩, hu, ⟨hcard9, hfaith⟩, hiv⟩
  intro hcov
  have hcore : GLAPPrimeCoreOf 3 (Cg a) ≤ M ⊓ Cg a :=
    le_inf ((prop111_of_prop112 h112) hSec ha ha1) (Subgroup.map_subtype_le _)
  exact P.hKM ((Lemma123.le_M_of_barX_le P.hK.1 hcov hcore).trans inf_le_left)


end Corrected

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs123b

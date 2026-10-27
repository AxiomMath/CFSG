module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3AEta
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AExcl
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AInner
public import CFSG.RankThree.PartTwo.KFacts.K72SLPiAut

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns

theorem fixSub_one {Y : Type*} [Group Y] : fixSub (1 : MulAut Y) = ⊤ := by
  ext y
  simp [mem_fixSub]

theorem fixData_of_congr_eq {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') {α : MulAut Y}
    {β : MulAut Y'} (h : MulAut.congr e α = β) (hF : FixData Y' β) : FixData Y α := by
  have h1 := FixData.congr e.symm hF
  have h2 : MulAut.congr e.symm β = α := by
    rw [← h]
    ext y
    simp [MulAut.congr_apply]
  rwa [h2] at h1

theorem fixData_one {X : Type} [Group X] (hq : CFSG.Open.IsQuasisimple X) (hT : IsL3Type X)
    (hz3 : ∀ z : X, z ∈ Subgroup.center X → z ^ 3 = 1) (h3 : 3 ∣ Nat.card X)
    (he : (∃ z ∈ Subgroup.center X, z ≠ 1) → IsSLThreeEpsAny X) : FixData X 1 := by
  refine ⟨⊤, by rw [fixSub_one], le_top, fun a _ => ⟨0, by simp⟩, ?_, ?_, ?_, ?_, ?_,
    fun z _ => ?_, ?_⟩
  · exact isQuasisimple_open_of_mulEquiv Subgroup.topEquiv hq
  · exact isL3Type_of_mulEquiv Subgroup.topEquiv.symm hT
  · intro z hz
    apply Subtype.ext
    have : (z : X) ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      exact congrArg Subtype.val (hz ⟨g, trivial⟩)
    exact hz3 _ this
  · rw [Nat.card_congr (Subgroup.topEquiv (G := X)).toEquiv]
    exact h3
  · intro z hz
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    exact congrArg Subtype.val (hz ⟨g, trivial⟩)
  · exact Subgroup.mem_top z
  · exact fun hz => ⟨by rw [fixSub_one], isSLThreeEpsAny_of_mulEquiv Subgroup.topEquiv.symm (he hz)⟩

theorem isL3Type_slPi {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) : IsL3Type ↥(slPi π 3 (p ^ f) K) := by
  have := hK.finite
  cases π
  · exact Or.inr ⟨K, inferInstance, inferInstance, p ^ f, by rw [hK.card, piCard, Bool.cond_false],
      hq, Or.inr ⟨MulEquiv.refl _⟩⟩
  · exact Or.inl ⟨K, inferInstance, inferInstance, by rw [hK.card, piCard, Bool.cond_true]; exact hq,
      Or.inr ⟨MulEquiv.refl _⟩⟩

theorem isSLThreeEpsAny_slPi {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) (h2 : 2 < p ^ f) : IsSLThreeEpsAny ↥(slPi π 3 (p ^ f) K) := by
  have := hK.finite
  cases π
  · exact Or.inr ⟨K, inferInstance, inferInstance, p ^ f, by rw [hK.card, piCard, Bool.cond_false],
      hq, by omega, ⟨MulEquiv.refl _⟩⟩
  · exact Or.inl ⟨K, inferInstance, inferInstance, by rw [hK.card, piCard, Bool.cond_true]; exact hq,
      ⟨MulEquiv.refl _⟩⟩

@[expose] noncomputable def barEquiv {Y X : Type*} [Group Y] [Group X] (e : Y ≃* X) :
    (Y ⧸ Subgroup.center Y) ≃* (X ⧸ Subgroup.center X) :=
  QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)

theorem congr_barEquiv {Y X : Type*} [Group Y] [Group X] (e : Y ≃* X) (α : MulAut Y) :
    MulAut.congr (barEquiv e) (centerDescend Y α) = centerDescend X (MulAut.congr e α) := by
  ext x
  obtain ⟨y, rfl⟩ := (barEquiv e).surjective x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  simp only [MulAut.congr_apply]
  rfl

@[expose] noncomputable def barEquivBot {Y : Type*} [Group Y] (hZ : Subgroup.center Y = ⊥) :
    (Y ⧸ Subgroup.center Y) ≃* Y :=
  (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot

theorem congr_barEquivBot {Y : Type*} [Group Y] (hZ : Subgroup.center Y = ⊥) (α : MulAut Y) :
    MulAut.congr (barEquivBot hZ) (centerDescend Y α) = α := by
  ext y
  simp only [MulAut.congr_apply, MulEquiv.trans_apply]
  have : (barEquivBot hZ).symm y = (y : Y ⧸ Subgroup.center Y) := by
    rw [MulEquiv.symm_apply_eq]; rfl
  rw [this, centerDescend_mk]
  rfl

@[expose] noncomputable def conjSL' {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (hπ : π = false → UnitaryFieldData p f K) {h : GL (Fin 3) K} (hh : h ∈ glPi π 3 (p ^ f) K) :
    ↥(slPi π 3 (p ^ f) K) ≃* ↥(slPi π 3 (p ^ f) K) where
  toFun s := ⟨h⁻¹ * s * h, by simpa using conj_mem_slPi hπ (inv_mem hh) s.2⟩
  invFun s := ⟨h * s * h⁻¹, conj_mem_slPi hπ hh s.2⟩
  left_inv s := Subtype.ext (show h * (h⁻¹ * (s : GL (Fin 3) K) * h) * h⁻¹ = s by group)
  right_inv s := Subtype.ext (show h⁻¹ * (h * (s : GL (Fin 3) K) * h⁻¹) * h = s by group)
  map_mul' s t := Subtype.ext (show h⁻¹ * ((s : GL (Fin 3) K) * t) * h =
    h⁻¹ * s * h * (h⁻¹ * t * h) by group)

theorem congr_symm_congr {A B : Type*} [Group A] [Group B] (e : A ≃* B) (x : MulAut A) :
    MulAut.congr e.symm (MulAut.congr e x) = x := by
  ext a
  simp [MulAut.congr_apply]

structure EtaPkg {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K)
    (hq2 : 2 < p ^ f) where
  M : Type
  [inst : Group M]
  P : PinnedAut M
  good : GoodPinned P
  η : (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)) ≃* M
  conj_mem : ∀ (ζ : MulAut ↥(slPi π 3 (p ^ f) K)) (y : GL (Fin 3) K),
    y ∈ glPi π 3 (p ^ f) K →
      (∀ s : ↥(slPi π 3 (p ^ f) K), ((ζ s : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) = y * s * y⁻¹) →
      MulAut.congr η (centerDescend _ ζ) ∈ P.inndiag
  frob_mem : ∀ σ : K ≃+* K, MulAut.congr η (centerDescend _ (frobSL hK σ)) ∈ P.field
  dich : ∀ τ : MulAut M, τ ^ 3 = 1 → τ ∈ P.inndiag ∨ ∃ σ : K ≃+* K, orderOf σ = 3 ∧
    ∃ κ ∈ P.inndiag, τ = κ * MulAut.congr η (centerDescend _ (frobSL hK σ)) * κ⁻¹
  conj_of_inndiag : ∀ τ ∈ P.inndiag, ∃ x ∈ glPi π 3 (p ^ f) K,
    ∀ s t : ↥(slPi π 3 (p ^ f) K), (t : GL (Fin 3) K) = x * s * x⁻¹ →
      MulAut.congr η.symm τ (QuotientGroup.mk s) = QuotientGroup.mk t

attribute [instance] EtaPkg.inst

theorem exists_etaPkg {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K)
    (hq2 : 2 < p ^ f) : Nonempty (EtaPkg hK hq2) := by
  have := hK.finite
  cases π
  ·
    refine ⟨⟨unitaryPSU hK.unitary 3, stdPinnedPSU3 hK.unitary, goodPinned_psu hK.unitary hq2,
      etaFalse hK hq2,
      ?_, ?_, ?_, ?_⟩⟩
    · intro ζ y hy hζ
      rw [congr_eta_false_conj hK hq2 ζ hy hζ]
      exact ⟨_, rfl⟩
    · intro σ
      rw [congr_eta_false_frob hK hq2 σ]
      exact ⟨σ, rfl⟩
    · intro τ hτ
      by_cases hD : τ ∈ (stdPinnedPSU3 hK.unitary).inndiag
      · exact Or.inl hD
      · obtain ⟨σ, hσ, H, hH⟩ := unitary_order_three_field_descent hq2 τ hτ hD
        refine Or.inr ⟨σ, hσ, psuConj hK.unitary H, ⟨_, rfl⟩, ?_⟩
        rw [congr_eta_false_frob hK hq2 σ]
        exact hH
    · rintro τ ⟨H, rfl⟩
      have hy : (H : GL (Fin 3) K) ∈ glPi false 3 (p ^ f) K :=
        (mem_glPi_false hK.unitary).2 (mem_unitaryIsom3.1 H.2)
      have hπ : false = false → UnitaryFieldData p f K := fun _ => hK.unitary
      refine ⟨H, hy, fun s t ht => ?_⟩
      have hc : MulAut.congr (etaFalse hK hq2) (centerDescend _ (conjSL' hπ hy).symm) =
          psuConj hK.unitary H :=
        congr_eta_false_conj hK hq2 (conjSL' hπ hy).symm hy (fun s => rfl)
      have h1 : MulAut.congr (etaFalse hK hq2).symm (psuConj hK.unitary H) =
          centerDescend _ (conjSL' hπ hy).symm := by
        rw [← hc, congr_symm_congr]
      rw [h1, centerDescend_mk]
      congr 1
      exact Subtype.ext ht.symm
  · refine ⟨⟨projectiveSL 3 K, stdPinnedPSL 3 K, goodPinned_psl K, etaTrue (p ^ f) K, ?_, ?_, ?_, ?_⟩⟩
    · intro ζ y hy hζ
      rw [congr_etaTrue_conj (p ^ f) ζ hζ, stdPinnedPSL_inndiag]
      exact conjAut_mem_linearAutGroup y
    · intro σ
      rw [congr_etaTrue_frob hK σ, stdPinnedPSL_field]
      exact ⟨σ, rfl⟩
    · intro τ hτ
      by_cases hD : τ ∈ (stdPinnedPSL 3 K).inndiag
      · exact Or.inl hD
      · obtain ⟨σ, hσ, H, hH⟩ := linear_order_three_field_descent le_rfl τ hτ hD
        refine Or.inr ⟨σ, hσ, conjAut 3 K H, ?_, ?_⟩
        · rw [stdPinnedPSL_inndiag]; exact conjAut_mem_linearAutGroup H
        · rw [congr_etaTrue_frob hK σ]
          exact hH
    · intro τ hτ
      rw [stdPinnedPSL_inndiag, mem_linearAutGroup_iff] at hτ
      obtain ⟨A, rfl⟩ := hτ
      have hπ : true = false → UnitaryFieldData p f K := fun h => by simp at h
      have hy : A ∈ glPi true 3 (p ^ f) K := mem_glPi_true _ _
      refine ⟨A, hy, fun s t ht => ?_⟩
      have hc : MulAut.congr (etaTrue (p ^ f) K) (centerDescend _ (conjSL' hπ hy).symm) =
          conjAut 3 K A :=
        congr_etaTrue_conj (p ^ f) (conjSL' hπ hy).symm (y := A) (fun s => rfl)
      have h1 : MulAut.congr (etaTrue (p ^ f) K).symm (conjAut 3 K A) =
          centerDescend _ (conjSL' hπ hy).symm := by
        rw [← hc, congr_symm_congr]
      rw [h1, centerDescend_mk]
      congr 1
      exact Subtype.ext ht.symm

theorem eq_one_of_inndiag_model {Y : Type*} [Group Y] (hY : CFSG.Open.IsQuasisimple Y)
    {M₁ : Type*} [Group M₁] {P₁ : PinnedAut M₁} (g₁ : GoodPinned P₁)
    (e₁ : (Y ⧸ Subgroup.center Y) ≃* M₁) {α : MulAut Y}
    (h₁ : MulAut.congr e₁ (centerDescend Y α) ∈ P₁.inndiag) (hf : IsFieldAutThree α) :
    α = 1 := by
  rcases hf with h | hL | hU
  · exact h
  · obtain ⟨F, hFf, hFfin, et, σ, γ, he⟩ := fieldAutPSL3_data hL
    exact eq_one_of_centerDescend_eq_one hY
      (eq_one_of_inndiag_of_field g₁ (goodPinned_psl F) e₁ et h₁ ⟨σ, rfl⟩ γ he)
  · obtain ⟨p, f, F, hFf, hF, et, σ, γ, -, he⟩ := fieldAutPSU3_data hU
    have hq := two_lt_pow_of_quasisimple hY hF et
    exact eq_one_of_centerDescend_eq_one hY
      (eq_one_of_inndiag_of_field g₁ (goodPinned_psu hF hq) e₁ et h₁ ⟨σ, rfl⟩ γ he)

theorem congr_trans' {A B C : Type*} [Group A] [Group B] [Group C] (e₁ : A ≃* B) (e₂ : B ≃* C)
    (x : MulAut A) : MulAut.congr (e₁.trans e₂) x = MulAut.congr e₂ (MulAut.congr e₁ x) := by
  ext c
  simp [MulAut.congr_apply]

theorem congr_self {M : Type*} [Group M] (κ : MulAut M) (β : MulAut M) :
    MulAut.congr κ β = κ * β * κ⁻¹ := rfl

theorem fixData_cover {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (h8 : π = false → p ^ f ≠ 8) (hq2 : 2 < p ^ f) (e : Y ≃* ↥(slPi π 3 (p ^ f) K))
    {α : MulAut Y} (h3 : α ^ 3 = 1) (hf : IsFieldAutThree α) : FixData Y α := by
  obtain ⟨pkg⟩ := exists_etaPkg hK hq2
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  by_cases hα : α = 1
  · subst hα
    refine fixData_of_congr_eq e (β := 1) (map_one _) ?_
    exact fixData_one (isQuasisimple_slPi hK (fun _ h => by omega)) (isL3Type_slPi hK hq)
      (fun z hz => pow_three_of_mem_center hK hq hz) (three_dvd_card_slPi hK hq)
      (fun _ => isSLThreeEpsAny_slPi hK hq hq2)
  have hζ3 : MulAut.congr e α ^ 3 = 1 := by rw [← map_pow, h3, map_one]
  rcases exists_conj_or_field_of_pow_three_eq_one hK hq2 hζ3 with ⟨y, hy, hS⟩ | ⟨σ, hσ, H, hH, hζ⟩
  · exfalso
    apply hα
    refine eq_one_of_inndiag_model hY pkg.good ((barEquiv e).trans pkg.η) ?_ hf
    rw [congr_trans', congr_barEquiv]
    exact pkg.conj_mem _ y hy (semiAct_one_iff.1 hS)
  · have hc : MulAut.congr (conjSL' hπ hH) (MulAut.congr e α) = frobSL hK σ := by
      refine MulEquiv.ext fun s => Subtype.ext ?_
      rw [coe_frobSL]
      have h1 : (((conjSL' hπ hH).symm s : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) =
          H * s * H⁻¹ := rfl
      have h2 : ((conjSL' hπ hH ((MulAut.congr e α) ((conjSL' hπ hH).symm s)) :
          ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) =
          H⁻¹ * (((MulAut.congr e α) ((conjSL' hπ hH).symm s) : ↥(slPi π 3 (p ^ f) K)) :
            GL (Fin 3) K) * H := rfl
      show ((conjSL' hπ hH ((MulAut.congr e α) ((conjSL' hπ hH).symm s)) :
          ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) = _
      rw [h2, hζ, h1]
      have h3 : H⁻¹ * (H * (s : GL (Fin 3) K) * H⁻¹) * H = s := by group
      rw [h3]
      group
    exact fixData_of_congr_eq (e.trans (conjSL' hπ hH)) (by rw [congr_trans', hc])
      (fixData_frobSL hK hq h8 hσ)

theorem fixData_proj {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (h8 : π = false → p ^ f ≠ 8) (hq2 : 2 < p ^ f)
    (e : Y ≃* (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)))
    {α : MulAut Y} (h3 : α ^ 3 = 1) (hf : IsFieldAutThree α) : FixData Y α := by
  obtain ⟨pkg⟩ := exists_etaPkg hK hq2
  have hGq : CFSG.Open.IsQuasisimple ↥(slPi π 3 (p ^ f) K) :=
    isQuasisimple_slPi hK (fun _ h => by omega)
  have hGp : Group.IsPerfect ↥(slPi π 3 (p ^ f) K) := (Group.isPerfect_def).2 hGq.1
  have hcQ : Subgroup.center (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot _
  by_cases hα : α = 1
  · subst hα
    refine fixData_of_congr_eq e (β := 1) (map_one _) ?_
    refine fixData_one (isQuasisimple_quotient_center hGq) (isL3Type_slPi_quot hK hq)
      (fun z hz => by rw [hcQ] at hz; rw [Subgroup.mem_bot.1 hz]; exact one_pow 3)
      (three_dvd_card_slPi_quot hK hq) ?_
    rintro ⟨z, hz, hz1⟩
    rw [hcQ] at hz
    exact absurd (Subgroup.mem_bot.1 hz) hz1
  have hZ : Subgroup.center Y = ⊥ := center_eq_bot_of_mulEquiv_of_center_eq_bot e hcQ
  set ε : Y ≃* pkg.M := e.trans pkg.η with hε
  have hβ3 : MulAut.congr ε α ^ 3 = 1 := by rw [← map_pow, h3, map_one]
  rcases pkg.dich _ hβ3 with hin | ⟨σ, hσ, κ, hκ, hβ⟩
  · exfalso
    apply hα
    refine eq_one_of_inndiag_model hY pkg.good ((barEquivBot hZ).trans ε) ?_ hf
    rw [congr_trans', congr_barEquivBot]
    exact hin
  · let e2 : Y ≃* (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)) :=
      (ε.trans κ⁻¹).trans pkg.η.symm
    have hc : MulAut.congr e2 α = centerDescend _ (frobSL hK σ) := by
      have h1 : MulAut.congr e2 α =
          MulAut.congr pkg.η.symm (MulAut.congr κ⁻¹ (MulAut.congr ε α)) := by
        rw [congr_trans', congr_trans']
      rw [h1, hβ, congr_self, inv_inv]
      have h2 : κ⁻¹ * (κ * MulAut.congr pkg.η (centerDescend _ (frobSL hK σ)) * κ⁻¹) * κ =
          MulAut.congr pkg.η (centerDescend _ (frobSL hK σ)) := by group
      rw [h2]
      ext x
      simp [MulAut.congr_apply]
    exact fixData_of_congr_eq e2 hc (fixData_frobSL_proj hK hq h8 hσ)

end CFSG.HardMathSupport.Solomon.Coordinator

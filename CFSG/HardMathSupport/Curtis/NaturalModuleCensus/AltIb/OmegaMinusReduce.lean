module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinusDefs
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ResidualTwistedD.Conj
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ResidualTwistedD.Eichler
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.Blocks
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ResidualTwistedD.FlagSpinM
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinus

open Matrix CFSG.Assembly.LowTwoRank CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding
  CFSG.AGLEmbedding.LieOut

theorem exists_model_twistedD {G : Type} [Group G] (hX : IsLieOf IdxTwistedD G) :
    ∃ (r : ℕ) (F : Type) (_ : Field F), Finite F ∧ CharP F 2 ∧ ∃ b c : F,
      (∀ s : F, s ^ 2 + b * s + c ≠ 0) ∧ 3 ≤ r ∧ (Nat.card F = 2 ∨ 4 ≤ Nat.card F) ∧
      Nonempty (G ≃* StatedProj (Ωm r F b c)) := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hX
  cases d with
  | twistedD r' q =>
    have hp2 : q.p = 2 := hd
    have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r' q hv hp2 e
    rw [hp2] at hm
    obtain ⟨⟨-, hf, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e'⟩⟩ := hm
    have hchar : CharP F 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf
        hcard
    obtain ⟨r, rfl⟩ : ∃ r, r' = r + 1 := ⟨r' - 1, by omega⟩
    refine ⟨r, F, hF, hFfin, hchar, b, c, hirr, by omega, ?_, ⟨e'⟩⟩
    rw [hcard]
    rcases Nat.eq_or_lt_of_le hf with h1 | h2
    · left; rw [← h1]; norm_num
    · right
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) h2
  | _ => exact hd.elim

variable {r : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem omega_mk_injective (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hr : 1 ≤ r) :
    Function.Injective (QuotientGroup.mk' ((StatedScalars (Idx r) F).subgroupOf (Ωm r F b c))) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro A hA
  rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hA
  exact (Subgroup.mem_bot).2 (eq_one_of_mem_statedScalars_statedOmega_two' hirr (n := r + 1)
    (by omega) hA)

noncomputable def omegaProjEquiv (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hr : 1 ≤ r) :
    ↥(Ωm r F b c) ≃* StatedProj (Ωm r F b c) :=
  MulEquiv.ofBijective (QuotientGroup.mk' ((StatedScalars (Idx r) F).subgroupOf (Ωm r F b c)))
    ⟨omega_mk_injective hirr hr, QuotientGroup.mk'_surjective _⟩

section Spin

open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted

variable {n : ℕ} {K : Type} [Field K] {b c : K} {m : ℕ}

theorem not_mem_stabEM_of_mat {g : spinGroup (quadMinus n K b c)} {j : Fin (n - 1)}
    {a : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2} (hj : j.val < m)
    (ha : ∀ k : Fin (n - 1), k.val < m → a ≠ .inl k) (h : mat n g a (.inl j) ≠ 0) :
    g ∉ stabEM (n := n) (b := b) (c := c) m := by
  intro hg
  have h1 := hg (eVec n j) (Submodule.subset_span ⟨j, hj, rfl⟩)
  rw [mem_eSpanM_iff] at h1
  apply h
  rw [mat_apply]
  exact h1 a ha

theorem mem_eSpanM_iff_of_mem_stabEM {g : spinGroup (quadMinus n K b c)}
    (hg : g ∈ stabEM (n := n) (b := b) (c := c) m) (v : Vm n K) :
    v ∈ eSpanM n (K := K) m ↔ (spinMatrix (quadMinus n K b c) g : Matrix _ _ K) *ᵥ v ∈
      eSpanM n (K := K) m := by
  rw [spinMatrix_mulVec]
  refine ⟨hg v, fun h => ?_⟩
  have := (inv_mem hg) _ h
  rwa [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one] at this

variable (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

theorem rankOne_le_stabEM_of_ne {i j : Fin (n - 1)} (hij : i ≠ j) :
    rankOne (minusDatum n hirr).rootGroup i ≤ stabEM (n := n) (b := b) (c := c) (j.val + 1) := by
  by_cases hk : i.val + 1 < n - 1
  · exact rankOne_le_stabEM_of_lt hirr hk fun h => hij (Fin.ext (by omega))
  · refine rankOne_le_stabEM_short hirr hk ?_
    have h1 : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have h2 := i.2
    have h3 := j.2
    omega

theorem exists_mem_rankOne_not_mem_stabEM (j : Fin (n - 1)) :
    ∃ x ∈ rankOne (minusDatum n hirr).rootGroup j,
      x ∉ stabEM (n := n) (b := b) (c := c) (j.val + 1) := by
  by_cases hk : j.val + 1 < n - 1
  · refine ⟨(minusFrame n b c).longRoot (succ_ne_of_lt n hk).symm true false (.ofAdd 1),
      Subgroup.mem_sup_right (longRoot_mem_minusRootGroup n hirr (succ_ne_of_lt n hk).symm true
        false (toStdB_neg_single_of_lt' n hk) 1), ?_⟩
    refine not_mem_stabEM_of_mat (j := j) (a := .inl ⟨j.val + 1, hk⟩) (by simp) (fun k hk' h => ?_) ?_
    · have := congrArg Fin.val (Sum.inl.inj h)
      simp at this
      omega
    · have hne : (⟨j.val + 1, hk⟩ : Fin (n - 1)) ≠ j := (succ_ne_of_lt n hk).symm
      rw [mat_longRoot_apply]
      simp [minusPos, hne]
  · refine ⟨twShortRoot n hirr j false (.ofAdd ![1, 0]),
      Subgroup.mem_sup_right (twShortRoot_mem_minusRootGroup n hirr j false
        (toStdB_neg_single_of_not_lt' n hk) _), ?_⟩
    refine not_mem_stabEM_of_mat (j := j) (a := .inr (.inr 0)) (by simp) (fun k _ h => by simp at h) ?_
    rw [mat_twShortRoot_apply]
    simp [minusPos, planeVec]

end Spin

section Flag

open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted

variable {r : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

omit [Finite F] [CharP F 2] in
theorem eSpanM_eq_eSub (d : ℕ) : eSpanM (r + 1) (K := F) d = eSub r F d :=
  Submodule.ext fun v => by rw [mem_eSpanM_iff, mem_eSub]; exact Iff.rfl

noncomputable def spinΩ (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hr : 3 ≤ r)
    (k : spinGroup (quadMinus (r + 1) F b c)) : ↥(Ωm r F b c) :=
  ⟨spinMatrix (quadMinus (r + 1) F b c) k,
    spinMatrix_mem_of_range_eq _ (range_spinMatrix_quadMinus (by omega) hirr) k⟩

theorem exists_flagData (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hr : 3 ≤ r)
    (T : Sylow 2 (StatedProj (Ωm r F b c))) (J : Subgroup (StatedProj (Ωm r F b c)))
    (hNJ : Subgroup.normalizer (T : Set (StatedProj (Ωm r F b c))) ≤ J) :
    ∃ (Ag : ↥(Ωm r F b c)) (S : Finset ℕ), (∀ i ∈ S, 1 ≤ i ∧ i ≤ r) ∧
      ∀ B : ↥(Ωm r F b c),
        (QuotientGroup.mk (Ag * B * Ag⁻¹) : StatedProj (Ωm r F b c)) ∈ J ↔
          (B : GL (Idx r) F) ∈ JΩ r F b c S := by
  classical
  have hn4 : 4 ≤ r + 1 := by omega
  obtain ⟨g, π', hπ', hQ, hBJ⟩ := exists_conj_borelQuotient (n := r + 1) hirr hn4 T J hNJ
  obtain ⟨Ag, hAg⟩ : ∃ Ag : ↥(Ωm r F b c), (QuotientGroup.mk Ag : StatedProj (Ωm r F b c)) = g :=
    QuotientGroup.mk_surjective g
  have hπx : ∀ k, π' k = (QuotientGroup.mk (Ag * spinΩ hirr hr k * Ag⁻¹) :
      StatedProj (Ωm r F b c)) := by
    intro k
    rw [hπ' k, spinToStatedProj_apply, ← hAg, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv]
    rfl
  set P : Set (Fin (r + 1 - 1)) :=
    {j | (rankOne (minusDatum (r + 1) hirr).rootGroup j).map π' ≤ J} with hP
  set S : Finset ℕ := (Finset.univ.filter fun j : Fin (r + 1 - 1) => j ∉ P).image
    (fun j => j.val + 1) with hSdef
  have hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r := by
    intro i hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hi
    have := j.2
    exact ⟨by omega, by omega⟩
  have hSmem : ∀ j : Fin (r + 1 - 1), j ∉ P → j.val + 1 ∈ S := fun j hj =>
    Finset.mem_image.2 ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩, rfl⟩
  have hSmem' : ∀ d ∈ S, ∃ j : Fin (r + 1 - 1), j ∉ P ∧ j.val + 1 = d := fun d hd => by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hd
    exact ⟨j, (Finset.mem_filter.1 hj).2, rfl⟩
  let φ : ↥(Ωm r F b c) →* StatedProj (Ωm r F b c) :=
    (QuotientGroup.mk' ((StatedScalars (Idx r) F).subgroupOf (Ωm r F b c))).comp
      (MulAut.conj Ag).toMonoidHom
  have hφ : Function.Injective φ := (omega_mk_injective hirr (by omega)).comp (MulAut.conj Ag).injective
  have hφapp : ∀ B, φ B = (QuotientGroup.mk (Ag * B * Ag⁻¹) : StatedProj (Ωm r F b c)) :=
    fun B => rfl
  set J₀ : Subgroup (StatedProj (Ωm r F b c)) :=
    ((JΩ r F b c S).subgroupOf (Ωm r F b c)).map φ with hJ₀
  have hD : ∀ k, (∀ d ∈ S, k ∈ stabEM (n := r + 1) (b := b) (c := c) d) → π' k ∈ J₀ := by
    intro k hk
    refine ⟨spinΩ hirr hr k, ?_, by rw [hφapp, hπx]⟩
    refine Subgroup.mem_subgroupOf.2 ⟨(spinΩ hirr hr k).2, fun d hd v => ?_⟩
    have := mem_eSpanM_iff_of_mem_stabEM (hk d hd) v
    rw [eSpanM_eq_eSub] at this
    exact this
  have hC : ∀ k, π' k ∈ J₀ → ∀ d ∈ S, k ∈ stabEM (n := r + 1) (b := b) (c := c) d := by
    intro k hk d hd
    obtain ⟨B, hB, hBk⟩ := hk
    have hBk' : B = spinΩ hirr hr k := by
      have h1 : (QuotientGroup.mk (Ag * B * Ag⁻¹) : StatedProj (Ωm r F b c)) =
          QuotientGroup.mk (Ag * spinΩ hirr hr k * Ag⁻¹) := by rw [← hφapp, hBk, hπx]
      have h2 := omega_mk_injective hirr (by omega) h1
      exact mul_left_cancel (mul_right_cancel h2)
    subst hBk'
    intro v hv
    rw [← spinMatrix_mulVec]
    have := (Subgroup.mem_subgroupOf.1 hB).2 d hd v
    rw [eSpanM_eq_eSub] at hv ⊢
    exact this.1 hv
  have hB₀ : (borel (minusDatum (r + 1) hirr) (minusTorus (r + 1) hirr)).map π' ≤ J₀ := by
    rintro _ ⟨x, hx, rfl⟩
    exact hD x fun d _ => borel_le_stabEM hirr hx
  have hBA₀ : borel (minusDatum (r + 1) hirr) (minusTorus (r + 1) hirr) ≤ J₀.comap π' :=
    fun x hx => hB₀ ⟨x, hx, rfl⟩
  have hBA : borel (minusDatum (r + 1) hirr) (minusTorus (r + 1) hirr) ≤ J.comap π' :=
    fun x hx => hBJ ⟨x, hx, rfl⟩
  have hJeq := eq_map_borel_sup_of_le hQ.ct hQ.extras hQ.surj hBJ
  have hJ₀eq := eq_map_borel_sup_of_le hQ.ct hQ.extras hQ.surj hB₀
  have hJJ₀ : J ≤ J₀ := by
    refine hJeq.le.trans (sup_le hB₀ (iSup₂_le fun i hi => ?_))
    have hiP : i ∈ P := Subgroup.map_le_iff_le_comap.2 (rankOne_le_of_mem_negIndices hBA hi)
    rintro _ ⟨x, hx, rfl⟩
    refine hD x fun d hd => ?_
    obtain ⟨j, hjP, rfl⟩ := hSmem' d hd
    have hij : i ≠ j := fun h => hjP (h ▸ hiP)
    exact rankOne_le_stabEM_of_ne hirr hij hx
  have hJ₀J : J₀ ≤ J := by
    refine hJ₀eq.le.trans (sup_le hBJ (iSup₂_le fun i hi => ?_))
    by_contra hnot
    obtain ⟨x, hx, hxn⟩ := exists_mem_rankOne_not_mem_stabEM hirr i
    exact hxn (hC x (rankOne_le_of_mem_negIndices hBA₀ hi hx) _ (hSmem i hnot))
  refine ⟨Ag, S, hS, fun B => ?_⟩
  rw [← hφapp, le_antisymm hJJ₀ hJ₀J, hJ₀, Subgroup.mem_map_iff_mem hφ, Subgroup.mem_subgroupOf]

end Flag

section Lift

variable {Γ : Type} [Group Γ] {H J : Subgroup Γ} {p : ℕ}

theorem a1_lift (hJH : J ≤ H)
    (hA1 : ∀ X' : Subgroup ↥H, X' ≤ J.subgroupOf H → CFSG.Open.IsQuasisimple ↥X' →
      ¬ p ^ 2 ∣ Nat.card X') :
    ∀ X : Subgroup Γ, X ≤ J → CFSG.Open.IsQuasisimple ↥X → ¬ p ^ 2 ∣ Nat.card X := by
  intro X hXJ hq hd
  have hXH : X ≤ H := hXJ.trans hJH
  let e := Subgroup.subgroupOfEquivOfLe hXH
  refine hA1 (X.subgroupOf H) (fun y hy => Subgroup.mem_subgroupOf.2
    (hXJ (Subgroup.mem_subgroupOf.1 hy)))
    (CFSG.ComponentClassification.Components.quasisimple_of_equiv e hq) ?_
  rwa [Nat.card_congr e.toEquiv]

theorem a2_lift (hJH : J ≤ H)
    (hA2 : ∀ X₁ X₂ : Subgroup ↥H, X₁ ≤ J.subgroupOf H → X₂ ≤ J.subgroupOf H →
      CFSG.Open.IsQuasisimple ↥X₁ → CFSG.Open.IsQuasisimple ↥X₂ →
      X₂ ≤ Subgroup.centralizer (X₁ : Set ↥H) → p ∣ Nat.card X₁ → p ∣ Nat.card X₂ →
      NoAp p (↥X₁ ⧸ Subgroup.center ↥X₁) → NoAp p (↥X₂ ⧸ Subgroup.center ↥X₂) → False) :
    ∀ X₁ X₂ : Subgroup Γ, X₁ ≤ J → X₂ ≤ J →
      CFSG.Open.IsQuasisimple ↥X₁ → CFSG.Open.IsQuasisimple ↥X₂ →
      X₂ ≤ Subgroup.centralizer (X₁ : Set Γ) → p ∣ Nat.card X₁ → p ∣ Nat.card X₂ →
      NoAp p (↥X₁ ⧸ Subgroup.center ↥X₁) → NoAp p (↥X₂ ⧸ Subgroup.center ↥X₂) → False := by
  intro X₁ X₂ h₁ h₂ hq₁ hq₂ hc hp₁ hp₂ hn₁ hn₂
  have hX₁H : X₁ ≤ H := h₁.trans hJH
  have hX₂H : X₂ ≤ H := h₂.trans hJH
  let e₁ := Subgroup.subgroupOfEquivOfLe hX₁H
  let e₂ := Subgroup.subgroupOfEquivOfLe hX₂H
  refine hA2 (X₁.subgroupOf H) (X₂.subgroupOf H)
    (fun y hy => Subgroup.mem_subgroupOf.2 (h₁ (Subgroup.mem_subgroupOf.1 hy)))
    (fun y hy => Subgroup.mem_subgroupOf.2 (h₂ (Subgroup.mem_subgroupOf.1 hy)))
    (CFSG.ComponentClassification.Components.quasisimple_of_equiv e₁ hq₁)
    (CFSG.ComponentClassification.Components.quasisimple_of_equiv e₂ hq₂) ?_
    (by rwa [Nat.card_congr e₁.toEquiv]) (by rwa [Nat.card_congr e₂.toEquiv])
    (noAp_center_quotient_of_surjective e₁.toMonoidHom e₁.surjective hn₁)
    (noAp_center_quotient_of_surjective e₂.toMonoidHom e₂.surjective hn₂)
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hc (Subgroup.mem_subgroupOf.1 hy)) z
    (Subgroup.mem_subgroupOf.1 hz))

end Lift

theorem isElemAbelian_map_hom {p : ℕ} {G G' : Type} [Group G] [Group G'] (θ : G →* G')
    {E : Subgroup G} (h : IsElemAbelian p E) : IsElemAbelian p (E.map θ) :=
  CFSG.Open.IsElemAbelian.map h _

theorem altIbBarCell_twistedD_of_flagCell (h : TwistedDFlagCell) :
    AltIbBarCell (IsLieOf IdxTwistedD) := by
  intro G _ _ hX Jb hsyl hJtop p hp57 a1 a2 x hxp hfix V E hVJ hVx hV hEV hEel hEc
  obtain ⟨r, F, _, hfin, hchar, b, c, hirr, hr, hF, ⟨ee⟩⟩ := exists_model_twistedD hX
  have : Finite F := hfin
  have : CharP F 2 := hchar
  obtain ⟨T, hT, hNT⟩ := hsyl
  have hT' : ∃ T' : Subgroup (StatedProj (Ωm r F b c)), IsSylowTwoOf T' ⊤ ∧
      Subgroup.normalizer (T' : Set (StatedProj (Ωm r F b c))) ≤ Jb.map ee.toMonoidHom := by
    refine ⟨T.map ee.toMonoidHom, ⟨le_top, hT.2.1.map _, ?_⟩, ?_⟩
    · have h2 := hT.2.2
      rw [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] at h2
      have h3 : (T.map ee.toMonoidHom).index = T.index := Subgroup.index_map_equiv T ee
      rw [show ((T.map ee.toMonoidHom).subgroupOf ⊤).index = (T.map ee.toMonoidHom).index from
        Subgroup.relIndex_top_right _, h3]
      exact h2
    · rw [← Subgroup.map_normalizer_eq_of_bijective T ee.bijective]
      exact Subgroup.map_mono hNT
  obtain ⟨T', hT'syl, hNT'⟩ := hT'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ T'.index := by
    have h2 := hT'syl.2.2
    rwa [show (T'.subgroupOf ⊤).index = T'.index from Subgroup.relIndex_top_right T'] at h2
  let Tsyl : Sylow 2 (StatedProj (Ωm r F b c)) := hT'syl.2.1.toSylow hidx
  have hNTs : Subgroup.normalizer (Tsyl : Set (StatedProj (Ωm r F b c))) ≤ Jb.map ee.toMonoidHom :=
    hNT'
  obtain ⟨Ag, S, hS, hflag⟩ := exists_flagData hirr hr Tsyl (Jb.map ee.toMonoidHom) hNTs
  let ψ := omegaProjEquiv hirr (by omega : 1 ≤ r)
  let θ : G ≃* ↥(Ωm r F b c) := ee.trans (ψ.symm.trans (MulAut.conj Ag⁻¹))
  have hθsymm : ∀ B : ↥(Ωm r F b c),
      θ.symm B = ee.symm (QuotientGroup.mk (Ag * B * Ag⁻¹) : StatedProj (Ωm r F b c)) := by
    intro B
    rw [MulEquiv.symm_apply_eq]
    show B = Ag⁻¹ * ψ.symm (ee (ee.symm (QuotientGroup.mk (Ag * B * Ag⁻¹)))) * Ag⁻¹⁻¹
    rw [MulEquiv.apply_symm_apply]
    have : ψ.symm (QuotientGroup.mk (Ag * B * Ag⁻¹) : StatedProj (Ωm r F b c)) = Ag * B * Ag⁻¹ :=
      ψ.symm_apply_eq.2 rfl
    rw [this]
    group
  have hθ : ∀ B : ↥(Ωm r F b c), B ∈ Jb.map θ.toMonoidHom ↔ (B : GL (Idx r) F) ∈ JΩ r F b c S := by
    intro B
    rw [Subgroup.mem_map_equiv, hθsymm, ← hflag B, Subgroup.mem_map_equiv]
  have hθJ : Jb.map θ.toMonoidHom = (JΩ r F b c S).subgroupOf (Ωm r F b c) :=
    Subgroup.ext fun B => (hθ B).trans Subgroup.mem_subgroupOf.symm
  have hJH : JΩ r F b c S ≤ Ωm r F b c := fun A hA => hA.1
  have hA1 := transport_a1 θ a1
  have hA2 := transport_a2 θ a2
  rw [hθJ] at hA1 hA2
  let ι : G →* GL (Idx r) F := (Ωm r F b c).subtype.comp θ.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp θ.injective
  have hιJ : ∀ g ∈ Jb, ι g ∈ JΩ r F b c S := fun g hg =>
    (hθ _).1 ⟨g, hg, rfl⟩
  have hxΩ : ι x ∈ Ωm r F b c := (θ x).2
  have hxp' : (ι x) ^ p = 1 := by rw [← map_pow, hxp, map_one]
  have hfix' : ∀ g ∈ Ωm r F b c, g * ι x = ι x * g → g ∈ JΩ r F b c S := by
    intro g hg hgx
    have h1 : θ.symm ⟨g, hg⟩ * x = x * θ.symm ⟨g, hg⟩ := by
      apply θ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subtype.ext hgx
    have h2 := hιJ _ (hfix _ h1)
    simpa [ι] using h2
  refine h r F b c hirr hr hF p hp57 S hS (a1_lift hJH hA1) (a2_lift hJH hA2) (ι x) hxΩ hxp'
    hfix' (V.map ι) (E.map ι) ?_ ?_ ?_ (Subgroup.map_mono hEV) (isElemAbelian_map_hom ι hEel) ?_
  · rintro _ ⟨v, hv, rfl⟩
    exact hιJ v (hVJ hv)
  · rintro _ ⟨v, hv, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h' hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    show ι x * ι v = ι v * ι x
    rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.1 (hVx hv) x (Set.mem_singleton x))]
  · rw [← Subgroup.map_commutator, hV]
  · rw [Subgroup.card_map_of_injective hι, hEc]

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinus

module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffCharDetCover
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldOrthogonal

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower

open CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  CFSG.Assembly.LowTwoRank CFSG.LieType.SeitzGeneration CFSG.RankThree.PartTwo.Census
open scoped commutatorElement

theorem pElement_comm_mem_of_relIndex_le {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (I D : Subgroup G) (hID : ∀ d ∈ D, ∀ i ∈ I, d * i * d⁻¹ ∈ I)
    {α : G} {k : ℕ} (hk : α ^ (p ^ k) = 1)
    (hαI : ∀ i ∈ I, α * i * α⁻¹ ∈ I) (hαD : ∀ d ∈ D, α * d * α⁻¹ ∈ D)
    (hcard : I.relIndex D ≤ p) {δ : G} (hδ : δ ∈ D) :
    α * δ * α⁻¹ * δ⁻¹ ∈ I := by
  set N := I.subgroupOf D with hN
  haveI hNn : N.Normal := ⟨fun x hx d => by
    have h1 : ((x : D) : G) ∈ I := hx
    show ((d * x * d⁻¹ : D) : G) ∈ I
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hID d d.2 _ h1⟩
  let Φ₀ : D →* D :=
    { toFun := fun x => ⟨α * x * α⁻¹, hαD x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  let Φ : Monoid.End D := Φ₀
  have hΦN : N ≤ N.comap Φ₀ := by
    intro x hx
    change ((Φ₀ x : D) : G) ∈ I
    exact hαI _ hx
  let M : (D ⧸ N) →* (D ⧸ N) := QuotientGroup.map N N Φ₀ hΦN
  let f : Function.End (D ⧸ N) := ⇑M
  have hΦpow : ∀ (j : ℕ) (x : D), (((Φ ^ j) x : D) : G) = α ^ j * x * (α ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro x; rw [pow_zero, pow_zero, one_mul, inv_one, mul_one]; rfl
    | succ j ih =>
      intro x
      rw [pow_succ']
      change α * (((Φ ^ j) x : D) : G) * α⁻¹ = _
      rw [ih, pow_succ']
      group
  have hMpow : ∀ (j : ℕ) (x : D), (f ^ j) (x : D ⧸ N) = (((Φ ^ j) x : D) : D ⧸ N) := by
    intro j
    induction j with
    | zero => intro x; rfl
    | succ j ih =>
      intro x
      rw [pow_succ', pow_succ']
      change f ((f ^ j) (x : D ⧸ N)) = ((Φ ((Φ ^ j) x) : D) : D ⧸ N)
      rw [ih]
      rfl
  have hMp : f ^ (p ^ k) = 1 := by
    funext z
    induction z using QuotientGroup.induction_on with
    | H x =>
      rw [hMpow]
      change (((Φ ^ (p ^ k)) x : D) : D ⧸ N) = (x : D ⧸ N)
      congr 1
      apply Subtype.ext
      rw [hΦpow, hk, one_mul, inv_one, mul_one]
  have hcard' : Nat.card (D ⧸ N) ≤ p := hcard
  have hfix := eq_of_pow_eq_one_of_card_le hMp hcard' (a := 1) (map_one M)
    ((⟨δ, hδ⟩ : D) : D ⧸ N)
  change ((Φ₀ ⟨δ, hδ⟩ : D) : D ⧸ N) = _ at hfix
  have h6 := (QuotientGroup.eq).1 hfix
  have h7 : (α * δ * α⁻¹)⁻¹ * δ ∈ I := by
    have := Subgroup.mem_subgroupOf.1 h6
    simpa [Φ₀] using this
  have h8 := hID δ hδ _ (I.inv_mem h7)
  have h9 : δ * ((α * δ * α⁻¹)⁻¹ * δ)⁻¹ * δ⁻¹ = α * δ * α⁻¹ * δ⁻¹ := by group
  rwa [h9] at h8

theorem mem_of_comm_pow {G : Type*} [Group G] {N M : Subgroup G} [N.Normal]
    {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : ¬ p ∣ n)
    (hexp : ∀ y : M ⧸ N.subgroupOf M, y ^ n = 1)
    {α x : G} {k : ℕ} (hk : α ^ (p ^ k) = 1)
    (hc : α * x * α⁻¹ * x⁻¹ ∈ M)
    (hcomm : α * (α * x * α⁻¹ * x⁻¹) * α⁻¹ * (α * x * α⁻¹ * x⁻¹)⁻¹ ∈ N) :
    α * x * α⁻¹ * x⁻¹ ∈ N := by
  set c := α * x * α⁻¹ * x⁻¹ with hc_def
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  have hC : π c = π α * π x * (π α)⁻¹ * (π x)⁻¹ := by
    simp only [hc_def, map_mul, map_inv]
  have hcomm' : Commute (π α) (π c) := by
    have h1 : π (α * c * α⁻¹ * c⁻¹) = 1 := (QuotientGroup.eq_one_iff _).2 hcomm
    simp only [map_mul, map_inv] at h1
    have h2 := mul_inv_eq_one.1 h1
    exact mul_inv_eq_iff_eq_mul.1 h2
  have hpow : ∀ j : ℕ, (π α) ^ j * π x * ((π α) ^ j)⁻¹ = (π c) ^ j * π x := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hX : π α * π x * (π α)⁻¹ = π c * π x := by rw [hC]; group
      have hcom : π α * (π c) ^ j * (π α)⁻¹ = (π c) ^ j := by
        have := (hcomm'.pow_right j).eq
        rw [this]; group
      calc (π α) ^ (j + 1) * π x * ((π α) ^ (j + 1))⁻¹
          = π α * ((π α) ^ j * π x * ((π α) ^ j)⁻¹) * (π α)⁻¹ := by
            rw [pow_succ']; group
        _ = π α * ((π c) ^ j * π x) * (π α)⁻¹ := by rw [ih]
        _ = (π α * (π c) ^ j * (π α)⁻¹) * (π α * π x * (π α)⁻¹) := by group
        _ = (π c) ^ (j + 1) * π x := by rw [hcom, hX, pow_succ]; group
  have hα1 : (π α) ^ (p ^ k) = 1 := by rw [← map_pow, hk, map_one]
  have h3 := hpow (p ^ k)
  rw [hα1] at h3
  simp only [one_mul, inv_one, mul_one] at h3
  have h4 : (π c) ^ (p ^ k) = 1 := by
    have : (π c) ^ (p ^ k) * π x = 1 * π x := by rw [one_mul]; exact h3.symm
    exact mul_right_cancel this
  have h5 : c ^ (p ^ k) ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact h4
  exact CFSG.RankThree.PartOne.OutStructure.mem_of_pow_mem_of_exponent hp hn hexp hc h5

theorem comm_mem_of_series {G : Type*} [Group G] [Finite G] (N O D E : Subgroup G) [N.Normal]
    (hNO : N ≤ O) (hOD : O ≤ D) (hDE : D ≤ E)
    (hOE : ∀ e ∈ E, ∀ o ∈ O, e * o * e⁻¹ ∈ O)
    (hEE : ∀ a ∈ E, ∀ b ∈ E, a * b * a⁻¹ * b⁻¹ ∈ D)
    (hO4 : N.relIndex O ≤ 4) (hD2 : O.relIndex D ≤ 2)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {α : G} (hαE : α ∈ E) {k : ℕ} (hk : α ^ (p ^ k) = 1)
    {x : G} (hx : x ∈ E) : x * α * x⁻¹ * α⁻¹ ∈ N := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hαD : ∀ d ∈ D, α * d * α⁻¹ ∈ D := by
    intro d hd
    have h1 := hEE α hαE d (hDE hd)
    have : α * d * α⁻¹ = (α * d * α⁻¹ * d⁻¹) * d := by group
    rw [this]
    exact D.mul_mem h1 hd
  have hNO0 : N.relIndex O ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hOD0 : O.relIndex D ≠ 0 := Subgroup.index_ne_zero_of_finite
  have Y1 : ∀ y ∈ O, α * y * α⁻¹ * y⁻¹ ∈ N := fun y hy =>
    pElement_comm_mem_of_relIndex_le N O (fun o _ n hn => ‹N.Normal›.conj_mem n hn o)
      hk (fun i hi => ‹N.Normal›.conj_mem i hi α) (fun o ho => hOE α hαE o ho)
      (hO4.trans (by omega)) hy
  have Y2 : ∀ d ∈ D, α * d * α⁻¹ * d⁻¹ ∈ O := fun d hd =>
    pElement_comm_mem_of_relIndex_le O D (fun d' hd' o ho => hOE d' (hDE hd') o ho) hk
      (fun i hi => hOE α hαE i hi) hαD (hD2.trans (by omega)) hd
  have Y3 : ∀ d ∈ D, α * d * α⁻¹ * d⁻¹ ∈ N := fun d hd => by
    have hc : α * d * α⁻¹ * d⁻¹ ∈ O := Y2 d hd
    refine mem_of_comm_pow hp (n := N.relIndex O) (M := O) ?_ ?_ hk hc (Y1 _ hc)
    · exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hNO0) (by omega)
    · intro y
      exact pow_card_eq_one' (G := O ⧸ N.subgroupOf O) (x := y)
  have hND : N.relIndex D = N.relIndex O * O.relIndex D :=
    (Subgroup.relIndex_mul_relIndex N O D hNO hOD).symm
  have Y4 : ∀ x ∈ E, α * x * α⁻¹ * x⁻¹ ∈ N := fun x hx => by
    have hc : α * x * α⁻¹ * x⁻¹ ∈ D := hEE α hαE x hx
    refine mem_of_comm_pow hp (n := N.relIndex D) (M := D) ?_ ?_ hk hc (Y3 _ hc)
    · rw [hND]
      intro hdvd
      rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
      · have := Nat.le_of_dvd (Nat.pos_of_ne_zero hNO0) h
        omega
      · have := Nat.le_of_dvd (Nat.pos_of_ne_zero hOD0) h
        omega
    · intro y
      exact pow_card_eq_one' (G := D ⧸ N.subgroupOf D) (x := y)
  have e : x * α * x⁻¹ * α⁻¹ = (α * x * α⁻¹ * x⁻¹)⁻¹ := by group
  rw [e]
  exact N.inv_mem (Y4 x hx)

theorem outTowerAt_of_series {K : Type*} [Group K] [Finite K]
    (O D E : Subgroup (MulAut K))
    (hNO : inner K ≤ O) (hOD : O ≤ D) (hDE : D ≤ E)
    (hOE : ∀ e ∈ E, ∀ o ∈ O, e * o * e⁻¹ ∈ O)
    (hEE : ∀ a ∈ E, ∀ b ∈ E, a * b * a⁻¹ * b⁻¹ ∈ D)
    (hO4 : (inner K).relIndex O ≤ 4) (hD2 : O.relIndex D ≤ 2) (hidx : E.index ≤ 3)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OutTowerAt K p := by
  haveI : Finite (MulAut K) := CFSG.RankThree.PartOne.OutStructure.instFiniteMulAut' K
  haveI : (inner K).Normal := inner_normal K
  have hp3 : 3 < p := by omega
  have hcore : ∀ α : MulAut K, (∃ k : ℕ, α ^ (p ^ k) = 1) → α ∈ E.normalCore := by
    rintro α ⟨k, hk⟩ b
    refine CFSG.RankThree.PartOne.OutStructure.mem_of_pow_mem_of_index_le_three E hidx hp hp3
      (k := k) (α := b * α * b⁻¹) ?_
    rw [conj_pow, hk, mul_one, mul_inv_cancel]
    exact E.one_mem
  refine ⟨E.normalCore, fun γ α hα => ?_, fun α hα δ hδ => ?_⟩
  · have h1 := hcore α hα
    have h2 : γ * α * γ⁻¹ ∈ E.normalCore := (Subgroup.normalCore_normal E).conj_mem α h1 γ
    exact E.normalCore.mul_mem h2 (E.normalCore.inv_mem h1)
  · obtain ⟨k, hk⟩ := hα
    have hαE : α ∈ E := Subgroup.normalCore_le E (hcore α ⟨k, hk⟩)
    have hδE : δ ∈ E := Subgroup.normalCore_le E hδ
    have := comm_mem_of_series (inner K) O D E hNO hOD hDE hOE hEE hO4 hD2 hp hp5 hαE hk hδE
    have e : α * δ * α⁻¹ * δ⁻¹ = (δ * α * δ⁻¹ * α⁻¹)⁻¹ := by group
    rw [e]
    exact (inner K).inv_mem this

theorem outTowerAt_matrixProjectiveDerived {K : Type} [Field K] [Finite K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (hQ : Q ≠ 0)
    (hab : Nat.card (Abelianization (matrixIsometries Q)) ≤ 4)
    (hidx : (matrixProjectiveImage Q).index ≤ 3) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    OutTowerAt (matrixProjectiveDerived Q) p := by
  have hQv := exists_nonzero_value Q hQ
  have hNO : inner (matrixProjectiveDerived Q) ≤ (isometryConjugationHom Q).range := by
    rw [inner_eq_map_commutator Q]
    exact Subgroup.map_le_range _ _
  have hOD := isometryConjugationHom_range_le Q
  have hDE : (linearConjugationHom Q).range ≤ matrixProjectiveImage Q := by
    rintro _ ⟨g, rfl⟩
    exact (mem_matrixProjectiveImage_iff Q _).mpr ⟨g.val, rfl⟩
  have hOE : ∀ e ∈ matrixProjectiveImage Q, ∀ o ∈ (isometryConjugationHom Q).range,
      e * o * e⁻¹ ∈ (isometryConjugationHom Q).range := by
    rintro e he _ ⟨A, rfl⟩
    obtain ⟨g, rfl⟩ := (mem_matrixProjectiveImage_iff Q _).1 he
    have hmem : g * matrixIsometryInclusion Q A * g⁻¹ ∈ matrixIsometryPairs Q :=
      (matrixIsometryPairs_normal Q).conj_mem _ ⟨A, rfl⟩ g
    obtain ⟨A', hA'⟩ := hmem
    refine ⟨A', ?_⟩
    change matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q A') = _
    rw [hA']
    simp only [map_mul, map_inv]
    rfl
  have hEE : ∀ a ∈ matrixProjectiveImage Q, ∀ b ∈ matrixProjectiveImage Q,
      a * b * a⁻¹ * b⁻¹ ∈ (linearConjugationHom Q).range := by
    intro a ha b hb
    obtain ⟨g₁, rfl⟩ := (mem_matrixProjectiveImage_iff Q _).1 ha
    obtain ⟨g₂, rfl⟩ := (mem_matrixProjectiveImage_iff Q _).1 hb
    change ⁅matrixProjectiveConjugationHom Q g₁, matrixProjectiveConjugationHom Q g₂⁆ ∈ _
    rw [← map_commutatorElement]
    refine ⟨⟨⁅g₁, g₂⁆, ?_⟩, rfl⟩
    rw [mem_linearSimilarityPairs_iff]
    change fieldProjection Q ⁅g₁, g₂⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact CFSG.RankThree.PartOne.OutStructure.ringAut_comm K _ _
  have hO4 : (inner (matrixProjectiveDerived Q)).relIndex (isometryConjugationHom Q).range ≤ 4 :=
    (Nat.le_of_dvd Nat.card_pos (relIndex_inner_dvd Q)).trans hab
  have hsq : (powMonoidHom 2 : Kˣ →* Kˣ).range.index ≤ 2 := by
    rw [IsCyclic.index_powMonoidHom_range, Nat.card_units]
    exact Nat.gcd_le_right _ two_pos
  have hsq0 : 0 < (powMonoidHom 2 : Kˣ →* Kˣ).range.index :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hD2 : (isometryConjugationHom Q).range.relIndex (linearConjugationHom Q).range ≤ 2 :=
    (Nat.le_of_dvd hsq0 (relIndex_isometryRange_dvd Q hQv)).trans hsq
  haveI : Finite (matrixProjectiveDerived Q) := inferInstance
  exact outTowerAt_of_series _ _ _ hNO hOD hDE hOE hEE hO4 hD2 hidx hp hp5

theorem outTowerAt_of_statedOdd {X : Type} [Group X] {n r m : ℕ}
    (h : StatedClassicalModel X .POmegaOdd n r m) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    OutTowerAt X p := by
  have h0 := h
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  obtain ⟨hQ, hab, hidx⟩ := CFSG.SignalizerFunctorTheorem.CatalogBridge.orthOdd_hyps h K hK e
  exact OutTowerAt.of_mulEquiv (coordinateOddWitnessEquiv K e)
    (outTowerAt_matrixProjectiveDerived _ hQ hab hidx hp hp5)

theorem outTowerAt_of_statedPlus {X : Type} [Group X] {n r m : ℕ}
    (h : StatedClassicalModel X .POmegaPlus n r m) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    OutTowerAt X p := by
  have h0 := h
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  obtain ⟨hQ, hab, hidx⟩ := CFSG.SignalizerFunctorTheorem.CatalogBridge.orthPlus_hyps h K hK e
  exact OutTowerAt.of_mulEquiv (coordinatePlusWitnessEquiv K e)
    (outTowerAt_matrixProjectiveDerived _ hQ hab hidx hp hp5)

theorem outTowerAt_of_statedMinus {X : Type} [Group X] {n r m : ℕ}
    (h : StatedClassicalModel X .POmegaMinus n r m) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    OutTowerAt X p := by
  have h0 := h
  obtain ⟨⟨-, -, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h0
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hQ, hab, hidx⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.orthMinus_hyps h K hK b c hirr hn1 e
  exact OutTowerAt.of_mulEquiv (coordinateMinusWitnessEquiv K hn1 b c e)
    (outTowerAt_matrixProjectiveDerived _ hQ hab hidx hp hp5)

theorem outTowerAt_orthogonal {d : TauCeti.ValidLieTypeIndex} (hd : IsOrthogonalIndex d.1)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : OutTowerAt (TauCeti.CFSGIndex.lie d).Group p := by
  obtain ⟨d, hv⟩ := d
  rcases hd with ⟨r, q, rfl, hr3, hq⟩ | ⟨r, q, rfl⟩ | ⟨r, q, rfl⟩
  · exact outTowerAt_of_statedOdd
      (statedClassicalModel_typeB_odd r q hv hq hr3 (MulEquiv.refl _)) hp hp5
  · exact outTowerAt_of_statedPlus (statedClassicalModel_typeD r q hv (MulEquiv.refl _)) hp hp5
  · exact outTowerAt_of_statedMinus
      (statedClassicalModel_typeTwistedD r q hv (MulEquiv.refl _)) hp hp5

theorem p1OffCharAlmostSimpleNonNormalAt_orthogonal {d : TauCeti.ValidLieTypeIndex}
    (hd : IsOrthogonalIndex d.1) : P1OffCharAlmostSimpleNonNormalAt d := by
  refine p1OffCharAlmostSimpleNonNormalAt_of_towerOrCover fun p _ hp2 _ hno => ?_
  have hp : p.Prime := Fact.out
  by_cases hp3 : p = 3
  · subst hp3
    exact absurd
      (exists_isElemAbelian_card_of_not_rankLE2 hp (not_rankLE2_orthogonal_three d hd)).2 hno
  · left
    have hp5 : 5 ≤ p := by
      have h2 := hp.two_le
      by_contra h
      have h4 : p = 4 := by omega
      subst h4
      exact absurd hp (by norm_num)
    exact outTowerAt_orthogonal hd hp hp5

theorem p1OffCharAlmostSimpleNonNormalAt_B_odd {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.B r q).Valid) (hr3 : 3 ≤ r) (hq : q.p ≠ 2) :
    P1OffCharAlmostSimpleNonNormalAt ⟨.B r q, hv⟩ :=
  p1OffCharAlmostSimpleNonNormalAt_orthogonal (Or.inl ⟨r, q, rfl, hr3, hq⟩)

theorem p1OffCharAlmostSimpleNonNormalAt_D {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.D r q).Valid) :
    P1OffCharAlmostSimpleNonNormalAt ⟨.D r q, hv⟩ :=
  p1OffCharAlmostSimpleNonNormalAt_orthogonal (Or.inr (Or.inl ⟨r, q, rfl⟩))

theorem p1OffCharAlmostSimpleNonNormalAt_twistedD {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid) :
    P1OffCharAlmostSimpleNonNormalAt ⟨.twistedD r q, hv⟩ :=
  p1OffCharAlmostSimpleNonNormalAt_orthogonal (Or.inr (Or.inr ⟨r, q, rfl⟩))

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower


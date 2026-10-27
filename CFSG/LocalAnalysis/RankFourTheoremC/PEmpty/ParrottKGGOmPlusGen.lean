module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottKGGOmPlusPlane
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottKGGOmPlusFrame
public import CFSG.LieType.SeitzGeneration.RootPairOrthTailCenter
public import CFSG.LieType.SeitzGeneration.RootPairOrthModel
public import CFSG.HardMathSupport.Timmesfeld.Proving.OmegaEmbed

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottKGGOmPlus

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

theorem semilinear_eichler_apply {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {σ : K ≃+* K} {Q : QuadraticForm K V} {T : V →ₛₗ[(σ : K →+* K)] V}
    (hTQ : ∀ v, Q (T v) = σ (Q v)) (u w x : V) :
    T (eichler Q u w x) = eichler Q (T u) (T w) (T x) := by
  have hpol : ∀ x y, polar Q (T x) (T y) = σ (polar Q x y) :=
    CFSG.ComponentClassification.UnbalancedCatalog.polar_semilinear hTQ
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · have hu : Q (T u) = 0 := by rw [hTQ, h.1, map_zero]
    have hw : polar Q (T u) (T w) = 0 := by rw [hpol, h.2, map_zero]
    rw [eichler_apply h.1 h.2, eichler_apply hu hw, hpol, hpol, hTQ]
    simp only [map_sub, map_add, map_smulₛₗ, RingEquiv.coe_toRingHom, map_mul]
  · have h' : ¬(Q (T u) = 0 ∧ polar Q (T u) (T w) = 0) := by
      rwa [hTQ, hpol, map_eq_zero_iff σ σ.injective, map_eq_zero_iff σ σ.injective]
    rw [eichler_of_not h, eichler_of_not h']
    rfl

namespace KGF

open CFSG.ComponentClassification.UnbalancedCatalog CFSG.LieType.SeitzGeneration.RootPairOrth
  CFSG.HardMathSupport.Timmesfeld.Proving

theorem starNat_lt_six {a : ℕ} (ha : a < 6) : starNat a < 6 := by
  unfold starNat
  split_ifs <;> omega

theorem starNat_starNat {a : ℕ} (ha : a < 6) : starNat (starNat a) = a := by
  interval_cases a <;> decide

theorem starNat_ne {a : ℕ} (ha : a < 6) : starNat a ≠ a := by
  unfold starNat
  split_ifs <;> omega

theorem starNat_lt {d : ℕ} (hd : 6 ≤ d) (a : Fin d) : starNat a.val < d := by
  have := a.isLt
  unfold starNat
  split_ifs <;> omega

variable {F : Type} [Field F]

@[expose] def hypCoord {d : ℕ} (hd : 6 ≤ d) (Q : QuadraticForm F (Fin d → F))
    (hQ : ∀ a : Fin d, a.val < 6 → Q (Pi.single a 1) = 0)
    (hpol : ∀ a : Fin d, a.val < 6 → ∀ w : Fin d → F,
      polar Q (Pi.single a 1) w = w ⟨starNat a.val, starNat_lt hd a⟩) : HypCoord Q where
  hyp := Finset.univ.filter fun a => a.val < 6
  star a := ⟨starNat a.val, starNat_lt hd a⟩
  star_mem a ha := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    starNat_lt_six (Finset.mem_filter.mp ha).2⟩
  star_star a ha := Fin.ext (starNat_starNat (Finset.mem_filter.mp ha).2)
  star_ne a ha h := starNat_ne (Finset.mem_filter.mp ha).2 (congrArg Fin.val h)
  Q_single a ha := hQ a (Finset.mem_filter.mp ha).2
  polar_single a ha := hpol a (Finset.mem_filter.mp ha).2
  card_hyp := by
    rw [Fin.card_filter_val_lt]
    omega

theorem mem_hypCoord_hyp {d : ℕ} {hd : 6 ≤ d} {Q : QuadraticForm F (Fin d → F)}
    {hQ : ∀ a : Fin d, a.val < 6 → Q (Pi.single a 1) = 0}
    {hpol : ∀ a : Fin d, a.val < 6 → ∀ w : Fin d → F,
      polar Q (Pi.single a 1) w = w ⟨starNat a.val, starNat_lt hd a⟩} {a : Fin d}
    (ha : a.val < 6) : a ∈ (hypCoord hd Q hQ hpol).hyp :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩

theorem hypCoord_star {d : ℕ} {hd : 6 ≤ d} {Q : QuadraticForm F (Fin d → F)}
    {hQ : ∀ a : Fin d, a.val < 6 → Q (Pi.single a 1) = 0}
    {hpol : ∀ a : Fin d, a.val < 6 → ∀ w : Fin d → F,
      polar Q (Pi.single a 1) w = w ⟨starNat a.val, starNat_lt hd a⟩} (a : Fin d) :
    (hypCoord hd Q hQ hpol).star a = ⟨starNat a.val, starNat_lt hd a⟩ :=
  rfl

theorem equivFun_self_eq_single {ι V : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup V]
    [Module F V] (b : Basis ι F V) (i : ι) : b.equivFun (b i) = Pi.single i 1 := by
  rw [← Basis.equivFun_symm_single b i, LinearEquiv.apply_symm_apply]

theorem polar_comp_equivFun_symm_single {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module F V] (Q : QuadraticForm F V) (b : Basis ι F V) {a s : ι}
    (h : ∀ j, polar Q (b a) (b j) = if j = s then 1 else 0) (w : ι → F) :
    polar (Q.comp (b.equivFun.symm : (ι → F) →ₗ[F] V)) (Pi.single a 1) w = w s := by
  simp only [polar_comp_linearMap, LinearEquiv.coe_coe]
  rw [Basis.equivFun_symm_single, Basis.equivFun_symm_apply, ← polarBilin_apply_apply, map_sum]
  simp only [map_smul, polarBilin_apply_apply, h, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

section Transport

variable {V V' : Type*} [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F V']
  {Q : QuadraticForm F V} {Q' : QuadraticForm F V'}

theorem nondegenerate_of_iso (e : V ≃ₗ[F] V') (he : ∀ x, Q' (e x) = Q x)
    (hQ : (polarBilin Q).Nondegenerate) : (polarBilin Q').Nondegenerate := by
  refine CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun x hx => ?_
  have h : ∀ y, polar Q (e.symm x) y = 0 := fun y => by
    rw [← polar_iso e he, LinearEquiv.apply_symm_apply]
    exact hx (e y)
  rw [← e.apply_symm_apply x, eq_zero_of_polar_eq_zero hQ h, map_zero]

theorem isoConjHom_mem_orthogonalGroup (e : V ≃ₗ[F] V') (he : ∀ x, Q' (e x) = Q x)
    {g : V ≃ₗ[F] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    isoConjHom e g ∈ TauCeti.QuadraticMap.orthogonalGroup Q' := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro x
  rw [isoConjHom_apply, he, map_of_mem hg, ← he, LinearEquiv.apply_symm_apply]

theorem map_isoConjHom_le_orthogonalGroup (e : V ≃ₗ[F] V') (he : ∀ x, Q' (e x) = Q x)
    {L : Subgroup (V ≃ₗ[F] V)} (hL : L ≤ TauCeti.QuadraticMap.orthogonalGroup Q) :
    L.map (isoConjHom e) ≤ TauCeti.QuadraticMap.orthogonalGroup Q' := by
  rintro _ ⟨g, hg, rfl⟩
  exact isoConjHom_mem_orthogonalGroup e he (hL hg)

theorem eichler_mem_map (e : V ≃ₗ[F] V') (he : ∀ x, Q' (e x) = Q x)
    {L : Subgroup (V ≃ₗ[F] V)} {x y : V} (h : eichler Q x y ∈ L) :
    eichler Q' (e x) (e y) ∈ L.map (isoConjHom e) :=
  Subgroup.mem_map.mpr ⟨_, h, isoConjHom_eichler e he x y⟩

theorem elementaryGroup_le_of_map (e : V ≃ₗ[F] V') (he : ∀ x, Q' (e x) = Q x)
    {L : Subgroup (V ≃ₗ[F] V)} (h : elementaryGroup Q' ≤ L.map (isoConjHom e)) :
    elementaryGroup Q ≤ L := by
  intro g hg
  obtain ⟨g', hg', hgg'⟩ := Subgroup.mem_map.mp (h (isoConjHom_mem_elementaryGroup e he hg))
  rwa [← isoConjHom_injective e hgg']

end Transport

theorem elementaryGroup_le_of_adapted {d : ℕ} (hd : 6 ≤ d) {Q : QuadraticForm F (Fin d → F)}
    (hQ : (polarBilin Q).Nondegenerate) (b : Basis (Fin d) F (Fin d → F))
    (hbQ : ∀ a : Fin d, a.val < 6 → Q (b a) = 0)
    (hbpol : ∀ a j : Fin d, a.val < 6 →
      polar Q (b a) (b j) = if j.val = starNat a.val then 1 else 0)
    (k : Subfield F) {L : Subgroup ((Fin d → F) ≃ₗ[F] (Fin d → F))}
    (hL : L ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hrat : ∀ x y : Fin d → F, IsRat k x → IsRat k y →
      eichler Q (b.equivFun.symm x) (b.equivFun.symm y) ∈ L)
    (hline : ∀ t : F, eichler Q (b ⟨0, by omega⟩) (t • b ⟨2, by omega⟩) ∈ L) :
    elementaryGroup Q ≤ L := by
  set Q' : QuadraticForm F (Fin d → F) :=
    Q.comp (b.equivFun.symm : (Fin d → F) →ₗ[F] (Fin d → F)) with hQ'
  have he : ∀ x, Q' (b.equivFun x) = Q x := fun x => by
    rw [hQ', QuadraticMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  have hQs : ∀ a : Fin d, a.val < 6 → Q' (Pi.single a 1) = 0 := fun a ha => by
    rw [hQ', QuadraticMap.comp_apply, LinearEquiv.coe_coe, Basis.equivFun_symm_single]
    exact hbQ a ha
  have hps : ∀ a : Fin d, a.val < 6 → ∀ w : Fin d → F,
      polar Q' (Pi.single a 1) w = w ⟨starNat a.val, starNat_lt hd a⟩ := by
    intro a ha w
    refine polar_comp_equivFun_symm_single Q b (fun j => ?_) w
    rw [hbpol a j ha]
    by_cases hj : j.val = starNat a.val
    · rw [if_pos hj, if_pos (Fin.ext hj)]
    · rw [if_neg hj, if_neg fun h => hj (congrArg Fin.val h)]
  have hs : (⟨2, by omega⟩ : Fin d) ≠ (hypCoord hd Q' hQs hps).star ⟨0, by omega⟩ := by
    rw [hypCoord_star]
    intro h
    have h' : (2 : ℕ) = starNat 0 := congrArg Fin.val h
    exact absurd h' (by decide)
  have hne : (Pi.single ⟨0, by omega⟩ 1 : Fin d → F) ≠ Pi.single ⟨2, by omega⟩ 1 := by
    intro h
    have h0 := congrFun h ⟨0, by omega⟩
    simp at h0
  refine elementaryGroup_le_of_map b.equivFun he
    ((hypCoord hd Q' hQs hps).elementaryGroup_le_of_basic_line_T (k := k) _
      (nondegenerate_of_iso b.equivFun he hQ) (map_isoConjHom_le_orthogonalGroup b.equivFun he hL)
      (fun u w hu hw _ _ => ?_)
      (IsBasicT.single (mem_hypCoord_hyp (by simp)) (mem_hypCoord_hyp (by simp)) hs) hne
      (fun t => ?_))
  · have h := eichler_mem_map b.equivFun he (hrat u w hu hw)
    rwa [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
  · have h := eichler_mem_map b.equivFun he (hline t)
    rwa [map_smul, equivFun_self_eq_single, equivFun_self_eq_single] at h

section Descent

variable {V : Type*} [AddCommGroup V] [Module F V] {σ : F ≃+* F}
  {T : V →ₛₗ[(σ : F →+* F)] V}

theorem semilinear_equivFun_symm_fixed {ι : Type*} [Fintype ι] (b : Basis ι F V)
    (hb : ∀ i, T (b i) = b i) {x : ι → F} (hx : ∀ i, σ (x i) = x i) :
    T (b.equivFun.symm x) = b.equivFun.symm x := by
  rw [Basis.equivFun_symm_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smulₛₗ, RingEquiv.coe_toRingHom, hx, hb]

theorem restrictFix_mem_orthogonalGroup {Q : QuadraticForm F V} (hTQ : ∀ v, Q (T v) = σ (Q v))
    {g : V ≃ₗ[F] V} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hg : g ∈ semilinCentralizer T) :
    restrictFix hg ∈ TauCeti.QuadraticMap.orthogonalGroup (descentForm hTQ) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro w
  exact Subtype.ext (by rw [coe_descentForm, coe_descentForm, coe_restrictFix, map_of_mem hgO])

theorem restrictFix_mul_self {g : V ≃ₗ[F] V} (hgg : g * g = 1) (hg : g ∈ semilinCentralizer T) :
    restrictFix hg * restrictFix hg = 1 := by
  refine LinearEquiv.ext fun w => Subtype.ext ?_
  change g (g w) = w
  rw [← LinearEquiv.mul_apply, hgg]
  rfl

end Descent

theorem eichler_mem_liftSubgroup {d : ℕ} {Q : QuadraticForm F (Fin d → F)}
    (hder : elementaryGroup Q = CFSG.RankThree.Classical2.orthDerived Q)
    {H : Subgroup (matrixProjectiveDerived Q)} {P : ((Fin d → F) ≃ₗ[F] (Fin d → F)) → Prop}
    (hH : ∀ X : matrixDerived Q, P (matrixLinearIso (X : GL (Fin d) F)) →
      matrixProjectiveProjection Q X ∈ H)
    {u w : Fin d → F} (h : P (eichler Q u w)) : eichler Q u w ∈ liftSubgroup Q H := by
  have hX : matrixLinearIso
      ((⟨_, eichlerMat_mem_derived hder u w⟩ : matrixDerived Q) : GL (Fin d) F) =
        eichler Q u w :=
    matrixLinearIso_symm_apply_apply _
  exact mem_liftSubgroup.mpr ⟨_, hH _ (by rw [hX]; exact h), hX⟩

theorem eq_top_of_adapted_basis {d : ℕ} (hd : 6 ≤ d) {Q : QuadraticForm F (Fin d → F)}
    (hQ : (polarBilin Q).Nondegenerate)
    (hder : elementaryGroup Q = CFSG.RankThree.Classical2.orthDerived Q) {σ : F ≃+* F}
    {T : (Fin d → F) →ₛₗ[(σ : F →+* F)] (Fin d → F)} (hTQ : ∀ v, Q (T v) = σ (Q v))
    {A : (Fin d → F) ≃ₗ[F] (Fin d → F)} (hAO : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {H : Subgroup (matrixProjectiveDerived Q)}
    (hHT : ∀ X : matrixDerived Q,
      (∀ v, matrixLinearIso (X : GL (Fin d) F) (T v) =
        T (matrixLinearIso (X : GL (Fin d) F) v)) →
      matrixProjectiveProjection Q X ∈ H)
    (hHA : ∀ X : matrixDerived Q,
      matrixLinearIso (X : GL (Fin d) F) * A = A * matrixLinearIso (X : GL (Fin d) F) →
      matrixProjectiveProjection Q X ∈ H)
    (b : Basis (Fin d) F (Fin d → F)) (hbQ : ∀ a : Fin d, a.val < 6 → Q (b a) = 0)
    (hbpol : ∀ a j : Fin d, a.val < 6 →
      polar Q (b a) (b j) = if j.val = starNat a.val then 1 else 0)
    (hbT : ∀ i, T (b i) = b i) (hA0 : A (b ⟨0, by omega⟩) = b ⟨0, by omega⟩)
    (hA2 : A (b ⟨2, by omega⟩) = b ⟨2, by omega⟩) :
    H = ⊤ := by
  refine eq_top_of_elementaryGroup_le hder (elementaryGroup_le_of_adapted hd hQ b hbQ hbpol
    (descentField σ) (liftSubgroup_le_orthogonalGroup H) (fun x y hx hy => ?_) (fun t => ?_))
  · have hX := semilinear_equivFun_symm_fixed b hbT fun i => mem_descentField.1 (hx i)
    have hY := semilinear_equivFun_symm_fixed b hbT fun i => mem_descentField.1 (hy i)
    refine eichler_mem_liftSubgroup hder (P := fun E => ∀ v, E (T v) = T (E v)) hHT fun v => ?_
    rw [semilinear_eichler_apply hTQ, hX, hY]
  · refine eichler_mem_liftSubgroup hder (P := fun E => E * A = A * E) hHA ?_
    have h := eichler_conj hAO (b ⟨0, by omega⟩) (t • b ⟨2, by omega⟩)
    rw [map_smul, hA0, hA2] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm

theorem exists_fixBasis_adapted [Finite F] [CharP F 2] {n : ℕ} (hn : 4 ≤ n)
    {Q : QuadraticForm F (Fin (2 * n) → F)} (hQ : (polarBilin Q).Nondegenerate)
    {σ : F ≃+* F} (hσσ : σ * σ = 1) (hσ1 : σ ≠ 1)
    {T : (Fin (2 * n) → F) →ₛₗ[(σ : F →+* F)] (Fin (2 * n) → F)} (hTT : ∀ v, T (T v) = v)
    (hTQ : ∀ v, Q (T v) = σ (Q v)) {A : (Fin (2 * n) → F) ≃ₗ[F] (Fin (2 * n) → F)}
    (hAO : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hAA : A * A = 1)
    (hAT : ∀ v, A (T v) = T (A v)) :
    ∃ b : Basis (Fin (2 * n)) F (Fin (2 * n) → F),
      (∀ a : Fin (2 * n), a.val < 6 → Q (b a) = 0) ∧
      (∀ a j : Fin (2 * n), a.val < 6 →
        polar Q (b a) (b j) = if j.val = starNat a.val then 1 else 0) ∧
      (∀ i, T (b i) = b i) ∧ A (b ⟨0, by omega⟩) = b ⟨0, by omega⟩ ∧
      A (b ⟨2, by omega⟩) = b ⟨2, by omega⟩ := by
  have hσσ' : ∀ a, σ (σ a) = a := fun a => by
    change (σ * σ) a = a
    rw [hσσ]
    rfl
  obtain ⟨c, hc⟩ : ∃ c, σ c ≠ c := by
    by_contra! h
    exact hσ1 (RingEquiv.ext h)
  have : Module.Finite (descentField σ) (fixSpace T) := finite_fixSpace
  have hdimW : finrank (descentField σ) (fixSpace T) = 2 * n := by
    rw [finrank_fixSpace hσσ' hTT hc, Module.finrank_fin_fun]
  have hQ₀ := nondegenerate_descentForm hTQ hQ (span_fixSpace hσσ' hTT hc)
  have hAc : A ∈ semilinCentralizer T := hAT
  obtain ⟨u₀, w₀, huw, hu, hw, hp, htu, htw⟩ := exists_singular_plane_of_involution hQ₀
    (by omega) (restrictFix_mem_orthogonalGroup hTQ hAO hAc) (restrictFix_mul_self hAA hAc)
  obtain ⟨b₀, hb0, hb2, hbQ, hbpol⟩ := exists_adapted_basis hQ₀ hn hdimW huw hu hw hp
  have hb := fixSpaceBasis_apply hσσ' hTT hc b₀
  refine ⟨fixSpaceBasis hσσ' hTT hc b₀, fun a ha => ?_, fun a j ha => ?_, fun i => ?_, ?_, ?_⟩
  · rw [hb, ← coe_descentForm hTQ, hbQ a ha, ZeroMemClass.coe_zero]
  · rw [hb, hb, ← coe_polar_descentForm hTQ, hbpol a j ha]
    split_ifs <;> simp
  · rw [hb]
    exact mem_fixSpace.1 (b₀ i).2
  · rw [hb, hb0 _ rfl]
    exact congrArg Subtype.val htu
  · rw [hb, hb2 _ rfl]
    exact congrArg Subtype.val htw

end KGF

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem eq_top_of_fix_semilinear_linear (hn : 4 ≤ n) {Q : QuadraticForm F (Fin (2 * n) → F)}
    (hQ : (polarBilin Q).Nondegenerate)
    (hder : elementaryGroup Q = CFSG.RankThree.Classical2.orthDerived Q)
    {σ : F ≃+* F} (hσσ : σ * σ = 1) (hσ1 : σ ≠ 1)
    {T : (Fin (2 * n) → F) →ₛₗ[(σ : F →+* F)] (Fin (2 * n) → F)} (hTT : ∀ v, T (T v) = v)
    (hTQ : ∀ v, Q (T v) = σ (Q v))
    {A : (Fin (2 * n) → F) ≃ₗ[F] (Fin (2 * n) → F)}
    (hAO : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hAA : A * A = 1)
    (hAT : ∀ v, A (T v) = T (A v)) {H : Subgroup (matrixProjectiveDerived Q)}
    (hHT : ∀ X : matrixDerived Q,
      (∀ v, matrixLinearIso (X : GL (Fin (2 * n)) F) (T v) =
        T (matrixLinearIso (X : GL (Fin (2 * n)) F) v)) →
      matrixProjectiveProjection Q X ∈ H)
    (hHA : ∀ X : matrixDerived Q,
      matrixLinearIso (X : GL (Fin (2 * n)) F) * A = A * matrixLinearIso (X : GL (Fin (2 * n)) F) →
      matrixProjectiveProjection Q X ∈ H) :
    H = ⊤ := by
  obtain ⟨b, hbQ, hbpol, hbT, hA0, hA2⟩ :=
    KGF.exists_fixBasis_adapted hn hQ hσσ hσ1 hTT hTQ hAO hAA hAT
  exact KGF.eq_top_of_adapted_basis (by omega) hQ hder hTQ hAO hHT hHA b hbQ hbpol hbT hA0 hA2

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottKGGOmPlus

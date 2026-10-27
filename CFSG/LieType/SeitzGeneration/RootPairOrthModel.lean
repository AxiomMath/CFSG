module

public import CFSG.LieType.SeitzGeneration.RootPairOrthCenter
public import CFSG.LieType.SeitzGeneration.RootPairOrthSL2
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorBridge

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  (matrixProjectiveConjugationHom_eq_of_left_eq_mul_scalar)

namespace RootPairOrth

section Rational

variable {K : Type} [Field K] {k : Subfield K} {d : ℕ} {Q₀ : QuadraticForm k (Fin d → k)}
  {Q : QuadraticForm K (Fin d → K)}

theorem Q_isRat_mem (hext : IsExtension k Q₀ Q) {w : Fin d → K} (hw : IsRat k w) : Q w ∈ k := by
  have : w = vecIncl k (fun i => ⟨w i, hw i⟩) := rfl
  rw [this, hext]
  exact (Q₀ _).2

theorem polar_isRat_mem (hext : IsExtension k Q₀ Q) {x y : Fin d → K} (hx : IsRat k x)
    (hy : IsRat k y) : polar Q x y ∈ k := by
  unfold QuadraticMap.polar
  exact k.sub_mem (k.sub_mem (Q_isRat_mem hext (hx.add hy)) (Q_isRat_mem hext hx))
    (Q_isRat_mem hext hy)

theorem eichler_entry_mem (S : SplitCoord Q) (hext : IsExtension k Q₀ Q) {u w : Fin d → K}
    (hu : IsRat k u) (hw : IsRat k w) (hQu : Q u = 0) (hp : polar Q u w = 0) (i j : Fin d) :
    eichler Q u w (Pi.single j 1) i ∈ k := by
  rw [eichler_apply hQu hp]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, S.polar_single]
  exact k.sub_mem (k.add_mem (isRat_single k j i) (k.mul_mem (hu _) (hw i)))
    (k.mul_mem (k.add_mem (hw _) (k.mul_mem (Q_isRat_mem hext hw) (hu _))) (hu i))

theorem eichlerMat_rational (S : SplitCoord Q) (hext : IsExtension k Q₀ Q) {σ : K ≃+* K}
    (hσk : ∀ x, x ∈ k ↔ σ x = x) {u w : Fin d → K} (hu : IsRat k u) (hw : IsRat k w)
    (hQu : Q u = 0) (hp : polar Q u w = 0) :
    ∃ B ∈ matrixIsometries Q₀, glIncl k B = (matrixLinearIso (d := d) (K := K)).symm
      (eichler Q u w) := by
  set M : GL (Fin d) K := (matrixLinearIso (d := d) (K := K)).symm (eichler Q u w) with hMdef
  have hMv : ∀ v, M.val *ᵥ v = eichler Q u w v := fun v => by
    have h1 : matrixLinearIso M v = M.val *ᵥ v := rfl
    rw [← h1, hMdef, MulEquiv.apply_symm_apply]
  have hfix : glFieldAut (Fin d) K σ M = M := by
    apply Units.ext
    ext i j
    show σ (M.val i j) = M.val i j
    have hent : M.val i j = eichler Q u w (Pi.single j 1) i := by
      rw [← hMv, Matrix.mulVec_single_one]
      rfl
    rw [hent]
    exact (hσk _).mp (eichler_entry_mem S hext hu hw hQu hp i j)
  obtain ⟨B, hB⟩ := exists_glIncl_of_fixed k hσk hfix
  refine ⟨B, ?_, hB⟩
  rw [mem_matrixIsometries_iff]
  intro v
  have h1 : ((Q₀ (matrixLinearEquiv B v) : k) : K) = ((Q₀ v : k) : K) := by
    rw [← hext, ← hext, matrixLinearEquiv_apply, ← mulVec_vecIncl, hB, hMv]
    exact (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (eichler_mem_orthogonalGroup Q u w)) _
  exact Subtype.ext h1

end Rational

section Lift

variable {K : Type} [Field K] {k : Subfield K} {d : ℕ} {Q₀ : QuadraticForm k (Fin d → k)}
  {Q : QuadraticForm K (Fin d → K)}

variable (Q) in
@[expose] def liftSubgroup (H : Subgroup (matrixProjectiveDerived Q)) :
    Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
  (H.comap (matrixProjectiveProjection Q)).map
    ((matrixLinearIso (d := d) (K := K)).toMonoidHom.comp (matrixDerived Q).subtype)

theorem mem_liftSubgroup {H : Subgroup (matrixProjectiveDerived Q)}
    {E : (Fin d → K) ≃ₗ[K] (Fin d → K)} :
    E ∈ liftSubgroup Q H ↔ ∃ A : matrixDerived Q, matrixProjectiveProjection Q A ∈ H ∧
      matrixLinearIso (A : GL (Fin d) K) = E := by
  unfold liftSubgroup
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact ⟨A, hA, rfl⟩
  · rintro ⟨A, hA, rfl⟩
    exact ⟨A, hA, rfl⟩

theorem liftSubgroup_le_orthogonalGroup (H : Subgroup (matrixProjectiveDerived Q)) :
    liftSubgroup Q H ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
  intro E hE
  obtain ⟨A, -, rfl⟩ := mem_liftSubgroup.mp hE
  exact matrixDerived_le_isometries Q A.2

theorem eq_top_of_elementaryGroup_le (hder : elementaryGroup Q = orthDerived Q)
    {H : Subgroup (matrixProjectiveDerived Q)} (h : elementaryGroup Q ≤ liftSubgroup Q H) :
    H = ⊤ := by
  rw [eq_top_iff]
  intro t _
  obtain ⟨A, rfl⟩ := matrixProjectiveProjection_surjective Q t
  have hA : matrixLinearIso (A : GL (Fin d) K) ∈ elementaryGroup Q := by
    rw [hder, ← CFSG.RankThree.PartOne.KCOrthComm.map_matrixDerived Q]
    exact ⟨A.1, A.2, rfl⟩
  obtain ⟨A', hA'H, hA'⟩ := mem_liftSubgroup.mp (h hA)
  have : A' = A := Subtype.ext (matrixLinearIso.injective hA')
  rwa [this] at hA'H

end Lift

section Members

variable {K : Type} [Field K] {k : Subfield K} {d : ℕ} {Q₀ : QuadraticForm k (Fin d → k)}
  {Q : QuadraticForm K (Fin d → K)} (SC : SplitCoord Q) (hext : IsExtension k Q₀ Q)
  {σ : K ≃+* K} (hσk : ∀ x, x ∈ k ↔ σ x = x) (hder : elementaryGroup Q = orthDerived Q)

theorem matrixLinearIso_symm_apply_apply (E : (Fin d → K) ≃ₗ[K] (Fin d → K)) :
    matrixLinearIso ((matrixLinearIso (d := d) (K := K)).symm E) = E :=
  MulEquiv.apply_symm_apply _ _

include hder in
theorem eichlerMat_mem_derived (u w : Fin d → K) :
    (matrixLinearIso (d := d) (K := K)).symm (eichler Q u w) ∈ matrixDerived Q := by
  have h : eichler Q u w ∈ orthDerived Q := hder ▸ eichler_mem_elementaryGroup Q u w
  rw [← CFSG.RankThree.PartOne.KCOrthComm.map_matrixDerived Q] at h
  obtain ⟨M, hM, hMe⟩ := h
  have : M = (matrixLinearIso (d := d) (K := K)).symm (eichler Q u w) :=
    (MulEquiv.eq_symm_apply _).mpr hMe
  rwa [← this]

include SC hext hσk hder in
theorem eichler_mem_lift {H : Subgroup (matrixProjectiveDerived Q)}
    (hN : subfieldFixedGroup k Q₀ Q ≤ H) {u w : Fin d → K} (hu : IsRat k u) (hw : IsRat k w)
    (hQu : Q u = 0) (hp : polar Q u w = 0) : eichler Q u w ∈ liftSubgroup Q H := by
  obtain ⟨B, hB, hBM⟩ := eichlerMat_rational SC hext hσk hu hw hQu hp
  have hA : (⟨_, eichlerMat_mem_derived hder u w⟩ : matrixDerived Q) ∈
      subfieldIsometries k Q₀ Q := by
    rw [subfieldIsometries, Subgroup.mem_subgroupOf]
    exact ⟨B, hB, hBM⟩
  refine mem_liftSubgroup.mpr ⟨⟨_, eichlerMat_mem_derived hder u w⟩, hN ⟨_, hA, rfl⟩, ?_⟩
  exact matrixLinearIso_symm_apply_apply _

include SC hext hσk hder in
theorem conj_eichler_mem_lift {H : Subgroup (matrixProjectiveDerived Q)} (gp : similarityPairs Q)
    (hgp : gp.val.right = 1)
    (hN' : (subfieldFixedGroup k Q₀ Q).map (matrixProjectiveConjugationHom Q gp).toMonoidHom ≤ H)
    {u w : Fin d → K} (hu : IsRat k u) (hw : IsRat k w) (hQu : Q u = 0) (hp : polar Q u w = 0) :
    matrixLinearIso gp.val.left * eichler Q u w * (matrixLinearIso gp.val.left)⁻¹ ∈
      liftSubgroup Q H := by
  obtain ⟨B, hB, hBM⟩ := eichlerMat_rational SC hext hσk hu hw hQu hp
  have hA : (⟨_, eichlerMat_mem_derived hder u w⟩ : matrixDerived Q) ∈
      subfieldIsometries k Q₀ Q := by
    rw [subfieldIsometries, Subgroup.mem_subgroupOf]
    exact ⟨B, hB, hBM⟩
  set A : matrixDerived Q := ⟨_, eichlerMat_mem_derived hder u w⟩ with hAdef
  refine mem_liftSubgroup.mpr ⟨matrixDerivedConjugation Q gp A, ?_, ?_⟩
  · rw [← matrixProjectiveConjugation_mk]
    exact hN' ⟨_, ⟨A, hA, rfl⟩, rfl⟩
  · rw [matrixDerivedConjugation_val, hgp, map_one]
    change matrixLinearIso (gp.val.left * A.val * gp.val.left⁻¹) = _
    rw [map_mul, map_mul, map_inv, hAdef]
    simp only [matrixLinearIso_symm_apply_apply]

end Members

section Frobenius

theorem exists_gen_aut {K : Type} [Field K] [Finite K] (k : Subfield K) {p : ℕ} (hp : p.Prime)
    (hdeg : Module.finrank k K = p) :
    ∃ σ : K ≃+* K, orderOf σ = p ∧ ∀ x, x ∈ k ↔ σ x = x := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := K ≃ₐ[k] K)
  have hord : orderOf g = p := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, IsGalois.card_aut_eq_finrank, hdeg]
  have hpow : ∀ (n : ℕ) (x : K), (g.toRingEquiv ^ n) x = (g ^ n) x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ', pow_succ']
      change g ((g.toRingEquiv ^ n) x) = g ((g ^ n) x)
      rw [ih]
  have := Fact.mk hp
  refine ⟨g.toRingEquiv, ?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · apply orderOf_eq_prime
    · have h1 : g ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one g
      ext x
      rw [hpow, h1]
      rfl
    · intro h
      have : g = 1 := by
        ext x
        have := congrArg (fun f : K ≃+* K => f x) h
        exact this
      rw [this, orderOf_one] at hord
      exact hp.one_lt.ne hord
  · exact g.commutes ⟨x, hx⟩
  · have hfix : ∀ f : K ≃ₐ[k] K, f x = x := by
      intro f
      have hf := hg f
      have hle : Subgroup.zpowers g ≤ MulAction.stabilizer (K ≃ₐ[k] K) x :=
        (Subgroup.zpowers_le).mpr (MulAction.mem_stabilizer_iff.mpr hx)
      exact MulAction.mem_stabilizer_iff.mp (hle hf)
    have hbot := (IsGalois.mem_bot_iff_fixed (F := k) x).mpr hfix
    obtain ⟨y, hy⟩ := IntermediateField.mem_bot.mp hbot
    rw [← hy]
    exact y.2

end Frobenius

section Eigen

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ} {Q₀ : QuadraticForm k (Fin d → k)}
  {Q : QuadraticForm K (Fin d → K)} {σ : K ≃+* K} {p : ℕ}

omit [Finite K] in
theorem map_le_of_eigen (hS : SubfieldSetup k Q₀ Q σ p) (gp : similarityPairs Q)
    (hgp : gp.val.right = 1) {a : K} (ha : a ≠ 0)
    (heig : ∀ r c, σ (gp.val.left.val r c) = a * gp.val.left.val r c) :
    (subfieldFixedGroup k Q₀ Q).map (matrixProjectiveConjugationHom Q gp).toMonoidHom ≤
      subfieldFixedGroup k Q₀ Q := by
  have hleft : glFieldAut (Fin d) K σ gp.val.left =
      gp.val.left * GeneralLinearGroup.scalar (Fin d) (Units.mk0 a ha) := by
    apply Units.ext
    ext r c
    show σ (gp.val.left.val r c) = (gp.val.left.val *
      (GeneralLinearGroup.scalar (Fin d) (Units.mk0 a ha)).val) r c
    rw [heig]
    simp [Matrix.mul_diagonal, mul_comm]
  have hcomm : fieldAutT Q σ hS.hQσ * matrixProjectiveConjugationHom Q gp =
      matrixProjectiveConjugationHom Q gp * fieldAutT Q σ hS.hQσ := by
    unfold fieldAutT
    rw [← map_mul, ← map_mul]
    refine matrixProjectiveConjugationHom_eq_of_left_eq_mul_scalar Q (Units.mk0 a ha) ?_ ?_
    · change (fieldPair Q σ hS.hQσ).val.left * glFieldAut (Fin d) K
          (fieldPair Q σ hS.hQσ).val.right gp.val.left = (gp.val.left *
            glFieldAut (Fin d) K gp.val.right (fieldPair Q σ hS.hQσ).val.left) *
              GeneralLinearGroup.scalar (Fin d) (Units.mk0 a ha)
      rw [fieldPair_left, fieldPair_right, hgp, map_one]
      simp only [one_mul, mul_one]
      exact hleft
    · change (fieldPair Q σ hS.hQσ).val.right * gp.val.right = gp.val.right *
        (fieldPair Q σ hS.hQσ).val.right
      rw [fieldPair_right, hgp, mul_one, one_mul]
  rintro _ ⟨t, ht, rfl⟩
  have h1 : fieldAutT Q σ hS.hQσ t = t := (fieldAutT_apply_iff hS t).mpr ht
  refine (fieldAutT_apply_iff hS _).mp ?_
  calc fieldAutT Q σ hS.hQσ (matrixProjectiveConjugationHom Q gp t)
      = (fieldAutT Q σ hS.hQσ * matrixProjectiveConjugationHom Q gp) t := rfl
    _ = (matrixProjectiveConjugationHom Q gp * fieldAutT Q σ hS.hQσ) t := by rw [hcomm]
    _ = matrixProjectiveConjugationHom Q gp (fieldAutT Q σ hS.hQσ t) := rfl
    _ = matrixProjectiveConjugationHom Q gp t := by rw [h1]

end Eigen

section Fail

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ} {Q₀ : QuadraticForm k (Fin d → k)}
  {Q : QuadraticForm K (Fin d → K)} {σ : K ≃+* K}

omit [Finite K] in
theorem polar_similarity {g : (Fin d → K) ≃ₗ[K] (Fin d → K)} {μ : K}
    (hg : ∀ v, Q (g v) = μ * Q v) (x y : Fin d → K) : polar Q (g x) (g y) = μ * polar Q x y := by
  unfold QuadraticMap.polar
  rw [← g.map_add, hg, hg, hg]
  ring

theorem elementaryGroup_le_lift_of_fail (SC : SplitCoord Q)
    (hext : IsExtension k Q₀ Q) (hσk : ∀ x, x ∈ k ↔ σ x = x)
    (hder : elementaryGroup Q = orthDerived Q) (hd : 5 < d) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = Nat.card k ^ p) (hk3 : 3 ≤ Nat.card k)
    {H : Subgroup (matrixProjectiveDerived Q)} (hN : subfieldFixedGroup k Q₀ Q ≤ H)
    (gp : similarityPairs Q) (hgp : gp.val.right = 1)
    (hN' : (subfieldFixedGroup k Q₀ Q).map (matrixProjectiveConjugationHom Q gp).toMonoidHom ≤ H)
    (hfail : ¬ PairsRational SC k gp.val.left.val (multiplier Q gp : K)) :
    elementaryGroup Q ≤ liftSubgroup Q H := by
  simp only [PairsRational, not_forall] at hfail
  obtain ⟨x, y, x₀, y₀, hxy, hxy₀, hPhi⟩ := hfail
  set gm : GL (Fin d) K := gp.val.left with hgm
  set μ : K := (multiplier Q gp : K) with hμdef
  have hμ : μ ≠ 0 := Units.ne_zero _
  have hg : ∀ v, Q (matrixLinearIso gm v) = μ * Q v := fun v => by
    have h := multiplier_spec Q gp v
    rw [coordinateSemilinearMap_apply, hgp] at h
    exact h
  have hH := liftSubgroup_le_orthogonalGroup H
  have hb : CoordEichler (liftSubgroup Q H) SC := fun u v huv =>
    eichler_mem_lift SC hext hσk hder hN (isRat_single k u) (isRat_single k v) (SC.Q_single u)
      (SC.isTS_single huv).2.2
  obtain ⟨hx, hy, hxy'⟩ := hxy.isTS
  obtain ⟨hx₀, hy₀, hxy₀'⟩ := hxy₀.isTS
  obtain ⟨hxr, hyr⟩ := hxy.isRat k
  obtain ⟨hx₀r, hy₀r⟩ := hxy₀.isRat k
  have hne : x ≠ y := fun h => hPhi (by rw [h, phi_self_left]; exact k.zero_mem)
  have hc₁ : Q (gm.val *ᵥ x₀) = 0 := by
    have := hg x₀
    rw [hx₀, mul_zero] at this
    exact this
  have hc₂ : Q (gm.val *ᵥ y₀) = 0 := by
    have := hg y₀
    rw [hy₀, mul_zero] at this
    exact this
  have hc₁₂ : polar Q (gm.val *ᵥ x₀) (gm.val *ᵥ y₀) = 0 := by
    have := polar_similarity hg x₀ y₀
    rw [hxy₀', mul_zero] at this
    exact this
  have hHx : ∀ t ∈ k, eichler Q x (t • y) ∈ liftSubgroup Q H := by
    intro t ht
    have hty : IsRat k (t • y) := fun i => k.mul_mem ht (hyr i)
    have hpt : polar Q x (t • y) = 0 := by rw [polar_smul_right_eq, hxy', mul_zero]
    exact eichler_mem_lift SC hext hσk hder hN hxr hty hx hpt
  have hHc : ∀ t ∈ k, eichler Q (gm.val *ᵥ x₀) ((μ⁻¹ * t) • (gm.val *ᵥ y₀)) ∈
      liftSubgroup Q H := by
    intro t ht
    have hty : IsRat k (t • y₀) := fun i => k.mul_mem ht (hy₀r i)
    have hpt : polar Q x₀ (t • y₀) = 0 := by rw [polar_smul_right_eq, hxy₀', mul_zero]
    have h := conj_eichler_mem_lift SC hext hσk hder gp hgp hN' hx₀r hty hx₀ hpt
    rw [eichler_conj_similarity hμ hg] at h
    have e1 : matrixLinearIso gm x₀ = gm.val *ᵥ x₀ := rfl
    have e2 : μ⁻¹ • matrixLinearIso gm (t • y₀) = (μ⁻¹ * t) • (gm.val *ᵥ y₀) := by
      rw [map_smul, smul_smul]
      rfl
    rw [e1, e2] at h
    exact h
  have hline := eichler_line_of_irrational hp hp2 hK hk3 hx hy hxy' hc₁ hc₂ hc₁₂ hHx hHc hPhi
  exact SC.elementaryGroup_le_of_basic_line _ hd hH hb hxy hne hline

end Fail

section Assembly

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ} {Q₀ : QuadraticForm k (Fin d → k)}
  {Q : QuadraticForm K (Fin d → K)}

theorem orthPair_of_split (SC : SplitCoord Q)
    (hext : IsExtension k Q₀ Q) (hder : elementaryGroup Q = orthDerived Q) (hd : 5 < d)
    (h2 : (2 : K) ≠ 0) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hdeg : Module.finrank k K = p)
    (hK : Nat.card K = Nat.card k ^ p) (hk3 : 3 ≤ Nat.card k)
    (hsetup : ∀ σ : K ≃+* K, orderOf σ = p → (∀ x, x ∈ k ↔ σ x = x) →
      SubfieldSetup k Q₀ Q σ p)
    (gp : similarityPairs Q) (hgp : gp.val.right = 1)
    (hne : (subfieldFixedGroup k Q₀ Q).map (matrixProjectiveConjugationHom Q gp).toMonoidHom ≠
      subfieldFixedGroup k Q₀ Q) :
    Subgroup.closure ((subfieldFixedGroup k Q₀ Q : Set (matrixProjectiveDerived Q)) ∪
      ((subfieldFixedGroup k Q₀ Q).map (matrixProjectiveConjugationHom Q gp).toMonoidHom :
        Set (matrixProjectiveDerived Q))) = ⊤ := by
  obtain ⟨σ, hσo, hσk⟩ := exists_gen_aut k hp hdeg
  have hS := hsetup σ hσo hσk
  by_cases hP : PairsRational SC k gp.val.left.val (multiplier Q gp : K)
  · exfalso
    have hdet : gp.val.left.val.det ≠ 0 :=
      (((Matrix.isUnit_iff_isUnit_det _).mp gp.val.left.isUnit)).ne_zero
    obtain ⟨a, ha, heig⟩ := SC.rational_of_pairs hP h2 hd (σ := σ.toRingHom)
      (fun x => (hσk x).symm) (Units.ne_zero _) hdet
    have hle := map_le_of_eigen hS gp hgp ha heig
    apply hne
    have hcard : Nat.card ((subfieldFixedGroup k Q₀ Q).map
        (matrixProjectiveConjugationHom Q gp).toMonoidHom) = Nat.card (subfieldFixedGroup k Q₀ Q) :=
      Subgroup.card_map_of_injective (matrixProjectiveConjugationHom Q gp).injective
    exact Subgroup.eq_of_le_of_card_ge hle hcard.ge
  · have hl := elementaryGroup_le_lift_of_fail SC hext hσk hder hd hp hp2 hK hk3
      (H := Subgroup.closure ((subfieldFixedGroup k Q₀ Q : Set (matrixProjectiveDerived Q)) ∪
        ((subfieldFixedGroup k Q₀ Q).map (matrixProjectiveConjugationHom Q gp).toMonoidHom :
          Set (matrixProjectiveDerived Q))))
      (fun x hx => Subgroup.subset_closure (Or.inl hx)) gp hgp
      (fun x hx => Subgroup.subset_closure (Or.inr hx)) hP
    exact eq_top_of_elementaryGroup_le hder hl

end Assembly

end RootPairOrth

end CFSG.LieType.SeitzGeneration

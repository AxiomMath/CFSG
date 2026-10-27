module

public import CFSG.LieType.SeitzGeneration.OmegaF2.Sigma

public section

namespace CFSG.LieType.SeitzGeneration.OmegaF2

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.LieType.SeitzGeneration.RootPairOrth

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {k : Subfield K}
  {Q₀ : QuadraticForm k (Fin d → k)}

@[expose] def SigEigen (σ : K ≃+* K) (G : Matrix (Fin d) (Fin d) K) (v : Fin d → K) (θ : K) :
    Prop :=
  sigmaVec σ (G *ᵥ v) = θ • (G *ᵥ v)

private theorem coeff_eq_zero_of_mulVec_pair {G : Matrix (Fin d) (Fin d) K} (hdet : G.det ≠ 0)
    {v w : Fin d → K} (hind : LinearIndependent K ![v, w]) {s t : K}
    (h : s • (G *ᵥ v) + t • (G *ᵥ w) = 0) : s = 0 ∧ t = 0 := by
  have hinj : Function.Injective G.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det G).mpr (isUnit_iff_ne_zero.mpr hdet))
  refine LinearIndependent.pair_iff.mp hind s t ?_
  apply hinj
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_zero]
  exact h

theorem exists_sigEigen_of_two {G : Matrix (Fin d) (Fin d) K} (hdet : G.det ≠ 0) {σ : K ≃+* K}
    {v w w' : Fin d → K} (hind : LinearIndependent K ![v, w, w'])
    (h1 : sigmaVec σ (G *ᵥ v) ∈ Submodule.span K {G *ᵥ v, G *ᵥ w})
    (h2 : sigmaVec σ (G *ᵥ v) ∈ Submodule.span K {G *ᵥ v, G *ᵥ w'}) :
    ∃ θ : K, SigEigen σ G v θ := by
  have hunit : IsUnit G := (Matrix.isUnit_iff_isUnit_det G).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hinj : LinearMap.ker (Matrix.mulVecLin G) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (Matrix.mulVec_injective_iff_isUnit.mpr hunit)
  have hcomp : (Matrix.mulVecLin G) ∘ ![v, w, w'] = ![G *ᵥ v, G *ᵥ w, G *ᵥ w'] := by
    funext i
    fin_cases i <;> rfl
  have hind' : LinearIndependent K ![G *ᵥ v, G *ᵥ w, G *ᵥ w'] := by
    rw [← hcomp]
    exact hind.map' (Matrix.mulVecLin G) hinj
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp h1
  obtain ⟨a', b', hab'⟩ := Submodule.mem_span_pair.mp h2
  have hrel : (a - a') • (G *ᵥ v) + b • (G *ᵥ w) + (-b') • (G *ᵥ w') = 0 := by
    linear_combination (norm := module) hab - hab'
  have key := Fintype.linearIndependent_iff.mp hind' ![a - a', b, -b'] (by
    simpa [Fin.sum_univ_three] using hrel)
  have hb : b = 0 := by simpa using key 1
  refine ⟨a, ?_⟩
  show sigmaVec σ (G *ᵥ v) = a • (G *ᵥ v)
  rw [← hab, hb, zero_smul, add_zero]

theorem SigEigen.eq_of_add {G : Matrix (Fin d) (Fin d) K} (hdet : G.det ≠ 0) {σ : K ≃+* K}
    {v w : Fin d → K} (hind : LinearIndependent K ![v, w]) {θ₁ θ₂ θ₃ : K}
    (h₁ : SigEigen σ G v θ₁) (h₂ : SigEigen σ G w θ₂) (h₃ : SigEigen σ G (v + w) θ₃) :
    θ₁ = θ₂ := by
  have h₁' : sigmaVec σ (G *ᵥ v) = θ₁ • (G *ᵥ v) := h₁
  have h₂' : sigmaVec σ (G *ᵥ w) = θ₂ • (G *ᵥ w) := h₂
  have h₃' : sigmaVec σ (G *ᵥ (v + w)) = θ₃ • (G *ᵥ (v + w)) := h₃
  rw [Matrix.mulVec_add, sigmaVec_add, h₁', h₂'] at h₃'
  obtain ⟨e1, e2⟩ := coeff_eq_zero_of_mulVec_pair hdet hind (s := θ₁ - θ₃) (t := θ₂ - θ₃)
    (by linear_combination (norm := module) h₃')
  linear_combination e1 - e2

variable (S : HypCoord Q)

@[expose] def SigmaStable (Q : QuadraticForm K (Fin d → K)) (k : Subfield K) (σ : K ≃+* K)
    (G : Matrix (Fin d) (Fin d) K) : Prop :=
  ∀ v w : Fin d → K, IsRat k v → IsRat k w → Q v = 0 → Q w = 0 → polar Q v w = 0 →
    LinearIndependent K ![v, w] →
    sigmaVec σ (G *ᵥ v) ∈ Submodule.span K {G *ᵥ v, G *ᵥ w}

private theorem linearIndependent_single_comp {n : ℕ} (f : Fin n → Fin d)
    (hf : Function.Injective f) :
    LinearIndependent K (fun i => (Pi.single (f i) 1 : Fin d → K)) := by
  have h := (Pi.basisFun K (Fin d)).linearIndependent.comp f hf
  simpa [Function.comp_def, Pi.basisFun_apply] using h

private theorem linearIndependent_single_pair {a c : Fin d} (h1 : a ≠ c) :
    LinearIndependent K ![(Pi.single a 1 : Fin d → K), Pi.single c 1] := by
  have hinj : Function.Injective ![a, c] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have h := linearIndependent_single_comp (K := K) ![a, c] hinj
  convert h using 1
  funext i
  fin_cases i <;> rfl

private theorem linearIndependent_single_three {a c c' : Fin d} (h1 : a ≠ c) (h2 : a ≠ c')
    (h3 : c ≠ c') :
    LinearIndependent K ![(Pi.single a 1 : Fin d → K), Pi.single c 1, Pi.single c' 1] := by
  have hinj : Function.Injective ![a, c, c'] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have h := linearIndependent_single_comp (K := K) ![a, c, c'] hinj
  convert h using 1
  funext i
  fin_cases i <;> rfl

private theorem sigmaStable_single_pair (S : HypCoord Q) {σ : K ≃+* K}
    {G : Matrix (Fin d) (Fin d) K} (hstab : SigmaStable Q k σ G) {a c : Fin d} (ha : a ∈ S.hyp)
    (hc : c ∈ S.hyp) (hca : c ≠ a) (hcs : c ≠ S.star a) :
    sigmaVec σ (G *ᵥ (Pi.single a 1 : Fin d → K)) ∈
      Submodule.span K {G *ᵥ (Pi.single a 1 : Fin d → K), G *ᵥ (Pi.single c 1 : Fin d → K)} :=
  hstab _ _ (isRat_single k a) (isRat_single k c) (S.Q_single a ha) (S.Q_single c hc)
    (by rw [S.polar_single_single ha, if_neg (Ne.symm hcs)])
    (linearIndependent_single_pair (Ne.symm hca))

theorem exists_sigEigen_hyp {σ : K ≃+* K} {G : Matrix (Fin d) (Fin d) K} (hdet : G.det ≠ 0)
    (hstab : SigmaStable Q k σ G) {a : Fin d} (ha : a ∈ S.hyp) :
    ∃ θ : K, SigEigen σ G (Pi.single a 1) θ := by
  obtain ⟨c, c', hc, hc', hca, hcs, hc'a, hc's, hcc', -⟩ := S.exists_three_T ha
  exact exists_sigEigen_of_two hdet
    (linearIndependent_single_three (Ne.symm hca) (Ne.symm hc'a) (Ne.symm hcc'))
    (sigmaStable_single_pair S hstab ha hc hca hcs)
    (sigmaStable_single_pair S hstab ha hc' hc'a hc's)

private theorem linearIndependent_add_single_pair {a c e : Fin d} (hac : a ≠ c) (hae : a ≠ e)
    (hce : c ≠ e) :
    LinearIndependent K ![(Pi.single a 1 : Fin d → K) + Pi.single c 1, Pi.single e 1] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h0 := congrFun hst a
  have h1 := congrFun hst e
  simp [Pi.single_apply, hac, Ne.symm hac, hae, Ne.symm hae, hce, Ne.symm hce] at h0 h1
  exact ⟨h0, h1⟩

private theorem linearIndependent_add_single_three {a c e e' : Fin d} (hac : a ≠ c) (hae : a ≠ e)
    (hce : c ≠ e) (hae' : a ≠ e') (hce' : c ≠ e') (hee' : e ≠ e') :
    LinearIndependent K
      ![(Pi.single a 1 : Fin d → K) + Pi.single c 1, Pi.single e 1, Pi.single e' 1] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp [Fin.sum_univ_three] at hg
  have h0 := congrFun hg a
  have h1 := congrFun hg e
  have h2 := congrFun hg e'
  simp [Pi.single_apply, hac, Ne.symm hac, hae, Ne.symm hae, hce, Ne.symm hce, hae', Ne.symm hae',
    hce', Ne.symm hce', hee', Ne.symm hee'] at h0 h1 h2
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem exists_sigEigen_add_hyp {σ : K ≃+* K} {G : Matrix (Fin d) (Fin d) K} (hdet : G.det ≠ 0)
    (hstab : SigmaStable Q k σ G) {a c : Fin d} (ha : a ∈ S.hyp) (hc : c ∈ S.hyp) (hca : c ≠ a)
    (hcs : c ≠ S.star a) :
    ∃ θ : K, SigEigen σ G ((Pi.single a 1 : Fin d → K) + Pi.single c 1) θ := by
  classical
  have hac : a ≠ c := Ne.symm hca
  obtain ⟨e, he, he'⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, S.star a, c, S.star c} : Finset (Fin d))) (t := S.hyp)
    (lt_of_le_of_lt Finset.card_le_four (by have := S.card_hyp; omega))
  obtain ⟨e', he2, he2'⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, S.star a, c, S.star c, e} : Finset (Fin d))) (t := S.hyp)
    (lt_of_le_of_lt Finset.card_le_five (by have := S.card_hyp; omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he' he2'
  obtain ⟨hea, heSa, hec, heSc⟩ := he'
  obtain ⟨he'a, he'Sa, he'c, he'Sc, hee'⟩ := he2'
  have hrat : IsRat k ((Pi.single a 1 : Fin d → K) + Pi.single c 1) :=
    (isRat_single k a).add (isRat_single k c)
  have hQv : Q ((Pi.single a 1 : Fin d → K) + Pi.single c 1) = 0 := by
    rw [QuadraticMap.map_add Q, S.Q_single a ha, S.Q_single c hc, S.polar_single_single ha,
      if_neg (Ne.symm hcs)]
    ring
  have hpe : polar Q ((Pi.single a 1 : Fin d → K) + Pi.single c 1) (Pi.single e 1) = 0 := by
    rw [polar_add_left, S.polar_single_single ha, S.polar_single_single hc,
      if_neg (Ne.symm heSa), if_neg (Ne.symm heSc)]
    ring
  have hpe' : polar Q ((Pi.single a 1 : Fin d → K) + Pi.single c 1) (Pi.single e' 1) = 0 := by
    rw [polar_add_left, S.polar_single_single ha, S.polar_single_single hc,
      if_neg (Ne.symm he'Sa), if_neg (Ne.symm he'Sc)]
    ring
  have h1 := hstab _ _ hrat (isRat_single k e) hQv (S.Q_single e he) hpe
    (linearIndependent_add_single_pair hac (Ne.symm hea) (Ne.symm hec))
  have h2 := hstab _ _ hrat (isRat_single k e') hQv (S.Q_single e' he2) hpe'
    (linearIndependent_add_single_pair hac (Ne.symm he'a) (Ne.symm he'c))
  exact exists_sigEigen_of_two hdet
    (linearIndependent_add_single_three hac (Ne.symm hea) (Ne.symm hec) (Ne.symm he'a)
      (Ne.symm he'c) (Ne.symm hee'))
    h1 h2

private theorem sigEigen_hyp_of_pair (S : HypCoord Q) {σ : K ≃+* K}
    {G : Matrix (Fin d) (Fin d) K} (hdet : G.det ≠ 0) (hstab : SigmaStable Q k σ G)
    {a c : Fin d} (ha : a ∈ S.hyp) (hc : c ∈ S.hyp) (hca : c ≠ a) (hcs : c ≠ S.star a)
    {θ : K} (h : SigEigen σ G (Pi.single a 1) θ) : SigEigen σ G (Pi.single c 1) θ := by
  obtain ⟨θ₂, h₂⟩ := exists_sigEigen_hyp S hdet hstab hc
  obtain ⟨θ₃, h₃⟩ := exists_sigEigen_add_hyp S hdet hstab ha hc hca hcs
  have e : θ = θ₂ :=
    SigEigen.eq_of_add hdet (linearIndependent_single_pair (Ne.symm hca)) h h₂ h₃
  rw [e]
  exact h₂

theorem exists_common_sigEigen_hyp {σ : K ≃+* K} {G : Matrix (Fin d) (Fin d) K}
    (hdet : G.det ≠ 0) (hstab : SigmaStable Q k σ G) :
    ∃ θ : K, ∀ a ∈ S.hyp, SigEigen σ G (Pi.single a 1) θ := by
  have hcard := S.card_hyp
  obtain ⟨a₀, ha₀⟩ : S.hyp.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨θ, hθ⟩ := exists_sigEigen_hyp S hdet hstab ha₀
  obtain ⟨c, hc, hcn⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a₀, S.star a₀} : Finset (Fin d))) (t := S.hyp)
    (lt_of_le_of_lt Finset.card_le_two (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcn
  obtain ⟨hca₀, hcs₀⟩ := hcn
  refine ⟨θ, fun a ha => ?_⟩
  by_cases h1 : a = a₀
  · rw [h1]
    exact hθ
  by_cases h2 : a = S.star a₀
  · have hc' : SigEigen σ G (Pi.single c 1) θ :=
      sigEigen_hyp_of_pair S hdet hstab ha₀ hc hca₀ hcs₀ hθ
    refine sigEigen_hyp_of_pair S hdet hstab hc ha ?_ ?_ hc'
    · intro h
      exact hcs₀ (h.symm.trans h2)
    · intro h
      have hsc : S.star a₀ = S.star c := h2.symm.trans h
      exact hca₀ (((S.star_star a₀ ha₀).symm.trans
        ((congrArg S.star hsc).trans (S.star_star c hc))).symm)
  · exact sigEigen_hyp_of_pair S hdet hstab ha₀ ha h1 h2 hθ

private theorem linearIndependent_of_evalId {n : ℕ} {v : Fin n → Fin d → K} {f : Fin n → Fin d}
    (hM : ∀ i j, v i (f j) = if i = j then 1 else 0) : LinearIndependent K v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h := congrFun hg (f j)
  simpa [Finset.sum_apply, hM, mul_ite] using h

private theorem sigEigen_add_smul {σ : K ≃+* K} {G : Matrix (Fin d) (Fin d) K}
    (hσk : ∀ x, x ∈ k ↔ σ x = x) {v w : Fin d → K} {c θ : K} (hc : c ∈ k)
    (hv : SigEigen σ G v θ) (hw : SigEigen σ G w θ) : SigEigen σ G (v + c • w) θ := by
  have hσc : σ c = c := (hσk c).mp hc
  unfold SigEigen at hv hw ⊢
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, sigmaVec_add, sigmaVec_smul, hσc, hv, hw]
  module

private theorem sigma_mem_span_of_eigen_sum {σ : K ≃+* K} {G : Matrix (Fin d) (Fin d) K}
    {v w : Fin d → K} {l θ : K} (hx : SigEigen σ G (v + w) l) (hv : SigEigen σ G v θ) :
    sigmaVec σ (G *ᵥ w) ∈ Submodule.span K {G *ᵥ w, G *ᵥ v} := by
  unfold SigEigen at hx hv
  rw [Matrix.mulVec_add, sigmaVec_add] at hx
  rw [Submodule.mem_span_pair]
  exact ⟨l, l - θ, by linear_combination (norm := module) hv - hx⟩

private theorem isRat_smul_of_mem {c : K} {p : Fin d → K} (hc : c ∈ k) (hp : IsRat k p) :
    IsRat k (c • p) := by
  intro i
  exact k.mul_mem hc (hp i)

private theorem Q_sing_tail (S : HypCoord Q) {j t : Fin d} {c : K} (hj : j ∈ S.hyp)
    (ht : t ∉ S.hyp) (hc : Q (Pi.single t 1 : Fin d → K) + c = 0) :
    Q ((Pi.single j 1 + c • (Pi.single (S.star j) 1 : Fin d → K)) + Pi.single t 1) = 0 := by
  have hjs : S.star j ∈ S.hyp := S.star_mem j hj
  have hjt : j ≠ t := fun h => ht (h ▸ hj)
  have hjst : S.star j ≠ t := fun h => ht (h ▸ hjs)
  have hpjs : polar Q (Pi.single j 1 : Fin d → K) (Pi.single (S.star j) 1) = 1 := by
    rw [S.polar_single_single hj]
    simp
  have hpjt : polar Q (Pi.single j 1 : Fin d → K) (Pi.single t 1) = 0 := by
    rw [S.polar_single j hj, Pi.single_apply, if_neg hjst]
  have hpst : polar Q (Pi.single (S.star j) 1 : Fin d → K) (Pi.single t 1) = 0 := by
    rw [S.polar_single (S.star j) hjs, S.star_star j hj, Pi.single_apply, if_neg hjt]
  have hA : Q (Pi.single j 1 + c • (Pi.single (S.star j) 1 : Fin d → K)) = c := by
    rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, S.Q_single j hj, S.Q_single _ hjs,
      polar_smul_right_eq, hpjs]
    ring
  rw [QuadraticMap.map_add Q, hA, polar_add_left, polar_smul_left_eq, hpjt, hpst]
  linear_combination hc

private theorem sigEigen_sing_tail (S : HypCoord Q) (hext : IsExtension k Q₀ Q) {σ : K ≃+* K}
    {G : Matrix (Fin d) (Fin d) K} (hdet : G.det ≠ 0) (hstab : SigmaStable Q k σ G)
    {j t i₁ i₂ : Fin d} {c : K} (hck : c ∈ k) (hc : Q (Pi.single t 1 : Fin d → K) + c = 0)
    (ht : t ∉ S.hyp) (hj : j ∈ S.hyp) (hi₁ : i₁ ∈ S.hyp) (hi₂ : i₂ ∈ S.hyp)
    (h₁j : i₁ ≠ j) (h₁s : i₁ ≠ S.star j) (h₂j : i₂ ≠ j) (h₂s : i₂ ≠ S.star j) (h12 : i₁ ≠ i₂) :
    ∃ l : K, SigEigen σ G
      ((Pi.single j 1 + c • (Pi.single (S.star j) 1 : Fin d → K)) + Pi.single t 1) l := by
  have hjs : S.star j ∈ S.hyp := S.star_mem j hj
  have hjt : j ≠ t := fun h => ht (h ▸ hj)
  have hjst : S.star j ≠ t := fun h => ht (h ▸ hjs)
  have hi₁t : i₁ ≠ t := fun h => ht (h ▸ hi₁)
  have hi₂t : i₂ ≠ t := fun h => ht (h ▸ hi₂)
  have hrat : IsRat k ((Pi.single j 1 + c • (Pi.single (S.star j) 1 : Fin d → K)) + Pi.single t 1) :=
    ((isRat_single k j).add (isRat_smul_of_mem hck (isRat_single k (S.star j)))).add
      (isRat_single k t)
  have hQx := Q_sing_tail S hj ht hc
  have hpt : ∀ i ∈ S.hyp, polar Q (Pi.single t 1 : Fin d → K) (Pi.single i 1) = 0 := by
    intro i hi
    have hne : S.star i ≠ t := fun h => ht (h ▸ S.star_mem i hi)
    rw [polar_comm, S.polar_single i hi, Pi.single_apply, if_neg hne]
  have hpx : ∀ i ∈ S.hyp, i ≠ j → i ≠ S.star j →
      polar Q ((Pi.single j 1 + c • (Pi.single (S.star j) 1 : Fin d → K)) + Pi.single t 1)
        (Pi.single i 1) = 0 := by
    intro i hi hij his
    rw [polar_add_left, polar_add_left, polar_smul_left_eq, S.polar_single_single hj,
      if_neg (Ne.symm his), S.polar_single_single hjs, S.star_star j hj, if_neg (Ne.symm hij),
      hpt i hi]
    ring
  have hpair₁ : LinearIndependent K
      ![(Pi.single j 1 + c • (Pi.single (S.star j) 1 : Fin d → K)) + Pi.single t 1,
        Pi.single i₁ 1] := by
    refine linearIndependent_of_evalId (f := ![t, i₁]) ?_
    intro a b
    fin_cases a <;> fin_cases b <;>
      simp [Pi.single_apply, hjt, hjst, hi₁t, h₁j, h₁s, Ne.symm hjt, Ne.symm hjst, Ne.symm hi₁t,
        Ne.symm h₁j, Ne.symm h₁s]
  have hpair₂ : LinearIndependent K
      ![(Pi.single j 1 + c • (Pi.single (S.star j) 1 : Fin d → K)) + Pi.single t 1,
        Pi.single i₂ 1] := by
    refine linearIndependent_of_evalId (f := ![t, i₂]) ?_
    intro a b
    fin_cases a <;> fin_cases b <;>
      simp [Pi.single_apply, hjt, hjst, hi₂t, h₂j, h₂s, Ne.symm hjt, Ne.symm hjst, Ne.symm hi₂t,
        Ne.symm h₂j, Ne.symm h₂s]
  have hind : LinearIndependent K
      ![(Pi.single j 1 + c • (Pi.single (S.star j) 1 : Fin d → K)) + Pi.single t 1,
        Pi.single i₁ 1, Pi.single i₂ 1] := by
    refine linearIndependent_of_evalId (f := ![t, i₁, i₂]) ?_
    intro a b
    fin_cases a <;> fin_cases b <;>
      simp [Pi.single_apply, hjt, hjst, hi₁t, hi₂t, h₁j, h₁s, h₂j, h₂s, h12, Ne.symm hjt,
        Ne.symm hjst, Ne.symm hi₁t, Ne.symm hi₂t, Ne.symm h₁j, Ne.symm h₁s, Ne.symm h₂j,
        Ne.symm h₂s, Ne.symm h12]
  obtain ⟨l, hl⟩ := exists_sigEigen_of_two hdet hind
    (hstab _ _ hrat (isRat_single k i₁) hQx (S.Q_single i₁ hi₁) (hpx i₁ hi₁ h₁j h₁s) hpair₁)
    (hstab _ _ hrat (isRat_single k i₂) hQx (S.Q_single i₂ hi₂) (hpx i₂ hi₂ h₂j h₂s) hpair₂)
  exact ⟨l, hl⟩

theorem sigEigen_tail (hext : IsExtension k Q₀ Q) {σ : K ≃+* K} (hσk : ∀ x, x ∈ k ↔ σ x = x)
    {G : Matrix (Fin d) (Fin d) K} (hdet : G.det ≠ 0) (hstab : SigmaStable Q k σ G) {θ : K}
    (hθ : ∀ a ∈ S.hyp, SigEigen σ G (Pi.single a 1) θ) {t : Fin d} (ht : t ∉ S.hyp) :
    SigEigen σ G (Pi.single t 1) θ := by
  obtain ⟨c, hck, hc⟩ : ∃ c : K, c ∈ k ∧ Q (Pi.single t 1 : Fin d → K) + c = 0 :=
    ⟨-Q (Pi.single t 1 : Fin d → K), k.neg_mem (Q_isRat_mem hext (isRat_single k t)),
      add_neg_cancel _⟩
  have hcard := S.card_hyp
  obtain ⟨j, hj⟩ : S.hyp.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨j₂, hj₂, hj₂n⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({j, S.star j} : Finset (Fin d))) (t := S.hyp)
    (lt_of_le_of_lt Finset.card_le_two (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj₂n
  obtain ⟨hj₂j, hj₂s⟩ := hj₂n
  have hjs : S.star j ∈ S.hyp := S.star_mem j hj
  have hj₂s' : S.star j₂ ∈ S.hyp := S.star_mem j₂ hj₂
  have hsj₂j : S.star j₂ ≠ j := fun h => hj₂s (by
    have := congrArg S.star h
    rwa [S.star_star j₂ hj₂] at this)
  have hsj₂sj : S.star j₂ ≠ S.star j := fun h => hj₂j (by
    have := congrArg S.star h
    rwa [S.star_star j₂ hj₂, S.star_star j hj] at this)
  have hj₂sj₂ : j₂ ≠ S.star j₂ := Ne.symm (S.star_ne j₂ hj₂)
  have hjsj : j ≠ S.star j := Ne.symm (S.star_ne j hj)
  have hjt : j ≠ t := fun h => ht (h ▸ hj)
  have hj₂t : j₂ ≠ t := fun h => ht (h ▸ hj₂)
  have hsjt : S.star j ≠ t := fun h => ht (h ▸ hjs)
  have hsj₂t : S.star j₂ ≠ t := fun h => ht (h ▸ hj₂s')
  obtain ⟨l₁, hl₁⟩ := sigEigen_sing_tail S hext hdet hstab hck hc ht hj hj₂ hj₂s'
    hj₂j hj₂s hsj₂j hsj₂sj hj₂sj₂
  obtain ⟨l₂, hl₂⟩ := sigEigen_sing_tail S hext hdet hstab hck hc ht hj₂ hj hjs
    (Ne.symm hj₂j) (Ne.symm hsj₂j) (Ne.symm hj₂s) (Ne.symm hsj₂sj) hjsj
  have hy₁ : SigEigen σ G (Pi.single j 1 + c • (Pi.single (S.star j) 1 : Fin d → K)) θ :=
    sigEigen_add_smul hσk hck (hθ j hj) (hθ (S.star j) hjs)
  have hy₂ : SigEigen σ G (Pi.single j₂ 1 + c • (Pi.single (S.star j₂) 1 : Fin d → K)) θ :=
    sigEigen_add_smul hσk hck (hθ j₂ hj₂) (hθ (S.star j₂) hj₂s')
  have h1 := sigma_mem_span_of_eigen_sum hl₁ hy₁
  have h2 := sigma_mem_span_of_eigen_sum hl₂ hy₂
  have hind : LinearIndependent K
      ![(Pi.single t 1 : Fin d → K), Pi.single j 1 + c • (Pi.single (S.star j) 1 : Fin d → K),
        Pi.single j₂ 1 + c • (Pi.single (S.star j₂) 1 : Fin d → K)] := by
    refine linearIndependent_of_evalId (f := ![t, j, j₂]) ?_
    intro a b
    fin_cases a <;> fin_cases b <;>
      simp [Pi.single_apply, hjt, hj₂t, hsjt, hsj₂t, hjsj, hj₂j, hj₂s, hsj₂j, hsj₂sj, hj₂sj₂,
        Ne.symm hjt, Ne.symm hj₂t, Ne.symm hsjt, Ne.symm hsj₂t, Ne.symm hjsj, Ne.symm hj₂j,
        Ne.symm hj₂s, Ne.symm hsj₂j, Ne.symm hsj₂sj, Ne.symm hj₂sj₂]
  have hindYU : LinearIndependent K
      ![Pi.single j 1 + c • (Pi.single (S.star j) 1 : Fin d → K), (Pi.single t 1 : Fin d → K)] := by
    refine linearIndependent_of_evalId (f := ![j, t]) ?_
    intro a b
    fin_cases a <;> fin_cases b <;>
      simp [Pi.single_apply, hjt, hsjt, hjsj, Ne.symm hjt, Ne.symm hsjt, Ne.symm hjsj]
  obtain ⟨θ', hθ'⟩ := exists_sigEigen_of_two hdet hind h1 h2
  have e : θ = θ' := SigEigen.eq_of_add hdet hindYU hy₁ hθ' hl₁
  rw [e]
  exact hθ'

theorem eigen_of_sigma_stable_hyp (S : HypCoord Q) (hext : IsExtension k Q₀ Q)
    {σ : K ≃+* K} (hσk : ∀ x, x ∈ k ↔ σ x = x) {G : Matrix (Fin d) (Fin d) K}
    (hdet : G.det ≠ 0) (hstab : SigmaStable Q k σ G) :
    ∃ a : K, a ≠ 0 ∧ ∀ r c, σ (G r c) = a * G r c := by
  obtain ⟨θ, hθ⟩ := exists_common_sigEigen_hyp S hdet hstab
  have hall : ∀ t : Fin d, SigEigen σ G (Pi.single t 1) θ := by
    intro t
    by_cases ht : t ∈ S.hyp
    · exact hθ t ht
    · exact sigEigen_tail S hext hσk hdet hstab hθ ht
  have hmul : ∀ r c : Fin d, (G *ᵥ (Pi.single c 1 : Fin d → K)) r = G r c := by
    intro r c
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hent : ∀ r c : Fin d, σ (G r c) = θ * G r c := by
    intro r c
    have h' : sigmaVec σ (G *ᵥ (Pi.single c 1 : Fin d → K)) =
        θ • (G *ᵥ (Pi.single c 1 : Fin d → K)) := hall c
    have hr := congrFun h' r
    simp only [sigmaVec, Pi.smul_apply, smul_eq_mul, hmul] at hr
    exact hr
  have hθne : θ ≠ 0 := by
    intro h0
    have hG : G = 0 := by
      ext r c
      have h2 : σ (G r c) = σ 0 := by
        rw [hent r c, h0, zero_mul, map_zero]
      simpa using σ.injective h2
    obtain ⟨j, -⟩ : S.hyp.Nonempty := Finset.card_pos.mp (by have := S.card_hyp; omega)
    haveI : Nonempty (Fin d) := ⟨j⟩
    exact hdet (by simp [hG, Matrix.det_zero])
  exact ⟨θ, hθne, hent⟩

end CFSG.LieType.SeitzGeneration.OmegaF2

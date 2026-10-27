module

public import CFSG.LieType.SeitzGeneration.OmegaF2.Spread
public import CFSG.LieType.SeitzGeneration.OmegaF2.Full
public import CFSG.LieType.SeitzGeneration.RootPairOrthGen

public section

namespace CFSG.LieType.SeitzGeneration.OmegaF2

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.LieType.SeitzGeneration.RootPairOrth
open CFSG.RankThree.Classical2 (orthDerived)

variable {K : Type} [Field K] {d : ℕ}

@[expose] def BadPlane (Q : QuadraticForm K (Fin d → K)) (k : Subfield K) (c₁ c₂ : Fin d → K) :
    Prop :=
  ∀ x y z : Fin d → K, IsRat k x → IsRat k y → IsRat k z → Q x = 0 → Q y = 0 → Q z = 0 →
    polar Q x y = 0 → polar Q x z = 0 → polar Q y z = 0 → pairDet Q c₁ c₂ x y ≠ 0 →
    pairDet Q c₁ c₂ y z / pairDet Q c₁ c₂ x y ∈ k ∧ pairDet Q c₁ c₂ z x / pairDet Q c₁ c₂ x y ∈ k

@[expose] def GoodConfig (Q : QuadraticForm K (Fin d → K)) (k : Subfield K)
    (g : Matrix (Fin d) (Fin d) K) (μ : K) : Prop :=
  ∃ x₀ y₀ : Fin d → K, IsRat k x₀ ∧ IsRat k y₀ ∧ Q x₀ = 0 ∧ Q y₀ = 0 ∧ polar Q x₀ y₀ = 0 ∧
    ¬ BadPlane Q k (g *ᵥ x₀) (μ⁻¹ • (g *ᵥ y₀))

@[expose] def GenerationFromLine (Q : QuadraticForm K (Fin d → K)) (k : Subfield K) : Prop :=
  ∀ H : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K)), H ≤ TauCeti.QuadraticMap.orthogonalGroup Q →
    (∀ u w : Fin d → K, IsRat k u → IsRat k w → Q u = 0 → polar Q u w = 0 →
      eichler Q u w ∈ H) →
    ∀ x y : Fin d → K, IsRat k x → IsRat k y → Q x = 0 → Q y = 0 → polar Q x y = 0 →
      LinearIndependent K ![x, y] → (∀ t : K, eichler Q x (t • y) ∈ H) → elementaryGroup Q ≤ H

private theorem polar_mulVec_sim_good {Q : QuadraticForm K (Fin d → K)}
    {g : Matrix (Fin d) (Fin d) K} {μ : K} (hg : ∀ v, Q (g *ᵥ v) = μ * Q v) (a b : Fin d → K) :
    polar Q (g *ᵥ a) (g *ᵥ b) = μ * polar Q a b := by
  unfold QuadraticMap.polar
  simp only [← Matrix.mulVec_add, hg]
  ring

private theorem polar_expand_right_good {Q : QuadraticForm K (Fin d → K)} (v w : Fin d → K) :
    polar Q v w = ∑ c, w c * polar Q v (Pi.single c 1 : Fin d → K) := by
  have hw : w = ∑ c, w c • (Pi.single c 1 : Fin d → K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hw]
  rw [← polarBilin_apply_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, polarBilin_apply_apply, smul_eq_mul]

theorem exists_rat_dual {k : Subfield K} {Q₀ : QuadraticForm k (Fin d → k)}
    {Q : QuadraticForm K (Fin d → K)} (hext : IsExtension k Q₀ Q)
    (hnd : (polarBilin Q).Nondegenerate) (e : Fin 3 → Fin d → K) (he : ∀ i, IsRat k (e i))
    (hind : LinearIndependent K e) :
    ∃ e' : Fin 3 → Fin d → K, (∀ j, IsRat k (e' j)) ∧
      ∀ i j, polar Q (e i) (e' j) = if i = j then 1 else 0 := by
  classical
  have hcoef : ∀ (i : Fin 3) (r : Fin d), ∃ a : k, (a : K) = polar Q (e i) (Pi.single r 1) :=
    fun i r => ⟨⟨polar Q (e i) (Pi.single r 1), polar_isRat_mem hext (he i) (isRat_single k r)⟩, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 3) (Fin d) k,
      ∀ i r, (M i r : K) = polar Q (e i) (Pi.single r 1) :=
    ⟨fun i r => (hcoef i r).choose, fun i r => (hcoef i r).choose_spec⟩
  have hcore : ∀ c : Fin 3 → k,
      (∀ r : Fin d, ∑ i, (c i : K) * polar Q (e i) (Pi.single r 1) = 0) → c = 0 := by
    intro c hc
    set w : Fin d → K := ∑ i, (c i : K) • e i with hw
    have hpolw : ∀ x : Fin d → K, polar Q w x = ∑ i, (c i : K) * polar Q (e i) x := fun x => by
      rw [hw]
      simp only [Fin.sum_univ_three, polar_add_left, polar_smul_left_eq]
    have hw0 : w = 0 := by
      apply hnd.1 w
      intro y
      rw [polarBilin_apply_apply, polar_expand_right_good]
      apply Finset.sum_eq_zero
      intro r _
      rw [hpolw, hc r, mul_zero]
    have hc0 : ∀ i, (c i : K) = 0 := by
      have h := hw0
      rw [hw] at h
      exact Fintype.linearIndependent_iff.mp hind (fun i => (c i : K)) (by simpa using h)
    funext i
    exact Subtype.ext (hc0 i)
  have hsurj : LinearMap.range M.mulVecLin = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hfr⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    obtain ⟨c, hc⟩ : ∃ c : Fin 3 → k, ∀ i, c i = f (Pi.single i 1) :=
      ⟨fun i => f (Pi.single i 1), fun i => rfl⟩
    have hfc : ∀ b : Fin 3 → k, f b = ∑ i, b i * c i := by
      intro b
      conv_lhs => rw [pi_eq_sum_univ' b]
      rw [map_sum]
      simp [map_smul, smul_eq_mul, hc]
    have hrel : ∀ r : Fin d, ∑ i, (c i : K) * polar Q (e i) (Pi.single r 1) = 0 := by
      intro r
      have h0 : f (M.mulVecLin (Pi.single r 1)) = 0 := hfr (LinearMap.mem_range_self _ _)
      rw [hfc, Matrix.mulVecLin_apply] at h0
      have h1 : ∀ i, (M *ᵥ (Pi.single r 1 : Fin d → k)) i = M i r := fun i => by
        simp [Matrix.mulVec_single]
      simp only [h1] at h0
      have h4 : ((∑ i, M i r * c i : k) : K) = 0 := by
        rw [h0]
        rfl
      push_cast at h4
      simpa only [hM, mul_comm] using h4
    have hc0 := hcore c hrel
    apply hf0
    apply LinearMap.ext
    intro b
    simp [hfc b, hc0]
  obtain ⟨g, hg⟩ := M.mulVecLin.exists_rightInverse_of_surjective hsurj
  have hMg : ∀ b : Fin 3 → k, M *ᵥ g b = b := fun b => by
    have := congrArg (fun L : (Fin 3 → k) →ₗ[k] (Fin 3 → k) => L b) hg
    simpa [Matrix.mulVecLin_apply] using this
  have hexp : ∀ (i : Fin 3) (v : Fin d → k),
      polar Q (e i) (fun r => ((v r : k) : K)) = (((M *ᵥ v) i : k) : K) := by
    intro i v
    have hcoe_sum : ((∑ j, M i j * v j : k) : K) = ∑ j, ((M i j * v j : k) : K) :=
      map_sum k.subtype (fun j => M i j * v j) Finset.univ
    rw [polar_expand_right_good]
    show _ = ((∑ j, M i j * v j : k) : K)
    rw [hcoe_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Subfield.coe_mul, hM]
    ring
  refine ⟨fun j r => ((g (Pi.single j 1) r : k) : K), fun j r => (g (Pi.single j 1) r).2,
    fun i j => ?_⟩
  rw [hexp i, hMg, Pi.single_apply]
  split_ifs <;> simp

theorem coeffs_mem_of_isRat {k : Subfield K} {x y z : Fin d → K} (hx : IsRat k x) (hy : IsRat k y)
    (hz : IsRat k z) (hind : LinearIndependent K ![x, y]) {a b : K} (h : z = a • x + b • y) :
    a ∈ k ∧ b ∈ k := by
  obtain ⟨i, j, hD⟩ := exists_minor_ne_zero (u := x) (w := y)
    (fun s t hst => LinearIndependent.pair_iff.mp hind s t hst)
  have hzi : z i = a * x i + b * y i := by rw [h]; simp
  have hzj : z j = a * x j + b * y j := by rw [h]; simp
  have ha : a * (x i * y j - x j * y i) = z i * y j - z j * y i := by
    rw [hzi, hzj]; ring
  have hb : b * (x i * y j - x j * y i) = x i * z j - x j * z i := by
    rw [hzi, hzj]; ring
  have ha' := eq_div_of_mul_eq hD ha
  have hb' := eq_div_of_mul_eq hD hb
  constructor
  · rw [ha']
    exact div_mem (sub_mem (mul_mem (hz i) (hy j)) (mul_mem (hz j) (hy i)))
      (sub_mem (mul_mem (hx i) (hy j)) (mul_mem (hx j) (hy i)))
  · rw [hb']
    exact div_mem (sub_mem (mul_mem (hx i) (hz j)) (mul_mem (hx j) (hz i)))
      (sub_mem (mul_mem (hx i) (hy j)) (mul_mem (hx j) (hy i)))

theorem linearIndependent_of_not_bad {k : Subfield K} {Q : QuadraticForm K (Fin d → K)}
    {x y z c₁ c₂ : Fin d → K} (hx : IsRat k x) (hy : IsRat k y) (hz : IsRat k z)
    (hΔ : pairDet Q c₁ c₂ x y ≠ 0)
    (hαβ : ¬ (pairDet Q c₁ c₂ y z / pairDet Q c₁ c₂ x y ∈ k ∧
      pairDet Q c₁ c₂ z x / pairDet Q c₁ c₂ x y ∈ k)) :
    LinearIndependent K ![x, y, z] := by
  have hxy : LinearIndependent K ![x, y] := (linearIndependent_of_pairDet_ne hΔ).1
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hsum : g 0 • x + g 1 • y + g 2 • z = 0 := by
    simpa [Fin.sum_univ_three] using hg
  by_cases h2 : g 2 = 0
  · have h01 : g 0 • x + g 1 • y = 0 := by
      rw [h2, zero_smul, add_zero] at hsum
      exact hsum
    obtain ⟨h0, h1⟩ := LinearIndependent.pair_iff.mp hxy (g 0) (g 1) h01
    intro i
    fin_cases i <;> simp [h0, h1, h2]
  · exfalso
    have hsz : g 2 • z = -(g 0 • x + g 1 • y) := by
      rw [← add_eq_zero_iff_eq_neg, add_comm (g 2 • z)]
      exact hsum
    obtain ⟨a, b, hz'⟩ : ∃ a b : K, z = a • x + b • y := by
      refine ⟨-(g 0 / g 2), -(g 1 / g 2), ?_⟩
      have h5 : z = (g 2)⁻¹ • (g 2 • z) := by
        rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
      rw [h5, hsz]
      module
    obtain ⟨ha, _⟩ := coeffs_mem_of_isRat hx hy hz hxy hz'
    have e1 : pairDet Q c₁ c₂ y z = -a * pairDet Q c₁ c₂ x y := by
      rw [hz']
      unfold pairDet
      simp only [polar_add_left, polar_smul_left_eq]
      ring
    have e2 : pairDet Q c₁ c₂ z x = -b * pairDet Q c₁ c₂ x y := by
      rw [hz']
      unfold pairDet
      simp only [polar_add_left, polar_smul_left_eq]
      ring
    have hb : b ∈ k := (coeffs_mem_of_isRat hx hy hz hxy hz').2
    apply hαβ
    have hα : pairDet Q c₁ c₂ y z / pairDet Q c₁ c₂ x y = -a := by
      rw [e1, mul_div_assoc, div_self hΔ, mul_one]
    have hβ : pairDet Q c₁ c₂ z x / pairDet Q c₁ c₂ x y = -b := by
      rw [e2, mul_div_assoc, div_self hΔ, mul_one]
    rw [hα, hβ]
    exact ⟨neg_mem ha, neg_mem hb⟩

theorem similarity_plane_ts {Q : QuadraticForm K (Fin d → K)} {g : Matrix (Fin d) (Fin d) K}
    {μ : K} (hμ : μ ≠ 0) (hg : ∀ v, Q (g *ᵥ v) = μ * Q v) {x₀ y₀ : Fin d → K} (hx₀ : Q x₀ = 0)
    (hy₀ : Q y₀ = 0) (hxy₀ : polar Q x₀ y₀ = 0) :
    Q (g *ᵥ x₀) = 0 ∧ Q (μ⁻¹ • (g *ᵥ y₀)) = 0 ∧
      polar Q (g *ᵥ x₀) (μ⁻¹ • (g *ᵥ y₀)) = 0 := by
  have h1 : Q (g *ᵥ x₀) = 0 := by rw [hg, hx₀, mul_zero]
  have hgy : Q (g *ᵥ y₀) = 0 := by rw [hg, hy₀, mul_zero]
  have h2 : Q (μ⁻¹ • (g *ᵥ y₀)) = 0 := by rw [map_smul_eq_sq, hgy, mul_zero]
  have h3 : polar Q (g *ᵥ x₀) (μ⁻¹ • (g *ᵥ y₀)) = 0 := by
    simp [polar_smul_right_eq, polar_mulVec_sim_good hg, hxy₀]
  exact ⟨h1, h2, h3⟩

theorem conj_plane_mem_lift [Finite K] {k : Subfield K}
    {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)} {σ : K ≃+* K}
    (hext : IsExtension k Q₀ Q) (hσk : ∀ x, x ∈ k ↔ σ x = x)
    (hder : elementaryGroup Q = orthDerived Q) {H : Subgroup (matrixProjectiveDerived Q)}
    (hN : subfieldFixedGroup k Q₀ Q ≤ H) (gp : similarityPairs Q) (hgp : gp.val.right = 1)
    (hN' : (subfieldFixedGroup k Q₀ Q).map (matrixProjectiveConjugationHom Q gp).toMonoidHom ≤ H)
    {x₀ y₀ : Fin d → K} (hx₀r : IsRat k x₀) (hy₀r : IsRat k y₀) (hx₀ : Q x₀ = 0)
    (hy₀ : Q y₀ = 0) (hxy₀ : polar Q x₀ y₀ = 0) :
    eichler Q (gp.val.left.val *ᵥ x₀) ((multiplier Q gp : K)⁻¹ • (gp.val.left.val *ᵥ y₀)) ∈
      liftSubgroup Q H := by
  have hμ : (multiplier Q gp : K) ≠ 0 := Units.ne_zero _
  have hg : ∀ v, Q (gp.val.left.val *ᵥ v) = (multiplier Q gp : K) * Q v := fun v => by
    have h := multiplier_spec Q gp v
    rw [coordinateSemilinearMap_apply, hgp] at h
    exact h
  have hconj := conj_eichler_mem_lift_gen hext hσk hder gp hgp hN' hx₀r hy₀r hx₀ hxy₀
  rw [eichler_conj_similarity (g := matrixLinearIso gp.val.left) hμ hg] at hconj
  exact hconj

theorem tsFrame_of_triple {Q : QuadraticForm K (Fin d → K)} {x y z : Fin d → K} (hx : Q x = 0)
    (hy : Q y = 0) (hz : Q z = 0) (hxy : polar Q x y = 0) (hxz : polar Q x z = 0)
    (hyz : polar Q y z = 0) : TSFrame Q ![x, y, z] := by
  have hxx := polar_self_eq_zero hx
  have hyy := polar_self_eq_zero hy
  have hzz := polar_self_eq_zero hz
  have hyx : polar Q y x = 0 := by rw [polar_comm]; exact hxy
  have hzx : polar Q z x = 0 := by rw [polar_comm]; exact hxz
  have hzy : polar Q z y = 0 := by rw [polar_comm]; exact hyz
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · fin_cases i <;> simp [hx, hy, hz]
  · fin_cases i <;> fin_cases j <;> simp [hxx, hyy, hzz, hxy, hxz, hyz, hyx, hzx, hzy]

theorem elementaryGroup_le_lift_of_good_F2 [Finite K] [CharP K 2]
    {k : Subfield K} {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)}
    {σ : K ≃+* K} (hk : Nat.card k = 2) (hext : IsExtension k Q₀ Q)
    (hσk : ∀ x, x ∈ k ↔ σ x = x) (hder : elementaryGroup Q = orthDerived Q)
    (hnd : (polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = Nat.card k ^ p) (hGen : GenerationFromLine Q k)
    {H : Subgroup (matrixProjectiveDerived Q)} (hN : subfieldFixedGroup k Q₀ Q ≤ H)
    (gp : similarityPairs Q) (hgp : gp.val.right = 1)
    (hN' : (subfieldFixedGroup k Q₀ Q).map (matrixProjectiveConjugationHom Q gp).toMonoidHom ≤ H)
    (hgood : GoodConfig Q k gp.val.left.val (multiplier Q gp : K)) :
    elementaryGroup Q ≤ liftSubgroup Q H := by
  classical
  obtain ⟨x₀, y₀, hx₀r, hy₀r, hx₀, hy₀, hxy₀, hnot⟩ := hgood
  unfold BadPlane at hnot
  simp only [not_forall, not_imp] at hnot
  obtain ⟨x, y, z, hxr, hyr, hzr, hx, hy, hz, hxy, hxz, hyz, hΔ, hαβ⟩ := hnot
  set gm : GL (Fin d) K := gp.val.left with hgm
  set μ : K := (multiplier Q gp : K) with hμdef
  have hμ : μ ≠ 0 := Units.ne_zero _
  have hg : ∀ v, Q (gm.val *ᵥ v) = μ * Q v := fun v => by
    have h := multiplier_spec Q gp v
    rw [coordinateSemilinearMap_apply, hgp] at h
    exact h
  obtain ⟨hc₁, hc₂, hc₁₂⟩ := similarity_plane_ts hμ hg hx₀ hy₀ hxy₀
  have hHc := conj_plane_mem_lift hext hσk hder hN gp hgp hN' hx₀r hy₀r hx₀ hy₀ hxy₀
  have hH := liftSubgroup_le_orthogonalGroup H
  have hrat : ∀ u w : Fin d → K, IsRat k u → IsRat k w → Q u = 0 → polar Q u w = 0 →
      eichler Q u w ∈ liftSubgroup Q H := fun u w hu hw hQu hp' =>
    eichler_mem_lift_gen hext hσk hder hN hu hw hQu hp'
  obtain ⟨a₁, a₂, hne, hline⟩ := exists_full_line hk hp hp2 hK (H := liftSubgroup Q H) hx hy hz
    hxy hxz hyz hc₁ hc₂ hc₁₂ hΔ hαβ (hrat x y hxr hyr hx hxy) (hrat x z hxr hzr hx hxz)
    (hrat y z hyr hzr hy hyz) hHc
  have hind3 : LinearIndependent K ![x, y, z] :=
    linearIndependent_of_not_bad hxr hyr hzr hΔ hαβ
  have hrat3 : ∀ i, IsRat k (![x, y, z] i) := fun i => by fin_cases i <;> simpa
  obtain ⟨e', he'r, hdual⟩ := exists_rat_dual hext hnd ![x, y, z] hrat3 hind3
  have hframe : TSFrame Q ![x, y, z] := tsFrame_of_triple hx hy hz hxy hxz hyz
  have hT : ∀ i j : Fin 3, i ≠ j → eichler Q (![x, y, z] i) (e' j) ∈ liftSubgroup Q H :=
    fun i j hij => hrat _ _ (hrat3 i) (he'r j) (hframe.Q_e i) (by rw [hdual]; simp [hij])
  set α := pairDet Q (gm.val *ᵥ x₀) (μ⁻¹ • (gm.val *ᵥ y₀)) y z /
    pairDet Q (gm.val *ᵥ x₀) (μ⁻¹ • (gm.val *ᵥ y₀)) x y with hα
  set β := pairDet Q (gm.val *ᵥ x₀) (μ⁻¹ • (gm.val *ᵥ y₀)) z x /
    pairDet Q (gm.val *ᵥ x₀) (μ⁻¹ • (gm.val *ᵥ y₀)) x y with hβ
  have e1 : frameVec ![x, y, z] ![α, β, 1] = z + α • x + β • y := by
    simp only [frameVec, Fin.sum_univ_three]
    simp
    abel
  have e2 : frameVec ![x, y, z] ![a₁, a₂, 0] = a₁ • x + a₂ • y := by
    simp [frameVec, Fin.sum_univ_three]
  have hnz : cross3 ![α, β, 1] ![a₁, a₂, 0] ≠ 0 := by
    intro h0
    have h1 := congrFun h0 0
    have h2 := congrFun h0 1
    simp [cross3] at h1 h2
    rcases hne with h | h
    · exact h h2
    · exact h h1
  have hspread := full_line_of_spread (H := liftSubgroup Q H) hframe hdual hT ![α, β, 1]
    ![a₁, a₂, 0] hnz (fun t => by rw [e1, e2]; exact hline t)
  exact hGen _ hH hrat x y hxr hyr hx hy hxy (linearIndependent_of_pairDet_ne hΔ).1
    (by simpa using hspread 0 1 (by decide))

end CFSG.LieType.SeitzGeneration.OmegaF2

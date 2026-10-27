module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.ModelParabTorus
public import CFSG.ClassicalInvolution.Phan.PhanDn.FrameAdjacency

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.BorelTits
open CFSG.LieType.Steinberg

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]
variable (E : QuadExt F K (unitaryInvolution K 2 1))

theorem bcLin_firstHalf_eq_of_mem_stdLag {n : ℕ}
    (g : (Fin n → K) →ₗ[F] (Fin n → K)) (x : Fin n → K)
    (hx : bcLin E n g (Sum.elim x 0) ∈ stdLag n K) :
    bcLin E n g (Sum.elim x 0) = Sum.elim (g x) 0 := by
  have hdec : jEmb E n x = (Sum.elim x 0 : Fin n ⊕ Fin n → K) +
      dFlip (unitaryInvolution K 2 1) (Sum.elim x 0) := by
    ext (i | i) <;> simp [jEmb, dFlip]
  have hzero := mem_stdLag.mp hx
  ext (i | i)
  · change bcLin E n g (Sum.elim x 0) (Sum.inl i) = g x i
    have h := congrFun (bcLin_jEmb E n g x) (Sum.inl i)
    rw [hdec, map_add, bcLin_dFlip] at h
    simpa only [Pi.add_apply, dFlip_apply_inl, hzero, map_zero, add_zero, jEmb_apply_inl]
      using h
  · exact hzero i

theorem isKLinear_at_of_bcLin_mem_stdLag {n : ℕ}
    (g : (Fin n → K) →ₗ[F] (Fin n → K)) (x : Fin n → K)
    (hx : bcLin E n g (Sum.elim x 0) ∈ stdLag n K) (a : K) :
    g (a • x) = a • g x := by
  have hhalf : (Sum.elim (a • x) 0 : Fin n ⊕ Fin n → K) =
      a • (Sum.elim x 0 : Fin n ⊕ Fin n → K) := by
    ext (i | i) <;> simp
  have hax : bcLin E n g (Sum.elim (a • x) 0) ∈ stdLag n K := by
    rw [hhalf, map_smul]
    exact Submodule.smul_mem _ a hx
  have h1 := bcLin_firstHalf_eq_of_mem_stdLag E g x hx
  have h2 := bcLin_firstHalf_eq_of_mem_stdLag E g (a • x) hax
  rw [hhalf, map_smul, h1] at h2
  funext i
  exact (congrFun h2 (Sum.inl i)).symm

theorem qTwoParab_fixes_prefix_lines (m : ℕ) (hm : 3 ≤ m) (r : ℕ) (hr : r < m)
    {C : Set (Fin (m + 1))} (hC : ∀ i ∈ C, r ≤ i.val)
    {x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    (hx : x ∈ qTwoParab E m C) {i : Fin (m + 1)} (hi : i.val < r) :
    (x • stdDChamber (unitaryInvolution K 2 1) (m + 1)).line i =
      (stdDChamber (unitaryInvolution K 2 1) (m + 1)).line i := by
  let c := x • stdDChamber (unitaryInvolution K 2 1) (m + 1)
  let d := stdDChamber (unitaryInvolution K 2 1) (m + 1)
  have hsub (k : ℕ) (hk : k ≤ r) : c.sub k = d.sub k := by
    by_cases hk0 : k = 0
    · simp [hk0, FlipFrame.sub_zero]
    have hkm : k - 1 < m + 1 := by omega
    let j : Fin (m + 1) := ⟨k - 1, hkm⟩
    have hj : j ∉ C := by
      intro hj
      have := hC j hj
      dsimp [j] at this
      omega
    have hfix := (mem_qTwoParab E).mp hx j hj
    have hval := congrArg Subtype.val hfix
    rw [coe_smul_flagVert, coe_flagChamber] at hval
    have helt : c.elt j = d.elt j := by
      change (x • d).elt j = d.elt j
      rw [elt_smul]
      exact hval
    have hjm : j.val + 1 < m := by dsimp [j]; omega
    rw [FlipFrame.elt_of_add_one_lt c.toFlipFrame j hjm,
      FlipFrame.elt_of_add_one_lt d.toFlipFrame j hjm] at helt
    simpa [j, show k - 1 + 1 = k by omega] using helt
  change c.line i = d.line i
  rw [FlipFrame.line_eq_flipOrth_sub_inf E.isUnitary.invol c.toFlipFrame i.isLt,
    FlipFrame.line_eq_flipOrth_sub_inf E.isUnitary.invol d.toFlipFrame i.isLt,
    hsub i.val (by omega), hsub (i.val + 1) (by omega)]

theorem qTwo_fixed_line_scalar {m : ℕ}
    {x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    (i : Fin (m + 1))
    (hi : (x • stdDChamber (unitaryInvolution K 2 1) (m + 1)).line i =
      (stdDChamber (unitaryInvolution K 2 1) (m + 1)).line i) :
    ∃ u : normOne (unitaryInvolution K 2 1), ∀ a : K,
      (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) (Pi.single i a) =
        Pi.single i (((u : Kˣ) : K) * a) := by
  classical
  rw [smul_line, stdDChamber_line] at hi
  let g : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K) := x
  have hb : bcLin E (m + 1) g (stdE i) ∈ (K ∙ stdE (K := K) i) := by
    rw [← hi]
    exact Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self _)
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp hb
  have he : (Sum.elim (Pi.single i (1 : K)) 0 : Fin (m + 1) ⊕ Fin (m + 1) → K) =
      stdE i := by
    ext (j | j) <;> simp [stdE_inl, stdE_inr, Pi.single_apply]
  have hbLag : bcLin E (m + 1) g (Sum.elim (Pi.single i 1) 0) ∈ stdLag (m + 1) K := by
    rw [he, ← hu]
    apply Submodule.smul_mem
    rw [mem_stdLag]
    intro j
    simp [stdE_inr]
  have hscalar : g (Pi.single i 1) = Pi.single i u := by
    have hfirst := bcLin_firstHalf_eq_of_mem_stdLag E g (Pi.single i 1) hbLag
    rw [he, ← hu] at hfirst
    ext j
    have h := congrFun hfirst (Sum.inl j)
    simpa [Pi.smul_apply, stdE_inl, Pi.single_apply] using h.symm
  have hxO := (mem_rulingGroup E (m + 1) _).mp
    (orthDerived_le_rulingGroup E (m + 1) x.2)
  have hnorm : normQuad E u = 1 := by
    have h := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hxO.1 (Pi.single i 1)
    change Qn E (m + 1) (g (Pi.single i 1)) = Qn E (m + 1) (Pi.single i 1) at h
    rw [hscalar, Qn_single_one] at h
    simpa [Qn_apply, Pi.single_apply, apply_ite] using h
  have huN : u * unitaryInvolution K 2 1 u = 1 := by
    simpa only [algebraMap_normQuad, map_one] using congrArg (algebraMap F K) hnorm
  let un : normOne (unitaryInvolution K 2 1) :=
    ⟨Units.mk0 u (left_ne_zero_of_mul_eq_one huN),
      (mem_normOne _).mpr (by simpa [mul_comm] using huN)⟩
  refine ⟨un, fun a => ?_⟩
  have h := isKLinear_at_of_bcLin_mem_stdLag E g (Pi.single i 1) hbLag a
  have hs : a • (Pi.single i (1 : K) : Fin (m + 1) → K) = Pi.single i a := by
    ext j
    by_cases hji : j = i <;> simp [Pi.single_apply, hji]
  rw [hs, hscalar] at h
  change g (Pi.single i a) = Pi.single i (u * a)
  rw [h]
  ext j
  by_cases hji : j = i <;> simp [Pi.single_apply, hji, mul_comm]

theorem qTwoParab_remove_prefix (hK : Nat.card K = 4) (m : ℕ) (hm : 3 ≤ m)
    (r : ℕ) (hr : r < m) {C : Set (Fin (m + 1))} (hC : ∀ i ∈ C, r ≤ i.val)
    {x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    (hx : x ∈ qTwoParab E m C) :
    ∃ t ∈ ⨆ i, qTwoTor E m hm i, ∀ (i : Fin (m + 1)), i.val < r → ∀ a : K,
      ((t⁻¹ * x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
        (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) (Pi.single i a) = Pi.single i a := by
  classical
  have hsc (i : Fin (m + 1)) (hi : i.val < r) :
      ∃ u : normOne (unitaryInvolution K 2 1), ∀ a : K,
        (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) (Pi.single i a) =
          Pi.single i (((u : Kˣ) : K) * a) :=
    qTwo_fixed_line_scalar E i (qTwoParab_fixes_prefix_lines E m hm r hr hC hx hi)
  let u (i : Fin (m + 1)) : normOne (unitaryInvolution K 2 1) :=
    if hi : i.val < r then Classical.choose (hsc i hi) else 1
  let d := diagHom F (unitaryInvolution K 2 1) (m + 1) u
  have hd : d ∈ (⨆ i, qTwoTor E m hm i).map
      (Subgroup.subtype (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) := by
    rw [map_qTwoTor_iSup_eq_diagTorus E hK m hm]
    exact ⟨u, rfl⟩
  obtain ⟨t, ht, htd⟩ := Subgroup.mem_map.mp hd
  change (t : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) = d at htd
  refine ⟨t, ht, fun i hi a => ?_⟩
  have hxi := Classical.choose_spec (hsc i hi) a
  have hti : (t : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) (Pi.single i a) =
      (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) (Pi.single i a) := by
    rw [htd, hxi]
    ext j
    by_cases hji : j = i
    · subst j
      simp [d, diagHom_apply, u, hi]
    · simp [d, diagHom_apply, Pi.single_apply, hji]
  change (t : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)).symm
    ((x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) (Pi.single i a)) = Pi.single i a
  rw [← hti, LinearEquiv.symm_apply_apply]

end CFSG.ClassicalInvolution.PhanDn.QTwo

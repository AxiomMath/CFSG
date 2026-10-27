module

public import CFSG.ClassicalInvolution.RouteD.TWEB4Class

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE.B3

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TWE.B6
  CFSG.ClassicalInvolution.RouteD.TWE.B4
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Complex

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem polar_self_complex (h2 : (2 : K) ≠ 0) {J : V ≃ₗ[K] V}
    (hJ : J ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {x : V} (hx : J (J x) = -x) :
    polar Q x (J x) = 0 := by
  have h := polar_map_of_mem hJ x (J x)
  rw [hx, polar_neg_right, polar_comm Q (J x) x] at h
  have h' : (2 : K) * polar Q x (J x) = 0 := by linear_combination -h
  exact (mul_eq_zero.mp h').resolve_left h2

theorem linearIndependent_complex (h2 : (2 : K) ≠ 0) (hnsq : ∀ c : K, c * c ≠ -1)
    {J : V ≃ₗ[K] V} (hJ : J ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {e f : V}
    (hee : Q e = 0) (hff : Q f = 0) (hef : polar Q e f = 1) (hJe : J (J e) = -e)
    (hJf : J (J f) = -f) : LinearIndependent K ![e, J e, f, J f] := by
  have hQJe : Q (J e) = 0 := by rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hJ e, hee]
  have hQJf : Q (J f) = 0 := by rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hJ f, hff]
  set a : K := polar Q e (J f) with ha
  have p_ee : polar Q e e = 0 := polar_self_eq_zero hee
  have p_eJe : polar Q e (J e) = 0 := polar_self_complex h2 hJ hJe
  have p_Jee : polar Q (J e) e = 0 := by rw [polar_comm]; exact p_eJe
  have p_JeJe : polar Q (J e) (J e) = 0 := polar_self_eq_zero hQJe
  have p_Jef : polar Q (J e) f = -a := by
    have h := polar_map_of_mem hJ (J e) f
    rw [hJe, polar_neg_left] at h
    exact h.symm
  have p_JeJf : polar Q (J e) (J f) = 1 := by
    rw [polar_map_of_mem hJ e f, hef]
  have p_fe : polar Q f e = 1 := by rw [polar_comm]; exact hef
  have p_fJe : polar Q f (J e) = -a := by rw [polar_comm]; exact p_Jef
  have p_ff : polar Q f f = 0 := polar_self_eq_zero hff
  have p_fJf : polar Q f (J f) = 0 := polar_self_complex h2 hJ hJf
  have p_Jfe : polar Q (J f) e = a := by rw [polar_comm]
  have p_JfJe : polar Q (J f) (J e) = 1 := by rw [polar_comm]; exact p_JeJf
  have p_Jff : polar Q (J f) f = 0 := by rw [polar_comm]; exact p_fJf
  have p_JfJf : polar Q (J f) (J f) = 0 := polar_self_eq_zero hQJf
  have hna : a * a + 1 ≠ 0 := fun h => hnsq a (by linear_combination h)
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hg' : g 0 • e + g 1 • J e + g 2 • f + g 3 • J f = 0 := by
    simpa [Fin.sum_univ_four] using hg
  have key : ∀ v : V, g 0 * polar Q v e + g 1 * polar Q v (J e) + g 2 * polar Q v f +
      g 3 * polar Q v (J f) = 0 := by
    intro v
    have := congrArg (fun w => polar Q v w) hg'
    simpa only [polar_add_right, polar_smul_right_eq, polar_zero_right] using this
  have E1 := key e
  have E2 := key (J e)
  have E3 := key f
  have E4 := key (J f)
  rw [p_ee, p_eJe, hef, ← ha] at E1
  rw [p_Jee, p_JeJe, p_Jef, p_JeJf] at E2
  rw [p_fe, p_fJe, p_ff, p_fJf] at E3
  rw [p_Jfe, p_JfJe, p_Jff, p_JfJf] at E4
  have h3 : g 3 = 0 := by
    have : (a * a + 1) * g 3 = 0 := by linear_combination E2 + a * E1
    exact (mul_eq_zero.mp this).resolve_left hna
  have h2' : g 2 = 0 := by linear_combination E1 - a * h3
  have h1 : g 1 = 0 := by
    have : (a * a + 1) * g 1 = 0 := by linear_combination E4 - a * E3
    exact (mul_eq_zero.mp this).resolve_left hna
  have h0 : g 0 = 0 := by linear_combination E3 + a * h1
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2'
  · exact h3

theorem span_eq_of_complex (h2 : (2 : K) ≠ 0) (hnsq : ∀ c : K, c * c ≠ -1)
    {J : V ≃ₗ[K] V} (hJ : J ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {e f : V}
    (hee : Q e = 0) (hff : Q f = 0) (hef : polar Q e f = 1) (hJe : J (J e) = -e)
    (hJf : J (J f) = -f) {WJ : Submodule K V} (hWJ : Module.finrank K WJ = 4) (he : e ∈ WJ)
    (hf : f ∈ WJ) (hJW : ∀ x ∈ WJ, J x ∈ WJ) :
    Submodule.span K (Set.range ![e, J e, f, J f]) = WJ := by
  have hli := linearIndependent_complex h2 hnsq hJ hee hff hef hJe hJf
  have hle : Submodule.span K (Set.range ![e, J e, f, J f]) ≤ WJ := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact he
    · exact hJW e he
    · exact hf
    · exact hJW f hf
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [finrank_span_eq_card hli, Fintype.card_fin, hWJ]

end Complex

section Eigen

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem negSpace_eq_plane_b3 (h2 : (2 : K) ≠ 0) (hd : Module.finrank K V = 7) {g : V ≃ₗ[K] V}
    (hg2 : g * g = 1) {WJ : Submodule K V} (hWJ : Module.finrank K WJ = 4)
    (hgJ : ∀ x ∈ WJ, g x = x) (π ρ : HypPair Q) (hgπ : ∀ x ∈ hypPlane π, g x = -x)
    (hgρ : ∀ x ∈ hypPlane ρ, g x = x) (hρ : ¬ hypPlane ρ ≤ WJ) :
    negSpace g = hypPlane π := by
  have hcompl := isCompl_pos_neg h2 hg2
  have hsum : Module.finrank K (posSpace g) + Module.finrank K (negSpace g) = 7 := by
    rw [← hd]
    exact Submodule.finrank_add_eq_of_isCompl hcompl
  have hπle : hypPlane π ≤ negSpace g := fun x hx => mem_negSpace_iff'.mpr (hgπ x hx)
  have hρle : hypPlane ρ ≤ posSpace g := fun x hx => mem_posSpace_iff'.mpr (hgρ x hx)
  have hJle : WJ ≤ posSpace g := fun x hx => mem_posSpace_iff'.mpr (hgJ x hx)
  have hinf : Module.finrank K ↥(WJ ⊓ hypPlane ρ) < 2 := by
    have hlt : WJ ⊓ hypPlane ρ < hypPlane ρ :=
      lt_of_le_of_ne inf_le_right fun h => hρ (h ▸ inf_le_left)
    have := Submodule.finrank_lt_finrank_of_lt hlt
    rwa [finrank_hypPlane] at this
  have hsupfin := Submodule.finrank_sup_add_finrank_inf_eq WJ (hypPlane ρ)
  rw [hWJ, finrank_hypPlane] at hsupfin
  have hpos5 : 5 ≤ Module.finrank K (posSpace g) := by
    have := Submodule.finrank_mono (sup_le hJle hρle)
    omega
  have hneg2 : 2 ≤ Module.finrank K (negSpace g) := by
    have := Submodule.finrank_mono hπle
    rwa [finrank_hypPlane] at this
  exact (Submodule.eq_of_le_of_finrank_eq hπle (by rw [finrank_hypPlane]; omega)).symm

end Eigen

section Class

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem class_b3_model (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hnsq : ∀ c : K, c * c ≠ -1) {p : ℕ} [Fact p.Prime] [CharP K p]
    (hd : Module.finrank K V = 7) {g u J₁ : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg2 : g * g = 1)
    (hJ₁O : J₁ ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (FJ FN : OFrame Q)
    (hgJ : ∀ x ∈ FJ.span, g x = x) (hJ₁J : ∀ x ∈ FJ.span, J₁ x ∈ FJ.span)
    (hJ₁2 : ∀ x ∈ FJ.span, J₁ (J₁ x) = -x) (huJ₁ : ∀ x, u (J₁ x) = J₁ (u x))
    (hu_ne : ∃ x ∈ FJ.span, u x ≠ x) (huN : ∀ x ∈ FN.span, u x = x)
    (hgN : ∀ x ∈ FN.span, g x ∈ FN.span) {A : SL(2, K)} (hA1 : A ≠ 1) (hAp : A ^ p = 1)
    (hinv : ∀ v, g (FN.La A v) = (FN.La A).symm (g v)) :
    ∃ π ρ : HypPair Q, π.Orth ρ ∧ hypPlane π ⊔ hypPlane ρ = FN.span ∧
      negSpace g = hypPlane π ∧ (∀ y ∈ π.perp, g y = y) := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨π, ρ, horth, hsup, hπ, hρ⟩ := eigen_planes_of_inverted hodd hQ hgO hg2 FN hgN hA1 hAp
    hinv
  have hneg : negSpace g = hypPlane π := by
    refine negSpace_eq_plane_b3 h2 hd hg2 FJ.finrank_span hgJ π ρ hπ hρ ?_
    intro hρJ
    have hρN : hypPlane ρ ≤ FN.span := hsup ▸ le_sup_right
    have he : ρ.e ∈ FJ.span := hρJ (e_mem_hypPlane ρ)
    have hf : ρ.f ∈ FJ.span := hρJ (f_mem_hypPlane ρ)
    have hspan := span_eq_of_complex h2 hnsq hJ₁O ρ.Q_e ρ.Q_f ρ.polar_ef (hJ₁2 _ he) (hJ₁2 _ hf)
      FJ.finrank_span he hf hJ₁J
    have hue : u ρ.e = ρ.e := huN _ (hρN (e_mem_hypPlane ρ))
    have huf : u ρ.f = ρ.f := huN _ (hρN (f_mem_hypPlane ρ))
    have hle : FJ.span ≤ LinearMap.ker ((u : V →ₗ[K] V) - LinearMap.id) := by
      rw [← hspan, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · simpa [sub_eq_zero] using hue
      · simp [huJ₁, hue]
      · simpa [sub_eq_zero] using huf
      · simp [huJ₁, huf]
    obtain ⟨x, hx, hux⟩ := hu_ne
    have := hle hx
    simp [sub_eq_zero] at this
    exact hux this
  exact ⟨π, ρ, horth, hsup, hneg, fun y hy => eq_self_of_perp_plane h2 hgO hg2 π hneg hy⟩

theorem class_b3_model_sign (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hnsq : ∀ c : K, c * c ≠ -1) {p : ℕ} [Fact p.Prime] [CharP K p]
    (hd : Module.finrank K V = 7) {g u J₁ : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg2 : g * g = 1)
    (hJ₁O : J₁ ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (FJ FN : OFrame Q) {ε : K}
    (hε : ε = 1 ∨ ε = -1) (hgJ : ∀ x ∈ FJ.span, g x = ε • x)
    (hJ₁J : ∀ x ∈ FJ.span, J₁ x ∈ FJ.span) (hJ₁2 : ∀ x ∈ FJ.span, J₁ (J₁ x) = -x)
    (huJ₁ : ∀ x, u (J₁ x) = J₁ (u x)) (hu_ne : ∃ x ∈ FJ.span, u x ≠ x)
    (huN : ∀ x ∈ FN.span, u x = x) (hgN : ∀ x ∈ FN.span, g x ∈ FN.span) {A : SL(2, K)}
    (hA1 : A ≠ 1) (hAp : A ^ p = 1) (hinv : ∀ v, g (FN.La A v) = (FN.La A).symm (g v)) :
    ∃ π ρ : HypPair Q, π.Orth ρ ∧ hypPlane π ⊔ hypPlane ρ = FN.span ∧
      ∀ y ∈ π.perp, g y = ε • y := by
  rcases hε with rfl | rfl
  · obtain ⟨π, ρ, horth, hsup, -, hperp⟩ := class_b3_model hodd hQ hnsq hd hgO hg2 hJ₁O FJ FN
      (fun x hx => by simpa using hgJ x hx) hJ₁J hJ₁2 huJ₁ hu_ne huN hgN hA1 hAp hinv
    exact ⟨π, ρ, horth, hsup, fun y hy => by rw [hperp y hy, one_smul]⟩
  · set g₁ : V ≃ₗ[K] V := g.trans (LinearEquiv.neg K) with hg₁
    have hg₁apply : ∀ v, g₁ v = -g v := fun v => rfl
    have hg₁O : g₁ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by
        rw [hg₁apply, QuadraticMap.map_neg]
        exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hgO v
    have hg₁2 : g₁ * g₁ = 1 := by
      refine LinearEquiv.ext fun v => ?_
      have := LinearEquiv.congr_fun hg2 v
      simp only [LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq] at this ⊢
      rw [hg₁apply, hg₁apply, map_neg, neg_neg]
      exact this
    obtain ⟨π, ρ, horth, hsup, -, hperp⟩ := class_b3_model hodd hQ hnsq hd hg₁O hg₁2 hJ₁O FJ FN
      (fun x hx => by rw [hg₁apply, hgJ x hx]; simp) hJ₁J hJ₁2 huJ₁ hu_ne huN
      (fun x hx => by rw [hg₁apply]; exact (FN.span).neg_mem (hgN x hx)) hA1 hAp
      (fun v => by
        rw [hg₁apply, hg₁apply, hinv v, map_neg])
    refine ⟨π, ρ, horth, hsup, fun y hy => ?_⟩
    have := hperp y hy
    rw [hg₁apply] at this
    rw [neg_smul, one_smul]
    exact neg_eq_iff_eq_neg.mp this

end Class

end CFSG.ClassicalInvolution.RouteD.TWE.B3

module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUAlignRigid

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.Universal.Symplectic.SpExtras (elt mat_elt E)
open CFSG.LieType.Steinberg (IsBlkOn)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply unitaryInvolution_involutive)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

section Perm

variable {K : Type} [Field K] {N : ℕ}

theorem permSp_mem_spBlock_of_forall_fix {π : Equiv.Perm (Fin N)} {R : Finset (Fin N)}
    (hπ : ∀ i, i ∉ R → π i = i) : permSp K π ∈ spBlock K R := by
  rw [mem_spBlock]
  intro a b hab
  rw [mat_permSp, spIncl_apply, Matrix.one_apply]
  have hp : ∀ c : Fin N ⊕ Fin N, planeOf (Sum.map π π c) = π (planeOf c) := fun c => by
    rcases c with i | i <;> rfl
  have hfix : ∀ c : Fin N ⊕ Fin N, c ∉ planeCoords R → Sum.map π π c = c := fun c hc => by
    rw [mem_planeCoords] at hc
    rcases c with i | i
    · simp only [Sum.map_inl, hπ i hc]
    · simp only [Sum.map_inr, hπ i hc]
  by_cases hb : b ∈ planeCoords R
  · have ha : a ∉ planeCoords R := fun ha => hab ⟨ha, hb⟩
    have h1 : a ≠ Sum.map π π b := by
      rintro rfl
      apply ha
      rw [mem_planeCoords] at hb ⊢
      rw [hp]
      by_contra hc
      have h2 := hπ _ hc
      exact hc (by rwa [π.injective h2])
    have h2 : a ≠ b := fun h => ha (h ▸ hb)
    rw [ite_eq_right h1, ite_eq_right h2]
  · rw [hfix b hb]

theorem permSp_swap_mem_spBlock_compl {R : Finset (Fin N)} {p p' : Fin N} (hp : p ∉ R)
    (hp' : p' ∉ R) : permSp K (Equiv.swap p p') ∈ spBlock K Rᶜ :=
  permSp_mem_spBlock_of_forall_fix fun i hi => by
    rw [Finset.mem_compl, not_not] at hi
    exact Equiv.swap_apply_of_ne_of_ne (fun h => hp (h ▸ hi)) (fun h => hp' (h ▸ hi))

end Perm

section Steps

variable {N ε : ℕ} {K F : Type} [Field K] [Field F] [CharP K 2] {hε : ε ≤ 1} {σ : F ≃+* F}
  {ι : K →+* F} {hι : ∀ c, σ (ι c) = ι c}

theorem ctuEmbed_permSp_swap_apply (p p' : Fin N) :
    (((ctuEmbed ε hε σ ι hι (permSp K (Equiv.swap p p')) : SU σ (2 * N + ε)) :
      GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F)
        (ctuCoord N ε (Sum.inl (Sum.inl p))) (ctuCoord N ε (Sum.inl (Sum.inl p'))) = 1 := by
  rw [ctuEmbed_apply_ctuCoord, fromBlocks_apply₁₁, map_apply, mat_permSp, spIncl_apply]
  simp [Equiv.swap_apply_right]

theorem ctua_field_fix_of_long {A : GL (Fin (2 * N + ε)) F} {φ : F ≃+* F} {p : Fin N}
    (hkey : ∀ c : K, A * glAut φ ((ctuEmbed ε hε σ ι hι (elt (.positiveLong p) c) :
      SU σ (2 * N + ε)) : GL (Fin (2 * N + ε)) F) * A⁻¹ =
        (ctuEmbed ε hε σ ι hι (elt (.positiveLong p) c) : GL (Fin (2 * N + ε)) F))
    (c : K) : φ (ι c) = ι c := by
  have h1 := congrArg (fun g : GL (Fin (2 * N + ε)) F =>
    (g : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F)) (hkey c)
  have h0 := congrArg (fun g : GL (Fin (2 * N + ε)) F =>
    (g : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F)) (hkey 1)
  simp only [Units.val_mul, coe_glAut, coe_ctuEmbed_elt_positiveLong] at h1 h0
  set a := ctuCoord N ε (Sum.inl (Sum.inl p)) with ha
  set b := ctuCoord N ε (Sum.inl (Sum.inr p)) with hb
  have hmap : ∀ t : F, (1 + single a b t : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F).map φ =
      1 + single a b (φ t) := by
    intro t
    ext i j
    simp only [map_apply, Matrix.add_apply, one_apply, single_apply]
    split_ifs <;> simp
  rw [hmap] at h1 h0
  rw [map_one, map_one] at h0
  set P := ((A : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F)
  set Pi := ((A⁻¹ : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F)
  have hPPi : P * Pi = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hS : P * single a b (1 : F) * Pi = single a b 1 := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hPPi] at h0
    exact add_left_cancel h0
  rw [show single a b (φ (ι c)) = φ (ι c) • single a b (1 : F) by
      rw [smul_single, smul_eq_mul, mul_one], Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    hPPi, Matrix.mul_smul, Matrix.smul_mul, hS] at h1
  have h3 : (φ (ι c) • single a b (1 : F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) =
      single a b (ι c) := add_left_cancel h1
  have h2 := congrFun (congrFun h3 a) b
  simpa using h2

theorem ctua_diag_of_comm_long (hε : ε ≤ 1) {A : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F}
    {R : Finset (Fin N)} (hblk : IsBlkOn (ctuaIdx R ε) A)
    (hpos : ∀ p, p ∉ R → A * (((ctuEmbed ε hε σ ι hι (elt (.positiveLong p) (1 : K)) :
      SU σ (2 * N + ε)) : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) =
        (((ctuEmbed ε hε σ ι hι (elt (.positiveLong p) (1 : K)) : SU σ (2 * N + ε)) :
          GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) * A)
    (hneg : ∀ p, p ∉ R → A * (((ctuEmbed ε hε σ ι hι (elt (.negativeLong p) (1 : K)) :
      SU σ (2 * N + ε)) : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) =
        (((ctuEmbed ε hε σ ι hι (elt (.negativeLong p) (1 : K)) : SU σ (2 * N + ε)) :
          GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) * A) :
    ∀ i j, i ≠ j → A i j = 0 := by
  have hplane : ∀ u : Fin N ⊕ Fin N,
      (∀ i, i ≠ ctuCoord N ε (Sum.inl u) → A i (ctuCoord N ε (Sum.inl u)) = 0) ∧
      (∀ j, j ≠ ctuCoord N ε (Sum.inl u) → A (ctuCoord N ε (Sum.inl u)) j = 0) := by
    intro u
    by_cases hu : planeOf u ∈ R
    · have hnr : ctuCoord N ε (Sum.inl u) ∉ Set.range (ctuaIdx R ε) := by
        rw [mem_range_ctuaIdx_iff, not_not, ctuCoord_mem_ctuPlanes]
        exact hu
      exact ⟨fun i hi => by rw [hblk i _ (Or.inr hnr), one_apply_ne hi],
        fun j hj => by rw [hblk _ j (Or.inl hnr), one_apply_ne (Ne.symm hj)]⟩
    · have e1 := hpos _ hu
      rw [coe_ctuEmbed_elt_positiveLong, map_one] at e1
      have e2 := hneg _ hu
      rw [coe_ctuEmbed_elt_negativeLong, map_one] at e2
      have h1 := ctua_comm_single (ctua_comm_one_add e1)
      have h2 := ctua_comm_single (ctua_comm_one_add e2)
      rcases u with p | p
      · exact ⟨h1.1, h2.2.1⟩
      · exact ⟨h2.1, h1.2.1⟩
  intro i j hij
  obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective i
  obtain ⟨w', rfl⟩ := (ctuCoord N ε).surjective j
  rcases w with u | a
  · exact (hplane u).2 _ (Ne.symm hij)
  · rcases w' with v | b
    · exact (hplane v).1 _ hij
    · exfalso
      apply hij
      congr 2
      ext
      have := a.2
      have := b.2
      omega

theorem ctua_diag_values_swap {A : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F}
    {R : Finset (Fin N)}
    (hpos : ∀ p, p ∉ R → A * (((ctuEmbed ε hε σ ι hι (elt (.positiveLong p) (1 : K)) :
      SU σ (2 * N + ε)) : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) =
        (((ctuEmbed ε hε σ ι hι (elt (.positiveLong p) (1 : K)) : SU σ (2 * N + ε)) :
          GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) * A)
    (hswap : ∀ p p', p ∉ R → p' ∉ R → p ≠ p' →
      A * (((ctuEmbed ε hε σ ι hι (permSp K (Equiv.swap p p')) : SU σ (2 * N + ε)) :
        GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) =
        (((ctuEmbed ε hε σ ι hι (permSp K (Equiv.swap p p')) : SU σ (2 * N + ε)) :
          GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) * A)
    (hdiag : ∀ i j, i ≠ j → A i j = 0) {p p' : Fin N} (hp : p ∉ R) (hp' : p' ∉ R) :
    A (ctuCoord N ε (Sum.inl (Sum.inl p))) (ctuCoord N ε (Sum.inl (Sum.inl p))) =
        A (ctuCoord N ε (Sum.inl (Sum.inr p))) (ctuCoord N ε (Sum.inl (Sum.inr p))) ∧
      A (ctuCoord N ε (Sum.inl (Sum.inl p))) (ctuCoord N ε (Sum.inl (Sum.inl p))) =
        A (ctuCoord N ε (Sum.inl (Sum.inl p'))) (ctuCoord N ε (Sum.inl (Sum.inl p'))) := by
  have e1 := hpos p hp
  rw [coe_ctuEmbed_elt_positiveLong, map_one] at e1
  refine ⟨(ctua_comm_single (ctua_comm_one_add e1)).2.2, ?_⟩
  by_cases hpp : p = p'
  · rw [hpp]
  set a := ctuCoord N ε (Sum.inl (Sum.inl p)) with ha
  set b := ctuCoord N ε (Sum.inl (Sum.inl p')) with hb
  have h := congrFun (congrFun (hswap p p' hp hp' hpp) a) b
  rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single a, Finset.sum_eq_single b] at h
  · rw [ctuEmbed_permSp_swap_apply, mul_one, one_mul] at h
    exact h
  · intro k _ hkb
    rw [hdiag k b hkb, mul_zero]
  · simp
  · intro k _ hka
    rw [hdiag a k (Ne.symm hka), zero_mul]
  · simp

end Steps

section Main

variable {N ε : ℕ} {K F : Type} [Field K] [CharP K 2] [Field F] [Finite F] [CharP F 2] {f : ℕ}

theorem exists_ctuaTwist_of_mulAut_fix_long_swap (hKc : Nat.card K = 2 ^ f)
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hε : ε ≤ 1) {ι : K →+* F}
    (hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c) {R : Finset (Fin N)} (hR : 2 ≤ Rᶜ.card)
    {S : Set (StatedSp N K)}
    (hSpos : ∀ p, p ∉ R → ∀ c : K, elt (.positiveLong p) c ∈ S)
    (hSneg : ∀ p, p ∉ R → ∀ c : K, elt (.negativeLong p) c ∈ S)
    (hSswap : ∀ p p', p ∉ R → p' ∉ R → p ≠ p' → permSp K (Equiv.swap p p') ∈ S)
    (α : MulAut (ctuBlock (unitaryInvolution F 2 f) ε R))
    (hα : ∀ (y : StatedSp N K) (hy : y ∈ spBlock K Rᶜ), y ∈ S →
      α ⟨ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι y, ctuEmbed_mem_ctuBlock_iff.2 hy⟩ =
        ⟨ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι y, ctuEmbed_mem_ctuBlock_iff.2 hy⟩) :
    ∃ (ν : Fˣ) (hν : unitaryInvolution F 2 f ν * ν = 1) (b : Bool),
      ∀ x : ctuBlock (unitaryInvolution F 2 f) ε R,
        (α x : SU (unitaryInvolution F 2 f) (2 * N + ε)) =
          ctuaTwist hε (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) ν hν b x := by
  obtain ⟨A, φ, hAblk, hAiso, hαA⟩ := exists_conj_glAut_of_mulAut_ctuBlock hF hf hε hR α
  have hkey : ∀ y ∈ spBlock K Rᶜ, y ∈ S →
      A * glAut φ ((ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι y :
        SU (unitaryInvolution F 2 f) (2 * N + ε)) : GL (Fin (2 * N + ε)) F) * A⁻¹ =
          (ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι y : GL (Fin (2 * N + ε)) F) := by
    intro y hy hyS
    have h1 := hαA ⟨ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι y, ctuEmbed_mem_ctuBlock_iff.2 hy⟩
    rw [hα y hy hyS] at h1
    exact h1.symm
  obtain ⟨p₀, hp₀, p₁, hp₁, hp01⟩ := Finset.one_lt_card.1 (by omega : 1 < Rᶜ.card)
  have hp₀R : p₀ ∉ R := Finset.mem_compl.1 hp₀
  have hφι : ∀ c : K, φ (ι c) = ι c := ctua_field_fix_of_long (p := p₀) fun c =>
    hkey _ (elt_positiveLong_mem_spBlock hp₀ c) (hSpos p₀ hp₀R c)
  obtain ⟨b, hb⟩ := ctua_field_dichotomy hKc hF hf hι hφι
  have hcomm : ∀ y ∈ spBlock K Rᶜ, y ∈ S →
      (A : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) *
        (((ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι y : SU (unitaryInvolution F 2 f)
          (2 * N + ε)) : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) =
      (((ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι y : SU (unitaryInvolution F 2 f)
        (2 * N + ε)) : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) *
          (A : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) := by
    intro y hy hyS
    have hφy : glAut φ ((ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι y :
        SU (unitaryInvolution F 2 f) (2 * N + ε)) : GL (Fin (2 * N + ε)) F) =
          (ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι y : GL (Fin (2 * N + ε)) F) :=
      Units.ext (by rw [coe_glAut, coe_ctuEmbed, ctuEmbedMat_map φ hφι])
    have h1 := hkey y hy hyS
    rw [hφy] at h1
    have h2 : A * (ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι y : GL (Fin (2 * N + ε)) F) =
        (ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι y : GL (Fin (2 * N + ε)) F) * A := by
      calc _ = A * (ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι y : GL (Fin (2 * N + ε)) F) *
            A⁻¹ * A := by group
        _ = _ := by rw [h1]
    exact congrArg (fun g : GL (Fin (2 * N + ε)) F =>
      (g : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F)) h2
  have hpos := fun (p : Fin N) (hp : p ∉ R) =>
    hcomm _ (elt_positiveLong_mem_spBlock (Finset.mem_compl.2 hp) (1 : K)) (hSpos p hp 1)
  have hneg := fun (p : Fin N) (hp : p ∉ R) =>
    hcomm _ (elt_negativeLong_mem_spBlock (Finset.mem_compl.2 hp) (1 : K)) (hSneg p hp 1)
  have hswap := fun (p p' : Fin N) (hp : p ∉ R) (hp' : p' ∉ R) (hpp : p ≠ p') =>
    hcomm _ (permSp_swap_mem_spBlock_compl hp hp') (hSswap p p' hp hp' hpp)
  have hdiag := ctua_diag_of_comm_long hε hAblk hpos hneg
  set dA : Fin (2 * N + ε) → F := fun i => (A : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) i i
    with hdAdef
  have hAd : (A : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) = diagonal dA := by
    ext i j
    by_cases h : i = j
    · subst h
      rw [diagonal_apply_eq]
    · rw [hdiag i j h, diagonal_apply_ne _ h]
  have hPPi : (A : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) *
      ((A⁻¹ : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPiP : ((A⁻¹ : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) *
      (A : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hdA0 : ∀ i, dA i ≠ 0 := by
    intro i h0
    have := congrFun (congrFun hPPi i) i
    rw [hAd, diagonal_mul, h0, zero_mul, one_apply_eq] at this
    exact zero_ne_one this
  have hAi : ((A⁻¹ : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) =
      diagonal fun i => (dA i)⁻¹ := by
    ext i j
    have := congrFun (congrFun hPiP i) j
    rw [hAd, mul_diagonal] at this
    by_cases h : i = j
    · subst h
      rw [one_apply_eq] at this
      rw [diagonal_apply_eq, eq_inv_of_mul_eq_one_left this]
    · rw [one_apply_ne h, mul_eq_zero] at this
      rw [diagonal_apply_ne _ h]
      exact this.resolve_right (hdA0 j)
  have huni : ∀ i, unitaryInvolution F 2 f (dA i) * dA (Fin.rev i) = 1 := by
    intro i
    have h1 := congrFun (congrFun hAiso i) (Fin.rev i)
    rw [CFSG.LieType.Steinberg.conjTr_mul_antidiag_mul_apply, Finset.sum_eq_single i] at h1
    · rw [antidiag, of_apply, ite_eq_left rfl] at h1
      exact h1
    · intro t _ hti
      rw [hdiag t i hti, map_zero, zero_mul]
    · simp
  set lam := dA (ctuCoord N ε (Sum.inl (Sum.inl p₀))) with hlam
  have hlam : ∀ u : Fin N ⊕ Fin N, planeOf u ∉ R → dA (ctuCoord N ε (Sum.inl u)) = lam := by
    intro u hu
    rcases u with p | p
    · exact ((ctua_diag_values_swap hpos hswap hdiag hp₀R hu).2).symm
    · have hu' : p ∉ R := hu
      exact ((ctua_diag_values_swap hpos hswap hdiag hu' hu').1).symm.trans
        ((ctua_diag_values_swap hpos hswap hdiag hp₀R hu').2).symm
  have hlam0 : lam ≠ 0 := hdA0 _
  have hσlam : unitaryInvolution F 2 f lam * lam = 1 := by
    have h1 := huni (ctuCoord N ε (Sum.inl (Sum.inl p₀)))
    rw [ctuCoord_rev hε, ctuPar_inl, par_inl, hlam (Sum.inr p₀) hp₀R] at h1
    exact h1
  obtain ⟨ν, hν, hdν⟩ : ∃ ν : Fˣ, unitaryInvolution F 2 f ν * ν = 1 ∧
      ∀ i : Fin ε, dA (ctuCoord N ε (Sum.inr i)) = lam * ν := by
    by_cases hε0 : ε = 0
    · subst hε0
      exact ⟨1, by rw [Units.val_one, map_one, one_mul], fun i => i.elim0⟩
    · have hε1 : 0 < ε := Nat.pos_of_ne_zero hε0
      set m := ctuCoord N ε (Sum.inr ⟨0, hε1⟩) with hm
      refine ⟨Units.mk0 (dA m / lam) (div_ne_zero (hdA0 m) hlam0), ?_, fun i => ?_⟩
      · have h1 := huni m
        rw [hm, ctuCoord_inr_rev hε, ← hm] at h1
        rw [Units.val_mk0, map_div₀, div_mul_div_comm, h1, hσlam, div_one]
      · have hi : i = ⟨0, hε1⟩ := Fin.ext (by have := i.2; omega)
        subst hi
        rw [Units.val_mk0, ← hm]
        field_simp
  refine ⟨ν, hν, b, fun x => ?_⟩
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [ctuaTwist_apply_apply, hαA x, Units.val_mul, Units.val_mul, coe_glAut, hAd, hAi,
    mul_diagonal, diagonal_mul, map_apply, hb, ctuaTorEntry_inv_eq]
  by_cases hij : i ∈ ctuPlanes ε R ∨ j ∈ ctuPlanes ε R
  · have hx := mem_ctuBlock.1 x.2 i j hij
    have hm : (bif b then unitaryInvolution F 2 f (((x : SU (unitaryInvolution F 2 f) (2 * N + ε)) :
        GL (Fin (2 * N + ε)) F) i j) else (((x : SU (unitaryInvolution F 2 f) (2 * N + ε)) :
          GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) i j) =
        (1 : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) i j := by
      cases b
      · exact hx
      · change unitaryInvolution F 2 f _ = _
        rw [hx]
        by_cases h : i = j
        · rw [h, one_apply_eq, map_one]
        · rw [one_apply_ne h, map_zero]
    rw [hm]
    by_cases h : i = j
    · subst h
      rw [one_apply_eq, mul_one, mul_one, mul_inv_cancel₀ (hdA0 i),
        mul_inv_cancel₀ (ctuaTorEntry_ne_zero ν i)]
    · rw [one_apply_ne h, mul_zero, zero_mul, mul_zero, zero_mul]
  · push Not at hij
    have hdi : ∀ c, c ∉ ctuPlanes ε R → dA c = lam * ctuaTorEntry (ν : F) c := by
      intro c hc
      obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective c
      rcases w with u | a
      · rw [ctuaTorEntry_inl, mul_one]
        exact hlam u (fun h => hc (ctuCoord_mem_ctuPlanes.2 h))
      · rw [ctuaTorEntry_inr]
        exact hdν a
    rw [hdi i hij.1, hdi j hij.2]
    have h1 := ctuaTorEntry_ne_zero (N := N) (ε := ε) ν j
    field_simp

end Main

end CFSG.SeitzReduction.SymplecticPilot

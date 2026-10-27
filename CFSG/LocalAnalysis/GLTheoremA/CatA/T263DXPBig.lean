module

public import CFSG.HardMathSupport.Seitz.Proving.SL2PrimeOrder
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterPass

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section SL2Facts

variable {K : Type*} [Field K]

private theorem sl2_entries_of_commute_uSL {C : SL2 K} (h : C * uSL 1 = uSL 1 * C) :
    (C : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
      (C : Matrix (Fin 2) (Fin 2) K) 0 0 = (C : Matrix (Fin 2) (Fin 2) K) 1 1 := by
  have h00 := congrArg (fun M : SL2 K => (M : Matrix (Fin 2) (Fin 2) K) 0 0) h
  have h01 := congrArg (fun M : SL2 K => (M : Matrix (Fin 2) (Fin 2) K) 0 1) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    coe_uSL] at h00 h01
  simp at h00 h01
  exact ⟨h00, by linear_combination h01⟩

private theorem uSL_mul_uSL' (s t : K) : (uSL s : SL2 K) * uSL t = uSL (s + t) := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_uSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem uSL_pow_nat (t : K) (n : ℕ) : (uSL t : SL2 K) ^ n = uSL ((n : K) * t) := by
  induction n with
  | zero =>
    refine SL2_ext ?_ ?_ ?_ ?_ <;> simp [coe_uSL]
  | succ n ih =>
    rw [pow_succ, ih, uSL_mul_uSL']
    congr 1
    push_cast
    ring

private theorem sl2_mul_self_of_entries {C : SL2 K}
    (h10 : (C : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (h11 : (C : Matrix (Fin 2) (Fin 2) K) 0 0 = (C : Matrix (Fin 2) (Fin 2) K) 1 1) :
    C * C = uSL (2 * ((C : Matrix (Fin 2) (Fin 2) K) 0 0 *
      (C : Matrix (Fin 2) (Fin 2) K) 0 1)) := by
  have hdet := det_SL2 C
  rw [h10, ← h11] at hdet
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_uSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, h10,
      ← h11]
  · linear_combination hdet
  · ring
  · linear_combination hdet

private theorem sl2_pow_two_mul_card_of_entries [Finite K] {C : SL2 K}
    (h10 : (C : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (h11 : (C : Matrix (Fin 2) (Fin 2) K) 0 0 = (C : Matrix (Fin 2) (Fin 2) K) 1 1) :
    C ^ (2 * Nat.card K) = 1 := by
  have : Fintype K := Fintype.ofFinite K
  rw [pow_mul, pow_two, sl2_mul_self_of_entries h10 h11, uSL_pow_nat, Nat.card_eq_fintype_card,
    Nat.cast_card_eq_zero, zero_mul]
  refine SL2_ext ?_ ?_ ?_ ?_ <;> simp [coe_uSL]

private theorem exists_sl2_orderOf_prime_entries [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ Nat.card K ^ 2 - 1) :
    ∃ C : SL2 K, orderOf C = p ∧ ((C : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 ∨
      (C : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ (C : Matrix (Fin 2) (Fin 2) K) 1 1) := by
  obtain ⟨C, hC⟩ := CFSG.HardMathSupport.Seitz.Proving.exists_orderOf_eq_prime_SL2 hp hdvd
  refine ⟨C, hC, ?_⟩
  by_contra hcon
  push Not at hcon
  have h1 := sl2_pow_two_mul_card_of_entries hcon.1 hcon.2
  have h2 : p ∣ 2 * Nat.card K := hC ▸ orderOf_dvd_of_pow_eq_one h1
  rcases (Nat.Prime.dvd_mul hp).1 h2 with h | h
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  · have h3 : p ∣ Nat.card K ^ 2 := dvd_pow h two_ne_zero
    have h4 : p ∣ Nat.card K ^ 2 - (Nat.card K ^ 2 - 1) := Nat.dvd_sub h3 hdvd
    have hpos : 0 < Nat.card K ^ 2 := pow_pos Nat.card_pos 2
    have h5 : Nat.card K ^ 2 - (Nat.card K ^ 2 - 1) = 1 := by omega
    rw [h5] at h4
    exact hp.one_lt.ne' (Nat.dvd_one.1 h4)

end SL2Facts


section PBig

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)

private theorem outer_p_dvd_of_orbit {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hQ4 : 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
    {z₀ : ModGL τ L}
    (hz₀ : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      z₀ * g * z₀⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    {φ₁ : ModGL τ L →* ModGL τ L}
    (hφ₁ : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      iterHom S.D.step (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
        (z₀ * g * z₀⁻¹) = z₀ * φ₁ g * z₀⁻¹)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ componentRoots (rootCharHom a) i) {m : ℕ} (hm : 0 < m)
    (β : ℕ → Fin τ.rank → ℤ) (hβΨ : ∀ j, β j ∈ componentRoots (rootCharHom a) i)
    (hβ : ∀ j < m, ∀ B, φ₁^[j] (rootSL2 τ L γ B) ∈ rootRankOneGroup τ L (β j))
    (hcomm₁ : ∀ j l, j < m → l < m → j ≠ l → ∀ x ∈ rootRankOneGroup τ L (β j),
      ∀ y ∈ rootRankOneGroup τ L (β l), Commute x y)
    (σm : L ≃+* L) (hσm : ∀ c, σm c = c ^ (S.D.q ^
      (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) * m)))
    (X : GL (Fin 2) L)
    (hret : ∀ B, φ₁^[m] (rootSL2 τ L γ B) =
      rootSL2 τ L γ (conjSL X (Matrix.SpecialLinearGroup.map σm.toRingHom B)))
    (P : GL (Fin 2) L) (hP : P * Matrix.GeneralLinearGroup.map σm.toRingHom P⁻¹ = X)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (C : SL(2, fixSubfield σm)) (hCℓ : orderOf C = ℓ)
    (hCu : (C : Matrix (Fin 2) (Fin 2) (fixSubfield σm)) 1 0 ≠ 0 ∨
      (C : Matrix (Fin 2) (Fin 2) (fixSubfield σm)) 0 0 ≠
        (C : Matrix (Fin 2) (Fin 2) (fixSubfield σm)) 1 1) :
    ℓ ∣ Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have : NeZero s := ⟨hs0.ne'⟩
  have hP0 : (outerOrbitFamily S hT i hs hmin).S 0 =
      rootSpan τ L (componentRoots (rootCharHom a) i) := by
    rw [outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
  obtain ⟨hfin, hcard⟩ := outer_card_fixSubfield S σm (Nat.mul_pos hs0 hm) hσm
  have : Finite (fixSubfield σm) := hfin
  have hQ4m : 4 ≤ S.D.q ^ (s * m) :=
    hQ4.trans (Nat.pow_le_pow_right S.q_pos (Nat.le_mul_of_pos_right s hm))
  have hperf : Group.IsPerfect (SL(2, fixSubfield σm)) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card _
      (by rw [hcard]; exact hQ4m)
  obtain ⟨θ, hθ, hθfix, hθS⟩ := outer_exists_theta i hm β hβΨ hβ hcomm₁ σm X hret P hP
  let θ₁ : SL(2, fixSubfield σm) →* (outerOrbitFamily S hT i hs hmin).S 0 :=
    ((MulAut.conj z₀).toMonoidHom.comp θ).codRestrict _ fun A => by
      rw [hP0]
      exact hz₀ _ (hθS A)
  have hθ₁ : ∀ A, ((θ₁ A : (outerOrbitFamily S hT i hs hmin).S 0) : ModGL τ L) =
      z₀ * θ A * z₀⁻¹ := fun A => rfl
  have hθ₁fix : ∀ A, iterHom S.D.step s ((θ₁ A : (outerOrbitFamily S hT i hs hmin).S 0) :
      ModGL τ L) = θ₁ A := fun A => by
    rw [hθ₁, hφ₁ _ (hθS A), hθfix]
  set x := (outerOrbitFamily S hT i hs hmin).norm (θ₁ C) with hx
  have hxR : x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    outer_norm_mem_rationalComponent S hT i hs hmin hperf θ₁ hθ₁fix _
  have hxℓ : x ^ ℓ = 1 := by
    have hCpow : C ^ ℓ = 1 := hCℓ ▸ pow_orderOf_eq_one C
    rw [hx, ← map_pow, ← map_pow, hCpow, map_one, map_one]
  have hx1 : x ≠ 1 := by
    intro hx1
    have hZ := (outerOrbitFamily S hT i hs hmin).mem_Z_of_mu_eq_one
      ((outerOrbitFamily S hT i hs hmin).diag (θ₁ C)) hx1 0
    have hy : ((((outerOrbitFamily S hT i hs hmin).diag (θ₁ C)) 0 :
        (outerOrbitFamily S hT i hs hmin).S 0) : ModGL τ L) = z₀ * θ C * z₀⁻¹ := by
      show iterHom S.D.step (0 : ZMod s).val _ = _
      rw [ZMod.val_zero, iterHom_zero]
      rfl
    rw [hy] at hZ
    have hcB : ∀ B : SL2 L, Commute (θ C) (rootSL2 τ L γ B) := by
      intro B
      have hρS : rootSL2 τ L γ B ∈ rootSpan τ L (componentRoots (rootCharHom a) i) :=
        outer_rankOne_le_rootSpan hγ ⟨B, rfl⟩
      have hmemA : z₀ * rootSL2 τ L γ B * z₀⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).A :=
        (outerOrbitFamily S hT i hs hmin).S_le_A 0 (by rw [hP0]; exact hz₀ _ hρS)
      have h1 := ((outerOrbitFamily S hT i hs hmin).mem_Z.1 hZ) _ hmemA
      have h2 : z₀ * (rootSL2 τ L γ B * θ C) * z₀⁻¹ = z₀ * (θ C * rootSL2 τ L γ B) * z₀⁻¹ := by
        calc z₀ * (rootSL2 τ L γ B * θ C) * z₀⁻¹ =
              z₀ * rootSL2 τ L γ B * z₀⁻¹ * (z₀ * θ C * z₀⁻¹) := by
              group
          _ = z₀ * θ C * z₀⁻¹ * (z₀ * rootSL2 τ L γ B * z₀⁻¹) := h1
          _ = z₀ * (θ C * rootSL2 τ L γ B) * z₀⁻¹ := by group
      exact (mul_left_cancel (mul_right_cancel h2)).symm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    set D : SL2 L := conjSL P (Matrix.SpecialLinearGroup.map (algebraMap (fixSubfield σm) L) C)
      with hD
    have hθC : θ C = rootSL2 τ L γ D *
        ((List.range m').map fun j => (⇑φ₁)^[j + 1] (rootSL2 τ L γ D)).prod := by
      rw [hθ, List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
      rfl
    have hR : ∀ B : SL2 L, Commute
        ((List.range m').map fun j => (⇑φ₁)^[j + 1] (rootSL2 τ L γ D)).prod
        (rootSL2 τ L γ B) := by
      intro B
      refine Commute.list_prod_left _ _ fun y hy => ?_
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
      have hj' := List.mem_range.1 hj
      exact hcomm₁ (j + 1) 0 (by omega) hm (by omega) _ (hβ (j + 1) (by omega) D) _
        (hβ 0 hm B)
    have hDB : ∀ B : SL2 L, Commute (rootSL2 τ L γ D) (rootSL2 τ L γ B) := by
      intro B
      have h1 := hcB B
      rw [hθC] at h1
      have h2 := h1.mul_left (hR B).inv_left
      rwa [mul_inv_cancel_right] at h2
    have hinj := rootSL2_injective_of_field (τ := τ) (K := L) γ
    have hPinj : Function.Injective (conjSL P) := fun y y' h => by
      have := congrArg (conjSL P⁻¹) h
      rwa [← conjSL_mul, ← conjSL_mul, inv_mul_cancel, conjSL_one, conjSL_one] at this
    have hcu : Matrix.SpecialLinearGroup.map (algebraMap (fixSubfield σm) L) C * uSL 1 =
        uSL 1 * Matrix.SpecialLinearGroup.map (algebraMap (fixSubfield σm) L) C := by
      apply hPinj
      apply hinj
      simp only [map_mul]
      exact hDB (conjSL P (uSL 1))
    obtain ⟨h10, h11⟩ := sl2_entries_of_commute_uSL hcu
    have hC : ∀ k l, ((Matrix.SpecialLinearGroup.map (algebraMap (fixSubfield σm) L) C : SL2 L) :
        Matrix (Fin 2) (Fin 2) L) k l =
        algebraMap (fixSubfield σm) L ((C : Matrix (Fin 2) (Fin 2) (fixSubfield σm)) k l) :=
      fun k l => rfl
    rw [hC, ← map_zero (algebraMap (fixSubfield σm) L)] at h10
    rw [hC, hC] at h11
    rcases hCu with hCu | hCu
    · exact hCu ((algebraMap (fixSubfield σm) L).injective h10)
    · exact hCu ((algebraMap (fixSubfield σm) L).injective h11)
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hoℓ : orderOf x = ℓ := orderOf_eq_prime hxℓ hx1
  have := Subgroup.orderOf_dvd_natCard (rationalComponent S.ρ S.Γ (rootCharHom a) i) hxR
  rwa [hoℓ] at this

end PBig

theorem pBigComponents_of_dvd_sq_sub_one {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (h1 : rootDiagUnit τ a ≠ 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ S.D.q ^ 2 - 1) (hq4 : 4 ≤ S.D.q) (i : KernelComponent (rootCharHom a)) :
    ¬ Nat.Coprime p (Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  have hQ4 : 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) :=
    hq4.trans (by
      calc S.D.q = S.D.q ^ 1 := (pow_one _).symm
        _ ≤ _ := Nat.pow_le_pow_right S.q_pos hs0)
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  obtain ⟨f, z₀, φ₁, hf, hpos, hpin, hz₀n, hφ₁, -, -⟩ := outer_exists_lang_data S hT i
  obtain ⟨⟨γ, hγk⟩, hγi⟩ := Quotient.exists_rep i
  have hγ : γ ∈ componentRoots (rootCharHom a) i := ⟨hγk, hγi⟩
  obtain ⟨δ, hδ, m, hm, hper, horth⟩ := outerRoots_exists_orth hΨ hf hpos hγ
  obtain ⟨hβ, hcomm₁, σm, X, P, hσm, hret, hP⟩ :=
    outer_exists_first_data S hT i hf hpos hpin hδ.1 hm hper horth
  obtain ⟨hfin, hcard⟩ := outer_card_fixSubfield S σm
    (Nat.mul_pos hs0 hm) hσm
  have : Finite (fixSubfield σm) := hfin
  have hdvd : p ∣ Nat.card (fixSubfield σm) ^ 2 - 1 := by
    rw [hcard, ← pow_mul]
    exact hpq.trans (Nat.pow_sub_one_dvd_pow_sub_one S.D.q (dvd_mul_left 2 _))
  obtain ⟨C, hCp, hCu⟩ := exists_sl2_orderOf_prime_entries hp hp2 hdvd
  have h3 := outer_p_dvd_of_orbit S hT i hQ4 (fun g hg => (hz₀n g).1 hg) hφ₁ hδ.1 hm
    (fun j => f^[j] δ) (fun j => outerRoots_iterate_mem hf j hδ.1) hβ hcomm₁ σm hσm X hret P hP
    hp C hCp hCu
  intro hcop
  exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop h3)

end CFSG.LocalAnalysis.GLTheoremA.T263.DX

module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256j
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256j2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256r

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup PerfectInLayer)

section Lang

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256j
open scoped Pointwise


variable {τ : Tag} {K : Type} [Field K] [Finite K] {ℓ : ℕ}

variable {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀)

section SuN

open Matrix CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.SectionRank.OddCover
open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.Steinberg.Adjoint
open scoped MatrixGroups commutatorElement

theorem compCharElem_of_unitary_frame_of_four_le (hK : ringChar K = ℓ) (hℓp : ℓ.Prime) (hq4 : 4 ≤ S.D.q)
    {ta : Fin τ.rank → (AlgebraicClosure K)ˣ} (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta)) {ν : ℕ} (hν : 3 ≤ ν)
    {ψ : SL(ν, AlgebraicClosure K) →* ModGL τ (AlgebraicClosure K)} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom ta) i)] (σ a b) = σ (π b) (π a)) :
    CompCharElem S ℓ ta i := by
  classical
  set L := AlgebraicClosure K with hLdef
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) with hsdef
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  have hrℓ : r = ℓ := by
    have hLℓ : ringChar L = ℓ := by
      rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_algebraicClosure, hK]
    rw [← hLℓ]
    exact (ringChar.eq L r).symm
  obtain ⟨σQ, hσQ⟩ := exists_ringEquiv_frob (L := L) r (e * s)
  have hσc : ∀ c, σQ c = c ^ (r ^ (e * s)) := fun c => by
    have h1 : σQ c = iterateFrobenius L r (e * s) c := by
      rw [← hσQ]
      rfl
    rw [h1, iterateFrobenius_def]
  have hQ : S.D.q ^ s = r ^ (e * s) := by rw [hq, ← pow_mul]
  set Fs : ModGL τ L →* ModGL τ L := iterHom S.D.step s with hFs
  choose! ε hε using fun (a b : Fin ν) (hab : a ≠ b) => hψ.transv a b hab
  have hπne : ∀ a b : Fin ν, a ≠ b → π b ≠ π a := fun a b hab => (π.injective.ne hab).symm
  have hstepU : ∀ a b : Fin ν, a ≠ b → ∃ μ : Lˣ, ∀ c : L,
      Fs (pinnedX τ L (σ a b) c) = pinnedX τ L (σ (π b) (π a)) ((μ : L) * σQ c) := by
    intro a b hab
    obtain ⟨μ, hμ0, hμ⟩ := iter_step_pinnedX S s (hψ.isRoot a b hab)
    refine ⟨Units.mk0 μ hμ0, fun c => ?_⟩
    rw [hFs, iterHom_eq_iterate, hμ, hπ a b hab, hσc, ← hQ]
    rfl
  choose! μ hμ using hstepU
  set β : Fin ν → Fin ν → Lˣ := fun a b =>
    μ a b * ε a b ^ (r ^ (e * s)) * (ε (π b) (π a))⁻¹ with hβ
  have hkey : ∀ (a b : Fin ν) (hab : a ≠ b) (t : L),
      Fs (ψ (Matrix.SpecialLinearGroup.transvection hab t)) =
        ψ (Matrix.SpecialLinearGroup.transvection (hπne a b hab) ((β a b : L) * σQ t)) := by
    intro a b hab t
    rw [hε a b hab t, hμ a b hab, hε (π b) (π a) (hπne a b hab)]
    congr 1
    rw [map_mul, hσc (ε a b : L), hβ]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    have h0 : (ε (π b) (π a) : L) ≠ 0 := Units.ne_zero _
    field_simp
    ring
  have hcoc : ∀ a b c : Fin ν, a ≠ b → b ≠ c → a ≠ c → β a c = -(β a b * β b c) := by
    intro a b c hab hbc hac
    have hcomm := Matrix.SpecialLinearGroup.commutatorElement_transvection hab hbc hac (1 : L) 1
    rw [mul_one] at hcomm
    have h1 := congrArg (fun X => Fs (ψ X)) hcomm
    simp only [map_commutatorElement] at h1
    rw [hkey a b hab, hkey b c hbc, hkey a c hac, map_one, mul_one, mul_one, mul_one,
      ← map_commutatorElement ψ,
      commutator_transvection_rev (hπne a b hab) (hπne b c hbc) (hπne a c hac),
      hε _ _ (hπne a c hac), hε _ _ (hπne a c hac)] at h1
    have h2 := pinnedX_injective τ L _ h1
    have h0 : (ε (π c) (π a) : L) ≠ 0 := Units.ne_zero _
    apply Units.ext
    have h3 := mul_left_cancel₀ h0 h2
    rw [Units.val_neg, Units.val_mul]
    exact h3.symm
  obtain ⟨d, hd⟩ := exists_units_of_cocycle hν β hcoc
  set M : GL (Fin ν) L := diagHom ν d * (permGL π : GL (Fin ν) L)⁻¹ with hMdef
  obtain ⟨B, hB⟩ := exists_specialLinear_conj_eq (n := ν) (by omega) M
  have hBconj : ∀ (a b : Fin ν) (hab : a ≠ b) (u : L),
      B * Matrix.SpecialLinearGroup.transvection (hπne a b hab) u * B⁻¹ =
        Matrix.SpecialLinearGroup.transvection (Ne.symm hab) ((d b : L) * u * ((d a)⁻¹ : Lˣ)) := by
    intro a b hab u
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe, hB]
    have hM : ∀ Y : Matrix (Fin ν) (Fin ν) L, (M : Matrix (Fin ν) (Fin ν) L) * Y *
        (↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) = (diagHom ν d : Matrix (Fin ν) (Fin ν) L) *
          ((↑(permGL π : GL (Fin ν) L)⁻¹ : Matrix (Fin ν) (Fin ν) L) * Y *
            ((permGL π : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)) *
              (↑(diagHom ν d)⁻¹ : Matrix (Fin ν) (Fin ν) L) := by
      intro Y
      simp only [hMdef, _root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
    rw [hM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.inv_mul,
      permGL_inv_mul_single_mul, diagHom_mul_one_add_single_mul d (Ne.symm hab) u]
  have hstd : ∀ X : SL(ν, L), ψ B * Fs (ψ X) * (ψ B)⁻¹ = ψ (stdUnitary σQ.toRingHom X) := by
    have h : (MulAut.conj (ψ B)).toMonoidHom.comp (Fs.comp ψ) =
        ψ.comp (stdUnitary σQ.toRingHom) := by
      refine MonoidHom.eq_of_eqOn_dense
        (CFSG.LinearGroups.special_linear_elementary_generation (n := ν) (K := L)) ?_
      rintro _ ⟨a, b, hab, t, rfl⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hkey a b hab t, ← map_mul, ← map_inv, ← map_mul, hBconj a b hab,
        stdUnitary_transvection]
      congr 2
      rw [hd a b hab]
      simp only [Units.val_neg, Units.val_mul, Units.val_inv_eq_inv_val,
        RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      have h0 : (d a : L) ≠ 0 := Units.ne_zero _
      have h0' : (d b : L) ≠ 0 := Units.ne_zero _
      have e1 : (d b : L) * (-((d a : L) * (d b : L)⁻¹) * σQ t) * (d a : L)⁻¹ =
          -(σQ t) * ((d b : L) * (d b : L)⁻¹) * ((d a : L) * (d a : L)⁻¹) := by ring
      rw [e1, mul_inv_cancel₀ h0', mul_inv_cancel₀ h0, mul_one, mul_one]
    intro X
    have := DFunLike.congr_fun h X
    simpa [MulAut.conj_apply] using this
  have hψS : ∀ X, ψ X ∈ rootSpan τ L (componentRoots (rootCharHom ta) i) := fun X => by
    rw [hΨ, ← hψ.range]
    exact ⟨X, rfl⟩
  have hy₁ : ψ B ∈ rootSpan τ L (kernelRoots (rootCharHom ta)) :=
    rootSpan_mono (fun γ hγ => hγ.1) (hψS B)
  obtain ⟨z, hz, hnorm⟩ := exists_lang_mul_T S hT hs0 hy₁
  have hconj : ∀ X : SL(ν, L), Fs (z * ψ X * z⁻¹) = z * ψ (stdUnitary σQ.toRingHom X) * z⁻¹ := by
    intro X
    rw [← hstd X, map_mul, map_mul, map_inv, hz]
    group
  have hker : ψ.ker ≠ ⊤ := by
    intro h
    have h01 : (⟨0, by omega⟩ : Fin ν) ≠ ⟨1, by omega⟩ := by simp
    have h1 : Matrix.SpecialLinearGroup.transvection h01 (1 : L) ∈ ψ.ker := by
      rw [h]
      exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker, hε _ _ h01, mul_one, ← pinnedX_zero τ L (σ _ _)] at h1
    exact Units.ne_zero _ (pinnedX_injective τ L _ h1)
  have hkerc : ∀ X : SL(ν, L), ψ X = 1 → X ∈ Subgroup.center SL(ν, L) := fun X hX =>
    mem_center_SL_of_commute hν ψ hker fun Y => by rw [hX, one_mul, mul_one]
  set C := CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ) with hCdef
  have hCmem : ∀ X : SL(ν, L), X ∈ C ↔ stdUnitary σQ.toRingHom X = X := fun X => by
    rw [hCdef, CFSG.RankThree.Classical2.mem_fixSubgroup, stdUnitaryEquiv_apply]
  obtain ⟨-, hqsC, -⟩ := stdUnitary_fixSubgroup (ν := ν) hr (Nat.mul_pos he hs0) σQ hσc hν
  have hne : (ν, r ^ (e * s)) ≠ (3, 2) := by
    intro h
    have h2 : r ^ (e * s) = 2 := congrArg Prod.snd h
    have h3 : S.D.q ≤ r ^ (e * s) := by
      rw [hq]
      exact Nat.pow_le_pow_right hr.pos (Nat.le_mul_of_pos_right e hs0)
    omega
  have hCperf : ⁅C, C⁆ = C := Subgroup.isPerfect_iff.1 (hqsC hne).1
  set θ : SL(ν, L) →* ModGL τ L := (MulAut.conj z).toMonoidHom.comp ψ with hθdef
  have hθ : ∀ X, θ X = z * ψ X * z⁻¹ := fun X => rfl
  refine ⟨C.map θ, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨X, -, rfl⟩
    rw [hθ]
    exact (hnorm i _).1 (hψS X)
  · rintro _ ⟨X, hX, rfl⟩
    show Fs (θ X) = θ X
    rw [hθ, hconj, (hCmem X).1 hX]
  · rw [← Subgroup.map_commutator, hCperf]
  · intro y hy hyF ⟨n, hn⟩
    have hy' : z⁻¹ * y * z ∈ rootSpan τ L (componentRoots (rootCharHom ta) i) := (hnorm i _).2 (by
      have e : z * (z⁻¹ * y * z) * z⁻¹ = y := by group
      rw [e]
      exact hy)
    rw [hΨ, ← hψ.range] at hy'
    obtain ⟨X, hX⟩ := hy'
    have hyX : y = θ X := by rw [hθ, hX]; group
    have hrℓ' : ℓ = r := hrℓ.symm
    have hcX : X ^ ℓ ^ n ∈ Subgroup.center SL(ν, L) := by
      refine hkerc _ ?_
      have h1 : θ (X ^ ℓ ^ n) = 1 := by rw [map_pow, ← hyX, hn]
      rw [hθ] at h1
      have h2 : ψ (X ^ ℓ ^ n) = z⁻¹ * (z * ψ (X ^ ℓ ^ n) * z⁻¹) * z := by group
      rw [h2, h1]
      group
    obtain ⟨N, hN, hcN⟩ := exists_coprime_pow_of_mem_center_SL hℓp hK (by omega) hcX
    have hcopy : Nat.Coprime N (orderOf y) :=
      Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hn) (Nat.Coprime.pow_right n hN)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcopy
    set X₁ := (X ^ N) ^ m with hX₁
    have hyX₁ : y = θ X₁ := by
      rw [hX₁, map_pow, map_pow, ← hyX, hm]
    have hX₁n : X₁ ^ ℓ ^ n = 1 := by
      rw [hX₁, ← pow_mul, ← pow_mul, show N * (m * ℓ ^ n) = ℓ ^ n * N * m by ring, pow_mul, pow_mul, hcN,
        one_pow]
    set c₁ := stdUnitary σQ.toRingHom X₁ * X₁⁻¹ with hc₁
    have hc₁c : c₁ ∈ Subgroup.center SL(ν, L) := by
      refine hkerc _ ?_
      have h1 : Fs (θ X₁) = θ X₁ := by rw [← hyX₁]; exact hyF
      rw [hθ, hconj] at h1
      have h2 : ψ (stdUnitary σQ.toRingHom X₁) = ψ X₁ := by
        have := congrArg (fun g => z⁻¹ * g * z) h1
        simpa [mul_assoc] using this
      rw [hc₁, map_mul, map_inv, h2, mul_inv_cancel]
    have hc₁n : c₁ ^ ℓ ^ n = 1 := by
      have hcomm : Commute c₁ X₁ := (Subgroup.mem_center_iff.1 hc₁c X₁).symm
      have e1 : stdUnitary σQ.toRingHom X₁ = c₁ * X₁ := by rw [hc₁, inv_mul_cancel_right]
      have h1 : (stdUnitary σQ.toRingHom X₁) ^ ℓ ^ n = 1 := by rw [← map_pow, hX₁n, map_one]
      rw [e1, hcomm.mul_pow, hX₁n, mul_one] at h1
      exact h1
    haveI : Fact ℓ.Prime := ⟨hℓp⟩
    haveI : CharP L ℓ := hrℓ ▸ hchar
    have hc₁1 : c₁ = 1 := eq_one_of_mem_center_SL_charPow (by omega) hc₁c hc₁n
    have hX₁C : X₁ ∈ C := by
      rw [hCmem]
      exact mul_inv_eq_one.1 hc₁1
    exact ⟨X₁, hX₁C, hyX₁.symm⟩

theorem compCharElem_suN_of_four_le (hK : ringChar K = ℓ) (hℓp : ℓ.Prime) (hq4 : 4 ≤ S.D.q) {p : ℕ}
    (hp : p.Prime)
    {ta : Fin τ.rank → (AlgebraicClosure K)ˣ} (hT : rootDiagUnit τ ta ∈ S.D.torus) (hap : ∀ i, ta i ^ p = 1)
    (h1 : rootDiagUnit τ ta ≠ 1) (i : KernelComponent (rootCharHom ta))
    (hkind : twistKind S.ρ (rootCharHom ta) i = .suN) :
    CompCharElem S ℓ ta i := by
  classical
  have hℓL : ringChar (AlgebraicClosure K) ≠ p :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.natCast_ne_zero_of_ringChar_ne hp hℓL
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  obtain ⟨h2, hn⟩ := suN_rank_ncard hkind
  obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ :=
    exists_frame_of_typeA_tag_T_of_prime g2LongA2Frame_proved S hp hpL hTp i h2 hn
  obtain ⟨hs0, hs, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) with hsdef
  have hout : ¬ twistInner (componentRoots (rootCharHom ta) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) := by
    intro h
    unfold twistKind at hkind
    rw [ite_eq_left_iff.2 (fun h' => absurd h h')] at hkind
    exact absurd hkind (by decide)
  have hmaps : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ a b) ∈ frameRoots σ := by
    intro a b hab
    have h1 : σ a b ∈ componentRoots (rootCharHom ta) i := by
      rw [hΨ]
      exact ⟨a, b, hab, rfl⟩
    have h2 : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ a b) ∈
        (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom ta) i := ⟨_, h1, rfl⟩
    rw [hs, hΨ] at h2
    exact h2
  have hneg : ∀ (n : ℕ) (γ : Fin τ.rank → ℤ),
      (S.ρ : (Fin τ.rank → ℤ) → _)^[n] (-γ) = -(S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ := by
    intro n
    induction n with
    | zero => exact fun γ => rfl
    | succ n ih =>
      intro γ
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, S.frob.neg_eq]
  rcases hψ.aut_cases hν hκ hnorm ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) hmaps (hneg s)
      (iform_rho_iterate S s) with ⟨π, hπ⟩ | ⟨π, hπ⟩
  · exfalso
    apply hout
    obtain ⟨w, hw, hwσ⟩ := hψ.exists_weyl_perm hκ hnorm π
    refine ⟨w, ?_, fun γ hγ => ?_⟩
    · rw [hΨ]
      exact hw
    · rw [hΨ] at hγ
      obtain ⟨a, b, hab, rfl⟩ := hγ
      rw [hπ a b hab, hwσ]
  · exact compCharElem_of_unitary_frame_of_four_le S hK hℓp hq4 hT i hν hψ hΨ π hπ

end SuN


open CFSG.HardMathSupport.Timmesfeld.CrossChar in
theorem orbitCharElemPerfect_twoD_exc_any {p : ℕ} (hp : p.Prime) {a : Fin τ.rank → (AlgebraicClosure K)ˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .twoD ∨ twistKind S.ρ (rootCharHom a) i = .exc) :
    OrbitCharElemPerfect S (ringChar K) a i := by
  classical
  have hℓ : (ringChar K).Prime := by
    haveI : Fintype K := Fintype.ofFinite K
    exact (FiniteField.card K (ringChar K)).choose_spec.1
  have hLℓ : ringChar (AlgebraicClosure K) = ringChar K :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_algebraicClosure K
  have hℓL : ringChar (AlgebraicClosure K) ≠ p :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.natCast_ne_zero_of_ringChar_ne hp hℓL
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  rcases hkind with hk | hk
  · obtain ⟨hnin, h4, hcard⟩ := twoD_kind_unpack hk
    by_cases h5' : 5 ≤ compRank (componentRoots (rootCharHom a) i)
    · have hr := le_trans h5' (compRank_le_rank (componentRoots (rootCharHom a) i))
      have hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
        cases τ <;> simp_all [Tag.rank]
      refine exists_perfect_orbit_twoD_high S hLℓ (fun t ht => ?_) hτ hT i hk h5'
      obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
      obtain ⟨N, hN, hlN⟩ := exists_coprime_pow_eq_one_algClosure hℓ rfl l
      exact ⟨N, hN, rootDiagUnit_pow_eq_one_of_forall hlN⟩
    · have hr : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
      have hc : (componentRoots (rootCharHom a) i).ncard = 24 := by
        rw [hcard, hr]
      exact orbitCharElemPerfect_rank_four e6FixDNAll_proved S hp hpL hT hTp h1 i hr hc hnin
  · exact orbitCharElemPerfect_exc S hp hpL hT hTp h1 i hk


theorem exists_perfect_of_charElem_of_four_le (hK : ringChar K = ℓ) (hℓp : ℓ.Prime) (hq4 : 4 ≤ S.D.q)
    {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ) {a : Fin τ.rank → (AlgebraicClosure K)ˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    {k : ModGL τ (AlgebraicClosure K)} (hk : k ∈ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a})
    {m : ℕ} (hkm : k ^ ℓ ^ m = 1) :
    ∃ P ≤ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a}, ⁅P, P⁆ = P ∧ k ∈ P := by
  classical
  have hgood : ∀ O : Set.range (rationalRoots S.ρ (rootCharHom a)),
      ∃ P' : Subgroup (ModGL τ (AlgebraicClosure K)), ⁅P', P'⁆ = P' ∧
        P' ≤ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} ∧
        ∀ g ∈ rootSpan τ (AlgebraicClosure K) O.1, g ∈ S.D.model → (∃ n : ℕ, g ^ ℓ ^ n = 1) → g ∈ P' := by
    rintro ⟨_, i, rfl⟩
    have horb : ∃ P' : Subgroup (ModGL τ (AlgebraicClosure K)), ⁅P', P'⁆ = P' ∧
        P' ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
        ∀ g ∈ rootSpan τ (AlgebraicClosure K) (rationalRoots S.ρ (rootCharHom a) i), g ∈ S.D.model →
          (∃ n : ℕ, g ^ ℓ ^ n = 1) → g ∈ P' := by
      cases hkind : twistKind S.ρ (rootCharHom a) i with
      | inner => exact exists_perfect_orbit_of_comp S hK hℓp hT i (compCharElem_inner S hK hℓp hq4 hT i hkind)
      | suN =>
        exact exists_perfect_orbit_of_comp S hK hℓp hT i
          (compCharElem_suN_of_four_le S hK hℓp hq4 hp hT hap h1 i hkind)
      | twoD =>
        obtain ⟨P', hP'A, hP'perf, hP'⟩ := orbitCharElemPerfect_twoD_exc_any S hp hT hap h1 i (Or.inl hkind)
        rw [hK] at hP'
        exact ⟨P', hP'perf, le_rationalComponent_of_perfect S i hP'A hP'perf, hP'⟩
      | exc =>
        obtain ⟨P', hP'A, hP'perf, hP'⟩ := orbitCharElemPerfect_twoD_exc_any S hp hT hap h1 i (Or.inr hkind)
        rw [hK] at hP'
        exact ⟨P', hP'perf, le_rationalComponent_of_perfect S i hP'A hP'perf, hP'⟩
    obtain ⟨P', hP'perf, hP'R, hP'⟩ := horb
    exact ⟨P', hP'perf, hP'R.trans (langSubnormal_of_mem_torus S hT i).1, hP'⟩
  choose Pf hPfperf hPfle hPfmem using hgood
  exact ⟨⨆ O, Pf O, iSup_le hPfle, commutator_iSup_eq_charQ Pf hPfperf,
    mem_iSup_of_charElem_family S hK hℓp hp hpℓ hT hap Pf hPfmem hk hkm⟩

theorem charElem_mem_glaLayer_of_langSetup (hK : ringChar K = ℓ) (hℓp : ℓ.Prime) (hq4 : 4 ≤ S.D.q)
    {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ)
    {C : Type} [Group C] (ι : C →* ModGL τ (AlgebraicClosure K)) (hι : Function.Injective ι)
    (hrange : ι.range = S.Γ) (β : MulAut C) {a : Fin τ.rank → (AlgebraicClosure K)ˣ}
    (hβ : ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    {s : C} (hs : β s = s) {m : ℕ} (hsm : s ^ ℓ ^ m = 1) :
    s ∈ GLALayer (fixSubgroup β) := by
  classical
  have hL : PerfectInLayer β :=
    perfectInLayer_of_langSetup_of_prime S hp ι hι hrange β hβ hT hap h1 hTame
  have hfix : (fixSubgroup β).map ι = S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.map_fixSubgroup_eq_of_conj ι hι β _ hβ, hrange]
  have hιs : ι s ∈ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} := by
    rw [← hfix]
    exact ⟨s, mem_fixSubgroup.2 hs, rfl⟩
  have hιm : ι s ^ ℓ ^ m = 1 := by rw [← map_pow, hsm, map_one]
  obtain ⟨P, hPle, hPperf, hsP⟩ :=
    exists_perfect_of_charElem_of_four_le S hK hℓp hq4 hp hpℓ hT hap h1 hιs hιm
  have hPr : P ≤ ι.range := fun x hx => by
    rw [hrange]
    exact (Subgroup.mem_inf.1 (hPle hx)).1
  have hmap : (P.comap ι).map ι = P := Subgroup.map_comap_eq_self hPr
  have hperf : ⁅P.comap ι, P.comap ι⁆ = P.comap ι := by
    apply Subgroup.map_injective hι
    rw [Subgroup.map_commutator, hmap, hPperf]
  have hle : P.comap ι ≤ fixSubgroup β := by
    intro x hx
    have hx' : ι x ∈ (fixSubgroup β).map ι := by
      rw [hfix]
      exact hPle hx
    obtain ⟨y, hy, hyx⟩ := hx'
    rwa [hι hyx] at hy
  exact hL (P.comap ι) hle hperf hsP

end Lang

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256r

end

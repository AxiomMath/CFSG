module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcOrthHull
public import CFSG.ClassicalInvolution.Balance.LayerGenerationShortTwistedE6Frame

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

namespace CFSG.ClassicalInvolution.ModelFacts

variable (p e : ℕ) [Fact p.Prime]

abbrev betaTw : Fin (Tag.rank .E6) → ℤ := Pi.single (nd 1) 1

theorem rho_betaTw : rho (betaTw) = betaTw := by
  rw [betaTw, rho_single]
  congr 2

theorem rho_neg_betaTw : rho (-betaTw) = -betaTw := by
  rw [betaTw, rho_neg_single]
  congr 3

theorem isRoot_betaTw : IsRoot .E6 betaTw := isRoot_single _ _

noncomputable abbrev stdRankTw : Subgroup (twistedE6Group p e) :=
  twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (proj betaTw) ⊔
    twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (-proj betaTw)

noncomputable abbrev psiTw : twistedE6Group p e →* ModGL .E6 (GaloisField p (2 * e)) :=
  twistedE6Phi p e (GaloisField p (2 * e))

theorem psiTw_xFixed {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) (hfix : rho γ = γ)
    (c : GaloisField p (2 * e)) (hc : frobQ p e c = c) :
    psiTw p e (xFixed (frobQ p e) hγ hfix c hc) =
      pinnedX .E6 (GaloisField p (2 * e)) γ ((e6Sign γ : GaloisField p (2 * e)) * c) := by
  have h := twistedE6Phi_xFixed p e (GaloisField p (2 * e)) hγ hfix c hc
  exact h

theorem map_twistedRootGroup_le {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ)
    (hfix : rho γ = γ) :
    (twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (proj γ)).map (psiTw p e) ≤
      rootSubgroup .E6 (GaloisField p (2 * e)) γ := by
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨c, hc, hgc⟩ := (mem_twistedRootGroup_iff_of_fixed _ hγ rfl hfix g).1 hg
  have hg' : g = xFixed (frobQ p e) hγ hfix c hc := Subtype.ext hgc
  rw [hg', psiTw_xFixed]
  exact mem_rootSubgroup.2 ⟨_, rfl⟩

theorem map_stdRankTw_le :
    (stdRankTw p e).map (psiTw p e) ≤
      rootRankOneGroup .E6 (GaloisField p (2 * e)) betaTw := by
  rw [rootRankOneGroup_eq_sup isRoot_betaTw, stdRankTw, Subgroup.map_sup, ← map_neg proj betaTw]
  exact sup_le_sup (map_twistedRootGroup_le p e isRoot_betaTw rho_betaTw)
    (map_twistedRootGroup_le p e (IsRoot.neg isRoot_betaTw) rho_neg_betaTw)

section Sat

variable {k : Type} [Field k]

theorem nSL_eq_uSL_mul_vSL_mul_uSL (t : kˣ) :
    (nSL t : SL(2, k)) = uSL (t : k) * vSL (-((t⁻¹ : kˣ) : k)) * uSL (t : k) := by
  refine Subtype.ext ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem mem_closure_fixed_of_mem_slFixed (θ : k →+* k) {M : SL(2, k)} (hM : M ∈ slFixed k θ) :
    M ∈ Subgroup.closure {g : SL(2, k) | ∃ c, θ c = c ∧ (g = uSL c ∨ g = vSL c)} := by
  set C := Subgroup.closure {g : SL(2, k) | ∃ c, θ c = c ∧ (g = uSL c ∨ g = vSL c)} with hC
  have hu : ∀ c, θ c = c → uSL c ∈ C := fun c hc => Subgroup.subset_closure ⟨c, hc, Or.inl rfl⟩
  have hv : ∀ c, θ c = c → vSL c ∈ C := fun c hc => Subgroup.subset_closure ⟨c, hc, Or.inr rfl⟩
  have h1 : θ (1 : k) = 1 := map_one θ
  have hW : (WSL : SL(2, k)) ∈ C := by
    rw [WSL_eq_uSL_mul_vSL_mul_uSL]
    exact mul_mem (mul_mem (hu 1 h1) (hv (-1) (by rw [map_neg, h1]))) (hu 1 h1)
  have hH : ∀ t : kˣ, θ (t : k) = t → (HSL t : SL(2, k)) ∈ C := by
    intro t ht
    have hti : θ ((t⁻¹ : kˣ) : k) = ((t⁻¹ : kˣ) : k) := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, ht]
    have hn : (nSL t : SL(2, k)) ∈ C := by
      rw [nSL_eq_uSL_mul_vSL_mul_uSL]
      exact mul_mem (mul_mem (hu _ ht) (hv _ (by rw [map_neg, hti]))) (hu _ ht)
    have : (HSL t : SL(2, k)) = nSL t * WSL⁻¹ := by
      rw [nSL_eq_HSL_mul]
      group
    rw [this]
    exact mul_mem hn (inv_mem hW)
  have hfix := (mem_slFixed θ).1 hM
  by_cases h0 : (M : Matrix (Fin 2) (Fin 2) k) 1 0 = 0
  · have hdet := M.det_coe
    rw [Matrix.det_fin_two, h0, mul_zero, sub_zero] at hdet
    have h00 : (M : Matrix (Fin 2) (Fin 2) k) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
    have hM' : M = HSL (Units.mk0 _ h00) *
        uSL ((M : Matrix (Fin 2) (Fin 2) k) 0 1 / (M : Matrix (Fin 2) (Fin 2) k) 0 0) := by
      refine Subtype.ext ?_
      rw [Matrix.SpecialLinearGroup.coe_mul, coe_HSL, coe_uSL]
      exact sl_eq_of_lower_eq_zero' M h0 h00
    rw [hM']
    exact mul_mem (hH _ (by rw [Units.val_mk0]; exact hfix 0 0))
      (hu _ (by rw [map_div₀, hfix, hfix]))
  · have hγ : -(M : Matrix (Fin 2) (Fin 2) k) 1 0 ≠ 0 := neg_ne_zero.2 h0
    have hM' : M = uSL ((M : Matrix (Fin 2) (Fin 2) k) 0 0 / (M : Matrix (Fin 2) (Fin 2) k) 1 0) *
        WSL * HSL (Units.mk0 _ hγ) *
        uSL ((M : Matrix (Fin 2) (Fin 2) k) 1 1 / (M : Matrix (Fin 2) (Fin 2) k) 1 0) := by
      refine Subtype.ext ?_
      simp only [Matrix.SpecialLinearGroup.coe_mul, coe_HSL, coe_uSL, coe_WSL]
      exact sl_eq_of_lower_ne_zero' M h0
    rw [hM']
    exact mul_mem (mul_mem (mul_mem (hu _ (by rw [map_div₀, hfix, hfix])) hW)
      (hH _ (by rw [Units.val_mk0, map_neg, hfix]))) (hu _ (by rw [map_div₀, hfix, hfix]))

end Sat

section SatTw

theorem rootSL2_betaTw :
    rootSL2 .E6 (GaloisField p (2 * e)) betaTw =
      simpleRootSL2 .E6 (GaloisField p (2 * e)) (nd 1) := by
  ext A
  rw [rootSL2_apply]
  simp [pinnedWeyl, pinnedData_single]

theorem rho_nd_one : rhoPerm (nd 1) = nd 1 := by decide

theorem twistHom_simpleRootSL2 (θ : GaloisField p (2 * e) →+* GaloisField p (2 * e))
    (A : SL(2, GaloisField p (2 * e))) :
    twistHom TwistTag.E6 (GaloisField p (2 * e)) θ
        (simpleRootSL2 .E6 (GaloisField p (2 * e)) (nd 1) A) =
      simpleRootSL2 .E6 (GaloisField p (2 * e)) (nd 1) (Matrix.SpecialLinearGroup.map θ A) := by
  have key := MonoidHom.eq_of_eqOn_dense (sl2_closure_upper_lower (K := GaloisField p (2 * e)))
    (f := (twistHom TwistTag.E6 (GaloisField p (2 * e)) θ).comp
      (simpleRootSL2 .E6 (GaloisField p (2 * e)) (nd 1)))
    (g := (simpleRootSL2 .E6 (GaloisField p (2 * e)) (nd 1)).comp
      (Matrix.SpecialLinearGroup.map θ)) (by
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · change twistHom TwistTag.E6 _ θ (simpleRootSL2 .E6 _ (nd 1) (uSL c)) =
          simpleRootSL2 .E6 _ (nd 1) (Matrix.SpecialLinearGroup.map θ (uSL c))
        have : Matrix.SpecialLinearGroup.map θ (uSL c) = uSL (θ c) := by
          refine Subtype.ext ?_
          ext i j
          fin_cases i <;> fin_cases j <;> simp [coe_uSL]
        rw [this, simpleRootSL2_uSL, simpleRootSL2_uSL]
        have h1 := twistHom_xUnit TwistTag.E6 (GaloisField p (2 * e)) θ (nd 1) (c)
        rw [show TwistTag.E6.perm (nd 1) = nd 1 from rho_nd_one] at h1
        exact h1
      · change twistHom TwistTag.E6 _ θ (simpleRootSL2 .E6 _ (nd 1) (vSL c)) =
          simpleRootSL2 .E6 _ (nd 1) (Matrix.SpecialLinearGroup.map θ (vSL c))
        have : Matrix.SpecialLinearGroup.map θ (vSL c) = vSL (θ c) := by
          refine Subtype.ext ?_
          ext i j
          fin_cases i <;> fin_cases j <;> simp [coe_vSL]
        rw [this, simpleRootSL2_vSL, simpleRootSL2_vSL]
        have h1 := twistHom_yUnit TwistTag.E6 (GaloisField p (2 * e)) θ (nd 1) (c)
        rw [show TwistTag.E6.perm (nd 1) = nd 1 from rho_nd_one] at h1
        exact h1)
  exact DFunLike.congr_fun key A

theorem psiTw_eq (x : twistedE6Group p e) :
    psiTw p e x = e6IsogenyFixed (frobQ p e) x := by
  unfold psiTw twistedE6Phi
  simp only [Algebra.algebraMap_self]
  exact baseChangeGL_id (GaloisField p (2 * e)) (e6IsogenyFixed (frobQ p e) x)

theorem twistHom_psiTw (x : twistedE6Group p e) :
    twistHom TwistTag.E6 (GaloisField p (2 * e)) (frobQ p e) (psiTw p e x) = psiTw p e x := by
  rw [psiTw_eq, e6IsogenyFixed_apply]
  have h := e6IsogenyT_sigma (frobQ p e) (x : ↥(e6Data_valid.minGroup (GaloisField p (2 * e))))
  rw [(mem_fixedGroup (frobQ p e)).1 x.2] at h
  exact (congrArg Subtype.val h).symm

theorem sat_stdRankTw (hp2 : p ≠ 2) :
    rootRankOneGroup .E6 (GaloisField p (2 * e)) betaTw ⊓ (psiTw p e).range ≤
      (stdRankTw p e).map (psiTw p e) := by
  intro y hy
  obtain ⟨⟨A, hA⟩, x, hx⟩ := hy
  have hK : ringChar (GaloisField p (2 * e)) ≠ 2 := by
    rw [ringChar.eq (GaloisField p (2 * e)) p]
    exact hp2
  rw [rootSL2_betaTw] at hA
  have hAfix : Matrix.SpecialLinearGroup.map (frobQ p e) A = A := by
    apply simpleRootSL2_injective hK (nd 1)
    rw [← twistHom_simpleRootSL2 p e (frobQ p e) A, hA, ← hx, twistHom_psiTw]
  have hcl := mem_closure_fixed_of_mem_slFixed (frobQ p e) (hAfix : A ∈ slFixed _ (frobQ p e))
  have hle : Subgroup.closure {g : SL(2, GaloisField p (2 * e)) |
      ∃ c, frobQ p e c = c ∧ (g = uSL c ∨ g = vSL c)} ≤
      ((stdRankTw p e).map (psiTw p e)).comap
        (simpleRootSL2 .E6 (GaloisField p (2 * e)) (nd 1)) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨c, hc, rfl | rfl⟩
    · change simpleRootSL2 .E6 _ (nd 1) (uSL c) ∈ (stdRankTw p e).map (psiTw p e)
      have hε := e6Sign_mul_self (K := GaloisField p (2 * e)) betaTw
      have hfix : frobQ p e ((e6Sign betaTw : GaloisField p (2 * e)) * c) =
          (e6Sign betaTw : GaloisField p (2 * e)) * c := by
        rw [map_mul, map_intCast, hc]
      refine ⟨xFixed (frobQ p e) isRoot_betaTw rho_betaTw _ hfix,
        Subgroup.mem_sup_left (xFixed_mem _ isRoot_betaTw rho_betaTw _ hfix), ?_⟩
      rw [psiTw_xFixed, simpleRootSL2_uSL, ← mul_assoc, hε, one_mul]
      exact pinnedX_single .E6 _ (nd 1) c
    · change simpleRootSL2 .E6 _ (nd 1) (vSL c) ∈ (stdRankTw p e).map (psiTw p e)
      have hε := e6Sign_mul_self (K := GaloisField p (2 * e)) (-betaTw)
      have hfix : frobQ p e ((e6Sign (-betaTw) : GaloisField p (2 * e)) * c) =
          (e6Sign (-betaTw) : GaloisField p (2 * e)) * c := by
        rw [map_mul, map_intCast, hc]
      refine ⟨xFixed (frobQ p e) (IsRoot.neg isRoot_betaTw) rho_neg_betaTw _ hfix,
        Subgroup.mem_sup_right (by
          rw [← map_neg proj betaTw]
          exact xFixed_mem _ (IsRoot.neg isRoot_betaTw) rho_neg_betaTw _ hfix),
        ?_⟩
      rw [psiTw_xFixed, simpleRootSL2_vSL, ← mul_assoc, hε, one_mul]
      exact pinnedX_neg_single .E6 _ (nd 1) c
  have := hle hcl
  rw [← hA]
  exact this

end SatTw

section Main

theorem psiTw_mem_adjointGroup (x : twistedE6Group p e) :
    psiTw p e x ∈ adjointGroup .E6 (GaloisField p (2 * e)) := by
  rw [psiTw_eq, e6IsogenyFixed_apply]
  exact (e6IsogenyT _ _).2

theorem exists_sign_of_mem_twistedE6SignGroup {c : twistedE6Group p e}
    (hc : c ∈ CFSG.ClassicalInvolution.Balance.Bootstrap.twistedE6SignGroup 0 p e) :
    ∃ b : Fin (Tag.rank .E6) → (GaloisField p (2 * e))ˣ, (∀ i, b i = 1 ∨ b i = -1) ∧
      psiTw p e c = rootDiagUnit .E6 b := by
  obtain ⟨b₄, hb₄, hcb⟩ := hc
  classical
  let b' : Fin (Tag.rank .F4) → (GaloisField p (2 * e))ˣ := fun j => if b₄ j = 1 then 1 else -1
  have hb' : ∀ j, b' j = 1 ∨ b' j = -1 := fun j => by
    by_cases h : b₄ j = 1 <;> simp [b', h]
  have hmap : ∀ j, Units.map (algebraMap (GaloisField p (2 * e))
      (AlgebraicClosure (GaloisField p (2 * e)))).toMonoidHom (b' j) = b₄ j := fun j => by
    by_cases h : b₄ j = 1
    · simp [b', h]
    · have h' : b₄ j = -1 := (hb₄ j).resolve_left h
      have hne : (-1 : (AlgebraicClosure (GaloisField p (2 * e)))ˣ) ≠ 1 := fun h1 => h (h'.trans h1)
      have hne' : (-1 : (GaloisField p (2 * e))ˣ) ≠ 1 := fun h1 => hne (by
        have := congrArg (Units.map (algebraMap (GaloisField p (2 * e))
          (AlgebraicClosure (GaloisField p (2 * e)))).toMonoidHom) h1
        simpa using this)
      have e1 : b' j = -1 := by simp [b', h]
      rw [e1, h']
      exact Units.ext (by simp)
  refine ⟨fun l => b' (orbitMap l), fun l => hb' _, ?_⟩
  apply baseChangeGL_injective (algebraMap (GaloisField p (2 * e))
    (AlgebraicClosure (GaloisField p (2 * e))))
  rw [baseChangeGL_rootDiagUnit]
  have hΦ : baseChangeGL (algebraMap (GaloisField p (2 * e))
      (AlgebraicClosure (GaloisField p (2 * e)))) (psiTw p e c) =
      twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) c := by
    rw [psiTw_eq]
    rfl
  have hrhs : rootDiagUnit TwistTag.E6.tag (fun l => b₄ (orbitMap l)) =
      rootDiagUnit .E6 (fun i => Units.map (algebraMap (GaloisField p (2 * e))
        (AlgebraicClosure (GaloisField p (2 * e)))).toMonoidHom (b' (orbitMap i))) := by
    congr 1
    funext l
    exact (hmap _).symm
  exact hΦ.trans (hcb.trans hrhs)

variable {p e} in
theorem orthBranch_twistedE6 (hadm : StatedLieAdmissible .twistedE6 0 p e) :
    OrthBranch p .twistedE6 0 e := by
  intro hp2 hq
  have hq2 : 5 ≤ p ^ (2 * e) := by
    rw [pow_mul']
    nlinarith
  have hθ : IsLongRoot .E6 betaTw :=
    isLongRoot_of_isRoot_of_simplyLaced (Or.inl rfl) isRoot_betaTw
  have hlongD : Generic.IsLongestRoot (Generic.modelUniv .twistedE6 0 p e Fact.out).D
      (proj betaTw) := isLongestRoot_twistedDatum_proj (frobQ p e) isRoot_betaTw rho_betaTw
  refine (orthBranch_of_hullEmbedding (t := .twistedE6) (τ := .E6) (f := 2 * e) hp2 hq hq2
    trivial (by decide) (by decide) (by decide) hadm (psiTw p e) (fun x => ?_)
    (ker_twistedE6Phi_le_center p e (GaloisField p (2 * e)))
    (CFSG.ClassicalInvolution.Balance.Bootstrap.twistedE6SignGroup 0 p e)
    (fun c hc => exists_sign_of_mem_twistedE6SignGroup p e hc)
    (CFSG.ClassicalInvolution.Balance.Bootstrap.twistedE6_pairFrame hadm hp2)
    (fundamentalSingleClass .twistedE6 0 p e Fact.out trivial hadm (by decide) (by decide))
    (Rθ := stdRankTw p e) ⟨1, proj betaTw, Or.inl hlongD, (Generic.conjSub_one _).symm⟩ hθ
    (map_stdRankTw_le p e) (sat_stdRankTw p e hp2)
    fun _ γ hγ _ => isLongRoot_of_isRoot_of_simplyLaced (Or.inl rfl) hγ.1) hp2 hq
  exact psiTw_mem_adjointGroup p e x

end Main

end CFSG.ClassicalInvolution.ModelFacts

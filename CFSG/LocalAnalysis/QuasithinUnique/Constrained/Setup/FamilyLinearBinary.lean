module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.GH74.Exceptional.LinearFourTwo

public section

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
  Module CFSG.QuasithinUnique.Setup.X6

section General

variable {K : Type*} [Field K] {n : ℕ}

theorem mem_stabilizer_flagSpace_of_normal {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ n)
    (hN : (flagStabilizer n K I).Normal) {d : ℕ} (hd : d ∈ I) (hdn : d < n) (hd1 : 1 ≤ d)
    (g : Matrix.SpecialLinearGroup (Fin n) K) : g ∈ stabilizer (flagSpace n K d) := by
  have hQ : ∀ q ∈ flagStabilizer n K I, ∀ v ∈ flagSpace n K d,
      (q : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ flagSpace n K d := by
    intro q hq v hv
    have h := mem_stabilizer.1 (mem_flagStabilizer.1 hq d hd)
    have h' : (q : Matrix (Fin n) (Fin n) K) *ᵥ v ∈
        (flagSpace n K d).map (mulVecLin (q : Matrix (Fin n) (Fin n) K)) := ⟨v, hv, rfl⟩
    rwa [h] at h'
  have hinv : ∀ q ∈ flagStabilizer n K I,
      ∀ v ∈ (flagSpace n K d).map (mulVecLin (g : Matrix (Fin n) (Fin n) K)),
        (q : Matrix (Fin n) (Fin n) K) *ᵥ v ∈
          (flagSpace n K d).map (mulVecLin (g : Matrix (Fin n) (Fin n) K)) := by
    rintro q hq _ ⟨v, hv, rfl⟩
    have hq' : g⁻¹ * q * g ∈ flagStabilizer n K I := by
      have := hN.conj_mem q hq g⁻¹
      simpa using this
    refine ⟨((g⁻¹ * q * g : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v,
      hQ _ hq' v hv, ?_⟩
    have e : (g : Matrix (Fin n) (Fin n) K) *
        ((g⁻¹ * q * g : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (q : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) :=
      (Matrix.SpecialLinearGroup.coe_mul g (g⁻¹ * q * g)).symm.trans
        ((congrArg (fun M : Matrix.SpecialLinearGroup (Fin n) K => (M : Matrix (Fin n) (Fin n) K))
          (show g * (g⁻¹ * q * g) = q * g by group)).trans (Matrix.SpecialLinearGroup.coe_mul q g))
    rw [mulVecLin_apply, mulVecLin_apply, mulVec_mulVec, e, ← mulVec_mulVec]
  have hfin : finrank K ((flagSpace n K d).map (mulVecLin (g : Matrix (Fin n) (Fin n) K))) = d := by
    rw [show finrank K ((flagSpace n K d).map (mulVecLin (g : Matrix (Fin n) (Fin n) K))) =
      finrank K (flagSpace n K d) from
        LinearEquiv.finrank_map_eq (Matrix.SpecialLinearGroup.toLin' g) _,
      finrank_flagSpace hdn.le]
  rcases ((subflag_stabilizer_generation (K := K) (n := n) I).2.1 _).1 hinv with
    h | h | ⟨i, hiI, h⟩
  · rw [h, finrank_bot] at hfin
    omega
  · rw [h, finrank_top, finrank_fin_fun] at hfin
    omega
  · rw [h, finrank_flagSpace (hI i hiI)] at hfin
    have hid : i = d := hfin
    rw [hid] at h
    exact mem_stabilizer.2 h

theorem not_normal_flagStabilizer {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ n) {d : ℕ} (hd : d ∈ I)
    (hd1 : 1 ≤ d) (hdn : d < n) : ¬ (flagStabilizer n K I).Normal := by
  intro hN
  have hgstab := mem_stabilizer_flagSpace_of_normal hI hN hd hdn hd1 (reflection n K d hd1 hdn)
  have hr := ((subflag_stabilizer_generation (K := K) (n := n) ({d} : Set ℕ)).2.2 d hd1 hdn).1
    (mem_flagStabilizer.2 fun j hj => by rw [Set.mem_singleton_iff.1 hj]; exact hgstab)
  exact hr (Set.mem_singleton d)

theorem flagStabilizer_sup_eq_top (hn : 4 ≤ n) :
    flagStabilizer n K {1, n - 1} ⊔ flagStabilizer n K {2, n - 2} = ⊤ := by
  set A := flagStabilizer n K {1, n - 1} ⊔ flagStabilizer n K {2, n - 2} with hA
  have hBA : upperTriangular n K ≤ A :=
    (upperTriangular_le_flagStabilizer (K := K) (n := n) {1, n - 1}).trans le_sup_left
  obtain ⟨hAeq, -⟩ := borel_overgroups A hBA
  have hcuts : borelOvergroupCuts A = ∅ := by
    ext i
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hi, hin, hnot⟩
    apply hnot
    by_cases h1 : i ∈ ({1, n - 1} : Set ℕ)
    · have h2 : i ∉ ({2, n - 2} : Set ℕ) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 ⊢
        omega
      exact Subgroup.mem_sup_right
        (((subflag_stabilizer_generation (K := K) (n := n) {2, n - 2}).2.2 i hi hin).2 h2)
    · exact Subgroup.mem_sup_left
        (((subflag_stabilizer_generation (K := K) (n := n) {1, n - 1}).2.2 i hi hin).2 h1)
  rw [hAeq, hcuts]
  exact flagStabilizer_empty n K

theorem finrank_map_mulVecLin_gl (A : GL (Fin n) K) (W : Submodule K (Fin n → K)) :
    finrank K (W.map (mulVecLin (A : Matrix (Fin n) (Fin n) K))) = finrank K W := by
  have hinj : Function.Injective (mulVecLin (A : Matrix (Fin n) (Fin n) K)) :=
    Matrix.mulVec_injective_iff_isUnit.2 A.isUnit
  exact (Submodule.equivMapOfInjective _ hinj W).finrank_eq.symm

end General

section BinaryField

variable {n : ℕ}

theorem scalars_zmod_two (n : ℕ) : scalars n (ZMod 2) = ⊥ := by
  refine eq_bot_iff.2 ?_
  rintro A ⟨c, -, hA⟩
  rw [Subgroup.mem_bot]
  have hc : c = 1 := Subsingleton.elim c 1
  ext i j
  rw [hA, hc]
  simp

theorem proj_injective_zmod_two (n : ℕ) : Function.Injective (proj n (ZMod 2)) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_proj, scalars_zmod_two]

@[expose] noncomputable def projEquiv (n : ℕ) :
    Matrix.SpecialLinearGroup (Fin n) (ZMod 2) ≃* projectiveSL n (ZMod 2) :=
  MulEquiv.ofBijective (proj n (ZMod 2)) ⟨proj_injective_zmod_two n, proj_surjective n (ZMod 2)⟩

theorem center_projectiveSL_zmod_two (n : ℕ) :
    Subgroup.center (projectiveSL n (ZMod 2)) = ⊥ := by
  have h := Subgroup.map_center_eq (projEquiv n)
  have hc : Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) = ⊥ := by
    rw [← scalars_eq_center]
    exact scalars_zmod_two n
  rw [hc, Subgroup.map_bot] at h
  exact h.symm

theorem isSylowOf_projUnitriangular (hn : 1 ≤ n) :
    CFSG.ABGLocalTools.IsSylowOf 2 (projUnitriangular n (ZMod 2)) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := exists_sylow_projUnitriangular (K := ZMod 2) 2 hn
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨le_top, ?_, ?_⟩
  · rw [← hQ]
    exact Q.isPGroup'
  · rw [Subgroup.relIndex_top_right, ← hQ]
    exact Q.not_dvd_index

theorem map_proj_flagStabilizer_pair (a b : ℕ) :
    (flagStabilizer n (ZMod 2) {a, b}).map (proj n (ZMod 2)) =
      projStabilizer (flagSpace n (ZMod 2) a) ⊓ projStabilizer (flagSpace n (ZMod 2) b) := by
  have h : flagStabilizer n (ZMod 2) {a, b} =
      stabilizer (flagSpace n (ZMod 2) a) ⊓ stabilizer (flagSpace n (ZMod 2) b) := by
    ext g
    rw [mem_flagStabilizer, Subgroup.mem_inf]
    simp
  rw [h, Subgroup.map_inf _ _ _ (proj_injective_zmod_two n)]
  rfl

theorem coordImage_zmod_two (σ : ZMod 2 ≃+* ZMod 2) (W : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    coordImage σ W = W := by
  have hσ : σ = RingEquiv.refl _ := Subsingleton.elim _ _
  subst hσ
  ext v
  simp [mem_coordImage]

theorem invariant_of_projUnitriangular_le {W : Submodule (ZMod 2) (Fin n → ZMod 2)}
    (h : projUnitriangular n (ZMod 2) ≤ projStabilizer W) :
    ∀ u ∈ unitriangular n (ZMod 2), ∀ v ∈ W,
      (u : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v ∈ W := by
  intro u hu v hv
  obtain ⟨s, hs, hsu⟩ := h (Subgroup.mem_map_of_mem _ hu)
  have hsu' : s = u := proj_injective_zmod_two n hsu
  rw [hsu'] at hs
  have h2 := mem_stabilizer.1 hs
  have h3 : (u : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v ∈
      W.map (mulVecLin (u : Matrix (Fin n) (Fin n) (ZMod 2))) := ⟨v, hv, rfl⟩
  rwa [h2] at h3

theorem projStabilizer_eq_of_projUnitriangular_le {W : Submodule (ZMod 2) (Fin n → ZMod 2)}
    (h : projUnitriangular n (ZMod 2) ≤ projStabilizer W) :
    projStabilizer W = projStabilizer (flagSpace n (ZMod 2) (finrank (ZMod 2) W)) := by
  obtain ⟨m, hm, hW⟩ := eq_flagSpace_of_invariant (invariant_of_projUnitriangular_le h)
  have hfin : finrank (ZMod 2) W = m := by rw [hW, finrank_flagSpace hm]
  rw [hfin, ← hW]

theorem map_toMonoidHom_mul {G : Type*} [Group G] (α β : MulAut G) (H : Subgroup G) :
    H.map (α * β).toMonoidHom = (H.map β.toMonoidHom).map α.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem automorphism_flag_dichotomy (hn : 3 ≤ n) (α : MulAut (projectiveSL n (ZMod 2)))
    (hα : (projUnitriangular n (ZMod 2)).map α.toMonoidHom = projUnitriangular n (ZMod 2)) :
    (∀ d ≤ n, (projStabilizer (flagSpace n (ZMod 2) d)).map α.toMonoidHom =
        projStabilizer (flagSpace n (ZMod 2) d)) ∨
      (∀ d ≤ n, (projStabilizer (flagSpace n (ZMod 2) d)).map α.toMonoidHom =
        projStabilizer (flagSpace n (ZMod 2) (n - d))) := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := ZMod 2) (n := n) hn
  obtain ⟨A, σ, ε, hε, hαeq⟩ := hgen α
  have htrans := standard_automorphism_transport (K := ZMod 2) (n := n)
  have hUd : ∀ d : ℕ, projUnitriangular n (ZMod 2) ≤
      projStabilizer (flagSpace n (ZMod 2) d) := by
    intro d
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u, mem_flagStabilizer.1 (upperTriangular_le_flagStabilizer (K := ZMod 2) (n := n) {d}
      (unitriangular_le_upperTriangular n _ hu)) d (Set.mem_singleton d), rfl⟩
  have hgenl : ∀ (d : ℕ) (W' : Submodule (ZMod 2) (Fin n → ZMod 2)),
      (projStabilizer (flagSpace n (ZMod 2) d)).map α.toMonoidHom = projStabilizer W' →
      (projStabilizer (flagSpace n (ZMod 2) d)).map α.toMonoidHom =
        projStabilizer (flagSpace n (ZMod 2) (finrank (ZMod 2) W')) := by
    intro d W' h
    rw [h]
    exact projStabilizer_eq_of_projUnitriangular_le
      (hα.symm.le.trans ((Subgroup.map_mono (hUd d)).trans h.le))
  have h7 : ∀ (B : GL (Fin n) (ZMod 2)) (W : Submodule (ZMod 2) (Fin n → ZMod 2)),
      (projStabilizer W).map (conjAut n (ZMod 2) B).toMonoidHom =
        projStabilizer (W.map (mulVecLin (B : Matrix (Fin n) (Fin n) (ZMod 2)))) :=
    fun B W => htrans.2.2.2.2.2.2.1 B W
  have h8 : ∀ (τ : ZMod 2 ≃+* ZMod 2) (W : Submodule (ZMod 2) (Fin n → ZMod 2)),
      (projStabilizer W).map (fieldAut n (ZMod 2) τ).toMonoidHom = projStabilizer W := by
    intro τ W
    have := htrans.2.2.2.2.2.2.2.1 τ W
    rw [coordImage_zmod_two] at this
    exact this
  have h9 : ∀ W : Submodule (ZMod 2) (Fin n → ZMod 2),
      (projStabilizer W).map (dualAut n (ZMod 2)).toMonoidHom = projStabilizer (dotOrth W) :=
    fun W => htrans.2.2.2.2.2.2.2.2.1 W
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · left
    have hα' : α = conjAut n (ZMod 2) A * fieldAut n (ZMod 2) σ := by
      rw [hαeq, pow_zero, mul_one]
    have hmap : ∀ P : Subgroup (projectiveSL n (ZMod 2)), P.map α.toMonoidHom =
        (P.map (fieldAut n (ZMod 2) σ).toMonoidHom).map (conjAut n (ZMod 2) A).toMonoidHom := by
      intro P
      rw [hα', map_toMonoidHom_mul]
    intro d hd
    have h1 : (projStabilizer (flagSpace n (ZMod 2) d)).map α.toMonoidHom =
        projStabilizer ((flagSpace n (ZMod 2) d).map
          (mulVecLin (A : Matrix (Fin n) (Fin n) (ZMod 2)))) := by
      rw [hmap, h8, h7]
    rw [hgenl d _ h1, finrank_map_mulVecLin_gl, finrank_flagSpace hd]
  · right
    have hα' : α = conjAut n (ZMod 2) A * fieldAut n (ZMod 2) σ * dualAut n (ZMod 2) := by
      rw [hαeq, pow_one]
    have hmap : ∀ P : Subgroup (projectiveSL n (ZMod 2)), P.map α.toMonoidHom =
        ((P.map (dualAut n (ZMod 2)).toMonoidHom).map
          (fieldAut n (ZMod 2) σ).toMonoidHom).map (conjAut n (ZMod 2) A).toMonoidHom := by
      intro P
      rw [hα', map_toMonoidHom_mul, map_toMonoidHom_mul]
    intro d hd
    have h1 : (projStabilizer (flagSpace n (ZMod 2) d)).map α.toMonoidHom =
        projStabilizer ((dotOrth (flagSpace n (ZMod 2) d)).map
          (mulVecLin (A : Matrix (Fin n) (Fin n) (ZMod 2)))) := by
      rw [hmap, h9, h8, h7]
    rw [hgenl d _ h1, finrank_map_mulVecLin_gl, finrank_dotOrth, finrank_flagSpace hd]

theorem pair_invariant (hn : 4 ≤ n) (α : MulAut (projectiveSL n (ZMod 2)))
    (hα : (projUnitriangular n (ZMod 2)).map α.toMonoidHom = projUnitriangular n (ZMod 2)) :
    (projStabilizer (flagSpace n (ZMod 2) 1) ⊓
        projStabilizer (flagSpace n (ZMod 2) (n - 1))).map α.toMonoidHom =
      projStabilizer (flagSpace n (ZMod 2) 1) ⊓ projStabilizer (flagSpace n (ZMod 2) (n - 1)) ∧
    (projStabilizer (flagSpace n (ZMod 2) 2) ⊓
        projStabilizer (flagSpace n (ZMod 2) (n - 2))).map α.toMonoidHom =
      projStabilizer (flagSpace n (ZMod 2) 2) ⊓ projStabilizer (flagSpace n (ZMod 2) (n - 2)) := by
  rcases automorphism_flag_dichotomy (by omega) α hα with h | h
  · refine ⟨?_, ?_⟩
    · rw [Subgroup.map_inf _ _ _ α.injective, h 1 (by omega), h (n - 1) (by omega)]
    · rw [Subgroup.map_inf _ _ _ α.injective, h 2 (by omega), h (n - 2) (by omega)]
  · refine ⟨?_, ?_⟩
    · rw [Subgroup.map_inf _ _ _ α.injective, h 1 (by omega), h (n - 1) (by omega),
        show n - (n - 1) = 1 by omega, inf_comm]
    · rw [Subgroup.map_inf _ _ _ α.injective, h 2 (by omega), h (n - 2) (by omega),
        show n - (n - 2) = 2 by omega, inf_comm]

theorem not_normal_pair {a b : ℕ} (ha : a ≤ n) (hb : b ≤ n) (ha1 : 1 ≤ a) (han : a < n) :
    ¬ (projStabilizer (flagSpace n (ZMod 2) a) ⊓
      projStabilizer (flagSpace n (ZMod 2) b)).Normal := by
  intro hN
  rw [← map_proj_flagStabilizer_pair] at hN
  have h := hN.comap (proj n (ZMod 2))
  rw [Subgroup.comap_map_eq_self_of_injective (proj_injective_zmod_two n)] at h
  refine not_normal_flagStabilizer (K := ZMod 2) (I := {a, b}) ?_ (Set.mem_insert a {b}) ha1 han h
  intro i hi
  rcases hi with rfl | hi
  · exact ha
  · rw [Set.mem_singleton_iff.1 hi]
    exact hb

theorem twoGeneratingSylowOvergroups_projectiveSL_zmod_two (hn : 4 ≤ n) :
    TwoGeneratingSylowOvergroups (projectiveSL n (ZMod 2)) := by
  intro D hD R hR
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgen : (projStabilizer (flagSpace n (ZMod 2) 1) ⊓
        projStabilizer (flagSpace n (ZMod 2) (n - 1))) ⊔
      (projStabilizer (flagSpace n (ZMod 2) 2) ⊓
        projStabilizer (flagSpace n (ZMod 2) (n - 2))) = ⊤ := by
    rw [← map_proj_flagStabilizer_pair, ← map_proj_flagStabilizer_pair, ← Subgroup.map_sup,
      flagStabilizer_sup_eq_top hn, Subgroup.map_top_of_surjective _ (proj_surjective n (ZMod 2))]
  exact automorphism_invariant_generating_Sylow_overgroups_lift (center_projectiveSL_zmod_two n)
    (isSylowOf_projUnitriangular (by omega)) (not_normal_pair (by omega) (by omega) le_rfl
      (by omega)) (not_normal_pair (by omega) (by omega) (by omega) (by omega)) hgen
    (fun α hα => pair_invariant hn α hα) hD (isSylowTwoOf_iff_isSylowOf.1 hR)

theorem twoGeneratingSylowOvergroups_binary_linear (hn : 4 ≤ n) :
    TwoGeneratingSylowOvergroups (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
  TwoGeneratingSylowOvergroups.of_mulEquiv (projEquiv n).symm
    (twoGeneratingSylowOvergroups_projectiveSL_zmod_two hn)

@[expose] noncomputable def slEquivGL (n : ℕ) :
    Matrix.SpecialLinearGroup (Fin n) (ZMod 2) ≃* GL (Fin n) (ZMod 2) :=
  MulEquiv.ofBijective
    (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) →* _)
    ⟨Matrix.SpecialLinearGroup.toGL_injective, fun A => by
      have hdet : (A : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1 := by
        have h1 : Matrix.GeneralLinearGroup.det A = 1 := Subsingleton.elim _ _
        have h2 := congrArg (fun u : (ZMod 2)ˣ => (u : ZMod 2)) h1
        simpa using h2
      refine ⟨⟨(A : Matrix (Fin n) (Fin n) (ZMod 2)), hdet⟩, ?_⟩
      apply Units.ext
      rfl⟩

end BinaryField

theorem twoGeneratingSylowOvergroups_alt_eight :
    TwoGeneratingSylowOvergroups (alternatingGroup (Fin 8)) :=
  TwoGeneratingSylowOvergroups.of_mulEquiv
    ((slEquivGL 4).trans CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.symm)
    (twoGeneratingSylowOvergroups_binary_linear (n := 4) le_rfl)

end CFSG.QuasithinUnique.Setup.Family

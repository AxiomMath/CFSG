module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderNat
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.Subnormal
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Quasithin.H13.L32AC44b
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF Module Matrix
open scoped MatrixGroups

theorem NatQuot.exists_of_section {G : Type} [Group G] {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {L : Subgroup G} {F : Type} [Field F]
    {r : ℕ} (hperf : commutator ↥L = ⊤) (Mat : ↥L →* GL (Fin r) F)
    (hMat : Function.Injective Mat)
    (hirr : ∀ S : AddSubgroup (Fin r → F),
      (∀ (l : ↥L), ∀ u ∈ S, (Mat l : Matrix (Fin r) (Fin r) F) *ᵥ u ∈ S) → S = ⊥ ∨ S = ⊤)
    (hnt : ∃ l : ↥L, Mat l ≠ 1)
    {W : Submodule (ZMod 2) V} (hWL : ∀ l ∈ L, ∀ v ∈ W, ρ l v ∈ W)
    (p : ↥W →+ (Fin r → F)) (hp : Function.Surjective p)
    (hpL : ∀ (l : ↥L) (v : ↥W),
      p ⟨ρ l v, hWL l l.2 v v.2⟩ = (Mat l : Matrix (Fin r) (Fin r) F) *ᵥ p v)
    (hker : ∀ v : ↥W, p v = 0 ↔ ∀ l ∈ L, ρ l v = v)
    {A : Subgroup G} (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hAW : ∀ a ∈ A, ∀ v ∈ W, ρ a v ∈ W) :
    ∃ N : NatQuot ρ L F r, N.Mat = Mat ∧
      (∀ v ∈ N.I, v ∈ Submodule.span (ZMod 2) {w | ∃ l ∈ L, ∃ x ∈ N.I, w = ρ l x - x}) ∧
      ∀ a ∈ A, ∀ v ∈ N.I, ρ a v ∈ N.I := by
  classical
  let I : Submodule (ZMod 2) V :=
    Submodule.span (ZMod 2) {w | ∃ l ∈ L, ∃ x ∈ W, w = ρ l x - x}
  have hIW : I ≤ W := by
    refine Submodule.span_le.mpr ?_
    rintro w ⟨l, hl, x, hx, rfl⟩
    exact W.sub_mem (hWL l hl x hx) hx
  have hI_inv : ∀ l ∈ L, ∀ v ∈ I, ρ l v ∈ I := by
    intro l hl v hv
    have hle : I ≤ Submodule.comap (ρ l) I := by
      refine Submodule.span_le.mpr ?_
      rintro w ⟨m, hm, x, hx, rfl⟩
      change ρ l (ρ m x - x) ∈ I
      have hgen1 : ρ (l * m) x - x ∈ I :=
        Submodule.subset_span ⟨l * m, L.mul_mem hl hm, x, hx, rfl⟩
      have hgen2 : ρ l x - x ∈ I :=
        Submodule.subset_span ⟨l, hl, x, hx, rfl⟩
      have hEq : ρ l (ρ m x - x) = (ρ (l * m) x - x) - (ρ l x - x) := by
        rw [map_sub]
        have hmul : ρ l (ρ m x) = ρ (l * m) x := by
          rw [← Module.End.mul_apply, ← map_mul]
        rw [hmul]
        abel
      rw [hEq]
      exact I.sub_mem hgen1 hgen2
    exact hle hv
  have hI_A : ∀ a ∈ A, ∀ v ∈ I, ρ a v ∈ I := by
    intro a ha v hv
    have hle : I ≤ Submodule.comap (ρ a) I := by
      refine Submodule.span_le.mpr ?_
      rintro w ⟨m, hm, x, hx, rfl⟩
      change ρ a (ρ m x - x) ∈ I
      have hmem : a * m * a⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hAN ha) m).mp hm
      have hx' : ρ a x ∈ W := hAW a ha x hx
      have hgen : ρ (a * m * a⁻¹) (ρ a x) - ρ a x ∈ I :=
        Submodule.subset_span ⟨a * m * a⁻¹, hmem, ρ a x, hx', rfl⟩
      have hEq : ρ a (ρ m x - x) = ρ (a * m * a⁻¹) (ρ a x) - ρ a x := by
        rw [map_sub]
        congr 1
        have h1 : ρ a (ρ m x) = ρ (a * m) x := by
          rw [← Module.End.mul_apply, ← map_mul]
        have h2 : ρ (a * m) x = ρ (a * m * a⁻¹) (ρ a x) := by
          have hconj : (a * m * a⁻¹) * a = a * m := by group
          calc ρ (a * m) x = ρ ((a * m * a⁻¹) * a) x := by rw [hconj]
            _ = ρ (a * m * a⁻¹) (ρ a x) := by rw [map_mul, Module.End.mul_apply]
        rw [h1, h2]
      rw [hEq]
      exact hgen
    exact hle hv
  let J : Submodule (ZMod 2) V :=
    Submodule.span (ZMod 2) {w | ∃ l ∈ L, ∃ x ∈ I, w = ρ l x - x}
  have hJI : J ≤ I := by
    refine Submodule.span_le.mpr ?_
    rintro w ⟨l, hl, x, hx, rfl⟩
    exact I.sub_mem (hI_inv l hl x hx) hx
  have hcomm_triv : ∀ (x : ↥W) (l : ↥L), ρ (l : G) (x : V) - (x : V) ∈ J := by
    intro x l
    let φ : ↥L →* Multiplicative (V ⧸ J) :=
      { toFun := fun l => Multiplicative.ofAdd
          (Submodule.Quotient.mk (ρ (l : G) (x : V) - (x : V)))
        map_one' := by simp
        map_mul' := fun a b => by
          rw [← ofAdd_add]
          congr 1
          rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
          have hy : ρ (b : G) (x : V) - (x : V) ∈ I :=
            Submodule.subset_span ⟨(b : G), b.2, (x : V), x.2, rfl⟩
          have hgen : ρ (a : G) (ρ (b : G) (x : V) - (x : V)) -
              (ρ (b : G) (x : V) - (x : V)) ∈ J :=
            Submodule.subset_span ⟨(a : G), a.2, ρ (b : G) (x : V) - (x : V), hy, rfl⟩
          have hEq : ρ (a : G) (ρ (b : G) (x : V) - (x : V)) -
                (ρ (b : G) (x : V) - (x : V)) =
              ρ ((a * b : ↥L) : G) (x : V) - (x : V) -
                ((ρ (a : G) (x : V) - (x : V)) +
                  (ρ (b : G) (x : V) - (x : V))) := by
            rw [map_sub]
            have hmul : ρ (a : G) (ρ (b : G) (x : V)) =
                ρ ((a * b : ↥L) : G) (x : V) := by
              rw [← Module.End.mul_apply, ← map_mul]
              rfl
            rw [hmul]
            abel
          rw [← hEq]
          exact hgen }
    have hkerφ := Abelianization.commutator_subset_ker φ
    rw [hperf] at hkerφ
    have hφ1 : φ l = 1 := hkerφ (Subgroup.mem_top l)
    have h0 : (Submodule.Quotient.mk (ρ (l : G) (x : V) - (x : V)) : V ⧸ J) = 0 :=
      ofAdd_eq_one.mp hφ1
    exact (Submodule.Quotient.mk_eq_zero (p := J)).mp h0
  have hI_comm : ∀ v ∈ I, v ∈ J := by
    refine Submodule.span_le.mpr ?_
    rintro w ⟨l, hl, x, hx, rfl⟩
    exact hcomm_triv ⟨x, hx⟩ ⟨l, hl⟩
  let π : ↥I →+ (Fin r → F) :=
    { toFun := fun v => p ⟨(v : V), hIW v.2⟩
      map_zero' := by
        have h0 : (⟨((0 : ↥I) : V), hIW (0 : ↥I).2⟩ : ↥W) = 0 := Subtype.ext rfl
        rw [h0]
        exact map_zero p
      map_add' := fun v w => by
        have h : (⟨((v + w : ↥I) : V), hIW (v + w).2⟩ : ↥W) =
            (⟨(v : V), hIW v.2⟩ : ↥W) + ⟨(w : V), hIW w.2⟩ := by
          ext
          rfl
        rw [h, map_add] }
  have hS_inv : ∀ l : ↥L, ∀ u ∈ π.range,
      (Mat l : Matrix (Fin r) (Fin r) F) *ᵥ u ∈ π.range := by
    rintro l u ⟨v, rfl⟩
    refine ⟨⟨ρ (l : G) (v : V), hI_inv (l : G) l.2 (v : V) v.2⟩, ?_⟩
    have h := hpL l ⟨v, hIW v.2⟩
    have hsub : (⟨ρ (l : G) (v : V), hWL (l : G) l.2 (v : V) (hIW v.2)⟩ : ↥W) =
        (⟨ρ (l : G) (v : V),
          hIW (hI_inv (l : G) l.2 (v : V) v.2)⟩ : ↥W) := by
      ext
      rfl
    rw [hsub] at h
    simpa [π] using h
  have hnotbot : π.range ≠ ⊥ := by
    intro hbot
    obtain ⟨l, hl⟩ := hnt
    have hdiff : ∃ u : Fin r → F,
        (Mat l : Matrix (Fin r) (Fin r) F) *ᵥ u ≠ u := by
      by_contra h
      push Not at h
      apply hl
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      have hM : (Mat l : Matrix (Fin r) (Fin r) F) = 1 := by
        rw [Matrix.ext_iff_mulVec]
        intro u
        simpa using h u
      simpa using congrArg (fun M : Matrix (Fin r) (Fin r) F => M i j) hM
    obtain ⟨u, hu⟩ := hdiff
    obtain ⟨x, hx⟩ := hp u
    let w : ↥I := ⟨ρ (l : G) (x : V) - (x : V),
      Submodule.subset_span ⟨(l : G), l.2, (x : V), x.2, rfl⟩⟩
    have hπw : π w = (Mat l : Matrix (Fin r) (Fin r) F) *ᵥ u - u := by
      have hsub : (⟨(w : V), hIW w.2⟩ : ↥W) =
          (⟨ρ (l : G) (x : V), hWL (l : G) l.2 (x : V) x.2⟩ : ↥W) - x := by
        ext
        rfl
      have hcalc : π w = p ⟨ρ (l : G) (x : V),
          hWL (l : G) l.2 (x : V) x.2⟩ - p x := by
        rw [show π w = p ⟨(w : V), hIW w.2⟩ from rfl, hsub, map_sub]
      rw [hcalc, hpL l x, hx]
    have hne : π w ≠ 0 := by
      rw [hπw]
      exact sub_ne_zero.mpr hu
    have hmem : π w ∈ π.range := AddMonoidHom.mem_range.mpr ⟨w, rfl⟩
    rw [hbot] at hmem
    exact hne (AddSubgroup.mem_bot.mp hmem)
  have htop : π.range = ⊤ := by
    rcases hirr π.range hS_inv with h | h
    · exact absurd h hnotbot
    · exact h
  have hsurj : Function.Surjective π := by
    intro u
    have : u ∈ π.range := by rw [htop]; exact AddSubgroup.mem_top u
    exact AddMonoidHom.mem_range.mp this
  have hequiv : ∀ (l : ↥L) (v : ↥I),
      π ⟨ρ (l : G) (v : V), hI_inv (l : G) l.2 (v : V) v.2⟩ =
        (Mat l : Matrix (Fin r) (Fin r) F) *ᵥ π v := by
    intro l v
    have h := hpL l ⟨v, hIW v.2⟩
    have hsub : (⟨ρ (l : G) (v : V), hWL (l : G) l.2 (v : V) (hIW v.2)⟩ : ↥W) =
        (⟨ρ (l : G) (v : V),
          hIW (hI_inv (l : G) l.2 (v : V) v.2)⟩ : ↥W) := by
      ext
      rfl
    rw [hsub] at h
    simpa [π] using h
  have hker_iff : ∀ v : ↥I, π v = 0 ↔ ∀ l ∈ L, ρ l (v : V) = (v : V) := by
    intro v
    constructor
    · intro hv l hl
      have hv' : p ⟨(v : V), hIW v.2⟩ = 0 := by
        simpa [π] using hv
      exact (hker ⟨(v : V), hIW v.2⟩).mp hv' l hl
    · intro hv
      have hv' : p ⟨(v : V), hIW v.2⟩ = 0 := (hker ⟨(v : V), hIW v.2⟩).mpr hv
      simpa [π] using hv'
  refine ⟨{ Mat := Mat
            mat_inj := hMat
            I := I
            inv := hI_inv
            π := π
            surj := hsurj
            equiv := hequiv
            ker_iff := hker_iff }, rfl, hI_comm, hI_A⟩

theorem finrank_quotient_sub_finrank_fixSub_le {K V : Type} [Group K] [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] {ρ : Representation (ZMod 2) K V} (C : Subrepresentation ρ)
    (H : Subgroup K) :
    finrank (ZMod 2) (V ⧸ C.toSubmodule) - finrank (ZMod 2) ↥(fixSub C.quotient H) ≤
      finrank (ZMod 2) V - finrank (ZMod 2) ↥(fixSub ρ H) := by
  classical
  let fFun : ↥(fixSub ρ H) → ↥(fixSub C.quotient H) := fun v =>
    ⟨Submodule.Quotient.mk (p := C.toSubmodule) (v : V), by
      intro h hh
      have hmk : (C.quotient h) (Submodule.Quotient.mk (p := C.toSubmodule) (v : V)) =
          (Submodule.Quotient.mk (p := C.toSubmodule) (ρ h (v : V)) : V ⧸ C.toSubmodule) :=
        Subrepresentation.quotient_apply_mk C h (v : V)
      rw [hmk]
      rw [Submodule.Quotient.eq]
      have hv : ρ h (v : V) = (v : V) := (mem_fixSub.mp v.2) h hh
      simp [hv]⟩
  have fFun_add : ∀ x y, fFun (x + y) = fFun x + fFun y := by
    intro x y
    apply Subtype.ext
    simp [fFun, Submodule.Quotient.mk_add]
  have fFun_smul : ∀ (c : ZMod 2) (x : ↥(fixSub ρ H)),
      fFun (c • x) = c • fFun x := by
    intro c x
    apply Subtype.ext
    simp [fFun, Submodule.Quotient.mk_smul]
  let f : ↥(fixSub ρ H) →ₗ[ZMod 2] ↥(fixSub C.quotient H) :=
    { toFun := fFun
      map_add' := fFun_add
      map_smul' := fFun_smul }
  have hker_le : (LinearMap.ker f).map (fixSub ρ H).subtype ≤ C.toSubmodule := by
    rintro v ⟨w, hw, rfl⟩
    have hw0 : fFun w = 0 := by
      simpa [f] using LinearMap.mem_ker.mp hw
    have hw0' : (Submodule.Quotient.mk (w : V) : V ⧸ C.toSubmodule) = 0 := by
      simpa [fFun] using congrArg Subtype.val hw0
    exact (Submodule.Quotient.mk_eq_zero (p := C.toSubmodule)).mp hw0'
  have hkerdim : finrank (ZMod 2) (LinearMap.ker f) =
      finrank (ZMod 2) ↥((LinearMap.ker f).map (fixSub ρ H).subtype) :=
    (Submodule.finrank_map_subtype_eq (fixSub ρ H) (LinearMap.ker f)).symm
  have hkermono : finrank (ZMod 2) ↥((LinearMap.ker f).map (fixSub ρ H).subtype) ≤
      finrank (ZMod 2) ↥C.toSubmodule := Submodule.finrank_mono hker_le
  have hker : finrank (ZMod 2) (LinearMap.ker f) ≤ finrank (ZMod 2) ↥C.toSubmodule := by
    rw [hkerdim]
    exact hkermono
  have hrange : finrank (ZMod 2) (LinearMap.range f) ≤
      finrank (ZMod 2) ↥(fixSub C.quotient H) := Submodule.finrank_le _
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  have hquot := Submodule.finrank_quotient_add_finrank C.toSubmodule
  omega

theorem isQuasisimple_of_mulEquiv_sl3 {Q : Type} [Group Q] {F : Type} [Field F]
    (e : Q ≃* SL(3, F)) : CFSG.Open.IsQuasisimple Q := by
  have hperf : commutator (SpecialLinearGroup (Fin 3) F) = ⊤ :=
    (CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect
      (K := F) (n := 3) (by norm_num)).commutator_eq_top
  have hsimplePSL : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :=
    (CFSG.LinearGroups.linear_projective_simple (K := F) (n := 3)
      (by norm_num) (Or.inl (by norm_num))).2.1
  have hsimple : IsSimpleGroup
      (SpecialLinearGroup (Fin 3) F ⧸ Subgroup.center (SpecialLinearGroup (Fin 3) F)) := by
    have q : (SpecialLinearGroup (Fin 3) F ⧸
        Subgroup.center (SpecialLinearGroup (Fin 3) F)) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 3) F :=
      (QuotientGroup.quotientMulEquivOfEq (G := SpecialLinearGroup (Fin 3) F)
        CFSG.LinearGroups.scalarSubgroup_eq_center).symm.trans
        (CFSG.LinearGroups.scalarQuotientEquivPSL (n := 3) (K := F))
    exact q.isSimpleGroup
  exact CFSG.Open.IsQuasisimple.of_mulEquiv e ⟨hperf, hsimple⟩

theorem addSubgroup_eq_bot_or_top_of_range {Λ : Type} [Group Λ] {F : Type} [Field F]
    (Mat : Λ →* GL (Fin 3) F)
    (hMatr : Mat.range = (Matrix.SpecialLinearGroup.toGL : SL(3, F) →* GL (Fin 3) F).range)
    (S : AddSubgroup (Fin 3 → F))
    (hS : ∀ (l : Λ), ∀ u ∈ S, (Mat l : Matrix (Fin 3) (Fin 3) F) *ᵥ u ∈ S) : S = ⊥ ∨ S = ⊤ := by
  refine CFSG.Quasithin.H13.L32A.C.SL3N.eq_bot_or_eq_top S ?_
  intro g u hu
  have hmem : (Matrix.SpecialLinearGroup.toGL g : GL (Fin 3) F) ∈ Mat.range := by
    rw [hMatr]
    exact MonoidHom.mem_range.mpr ⟨g, rfl⟩
  obtain ⟨l, hl⟩ := hmem
  have hcoe : ((Matrix.SpecialLinearGroup.toGL g : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = (g : Matrix (Fin 3) (Fin 3) F) := by
    ext i j
    rfl
  have hmat : (Mat l : Matrix (Fin 3) (Fin 3) F) = (g : Matrix (Fin 3) (Fin 3) F) := by
    rw [hl]
    exact hcoe
  have := hS l u hu
  rwa [hmat] at this

theorem exists_ne_one_of_mulEquiv_sl3 {Λ : Type} [Group Λ] {F : Type} [Field F]
    (e : Λ ≃* SL(3, F)) (Mat : Λ →* GL (Fin 3) F) (hMat : Function.Injective Mat) :
    ∃ l : Λ, Mat l ≠ 1 := by
  have hg : Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 3)) (j := 1)
      (by decide : (0 : Fin 3) ≠ 1) (1 : F) ≠ 1 := by
    intro h
    have h' := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) F =>
      (g : Matrix (Fin 3) (Fin 3) F) 0 1) h
    rw [Matrix.SpecialLinearGroup.transvection_coe] at h'
    simp at h'
  refine ⟨e.symm (Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 3)) (j := 1)
      (by decide : (0 : Fin 3) ≠ 1) (1 : F)), ?_⟩
  intro h
  have hml : e.symm (Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 3)) (j := 1)
      (by decide : (0 : Fin 3) ≠ 1) (1 : F)) = 1 := hMat (by simpa using h)
  exact hg (by simpa using congrArg e hml)

end CFSG.LocalAnalysis.RankThreeUC.S15

module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerC3Core
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerC3Lift
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerC3SpGroup
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerC3SpModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KC3

open CFSG.Open CFSG.Open.StatedAPI CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KC3.Plane
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KC3.Model

noncomputable section

theorem card_map_injOn {G H : Type} [Group G] [Group H] (f : G →* H) (P : Subgroup G)
    (hf : ∀ x ∈ P, f x = 1 → x = 1) : Nat.card (P.map f) = Nat.card P := by
  let g : P →* H := f.comp P.subtype
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hf x.1 x.2 hx)
  have h1 : P.map f = g.range := by
    ext h
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨⟨x, hx⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
  rw [h1]
  exact (Nat.card_congr (MonoidHom.ofInjective hg).toEquiv).symm

theorem lift_props (K : Type) [Field K] [Finite K] (E : Subgroup (StatedProj (StatedSp 3 K)))
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 27) :
    ∃ P : Subgroup (StatedSp 3 K), Nat.card P = 27 ∧ (∀ x ∈ P, x ^ 3 = 1) ∧
      (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧
      (∀ x ∈ P, (QuotientGroup.mk x : StatedProj (StatedSp 3 K)) = 1 → x = 1) ∧
      P.map (QuotientGroup.mk' ((StatedScalars (Fin 3 ⊕ Fin 3) K).subgroupOf
        (StatedSp 3 K))) = E := by
  obtain ⟨P, hinj, himg⟩ := lift_exists K E hc
  have hmemE : ∀ x ∈ P, (QuotientGroup.mk x : StatedProj (StatedSp 3 K)) ∈ E := by
    intro x hx
    rw [← himg]
    exact Subgroup.mem_map_of_mem _ hx
  have hcard : Nat.card P = 27 := by
    rw [← hc, ← himg, card_map_injOn _ P hinj]
  have hexp : ∀ x ∈ P, x ^ 3 = 1 := by
    intro x hx
    apply hinj (x ^ 3) (P.pow_mem hx 3)
    rw [QuotientGroup.mk_pow]
    exact hE.2 _ (hmemE x hx)
  have hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    apply commute_of_mk_commute (hexp y hy)
    have := hE.1.is_comm.comm ⟨QuotientGroup.mk x, hmemE x hx⟩ ⟨QuotientGroup.mk y, hmemE y hy⟩
    exact congrArg Subtype.val this
  exact ⟨P, hcard, hexp, hcomm, hinj, himg⟩

def repP {K : Type} [Field K] (P : Subgroup (StatedSp 3 K)) :
    P →* Module.End K ((Fin 3 ⊕ Fin 3) → K) where
  toFun g := Matrix.toLin' (g.1.1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)
  map_one' := by
    simp only [Subgroup.coe_one, OneMemClass.coe_one, Units.val_one]
    rw [Matrix.toLin'_one]
    rfl
  map_mul' g h := by
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [Matrix.toLin'_mul]
    rfl

theorem repP_faithful {K : Type} [Field K] (P : Subgroup (StatedSp 3 K)) :
    ∀ g : P, (∀ v : (Fin 3 ⊕ Fin 3) → K, repP P g v = v) → g = 1 := by
  intro g hg
  have h1 : repP P g = 1 := LinearMap.ext fun v => by rw [Module.End.one_apply]; exact hg v
  have h2 : Matrix.toLin' (g.1.1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) =
      Matrix.toLin' 1 := by
    rw [Matrix.toLin'_one]
    exact h1
  have h3 := Matrix.toLin'.injective h2
  have h4 : g.1.1 = 1 := Units.ext h3
  exact Subtype.ext (Subtype.ext h4)

theorem repP_inv {K : Type} [Field K] (P : Subgroup (StatedSp 3 K)) (g : P)
    (u v : (Fin 3 ⊕ Fin 3) → K) : Bsp K (repP P g u) (repP P g v) = Bsp K u v :=
  Bsp_comp_mem (K := K) (g.1 : GL (Fin 3 ⊕ Fin 3) K) g.1.2 u v

theorem right_mul_av {K V Γ : Type} [Field K] [AddCommGroup V] [Module K V] [Group Γ]
    [Fintype Γ] {ρ : Γ →* Module.End K V} {D : Subgroup Γ} {g : Γ} (hg : g ∈ D) :
    av ρ D * ρ g = av ρ D := by
  unfold av
  rw [smul_mul_assoc, sum_right_mul ρ hg]

theorem commute_av {K V Γ : Type} [Field K] [AddCommGroup V] [Module K V] [Group Γ]
    [Fintype Γ] {ρ : Γ →* Module.End K V} (D : Subgroup Γ) (Y : Module.End K V)
    (hY : ∀ g ∈ D, Y * ρ g = ρ g * Y) : Y * av ρ D = av ρ D * Y := by
  unfold av
  rw [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun g hg => ?_
  exact hY g ((mem_subEl D g).1 hg)

theorem toMatrix_comm_of_lin {K : Type} [Field K] (Φ : Module.End K ((Fin 3 ⊕ Fin 3) → K))
    (M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)
    (h : Φ * Matrix.toLin' M = Matrix.toLin' M * Φ) :
    LinearMap.toMatrix' Φ * M = M * LinearMap.toMatrix' Φ := by
  have := congrArg LinearMap.toMatrix' h
  rw [LinearMap.toMatrix'_mul, LinearMap.toMatrix'_mul, LinearMap.toMatrix'_toLin'] at this
  exact this

@[expose] def piSp (K : Type) [Field K] : StatedSp 3 K →* StatedProj (StatedSp 3 K) :=
  QuotientGroup.mk' ((StatedScalars (Fin 3 ⊕ Fin 3) K).subgroupOf (StatedSp 3 K))

theorem piSp_apply {K : Type} [Field K] (x : StatedSp 3 K) :
    piSp K x = QuotientGroup.mk x := rfl

theorem PhiGL_val {K : Type} [Field K] {Q : Module.End K ((Fin 3 ⊕ Fin 3) → K)}
    (D : PlaneData K Q) (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((PhiGL D A : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) =
      LinearMap.toMatrix' (Phi D.S A.1) := rfl

theorem piSp_ΦSp_comm {K : Type} [Field K] {Q : Module.End K ((Fin 3 ⊕ Fin 3) → K)}
    (D : PlaneData K Q) (P : Subgroup (StatedSp 3 K)) (g : P)
    (hcommQ : repP P g * Q = Q * repP P g)
    (hfix : ∀ w ∈ LinearMap.range Q, repP P g w = w) (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    piSp K (ΦSp D A) * piSp K g.1 = piSp K g.1 * piSp K (ΦSp D A) := by
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, ΦSp, MonoidHom.coe_mk, OneHom.coe_mk, PhiGL_val]
  have hlin := Phi_comm D.S D.hP (repP P g) hcommQ hfix A.1
  exact toMatrix_comm_of_lin (Phi D.S A.1) (g.1.1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) hlin

theorem exists_ker_ne_zero {K : Type} [Field K] {Q : Module.End K ((Fin 3 ⊕ Fin 3) → K)}
    (hdim : Module.finrank K (LinearMap.range Q) = 2) : ∃ u, Q u = 0 ∧ u ≠ 0 := by
  have h := LinearMap.finrank_range_add_finrank_ker Q
  rw [hdim] at h
  have hfin : Module.finrank K ((Fin 3 ⊕ Fin 3) → K) = 6 := by simp
  have hker : LinearMap.ker Q ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot, hfin] at h
    omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨u, LinearMap.mem_ker.1 hu, hu0⟩

theorem ΦSp_ker_trivial {K : Type} [Field K] {Q : Module.End K ((Fin 3 ⊕ Fin 3) → K)}
    (D : PlaneData K Q) (hdimQ : Module.finrank K (LinearMap.range Q) = 2)
    (A : Matrix.SpecialLinearGroup (Fin 2) K) (hA : piSp K (ΦSp D A) = 1) : A = 1 := by
  have hmk : (QuotientGroup.mk (ΦSp D A) : StatedProj (StatedSp 3 K)) = 1 := by
    rw [← piSp_apply]
    exact hA
  obtain ⟨c, hc⟩ := ker_mk_scalar (ΦSp D A) hmk
  have hmat : LinearMap.toMatrix' (Phi D.S A.1) =
      ((Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin 3) c : GL (Fin 3 ⊕ Fin 3) K) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) := by
    rw [← PhiGL_val]
    exact congrArg (fun g : GL (Fin 3 ⊕ Fin 3) K => (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K))
      hc
  have hlin : Phi D.S A.1 = Matrix.toLin'
      ((Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin 3) c : GL (Fin 3 ⊕ Fin 3) K) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) := by
    rw [← hmat, Matrix.toLin'_toMatrix']
  obtain ⟨u, hu0, hune⟩ := exists_ker_ne_zero hdimQ
  have hPu : Phi D.S A.1 u = u := by
    rw [Phi_apply']
    simp [hu0, l0_apply, l1_apply]
  have hscal : ∀ i, (c : K) * u i = u i := by
    intro i
    have h := congrFun (congrArg (fun f : Module.End K ((Fin 3 ⊕ Fin 3) → K) => f u) hlin) i
    rw [hPu, Matrix.toLin'_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.mulVec_diagonal] at h
    exact h.symm
  have hc1 : (c : K) = 1 := by
    obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hune (funext hcon)
    have h := hscal i
    have : ((c : K) - 1) * u i = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h1 | h1
    · linear_combination h1
    · exact absurd h1 hi
  have hc' : c = 1 := Units.ext hc1
  have hPhi1 : Phi D.S A.1 = Phi D.S 1 := by
    rw [hlin, hc', Phi_one D.S D.hP, map_one, Units.val_one, Matrix.toLin'_one]
    rfl
  exact Subtype.ext (Phi_inj D.S (Bsp_halt K) D.hP A.1 1 hPhi1)

theorem conj_ΦSp {K : Type} [Field K] {Q : Module.End K ((Fin 3 ⊕ Fin 3) → K)}
    (D : PlaneData K Q) (P : Subgroup (StatedSp 3 K)) (F : Subgroup P)
    (hexp : ∀ x ∈ P, x ^ 3 = 1)
    (hQcomm : ∀ Y : Module.End K ((Fin 3 ⊕ Fin 3) → K),
      (∀ g ∈ F, Y * repP P g = repP P g * Y) → Y * Q = Q * Y)
    (y : StatedProj (StatedSp 3 K)) (hy : ∀ g ∈ F, piSp K g.1 * y = y * piSp K g.1)
    (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    ∃ A' : Matrix.SpecialLinearGroup (Fin 2) K,
      y * piSp K (ΦSp D A) = piSp K (ΦSp D A') * y := by
  obtain ⟨yt, rfl⟩ := QuotientGroup.mk_surjective y
  have hcomm_yt : ∀ g ∈ F, yt * g.1 = g.1 * yt := by
    intro g hg
    have h := hy g hg
    rw [piSp_apply] at h
    exact commute_of_mk_commute (hexp g.1 g.2) h.symm
  set Y : Module.End K ((Fin 3 ⊕ Fin 3) → K) := Matrix.toLin' (yt.1.1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) with hY
  have hYcomm : ∀ g ∈ F, Y * repP P g = repP P g * Y := by
    intro g hg
    have h := hcomm_yt g hg
    rw [hY]
    have hmat : (yt.1.1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *
        (g.1.1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) =
        (g.1.1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *
        (yt.1.1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) := by
      have h' := congrArg (fun z : StatedSp 3 K => (z : GL (Fin 3 ⊕ Fin 3) K)) h
      simp only [Subgroup.coe_mul, Units.val_mul] at h'
      exact congrArg (fun z : GL (Fin 3 ⊕ Fin 3) K => (z : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)) h'
    show Matrix.toLin' (yt.1.1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) ∘ₗ
      Matrix.toLin' (g.1.1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) =
      Matrix.toLin' (g.1.1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) ∘ₗ
      Matrix.toLin' (yt.1.1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)
    rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hmat]
  have hYQ := hQcomm Y hYcomm
  obtain ⟨M, hM, hconj⟩ := Phi_conj D.S (Bsp_halt K) D.hP Y hYQ
    (fun u v => Bsp_comp_mem K (yt.1 : GL (Fin 3 ⊕ Fin 3) K) yt.2 u v)
  refine ⟨⟨M * A.1 * M⁻¹, ?_⟩, ?_⟩
  · simp [Matrix.det_mul, Matrix.det_nonsing_inv, hM, A.2]
  · show piSp K yt * piSp K (ΦSp D A) = piSp K (ΦSp D ⟨M * A.1 * M⁻¹, _⟩) * piSp K yt
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, ΦSp, MonoidHom.coe_mk, OneHom.coe_mk, PhiGL_val]
    have h2 := congrArg LinearMap.toMatrix' (hconj A.1)
    rw [LinearMap.toMatrix'_mul, LinearMap.toMatrix'_mul, LinearMap.toMatrix'_toLin'] at h2
    exact h2

theorem fix_of_mem_F {K : Type} [Field K] {P : Subgroup (StatedSp 3 K)} [Fintype P] {F : Subgroup P}
    {g : P} (hg : g ∈ F) (Q : Module.End K ((Fin 3 ⊕ Fin 3) → K)) (hQ : Q = av (repP P) F) :
    repP P g * Q = Q * repP P g ∧ ∀ w ∈ LinearMap.range Q, repP P g w = w := by
  subst hQ
  refine ⟨?_, ?_⟩
  · rw [left_mul_av hg, right_mul_av hg]
  · rintro w ⟨x, rfl⟩
    have := congrArg (fun f : Module.End K ((Fin 3 ⊕ Fin 3) → K) => f x)
      (left_mul_av (ρ := repP P) (D := F) hg)
    simpa [Module.End.mul_apply] using this

theorem kerConcl_sp3 (K : Type) [Field K] [Finite K] (h3 : (3 : K) ≠ 0) (h4 : 4 ≤ Nat.card K)
    (E : Subgroup (StatedProj (StatedSp 3 K))) (hE : IsElemAbelian 3 E) (hc : Nat.card E = 27) :
    CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.KerConcl E := by
  obtain ⟨P, hcard, hexp, hcomm, hinj, himg⟩ := lift_props K E hE hc
  haveI : Fintype P := Fintype.ofFinite P
  have hexp' : ∀ g : P, g ^ 3 = 1 := fun g => Subtype.ext (by simpa using hexp g.1 g.2)
  have hcomm' : ∀ g h : P, g * h = h * g := fun g h =>
    Subtype.ext (by simpa using hcomm g.1 g.2 h.1 h.2)
  have hdim : Module.finrank K ((Fin 3 ⊕ Fin 3) → K) = 6 := by simp
  obtain ⟨F, hFidx, hFd, hFnd, hT⟩ := core_exists (ρ := repP P) h3 hcard hexp' hcomm' hdim
    (repP_faithful P) (Bsp K) (Bsp_halt K) (Bsp_nd K) (repP_inv P)
  have hFindex : F.index = 3 := (mem_idx3 F).1 hFidx
  have hFcard : Nat.card F = 9 := card_of_index_eq_three hcard hFindex
  have hQQ : av (repP P) F * av (repP P) F = av (repP P) F :=
    av_mul_self (repP P) (natCard_ne_zero' h3 hcard F)
  have hQa : ∀ u v, Bsp K (av (repP P) F u) v = Bsp K u (av (repP P) F v) :=
    fun u v => bilin_av (repP P) (Bsp K) (repP_inv P) F u v
  obtain ⟨S⟩ := exists_sympPair (Bsp_halt K) hQQ hFd hFnd
  let D : PlaneData K (av (repP P) F) := ⟨hQQ, hQa, S⟩
  have hQcomm : ∀ Y : Module.End K ((Fin 3 ⊕ Fin 3) → K),
      (∀ g ∈ F, Y * repP P g = repP P g * Y) → Y * av (repP P) F = av (repP P) F * Y :=
    fun Y hY => commute_av F Y hY
  have hPE : P.map (piSp K) = E := himg
  have hpm_inj : Function.Injective ((piSp K).comp P.subtype) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    exact Subtype.ext (hinj g.1 g.2 hg)
  have hinjΦ : Function.Injective ((piSp K).comp (ΦSp D)) := by
    rw [injective_iff_map_eq_one]
    intro A hA
    exact ΦSp_ker_trivial D hFd A hA
  set H := ((piSp K).comp (ΦSp D)).range with hH
  set C := Subgroup.centralizer
    (((F.map ((piSp K).comp P.subtype) : Subgroup _)) : Set (StatedProj (StatedSp 3 K))) with hC
  have hHC : H ≤ C := by
    rintro x hx
    obtain ⟨A, rfl⟩ := MonoidHom.mem_range.1 hx
    rw [hC, Subgroup.mem_centralizer_iff]
    rintro s hs
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hs
    obtain ⟨hcommQ, hfix⟩ := fix_of_mem_F hg (av (repP P) F) rfl
    exact (piSp_ΦSp_comm D P g hcommQ hfix A).symm
  refine ⟨F.map ((piSp K).comp P.subtype), ?_, ?_, H, hHC, ?_, ?_, ?_⟩
  · rintro x hx
    obtain ⟨g, _, rfl⟩ := Subgroup.mem_map.1 hx
    rw [← hPE]
    exact Subgroup.mem_map_of_mem (piSp K) g.2
  · rw [Subgroup.card_map_of_injective hpm_inj, hFcard]
  · have hnorm : (H.subgroupOf C).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨A, hA⟩ := MonoidHom.mem_range.1 hn
      have hy : ∀ g' ∈ F, piSp K g'.1 * (g.1 : StatedProj (StatedSp 3 K)) =
          (g.1 : StatedProj (StatedSp 3 K)) * piSp K g'.1 := by
        intro g' hg'
        exact Subgroup.mem_centralizer_iff.1 g.2 _ (Subgroup.mem_map_of_mem _ hg')
      obtain ⟨A', hA'⟩ := conj_ΦSp D P F hexp hQcomm (g.1 : StatedProj (StatedSp 3 K)) hy A
      refine MonoidHom.mem_range.2 ⟨A', ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hA]
      show piSp K (ΦSp D A') = (g.1 : StatedProj (StatedSp 3 K)) * piSp K (ΦSp D A) *
        (g.1 : StatedProj (StatedSp 3 K))⁻¹
      rw [eq_mul_inv_iff_mul_eq]
      exact hA'.symm
    exact CFSG.Open.IsSubnormal.step hHC hnorm (CFSG.Open.IsSubnormal.refl C)
  · exact CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.isQuasisimple_equiv
      (MonoidHom.ofInjective hinjΦ) (isQuasisimple_SL2_field K h4)
  · rw [CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.card_quotient_center_equiv
      (MonoidHom.ofInjective hinjΦ).symm]
    exact three_dvd_card_SL2_quot K h3

end

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KC3

end

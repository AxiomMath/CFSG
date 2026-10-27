module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLForm
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLSym
public import CFSG.ClassicalGroups.Alternating.Generation
public import CFSG.ClassicalGroups.Orthogonal.CharTwoTransvection
public import CFSG.LocalAnalysis.PreuniquenessRankFour.AlternatingForm

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.OutcomeLocal

open Module Submodule CFSG.LocalAnalysis.ComponentInitial CFSG.Fischer.Classification.Symplectic

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {G : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)}

theorem gl_apply_ne_zero (g : LinearMap.GeneralLinearGroup (ZMod 2) V) {v : V} (hv : v ≠ 0) :
    (g : V →ₗ[ZMod 2] V) v ≠ 0 := by
  have h := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V g).map_ne_zero_iff.mpr hv
  rwa [LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv] at h

theorem eq_one_of_finrank_eq_one [FiniteDimensional (ZMod 2) V] (h1 : finrank (ZMod 2) V = 1)
    (g : LinearMap.GeneralLinearGroup (ZMod 2) V) : g = 1 := by
  obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 :=
    (Module.finrank_pos_iff_exists_ne_zero (R := ZMod 2)).mp (by omega)
  have hspan := (finrank_eq_one_iff_of_nonzero' v hv).mp h1
  obtain ⟨c, hc⟩ := hspan ((g : V →ₗ[ZMod 2] V) v)
  have hc1 : c = 1 := by
    rcases zmod2_eq_zero_or_one c with rfl | rfl
    · rw [zero_smul] at hc
      exact absurd hc.symm (gl_apply_ne_zero g hv)
    · rfl
  refine tv_ext fun w => ?_
  obtain ⟨c', rfl⟩ := hspan w
  rw [map_smul, ← hc, hc1, one_smul]
  rfl

theorem centres_nonempty [FiniteDimensional (ZMod 2) V] (hgen : GenByTransvections G)
    (hirr : IsIrreducibleOn G) (h2 : 2 ≤ finrank (ZMod 2) V) : (centres G).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  obtain ⟨S, hS, hG⟩ := hgen
  have hS0 : S = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro t ht
    obtain ⟨φ, a, h, hφ, ha, rfl⟩ := (isF2Transvection_iff t).mp (hS t ht)
    have hmem : a ∈ centres G := ⟨ha, φ, hφ, h, hG ▸ Subgroup.subset_closure ht⟩
    rw [hne] at hmem
    exact hmem
  rw [hS0, Subgroup.closure_empty] at hG
  obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 :=
    (Module.finrank_pos_iff_exists_ne_zero (R := ZMod 2)).mp (by omega)
  have hinv : IsGInvariant G (span (ZMod 2) {v}) := by
    intro g hg w hw
    rw [hG, Subgroup.mem_bot] at hg
    subst hg
    exact hw
  rcases hirr _ hinv with h | h
  · exact hv (span_singleton_eq_bot.mp h)
  · have h' := finrank_span_singleton (K := ZMod 2) hv
    rw [h, finrank_top] at h'
    omega

theorem congrLinearEquiv_symm_apply_eq {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (e : W ≃ₗ[ZMod 2] V) (g : LinearMap.GeneralLinearGroup (ZMod 2) V)
    (h : LinearMap.GeneralLinearGroup (ZMod 2) W)
    (hgh : ∀ w, (g : V →ₗ[ZMod 2] V) (e w) = e ((h : W →ₗ[ZMod 2] W) w)) :
    LinearMap.GeneralLinearGroup.congrLinearEquiv e.symm g = h := by
  refine Units.ext (LinearMap.ext fun w => ?_)
  change e.symm ((g : V →ₗ[ZMod 2] V) (e w)) = (h : W →ₗ[ZMod 2] W) w
  rw [hgh, LinearEquiv.symm_apply_apply]

section Cases

variable [FiniteDimensional (ZMod 2) V] {f : LinearMap.BilinForm (ZMod 2) V}

theorem eq_bilinIsometryGroup_of_forall (hgen : GenByTransvections G) (halt : ∀ v, f v v = 0)
    (hcomm : ∀ u v, f u v = f v u) (hnd : ∀ u, (∀ v, f u v = 0) → u = 0)
    (hF4 : ∀ (φ : Dual (ZMod 2) V) (a : V), a ≠ 0 → φ ≠ 0 → InG G φ a → φ = f a)
    (hF5 : ∀ a ∈ centres G, InG G (f a) a) (hall : ∀ v : V, v ≠ 0 → v ∈ centres G) :
    G = bilinIsometryGroup f := by
  refine le_antisymm (le_bilinIsometryGroup hF4 hgen hcomm) ?_
  have hB : f.IsAlt := halt
  have hBn : f.Nondegenerate :=
    ⟨fun u hu => hnd u hu, fun u hu => hnd u fun v => by rw [hcomm]; exact hu v⟩
  rw [CFSG.ClassicalGroups.Alternating.alternating_transvection_generation hB hBn,
    Subgroup.closure_le]
  rintro g ⟨a, c, rfl⟩
  by_cases h1 : c = 1 ∧ a ≠ 0
  · obtain ⟨rfl, ha⟩ := h1
    have heq : CFSG.ClassicalGroups.Alternating.symplecticTransvection f hB a 1 =
        tv (f a) a (halt a) := tv_ext fun x => by
      rw [CFSG.ClassicalGroups.Alternating.symplecticTransvection_apply, tv_apply, one_mul,
        hcomm]
    rw [SetLike.mem_coe, heq]
    exact (hF5 a (hall a ha)).2
  · have heq : CFSG.ClassicalGroups.Alternating.symplecticTransvection f hB a c = 1 :=
      tv_ext fun x => by
        rw [CFSG.ClassicalGroups.Alternating.symplecticTransvection_apply]
        rcases zmod2_eq_zero_or_one c with rfl | rfl
        · rw [zero_mul, zero_smul, add_zero]
          rfl
        · have ha : a = 0 := by
            by_contra ha
            exact h1 ⟨rfl, ha⟩
          rw [ha, smul_zero, add_zero]
          rfl
    rw [SetLike.mem_coe, heq]
    exact G.one_mem

theorem eq_comap_orthogonalGroup (hgen : GenByTransvections G) (halt : ∀ v, f v v = 0)
    (hcomm : ∀ u v, f u v = f v u) (hnd : ∀ u, (∀ v, f u v = 0) → u = 0)
    (hF4 : ∀ (φ : Dual (ZMod 2) V) (a : V), a ≠ 0 → φ ≠ 0 → InG G φ a → φ = f a)
    (hF5 : ∀ a ∈ centres G, InG G (f a) a) {Q : QuadraticForm (ZMod 2) V}
    (hpol : ∀ u v, QuadraticMap.polar Q u v = f u v) (hQ : ∀ v, v ∈ centres G ↔ Q v = 1)
    (h3 : 3 ≤ finrank (ZMod 2) V)
    (hE : 5 ≤ finrank (ZMod 2) V ∨
      ¬ ∃ W : Submodule (ZMod 2) V, finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0) :
    G = (TauCeti.QuadraticMap.orthogonalGroup Q).comap
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom := by
  have hQnd : (QuadraticMap.polarBilin Q).Nondegenerate := by
    have hpb : QuadraticMap.polarBilin Q = f := LinearMap.ext₂ fun u v => hpol u v
    rw [hpb]
    exact ⟨fun u hu => hnd u hu, fun u hu => hnd u fun v => by rw [hcomm]; exact hu v⟩
  apply le_antisymm
  · rw [eq_closure_tv hF4 hgen halt hF5, Subgroup.closure_le]
    rintro t ⟨d, hd, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro x
    rw [LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv]
    change Q (x + f d x • d) = Q x
    rw [QuadraticMap.map_add Q x (f d x • d), QuadraticMap.map_smul, hpol, (hQ d).mp hd, map_smul,
      hcomm x d, smul_eq_mul, smul_eq_mul, mul_one]
    generalize f d x = c
    generalize Q x = q
    revert c q
    decide
  · intro g hg
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
      CFSG.ClassicalGroups.Orthogonal.orthogonalGroup_eq_closure_reflect hQnd h3 hE] at hg
    have hle : Subgroup.closure (Set.range (CFSG.ClassicalGroups.Orthogonal.reflect Q)) ≤
        G.map (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro _ ⟨v, rfl⟩
      rcases zmod2_eq_zero_or_one (Q v) with h0 | h1
      · rw [CFSG.ClassicalGroups.Orthogonal.reflect_of_map_eq_zero h0]
        exact (G.map _).one_mem
      · refine ⟨tv (f v) v (halt v), ((hF5 v ((hQ v).mpr h1)).2), ?_⟩
        refine LinearEquiv.ext fun x => ?_
        rw [MulEquiv.coe_toMonoidHom, LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv,
          CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_map_eq_one h1, tv_apply, hpol,
          hcomm]
    obtain ⟨g', hg', hgg'⟩ := hle hg
    rw [MulEquiv.coe_toMonoidHom] at hgg'
    rwa [(LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).injective hgg'] at hg'

theorem exists_heart_conj (hgen : GenByTransvections G) (P : PreConfig V)
    (hPD : P.D = centres G)
    (hF4 : ∀ (φ : Dual (ZMod 2) V) (a : V), a ≠ 0 → φ ≠ 0 → InG G φ a → φ = P.b a)
    (hF5 : ∀ a ∈ centres G, InG G (P.b a) a) (hTN : P.toSympConfig.TN)
    (hn : 1 ≤ finrank (ZMod 2) V) :
    (∃ β : V ≃ₗ[ZMod 2] sumZero (finrank (ZMod 2) V + 1),
        G.map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
          (sumZeroRep (finrank (ZMod 2) V + 1)).range) ∨
      ∃ β : V ≃ₗ[ZMod 2] sumZero (finrank (ZMod 2) V + 2) ⧸ onesLine (finrank (ZMod 2) V + 2),
        G.map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
          (heartRep (finrank (ZMod 2) V + 2)).range := by
  classical
  have : Finite V := Module.finite_of_finite (ZMod 2)
  obtain ⟨v₀, hv₀⟩ : ∃ v : V, v ≠ 0 :=
    (Module.finrank_pos_iff_exists_ne_zero (R := ZMod 2)).mp (by omega)
  obtain ⟨d₀, hd₀, -⟩ := P.exists_mem_b_eq_one hv₀
  obtain ⟨m, γ, hiso, hmem, hall⟩ := exists_sumZero_hom P.toSympConfig hTN ⟨d₀, hd₀⟩
  have hsurj := surjective_of_forall_mem hall
  have hker := ker_eq_onesLine hiso hall
  have hGcl := eq_closure_tv hF4 hgen P.self_eq_zero hF5
  have hDD : P.toSympConfig.D = centres G := hPD
  have hkey : ∀ (i j : Fin m) (x : sumZero m),
      (tv (P.b (γ (pairVec i j))) (γ (pairVec i j)) (P.self_eq_zero _) : V →ₗ[ZMod 2] V) (γ x) =
        γ (sumZeroEquiv (Equiv.swap i j) x) := by
    intro i j x
    rw [tv_apply, map_sumZeroEquiv_swap hiso, P.comm]
    rfl
  have hm1 : 1 ≤ m := by
    by_contra hm
    obtain ⟨x, hx⟩ := hsurj v₀
    have hm0 : m = 0 := by omega
    subst hm0
    have hx0 : x = 0 := Subtype.ext (funext fun i => i.elim0)
    rw [hx0, map_zero] at hx
    exact hv₀ hx.symm
  have himage : ∀ (W : Type) [AddCommGroup W] [Module (ZMod 2) W] (e : W ≃ₗ[ZMod 2] V)
      (ρ : Equiv.Perm (Fin m) →* LinearMap.GeneralLinearGroup (ZMod 2) W),
      (∀ (i j : Fin m) (w : W) (x : sumZero m), e w = γ x →
        e ((ρ (Equiv.swap i j) : W →ₗ[ZMod 2] W) w) = γ (sumZeroEquiv (Equiv.swap i j) x)) →
      (∀ w : W, ∃ x : sumZero m, e w = γ x) →
      G.map (LinearMap.GeneralLinearGroup.congrLinearEquiv e.symm).toMonoidHom = ρ.range := by
    intro W _ _ e ρ hρ hcover
    have hconj : ∀ i j : Fin m, LinearMap.GeneralLinearGroup.congrLinearEquiv e.symm
        (tv (P.b (γ (pairVec i j))) (γ (pairVec i j)) (P.self_eq_zero _)) =
          ρ (Equiv.swap i j) := by
      intro i j
      refine congrLinearEquiv_symm_apply_eq e _ _ fun w => ?_
      obtain ⟨x, hx⟩ := hcover w
      rw [hx, hkey, hρ i j w x hx]
    rw [hGcl, MonoidHom.map_closure, MonoidHom.range_eq_map, ← Equiv.Perm.closure_isSwap,
      MonoidHom.map_closure]
    congr 1
    ext t
    constructor
    · rintro ⟨_, ⟨d, hd, rfl⟩, rfl⟩
      obtain ⟨i, j, hij, rfl⟩ := hall d (hDD ▸ hd)
      exact ⟨Equiv.swap i j, ⟨i, j, hij, rfl⟩, (hconj i j).symm⟩
    · rintro ⟨σ, ⟨i, j, hij, rfl⟩, rfl⟩
      exact ⟨_, ⟨γ (pairVec i j), hDD ▸ hmem i j hij, rfl⟩, hconj i j⟩
  rcases Nat.even_or_odd m with hme | hmo
  ·
    right
    have hm2 : 2 ≤ m := by
      obtain ⟨k, hk⟩ := hme
      omega
    let eγ : (sumZero m ⧸ onesLine m) ≃ₗ[ZMod 2] V :=
      (Submodule.quotEquivOfEq _ _ hker.symm).trans (γ.quotKerEquivOfSurjective hsurj)
    have heγ : ∀ x, eγ (Submodule.Quotient.mk x) = γ x := fun x => rfl
    have hdim : finrank (ZMod 2) V = m - 2 := by
      rw [← eγ.finrank_eq, finrank_quotient_onesLine hm2 hme]
    have hmn : m = finrank (ZMod 2) V + 2 := by omega
    subst hmn
    refine ⟨eγ.symm, himage _ eγ (heartRep _) ?_ ?_⟩
    · intro i j w x hx
      induction w using Submodule.Quotient.induction_on with
      | H y =>
        rw [heγ] at hx
        rw [heartRep_apply_mk, heγ, map_sumZeroEquiv_swap hiso, map_sumZeroEquiv_swap hiso, hx]
    · intro w
      induction w using Submodule.Quotient.induction_on with
      | H y => exact ⟨y, heγ y⟩
  ·
    left
    have hinj : Function.Injective γ := by
      rw [← LinearMap.ker_eq_bot, hker, onesLine_eq_bot hmo]
    let eγ : sumZero m ≃ₗ[ZMod 2] V := LinearEquiv.ofBijective γ ⟨hinj, hsurj⟩
    have heγ : ∀ x, eγ x = γ x := fun x => rfl
    have hdim : finrank (ZMod 2) V = m - 1 := by
      rw [← eγ.finrank_eq, finrank_sumZero hm1]
    have hmn : m = finrank (ZMod 2) V + 1 := by omega
    subst hmn
    refine ⟨eγ.symm, himage _ eγ (sumZeroRep _) ?_ ?_⟩
    · intro i j w x hx
      rw [heγ] at hx
      rw [sumZeroRep_apply, heγ, hinj hx]
    · intro w
      exact ⟨w, heγ w⟩

end Cases

theorem mclaughlin_transvection_groups_F2 [FiniteDimensional (ZMod 2) V]
    (hn : 1 ≤ finrank (ZMod 2) V) (G : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V))
    (hgen : ∃ S : Set (LinearMap.GeneralLinearGroup (ZMod 2) V),
      (∀ t ∈ S, IsF2Transvection t) ∧ G = Subgroup.closure S)
    (hirr : ∀ W : Submodule (ZMod 2) V,
      (∀ g ∈ G, ∀ w ∈ W, (g : V →ₗ[ZMod 2] V) w ∈ W) → W = ⊥ ∨ W = ⊤) :
    G = ⊤ ∨
      (Even (finrank (ZMod 2) V) ∧ ∃ f : LinearMap.BilinForm (ZMod 2) V,
        f.Nondegenerate ∧ f.IsAlt ∧ G = bilinIsometryGroup f) ∨
      (Even (finrank (ZMod 2) V) ∧ ∃ Q : QuadraticForm (ZMod 2) V,
        (QuadraticMap.polarBilin Q).Nondegenerate ∧
          G = (TauCeti.QuadraticMap.orthogonalGroup Q).comap
            (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom) ∨
      (Even (finrank (ZMod 2) V) ∧
        ((∃ β : V ≃ₗ[ZMod 2] sumZero (finrank (ZMod 2) V + 1),
            G.map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
              (sumZeroRep (finrank (ZMod 2) V + 1)).range) ∨
          ∃ β : V ≃ₗ[ZMod 2] sumZero (finrank (ZMod 2) V + 2) ⧸ onesLine (finrank (ZMod 2) V + 2),
            G.map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
              (heartRep (finrank (ZMod 2) V + 2)).range)) := by
  by_cases h1 : finrank (ZMod 2) V = 1
  · left
    refine eq_top_iff.mpr fun g _ => ?_
    rw [eq_one_of_finrank_eq_one h1 g]
    exact G.one_mem
  by_cases hdih : ∃ (φ ψ : Dual (ZMod 2) V) (a b : V), a ≠ 0 ∧ ψ ≠ 0 ∧ InG G φ a ∧
      InG G ψ b ∧ φ b = 1 ∧ ψ a = 0
  · left
    obtain ⟨φ, ψ, a, b, ha, hψ, hφa, hψb, hφb, hψa⟩ := hdih
    exact eq_top_of_dihedral hgen hirr ha hψ hφa hψb hφb hψa
  have hno : NoDihedralPair G := fun φ ψ a b ha hψ hφa hψb hφb hψa =>
    hdih ⟨φ, ψ, a, b, ha, hψ, hφa, hψb, hφb, hψa⟩
  have hne := centres_nonempty hgen hirr (by omega)
  obtain ⟨P, hPD, hF4, hF5⟩ := exists_preConfig hgen hirr hno hne
  have hBnd : P.b.Nondegenerate :=
    ⟨fun u hu => P.nondeg u hu, fun u hu => P.nondeg u fun v => by rw [P.comm]; exact hu v⟩
  have heven : Even (finrank (ZMod 2) V) :=
    CFSG.PreuniquenessRankFour.Helpers.alternating_nondegenerate_form_finrank_even P.b
      P.self_eq_zero hBnd
  rcases P.toSympConfig.trichotomy with ⟨hall, -⟩ | ⟨⟨Q, hpol, hQ⟩, x, hx, y, hy, hxy, hbxy⟩ | hTN
  ·
    right; left
    have hall' : ∀ v, v ∈ P.D ↔ v ≠ 0 := hall
    refine ⟨heven, P.b, hBnd, P.self_eq_zero, ?_⟩
    exact eq_bilinIsometryGroup_of_forall hgen P.self_eq_zero P.comm P.nondeg hF4 hF5
      fun v hv => hPD ▸ (hall' v).mpr hv
  ·
    right; right; left
    have hpol' : ∀ u v, QuadraticMap.polar Q u v = P.b u v := hpol
    have hQ' : ∀ v, v ∈ P.D ↔ Q v = 1 := hQ
    have hQc : ∀ v, v ∈ centres G ↔ Q v = 1 := fun v => hPD ▸ hQ' v
    have hx' : x ∈ P.D := hx
    have hy' : y ∈ P.D := hy
    have hbxy' : P.b x y = 0 := hbxy
    have h3 : 3 ≤ finrank (ZMod 2) V := by
      have hx0 : x ≠ 0 := P.ne_zero_of_mem hx'
      obtain ⟨z, -, hzx⟩ := P.exists_mem_b_eq_one hx0
      have hyx : y ∉ span (ZMod 2) {x} := by
        intro hmem
        obtain ⟨c, rfl⟩ := mem_span_singleton.mp hmem
        rcases zmod2_eq_zero_or_one c with rfl | rfl
        · exact P.ne_zero_of_mem hy' (zero_smul _ _)
        · exact hxy (one_smul _ _).symm
      have hz : z ∉ span (ZMod 2) {x} ⊔ span (ZMod 2) {y} := by
        intro hmem
        obtain ⟨u, hu, w, hw, rfl⟩ := mem_sup.mp hmem
        obtain ⟨c, rfl⟩ := mem_span_singleton.mp hu
        obtain ⟨c', rfl⟩ := mem_span_singleton.mp hw
        rw [P.b_add_left, map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply,
          P.self_eq_zero, P.comm y x, hbxy', smul_zero, smul_zero, add_zero] at hzx
        exact zero_ne_one hzx
      have h2 := finrank_sup_span_of_notMem hyx
      have h3' := finrank_sup_span_of_notMem hz
      rw [finrank_span_singleton hx0] at h2
      have := Submodule.finrank_le (span (ZMod 2) {x} ⊔ span (ZMod 2) {y} ⊔ span (ZMod 2) {z})
      omega
    have hE : 5 ≤ finrank (ZMod 2) V ∨
        ¬ ∃ W : Submodule (ZMod 2) V, finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0 := by
      by_cases h5 : 5 ≤ finrank (ZMod 2) V
      · exact Or.inl h5
      · right
        have h4 : finrank (ZMod 2) V = 4 := by
          obtain ⟨k, hk⟩ := heven
          omega
        exact P.toSympConfig.not_exists_totallySingular h4 hpol hQ
    refine ⟨heven, Q, ?_, eq_comap_orthogonalGroup hgen P.self_eq_zero P.comm P.nondeg hF4 hF5
      hpol' hQc h3 hE⟩
    have hpb : QuadraticMap.polarBilin Q = P.b := LinearMap.ext₂ fun u v => hpol' u v
    rw [hpb]
    exact hBnd
  ·
    right; right; right
    exact ⟨heven, exists_heart_conj hgen P hPD hF4 hF5 hTN hn⟩

end CFSG.ComponentClassification.OutcomeLocal

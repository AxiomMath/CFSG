module

public import CFSG.HardMathSupport.Dickson.Bal207.FamF42Levi
public import CFSG.HardMathSupport.Dickson.Bal207.FamF42Glue
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoMain
import CFSG.RankThree.Chevalley.SteinbergCFEvenF4StandardParabolic

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.FamF42

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
open scoped MatrixGroups

set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

abbrev connP (k0 k1 k2 k3 : ℕ) : Prop :=
  (∃ e ∈ rts, ∀ γ ∈ rts, kdL k0 k1 k2 k3 γ % 3 = 0 → ipL γ e = 0) →
    (rts.filter (fun γ => kdL k0 k1 k2 k3 γ % 3 = 0)).length = 18 ∧
    ∃ r ∈ rts, kdL k0 k1 k2 k3 r % 3 = 0 ∧ ∀ γ ∈ rts, kdL k0 k1 k2 k3 γ % 3 = 0 →
      ∃ ε ∈ rts, kdL k0 k1 k2 k3 ε % 3 = 0 ∧ ipL γ ε ≠ 0 ∧ ipL ε r ≠ 0

theorem conn_all : ∀ k0 ∈ [0, 1, 2], ∀ k1 ∈ [0, 1, 2], ∀ k2 ∈ [0, 1, 2], ∀ k3 ∈ [0, 1, 2],
    (k0 ≠ 0 ∨ k1 ≠ 0 ∨ k2 ≠ 0 ∨ k3 ≠ 0) → connP k0 k1 k2 k3 := by
  decide +kernel

theorem kernel_conn_of_orth (k : Fin Tag.F4.rank → ℕ)
    (hk3 : ∀ i, k i < 3) (hk0 : ∃ i, k i ≠ 0)
    (he : ∃ e : V4, IsRoot Tag.F4 e ∧
      ∀ γ : V4, IsRoot Tag.F4 γ → kdot k γ % 3 = 0 → ipF4 γ e = 0) :
    {γ : V4 | IsRoot Tag.F4 γ ∧ kdot k γ % 3 = 0}.ncard = 18 ∧
      ∃ r : V4, IsRoot Tag.F4 r ∧ kdot k r % 3 = 0 ∧ ∀ γ : V4, IsRoot Tag.F4 γ →
        kdot k γ % 3 = 0 → ∃ ε : V4, IsRoot Tag.F4 ε ∧ kdot k ε % 3 = 0 ∧ ipF4 γ ε ≠ 0 ∧
          ipF4 ε r ≠ 0 := by
  have hne := exists_ne_zero_idx hk0
  have hm : ∀ n : ℕ, n < 3 → n ∈ [0, 1, 2] := fun n hn => by simp; omega
  have h := conn_all (k (idx 0)) (hm _ (hk3 _)) (k (idx 1)) (hm _ (hk3 _)) (k (idx 2))
    (hm _ (hk3 _)) (k (idx 3)) (hm _ (hk3 _)) hne
  obtain ⟨e, he, hall⟩ := he
  obtain ⟨l, hl, rfl⟩ := (mem_rts_iff e).1 he
  obtain ⟨hcard, r, hr, hrk, hconn⟩ := h ⟨l, hl, fun γ hγ hk => by
    have := hall (vec4 γ) ((mem_rts_iff _).2 ⟨γ, hγ, rfl⟩) (by rwa [kdot_vec4])
    rwa [ipF4_vec4] at this⟩
  refine ⟨?_, vec4 r, (mem_rts_iff _).2 ⟨r, hr, rfl⟩, by rwa [kdot_vec4], fun γ hγ hk => ?_⟩
  · rw [ncard_roots_filter (fun γ : V4 => kdot k γ % 3 = 0)]
    exact hcard
  · obtain ⟨l', hl', rfl⟩ := (mem_rts_iff γ).1 hγ
    obtain ⟨ε, hε, hεk, h1, h2⟩ := hconn l' hl' (by rwa [kdot_vec4] at hk)
    exact ⟨vec4 ε, (mem_rts_iff _).2 ⟨ε, hε, rfl⟩, by rwa [kdot_vec4], by rwa [ipF4_vec4],
      by rwa [ipF4_vec4]⟩

theorem eq_of_kernel_conn {L : Type} [Field L] {a : Fin Tag.F4.rank → Lˣ} {ω : Lˣ}
    {k : Fin Tag.F4.rank → ℕ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hak : ∀ i, a i = ω ^ k i)
    (hconn : ∃ r : V4, IsRoot Tag.F4 r ∧ kdot k r % 3 = 0 ∧ ∀ γ : V4, IsRoot Tag.F4 γ →
      kdot k γ % 3 = 0 → ∃ ε : V4, IsRoot Tag.F4 ε ∧ kdot k ε % 3 = 0 ∧ ipF4 γ ε ≠ 0 ∧
        ipF4 ε r ≠ 0)
    (i j : KernelComponent (rootCharHom a)) : i = j := by
  have hker : ∀ γ : V4, γ ∈ kernelRoots (rootCharHom a) ↔ IsRoot Tag.F4 γ ∧ kdot k γ % 3 = 0 :=
    fun γ => and_congr_right fun _ => rootChar_eq_one_iff hω3 hω1 hak γ
  obtain ⟨r, hr, hrk, hconn⟩ := hconn
  have hrel : ∀ γ δ : kernelRoots (rootCharHom a), ipF4 (γ : V4) δ ≠ 0 →
      (⟦γ⟧ : KernelComponent (rootCharHom a)) = ⟦δ⟧ := by
    intro γ δ h
    refine Quotient.sound (Relation.EqvGen.rel _ _ ?_)
    rw [dotProduct_mulVec_eq_iform, iform_F4]
    exact h
  have hall : ∀ c : KernelComponent (rootCharHom a), c = ⟦⟨r, (hker r).2 ⟨hr, hrk⟩⟩⟧ := by
    intro c
    induction c using Quotient.ind with
    | _ γ =>
      obtain ⟨ε, hε, hεk, h1, h2⟩ := hconn γ ((hker γ).1 γ.2).1 ((hker γ).1 γ.2).2
      exact (hrel γ ⟨ε, (hker ε).2 ⟨hε, hεk⟩⟩ h1).trans (hrel _ _ h2)
  rw [hall i, hall j]

@[expose] def F42CompType (Q : Type) [Group Q] : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
    Nonempty (Q ≃* (StatedSp 3 F ⧸ Subgroup.center (StatedSp 3 F)))

theorem isoInvariant_f42CompType : IsoInvariant F42CompType := by
  rintro Q Q' _ _ e ⟨F, hF1, hF2, hF, ⟨f⟩⟩
  exact ⟨F, hF1, hF2, hF, ⟨e.symm.trans f⟩⟩

section Lang


variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}

theorem isSolvable_rationalComponent_of_a2a2 (S : LangSetup Tag.F4 L p₀)
    {a : Fin Tag.F4.rank → Lˣ} (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1)
    {ω : Lˣ} {k : Fin Tag.F4.rank → ℕ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hk3 : ∀ i, k i < 3)
    (hk0 : ∃ i, k i ≠ 0) (hak : ∀ i, a i = ω ^ k i) (hk : KernelA2A2 k) (hq2 : S.D.q = 2)
    (j : KernelComponent (rootCharHom a)) :
    Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) j) := by
  classical
  obtain ⟨σ, τ, κ, κ', ψ, ψ', iΛ, iΘ, hP, hψ, hψ', hΛ, hΘ, hSig, hall, hρΛ, hρΘ⟩ :=
    exists_pair_frames S hT hap hω3 hω1 hak hk
  have hSig' : ∀ γ : V4, IsRoot Tag.F4 γ → kdot k γ % 3 = 0 →
      γ ∈ frameRoots τ ∨ γ ∈ frameRoots σ := fun γ h1 h2 => (hSig γ h1 h2).symm
  have hqmod : S.D.q % 3 = 2 := by rw [hq2]
  obtain ⟨π₁, hπ₁⟩ := exists_outer_shape S hT hω3 hω1 hk3 hk0 hak hP hψ hSig hqmod hρΛ
  obtain ⟨π₂, hπ₂⟩ := exists_outer_shape S hT hω3 hω1 hk3 hk0 hak hP.symm hψ' hSig' hqmod hρΘ
  have hs1Λ : componentOrbitLength S.ρ (componentRoots (rootCharHom a) iΛ) = 1 :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.componentOrbitLength_eq_one S hT iΛ
      (by rw [hΛ]; exact hρΛ)
  have hs1Θ : componentOrbitLength S.ρ (componentRoots (rootCharHom a) iΘ) = 1 :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.componentOrbitLength_eq_one S hT iΘ
      (by rw [hΘ]; exact hρΘ)
  have hπ₁' : ∀ x y : Fin 3, x ≠ y →
      (S.ρ : V4 → V4)^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) iΛ)] (σ x y) =
        σ (π₁ y) (π₁ x) := by
    intro x y hxy
    rw [hs1Λ, Function.iterate_one]
    exact hπ₁ x y hxy
  have hπ₂' : ∀ x y : Fin 3, x ≠ y →
      (S.ρ : V4 → V4)^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) iΘ)] (τ x y) =
        τ (π₂ y) (π₂ x) := by
    intro x y hxy
    rw [hs1Θ, Function.iterate_one]
    exact hπ₂ x y hxy
  have hRU := rationalComponent_of_unitary_frame_T S hT iΛ (le_refl 3)
    (IsSLFrame.of_isA2Frame hψ) hΛ π₁ hπ₁'
  have hRU' := rationalComponent_of_unitary_frame_T S hT iΘ (le_refl 3)
    (IsSLFrame.of_isA2Frame hψ') hΘ π₂ hπ₂'
  rcases hall j with rfl | rfl
  · exact isSolvable_of_card_dvd_216 (hRU.2 (by rw [hs1Λ, pow_one, hq2]))
  · exact isSolvable_of_card_dvd_216 (hRU'.2 (by rw [hs1Θ, pow_one, hq2]))

theorem exists_sp3_cover (S : LangSetup Tag.F4 L p₀) (hq2 : S.D.q = 2)
    {a : Fin Tag.F4.rank → Lˣ} (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) (v : WeylGroup Tag.F4) {J : Set (Fin (Tag.rank .F4))}
    (hJ : J = f4LeviB3 ∨ J = CFSG.ComponentClassification.CatLeafProof.f4LeviC3)
    (hroots : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots Tag.F4 J)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1) :
    ∃ F : Subfield L, Finite ↥F ∧ Nat.card ↥F = 2 ∧
      ∃ g : StatedSp 3 ↥F →* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i),
        Function.Surjective g ∧ g.ker ≤ Subgroup.center (StatedSp 3 ↥F) := by
  classical
  obtain ⟨σ, hfin, hcard, f, hf1, hker, hf2⟩ := exists_inner_cover S hT i hinner
  have hF2 : Nat.card ↥(fixSubfield σ) = 2 := by rw [hcard, hs1, pow_one, hq2]
  obtain ⟨Ψ, hΨk, hΨr⟩ : ∃ Ψ : StatedSp 3 ↥(fixSubfield σ) →* ModGL Tag.F4 ↥(fixSubfield σ),
      Ψ.ker ≤ Subgroup.center (StatedSp 3 ↥(fixSubfield σ)) ∧
        Ψ.range = subsystemGroup .F4 ↥(fixSubfield σ) J := by
    rcases hJ with rfl | rfl
    · exact exists_sp3Hom_f4_B3_two hF2
    · exact exists_sp3Hom_f4_C3 Nat.prime_two Nat.one_pos (by rw [hF2]; norm_num)
  have hsub : subsystemGroup Tag.F4 ↥(fixSubfield σ) J =
      rootSpan Tag.F4 ↥(fixSubfield σ) (parabolicRoots Tag.F4 J) :=
    CFSG.RankThree.Chevalley.subsystemGroup_eq_iSup_rootSubgroup (τ := Tag.F4) (J := J) _
  obtain ⟨Ψv, hΨvr, hΨvk⟩ : ∃ Ψv : StatedSp 3 ↥(fixSubfield σ) →* ModGL Tag.F4 ↥(fixSubfield σ),
      Ψv.range = componentRootSpan (fixSubfield σ) (rootCharHom a) i ∧
        Ψv.ker ≤ Subgroup.center (StatedSp 3 ↥(fixSubfield σ)) := by
    refine ⟨(MulAut.conj
      (canonicalRep (coxeterSystem Tag.F4) (↥(fixSubfield σ)) v)).toMonoidHom.comp Ψ, ?_,
      fun y hy => hΨk ?_⟩
    · rw [MonoidHom.range_comp, hΨr, hsub,
        (canonical_weyl_root_transport Tag.F4 ↥(fixSubfield σ)).1 v _ (fun α hα => hα.1)]
      show _ = rootSpan Tag.F4 _ (componentRoots (rootCharHom a) i)
      rw [hroots]
    · rw [MonoidHom.mem_ker] at hy ⊢
      refine (MulAut.conj (canonicalRep (coxeterSystem Tag.F4) (↥(fixSubfield σ)) v)).injective ?_
      rw [map_one]
      exact hy
  haveI hperf : Group.IsPerfect (StatedSp 3 ↥(fixSubfield σ)) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp 3 _ (Or.inr (Or.inr ⟨hF2, le_rfl⟩))
  have hmem : ∀ y, Ψv y ∈ componentRootSpan (fixSubfield σ) (rootCharHom a) i :=
    fun y => hΨvr ▸ ⟨y, rfl⟩
  let g₀ := Ψv.codRestrict _ hmem
  have hg₀ : Function.Surjective g₀ := by
    rintro ⟨c, hc⟩
    obtain ⟨y, hy⟩ : c ∈ Ψv.range := hΨvr ▸ hc
    exact ⟨y, Subtype.ext hy⟩
  have hg₀k : g₀.ker ≤ Subgroup.center (StatedSp 3 ↥(fixSubfield σ)) := fun y hy =>
    hΨvk (by rw [MonoidHom.mem_ker] at hy ⊢; exact congrArg Subtype.val hy)
  have hCperf := Subgroup.isPerfect_iff.1 (Group.IsPerfect.ofSurjective (f := g₀) hg₀)
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    le_antisymm (hf2 hCperf) hf1
  have hmem' : ∀ y, f (g₀ y) ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    fun y => hRf ▸ ⟨g₀ y, rfl⟩
  refine ⟨fixSubfield σ, hfin, hF2, (f.comp g₀).codRestrict _ hmem', ?_, fun y hy => ?_⟩
  · rintro ⟨r, hr⟩
    obtain ⟨c, hc⟩ : r ∈ f.range := hRf ▸ hr
    obtain ⟨y, rfl⟩ := hg₀ c
    exact ⟨y, Subtype.ext hc⟩
  · rw [MonoidHom.mem_ker] at hy
    have h1 : f (g₀ y) = 1 := congrArg Subtype.val hy
    have h2 : g₀ y ∈ Subgroup.center _ := hker (MonoidHom.mem_ker.2 h1)
    rw [← comap_center_of_surjective (Group.isPerfect_def.1 hperf) g₀ hg₀ hg₀k]
    exact h2

theorem compShape_conj_F4_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (x : ↥(adjointGroup Tag.F4 K)) (hx : orderOf x = 3) :
    CompShape F42CompType (MulAut.conj x) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : Finite ↥(adjointGroup Tag.F4 K) := by
    have : Finite (Module.End K (RootModule Tag.F4 K)) := Module.finite_of_finite K
    infer_instance
  have hpK : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    norm_num
  obtain ⟨p₀, S, a, ι, hSq, hT, hap, h1, hinj, hrange, -, hconj, hTame⟩ :=
    exists_langSetup_F4_of_orderOf_eq_three hpK x hx
  have hq2 : S.D.q = 2 := hSq.trans hK
  obtain ⟨ω, k, hω3, hω1, hk3, hak⟩ := exists_omega_param (L := AlgebraicClosure K) hap
  have hk0 : ∃ i, k i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply h1
    rw [show a = 1 from funext fun i => by rw [hak i, hcon i, pow_zero]; rfl, rootDiagUnit_one]
  have hlayer := perfectInLayer_of_langSetup_of_prime S Nat.prime_three ι hinj hrange
    (MulAut.conj x) hconj hT hap h1 hTame
  have hcomp : ∀ L : Subgroup ↥(adjointGroup Tag.F4 K),
      CFSG.Open.IsComponentOf L (fixSubgroup (MulAut.conj x)) →
        ∃ i : KernelComponent (rootCharHom a),
          CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
            L.map ι = rationalComponent S.ρ S.Γ (rootCharHom a) i := fun L hL =>
    components_of_langSetup S Nat.prime_three ι hinj hrange (MulAut.conj x) hconj hT hap h1
      hTame hL
  rcases classify_kernel k hk3 hk0 with he | hA2
  ·
    obtain ⟨hcard, hconn⟩ := kernel_conn_of_orth k hk3 hk0 he
    have huniq : ∀ i j : KernelComponent (rootCharHom a), i = j :=
      eq_of_kernel_conn hω3 hω1 hak hconn
    have hker : kernelRoots (rootCharHom a) = {γ : V4 | IsRoot Tag.F4 γ ∧ kdot k γ % 3 = 0} :=
      Set.ext fun γ => and_congr_right fun _ => rootChar_eq_one_iff hω3 hω1 hak γ
    have hroots_eq : ∀ i : KernelComponent (rootCharHom a),
        componentRoots (rootCharHom a) i = kernelRoots (rootCharHom a) := fun i =>
      Set.ext fun γ => ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, huniq _ _⟩⟩
    have hn18 : ∀ i, (componentRoots (rootCharHom a) i).ncard = 18 := fun i => by
      rw [hroots_eq i, hker]
      exact hcard
    refine compShape_of_subsingleton _ hlayer (fun L L' hL hL' => ?_) (fun L hL => ?_)
    · obtain ⟨i, -, hi⟩ := hcomp L hL
      obtain ⟨j, -, hj⟩ := hcomp L' hL'
      rw [huniq i j] at hi
      exact Subgroup.map_injective hinj (hi.trans hj.symm)
    · obtain ⟨i, -, hi⟩ := hcomp L hL
      have hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
          (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) + 1)) := by
        rintro ⟨-, h2⟩
        rw [hn18 i] at h2
        generalize compRank (componentRoots (rootCharHom a) i) = r at h2
        have hr : r ≤ 4 := by nlinarith
        interval_cases r <;> omega
      have hℓp : ringChar (AlgebraicClosure K) ≠ 3 :=
        ringChar_ne_of_pow_eq_one Nat.prime_three hap h1
      have hpL : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 :=
        natCast_ne_zero_of_ringChar_ne Nat.prime_three hℓp
      rcases f4_nonA_casesP Nat.prime_three (by norm_num) S hpL
          (rootDiagUnit_pow_eq_one_of_forall hap) h1 i hnonA with
        ⟨-, hn⟩ | ⟨v, J, hJ, hroots, hr3, -⟩
      · rw [hn18 i] at hn
        omega
      have hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 := by
        refine CFSG.HardMathSupport.Timmesfeld.LangTorus.componentOrbitLength_eq_one
          (Set.finite_of_ncard_ne_zero (by rw [hn18 i]; norm_num)) fun γ hγ => ?_
        rw [hroots_eq i] at hγ ⊢
        exact outer_rho_mem_kernelRoots S hT hγ
      have hinner := twistInner_of_shape S hT i 3 18 hr3 (hn18 i) (by decide) (by decide)
        (by decide) (by decide)
      obtain ⟨F, hfin, hF2, g, hg, hgk⟩ := exists_sp3_cover S hq2 hT i v hJ hroots hinner hs1
      have hperf : commutator (StatedSp 3 ↥F) = ⊤ := Group.isPerfect_def.1
        (CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp 3 _ (Or.inr (Or.inr ⟨hF2, le_rfl⟩)))
      obtain ⟨eR⟩ := nonempty_centralQuotient_mulEquiv hperf g hg hgk
      let eL : ↥L ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
        (L.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hi)
      exact ⟨↥F, inferInstance, hfin, hF2, ⟨(centerQuotientCongr eL).trans eR.symm⟩⟩
  ·
    have hno : ∀ L : Subgroup ↥(adjointGroup Tag.F4 K),
        ¬ CFSG.Open.IsComponentOf L (fixSubgroup (MulAut.conj x)) := fun L hL => by
      obtain ⟨i, hiq, -⟩ := hcomp L hL
      exact not_isSolvable_of_isQuasisimple' hiq
        (isSolvable_rationalComponent_of_a2a2 S hT hap hω3 hω1 hk3 hk0 hak hA2 hq2 i)
    exact compShape_of_subsingleton _ hlayer (fun L _ hL _ => absurd hL (hno L))
      (fun L hL => absurd hL (hno L))

end Lang

end CFSG.HardMathSupport.Dickson.Bal207.FamF42

end

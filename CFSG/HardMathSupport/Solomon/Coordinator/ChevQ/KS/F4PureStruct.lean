module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.F4StdModel
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.F4SU3Rank

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSF4Pure

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KF4 CFSG.Timmesfeld
  CFSG.ComponentClassification.CatLeafProof
open scoped MatrixGroups

set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

section Frame


variable {L : Type} [Field L] [IsAlgClosed L]

theorem frame_omega_eq_pow {a : Fin Tag.F4.rank → Lˣ} {ω : Lˣ} {k : Fin Tag.F4.rank → ℕ}
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hk3 : ∀ i, k i < 3) (hk0 : ∃ i, k i ≠ 0)
    (hak : ∀ i, a i = ω ^ k i) {σ τ : Fin 3 → Fin 3 → V4} {κ κ' : ℤ} (hP : A2Pair σ τ κ κ')
    {ψ : SL(3, L) →* ModGL Tag.F4 L} (hψ : IsA2Frame ψ σ)
    (hSig : ∀ γ : V4, IsRoot Tag.F4 γ → kdot k γ % 3 = 0 → γ ∈ frameRoots σ ∨ γ ∈ frameRoots τ) :
    ∃ m : ℕ, ψ (diagSL3 (fun _ => ω) (omega_det hω3)) = rootDiagUnit Tag.F4 a ^ m := by
  classical
  have hord : orderOf ω = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hω3 hω1
  set l : Fin 3 → Lˣ := fun _ => ω with hl
  have hl1 : l 0 * l 1 * l 2 = 1 := omega_det hω3
  obtain ⟨b, hb⟩ := exists_param_of_diag hψ l hl1
  have hchar : ∀ v : V4, rootChar b v = ω ^ (lab1 σ κ v + 2 * lab2 σ κ v) := by
    intro v
    rw [hP.diag_chars hψ hb v]
    show ω ^ _ * ω ^ _ = _
    rw [← zpow_add]
    congr 1
    ring
  have hb3 : ∀ i, ∃ n : ℕ, n < 3 ∧ b i = ω ^ n := by
    intro i
    have h1 := hchar (Pi.single i 1)
    rw [rootChar_single'] at h1
    refine ⟨((lab1 σ κ (Pi.single i 1) + 2 * lab2 σ κ (Pi.single i 1)) % 3).toNat, ?_, ?_⟩
    · omega
    · rw [h1, ← zpow_natCast, zpow_eq_zpow_iff_mod hω3 hω1]
      omega
  choose β hβ3 hbβ using hb3
  have hbSig : ∀ γ : V4, IsRoot Tag.F4 γ → kdot k γ % 3 = 0 → kdot β γ % 3 = 0 := by
    intro γ hγ hk
    have h1 : rootChar b γ = 1 := by
      rcases hSig γ hγ hk with ⟨x, y, hxy, rfl⟩ | hτ
      · rw [char_frame_root hψ hb hxy]
        simp [hl]
      · exact char_orth_root hψ hb hγ (fun x y hxy c c' => hP.comm γ hτ x y hxy c c')
    exact (rootChar_eq_one_iff hω3 hω1 hbβ γ).1 h1
  obtain ⟨m, hm3, hmk⟩ := unique_of_orth_kernel k β hk3 hk0 hβ3 hbSig
  have hbm : b = a ^ m := by
    funext i
    have h1 := pow_mod_orderOf ω (m * k i)
    rw [hord] at h1
    rw [hbβ i, hmk i, Pi.pow_apply, hak i, ← pow_mul, mul_comm (k i) m, h1]
  refine ⟨m, ?_⟩
  rw [hb, hbm]
  exact (rootDiagUnitHom Tag.F4 L).map_pow a m

end Frame


section Classes


variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}

open KSF4Std in
theorem classB_isB3 (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1) (hq : S.D.q = 8)
    (hpL : ((3 : ℕ) : L) ≠ 0) {ω : Lˣ} {k : Fin Tag.F4.rank → ℕ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (hak : ∀ i, a i = ω ^ k i) (hk : KernelB k) (i : KernelComponent (rootCharHom a)) :
    CFSG.Open.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
      IsLieQuot ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) KSF4Out.IsB3EightIndex := by
  classical
  have hT3 : rootDiagUnit Tag.F4 a ^ 3 = 1 := rootDiagUnit_pow_eq_one hap
  obtain ⟨v, μ, x, c, hμ, hc, hcomp, hlen, hroots, hrank, hncard⟩ :=
    exists_cand_of_class kacF4 facts_F4 f4_tree f4_adj f4_check f4_lt f4_card S Nat.prime_three
      hpL hT3 i
  have hn18 := ncard_componentRoots_of_kernelB hω3 hω1 hak hk i
  have hc18 : c = [1, 2, 3] ∨ c = [2, 3, 4] := by
    exact f4_count18 c hc (hncard.symm.trans hn18)
  have hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 :=
    componentOrbitLength_eq_one S hT i (rho_image_eq_of_kernelB S hT hω3 hω1 hak hk i)
  have hQ : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 8 := by
    rw [hs1, hq]
    norm_num
  rcases hc18 with rfl | rfl
  · have hr3 : compRank (componentRoots (rootCharHom a) i) = 3 := by rw [hrank]; rfl
    have hroots' : componentRoots (rootCharHom a) i =
        (fun α => v • α) '' parabolicRoots Tag.F4 f4LeviB3 := by
      rw [hroots, rootsOf_eq_parabolicRoots kacF4 facts_F4 (J := f4LeviB3) (by decide)
        (fun j => by rw [mem_f4LeviB3]; revert j; decide)]
    obtain ⟨hqs, hmodel⟩ := KSExactSp.rationalComponent_sp3_model S hT i v (J := f4LeviB3)
      (Or.inl rfl) hroots' (twistInner_of_rank3_card18 S hT i hr3 hn18) hQ
    exact ⟨hqs, KSExactSp.isLieQuot_of_B_model hmodel (by norm_num) _
      (fun q hp he => ⟨q, ⟨hp, he⟩, rfl⟩)⟩
  · have hr3 : compRank (componentRoots (rootCharHom a) i) = 3 := by rw [hrank]; rfl
    have hroots' : componentRoots (rootCharHom a) i =
        (fun α => v • α) '' parabolicRoots Tag.F4 f4LeviC3 := by
      rw [hroots, rootsOf_eq_parabolicRoots kacF4 facts_F4 (J := f4LeviC3) (by decide)
        (fun j => by rw [mem_f4LeviC3]; revert j; decide)]
    obtain ⟨hqs, hmodel⟩ := KSExactSp.rationalComponent_sp3_model S hT i v (J := f4LeviC3)
      (Or.inr rfl) hroots' (twistInner_of_rank3_card18 S hT i hr3 hn18) hQ
    exact ⟨hqs, KSExactSp.isLieQuot_of_B_model hmodel (by norm_num) _
      (fun q hp he => ⟨q, ⟨hp, he⟩, rfl⟩)⟩

open KSF4Std in
theorem classesA2A2_U3 (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1)
    (h1 : rootDiagUnit Tag.F4 a ≠ 1) (hq : S.D.q = 8)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    {ω : Lˣ} {k : Fin Tag.F4.rank → ℕ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hk3 : ∀ i, k i < 3)
    (hk0 : ∃ i, k i ≠ 0) (hak : ∀ i, a i = ω ^ k i) (hk : KernelA2A2 k) :
    (∀ i : KernelComponent (rootCharHom a),
      CFSG.Open.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
        IsLieQuot ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) KSF4SU3.IsU3EightIndexTwo ∧
        rootDiagUnit Tag.F4 a ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
    ∀ i j l : KernelComponent (rootCharHom a), i = j ∨ i = l ∨ j = l := by
  classical
  obtain ⟨σ, τ, κ, κ', ψ, ψ', iΛ, iΘ, hP, hψ, hψ', hΛ, hΘ, hSig, hall, hρσ, hρτ⟩ :=
    exists_pair_frames S hT hap hω3 hω1 hak hk
  have hq3 : S.D.q % 3 = 2 := by rw [hq]
  have hSig' : ∀ γ : V4, IsRoot Tag.F4 γ → kdot k γ % 3 = 0 →
      γ ∈ frameRoots τ ∨ γ ∈ frameRoots σ := fun γ h1 h2 => (hSig γ h1 h2).symm
  obtain ⟨π, hπ⟩ := exists_outer_shape S hT hω3 hω1 hk3 hk0 hak hP hψ hSig hq3 hρσ
  obtain ⟨π', hπ'⟩ := exists_outer_shape S hT hω3 hω1 hk3 hk0 hak hP.symm hψ' hSig' hq3 hρτ
  have hψSL := IsSLFrame.of_isA2Frame hψ
  have hψSL' := IsSLFrame.of_isA2Frame hψ'
  have hs1Λ : componentOrbitLength S.ρ (componentRoots (rootCharHom a) iΛ) = 1 :=
    componentOrbitLength_eq_one S hT iΛ (by rw [hΛ]; exact hρσ)
  have hs1Θ : componentOrbitLength S.ρ (componentRoots (rootCharHom a) iΘ) = 1 :=
    componentOrbitLength_eq_one S hT iΘ (by rw [hΘ]; exact hρτ)
  have hΛtype : CFSG.Open.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) iΛ) ∧
      IsLieQuot ↥(rationalComponent S.ρ S.Γ (rootCharHom a) iΛ) KSF4SU3.IsU3EightIndexTwo := by
    obtain ⟨hqs, hmodel⟩ := rationalComponent_su3_model S hT iΛ hψSL hΛ π hπ hs1Λ hq (hTame iΛ)
    exact ⟨hqs, KSExact.isLieQuot_of_twistedA_model hmodel _
      (fun q hp he => ⟨q, ⟨hp, he⟩, rfl⟩)⟩
  have hΘtype : CFSG.Open.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) iΘ) ∧
      IsLieQuot ↥(rationalComponent S.ρ S.Γ (rootCharHom a) iΘ) KSF4SU3.IsU3EightIndexTwo := by
    obtain ⟨hqs, hmodel⟩ := rationalComponent_su3_model S hT iΘ hψSL' hΘ π' hπ' hs1Θ hq (hTame iΘ)
    exact ⟨hqs, KSExact.isLieQuot_of_twistedA_model hmodel _
      (fun q hp he => ⟨q, ⟨hp, he⟩, rfl⟩)⟩
  have hq2 : S.D.q ≠ 2 := by rw [hq]; norm_num
  obtain ⟨σQ, hσc⟩ := exists_sigmaQ S
  obtain ⟨B₁, hB₁⟩ := exists_unitary_pinning S (le_refl 3) hψSL π hπ σQ hσc
  obtain ⟨B₂, hB₂⟩ := exists_unitary_pinning S (le_refl 3) hψSL' π' hπ' σQ hσc
  have hψS : ∀ X : SL(3, L), ψ X ∈ rootSpan Tag.F4 L (componentRoots (rootCharHom a) iΛ) :=
    fun X => by
      rw [hΛ, ← hψSL.range]
      exact ⟨X, rfl⟩
  have hψS' : ∀ X : SL(3, L), ψ' X ∈ rootSpan Tag.F4 L (componentRoots (rootCharHom a) iΘ) :=
    fun X => by
      rw [hΘ, ← hψSL'.range]
      exact ⟨X, rfl⟩
  have hy₁ : ψ B₁ * ψ' B₂ ∈ rootSpan Tag.F4 L (kernelRoots (rootCharHom a)) :=
    mul_mem (rootSpan_mono (fun γ hγ => hγ.1) (hψS B₁))
      (rootSpan_mono (fun γ hγ => hγ.1) (hψS' B₂))
  obtain ⟨z, hzZ, hnorm, hc₁, hc₂⟩ :=
    exists_common_lang S hT B₁ B₂ σQ hB₁ hB₂ (hP.commute_frames hψ hψ') hy₁
  have hperf := fix_perfect S hσc hq2
  have hmemΛ : ∀ X : SL(3, L), stdUnitary σQ.toRingHom X = X →
      z * ψ X * z⁻¹ ∈ rationalComponent S.ρ S.Γ (rootCharHom a) iΛ := fun X hX =>
    conj_mem_rationalComponent S iΛ hψSL hΛ (fun g hg => (hnorm iΛ g).1 hg) hc₁ hperf hX
  have hmemΘ : ∀ X : SL(3, L), stdUnitary σQ.toRingHom X = X →
      z * ψ' X * z⁻¹ ∈ rationalComponent S.ρ S.Γ (rootCharHom a) iΘ := fun X hX =>
    conj_mem_rationalComponent S iΘ hψSL' hΘ (fun g hg => (hnorm iΘ g).1 hg) hc₂ hperf hX
  have hωu : ω ^ (S.D.q + 1) = 1 := by
    obtain ⟨t, ht⟩ : 3 ∣ S.D.q + 1 := by omega
    rw [ht, pow_mul, hω3, one_pow]
  have hωC : stdUnitary σQ.toRingHom (diagSL3 (fun _ => ω) (omega_det hω3)) =
      diagSL3 (fun _ => ω) (omega_det hω3) :=
    stdUnitary_diagSL3_eq_self _ _ _ (fun i => scalar_unitary hσc ω hωu)
  have hd3 : rootDiagUnit Tag.F4 a ^ 3 = 1 := rootDiagUnit_pow_eq_one hap
  have hcommd : rootDiagUnit Tag.F4 a * z = z * rootDiagUnit Tag.F4 a :=
    commute_of_mem_torus_sup_kernel S hzZ
  have hdpow : ∀ (R : Subgroup (ModGL Tag.F4 L)) (m : ℕ),
      z * rootDiagUnit Tag.F4 a ^ m * z⁻¹ ∈ R →
        orderOf (z * rootDiagUnit Tag.F4 a ^ m * z⁻¹) = 3 → rootDiagUnit Tag.F4 a ∈ R := by
    intro R m hmem hord
    have hzd : z * rootDiagUnit Tag.F4 a ^ m * z⁻¹ = rootDiagUnit Tag.F4 a ^ m := by
      have hc : Commute (rootDiagUnit Tag.F4 a ^ m) z :=
        Commute.pow_left (show Commute (rootDiagUnit Tag.F4 a) z from hcommd) m
      calc z * rootDiagUnit Tag.F4 a ^ m * z⁻¹ = (z * rootDiagUnit Tag.F4 a ^ m) * z⁻¹ := rfl
        _ = (rootDiagUnit Tag.F4 a ^ m * z) * z⁻¹ := by rw [hc.eq]
        _ = rootDiagUnit Tag.F4 a ^ m := by group
    rw [hzd] at hmem hord
    have h3m : ¬ (3 : ℤ) ∣ (m : ℤ) := by
      intro h
      have h3 : 3 ∣ m := by exact_mod_cast h
      obtain ⟨t, rfl⟩ := h3
      rw [pow_mul, hd3, one_pow, orderOf_one] at hord
      omega
    refine Bal209F4Aux.mem_of_zpow_mem hd3 h1 h3m ?_
    rwa [zpow_natCast]
  have hdΛ : rootDiagUnit Tag.F4 a ∈ rationalComponent S.ρ S.Γ (rootCharHom a) iΛ := by
    obtain ⟨m, hm⟩ := frame_omega_eq_pow hω3 hω1 hk3 hk0 hak hP hψ hSig
    have hmem := hmemΛ _ hωC
    have hord := orderOf_conj_frame_omega hψ.injective hω3 hω1 z
    rw [hm] at hmem hord
    exact hdpow _ m hmem hord
  have hdΘ : rootDiagUnit Tag.F4 a ∈ rationalComponent S.ρ S.Γ (rootCharHom a) iΘ := by
    obtain ⟨m, hm⟩ := frame_omega_eq_pow hω3 hω1 hk3 hk0 hak hP.symm hψ' hSig'
    have hmem := hmemΘ _ hωC
    have hord := orderOf_conj_frame_omega hψ'.injective hω3 hω1 z
    rw [hm] at hmem hord
    exact hdpow _ m hmem hord
  refine ⟨fun i => ?_, fun i j l => ?_⟩
  · rcases hall i with rfl | rfl
    · exact ⟨hΛtype.1, hΛtype.2, hdΛ⟩
    · exact ⟨hΘtype.1, hΘtype.2, hdΘ⟩
  · rcases hall i with rfl | rfl <;> rcases hall j with rfl | rfl <;>
      rcases hall l with rfl | rfl <;> simp

end Classes

section Struct


@[expose] def F4EightStruct : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → IsLieQuot K IsF4EightIndex →
    ∀ u : K, orderOf u = 3 →
      (∀ J : Subgroup K, GLAPComponent 3 (Subgroup.centralizer ({u} : Set K)) J →
        IsComponentOf J (Subgroup.centralizer ({u} : Set K))) ∧
      (∀ P : Subgroup K, P ≤ Subgroup.centralizer ({u} : Set K) → ⁅P, P⁆ = P →
        P ≤ GLALayer (Subgroup.centralizer ({u} : Set K))) ∧
      (∀ J₁ J₂ J₃ : Subgroup K, IsComponentOf J₁ (Subgroup.centralizer ({u} : Set K)) →
        IsComponentOf J₂ (Subgroup.centralizer ({u} : Set K)) →
        IsComponentOf J₃ (Subgroup.centralizer ({u} : Set K)) → J₁ = J₂ ∨ J₁ = J₃ ∨ J₂ = J₃) ∧
      ((∀ J : Subgroup K, IsComponentOf J (Subgroup.centralizer ({u} : Set K)) →
          IsLieQuot ↥J KSF4Out.IsB3EightIndex) ∨
       (∀ J : Subgroup K, IsComponentOf J (Subgroup.centralizer ({u} : Set K)) →
          IsLieQuot ↥J KSF4SU3.IsU3EightIndexTwo ∧ u ∈ J))

theorem f4EightStruct_lang {K : Type} [Group K] [Finite K]
    (e : K ≃* ↥(adjointGroup Tag.F4 (GaloisField 2 3))) (u : K) (hu3 : orderOf u = 3) :
    (∀ P : Subgroup K, P ≤ Subgroup.centralizer ({u} : Set K) → ⁅P, P⁆ = P →
        P ≤ GLALayer (Subgroup.centralizer ({u} : Set K))) ∧
      (∀ J₁ J₂ J₃ : Subgroup K, IsComponentOf J₁ (Subgroup.centralizer ({u} : Set K)) →
        IsComponentOf J₂ (Subgroup.centralizer ({u} : Set K)) →
        IsComponentOf J₃ (Subgroup.centralizer ({u} : Set K)) → J₁ = J₂ ∨ J₁ = J₃ ∨ J₂ = J₃) ∧
      ((∀ J : Subgroup K, IsComponentOf J (Subgroup.centralizer ({u} : Set K)) →
          IsLieQuot ↥J KSF4Out.IsB3EightIndex) ∨
       (∀ J : Subgroup K, IsComponentOf J (Subgroup.centralizer ({u} : Set K)) →
          IsLieQuot ↥J KSF4SU3.IsU3EightIndexTwo ∧ u ∈ J)) := by
  classical
  have hs : orderOf (e u) = 3 := by rw [MulEquiv.orderOf_eq]; exact hu3
  have hcardK : Nat.card (GaloisField 2 3) = 2 ^ 3 := GaloisField.card 2 3 (by norm_num)
  have hpK : ¬ 3 ∣ Nat.card (GaloisField 2 3) := by rw [hcardK]; norm_num
  obtain ⟨p₀, S, a, ι, hq, hT, hap, h1, hinj, hrange, hxι, hconj, hTame⟩ :=
    exists_langSetup_F4_of_orderOf_eq_three hpK (e u) hs
  have hq8 : S.D.q = 8 := by rw [hq, hcardK]; norm_num
  have hpL : ((3 : ℕ) : AlgebraicClosure (GaloisField 2 3)) ≠ 0 :=
    LieSemisimple.natCast_ne_zero_algebraicClosure Nat.prime_three hpK
  haveI : CharP (AlgebraicClosure (GaloisField 2 3)) 2 := inferInstance
  set ι' : K →* ModGL Tag.F4 (AlgebraicClosure (GaloisField 2 3)) := ι.comp e.toMonoidHom with hι'
  have hinj' : Function.Injective ι' := hinj.comp e.injective
  have hrange' : ι'.range = S.Γ := by
    rw [← hrange]
    ext y
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨e c, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨e.symm g, by simp [hι']⟩
  have hβ : ∀ c : K, ι' (MulAut.conj u c) =
      rootDiagUnit Tag.F4 a * ι' c * (rootDiagUnit Tag.F4 a)⁻¹ := by
    intro c
    have h := hconj (e c)
    have e1 : ι' (MulAut.conj u c) = ι (MulAut.conj (e u) (e c)) := by
      simp [hι', MulAut.conj_apply, map_mul, map_inv]
    rw [e1, h]
    rfl
  have hkey : ∀ J : Subgroup K, IsComponentOf J (Subgroup.centralizer ({u} : Set K)) →
      ∃ i : KernelComponent (rootCharHom a),
        CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
          J.map ι' = rationalComponent S.ρ S.Γ (rootCharHom a) i := fun J hJ =>
    components_of_langSetup S Nat.prime_three ι' hinj' hrange' (MulAut.conj u) hβ hT hap h1 hTame
      (by rwa [KSF4Rank.fixSubgroup_conj_eq'])
  have hmap : ∀ {A B : Subgroup K}, A.map ι' = B.map ι' → A = B := fun h =>
    Subgroup.map_injective hinj' h
  have hequiv : ∀ (J : Subgroup K) (i : KernelComponent (rootCharHom a)),
      J.map ι' = rationalComponent S.ρ S.Γ (rootCharHom a) i →
        ↥J ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := fun J i h =>
    (Subgroup.equivMapOfInjective J ι' hinj').trans (MulEquiv.subgroupCongr h)
  have hlayer : CFSG.HardMathSupport.Solomon.Coordinator.PerfectInLayer (MulAut.conj u) :=
    perfectInLayer_of_langSetup_of_prime S Nat.prime_three ι' hinj' hrange' (MulAut.conj u) hβ hT
      hap h1 hTame
  have hS1 : ∀ P : Subgroup K, P ≤ Subgroup.centralizer ({u} : Set K) → ⁅P, P⁆ = P →
      P ≤ GLALayer (Subgroup.centralizer ({u} : Set K)) := by
    intro P hP hperf
    have := hlayer P (by rwa [KSF4Rank.fixSubgroup_conj_eq']) hperf
    rwa [KSF4Rank.fixSubgroup_conj_eq'] at this
  obtain ⟨ω, k, hω3, hω1, hk3, hak⟩ := exists_omega_param hap
  have hk0 : ∃ i, k i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply h1
    have : a = 1 := funext fun i => by rw [hak i, hcon i]; simp
    rw [this]
    exact rootDiagUnit_one
  rcases KSF4Std.classify_kernel2 k hk3 hk0 with hB | hA
  · refine ⟨hS1, fun J₁ J₂ J₃ h₁ h₂ h₃ => ?_, Or.inl fun J hJ => ?_⟩
    · obtain ⟨i₁, -, e₁⟩ := hkey J₁ h₁
      obtain ⟨i₂, -, e₂⟩ := hkey J₂ h₂
      exact Or.inl (hmap (by rw [e₁, e₂, KSF4Std.eq_of_kernelB hω3 hω1 hak hB i₁ i₂]))
    · obtain ⟨i, -, hJi⟩ := hkey J hJ
      exact Bal209F4Aux.isLieQuot_mulEquiv (hequiv J i hJi).symm
        (classB_isB3 S hT hap hq8 hpL hω3 hω1 hak hB i).2
  · obtain ⟨hgood, hcnt⟩ := classesA2A2_U3 S hT hap h1 hq8 hTame hω3 hω1 hk3 hk0 hak hA
    refine ⟨hS1, fun J₁ J₂ J₃ h₁ h₂ h₃ => ?_, Or.inr fun J hJ => ?_⟩
    · obtain ⟨i₁, -, e₁⟩ := hkey J₁ h₁
      obtain ⟨i₂, -, e₂⟩ := hkey J₂ h₂
      obtain ⟨i₃, -, e₃⟩ := hkey J₃ h₃
      rcases hcnt i₁ i₂ i₃ with h | h | h
      · exact Or.inl (hmap (by rw [e₁, e₂, h]))
      · exact Or.inr (Or.inl (hmap (by rw [e₁, e₃, h])))
      · exact Or.inr (Or.inr (hmap (by rw [e₂, e₃, h])))
    · obtain ⟨i, -, hJi⟩ := hkey J hJ
      obtain ⟨-, hU, hd⟩ := hgood i
      refine ⟨Bal209F4Aux.isLieQuot_mulEquiv (hequiv J i hJi).symm hU, ?_⟩
      have hmem : ι' u ∈ J.map ι' := by
        rw [hJi]
        have : ι' u = rootDiagUnit Tag.F4 a := hxι
        rw [this]
        exact hd
      exact (Subgroup.mem_map_iff_mem hinj').1 hmem

theorem map_map_symm {K G : Type*} [Group K] [Group G] (e : K ≃* G) (H : Subgroup K) :
    (H.map (e : K →* G)).map (e.symm : G →* K) = H := by
  rw [Subgroup.map_map]
  have : (e.symm : G →* K).comp (e : K →* G) = MonoidHom.id K := by
    ext x
    simp
  rw [this, Subgroup.map_id]

theorem f4EightStruct_of_core_iso (hCore : F4LocalOneAux.F4EightOPrimeCore)
    (hIso : KSF4Std.F4IsoStatement) : F4EightStruct := by
  classical
  intro K _ _ hq hLie u hu3
  obtain ⟨-, ⟨e⟩⟩ := hIso K hq hLie
  have hs : orderOf (e u) = 3 := by rw [MulEquiv.orderOf_eq]; exact hu3
  have hcardK : Nat.card (GaloisField 2 3) = 2 ^ 3 := GaloisField.card 2 3 (by norm_num)
  have hC : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({e u} : Set _)) = ⊥ :=
    hCore (GaloisField 2 3) hcardK (e u) hs
  refine ⟨fun J hJ => ?_, f4EightStruct_lang e u hu3⟩
  have h1 := glaPComponent_map_equiv e hJ
  rw [map_centralizer_singleton_equiv e u] at h1
  have h3 := KSF4Std.isComponentOf_of_glaPComponent_of_core_eq_bot hC h1
  have h4 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e.symm h3
  have hC' : (Subgroup.centralizer ({e u} : Set _)).map (e.symm : _ →* K) =
      Subgroup.centralizer ({u} : Set K) := by
    rw [← map_centralizer_singleton_equiv e u]
    exact map_map_symm e _
  have hJ' : (J.map e.toMonoidHom).map (e.symm : _ →* K) = J := map_map_symm e J
  rwa [hJ', hC'] at h4

end Struct

end KSF4Pure

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end

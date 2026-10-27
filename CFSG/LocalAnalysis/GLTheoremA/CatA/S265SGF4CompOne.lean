module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGF4A2A2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGF4Comp
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.F4ThreeLangInner
import CFSG.HardMathSupport.Dickson.Bal207.CompShape

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433 (KernelA2A2)

section Helpers

private lemma two_le_f_of_card_eq_two_pow_of_dvd_sub_one {F : Type} [Field F] [Finite F]
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (h3 : 3 ∣ 2 ^ f - 1) : 2 ≤ f := by
  have hcard : 1 < Nat.card F := Finite.one_lt_card
  rw [hF] at hcard
  have hf0 : f ≠ 0 := by rintro rfl; norm_num at hcard
  have hf1 : f ≠ 1 := by rintro rfl; norm_num at h3
  omega

private lemma model_setup_nat {F : Type} [Field F] [Finite F] {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (h3 : 3 ∣ 2 ^ f - 1) :
    2 ≤ f ∧ ¬ 3 ∣ Nat.card F ∧ 4 ≤ Nat.card F := by
  have hf := two_le_f_of_card_eq_two_pow_of_dvd_sub_one hF h3
  refine ⟨hf, ?_, ?_⟩
  · rw [hF]
    intro h3dvd
    have h2 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3dvd
    norm_num at h2
  · rw [hF]; simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hf

private lemma mod_three_eq_one_of_dvd_sub_one {f : ℕ} (h3 : 3 ∣ 2 ^ f - 1) :
    2 ^ f % 3 = 1 := by
  obtain ⟨k, hk⟩ := h3
  have hpos : 0 < 2 ^ f := pow_pos (by norm_num) f
  have h2 : 2 ^ f = 3 * k + 1 := by omega
  rw [h2, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (by norm_num : 1 < 3)]

end Helpers


section A2A2

variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}

omit
  [CharP L 2] in
private lemma inner_quasisimple_of_class (S : LangSetup Tag.F4 L 3)
    {a : Fin Tag.F4.rank → Lˣ} (hE : rootDiagUnit Tag.F4 a ∈ S.E)
    (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus)
    {f : ℕ} (hf : 2 ≤ f) (hq : S.D.q = 2 ^ f) (hq3 : S.D.q % 3 = 1)
    (i : KernelComponent (rootCharHom a))
    (hi_orbit : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1) :
    CFSG.Open.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  obtain ⟨w, hn⟩ := S.D.n_weyl
  have hτ : ∀ t : TwistTag, t.tag ≠ Tag.F4 := by intro t; cases t <;> decide
  have hρ : ∀ γ, IsRoot Tag.F4 γ → S.ρ γ = w • γ := fun γ hγ =>
    S.rho_eq_smul hτ hn hγ
  have hkind : twistKind S.ρ (rootCharHom a) i = .inner := by
    unfold twistKind
    rw [hi_orbit, if_pos (f4Three_twistInner_one S hρ hE hq3 i)]
  have hQ : 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) := by
    rw [hi_orbit, hq, pow_one]
    calc 4 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple
    (rationalComponent_quasisimple_inner_of_four_leT S
      CFSG.HardMathSupport.Timmesfeld.RootAut.rootAutIsWeyl_holds hT i hkind hQ)

theorem SG.false_of_kernelA2A2_of_le_of_mod_one (S : LangSetup Tag.F4 L 3)
    {a : Fin Tag.F4.rank → Lˣ} (hE : rootDiagUnit Tag.F4 a ∈ S.E) (hap : ∀ i, a i ^ 3 = 1)
    {f : ℕ} (hf : 2 ≤ f) (hq : S.D.q = 2 ^ f) (hq3 : S.D.q % 3 = 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    {ω : Lˣ} {k : Fin Tag.F4.rank → ℕ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hk3 : ∀ i, k i < 3)
    (hk0 : ∃ i, k i ≠ 0) (hak : ∀ i, a i = ω ^ k i) (hk : KernelA2A2 k)
    {C : Type} [Group C] [Finite C] (ι : C →* ModGL Tag.F4 L) (hι : Function.Injective ι)
    (hrange : ι.range = S.Γ) (β : MulAut C)
    (hβ : ∀ c, ι (β c) = rootDiagUnit Tag.F4 a * ι c * (rootDiagUnit Tag.F4 a)⁻¹)
    {J : Subgroup C} (hJ : IsComponentOf J (fixSubgroup β))
    (hle : ∀ J' : Subgroup C, IsComponentOf J' (fixSubgroup β) → J' ≤ J) : False := by
  classical
  have hT : rootDiagUnit Tag.F4 a ∈ S.D.torus := (S.E_le hE).1
  obtain ⟨σ, τ, κ, κ', ψ, ψ', iΛ, iΘ, hP, hψ, hψ', hΛ, hΘ, hSig, hall, hρσ, hρτ⟩ :=
    Lemma27Ns.I1433.exists_pair_frames S hT hap hω3 hω1 hak hk
  have hqs : ∀ i : KernelComponent (rootCharHom a),
      CFSG.Open.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
    intro i
    rcases hall i with hi | hi
    · rw [hi]
      have hi_orbit := Lemma27Ns.I1433.componentOrbitLength_eq_one S hT iΛ (by rw [hΛ]; exact hρσ)
      exact inner_quasisimple_of_class S hE hT hf hq hq3 iΛ hi_orbit
    · rw [hi]
      have hi_orbit := Lemma27Ns.I1433.componentOrbitLength_eq_one S hT iΘ (by rw [hΘ]; exact hρτ)
      exact inner_quasisimple_of_class S hE hT hf hq hq3 iΘ hi_orbit
  exact SG.false_of_kernelA2A2_of_le_of_quasisimple S hT hap hTame hqs hω3 hω1 hk3 hk0 hak hk
    ι hι hrange β hβ hJ hle

end A2A2

section Model


private lemma model_of_le_component_F4_of_dvd_sub_one_setup {F : Type} [Field F] [Finite F]
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (h3 : 3 ∣ 2 ^ f - 1)
    (g : ↥(adjointGroup Tag.F4 F)) (hg : orderOf g = 3) :
    ∃ (S : LangSetup Tag.F4 (AlgebraicClosure F) 3)
      (a : Fin Tag.F4.rank → (AlgebraicClosure F)ˣ)
      (ι : ↥(adjointGroup Tag.F4 F) →* ModGL Tag.F4 (AlgebraicClosure F)),
      S.D.q = Nat.card F ∧ rootDiagUnit Tag.F4 a ∈ S.D.torus ∧ (∀ i, a i ^ 3 = 1) ∧
      rootDiagUnit Tag.F4 a ≠ 1 ∧ Function.Injective ι ∧ ι.range = S.Γ ∧
      ι g = rootDiagUnit Tag.F4 a ∧
      (∀ c, ι (MulAut.conj g c) =
        rootDiagUnit Tag.F4 a * ι c * (rootDiagUnit Tag.F4 a)⁻¹) ∧
      rootDiagUnit Tag.F4 a ∈ S.E ∧
      (∀ i : KernelComponent (rootCharHom a),
        CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
          Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  obtain ⟨hf, hpK, h4⟩ := model_setup_nat hF h3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := f)
    (by rw [← Nat.card_eq_fintype_card, hF])
  have : CharP (AlgebraicClosure F) 2 :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective 2
  have : Finite ↥(adjointGroup Tag.F4 F) := by
    have : Finite (Module.End F (RootModule Tag.F4 F)) := Module.finite_of_finite F
    infer_instance
  have hperf : commutator ↥(adjointGroup Tag.F4 F) = ⊤ := single_edge_perfect Tag.F4 F (by simp)
  have hmon : MonomialToralAt Tag.F4 3 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_exc
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_E6_five
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_E7_five
      (by simp) Nat.prime_three (by norm_num)
  have hx3 : g ^ 3 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hx1 : g ≠ 1 := by intro h; rw [h, orderOf_one] at hg; omega
  obtain ⟨S, a, ι, hSq, hT, hap, h1, hinj, hrange, hι, hconj⟩ :=
    Lemma27Ns.I1433.exists_langSetup_of_inner_untw_of_prime_eq (Or.inr (Or.inl rfl))
      Nat.prime_three hpK Nat.prime_three hpK (Or.inr h4) hmon hperf g hx3 hx1
  have hTame := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.langSetup_hTame S hT hap h1
  have hE : rootDiagUnit Tag.F4 a ∈ S.E := by
    refine S.E_all (rootDiagUnit Tag.F4 a) ⟨hT, ?_⟩
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.rootDiagUnit_pow_eq_one_of_forall hap)
    rw [← hι]
    change ι g ∈ S.Γ
    rw [← hrange]
    exact MonoidHom.mem_range.2 ⟨g, rfl⟩
  exact ⟨S, a, ι, hSq, hT, hap, h1, hinj, hrange, hι, hconj, hE, hTame⟩

theorem SG.model_of_le_component_F4_of_dvd_sub_one {F : Type} [Field F] [Finite F] {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (h3 : 3 ∣ 2 ^ f - 1) (g : ↥(adjointGroup Tag.F4 F))
    (hg : orderOf g = 3) {J : Subgroup ↥(adjointGroup Tag.F4 F)}
    (hJ : IsComponentOf J (fixSubgroup (MulAut.conj g)))
    (hle : ∀ J' : Subgroup ↥(adjointGroup Tag.F4 F),
      IsComponentOf J' (fixSubgroup (MulAut.conj g)) → J' ≤ J) :
    StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSp 3 2 f := by
  classical
  obtain ⟨S, a, ι, hSq, hT, hap, h1, hinj, hrange, hι, hconj, hE, hTame⟩ :=
    model_of_le_component_F4_of_dvd_sub_one_setup hF h3 g hg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := f)
    (by rw [← Nat.card_eq_fintype_card, hF])
  have : CharP (AlgebraicClosure F) 2 :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective 2
  have hf : 2 ≤ f := two_le_f_of_card_eq_two_pow_of_dvd_sub_one hF h3
  have hq : S.D.q = 2 ^ f := hSq.trans hF
  have hq3 : S.D.q % 3 = 1 := by
    rw [hq]
    exact mod_three_eq_one_of_dvd_sub_one h3
  obtain ⟨ω, k, hω3, hω1, hk3, hak⟩ :=
    Lemma27Ns.I1433.exists_omega_param (L := AlgebraicClosure F) hap
  have hk0 : ∃ i, k i ≠ 0 := by
    by_contra hcon
    apply h1
    have ha : a = 1 := funext fun i => by
      rw [hak i, show k i = 0 from Classical.byContradiction fun h => hcon ⟨i, h⟩, pow_zero]
      rfl
    rw [ha, rootDiagUnit_one]
  rcases KSF4Std.classify_kernel2 k hk3 hk0 with hB | hA
  · obtain ⟨i, -, hi⟩ :=
      components_of_langSetup S Nat.prime_three ι hinj hrange (MulAut.conj g) hconj hT hap h1
        hTame hJ
    obtain ⟨-, hadm, K, hK1, hK2, hK, ⟨θ⟩⟩ :=
      SG.rationalComponent_model_of_kernelB S hT hap hf hq hω3 hω1 hak hB i
    let eJ : ↥J ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
      (J.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hi)
    exact ⟨hadm, K, hK1, hK2, hK,
      ⟨(CFSG.HardMathSupport.Dickson.Bal207.centerQuotientCongr eJ).trans θ⟩⟩
  · exact (SG.false_of_kernelA2A2_of_le_of_mod_one S hE hap hf hq hq3 hTame hω3 hω1 hk3 hk0
      hak hA ι hinj hrange (MulAut.conj g) hconj hJ hle).elim


theorem SG.model_of_le_component_F4_of_card {F : Type} [Field F] [Finite F] {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (g : ↥(adjointGroup Tag.F4 F))
    (hg : orderOf g = 3) {J : Subgroup ↥(adjointGroup Tag.F4 F)}
    (hJ : IsComponentOf J (fixSubgroup (MulAut.conj g)))
    (hle : ∀ J' : Subgroup ↥(adjointGroup Tag.F4 F),
      IsComponentOf J' (fixSubgroup (MulAut.conj g)) → J' ≤ J) :
    StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSp 3 2 f := by
  have h3 : 2 ^ f % 3 = 1 ∨ 2 ^ f % 3 = 2 := by
    have hlt : 2 ^ f % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have hne : 2 ^ f % 3 ≠ 0 := by
      intro h0
      have hdvd : 3 ∣ 2 ^ f := Nat.dvd_of_mod_eq_zero h0
      have h2 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
      norm_num at h2
    omega
  rcases h3 with h3 | h3
  · apply SG.model_of_le_component_F4_of_dvd_sub_one hF ?_ g hg hJ hle
    have hdiv := Nat.div_add_mod (2 ^ f) 3
    rw [h3] at hdiv
    use 2 ^ f / 3
    omega
  · apply SG.model_of_le_component_F4 hF ?_ g hg hJ hle
    have hdiv := Nat.div_add_mod (2 ^ f) 3
    rw [h3] at hdiv
    use 2 ^ f / 3 + 1
    omega

end Model

end CFSG.LocalAnalysis.GLTheoremA.S265

end

module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGF4Sp
import CFSG.HardMathSupport.Dickson.Bal207.FamF42Class
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGF4A2A2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433 (KernelA2A2)

section A2A2


variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}

theorem SG.false_of_kernelA2A2_of_le (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1) {f : ℕ} (hf : 2 ≤ f)
    (hq : S.D.q = 2 ^ f) (hq3 : S.D.q % 3 = 2)
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
  obtain ⟨σ, τ, κ, κ', ψ, ψ', iΛ, iΘ, hP, hψ, hψ', hΛ, hΘ, hSig, hall, hρσ, hρτ⟩ :=
    Lemma27Ns.I1433.exists_pair_frames S hT hap hω3 hω1 hak hk
  obtain ⟨π, hπ⟩ := Lemma27Ns.I1433.exists_outer_shape S hT hω3 hω1 hk3 hk0 hak hP hψ hSig hq3 hρσ
  obtain ⟨π', hπ'⟩ := Lemma27Ns.I1433.exists_outer_shape S hT hω3 hω1 hk3 hk0 hak hP.symm hψ'
    (fun γ hγ hk' => (hSig γ hγ hk').symm) hq3 hρτ
  have hνQ : (3, 2 ^ (f * 1)) ≠ (3, 2) := by
    rw [mul_one]
    intro h
    have h2 : 2 ^ f = 2 := congrArg Prod.snd h
    have h4 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    rw [h2] at h4
    norm_num at h4
  have hqsΛ : CFSG.Open.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) iΛ) := by
    have hs1 := Lemma27Ns.I1433.componentOrbitLength_eq_one S hT iΛ (by rw [hΛ]; exact hρσ)
    have hmodel := KSExact.rationalComponent_suN_model S hT iΛ (le_refl 3)
      (IsSLFrame.of_isA2Frame hψ) hΛ π (fun x y hxy => by rw [hs1]; simpa using hπ x y hxy)
      Nat.prime_two inferInstance (by omega : 0 < f) hq (by rw [hs1]; exact hνQ)
    rw [hs1] at hmodel
    exact KSF4Std.isQuasisimple_of_tame_of_model_PSU (hTame iΛ) hmodel
  have hqsΘ : CFSG.Open.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) iΘ) := by
    have hs1 := Lemma27Ns.I1433.componentOrbitLength_eq_one S hT iΘ (by rw [hΘ]; exact hρτ)
    have hmodel := KSExact.rationalComponent_suN_model S hT iΘ (le_refl 3)
      (IsSLFrame.of_isA2Frame hψ') hΘ π' (fun x y hxy => by rw [hs1]; simpa using hπ' x y hxy)
      Nat.prime_two inferInstance (by omega : 0 < f) hq (by rw [hs1]; exact hνQ)
    rw [hs1] at hmodel
    exact KSF4Std.isQuasisimple_of_tame_of_model_PSU (hTame iΘ) hmodel
  exact SG.false_of_kernelA2A2_of_le_of_quasisimple S hT hap hTame
    (fun i => (hall i).elim (· ▸ hqsΛ) (· ▸ hqsΘ)) hω3 hω1 hk3 hk0 hak hk ι hι hrange β hβ hJ hle

end A2A2

section Model


theorem SG.model_of_le_component_F4 {F : Type} [Field F] [Finite F] {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (h3 : 3 ∣ 2 ^ f + 1) (g : ↥(adjointGroup Tag.F4 F))
    (hg : orderOf g = 3) {J : Subgroup ↥(adjointGroup Tag.F4 F)}
    (hJ : IsComponentOf J (fixSubgroup (MulAut.conj g)))
    (hle : ∀ J' : Subgroup ↥(adjointGroup Tag.F4 F),
      IsComponentOf J' (fixSubgroup (MulAut.conj g)) → J' ≤ J) :
    StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSp 3 2 f := by
  classical
  have hf0 : f ≠ 0 := by
    rintro rfl
    norm_num at h3
  rcases Nat.lt_or_ge f 2 with hf | hf
  ·
    obtain rfl : f = 1 := by omega
    obtain ⟨F', _, _, hF', ⟨e⟩⟩ :=
      (CFSG.HardMathSupport.Dickson.Bal207.FamF42.compShape_conj_F4_two hF g hg).type J hJ
    exact ⟨⟨Nat.prime_two, le_rfl, by norm_num, by simp⟩, F', inferInstance, inferInstance,
      by rw [hF']; norm_num, ⟨e.trans (QuotientGroup.quotientMulEquivOfEq
        (CFSG.LieType.Universal.Symplectic.center_eq 3 F'))⟩⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := f)
    (by rw [← Nat.card_eq_fintype_card, hF])
  haveI : CharP (AlgebraicClosure F) 2 :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective 2
  haveI : Finite ↥(adjointGroup Tag.F4 F) := by
    have : Finite (Module.End F (RootModule Tag.F4 F)) := Module.finite_of_finite F
    infer_instance
  have hpK : ¬ 3 ∣ Nat.card F := by
    rw [hF]
    omega
  obtain ⟨p₀, S, a, ι, hSq, hT, hap, h1, hinj, hrange, -, hconj, hTame⟩ :=
    Lemma27Ns.I1433.exists_langSetup_F4_of_orderOf_eq_three hpK g hg
  obtain ⟨ω, k, hω3, hω1, hk3, hak⟩ :=
    Lemma27Ns.I1433.exists_omega_param (L := AlgebraicClosure F) hap
  have hk0 : ∃ i, k i ≠ 0 := by
    by_contra hcon
    apply h1
    have ha : a = 1 := funext fun i => by
      rw [hak i, show k i = 0 from Classical.byContradiction fun h => hcon ⟨i, h⟩, pow_zero]
      rfl
    rw [ha, rootDiagUnit_one]
  have hq : S.D.q = 2 ^ f := hSq.trans hF
  have hq3 : S.D.q % 3 = 2 := by
    rw [hq]
    omega
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
  · exact (SG.false_of_kernelA2A2_of_le S hT hap hf hq hq3 hTame hω3 hω1 hk3 hk0 hak hA ι hinj
      hrange (MulAut.conj g) hconj hJ hle).elim

end Model

end CFSG.LocalAnalysis.GLTheoremA.S265

end

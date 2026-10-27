module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6InnerCompClass
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqRat
public import CFSG.Fischer.Classification.Recognition.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma52
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.LocalAnalysis.GLTheoremB TwE6UniqAbs

namespace TwE6InnerAbs


section Generic


theorem glaPComponent_eq_comap_of_langSetup {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) {C : Type} [Group C] [Finite C]
    (ι : C →* ModGL τ L) (hι : Function.Injective ι) (hrange : ι.range = S.Γ) (β : MulAut C)
    {a : Fin τ.rank → Lˣ}
    (hβ : ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hU : ∀ i j : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) j) →
        rationalComponent S.ρ S.Γ (rootCharHom a) i = rationalComponent S.ρ S.Γ (rootCharHom a) j)
    {J : Subgroup C} (hJ : GLAPComponent 3 (fixSubgroup β) J) :
    ∃ i, CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
      rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ ι.range ∧
        J = (rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι := by
  classical
  set d : ModGL τ L := rootDiagUnit τ a with hd
  set R : KernelComponent (rootCharHom a) → Subgroup (ModGL τ L) :=
    fun i => rationalComponent S.ρ S.Γ (rootCharHom a) i with hR
  have hfix : (fixSubgroup β).map ι = S.Γ ⊓ Subgroup.centralizer {d} := by
    rw [map_fixSubgroup_eq_of_conj ι hι β d hβ, hrange]
  have hcomapfix : (S.Γ ⊓ Subgroup.centralizer {d}).comap ι = fixSubgroup β := by
    rw [← hfix]
    exact Subgroup.comap_map_eq_self_of_injective hι _
  have hCdrange : S.Γ ⊓ Subgroup.centralizer {d} ≤ ι.range := fun x hx => by
    rw [hrange]
    exact (Subgroup.mem_inf.1 hx).1
  haveI : Finite (KernelComponent (rootCharHom a)) :=
    (root_character_kernel_orthogonal_central_product τ L (rootCharHom a)).2.1
  have hcompR : ∀ i : KernelComponent (rootCharHom a), CFSG.IsQuasisimple (R i) →
      IsComponentOf (R i) (S.Γ ⊓ Subgroup.centralizer {d}) := by
    intro i hi
    obtain ⟨hle, hsub⟩ := langSubnormal_of_mem_torus S hT i
    exact ⟨hle, (CFSG.Open.IsSubnormal.iff_subgroupOf hle).2 hsub, open_isQuasisimple hi⟩
  have hperf : ⁅J, J⁆ = J := glaPComponent_perfect hJ
  have hne : J ≠ ⊥ := glaPComponent_ne_bot hJ
  have hJC : J ≤ fixSubgroup β := hJ.1
  have hPmap : J.map ι ≤ S.Γ ⊓ Subgroup.centralizer {d} := by
    rw [← hfix]
    exact Subgroup.map_mono hJC
  have hperfmap : ⁅J.map ι, J.map ι⁆ = J.map ι := by
    rw [← Subgroup.map_commutator, hperf]
  have h2 := perfect_le_iSup_rationalComponent_of_prime S hp hT hap h1 hTame (J.map ι) hPmap
    hperfmap
  obtain ⟨i₀, hi₀⟩ : ∃ i, CFSG.IsQuasisimple (R i) := by
    by_contra hcon
    push Not at hcon
    haveI : IsEmpty {i : KernelComponent (rootCharHom a) // CFSG.IsQuasisimple (R i)} :=
      ⟨fun ⟨i, hi⟩ => hcon i hi⟩
    rw [iSup_of_empty] at h2
    exact hne ((Subgroup.map_eq_bot_iff_of_injective _ hι).1 (le_bot_iff.1 h2))
  have hle : J.map ι ≤ R i₀ := h2.trans (iSup_le fun i => (hU i.1 i₀ i.2 hi₀).le)
  have hJR : J ≤ (R i₀).comap ι := (Subgroup.map_le_iff_le_comap).1 hle
  have hRrange : R i₀ ≤ ι.range := (hcompR i₀ hi₀).1.trans hCdrange
  have hcomp := isComponentOf_comap_of_injective ι hι hRrange hCdrange (hcompR i₀ hi₀)
  rw [hcomapfix] at hcomp
  refine ⟨i₀, hi₀, hRrange, ?_⟩
  have hsub : IsSubnormal J ((R i₀).comap ι) := isSubnormal_of_le_of_le hJ.2.1 hJR hcomp.1
  rcases CFSG.Fischer.Classification.Recognition.IsSubnormal.eq_or_le_center hsub hcomp.2.2 with
    h | h
  · exact h
  · exfalso
    have hcomm : ⁅J, J⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨x', hx', rfl⟩ := h hx
      obtain ⟨y', hy', rfl⟩ := h hy
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hx' y')
    exact hne (hperf ▸ hcomm)

end Generic


@[expose] def TwE6InnerCompModel :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 4 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ 2) →
    ∀ s : twistedE6RootGroup K σ, s ^ 3 = 1 → s ≠ 1 →
      ∀ J : Subgroup (twistedE6RootGroup K σ), GLAPComponent 3 (fixSubgroup (MulAut.conj s)) J →
        IsLieQuot ↥J TwE6TwoInnerCompIndex

section Model


theorem twE6InnerCompModel_holds : TwE6InnerCompModel := by
  classical
  intro K _ _ hK σ hσ s hs3 hs1 J hJ
  haveI : Fintype K := Fintype.ofFinite K
  haveI hcK : CharP K 2 := charP_of_card_eq_prime_pow (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  haveI hcL : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨S, a, ι, hq, hρ, hT, hap, h1, hin, hinj, hrange, hιs⟩ :=
    exists_stdSetup_of_inner hK σ hσ hs3 hs1
  have h3 : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 := natCast_three_ne_zero_of_charTwo
  have hTame := langSetup_hTame_of_prime S Nat.prime_three h3 (fun h => absurd h (by decide)) hT
    hap h1
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite ↥(twistedE6RootGroup K σ) :=
    Finite.of_injective (fun x => (x : ModGL TwistTag.E6.tag K)) Subtype.val_injective
  have hβ : ∀ c, ι (MulAut.conj s c) = rootDiagUnit Tag.E6 a * ι c * (rootDiagUnit Tag.E6 a)⁻¹ := by
    intro c
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hιs]
  obtain ⟨i, hiq, hiR, rfl⟩ := glaPComponent_eq_comap_of_langSetup S Nat.prime_three ι hinj hrange
    (MulAut.conj s) hβ hT hap h1 hTame (ratQuasiEq_holds _ _ S a hq hT hap h1) hJ
  have hmap : ((rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι).map ι =
      rationalComponent S.ρ S.Γ (rootCharHom a) i := Subgroup.map_comap_eq_self hiR
  let e : ↥((rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι) ≃*
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (Subgroup.equivMapOfInjective _ ι hinj).trans (MulEquiv.subgroupCongr hmap)
  exact Bal209F4Aux.isLieQuot_mulEquiv e.symm
    (class_isLieQuot_of_inner S hq hρ hT hap h1 hin i hiq)

end Model

end TwE6InnerAbs

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

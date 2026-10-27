module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6OuterLift
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeClass
import all CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcE6Kern
import all CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwE6Conn
import CFSG.LocalAnalysis.StandardType.GGTwE6K1ClassStab
import CFSG.LieType.SeitzGeneration.ExcHighThree.TwConjClass
import CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagRegularBridge
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6OuterDescent

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs (zlC cmpF dotμ kac_class_data
  eq_of_componentRoots_eq)

private def kcOmegaB (m0 m1 m2 m3 m4 m5 : ℤ) : Bool :=
  (zlC m0 m1 m2 m3 m4 m5).all fun x => (zlC m0 m1 m2 m3 m4 m5).all fun y =>
    (zlC m0 m1 m2 m3 m4 m5).all fun z =>
      (cmpF (zlC m0 m1 m2 m3 m4 m5) x == cmpF (zlC m0 m1 m2 m3 m4 m5) y) ||
        (cmpF (zlC m0 m1 m2 m3 m4 m5) x == cmpF (zlC m0 m1 m2 m3 m4 m5) z) ||
          (cmpF (zlC m0 m1 m2 m3 m4 m5) y == cmpF (zlC m0 m1 m2 m3 m4 m5) z) ||
            (dotμ e6Omega3 m0 m1 m2 m3 m4 m5 % 3 == 0)

private theorem kc_omega : ∀ m0 m1 m2 m3 m4 m5 : Fin 4,
    (m0.val + 2 * m1.val + 2 * m2.val + 3 * m3.val + 2 * m4.val + m5.val ≤ 3) →
    kcOmegaB m0 m1 m2 m3 m4 m5 = true := by
  decide +kernel

private theorem rootChar_pow_three' {L : Type} [Field L] {a : Fin Tag.E6.rank → Lˣ}
    (ha : ∀ j, a j ^ 3 = 1) (v : Fin Tag.E6.rank → ℤ) : rootChar a v ^ 3 = 1 := by
  simp only [rootChar, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha j, one_zpow]

private theorem rootChar_neg'' {L : Type} [Field L] (a : Fin Tag.E6.rank → Lˣ)
    (v : Fin Tag.E6.rank → ℤ) : rootChar a (-v) = (rootChar a v)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← rootChar_add, neg_add_cancel, rootChar_zero])

private theorem dotμ_add (v v' : Fin Tag.E6.rank → ℤ) (m0 m1 m2 m3 m4 m5 : ℤ) :
    dotμ (v + v') m0 m1 m2 m3 m4 m5 = dotμ v m0 m1 m2 m3 m4 m5 + dotμ v' m0 m1 m2 m3 m4 m5 := by
  simp only [dotμ, Pi.add_apply]
  ring

private theorem dotμ_three_smul (v : Fin Tag.E6.rank → ℤ) (m0 m1 m2 m3 m4 m5 : ℤ) :
    dotμ ((3 : ℤ) • v) m0 m1 m2 m3 m4 m5 = 3 * dotμ v m0 m1 m2 m3 m4 m5 := by
  simp only [dotμ, Pi.smul_apply, smul_eq_mul]
  ring

private def e6Omega3Quot : Fin Tag.E6.rank → ℤ := ![1, 1, 1, 2, 1, 0]

private theorem e6Omega3_eq : e6Omega3 = e6c + (3 : ℤ) • e6Omega3Quot := by
  funext j
  fin_cases j <;> rfl

section Kac


theorem prod_e6c_eq_one_of_ncard_eighteen {L : Type} [Field L] [IsAlgClosed L]
    (h3 : ((3 : ℕ) : L) ≠ 0) {a : Fin Tag.E6.rank → Lˣ} (ha : ∀ j, a j ^ 3 = 1)
    (h18 : (kernelRoots (rootCharHom a)).ncard = 18) : ∏ j, a j ^ e6c j = 1 := by
  classical
  obtain ⟨c, hc, -⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24.kernel_classes_of_ncard_eighteen
      h3 ha h18
  obtain ⟨ζ, w, m0, m1, m2, m3, m4, m5, hζ, hsum, hchar, hcl⟩ := kac_class_data h3 ha
  choose xs hxs hroots using fun k : Fin 3 => (hcl (c k))
  have hne : ∀ k l : Fin 3, k ≠ l →
      cmpF (zlC m0 m1 m2 m3 m4 m5) (xs k) ≠ cmpF (zlC m0 m1 m2 m3 m4 m5) (xs l) := by
    intro k l hkl h
    exact hkl (hc.1 (eq_of_componentRoots_eq (by rw [(hroots k).1, (hroots l).1, h])))
  have hchk := kc_omega m0 m1 m2 m3 m4 m5 hsum
  unfold kcOmegaB at hchk
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 hchk (xs 0) (hxs 0))
    (xs 1) (hxs 1)) (xs 2) (hxs 2)
  simp only [Bool.or_eq_true, beq_iff_eq] at h1
  have hdiv : dotμ e6Omega3 m0 m1 m2 m3 m4 m5 % 3 = 0 := by
    rcases h1 with ((h1 | h1) | h1) | h1
    · exact absurd h1 (hne 0 1 (by decide))
    · exact absurd h1 (hne 0 2 (by decide))
    · exact absurd h1 (hne 1 2 (by decide))
    · exact h1
  have hζu : IsPrimitiveRoot ζ 3 := IsPrimitiveRoot.coe_units_iff.1 hζ
  have hζ3 : ζ ^ 3 = 1 := hζu.pow_eq_one
  have hΩ : rootChar a e6Omega3 = 1 := by
    have e1 : w • e6Omega3 = e6Omega3 + (3 : ℤ) • e6Shift w := by
      rw [three_smul_e6Shift]
      abel
    rw [hchar, e1, dotμ_add, dotμ_three_smul]
    obtain ⟨t, ht⟩ : ∃ t, dotμ e6Omega3 m0 m1 m2 m3 m4 m5 = 3 * t :=
      ⟨dotμ e6Omega3 m0 m1 m2 m3 m4 m5 / 3, by omega⟩
    rw [ht, ← mul_add, zpow_mul]
    norm_cast
    rw [hζ3, one_zpow]
  have e2 : ∏ j, a j ^ e6c j = rootChar a e6c := rfl
  rw [e2]
  have e3 : rootChar a e6Omega3 =
      rootChar a e6c * rootChar a ((3 : ℤ) • e6Omega3Quot) := by
    rw [e6Omega3_eq, rootChar_add]
  have e4 : rootChar a ((3 : ℤ) • e6Omega3Quot) = 1 := by
    rw [CFSG.LieType.Chevalley.rootChar_zsmul]
    norm_cast
    exact rootChar_pow_three' ha _
  rw [e4, mul_one] at e3
  rw [← e3, hΩ]

end Kac

section Classes


private theorem neg_mem_componentRoots_aux {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* M} {i : KernelComponent χ}
    {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ componentRoots χ i) : -α ∈ componentRoots χ i := by
  obtain ⟨hα', rfl⟩ := hα
  have hneg : -α ∈ kernelRoots χ := ⟨IsRoot.neg hα'.1, chi_neg hα'.2⟩
  refine ⟨hneg, (mk_eq_of_iform_ne_zero (α := ⟨α, hα'⟩) (β := ⟨-α, hneg⟩) ?_).symm⟩
  change CFSG.LieType.Steinberg.Adjoint.iform α (-α) ≠ 0
  have e : CFSG.LieType.Steinberg.Adjoint.iform α (-α) =
      -CFSG.LieType.Steinberg.Adjoint.iform α α := by
    simp [CFSG.LieType.Steinberg.Adjoint.iform, Finset.sum_neg_distrib]
  rw [e]
  exact neg_ne_zero.2 (iform_self_pos_of_isRoot hα'.1).ne'

theorem image_componentRoots_of_eq_smul {L : Type} [Field L] {a : Fin Tag.E6.rank → Lˣ}
    {σ : Equiv.Perm (Fin Tag.E6.rank → ℤ)} {v : WeylGroup Tag.E6}
    (hv : v ∈ kernelReflectionGroup a) (hσ : ∀ x, σ x = v • x)
    (i : KernelComponent (rootCharHom a)) :
    σ '' componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i := by
  ext γ
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    rw [hσ]
    exact CFSG.StandardType.SCFourCover.smul_mem_componentRoots_of_mem_kernelWeylGroup hδ hv
  · intro hγ
    refine ⟨v⁻¹ • γ,
      CFSG.StandardType.SCFourCover.smul_mem_componentRoots_of_mem_kernelWeylGroup hγ (inv_mem hv),
      ?_⟩
    rw [hσ, smul_inv_smul]

theorem image_componentRoots_of_eq_neg_smul {L : Type} [Field L] {a : Fin Tag.E6.rank → Lˣ}
    {σ : Equiv.Perm (Fin Tag.E6.rank → ℤ)} {v : WeylGroup Tag.E6}
    (hv : v ∈ kernelReflectionGroup a) (hσ : ∀ x, σ x = -(v • x))
    (i : KernelComponent (rootCharHom a)) :
    σ '' componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i := by
  ext γ
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    rw [hσ]
    exact neg_mem_componentRoots_aux
      (CFSG.StandardType.SCFourCover.smul_mem_componentRoots_of_mem_kernelWeylGroup hδ hv)
  · intro hγ
    refine ⟨-(v⁻¹ • γ), neg_mem_componentRoots_aux
      (CFSG.StandardType.SCFourCover.smul_mem_componentRoots_of_mem_kernelWeylGroup hγ (inv_mem hv)),
      ?_⟩
    rw [hσ, smul_neg, smul_inv_smul, neg_neg]

theorem componentOrbitLength_le_one {τ : Tag} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {Ψ : Set (Fin τ.rank → ℤ)} (h : ρ '' Ψ = Ψ) : componentOrbitLength ρ Ψ ≤ 1 :=
  Nat.sInf_le (show 1 ∈ {s : ℕ | 0 < s ∧ (ρ : (Fin τ.rank → ℤ) → _)^[s] '' Ψ = Ψ} from
    ⟨one_pos, by rw [Function.iterate_one]; exact h⟩)

end Classes

section Main


theorem e6A2OrbitThreeOuter_holds : E6A2OrbitThreeOuter := by
  intro L _ _ hL2 p₀ S hS a hT hap h18 i horb hmem
  classical
  have h3L : ((3 : ℕ) : L) ≠ 0 := by
    have e : ((3 : ℕ) : L) = 1 := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.cast_add, CharP.cast_eq_zero L 2, zero_add,
        Nat.cast_one]
    rw [e]
    exact one_ne_zero
  have hc := prod_e6c_eq_one_of_ncard_eighteen h3L hap h18
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ζ, hζ⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHighThree.exists_primCubeRoot_of_charP (L := L) (p := 2)
      (by norm_num)
  set E : Finset L := insert (ζ : L) (Finset.univ.image fun j => ((a j : Lˣ) : L)) with hEdef
  have hE : ∀ c ∈ E, c ^ 3 = 1 := by
    intro c hcE
    rw [hEdef, Finset.mem_insert, Finset.mem_image] at hcE
    rcases hcE with rfl | ⟨j, -, rfl⟩
    · exact hζ.pow_eq_one
    · have := congrArg Units.val (hap j)
      simpa using this
  obtain ⟨K, _, _, ι, hdesc, hEι⟩ := exists_finite_model_descent S hS E hE
  have hrange : ∀ c : Lˣ, (c : L) ∈ Set.range ι → ∃ c₃ : Kˣ, Units.map ι.toMonoidHom c₃ = c := by
    rintro c ⟨c₃, hc₃⟩
    have h0 : c₃ ≠ 0 := by
      rintro rfl
      rw [map_zero] at hc₃
      exact c.ne_zero hc₃.symm
    exact ⟨Units.mk0 c₃ h0, Units.ext (by simp [hc₃])⟩
  choose a₃ ha₃ using fun j => hrange (a j)
    (hEι _ (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩)))
  obtain ⟨ζ₃, hζ₃⟩ := hrange ζ (hEι _ (Finset.mem_insert_self _ _))
  have hιu : Function.Injective (Units.map ι.toMonoidHom) := Units.map_injective ι.injective
  have hζ₃p : IsPrimitiveRoot ((ζ₃ : Kˣ) : K) 3 := by
    have e : ι ((ζ₃ : Kˣ) : K) = (ζ : L) := by rw [← hζ₃]; rfl
    rw [← IsPrimitiveRoot.map_iff_of_injective (f := ι) ι.injective, e]
    exact hζ
  have ha₃3 : ∀ j, a₃ j ^ 3 = 1 := fun j => hιu (by rw [map_pow, ha₃ j, hap j, map_one])
  have hc₃ : ∏ j, a₃ j ^ e6c j = 1 := hιu (by
    rw [map_prod, map_one]
    simp only [map_zpow, ha₃]
    exact hc)
  obtain ⟨u₃, hu₃3, hu₃c⟩ :=
    CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagRegular.exists_cube_params hζ₃p ha₃3 hc₃
  have hda : baseChangeGL ι (rootDiagUnit Tag.E6 (e6RootParams u₃)) = rootDiagUnit Tag.E6 a := by
    rw [baseChangeGL_rootDiagUnit, hu₃c]
    congr 1
    funext j
    exact ha₃ j
  have hχ : ∀ v, rootChar a v = Units.map ι.toMonoidHom (rootChar (e6RootParams u₃) v) := by
    intro v
    have e : a = fun j => Units.map ι.toMonoidHom (e6RootParams u₃ j) := by
      funext j
      rw [hu₃c]
      exact (ha₃ j).symm
    rw [e]
    simp only [rootChar, map_prod, map_zpow]
  obtain ⟨Fr, hFr, hcase⟩ := hS
  obtain ⟨w, hn⟩ := S.D.n_weyl
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem Tag.E6).exists_isReduced w
  haveI : CharP K 2 := (ι.charP_iff_charP 2).2 inferInstance
  obtain ⟨r, e, -, hchar, -, hqe⟩ := exists_char_pow S
  have hr2 : r = 2 := CharP.eq L hchar hL2
  subst hr2
  set φ : K →+* K := iterateFrobenius K 2 e with hφdef
  have hφq : ∀ c, φ c = c ^ S.D.q := fun c => by rw [hφdef, iterateFrobenius_def, hqe]
  have hιφ : ι.comp φ = Fr.comp ι :=
    RingHom.ext fun c => by simp only [RingHom.comp_apply, hφq, hFr, map_pow]
  have hq1 : 1 < S.D.q := S.hqpow.1.one_lt
  have hcls : ⇑S.ρ '' componentRoots (rootCharHom a) i ≠ componentRoots (rootCharHom a) i :=
    fun h => by
      have := componentOrbitLength_le_one h
      omega
  rcases hcase with ⟨hΦ, hq3⟩ | ⟨hΦ, hq3⟩
  ·
    have hqmod : S.D.q % 3 = 1 := by
      obtain ⟨k, hk⟩ := hq3
      omega
    obtain ⟨x, hxF, hxγ⟩ := exists_fixed_lift_of_mem_Γ S hω hn ι hdesc (minBC e6Data_valid φ)
      (baseChangeGL φ) (fun x => e6Isogeny_minBC φ x) (fun g => by
        rw [hΦ, CFSG.RankThree.Chevalley.units_map_entrywiseHom_eq_baseChangeGL_self,
          baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, hιφ]) _ hmem
    have hxπ : ((e6Isogeny K x : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
        rootDiagUnit Tag.E6 (e6RootParams u₃) := baseChangeGL_injective ι (hxγ.trans hda.symm)
    have hφ1 : ∀ c : Kˣ, c ^ 3 = 1 → Units.map φ.toMonoidHom c = c := by
      intro c hc3
      have h1 : Units.map φ.toMonoidHom c = c ^ S.D.q := Units.ext (by simp [hφq])
      rw [h1, pow_eq_pow_mod S.D.q hc3, hqmod, pow_one]
    have hconj := nWord_conj_minTorus_of_fixed φ hφ1 ω u₃ hu₃3 x hxF hxπ
    have hsh₃ := rootChar_e6Shift_inv_of_conj_eq K u₃ hconj
    set v := (coxeterSystem Tag.E6).wordProd ω
    have hsh : rootChar a (e6Shift v⁻¹) = 1 := by rw [hχ, hsh₃, map_one]
    have hρ := CFSG.LocalAnalysis.GLTheoremA.T171Sh.rho_eq_smul_all S hFr hΦ hn
    have hva : v ∈ rootCharStabilizerSubgroup a := by
      intro x
      rw [← hρ x, CFSG.LocalAnalysis.GLTheoremA.T171Sh.langSetup_rootChar_rho_apply S hT x,
        pow_eq_pow_mod S.D.q (rootChar_pow_three' hap x), hqmod, pow_one]
    have hvK : v⁻¹ ∈ kernelReflectionGroup a :=
      mem_kernelReflectionGroup_of_e6Shift a hap (inv_mem hva) hsh
    have hvK' : v ∈ kernelReflectionGroup a := by simpa using inv_mem hvK
    exact hcls (image_componentRoots_of_eq_smul hvK' hρ i)
  ·
    have hqmod : S.D.q % 3 = 2 := by
      obtain ⟨k, hk⟩ := hq3
      omega
    obtain ⟨x, hxF, hxγ⟩ := exists_fixed_lift_of_mem_Γ S hω hn ι hdesc
      (CFSG.LieType.Steinberg.TwistedE6.sigma K φ) (twistHom TwistTag.E6 K φ)
      (fun x => by rw [e6Isogeny_sigma]; rfl)
      (fun g => by
        rw [hΦ]
        exact (twistHom_baseChangeGL (t := TwistTag.E6) ι hιφ g).symm) _ hmem
    have hxπ : ((e6Isogeny K x : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
        rootDiagUnit Tag.E6 (e6RootParams u₃) := baseChangeGL_injective ι (hxγ.trans hda.symm)
    have hconj := nWord_w0_conj_minTorus_of_fixed φ S.D.q hφq hqmod ω u₃ hu₃3 x hxF hxπ
    have hsh₃ := rootChar_e6Shift_inv_of_conj_eq K u₃ hconj
    rw [CoxeterSystem.wordProd_append] at hsh₃
    set v := (coxeterSystem Tag.E6).wordProd ω *
      (coxeterSystem Tag.E6).wordProd CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.e6W0FourWord
      with hv
    have hsh : rootChar a (e6Shift v⁻¹) = 1 := by rw [hχ, hsh₃, map_one]
    have hρ := CFSG.LocalAnalysis.GLTheoremA.T171Sh.rho_eq_smul_all_tw S hFr hΦ hn
    have hvρ : ∀ x, v • x = -(S.ρ x) := by
      intro x
      have e1 : (coxeterSystem Tag.E6).wordProd
          CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.e6W0FourWord • x =
            -(permLattice CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.e6RhoFour x) :=
        CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.e6W0Four_smul x
      rw [hv, mul_smul, e1, smul_neg, hρ x,
        CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.e6RhoFour_eq_twistPerm]
    have hva : v ∈ rootCharStabilizerSubgroup a := by
      intro x
      have h3 := rootChar_pow_three' hap x
      rw [hvρ, rootChar_neg'', CFSG.LocalAnalysis.GLTheoremA.T171Sh.langSetup_rootChar_rho_apply S hT x,
        pow_eq_pow_mod S.D.q h3, hqmod]
      rw [inv_eq_iff_mul_eq_one, ← pow_succ]
      exact h3
    have hvK : v⁻¹ ∈ kernelReflectionGroup a :=
      mem_kernelReflectionGroup_of_e6Shift a hap (inv_mem hva) hsh
    have hvK' : v ∈ kernelReflectionGroup a := by simpa using inv_mem hvK
    exact hcls (image_componentRoots_of_eq_neg_smul hvK' (fun x => by rw [hvρ, neg_neg]) i)

end Main

end CFSG.LocalAnalysis.GLTheoremA.T158

end

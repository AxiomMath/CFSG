module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgExcCore
import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoLang
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBG2ThreeRoots
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcInner
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc2
import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24EvenD5Index
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResOutF4
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OutG2
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPReduction
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdx

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

section G2W

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.Timmesfeld.ExceptionalOrders
  CFSG.RankThree.Chevalley

theorem rootCharStabilizer_le_kernelReflectionGroup_G2_three_kd264alg
    {K : Type} [Field K] {a : Fin Tag.G2.rank → Kˣ}
    (hap : a ^ 3 = 1) (ha1 : a ≠ 1) :
    rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a := by
  by_cases ha0 : rootChar a g2a = 1
  swap
  · exact rootCharStabilizer_le_kernelReflectionGroup_G2_three hap ha1 ha0
  intro w hw
  have hw' : ∀ v, rootChar a (w • v) = rootChar a v := hw
  have hrot : ∀ X Y : Fin Tag.G2.rank → ℤ, w • g2a = X → w • g2r = Y →
      ¬ ((3 : ℕ) : ℤ) ∣ ((X - g2a) g2ia * (Y - g2r) g2ir - (X - g2a) g2ir * (Y - g2r) g2ia) →
        w ∈ kernelReflectionGroup a := by
    intro X Y hX hY hd
    refine absurd (eq_one_of_rootChar_det Nat.prime_three hap ?_ ?_ hd) ha1
    · rw [rootChar_sub, ← hX, hw', mul_inv_cancel]
    · rw [rootChar_sub, ← hY, hw', mul_inv_cancel]
  have hrefl : ∀ (g : WeylGroup .G2) (i : Fin Tag.G2.rank), w = g * simple .G2 i * g⁻¹ →
      w ∈ kernelReflectionGroup a := by
    intro g i hwg
    refine Subgroup.subset_closure ⟨g, i, ⟨IsRoot.smul (isRoot_single _ i) g, ?_⟩, hwg⟩
    have hwα : w • (g • (Pi.single i 1 : Fin Tag.G2.rank → ℤ)) =
        -(g • (Pi.single i 1 : Fin Tag.G2.rank → ℤ)) := by
      rw [hwg, mul_smul, mul_smul, inv_smul_smul, simple_smul, reflect_single_self, smul_neg]
    have h1 : (rootChar a (g • (Pi.single i 1 : Fin Tag.G2.rank → ℤ)))⁻¹ =
        rootChar a (g • (Pi.single i 1 : Fin Tag.G2.rank → ℤ)) := by
      rw [← rootChar_neg_eq_inv, ← hwα, hw']
    have h2 : rootChar a (g • (Pi.single i 1 : Fin Tag.G2.rank → ℤ)) ^ (2 : ℤ) = 1 := by
      rw [zpow_two]
      calc _ = (rootChar a (g • (Pi.single i 1 : Fin Tag.G2.rank → ℤ)))⁻¹ *
            rootChar a (g • (Pi.single i 1 : Fin Tag.G2.rank → ℤ)) := by rw [h1]
        _ = 1 := inv_mul_cancel _
    exact eq_one_of_pow_prime_of_zpow Nat.prime_three (rootChar_pow_of_pow_eq_one hap _) h2
      (not_dvd_of_natAbs_lt (by norm_num) (by norm_num))
  have hinv : ∀ i : Fin Tag.G2.rank, (simple .G2 i)⁻¹ = simple .G2 i :=
    (coxeterSystem .G2).inv_simple
  have hsa : simple .G2 g2ia ∈ kernelReflectionGroup a := by
    refine Subgroup.subset_closure ⟨1, g2ia, ⟨IsRoot.smul (isRoot_single _ g2ia) 1, ?_⟩,
      by rw [one_mul, inv_one, mul_one]⟩
    rw [one_smul, ← g2a_eq_single]
    exact ha0
  have hsb : simple .G2 g2ir * simple .G2 g2ia * (simple .G2 g2ir)⁻¹ ∈
      kernelReflectionGroup a := by
    refine Subgroup.subset_closure ⟨simple .G2 g2ir, g2ia,
      ⟨IsRoot.smul (isRoot_single _ g2ia) _, ?_⟩, rfl⟩
    have hb : simple .G2 g2ir • (Pi.single g2ia 1 : Fin Tag.G2.rank → ℤ) =
        g2a + (3 : ℤ) • g2r := by
      rw [← g2a_eq_single, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have h3 : rootChar a g2r ^ (3 : ℤ) = 1 := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
      exact rootChar_pow_of_pow_eq_one hap g2r
    rw [hb, CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar_add,
      CFSG.LieType.Chevalley.rootChar_zsmul, ha0, h3, one_mul]
  rcases g2_weyl_cases w with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  ·
    have hw1 : w = 1 := weyl_G2_ext (by rw [h1, one_smul]) (by rw [h2, one_smul])
    rw [hw1]
    exact one_mem _
  ·
    refine hrefl 1 g2ia (weyl_G2_ext ?_ ?_)
    · rw [h1, one_mul, inv_one, mul_one, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    · rw [h2, one_mul, inv_one, mul_one, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
  ·
    refine hrefl 1 g2ir (weyl_G2_ext ?_ ?_)
    · rw [h1, one_mul, inv_one, mul_one, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    · rw [h2, one_mul, inv_one, mul_one, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
  · exact hrot _ _ h1 h2 (by
      rw [show (g2c - g2a) g2ia * (-g2u - g2r) g2ir - (g2c - g2a) g2ir * (-g2u - g2r) g2ia = 1
        by decide]
      norm_num)
  · exact hrot _ _ h1 h2 (by
      rw [show (-g2b - g2a) g2ia * (g2v - g2r) g2ir - (-g2b - g2a) g2ir * (g2v - g2r) g2ia = 1
        by decide]
      norm_num)
  ·
    refine hrefl (simple .G2 g2ia) g2ir (weyl_G2_ext ?_ ?_)
    · rw [h1, hinv, mul_smul, mul_smul, simple_smul, simple_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    · rw [h2, hinv, mul_smul, mul_smul, simple_smul, simple_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
  ·
    refine hrefl (simple .G2 g2ir) g2ia (weyl_G2_ext ?_ ?_)
    · rw [h1, hinv, mul_smul, mul_smul, simple_smul, simple_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    · rw [h2, hinv, mul_smul, mul_smul, simple_smul, simple_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
  ·
    have hwe : w = (simple .G2 g2ir * simple .G2 g2ia * (simple .G2 g2ir)⁻¹) *
        simple .G2 g2ia := by
      refine weyl_G2_ext ?_ ?_
      · rw [h1]
        simp only [hinv, mul_smul, simple_smul]
        exact List.ofFn_injective (by decide +kernel)
      · rw [h2]
        simp only [hinv, mul_smul, simple_smul]
        exact List.ofFn_injective (by decide +kernel)
    rw [hwe]
    exact mul_mem hsb hsa
  ·
    have hwe : w = simple .G2 g2ia *
        (simple .G2 g2ir * simple .G2 g2ia * (simple .G2 g2ir)⁻¹) := by
      refine weyl_G2_ext ?_ ?_
      · rw [h1]
        simp only [hinv, mul_smul, simple_smul]
        exact List.ofFn_injective (by decide +kernel)
      · rw [h2]
        simp only [hinv, mul_smul, simple_smul]
        exact List.ofFn_injective (by decide +kernel)
    rw [hwe]
    exact mul_mem hsa hsb
  ·
    refine hrefl (simple .G2 g2ia * simple .G2 g2ir) g2ia (weyl_G2_ext ?_ ?_)
    · rw [h1]
      simp only [mul_inv_rev, hinv, mul_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    · rw [h2]
      simp only [mul_inv_rev, hinv, mul_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
  ·
    refine hrefl (simple .G2 g2ir * simple .G2 g2ia) g2ir (weyl_G2_ext ?_ ?_)
    · rw [h1]
      simp only [mul_inv_rev, hinv, mul_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    · rw [h2]
      simp only [mul_inv_rev, hinv, mul_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
  · exact hrot _ _ h1 h2 (by
      rw [show (-g2a - g2a) g2ia * (-g2r - g2r) g2ir - (-g2a - g2a) g2ir * (-g2r - g2r) g2ia = 4
        by decide]
      norm_num)

end G2W

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.PerfectAutomorphisms

section Defs


@[expose] def ExcAlgTypeAAt (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup τ L p₀),
    S.D.q = 8 → ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ S.D.torus → (∀ j, a j ^ 3 = 1) →
      rootDiagUnit τ a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
        CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        (Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
            Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 504 ∨
          Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
            Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 5515776) →
        1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
          (componentRoots (rootCharHom a) i).ncard =
            compRank (componentRoots (rootCharHom a) i) *
              (compRank (componentRoots (rootCharHom a) i) + 1)

end Defs

@[expose] def E6CompAlgEight : Prop :=
  LieCompAlg fun e => ∃ q : TauCeti.PrimePower, e = .E6 q

section E6Defs


@[expose] def E6D4OuterNotEight : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup Tag.E6 L p₀),
    S.D.q = 8 → ∀ a : Fin Tag.E6.rank → Lˣ, rootDiagUnit Tag.E6 a ∈ S.D.torus →
      (∀ j, a j ^ 3 = 1) → rootDiagUnit Tag.E6 a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
        compRank (componentRoots (rootCharHom a) i) = 4 →
        (componentRoots (rootCharHom a) i).ncard = 24 →
        ¬ twistInner (componentRoots (rootCharHom a) i)
          ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom a) i)]) →
        CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        ¬ (Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
              Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 504 ∨
            Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
              Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 5515776)

@[expose] def E6EightCentralizerConn : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup Tag.E6 L p₀),
    S.D.q = 8 → ∀ a : Fin Tag.E6.rank → Lˣ, rootDiagUnit Tag.E6 a ∈ S.D.torus →
      (∀ j, a j ^ 3 = 1) → rootDiagUnit Tag.E6 a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
        CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        (Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
            Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 504 ∨
          Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
            Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 5515776) →
        ∀ y ∈ toralCentralizer Tag.E6 L a, S.D.step y = y →
          MulAut.conj y ∈
            CFSG.GroupActions.subgroupStabAut (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
          y ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a))

end E6Defs

section Adjoint


private theorem natCast_three_ne_zero_kd264alg {L : Type} [Field L] [CharP L 2] :
    ((3 : ℕ) : L) ≠ 0 := by
  have h2 : ((2 : ℕ) : L) = 0 := CharP.cast_eq_zero L 2
  have h3 : ((3 : ℕ) : L) = 1 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.cast_add, h2, zero_add, Nat.cast_one]
  rw [h3]
  exact one_ne_zero

theorem mem_inner_of_mem_innAutDerived_E_eight_kd264alg {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8)
    {β : MulAut ↥(adjointGroup τ K)} (hβmem : β ∈ innAutDerived ↥(adjointGroup τ K))
    (hβ3 : β ^ 3 = 1) : β ∈ inner ↥(adjointGroup τ K) := by
  classical
  obtain ⟨Θ, -, -, hker, -, -⟩ := ordinary_E_field_graph_quotient_and_involutions τ hτ K
  have hcomm : ∀ x y : RingAut K × Multiplicative (ZMod (exactE τ)), x * y = y * x := by
    rintro ⟨x1, x2⟩ ⟨y1, y2⟩
    exact Prod.ext (CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K x1 y1) (mul_comm x2 y2)
  have hinner : inner ↥(adjointGroup τ K) ≤ Θ.ker := by
    rintro _ ⟨g, rfl⟩
    refine (hker _).2 ⟨g, 1, fun h => ?_⟩
    simp [rootDiagUnit_one, MulAut.conj_apply]
  have hle : innAutDerived ↥(adjointGroup τ K) ≤ Θ.ker :=
    sup_le hinner (CFSG.HardMathSupport.Dickson.Sec6.I1431.excres_commutator_le_ker Θ hcomm)
  obtain ⟨g, a, hga⟩ := (hker β).1 (hle hβmem)
  have hβeq : β = MulAut.conj g * rootDiagAut τ K a := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    have h1 : ((rootDiagAut τ K a h : adjointGroup τ K) : ModGL τ K) =
        rootDiagUnit τ a * h * (rootDiagUnit τ a)⁻¹ := rfl
    rw [hga h, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, h1]
    group
  by_contra hβinn
  obtain ⟨-, h7⟩ := CFSG.HardMathSupport.Lang.E6Descent.prime_dvd_of_diag_noninner τ hτ K
    Nat.prime_three g a β hβeq hβ3 hβinn
  rw [hK] at h7
  norm_num at h7

theorem compAlgAt_adjointGroup_kd264alg
    {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 8)
    (hinn : ∀ β : MulAut ↥(adjointGroup τ K), β ∈ innAutDerived ↥(adjointGroup τ K) →
      β ^ 3 = 1 → β ∈ inner ↥(adjointGroup τ K))
    (hW : ∀ a : Fin τ.rank → (AlgebraicClosure K)ˣ, (∀ j, a j ^ 3 = 1) →
      rootDiagUnit τ a ≠ 1 → rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a)
    (hA : ExcAlgTypeAAt τ) :
    CompAlgAt ↥(adjointGroup τ K) := by
  classical
  intro β hβmem hβ3 hβ1 J hJ e he hiso x' hx'mem hx'3 hβx' hx'stab
  obtain ⟨x, rfl⟩ := hinn β hβmem hβ3
  obtain ⟨w, rfl⟩ := hinn x' hx'mem hx'3
  have hZ : Subgroup.center ↥(adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  have hx3 : x ^ 3 = 1 :=
    mulAut_conj_injective_of_center_eq_bot hZ (by rw [map_pow, hβ3, map_one])
  have hx1 : x ≠ 1 := fun h => hβ1 (by rw [h, map_one])
  have hxw : x * w = w * x :=
    mulAut_conj_injective_of_center_eq_bot hZ (by rw [map_mul, map_mul]; exact hβx')
  have h3K : ¬ 3 ∣ Nat.card K := by rw [hK]; norm_num
  have hmon : CFSG.HardMathSupport.Timmesfeld.CrossChar.MonomialToralAt τ 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (by rcases hτ with rfl | rfl | rfl | rfl | rfl <;> simp) Nat.prime_three (by norm_num)
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ := by
    rcases hτ with h' | h' | h' | h' | h'
    · subst h'
      exact (CFSG.LieType.Steinberg.Adjoint.isPerfect_g2_of_three_le_card K
        (by rw [hK]; norm_num)).commutator_eq_top
    all_goals exact single_edge_perfect τ K (by simp [h'])
  obtain ⟨S, a, ι, hSq, hT, hap, h1, hinj, hrange, hx, -⟩ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.exists_langSetup_of_inner_untw_of_prime_eq
      hτ Nat.prime_three h3K Nat.prime_three h3K (Or.inr (by rw [hK]; norm_num)) hmon hperf x hx3
      hx1
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 3)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hq8 : S.D.q = 8 := by rw [hSq, hK]
  have hTame := langSetup_hTame_of_prime S Nat.prime_three natCast_three_ne_zero_kd264alg
    (fun _ => Or.inr (by rw [hq8]; norm_num)) hT hap h1
  have hN := card_eq_of_compAlgEight_kd264alg e he hiso
  exact centerQuotientHom_mem_innAutDerived_of_langSetup_kd264alg S hq8 ι hinj hrange hT hap h1
    (hW a hap h1) hTame (fun i hqs hNi => hA (AlgebraicClosure K) 3 S hq8 a hT hap h1 i hqs hNi)
    hx hJ hN hxw hx'stab

end Adjoint

section NotTypeA

open CFSG.HardMathSupport.Dickson.Sec6.Up34Exc

set_option linter.unusedSectionVars false


theorem not_card_compAlgEight_of_inner_kd264alg {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀) (hq8 : S.D.q = 8) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hbig : 8 ≤ (componentRoots (rootCharHom a) i).ncard) :
    ¬ (Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 504 ∨
        Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 5515776) := by
  classical
  intro hN
  have hk : twistKind S.ρ (rootCharHom a) i = .inner := by
    unfold twistKind
    rw [if_pos hinner]
  obtain ⟨D⟩ := nonempty_innerData S hT i hk
  haveI := D.hKfin
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have he3 : D.e = 3 := by
    have h : (2 : ℕ) ^ D.e = 2 ^ 3 := by rw [← D.hq, hq8]; norm_num
    exact Nat.pow_right_injective le_rfl h
  have hs1 := D.hs0
  have hQ' : 4 ≤ 2 ^ (D.e * D.s) := by
    rw [he3]
    calc 4 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (3 * D.s) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨t, ht⟩ := CFSG.HardMathSupport.Timmesfeld.LangTorus.exists_unit_sq_ne_one (L := L) D.σ
    D.hσ (Nat.mul_pos D.he D.hs0) hQ'
  have hperf := isPerfect_componentRootSpan_of_sq_ne_one (K := fixSubfield D.σ)
    (χ := rootCharHom a) ht i
  obtain ⟨g, hg, hgk⟩ := exists_surjective_central_of_perfect D hperf
  obtain ⟨V, -, hVcard, hVZ⟩ := uniEmbed_holds τ (rootCharHom a) i (fixSubfield D.σ) 2
  obtain ⟨e⟩ := CFSG.Goldschmidt.G37.nonempty_centerQuotientEquiv hperf g hg hgk
  let g' : ↥V →* ↥(componentRootSpan (fixSubfield D.σ) (rootCharHom a) i) ⧸
      Subgroup.center ↥(componentRootSpan (fixSubfield D.σ) (rootCharHom a) i) :=
    (QuotientGroup.mk' _).comp V.subtype
  have hg'inj : Function.Injective g' := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : (x : ↥(componentRootSpan (fixSubfield D.σ) (rootCharHom a) i)) ∈
        Subgroup.center ↥(componentRootSpan (fixSubfield D.σ) (rootCharHom a) i) :=
      (QuotientGroup.eq_one_iff _).1 hx
    have hmem : (x : ↥(componentRootSpan (fixSubfield D.σ) (rootCharHom a) i)) ∈
        V ⊓ Subgroup.center ↥(componentRootSpan (fixSubfield D.σ) (rootCharHom a) i) :=
      ⟨x.2, hx'⟩
    rw [hVZ, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hdvd : Nat.card V ∣ Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
    rw [← Nat.card_congr e.toEquiv]
    exact Subgroup.card_dvd_of_injective g' hg'inj
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot τ).subset fun γ hγ => hΨ.isRoot γ hγ
  have h2N := ncard_eq_two_mul_ncard_posRoots hΨ hfin
  have hN4 : 4 ≤ (posRoots (componentRoots (rootCharHom a) i)).ncard := by omega
  rw [hVcard, D.hKcard, he3, ← pow_mul] at hdvd
  have hdvd' : 2 ^ (3 * D.s * (posRoots (componentRoots (rootCharHom a) i)).ncard) ∣
      Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) * 1 := by
    rw [mul_one]
    exact hdvd
  obtain ⟨h9, -⟩ := two_pow_le_of_dvd_kd264alg (by decide) hN hdvd'
  have : 3 * 1 * 4 ≤ 3 * D.s * (posRoots (componentRoots (rootCharHom a) i)).ncard :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 3 hs1) hN4
  omega

private theorem two_pow_dvd_orderTwistedD_kd264alg {n k : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    2 ^ (k * (n * (n - 1))) ∣ CFSG.Open.orderTwistedD n (2 ^ k) := by
  have hev : Even ((2 ^ k) ^ n) :=
    (Nat.even_pow' (by omega)).2 ((Nat.even_pow' (by omega)).2 even_two)
  have hodd : Odd ((2 ^ k) ^ n + 1) := hev.add_one
  have hg : Nat.gcd 4 ((2 ^ k) ^ n + 1) = 1 := by
    have h := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hodd)
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num] at h
    exact h
  unfold CFSG.Open.orderTwistedD
  rw [hg, Nat.div_one, pow_mul, mul_assoc]
  exact Dvd.intro _ rfl

private theorem two_pow_dvd_orderTwistedE6_kd264alg {k : ℕ} :
    2 ^ (36 * k) ∣ CFSG.Open.orderTwistedE6 (2 ^ k) := by
  set q : ℕ := 2 ^ k with hq
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  have hsq : q + 1 ∣ q ^ 2 - 1 := ⟨q - 1, by rw [← Nat.sq_sub_sq, one_pow]⟩
  have hGd : Nat.gcd 3 (q + 1) ∣ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) *
      (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1) :=
    Dvd.dvd.mul_left ((Nat.gcd_dvd_right _ _).trans hsq) _
  have hmul := Nat.div_mul_cancel hGd
  have h36 : 2 ^ (36 * k) ∣ CFSG.Open.orderTwistedE6 q * Nat.gcd 3 (q + 1) := by
    unfold CFSG.Open.orderTwistedE6
    rw [hmul, mul_comm 36 k, pow_mul, ← hq]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right
      (Dvd.dvd.mul_right (Dvd.dvd.mul_right dvd_rfl _) _) _) _) _) _
  have hcop : Nat.Coprime (2 ^ (36 * k)) (Nat.gcd 3 (q + 1)) :=
    Nat.Coprime.pow_left _ (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 3 _) (by norm_num))
  exact hcop.dvd_of_dvd_mul_right h36


open CFSG.Open CFSG.Blueprint in
theorem not_card_compAlgEight_of_lieModel_POmegaMinus_kd264alg {G : Type} [Group G] [Finite G]
    {n e : ℕ} (h : LieModel G .POmegaMinus n 2 e) :
    ¬ (Nat.card G = 504 ∨ Nat.card G = 5515776) := by
  intro hG
  have hclass : StatedClassicalModel G .POmegaMinus n 2 e := h.statedClassicalModel (by decide)
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨eG⟩⟩ := hclass
  haveI : Fintype K := Fintype.ofFinite K
  have hn4 : 4 ≤ n := h.admissible.2.2
  have he : 0 < e := h.admissible.2.1
  obtain ⟨q, hv, hqp, ⟨eq⟩⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn.exists_twistedD_of_statedProj_minus
      (K := K) n hn4 hirr
  have hcard : Nat.card G = CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula
      (.twistedD n q) :=
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.twistedD n q, hv⟩ G
      ⟨eG.trans eq⟩
  change Nat.card G = CFSG.Open.orderTwistedD n q.card at hcard
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := e)
    (by rw [← Nat.card_eq_fintype_card, hK])
  have hq2 : q.p = 2 := hqp.trans (ringChar.eq K 2)
  have hqc : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq2]
  rw [hqc] at hcard
  have hdvd := two_pow_dvd_orderTwistedD_kd264alg (n := n) q.exponent_pos (by omega)
  rw [← hcard] at hdvd
  have hdvd' : 2 ^ (q.exponent * (n * (n - 1))) ∣ Nat.card G * 1 := by
    rw [mul_one]
    exact hdvd
  obtain ⟨h9, -⟩ := two_pow_le_of_dvd_kd264alg (by decide) hG hdvd'
  have h12 : 12 ≤ n * (n - 1) := le_trans (by norm_num : 12 ≤ 4 * 3) (Nat.mul_le_mul hn4 (by omega))
  have : 1 * 12 ≤ q.exponent * (n * (n - 1)) := Nat.mul_le_mul q.exponent_pos h12
  omega

open CFSG.Open CFSG.Blueprint in
theorem not_card_compAlgEight_of_lieModel_twistedE6_kd264alg {G : Type} [Group G] [Finite G]
    {f : ℕ} (h : LieModel G .twistedE6 0 2 f) :
    ¬ (Nat.card G = 504 ∨ Nat.card G = 5515776) := by
  intro hG
  have hadm := LieModel.admissible h
  have hp : (2 : ℕ).Prime := hadm.1
  have hf : 0 < f := hadm.2.1
  rcases h with ⟨ht, -⟩ | ⟨-, -, hmod⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · simp [classicalTags] at ht
  · obtain ⟨-, K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hmod
    let q : TauCeti.PrimePower := ⟨2, f, hp, hf⟩
    have hv := TauCeti.LieTypeIndex.valid_twistedE6 q
    obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q hv K
      (by rw [hK, TauCeti.PrimePower.card_def]) σ
      (fun x => by rw [hσ, TauCeti.PrimePower.card_def])
    have hcard : Nat.card G = CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula
        (.twistedE6 q) :=
      CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.twistedE6 q, hv⟩ G
        ⟨e.trans b⟩
    change Nat.card G = CFSG.Open.orderTwistedE6 q.card at hcard
    have hqc : q.card = 2 ^ f := TauCeti.PrimePower.card_def q
    rw [hqc] at hcard
    have hdvd := two_pow_dvd_orderTwistedE6_kd264alg (k := f)
    rw [← hcard] at hdvd
    have hdvd' : 2 ^ (36 * f) ∣ Nat.card G * 1 := by
      rw [mul_one]
      exact hdvd
    obtain ⟨h9, -⟩ := two_pow_le_of_dvd_kd264alg (by decide) hG hdvd'
    omega
  · simp [reeTitsTags] at ht
  · exact absurd ht (by decide)

end NotTypeA

section D4Shape

open CFSG.LieType.Steinberg.Adjoint
open scoped Matrix


theorem not_d4Shape_E8_three_kd264alg {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E8 L p₀) (h3 : ((3 : ℕ) : L) ≠ 0)
    {a : Fin Tag.E8.rank → Lˣ} (hTp : rootDiagUnit Tag.E8 a ^ 3 = 1)
    (i : KernelComponent (rootCharHom a)) :
    ¬ (compRank (componentRoots (rootCharHom a) i) = 4 ∧
       (componentRoots (rootCharHom a) i).ncard = 24) := by
  rintro ⟨hrank, hncard⟩
  obtain ⟨v, μ, hμ, hall⟩ :=
    S.exists_kacT_of_prime (K := kacE8) Nat.prime_three h3 facts_E8 hTp
  obtain ⟨x, -, hi⟩ := hall i
  let C : Finset (Option (Fin Tag.E8.rank)) :=
    (Set.toFinite (KacData.comp kacE8 3 μ x)).toFinset
  have hCcoe : KacData.comp kacE8 3 μ x = (C : Set (Option (Fin Tag.E8.rank))) :=
    (Set.toFinite _).coe_toFinset.symm
  have hCp : ∃ z, z ∉ C := by
    obtain ⟨z, hz⟩ := exists_not_mem_comp kacE8 (by norm_num : 0 < 3) μ x
    exact ⟨z, fun h => hz ((Set.toFinite _).mem_toFinset.1 h)⟩
  rw [hCcoe] at hi
  have hrankC : compRank (componentRoots (rootCharHom a) i) = C.card := by
    rw [hi, compRank_image, compRank_rootsOf kacE8 facts_E8 hCp]
  have hncardC : (componentRoots (rootCharHom a) i).ncard =
      kacCount .E8 kacE8.θ C := by
    rw [hi, ncard_image_smul, ncard_rootsOf kacE8 facts_E8 hCp]
  rw [hrankC] at hrank
  rw [hncardC] at hncard
  have hCeq : C = {some 1, some 2, some 3, some 4} := kacCount_E8_four C hrank hncard
  have h2c : (some 2 : Option (Fin Tag.E8.rank)) ∈ KacData.comp kacE8 3 μ x := by
    rw [hCcoe, hCeq]
    simp
  have h4c : (some 4 : Option (Fin Tag.E8.rank)) ∈ KacData.comp kacE8 3 μ x := by
    rw [hCcoe, hCeq]
    simp
  have h0z : ¬ KacData.IsZ kacE8 3 μ (some 0) := by
    intro hz
    have hadj : KacData.Adj kacE8 (some 2) (some 0) := by
      rw [e8_adj]
      decide
    have hm : (some 0 : Option (Fin Tag.E8.rank)) ∈ KacData.comp kacE8 3 μ x :=
      ⟨hz, h2c.2.trans _ _ _ (Relation.EqvGen.rel _ _ ⟨h2c.1, hz, hadj⟩)⟩
    rw [hCcoe, hCeq] at hm
    exact absurd hm (by decide)
  have h5z : ¬ KacData.IsZ kacE8 3 μ (some 5) := by
    intro hz
    have hadj : KacData.Adj kacE8 (some 4) (some 5) := by
      rw [e8_adj]
      decide
    have hm : (some 5 : Option (Fin Tag.E8.rank)) ∈ KacData.comp kacE8 3 μ x :=
      ⟨hz, h4c.2.trans _ _ _ (Relation.EqvGen.rel _ _ ⟨h4c.1, hz, hadj⟩)⟩
    rw [hCcoe, hCeq] at hm
    exact absurd hm (by decide)
  change ¬ μ 0 = 0 at h0z
  change ¬ μ 5 = 0 at h5z
  have hm0 : 1 ≤ μ 0 := by
    have := hμ.1 0
    omega
  have hm5 : 1 ≤ μ 5 := by
    have := hμ.1 5
    omega
  have hθ : kacE8.θ ⬝ᵥ μ =
      2 * μ 0 + 3 * μ 1 + 4 * μ 2 + 6 * μ 3 + 5 * μ 4 + 4 * μ 5 + 3 * μ 6 +
        2 * μ 7 := by
    rw [show kacE8.θ = ![2, 3, 4, 6, 5, 4, 3, 2] from rfl]
    show ∑ j : Fin 8, (![2, 3, 4, 6, 5, 4, 3, 2] : Fin 8 → ℤ) j * μ j = _
    rw [Fin.sum_univ_eight]
    rfl
  have hμ2 : kacE8.θ ⬝ᵥ μ ≤ (3 : ℤ) := hμ.2
  rw [hθ] at hμ2
  have h1 := hμ.1 1
  have h2 := hμ.1 2
  have h3' := hμ.1 3
  have h4 := hμ.1 4
  have h6 := hμ.1 6
  have h7 := hμ.1 7
  omega

theorem not_d4Shape_E7_three_kd264alg {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E7 L p₀) (h3 : ((3 : ℕ) : L) ≠ 0)
    {a : Fin Tag.E7.rank → Lˣ} (hTp : rootDiagUnit Tag.E7 a ^ 3 = 1)
    (i : KernelComponent (rootCharHom a)) :
    ¬ (compRank (componentRoots (rootCharHom a) i) = 4 ∧
       (componentRoots (rootCharHom a) i).ncard = 24) := by
  rintro ⟨hrank, hncard⟩
  obtain ⟨v, μ, hμ, hall⟩ :=
    S.exists_kacT_of_prime (K := kacE7) Nat.prime_three h3 facts_E7 hTp
  obtain ⟨x, -, hi⟩ := hall i
  let C : Finset (Option (Fin Tag.E7.rank)) :=
    (Set.toFinite (KacData.comp kacE7 3 μ x)).toFinset
  have hCcoe : KacData.comp kacE7 3 μ x = (C : Set (Option (Fin Tag.E7.rank))) :=
    (Set.toFinite _).coe_toFinset.symm
  have hCp : ∃ z, z ∉ C := by
    obtain ⟨z, hz⟩ := exists_not_mem_comp kacE7 (by norm_num : 0 < 3) μ x
    exact ⟨z, fun h => hz ((Set.toFinite _).mem_toFinset.1 h)⟩
  rw [hCcoe] at hi
  have hrankC : compRank (componentRoots (rootCharHom a) i) = C.card := by
    rw [hi, compRank_image, compRank_rootsOf kacE7 facts_E7 hCp]
  have hncardC : (componentRoots (rootCharHom a) i).ncard =
      kacCount .E7 kacE7.θ C := by
    rw [hi, ncard_image_smul, ncard_rootsOf kacE7 facts_E7 hCp]
  rw [hrankC] at hrank
  rw [hncardC] at hncard
  have hCeq : C = {some 1, some 2, some 3, some 4} := kacCount_E7_four C hrank hncard
  have h2c : (some 2 : Option (Fin Tag.E7.rank)) ∈ KacData.comp kacE7 3 μ x := by
    rw [hCcoe, hCeq]
    simp
  have h4c : (some 4 : Option (Fin Tag.E7.rank)) ∈ KacData.comp kacE7 3 μ x := by
    rw [hCcoe, hCeq]
    simp
  have h0z : ¬ KacData.IsZ kacE7 3 μ (some 0) := by
    intro hz
    have hadj : KacData.Adj kacE7 (some 2) (some 0) := by
      rw [e7_adj]
      decide
    have hm : (some 0 : Option (Fin Tag.E7.rank)) ∈ KacData.comp kacE7 3 μ x :=
      ⟨hz, h2c.2.trans _ _ _ (Relation.EqvGen.rel _ _ ⟨h2c.1, hz, hadj⟩)⟩
    rw [hCcoe, hCeq] at hm
    exact absurd hm (by decide)
  have h5z : ¬ KacData.IsZ kacE7 3 μ (some 5) := by
    intro hz
    have hadj : KacData.Adj kacE7 (some 4) (some 5) := by
      rw [e7_adj]
      decide
    have hm : (some 5 : Option (Fin Tag.E7.rank)) ∈ KacData.comp kacE7 3 μ x :=
      ⟨hz, h4c.2.trans _ _ _ (Relation.EqvGen.rel _ _ ⟨h4c.1, hz, hadj⟩)⟩
    rw [hCcoe, hCeq] at hm
    exact absurd hm (by decide)
  change ¬ μ 0 = 0 at h0z
  change ¬ μ 5 = 0 at h5z
  have hm0 : 1 ≤ μ 0 := by
    have := hμ.1 0
    omega
  have hm5 : 1 ≤ μ 5 := by
    have := hμ.1 5
    omega
  have hθ : kacE7.θ ⬝ᵥ μ =
      2 * μ 0 + 2 * μ 1 + 3 * μ 2 + 4 * μ 3 + 3 * μ 4 + 2 * μ 5 + 1 * μ 6 := by
    rw [show kacE7.θ = ![2, 2, 3, 4, 3, 2, 1] from rfl]
    show ∑ j : Fin 7, (![2, 2, 3, 4, 3, 2, 1] : Fin 7 → ℤ) j * μ j = _
    rw [Fin.sum_univ_seven]
    rfl
  have hμ2 : kacE7.θ ⬝ᵥ μ ≤ (3 : ℤ) := hμ.2
  rw [hθ] at hμ2
  have h1 := hμ.1 1
  have h2 := hμ.1 2
  have h3' := hμ.1 3
  have h4 := hμ.1 4
  have h6 := hμ.1 6
  omega

end D4Shape

section TypeAHolds

open CFSG.HardMathSupport.Dickson.Sec6.Up34Exc ExcUntw

set_option linter.unusedSectionVars false


theorem excAlgTypeAAt_F4_kd264alg : ExcAlgTypeAAt .F4 := by
  intro L _ _ _ p₀ S hq8 a hT hap h1 i _ hN
  by_contra hnA
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  rcases f4_nonA_casesP Nat.prime_three (by norm_num) S natCast_three_ne_zero_kd264alg hTp h1 i
    hnA with ⟨hr, hn⟩ | ⟨v, J, -, -, hr, hn⟩
  · exact not_card_compAlgEight_of_inner_kd264alg S hq8 hT i
      (twistInner_of_shape S hT i 2 8 hr hn (by omega) (by omega) (by omega) (by omega))
      (by omega) hN
  · exact not_card_compAlgEight_of_inner_kd264alg S hq8 hT i
      (twistInner_of_shape S hT i 3 18 hr hn (by omega) (by omega) (by omega) (by omega))
      (by omega) hN

theorem excAlgTypeAAt_E8_kd264alg : ExcAlgTypeAAt .E8 := by
  intro L _ _ _ p₀ S hq8 a hT hap h1 i _ hN
  classical
  by_contra hnA
  have h3L := natCast_three_ne_zero_kd264alg (L := L)
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  haveI := finite_rationalComponent S a i
  obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
    exists_cand_of_class kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card S Nat.prime_three
      h3L hTp i
  have hshape := e8_shape c hc hlen
  rw [← hncard, ← hrank] at hshape
  rcases hshape with hA' | hD | hE
  · exact hnA hA'
  ·
    have hr5 : 5 ≤ compRank (componentRoots (rootCharHom a) i) := by
      by_contra hlt
      have hr4 : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
      exact not_d4Shape_E8_three_kd264alg S h3L hTp i ⟨hr4, by rw [hD.2, hr4]⟩
    by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])
    · refine not_card_compAlgEight_of_inner_kd264alg S hq8 hT i hinner ?_ hN
      rw [hD.2]
      calc 8 ≤ 2 * 5 * 4 := by norm_num
        _ ≤ 2 * compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) - 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 2 hr5) (by omega)
    · obtain ⟨m, e, -, hlie⟩ := lieModel_rationalComponent_of_twoD_highG Nat.prime_three S hT hap h1
        i hr5 hD.2 hinner (fun _ _ => True)
        (fun r _ _ e m he hm5 _ => CompsPTwoDChainO.twoDChainRecog_all he (by omega)) trivial
      rw [ringChar.eq L 2] at hlie
      exact not_card_compAlgEight_of_lieModel_POmegaMinus_kd264alg hlie hN
  ·
    by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])
    · refine not_card_compAlgEight_of_inner_kd264alg S hq8 hT i hinner ?_ hN
      have hr8 : compRank (componentRoots (rootCharHom a) i) ≤ 8 := by
        have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
        rwa [show Tag.E8.rank = 8 from rfl] at hle
      rw [hE.2]
      have hc : compRank (componentRoots (rootCharHom a) i) = 6 ∨
          compRank (componentRoots (rootCharHom a) i) = 7 ∨
          compRank (componentRoots (rootCharHom a) i) = 8 := by omega
      rcases hc with h6 | h7 | h8
      · rw [h6]
        norm_num [eRootCount]
      · rw [h7]
        norm_num [eRootCount]
      · rw [h8]
        norm_num [eRootCount]
    · obtain ⟨f, -, -, hlie⟩ := lieModel_rationalComponent_of_outer_E8 S Nat.prime_three h3L hT hTp
        i hE.1 hE.2 hinner
      rw [ringChar.eq L 2] at hlie
      exact not_card_compAlgEight_of_lieModel_twistedE6_kd264alg hlie hN

theorem excAlgTypeAAt_E7_kd264alg : ExcAlgTypeAAt .E7 := by
  intro L _ _ _ p₀ S hq8 a hT hap h1 i _ hN
  classical
  by_contra hnA
  have h3L := natCast_three_ne_zero_kd264alg (L := L)
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  haveI := finite_rationalComponent S a i
  obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
    exists_cand_of_class kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt e7_card S Nat.prime_three
      h3L hTp i
  have hshape := e7_shape c hc hlen
  rw [← hncard, ← hrank] at hshape
  rcases hshape with hA' | hD | hE
  · exact hnA hA'
  ·
    have hr5 : 5 ≤ compRank (componentRoots (rootCharHom a) i) := by
      by_contra hlt
      have hr4 : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
      exact not_d4Shape_E7_three_kd264alg S h3L hTp i ⟨hr4, by rw [hD.2, hr4]⟩
    by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])
    · refine not_card_compAlgEight_of_inner_kd264alg S hq8 hT i hinner ?_ hN
      rw [hD.2]
      calc 8 ≤ 2 * 5 * 4 := by norm_num
        _ ≤ 2 * compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) - 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 2 hr5) (by omega)
    · obtain ⟨m, e, -, hlie⟩ := lieModel_rationalComponent_of_twoD_highG Nat.prime_three S hT hap h1
        i hr5 hD.2 hinner (fun _ _ => True)
        (fun r _ _ e m he hm5 _ => CompsPTwoDChainO.twoDChainRecog_all he (by omega)) trivial
      rw [ringChar.eq L 2] at hlie
      exact not_card_compAlgEight_of_lieModel_POmegaMinus_kd264alg hlie hN
  ·
    by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])
    · refine not_card_compAlgEight_of_inner_kd264alg S hq8 hT i hinner ?_ hN
      have hr7 : compRank (componentRoots (rootCharHom a) i) ≤ 7 := by
        have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
        rwa [show Tag.E7.rank = 7 from rfl] at hle
      rw [hE.2]
      have hc : compRank (componentRoots (rootCharHom a) i) = 6 ∨
          compRank (componentRoots (rootCharHom a) i) = 7 := by omega
      rcases hc with h6 | h7
      · rw [h6]
        norm_num [eRootCount]
      · rw [h7]
        norm_num [eRootCount]
    · obtain ⟨f, -, -, hlie⟩ := lieModel_rationalComponent_of_outer_E7 S Nat.prime_three h3L hT hTp
        i hE.1 hE.2 hinner
      rw [ringChar.eq L 2] at hlie
      exact not_card_compAlgEight_of_lieModel_twistedE6_kd264alg hlie hN

theorem excAlgTypeAAt_E6_of_kd264alg (hR1 : E6D4OuterNotEight) : ExcAlgTypeAAt .E6 := by
  intro L _ _ _ p₀ S hq8 a hT hap h1 i hqs hN
  classical
  by_contra hnA
  have h3L := natCast_three_ne_zero_kd264alg (L := L)
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  haveI := finite_rationalComponent S a i
  obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
    exists_cand_of_class kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt e6_card S Nat.prime_three
      h3L hTp i
  have hshape := e6_shape c hc hlen
  rw [← hncard, ← hrank] at hshape
  rcases hshape with hA' | hD | hE
  · exact hnA hA'
  · by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])
    · refine not_card_compAlgEight_of_inner_kd264alg S hq8 hT i hinner ?_ hN
      rw [hD.2]
      calc 8 ≤ 2 * 4 * 3 := by norm_num
        _ ≤ 2 * compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) - 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 2 hD.1) (by omega)
    · rcases Nat.lt_or_ge (compRank (componentRoots (rootCharHom a) i)) 5 with hlt | hr5
      · have hr4 : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
        exact hR1 L p₀ S hq8 a hT hap h1 i hr4 (by rw [hD.2, hr4]) hinner hqs hN
      · obtain ⟨m, e, -, hlie⟩ := lieModel_rationalComponent_of_twoD_highG Nat.prime_three S hT hap
          h1 i hr5 hD.2 hinner (fun _ _ => True)
          (fun r _ _ e m he hm5 _ => CompsPTwoDChainO.twoDChainRecog_all he (by omega)) trivial
        rw [ringChar.eq L 2] at hlie
        exact not_card_compAlgEight_of_lieModel_POmegaMinus_kd264alg hlie hN
  · exact false_of_e6Class_E S Nat.prime_three h3L hTp h1 i hE.1 hE.2

end TypeAHolds

section Family

open CFSG.LieType.SeitzGeneration

set_option linter.unusedSectionVars false


theorem excAlgTypeAAt_G2_kd264alg : ExcAlgTypeAAt .G2 := by
  intro L _ _ _ p₀ S _ a _ hap h1 i _ _
  by_contra hnA
  exact false_of_g2Class_nonAP Nat.prime_three S natCast_three_ne_zero_kd264alg
    (rootDiagUnit_pow_eq_one_of_forall hap) h1 i hnA

private theorem ne_one_of_rootDiagUnit_ne_one_kd264alg {τ : Tag} {L : Type} [Field L]
    {a : Fin τ.rank → Lˣ} (h1 : rootDiagUnit τ a ≠ 1) : a ≠ 1 := fun h =>
  h1 (by rw [h, rootDiagUnit_one])

theorem lieCompAlg_excUntwisted_of_kd264alg (hE6 : E6CompAlgEight) (hF4 : ExcAlgTypeAAt .F4)
    (hE7 : ExcAlgTypeAAt .E7) (hE8 : ExcAlgTypeAAt .E8) : LieCompAlg isExcUntwistedIdx := by
  intro d hP hfield
  obtain ⟨e, hv⟩ := d
  cases e with
  | G2 q =>
    obtain ⟨K, _, _, hK, hKc, ⟨eK⟩⟩ :=
      exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
    have hK8 : Nat.card K = 8 := by rw [hK]; exact hfield
    haveI : Fintype K := Fintype.ofFinite K
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 3)
      (by rw [← Nat.card_eq_fintype_card, hK8]; norm_num)
    have hchar : ringChar K ≠ 3 := by rw [ringChar.eq K 2]; norm_num
    refine compAlgAt_of_mulEquiv eK.symm (compAlgAt_adjointGroup_kd264alg (Or.inl rfl) hK8
      (fun β hβ _ => CFSG.HardMathSupport.Dickson.Sec6.I1431.t6outg2_innAutDerived_le_inner hchar
        (by rw [hK8]; norm_num) hβ)
      (fun a hap h1 => rootCharStabilizer_le_kernelReflectionGroup_G2_three_kd264alg
        (funext fun j => by rw [Pi.pow_apply, hap j, Pi.one_apply])
        (ne_one_of_rootDiagUnit_ne_one_kd264alg h1))
      excAlgTypeAAt_G2_kd264alg)
  | F4 q =>
    obtain ⟨K, _, _, hK, hKc, ⟨eK⟩⟩ :=
      exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv
    have hK8 : Nat.card K = 8 := by rw [hK]; exact hfield
    refine compAlgAt_of_mulEquiv eK.symm (compAlgAt_adjointGroup_kd264alg (Or.inr (Or.inl rfl)) hK8
      (fun β hβ _ => CFSG.HardMathSupport.Dickson.Sec6.I1431.excres_innAutDerived_le_inner_F4
        (p := 2) (f := 3) Nat.prime_two (by norm_num) (by rw [hK8]; norm_num) hβ)
      (fun a hap _ =>
        (CFSG.HardMathSupport.Timmesfeld.Steinberg.rootCharStabilizerSubgroup_eq_kernelReflectionGroup_F4_three
          a hap).le)
      hF4)
  | E6 q => exact hE6 ⟨.E6 q, hv⟩ ⟨q, rfl⟩ hfield
  | E7 q =>
    obtain ⟨K, _, _, hK, hKc, ⟨eK⟩⟩ :=
      exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv
    have hK8 : Nat.card K = 8 := by rw [hK]; exact hfield
    refine compAlgAt_of_mulEquiv eK.symm (compAlgAt_adjointGroup_kd264alg
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hK8
      (fun β hβ hβ3 => mem_inner_of_mem_innAutDerived_E_eight_kd264alg (Or.inr (Or.inl rfl)) hK8
        hβ hβ3)
      (fun a hap _ =>
        (CFSG.HardMathSupport.Timmesfeld.Steinberg.rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E7_three
          a hap).le)
      hE7)
  | E8 q =>
    obtain ⟨K, _, _, hK, hKc, ⟨eK⟩⟩ :=
      exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv
    have hK8 : Nat.card K = 8 := by rw [hK]; exact hfield
    refine compAlgAt_of_mulEquiv eK.symm (compAlgAt_adjointGroup_kd264alg
      (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hK8
      (fun β hβ hβ3 => mem_inner_of_mem_innAutDerived_E_eight_kd264alg (Or.inr (Or.inr rfl)) hK8
        hβ hβ3)
      (fun a hap _ =>
        (CFSG.HardMathSupport.Timmesfeld.Steinberg.rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E8_three
          a hap).le)
      hE8)
  | _ => exact absurd hP (by simp [isExcUntwistedIdx])

theorem lieCompAlg_excUntwisted_of_E6_kd264alg (hE6 : E6CompAlgEight) :
    LieCompAlg isExcUntwistedIdx :=
  lieCompAlg_excUntwisted_of_kd264alg hE6 excAlgTypeAAt_F4_kd264alg excAlgTypeAAt_E7_kd264alg
    excAlgTypeAAt_E8_kd264alg

theorem compAlgAt_adjointGroup_E6_kd264alg {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8)
    (hR1 : E6D4OuterNotEight) (hR2 : E6EightCentralizerConn) :
    CompAlgAt ↥(adjointGroup .E6 K) := by
  classical
  intro β hβmem hβ3 hβ1 J hJ e he hiso x' hx'mem hx'3 hβx' hx'stab
  obtain ⟨x, rfl⟩ := mem_inner_of_mem_innAutDerived_E_eight_kd264alg (Or.inl rfl) hK hβmem hβ3
  obtain ⟨w, rfl⟩ := mem_inner_of_mem_innAutDerived_E_eight_kd264alg (Or.inl rfl) hK hx'mem hx'3
  have hZ : Subgroup.center ↥(adjointGroup .E6 K) = ⊥ := center_adjointGroup_eq_bot
  have hx3 : x ^ 3 = 1 :=
    mulAut_conj_injective_of_center_eq_bot hZ (by rw [map_pow, hβ3, map_one])
  have hx1 : x ≠ 1 := fun h => hβ1 (by rw [h, map_one])
  have hxw : x * w = w * x :=
    mulAut_conj_injective_of_center_eq_bot hZ (by rw [map_mul, map_mul]; exact hβx')
  have h3K : ¬ 3 ∣ Nat.card K := by rw [hK]; norm_num
  have hmon : CFSG.HardMathSupport.Timmesfeld.CrossChar.MonomialToralAt .E6 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) Nat.prime_three
      (by norm_num)
  have hperf : commutator ↥(adjointGroup .E6 K) = ⊤ := single_edge_perfect .E6 K (by simp)
  obtain ⟨S, a, ι, hSq, hT, hap, h1, hinj, hrange, hx, -⟩ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.exists_langSetup_of_inner_untw_of_prime_eq
      (Or.inr (Or.inr (Or.inl rfl))) Nat.prime_three h3K Nat.prime_three h3K
      (Or.inr (by rw [hK]; norm_num)) hmon hperf x hx3 hx1
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 3)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hq8 : S.D.q = 8 := by rw [hSq, hK]
  have hTame := langSetup_hTame_of_prime S Nat.prime_three natCast_three_ne_zero_kd264alg
    (fun h => absurd h (by decide)) hT hap h1
  have hN := card_eq_of_compAlgEight_kd264alg e he hiso
  have hβ : ∀ c, ι (MulAut.conj x c) = rootDiagUnit .E6 a * ι c * (rootDiagUnit .E6 a)⁻¹ :=
    fun c => by rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hx]
  have hφy : ∀ c, ι (MulAut.conj w c) = ι w * ι c * (ι w)⁻¹ :=
    fun c => by rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hyΓ : ι w ∈ S.Γ := hrange ▸ ⟨w, rfl⟩
  have hyF : S.D.step (ι w) = ι w := ((Subgroup.commutator_le_self S.D.model) hyΓ).2
  have hyG : ι w ∈ adjointGroup .E6 (AlgebraicClosure K) :=
    ((Subgroup.commutator_le_self S.D.model) hyΓ).1
  have hyd : rootDiagUnit .E6 a * ι w * (rootDiagUnit .E6 a)⁻¹ = ι w := by
    rw [← hx, ← map_mul, ← map_inv, ← map_mul, hxw, mul_inv_cancel_right]
  have hyC : ι w ∈ toralCentralizer .E6 (AlgebraicClosure K) a := mem_toralCentralizer.2 ⟨hyG, hyd⟩
  exact centerQuotientHom_mem_innAutDerived_of_langSetup_conj_kd264alg S hq8 ι hinj hrange hT hap
    h1 hTame
    (fun i hqs hNi => excAlgTypeAAt_E6_of_kd264alg hR1 (AlgebraicClosure K) 3 S hq8 a hT hap h1 i
      hqs hNi)
    hβ hJ hN hx'stab hφy hyF
    (fun i hqs hNi hyR => hR2 (AlgebraicClosure K) 3 S hq8 a hT hap h1 i hqs hNi (ι w) hyC hyF hyR)

theorem e6CompAlgEight_of_kd264alg (hR1 : E6D4OuterNotEight) (hR2 : E6EightCentralizerConn) :
    E6CompAlgEight := by
  intro d hP hfield
  obtain ⟨e, hv⟩ := d
  obtain ⟨q, rfl⟩ := hP
  obtain ⟨K, _, _, hK, -, ⟨eK⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
  have hK8 : Nat.card K = 8 := by rw [hK]; exact hfield
  exact compAlgAt_of_mulEquiv eK.symm (compAlgAt_adjointGroup_E6_kd264alg hK8 hR1 hR2)

theorem lieCompAlg_excUntwisted_of_E6res_kd264alg (hR1 : E6D4OuterNotEight)
    (hR2 : E6EightCentralizerConn) : LieCompAlg isExcUntwistedIdx :=
  lieCompAlg_excUntwisted_of_E6_kd264alg (e6CompAlgEight_of_kd264alg hR1 hR2)

end Family

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end

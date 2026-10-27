module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsTwoE
public import CFSG.LieType.Chevalley.EvenF4OuterInvolutionsCanonical

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T

set_option linter.unusedSectionVars false

theorem mem_torusGroup_of_commute_dV {τ : Tag} {L : Type} [Field L]
    {ω : Lˣ} (hω : orderOf ω = 3) (hcert : Native.hypOK τ = true) {g : ModGL τ L}
    (hg : g ∈ adjointGroup τ L) (h : ∀ x : Fin τ.rank → ZMod 3, Commute (dV ω x) g) :
    g ∈ torusGroup τ L := by
  have hstd := famData0_of_famOK0 (τ := τ) hω length_of_mem_stdBasis lt_of_mem_stdBasis
    (famOK_std_of_hypOK hcert)
  have hgC : g ∈ familyCentralizer τ L (famV (τ := τ) ω (Native.stdBasis τ.rank)) := by
    rw [mem_familyCentralizer]
    refine ⟨hg, fun j => ?_⟩
    change dV ω (listVec τ.rank ((Native.stdBasis τ.rank).get j)) * g *
      (dV ω (listVec τ.rank ((Native.stdBasis τ.rank).get j)))⁻¹ = g
    rw [(h _).eq, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨w, hw, m, hm, rfl⟩ := familyCentralizer_le_mul τ L _ hgC
  rw [hstd.2 w hw, canonicalRep_one, mul_one]
  have hm' : m ∈ torusGroup τ L ⊔
      rootSpan τ L (familyKernel (famV (τ := τ) ω (Native.stdBasis τ.rank))) := hm
  rw [hstd.1] at hm'
  have hbot : rootSpan τ L (∅ : Set (Fin τ.rank → ℤ)) = ⊥ := by simp [rootSpan]
  rwa [hbot, sup_bot_eq] at hm'

variable {K : Type} [Field K] [Finite K]

section Rigid


open CFSG.LieType.Ree CFSG.RankThree.LargeReeOrder in
theorem mem_innerAut_of_fix_reeF4_two (hK : Nat.card K = 2) {t : adjointGroup ReeTag.F4.tag K}
    {A : Subgroup (adjointGroup ReeTag.F4.tag K)} (hAt : A ≤ Subgroup.centralizer {t})
    (hAcard : Nat.card A = 81)
    (hAc : ∀ y : adjointGroup ReeTag.F4.tag K, (∀ a ∈ A, y * a = a * y) → y ^ 3 = 1)
    (α : MulAut (adjointGroup ReeTag.F4.tag K))
    (hfix : ∀ y ∈ Subgroup.centralizer {t}, α y = y) :
    α ∈ innerAut (adjointGroup ReeTag.F4.tag K) := by
  have : CharP K 2 := charP_two_of_card_two hK
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  have hK1 : Nat.card K = 2 ^ 1 := by rw [hK]; norm_num
  obtain ⟨-, hnf, ⟨Θ, hΘ, -, hker⟩, -, ⟨hφ2, -⟩, -, hodd⟩ :=
    even_F4_exact_automorphism_normal_form (f := 1) le_rfl K hK1
  set φ := ReeTag.F4.finiteExceptionalAut K with hφ
  have hφsq : φ * φ = 1 := by
    rw [pow_one, pow_two] at hφ2
    exact hφ2
  obtain ⟨⟨g, k⟩, hgk, -⟩ := hnf α
  simp only at hgk
  have hk : (k : ℕ) = 0 ∨ (k : ℕ) = 1 := by
    have := k.2
    omega
  rcases hk with hk0 | hk1
  · rw [hk0, pow_zero, mul_one] at hgk
    exact ⟨g, hgk.symm⟩
  · exfalso
    rw [hk1, pow_one] at hgk
    have hconj : ∀ (ψ : MulAut (adjointGroup ReeTag.F4.tag K)) (x : adjointGroup ReeTag.F4.tag K),
        ψ * MulAut.conj x = MulAut.conj (ψ x) * ψ := fun ψ x => by
      ext y
      simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
    have hα2 : α ^ 2 = MulAut.conj (g * φ g) := by
      rw [hgk, pow_two, mul_assoc, ← mul_assoc φ, hconj, mul_assoc, hφsq, mul_one, ← map_mul]
    have hfix2 : ∀ y ∈ Subgroup.centralizer {t}, (α ^ 2) y = y := fun y hy => by
      rw [pow_two, MulAut.mul_apply, hfix y hy, hfix y hy]
    have hh3 : (g * φ g) ^ 3 = 1 := hAc _ fun a ha => by
      have h1 := hfix2 a (hAt ha)
      rw [hα2, MulAut.conj_apply] at h1
      calc g * φ g * a = g * φ g * a * (g * φ g)⁻¹ * (g * φ g) := by group
        _ = a * (g * φ g) := by rw [h1]
    set β := α ^ 3 with hβ
    have hβ2 : β ^ 2 = 1 := by
      rw [hβ, ← pow_mul, show 3 * 2 = 2 * 3 by norm_num, pow_mul, hα2, ← map_pow, hh3, map_one]
    have hβfix : ∀ y ∈ Subgroup.centralizer {t}, β y = y := fun y hy => by
      rw [hβ, pow_succ, MulAut.mul_apply, hfix y hy, hfix2 y hy]
    have hΘα : Θ α = Multiplicative.ofAdd (1 : ZMod (2 * 1)) := by
      have := hΘ α g 1 (by rw [pow_one]; exact hgk)
      simpa using this
    have hβo : β ∉ (MulAut.conj : adjointGroup ReeTag.F4.tag K →*
        MulAut (adjointGroup ReeTag.F4.tag K)).range := by
      intro hmem
      rw [← hker] at hmem
      have h1 : Θ β = 1 := hmem
      rw [hβ, map_pow, hΘα] at h1
      revert h1
      decide
    obtain ⟨ψ, hψ, -⟩ := even_F4_all_outer_involutions_canonical (f := 1) le_rfl K hK1 β hβ2 hβo
    obtain ⟨-, -, hFIX⟩ := hodd 0 rfl
    have hle : A.map ψ.toMonoidHom ≤ ReeTag.F4.finiteReeFixedGroup K 0 := by
      rintro _ ⟨a, ha, rfl⟩
      refine (hFIX _).2 ?_
      have hβa : β a = a := hβfix a (hAt ha)
      rw [← hψ]
      change ψ (β (ψ⁻¹ (ψ a))) = ψ a
      rw [MulAut.inv_apply_self, hβa]
    have hcard : Nat.card (A.map ψ.toMonoidHom) = 81 := by
      rw [Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, hAcard]
    have hdvd := Subgroup.card_dvd_of_le hle
    have hR : Nat.card (ReeTag.F4.finiteReeFixedGroup K 0) =
        Nat.card (ReeTag.F4.reeGamma K 0) :=
      (Subgroup.card_map_of_injective (adjointGroup ReeTag.F4.tag K).subtype_injective).symm
    have hK' : Nat.card K = 2 ^ (2 * 0 + 1) := by rw [hK]; norm_num
    have hord := (large_Ree_exact_native_order_and_prime_factor_exhaustion 0 K hK').1
    rw [hcard, hR, hord] at hdvd
    norm_num at hdvd

theorem mem_innerAut_of_fix_F4_two (hK : Nat.card K = 2) {t : adjointGroup Tag.F4 K}
    {A : Subgroup (adjointGroup Tag.F4 K)} (hAt : A ≤ Subgroup.centralizer {t})
    (hAcard : Nat.card A = 81)
    (hAc : ∀ y : adjointGroup Tag.F4 K, (∀ a ∈ A, y * a = a * y) → y ^ 3 = 1)
    (α : MulAut (adjointGroup Tag.F4 K)) (hfix : ∀ y ∈ Subgroup.centralizer {t}, α y = y) :
    α ∈ innerAut (adjointGroup Tag.F4 K) :=
  mem_innerAut_of_fix_reeF4_two hK hAt hAcard hAc α hfix

end Rigid

section Consumer


theorem innerOneBalanceThree_F4_two (hK : Nat.card K = 2) :
    InnerOneBalanceThree (adjointGroup Tag.F4 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_two_of_card_two hK
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨Fr, hFr, g0, hg0C, hg0⟩ := exists_lang_data Tag.F4 K CrossChar.f4Neg
  have hFr2 : Fr = iterateFrobenius (AlgebraicClosure K) 2 1 :=
    RingHom.ext fun c => by rw [hFr, hK, iterateFrobenius_two_one]
  subst hFr2
  set W := twModel (canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) CrossChar.f4Neg)
    (iterateFrobenius (AlgebraicClosure K) 2 1) with hW
  have : Finite W := finite_twModel hg0C hg0
  set e := twModelEquivF4 K (AlgebraicClosure K) hFr hg0C hg0 with he
  have htorL : ∀ a : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ,
      rootDiagUnit Tag.F4 a ∈ torusGroup Tag.F4 (AlgebraicClosure K) :=
    rootDiagUnit_mem_torusGroup_of_unimodular CrossChar.exists_mul_cartan_F4.choose_spec
  obtain ⟨ω, hω, -⟩ := exists_orderOf_eq_of_dvd_add_one K (L := AlgebraicClosure K) (N := 3)
    (by rw [hK])
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hG : ∀ x, dV (τ := Tag.F4) ω x ∈ W := dV_mem_twModel htorL CrossChar.f4Neg_smul hω3
  have hLang : ∀ a : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ, (∀ i, a i ^ 3 = 1) →
      ∀ c ∈ toralCentralizer Tag.F4 (AlgebraicClosure K) a,
        ∃ z ∈ toralCentralizer Tag.F4 (AlgebraicClosure K) a, z⁻¹ * frobTwistGL Tag.F4
          (AlgebraicClosure K) 2 1 (canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K)
            CrossChar.f4Neg) z = c := fun a ha3 c hc =>
    toral_centralizer_Lang_F4_three 2 (AlgebraicClosure K) (by norm_num) a ha3 1 le_rfl
      (canonicalRep_mem_adjointGroup _ _ _) (s := 2) (by norm_num)
      (canonicalRep_conj_rootDiagUnit_sq CrossChar.f4Neg_smul ha3) c hc
  have hfus : ∀ s ∈ W, s ^ 3 = 1 → ∃ u ∈ W, ∃ x : Fin Tag.F4.rank → ZMod 3,
      u * s * u⁻¹ = dV ω x := fun s hs hs3 =>
    exists_conj_dV_twModel (isAlgebraic_zmod_algebraicClosure_of_finite K 2)
      (monomialToralAt_three_of_block a2BlockToral_F4) CrossChar.f4Neg_smul hLang hω hs hs3
  have hcert : Native.hypOK Tag.F4 = true := Certificates.certificate13666.1
  refine innerOneBalanceThree_of_model mulAut_conj_injective_adjointGroup e le_rfl
    (fun u hu m hm => mul_mem (mul_mem hu hm) (inv_mem hu)) hG hfus
    (fun x hx => gLAPPrimeCoreOf_centralizer_dV_two htorL CrossChar.f4Neg_smul le_rfl
      (fun g hg _ => hg) hω hG hcert hx) ?_
  intro t ht3 ht1 α hα
  have hs3 : ((e t : W) : ModGL Tag.F4 (AlgebraicClosure K)) ^ 3 = 1 := by
    have h1 : (e t) ^ 3 = 1 := by rw [← map_pow, ht3, map_one]
    have := congrArg (fun m : W => (m : ModGL Tag.F4 (AlgebraicClosure K))) h1
    simpa using this
  obtain ⟨u, huW, x, hux⟩ := hfus _ (e t).2 hs3
  set uW : W := ⟨u, huW⟩ with huW'
  set φt : W ≃* adjointGroup Tag.F4 K := (MulAut.conj uW⁻¹).trans e.symm with hφt
  have hφt_symm : ∀ y, ((φt.symm y : W) : ModGL Tag.F4 (AlgebraicClosure K)) =
      u * (e y : ModGL Tag.F4 (AlgebraicClosure K)) * u⁻¹ := fun y => by
    simp [hφt, huW']
  have htx : φt.symm t = dG hG x := Subtype.ext ((hφt_symm t).trans hux)
  set AW : Subgroup W := (dGHom hω3 hG).range with hAW
  have hAWcomm : ∀ a ∈ AW, ∀ b ∈ AW, a * b = b * a := by
    rintro _ ⟨y, rfl⟩ _ ⟨z, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  have hxAW : dG hG x ∈ AW := ⟨Multiplicative.ofAdd x, dGHom_ofAdd hω3 hG x⟩
  refine mem_innerAut_of_fix_F4_two hK (A := AW.map φt.toMonoidHom) ?_ ?_ ?_ α hα
  · rintro _ ⟨d, hd, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply φt.symm.injective
    rw [map_mul, map_mul, htx]
    change φt.symm (φt d) * dG hG x = dG hG x * φt.symm (φt d)
    rw [MulEquiv.symm_apply_apply]
    exact hAWcomm d hd _ hxAW
  · have hinj : Function.Injective (dGHom hω3 hG) := by
      intro a b hab
      have h1 := congrArg Subtype.val hab
      rw [← ofAdd_toAdd a, ← ofAdd_toAdd b, dGHom_ofAdd, dGHom_ofAdd] at h1
      have h2 := dV_injective (τ := Tag.F4) hω h1
      rw [← ofAdd_toAdd a, ← ofAdd_toAdd b, h2]
    have h1 : Nat.card AW = 81 := by
      rw [hAW, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top,
        Nat.card_eq_fintype_card]
      simp [Fintype.card_multiplicative, Fintype.card_pi, ZMod.card]
      rfl
    change Nat.card (AW.map φt.toMonoidHom) = 81
    rw [Subgroup.card_map_of_injective φt.injective, h1]
  · intro y hy
    set y' := φt.symm y with hy'
    have hcomm : ∀ z : Fin Tag.F4.rank → ZMod 3,
        Commute (dV ω z) (y' : ModGL Tag.F4 (AlgebraicClosure K)) := by
      intro z
      have hz : φt (dG hG z) ∈ AW.map φt.toMonoidHom :=
        ⟨dG hG z, ⟨Multiplicative.ofAdd z, dGHom_ofAdd hω3 hG z⟩, rfl⟩
      have h1 := hy _ hz
      have h2 := congrArg φt.symm h1
      rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at h2
      have h3 := congrArg Subtype.val h2
      exact (h3.symm : (dV ω z) * y' = y' * dV ω z)
    have hy'T := mem_torusGroup_of_commute_dV hω hcert (y'.2.1) hcomm
    have hy'3 := pow_three_of_mem_twModel htorL CrossChar.f4Neg_smul y'.2 hy'T
    have h4 : y' ^ 3 = 1 := Subtype.ext (by simpa using hy'3)
    have h5 : y = φt y' := by rw [hy', MulEquiv.apply_symm_apply]
    rw [h5, ← map_pow, h4, map_one]

end Consumer

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

end

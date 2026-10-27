module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoDefs
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Cont
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoKill
import CFSG.LieType.SeitzGeneration.ExcHighThree.TwConjExp
import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6O2Regular
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LieType.SeitzGeneration.ExcHighThree

set_option linter.unusedSectionVars false


@[expose] def TwE6RegularLangNeg : Prop :=
  ∀ (q : ℕ) (K : Type) [Field K] [Finite K] (σ : K ≃+* K),
    Nat.card K = q ^ 2 → (∀ c : K, σ c = c ^ q) → ringChar K ≠ 3 → q % 3 = 2 →
    ∀ E₀ : Subgroup (twistedE6RootGroup K σ), IsElemAbelian 3 E₀ → Nat.card E₀ = 3 ^ 3 →
    ∀ (Fr : AlgebraicClosure K →+* AlgebraicClosure K), (∀ c, Fr c = c ^ q) →
    ∀ (v : WeylGroup TwistTag.E6.tag) (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)),
      g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) →
      twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v →
      (∀ x ∈ E₀,
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) ∈
          (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
            (twistHom TwistTag.E6 (AlgebraicClosure K) Fr)).map (MulAut.conj g0).toMonoidHom) →
      (∀ α : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag α → ¬ TwKills K σ E₀ g0 α) →
      ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, v • permLattice TwistTag.E6.perm γ = -γ

theorem twE6ToralNegTwo_of_regularLangNeg (hO2 : TwE6RegularLangNeg) : TwE6ToralNegTwo := by
  intro K _ _ σ q hK hσ hq E₀ hE₀ hcard hNR hbar
  obtain ⟨g, hgC, hgT⟩ := hbar
  obtain ⟨hp, f, hf, hqf⟩ := exists_pow_ringChar_of_card_sq K q hK (by omega)
  have hℓ3 : ringChar K ≠ 3 := by
    intro h
    rw [h] at hqf
    have h3 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
    omega
  haveI : Fact (ringChar K).Prime := ⟨hp⟩
  haveI : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  have hFr : ∀ c, iterateFrobenius (AlgebraicClosure K) (ringChar K) f c = c ^ q := fun c => by
    rw [iterateFrobenius_def, hqf]
  obtain ⟨v, g0, hg0C, hg0, hT⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_lang_torus_of_conj_torus_twisted
      (ringChar K) TwistTag.E6 f hf (A := twBase K σ E₀)
      (fun y hy => by
        obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.1 hy
        exact twBase_twistHom_fix K σ q
          (iterateFrobenius (AlgebraicClosure K) (ringChar K) f) hσ hFr x.1 x.2)
      hgC (fun y hy => by
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
        exact hgT x hx)
  have hT' : ∀ x ∈ E₀,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) ∈
        (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
          (twistHom TwistTag.E6 (AlgebraicClosure K)
            (iterateFrobenius (AlgebraicClosure K) (ringChar K) f))).map
          (MulAut.conj g0).toMonoidHom :=
    fun x hx => hT _ (Subgroup.mem_map_of_mem _ hx)
  have hreg : ∀ α : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag α →
      ¬ TwKills K σ E₀ g0 α := fun α hα hk =>
    hNR (normalizesRGroup_of_twKills q K σ hK hσ hℓ3 E₀ _ hFr v g0 hg0C hg0 hT' hα hk)
  have hv := hO2 q K σ hK hσ hℓ3 hq E₀ hE₀ hcard _ hFr v g0 hg0C hg0 hT' hreg
  refine ⟨_, hFr, v, hv, g0, hg0C, hg0, fun x hx => ?_⟩
  obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.1 (hT' x hx)
  have htg : t = g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (x : ModGL TwistTag.E6.tag K) * g0 := by
    rw [← hte]
    simp [MulAut.conj_apply, mul_assoc]
  rw [← htg]
  exact (mem_twistedTorusOf.1 ht).1

section Lift

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3 (e6RhoFour e6RhoFour_eq_twistPerm)

private theorem toralNeg_class_dvd {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (hq : (p ^ f) % 3 = 2) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ (p ^ f)) (v : WeylGroup Tag.E6) (g0 : ModGL Tag.E6 (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) v)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : IsPrimitiveRoot ζ 9) (m : Fin Tag.E6.rank → ℤ)
    {y : ModGL Tag.E6 K} (hy : y ∈ twistedE6RootGroup K σ)
    (hyu : baseChangeGL (algebraMap K (AlgebraicClosure K)) y =
      g0 * rootDiagUnit Tag.E6 (e6RootParams (fun l => ζ ^ m l)) * g0⁻¹)
    (l : Fin Tag.E6.rank) :
    (9 : ℤ) ∣ ((p ^ f : ℕ) : ℤ) * (v • permLattice CFSG.RankThree.E6.e6Rho m) l - m l := by
  obtain ⟨ωv, hωv, hvw⟩ := (coxeterSystem Tag.E6).exists_isReduced v
  have hF' : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K)
        ((coxeterSystem Tag.E6).wordProd ωv) := by
    rw [← hvw]
    exact hg0
  have key := tw_class_trivial_of_mem hp hf hK σ hσ hq Fr hFr g0 hg0C hωv hF'
    (fun l => ζ ^ m l) hy hyu
  have hFrζ : Units.map Fr.toMonoidHom ζ = ζ ^ (p ^ f) :=
    Units.ext (by rw [Units.coe_map, Units.val_pow_eq_pow_val]; exact hFr _)
  have hρ : e6RhoFour = CFSG.RankThree.E6.e6Rho := e6RhoFour_eq_twistPerm
  have hinner : (fun l => Units.map Fr.toMonoidHom ((fun l => ζ ^ m l) (e6RhoFour l))) =
      fun l => ζ ^ ((((p ^ f : ℕ) : ℤ) • permLattice CFSG.RankThree.E6.e6Rho m) l) := by
    funext l
    show Units.map Fr.toMonoidHom (ζ ^ m (e6RhoFour l)) = _
    rw [map_zpow, hFrζ, ← zpow_natCast, ← zpow_mul]
    congr 1
    simp only [Pi.smul_apply, smul_eq_mul, permLattice, Function.comp_apply,
      CFSG.RankThree.E6.e6Rho_symm, hρ]
  have key2 : ωv.foldr e6StarS
      (fun l => ζ ^ ((((p ^ f : ℕ) : ℤ) • permLattice CFSG.RankThree.E6.e6Rho m) l)) =
      fun l => ζ ^ m l :=
    (congrArg (ωv.foldr e6StarS) hinner.symm).trans key
  have key3 : (fun l => ζ ^ (((coxeterSystem Tag.E6).wordProd ωv •
      (((p ^ f : ℕ) : ℤ) • permLattice CFSG.RankThree.E6.e6Rho m)) l)) =
      fun l => ζ ^ m l := by
    rw [wordProd_smul_eq_foldr]
    exact (foldr_e6StarS_zpow ζ ωv _).symm.trans key2
  rw [← hvw, smul_comm v (((p ^ f : ℕ) : ℤ))] at key3
  have h1 : ζ ^ ((((p ^ f : ℕ) : ℤ) • (v • permLattice CFSG.RankThree.E6.e6Rho m)) l) =
      ζ ^ m l := congrFun key3 l
  have h2 : ζ ^ ((((p ^ f : ℕ) : ℤ) • (v • permLattice CFSG.RankThree.E6.e6Rho m)) l - m l) =
      1 := by
    rw [zpow_sub, h1, mul_inv_cancel]
  have h3 := (hζ.zpow_eq_one_iff_dvd _).1 h2
  rw [Pi.smul_apply, smul_eq_mul] at h3
  exact_mod_cast h3

private theorem toralNeg_exponent_congr {q : ℕ} {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hK : Nat.card K = q ^ 2) (hσ : ∀ c : K, σ c = c ^ q) (hq : q % 3 = 2)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ q)
    {v : WeylGroup TwistTag.E6.tag} {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : IsPrimitiveRoot ζ 9)
    (x : twistedE6RootGroup K σ) (hx3 : x ^ 3 = 1)
    (hxT : baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) ∈
      (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
        (twistHom TwistTag.E6 (AlgebraicClosure K) Fr)).map (MulAut.conj g0).toMonoidHom) :
    ∃ (k : Fin Tag.E6.rank → ℕ) (m : Fin Tag.E6.rank → ℤ),
      rootDiagUnit TwistTag.E6.tag (fun i => (ζ ^ 3) ^ k i) =
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (x : ModGL TwistTag.E6.tag K) * g0 ∧
      (∀ j, ∑ l, Tag.E6.cartan l j * m l = 3 * (k j : ℤ)) ∧
      ∀ l, (9 : ℤ) ∣ (q : ℤ) * (v • permLattice TwistTag.E6.perm m) l - m l := by
  classical
  obtain ⟨hpr, f, hf1, hqf⟩ := exists_pow_ringChar_of_card_sq K q hK (by omega)
  have hK' : Nat.card K = (ringChar K ^ f) ^ 2 := by rw [hK, hqf]
  have hσ' : ∀ c, σ c = c ^ (ringChar K ^ f) := fun c => by rw [hσ c, hqf]
  have hFrc : ∀ c, Fr c = c ^ (ringChar K ^ f) := fun c => by rw [hFr, hqf]
  have hq' : (ringChar K ^ f) % 3 = 2 := by rw [← hqf]; exact hq
  have hω' : IsPrimitiveRoot (ζ ^ 3) 3 := hζ.pow (by norm_num) (by norm_num)
  have hω : IsPrimitiveRoot ((ζ ^ 3 : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) 3 :=
    IsPrimitiveRoot.coe_units_iff.2 hω'
  obtain ⟨k, hk, -⟩ := tw_diag_exponent hω Fr _ g0 x hx3 hxT
  obtain ⟨m, hm⟩ : ∃ m : Fin Tag.E6.rank → ℤ,
      m = fun l => ∑ i, e6CartanAdj i l * (k i : ℤ) := ⟨_, rfl⟩
  have hmc : ∀ j : Fin Tag.E6.rank, ∑ l : Fin Tag.E6.rank, Tag.E6.cartan l j * m l =
      3 * (k j : ℤ) := by
    intro j
    have e : ∀ i, ∑ l, Tag.E6.cartan l j * (e6CartanAdj i l * (k i : ℤ)) =
        (k i : ℤ) * (if i = j then 3 else 0) := by
      intro i
      rw [← e6CartanAdj_mul i j, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [hm]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [e, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have hpar : e6RootParams (fun l => ζ ^ m l) = fun i => (ζ ^ 3) ^ k i := by
    refine (tw_e6RootParams_zpow ζ m).trans ?_
    funext j
    show ζ ^ _ = (ζ ^ 3) ^ k j
    rw [hmc j, ← pow_mul, ← zpow_natCast, Nat.cast_mul, Nat.cast_ofNat]
  have hyu : baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) =
      g0 * rootDiagUnit TwistTag.E6.tag (e6RootParams (fun l => ζ ^ m l)) * g0⁻¹ := by
    rw [hpar, hk]
    group
  refine ⟨k, m, hk, hmc, fun l => ?_⟩
  have h := toralNeg_class_dvd hpr hf1 hK' σ hσ' hq' Fr hFrc v g0 hg0C hg0 hζ m x.2 hyu l
  rw [← hqf] at h
  exact h

private theorem toralNeg_mul_w0_smul (v : WeylGroup Tag.E6) (z : Fin Tag.E6.rank → ℤ) :
    (v * CFSG.HardMathSupport.Lang.E6Descent.twE6W0) • z =
      -(v • permLattice CFSG.RankThree.E6.e6Rho z) := by
  rw [mul_smul, CFSG.HardMathSupport.Lang.E6Descent.twE6W0_smul, smul_neg]

private theorem toralNeg_neg_of_mul_w0_eq_one {v : WeylGroup Tag.E6}
    (h : v * CFSG.HardMathSupport.Lang.E6Descent.twE6W0 = 1) (γ : Fin Tag.E6.rank → ℤ) :
    v • permLattice CFSG.RankThree.E6.e6Rho γ = -γ := by
  have h1 := toralNeg_mul_w0_smul v γ
  rw [h, one_smul] at h1
  exact neg_eq_iff_eq_neg.1 h1.symm

end Lift

section Cert

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


private theorem toralNeg_core {q : ℕ} (hq : q % 3 = 2) (v : WeylGroup Tag.E6) {ι : Type}
    [Fintype ι] (k : ι → Fin Tag.E6.rank → ℕ) (m : ι → Fin Tag.E6.rank → ℤ)
    (hm : ∀ x j, ∑ l, Tag.E6.cartan l j * m x l = 3 * (k x j : ℤ))
    (hcl : ∀ x l, (9 : ℤ) ∣
      (q : ℤ) * (v • permLattice CFSG.RankThree.E6.e6Rho (m x)) l - m x l)
    (hinj : Function.Injective fun x i => (((k x i : ℕ) : ℤ) : ZMod 3))
    (hcard : 27 ≤ Fintype.card ι)
    (hreg : ∀ a : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 a →
      ∃ x, ¬ (3 : ℤ) ∣ ∑ i, (k x i : ℤ) * a i)
    (γ : Fin Tag.E6.rank → ℤ) :
    v • permLattice CFSG.RankThree.E6.e6Rho γ = -γ := by
  classical
  by_cases hw1 : v * CFSG.HardMathSupport.Lang.E6Descent.twE6W0 = 1
  · exact toralNeg_neg_of_mul_w0_eq_one hw1 γ
  exfalso
  set w := v * CFSG.HardMathSupport.Lang.E6Descent.twE6W0 with hwdef
  set b : ι → Fin Tag.E6.rank → ZMod 3 := fun x i => (((k x i : ℕ) : ℤ) : ZMod 3) with hb
  have hV : 27 ≤ (Finset.univ.image b).card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
    exact hcard
  have hVc : ∀ c ∈ Finset.univ.image b, w ∈ charStabilizer (triChar c) ∧
      triPairing c (e6Shift w) = -(((q + 1) / 3 : ℕ) : ZMod 3) * triPairing c e6Omega3 := by
    intro c hc
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hc
    refine e6O2_fix_shift_of_congr hq w (fun i => (k x i : ℤ)) (m x) (hm x) fun l => ?_
    have h1 := hcl x l
    rw [hwdef, toralNeg_mul_w0_smul, Pi.neg_apply]
    have e : (q : ℤ) * -(v • permLattice CFSG.RankThree.E6.e6Rho (m x)) l + m x l =
        -((q : ℤ) * (v • permLattice CFSG.RankThree.E6.e6Rho (m x)) l - m x l) := by ring
    rw [e]
    exact (dvd_neg).2 h1
  obtain ⟨a, ha, hka⟩ := e6O2Regular_holds w hw1 _ _ hV hVc
  obtain ⟨x, hx⟩ := hreg a ha
  apply hx
  have h0 := hka (b x) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  have h1 : (((∑ i, (k x i : ℤ) * a i : ℤ)) : ZMod 3) = 0 := by
    rw [← h0, hb]
    simp only [triPairing, Int.cast_sum, Int.cast_mul]
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 h1

theorem twE6RegularLangNeg_of_cert : TwE6RegularLangNeg := by
  intro q K _ _ σ hK hσ hℓ3 hq E₀ hE₀ hcard Fr hFr v g0 hg0C hg0 hT hreg γ
  classical
  obtain ⟨hp, f, hf, hqf⟩ := exists_pow_ringChar_of_card_sq K q hK (by omega)
  haveI : Fact (ringChar K).Prime := ⟨hp⟩
  haveI : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  have h9 : ((9 : ℕ) : AlgebraicClosure K) ≠ 0 := by
    intro h
    have hd : ringChar K ∣ 9 := (CharP.cast_eq_zero_iff (AlgebraicClosure K) (ringChar K) 9).1 h
    have h3 : ringChar K ∣ 3 := hp.dvd_of_dvd_pow (n := 2) (by norm_num; exact hd)
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3)
  haveI : NeZero ((9 : ℕ) : AlgebraicClosure K) := ⟨h9⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) 9
  have hu : IsUnit ζ₀ := hζ₀.isUnit (by norm_num)
  have hζ : IsPrimitiveRoot hu.unit 9 :=
    IsPrimitiveRoot.coe_units_iff.1 (by rwa [IsUnit.unit_spec])
  set ζ := hu.unit with hζdef
  have hω3 : (ζ ^ 3) ^ 3 = 1 := by
    rw [← pow_mul]
    exact hζ.pow_eq_one
  choose k m hk hm hcl using fun x : E₀ => toralNeg_exponent_congr hK hσ hq hFr hg0C hg0 hζ
    (x : twistedE6RootGroup K σ) (hE₀.2 x x.2) (hT x x.2)
  haveI : Finite E₀ := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Fintype E₀ := Fintype.ofFinite E₀
  have hωpow : ∀ a : ℕ, (ζ ^ 3) ^ a = (ζ ^ 3) ^ (a % 3) := fun a => by
    conv_lhs => rw [← Nat.div_add_mod a 3, pow_add, pow_mul, hω3, one_pow, one_mul]
  have hinj : Function.Injective
      fun (x : E₀) (i : Fin Tag.E6.rank) => (((k x i : ℕ) : ℤ) : ZMod 3) := by
    intro x y hxy
    have hkk : (fun i => (ζ ^ 3) ^ k x i) = fun i => (ζ ^ 3) ^ k y i := by
      funext i
      have h1 := congrFun hxy i
      simp only [Int.cast_natCast] at h1
      rw [hωpow (k x i), hωpow (k y i), (ZMod.natCast_eq_natCast_iff' _ _ 3).1 h1]
    have h2 := (hk x).symm.trans ((congrArg (rootDiagUnit TwistTag.E6.tag) hkk).trans (hk y))
    have h3 := mul_left_cancel (mul_right_cancel h2)
    exact Subtype.ext (Subtype.ext
      (baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) h3))
  have hc27 : 27 ≤ Fintype.card E₀ := by
    rw [← Nat.card_eq_fintype_card, hcard]
    norm_num
  have hreg' : ∀ a : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 a →
      ∃ x : E₀, ¬ (3 : ℤ) ∣ ∑ i, (k x i : ℤ) * a i := by
    intro a ha
    by_contra hall
    push_neg at hall
    refine hreg a ha fun x hx => ⟨_, hk ⟨x, hx⟩, ?_⟩
    refine (tw_rootChar_pow_exp (ζ ^ 3) (k ⟨x, hx⟩) a).trans ?_
    obtain ⟨c, hc⟩ := hall ⟨x, hx⟩
    have h3 : (ζ ^ 3) ^ (3 : ℤ) = 1 := by
      rw [zpow_ofNat]
      exact hω3
    rw [hc, zpow_mul, h3, one_zpow]
  exact toralNeg_core hq v k m hm hcl hinj hc27 hreg' γ

end Cert

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

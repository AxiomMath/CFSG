module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Cont
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Normalizer
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwConj
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoModel
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwConjLift
public import CFSG.LieType.SeitzGeneration.ExcWideThree.ConjFin
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Lang.E6Descent CFSG.LieType.SeitzGeneration.ExcWideThree
open CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag (delta twE6W0_inv w0_mul_delta_mul_w0_inv)
open CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3 (e6RhoFour e6RhoFour_eq_twistPerm)
open scoped Matrix

set_option linter.unusedSectionVars false

section Exp


@[expose] def dlt : WeylGroup Tag.E6 ≃* WeylGroup Tag.E6 := weylTwist TwistTag.E6

theorem tw_dlt_eq_conj_w0 (x : WeylGroup Tag.E6) : dlt x = twE6W0 * x * twE6W0⁻¹ := by
  have h : twE6W0 * dlt x * twE6W0⁻¹ = x := w0_mul_delta_mul_w0_inv x
  calc dlt x = twE6W0⁻¹ * (twE6W0 * dlt x * twE6W0⁻¹) * twE6W0 := by group
    _ = twE6W0⁻¹ * x * twE6W0 := by rw [h]
    _ = twE6W0 * x * twE6W0⁻¹ := by rw [twE6W0_inv]

theorem tw_dlt_w0 : dlt twE6W0 = twE6W0 := by
  rw [tw_dlt_eq_conj_w0]
  group

theorem tw_inner_hw (v V : WeylGroup Tag.E6)
    (h : dlt (V * (twE6W0 * v⁻¹) * V⁻¹) = V * (twE6W0 * v⁻¹) * V⁻¹) :
    dlt (V * v * (dlt V)⁻¹) = V * v * (dlt V)⁻¹ := by
  have hW0 : twE6W0⁻¹ = twE6W0 := twE6W0_inv
  set y : WeylGroup Tag.E6 := V * v * twE6W0 * V⁻¹ with hy
  have hyy : dlt y = y := by
    have h1 : y = (V * (twE6W0 * v⁻¹) * V⁻¹)⁻¹ := by
      calc y = V * v * twE6W0⁻¹ * V⁻¹ := by rw [hW0]
        _ = (V * (twE6W0 * v⁻¹) * V⁻¹)⁻¹ := by group
    rw [h1, map_inv, h]
  have e1 : V * v * (dlt V)⁻¹ = y * twE6W0⁻¹ := by
    rw [tw_dlt_eq_conj_w0 V, hy]
    group
  rw [e1, map_mul, map_inv, hyy, tw_dlt_w0]

theorem tw_inv_smul_mod3 (g : WeylGroup Tag.E6) (m : Fin Tag.E6.rank → ℤ)
    (h : ∀ i, (3 : ℤ) ∣ (g • m) i - m i) : ∀ i, (3 : ℤ) ∣ (g⁻¹ • m) i - m i := by
  choose y hy using h
  have h1 : g • m - m = (3 : ℤ) • y := by
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith [hy i]
  have h2 : g⁻¹ • m - m = -((3 : ℤ) • (g⁻¹ • y)) := by
    have h3 : g⁻¹ • (g • m - m) = m - g⁻¹ • m := by
      rw [smul_sub, inv_smul_smul]
    have h4 : g⁻¹ • ((3 : ℤ) • y) = (3 : ℤ) • (g⁻¹ • y) := smul_comm _ _ _
    rw [h1, h4] at h3
    rw [h3]
    abel
  intro i
  have := congrFun h2 i
  simp only [Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at this
  exact ⟨-(g⁻¹ • y) i, by linarith⟩

theorem tw_rootChar_pow_exp {L : Type} [Field L] (ω : Lˣ) (k : Fin Tag.E6.rank → ℕ)
    (v : Fin Tag.E6.rank → ℤ) :
    rootChar (fun i => ω ^ k i) v = ω ^ (∑ i, (k i : ℤ) * v i) := by
  unfold rootChar
  rw [← liftProd_zpow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  show (ω ^ k i) ^ v i = _
  rw [← zpow_natCast, ← zpow_mul]

theorem tw_torus_exp_fix {L : Type} [Field L] {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (hq : q % 3 = 2) {ω : Lˣ} (hω : IsPrimitiveRoot (ω : L) 3) (v : WeylGroup Tag.E6)
    (k : Fin Tag.E6.rank → ℕ)
    (h : twistHom TwistTag.E6 L Fr (rootDiagUnit Tag.E6 (fun i => ω ^ k i)) =
      (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ * rootDiagUnit Tag.E6 (fun i => ω ^ k i) *
        canonicalRep (coxeterSystem Tag.E6) L v) :
    ∀ t : Fin Tag.E6.rank, (3 : ℤ) ∣
      (∑ i, (k i : ℤ) * ((twE6W0 * v⁻¹) • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)) i) - (k t : ℤ) := by
  intro t
  have hωu : IsPrimitiveRoot ω 3 := IsPrimitiveRoot.coe_units_iff.1 hω
  have h1 : twistHom TwistTag.E6 L Fr (rootDiagUnit Tag.E6 (fun i => ω ^ k i)) =
      rootDiagUnit Tag.E6
        (fun i => Units.map Fr.toMonoidHom ((fun i => ω ^ k i) (CFSG.RankThree.E6.e6Rho.symm i))) :=
    twistHom_rootDiagUnit_eq (t := TwistTag.E6) (σ := Fr) _
  have h3 : rootDiagUnit Tag.E6 (fun i => ω ^ k i) =
      canonicalRep (coxeterSystem Tag.E6) L v * rootDiagUnit Tag.E6
        (fun i => Units.map Fr.toMonoidHom ((fun i => ω ^ k i) (CFSG.RankThree.E6.e6Rho.symm i))) *
        (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ := by
    rw [h1.symm.trans h]
    group
  rw [canonicalRep_conj_rootDiagUnit] at h3
  have h2 := (congrFun (CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective h3) t).symm
  simp only [weylTuple] at h2
  set m : Fin Tag.E6.rank → ℤ := v⁻¹ • (Pi.single t 1 : Fin Tag.E6.rank → ℤ) with hm
  clear_value m
  obtain ⟨S, hS⟩ : ∃ S : ℤ, S = ∑ i, (k i : ℤ) * (twE6W0 • m) i := ⟨_, rfl⟩
  have e1 := rootChar_units_map_pow (τ := Tag.E6) (L := L) hFr
    (fun j => ω ^ k (CFSG.RankThree.E6.e6Rho.symm j)) m
  have e2 := tw_rootChar_pow_exp ω (fun j => k (CFSG.RankThree.E6.e6Rho.symm j)) ((q : ℤ) • m)
  have h3' : ω ^ (∑ j, (k (CFSG.RankThree.E6.e6Rho.symm j) : ℤ) * (((q : ℤ) • m) j)) =
      ω ^ k t :=
    e2.symm.trans (e1.symm.trans h2)
  have hW : ∀ m' : Fin Tag.E6.rank → ℤ,
      permLattice CFSG.RankThree.E6.e6Rho.symm m' = -(twE6W0 • m') :=
    fun m' => by
      rw [twE6W0_smul, neg_neg, CFSG.RankThree.E6.e6Rho_symm]
  have hsum : ∑ j, (k (CFSG.RankThree.E6.e6Rho.symm j) : ℤ) * (((q : ℤ) • m) j) =
      (q : ℤ) * (-S) := by
    have e3 : ∑ j, (k (CFSG.RankThree.E6.e6Rho.symm j) : ℤ) * (((q : ℤ) • m) j) =
        (q : ℤ) * ∑ i, (k i : ℤ) * (permLattice CFSG.RankThree.E6.e6Rho.symm m) i := by
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv CFSG.RankThree.E6.e6Rho.symm _ _ (fun j => ?_)
      simp only [permLattice, Function.comp_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
        Pi.smul_apply, smul_eq_mul]
      ring
    rw [e3, hW m]
    simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, ← hS]
  rw [hsum] at h3'
  have h4 : ω ^ ((q : ℤ) * (-S) - (k t : ℤ)) = 1 := by
    rw [zpow_sub, h3', ← zpow_natCast, mul_inv_cancel]
  have h5 := (hωu.zpow_eq_one_iff_dvd _).1 h4
  obtain ⟨a, ha⟩ : ∃ a : ℕ, q = 3 * a + 2 := ⟨q / 3, by omega⟩
  rw [ha] at h5
  push_cast at h5
  rw [hm] at hS
  rw [mul_smul, ← hS]
  have e4 : S - (k t : ℤ) = ((3 * (a : ℤ) + 2) * (-S) - (k t : ℤ)) + 3 * (((a : ℤ) + 1) * S) := by
    ring
  rw [e4]
  exact dvd_add h5 (dvd_mul_right _ _)

theorem tw_diag_exponent {K : Type} [Field K] {σ : K ≃+* K} {ω : (AlgebraicClosure K)ˣ}
    (hω : IsPrimitiveRoot (ω : AlgebraicClosure K) 3)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (n g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)) (x : twistedE6RootGroup K σ)
    (hx3 : x ^ 3 = 1)
    (hmem : baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) ∈
      (twistedTorusOf n (twistHom TwistTag.E6 (AlgebraicClosure K) Fr)).map
        (MulAut.conj g0).toMonoidHom) :
    ∃ k : Fin TwistTag.E6.tag.rank → ℕ,
      rootDiagUnit TwistTag.E6.tag (fun i => ω ^ k i) =
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
          g0 ∧
      n * twistHom TwistTag.E6 (AlgebraicClosure K) Fr
          (rootDiagUnit TwistTag.E6.tag (fun i => ω ^ k i)) * n⁻¹ =
        rootDiagUnit TwistTag.E6.tag (fun i => ω ^ k i) := by
  obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.1 hmem
  obtain ⟨htor, hfix⟩ := mem_twistedTorusOf.1 ht
  have htg : t = g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (x : ModGL TwistTag.E6.tag K) * g0 := by
    rw [← hte]
    simp [MulAut.conj_apply, mul_assoc]
  obtain ⟨a, rfl⟩ := torusGroup_le_range_rootDiagUnitHom htor
  have ht3 : (rootDiagUnitHom TwistTag.E6.tag (AlgebraicClosure K) a) ^ 3 = 1 := by
    have h1 : (MulAut.conj g0).toMonoidHom
        ((rootDiagUnitHom TwistTag.E6.tag (AlgebraicClosure K) a) ^ 3) = 1 := by
      rw [map_pow, hte, ← map_pow, ← Subgroup.coe_pow, hx3]
      simp
    have h2 : (MulAut.conj g0).toMonoidHom 1 = 1 := map_one _
    exact (MulAut.conj g0).injective (h1.trans h2.symm)
  have ha3 : ∀ i, a i ^ 3 = 1 := by
    have h1 : rootDiagUnit TwistTag.E6.tag (a ^ 3) =
        rootDiagUnit TwistTag.E6.tag (1 : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ) := by
      have e1 : rootDiagUnit TwistTag.E6.tag (a ^ 3) =
          (rootDiagUnitHom TwistTag.E6.tag (AlgebraicClosure K) a) ^ 3 :=
        map_pow (rootDiagUnitHom TwistTag.E6.tag (AlgebraicClosure K)) a 3
      rw [e1, ht3]
      exact (map_one (rootDiagUnitHom TwistTag.E6.tag (AlgebraicClosure K))).symm
    intro i
    have := congrFun (CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective h1) i
    simpa using this
  have hpow : ∀ b : (AlgebraicClosure K)ˣ, b ^ 3 = 1 → ∃ k : ℕ, b = ω ^ k := by
    intro b hb
    have hb' : (b : AlgebraicClosure K) ^ 3 = 1 := by
      have := congrArg (fun u : (AlgebraicClosure K)ˣ => (u : AlgebraicClosure K)) hb
      simpa using this
    obtain ⟨k, -, hk⟩ := hω.eq_pow_of_pow_eq_one hb'
    exact ⟨k, Units.ext (by rw [Units.val_pow_eq_pow_val, hk])⟩
  choose k hk using fun i => hpow (a i) (ha3 i)
  have hak : a = fun i => ω ^ k i := funext hk
  subst hak
  exact ⟨k, htg, hfix⟩

theorem tw_e6RootParams_zpow {L : Type} [Field L] (ζ : Lˣ) (m : Fin Tag.E6.rank → ℤ) :
    e6RootParams (fun l => ζ ^ m l) = fun j => ζ ^ (∑ l, Tag.E6.cartan l j * m l) := by
  funext j
  simp only [e6RootParams]
  rw [← liftProd_zpow_sum]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [← zpow_mul, mul_comm]

theorem tw_kills_of_pair {K : Type} [Field K] {σ : K ≃+* K}
    {E₀ : Subgroup (twistedE6RootGroup K σ)} {ω : (AlgebraicClosure K)ˣ} (hω3 : ω ^ 3 = 1)
    {x₁ x₂ : twistedE6RootGroup K σ}
    (hgen : Subgroup.closure ({x₁, x₂} : Set (twistedE6RootGroup K σ)) = E₀)
    (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)) (k₁ k₂ : Fin Tag.E6.rank → ℕ)
    (ha₁ : rootDiagUnit TwistTag.E6.tag (fun i => ω ^ k₁ i) =
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (x₁ : ModGL TwistTag.E6.tag K) * g0)
    (ha₂ : rootDiagUnit TwistTag.E6.tag (fun i => ω ^ k₂ i) =
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (x₂ : ModGL TwistTag.E6.tag K) * g0)
    {α : Fin Tag.E6.rank → ℤ}
    (h₁ : (3 : ℤ) ∣ ∑ i, α i * (k₁ i : ℤ)) (h₂ : (3 : ℤ) ∣ ∑ i, α i * (k₂ i : ℤ)) :
    TwKills K σ E₀ g0 α := by
  classical
  have hω3' : ∀ (k : Fin Tag.E6.rank → ℕ), (3 : ℤ) ∣ ∑ i, α i * (k i : ℤ) →
      rootChar (fun i => ω ^ k i) α = 1 := by
    intro k hk
    rw [tw_rootChar_pow_exp]
    have hk' : (3 : ℤ) ∣ ∑ i, (k i : ℤ) * α i := by
      simpa only [mul_comm] using hk
    obtain ⟨c, hc⟩ := hk'
    rw [hc, zpow_mul]
    have : ω ^ (3 : ℤ) = 1 := by simpa using hω3
    rw [this, one_zpow]
  set φ : twistedE6RootGroup K σ →* ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
    (MulAut.conj g0⁻¹).toMonoidHom.comp ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
      (twistedE6RootGroup K σ).subtype) with hφ
  have hφx : ∀ x : twistedE6RootGroup K σ, φ x =
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (x : ModGL TwistTag.E6.tag K) * g0 := fun x => by
    simp [hφ, MulAut.conj_apply]
  set Sg : Subgroup (twistedE6RootGroup K σ) :=
    ((rootCharHom (τ := TwistTag.E6.tag) (L := AlgebraicClosure K) α).ker.map
      (rootDiagUnitHom TwistTag.E6.tag (AlgebraicClosure K))).comap φ with hSg
  have hmemSg : ∀ (x : twistedE6RootGroup K σ) (a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ),
      rootDiagUnit TwistTag.E6.tag a = φ x → rootChar a α = 1 → x ∈ Sg := by
    intro x a hax hr
    refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨a, ?_, hax⟩)
    exact MonoidHom.mem_ker.2 (show rootCharHom (τ := TwistTag.E6.tag) (L := AlgebraicClosure K)
      α a = 1 from hr)
  have hx₁ : x₁ ∈ Sg := hmemSg x₁ _ (by rw [hφx]; exact ha₁) (hω3' k₁ h₁)
  have hx₂ : x₂ ∈ Sg := hmemSg x₂ _ (by rw [hφx]; exact ha₂) (hω3' k₂ h₂)
  have hES : E₀ ≤ Sg := by
    rw [← hgen]
    refine (Subgroup.closure_le Sg).2 ?_
    intro z hz
    rcases hz with rfl | rfl
    · exact hx₁
    · exact hx₂
  intro x hx
  obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 (hES hx))
  refine ⟨a, ?_, MonoidHom.mem_ker.1 ha⟩
  rw [← hφx]
  exact hax

theorem tw_diagramMap_conj_diag {L : Type} [Field L] (ω : Lˣ) (hω3 : ω ^ 3 = 1)
    (v : WeylGroup TwistTag.E6.tag) (k : Fin TwistTag.E6.tag.rank → ℕ)
    (hk : InvFixedZ v (fun j => (k j : ℤ))) :
    diagramMap TwistTag.E6 L *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L v *
          rootDiagUnit TwistTag.E6.tag (fun i => ω ^ k i) *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)⁻¹) *
        (diagramMap TwistTag.E6 L)⁻¹ =
      canonicalRep (coxeterSystem TwistTag.E6.tag) L v *
        rootDiagUnit TwistTag.E6.tag (fun i => ω ^ k i) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)⁻¹ := by
  rw [canonicalRep_conj_rootDiagUnit]
  have h1 := diagramMap_mul_rootDiagUnit (t := TwistTag.E6) (K := L)
    (weylTuple v fun i => ω ^ k i)
  rw [h1, mul_inv_cancel_right]
  congr 1
  funext i
  have hinv : ∀ c : Fin TwistTag.E6.tag.rank, TwistTag.E6.perm (TwistTag.E6.perm c) = c := by
    intro c
    revert c
    decide
  have hs : TwistTag.E6.perm.symm i = TwistTag.E6.perm i := by
    rw [Equiv.symm_apply_eq, hinv]
  simp only [weylTuple]
  rw [hs]
  have e1 := tw_rootChar_pow_exp (L := L) ω k
    (v⁻¹ • (Pi.single (TwistTag.E6.perm i) 1 : Fin TwistTag.E6.tag.rank → ℤ))
  have e2 := tw_rootChar_pow_exp (L := L) ω k
    (v⁻¹ • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ))
  exact e1.trans ((zpow_eq_zpow_of_dvd hω3 (hk i)).trans e2.symm)

theorem tw_outer_false {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (hq : (p ^ f) % 3 = 2)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (p ^ f))
    (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (v : WeylGroup Tag.E6)
    (hF : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    {ω : (AlgebraicClosure K)ˣ} (hω : IsPrimitiveRoot (ω : AlgebraicClosure K) 3)
    {x₁ x₂ : twistedE6RootGroup K σ} (k₁ k₂ : Fin Tag.E6.rank → ℕ)
    (ha₁ : rootDiagUnit TwistTag.E6.tag (fun i => ω ^ k₁ i) =
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (x₁ : ModGL TwistTag.E6.tag K) * g0)
    (ha₂ : rootDiagUnit TwistTag.E6.tag (fun i => ω ^ k₂ i) =
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (x₂ : ModGL TwistTag.E6.tag K) * g0)
    (a b : ℕ) (m : Fin Tag.E6.rank → ℤ)
    (hm : ∀ j : Fin Tag.E6.rank, (3 : ℤ) ∣
      (∑ l, Tag.E6.cartan l j * m l) - ((a : ℤ) * (k₁ j : ℤ) + (b : ℤ) * (k₂ j : ℤ)))
    (hnot : ¬ ∀ i, (3 : ℤ) ∣ ((twE6W0 * v⁻¹) • m) i - m i) : False := by
  classical
  set L := AlgebraicClosure K with hL
  set ι : K →+* L := algebraMap K L with hι
  have hωu : IsPrimitiveRoot ω 3 := IsPrimitiveRoot.coe_units_iff.1 hω
  have hω3 : ω ^ 3 = 1 := Units.ext (by simpa using hω.pow_eq_one)
  obtain ⟨ωv, hωv, hvw⟩ := (coxeterSystem Tag.E6).exists_isReduced v
  have hF' : twistHom TwistTag.E6 L Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) L ((coxeterSystem Tag.E6).wordProd ωv) := by
    rw [← hvw]
    exact hF
  set y : ModGL TwistTag.E6.tag K :=
    (x₁ : ModGL TwistTag.E6.tag K) ^ a * (x₂ : ModGL TwistTag.E6.tag K) ^ b with hy
  have hymem : y ∈ twistedE6RootGroup K σ := mul_mem (pow_mem x₁.2 a) (pow_mem x₂.2 b)
  have hx₁L : baseChangeGL ι (x₁ : ModGL TwistTag.E6.tag K) =
      g0 * rootDiagUnit TwistTag.E6.tag (fun i => ω ^ k₁ i) * g0⁻¹ := by
    rw [ha₁]
    group
  have hx₂L : baseChangeGL ι (x₂ : ModGL TwistTag.E6.tag K) =
      g0 * rootDiagUnit TwistTag.E6.tag (fun i => ω ^ k₂ i) * g0⁻¹ := by
    rw [ha₂]
    group
  have hyL : baseChangeGL ι y = g0 * (rootDiagUnit TwistTag.E6.tag (fun i => ω ^ k₁ i) ^ a *
      rootDiagUnit TwistTag.E6.tag (fun i => ω ^ k₂ i) ^ b) * g0⁻¹ := by
    rw [hy, map_mul, map_pow, map_pow, hx₁L, hx₂L, conj_pow, conj_pow]
    group
  have hparam : ((fun i => ω ^ k₁ i) ^ a * (fun i => ω ^ k₂ i) ^ b : Fin Tag.E6.rank → Lˣ) =
      e6RootParams (fun l => ω ^ m l) := by
    funext j
    rw [tw_e6RootParams_zpow]
    simp only [Pi.mul_apply, Pi.pow_apply]
    have e1 : (ω ^ k₁ j) ^ a = ω ^ ((a : ℤ) * (k₁ j : ℤ)) := by
      rw [← pow_mul, ← zpow_natCast]
      congr 1
      push_cast
      ring
    have e2 : (ω ^ k₂ j) ^ b = ω ^ ((b : ℤ) * (k₂ j : ℤ)) := by
      rw [← pow_mul, ← zpow_natCast]
      congr 1
      push_cast
      ring
    rw [e1, e2, ← zpow_add]
    exact zpow_eq_zpow_of_dvd hω3 (by
      have := dvd_neg.2 (hm j)
      rwa [neg_sub] at this)
  have hd' : rootDiagUnit TwistTag.E6.tag (fun i => ω ^ k₁ i) ^ a *
      rootDiagUnit TwistTag.E6.tag (fun i => ω ^ k₂ i) ^ b =
      rootDiagUnit TwistTag.E6.tag (e6RootParams (fun l => ω ^ m l)) := by
    have h1 := map_mul (rootDiagUnitHom Tag.E6 L) ((fun i => ω ^ k₁ i) ^ a)
      ((fun i => ω ^ k₂ i) ^ b)
    rw [map_pow, map_pow] at h1
    exact h1.symm.trans (congrArg (rootDiagUnitHom Tag.E6 L) hparam)
  have hyu : baseChangeGL ι y =
      g0 * rootDiagUnit TwistTag.E6.tag (e6RootParams (fun l => ω ^ m l)) * g0⁻¹ :=
    hyL.trans (congrArg (fun z => g0 * z * g0⁻¹) hd')
  have key := tw_class_trivial_of_mem hp hf hK σ hσ hq Fr hFr g0 hg0C hωv hF'
    (fun l => ω ^ m l) hymem hyu
  have hFrω : Units.map Fr.toMonoidHom ω = ω ^ (p ^ f) :=
    Units.ext (by rw [Units.coe_map, Units.val_pow_eq_pow_val]; exact hFr _)
  obtain ⟨c, hc⟩ : ∃ c : ℕ, p ^ f = 3 * c + 2 := ⟨p ^ f / 3, by omega⟩
  have hinner : (fun l => Units.map Fr.toMonoidHom ((fun l => ω ^ m l) (e6RhoFour l))) =
      fun l => ω ^ ((twE6W0 • m) l) := by
    funext l
    have h1 : Units.map Fr.toMonoidHom (ω ^ m (e6RhoFour l)) =
        ω ^ (((p ^ f : ℕ) : ℤ) * m (e6RhoFour l)) := by
      rw [map_zpow, hFrω, ← zpow_natCast, ← zpow_mul]
    have h2 : (twE6W0 • m) l = -(m (e6RhoFour l)) := by
      rw [twE6W0_smul]
      simp only [Pi.neg_apply, permLattice, Function.comp_apply]
      rw [CFSG.RankThree.E6.e6Rho_symm]
      have : e6RhoFour = CFSG.RankThree.E6.e6Rho := e6RhoFour_eq_twistPerm
      rw [this]
    show Units.map Fr.toMonoidHom (ω ^ m (e6RhoFour l)) = _
    rw [h1, h2]
    refine zpow_eq_zpow_of_dvd hω3 ?_
    rw [hc]
    push_cast
    exact ⟨(c + 1) * m (e6RhoFour l), by ring⟩
  have key2 : ωv.foldr e6StarS (fun l => ω ^ ((twE6W0 • m) l)) = fun l => ω ^ m l :=
    (congrArg (ωv.foldr e6StarS) hinner.symm).trans key
  have key3 : (fun l => ω ^ (((coxeterSystem Tag.E6).wordProd ωv • (twE6W0 • m)) l)) =
      fun l => ω ^ m l := by
    rw [wordProd_smul_eq_foldr]
    exact (foldr_e6StarS_zpow ω ωv (twE6W0 • m)).symm.trans key2
  have hv3 : ∀ l, (3 : ℤ) ∣ (((coxeterSystem Tag.E6).wordProd ωv • (twE6W0 • m)) l) - m l := by
    intro l
    have h1 : ω ^ (((coxeterSystem Tag.E6).wordProd ωv • (twE6W0 • m)) l) = ω ^ m l :=
      congrFun key3 l
    have h2 : ω ^ ((((coxeterSystem Tag.E6).wordProd ωv • (twE6W0 • m)) l) - m l) = 1 := by
      rw [zpow_sub, h1, mul_inv_cancel]
    exact (hωu.zpow_eq_one_iff_dvd _).1 h2
  rw [← hvw, ← mul_smul] at hv3
  apply hnot
  have := tw_inv_smul_mod3 (v * twE6W0) m hv3
  rwa [mul_inv_rev, twE6W0_inv] at this

end Exp

end CFSG.LieType.SeitzGeneration.ExcHighThree

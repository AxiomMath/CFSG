module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4ZPlane
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4ZTorusClose

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.HardMathSupport.Lang.AnisoE6 CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint

set_option linter.unusedSectionVars false


@[expose] def e6Orb (j : Fin Tag.F4.rank) : List (Fin TwistTag.E6.tag.rank) :=
  TwistTag.E6.orbitWord (f4FoldedIndex j)

@[expose] def e6Flat (ω : List (Fin Tag.F4.rank)) : List (Fin TwistTag.E6.tag.rank) :=
  ω.flatMap e6Orb

abbrev e6Three : Fin TwistTag.E6.tag.rank := ⟨3, by decide⟩

theorem e6Orb_one : e6Orb f4One = [e6Three] := by
  decide +kernel

theorem e6Flat_nil : e6Flat [] = [] := rfl

theorem e6Flat_cons (j : Fin Tag.F4.rank) (ω : List (Fin Tag.F4.rank)) :
    e6Flat (j :: ω) = e6Orb j ++ e6Flat ω := rfl

theorem e6Flat_zero : e6Flat (f4Word 0) = [] := rfl

theorem e6Flat_one : e6Flat (f4Word 1) =
    [(⟨2, by decide⟩ : Fin TwistTag.E6.tag.rank), ⟨4, by decide⟩] := by
  decide +kernel

theorem e6Flat_two : e6Flat (f4Word 2) =
    [(⟨0, by decide⟩ : Fin TwistTag.E6.tag.rank), ⟨5, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩] := by
  decide +kernel

section Theta

variable (k : Type) [Field k]

@[expose] def thetaE6 : adjointGroup Tag.F4 k →* ModGL TwistTag.E6.tag k :=
  (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).subtype.comp
    (e6FixedF4EquivAll k).symm.toMonoidHom

variable {k}

theorem thetaE6_x (j : Fin Tag.F4.rank) (c : k) :
    thetaE6 k ⟨xUnit Tag.F4 k j c, xUnit_mem_adjointGroup j c⟩ = f4OrbitXUnit k j c := by
  have h : (e6FixedF4EquivAll k).symm ⟨xUnit Tag.F4 k j c, xUnit_mem_adjointGroup j c⟩ =
      ⟨f4OrbitXUnit k j c, f4OrbitXUnit_mem j c⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext (by rw [coe_e6FixedF4EquivAll, e6FixedToF4_f4OrbitXUnit_all])
  exact congrArg Subtype.val h

theorem thetaE6_y (j : Fin Tag.F4.rank) (c : k) :
    thetaE6 k ⟨yUnit Tag.F4 k j c, yUnit_mem_adjointGroup j c⟩ = f4OrbitYUnit k j c := by
  have h : (e6FixedF4EquivAll k).symm ⟨yUnit Tag.F4 k j c, yUnit_mem_adjointGroup j c⟩ =
      ⟨f4OrbitYUnit k j c, f4OrbitYUnit_mem j c⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext (by rw [coe_e6FixedF4EquivAll, e6FixedToF4_f4OrbitYUnit_all])
  exact congrArg Subtype.val h

theorem f4OrbitN_eq_weylWord (j : Fin Tag.F4.rank) :
    f4OrbitXUnit k j 1 * f4OrbitYUnit k j (-1) * f4OrbitXUnit k j 1 = weylWord k (e6Orb j) := by
  have h := coe_orbitN_one TwistTag.E6 (RingHom.id k) (f4FoldedIndex j)
  rw [orbitN, Subgroup.coe_mul, Subgroup.coe_mul] at h
  rw [weylWord, e6Orb, ← h, f4OrbitXUnit_eq_orbitX, f4OrbitYUnit_eq_orbitY]
  congr 3

theorem thetaE6_weylElt (j : Fin Tag.F4.rank) :
    thetaE6 k ⟨weylElt Tag.F4 k j 1, weylElt_mem_adjointGroup j 1⟩ = weylWord k (e6Orb j) := by
  have h : (⟨weylElt Tag.F4 k j 1, weylElt_mem_adjointGroup j 1⟩ : adjointGroup Tag.F4 k) =
      ⟨xUnit Tag.F4 k j 1, xUnit_mem_adjointGroup j 1⟩ *
        ⟨yUnit Tag.F4 k j (-1), yUnit_mem_adjointGroup j (-1)⟩ *
          ⟨xUnit Tag.F4 k j 1, xUnit_mem_adjointGroup j 1⟩ := by
    refine Subtype.ext ?_
    show weylElt Tag.F4 k j 1 = xUnit Tag.F4 k j 1 * yUnit Tag.F4 k j (-1) * xUnit Tag.F4 k j 1
    rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
    simp
  rw [h, map_mul, map_mul, thetaE6_x, thetaE6_y, f4OrbitN_eq_weylWord]

theorem thetaE6_weylWord (ω : List (Fin Tag.F4.rank)) :
    thetaE6 k ⟨weylWord k ω, weylWord_mem_adjointGroup ω⟩ = weylWord k (e6Flat ω) := by
  induction ω with
  | nil =>
    have h : (⟨weylWord k ([] : List (Fin Tag.F4.rank)), weylWord_mem_adjointGroup _⟩ :
        adjointGroup Tag.F4 k) = 1 := Subtype.ext (weylWord_nil k)
    rw [h, map_one, e6Flat_nil, weylWord_nil]
  | cons j ω ih =>
    have h : (⟨weylWord k (j :: ω), weylWord_mem_adjointGroup _⟩ : adjointGroup Tag.F4 k) =
        ⟨weylElt Tag.F4 k j 1, weylElt_mem_adjointGroup j 1⟩ *
          ⟨weylWord k ω, weylWord_mem_adjointGroup _⟩ := Subtype.ext (weylWord_cons k j ω)
    rw [h, map_mul, thetaE6_weylElt, ih, e6Flat_cons, weylWord_append]

theorem f4S_mem_adjointGroup : f4S k ∈ adjointGroup Tag.F4 k :=
  mul_mem (xUnit_mem_adjointGroup _ _) (yUnit_mem_adjointGroup _ _)

theorem thetaE6_f4S :
    thetaE6 k ⟨f4S k, f4S_mem_adjointGroup⟩ =
      xUnit TwistTag.E6.tag k e6Three 1 * yUnit TwistTag.E6.tag k e6Three (-3) := by
  have h : (⟨f4S k, f4S_mem_adjointGroup⟩ : adjointGroup Tag.F4 k) =
      ⟨xUnit Tag.F4 k f4One 1, xUnit_mem_adjointGroup _ _⟩ *
        ⟨yUnit Tag.F4 k f4One (-3), yUnit_mem_adjointGroup _ _⟩ := rfl
  have hX : ∀ c : k, f4OrbitXUnit k f4One c = xUnit TwistTag.E6.tag k e6Three c := fun c => by
    rw [f4OrbitXUnit, ← e6Orb, e6Orb_one]
    simp
  have hY : ∀ c : k, f4OrbitYUnit k f4One c = yUnit TwistTag.E6.tag k e6Three c := fun c => by
    rw [f4OrbitYUnit, ← e6Orb, e6Orb_one]
    simp
  rw [h, map_mul, thetaE6_x, thetaE6_y, hX, hY]

theorem thetaE6_f4Z :
    thetaE6 k ⟨f4Z k, f4Z_mem_adjointGroup⟩ =
      (weylWord k (e6Flat (f4Word 0)) * (xUnit TwistTag.E6.tag k e6Three 1 * yUnit TwistTag.E6.tag k e6Three (-3)) *
          (weylWord k (e6Flat (f4Word 0)))⁻¹) *
        ((weylWord k (e6Flat (f4Word 1)) * (xUnit TwistTag.E6.tag k e6Three 1 * yUnit TwistTag.E6.tag k e6Three (-3)) *
            (weylWord k (e6Flat (f4Word 1)))⁻¹) *
          (weylWord k (e6Flat (f4Word 2)) * (xUnit TwistTag.E6.tag k e6Three 1 * yUnit TwistTag.E6.tag k e6Three (-3)) *
            (weylWord k (e6Flat (f4Word 2)))⁻¹)) := by
  have hi : ∀ i : Fin 3, thetaE6 k ⟨f4Phi k i zA, f4Phi_mem_adjointGroup i zA⟩ =
      weylWord k (e6Flat (f4Word i)) * (xUnit TwistTag.E6.tag k e6Three 1 * yUnit TwistTag.E6.tag k e6Three (-3)) *
        (weylWord k (e6Flat (f4Word i)))⁻¹ := fun i => by
    have h : (⟨f4Phi k i zA, f4Phi_mem_adjointGroup i zA⟩ : adjointGroup Tag.F4 k) =
        ⟨weylWord k (f4Word i), weylWord_mem_adjointGroup _⟩ * ⟨f4S k, f4S_mem_adjointGroup⟩ *
          (⟨weylWord k (f4Word i), weylWord_mem_adjointGroup _⟩)⁻¹ :=
      Subtype.ext (f4Phi_zA i)
    rw [h, map_mul, map_mul, map_inv, thetaE6_weylWord, thetaE6_f4S]
  have h : (⟨f4Z k, f4Z_mem_adjointGroup⟩ : adjointGroup Tag.F4 k) =
      ⟨f4Phi k 0 zA, f4Phi_mem_adjointGroup 0 zA⟩ *
        (⟨f4Phi k 1 zA, f4Phi_mem_adjointGroup 1 zA⟩ *
          ⟨f4Phi k 2 zA, f4Phi_mem_adjointGroup 2 zA⟩) := Subtype.ext f4Z_eq
  rw [h, map_mul, map_mul, hi, hi, hi]

end Theta


section Commute

@[expose] def torusExp : Fin TwistTag.E6.tag.rank → ℤ := ![2, 0, -1, 0, 1, -2]

theorem torusChar_eq_zpow {K : Type} [Field K] (σ : K ≃+* K) (t : Kˣ)
    (hs : Units.map σ.toRingHom.toMonoidHom t = t⁻¹) :
    torusChar σ t = fun l => t ^ torusExp l := by
  have e : ∀ l : Fin TwistTag.E6.tag.rank, TwistTag.E6.tag.cartan ⟨0, by decide⟩ l -
      TwistTag.E6.tag.cartan ⟨5, by decide⟩ l = torusExp l := by
    decide +kernel
  funext l
  unfold torusChar
  rw [hs, ← e l, zpow_sub, inv_zpow]

theorem rootChar_torusChar_flat {K : Type} [Field K] (σ : K ≃+* K) (t : Kˣ)
    (hs : Units.map σ.toRingHom.toMonoidHom t = t⁻¹) (i : Fin 3) :
    ∏ l, torusChar σ t l ^ ((coxeterSystem TwistTag.E6.tag).wordProd (e6Flat (f4Word i)) •
      (Pi.single e6Three 1 : Fin TwistTag.E6.tag.rank → ℤ)) l = 1 := by
  have h := rootChar_zpow_tuple t torusExp
    ((coxeterSystem TwistTag.E6.tag).wordProd (e6Flat (f4Word i)) •
      (Pi.single e6Three 1 : Fin TwistTag.E6.tag.rank → ℤ))
  have hsum : ∑ l, ((coxeterSystem TwistTag.E6.tag).wordProd (e6Flat (f4Word i)) •
      (Pi.single e6Three 1 : Fin TwistTag.E6.tag.rank → ℤ)) l * torusExp l = 0 := by
    fin_cases i
    · simp only [Fin.zero_eta, e6Flat_zero, CoxeterSystem.wordProd_nil, one_smul]
      decide +kernel
    · simp only [Fin.mk_one, e6Flat_one, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil,
        mul_one, mul_smul, simple_smul]
      decide +kernel
    · simp only [Fin.reduceFinMk, e6Flat_two, CoxeterSystem.wordProd_cons,
        CoxeterSystem.wordProd_nil, mul_one, mul_smul, simple_smul]
      decide +kernel
  rw [hsum, zpow_zero] at h
  rw [torusChar_eq_zpow σ t hs]
  exact h

theorem commute_rootDiagUnit_conj {K : Type} [Field K] (a : Fin TwistTag.E6.tag.rank → Kˣ)
    (ω : List (Fin TwistTag.E6.tag.rank))
    (h : ∏ l, a l ^ ((coxeterSystem TwistTag.E6.tag).wordProd ω •
      (Pi.single e6Three 1 : Fin TwistTag.E6.tag.rank → ℤ)) l = 1) :
    Commute (rootDiagUnit TwistTag.E6.tag a)
      (weylWord K ω * (xUnit TwistTag.E6.tag K e6Three 1 * yUnit TwistTag.E6.tag K e6Three (-3)) *
        (weylWord K ω)⁻¹) := by
  have hmem : weylWord K ω * (xUnit TwistTag.E6.tag K e6Three 1 *
      yUnit TwistTag.E6.tag K e6Three (-3)) * (weylWord K ω)⁻¹ ∈
      rootRankOneGroup TwistTag.E6.tag K ((coxeterSystem TwistTag.E6.tag).wordProd ω •
        (Pi.single e6Three 1 : Fin TwistTag.E6.tag.rank → ℤ)) := by
    refine conj_mem_rootRankOneGroup ω (isRoot_single _ _) ?_
    have h1 := simpleRootSL2_mem_rootRankOneGroup (L := K) (τ := TwistTag.E6.tag) e6Three zA
    rwa [zA, map_mul, simpleRootSL2_uSL, simpleRootSL2_vSL] at h1
  obtain ⟨-, -, -, -, -, -, -, hcomm⟩ := exceptional_Lang_root_rank_one_torus_transport
    TwistTag.E6.tag K (IsRoot.smul (isRoot_single _ _) ((coxeterSystem TwistTag.E6.tag).wordProd ω))
  exact hcomm a h _ hmem

variable {k K : Type} [Field k] [Finite k] [Field K] [Finite K] [Algebra k K]

theorem commute_iota_f4Z (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ Nat.card k)
    (hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c) (hK : Nat.card K = Nat.card k ^ 2)
    (t : Kˣ) (ht : (t : K) ^ (Nat.card k + 1) = 1) :
    Commute (((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom)
      ⟨f4Z k, f4Z_mem_adjointGroup⟩) (torusWord σ hσ hK t) := by
  have hs : Units.map σ.toRingHom.toMonoidHom t = t⁻¹ := by
    refine Units.ext ?_
    show σ (t : K) = ((t⁻¹ : Kˣ) : K)
    rw [hσ, Units.val_inv_eq_inv_val]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact ht)
  have hcoe : ((((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom)
      ⟨f4Z k, f4Z_mem_adjointGroup⟩ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      baseChangeGL (algebraMap k K) (thetaE6 k ⟨f4Z k, f4Z_mem_adjointGroup⟩) := rfl
  have hS : baseChangeGL (algebraMap k K) (xUnit TwistTag.E6.tag k e6Three 1 *
      yUnit TwistTag.E6.tag k e6Three (-3)) =
      xUnit TwistTag.E6.tag K e6Three 1 * yUnit TwistTag.E6.tag K e6Three (-3) := by
    rw [map_mul, baseChangeGL_xUnit, baseChangeGL_yUnit, map_one, map_neg, map_ofNat]
  have hW : ∀ i : Fin 3, baseChangeGL (algebraMap k K)
      (weylWord k (e6Flat (f4Word i)) * (xUnit TwistTag.E6.tag k e6Three 1 *
        yUnit TwistTag.E6.tag k e6Three (-3)) * (weylWord k (e6Flat (f4Word i)))⁻¹) =
      weylWord K (e6Flat (f4Word i)) * (xUnit TwistTag.E6.tag K e6Three 1 *
        yUnit TwistTag.E6.tag K e6Three (-3)) * (weylWord K (e6Flat (f4Word i)))⁻¹ := fun i => by
    rw [map_mul, map_mul, map_inv, baseChangeGL_weylWord, hS]
  have e3 : ∀ a b c : ModGL TwistTag.E6.tag k, baseChangeGL (algebraMap k K) (a * (b * c)) =
      baseChangeGL (algebraMap k K) a *
        (baseChangeGL (algebraMap k K) b * baseChangeGL (algebraMap k K) c) :=
    fun a b c => by rw [map_mul, map_mul]
  have hc : ∀ i : Fin 3, Commute (rootDiagUnit TwistTag.E6.tag (torusChar σ t))
      (weylWord K (e6Flat (f4Word i)) * (xUnit TwistTag.E6.tag K e6Three 1 *
        yUnit TwistTag.E6.tag K e6Three (-3)) * (weylWord K (e6Flat (f4Word i)))⁻¹) := fun i =>
    commute_rootDiagUnit_conj _ _ (rootChar_torusChar_flat σ t hs i)
  have hz : ((((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom)
      ⟨f4Z k, f4Z_mem_adjointGroup⟩ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      (weylWord K (e6Flat (f4Word 0)) * (xUnit TwistTag.E6.tag K e6Three 1 *
        yUnit TwistTag.E6.tag K e6Three (-3)) * (weylWord K (e6Flat (f4Word 0)))⁻¹) *
      ((weylWord K (e6Flat (f4Word 1)) * (xUnit TwistTag.E6.tag K e6Three 1 *
        yUnit TwistTag.E6.tag K e6Three (-3)) * (weylWord K (e6Flat (f4Word 1)))⁻¹) *
      (weylWord K (e6Flat (f4Word 2)) * (xUnit TwistTag.E6.tag K e6Three 1 *
        yUnit TwistTag.E6.tag K e6Three (-3)) * (weylWord K (e6Flat (f4Word 2)))⁻¹)) := by
    rw [hcoe, thetaE6_f4Z, e3, hW 0, hW 1, hW 2]
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_torusWord, hz]
  exact ((hc 0).mul_right ((hc 1).mul_right (hc 2))).symm.eq

end Commute

end CFSG.LieType.SeitzGeneration.ExcHighThree

module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E7TwoSevenDescent
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeScLift
public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.LieType.SeitzGeneration.ExcHigh

namespace E7S

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.LieType.Steinberg.Isogeny CFSG.HardMathSupport.Timmesfeld.CrossChar

def node : Fin Tag.E7.rank := ⟨6, by decide⟩

theorem cartan_symm : ∀ i j : Fin Tag.E7.rank, Tag.cartan Tag.E7 i j = Tag.cartan Tag.E7 j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem exp_sum (j : Fin Tag.E7.rank) :
    ∑ l, e7B l node * Tag.cartan Tag.E7 l j = if j = node then 2 else 0 := by
  calc ∑ l, e7B l node * Tag.cartan Tag.E7 l j
      = ∑ l, Tag.cartan Tag.E7 j l * e7B l node :=
        Finset.sum_congr rfl fun l _ => by rw [cartan_symm l j, mul_comm]
    _ = if j = node then ((2 : ℕ) : ℤ) else 0 := e7B_spec j node
    _ = if j = node then 2 else 0 := by split_ifs <;> simp

theorem zpow_sum_prod {G : Type} [CommGroup G] {ι : Type} (g : G) (f : ι → ℤ) (s : Finset ι) :
    g ^ (∑ i ∈ s, f i) = ∏ i ∈ s, g ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add, ih]

theorem two_pow_mod_seven (e : ℕ) : 2 ^ e % 7 = 1 ∨ 2 ^ e % 7 = 2 ∨ 2 ^ e % 7 = 4 := by
  induction e with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; omega

theorem not_seven_dvd_two_pow_add_one (e : ℕ) : ¬ 7 ∣ 2 ^ e + 1 := by
  have h := two_pow_mod_seven e
  intro hd
  generalize 2 ^ e = x at h hd
  omega

def params {L : Type} [Field L] (u : Fin Tag.E7.rank → Lˣ) : Fin Tag.E7.rank → Lˣ :=
  fun j => ∏ l, u l ^ Tag.cartan Tag.E7 l j

theorem eltElement_neg {L : Type} [Field L] (i : Fin Tag.E7.rank) (c : L) :
    (rootOperatorFamily Tag.E7).eltElement (-simpleRoot Tag.E7 i) c = yElement i c :=
  Subtype.ext ((rootOperatorFamily Tag.E7).eltUnit_neg_simple i c)

theorem isogeny_nt {L : Type} [Field L] [Finite L] (a : Fin Tag.E7.rank) (s : Lˣ) :
    ((e7Isogeny L (e7Data_valid.nt L a s) : adjointGroup Tag.E7 L) : ModGL Tag.E7 L) =
      weylElt Tag.E7 L a s := by
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
  change ((e7Isogeny L (e7Data_valid.xm L (Pi.single a 1) s *
    e7Data_valid.xm L (-Pi.single a 1) (-((s⁻¹ : Lˣ) : L)) *
      e7Data_valid.xm L (Pi.single a 1) s) : adjointGroup Tag.E7 L) : ModGL Tag.E7 L) = _
  rw [map_mul, map_mul, e7Isogeny_xm_single, e7Isogeny_xm_neg_single, eltElement_simpleRoot,
    eltElement_neg]
  rfl

theorem isogeny_hm {L : Type} [Field L] [Finite L] (a : Fin Tag.E7.rank) (s : Lˣ) :
    ((e7Isogeny L (e7Data_valid.hm L a s) : adjointGroup Tag.E7 L) : ModGL Tag.E7 L) =
      rootDiagUnit Tag.E7 (fun j => s ^ Tag.cartan Tag.E7 a j) := by
  rw [← torusElt_eq_rootDiagUnit]
  change ((e7Isogeny L (e7Data_valid.nt L a s * (e7Data_valid.nt L a 1)⁻¹) :
    adjointGroup Tag.E7 L) : ModGL Tag.E7 L) = _
  rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, isogeny_nt, isogeny_nt,
    CFSG.Blueprint.Chevalley.weylElt_inv]
  rfl

theorem isogeny_minTorus {L : Type} [Field L] [Finite L] (u : Fin Tag.E7.rank → Lˣ) :
    ((e7Isogeny L (minTorus e7Data_valid L u) : adjointGroup Tag.E7 L) : ModGL Tag.E7 L) =
      rootDiagUnit Tag.E7 (params u) := by
  induction u using CFSG.LieType.Chevalley.ExceptionalCover.torusVec_induction with
  | h1 =>
    rw [map_one, map_one, OneMemClass.coe_one]
    have e : params (1 : Fin Tag.E7.rank → Lˣ) = 1 := by
      funext j
      simp [params]
    rw [e, rootDiagUnit_one]
  | hmul t t' ht ht' =>
    rw [map_mul, map_mul, Subgroup.coe_mul, ht, ht', ← rootDiagUnit_mul]
    congr 1
    funext j
    simp only [params, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]
  | hsingle a s =>
    rw [minTorus_mulSingle, isogeny_hm]
    congr 1
    funext j
    simp only [params]
    rw [Finset.prod_eq_single a (fun l _ hl => by rw [Pi.mulSingle_eq_of_ne hl, one_zpow])
      (fun h => absurd (Finset.mem_univ a) h), Pi.mulSingle_eq_same]

theorem minBC_minBC {k k' k'' : Type} [Field k] [Field k'] [Field k''] (ι : k →+* k')
    (φ : k' →+* k'') (g : e7Data_valid.minGroup k) :
    minBC e7Data_valid φ (minBC e7Data_valid ι g) = minBC e7Data_valid (φ.comp ι) g := by
  apply Subtype.ext
  apply Units.ext
  simp only [minBC, MonoidHom.codRestrict_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
    coe_minUnitsBC]
  refine minEnd_ext fun a => ?_
  rw [minEndBC_single, minEndBC_single, minEndBC_single]
  ext b
  simp

theorem minBC_minTorus {k k' : Type} [Field k] [Field k'] (φ : k →+* k')
    (u : Fin Tag.E7.rank → kˣ) :
    minBC e7Data_valid φ (minTorus e7Data_valid k u) =
      minTorus e7Data_valid k' (fun j => Units.map φ.toMonoidHom (u j)) := by
  induction u using CFSG.LieType.Chevalley.ExceptionalCover.torusVec_induction with
  | h1 =>
    have e : (fun j => Units.map φ.toMonoidHom ((1 : Fin Tag.E7.rank → kˣ) j)) = 1 := by
      funext j
      simp
    rw [map_one, map_one, e, map_one]
  | hmul t t' ht ht' =>
    have e : (fun j => Units.map φ.toMonoidHom ((t * t') j)) =
        (fun j => Units.map φ.toMonoidHom (t j)) * fun j => Units.map φ.toMonoidHom (t' j) := by
      funext j
      simp
    rw [map_mul, map_mul, ht, ht', e, map_mul]
  | hsingle a s =>
    have e : (fun j => Units.map φ.toMonoidHom ((Pi.mulSingle a s : Fin Tag.E7.rank → kˣ) j)) =
        Pi.mulSingle a (Units.map φ.toMonoidHom s) := by
      funext j
      by_cases hj : j = a
      · subst hj
        simp
      · simp [Pi.mulSingle_eq_of_ne hj]
    rw [e, minTorus_mulSingle, minTorus_mulSingle]
    simp [MinData.Valid.hm, MinData.Valid.nt, minBC_xm_single, minBC_xm_neg_single]

theorem isogeny_minBC {k k' : Type} [Field k] [Finite k] [Field k'] [Finite k'] (ι : k →+* k')
    (g : e7Data_valid.minGroup k) :
    ((e7Isogeny k' (minBC e7Data_valid ι g) : adjointGroup Tag.E7 k') : ModGL Tag.E7 k') =
      baseChangeGL ι ((e7Isogeny k g : adjointGroup Tag.E7 k) : ModGL Tag.E7 k) := by
  have h : (adjointGroup Tag.E7 k').subtype.comp ((e7Isogeny k').comp (minBC e7Data_valid ι)) =
      (baseChangeGL ι).comp ((adjointGroup Tag.E7 k).subtype.comp (e7Isogeny k)) := by
    refine MonoidHom.eq_of_eqOn_dense (closure_xm_simple_eq_top e7Data_valid k) ?_
    rintro _ ⟨i, c, rfl | rfl⟩
    · simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
      rw [minBC_xm_single, e7Isogeny_xm_single, e7Isogeny_xm_single, eltElement_simpleRoot,
        eltElement_simpleRoot]
      exact (baseChangeGL_xUnit ι i c).symm
    · simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
      rw [minBC_xm_neg_single, e7Isogeny_xm_neg_single, e7Isogeny_xm_neg_single,
        eltElement_neg, eltElement_neg]
      exact (baseChangeGL_yUnit ι i c).symm
  exact DFunLike.congr_fun h g

theorem center_minTorus {L : Type} [Field L] [Finite L] {c : e7Data_valid.minGroup L}
    (hc : c ∈ Subgroup.center (e7Data_valid.minGroup L)) :
    ∃ v : Fin Tag.E7.rank → Lˣ, c = minTorus e7Data_valid L v ∧ ∀ m, v m ^ 2 = 1 := by
  obtain ⟨v, rfl⟩ := center_le_range_minTorus e7Data_valid L isFiniteType_cartan_E7
    (e7Datum_isCTGroupDatum L) (e7Datum_steinbergExtras L) (e7Datum_bruhatExtras L) hc
  exact ⟨v, rfl, fun m => pow_eq_one_of_mem_centerChars e7B_spec
    ((minTorus_mem_center_iff e7Data_valid L v).1 hc) m⟩

theorem pow_odd_of_sq {L : Type} [Field L] {N : ℕ} (hN : Odd N) {x : L} (hx : x ^ 2 = 1) :
    x ^ N = x := by
  obtain ⟨t, rfl⟩ := hN
  rw [pow_succ, pow_mul, hx, one_pow, one_mul]

theorem not_mem_core {K L : Type} [Field K] [Finite K] [Field L] [Finite L]
    (ι : K →+* L) (ζ : Kˣ) (s : L) (ψ : L →+* L)
    (hs2 : s ^ 2 = ι (ζ : K)) (hsN : s ^ Nat.card K = -s)
    (hψ : ∀ x : L, ψ x = x ^ Nat.card K) (hcN : ∀ c : K, c ^ Nat.card K = c)
    (hodd : Odd (Nat.card K)) (h2 : (2 : L) ≠ 0) :
    rootDiagUnit Tag.E7 (Pi.mulSingle node ζ) ∉ adjointGroup Tag.E7 K := by
  intro hmem
  obtain ⟨x, hx⟩ := e7Isogeny_surjective K ⟨_, hmem⟩
  have hxK : ((e7Isogeny K x : adjointGroup Tag.E7 K) : ModGL Tag.E7 K) =
      rootDiagUnit Tag.E7 (Pi.mulSingle node ζ) := congrArg Subtype.val hx
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hs2
    exact Units.ne_zero ζ ((map_eq_zero ι).1 hs2.symm)
  let sU : Lˣ := Units.mk0 s hs0
  let uL : Fin Tag.E7.rank → Lˣ := fun l => sU ^ e7B l node
  let εT : Fin Tag.E7.rank → Lˣ := fun l => (-1 : Lˣ) ^ e7B l node
  have harith : params uL =
      fun j => Units.map ι.toMonoidHom ((Pi.mulSingle node ζ : Fin Tag.E7.rank → Kˣ) j) := by
    funext j
    have e1 : ∀ l, (sU ^ e7B l node) ^ Tag.cartan Tag.E7 l j =
        sU ^ (e7B l node * Tag.cartan Tag.E7 l j) := fun l => (zpow_mul _ _ _).symm
    simp only [params, uL]
    simp_rw [e1]
    rw [← zpow_sum_prod, exp_sum j]
    by_cases hj : j = node
    · subst hj
      rw [if_pos rfl, Pi.mulSingle_eq_same]
      apply Units.ext
      simp [sU, hs2]
    · rw [if_neg hj, zpow_zero, Pi.mulSingle_eq_of_ne hj, map_one]
  have hyL : ((e7Isogeny L (minTorus e7Data_valid L uL) : adjointGroup Tag.E7 L) :
      ModGL Tag.E7 L) =
      rootDiagUnit Tag.E7
        (fun j => Units.map ι.toMonoidHom ((Pi.mulSingle node ζ : Fin Tag.E7.rank → Kˣ) j)) := by
    rw [isogeny_minTorus, harith]
  have hxL : ((e7Isogeny L (minBC e7Data_valid ι x) : adjointGroup Tag.E7 L) : ModGL Tag.E7 L) =
      rootDiagUnit Tag.E7
        (fun j => Units.map ι.toMonoidHom ((Pi.mulSingle node ζ : Fin Tag.E7.rank → Kˣ) j)) := by
    rw [isogeny_minBC, hxK, baseChangeGL_rootDiagUnit]
  have hck : ((e7Isogeny L (minBC e7Data_valid ι x * (minTorus e7Data_valid L uL)⁻¹) :
      adjointGroup Tag.E7 L) : ModGL Tag.E7 L) = 1 := by
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hxL, hyL, mul_inv_cancel]
  have hcker : minBC e7Data_valid ι x * (minTorus e7Data_valid L uL)⁻¹ ∈
      (e7Isogeny L).ker := by
    rw [MonoidHom.mem_ker]
    exact Subtype.ext hck
  rw [CFSG.LieType.Steinberg.CentralExt.FieldFour.e7Isogeny_ker_eq_center] at hcker
  obtain ⟨v, hv, hv2⟩ := center_minTorus hcker
  have hcomp : ψ.comp ι = ι := by
    ext c
    rw [RingHom.comp_apply, hψ, ← map_pow, hcN]
  have hΦx : minBC e7Data_valid ψ (minBC e7Data_valid ι x) = minBC e7Data_valid ι x := by
    rw [minBC_minBC, hcomp]
  have hpsiU : (fun j => Units.map ψ.toMonoidHom (uL j)) = εT * uL := by
    have hsU : Units.map ψ.toMonoidHom sU = (-1 : Lˣ) * sU := by
      apply Units.ext
      simp [sU, hψ, hsN]
    funext j
    show Units.map ψ.toMonoidHom (sU ^ e7B j node) = (-1 : Lˣ) ^ e7B j node * sU ^ e7B j node
    rw [map_zpow, hsU, mul_zpow]
  have hΦY : minBC e7Data_valid ψ (minTorus e7Data_valid L uL) =
      minTorus e7Data_valid L εT * minTorus e7Data_valid L uL := by
    have e : minTorus e7Data_valid L (fun j => Units.map ψ.toMonoidHom (uL j)) =
        minTorus e7Data_valid L (εT * uL) := congrArg (minTorus e7Data_valid L) hpsiU
    rw [minBC_minTorus, e, map_mul]
  have hvψ : (fun j => Units.map ψ.toMonoidHom (v j)) = v := by
    funext j
    apply Units.ext
    have hx2 : ((v j : Lˣ) : L) ^ 2 = 1 := by
      have h := congrArg Units.val (hv2 j)
      simpa using h
    simp [hψ, pow_odd_of_sq hodd hx2]
  have hΦW : minBC e7Data_valid ψ (minTorus e7Data_valid L v) = minTorus e7Data_valid L v := by
    have e : minTorus e7Data_valid L (fun j => Units.map ψ.toMonoidHom (v j)) =
        minTorus e7Data_valid L v := congrArg (minTorus e7Data_valid L) hvψ
    rw [minBC_minTorus, e]
  have h5 := congrArg (minBC e7Data_valid ψ) hv
  rw [map_mul, map_inv, hΦx, hΦY, hΦW] at h5
  have h6 : minTorus e7Data_valid L v * (minTorus e7Data_valid L εT)⁻¹ =
      minTorus e7Data_valid L v := by
    calc minTorus e7Data_valid L v * (minTorus e7Data_valid L εT)⁻¹
        = minBC e7Data_valid ι x * (minTorus e7Data_valid L uL)⁻¹ *
            (minTorus e7Data_valid L εT)⁻¹ := by rw [hv]
      _ = minBC e7Data_valid ι x *
            (minTorus e7Data_valid L εT * minTorus e7Data_valid L uL)⁻¹ := by
          simp only [mul_inv_rev, mul_assoc]
      _ = minTorus e7Data_valid L v := h5
  have hZ : minTorus e7Data_valid L εT = 1 := by
    simpa using h6
  have hε : εT = 1 :=
    minTorus_injective e7Data_valid L (hZ.trans (map_one (minTorus e7Data_valid L)).symm)
  have hεj : (-1 : Lˣ) ^ e7B (⟨1, by decide⟩ : Fin Tag.E7.rank) node = 1 :=
    congrFun hε (⟨1, by decide⟩ : Fin Tag.E7.rank)
  have hε1 : e7B (⟨1, by decide⟩ : Fin Tag.E7.rank) node = 3 := by decide
  rw [hε1] at hεj
  have hv1 := congrArg Units.val hεj
  simp only [Units.val_zpow_eq_zpow_val, Units.val_neg, Units.val_one] at hv1
  have h3 : (-1 : L) ^ 3 = 1 := by simpa using hv1
  exact h2 (by linear_combination -h3)

end E7S

open E7S in
theorem e7SplitTorusNonSimple_holds : E7SplitTorusNonSimple := by
  intro K _ _ h7
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hchar, n, hp, hcardK⟩ := FiniteField.card' K
  have hcard : Nat.card K = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcardK]
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [hcard] at h7
    exact not_seven_dvd_two_pow_add_one _ h7
  have hodd : Odd (Nat.card K) := by
    rw [hcard]
    exact (hp.odd_of_ne_two hp2).pow
  have hF : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    exact hp2
  have hcN : ∀ c : K, c ^ Nat.card K = c := fun c => by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  obtain ⟨ζ0, hζ0⟩ := FiniteField.exists_nonsquare hF
  have hζne : ζ0 ≠ 0 := fun h => hζ0 ⟨0, by rw [h, mul_zero]⟩
  obtain ⟨m, hm⟩ := id hodd
  have hFerm : ζ0 ^ (2 * m) = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one ζ0 hζne
    have hc : Fintype.card K = 2 * m + 1 := by
      rw [← Nat.card_eq_fintype_card]
      exact hm
    rwa [hc, Nat.add_sub_cancel] at h
  have hm1 : ζ0 ^ m ≠ 1 := by
    intro h
    apply hζ0
    rw [FiniteField.isSquare_iff hF hζne]
    have hc : Fintype.card K / 2 = m := by
      rw [← Nat.card_eq_fintype_card, hm]
      omega
    rw [hc]
    exact h
  have hζm : ζ0 ^ m = -1 := by
    have hsq : ζ0 ^ m * ζ0 ^ m = 1 := by
      rw [← pow_add, ← two_mul, hFerm]
    rcases mul_self_eq_one_iff.1 hsq with h | h
    · exact absurd h hm1
    · exact h
  obtain ⟨P, hP⟩ : ∃ P : Polynomial K, P = Polynomial.X ^ 2 - Polynomial.C ζ0 := ⟨_, rfl⟩
  have hirr : Irreducible P := by
    rw [hP]
    exact X_pow_sub_C_irreducible_of_prime Nat.prime_two fun b hb => hζ0 ⟨b, by rw [← hb, sq]⟩
  have hmon : P.Monic := by
    rw [hP]
    exact Polynomial.monic_X_pow_sub_C ζ0 two_ne_zero
  haveI : Fact (Irreducible P) := ⟨hirr⟩
  haveI : Module.Finite K (AdjoinRoot P) := hmon.finite_adjoinRoot
  haveI : Finite (AdjoinRoot P) := Module.finite_of_finite K
  haveI : CharP (AdjoinRoot P) p :=
    charP_of_injective_algebraMap (algebraMap K (AdjoinRoot P)).injective p
  haveI : Fact p.Prime := ⟨hp⟩
  have hs2 : (AdjoinRoot.root P) ^ 2 = algebraMap K (AdjoinRoot P) ζ0 := by
    have h0 : AdjoinRoot.mk P (Polynomial.X ^ 2 - Polynomial.C ζ0) = 0 := by
      rw [← hP]
      exact AdjoinRoot.mk_self
    rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h0
    exact sub_eq_zero.1 h0
  have hsN : (AdjoinRoot.root P) ^ Nat.card K = -(AdjoinRoot.root P) := by
    rw [hm, pow_succ, pow_mul, hs2, ← map_pow, hζm, map_neg, map_one, neg_one_mul]
  have hψ : ∀ x : AdjoinRoot P,
      iterateFrobenius (AdjoinRoot P) p (n : ℕ) x = x ^ Nat.card K := by
    intro x
    rw [iterateFrobenius_def, hcard]
  have h2L : (2 : AdjoinRoot P) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : AdjoinRoot P) = 0 := by exact_mod_cast h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
      ((CharP.cast_eq_zero_iff (AdjoinRoot P) p 2).1 h'))
  refine ⟨Pi.mulSingle node (Units.mk0 ζ0 hζne), ?_⟩
  exact not_mem_core (algebraMap K (AdjoinRoot P)) (Units.mk0 ζ0 hζne) (AdjoinRoot.root P)
    (iterateFrobenius (AdjoinRoot P) p (n : ℕ)) (by rw [Units.val_mk0]; exact hs2) hsN hψ hcN
    hodd h2L

end CFSG.LieType.SeitzGeneration.ExcHigh

end

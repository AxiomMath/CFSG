module

public import CFSG.Fischer.Classification.PartIII.Arf.Witt
public import CFSG.Fischer.Classification.PartIII.Symp.Gauss
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.RankThree.OrthogonalInvolutions.Dickson

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S12DW

open Module QuadraticMap

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem map_add_add_self (Q : QuadraticForm (ZMod 2) V) (v x : V) :
    Q (x + v) + Q v = Q x + polar Q v x := by
  rw [polar_comm]
  unfold polar
  generalize Q (x + v) = a
  generalize Q x = b
  generalize Q v = c
  revert a b c
  decide

theorem ncard_add_polar_eq (Q : QuadraticForm (ZMod 2) V) (v : V) :
    {x | Q x + polar Q v x = 1}.ncard = {y | Q y = 1 + Q v}.ncard := by
  have himg : (fun x => x + v) '' {x | Q x + polar Q v x = 1} = {y | Q y = 1 + Q v} := by
    ext y
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    have key : ∀ a c : ZMod 2, a + c = 1 ↔ a = 1 + c := by decide
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← map_add_add_self] at hx
      exact (key _ _).mp hx
    · intro hy
      refine ⟨y - v, ?_, sub_add_cancel y v⟩
      rw [← map_add_add_self, sub_add_cancel]
      exact (key _ _).mpr hy
  rw [← himg, Set.ncard_image_of_injective _ (add_left_injective v)]

theorem exists_eq_add_polar [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : (polarBilin Q).Nondegenerate) {Q' : V → ZMod 2}
    (h0 : Q' 0 = 0) (h : ∀ x y, polar Q' x y = polar Q x y) :
    ∃ v, ∀ x, Q' x = Q x + polar Q v x := by
  have hadd : ∀ x y, Q' (x + y) - Q (x + y) = (Q' x - Q x) + (Q' y - Q y) := by
    intro x y
    have h1 := h x y
    unfold polar at h1
    linear_combination h1
  let ℓ : Module.Dual (ZMod 2) V :=
    { toFun := fun x => Q' x - Q x
      map_add' := hadd
      map_smul' := fun c x => by
        have hc : c = 0 ∨ c = 1 := by revert c; decide
        rcases hc with rfl | rfl
        · simp [h0]
        · simp }
  refine ⟨(LinearMap.BilinForm.toDual (polarBilin Q) hQ).symm ℓ, fun x => ?_⟩
  have h2 := LinearMap.BilinForm.toDual_def hQ
    (m := (LinearMap.BilinForm.toDual (polarBilin Q) hQ).symm ℓ) (n := x)
  rw [LinearEquiv.apply_symm_apply, polarBilin_apply_apply] at h2
  change Q' x - Q x = _ at h2
  linear_combination h2

theorem eq_of_add_polar_eq {Q : QuadraticForm (ZMod 2) V} (hQ : (polarBilin Q).Nondegenerate)
    {v w : V} (h : ∀ x, Q x + polar Q v x = Q x + polar Q w x) : v = w := by
  have hvw : ∀ x, polarBilin Q (v - w) x = 0 := by
    intro x
    rw [map_sub, LinearMap.sub_apply, polarBilin_apply_apply, polarBilin_apply_apply,
      add_left_cancel (h x), sub_self]
  exact sub_eq_zero.mp (hQ.1 _ hvw)

@[expose] def addPolar (Q : QuadraticForm (ZMod 2) V) (v : V) : QuadraticForm (ZMod 2) V :=
  Q + QuadraticMap.linMulLin (polarBilin Q v) (polarBilin Q v)

theorem addPolar_apply (Q : QuadraticForm (ZMod 2) V) (v x : V) :
    addPolar Q v x = Q x + polar Q v x := by
  have h : ∀ a : ZMod 2, a * a = a := by decide
  change Q x + QuadraticMap.linMulLin (polarBilin Q v) (polarBilin Q v) x = _
  rw [QuadraticMap.linMulLin_apply, polarBilin_apply_apply, h]

theorem polar_addPolar (Q : QuadraticForm (ZMod 2) V) (v x y : V) :
    polar (addPolar Q v) x y = polar Q x y := by
  have h : ∀ a b : ZMod 2, a + b + b = a := by decide
  unfold polar
  rw [addPolar_apply, addPolar_apply, addPolar_apply, polar_add_right]
  generalize polar Q v x = a
  generalize polar Q v y = b
  generalize Q (x + y) = c
  generalize Q x = d
  generalize Q y = e
  revert a b c d e
  decide

section Count

variable [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

omit [FiniteDimensional (ZMod 2) V] in
theorem polar_comp_symm {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.BilinForm.isometryGroup (polarBilin Q)) (x y : V) :
    polar (fun x => Q (g.symm x)) x y = polar Q x y := by
  have hg' := TauCeti.BilinForm.isIsometry_iff.mp
    (TauCeti.BilinForm.mem_isometryGroup.mp (inv_mem hg)) x y
  rw [polarBilin_apply_apply, polarBilin_apply_apply] at hg'
  rw [← hg']
  show Q (g.symm (x + y)) - Q (g.symm x) - Q (g.symm y) =
    Q (g.symm x + g.symm y) - Q (g.symm x) - Q (g.symm y)
  rw [map_add]

omit [FiniteDimensional (ZMod 2) V] in
theorem orthogonalGroup_le_isometryGroup :
    TauCeti.QuadraticMap.orthogonalGroup Q ≤ TauCeti.BilinForm.isometryGroup (polarBilin Q) :=
  fun g hg => TauCeti.BilinForm.mem_isometryGroup.mpr <| TauCeti.BilinForm.isIsometry_iff.mpr
    fun x y => by
      rw [polarBilin_apply_apply, polarBilin_apply_apply]
      exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg x y

omit [FiniteDimensional (ZMod 2) V] in
theorem polar_eq_zero_imp (hQ : (polarBilin Q).Nondegenerate) :
    ∀ x, (∀ y, polar Q x y = 0) → x = 0 :=
  fun x hx => hQ.1 x fun y => by rw [polarBilin_apply_apply]; exact hx y

theorem natCard_eq_four_pow {m : ℕ} (hV : finrank (ZMod 2) V = 2 * m) : Nat.card V = 4 ^ m := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hV, pow_mul]
  norm_num

theorem two_mul_ncard_ne (hQ : (polarBilin Q).Nondegenerate) {m : ℕ}
    (hV : finrank (ZMod 2) V = 2 * m) : 2 * {x | Q x = 1}.ncard ≠ Nat.card V := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have hc := natCard_eq_four_pow hV
  have h2 := CFSG.Fischer.Classification.LocalSymp.two_mul_ncard_quadratic Q
    (polar_eq_zero_imp hQ) hc
  have hpos : 0 < 2 ^ m := by positivity
  omega

theorem ncard_eq_zero_eq (Q : QuadraticForm (ZMod 2) V) :
    {x | Q x = 0}.ncard = Nat.card V - {x | Q x = 1}.ncard := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have h : {x | Q x = 0} = {x | Q x = 1}ᶜ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
    have key : ∀ a : ZMod 2, a = 0 ↔ ¬ a = 1 := by decide
    exact key _
  rw [h, Set.ncard_compl]

omit [FiniteDimensional (ZMod 2) V] in
theorem ncard_comp_symm (g : V ≃ₗ[ZMod 2] V) :
    {x | Q (g.symm x) = 1}.ncard = {x | Q x = 1}.ncard := by
  have h : (g : V → V) '' {x | Q x = 1} = {x | Q (g.symm x) = 1} := by
    ext x
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rwa [LinearEquiv.symm_apply_apply]
    · intro hx
      exact ⟨g.symm x, hx, LinearEquiv.apply_symm_apply g x⟩
  rw [← h, Set.ncard_image_of_injective _ g.injective]

theorem exists_vec (hQ : (polarBilin Q).Nondegenerate) {m : ℕ} (hV : finrank (ZMod 2) V = 2 * m)
    {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ TauCeti.BilinForm.isometryGroup (polarBilin Q)) :
    ∃ v, Q v = 0 ∧ ∀ x, Q (g.symm x) = Q x + polar Q v x := by
  obtain ⟨v, hv⟩ := exists_eq_add_polar hQ (Q' := fun x => Q (g.symm x))
    (by simp only [map_zero]) (polar_comp_symm hg)
  refine ⟨v, ?_, hv⟩
  by_contra hv0
  have hv1 : Q v = 1 := by
    have key : ∀ a : ZMod 2, ¬ a = 0 → a = 1 := by decide
    exact key _ hv0
  have h1 := ncard_comp_symm (Q := Q) g
  have hset : {x | Q (g.symm x) = 1} = {x | Q x + polar Q v x = 1} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [hv x]
  rw [hset, ncard_add_polar_eq, hv1, show (1 : ZMod 2) + 1 = 0 from rfl, ncard_eq_zero_eq] at h1
  have h2 := two_mul_ncard_ne hQ hV
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have h3 : {x | Q x = 1}.ncard ≤ Nat.card V := by
    rw [← Set.ncard_univ]
    exact Set.ncard_le_ncard (Set.subset_univ _)
  omega

theorem exists_mem_isometryGroup (hQ : (polarBilin Q).Nondegenerate) {v : V} (hv : Q v = 0) :
    ∃ g ∈ TauCeti.BilinForm.isometryGroup (polarBilin Q),
      ∀ x, Q ((g : V ≃ₗ[ZMod 2] V).symm x) = Q x + polar Q v x := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have hnd := polar_eq_zero_imp hQ
  have hnd' : ∀ x, (∀ y, polar (addPolar Q v) x y = 0) → x = 0 := fun x hx =>
    hnd x fun y => by rw [← polar_addPolar Q v]; exact hx y
  have hN : {x | addPolar Q v x = 1}.ncard = {x | Q x = 1}.ncard := by
    have hset : {x | addPolar Q v x = 1} = {x | Q x + polar Q v x = 1} := by
      ext x
      simp only [Set.mem_ofPred_eq, addPolar_apply]
    rw [hset, ncard_add_polar_eq, hv, add_zero]
  obtain ⟨L, hL⟩ := CFSG.Fischer.Classification.exists_linearEquiv_of_ncard_eq (addPolar Q v) Q
    hnd' hnd rfl hN
  have hLSp : L ∈ TauCeti.BilinForm.isometryGroup (polarBilin Q) :=
    TauCeti.BilinForm.mem_isometryGroup.mpr <| TauCeti.BilinForm.isIsometry_iff.mpr fun x y => by
      rw [polarBilin_apply_apply, polarBilin_apply_apply, ← polar_addPolar Q v x y]
      unfold polar
      show Q (L x + L y) - Q (L x) - Q (L y) = _
      rw [← map_add L x y, hL, hL, hL]
  refine ⟨L⁻¹, inv_mem hLSp, fun x => ?_⟩
  change Q (L x) = _
  rw [hL, addPolar_apply]

theorem card_orthogonalGroup_mul_ncard (hQ : (polarBilin Q).Nondegenerate) {m : ℕ}
    (hV : finrank (ZMod 2) V = 2 * m) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) * {v | Q v = 0}.ncard =
      Nat.card (TauCeti.BilinForm.isometryGroup (polarBilin Q)) := by
  classical
  set Sp := TauCeti.BilinForm.isometryGroup (polarBilin Q) with hSp
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  set H : Subgroup Sp := O.subgroupOf Sp with hH
  have hvec : ∀ g : Sp, ∃ v, Q v = 0 ∧
      ∀ x, Q ((g : V ≃ₗ[ZMod 2] V).symm x) = Q x + polar Q v x :=
    fun g => exists_vec hQ hV g.2
  choose vec hvec0 hvecQ using hvec
  have hiff : ∀ g h : Sp, vec g = vec h ↔ g⁻¹ * h ∈ H := by
    intro g h
    rw [hH, Subgroup.mem_subgroupOf, hO, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    constructor
    · intro e y
      show Q ((g : V ≃ₗ[ZMod 2] V).symm ((h : V ≃ₗ[ZMod 2] V) y)) = Q y
      rw [hvecQ g, e, ← hvecQ h, LinearEquiv.symm_apply_apply]
    · intro hgh
      refine eq_of_add_polar_eq hQ fun x => ?_
      rw [← hvecQ g x, ← hvecQ h x]
      have := hgh ((h : V ≃ₗ[ZMod 2] V).symm x)
      change Q ((g : V ≃ₗ[ZMod 2] V).symm
        ((h : V ≃ₗ[ZMod 2] V) ((h : V ≃ₗ[ZMod 2] V).symm x))) = _ at this
      rwa [LinearEquiv.apply_symm_apply] at this
  let F : Sp ⧸ H → ({v | Q v = 0} : Set V) := Quotient.lift (fun g => ⟨vec g, hvec0 g⟩)
    (fun g h hgh => Subtype.ext ((hiff g h).mpr (QuotientGroup.leftRel_apply.mp hgh)))
  have hF : Function.Bijective F := by
    constructor
    · intro a b hab
      induction a using QuotientGroup.induction_on with | H g => ?_
      induction b using QuotientGroup.induction_on with | H h => ?_
      exact QuotientGroup.eq.mpr ((hiff g h).mp (congrArg Subtype.val hab))
    · rintro ⟨v, hv⟩
      obtain ⟨g, hg, hgQ⟩ := exists_mem_isometryGroup hQ hv
      refine ⟨QuotientGroup.mk ⟨g, hg⟩, Subtype.ext ?_⟩
      refine eq_of_add_polar_eq hQ fun x => ?_
      show Q x + polar Q (vec ⟨g, hg⟩) x = Q x + polar Q v x
      rw [← hvecQ ⟨g, hg⟩ x, ← hgQ x]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup H
  rw [Nat.card_congr (Equiv.ofBijective F hF), Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    orthogonalGroup_le_isometryGroup).toEquiv, Nat.card_coe_set_eq] at h1
  rw [h1, mul_comm]

omit [FiniteDimensional (ZMod 2) V] in
theorem polarBilin_isAlt (Q : QuadraticForm (ZMod 2) V) : (polarBilin Q).IsAlt := fun x => by
  rw [polarBilin_apply_apply]
  exact CFSG.Fischer.Classification.Arf.polar_self_zmod2 Q x

theorem card_orthogonalGroup_mul_ncard_eq (hQ : (polarBilin Q).Nondegenerate) {m : ℕ}
    (hV : finrank (ZMod 2) V = 2 * m) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) * {v | Q v = 0}.ncard =
      2 ^ (m ^ 2) * ∏ j ∈ Finset.Icc 1 m, (2 ^ (2 * j) - 1) := by
  rw [card_orthogonalGroup_mul_ncard hQ hV,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_isometryGroup m (polarBilin Q)
      (polarBilin_isAlt Q) hQ hV, Nat.card_zmod]

theorem card_orthogonalGroup_eq (hQ : (polarBilin Q).Nondegenerate) [Nontrivial V] :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) =
      2 * Nat.card (CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ) := by
  have h1 := Subgroup.card_mul_index
    ((CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ).subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup Q))
  rw [← Subgroup.relIndex, CFSG.RankThree.OrthogonalInvolutions.relIndex_omegaGroup Q hQ,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (CFSG.RankThree.OrthogonalInvolutions.omegaGroup_le Q hQ)).toEquiv] at h1
  rw [← h1, mul_comm]

end Count

theorem ncard_eq_of_card_omegaGroup_dvd [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} {V' : Type*} [AddCommGroup V'] [Module (ZMod 2) V']
    [FiniteDimensional (ZMod 2) V'] {Q' : QuadraticForm (ZMod 2) V'}
    (hQ : (polarBilin Q).Nondegenerate) (hQ' : (polarBilin Q').Nondegenerate) {m : ℕ}
    (hm : 2 ≤ m) (hV : finrank (ZMod 2) V = 2 * m) (hV' : finrank (ZMod 2) V' = 2 * m)
    (h : Nat.card (CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q' hQ') ∣
      Nat.card (CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ)) :
    {v | Q v = 1}.ncard = {v | Q' v = 1}.ncard := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite V' := Module.finite_of_finite (ZMod 2)
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have : Nontrivial V' := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have : Finite (V' ≃ₗ[ZMod 2] V') :=
    Finite.of_injective (fun g : V' ≃ₗ[ZMod 2] V' => (g : V' → V'))
      fun _ _ e => LinearEquiv.ext (congrFun e)
  obtain ⟨k, hk⟩ := h
  have e1 := card_orthogonalGroup_mul_ncard_eq hQ hV
  have e2 := card_orthogonalGroup_mul_ncard_eq hQ' hV'
  rw [card_orthogonalGroup_eq hQ, ncard_eq_zero_eq, natCard_eq_four_pow hV] at e1
  rw [card_orthogonalGroup_eq hQ', ncard_eq_zero_eq, natCard_eq_four_pow hV'] at e2
  rw [hk] at e1
  have hpos : 0 < Nat.card (CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q' hQ') :=
    Nat.card_pos
  have hc := CFSG.Fischer.Classification.LocalSymp.two_mul_ncard_quadratic Q
    (polar_eq_zero_imp hQ) (natCard_eq_four_pow hV)
  have hc' := CFSG.Fischer.Classification.LocalSymp.two_mul_ncard_quadratic Q'
    (polar_eq_zero_imp hQ') (natCard_eq_four_pow hV')
  set N := {v | Q v = 1}.ncard
  set N' := {v | Q' v = 1}.ncard
  set w := Nat.card (CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q' hQ')
  set a := 2 ^ m with ha
  have ha4 : 4 ≤ a := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hA : 4 ^ m = a * a := by rw [ha, ← mul_pow]; norm_num
  rw [hA] at hc hc' e1 e2
  have hkey : k * (a * a - N) = a * a - N' := by
    have e3 : 2 * w * (k * (a * a - N)) = 2 * w * (a * a - N') :=
      calc 2 * w * (k * (a * a - N)) = 2 * (w * k) * (a * a - N) := by ring
        _ = _ := e1
        _ = 2 * w * (a * a - N') := e2.symm
    exact Nat.eq_of_mul_eq_mul_left (by positivity) e3
  have h4a : 4 * a ≤ a * a := Nat.mul_le_mul_right a ha4
  by_contra hne
  rcases hc with h1 | h1 <;> rcases hc' with h2 | h2
  · omega
  ·
    have hz : 2 * (a * a - N) = a * a + a := by omega
    have hz' : 2 * (a * a - N') = a * a - a := by omega
    have h3 : k * (a * a + a) = a * a - a := by
      rw [← hz, ← hz', ← hkey]
      ring
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · rw [hk0, zero_mul] at h3
      omega
    · have : a * a + a ≤ k * (a * a + a) := Nat.le_mul_of_pos_left _ hk0
      omega
  ·
    have hz : 2 * (a * a - N) = a * a - a := by omega
    have hz' : 2 * (a * a - N') = a * a + a := by omega
    have h3 : k * (a * a - a) = a * a + a := by
      rw [← hz, ← hz', ← hkey]
      ring
    have hle : a ≤ a * a := by omega
    set A := a * a with hAdef
    have h4 : (k : ℤ) * ((A : ℤ) - a) = (A : ℤ) + a := by
      have := congrArg (fun n : ℕ => (n : ℤ)) h3
      push_cast [Nat.cast_sub hle] at this
      linarith
    have hA4 : (4 : ℤ) * a ≤ A := by exact_mod_cast h4a
    have ha4' : (4 : ℤ) ≤ a := by exact_mod_cast ha4
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with hk | hk | hk | hk
    · subst hk
      push_cast at h4
      linarith
    · subst hk
      push_cast at h4
      linarith
    · subst hk
      push_cast at h4
      linarith
    · have hk3 : (3 : ℤ) ≤ k := by exact_mod_cast hk
      nlinarith [mul_nonneg (sub_nonneg.mpr hk3) (show (0 : ℤ) ≤ A - a by linarith)]
  · omega

end CFSG.LargeExtraspecial.S12DW

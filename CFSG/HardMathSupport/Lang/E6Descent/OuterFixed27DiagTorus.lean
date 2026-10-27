module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27DiagGroup
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27DiagArith
public import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter
public import CFSG.LieType.Chevalley.LangFiniteNormalizerOddIndex
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27DiagWeyl

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Lang.E6Descent

namespace DiagTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Timmesfeld.ExceptionalOrders
  CFSG.SeitzReduction.E6Pilot CFSG.Open CFSG.RankThree.E6 CFSG.HardMathSupport.Lang.E6Descent.DiagWeyl

variable {K : Type} [Field K]

@[expose] def Dgrp (K : Type) [Field K] : Subgroup (ModGL Tag.E6 K) :=
  (rootDiagUnitHom Tag.E6 K).range

theorem rootDiagUnitHom_apply (a : Fin Tag.E6.rank → Kˣ) :
    rootDiagUnitHom Tag.E6 K a = rootDiagUnit Tag.E6 a := rfl

theorem rootDiagUnit_mem_Dgrp (a : Fin Tag.E6.rank → Kˣ) : rootDiagUnit Tag.E6 a ∈ Dgrp K :=
  ⟨a, rfl⟩

theorem Dgrp_comm {x y : ModGL Tag.E6 K} (hx : x ∈ Dgrp K) (hy : y ∈ Dgrp K) : x * y = y * x := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  rw [rootDiagUnitHom_apply, rootDiagUnitHom_apply, ← rootDiagUnit_mul, ← rootDiagUnit_mul,
    mul_comm]

theorem rootDiagUnit_injective :
    Function.Injective (rootDiagUnit Tag.E6 : (Fin Tag.E6.rank → Kˣ) → ModGL Tag.E6 K) := by
  intro a b h
  refine rootDiagAutHom_injective (τ := Tag.E6) (K := K) (MulEquiv.ext fun g => Subtype.ext ?_)
  change ((rootDiagAut Tag.E6 K a g : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
    ((rootDiagAut Tag.E6 K b g : adjointGroup Tag.E6 K) : ModGL Tag.E6 K)
  rw [coe_rootDiagAut, coe_rootDiagAut, h]

theorem card_Dgrp [Finite K] : Nat.card (Dgrp K) = (Nat.card K - 1) ^ 6 := by
  have h := Nat.card_congr (MonoidHom.ofInjective (f := rootDiagUnitHom Tag.E6 K)
    rootDiagUnit_injective).toEquiv
  change Nat.card (Dgrp K) = _
  rw [Dgrp, ← h]
  show Nat.card (Fin Tag.E6.rank → Kˣ) = _
  rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.card_units]
  rfl

theorem torusGroup_le_Dgrp : torusGroup Tag.E6 K ≤ Dgrp K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨i, t⟩, rfl⟩
  change torusElt Tag.E6 K i t ∈ Dgrp K
  rw [torusElt_eq_rootDiagUnit]
  exact rootDiagUnit_mem_Dgrp _

theorem torusGroup_le_adjointGroup : torusGroup Tag.E6 K ≤ adjointGroup Tag.E6 K :=
  (Subgroup.closure_le _).2 (by
    rintro _ ⟨⟨i, t⟩, rfl⟩
    exact torusElt_mem_adjointGroup i t)

theorem torusGroup_le_monomialSubgroup : torusGroup Tag.E6 K ≤ monomialSubgroup Tag.E6 K :=
  le_sup_left

theorem card_torusGroup_mul_three [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    Nat.card (torusGroup Tag.E6 K) * 3 = Nat.card (Dgrp K) := by
  have h := card_torusGroup_E6 (K := K)
  rw [Nat.gcd_eq_right h3] at h
  rw [card_Dgrp, ← h]

theorem Dgrp_le_normalizer_adjoint :
    Dgrp K ≤ Subgroup.normalizer (adjointGroup Tag.E6 K : Set (ModGL Tag.E6 K)) := by
  rintro _ ⟨a, rfl⟩
  exact (root_diagonal_conjugation Tag.E6 K a).2.2

theorem conj_mem_monomial_of_Dgrp {d : ModGL Tag.E6 K} (hd : d ∈ Dgrp K)
    {m : ModGL Tag.E6 K} (hm : m ∈ monomialSubgroup Tag.E6 K) :
    d * m * d⁻¹ ∈ monomialSubgroup Tag.E6 K := by
  obtain ⟨a, rfl⟩ := hd
  rw [rootDiagUnitHom_apply]
  obtain ⟨w, k, hk, rfl⟩ := monomialSubgroup_le_torusWeylCosets hm
  obtain ⟨t, ht, hconj⟩ := exists_conj_canonicalRep (K := K) a w
  have h : rootDiagUnit Tag.E6 a * (k * canonicalRep (coxeterSystem Tag.E6) K w) *
      (rootDiagUnit Tag.E6 a)⁻¹ = k * (t * canonicalRep (coxeterSystem Tag.E6) K w) := by
    calc rootDiagUnit Tag.E6 a * (k * canonicalRep (coxeterSystem Tag.E6) K w) *
          (rootDiagUnit Tag.E6 a)⁻¹ =
        (rootDiagUnit Tag.E6 a * k * (rootDiagUnit Tag.E6 a)⁻¹) *
          (rootDiagUnit Tag.E6 a * canonicalRep (coxeterSystem Tag.E6) K w *
            (rootDiagUnit Tag.E6 a)⁻¹) := by group
      _ = _ := by rw [conj_rootDiagUnit_of_mem_torusGroup a hk, hconj]
  rw [h]
  exact mul_mem (Subgroup.mem_sup_left hk) (mul_mem (Subgroup.mem_sup_left ht)
    (Subgroup.mem_sup_right (canonicalRep_mem_closure _ _ w)))

theorem Dgrp_le_normalizer_monomial :
    Dgrp K ≤ Subgroup.normalizer (monomialSubgroup Tag.E6 K : Set (ModGL Tag.E6 K)) := by
  intro d hd
  refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => conj_mem_monomial_of_Dgrp hd hh,
    fun hh => ?_⟩
  have := conj_mem_monomial_of_Dgrp (inv_mem hd) hh
  simpa [mul_assoc] using this

section Theta

@[expose] def theta (ζ : Kˣ) (a : ZMod 3) : Kˣ := ζ ^ a.val

theorem theta_zero (ζ : Kˣ) : theta ζ 0 = 1 := by
  simp [theta]

theorem theta_add {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (a b : ZMod 3) :
    theta ζ (a + b) = theta ζ a * theta ζ b := by
  unfold theta
  rw [ZMod.val_add, ← pow_add]
  exact (pow_eq_pow_mod _ hζ).symm

@[expose] def thetaHom {ζ : Kˣ} (hζ : ζ ^ 3 = 1) : Multiplicative (ZMod 3) →* Kˣ where
  toFun a := theta ζ (Multiplicative.toAdd a)
  map_one' := theta_zero ζ
  map_mul' _ _ := theta_add hζ _ _

theorem theta_zpow {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (a : ZMod 3) (n : ℤ) :
    theta ζ a ^ n = theta ζ ((n : ZMod 3) * a) := by
  have h := map_zpow (thetaHom hζ) (Multiplicative.ofAdd a) n
  rw [← ofAdd_zsmul, zsmul_eq_mul] at h
  exact h.symm

theorem theta_sum {ζ : Kˣ} (hζ : ζ ^ 3 = 1) {ι : Type*} (s : Finset ι) (f : ι → ZMod 3) :
    theta ζ (∑ i ∈ s, f i) = ∏ i ∈ s, theta ζ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [theta_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, theta_add hζ, ih]

theorem theta_injective {ζ : Kˣ} (hζ : orderOf ζ = 3) : Function.Injective (theta ζ) := by
  intro a b h
  unfold theta at h
  rw [pow_inj_mod, hζ, Nat.mod_eq_of_lt (ZMod.val_lt a), Nat.mod_eq_of_lt (ZMod.val_lt b)] at h
  exact ZMod.val_injective 3 h

@[expose] def dotZ (u : Fin Tag.E6.rank → ZMod 3) (x : Fin Tag.E6.rank → ℤ) : ZMod 3 :=
  ∑ i, (x i : ZMod 3) * u i

theorem rootChar_theta {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (u : Fin Tag.E6.rank → ZMod 3)
    (x : Fin Tag.E6.rank → ℤ) :
    rootChar (fun i => theta ζ (u i)) x = theta ζ (dotZ u x) := by
  unfold rootChar dotZ
  rw [theta_sum hζ]
  exact Finset.prod_congr rfl fun i _ => theta_zpow hζ _ _

theorem dotZ_smul {w : WeylGroup Tag.E6} {u : Fin Tag.E6.rank → ZMod 3}
    (hu : (cm w).transpose.mulVec u = u) (v : Fin Tag.E6.rank → ℤ) :
    dotZ u (w • v) = dotZ u v := by
  have h1 : (fun i => ((w • v) i : ZMod 3)) = (cm w).mulVec (fun i => (v i : ZMod 3)) := by
    rw [← weylMatrix_mulVec]
    funext i
    simp only [Matrix.mulVec, dotProduct, cm, Matrix.map_apply, Int.coe_castRingHom, Int.cast_sum,
      Int.cast_mul]
  have h2 : dotZ u (w • v) = (fun i => ((w • v) i : ZMod 3)) ⬝ᵥ u := rfl
  have h3 : dotZ u v = (fun i => (v i : ZMod 3)) ⬝ᵥ u := rfl
  rw [h2, h3, h1, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hu,
    dotProduct_comm]

end Theta

section Fix

variable {ζ : Kˣ}

@[expose] def Psi (hζ : ζ ^ 3 = 1) :
    Multiplicative (Fin Tag.E6.rank → ZMod 3) →* ModGL Tag.E6 K where
  toFun u := rootDiagUnit Tag.E6 (fun i => theta ζ (Multiplicative.toAdd u i))
  map_one' := by
    have : (fun i => theta ζ (Multiplicative.toAdd
        (1 : Multiplicative (Fin Tag.E6.rank → ZMod 3)) i)) = 1 := by
      funext i
      exact theta_zero ζ
    rw [this]
    exact rootDiagUnit_one
  map_mul' u v := by
    rw [← rootDiagUnit_mul]
    congr 1
    funext i
    exact theta_add hζ _ _

theorem Psi_apply (hζ : ζ ^ 3 = 1) (u : Multiplicative (Fin Tag.E6.rank → ZMod 3)) :
    Psi (K := K) hζ u = rootDiagUnit Tag.E6 (fun i => theta ζ (Multiplicative.toAdd u i)) := rfl

theorem Psi_mem_Dgrp (hζ : ζ ^ 3 = 1) (u : Multiplicative (Fin Tag.E6.rank → ZMod 3)) :
    Psi (K := K) hζ u ∈ Dgrp K :=
  rootDiagUnit_mem_Dgrp _

theorem Psi_injective (hζ : ζ ^ 3 = 1) (hζ' : orderOf ζ = 3) :
    Function.Injective (Psi (K := K) hζ) := by
  intro u v h
  have h' := rootDiagUnit_injective h
  have : Multiplicative.toAdd u = Multiplicative.toAdd v := by
    funext i
    exact theta_injective hζ' (congrFun h' i)
  exact this

theorem Psi_pow_three (hζ : ζ ^ 3 = 1) (u : Multiplicative (Fin Tag.E6.rank → ZMod 3)) :
    Psi (K := K) hζ u ^ 3 = 1 := by
  rw [← map_pow]
  have : u ^ 3 = 1 := by
    apply Multiplicative.toAdd.injective
    funext i
    simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply]
    generalize Multiplicative.toAdd u i = a
    revert a
    decide
  rw [this, map_one]

theorem conj_Psi (hζ : ζ ^ 3 = 1) (w : WeylGroup Tag.E6) (u : Fin Tag.E6.rank → ZMod 3)
    (hu : (cm w).transpose.mulVec u = u) :
    canonicalRep (coxeterSystem Tag.E6) K w * Psi hζ (Multiplicative.ofAdd u) *
      (canonicalRep (coxeterSystem Tag.E6) K w)⁻¹ = Psi hζ (Multiplicative.ofAdd u) := by
  refine ((rootDiagUnit_eq_conj_canonicalRep_iff _ _ w).2 fun v => ?_).symm
  simp only [toAdd_ofAdd]
  rw [rootChar_theta hζ, rootChar_theta hζ, dotZ_smul hu]

@[expose] def fixSub (w : WeylGroup Tag.E6) :
    Subgroup (Multiplicative (Fin Tag.E6.rank → ZMod 3)) where
  carrier := {u | (cm w).transpose.mulVec (Multiplicative.toAdd u) = Multiplicative.toAdd u}
  one_mem' := by
    show (cm w).transpose.mulVec (Multiplicative.toAdd 1) = Multiplicative.toAdd 1
    simp
  mul_mem' := by
    intro a b ha hb
    show (cm w).transpose.mulVec (Multiplicative.toAdd (a * b)) = Multiplicative.toAdd (a * b)
    have ha' : (cm w).transpose.mulVec (Multiplicative.toAdd a) = Multiplicative.toAdd a := ha
    have hb' : (cm w).transpose.mulVec (Multiplicative.toAdd b) = Multiplicative.toAdd b := hb
    rw [toAdd_mul, Matrix.mulVec_add, ha', hb']
  inv_mem' := by
    intro a ha
    show (cm w).transpose.mulVec (Multiplicative.toAdd a⁻¹) = Multiplicative.toAdd a⁻¹
    have ha' : (cm w).transpose.mulVec (Multiplicative.toAdd a) = Multiplicative.toAdd a := ha
    rw [toAdd_inv]
    exact (Matrix.mulVec_neg _ _).trans (by rw [ha']; rfl)

theorem card_fixSub (w : WeylGroup Tag.E6) : Nat.card (fixSub w) = Nat.card (FixSet w) :=
  Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun _ => Iff.rfl)

end Fix

section Index

variable [Finite K]

theorem inf_Dgrp_adjoint_eq (h3 : 3 ∣ Nat.card K - 1) (hD : ¬ Dgrp K ≤ adjointGroup Tag.E6 K) :
    Dgrp K ⊓ adjointGroup Tag.E6 K = torusGroup Tag.E6 K := by
  have hHT : torusGroup Tag.E6 K ≤ Dgrp K ⊓ adjointGroup Tag.E6 K :=
    le_inf torusGroup_le_Dgrp torusGroup_le_adjointGroup
  have hTD : Dgrp K ⊓ adjointGroup Tag.E6 K ≤ Dgrp K := inf_le_left
  have hcard := card_torusGroup_mul_three (K := K) h3
  obtain ⟨j, hj⟩ := Subgroup.card_dvd_of_le hHT
  obtain ⟨i, hi⟩ := Subgroup.card_dvd_of_le hTD
  have hH : 0 < Nat.card (torusGroup Tag.E6 K) := Nat.card_pos
  have hji : j * i = 3 := by
    have : Nat.card (torusGroup Tag.E6 K) * 3 =
        Nat.card (torusGroup Tag.E6 K) * (j * i) := by
      rw [hcard, hi, hj]
      ring
    exact (Nat.eq_of_mul_eq_mul_left hH this).symm
  have hi1 : i ≠ 1 := by
    rintro rfl
    refine hD ?_
    have := Subgroup.eq_of_le_of_card_ge hTD (by rw [hi, mul_one])
    rw [← this]
    exact inf_le_right
  have hj1 : j = 1 := by
    have hi3 : i ∣ 3 := Dvd.intro_left j hji
    rcases (Nat.dvd_prime Nat.prime_three).1 hi3 with h | h
    · exact absurd h hi1
    · subst h
      omega
  have := Subgroup.eq_of_le_of_card_ge hHT (by rw [hj, hj1, mul_one])
  exact this.symm

theorem inf_Dgrp_monomial_eq (h3 : 3 ∣ Nat.card K - 1) (hD : ¬ Dgrp K ≤ adjointGroup Tag.E6 K) :
    Dgrp K ⊓ monomialSubgroup Tag.E6 K = torusGroup Tag.E6 K :=
  le_antisymm
    ((inf_le_inf_left _ monomialSubgroup_le_adjointGroup').trans (inf_Dgrp_adjoint_eq h3 hD).le)
    (le_inf torusGroup_le_Dgrp torusGroup_le_monomialSubgroup)

theorem relIndex_adjoint_Dgrp (h3 : 3 ∣ Nat.card K - 1) (hD : ¬ Dgrp K ≤ adjointGroup Tag.E6 K) :
    (adjointGroup Tag.E6 K).relIndex (Dgrp K) = 3 := by
  have h := Subgroup.relIndex_mul_card (adjointGroup Tag.E6 K) (Dgrp K)
  rw [inf_comm, inf_Dgrp_adjoint_eq h3 hD, ← card_torusGroup_mul_three h3] at h
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (by rw [mul_comm]; exact h)

theorem not_three_dvd_relIndex_monomial (h3 : 3 ∣ Nat.card K - 1) :
    ¬ 3 ∣ (monomialSubgroup Tag.E6 K).relIndex (adjointGroup Tag.E6 K) := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  set r := (monomialSubgroup Tag.E6 K).relIndex (adjointGroup Tag.E6 K) with hr
  have hrel := Subgroup.relIndex_mul_card (monomialSubgroup Tag.E6 K) (adjointGroup Tag.E6 K)
  rw [inf_of_le_left monomialSubgroup_le_adjointGroup', card_monomialSubgroup, card_weylGroup_E6,
    card_adjointGroup_E6] at hrel
  have hH := card_torusGroup_E6 (K := K)
  rw [Nat.gcd_eq_right h3] at hH
  have hnum := ordE6_mul_gcd (Nat.card K)
  rw [Nat.gcd_eq_left h3] at hnum
  refine three_not_dvd_of_mul_eq (Nat.card K) r hq h3 ?_
  rw [← hnum, ← hH, ← hrel]
  ring

end Index

section Main

variable [Finite K]

theorem mapsRootLines_rootDiagUnit (a : Fin Tag.E6.rank → Kˣ) :
    MapsRootLines (rootDiagUnit Tag.E6 a : (Module.End K (RootModule Tag.E6 K))ˣ) 1 := by
  intro α hα
  refine ⟨rootChar a α, ?_⟩
  rw [one_smul]
  exact rootDiag_rootVec a hα

theorem mapsRootLines_of_mem_Dgrp {y : ModGL Tag.E6 K} (hy : y ∈ Dgrp K) :
    MapsRootLines (y : (Module.End K (RootModule Tag.E6 K))ˣ) 1 := by
  obtain ⟨a, rfl⟩ := hy
  exact mapsRootLines_rootDiagUnit a

theorem weyl_pow_three_eq_one {y : ModGL Tag.E6 K} {w : WeylGroup Tag.E6}
    (hy : MapsRootLines (y : (Module.End K (RootModule Tag.E6 K))ˣ) w) (hy3 : y ^ 3 = 1) :
    w ^ 3 = 1 := by
  have h := (hy.mul hy).mul hy
  rw [← pow_three', hy3, ← pow_three'] at h
  exact MapsRootLines.unique h mapsRootLines_one |>.trans (by rfl)

theorem weyl_eq_one_of_mem_Dgrp {y : ModGL Tag.E6 K} {w : WeylGroup Tag.E6} (hy : y ∈ Dgrp K)
    (hyw : MapsRootLines (y : (Module.End K (RootModule Tag.E6 K))ˣ) w) : w = 1 :=
  MapsRootLines.unique hyw (mapsRootLines_of_mem_Dgrp hy)

theorem exists_cube_root (h3 : 3 ∣ Nat.card K - 1) : ∃ ζ : Kˣ, ζ ^ 3 = 1 ∧ orderOf ζ = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype Kˣ := Fintype.ofFinite _
  have hdvd : 3 ∣ Fintype.card Kˣ := by
    rw [← Nat.card_eq_fintype_card, Nat.card_units]
    exact h3
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card 3 hdvd
  exact ⟨ζ, by rw [← hζ]; exact pow_orderOf_eq_one ζ, hζ⟩

theorem exists_fixed_group {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (hζ' : orderOf ζ = 3)
    {w : WeylGroup Tag.E6} (hw3 : w ^ 3 = 1) :
    ∃ F : Subgroup (ModGL Tag.E6 K), F ≤ Dgrp K ∧ (∀ f ∈ F, f ^ 3 = 1) ∧
      (∀ f ∈ F, ∀ d ∈ Dgrp K, f * (d * canonicalRep (coxeterSystem Tag.E6) K w) =
        (d * canonicalRep (coxeterSystem Tag.E6) K w) * f) ∧
      27 ≤ Nat.card F ∧ (w = 1 → 81 ≤ Nat.card F) := by
  have hcard : Nat.card ((fixSub w).map (Psi (K := K) hζ)) = Nat.card (FixSet w) := by
    rw [Subgroup.card_map_of_injective (Psi_injective hζ hζ'), card_fixSub]
  obtain ⟨h27, h81⟩ := card_fixed_ge' hw3
  refine ⟨(fixSub w).map (Psi hζ), ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨u, -, rfl⟩
    exact Psi_mem_Dgrp hζ u
  · rintro _ ⟨u, -, rfl⟩
    exact Psi_pow_three hζ u
  · rintro _ ⟨u, hu, rfl⟩ d hd
    have hc := conj_Psi (K := K) hζ w (Multiplicative.toAdd u) hu
    rw [ofAdd_toAdd] at hc
    have hc' : canonicalRep (coxeterSystem Tag.E6) K w * Psi hζ u =
        Psi hζ u * canonicalRep (coxeterSystem Tag.E6) K w :=
      mul_inv_eq_iff_eq_mul.1 hc
    have hcd := Dgrp_comm (Psi_mem_Dgrp (K := K) hζ u) hd
    calc Psi hζ u * (d * canonicalRep (coxeterSystem Tag.E6) K w) =
        (Psi hζ u * d) * canonicalRep (coxeterSystem Tag.E6) K w := by group
      _ = d * (Psi hζ u * canonicalRep (coxeterSystem Tag.E6) K w) := by rw [hcd]; group
      _ = d * (canonicalRep (coxeterSystem Tag.E6) K w * Psi hζ u) := by rw [hc']
      _ = (d * canonicalRep (coxeterSystem Tag.E6) K w) * Psi hζ u := by group
  · rw [hcard]
    exact h27
  · intro hw1
    rw [hcard]
    exact h81 hw1

theorem diag_main (h3 : 3 ∣ Nat.card K - 1) {x : ModGL Tag.E6 K}
    (hxA : x ∈ Dgrp K ⊔ adjointGroup Tag.E6 K) (hxC : x ∉ adjointGroup Tag.E6 K)
    (hx3 : x ^ 3 = 1) :
    27 ∣ Nat.card ↥(Subgroup.centralizer {x} ⊓ adjointGroup Tag.E6 K) := by
  classical
  have : Finite (ModGL Tag.E6 K) := finite_modGL
  have hDC : ¬ Dgrp K ≤ adjointGroup Tag.E6 K := fun h =>
    hxC (by rw [sup_eq_right.2 h] at hxA; exact hxA)
  have hinf : Dgrp K ⊓ adjointGroup Tag.E6 K = Dgrp K ⊓ monomialSubgroup Tag.E6 K :=
    (inf_Dgrp_adjoint_eq h3 hDC).trans (inf_Dgrp_monomial_eq h3 hDC).symm
  obtain ⟨u, huA, d, hd, m, hm, hdm⟩ := DiagGroup.exists_conj_mem_mul
    (adjointGroup Tag.E6 K) (monomialSubgroup Tag.E6 K) (Dgrp K)
    monomialSubgroup_le_adjointGroup' Dgrp_le_normalizer_adjoint Dgrp_le_normalizer_monomial hinf
    (not_three_dvd_relIndex_monomial h3) hxA hx3
  have hy3 : (u⁻¹ * x * u) ^ 3 = 1 := by
    have := conj_pow (a := u⁻¹) (b := x) (i := 3)
    rw [inv_inv] at this
    rw [this, hx3]
    simp
  obtain ⟨w, k, hk, rfl⟩ := monomialSubgroup_le_torusWeylCosets hm
  have hd1 : d * k ∈ Dgrp K := mul_mem hd (torusGroup_le_Dgrp hk)
  have hy : u⁻¹ * x * u = (d * k) * canonicalRep (coxeterSystem Tag.E6) K w := by
    rw [hdm, mul_assoc]
  have hyw : MapsRootLines ((u⁻¹ * x * u : ModGL Tag.E6 K) :
      (Module.End K (RootModule Tag.E6 K))ˣ) w := by
    rw [hy]
    have := (mapsRootLines_of_mem_Dgrp hd1).mul (mapsRootLines_canonicalRep (R := K) w)
    rwa [one_mul] at this
  have hw3 := weyl_pow_three_eq_one hyw hy3
  obtain ⟨ζ, hζ, hζ'⟩ := exists_cube_root (K := K) h3
  obtain ⟨F, hFD, hF3, hFy, hF27, hF81⟩ := exists_fixed_group (K := K) hζ hζ' hw3
  have hnorm : Dgrp K ⊔ adjointGroup Tag.E6 K ≤
      Subgroup.normalizer (adjointGroup Tag.E6 K : Set (ModGL Tag.E6 K)) :=
    sup_le Dgrp_le_normalizer_adjoint Subgroup.le_normalizer
  have hCA : (adjointGroup Tag.E6 K).relIndex (Dgrp K ⊔ adjointGroup Tag.E6 K) ≤ 3 := by
    rw [DiagGroup.relIndex_sup_right_of_le_normalizer _ _ Dgrp_le_normalizer_adjoint,
      relIndex_adjoint_Dgrp h3 hDC]
  have hyA : u⁻¹ * x * u ∈ Dgrp K ⊔ adjointGroup Tag.E6 K :=
    mul_mem (mul_mem (inv_mem huA) hxA) huA
  have key := DiagGroup.twentySeven_dvd_card_centralizer (adjointGroup Tag.E6 K)
    (Dgrp K ⊔ adjointGroup Tag.E6 K) F hy3 hyA (hFD.trans le_sup_left) hCA hF3
    (fun f hf => by
      have := hFy f hf (d * k) hd1
      rw [hy]
      exact this)
    hF27 (fun hyF => by
      have hyD : u⁻¹ * x * u ∈ Dgrp K := hFD hyF
      exact hF81 (weyl_eq_one_of_mem_Dgrp hyD hyw))
  rw [DiagGroup.card_centralizer_inf_conj _ (hnorm huA)] at key
  exact key

end Main

end DiagTorus

end CFSG.HardMathSupport.Lang.E6Descent

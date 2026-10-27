module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndDefs
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.DSFactsModel
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaAutFusion
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndCentralizer

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaInputs

open Subgroup
open CFSG.ComponentClassification.PerfectAutomorphisms (onCenterQuotient onCenterQuotient_apply_mk)

section Lift

variable {Q : Type*} [Group Q] [Finite Q]

omit [Finite Q] in
theorem exists_fixed_lift (hodd : Odd (Nat.card (center Q))) (α : MulAut Q)
    (hα : ∀ q, α (α q) = q) (x : Q)
    (hx : onCenterQuotient α (QuotientGroup.mk' (center Q) x) = QuotientGroup.mk' (center Q) x) :
    ∃ z ∈ center Q, α (x * z) = x * z := by
  rw [onCenterQuotient_apply_mk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq] at hx
  set c := x⁻¹ * α x with hc
  have hcZ : c ∈ center Q := by
    have : c = ((α x)⁻¹ * x)⁻¹ := by rw [hc, mul_inv_rev, inv_inv]
    exact this ▸ inv_mem hx
  have hαx : α x = x * c := by rw [hc, mul_inv_cancel_left]
  have hαc : α c = c⁻¹ := by
    have h1 : x = x * c * α c := by
      conv_lhs => rw [← hα x, hαx]
      rw [map_mul, hαx]
    rw [eq_inv_iff_mul_eq_one]
    have h2 : x * c * α c = x * (α c * c) := by
      rw [mul_assoc, ← mem_center_iff.mp hcZ (α c)]
    exact mul_left_cancel (a := x) (by rw [mul_one, ← h2, ← h1])
  obtain ⟨k, hk⟩ := hodd
  have hcn : c ^ (2 * k + 1) = 1 := by
    have := pow_card_eq_one' (G := center Q) (x := ⟨c, hcZ⟩)
    rw [hk] at this
    exact congrArg Subtype.val this
  refine ⟨c ^ (k + 1), pow_mem hcZ _, ?_⟩
  rw [map_mul, hαx, map_pow, hαc, inv_pow, mul_assoc]
  congr 1
  rw [mul_inv_eq_iff_eq_mul, ← pow_add, show k + 1 + (k + 1) = 2 * k + 1 + 1 by ring, pow_succ,
    hcn, one_mul]

omit [Finite Q] in
theorem eq_one_of_mem_center_of_pow (hodd : Odd (Nat.card (center Q))) {w : Q}
    (hw : w ∈ center Q) {n : ℕ} (hn : w ^ 2 ^ n = 1) : w = 1 := by
  have h1 : orderOf w ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  have h2 : orderOf w ∣ Nat.card (center Q) := by
    have := orderOf_dvd_natCard (⟨w, hw⟩ : center Q)
    rwa [Subgroup.orderOf_mk] at this
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  rcases m with _ | m
  · rwa [pow_zero, orderOf_eq_one_iff] at hm
  · exfalso
    rw [hm, pow_succ] at h2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (dvd_of_mul_left_dvd h2))

@[expose] def fixedOver (α : MulAut Q) (E : Subgroup (Q ⧸ center Q)) : Subgroup Q where
  carrier := {w | QuotientGroup.mk' (center Q) w ∈ E ∧ α w = w}
  mul_mem' ha hb := ⟨by rw [map_mul]; exact mul_mem ha.1 hb.1, by rw [map_mul, ha.2, hb.2]⟩
  one_mem' := ⟨by rw [map_one]; exact one_mem _, map_one α⟩
  inv_mem' ha := ⟨by rw [map_inv]; exact inv_mem ha.1, by rw [map_inv, ha.2]⟩

theorem exists_fixed_elementary_lift (hodd : Odd (Nat.card (center Q))) (α : MulAut Q)
    (hα : ∀ q, α (α q) = q) (E : Subgroup (Q ⧸ center Q))
    (hfix : ∀ e ∈ E, onCenterQuotient α e = e) (hsq : ∀ e ∈ E, e * e = 1) :
    ∃ E' : Subgroup Q, (∀ e ∈ E', α e = e) ∧ (∀ e ∈ E', e * e = 1) ∧
      Nat.card E' = Nat.card E := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := fixedOver α E
  let π : W →* E :=
    ((QuotientGroup.mk' (center Q)).comp W.subtype).codRestrict E fun w => w.2.1
  have hπ : Function.Surjective π := by
    rintro ⟨e, he⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center Q) e
    obtain ⟨z, hz, hxz⟩ := exists_fixed_lift hodd α hα x (hfix _ he)
    have hmk : QuotientGroup.mk' (center Q) (x * z) = QuotientGroup.mk' (center Q) x := by
      rw [map_mul, QuotientGroup.mk'_apply (center Q) z, (QuotientGroup.eq_one_iff z).mpr hz,
        mul_one]
    exact ⟨⟨x * z, hmk ▸ he, hxz⟩, Subtype.ext hmk⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 W) := inferInstance
  have hE2 : IsPGroup 2 E := fun e => ⟨1, Subtype.ext (by rw [pow_one, sq]; exact hsq e e.2)⟩
  have hPtop : P.map π = ⊤ := by
    rw [← Sylow.coe_mapSurjective hπ]
    exact ((P.mapSurjective hπ).is_maximal' (hE2.to_subgroup ⊤) le_top).symm
  have hker : ∀ p ∈ P, π p = 1 → p = 1 := by
    intro p hp hp1
    obtain ⟨n, hn⟩ := P.2 ⟨p, hp⟩
    have hpZ : (p : Q) ∈ center Q := by
      have := congrArg Subtype.val hp1
      exact (QuotientGroup.eq_one_iff _).mp this
    refine Subtype.ext (eq_one_of_mem_center_of_pow hodd hpZ (n := n) ?_)
    have := congrArg (fun y : P => ((y : W) : Q)) hn
    simpa using this
  have hinj : Function.Injective (π.comp (P : Subgroup W).subtype) := by
    rw [injective_iff_map_eq_one]
    intro p hp
    exact Subtype.ext (hker p p.2 hp)
  have hrange : (π.comp (P : Subgroup W).subtype).range = ⊤ := by
    rw [MonoidHom.range_comp, range_subtype, hPtop]
  refine ⟨(P : Subgroup W).map W.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨w, -, rfl⟩
    exact w.2.2
  · rintro _ ⟨w, hw, rfl⟩
    have h1 : π (w * w) = 1 := by
      rw [map_mul]
      exact Subtype.ext (hsq _ (π w).2)
    have := hker _ (mul_mem hw hw) h1
    simpa using congrArg Subtype.val this
  · rw [card_map_of_injective W.subtype_injective,
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hrange, card_top]

end Lift

section Model

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoAut

variable {F : Type} [Field F] (h : UnitaryFieldData 2 1 F)

@[expose] noncomputable def binSym (c : Fin 6 → ZMod 2) : Matrix (Fin 3) (Fin 3) F :=
  !![binCast h (c 0), binCast h (c 1), binCast h (c 2);
    binCast h (c 1), binCast h (c 3), binCast h (c 4);
    binCast h (c 2), binCast h (c 4), binCast h (c 5)]

theorem binSym_map_bar (c : Fin 6 → ZMod 2) : (binSym h c).map h.bar = binSym h c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [binSym, bar_binCast]

theorem binSym_transpose (c : Fin 6 → ZMod 2) : (binSym h c)ᵀ = binSym h c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [binSym]

theorem binSym_hermitian (c : Fin 6 → ZMod 2) : ((binSym h c).map h.bar)ᵀ = binSym h c := by
  rw [binSym_map_bar, binSym_transpose]

theorem binSym_add (c c' : Fin 6 → ZMod 2) : binSym h (c + c') = binSym h c + binSym h c' := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [binSym]

theorem binSym_zero : binSym h 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [binSym]

theorem binSym_injective : Function.Injective (binSym h) := by
  intro c c' hcc
  have hb : Function.Injective (binCast h) := (binCast h).injective
  have e : ∀ i j, binSym h c i j = binSym h c' i j := fun i j => by rw [hcc]
  funext k
  fin_cases k
  · exact hb (by simpa [binSym] using e 0 0)
  · exact hb (by simpa [binSym] using e 0 1)
  · exact hb (by simpa [binSym] using e 0 2)
  · exact hb (by simpa [binSym] using e 1 1)
  · exact hb (by simpa [binSym] using e 1 2)
  · exact hb (by simpa [binSym] using e 2 2)

@[expose] noncomputable def nBin (c : Fin 6 → ZMod 2) : sixS h :=
  nElt h (binSym h c) (binSym_hermitian h c)

theorem coe_nBin (c : Fin 6 → ZMod 2) :
    ((nBin h c : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = nMat (binSym h c) :=
  rfl

theorem nBin_add (c c' : Fin 6 → ZMod 2) : nBin h (c + c') = nBin h c * nBin h c' :=
  Subtype.ext (Units.ext (by
    rw [Subgroup.coe_mul, Units.val_mul, coe_nBin, coe_nBin, coe_nBin, nMat_mul, binSym_add]))

theorem nBin_zero : nBin h 0 = 1 :=
  Subtype.ext (Units.ext (by rw [coe_nBin, binSym_zero, nMat_zero]; rfl))

theorem tElt_mul_nBin (k : ℕ) (c : Fin 6 → ZMod 2) :
    tElt h k * nBin h c = nBin h c * tElt h k :=
  Subtype.ext (Units.ext (by
    rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_mul, Units.val_mul, coe_nBin, coe_tElt,
      nMat_mul, nMat_mul, add_comm]))

theorem glAut_nBin (c : Fin 6 → ZMod 2) :
    glAut (barEquiv h) (nBin h c : GL (Fin 6) F) = nBin h c := by
  refine Units.ext ?_
  rw [coe_glAut, coe_nBin, Yamada.nMat_map_of _ (map_zero _) (map_one _)]
  congr 1
  calc (binSym h c).map (barEquiv h) = (binSym h c).map h.bar := by
        ext i j
        simp [barEquiv_eq_bar]
    _ = binSym h c := binSym_map_bar h c

@[expose] noncomputable def binHom : Multiplicative (Fin 6 → ZMod 2) →* sixQ h where
  toFun c := sixProj h (nBin h c.toAdd)
  map_one' := by
    change sixProj h (nBin h 0) = 1
    rw [nBin_zero, map_one]
  map_mul' c c' := by
    change sixProj h (nBin h (c.toAdd + c'.toAdd)) = _
    rw [nBin_add, map_mul]

theorem binHom_apply (c : Multiplicative (Fin 6 → ZMod 2)) :
    binHom h c = sixProj h (nBin h c.toAdd) :=
  rfl

theorem binHom_injective : Function.Injective (binHom h) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  by_contra hne
  have hne' : binSym h c.toAdd ≠ 0 := by
    intro h0
    apply hne
    exact toAdd_eq_zero.mp (binSym_injective h (by rw [h0, binSym_zero]))
  obtain ⟨i, j, hij⟩ : ∃ i j, binSym h c.toAdd i j ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne' (Matrix.ext hall)
  refine sixProj_ne_one_of_apply h (a := sixEquiv (Sum.inl i)) (b := sixEquiv (Sum.inr j))
    (fun e => Sum.inl_ne_inr (sixEquiv.injective e)) ?_ hc
  rw [coe_nBin, nMat_apply_inl_inr]
  exact hij

theorem binHom_mul_self (c : Multiplicative (Fin 6 → ZMod 2)) :
    binHom h c * binHom h c = 1 := by
  have : c * c = 1 := by
    rw [← toAdd_eq_zero, toAdd_mul]
    funext k
    exact CharTwo.add_self_eq_zero _
  rw [← map_mul, this, map_one]

theorem card_range_binHom : Nat.card (binHom h).range = 2 ^ 6 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (binHom_injective h)).toEquiv]
  simp [Nat.card_eq_fintype_card]

theorem conj_tElt_binHom (k : ℕ) (c : Multiplicative (Fin 6 → ZMod 2)) :
    MulAut.conj (sixProj h (tElt h k)) (binHom h c) = binHom h c := by
  rw [MulAut.conj_apply, binHom_apply, ← map_mul, ← map_inv, ← map_mul, tElt_mul_nBin,
    mul_inv_cancel_right]

theorem sigmaQ_binHom (c : Multiplicative (Fin 6 → ZMod 2)) :
    sigmaQ h (binHom h c) = binHom h c := by
  rw [binHom_apply, sigmaQ_sixProj]
  congr 1
  exact Subtype.ext (glAut_nBin h _)

theorem alphaOne_binHom (c : Multiplicative (Fin 6 → ZMod 2)) :
    alphaOne h (binHom h c) = binHom h c := by
  rw [alphaOne, MulAut.mul_apply, sigmaQ_binHom, t0Elt, conj_tElt_binHom]

theorem exists_fixed_binary_sixQ (α : MulAut (sixQ h)) (hα : α * α = 1) :
    ∃ B : Subgroup (sixQ h), (∀ b ∈ B, α b = b) ∧ (∀ b ∈ B, b * b = 1) ∧
      2 ^ 6 ≤ Nat.card B := by
  by_cases h1 : α = 1
  · refine ⟨(binHom h).range, fun b _ => by rw [h1, MulAut.one_apply], ?_,
      (card_range_binHom h).ge⟩
    rintro _ ⟨c, rfl⟩
    exact binHom_mul_self h c
  have hα2 : orderOf α = 2 := orderOf_eq_prime (by rw [sq, hα]) h1
  obtain ⟨ω, hω⟩ := exists_omega h
  obtain ⟨A, hA⟩ := exists_conj_eq_of_orderOf_eq_two h ω hω α hα2
  set c := primeFormConjHom h _ A
  have key : ∀ γ : MulAut (sixQ h), c * α * c⁻¹ = γ →
      (∀ x, γ (binHom h x) = binHom h x) → ∃ B : Subgroup (sixQ h),
        (∀ b ∈ B, α b = b) ∧ (∀ b ∈ B, b * b = 1) ∧ 2 ^ 6 ≤ Nat.card B := by
    intro γ hγ hfix
    have hαγ : α = c⁻¹ * γ * c := by rw [← hγ]; group
    refine ⟨(binHom h).range.map (c⁻¹ : MulAut (sixQ h)).toMonoidHom, ?_, ?_, ?_⟩
    · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      change α (c⁻¹ (binHom h x)) = c⁻¹ (binHom h x)
      rw [hαγ, MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self, hfix]
    · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      change c⁻¹ (binHom h x) * c⁻¹ (binHom h x) = 1
      rw [← map_mul, binHom_mul_self, map_one]
    · rw [card_map_of_injective (MulEquiv.injective _), card_range_binHom]
  rcases hA with ⟨k, -, hk⟩ | hσ | hα1
  · exact key _ hk (conj_tElt_binHom h k)
  · exact key _ hσ (sigmaQ_binHom h)
  · exact key _ hα1 (alphaOne_binHom h)

end Model

section Lie

open CFSG.Blueprint

theorem exists_fixed_elementary_of_lieModel {X : Type} [Group X] (hX : LieModel X .PSU 6 2 1)
    (β : MulAut X) (hβ : β * β = 1) :
    ∃ B : Subgroup X, (∀ b ∈ B, β b = b) ∧ (∀ b ∈ B, b * b = 1) ∧ 2 ^ 6 ≤ Nat.card B := by
  obtain ⟨F, _, h, ⟨f⟩⟩ := exists_hypPSU_mulEquiv hX
  set φ : X ≃* CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoAut.sixQ h :=
    f.symm.trans (hypSixQ h)
  obtain ⟨B, hfix, hsq, hcard⟩ := exists_fixed_binary_sixQ h (MulAut.congr φ β)
    (by rw [← map_mul, hβ, map_one])
  refine ⟨B.map φ.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    have := congrArg φ.symm (hfix b hb)
    change φ.symm (φ (β (φ.symm b))) = φ.symm b at this
    rwa [MulEquiv.symm_apply_apply] at this
  · rintro _ ⟨b, hb, rfl⟩
    change φ.symm b * φ.symm b = 1
    rw [← map_mul, hsq b hb, map_one]
  · rwa [card_map_of_injective φ.symm.injective]

theorem mul_comm_of_mul_self {M : Type*} [Group M] {a b : M} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b * (a * b) = 1) : a * b = b * a := by
  have h1 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right hab
  rw [← h1, mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb]

open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer) in
theorem card_le_of_elementary_mulAut {X : Type} [Group X] (hX : LieModel X .PSU 6 2 1)
    (E : Subgroup (MulAut X)) (hsq : ∀ e ∈ E, e * e = 1) : Nat.card E ≤ 2 ^ 9 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₀⟩ := CFSG.LieType.Multipliers.U62.nonempty_mulEquiv_T46 hX
  set D := ToddParabolic.ofMulEquivT46 e₀
  have := D.finite
  set B := E.comap (MulAut.conj : X →* MulAut X)
  have hBsq : ∀ x ∈ B, x ^ 2 = 1 := fun x hx =>
    D.conj_injective (by rw [map_pow, sq, map_one]; exact hsq _ hx)
  have hB9 : Nat.card B ≤ 2 ^ 9 := (D.exists_conj_eq_A hBsq).1
  let f : E →* Outer X := (QuotientGroup.mk' (inner X)).comp E.subtype
  have hker : Nat.card f.ker = Nat.card B := by
    have h1 : f.ker.map E.subtype = E ⊓ inner X := by
      ext a
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.2, (QuotientGroup.eq_one_iff _).mp hx⟩
      · rintro ⟨haE, hainn⟩
        exact ⟨⟨a, haE⟩, (QuotientGroup.eq_one_iff _).mpr hainn, rfl⟩
    have h2 : B.map (MulAut.conj : X →* MulAut X) = E ⊓ inner X := by
      rw [map_comap_eq, inf_comm]
      rfl
    rw [← card_map_of_injective E.subtype_injective, h1, ← h2,
      card_map_of_injective D.conj_injective]
  have hO : Nat.card (Outer X) = 6 := YamadaEnd.card_outer_of_lieModel_PSU hX
  have hrange : Nat.card f.range ≤ 2 := by
    have : Finite (Outer X) := Nat.finite_of_card_ne_zero (by rw [hO]; norm_num)
    have hp : IsPGroup 2 f.range := by
      rintro ⟨_, ⟨x, rfl⟩⟩
      refine ⟨1, Subtype.ext ?_⟩
      rw [pow_one, Subgroup.coe_pow, sq, ← map_mul, Subgroup.coe_one]
      rw [show x * x = 1 from Subtype.ext (hsq _ x.2), map_one]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
    have hdvd : Nat.card f.range ∣ 6 := hO ▸ card_subgroup_dvd_card _
    rw [hk] at hdvd ⊢
    rcases k with _ | _ | k
    · norm_num
    · norm_num
    · have h4 : 2 ^ 2 ∣ 6 := (pow_dvd_pow 2 (by omega : 2 ≤ k + 1 + 1)).trans hdvd
      norm_num at h4
  have hEq := card_ker_mul_card_range f
  by_cases hinn : ∀ e ∈ E, e ∈ inner X
  · have h1 : Nat.card f.range = 1 := by
      rw [card_eq_one, eq_bot_iff]
      rintro _ ⟨x, rfl⟩
      exact (QuotientGroup.eq_one_iff _).mpr (hinn _ x.2)
    rw [← hEq, h1, mul_one, hker]
    exact hB9
  push Not at hinn
  obtain ⟨e, heE, heout⟩ := hinn
  have hB6 : Nat.card B ≤ 2 ^ 6 := by
    refine card_le_of_fixed hX (α := e) (hsq e heE) (fun q hq => heout ⟨q, hq.symm⟩) ?_ hBsq
    intro x hx
    apply D.conj_injective
    have hc : e * MulAut.conj x = MulAut.conj x * e :=
      mul_comm_of_mul_self (hsq e heE) (hsq _ hx) (hsq _ (mul_mem heE hx))
    rw [← mulAut_mul_conj_mul_inv, hc, mul_inv_cancel_right]
  calc Nat.card E = Nat.card f.ker * Nat.card f.range := hEq.symm
    _ ≤ 2 ^ 6 * 2 := Nat.mul_le_mul (hker ▸ hB6) hrange
    _ ≤ 2 ^ 9 := by norm_num

theorem exists_fixed_elementary_of_normalizes {G : Type} [Group G] [Finite G] (Q : Subgroup G)
    (hLie : LieModel (Q ⧸ center Q) .PSU 6 2 1) (hodd : Odd (Nat.card (center Q))) (y : G)
    (hy : y ∈ normalizer (Q : Set G)) (hyy : y * y = 1) :
    ∃ E : Subgroup G, E ≤ Q ⊓ centralizer ({y} : Set G) ∧ (∀ e ∈ E, e * e = 1) ∧
      2 ^ 6 ≤ Nat.card E := by
  set α := Q.normalizerMonoidHom ⟨y, hy⟩
  have hαapp : ∀ q : Q, (α q : G) = y * q * y⁻¹ := fun q => rfl
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hα : ∀ q, α (α q) = q := fun q => Subtype.ext (by
    rw [hαapp, hαapp, hyinv, ← mul_assoc, ← mul_assoc, hyy, one_mul, mul_assoc, hyy, mul_one])
  have hᾱ : onCenterQuotient α * onCenterQuotient α = 1 := by
    ext x
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (center Q) x
    rw [MulAut.mul_apply, onCenterQuotient_apply_mk, onCenterQuotient_apply_mk, hα,
      MulAut.one_apply]
  obtain ⟨B, hfix, hsq, hcard⟩ := exists_fixed_elementary_of_lieModel hLie _ hᾱ
  obtain ⟨E', hfix', hsq', hcard'⟩ := exists_fixed_elementary_lift hodd α hα B hfix hsq
  refine ⟨E'.map Q.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    refine ⟨q.2, mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 := congrArg Subtype.val (hfix' q hq)
    rw [hαapp] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  · rintro _ ⟨q, hq, rfl⟩
    change (q : G) * q = 1
    rw [← Subgroup.coe_mul, hsq' q hq, Subgroup.coe_one]
  · rw [card_map_of_injective Q.subtype_injective, hcard']
    exact hcard

theorem u62RankInput : YamadaEnd.U62RankInput :=
  ⟨fun _ _ _ Q _ hLie hodd y hy hyy => exists_fixed_elementary_of_normalizes Q hLie hodd y hy hyy,
    fun _ _ hX E hsq => card_le_of_elementary_mulAut hX E hsq⟩

end Lie

end CFSG.EvenSmallLie.UnitarySix.YamadaInputs

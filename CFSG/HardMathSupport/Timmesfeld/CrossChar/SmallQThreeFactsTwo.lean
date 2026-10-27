module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsFour
public import CFSG.RankThree.PartOne.KGD.D4Twist

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KE

set_option linter.unusedSectionVars false

variable {τ : Tag} {L : Type} [Field L] [CharP L 2]

theorem exists_eq_pow_of_pow_three {F : Type} [Field F] {ω : Fˣ} (hω : orderOf ω = 3) {v : Fˣ}
    (hv : v ^ 3 = 1) : ∃ m : ℕ, v = ω ^ m := by
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hω1 : (ω : F) ≠ 1 := by
    intro h
    have h1 : ω = 1 := Units.ext h
    rw [h1, orderOf_one] at hω
    norm_num at hω
  have hw3 : (ω : F) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  have hsum : (ω : F) ^ 2 + ω + 1 = 0 := by
    have h1 : ((ω : F) - 1) * ((ω : F) ^ 2 + ω + 1) = 0 := by
      have : ((ω : F) - 1) * ((ω : F) ^ 2 + ω + 1) = (ω : F) ^ 3 - 1 := by ring
      rw [this, hw3, sub_self]
    exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hω1)
  have hv3 : (v : F) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hv, Units.val_one]
  have hprod : ((v : F) - 1) * ((v : F) - ω) * ((v : F) - (ω : F) ^ 2) = 0 := by
    have : ((v : F) - 1) * ((v : F) - ω) * ((v : F) - (ω : F) ^ 2) =
        (v : F) ^ 3 - ((ω : F) ^ 2 + ω + 1) * (v : F) ^ 2 +
          ((ω : F) ^ 2 + ω + 1) * ω * (v : F) - (ω : F) ^ 3 := by ring
    rw [this, hsum, hw3, hv3]
    ring
  rcases mul_eq_zero.1 hprod with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact ⟨0, Units.ext (by rw [pow_zero, Units.val_one]; exact sub_eq_zero.1 h)⟩
    · exact ⟨1, Units.ext (by rw [pow_one]; exact sub_eq_zero.1 h)⟩
  · exact ⟨2, Units.ext (by rw [Units.val_pow_eq_pow_val]; exact sub_eq_zero.1 h)⟩

section WeylConjugation


theorem canonicalRep_conj_rootDiagUnit_sq {τ : Tag} {L : Type} [Field L] {w₀ : WeylGroup τ}
    (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u) {a : Fin τ.rank → Lˣ} (ha3 : ∀ i, a i ^ 3 = 1) :
    canonicalRep (coxeterSystem τ) L w₀ * rootDiagUnit τ a *
      (canonicalRep (coxeterSystem τ) L w₀)⁻¹ = rootDiagUnit τ a ^ 2 := by
  rw [canonicalRep_conj_rootDiagUnit_of_neg hw₀]
  have hd3 : rootDiagUnit τ a ^ 3 = 1 := by
    have h1 : rootDiagUnit τ (a ^ 3) = rootDiagUnit τ a ^ 3 := map_pow (rootDiagUnitHom τ L) a 3
    rw [← h1, show a ^ 3 = 1 from funext ha3, rootDiagUnit_one]
  exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ', hd3])

end WeylConjugation

section Torus


theorem iterateFrobenius_two_one (c : L) : iterateFrobenius L 2 1 c = c ^ 2 := by
  rw [iterateFrobenius_def, pow_one]

theorem entrywise_two_rootDiagUnit (a : Fin τ.rank → Lˣ) :
    Units.map (entrywiseHom (iterateFrobenius L 2 1)) (rootDiagUnit τ a) =
      rootDiagUnit τ a ^ 2 := by
  change baseChangeGL (iterateFrobenius L 2 1) (rootDiagUnit τ a) = _
  rw [baseChangeGL_rootDiagUnit]
  have h : (fun i => Units.map (iterateFrobenius L 2 1).toMonoidHom (a i)) = a ^ 2 := by
    funext i
    apply Units.ext
    change iterateFrobenius L 2 1 (a i : L) = ((a ^ 2) i : L)
    rw [iterateFrobenius_two_one, Pi.pow_apply, Units.val_pow_eq_pow_val]
  rw [h]
  exact map_pow (rootDiagUnitHom τ L) a 2

variable {w₀ : WeylGroup τ}

theorem twFrob_rootDiagUnit (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u) (a : Fin τ.rank → Lˣ) :
    canonicalRep (coxeterSystem τ) L w₀ *
        Units.map (entrywiseHom (iterateFrobenius L 2 1)) (rootDiagUnit τ a) *
      (canonicalRep (coxeterSystem τ) L w₀)⁻¹ = (rootDiagUnit τ a)⁻¹ ^ 2 := by
  rw [entrywise_two_rootDiagUnit, ← conj_pow, canonicalRep_conj_rootDiagUnit_of_neg hw₀]

theorem pow_three_of_mem_twModel
    (htorL : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ torusGroup τ L)
    (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u) {g : ModGL τ L}
    (hg : g ∈ twModel (canonicalRep (coxeterSystem τ) L w₀) (iterateFrobenius L 2 1))
    (hgT : g ∈ torusGroup τ L) : g ^ 3 = 1 := by
  obtain ⟨a, rfl, ha⟩ := (mem_twistedTorus_of_neg htorL hw₀ iterateFrobenius_two_one).1
    (mem_twistedTorus.2 ⟨hgT, hg.2⟩)
  have h1 : rootDiagUnit τ (a ^ 3) = rootDiagUnit τ a ^ 3 := map_pow (rootDiagUnitHom τ L) a 3
  have h2 : a ^ 3 = 1 := funext fun i => by simpa using ha i
  rw [← h1, h2, rootDiagUnit_one]

theorem dV_mem_twModel (htorL : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ torusGroup τ L)
    (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u) {ω : Lˣ} (hω3 : ω ^ 3 = 1)
    (x : Fin τ.rank → ZMod 3) :
    dV ω x ∈ twModel (canonicalRep (coxeterSystem τ) L w₀) (iterateFrobenius L 2 1) :=
  twistedTorus_le_twModel _ _ ((mem_twistedTorus_of_neg htorL hw₀ iterateFrobenius_two_one).2
    ⟨torV ω x, rfl, fun i => by
      show (ω ^ (x i).val) ^ (2 + 1) = 1
      rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]⟩)

theorem dV_pow_three {ω : Lˣ} (hω3 : ω ^ 3 = 1) (x : Fin τ.rank → ZMod 3) :
    dV (τ := τ) ω x ^ 3 = 1 := by
  have h1 : rootDiagUnit τ (torV ω x ^ 3) = rootDiagUnit τ (torV ω x) ^ 3 :=
    map_pow (rootDiagUnitHom τ L) _ 3
  have h2 : torV ω x ^ 3 = 1 := funext fun i => by
    rw [Pi.pow_apply, torV, ← pow_mul, mul_comm, pow_mul, hω3, one_pow, Pi.one_apply]
  change rootDiagUnit τ (torV ω x) ^ 3 = 1
  rw [← h1, h2, rootDiagUnit_one]

end Torus

section Fusion

variable [IsAlgClosed L]
  {w₀ : WeylGroup τ}

theorem finite_twModel {n g0 : ModGL τ L} (hg0C : g0 ∈ adjointGroup τ L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L 2 1)) g0 = g0 * n) :
    Finite (twModel n (iterateFrobenius L 2 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin := CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum.finite_entrywise_fixed
    (τ := τ) (k := L) (p₀ := 2) (N := 1) one_pos
  set W := twModel n (iterateFrobenius L 2 1) with hW
  have hinj : Set.InjOn (fun y : ModGL τ L => g0 * y * g0⁻¹)
      ((fun y : ModGL τ L => g0 * y * g0⁻¹) ⁻¹'
        {g : ModGL τ L | Units.map (entrywiseHom (iterateFrobenius L 2 1)) g = g}) :=
    fun y _ z _ h => by simpa using h
  have hsub : (W : Set (ModGL τ L)) ⊆ (fun y : ModGL τ L => g0 * y * g0⁻¹) ⁻¹'
      {g : ModGL τ L | Units.map (entrywiseHom (iterateFrobenius L 2 1)) g = g} := by
    intro y hy
    have h1 : g0 * y * g0⁻¹ ∈ W.map (MulAut.conj g0).toMonoidHom := ⟨y, hy, rfl⟩
    rw [hW, map_conj_twModel hg0C hg0] at h1
    exact h1.2
  exact ((hfin.preimage hinj).subset hsub).to_subtype

theorem exists_conj_dV_twModel
    (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    (hmon : MonomialToralAt τ 3) (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u)
    (hLang : ∀ a : Fin τ.rank → Lˣ, (∀ i, a i ^ 3 = 1) → ∀ c ∈ toralCentralizer τ L a,
      ∃ z ∈ toralCentralizer τ L a,
        z⁻¹ * frobTwistGL τ L 2 1 (canonicalRep (coxeterSystem τ) L w₀) z = c)
    {ω : Lˣ} (hω : orderOf ω = 3) {s : ModGL τ L}
    (hs : s ∈ twModel (canonicalRep (coxeterSystem τ) L w₀) (iterateFrobenius L 2 1))
    (hs3 : s ^ 3 = 1) :
    ∃ u ∈ twModel (canonicalRep (coxeterSystem τ) L w₀) (iterateFrobenius L 2 1),
      ∃ x : Fin τ.rank → ZMod 3, u * s * u⁻¹ = dV ω x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnG : canonicalRep (coxeterSystem τ) L w₀ ∈ adjointGroup τ L :=
    canonicalRep_mem_adjointGroup _ L _
  set F := frobTwistGL τ L 2 1 (canonicalRep (coxeterSystem τ) L w₀) with hF
  have hFapp : ∀ g, F g = canonicalRep (coxeterSystem τ) L w₀ *
      Units.map (entrywiseHom (iterateFrobenius L 2 1)) g *
        (canonicalRep (coxeterSystem τ) L w₀)⁻¹ := fun g => rfl
  have hFG : ∀ g ∈ adjointGroup τ L, F g ∈ adjointGroup τ L := fun g hg =>
    mul_mem (mul_mem hnG (entrywiseFrobGL_mem 2 1 hg)) (inv_mem hnG)
  have hsG : s ∈ adjointGroup τ L := hs.1
  have hFs : F s = s := hs.2
  have hfin : ((Subgroup.zpowers s : Subgroup (ModGL τ L)) : Set (ModGL τ L)).Finite :=
    (finite_zpowers).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, hs3⟩)
  have hexp : ∀ x ∈ Subgroup.zpowers s, x ^ 3 = 1 := by
    rintro _ ⟨k, rfl⟩
    simp only
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hs3, one_zpow]
  have hzle : Subgroup.zpowers s ≤ adjointGroup τ L := by
    rw [Subgroup.zpowers_le]
    exact hsG
  obtain ⟨c₁, hc₁, hc₁m⟩ := exists_conj_le_monomial_bar (ℓ := 2) (p := 3) (by norm_num) halg
    hzle hfin hexp
  have hmn := hc₁m s (Subgroup.mem_zpowers s)
  have hn3 : (c₁ * s * c₁⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hs3, mul_one, mul_inv_cancel]
  have hL3 : ringChar L ≠ 3 := by
    rw [ringChar.eq L 2]
    norm_num
  obtain ⟨c₂, hc₂, hc₂t⟩ := exists_conj_mem_torusGroup_of_mem_monomial hmon hL3 hmn hn3
  obtain ⟨h, hh⟩ : ∃ h, h = c₂ * c₁ := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = h * s * h⁻¹ := ⟨_, rfl⟩
  have ht' : t = c₂ * (c₁ * s * c₁⁻¹) * c₂⁻¹ := by rw [ht, hh]; group
  have htT : t ∈ torusGroup τ L := ht' ▸ hc₂t
  obtain ⟨a, ha⟩ := torusGroup_le_range_rootDiagUnitHom htT
  have hta : t = rootDiagUnit τ a := ha.symm
  have ht3 : t ^ 3 = 1 := by rw [ht, conj_pow, hs3, mul_one, mul_inv_cancel]
  have ha3 : ∀ i, a i ^ 3 = 1 := by
    have h1 : rootDiagUnitHom τ L (a ^ 3) = rootDiagUnitHom τ L 1 := by
      rw [map_pow, map_one]
      change (rootDiagUnit τ a) ^ 3 = 1
      rw [← hta, ht3]
    have h2 := rootDiagUnit_injective (τ := τ) (K := L) h1
    intro i
    have := congrFun h2 i
    simpa using this
  have hFt : F t = t := by
    rw [hFapp, hta, twFrob_rootDiagUnit hw₀ a, inv_pow]
    have hd3 : rootDiagUnit τ a ^ 3 = 1 := by rw [← hta, ht3]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ, hd3])
  obtain ⟨y, hy⟩ : ∃ y, y = h⁻¹ := ⟨_, rfl⟩
  have hyG : y ∈ adjointGroup τ L := hy ▸ inv_mem (hh ▸ mul_mem hc₂ hc₁)
  have hsy : s = y * t * y⁻¹ := by rw [ht, hy]; group
  have hFsy : F y * t * (F y)⁻¹ = s := by
    have := congrArg F hsy
    rw [map_mul, map_mul, map_inv, hFt, hFs] at this
    exact this.symm
  have h1 : F y * t * (F y)⁻¹ = y * t * y⁻¹ := hFsy.trans hsy
  have hcc : y⁻¹ * F y ∈ toralCentralizer τ L a := by
    rw [mem_toralCentralizer]
    refine ⟨mul_mem (inv_mem hyG) (hFG y hyG), ?_⟩
    have h2 : (y⁻¹ * F y) * t = t * (y⁻¹ * F y) := by
      calc (y⁻¹ * F y) * t = y⁻¹ * (F y * t * (F y)⁻¹) * y * (y⁻¹ * F y) := by group
        _ = y⁻¹ * (y * t * y⁻¹) * y * (y⁻¹ * F y) := by rw [h1]
        _ = t * (y⁻¹ * F y) := by group
    rw [← hta]
    calc t * (y⁻¹ * F y) * t⁻¹ = (y⁻¹ * F y) * t * t⁻¹ := by rw [h2]
      _ = y⁻¹ * F y := by group
  obtain ⟨z, hz, hzc⟩ := hLang a ha3 _ hcc
  have hzc' : z⁻¹ * F z = y⁻¹ * F y := hzc
  obtain ⟨hzG, hzt⟩ := mem_toralCentralizer.1 hz
  obtain ⟨u, hu⟩ : ∃ u, u = y * z⁻¹ := ⟨_, rfl⟩
  have hFu : F u = u := by
    have hFz : F z = z * (y⁻¹ * F y) := by rw [← hzc']; group
    rw [hu, map_mul, map_inv, hFz]
    group
  have huG : u ∈ adjointGroup τ L := hu ▸ mul_mem hyG (inv_mem hzG)
  have hut : u * t * u⁻¹ = s := by
    have hzt' : z * t = t * z := by
      have h3 : t * z * t⁻¹ = z := by rw [hta]; exact hzt
      calc z * t = (t * z * t⁻¹) * t := by rw [h3]
        _ = t * z := by group
    rw [hsy, hu]
    calc y * z⁻¹ * t * (y * z⁻¹)⁻¹ = y * (z⁻¹ * (t * z)) * y⁻¹ := by group
      _ = y * (z⁻¹ * (z * t)) * y⁻¹ := by rw [hzt']
      _ = y * t * y⁻¹ := by group
  have huW : u ∈ twModel (canonicalRep (coxeterSystem τ) L w₀) (iterateFrobenius L 2 1) :=
    ⟨huG, hFu⟩
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  choose m hm using fun i => exists_eq_pow_of_pow_three hω (ha3 i)
  set x : Fin τ.rank → ZMod 3 := fun i => (m i : ZMod 3) with hx
  have hax : torV ω x = a := by
    funext i
    rw [hm i, torV, hx, ZMod.val_natCast]
    conv_rhs => rw [← Nat.mod_add_div (m i) 3]
    rw [pow_add, pow_mul, hω3, one_pow, mul_one]
  refine ⟨u⁻¹, inv_mem huW, x, ?_⟩
  change u⁻¹ * s * u⁻¹⁻¹ = rootDiagUnit τ (torV ω x)
  rw [hax, ← hta, ← hut]
  group

end Fusion

section RankOne

variable
  {w₀ : WeylGroup τ}

theorem exists_twFrob_rootSL2 (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    ∃ μ : Lˣ, ∀ A : SL2 L,
      canonicalRep (coxeterSystem τ) L w₀ *
          Units.map (entrywiseHom (iterateFrobenius L 2 1)) (rootSL2 τ L α A) *
        (canonicalRep (coxeterSystem τ) L w₀)⁻¹ =
      rootSL2 τ L α (conjSL (RankThree.Classical.swapGL * diagUnitOne μ)
        (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 1) A)) := by
  obtain ⟨s, hs⟩ := exists_conj_rootSL2_eq (canonicalRep_mem_monomialSubgroup L w₀)
    (mapsRootLines_canonicalRep w₀) hα (hw₀ α)
  obtain ⟨a, ha⟩ := CFSG.RankThree.PartOne.KGD.exists_rootSL2_neg_eq (L := L) hα
  refine ⟨a * s, fun A => ?_⟩
  rw [entrywise_rootSL2_of_field, hs, ha, ← conjSL_mul, mul_assoc, diagUnitOne_mul]

theorem twFix_cases {μ : Lˣ} {A : SL2 L}
    (hA : conjSL (RankThree.Classical.swapGL * diagUnitOne μ)
      (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 1) A) = A) :
    A ^ 3 = 1 ∨
      ((A : Matrix (Fin 2) (Fin 2) L) 0 0 = 0 ∧ (A : Matrix (Fin 2) (Fin 2) L) 1 1 = 0) := by
  obtain ⟨a, b, c, d, hAm⟩ : ∃ a b c d : L, (A : Matrix (Fin 2) (Fin 2) L) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hM : ((RankThree.Classical.swapGL * diagUnitOne μ : GL (Fin 2) L) :
      Matrix (Fin 2) (Fin 2) L) = !![0, 1; (μ : L), 0] := coe_swapGL_mul_diagUnitOne μ
  have hμ : (μ : L) * ((μ⁻¹ : Lˣ) : L) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hMi : (((RankThree.Classical.swapGL * diagUnitOne μ : GL (Fin 2) L)⁻¹ : GL (Fin 2) L) :
      Matrix (Fin 2) (Fin 2) L) = !![0, ((μ⁻¹ : Lˣ) : L); 1, 0] := by
    rw [Matrix.coe_units_inv, hM]
    apply Matrix.inv_eq_left_inv
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_comm]
  have hE : !![0, 1; (μ : L), 0] * (A : Matrix (Fin 2) (Fin 2) L).map (iterateFrobenius L 2 1) *
      !![0, ((μ⁻¹ : Lˣ) : L); 1, 0] = A := by
    have := congrArg (fun B : SL2 L => (B : Matrix (Fin 2) (Fin 2) L)) hA
    simp only [coe_conjSL, hM, hMi] at this
    exact this
  have hmap : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) L).map (iterateFrobenius L 2 1) =
      !![a ^ 2, b ^ 2; c ^ 2, d ^ 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [frobenius_def]
  rw [hAm, hmap, Matrix.mul_fin_two, Matrix.mul_fin_two] at hE
  have e00 := congrFun (congrFun hE 0) 0
  have e01 := congrFun (congrFun hE 0) 1
  have e10 := congrFun (congrFun hE 1) 0
  have e11 := congrFun (congrFun hE 1) 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at e00 e01 e10 e11
  have hdet : a * d - b * c = 1 := by
    have := A.2
    rw [hAm, Matrix.det_fin_two_of] at this
    exact this
  have hd' : d = a ^ 2 := by
    rw [← e11]
    linear_combination (a ^ 2) * hμ
  have ha' : a = d ^ 2 := by rw [← e00]; ring
  have hc' : c = (μ : L) * b ^ 2 := by rw [← e10]; ring
  by_cases ha0 : a = 0
  · right
    rw [hAm]
    refine ⟨ha0, ?_⟩
    change d = 0
    rw [hd', ha0]
    ring
  · left
    have ha3 : a ^ 3 = 1 := by
      have h1 : a * (a ^ 3 - 1) = 0 := by
        rw [hd'] at ha'
        linear_combination (-1 : L) * ha'
      exact sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left ha0)
    have hbc : b * c = 0 := by
      rw [hd'] at hdet
      linear_combination ha3 - hdet
    have hb0 : b = 0 := by
      rw [hc'] at hbc
      have h3 : (μ : L) * b ^ 3 = 0 := by linear_combination hbc
      exact pow_eq_zero_iff (n := 3) (by norm_num) |>.1
        ((mul_eq_zero.1 h3).resolve_left μ.ne_zero)
    have hc0 : c = 0 := by rw [hc', hb0]; ring
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hAm, hb0, hc0, hd', Matrix.SpecialLinearGroup.coe_one,
      pow_succ, pow_succ, pow_one, Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;>
      first | linear_combination ha3 | linear_combination (a ^ 3 + 1) * ha3

theorem HSL_conj_antidiag (ζ : Lˣ) {A : SL2 L} (h0 : (A : Matrix (Fin 2) (Fin 2) L) 0 0 = 0)
    (h1 : (A : Matrix (Fin 2) (Fin 2) L) 1 1 = 0) :
    HSL ζ * A * (HSL ζ)⁻¹ * A⁻¹ = HSL (ζ ^ 2) := by
  obtain ⟨b, c, hAm⟩ : ∃ b c : L, (A : Matrix (Fin 2) (Fin 2) L) = !![0, b; c, 0] :=
    ⟨(A : Matrix (Fin 2) (Fin 2) L) 0 1, (A : Matrix (Fin 2) (Fin 2) L) 1 0, by
      conv_lhs => rw [Matrix.eta_fin_two (A : Matrix (Fin 2) (Fin 2) L)]
      rw [h0, h1]⟩
  have hdet : -(b * c) = 1 := by
    have := A.2
    rw [hAm, Matrix.det_fin_two_of] at this
    linear_combination this
  have hH : ∀ t : Lˣ, ((HSL t : SL2 L) : Matrix (Fin 2) (Fin 2) L) =
      !![(t : L), 0; 0, ((t⁻¹ : Lˣ) : L)] := fun t => rfl
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.SpecialLinearGroup.coe_inv, hAm, hH, hH, Matrix.adjugate_fin_two_of,
    Matrix.adjugate_fin_two_of, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two]
  have hinv2 : (((ζ ^ 2)⁻¹ : Lˣ) : L) = ((ζ⁻¹ : Lˣ) : L) ^ 2 := by
    rw [← inv_pow, Units.val_pow_eq_pow_val]
  rw [hinv2, Units.val_pow_eq_pow_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;>
    first | linear_combination (ζ : L) ^ 2 * hdet | linear_combination ((ζ : L)⁻¹) ^ 2 * hdet

theorem HSL_pow_three {t : Lˣ} (ht : t ^ 3 = 1) : HSL t ^ 3 = 1 := by
  have h1 : (t : L) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
  have h2 : ((t : L)⁻¹) ^ 3 = 1 := by
    rw [← Units.val_inv_eq_inv_val, ← Units.val_pow_eq_pow_val, inv_pow, ht, inv_one,
      Units.val_one]
  have hH : ((HSL t : SL2 L) : Matrix (Fin 2) (Fin 2) L) =
      !![(t : L), 0; 0, ((t⁻¹ : Lˣ) : L)] := rfl
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, hH, Matrix.SpecialLinearGroup.coe_one, pow_succ,
    pow_succ, pow_one, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> first | linear_combination h1 | linear_combination h2

theorem twFix_HSL (μ : Lˣ) {ζ : Lˣ} (hζ : ζ ^ 3 = 1) :
    conjSL (RankThree.Classical.swapGL * diagUnitOne μ)
      (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 1) (HSL ζ)) = HSL ζ := by
  have hM : ((RankThree.Classical.swapGL * diagUnitOne μ : GL (Fin 2) L) :
      Matrix (Fin 2) (Fin 2) L) = !![0, 1; (μ : L), 0] := coe_swapGL_mul_diagUnitOne μ
  have hμ : (μ : L) * ((μ⁻¹ : Lˣ) : L) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hMi : (((RankThree.Classical.swapGL * diagUnitOne μ : GL (Fin 2) L)⁻¹ : GL (Fin 2) L) :
      Matrix (Fin 2) (Fin 2) L) = !![0, ((μ⁻¹ : Lˣ) : L); 1, 0] := by
    rw [Matrix.coe_units_inv, hM]
    apply Matrix.inv_eq_left_inv
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_comm]
  have hinv : ζ⁻¹ = ζ ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ', hζ])
  have h1 : (ζ : L) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hζ, Units.val_one]
  have hH : ((HSL ζ : SL2 L) : Matrix (Fin 2) (Fin 2) L) = !![(ζ : L), 0; 0, (ζ : L) ^ 2] := by
    change !![(ζ : L), 0; 0, ((ζ⁻¹ : Lˣ) : L)] = _
    rw [hinv, Units.val_pow_eq_pow_val]
  apply Subtype.ext
  rw [coe_conjSL, hM, hMi]
  change !![0, 1; (μ : L), 0] * ((HSL ζ : SL2 L) : Matrix (Fin 2) (Fin 2) L).map
    (iterateFrobenius L 2 1) * !![0, ((μ⁻¹ : Lˣ) : L); 1, 0] = _
  rw [hH]
  have hmap : (!![(ζ : L), 0; 0, (ζ : L) ^ 2] : Matrix (Fin 2) (Fin 2) L).map
      (iterateFrobenius L 2 1) = !![(ζ : L) ^ 2, 0; 0, (ζ : L) ^ 4] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [frobenius_def, ← pow_mul]
  rw [hmap, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;>
    first | linear_combination (ζ : L) * h1 | field_simp

theorem eq_bot_of_le_rootSpan_two (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u) {ω : Lˣ}
    (hω : orderOf ω = 3) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) {G : Subgroup (ModGL τ L)}
    (hGW : G ≤ twModel (canonicalRep (coxeterSystem τ) L w₀) (iterateFrobenius L 2 1))
    (h3G : ∀ g ∈ twModel (canonicalRep (coxeterSystem τ) L w₀) (iterateFrobenius L 2 1),
      g ∈ rootSpan τ L {α, -α} → g ^ 3 = 1 → g ∈ G)
    (N : Subgroup G) (hNL : ∀ m ∈ N, (m : ModGL τ L) ∈ rootSpan τ L {α, -α})
    (hnorm : ∀ g : G, (g : ModGL τ L) ∈ rootSpan τ L {α, -α} → ∀ m ∈ N, g * m * g⁻¹ ∈ N)
    (hcop : Nat.Coprime 3 (Nat.card N)) : N = ⊥ := by
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  obtain ⟨μ, hμ⟩ := exists_twFrob_rootSL2 (L := L) hw₀ hα
  have hspan : rootSpan τ L {α, -α} = (rootSL2 τ L α).range := by
    rw [range_rootSL2_of_isRoot hα, rootSpan, iSup_insert, iSup_singleton]
  have hinj := rootSL2_injective_of_field (τ := τ) (K := L) α
  have hρG : ∀ A : SL2 L, rootSL2 τ L α A ∈ adjointGroup τ L := fun A =>
    rootSpan_le_adjointGroup L {α, -α} (by rw [hspan]; exact ⟨A, rfl⟩)
  have hfix : ∀ A : SL2 L,
      rootSL2 τ L α A ∈ twModel (canonicalRep (coxeterSystem τ) L w₀) (iterateFrobenius L 2 1) →
      conjSL (RankThree.Classical.swapGL * diagUnitOne μ)
        (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 1) A) = A :=
    fun A hA => hinj ((hμ A).symm.trans hA.2)
  have ht₀W : rootSL2 τ L α (HSL ω) ∈
      twModel (canonicalRep (coxeterSystem τ) L w₀) (iterateFrobenius L 2 1) :=
    ⟨hρG _, (hμ (HSL ω)).trans (by rw [twFix_HSL μ hω3]; rfl)⟩
  have ht₀3 : rootSL2 τ L α (HSL ω) ^ 3 = 1 := by
    rw [← map_pow, HSL_pow_three hω3, map_one]
  have ht₀L : rootSL2 τ L α (HSL ω) ∈ rootSpan τ L {α, -α} := by
    rw [hspan]
    exact ⟨_, rfl⟩
  have ht₀G : rootSL2 τ L α (HSL ω) ∈ G := h3G _ ht₀W ht₀L ht₀3
  have hord : ∀ m ∈ N, (m : ModGL τ L) ^ 3 = 1 → m = 1 := by
    intro m hm h3
    have h1 : orderOf (⟨m, hm⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
    have h2 : orderOf (⟨m, hm⟩ : N) ∣ 3 := by
      rw [Subgroup.orderOf_mk, ← Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one h3
    have h3' : orderOf (⟨m, hm⟩ : N) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_right h1 hcop).symm h2
    rw [orderOf_eq_one_iff] at h3'
    exact congrArg Subtype.val h3'
  refine eq_bot_iff.2 fun m hm => ?_
  rw [Subgroup.mem_bot]
  obtain ⟨A, hA⟩ : (m : ModGL τ L) ∈ (rootSL2 τ L α).range := hspan ▸ hNL m hm
  have hAfix := hfix A (by rw [hA]; exact hGW m.2)
  rcases twFix_cases hAfix with h3 | ⟨h0, h1⟩
  · exact hord m hm (by rw [← hA, ← map_pow, h3, map_one])
  · exfalso
    set g₀ : G := ⟨rootSL2 τ L α (HSL ω), ht₀G⟩ with hg₀
    have hkN : g₀ * m * g₀⁻¹ * m⁻¹ ∈ N := N.mul_mem (hnorm g₀ ht₀L m hm) (N.inv_mem hm)
    have hk : ((g₀ * m * g₀⁻¹ * m⁻¹ : G) : ModGL τ L) = rootSL2 τ L α (HSL (ω ^ 2)) := by
      rw [← HSL_conj_antidiag ω h0 h1, map_mul, map_mul, map_mul, map_inv, map_inv, hA]
      rfl
    have hω23 : (ω ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]
    have hk3 : ((g₀ * m * g₀⁻¹ * m⁻¹ : G) : ModGL τ L) ^ 3 = 1 := by
      rw [hk, ← map_pow, HSL_pow_three hω23, map_one]
    have hk1 := hord _ hkN hk3
    have h4 : rootSL2 τ L α (HSL (ω ^ 2)) = rootSL2 τ L α 1 := by
      rw [← hk, hk1, map_one]
      rfl
    have h5 := congrArg (fun B : SL2 L => (B : Matrix (Fin 2) (Fin 2) L) 0 0) (hinj h4)
    have h6 : ((ω ^ 2 : Lˣ) : L) = 1 := by simpa [HSL] using h5
    have h7 : ω ^ 2 = 1 := Units.ext (by rw [h6, Units.val_one])
    have h8 := orderOf_dvd_of_pow_eq_one h7
    rw [hω] at h8
    norm_num at h8

theorem pow_three_mem_rootSpan_two (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) {g : ModGL τ L}
    (hg : g ∈ twModel (canonicalRep (coxeterSystem τ) L w₀) (iterateFrobenius L 2 1))
    (hgTL : g ∈ torusGroup τ L ⊔ rootSpan τ L {α, -α}) : g ^ 3 ∈ rootSpan τ L {α, -α} := by
  obtain ⟨μ, hμ⟩ := exists_twFrob_rootSL2 (L := L) hw₀ hα
  have hspan : rootSpan τ L {α, -α} = (rootSL2 τ L α).range := by
    rw [range_rootSL2_of_isRoot hα, rootSpan, iSup_insert, iSup_singleton]
  have hTN : torusGroup τ L ≤ Subgroup.normalizer (rootSpan τ L {α, -α} : Set (ModGL τ L)) :=
    CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan fun β hβ => by
      rcases hβ with rfl | rfl
      · exact hα
      · exact IsRoot.neg hα
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hTN] at hgTL
  obtain ⟨t, ht, l, hl, rfl⟩ := hgTL
  obtain ⟨b, rfl⟩ := torusGroup_le_range_rootDiagUnitHom ht
  obtain ⟨A, rfl⟩ : l ∈ (rootSL2 τ L α).range := hspan ▸ hl
  have hF : canonicalRep (coxeterSystem τ) L w₀ *
      Units.map (entrywiseHom (iterateFrobenius L 2 1))
        (rootDiagUnit τ b * rootSL2 τ L α A) * (canonicalRep (coxeterSystem τ) L w₀)⁻¹ =
      rootDiagUnit τ b * rootSL2 τ L α A := hg.2
  rw [map_mul] at hF
  have e : canonicalRep (coxeterSystem τ) L w₀ *
      (Units.map (entrywiseHom (iterateFrobenius L 2 1)) (rootDiagUnit τ b) *
        Units.map (entrywiseHom (iterateFrobenius L 2 1)) (rootSL2 τ L α A)) *
      (canonicalRep (coxeterSystem τ) L w₀)⁻¹ =
    (canonicalRep (coxeterSystem τ) L w₀ *
      Units.map (entrywiseHom (iterateFrobenius L 2 1)) (rootDiagUnit τ b) *
        (canonicalRep (coxeterSystem τ) L w₀)⁻¹) *
    (canonicalRep (coxeterSystem τ) L w₀ *
      Units.map (entrywiseHom (iterateFrobenius L 2 1)) (rootSL2 τ L α A) *
        (canonicalRep (coxeterSystem τ) L w₀)⁻¹) := by group
  rw [e, twFrob_rootDiagUnit hw₀ b, hμ A] at hF
  set B := conjSL (RankThree.Classical.swapGL * diagUnitOne μ)
    (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 1) A) with hB
  have hb3 : rootDiagUnit τ b ^ 3 ∈ rootSpan τ L {α, -α} := by
    have h1 : rootDiagUnit τ b ^ 3 = rootSL2 τ L α B * (rootSL2 τ L α A)⁻¹ := by
      calc rootDiagUnit τ b ^ 3 = rootDiagUnit τ b ^ 2 *
            (rootDiagUnit τ b * rootSL2 τ L α A) * (rootSL2 τ L α A)⁻¹ := by group
        _ = rootDiagUnit τ b ^ 2 * ((rootDiagUnit τ b)⁻¹ ^ 2 * rootSL2 τ L α B) *
            (rootSL2 τ L α A)⁻¹ := by rw [← hF]
        _ = rootSL2 τ L α B * (rootSL2 τ L α A)⁻¹ := by group
    rw [h1, hspan]
    exact mul_mem ⟨B, rfl⟩ (inv_mem ⟨A, rfl⟩)
  have hlL : rootSL2 τ L α A ∈ rootSpan τ L {α, -α} := by
    rw [hspan]
    exact ⟨A, rfl⟩
  have hc : ∀ k : ℕ, rootDiagUnit τ b ^ k * rootSL2 τ L α A * (rootDiagUnit τ b ^ k)⁻¹ ∈
      rootSpan τ L {α, -α} := fun k =>
    (Subgroup.mem_normalizer_iff.1 (hTN (pow_mem ht k)) _).1 hlL
  have e2 : (rootDiagUnit τ b * rootSL2 τ L α A) ^ 3 =
      (rootDiagUnit τ b ^ 1 * rootSL2 τ L α A * (rootDiagUnit τ b ^ 1)⁻¹) *
        (rootDiagUnit τ b ^ 2 * rootSL2 τ L α A * (rootDiagUnit τ b ^ 2)⁻¹) *
        (rootDiagUnit τ b ^ 3 * rootSL2 τ L α A * (rootDiagUnit τ b ^ 3)⁻¹) *
      rootDiagUnit τ b ^ 3 := by
    simp only [pow_succ, pow_zero, one_mul, mul_inv_rev]
    group
  change (rootDiagUnit τ b * rootSL2 τ L α A) ^ 3 ∈ _
  rw [e2]
  exact mul_mem (mul_mem (mul_mem (hc 1) (hc 2)) (hc 3)) hb3

theorem gLAPPrimeCoreOf_centralizer_dV_two
    (htorL : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ torusGroup τ L)
    (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u) {G : Subgroup (ModGL τ L)} [Finite G]
    (hGW : G ≤ twModel (canonicalRep (coxeterSystem τ) L w₀) (iterateFrobenius L 2 1))
    (h3G : ∀ g ∈ twModel (canonicalRep (coxeterSystem τ) L w₀) (iterateFrobenius L 2 1),
      g ^ 3 = 1 → g ∈ G)
    {ω : Lˣ} (hω : orderOf ω = 3) (hG : ∀ x, dV (τ := τ) ω x ∈ G)
    (hcert : Native.hypOK τ = true) {x : Fin τ.rank → ZMod 3} (hx : x ≠ 0) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer {dG hG x}) = ⊥ := by
  have hGC : G ≤ adjointGroup τ L := hGW.trans inf_le_left
  have hX3 : ∀ g ∈ G, g ∈ torusGroup τ L → g ^ 3 = 1 := fun g hg hgT =>
    pow_three_of_mem_twModel htorL hw₀ (hGW hg) hgT
  have hleaf : ∀ (kb : List (List ℕ)), (∀ b ∈ kb, b.length = τ.rank) →
      (∀ b ∈ kb, ∀ x ∈ b, x < 3) →
      Native.famOK (Native.gramL τ) (Native.rootsN τ) (Native.simpleL τ)
        ((Native.simpleL τ).map fun e => Native.formB (Native.gramL τ) e e) kb = true →
      GLAPPrimeCoreOf 3 (famCent hG kb) = ⊥ := by
    intro kb hlen hlt hok
    refine gLAPPrimeCoreOf_leaf (G := G) hGC hG hX3 ?_
    rcases famData_of_famOK hω hlen hlt hok with h | ⟨α, hα, hker, hW⟩
    · exact Or.inl h
    · exact Or.inr ⟨α, hα, hker, hW, fun g hg hgTL => pow_three_mem_rootSpan_two hw₀ hα (hGW hg)
        hgTL, fun N hNL hnorm hcop => eq_bot_of_le_rootSpan_two hw₀ hω hα hGW
          (fun g hg _ hg3 => h3G g hg hg3) N hNL hnorm hcop⟩
  have hstd := famData0_of_famOK0 (τ := τ) hω length_of_mem_stdBasis lt_of_mem_stdBasis
    (famOK_std_of_hypOK hcert)
  exact gLAPPrimeCoreOf_centralizer_dG hω hG
    (fun fl hfl => hleaf _ (length_of_mem_kerBasis hfl) lt_of_mem_kerBasis
      (famOK_of_hypOK hcert hfl))
    (gLAPPrimeCoreOf_leaf (G := G) hGC hG hX3 (Or.inl hstd)) hx

end RankOne

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

end

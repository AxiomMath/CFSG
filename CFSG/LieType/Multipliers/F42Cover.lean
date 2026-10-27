module

public import CFSG.LieType.Multipliers.F42Check
public import CFSG.LieType.Multipliers.PresentedCover
public import CFSG.LieType.Steinberg.Adjoint.Presentation
public import CFSG.LieType.Steinberg.CentralExt.MultiplierCongr
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.Chevalley.PerfectSimpleRoot
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite

public noncomputable section

namespace CFSG.LieType.Multipliers.F42

open CFSG.F3.Native CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.CentralExt
  CFSG.Open
open scoped commutatorElement

section Roots


theorem isRootB_iff {v : Fin Tag.F4.rank → ℤ} : isRootB v = true ↔ IsRoot .F4 v := by
  rw [isRootB, decide_eq_true_iff, f4_root_certificate.1]

theorem not_isRoot_of_isRootB_eq_false {v : Fin Tag.F4.rank → ℤ} (h : isRootB v = false) :
    ¬IsRoot .F4 v := fun h' => by
  rw [← isRootB_iff, h] at h'
  exact Bool.false_ne_true h'

theorem ofFn_rootAt {k : ℕ} (hk : k < f4ArtifactRoots.length) :
    List.ofFn (rootAt k) = f4ArtifactRoots[k] := by
  have hl : f4ArtifactRoots[k].length = 4 := f4_root_certificate.2.1 _ (List.getElem_mem hk)
  refine List.ext_getElem (by rw [List.length_ofFn, hl]; rfl) fun t h1 h2 => ?_
  rw [List.getElem_ofFn]
  simp only [rootAt]
  rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ h2]

theorem isRoot_rootAt {k : ℕ} (hk : k < 48) : IsRoot .F4 (rootAt k) := by
  have hk' : k < f4ArtifactRoots.length := hk.trans_eq (by decide)
  rw [f4_root_certificate.1, ofFn_rootAt hk']
  exact List.getElem_mem hk'

theorem rootIdx_lt {v : Fin Tag.F4.rank → ℤ} (hv : IsRoot .F4 v) : rootIdx v < 48 :=
  rootIdx_lt_of_isRootB (isRootB_iff.2 hv)

theorem rootAt_rootIdx {v : Fin Tag.F4.rank → ℤ} (hv : IsRoot .F4 v) : rootAt (rootIdx v) = v := by
  have hm := f4_root_certificate.1 v |>.1 hv
  have hk : rootIdx v < f4ArtifactRoots.length := List.idxOf_lt_length_iff.2 hm
  apply List.ofFn_injective
  rw [ofFn_rootAt hk]
  exact List.getElem_idxOf hk

theorem rootIdx_rootAt {k : ℕ} (hk : k < 48) : rootIdx (rootAt k) = k := by
  have hk' : k < f4ArtifactRoots.length := hk.trans_eq (by decide)
  rw [rootIdx, ofFn_rootAt hk']
  exact f4_root_certificate.2.2.1.idxOf_getElem k hk'

end Roots

section Two

variable {K : Type} [Field K]

theorem nonempty_ringEquiv_zmod_two (hK : Nat.card K = 2) : Nonempty (K ≃+* ZMod 2) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have := Fintype.ofFinite K
  exact ⟨FiniteField.ringEquivOfCardEq (by rw [← Nat.card_eq_fintype_card, hK, ZMod.card])⟩

theorem eq_zero_or_eq_one (hK : Nat.card K = 2) (c : K) : c = 0 ∨ c = 1 := by
  obtain ⟨σ⟩ := nonempty_ringEquiv_zmod_two hK
  have h : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases h (σ c) with h | h
  · exact Or.inl (σ.injective (by rw [h, map_zero]))
  · exact Or.inr (σ.injective (by rw [h, map_one]))

theorem one_add_one_eq_zero (hK : Nat.card K = 2) : (1 : K) + 1 = 0 := by
  obtain ⟨σ⟩ := nonempty_ringEquiv_zmod_two hK
  apply σ.injective
  rw [map_add, map_one, map_zero]
  decide

theorem intCast_eq_one (hK : Nat.card K = 2) {n : ℤ} (h : n.natAbs = 1) : (n : K) = 1 := by
  obtain ⟨σ⟩ := nonempty_ringEquiv_zmod_two hK
  apply σ.injective
  rw [map_intCast, map_one]
  rcases Int.natAbs_eq_iff.1 h with rfl | rfl <;> decide

theorem intCast_eq_zero (hK : Nat.card K = 2) {n : ℤ} (h : n.natAbs = 2) : (n : K) = 0 := by
  obtain ⟨σ⟩ := nonempty_ringEquiv_zmod_two hK
  apply σ.injective
  rw [map_intCast, map_zero]
  rcases Int.natAbs_eq_iff.1 h with rfl | rfl <;> decide

end Two

theorem neg_one_ne_one_GL : (-1 : GL (Fin 52) (ZMod 3)) ≠ 1 := by
  intro h
  have h' := congrArg (fun u : GL (Fin 52) (ZMod 3) =>
    (u : Matrix (Fin 52) (Fin 52) (ZMod 3)) 0 0) h
  simp only [Units.val_neg, Units.val_one, Matrix.neg_apply, Matrix.one_apply_eq] at h'
  exact absurd h' (by decide)

section Cover

variable {K : Type} [Field K]

variable (K) in
abbrev rootSys : RootSystem (Fin Tag.F4.rank) :=
  RootSystem.ofCartan (f4Datum K).isFiniteType (f4Datum K).divisible

abbrev coeffs : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℕ × ℕ → ℤ :=
  commC (rootOperatorFamily .F4) f4Data_valid

theorem roots_rootSys : (rootSys K).roots = {γ | IsRoot .F4 γ} :=
  adjDatum_roots (rootOperatorFamily .F4) K

theorem mem_rootSys_iff {γ : Fin Tag.F4.rank → ℤ} : γ ∈ (rootSys K).roots ↔ IsRoot .F4 γ := by
  rw [roots_rootSys]
  rfl

theorem commC_one_one_cast (hK : Nat.card K = 2) {α β : Fin Tag.F4.rank → ℤ}
    (hα : IsRoot .F4 α) (hβ : IsRoot .F4 β) (hsum : α + β ≠ 0) (hr : IsRoot .F4 (α + β)) :
    (IsRoot .F4 (β - α) → ((coeffs α β (1, 1) : ℤ) : K) = 0) ∧
      (¬IsRoot .F4 (β - α) → ((coeffs α β (1, 1) : ℤ) : K) = 1) := by
  have hβα : β ≠ -α := fun h => hsum (by rw [h, add_neg_cancel])
  have hN : (RootOperatorFamily'.coeff11 (rootOperatorFamily .F4) f4Data_valid ⟨α, hα⟩
      ⟨β, hβ⟩).natAbs = stringNorm α β :=
    RootOperatorFamily'.bracketCoeff_natAbs _ _ hβα hr
  rw [coeffs, commC_11 hα hβ hsum]
  refine ⟨fun h => intCast_eq_zero hK ?_, fun h => intCast_eq_one hK ?_⟩
  · rw [hN, stringNorm_of_isRoot h]
  · rw [hN, stringNorm_of_not_isRoot h]

theorem commC_one_two_cast (hK : Nat.card K = 2) {α β : Fin Tag.F4.rank → ℤ}
    (hα : IsRoot .F4 α) (hβ : IsRoot .F4 β) (hne : α ≠ β) (hne' : α ≠ -β)
    (hr : IsRoot .F4 (α + 2 • β)) : ((coeffs α β (1, 2) : ℤ) : K) = 1 := by
  have hsum : α + β ≠ 0 := fun h => hne' (eq_neg_of_add_eq_zero_left h)
  rw [coeffs, commC_12 hα hβ hsum]
  exact intCast_eq_one hK (natAbs_coeff12 (rootOperatorFamily .F4) f4Data_valid noG2_F4
    (α := ⟨α, hα⟩) (β := ⟨β, hβ⟩) hne hne' hr)

theorem commC_two_one_cast (hK : Nat.card K = 2) {α β : Fin Tag.F4.rank → ℤ}
    (hα : IsRoot .F4 α) (hβ : IsRoot .F4 β) (hne : α ≠ β) (hne' : α ≠ -β)
    (hr : IsRoot .F4 (2 • α + β)) : ((coeffs α β (2, 1) : ℤ) : K) = 1 := by
  have hsum : α + β ≠ 0 := fun h => hne' (eq_neg_of_add_eq_zero_left h)
  rw [coeffs, commC_21 hα hβ hsum]
  exact intCast_eq_one hK (natAbs_coeff21 (rootOperatorFamily .F4) f4Data_valid noG2_F4
    (α := ⟨α, hα⟩) (β := ⟨β, hβ⟩) hne hne' hr)

variable (K) in
open _root_.Classical in
@[expose] def coverGen : ChevGen (rootSys K) K → GL (Fin 52) (ZMod 3) :=
  fun g => if g.2 = 0 then 1 else liftGL (rootIdx g.1.1)

variable (K) in
open _root_.Classical in
@[expose] def coverWord : ChevGen (rootSys K) K → FreeGroup (ChevGen (rootSys K) K) :=
  fun g => if g.2 = 0 then 1 else
    ⁅chevOf (Φ := rootSys K) (rootAt (commPair (rootIdx g.1.1)).1) (1 : K),
      chevOf (Φ := rootSys K) (rootAt (commPair (rootIdx g.1.1)).2) (1 : K)⁆

theorem lift_coverGen_chevOf {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot .F4 γ) {c : K}
    (hc : c ≠ 0) :
    FreeGroup.lift (coverGen K) (chevOf (Φ := rootSys K) γ c) = liftGL (rootIdx γ) := by
  classical
  unfold chevOf
  rw [dite_eq_left (mem_rootSys_iff.2 hγ), FreeGroup.lift_apply_of]
  simp [coverGen, hc]

theorem lift_coverGen_chevOf_eq_one {γ : Fin Tag.F4.rank → ℤ} {c : K}
    (h : ¬IsRoot .F4 γ ∨ c = 0) :
    FreeGroup.lift (coverGen K) (chevOf (Φ := rootSys K) γ c) = 1 := by
  classical
  unfold chevOf
  by_cases hγ : γ ∈ (rootSys K).roots
  · rw [dite_eq_left hγ, FreeGroup.lift_apply_of]
    have hc : c = 0 := h.resolve_left (not_not.2 (mem_rootSys_iff.1 hγ))
    simp [coverGen, hc]
  · rw [dite_eq_right hγ, map_one]

theorem lift_coverGen_chevOf_eq_factorGL {γ : Fin Tag.F4.rank → ℤ} {c : K} {b : Bool}
    (hb : (b && isRootB γ) = true ↔ IsRoot .F4 γ ∧ c ≠ 0) :
    FreeGroup.lift (coverGen K) (chevOf (Φ := rootSys K) γ c) = factorGL b γ := by
  by_cases h : (b && isRootB γ) = true
  · rw [factorGL, ite_eq_left h]
    exact lift_coverGen_chevOf (hb.1 h).1 (hb.1 h).2
  · rw [factorGL, ite_eq_right h]
    refine lift_coverGen_chevOf_eq_one ?_
    by_cases hγ : IsRoot .F4 γ
    · exact Or.inr (by_contra fun hc => h (hb.2 ⟨hγ, hc⟩))
    · exact Or.inl hγ

theorem lift_f4Par_chevOf (γ : Fin Tag.F4.rank → ℤ) (c : K) :
    FreeGroup.lift (chevEval (f4Par K)) (chevOf (Φ := rootSys K) γ c) = f4Par K γ c := by
  classical
  unfold chevOf
  by_cases hγ : γ ∈ (rootSys K).roots
  · rw [dite_eq_left hγ, FreeGroup.lift_apply_of]
    rfl
  · rw [dite_eq_right hγ, map_one]
    exact (xPar_of_not_isRoot (fun h => hγ (mem_rootSys_iff.2 h)) c).symm

theorem lift_coverGen_factor (hK : Nat.card K = 2) {α β : Fin Tag.F4.rank → ℤ}
    (hα : IsRoot .F4 α) (hβ : IsRoot .F4 β) (hne : α ≠ β) (hne' : α ≠ -β) :
    FreeGroup.lift (coverGen K) (chevOf (Φ := rootSys K) ((1, 1).1 • α + (1, 1).2 • β)
        ((coeffs α β (1, 1) : K) * 1 ^ (1, 1).1 * 1 ^ (1, 1).2)) =
        fGL (rootIdx α) (rootIdx β) 0 ∧
      FreeGroup.lift (coverGen K) (chevOf (Φ := rootSys K) ((1, 2).1 • α + (1, 2).2 • β)
        ((coeffs α β (1, 2) : K) * 1 ^ (1, 2).1 * 1 ^ (1, 2).2)) =
        fGL (rootIdx α) (rootIdx β) 1 ∧
      FreeGroup.lift (coverGen K) (chevOf (Φ := rootSys K) ((2, 1).1 • α + (2, 1).2 • β)
        ((coeffs α β (2, 1) : K) * 1 ^ (2, 1).1 * 1 ^ (2, 1).2)) =
        fGL (rootIdx α) (rootIdx β) 2 := by
  have hsum : α + β ≠ 0 := fun h => hne' (eq_neg_of_add_eq_zero_left h)
  simp only [one_nsmul, one_pow, mul_one, fGL, rootAt_rootIdx hα, rootAt_rootIdx hβ]
  refine ⟨lift_coverGen_chevOf_eq_factorGL ?_, lift_coverGen_chevOf_eq_factorGL ?_,
    lift_coverGen_chevOf_eq_factorGL ?_⟩
  · rw [Bool.and_eq_true, Bool.not_eq_true', isRootB_iff]
    constructor
    · rintro ⟨h, hr⟩
      refine ⟨hr, ?_⟩
      rw [(commC_one_one_cast hK hα hβ hsum hr).2 (not_isRoot_of_isRootB_eq_false h)]
      exact one_ne_zero
    · rintro ⟨hr, hc⟩
      refine ⟨?_, hr⟩
      by_contra h
      exact hc ((commC_one_one_cast hK hα hβ hsum hr).1
        (isRootB_iff.1 (Bool.not_eq_false _ ▸ h)))
  · rw [Bool.true_and, isRootB_iff]
    exact ⟨fun hr => ⟨hr, by rw [commC_one_two_cast hK hα hβ hne hne' hr]; exact one_ne_zero⟩,
      fun h => h.1⟩
  · rw [Bool.true_and, isRootB_iff]
    exact ⟨fun hr => ⟨hr, by rw [commC_two_one_cast hK hα hβ hne hne' hr]; exact one_ne_zero⟩,
      fun h => h.1⟩

theorem lift_coverGen_relB_one (hK : Nat.card K = 2) (O : CommOrder (rootSys K))
    {α β : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α) (hβ : IsRoot .F4 β) (hne : α ≠ β)
    (hne' : α ≠ -β) :
    FreeGroup.lift (coverGen K) (⁅chevOf (Φ := rootSys K) α (1 : K), chevOf β (1 : K)⁆ *
      ((O.list α β).map fun p => chevOf (p.1 • α + p.2 • β)
        ((coeffs α β p : K) * 1 ^ p.1 * 1 ^ p.2)).prod⁻¹) =
      ⁅liftGL (rootIdx α), liftGL (rootIdx β)⁆ *
        (fGL (rootIdx α) (rootIdx β) 0 * fGL (rootIdx α) (rootIdx β) 1 *
          fGL (rootIdx α) (rootIdx β) 2)⁻¹ := by
  have hsum : α + β ≠ 0 := fun h => hne' (eq_neg_of_add_eq_zero_left h)
  have hΦ := roots_rootSys (K := K)
  have hi := rootIdx_lt hα
  have hj := rootIdx_lt hβ
  have hij : rootIdx α ≠ rootIdx β := fun h => hne (by
    rw [← rootAt_rootIdx hα, h, rootAt_rootIdx hβ])
  have hs : rootAt (rootIdx α) + rootAt (rootIdx β) ≠ 0 := by
    rw [rootAt_rootIdx hα, rootAt_rootIdx hβ]; exact hsum
  obtain ⟨f0, f1, f2⟩ := lift_coverGen_factor hK hα hβ hne hne'
  have hf : ∀ p ∈ pairs₀, ∃ a : Fin 3, FreeGroup.lift (coverGen K) (chevOf (Φ := rootSys K)
      (p.1 • α + p.2 • β) ((coeffs α β p : K) * 1 ^ p.1 * 1 ^ p.2)) =
        fGL (rootIdx α) (rootIdx β) a := by
    intro p hp
    simp only [pairs₀, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, f0⟩
    · exact ⟨1, f1⟩
    · exact ⟨2, f2⟩
  rw [map_mul, map_commutatorElement, map_inv, map_list_prod, List.map_map,
    prod_map_commOrder_list noG2_F4 hΦ O hα hβ hne hne' _ ?_ ?_]
  · simp only [Function.comp_apply]
    rw [f0, f1, f2, lift_coverGen_chevOf hα one_ne_zero, lift_coverGen_chevOf hβ one_ne_zero]
  · intro p hp q hq
    rw [O.mem_iff α (mem_rootSys_iff.2 hα) β (mem_rootSys_iff.2 hβ) hsum,
      mem_expPairs_iff noG2_F4 hΦ hα hβ hne hne'] at hp hq
    obtain ⟨a, ha⟩ := hf p hp.1
    obtain ⟨b, hb⟩ := hf q hq.1
    simp only [Function.comp_apply]
    rw [ha, hb]
    exact commute_fGL hi hj hij hs a b
  · intro p hp
    simp only [Function.comp_apply]
    exact lift_coverGen_chevOf_eq_one (Or.inl hp)

theorem lift_coverGen_relator (hK : Nat.card K = 2) (O : CommOrder (rootSys K))
    {r : FreeGroup (ChevGen (rootSys K) K)}
    (hr : r ∈ relA (rootSys K) K ∪ relB (rootSys K) K O coeffs) :
    FreeGroup.lift (coverGen K) r = 1 ∨ FreeGroup.lift (coverGen K) r = -1 := by
  have hΦ := roots_rootSys (K := K)
  have h2 := one_add_one_eq_zero hK
  rcases hr with ⟨γ, hγ, c, d, rfl⟩ | ⟨α, hα, β, hβ, hsum, c, d, rfl⟩
  · rw [mem_rootSys_iff] at hγ
    rw [map_mul, map_mul, map_inv]
    rcases eq_zero_or_eq_one hK c with rfl | rfl
    · left
      rw [zero_add, lift_coverGen_chevOf_eq_one (Or.inr rfl), one_mul, mul_inv_cancel]
    rcases eq_zero_or_eq_one hK d with rfl | rfl
    · left
      rw [add_zero, lift_coverGen_chevOf_eq_one (γ := γ) (c := (0 : K)) (Or.inr rfl), mul_one,
        mul_inv_cancel]
    rw [h2, lift_coverGen_chevOf_eq_one (γ := γ) (c := (0 : K)) (Or.inr rfl), inv_one, mul_one,
      lift_coverGen_chevOf hγ one_ne_zero]
    exact liftGL_mul_self (rootIdx_lt hγ)
  · rw [mem_rootSys_iff] at hα hβ
    have hzero : ∀ (c d : K), (c = 0 ∨ d = 0) →
        FreeGroup.lift (coverGen K) (⁅chevOf (Φ := rootSys K) α c, chevOf β d⁆ *
          ((O.list α β).map fun p => chevOf (p.1 • α + p.2 • β)
            ((coeffs α β p : K) * c ^ p.1 * d ^ p.2)).prod⁻¹) = 1 := by
      intro c d hcd
      rw [map_mul, map_commutatorElement, map_inv, map_list_prod, List.map_map]
      have hprod : ((O.list α β).map ((FreeGroup.lift (coverGen K)) ∘ fun p =>
          chevOf (Φ := rootSys K) (p.1 • α + p.2 • β)
            ((coeffs α β p : K) * c ^ p.1 * d ^ p.2))).prod = 1 := by
        rw [List.map_congr_left (g := fun _ => (1 : GL (Fin 52) (ZMod 3))) fun p hp => ?_,
          List.prod_map_one]
        rw [O.mem_iff α (mem_rootSys_iff.2 hα) β (mem_rootSys_iff.2 hβ) hsum] at hp
        obtain ⟨hp1, hp2, -⟩ := hp
        simp only [Function.comp_apply]
        refine lift_coverGen_chevOf_eq_one (Or.inr ?_)
        rcases hcd with rfl | rfl
        · rw [zero_pow (Nat.pos_iff_ne_zero.1 hp1), mul_zero, zero_mul]
        · rw [zero_pow (Nat.pos_iff_ne_zero.1 hp2), mul_zero]
      rw [hprod, inv_one, mul_one]
      rcases hcd with rfl | rfl
      · rw [lift_coverGen_chevOf_eq_one (γ := α) (c := (0 : K)) (Or.inr rfl),
          commutatorElement_one_left]
      · rw [lift_coverGen_chevOf_eq_one (γ := β) (c := (0 : K)) (Or.inr rfl),
          commutatorElement_one_right]
    rcases eq_zero_or_eq_one hK c with rfl | rfl
    · exact Or.inl (hzero 0 d (Or.inl rfl))
    rcases eq_zero_or_eq_one hK d with rfl | rfl
    · exact Or.inl (hzero 1 0 (Or.inr rfl))
    by_cases hne : α = β
    · subst hne
      left
      have hnil : O.list α α = [] := List.eq_nil_iff_forall_not_mem.2 fun p hp => by
        rw [O.mem_iff α (mem_rootSys_iff.2 hα) α (mem_rootSys_iff.2 hα) hsum] at hp
        obtain ⟨h1, h2, h3⟩ := hp
        rw [hΦ, ← add_nsmul] at h3
        have := eq_one_of_isRoot_nsmul (τ := .F4) h3
        omega
      rw [hnil, List.map_nil, List.prod_nil, inv_one, mul_one, map_commutatorElement,
        commutatorElement_self]
    · have hne' : α ≠ -β := fun h => hsum (by rw [h, neg_add_cancel])
      rw [lift_coverGen_relB_one hK O hα hβ hne hne']
      have hi := rootIdx_lt hα
      have hj := rootIdx_lt hβ
      have hij : rootIdx α ≠ rootIdx β := fun h => hne (by
        rw [← rootAt_rootIdx hα, h, rootAt_rootIdx hβ])
      have hs : rootAt (rootIdx α) + rootAt (rootIdx β) ≠ 0 := by
        rw [rootAt_rootIdx hα, rootAt_rootIdx hβ]; exact hsum
      rcases comm_liftGL hi hj hij hs with h | h
      · exact Or.inl (by rw [h, mul_inv_cancel])
      · exact Or.inr (by rw [h, neg_mul, mul_inv_cancel])

theorem lift_coverGen_neg (hK : Nat.card K = 2) (O : CommOrder (rootSys K)) :
    FreeGroup.lift (coverGen K) (⁅chevOf (Φ := rootSys K) (rootAt 0) (1 : K),
      chevOf (rootAt 35) (1 : K)⁆ * ((O.list (rootAt 0) (rootAt 35)).map fun p =>
        chevOf (p.1 • rootAt 0 + p.2 • rootAt 35)
          ((coeffs (rootAt 0) (rootAt 35) p : K) * 1 ^ p.1 * 1 ^ p.2)).prod⁻¹) = -1 := by
  obtain ⟨hs, hneg⟩ := comm_liftGL_neg
  have h0 := isRoot_rootAt (k := 0) (by norm_num)
  have h35 := isRoot_rootAt (k := 35) (by norm_num)
  have hne : rootAt 0 ≠ rootAt 35 := fun h => by
    have := congrArg rootIdx h
    rw [rootIdx_rootAt (by norm_num), rootIdx_rootAt (by norm_num)] at this
    omega
  have hne' : rootAt 0 ≠ -rootAt 35 := fun h => hs (by rw [h, neg_add_cancel])
  rw [lift_coverGen_relB_one hK O h0 h35 hne hne', rootIdx_rootAt (by norm_num),
    rootIdx_rootAt (by norm_num), hneg, neg_mul, mul_inv_cancel]

theorem coverWord_mem_commutator (g : ChevGen (rootSys K) K) :
    coverWord K g ∈ commutator (FreeGroup (ChevGen (rootSys K) K)) := by
  classical
  unfold coverWord
  split_ifs
  · exact one_mem _
  · rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem lift_coverWord_coverGen (g : ChevGen (rootSys K) K) :
    FreeGroup.lift (coverGen K) (coverWord K g) = coverGen K g := by
  classical
  obtain ⟨⟨γ, hγ⟩, c⟩ := g
  have hγ' := mem_rootSys_iff.1 hγ
  by_cases hc : c = 0
  · have hL : coverWord K (⟨γ, hγ⟩, c) = 1 := by simp [coverWord, hc]
    have hR : coverGen K (⟨γ, hγ⟩, c) = 1 := by simp [coverGen, hc]
    rw [hL, hR, map_one]
  have hL : coverWord K (⟨γ, hγ⟩, c) = ⁅chevOf (Φ := rootSys K)
      (rootAt (commPair (rootIdx γ)).1) (1 : K),
      chevOf (Φ := rootSys K) (rootAt (commPair (rootIdx γ)).2) (1 : K)⁆ := by
    simp [coverWord, hc]
  have hR : coverGen K (⟨γ, hγ⟩, c) = liftGL (rootIdx γ) := by simp [coverGen, hc]
  rw [hL, hR, map_commutatorElement]
  obtain ⟨h1, h2, -, -, -, -, -, -, hw⟩ := comm_liftGL_commPair (rootIdx_lt hγ')
  rw [lift_coverGen_chevOf (isRoot_rootAt h1) one_ne_zero,
    lift_coverGen_chevOf (isRoot_rootAt h2) one_ne_zero, rootIdx_rootAt h1, rootIdx_rootAt h2]
  exact hw

theorem lift_coverWord_f4Par (hK : Nat.card K = 2) (O : CommOrder (rootSys K))
    (hC : CommutatorFormula (f4Par K) O coeffs) (g : ChevGen (rootSys K) K) :
    FreeGroup.lift (chevEval (f4Par K)) (coverWord K g) = chevEval (f4Par K) g := by
  classical
  have hΦ := roots_rootSys (K := K)
  obtain ⟨⟨γ, hγ⟩, c⟩ := g
  have hγ' := mem_rootSys_iff.1 hγ
  rcases eq_zero_or_eq_one hK c with rfl | rfl
  · have hL : coverWord K (⟨γ, hγ⟩, 0) = 1 := by simp [coverWord]
    rw [hL, map_one]
    exact (xPar_zero γ).symm
  have hL : coverWord K (⟨γ, hγ⟩, 1) = ⁅chevOf (Φ := rootSys K)
      (rootAt (commPair (rootIdx γ)).1) (1 : K),
      chevOf (Φ := rootSys K) (rootAt (commPair (rootIdx γ)).2) (1 : K)⁆ := by
    simp [coverWord]
  rw [hL, map_commutatorElement, lift_f4Par_chevOf, lift_f4Par_chevOf]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := comm_liftGL_commPair (rootIdx_lt hγ')
  have hα := isRoot_rootAt h1
  have hβ := isRoot_rootAt h2
  have hne : rootAt (commPair (rootIdx γ)).1 ≠ rootAt (commPair (rootIdx γ)).2 := fun h => h3 (by
    rw [← rootIdx_rootAt h1, ← rootIdx_rootAt h2]; exact congrArg rootIdx h)
  have hne' : rootAt (commPair (rootIdx γ)).1 ≠ -rootAt (commPair (rootIdx γ)).2 := fun h =>
    h4 (by rw [h, neg_add_cancel])
  rw [rootAt_rootIdx hγ'] at h5
  have hr : IsRoot .F4 (rootAt (commPair (rootIdx γ)).1 + rootAt (commPair (rootIdx γ)).2) := by
    rw [h5]; exact hγ'
  have hx6 : ∀ c : K,
      f4Par K (rootAt (commPair (rootIdx γ)).1 + 2 • rootAt (commPair (rootIdx γ)).2) c = 1 :=
    xPar_of_not_isRoot (not_isRoot_of_isRootB_eq_false h6)
  have hx7 : ∀ c : K,
      f4Par K (2 • rootAt (commPair (rootIdx γ)).1 + rootAt (commPair (rootIdx γ)).2) c = 1 :=
    xPar_of_not_isRoot (not_isRoot_of_isRootB_eq_false h7)
  rw [hC _ (mem_rootSys_iff.2 hα) _ (mem_rootSys_iff.2 hβ) h4 1 1,
    prod_map_commOrder_list noG2_F4 hΦ O hα hβ hne hne' _ ?_ ?_]
  · simp only [one_nsmul, one_pow, mul_one]
    rw [hx6, hx7, mul_one, mul_one,
      (commC_one_one_cast hK hα hβ h4 hr).2 (not_isRoot_of_isRootB_eq_false h8), h5]
    rfl
  · intro p hp q hq
    rw [O.mem_iff _ (mem_rootSys_iff.2 hα) _ (mem_rootSys_iff.2 hβ) h4] at hp hq
    exact commute_xPar_pairs f4Data_valid noG2_F4 hα hβ hne hne' hp.1 hp.2.1 hq.1 hq.2.1 _ _
  · intro p hp
    exact xPar_of_not_isRoot hp _

theorem exists_isPresentation [Finite K] :
    ∃ O : CommOrder (rootSys K), CommutatorFormula (f4Par K) O coeffs ∧
      IsPresentation (chevEval (f4Par K)) (relA (rootSys K) K ∪ relB (rootSys K) K O coeffs) := by
  obtain ⟨-, ⟨O⟩, hPB, -⟩ := f4_conclusionB K
  have hC : CommutatorFormula (f4Par K) O coeffs :=
    commutatorFormula_commC f4Data_valid noG2_F4 _ (adjDatum_roots _ K) O
  obtain ⟨h, hbij⟩ := (hPB O).2 coeffs hC
  exact ⟨O, hC, IsPresentation.of_bijective h hbij⟩

theorem isPerfect_adjointGroup (hK : Nat.card K = 2) : Group.IsPerfect (adjointGroup .F4 K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  obtain ⟨O, hC, hP⟩ := exists_isPresentation (K := K)
  exact isPerfect_of_isPresentation hP coverWord_mem_commutator (lift_coverWord_f4Par hK O hC)

theorem exists_two_dvd_orderOf (hK : Nat.card K = 2) :
    ∃ z : griessHopfMultiplier (adjointGroup .F4 K), 2 ∣ orderOf z := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  obtain ⟨O, hC, hP⟩ := exists_isPresentation (K := K)
  have hw := coverWord_mem_commutator (K := K)
  have hwg := lift_coverWord_f4Par hK O hC
  have he : ∀ r ∈ coverRelators (relA (rootSys K) K ∪ relB (rootSys K) K O coeffs) (coverWord K),
      FreeGroup.lift (coverGen K) r = 1 := by
    refine lift_coverRelators_eq_one_iff.2 ⟨fun i r hr => ?_, lift_coverWord_coverGen⟩
    rcases lift_coverGen_relator hK O hr with h | h
    · rw [h, commutatorElement_one_right]
    · rw [h, commutatorElement_eq_one_iff_commute]
      exact (Commute.one_right _).neg_right
  set r₀ := ⁅chevOf (Φ := rootSys K) (rootAt 0) (1 : K),
    chevOf (Φ := rootSys K) (rootAt 35) (1 : K)⁆ *
    ((O.list (rootAt 0) (rootAt 35)).map fun p => chevOf (p.1 • rootAt 0 + p.2 • rootAt 35)
      ((coeffs (rootAt 0) (rootAt 35) p : K) * 1 ^ p.1 * 1 ^ p.2)).prod⁻¹ with hr₀
  have hmem : r₀ ∈ relA (rootSys K) K ∪ relB (rootSys K) K O coeffs :=
    Or.inr ⟨rootAt 0, mem_rootSys_iff.2 (isRoot_rootAt (by norm_num)), rootAt 35,
      mem_rootSys_iff.2 (isRoot_rootAt (by norm_num)), comm_liftGL_neg.1, 1, 1, rfl⟩
  have hz : (PresentedGroup.mk _ r₀ : PresentedCover _ (coverWord K)) ∈
      (coverMap hP hwg).ker := by
    rw [MonoidHom.mem_ker, coverMap_mk]
    exact hP.lift_eq_one hmem
  have hρ : PresentedGroup.toGroup he (PresentedGroup.mk _ r₀) = -1 :=
    lift_coverGen_neg hK O
  have h2 : 2 ∣ orderOf (PresentedGroup.mk _ r₀ :
      PresentedCover (relA (rootSys K) K ∪ relB (rootSys K) K O coeffs) (coverWord K)) := by
    have hneg : orderOf (-1 : GL (Fin 52) (ZMod 3)) = 2 :=
      orderOf_eq_prime (by rw [neg_one_sq]) neg_one_ne_one_GL
    rw [← hneg, ← hρ]
    exact orderOf_map_dvd _ _
  refine ⟨(griessHopfMultiplierEquivKer hP hw hwg).symm ⟨_, hz⟩, ?_⟩
  rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
  exact h2

theorem two_dvd_card_griessHopfMultiplier (hK : Nat.card K = 2) :
    2 ∣ Nat.card (griessHopfMultiplier (adjointGroup .F4 K)) := by
  obtain ⟨z, hz⟩ := exists_two_dvd_orderOf hK
  exact hz.trans (orderOf_dvd_natCard z)

theorem exists_orderOf_eq_two (hK : Nat.card K = 2) :
    Finite (griessHopfMultiplier (adjointGroup .F4 K)) ∧
      ∃ z : griessHopfMultiplier (adjointGroup .F4 K), orderOf z = 2 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Finite (adjointGroup .F4 K) := generated_group_finite .F4 K
  have : Finite (CFSG.RankThree.PerfectCover.hopfMultiplier (adjointGroup .F4 K)) :=
    CFSG.RankThree.PerfectCover.finite_hopfMultiplier (isPerfect_adjointGroup hK)
  have : Finite (griessHopfMultiplier (adjointGroup .F4 K)) :=
    Finite.of_equiv _ (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).symm.toEquiv
  exact ⟨inferInstance, exists_prime_orderOf_dvd_card' 2 (two_dvd_card_griessHopfMultiplier hK)⟩

theorem nontrivial_griessHopfMultiplier (hK : Nat.card K = 2) :
    Nontrivial (griessHopfMultiplier (adjointGroup .F4 K)) := by
  obtain ⟨z, hz⟩ := exists_two_dvd_orderOf hK
  refine ⟨⟨z, 1, fun h => ?_⟩⟩
  rw [h, orderOf_one] at hz
  omega

theorem two_dvd_card_griessHopfMultiplier_of_mulEquiv (hK : Nat.card K = 2) {X : Type}
    [Group X] (e : X ≃* adjointGroup .F4 K) : 2 ∣ Nat.card (griessHopfMultiplier X) := by
  rw [Nat.card_congr (griessHopfMultiplierCongr e).toEquiv]
  exact two_dvd_card_griessHopfMultiplier hK

end Cover

section Quotient

variable {K : Type} [Field K]

theorem two_dvd_card_griessHopfMultiplier_adjointQuotient (hK : Nat.card K = 2) :
    2 ∣ Nat.card (griessHopfMultiplier (AdjointQuotient .F4 K)) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  exact two_dvd_card_griessHopfMultiplier_of_mulEquiv hK
    ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot)

end Quotient

end CFSG.LieType.Multipliers.F42

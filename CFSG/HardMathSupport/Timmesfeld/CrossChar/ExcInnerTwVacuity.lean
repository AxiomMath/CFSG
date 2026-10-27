module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidSplit
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.BadThreeLang
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidSetup

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

section Torsion

theorem langTorusPlaneBalance_of_twistedTorus_torsion_le {τ : Tag} {w : WeylGroup τ} {p : ℕ}
    {Q : ℕ → Prop}
    (h : ∀ (K : Type) [Field K] [Finite K], Q (Nat.card K) →
      ∀ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ Nat.card K) →
      ∀ D : Subgroup (ModGL τ (AlgebraicClosure K)),
        D ≤ twistedTorusOf (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
          (Units.map (entrywiseHom Fr)) →
        (∀ x ∈ D, x ^ p = 1) → Finite D → Nat.card D ≤ p) :
    LangTorusPlaneBalance τ w p Q := by
  classical
  intro K _ _ hQK Fr hFr g0 hg0C hg0 D₀ hpow hcard htor H hH
  exfalso
  have : Finite (ModGL τ K) := finite_modGL
  set L := AlgebraicClosure K
  set f : adjointGroup τ K →* ModGL τ L := ((MulAut.conj g0⁻¹).toMonoidHom).comp
    ((baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype) with hf
  have hfinj : Function.Injective f := (MulAut.conj g0⁻¹).injective.comp
    ((baseChangeGL_injective _).comp (Subgroup.subtype_injective _))
  have hDT : D₀.map f ≤
      twistedTorusOf (canonicalRep (coxeterSystem τ) L w) (Units.map (entrywiseHom Fr)) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, ht, hte⟩ := htor x hx
    change g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL τ K) * g0⁻¹⁻¹ ∈ _
    rw [← hte]
    change g0⁻¹ * (g0 * t * g0⁻¹) * g0⁻¹⁻¹ ∈ _
    rw [show g0⁻¹ * (g0 * t * g0⁻¹) * g0⁻¹⁻¹ = t by group]
    exact ht
  have hDp : ∀ y ∈ D₀.map f, y ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hpow x hx, map_one]
  have hDfin : Finite (D₀.map f) :=
    Finite.of_surjective (f.subgroupMap D₀) (f.subgroupMap_surjective D₀)
  have h1 := h K hQK Fr hFr _ hDT hDp hDfin
  rw [Subgroup.card_map_of_injective hfinj] at h1
  omega

end Torsion

private theorem zpow_finset_sum_eq_prod {G : Type*} [CommGroup G] {ι : Type*} (g : G)
    (s : Finset ι) (f : ι → ℤ) : g ^ (∑ i ∈ s, f i) = ∏ i ∈ s, g ^ f i := by
  classical
  refine Finset.induction_on s (by simp) fun i s hi ih => ?_
  rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

section Matrix

theorem natCast_ne_zero_of_not_dvd_card (K : Type) [Field K] [Finite K] (L : Type) [Field L]
    [Algebra K L] {p : ℕ} (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K) : (p : L) ≠ 0 := by
  have : Fintype K := Fintype.ofFinite K
  have hK0 : ((Nat.card K : ℕ) : L) = 0 := by
    rw [← map_natCast (algebraMap K L), Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero K,
      map_zero]
  intro hp0
  have hcop : IsCoprime ((p : ℕ) : ℤ) ((Nat.card K : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpK)
  obtain ⟨u, v, huv⟩ := hcop
  have h := congrArg (Int.cast : ℤ → L) huv
  push_cast at h
  rw [hp0, hK0, mul_zero, mul_zero, add_zero] at h
  exact zero_ne_one h

theorem langTorusPlaneBalance_of_eigenspace_line {τ : Tag} {w : WeylGroup τ}
    {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} (hw : ∀ u, w • u = M *ᵥ u) {p : ℕ} (hp : p.Prime)
    {Q : ℕ → Prop} (hQp : ∀ q, Q q → ¬ p ∣ q)
    (hline : ∀ q, Q q → ∃ c : Fin τ.rank → ZMod p, ∀ v : Fin τ.rank → ZMod p,
      (M.map (Int.cast : ℤ → ZMod p)).transpose *ᵥ v = (q : ZMod p) • v →
        ∃ t : ZMod p, v = t • c) :
    LangTorusPlaneBalance τ w p Q := by
  classical
  refine langTorusPlaneBalance_of_twistedTorus_torsion_le
    fun K _ _ hQK Fr hFr D hDT hDp hDfin => ?_
  set L := AlgebraicClosure K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨c, hc⟩ := hline _ hQK
  have : NeZero ((p : ℕ) : L) := ⟨natCast_ne_zero_of_not_dvd_card K L hp (hQp _ hQK)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L p
  set ζu : Lˣ := (hζ.isUnit hp.ne_zero).unit with hζu
  have hζu' : IsPrimitiveRoot ζu p :=
    IsPrimitiveRoot.coe_units_iff.1 (by simpa [hζu] using hζ)
  have hya : ∀ y : D, ∃ a : Fin τ.rank → Lˣ, rootDiagUnit τ a = (y : ModGL τ L) := fun y => by
    obtain ⟨a, ha⟩ := torusGroup_le_range_rootDiagUnitHom (mem_twistedTorusOf.1 (hDT y.2)).1
    exact ⟨a, ha⟩
  choose a ha using hya
  have hafix : ∀ y : D, a y ∈ fixedCharTuples M Fr := fun y => by
    rw [← twistedFixedTuples_eq_fixedCharTuples hw Fr]
    refine mem_twistedFixedTuples_iff_conj.2 ?_
    rw [ha y]
    exact (mem_twistedTorusOf.1 (hDT y.2)).2
  have hapow : ∀ (y : D) (i : Fin τ.rank), a y i ^ p = 1 := fun y i => by
    have h1 : rootDiagUnit τ (a y ^ p) = rootDiagUnit τ 1 := by
      change rootDiagUnitHom τ L (a y ^ p) = rootDiagUnitHom τ L 1
      rw [map_pow, map_one]
      change rootDiagUnit τ (a y) ^ p = 1
      rw [ha y]
      exact hDp _ y.2
    simpa using congrFun (rootDiagUnit_injective h1) i
  have hlog : ∀ (y : D) (i : Fin τ.rank), ∃ k : ℕ, k < p ∧ ζu ^ k = a y i := fun y i => by
    obtain ⟨k, hk, hk'⟩ := hζ.eq_pow_of_pow_eq_one (ξ := (a y i : L))
      (by rw [← Units.val_pow_eq_pow_val, hapow y i, Units.val_one])
    exact ⟨k, hk, Units.ext (by rw [Units.val_pow_eq_pow_val, hζu, IsUnit.unit_spec, hk'])⟩
  choose k hk hka using hlog
  set v : D → Fin τ.rank → ZMod p := fun y i => (k y i : ZMod p) with hv
  have heig : ∀ y : D, (M.map (Int.cast : ℤ → ZMod p)).transpose *ᵥ v y =
      (Nat.card K : ZMod p) • v y := by
    intro y
    funext j
    have h1 := (mem_fixedCharTuples_iff.1 (hafix y)) (Pi.single j 1)
    have hMj : M *ᵥ Pi.single j 1 = fun i => M i j := by
      funext i
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have hl : FourGroupChevalley.rootChar (a y) (M *ᵥ Pi.single j 1) =
        ζu ^ (∑ i, (k y i : ℤ) * M i j) := by
      rw [hMj, zpow_finset_sum_eq_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← hka y i, zpow_mul, zpow_natCast]
    have hr : Units.map Fr.toMonoidHom (FourGroupChevalley.rootChar (a y) (Pi.single j 1)) =
        ζu ^ ((Nat.card K : ℤ) * (k y j : ℤ)) := by
      rw [CTTorus.rootChar_single, ← hka y j, show ((Nat.card K : ℤ) * (k y j : ℤ)) =
        ((k y j * Nat.card K : ℕ) : ℤ) by push_cast; ring, zpow_natCast, pow_mul]
      refine Units.ext ?_
      rw [Units.coe_map, Units.val_pow_eq_pow_val (ζu ^ k y j)]
      exact hFr _
    rw [hl, hr] at h1
    have h2 : ζu ^ ((∑ i, (k y i : ℤ) * M i j) - (Nat.card K : ℤ) * (k y j : ℤ)) = 1 := by
      rw [zpow_sub, h1, mul_inv_cancel]
    have h3 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 ((hζu'.zpow_eq_one_iff_dvd _).1 h2)
    push_cast at h3
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply,
      Pi.smul_apply, smul_eq_mul, hv]
    rw [← sub_eq_zero, ← h3]
    congr 1
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hlinev : ∀ y : D, ∃ t : ZMod p, v y = t • c := fun y => hc _ (heig y)
  choose t ht using hlinev
  have htinj : Function.Injective t := by
    intro y y' hyy
    have hvv : v y = v y' := by rw [ht y, ht y', hyy]
    have hkk : ∀ i, k y i = k y' i := fun i => by
      have h1 := congrFun hvv i
      simp only [hv] at h1
      rw [← ZMod.val_natCast_of_lt (hk y i), ← ZMod.val_natCast_of_lt (hk y' i), h1]
    have haa : a y = a y' := funext fun i => by rw [← hka y i, ← hka y' i, hkk i]
    exact Subtype.ext (by rw [← ha y, ← ha y', haa])
  have h1 := Nat.card_le_card_of_injective t htinj
  rwa [Nat.card_zmod] at h1

theorem langTorusPlaneBalance_neg_of_not_dvd {τ : Tag} {w : WeylGroup τ}
    (hw : ∀ u : Fin τ.rank → ℤ, w • u = -u) {p : ℕ} (hp : p.Prime) {Q : ℕ → Prop}
    (hQ : ∀ q, Q q → ¬ p ∣ q ∧ ¬ p ∣ q + 1) : LangTorusPlaneBalance τ w p Q := by
  refine langTorusPlaneBalance_of_eigenspace_line (M := -1)
    (fun u => by rw [hw u, Matrix.neg_mulVec, Matrix.one_mulVec]) hp (fun q hq => (hQ q hq).1)
    fun q hq => ⟨0, fun v hv => ⟨0, ?_⟩⟩
  have hneg : ((-1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ).map (Int.cast : ℤ → ZMod p)).transpose
      *ᵥ v = -v := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.neg_apply, Matrix.one_apply, Int.cast_neg, Int.cast_ite, Int.cast_one, Int.cast_zero,
      neg_mul, ite_mul, one_mul, zero_mul, Pi.neg_apply]
    rw [Finset.sum_neg_distrib, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]
  have hv' : -v = (q : ZMod p) • v := by rw [← hneg, hv]
  have h1 : ((q + 1 : ℕ) : ZMod p) • v = 0 := by
    rw [Nat.cast_add, Nat.cast_one, add_smul, one_smul, ← hv', neg_add_cancel]
  have hu : IsUnit ((q + 1 : ℕ) : ZMod p) :=
    (ZMod.isUnit_iff_coprime (q + 1) p).2 ((Nat.Prime.coprime_iff_not_dvd hp).2 (hQ q hq).2).symm
  rw [zero_smul]
  funext i
  have h3 := congrFun h1 i
  rw [Pi.smul_apply, smul_eq_mul] at h3
  exact hu.mul_right_eq_zero.1 h3

end Matrix

theorem threeLargeQ_regime {q : ℕ} (hq : ThreeLargeQ q) : ¬ 3 ∣ q ∧ (3 ∣ q + 1 → 4 ≤ q) :=
  ⟨hq.1, fun h => by
    obtain ⟨-, h2, -⟩ := hq
    rcases Nat.lt_or_ge q 4 with h4 | h4
    · interval_cases q <;> omega
    · exact h4⟩

section Consumers

theorem langTorusPlaneBalance_neg {τ : Tag} (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8)
    {w : WeylGroup τ} (hw : ∀ u : Fin τ.rank → ℤ, w • u = -u) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {Q : ℕ → Prop} (hQ : ∀ q, 2 ≤ q → Q q → ¬ p ∣ q ∧ (p ∣ q + 1 → 4 ≤ q))
    (hsub : LangSubnormal) (hin : LangComponentsQuasisimple .inner)
    (hsu : LangComponentsQuasisimple .suN) (htw : LangComponentsQuasisimple .twoD)
    (hex : LangComponentsQuasisimple .exc) : LangTorusPlaneBalance τ w p Q := by
  have hdvd : LangTorusPlaneBalance τ w p fun q => Q q ∧ p ∣ q + 1 :=
    langTorusPlaneBalance_neg_of_components hτ hw hp hp2
      (fun q hq2 hq => ⟨(hQ q hq2 hq.1).1, hq.2, (hQ q hq2 hq.1).2 hq.2⟩) hsub hin hsu htw hex
  have hnd : LangTorusPlaneBalance τ w p fun q => Q q ∧ ¬ p ∣ q + 1 ∧ 2 ≤ q :=
    langTorusPlaneBalance_neg_of_not_dvd hw hp fun q hq => ⟨(hQ q hq.2.2 hq.1).1, hq.2.1⟩
  intro K _ _ hQK
  by_cases h : p ∣ Nat.card K + 1
  · exact hdvd K ⟨hQK, h⟩
  · exact hnd K ⟨hQK, h, Finite.one_lt_card⟩

theorem langTorusPlaneBalance_forall_of_ne_one_neg {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8) {w₀ : WeylGroup τ}
    (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Q : ℕ → Prop} (hQ : ∀ q, 2 ≤ q → Q q → ¬ p ∣ q ∧ (p ∣ q + 1 → 4 ≤ q))
    (hsub : LangSubnormal)
    (hin : LangComponentsQuasisimple .inner) (hsu : LangComponentsQuasisimple .suN)
    (htw : LangComponentsQuasisimple .twoD) (hex : LangComponentsQuasisimple .exc)
    (hne : ∀ w : WeylGroup τ, w ≠ 1 → w ≠ w₀ → LangTorusPlaneBalance τ w p Q)
    (w : WeylGroup τ) : LangTorusPlaneBalance τ w p Q := by
  have hτ' : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h
    exacts [Or.inl h, Or.inr (Or.inr (Or.inl h)), Or.inr (Or.inr (Or.inr h))]
  by_cases h1 : w = 1
  · rw [h1]
    exact langTorusPlaneBalance_one hτ' hp hp2 Q hsub hin hsu htw hex
  · by_cases h0 : w = w₀
    · rw [h0]
      exact langTorusPlaneBalance_neg hτ hw₀ hp hp2 hQ hsub hin hsu htw hex
    · exact hne w h1 h0

theorem langTorusPlaneBalance_F4_three_of_ne (hsub : LangSubnormal)
    (hin : LangComponentsQuasisimple .inner) (hsu : LangComponentsQuasisimple .suN)
    (htw : LangComponentsQuasisimple .twoD) (hex : LangComponentsQuasisimple .exc)
    (hne : ∀ w : WeylGroup Tag.F4, w ≠ 1 → w ≠ f4Neg →
      LangTorusPlaneBalance Tag.F4 w 3 ThreeLargeQ) (w : WeylGroup Tag.F4) :
    LangTorusPlaneBalance Tag.F4 w 3 ThreeLargeQ :=
  langTorusPlaneBalance_forall_of_ne_one_neg (Or.inl rfl) f4Neg_smul Nat.prime_three
    (by norm_num) (fun _ _ hq => threeLargeQ_regime hq) hsub hin hsu htw hex hne w

end Consumers

end CFSG.HardMathSupport.Timmesfeld.CrossChar

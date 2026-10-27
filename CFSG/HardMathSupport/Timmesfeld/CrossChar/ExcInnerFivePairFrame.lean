module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFivePairRigid
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidModels

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.Steinberg.Adjoint
open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false


section Units

variable {L : Type} [Field L] [IsAlgClosed L]

theorem exists_orderOf_eq_of_natCast_ne_zero {N : ℕ} (hN : (N : L) ≠ 0) :
    ∃ ζ : Lˣ, orderOf ζ = N := by
  have hNpos : N ≠ 0 := fun h => hN (by rw [h, Nat.cast_zero])
  have : NeZero ((N : ℕ) : L) := ⟨hN⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L N
  set ζu : Lˣ := (hζ.isUnit hNpos).unit with hζu
  have hζu' : IsPrimitiveRoot ζu N :=
    IsPrimitiveRoot.coe_units_iff.1 (by simpa [hζu] using hζ)
  exact ⟨ζu, hζu'.eq_orderOf.symm⟩

theorem natCast_ne_zero_of_dvd_pow_sub_one {q k N : ℕ} (hq : (q : L) = 0) (hq1 : 1 ≤ q)
    (hk : 1 ≤ k) (hN : N ∣ q ^ k - 1) : (N : L) ≠ 0 := by
  intro h0
  obtain ⟨m, hm⟩ := hN
  have hqk : 1 ≤ q ^ k := Nat.one_le_pow _ _ hq1
  have h1 : ((q ^ k - 1 : ℕ) : L) = 0 := by rw [hm, Nat.cast_mul, h0, zero_mul]
  rw [Nat.cast_sub hqk, Nat.cast_pow, hq, zero_pow (by omega), Nat.cast_one, zero_sub,
    neg_eq_zero] at h1
  exact one_ne_zero h1

end Units

section Frame

variable {L : Type} [Field L] [IsAlgClosed L]

theorem exists_frame_inverted {τ : Tag} {K : Type} [Field K] [Finite K] [Algebra K L]
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card K) (hK4 : 4 ≤ Nat.card K)
    (hdeg : entryDegreeBound τ < Nat.card K) {w : WeylGroup τ} {g0 : ModGL τ L}
    (hg0C : g0 ∈ adjointGroup τ L)
    (hg0 : Units.map (entrywiseHom Fr) g0 = g0 * canonicalRep (coxeterSystem τ) L w)
    {i : Fin τ.rank} (hw : w • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single i 1) :
    ∃ X : Subgroup (ModGL τ L),
      X ≤ (LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0).Γ ∧ ⁅X, X⁆ = X ∧
      X ≤ rootSpan τ L {Pi.single i 1, -Pi.single i 1} ∧
      (∀ ζ : Lˣ, ζ ^ (Nat.card K + 1) = 1 → torusElt τ L i ζ ∈ X) ∧
      ∀ z : ModGL τ L, (∀ x ∈ X, Commute z x) →
        ∀ x ∈ rootRankOneGroup τ L (Pi.single i 1), Commute z x := by
  classical
  obtain ⟨P, hiff, hPH⟩ := exists_twisted_rootSL2 (K := K) hFr (isRoot_single τ i) hw
  obtain ⟨-, hqs⟩ := sl2_conj_range_quasisimple (K := K) (L := L) hK4 P
  set S₀ := (Matrix.SpecialLinearGroup.map (algebraMap K L)).range.map (conjSL P) with hS₀
  set X := S₀.map (rootSL2 τ L (Pi.single i 1)) with hX
  have hXp : ⁅X, X⁆ = X := by
    rw [hX, ← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hqs.1]
  have hXM : X ≤ (LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0).model := by
    rintro _ ⟨B, hB, rfl⟩
    exact ⟨rootSL2_mem_adjointGroup _ B, (hiff B).2 hB⟩
  refine ⟨X, ?_, hXp, ?_, fun ζ hζ => ?_, fun z hz => ?_⟩
  · rw [← hXp]
    exact Subgroup.commutator_mono hXM hXM
  · rintro _ ⟨B, -, rfl⟩
    exact rootSL2_mem_rootSpan_pair (isRoot_single τ i) B
  · obtain ⟨_, ⟨A', rfl⟩, hA'⟩ := hPH ζ hζ
    exact ⟨_, ⟨_, ⟨A', rfl⟩, rfl⟩, by rw [hA', rootSL2_single, simpleRootSL2_HSL]⟩
  · have : Fintype K := Fintype.ofFinite K
    exact commute_rootRankOneGroup_of_twisted (algebraMap K L)
      (by rwa [← Nat.card_eq_fintype_card]) _ P fun A => hz _ ⟨_, ⟨_, ⟨A, rfl⟩, rfl⟩, rfl⟩

theorem exists_split_rootSL2_twist {t : TwistTag} {K₀ : Type} [Field K₀] [Finite K₀]
    [Algebra K₀ L] {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card K₀) {w : WeylGroup t.tag}
    {β : Fin t.tag.rank → ℤ} (hβ : IsRoot t.tag β) (hw : w • permLattice t.perm β = β) :
    ∃ P : GL (Fin 2) L,
      (∀ B : SL2 L, canonicalRep (coxeterSystem t.tag) L w *
          twistHom t L Fr (rootSL2 t.tag L β B) *
            (canonicalRep (coxeterSystem t.tag) L w)⁻¹ = rootSL2 t.tag L β B ↔
        B ∈ (Matrix.SpecialLinearGroup.map (algebraMap K₀ L)).range.map (conjSL P)) ∧
      ∀ ζ : Lˣ, ζ ^ (Nat.card K₀ - 1) = 1 →
        HSL ζ ∈ (Matrix.SpecialLinearGroup.map (algebraMap K₀ L)).range.map (conjSL P) := by
  set n := canonicalRep (coxeterSystem t.tag) L w with hn
  have hnM : n ∈ monomialSubgroup t.tag L := canonicalRep_mem_monomialSubgroup L w
  have hwq : weylQuotientHom t.tag L ⟨n, hnM⟩ = w :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep w)
  obtain ⟨s, hs⟩ := exists_conj_rootSL2_eq_twist hnM hβ
  rw [hwq, hw] at hs
  obtain ⟨P, hP⟩ := exists_twist_diag (K := K₀) Fr hFr s
  have hact : ∀ B : SL2 L, n * twistHom t L Fr (rootSL2 t.tag L β B) * n⁻¹ =
      rootSL2 t.tag L β (conjSL (P * Matrix.GeneralLinearGroup.map Fr P⁻¹)
        (Matrix.SpecialLinearGroup.map Fr B)) := fun B => by
    have h1 : twistHom t L Fr (rootSL2 t.tag L β B) = diagramMap t L *
        rootSL2 t.tag L β (Matrix.SpecialLinearGroup.map Fr B) * (diagramMap t L)⁻¹ := by
      simp only [twistHom, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      rw [entrywise_rootSL2_of_field]
    rw [h1, hP, ← hs]
    group
  refine ⟨P, fun B => a1_hS1_of_action Fr hFr P hact B, fun ζ hζ => ?_⟩
  rw [← sl2_twistedFixed_iff Fr (frobenius_fixed_iff Fr hFr) P, hP, sl2_map_HSL,
    conjSL_diagUnitOne_HSL, units_map_eq_self_of_pow Nat.card_pos hFr hζ]

theorem exists_frame_fixed_twist {t : TwistTag} {K₀ : Type} [Field K₀] [Finite K₀]
    [Algebra K₀ L] {Fr : L →+* L} {q : ℕ} (hqK : Nat.card K₀ = q) (hFr : ∀ c, Fr c = c ^ q)
    (hK4 : 4 ≤ q) (hdeg : entryDegreeBound t.tag < q) {w : WeylGroup t.tag}
    {g0 : ModGL t.tag L} (hg0C : g0 ∈ adjointGroup t.tag L)
    (hg0 : twistHom t L Fr g0 = g0 * canonicalRep (coxeterSystem t.tag) L w)
    {i : Fin t.tag.rank}
    (hw : w • permLattice t.perm (Pi.single i 1 : Fin t.tag.rank → ℤ) = Pi.single i 1) :
    ∃ X : Subgroup (ModGL t.tag L),
      X ≤ (LangDatum.ofTwist t Fr q hFr w hg0C hg0).Γ ∧ ⁅X, X⁆ = X ∧
      X ≤ rootSpan t.tag L {Pi.single i 1, -Pi.single i 1} ∧
      (∀ ζ : Lˣ, ζ ^ (q - 1) = 1 → torusElt t.tag L i ζ ∈ X) ∧
      ∀ z : ModGL t.tag L, (∀ x ∈ X, Commute z x) →
        ∀ x ∈ rootRankOneGroup t.tag L (Pi.single i 1), Commute z x := by
  classical
  subst hqK
  obtain ⟨P, hiff, hPH⟩ := exists_split_rootSL2_twist (K₀ := K₀) hFr (isRoot_single t.tag i) hw
  obtain ⟨-, hqs⟩ := sl2_conj_range_quasisimple (K := K₀) (L := L) hK4 P
  set S₀ := (Matrix.SpecialLinearGroup.map (algebraMap K₀ L)).range.map (conjSL P) with hS₀
  set X := S₀.map (rootSL2 t.tag L (Pi.single i 1)) with hX
  have hXp : ⁅X, X⁆ = X := by
    rw [hX, ← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hqs.1]
  have hXM : X ≤ (LangDatum.ofTwist t Fr (Nat.card K₀) hFr w hg0C hg0).model := by
    rintro _ ⟨B, hB, rfl⟩
    exact ⟨rootSL2_mem_adjointGroup _ B, (hiff B).2 hB⟩
  refine ⟨X, ?_, hXp, ?_, fun ζ hζ => ?_, fun z hz => ?_⟩
  · rw [← hXp]
    exact Subgroup.commutator_mono hXM hXM
  · rintro _ ⟨B, -, rfl⟩
    exact rootSL2_mem_rootSpan_pair (isRoot_single t.tag i) B
  · obtain ⟨_, ⟨A', rfl⟩, hA'⟩ := hPH ζ hζ
    exact ⟨_, ⟨_, ⟨A', rfl⟩, rfl⟩, by rw [hA', rootSL2_single, simpleRootSL2_HSL]⟩
  · have : Fintype K₀ := Fintype.ofFinite K₀
    exact commute_rootRankOneGroup_of_twisted (algebraMap K₀ L)
      (by rwa [← Nat.card_eq_fintype_card]) _ P fun A => hz _ ⟨_, ⟨_, ⟨A, rfl⟩, rfl⟩, rfl⟩

theorem exists_pairGroup_frame {τ : Tag} (hdeg : entryDegreeBound τ = 2) {K₂ : Type} [Field K₂]
    [Finite K₂] [Algebra K₂ L] {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) (hq4 : 4 ≤ q)
    (hK₂ : Nat.card K₂ = q ^ 2) (hqL : (q : L) = 0) (m : ModGL τ L) {β β' : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (hβ' : IsRoot τ β') (h0 : iform β' β = 0)
    (hcomm : ∀ A B : SL2 L, Commute (rootSL2 τ L β A) (rootSL2 τ L β' B)) (s₁ s₂ : Lˣ)
    (h₁ : ∀ A, m * rootSL2 τ L β A * m⁻¹ = rootSL2 τ L β' (conjSL (diagUnitOne s₁) A))
    (h₂ : ∀ A, m * rootSL2 τ L β' A * m⁻¹ = rootSL2 τ L β (conjSL (diagUnitOne s₂) A)) :
    ∃ Y : Subgroup (ModGL τ L),
      Y ≤ adjointGroup τ L ∧ (∀ y ∈ Y, m * Units.map (entrywiseHom Fr) y * m⁻¹ = y) ∧
      ⁅Y, Y⁆ = Y ∧ Y ≤ rootSpan τ L {β, -β, β', -β'} ∧
      (∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ q ^ 2 - 1 → ∃ x ∈ Y, orderOf x = p) ∧
      ∀ z : ModGL τ L, (∀ x ∈ Y, Commute z x) → ∀ x ∈ rootRankOneGroup τ L β, Commute z x := by
  classical
  have hFr2 : ∀ c, Fr (Fr c) = c ^ Nat.card K₂ := fun c => by
    rw [hFr, hFr, ← pow_mul, hK₂, sq]
  obtain ⟨P, hfix, hHSL⟩ := exists_pairSL2_fixed hFr2 m hcomm s₁ s₂ h₁ h₂
  set Y := pairGroup Fr β β' hcomm s₁ P K₂ with hY
  refine ⟨Y, pairGroup_le_adjointGroup Fr hcomm s₁ P K₂, fun y hy => ?_,
    pairGroup_perfect Fr hcomm s₁ P (by rw [hK₂]; nlinarith),
    pairGroup_le_rootSpan Fr hβ hβ' hcomm s₁ P K₂, fun p hp hp2 hpq => ?_, fun z hz => ?_⟩
  · obtain ⟨B, rfl⟩ := (mem_pairGroup_iff Fr hcomm s₁ P).1 hy
    exact hfix B
  · obtain ⟨ζ, hζ⟩ := exists_orderOf_eq_of_natCast_ne_zero
      (natCast_ne_zero_of_dvd_pow_sub_one hqL (by omega) (by norm_num) hpq)
    have hζq : ζ ^ (Nat.card K₂ - 1) = 1 := by
      rw [hK₂]
      exact orderOf_dvd_iff_pow_eq_one.1 (by rw [hζ]; exact hpq)
    exact ⟨_, pairElt_mem_pairGroup Fr hcomm s₁ P (hHSL ζ hζq),
      orderOf_pairElt_HSL hβ hβ' h0 hcomm Fr s₁ hp hp2 hζ⟩
  · exact commute_rootRankOneGroup_of_pair hdeg (by omega) (by rw [hK₂]; nlinarith) hFr s₁ P
      fun B => hz _ ((mem_pairGroup_iff Fr hcomm s₁ P).2 ⟨B, rfl⟩)

theorem exists_frame_pair_untw {τ : Tag} (hdeg : entryDegreeBound τ = 2) {K : Type} [Field K]
    [Finite K] [Algebra K L] {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hK4 : 4 ≤ Nat.card K) {w : WeylGroup τ} {g0 : ModGL τ L} (hg0C : g0 ∈ adjointGroup τ L)
    (hg0 : Units.map (entrywiseHom Fr) g0 = g0 * canonicalRep (coxeterSystem τ) L w)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hww : w • w • β = β) (h0 : iform β (w • β) = 0)
    (hpr : ¬ IsRoot τ (β + w • β)) (hmr : ¬ IsRoot τ (β - w • β)) :
    ∃ Y : Subgroup (ModGL τ L),
      Y ≤ (LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0).Γ ∧ ⁅Y, Y⁆ = Y ∧
      Y ≤ rootSpan τ L {β, -β, w • β, -(w • β)} ∧
      (∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card K ^ 2 - 1 → ∃ x ∈ Y, orderOf x = p) ∧
      ∀ z : ModGL τ L, (∀ x ∈ Y, Commute z x) → ∀ x ∈ rootRankOneGroup τ L β, Commute z x := by
  classical
  obtain ⟨ℓ, f, hℓ, hf, hK, hchar⟩ := exists_char_data K L
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hqL : ((Nat.card K : ℕ) : L) = 0 := by
    have : Fintype K := Fintype.ofFinite K
    rw [← map_natCast (algebraMap K L), Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero K,
      map_zero]
  set K₂ : Subfield L := (Fr.comp Fr).eqLocusField (RingHom.id L) with hK₂def
  have hFF : ∀ c, Fr (Fr c) = c ^ ℓ ^ (f * 2) := fun c => by
    rw [hFr, hFr, ← pow_mul, pow_mul ℓ f 2, ← hK, sq]
  have hK₂card : Nat.card K₂ = Nat.card K ^ 2 := by
    have h1 : Nat.card K₂ = Nat.card {c : L | c ^ ℓ ^ (f * 2) = c} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun c => by
        simp only [hK₂def, RingHom.mem_eqLocusField, RingHom.comp_apply, RingHom.id_apply,
          Set.mem_setOf_eq, hFF])
    rw [h1, CFSG.RankThree.Classical2.natCard_setOf_pow_eq_self (by omega), pow_mul, hK]
  have : Finite K₂ := Nat.finite_of_card_ne_zero (by rw [hK₂card]; positivity)
  set n := canonicalRep (coxeterSystem τ) L w with hn
  have hnM : n ∈ monomialSubgroup τ L := canonicalRep_mem_monomialSubgroup L w
  have hβ' : IsRoot τ (w • β) := IsRoot.smul hβ w
  obtain ⟨s₁, h₁⟩ := exists_conj_rootSL2_eq hnM (mapsRootLines_canonicalRep w) hβ rfl
  obtain ⟨s₂, h₂⟩ := exists_conj_rootSL2_eq hnM (mapsRootLines_canonicalRep w) hβ' hww
  have hcomm := rootSL2_commute_of_orth (K := L) hβ hβ' h0 hpr hmr
  obtain ⟨Y, hYC, hYfix, hYp, hYspan, hYord, hYcomm⟩ := exists_pairGroup_frame hdeg hFr hK4
    hK₂card hqL n hβ hβ' (by rw [iform_comm]; exact h0) hcomm s₁ s₂ h₁ h₂
  refine ⟨Y, ?_, hYp, hYspan, hYord, hYcomm⟩
  have hYM : Y ≤ (LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0).model :=
    fun y hy => ⟨hYC hy, hYfix y hy⟩
  rw [← hYp]
  exact Subgroup.commutator_mono hYM hYM

theorem exists_frame_pair_twist {t : TwistTag} (hdeg : entryDegreeBound t.tag = 2) {K : Type}
    [Field K] [Finite K] [Algebra K L] {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (hq4 : 4 ≤ q) (hK : Nat.card K = q ^ 2) {w : WeylGroup t.tag} {g0 : ModGL t.tag L}
    (hg0C : g0 ∈ adjointGroup t.tag L)
    (hg0 : twistHom t L Fr g0 = g0 * canonicalRep (coxeterSystem t.tag) L w)
    {β : Fin t.tag.rank → ℤ} (hβ : IsRoot t.tag β)
    (hww : w • permLattice t.perm (w • permLattice t.perm β) = β)
    (h0 : iform β (w • permLattice t.perm β) = 0)
    (hpr : ¬ IsRoot t.tag (β + w • permLattice t.perm β))
    (hmr : ¬ IsRoot t.tag (β - w • permLattice t.perm β)) :
    ∃ Y : Subgroup (ModGL t.tag L),
      Y ≤ (LangDatum.ofTwist t Fr q hFr w hg0C hg0).Γ ∧ ⁅Y, Y⁆ = Y ∧
      Y ≤ rootSpan t.tag L {β, -β, w • permLattice t.perm β, -(w • permLattice t.perm β)} ∧
      (∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ q ^ 2 - 1 → ∃ x ∈ Y, orderOf x = p) ∧
      ∀ z : ModGL t.tag L, (∀ x ∈ Y, Commute z x) →
        ∀ x ∈ rootRankOneGroup t.tag L β, Commute z x := by
  classical
  have hqL : ((q : ℕ) : L) = 0 := by
    have : Fintype K := Fintype.ofFinite K
    have h1 : ((Nat.card K : ℕ) : L) = 0 := by
      rw [← map_natCast (algebraMap K L), Nat.card_eq_fintype_card,
        FiniteField.cast_card_eq_zero K, map_zero]
    rw [hK, Nat.cast_pow] at h1
    exact pow_eq_zero_iff (by norm_num) |>.1 h1
  set n := canonicalRep (coxeterSystem t.tag) L w with hn
  have hnM : n ∈ monomialSubgroup t.tag L := canonicalRep_mem_monomialSubgroup L w
  have hwq : weylQuotientHom t.tag L ⟨n, hnM⟩ = w :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep w)
  have hβ' : IsRoot t.tag (w • permLattice t.perm β) :=
    IsRoot.smul (hβ.permLattice t.cartan_perm) w
  obtain ⟨s₁, h₁⟩ := exists_conj_rootSL2_eq_twist hnM hβ
  obtain ⟨s₂, h₂⟩ := exists_conj_rootSL2_eq_twist hnM hβ'
  rw [hwq] at h₁ h₂
  rw [hww] at h₂
  have hcomm := rootSL2_commute_of_orth (K := L) hβ hβ' h0 hpr hmr
  obtain ⟨Y, hYC, hYfix, hYp, hYspan, hYord, hYcomm⟩ := exists_pairGroup_frame hdeg hFr hq4 hK
    hqL (n * diagramMap t L) hβ hβ' (by rw [iform_comm]; exact h0) hcomm s₁ s₂ h₁ h₂
  refine ⟨Y, ?_, hYp, hYspan, hYord, hYcomm⟩
  have hYM : Y ≤ (LangDatum.ofTwist t Fr q hFr w hg0C hg0).model := by
    intro y hy
    refine ⟨hYC hy, ?_⟩
    have h := hYfix y hy
    change n * twistHom t L Fr y * n⁻¹ = y
    simp only [twistHom, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    have e : n * (diagramMap t L * Units.map (entrywiseHom Fr) y * (diagramMap t L)⁻¹) * n⁻¹ =
        n * diagramMap t L * Units.map (entrywiseHom Fr) y * (n * diagramMap t L)⁻¹ := by
      group
    rw [e]
    exact h
  rw [← hYp]
  exact Subgroup.commutator_mono hYM hYM

end Frame

section SetupFrame

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem setupRigid_of_frame (S : LangSetup τ L p) {ι : Type*} (Z : ι → Subgroup (ModGL τ L))
    (β : ι → Fin τ.rank → ℤ) (hβ : ∀ i, IsRoot τ (β i)) (hZΓ : ∀ i, Z i ≤ S.Γ)
    (hZp : ∀ i, ⁅Z i, Z i⁆ = Z i)
    (hZspan : ∀ i, Z i ≤ rootSpan τ L {β i, -β i, S.ρ (β i), -S.ρ (β i)})
    (hZord : ∀ i, ∃ x ∈ Z i, orderOf x = p)
    (hrig : ∀ δ : MulAut S.Γ, (∀ x : S.Γ, (∃ i, (x : ModGL τ L) ∈ Z i) → δ x = x) → δ = 1) :
    SetupRigid S := by
  intro D₁ hD₁E hD₁c δ _ _ hfix
  refine hrig δ fun x ⟨i, hi⟩ => hfix x ?_
  obtain ⟨y, hyZ, hyp⟩ := hZord i
  refine subset_bigComponentSet_of_perfect S hD₁E hD₁c (hβ i) (hZΓ i) (hZp i)
    ((hZspan i).trans (biSup_mono ?_)) hyZ hyp hi
  rintro γ (rfl | rfl | rfl | rfl)
  · exact ⟨0, Or.inl rfl⟩
  · exact ⟨0, Or.inr rfl⟩
  · exact ⟨1, Or.inl rfl⟩
  · exact ⟨1, Or.inr (S.frob.neg_eq _).symm⟩

end SetupFrame

end CFSG.HardMathSupport.Timmesfeld.CrossChar

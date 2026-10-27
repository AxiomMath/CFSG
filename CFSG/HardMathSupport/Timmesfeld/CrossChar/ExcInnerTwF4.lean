module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwModel
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerF4

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.TauCetiBridge CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def F4TwistedResidual :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    (Fr : L →+* L), (∀ c, Fr c = c ^ Nat.card K) → ∀ p : ℕ, p.Prime → 5 ≤ p →
      p ∣ Nat.card K + 1 →
        RootSL2Generated (twModel (canonicalRep (coxeterSystem Tag.F4) L f4Neg) Fr) ∧
          RootComponentsQuasisimple (twModel (canonicalRep (coxeterSystem Tag.F4) L f4Neg) Fr) p

@[expose] def F4InnerResidualThree :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K], ¬ 3 ∣ Nat.card K →
    ∀ D : Subgroup (MulAut (adjointGroup Tag.F4 K)), IsElemAbelian 3 D → Nat.card D = 3 ^ 3 →
      D ≤ innerAut (adjointGroup Tag.F4 K) →
      (3 ∣ Nat.card K + 1 ∨ ∀ g : adjointGroup Tag.F4 K,
        ∃ x ∈ D.comap (MulAut.conj : adjointGroup Tag.F4 K →* MulAut (adjointGroup Tag.F4 K)),
          ((g * x * g⁻¹ : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) ∉ torusGroup Tag.F4 K) →
      ∀ H : Subgroup (MulAut (adjointGroup Tag.F4 K)), innerAut (adjointGroup Tag.F4 K) ≤ H →
        D ≤ Subgroup.normalizer (H : Set (MulAut (adjointGroup Tag.F4 K))) →
          localDeltaIn 3 H D = ⊥

section Twisted


theorem exists_lang_data_F4 (K : Type) [Field K] [Finite K] :
    ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ Nat.card K) ∧
      ∃ g0 ∈ adjointGroup Tag.F4 (AlgebraicClosure K), Units.map (entrywiseHom Fr) g0 =
        g0 * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) f4Neg := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hcard⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective (ringChar K)
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator Tag.F4 K (ℓ := ringChar K) (f := f) f.pos
    (AlgebraicClosure K) f4Neg
  refine ⟨iterateFrobenius (AlgebraicClosure K) (ringChar K) f, fun c => ?_, g0, hg0C, hg0⟩
  rw [iterateFrobenius_def, Nat.card_eq_fintype_card, hcard]

theorem coroot_mem_twistedTorus_F4 {L : Type} [Field L] {Fr : L →+* L} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) {ζ : Lˣ} (hζ : ζ ^ (q + 1) = 1) (w : WeylGroup Tag.F4)
    (k : Fin Tag.F4.rank) :
    canonicalRep (coxeterSystem Tag.F4) L w * torusElt Tag.F4 L k ζ *
        (canonicalRep (coxeterSystem Tag.F4) L w)⁻¹ ∈
      twistedTorus (canonicalRep (coxeterSystem Tag.F4) L f4Neg) Fr := by
  refine (mem_twistedTorus_of_neg
    (rootDiagUnit_mem_torusGroup_of_unimodular exists_mul_cartan_F4.choose_spec) f4Neg_smul
    hFr).2 ?_
  refine ⟨weylTuple w fun j => ζ ^ Tag.F4.cartan k j, ?_, fun i => ?_⟩
  · rw [torusElt_eq_rootDiagUnit, canonicalRep_conj_rootDiagUnit]
  · refine CTTorus.rootChar_pow_eq_one (fun j => ?_) _
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ, one_zpow]

theorem isInnerLocallyBalanced_adjointF4_of_dvd_add_one (h : F4TwistedResidual) (K : Type)
    [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1) :
    IsInnerLocallyBalanced p (adjointGroup Tag.F4 K) := by
  classical
  obtain ⟨Fr, hFr, g0, hg0C, hg0⟩ := exists_lang_data_F4 K
  set L := AlgebraicClosure K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set n := canonicalRep (coxeterSystem Tag.F4) L f4Neg with hn
  set M := twModel n Fr with hM
  have := finite_twModelF4 K L hFr hg0C hg0
  set e := twModelEquivF4 K L hFr hg0C hg0
  obtain ⟨hgen, hqs⟩ := h K L Fr hFr p hp hp5 hpq
  refine IsInnerLocallyBalanced.of_mulEquiv e ?_
  intro D hD hcard hDin H hH _
  have hZ : Subgroup.center M = ⊥ := by
    have h1 := Subgroup.map_center_eq e
    rw [center_adjointGroup_eq_bot, Subgroup.map_bot] at h1
    exact h1.symm
  have hinj : Function.Injective (MulAut.conj : M →* MulAut M) := by
    intro g g' hgg
    have hc : g'⁻¹ * g ∈ Subgroup.center M :=
      Subgroup.mem_center_iff.2 fun x => by
        have e1 := congrArg (fun φ : MulAut M => φ x) hgg
        simp only [MulAut.conj_apply] at e1
        calc x * (g'⁻¹ * g) = g'⁻¹ * (g' * x * g'⁻¹) * g := by group
          _ = g'⁻¹ * (g * x * g⁻¹) * g := by rw [e1]
          _ = g'⁻¹ * g * x := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact (inv_mul_eq_one.1 hc).symm
  set D₀ := D.comap (MulAut.conj : M →* MulAut M) with hD₀
  have hDD : D₀.map MulAut.conj = D := Subgroup.map_comap_eq_self hDin
  have hpow₀ : ∀ y ∈ D₀, y ^ p = 1 := fun y hy => hinj (by
    rw [map_pow, show (MulAut.conj y) ^ p = 1 from hD.2 _ hy, map_one])
  obtain ⟨g, hgM, hgT⟩ := exists_conj_into_twistedTorus_F4 K L hFr hg0C hg0 hp hp5 hpq
    (A := D₀.map M.subtype) (Subgroup.map_subtype_le _) (by
      rintro _ ⟨y, hy, rfl⟩
      rw [← map_pow, hpow₀ y hy, map_one])
  set g' : M := ⟨g, hgM⟩
  refine localDeltaIn_eq_bot_of_map_conj (c := MulAut.conj g') (hH ⟨g', rfl⟩) ?_
  have hmap : D.map (MulAut.conj (MulAut.conj g')).toMonoidHom =
      (D₀.map (MulAut.conj g').toMonoidHom).map MulAut.conj := by
    conv_lhs => rw [← hDD]
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  rw [hmap]
  have hK0 : ((Nat.card K : ℕ) : L) = 0 := by
    have : Fintype K := Fintype.ofFinite K
    rw [← map_natCast (algebraMap K L), Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero K,
      map_zero]
  have : NeZero ((p : ℕ) : L) := ⟨by
    obtain ⟨m, hm⟩ := hpq
    intro hp0
    have h1 : ((Nat.card K + 1 : ℕ) : L) = 0 := by rw [hm, Nat.cast_mul, hp0, zero_mul]
    rw [Nat.cast_add, hK0, zero_add, Nat.cast_one] at h1
    exact one_ne_zero h1⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L p
  set ζu : Lˣ := (hζ.isUnit hp.ne_zero).unit with hζu
  have hζu' : IsPrimitiveRoot ζu p :=
    IsPrimitiveRoot.coe_units_iff.1 (by simpa [hζu] using hζ)
  have hζp : orderOf ζu = p := hζu'.eq_orderOf.symm
  have hζ2 : ζu ^ 2 ≠ 1 := fun h2 => by
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hζp] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  have hζq : ζu ^ (Nat.card K + 1) = 1 := by
    obtain ⟨m, hm⟩ := hpq
    rw [hm, pow_mul, hζu'.pow_eq_one, one_pow]
  refine localDeltaIn_eq_bot_of_rootSL2 (A := M) inf_le_left hinj hp hζp hζ2
    (fun w k => twistedTorus_le_twModel n Fr (coroot_mem_twistedTorus_F4 hFr hζq w k))
    hgen hqs hH _ ?_ ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [conj_pow, hpow₀ y hy, mul_one, mul_inv_cancel]
  · have h1 : Nat.card D₀ = p ^ 3 := by
      rw [← hcard]
      conv_rhs => rw [← hDD]
      rw [Subgroup.card_map_of_injective hinj]
    rw [Subgroup.card_map_of_injective (MulAut.conj g').injective, h1]
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  · rintro _ ⟨y, hy, rfl⟩
    exact (hgT ⟨(y : ModGL Tag.F4 L), ⟨y, hy, rfl⟩, rfl⟩).1

theorem f4InnerResidual_of_twisted (hTw : F4TwistedResidual) (h3 : F4InnerResidualThree) :
    F4InnerResidual := by
  intro K _ _ p hp hp2 hpK D hD hcard hDin hcase H hH hDH
  rcases eq_three_or_five_le hp hp2 with rfl | h5
  · exact h3 K hpK D hD hcard hDin (hcase.imp id fun h => h.2) H hH hDH
  · rcases hcase with h1 | ⟨rfl, -⟩
    · exact isInnerLocallyBalanced_adjointF4_of_dvd_add_one hTw K hp h5 h1 D hD hcard hDin H hH hDH
    · omega

end Twisted

section Families


theorem crossCharInnerAt_F4_ge_three_of_twisted (hTw : F4TwistedResidual)
    (h3 : F4InnerResidualThree) :
    CrossCharInnerAt .F4 fun idx p => ∃ q : TauCeti.PrimePower, idx.1 = .F4 q ∧
      3 ≤ degCount Tag.F4 (orderOf ((q.card : ℕ) : ZMod p)) :=
  crossCharInnerAt_F4_ge_three_of_residual (f4InnerResidual_of_twisted hTw h3)

theorem crossCharFamAt_F4_ge_three_of_twisted (hTw : F4TwistedResidual)
    (h3 : F4InnerResidualThree) :
    CrossCharFamAt .F4 fun idx p => ∃ q : TauCeti.PrimePower, idx.1 = .F4 q ∧
      3 ≤ degCount Tag.F4 (orderOf ((q.card : ℕ) : ZMod p)) :=
  crossCharFamAt_F4_ge_three_of_residual (f4InnerResidual_of_twisted hTw h3)

end Families

end CFSG.HardMathSupport.Timmesfeld.CrossChar

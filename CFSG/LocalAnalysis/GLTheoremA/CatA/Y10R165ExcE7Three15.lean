module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE7Three14
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.I102Uniq
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Center
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Glue
public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.TwistedRankE6
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutTwE6
public import CFSG.Sporadic.Schreier.J4SNoCompCover

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KE6 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three
open CFSG.RankThree.E6 (weylMatrix weylMatrix_mulVec weylMatrix_mul weylMatrix_pow
  weylMatrix_injective)
open CFSG.HardMathSupport.Lang.TwE6Step3 (monoHom)
open CFSG.HardMathSupport.Foote.Coordinator
  (blockP extJ' extJ'_apply_mem weylMatrix_mulVec_extJ' weylMatrix_pow_mulVec_extJ'
    monoHom_sub_one)
open scoped Matrix MatrixGroups

section Transport

variable
  {τ : Tag} {L : Type} [Field L]

theorem rootSpan_inf_twistedFixedPoints_map_conj (Fr : L →+* L)
    (hFr : Function.Bijective Fr) (v : WeylGroup τ) (n : ModGL τ L)
    {S₀ : Set (Fin τ.rank → ℤ)} (hS₀ : ∀ r ∈ S₀, IsRoot τ r) :
    (rootSpan τ L S₀ ⊓ twistedFixedPoints
        ((canonicalRep (coxeterSystem τ) L v)⁻¹ * n * canonicalRep (coxeterSystem τ) L v)
        (Units.map (entrywiseHom Fr))).map
      (MulAut.conj (canonicalRep (coxeterSystem τ) L v)).toMonoidHom =
    rootSpan τ L ((fun γ => v • γ) '' S₀) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom Fr)) := by
  classical
  set Φ : ModGL τ L →* ModGL τ L := Units.map (entrywiseHom Fr) with hΦ
  set V : ModGL τ L := canonicalRep (coxeterSystem τ) L v with hV
  have hΦV : Φ V = V := by
    have h1 := entrywise_canonicalRep (RingEquiv.ofBijective Fr hFr) v
    have h2 : (RingEquiv.ofBijective Fr hFr).toRingHom = Fr := RingHom.ext fun _ => rfl
    rw [h2] at h1
    exact h1
  set c₀ : ModGL τ L →* ModGL τ L := (MulAut.conj V).toMonoidHom with hc₀
  have hcapp : ∀ x, c₀ x = V * x * V⁻¹ := fun x => by simp [hc₀, MulAut.conj_apply]
  have hQ : (rootSpan τ L S₀).map c₀ = rootSpan τ L ((fun γ => v • γ) '' S₀) :=
    map_conj_rootSpan v hS₀
  have hR : (twistedFixedPoints (V⁻¹ * n * V) Φ).map c₀ = twistedFixedPoints n Φ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hcapp]
      exact (mem_twistedFixedPoints_conj hΦV).1 hx
    · intro hy
      refine ⟨V⁻¹ * y * V, (mem_twistedFixedPoints_conj hΦV).2 ?_, ?_⟩
      · have e : V * (V⁻¹ * y * V) * V⁻¹ = y := by group
        rw [e]
        exact hy
      · rw [hcapp]
        group
  rw [Subgroup.map_inf _ _ c₀ (MulAut.conj V).injective, hQ, hR]

end Transport



section E7


theorem weylMatrix_e7T3Elt {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    weylMatrix (e7T3Elt ε) = ε • e7T3W := by
  rcases hε with hε | hε
  · subst hε
    ext i j
    have h := congrFun (show e7T3Elt (1 : ℤ) • (Pi.single j 1) =
      ((1 : ℤ) • e7T3W) *ᵥ (Pi.single j 1) from
        e7T3Elt_smul (ε := (1 : ℤ)) (by left; rfl) _) i
    rw [← weylMatrix_mulVec] at h
    simpa [Matrix.mulVec_single_one] using h
  · subst hε
    ext i j
    have h := congrFun (show e7T3Elt (-1 : ℤ) • (Pi.single j 1) =
      ((-1 : ℤ) • e7T3W) *ᵥ (Pi.single j 1) from
        e7T3Elt_smul (ε := (-1 : ℤ)) (by right; rfl) _) i
    rw [← weylMatrix_mulVec] at h
    simpa [Matrix.mulVec_single_one] using h

theorem det_cartanBlock_e7T3A2 :
    (cartanBlock Tag.E7 ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _)).det = 3 := by
  decide +kernel

section Image

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

theorem dvd_card_rootSpan_image_inf_twistedFixedPoints_e7 {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1)
    (n : ModGL Tag.E7 L) (hnm : n ∈ monomialSubgroup Tag.E7 L)
    (hnW : weylQuotientHom Tag.E7 L ⟨n, hnm⟩ = e7T3Elt ε)
    (v : WeylGroup Tag.E7)
    (hmaps : ∀ β ∈ parabolicRoots Tag.E7
      ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _),
      (v⁻¹ * e7T3Elt ε * v) • β ∈ parabolicRoots Tag.E7
        ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _))
    (hP : blockP (v⁻¹ * e7T3Elt ε * v)
        ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _) *
      blockP (v⁻¹ * e7T3Elt ε * v)
        ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _) +
      ε • blockP (v⁻¹ * e7T3Elt ε * v)
        ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _) + 1 = 0) :
    p ∣ Nat.card ↥(rootSpan Tag.E7 L ((fun γ => v • γ) '' parabolicRoots Tag.E7
      ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  classical
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c : L, Fr c = c ^ Nat.card K := fun c => by
    rw [hK, iterateFrobenius_def]
  have hFrbij : Function.Bijective Fr := ⟨Fr.injective, fun y => by
    obtain ⟨x, hx⟩ :=
      IsAlgClosed.exists_pow_nat_eq y (show 0 < ℓ ^ f from pow_pos (Fact.out : ℓ.Prime).pos f)
    exact ⟨x, by rw [hFr, hK, hx]⟩⟩
  set V : ModGL Tag.E7 L := canonicalRep (coxeterSystem Tag.E7) L v with hV
  have hVm : V ∈ monomialSubgroup Tag.E7 L := canonicalRep_mem_monomialSubgroup L v
  set n' : ModGL Tag.E7 L := V⁻¹ * n * V with hn'
  have hn'm : n' ∈ monomialSubgroup Tag.E7 L := mul_mem (mul_mem (inv_mem hVm) hnm) hVm
  have hπV : weylQuotientHom Tag.E7 L ⟨V, hVm⟩ = v :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep v)
  have hπn' : weylQuotientHom Tag.E7 L ⟨n', hn'm⟩ = v⁻¹ * e7T3Elt ε * v := by
    have : (⟨n', hn'm⟩ : monomialSubgroup Tag.E7 L) = ⟨V, hVm⟩⁻¹ * ⟨n, hnm⟩ * ⟨V, hVm⟩ :=
      Subtype.ext rfl
    rw [this, map_mul, map_mul, map_inv, hπV, hnW]
  have hq0 : ((Nat.card K : ℕ) : L) = 0 := by
    rw [hK, Nat.cast_pow, CharP.cast_eq_zero L ℓ, zero_pow (by omega : f ≠ 0)]
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hroots : ∀ r ∈ parabolicRoots Tag.E7
      ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _), IsRoot Tag.E7 r :=
    fun r hr => hr.1
  have hdet : (cartanBlock Tag.E7
      ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _)).det ≠ 0 := by
    rw [det_cartanBlock_e7T3A2]
    norm_num
  have hpd : ¬ p ∣ (cartanBlock Tag.E7
      ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _)).det.natAbs := by
    rw [det_cartanBlock_e7T3A2]
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  have hJ' : ∀ β ∈ parabolicRoots Tag.E7
      ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _),
      weylQuotientHom Tag.E7 L ⟨n', hn'm⟩ • β ∈ parabolicRoots Tag.E7
        ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _) := by
    intro β hβ
    rw [hπn']
    exact hmaps β hβ
  rcases hε with hε | hε
  · subst hε
    have hq : ((Nat.card K : L) ^ 2 + (Nat.card K : L) + 1) ≠ 0 := by
      rw [hq0]; norm_num
    have hdvd : p ∣ Nat.card K ^ 2 + Nat.card K + 1 := by
      have h : ((p : ℤ) ∣ ((Nat.card K ^ 2 + Nat.card K + 1 : ℕ) : ℤ)) := by
        push_cast
        simpa using hpf
      exact_mod_cast h
    have hP' : blockP (weylQuotientHom Tag.E7 L ⟨n', hn'm⟩)
        ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _) *
        blockP (weylQuotientHom Tag.E7 L ⟨n', hn'm⟩)
          ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _) +
        blockP (weylQuotientHom Tag.E7 L ⟨n', hn'm⟩)
          ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _) + 1 = 0 := by
      rw [hπn']
      simpa using hP
    have h := dvd_card_rootSpan_inf_twistedFixedPoints_add_of_blockP (τ := Tag.E7)
      (Ω := L) (by rfl) hFr n' hn'm
      ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _) hJ' hP' hdet hp hpd hq hdvd
    have hmap := rootSpan_inf_twistedFixedPoints_map_conj (τ := Tag.E7) Fr hFrbij v n hroots
    rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj V).injective]
    exact h
  · subst hε
    have hq : ((Nat.card K : L) ^ 2 - (Nat.card K : L) + 1) ≠ 0 := by
      rw [hq0]; norm_num
    have hdvd : p ∣ Nat.card K ^ 2 - Nat.card K + 1 := by
      have hcast : ((Nat.card K ^ 2 - Nat.card K + 1 : ℕ) : ℤ) =
          (Nat.card K : ℤ) ^ 2 - (Nat.card K : ℤ) + 1 := by
        have hle : Nat.card K ≤ Nat.card K ^ 2 := Nat.le_self_pow (by norm_num) _
        rw [Nat.cast_add, Nat.cast_sub hle, Nat.cast_pow]
        push_cast
        ring
      have h : ((p : ℤ) ∣ ((Nat.card K ^ 2 - Nat.card K + 1 : ℕ) : ℤ)) := by
        rw [hcast]
        simpa [sub_eq_add_neg] using hpf
      exact_mod_cast h
    have hP' : blockP (weylQuotientHom Tag.E7 L ⟨n', hn'm⟩)
        ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _) *
        blockP (weylQuotientHom Tag.E7 L ⟨n', hn'm⟩)
          ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _) -
        blockP (weylQuotientHom Tag.E7 L ⟨n', hn'm⟩)
          ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _) + 1 = 0 := by
      rw [hπn']
      simpa [sub_eq_add_neg] using hP
    have h := dvd_card_rootSpan_inf_twistedFixedPoints_sub_of_blockP (τ := Tag.E7)
      (Ω := L) (by rfl) hFr n' hn'm
      ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _) hJ' hP' hdet hp hpd hq2 hq hdvd
    have hmap := rootSpan_inf_twistedFixedPoints_map_conj (τ := Tag.E7) Fr hFrbij v n hroots
    rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj V).injective]
    exact h

end Image

end E7

end CFSG.LocalAnalysis.GLTheoremA.Y10F

module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Three8
public import CFSG.Quasithin.Vol2.Ch3Sec3InspF618Tools
public import CFSG.RankThree.PartOne.KE6.E8T3LayerA2
public import CFSG.RankThree.PartOne.KE6.E8T3Torus

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.E6 (weylMatrix weylMatrix_mulVec)

open scoped Matrix MatrixGroups

section Certs


private theorem e8T3YColumn_eq {p : ℕ} {ε : ℤ} {q : ZMod p} :
    e8T3YColumn ε q = (fun i => (e8T3ZAVec i - e8T3XAVec i : ZMod p)) +
      ((ε : ZMod p) * q) • (fun i => (e8T3ZDVec i - e8T3XDVec i : ZMod p)) := by
  funext k
  simp only [e8T3YColumn, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    cartanCoord_e8T3GammaOne, cartanCoord_e8T3GammaTwo, Pi.sub_apply]
  push_cast
  ring

theorem e8T3YColumn_eq_sub {p : ℕ} {ε : ℤ} {q : ZMod p} :
    e8T3YColumn ε q = e8T3ZColumn ε q - e8T3XColumn ε q := by
  rw [e8T3YColumn_eq, e8T3ZColumn_eq_add_smul, e8T3XColumn_eq_add_smul]
  funext k
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem e8T3YColumn_eigen {p : ℕ} {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {q : ℕ}
    (hq : (q : ZMod p) ^ 2 + (ε : ZMod p) * (q : ZMod p) + 1 = 0) :
    ((weylMatrix (e8T3We ε)).map (Int.cast : ℤ → ZMod p)).transpose *ᵥ
        e8T3YColumn ε (q : ZMod p) = (q : ZMod p) • e8T3YColumn ε (q : ZMod p) := by
  rw [e8T3YColumn_eq_sub, Matrix.mulVec_sub, e8T3ZColumn_eigen hε hq,
    e8T3XColumn_eigen hε hq, smul_sub]

theorem rootDiagUnit_e8T3YColumn_mem_twistedTorus {L : Type} [Field L] {p : ℕ} [NeZero p]
    {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p) {n : ModGL Tag.E8 L} {Fr : L →+* L} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hq : (q : ZMod p) ^ 2 + (ε : ZMod p) * (q : ZMod p) + 1 = 0)
    (hT : twistedTorusOf n (Units.map (entrywiseHom Fr)) =
      (fixedCharTuples (weylMatrix (e8T3We ε)) Fr).map (rootDiagUnitHom Tag.E8 L)) :
    rootDiagUnit Tag.E8 (fun i => ζ ^ ((e8T3YColumn ε (q : ZMod p)) i).val) ∈
      twistedTorusOf n (Units.map (entrywiseHom Fr)) :=
  rootDiagUnit_mem_twistedTorus_of_eigenColumn hζ hFr hT (e8T3YColumn_eigen hε hq)

variable {K : Type} [Field K] [Finite K] {ℓ f p : ℕ} [Fact ℓ.Prime] {L : Type} [Field L]
  [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] {ε : ℤ}

theorem rootDiagUnit_e8T3XColumn_mem_sigmaFactor (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) (hp3 : 3 < p) (hε : ε = 1 ∨ ε = -1) (hq2 : ε = -1 → 2 < ℓ ^ f)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1)
    (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L)
    (hnW : weylQuotientHom Tag.E8 L ⟨n, hnm⟩ = e8T3We ε) {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p) :
    ∃ P : Subgroup (ModGL Tag.E8 L),
      P = rootSpan Tag.E8 L (sigmaSetE8 ((coxeterSystem Tag.E8).wordProd e8T3W1)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) ∧
      Finite P ∧ CFSG.IsQuasisimple ↥P ∧ P ≤ adjointGroup Tag.E8 L ∧
      P ≤ twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) ∧
      rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3XColumn ε (Nat.card K : ZMod p) i).val) ∈ P := by
  classical
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hFr : ∀ c : L, iterateFrobenius L ℓ f c = c ^ ℓ ^ f := fun c => iterateFrobenius_def ℓ f c
  have hFrK : ∀ c : L, iterateFrobenius L ℓ f c = c ^ Nat.card K := by
    intro c; rw [hFr, hK]
  have hq : ((Nat.card K : ℕ) : ZMod p) ^ 2 + (ε : ZMod p) * (Nat.card K : ℕ) + 1 = 0 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1) p).2 hpf
    simpa using h
  have hnC : n ∈ adjointGroup Tag.E8 L := monomialSubgroup_le_adjointGroup' hnm
  have hnWv : ∀ x : Fin Tag.E8.rank → ℤ,
      weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • x = e8T3We ε • x := fun x => by rw [hnW]
  have hSv : ∀ α ∈ sigmaSetE8 ((coxeterSystem Tag.E8).wordProd e8T3W1),
      e8T3We ε • α ∈ sigmaSetE8 ((coxeterSystem Tag.E8).wordProd e8T3W1) := by
    intro α hα
    rw [sigmaSetE8_e8T3W1] at hα ⊢
    exact e8T3We_smul_mem_e8T3A2One hε α hα
  have hSneg : ∀ α ∈ sigmaSetE8 ((coxeterSystem Tag.E8).wordProd e8T3W1),
      -α ∈ sigmaSetE8 ((coxeterSystem Tag.E8).wordProd e8T3W1) := by
    intro α hα
    rw [sigmaSetE8_e8T3W1] at hα ⊢
    exact neg_mem_e8T3A2One hα
  obtain ⟨P, hPeq, hfac, -⟩ := layer_A2 hf hK hε hq2
    ((coxeterSystem Tag.E8).wordProd e8T3W1) n hnm hnC hnWv hSv hSneg
  refine ⟨P, hPeq, hfac.finite (), hfac.quasi (), hfac.le_adj (), hfac.le_fix (), ?_⟩
  rw [hPeq, Subgroup.mem_inf]
  refine ⟨?_, ?_⟩
  · refine rootDiagUnit_e8T3XColumn_mem_rootSpan hζ (e := (ε : ℤ) * (Nat.card K : ℤ)) ?_
      ?_ ?_ ?_ ?_
    · push_cast; ring
    · rw [sigmaSetE8_e8T3W1]; simp [e8T3A2One]
    · rw [sigmaSetE8_e8T3W1]; simp [e8T3A2One]
    · rw [sigmaSetE8_e8T3W1]; simp [e8T3A2One]
    · rw [sigmaSetE8_e8T3W1]; simp [e8T3A2One]
  · exact mem_twistedFixedPoints_of_mem_twistedTorusOf
      (e8T3XColumn_mem_twistedTorus hζ hFrK hε hq
        (e8T3_twistedTorus n hnm hnW (iterateFrobenius L ℓ f)))

theorem exists_adjointGroup_e8T3XPoint (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) (hp3 : 3 < p) (hε : ε = 1 ∨ ε = -1) (hq2 : ε = -1 → 2 < ℓ ^ f)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1)
    (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L)
    (hnW : weylQuotientHom Tag.E8 L ⟨n, hnm⟩ = e8T3We ε)
    (g0 : ModGL Tag.E8 L) (hg0C : g0 ∈ adjointGroup Tag.E8 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL Tag.E8 L), Finite P → P ≤ adjointGroup Tag.E8 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb Tag.E8 K L).range) {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p) :
    ∃ x : adjointGroup Tag.E8 K, adjEmb Tag.E8 K L x = g0 *
      rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3XColumn ε (Nat.card K : ZMod p) i).val) * g0⁻¹ := by
  obtain ⟨P, -, hPfin, hPq, hPadj, hPfix, htP⟩ :=
    rootDiagUnit_e8T3XColumn_mem_sigmaFactor hf hK hp hp3 hε hq2 hpf n hnm hnW hζ
  exact exists_adjointGroup_of_mem_perfectFixed_e8 n g0 hg0C hg0 hperf hPfin hPadj hPfix
    (CFSG.Quasithin.F6.InspRest.commutator_eq_self_of_isQuasisimple hPq) htP

theorem rootDiagUnit_e8T3YColumn_mem_sigmaFactor (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) (hp3 : 3 < p) (hε : ε = 1 ∨ ε = -1) (hq2 : ε = -1 → 2 < ℓ ^ f)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1)
    (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L)
    (hnW : weylQuotientHom Tag.E8 L ⟨n, hnm⟩ = e8T3We ε) {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p) :
    ∃ P : Subgroup (ModGL Tag.E8 L),
      P = rootSpan Tag.E8 L (sigmaSetE8 ((coxeterSystem Tag.E8).wordProd e8T3W2)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) ∧
      Finite P ∧ CFSG.IsQuasisimple ↥P ∧ P ≤ adjointGroup Tag.E8 L ∧
      P ≤ twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) ∧
      rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3YColumn ε (Nat.card K : ZMod p) i).val) ∈ P := by
  classical
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hFr : ∀ c : L, iterateFrobenius L ℓ f c = c ^ ℓ ^ f := fun c => iterateFrobenius_def ℓ f c
  have hFrK : ∀ c : L, iterateFrobenius L ℓ f c = c ^ Nat.card K := by
    intro c; rw [hFr, hK]
  have hq : ((Nat.card K : ℕ) : ZMod p) ^ 2 + (ε : ZMod p) * (Nat.card K : ℕ) + 1 = 0 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1) p).2 hpf
    simpa using h
  have hnC : n ∈ adjointGroup Tag.E8 L := monomialSubgroup_le_adjointGroup' hnm
  have hnWv : ∀ x : Fin Tag.E8.rank → ℤ,
      weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • x = e8T3We ε • x := fun x => by rw [hnW]
  have hSv : ∀ α ∈ sigmaSetE8 ((coxeterSystem Tag.E8).wordProd e8T3W2),
      e8T3We ε • α ∈ sigmaSetE8 ((coxeterSystem Tag.E8).wordProd e8T3W2) := by
    intro α hα
    rw [sigmaSetE8_e8T3W2] at hα ⊢
    exact e8T3We_smul_mem_e8T3A2Two hε α hα
  have hSneg : ∀ α ∈ sigmaSetE8 ((coxeterSystem Tag.E8).wordProd e8T3W2),
      -α ∈ sigmaSetE8 ((coxeterSystem Tag.E8).wordProd e8T3W2) := by
    intro α hα
    rw [sigmaSetE8_e8T3W2] at hα ⊢
    exact neg_mem_e8T3A2Two hα
  obtain ⟨P, hPeq, hfac, -⟩ := layer_A2 hf hK hε hq2
    ((coxeterSystem Tag.E8).wordProd e8T3W2) n hnm hnC hnWv hSv hSneg
  refine ⟨P, hPeq, hfac.finite (), hfac.quasi (), hfac.le_adj (), hfac.le_fix (), ?_⟩
  rw [hPeq, Subgroup.mem_inf]
  refine ⟨?_, ?_⟩
  · refine rootDiagUnit_e8T3YColumn_mem_rootSpan hζ (e := (ε : ℤ) * (Nat.card K : ℤ)) ?_
      ?_ ?_ ?_ ?_
    · push_cast; ring
    · rw [sigmaSetE8_e8T3W2]; simp [e8T3A2Two]
    · rw [sigmaSetE8_e8T3W2]; simp [e8T3A2Two]
    · rw [sigmaSetE8_e8T3W2]; simp [e8T3A2Two]
    · rw [sigmaSetE8_e8T3W2]; simp [e8T3A2Two]
  · exact mem_twistedFixedPoints_of_mem_twistedTorusOf
      (rootDiagUnit_e8T3YColumn_mem_twistedTorus hζ hFrK hε hq
        (e8T3_twistedTorus n hnm hnW (iterateFrobenius L ℓ f)))

theorem exists_adjointGroup_e8T3YPoint (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) (hp3 : 3 < p) (hε : ε = 1 ∨ ε = -1) (hq2 : ε = -1 → 2 < ℓ ^ f)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1)
    (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L)
    (hnW : weylQuotientHom Tag.E8 L ⟨n, hnm⟩ = e8T3We ε)
    (g0 : ModGL Tag.E8 L) (hg0C : g0 ∈ adjointGroup Tag.E8 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL Tag.E8 L), Finite P → P ≤ adjointGroup Tag.E8 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb Tag.E8 K L).range) {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p) :
    ∃ y : adjointGroup Tag.E8 K, adjEmb Tag.E8 K L y = g0 *
      rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3YColumn ε (Nat.card K : ZMod p) i).val) * g0⁻¹ := by
  obtain ⟨P, -, hPfin, hPq, hPadj, hPfix, htP⟩ :=
    rootDiagUnit_e8T3YColumn_mem_sigmaFactor hf hK hp hp3 hε hq2 hpf n hnm hnW hζ
  exact exists_adjointGroup_of_mem_perfectFixed_e8 n g0 hg0C hg0 hperf hPfin hPadj hPfix
    (CFSG.Quasithin.F6.InspRest.commutator_eq_self_of_isQuasisimple hPq) htP

private theorem e8T3ZColumn_eq_add_Y {p : ℕ} {ε : ℤ} {q : ZMod p} :
    e8T3ZColumn ε q = e8T3XColumn ε q + e8T3YColumn ε q := by
  rw [e8T3YColumn_eq_sub]
  abel

private theorem pow_val_add {L : Type} [Field L] {p : ℕ} [NeZero p] {ζ : Lˣ}
    (hζ : IsPrimitiveRoot ζ p) (a b : ZMod p) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  have ho : orderOf ζ = p := hζ.eq_orderOf.symm
  rw [← pow_add, pow_eq_pow_iff_modEq, ho, ZMod.val_add]
  exact Nat.mod_mod _ _

theorem rootDiagUnit_e8T3X_mul_Y {L : Type} [Field L] {p : ℕ} [NeZero p] {ζ : Lˣ}
    (hζ : IsPrimitiveRoot ζ p) {ε : ℤ} {q : ZMod p} :
    rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3XColumn ε q i).val) *
      rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3YColumn ε q i).val) =
    rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3ZColumn ε q i).val) := by
  change rootDiagUnitHom Tag.E8 L (fun i => ζ ^ (e8T3XColumn ε q i).val) *
      rootDiagUnitHom Tag.E8 L (fun i => ζ ^ (e8T3YColumn ε q i).val) =
    rootDiagUnitHom Tag.E8 L (fun i => ζ ^ (e8T3ZColumn ε q i).val)
  rw [← map_mul]
  congr 1
  funext k
  simp only [Pi.mul_apply, e8T3ZColumn_eq_add_Y, Pi.add_apply, pow_val_add hζ]

theorem exists_adjointGroup_e8T3ZPoint (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) (hp3 : 3 < p) (hε : ε = 1 ∨ ε = -1) (hq2 : ε = -1 → 2 < ℓ ^ f)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1)
    (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L)
    (hnW : weylQuotientHom Tag.E8 L ⟨n, hnm⟩ = e8T3We ε)
    (g0 : ModGL Tag.E8 L) (hg0C : g0 ∈ adjointGroup Tag.E8 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL Tag.E8 L), Finite P → P ≤ adjointGroup Tag.E8 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb Tag.E8 K L).range) {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p) :
    ∃ z : adjointGroup Tag.E8 K, adjEmb Tag.E8 K L z = g0 *
      rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3ZColumn ε (Nat.card K : ZMod p) i).val) * g0⁻¹ := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨x, hx⟩ := exists_adjointGroup_e8T3XPoint hf hK hp hp3 hε hq2 hpf n hnm hnW g0 hg0C
    hg0 hperf hζ
  obtain ⟨y, hy⟩ := exists_adjointGroup_e8T3YPoint hf hK hp hp3 hε hq2 hpf n hnm hnW g0 hg0C
    hg0 hperf hζ
  refine ⟨x * y, ?_⟩
  rw [map_mul, hx, hy]
  have hassoc : g0 * rootDiagUnit Tag.E8
        (fun i => ζ ^ (e8T3XColumn ε (Nat.card K : ZMod p) i).val) * g0⁻¹ *
      (g0 * rootDiagUnit Tag.E8
        (fun i => ζ ^ (e8T3YColumn ε (Nat.card K : ZMod p) i).val) * g0⁻¹) =
      g0 * (rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3XColumn ε (Nat.card K : ZMod p) i).val) *
        rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3YColumn ε (Nat.card K : ZMod p) i).val)) * g0⁻¹ := by
    group
  rw [hassoc, rootDiagUnit_e8T3X_mul_Y hζ]

end Certs

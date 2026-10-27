module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8TenTwelveAux.Generic
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8TenTwelveAux.TwelveFrame
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8TenTwelveAux.TwelveBasis
public import CFSG.RankThree.PartOne.KD4L.TrialityLayer

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.LocalRank
open CFSG.RankThree.PartOne CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE CFSG.Open
open scoped Matrix Pointwise MatrixGroups

set_option linter.unusedSectionVars false


section Rigid

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] {p : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

@[expose] def E8TwelveOrderP (F : E8TwelveFrame K L ℓ f p) : Prop :=
  ∀ ζ : Lˣ, orderOf ζ = p → ∀ c ∈ e8T12D4Certs,
    ∃ d ∈ rootSpan Tag.E8 L (classSetL e8T12Rows c.cls) ⊓
      twistedFixedPoints F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))), orderOf d = p

theorem e8Twelve_rigid_of_D4 (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (F : E8TwelveFrame K L ℓ f p) (hexist : E8TwelveOrderP F) {b : Fin Tag.E8.rank → Lˣ}
    (hap : ∀ i, b i ^ p = 1) (hb1 : b ≠ 1) {cc : D4Cert} (hcc : cc ∈ e8T12D4Certs)
    (hker : rootCharKernel b = classSetL e8T12Rows cc.cls) (hgood : cc.Good e8T12Rows e8T12WW) :
    E8RigidAt K F.n (iterateFrobenius L ℓ f) p b := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hnC : F.n ∈ adjointGroup .E8 L := monomialSubgroup_le_adjointGroup' F.hnm
  obtain ⟨hS1, u, hu, hcertw⟩ := D4Cert.sound hgood
  obtain ⟨-, -, -, hab, hbc, hac, ha, hbl, hcl, -⟩ := hgood
  set v : WeylGroup .E8 := (coxeterSystem .E8).wordProd cc.w with hv
  have hSeq : rootCharKernel b = (fun γ => v • γ) '' parabolicRoots .E8 (d4Nodes .E8) :=
    hker.trans hS1
  have hcert : ∃ u ∈ parabolicWeylGroup .E8 (d4Nodes .E8),
      ∀ α ∈ parabolicRoots .E8 (d4Nodes .E8),
        (v⁻¹ * weylQuotientHom .E8 L ⟨F.n, F.hnm⟩ * v) • α =
          u • permLattice (List.formPerm [cc.a, cc.b, cc.c]) α := by
    rw [F.hnW]
    exact ⟨u, hu, hcertw⟩
  obtain ⟨P, hfam, hP1, h₀, hh₀⟩ := e8_d4_family CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E8
    hf hK v F.n F.hnm hnC cc.a cc.b cc.c hab hbc hac
    (by rcases ha with h | h | h <;> simp [h]) (by rcases hbl with h | h | h <;> simp [h])
    (by rcases hcl with h | h | h <;> simp [h]) hcert
  obtain ⟨i, hi⟩ : ∃ i, b i ≠ 1 := Function.ne_iff.1 hb1
  have hζ : orderOf (b i) = p := orderOf_eq_prime (hap i) hi
  obtain ⟨d, hd, hdp⟩ := hexist (b i) hζ cc hcc
  have hdP : d ∈ P () := by
    rw [hP1, ← hS1]
    exact hd
  have hpdvd : p ∣ Nat.card (P ()) := by
    have h1 : orderOf (⟨d, hdP⟩ : P ()) ∣ Nat.card (P ()) := orderOf_dvd_natCard _
    rwa [← Subgroup.orderOf_coe, Subgroup.coe_mk, hdp] at h1
  unfold E8RigidAt
  rw [hSeq]
  exact ⟨P (), hfam, hP1, ⟨e8Index 3, h₀, hh₀⟩,
    fun hcop => hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hpdvd)⟩

theorem e8Twelve_rigid (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp7 : 7 < p)
    (hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 4 - ((Nat.card K : ℕ) : ZMod p) ^ 2 + 1 = 0)
    (F : E8TwelveFrame K L ℓ f p) (hexist : E8TwelveOrderP F) (b : Fin Tag.E8.rank → Lˣ)
    (hbT : rootDiagUnit Tag.E8 b ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    (hap : ∀ i, b i ^ p = 1) (hb1 : b ≠ 1) (hβ : ∃ j, e8T12Basis j ∈ rootCharKernel b) :
    E8RigidAt K F.n (iterateFrobenius L ℓ f) p b := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  have hb : b ∈ fixedCharTuples e8T12V Fr := by
    rw [F.hT] at hbT
    obtain ⟨b', hb', hbb'⟩ := hbT
    have : b' = b := rootDiagUnit_injective hbb'
    rwa [this] at hb'
  obtain ⟨j, hj⟩ := hβ
  rcases e8T12_kernel_structure Fr hFr hp (by omega) hΦ hb hap hb1 with
    hA | ⟨cc, hcc, hker, hgood⟩ | ⟨cc, hcc, hker, -⟩
  · exfalso
    rw [hA] at hj
    exact Set.notMem_empty _ hj
  · exact e8Twelve_rigid_of_D4 hf hK hp F hexist hap hb1 hcc hker hgood
  · exfalso
    rw [hker] at hj
    obtain ⟨l, hl, hl'⟩ := hj
    exact e8T12Basis_not_twoA2 cc hcc l hl j hl'.symm

end Rigid

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

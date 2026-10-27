module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsGen
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.Adapters.ProjectiveSpecialLinear
public meta import Mathlib
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsGen
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsSL3Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsSL3Raw
public import Certificates.Certificate4145
public meta import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public meta import CFSG.CGT.Timmesfeld75.ListWCBasic
public meta import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public meta import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementBlock
public meta import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementBlock
public import CFSG.ClassicalGroups
public meta import CFSG.ClassicalGroups
public import CFSG.LieType.BorelTits.CompleteFlag
public meta import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public meta import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public meta import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public meta import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.LocalAnalysis.ComponentInitial.LinearTwoOuterOrder
public meta import CFSG.LocalAnalysis.ComponentInitial.LinearTwoOuterOrder
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.D8
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.D8
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Elementary
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Elementary
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_12Aux
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_12Aux
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15Aux
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15Aux
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6
public meta import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.QuasithinUnique.Unc25K1

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups

theorem card_S3_fintype : Fintype.card S3 = 5616 :=
  Certificates.certificate4145.2.2.1

theorem card_S3 : Nat.card S3 = 5616 := by
  rw [Nat.card_eq_fintype_card]
  exact card_S3_fintype

theorem raw_combined : ∀ r ∈ rawList,
    (((rmul r (rr u0S) = rmul (rr u0S) r ∧ rmul r (rmul r r) = rone) ↔ r ∈ TlS.map rr) ∧
      (rmul r (rr u0S) = rmul (rr u0S) r → (∀ t ∈ TlS.map rr, rmul t r = rmul r t) →
        r = rone ∨ r = rr u0S) ∧
      ((∀ t ∈ TlS.map rr, rmul r t = rmul t r) → r = rone ∨ r = rr u0S)) :=
  Certificates.certificate4145.2.2.2.1

theorem raw_conj : ∀ u ∈ rawList, u ≠ rone → rmul u u = rone →
    ∃ g ∈ rawList, rmul g (rr u0S) = rmul u g :=
  Certificates.certificate4145.2.2.2.2.1

theorem hTlS : ∀ x : S3, (x * u0S = u0S * x ∧ x ^ 3 = 1) ↔ x ∈ TlS := by
  intro x
  have h := (raw_combined (rr x) (rr_mem x)).1
  rw [List.mem_map_of_injective rr_inj] at h
  rw [rr_comm_iff, rr_cube_iff]
  exact h

theorem hcenterS :
    ∀ w : S3, w * u0S = u0S * w → (∀ t ∈ TlS, t * w = w * t) → w = 1 ∨ w = u0S := by
  intro w h1 h2
  have h := (raw_combined (rr w) (rr_mem w)).2.1
  rw [rr_eq_one_iff, rr_eq_iff]
  apply h
  · exact (rr_comm_iff w u0S).1 h1
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact (rr_comm_iff s w).1 (h2 s hs)

theorem hcentS : ∀ b : S3, (∀ t ∈ TlS, b * t = t * b) → b = 1 ∨ b = u0S := by
  intro b h2
  have h := (raw_combined (rr b) (rr_mem b)).2.2
  rw [rr_eq_one_iff, rr_eq_iff]
  apply h
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact (rr_comm_iff b s).1 (h2 s hs)

theorem hconjS : ∀ u : S3, u ≠ 1 → u ^ 2 = 1 → ∃ g : S3, g * u0S * g⁻¹ = u := by
  intro u hu1 hu2
  have hu1' : rr u ≠ rone := fun h => hu1 ((rr_eq_one_iff u).2 h)
  have hu2' : rmul (rr u) (rr u) = rone := by
    rw [← rr_mul, ← rr_one]
    exact congrArg rr (by rw [← sq]; exact hu2)
  obtain ⟨g', hg', hgg⟩ := raw_conj (rr u) (rr_mem u) hu1' hu2'
  have hdet : rdet g' = 1 := det_of_mem_rawList hg'
  refine ⟨ofR9 g' hdet, ?_⟩
  have : ofR9 g' hdet * u0S = u * ofR9 g' hdet := by
    apply rr_inj
    rw [rr_mul, rr_mul, rr_ofR9]
    exact hgg
  rw [mul_inv_eq_iff_eq_mul]
  exact this

theorem hgenS : ∀ t ∈ TlS, ∃ w ∈ WsS, t = evB aS bS w :=
  Certificates.certificate4145.2.2.2.2.2.1

theorem u0S_word : u0S = evB aS bS [true, false, true, false] :=
  Certificates.certificate4145.2.2.2.2.2.2.1

theorem abS :
    aS ≠ 1 ∧ bS ≠ 1 ∧ (aS * bS) ^ 2 ≠ 1 ∧ (aS * bS) ^ 4 = 1 :=
  Certificates.certificate4145.2.2.2.2.2.2.2.1

theorem hPlS : ∀ x ∈ TlS, ∀ y ∈ TlS, x ≠ 1 → y ≠ 1 → (x * y) ^ 2 ≠ 1 → (x * y) ^ 4 = 1 →
    (x, y) ∈ PlS := by
  intro x hx y hy h1 h2 h3 h4
  unfold PlS
  rw [List.mem_filter]
  refine ⟨List.mem_product.mpr ⟨hx, hy⟩, ?_⟩
  simp [h1, h2, h3, h4]

theorem hPlcS : PlS.length ≤ 24 :=
  Certificates.certificate4145.2.2.2.2.2.2.2.2

theorem aS_mem : aS ∈ TlS := by simp [TlS]

theorem bS_mem : bS ∈ TlS := by simp [TlS]

theorem u0S_mem_closure : u0S ∈ Subgroup.closure {x : S3 | x ∈ TlS} := by
  rw [u0S_word]
  refine Subgroup.closure_mono ?_ (evB_mem_closure aS bS _)
  intro x hx
  rcases hx with rfl | rfl
  · exact aS_mem
  · exact bS_mem

def uniMat (a b : ZMod 3) : S3 := ⟨!![1,a,b;0,1,0;0,0,1], by norm_num [Matrix.det_fin_three]⟩

theorem uniMat_mul (a b c d : ZMod 3) : uniMat a b * uniMat c d = uniMat (a + c) (b + d) := by
  apply Subtype.ext
  change (!![1,a,b;0,1,0;0,0,1] : Matrix (Fin 3) (Fin 3) (ZMod 3)) * !![1,c,d;0,1,0;0,0,1] =
    !![1,a+c,b+d;0,1,0;0,0,1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, add_comm]

theorem uniMat_zero : uniMat 0 0 = 1 := by
  apply Subtype.ext
  change (!![1,0,0;0,1,0;0,0,1] : Matrix (Fin 3) (Fin 3) (ZMod 3)) = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

def uniHom : Multiplicative (ZMod 3 × ZMod 3) →* S3 where
  toFun x := uniMat (Multiplicative.toAdd x).1 (Multiplicative.toAdd x).2
  map_one' := by simpa using uniMat_zero
  map_mul' x y := by
    simp [uniMat_mul]

theorem uniHom_injective : Function.Injective uniHom := by
  intro x y h
  have h1 := congrArg (fun m : S3 => (m : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 1) h
  have h2 := congrArg (fun m : S3 => (m : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 2) h
  simp [uniHom, uniMat] at h1 h2
  exact Multiplicative.toAdd.injective (Prod.ext h1 h2)

theorem exists_E9_S3 :
    ∃ E : Subgroup S3, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  refine ⟨uniHom.range, ⟨?_, ?_⟩, ?_⟩
  · refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    apply Subtype.ext
    change (a : S3) * b = b * a
    rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ 3 = 1 := by
      apply Multiplicative.toAdd.injective
      simp only [toAdd_pow, toAdd_one]
      have h3 : ((3 : ℕ) : ZMod 3) = 0 := by decide
      rw [← Nat.cast_smul_eq_nsmul (ZMod 3), h3, zero_smul]
    rw [this, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective uniHom_injective).toEquiv]
    simp

theorem k33Facts_S3 : K33Facts (⊤ : Subgroup S3) := by
  refine ⟨?_, ?_, ?_⟩
  · left
    rw [Subgroup.card_top]
    exact card_S3
  · obtain ⟨E, hE, hcard⟩ := exists_E9_S3
    exact ⟨E, le_top, hE, hcard⟩
  · intro u _ hu1 hu2
    obtain ⟨-, -, hab2, hab4⟩ := abS
    exact k33InvFacts_top_of_data u0S hconjS TlS hTlS u0S_mem_closure hcenterS hcentS aS bS aS_mem
      bS_mem WsS hgenS abS.1 abS.2.1 hab2 hab4 PlS hPlS hPlcS u hu1 hu2

theorem psl33_equiv {X : Type} [Group X] (h : StatedClassicalModel X .PSL 3 3 1) :
    Nonempty (X ≃* PSL(3, ZMod 3)) := by
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := h
  have : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F = 3 := by rw [← Nat.card_eq_fintype_card]; simpa using hcard
  let eF : ZMod 3 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_three hF
  exact ⟨(e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm).trans
    (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv eF.symm (Fin 3))⟩

theorem zmod3_cube_eq_one : ∀ r : ZMod 3, r ^ 3 = 1 → r = 1 := by decide

theorem center_S3_eq_bot : Subgroup.center S3 = ⊥ := by
  ext A
  rw [Subgroup.mem_bot, Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hrA⟩
    have hr1 : r = 1 := zmod3_cube_eq_one r (by simpa [Fintype.card_fin] using hr)
    subst hr1
    apply Subtype.ext
    rw [← hrA]
    simp
  · rintro rfl
    exact ⟨1, by simp, by simp⟩

noncomputable def psl33EquivS3 : PSL(3, ZMod 3) ≃* S3 :=
  (QuotientGroup.quotientMulEquivOfEq center_S3_eq_bot).trans QuotientGroup.quotientBot

theorem k33Facts_of_L33 {G : Type} [Group G] {K : Subgroup G}
    (h : StatedClassicalModel ↥K .PSL 3 3 1) : K33Facts K := by
  obtain ⟨e⟩ := psl33_equiv h
  exact k33Facts_of_mulEquiv (e.trans psl33EquivS3) k33Facts_S3

end CFSG.QuasithinUnique.Unc25K1

module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.BlocksAbstract
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Aux.Defs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop42CaseThreeProof
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.RankThree.PartTwo.KFacts

theorem isInnerAut_inducedBarHom_of_barX_aut {G : Type} [Group G] [Finite G] {X J : Subgroup G}
    (hJ : GLAPComponent 3 X J) {φ : MulAut G} (h : φ ∈ stabAut J) {j₀ : G} (hj₀ : j₀ ∈ J)
    (hφj : ∀ j ∈ J, ∀ (h1 : φ j ∈ X) (h2 : j₀ * j * j₀⁻¹ ∈ X),
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨φ j, h1⟩ =
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨j₀ * j * j₀⁻¹, h2⟩) :
    IsInnerAut (inducedBarHom J ⟨φ, h⟩) := by
  have hsub : IsSubnormal J X := hJ.2.1
  have hJX : J ≤ X := hJ.1
  have key : ∀ u v : ↥J, (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)) (Subgroup.inclusion hJX u) =
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)) (Subgroup.inclusion hJX v) →
      (QuotientGroup.mk u : barOf 3 J) = QuotientGroup.mk v := by
    intro u v huv
    rw [QuotientGroup.eq]
    have h1 : Subgroup.inclusion hJX (u⁻¹ * v) ∈ GLAPPrimeCore 3 ↥X := by
      have h0 : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)) (Subgroup.inclusion hJX (u⁻¹ * v)) = 1 := by
        rw [map_mul (Subgroup.inclusion hJX), map_inv (Subgroup.inclusion hJX), map_mul, map_inv,
          huv, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).1 h0
    have h2 : ((u⁻¹ * v : ↥J) : G) ∈ GLAPPrimeCoreOf 3 X :=
      (mem_gLAPPrimeCoreOf_iff 3 X _).2 ⟨(u⁻¹ * v).2 |> hJX, h1⟩
    have h3 : ((u⁻¹ * v : ↥J) : G) ∈ GLAPPrimeCoreOf 3 J := by
      rw [glaPPrimeCoreOf_eq_inf_of_isSubnormal Nat.prime_three hsub]
      exact ⟨(u⁻¹ * v).2, h2⟩
    exact ((mem_gLAPPrimeCoreOf_iff 3 J _).1 h3).2
  refine ⟨QuotientGroup.mk ⟨j₀, hj₀⟩, ?_⟩
  ext y
  induction y using QuotientGroup.induction_on with
  | H j =>
    rw [inducedBarHom_mk]
    show (QuotientGroup.mk (⟨j₀, hj₀⟩ * j * ⟨j₀, hj₀⟩⁻¹) : barOf 3 J) =
      QuotientGroup.mk (restrictAut φ h j)
    exact key _ _ (hφj j j.2 _ _).symm

theorem exists_inner_of_blocks_aut {G : Type} [Group G] [Finite G] {X J : Subgroup G}
    (hJ : GLAPComponent 3 X J) {ι : Type*} (N : ι → Subgroup G) (hNX : ∀ i, N i ≤ X)
    (hNn : ∀ i, ∀ c ∈ X, ∀ n ∈ N i, c * n * c⁻¹ ∈ N i)
    (hNq : ∀ i, CFSG.IsQuasisimple (N i))
    (hk : ∃ k : ℕ, ∀ x ∈ derivedSeries ↥X k, (x : G) ∈ ⨆ i, N i)
    {φ : MulAut G} (hφX : ∀ x, φ x ∈ X ↔ x ∈ X)
    (hφ : ∀ i, barX 3 X (N i) = barX 3 X J →
      ∃ n ∈ N i, ∀ m ∈ N i, φ m = n * m * n⁻¹) :
    ∃ j₀ ∈ J, ∀ j ∈ J, ∀ (h1 : φ j ∈ X) (h2 : j₀ * j * j₀⁻¹ ∈ X),
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨φ j, h1⟩ =
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨j₀ * j * j₀⁻¹, h2⟩ := by
  classical
  obtain ⟨i, hi⟩ := exists_barX_eq_of_blocks hJ N hNX hNn hNq hk
  obtain ⟨n, hn, hφn⟩ := hφ i hi.symm
  set π : ↥X →* ↥X ⧸ GLAPPrimeCore 3 ↥X := QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) with hπ
  let σ : ↥X ≃* ↥X :=
    { toFun := fun x => ⟨φ (x : G), (hφX x).2 x.2⟩
      invFun := fun x => ⟨φ.symm (x : G), (hφX (φ.symm (x : G))).1 (by simpa using x.2)⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (map_mul φ (a : G) (b : G)) }
  have hσR : ∀ r ∈ GLAPPrimeCore 3 ↥X, σ r ∈ GLAPPrimeCore 3 ↥X := fun r hr =>
    map_gLAPPrimeCore_le 3 σ ⟨r, hr, rfl⟩
  have hnbar : π ⟨n, hNX i hn⟩ ∈ barX 3 X J := by
    rw [hi]
    exact ⟨⟨n, hNX i hn⟩, Subgroup.mem_subgroupOf.2 hn, rfl⟩
  obtain ⟨j₀', hj₀', hj₀π⟩ := hnbar
  refine ⟨(j₀' : G), Subgroup.mem_subgroupOf.1 hj₀', fun j hj h1 h2 => ?_⟩
  set n' : ↥X := ⟨n, hNX i hn⟩ with hn'
  set j' : ↥X := ⟨j, hJ.1 hj⟩ with hj'
  have hjbar : π j' ∈ barX 3 X (N i) := by
    rw [← hi]
    exact ⟨j', Subgroup.mem_subgroupOf.2 hj, rfl⟩
  obtain ⟨m', hm', hmπ⟩ := hjbar
  have hm'N : (m' : G) ∈ N i := Subgroup.mem_subgroupOf.1 hm'
  have hcong : π (σ j') = π (σ m') := by
    have h0' : π (j'⁻¹ * m') = 1 := by rw [map_mul, map_inv, hmπ, inv_mul_cancel]
    have h0 : j'⁻¹ * m' ∈ GLAPPrimeCore 3 ↥X := (QuotientGroup.eq_one_iff _).1 h0'
    have h3 := hσR _ h0
    rw [map_mul, map_inv] at h3
    have h4 : π ((σ j')⁻¹ * σ m') = 1 := (QuotientGroup.eq_one_iff _).2 h3
    rw [map_mul, map_inv] at h4
    exact (inv_mul_eq_one.1 h4)
  have e1 : (⟨φ j, h1⟩ : ↥X) = σ j' := rfl
  have e2 : (⟨(j₀' : G) * j * (j₀' : G)⁻¹, h2⟩ : ↥X) = j₀' * j' * j₀'⁻¹ := rfl
  have e3 : σ m' = n' * m' * n'⁻¹ := Subtype.ext (hφn (m' : G) hm'N)
  have hj₀π' : π j₀' = π n' := hj₀π
  have hmπ' : π m' = π j' := hmπ
  rw [e1, e2, hcong, e3]
  simp only [map_mul, map_inv, hj₀π', hmπ']

end CFSG.HardMathSupport.Dickson.Sec6.I1431

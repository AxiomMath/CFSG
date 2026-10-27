module

public import CFSG.RankThree.PartOne.S11c.G2Torus
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8FourAux.Expo
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8TenTwelveAux.TwelveD4Data
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne CFSG.RankThree.Chevalley CFSG.LieType.Steinberg.Adjoint
open scoped Matrix

set_option linter.unusedSectionVars false


theorem e8T12_rootSpan_mono {L : Type} [Field L] {A B : Set (Fin Tag.E8.rank → ℤ)} (h : A ⊆ B) :
    rootSpan Tag.E8 L A ≤ rootSpan Tag.E8 L B :=
  iSup₂_le fun γ hγ => le_iSup₂_of_le γ (h hγ) le_rfl

theorem e8T12_hm_coroot {γ : Fin Tag.E8.rank → ℤ} (hγ : IsRoot Tag.E8 γ)
    (δ : Fin Tag.E8.rank → ℤ) :
    2 * iform γ δ / iform γ γ = ∑ i, δ i * e8T12Coroot γ i := by
  have h2 : iform γ γ = 2 := by
    obtain ⟨j, hj⟩ := iform_self_of_isRoot hγ
    simpa [Tag.symmetrizer] using hj
  rw [h2]
  have hB : Tag.E8.symmetrizedCartan = Tag.E8.cartan := by
    simp [Tag.symmetrizedCartan, Tag.symmetrizer]
  have e : iform γ δ = ∑ i, δ i * e8T12Coroot γ i := by
    simp only [iform, hB, e8T12Coroot, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  omega

theorem e8T12_rootSL2_mem_rootSpan_pair {L : Type} [Field L] {β : Fin Tag.E8.rank → ℤ}
    (hβ : IsRoot Tag.E8 β) (B : SL2 L) : rootSL2 Tag.E8 L β B ∈ rootSpan Tag.E8 L {β, -β} := by
  have hB : rootSL2 Tag.E8 L β B ∈ rootRankOneGroup Tag.E8 L β := ⟨B, rfl⟩
  rw [(exceptional_Lang_root_rank_one_torus_transport Tag.E8 L hβ).1] at hB
  exact sup_le (le_iSup₂_of_le (f := fun γ (_ : γ ∈ ({β, -β} : Set (Fin Tag.E8.rank → ℤ))) =>
    rootSubgroup Tag.E8 L γ) β (Set.mem_insert _ _) le_rfl)
    (le_iSup₂_of_le (f := fun γ (_ : γ ∈ ({β, -β} : Set (Fin Tag.E8.rank → ℤ))) =>
      rootSubgroup Tag.E8 L γ) (-β) (Set.mem_insert_of_mem _ rfl) le_rfl) hB

theorem e8T12_rootDiagUnit_mem_rootSpan {L : Type} [Field L] (ζ : Lˣ)
    {S : Set (Fin Tag.E8.rank → ℤ)} (γ : Fin 4 → Fin Tag.E8.rank → ℤ)
    (hγ : ∀ k, IsRoot Tag.E8 (γ k)) (hS : ∀ k, γ k ∈ S ∧ -γ k ∈ S) (u : Fin 4 → ℤ) :
    rootDiagUnit Tag.E8 (fun i => ζ ^ (∑ k, u k * e8T12Coroot (γ k) i)) ∈ rootSpan Tag.E8 L S := by
  set x : Fin 4 → ModGL Tag.E8 L := fun k => rootSL2 Tag.E8 L (γ k) (HSL (ζ ^ u k)) with hx
  have hxk : ∀ k, x k = rootDiagUnit Tag.E8 (fun i => (ζ ^ u k) ^ e8T12Coroot (γ k) i) :=
    fun k => rootSL2_HSL_eq_rootDiagUnit (hγ k) (e8T12Coroot (γ k))
      (fun δ _ => e8T12_hm_coroot (hγ k) δ) _
  have hmem : ∀ k, x k ∈ rootSpan Tag.E8 L S := fun k => by
    have h1 := e8T12_rootSL2_mem_rootSpan_pair (L := L) (hγ k) (HSL (ζ ^ u k))
    refine (e8T12_rootSpan_mono ?_) h1
    intro y hy
    rcases hy with rfl | hy
    · exact (hS k).1
    · rw [Set.mem_singleton_iff.1 hy]
      exact (hS k).2
  have hprod : rootDiagUnit Tag.E8 (fun i => ζ ^ (∑ k, u k * e8T12Coroot (γ k) i)) =
      x 0 * x 1 * x 2 * x 3 := by
    rw [hxk 0, hxk 1, hxk 2, hxk 3, ← rootDiagUnit_mul, ← rootDiagUnit_mul, ← rootDiagUnit_mul]
    congr 1
    funext i
    simp only [Pi.mul_apply, Fin.sum_univ_four, zpow_add, ← zpow_mul]
  rw [hprod]
  exact mul_mem (mul_mem (mul_mem (hmem 0) (hmem 1)) (hmem 2)) (hmem 3)

theorem e8T12_rootDiagUnit_mem_twistedTorus {L : Type} [Field L] {p : ℕ} {ζ : Lˣ}
    (hζ : orderOf ζ = p) {n : ModGL Tag.E8 L} {Fr : L →+* L} {q : ℕ} (hFr : ∀ x, Fr x = x ^ q)
    {M : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ}
    (hT : twistedTorusOf n (Units.map (entrywiseHom Fr)) =
      (fixedCharTuples M Fr).map (rootDiagUnitHom Tag.E8 L))
    (e : Fin Tag.E8.rank → ℤ) (hW : ∀ j, (p : ℤ) ∣ (∑ i, e i * M i j) - q * e j) :
    rootDiagUnit Tag.E8 (fun i => ζ ^ e i) ∈ twistedTorusOf n (Units.map (entrywiseHom Fr)) := by
  rw [hT]
  refine ⟨fun i => ζ ^ e i, ?_, rfl⟩
  rw [SetLike.mem_coe, mem_fixedCharTuples_iff]
  intro v
  change rootChar (τ := Tag.E8) (tupE ζ e) (M *ᵥ v) =
    Units.map Fr.toMonoidHom (rootChar (τ := Tag.E8) (tupE ζ e) v)
  rw [rootChar_tupE, rootChar_tupE, CTTorus.map_units_eq_pow hFr, ← zpow_natCast, ← zpow_mul,
    zpow_eq_zpow_iff_modEq, hζ, dotE_mulVec]
  refine (Int.modEq_iff_dvd.2 ?_).symm
  have h : (∑ j, (∑ i, e i * M i j) * v j) - dotE e v * (q : ℤ) =
      ∑ j, ((∑ i, e i * M i j) - q * e j) * v j := by
    rw [dotE, Finset.sum_mul (s := Finset.univ) (f := fun j => e j * v j),
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [h]
  exact Finset.dvd_sum fun j _ => Dvd.dvd.mul_right (hW j) _

theorem e8T12_orderOf_rootDiagUnit {L : Type} [Field L] {p : ℕ} (hp : p.Prime) {ζ : Lˣ}
    (hζ : orderOf ζ = p) (e : Fin Tag.E8.rank → ℤ) (he : ∃ i, ¬ (p : ℤ) ∣ e i) :
    orderOf (rootDiagUnit Tag.E8 (fun i => ζ ^ e i) : ModGL Tag.E8 L) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine orderOf_eq_prime ?_ ?_
  · have : (rootDiagUnitHom Tag.E8 L (fun i => ζ ^ e i)) ^ p = rootDiagUnitHom Tag.E8 L 1 := by
      rw [← map_pow (rootDiagUnitHom Tag.E8 L)]
      congr 1
      funext i
      change (ζ ^ e i) ^ p = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hζ,
        pow_orderOf_eq_one, one_zpow]
    rw [map_one] at this
    exact this
  · intro h1
    obtain ⟨i, hi⟩ := he
    have h2 : (fun i => ζ ^ e i : Fin Tag.E8.rank → Lˣ) = 1 := by
      apply CFSG.LieType.Chevalley.rootDiagUnit_injective
      rw [h1, rootDiagUnit_one]
    have h3 : ζ ^ e i = 1 := congrFun h2 i
    exact hi (by have := orderOf_dvd_iff_zpow_eq_one.2 h3; rwa [hζ] at this)

@[expose] def e8T12D4Node (k : Fin 4) : Fin Tag.E8.rank :=
  ⟨k.val + 1, by have := k.2; change k.val + 1 < 8; omega⟩

theorem e8T12_wordProd_smul_node (w : List (Fin Tag.E8.rank)) (k : Fin 4) :
    (coxeterSystem Tag.E8).wordProd w • (Pi.single (e8T12D4Node k) 1 : Fin Tag.E8.rank → ℤ) =
      e8T12D4Gamma w k := by
  rw [wordProd_smul_eq_wordMat_mulVec, wordMat_e8wl]
  funext j
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, toMat, e8T12D4Gamma, e8T12D4Node]

theorem e8T12_D4Node_mem (k : Fin 4) : e8T12D4Node k ∈ d4Nodes Tag.E8 := by
  have := k.2
  show 1 ≤ k.val + 1 ∧ k.val + 1 ≤ 4
  omega

theorem e8T12_single_mem_D4 (k : Fin 4) :
    (Pi.single (e8T12D4Node k) 1 : Fin Tag.E8.rank → ℤ) ∈
      parabolicRoots Tag.E8 (d4Nodes Tag.E8) :=
  ⟨isRoot_single Tag.E8 _, fun j hj =>
    Pi.single_eq_of_ne (fun e => hj (by rw [e]; exact e8T12_D4Node_mem k)) 1⟩

theorem e8T12_neg_single_mem_D4 (k : Fin 4) :
    (-Pi.single (e8T12D4Node k) 1 : Fin Tag.E8.rank → ℤ) ∈
      parabolicRoots Tag.E8 (d4Nodes Tag.E8) :=
  ⟨isRoot_neg_single Tag.E8 _, fun j hj => by
    have hne : j ≠ e8T12D4Node k := fun e => hj (by rw [e]; exact e8T12_D4Node_mem k)
    have h : (Pi.single (e8T12D4Node k) 1 : Fin Tag.E8.rank → ℤ) j = 0 := Pi.single_eq_of_ne hne 1
    simp [h]⟩

theorem e8T12_isRoot_D4Gamma (w : List (Fin Tag.E8.rank)) (k : Fin 4) :
    IsRoot Tag.E8 (e8T12D4Gamma w k) := by
  rw [← e8T12_wordProd_smul_node]
  exact IsRoot.smul (isRoot_single Tag.E8 _) _

theorem e8T12_D4Gamma_mem (w : List (Fin Tag.E8.rank)) (k : Fin 4) :
    e8T12D4Gamma w k ∈ (fun γ => (coxeterSystem Tag.E8).wordProd w • γ) ''
        parabolicRoots Tag.E8 (d4Nodes Tag.E8) ∧
      -e8T12D4Gamma w k ∈ (fun γ => (coxeterSystem Tag.E8).wordProd w • γ) ''
        parabolicRoots Tag.E8 (d4Nodes Tag.E8) := by
  refine ⟨⟨_, e8T12_single_mem_D4 k, e8T12_wordProd_smul_node w k⟩,
    ⟨_, e8T12_neg_single_mem_D4 k, ?_⟩⟩
  show (coxeterSystem Tag.E8).wordProd w • (-Pi.single (e8T12D4Node k) 1 : Fin Tag.E8.rank → ℤ) =
    -e8T12D4Gamma w k
  rw [smul_neg, e8T12_wordProd_smul_node]

theorem e8T12_D4Exp_comb (w : List (Fin Tag.E8.rank)) (g₀ g₁ g₂ g₃ : ℤ) (y : Fin 4 → Fin 4 → ℤ)
    (i : Fin Tag.E8.rank) :
    e8T12D4Exp w (fun k => g₀ * y 0 k + g₁ * y 1 k + g₂ * y 2 k + g₃ * y 3 k) i =
      g₀ * e8T12D4Exp w (y 0) i + g₁ * e8T12D4Exp w (y 1) i + g₂ * e8T12D4Exp w (y 2) i +
        g₃ * e8T12D4Exp w (y 3) i := by
  simp only [e8T12D4Exp, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

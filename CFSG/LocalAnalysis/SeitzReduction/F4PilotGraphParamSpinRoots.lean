module

public import CFSG.LieType.Universal.Spin.Datum
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Steinberg.TwistedE6.Defs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG.Blueprint.Chevalley
open CFSG.LieType.Universal.Spin (cartanD isFiniteType_cartanD toStdD rootsD_eq boolSign)
open CFSG.LieType.RootSystem (roots weylAction coxeterMatrix reflection reflection_apply
  weylAction_simple weylAction_mul_apply)

local instance f4PilotGraphParamSpinRootsNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

@[expose] def d4Node (i : Fin 4) : Fin (Tag.rank .E6) := (![1, 3, 2, 4] : Fin 4 → Fin 6) i

@[expose] def d4Embed (v : Fin 4 → ℤ) : Fin (Tag.rank .E6) → ℤ :=
  (![0, v 0, v 2, v 1, v 3, 0] : Fin 6 → ℤ)

@[expose] def e6RestrictD4 (γ : Fin (Tag.rank .E6) → ℤ) : Fin 4 → ℤ := fun i => γ (d4Node i)

theorem d4Embed_d4Node (v : Fin 4 → ℤ) (i : Fin 4) : d4Embed v (d4Node i) = v i := by
  fin_cases i <;> rfl

theorem d4Embed_zero_apply (v : Fin 4 → ℤ) : d4Embed v 0 = 0 := rfl

theorem d4Embed_five_apply (v : Fin 4 → ℤ) : d4Embed v 5 = 0 := rfl

theorem eq_d4Node_or : ∀ j : Fin (Tag.rank .E6), j = 0 ∨ j = 5 ∨ ∃ i, j = d4Node i := by
  decide

theorem ext_d4Node {γ δ : Fin (Tag.rank .E6) → ℤ} (h : ∀ i, γ (d4Node i) = δ (d4Node i))
    (h0 : γ 0 = δ 0) (h5 : γ 5 = δ 5) : γ = δ := by
  funext j
  rcases eq_d4Node_or j with rfl | rfl | ⟨i, rfl⟩
  exacts [h0, h5, h i]

theorem e6RestrictD4_d4Embed (v : Fin 4 → ℤ) : e6RestrictD4 (d4Embed v) = v :=
  funext (d4Embed_d4Node v)

theorem d4Embed_injective : Function.Injective d4Embed := fun v w h => by
  rw [← e6RestrictD4_d4Embed v, h, e6RestrictD4_d4Embed]

theorem d4Embed_add (v w : Fin 4 → ℤ) : d4Embed (v + w) = d4Embed v + d4Embed w :=
  ext_d4Node (fun i => by simp only [d4Embed_d4Node, Pi.add_apply])
    (by simp only [Pi.add_apply, d4Embed_zero_apply, add_zero])
    (by simp only [Pi.add_apply, d4Embed_five_apply, add_zero])

theorem d4Embed_neg (v : Fin 4 → ℤ) : d4Embed (-v) = -d4Embed v :=
  ext_d4Node (fun i => by simp only [d4Embed_d4Node, Pi.neg_apply])
    (by simp only [Pi.neg_apply, d4Embed_zero_apply, neg_zero])
    (by simp only [Pi.neg_apply, d4Embed_five_apply, neg_zero])

theorem d4Embed_sub (v w : Fin 4 → ℤ) : d4Embed (v - w) = d4Embed v - d4Embed w := by
  rw [sub_eq_add_neg, d4Embed_add, d4Embed_neg, ← sub_eq_add_neg]

theorem d4Embed_smul (n : ℤ) (v : Fin 4 → ℤ) : d4Embed (n • v) = n • d4Embed v :=
  ext_d4Node (fun i => by simp only [d4Embed_d4Node, Pi.smul_apply])
    (by simp only [Pi.smul_apply, d4Embed_zero_apply, smul_zero])
    (by simp only [Pi.smul_apply, d4Embed_five_apply, smul_zero])

theorem d4Embed_zero : d4Embed 0 = 0 :=
  ext_d4Node (fun i => by simp only [d4Embed_d4Node, Pi.zero_apply])
    (by simp only [Pi.zero_apply, d4Embed_zero_apply])
    (by simp only [Pi.zero_apply, d4Embed_five_apply])

theorem d4Embed_single_check :
    ∀ i : Fin 4, d4Embed (Pi.single i 1) = Pi.single (d4Node i) 1 := by
  decide

theorem d4Embed_single (i : Fin 4) : d4Embed (Pi.single i 1) = Pi.single (d4Node i) 1 :=
  d4Embed_single_check i

theorem cartan_E6_d4Node_check : ∀ p : Fin 4 × Fin 4,
    Tag.cartan .E6 (d4Node p.1) (d4Node p.2) = cartanD 4 p.1 p.2 := by
  decide

theorem sum_cartan_E6_mul_d4Embed (i : Fin 4) (v : Fin 4 → ℤ) :
    ∑ j, Tag.cartan .E6 (d4Node i) j * d4Embed v j = ∑ j, cartanD 4 i j * v j := by
  have h := fun j => cartan_E6_d4Node_check (i, j)
  change (∑ j : Fin 6, Tag.cartan .E6 (d4Node i) j * d4Embed v j) = _
  rw [Fin.sum_univ_six, Fin.sum_univ_four, ← h 0, ← h 1, ← h 2, ← h 3]
  change Tag.cartan .E6 (d4Node i) 0 * 0 + Tag.cartan .E6 (d4Node i) 1 * v 0 +
      Tag.cartan .E6 (d4Node i) 2 * v 2 + Tag.cartan .E6 (d4Node i) 3 * v 1 +
      Tag.cartan .E6 (d4Node i) 4 * v 3 + Tag.cartan .E6 (d4Node i) 5 * 0 =
    Tag.cartan .E6 (d4Node i) 1 * v 0 + Tag.cartan .E6 (d4Node i) 3 * v 1 +
      Tag.cartan .E6 (d4Node i) 2 * v 2 + Tag.cartan .E6 (d4Node i) 4 * v 3
  ring

theorem d4Embed_reflection (i : Fin 4) (v : Fin 4 → ℤ) :
    d4Embed (reflection (cartanD 4) i v) = reflect .E6 (d4Node i) (d4Embed v) := by
  rw [reflection_apply, reflect, d4Embed_sub, d4Embed_smul, d4Embed_single,
    sum_cartan_E6_mul_d4Embed]

theorem isRoot_d4Embed {v : Fin 4 → ℤ} (hv : v ∈ roots (isFiniteType_cartanD 4) ∅) :
    IsRoot .E6 (d4Embed v) := by
  rcases hv with ⟨w, i, rfl⟩ | ⟨w, i, hi, -⟩
  · obtain ⟨ω, rfl⟩ :=
      (coxeterMatrix (isFiniteType_cartanD 4)).toCoxeterSystem.wordProd_surjective w
    induction ω with
    | nil =>
      rw [CoxeterSystem.wordProd_nil, map_one, Module.End.one_apply, d4Embed_single]
      exact IsRoot.basis _
    | cons j ω ih =>
      rw [CoxeterSystem.wordProd_cons, weylAction_mul_apply, weylAction_simple,
        d4Embed_reflection]
      exact IsRoot.reflect _ ih
  · exact absurd hi (Set.notMem_empty i)

set_option maxRecDepth 100000 in
theorem d4RootsCheck :
    ∀ γ ∈ rootFinset .E6, γ 0 = 0 → γ 5 = 0 → ∃ i j : Fin 4, i ≠ j ∧ ∃ s t : Bool,
      toStdD 4 (e6RestrictD4 γ) = Pi.single i (boolSign s) + Pi.single j (boolSign t) := by
  decide +kernel

theorem mem_rootsD_e6RestrictD4 {γ : Fin (Tag.rank .E6) → ℤ}
    (hγ : IsRoot .E6 γ) (h0 : γ 0 = 0) (h5 : γ 5 = 0) :
    e6RestrictD4 γ ∈ roots (isFiniteType_cartanD 4) ∅ := by
  obtain ⟨i, j, hij, s, t, h⟩ := d4RootsCheck γ (mem_rootFinset.2 hγ) h0 h5
  rw [rootsD_eq (n := 4) (by norm_num)]
  exact ⟨i, j, boolSign s, boolSign t, hij,
    CFSG.LieType.Universal.Spin.boolSign_eq_one_or_eq_neg_one s,
    CFSG.LieType.Universal.Spin.boolSign_eq_one_or_eq_neg_one t, h⟩

theorem isRoot_d4Embed_iff {v : Fin 4 → ℤ} :
    IsRoot .E6 (d4Embed v) ↔ v ∈ roots (isFiniteType_cartanD 4) ∅ := by
  refine ⟨fun h => ?_, isRoot_d4Embed⟩
  have := mem_rootsD_e6RestrictD4 h (d4Embed_zero_apply v) (d4Embed_five_apply v)
  rwa [e6RestrictD4_d4Embed] at this

@[expose] def d4Swap (v : Fin 4 → ℤ) : Fin 4 → ℤ := (![v 0, v 1, v 3, v 2] : Fin 4 → ℤ)

theorem rho_d4Embed (v : Fin 4 → ℤ) :
    CFSG.LieType.Steinberg.TwistedE6.rho (d4Embed v) = d4Embed (d4Swap v) := by
  funext j
  fin_cases j <;> rfl

theorem d4Swap_mem_roots {v : Fin 4 → ℤ}
    (hv : v ∈ roots (isFiniteType_cartanD 4) ∅) : d4Swap v ∈ roots (isFiniteType_cartanD 4) ∅ := by
  rw [← isRoot_d4Embed_iff, ← rho_d4Embed]
  exact CFSG.LieType.Steinberg.TwistedE6.isRoot_rho (isRoot_d4Embed hv)

end CFSG.SeitzReduction.F4Pilot

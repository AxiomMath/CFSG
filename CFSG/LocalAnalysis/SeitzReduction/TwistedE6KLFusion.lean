module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCentralizerT
public import CFSG.LocalAnalysis.SeitzReduction.EnKLOrderSix
import CFSG.RankThree.GF2n.Stroth80.Sec117ConfigBasic

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.GF2n.Stroth80


variable {f : ℕ} {K : Type} [Field K]

private theorem commutator_classV_pair_eq [CharP K 2] (σ : K →+* K) :
    (commutatorElement (G := ModGL TwistTag.E6.tag K)).bracket
        (twistedE6PairX σ twistedE6ClassRootA 1)
        (twistedE6PairX σ (fun i : Fin TwistTag.E6.tag.rank =>
          (![-1, 0, -1, -1, 0, 0] : Fin 6 → ℤ) i) 1) =
      twistedE6PairX σ (twistedE6ClassRootA + (fun i : Fin TwistTag.E6.tag.rank =>
        (![-1, 0, -1, -1, 0, 0] : Fin 6 → ℤ) i)) 1 := by
  let eps : Fin TwistTag.E6.tag.rank → ℤ :=
    fun i : Fin TwistTag.E6.tag.rank => (![-1, 0, -1, -1, 0, 0] : Fin 6 → ℤ) i
  change (commutatorElement (G := ModGL TwistTag.E6.tag K)).bracket
      (twistedE6PairX σ twistedE6ClassRootA 1) (twistedE6PairX σ eps 1) =
    twistedE6PairX σ (twistedE6ClassRootA + eps) 1
  have hδ : IsRoot TwistTag.E6.tag twistedE6ClassRootA :=
    isRoot_twistedE6ClassRoots.2.2.1
  have hε : IsRoot TwistTag.E6.tag eps := by
    rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel
  have hγ : IsRoot TwistTag.E6.tag (twistedE6ClassRootA + eps) := by
    rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel
  have hne : twistedE6ClassRootA ≠ eps := by decide
  have h1 : ¬ IsRoot TwistTag.E6.tag
      (twistedE6ClassRootA + permLattice TwistTag.E6.perm eps) := by
    rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel
  have h1' : twistedE6ClassRootA + permLattice TwistTag.E6.perm eps ≠ 0 := by decide
  have h2 : ¬ IsRoot TwistTag.E6.tag
      (permLattice TwistTag.E6.perm (twistedE6ClassRootA + eps) + twistedE6ClassRootA) := by
    rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel
  have h2' : permLattice TwistTag.E6.perm (twistedE6ClassRootA + eps) +
      twistedE6ClassRootA ≠ 0 := by decide
  have h3 : ¬ IsRoot TwistTag.E6.tag
      (permLattice TwistTag.E6.perm (twistedE6ClassRootA + eps) + eps) := by
    rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel
  have h3' : permLattice TwistTag.E6.perm (twistedE6ClassRootA + eps) + eps ≠ 0 := by decide
  have h := commutator_twistedE6PairX_pairSum σ hδ hε hγ hne h1 h1' h2 h2' h3 h3' 1 1
  simpa using h

private theorem commute_classV_pair_beta [CharP K 2] :
    Commute (pinnedX TwistTag.E6.tag K twistedE6ClassRootA 1 *
        pinnedX TwistTag.E6.tag K twistedE6ClassRootA' 1)
      (pinnedX TwistTag.E6.tag K twistedE6ClassRootB 1) := by
  have hA : IsRoot TwistTag.E6.tag twistedE6ClassRootA :=
    isRoot_twistedE6ClassRoots.2.2.1
  have hA' : IsRoot TwistTag.E6.tag twistedE6ClassRootA' :=
    isRoot_twistedE6ClassRoots.2.2.2.1
  have hB : IsRoot TwistTag.E6.tag twistedE6ClassRootB :=
    isRoot_twistedE6ClassRoots.2.2.2.2
  exact (commute_pinnedX_of_not_isRoot_of_ne_zero_E6 hA hB
      (by rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel) (by decide) 1 1).mul_left
    (commute_pinnedX_of_not_isRoot_of_ne_zero_E6 hA' hB
      (by rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel) (by decide) 1 1)

private theorem commute_classV_c_beta [CharP K 2] :
    Commute (pinnedX TwistTag.E6.tag K (fun i : Fin TwistTag.E6.tag.rank =>
        (![-1, 0, -1, -1, 0, 0] : Fin 6 → ℤ) i) 1 *
      pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm
        (fun i : Fin TwistTag.E6.tag.rank => (![-1, 0, -1, -1, 0, 0] : Fin 6 → ℤ) i)) 1)
      (pinnedX TwistTag.E6.tag K twistedE6ClassRootB 1) := by
  let eps : Fin TwistTag.E6.tag.rank → ℤ :=
    fun i : Fin TwistTag.E6.tag.rank => (![-1, 0, -1, -1, 0, 0] : Fin 6 → ℤ) i
  change Commute (pinnedX TwistTag.E6.tag K eps 1 *
    pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm eps) 1)
    (pinnedX TwistTag.E6.tag K twistedE6ClassRootB 1)
  have hε : IsRoot TwistTag.E6.tag eps := by
    rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel
  have hρε : IsRoot TwistTag.E6.tag (permLattice TwistTag.E6.perm eps) :=
    hε.permLattice TwistTag.E6.cartan_perm
  have hB : IsRoot TwistTag.E6.tag twistedE6ClassRootB :=
    isRoot_twistedE6ClassRoots.2.2.2.2
  exact (commute_pinnedX_of_not_isRoot_of_ne_zero_E6 hε hB
      (by rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel) (by decide) 1 1).mul_left
    (commute_pinnedX_of_not_isRoot_of_ne_zero_E6 hρε hB
      (by rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel) (by decide) 1 1)

private theorem commute_classV_pair_neg_beta [CharP K 2] :
    Commute (pinnedX TwistTag.E6.tag K twistedE6ClassRootA 1 *
        pinnedX TwistTag.E6.tag K twistedE6ClassRootA' 1)
      (pinnedX TwistTag.E6.tag K (-twistedE6ClassRootB) 1) := by
  have hA : IsRoot TwistTag.E6.tag twistedE6ClassRootA :=
    isRoot_twistedE6ClassRoots.2.2.1
  have hA' : IsRoot TwistTag.E6.tag twistedE6ClassRootA' :=
    isRoot_twistedE6ClassRoots.2.2.2.1
  have hB : IsRoot TwistTag.E6.tag (-twistedE6ClassRootB) :=
    CFSG.LieType.Chevalley.IsRoot.neg isRoot_twistedE6ClassRoots.2.2.2.2
  exact (commute_pinnedX_of_not_isRoot_of_ne_zero_E6 hA hB
      (by rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel) (by decide) 1 1).mul_left
    (commute_pinnedX_of_not_isRoot_of_ne_zero_E6 hA' hB
      (by rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel) (by decide) 1 1)

private theorem commute_classV_c_neg_beta [CharP K 2] :
    Commute (pinnedX TwistTag.E6.tag K (fun i : Fin TwistTag.E6.tag.rank =>
        (![-1, 0, -1, -1, 0, 0] : Fin 6 → ℤ) i) 1 *
      pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm
        (fun i : Fin TwistTag.E6.tag.rank => (![-1, 0, -1, -1, 0, 0] : Fin 6 → ℤ) i)) 1)
      (pinnedX TwistTag.E6.tag K (-twistedE6ClassRootB) 1) := by
  let eps : Fin TwistTag.E6.tag.rank → ℤ :=
    fun i : Fin TwistTag.E6.tag.rank => (![-1, 0, -1, -1, 0, 0] : Fin 6 → ℤ) i
  change Commute (pinnedX TwistTag.E6.tag K eps 1 *
    pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm eps) 1)
    (pinnedX TwistTag.E6.tag K (-twistedE6ClassRootB) 1)
  have hε : IsRoot TwistTag.E6.tag eps := by
    rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel
  have hρε : IsRoot TwistTag.E6.tag (permLattice TwistTag.E6.perm eps) :=
    hε.permLattice TwistTag.E6.cartan_perm
  have hB : IsRoot TwistTag.E6.tag (-twistedE6ClassRootB) :=
    CFSG.LieType.Chevalley.IsRoot.neg isRoot_twistedE6ClassRoots.2.2.2.2
  exact (commute_pinnedX_of_not_isRoot_of_ne_zero_E6 hε hB
      (by rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel) (by decide) 1 1).mul_left
    (commute_pinnedX_of_not_isRoot_of_ne_zero_E6 hρε hB
      (by rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel) (by decide) 1 1)

private theorem commute_classV_pair_correction [CharP K 2] :
    Commute (pinnedX TwistTag.E6.tag K twistedE6ClassRootA 1 *
        pinnedX TwistTag.E6.tag K twistedE6ClassRootA' 1)
      (pinnedX TwistTag.E6.tag K (twistedE6ClassRootA + (fun i : Fin TwistTag.E6.tag.rank =>
          (![-1, 0, -1, -1, 0, 0] : Fin 6 → ℤ) i)) 1 *
        pinnedX TwistTag.E6.tag K (twistedE6ClassRootA' + permLattice TwistTag.E6.perm
          (fun i : Fin TwistTag.E6.tag.rank => (![-1, 0, -1, -1, 0, 0] : Fin 6 → ℤ) i)) 1) := by
  let eps : Fin TwistTag.E6.tag.rank → ℤ :=
    fun i : Fin TwistTag.E6.tag.rank => (![-1, 0, -1, -1, 0, 0] : Fin 6 → ℤ) i
  change Commute (pinnedX TwistTag.E6.tag K twistedE6ClassRootA 1 *
    pinnedX TwistTag.E6.tag K twistedE6ClassRootA' 1)
    (pinnedX TwistTag.E6.tag K (twistedE6ClassRootA + eps) 1 *
      pinnedX TwistTag.E6.tag K (twistedE6ClassRootA' +
        permLattice TwistTag.E6.perm eps) 1)
  obtain ⟨-, -, hA, hA', hB⟩ := isRoot_twistedE6ClassRoots
  have hα : IsRoot TwistTag.E6.tag (twistedE6ClassRootA + eps) := by
    rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel
  have hρ : IsRoot TwistTag.E6.tag (twistedE6ClassRootA' +
      permLattice TwistTag.E6.perm eps) := by
    rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel
  have hcomm (a b : Fin TwistTag.E6.tag.rank → ℤ) (ha : IsRoot TwistTag.E6.tag a)
      (hb : IsRoot TwistTag.E6.tag b) (hab : ¬ IsRoot TwistTag.E6.tag (a + b))
      (h0 : a + b ≠ 0) : Commute (pinnedX TwistTag.E6.tag K a 1)
        (pinnedX TwistTag.E6.tag K b 1) :=
    commute_pinnedX_of_not_isRoot_of_ne_zero_E6 ha hb hab h0 1 1
  exact ((hcomm twistedE6ClassRootA (twistedE6ClassRootA + eps) hA hα
        (by rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel) (by decide)).mul_left
      (hcomm twistedE6ClassRootA' (twistedE6ClassRootA + eps) hA' hα
        (by rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel) (by decide))).mul_right
      ((hcomm twistedE6ClassRootA (twistedE6ClassRootA' + permLattice TwistTag.E6.perm eps)
          hA hρ (by rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel) (by decide)).mul_left
        (hcomm twistedE6ClassRootA' (twistedE6ClassRootA' + permLattice TwistTag.E6.perm eps)
          hA' hρ (by rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel) (by decide)))

private theorem twistedE6PairX_sq [CharP K 2] (σ : K →+* K)
    {δ : Fin TwistTag.E6.tag.rank → ℤ} (hδ : IsRoot TwistTag.E6.tag δ) :
    twistedE6PairX σ δ 1 ^ 2 = 1 := by
  have hcomm : Commute (pinnedX TwistTag.E6.tag K δ 1)
      (pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ) 1) :=
    commute_pinnedX_permLattice_twistedE6 (K := K) hδ 1 1
  rw [twistedE6PairX, map_one, hcomm.mul_pow, pinnedX_one_sq_of_charTwo,
    pinnedX_one_sq_of_charTwo, one_mul]

private theorem twistedE6PairX_ne_one_of_pos_of_ne_fixed [CharP K 2] (σ : K →+* K)
    {δ : Fin TwistTag.E6.tag.rank → ℤ} (hδ : IsRoot TwistTag.E6.tag δ)
    (hpos : 0 < height δ) (hρ : permLattice TwistTag.E6.perm δ ≠ δ) :
    twistedE6PairX σ δ 1 ≠ 1 := by
  intro h1
  have h1' : pinnedX TwistTag.E6.tag K δ 1 *
      pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ) 1 = 1 := by
    rw [twistedE6PairX, map_one] at h1
    exact h1
  have hnd : ([δ, permLattice TwistTag.E6.perm δ] :
      List (Fin TwistTag.E6.tag.rank → ℤ)).Nodup := by
    simpa [Ne, eq_comm] using hρ
  have hρδ : IsRoot TwistTag.E6.tag (permLattice TwistTag.E6.perm δ) :=
    hδ.permLattice TwistTag.E6.cartan_perm
  have hρpos : 0 < height (permLattice TwistTag.E6.perm δ) := by
    rwa [height_permLattice]
  have hL : ∀ γ ∈ [δ, permLattice TwistTag.E6.perm δ],
      IsRoot TwistTag.E6.tag γ ∧ 0 < height γ := by
    intro γ hγ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with rfl | rfl
    · exact ⟨hδ, hpos⟩
    · exact ⟨hρδ, hρpos⟩
  have hprod : ([δ, permLattice TwistTag.E6.perm δ].map fun γ =>
        pinnedX TwistTag.E6.tag K γ (1 : K)).prod =
      ([δ, permLattice TwistTag.E6.perm δ].map fun γ =>
        pinnedX TwistTag.E6.tag K γ (0 : K)).prod := by
    simpa [pinnedX_zero] using h1'
  have key := pinnedX_list_prod_injective (τ := TwistTag.E6.tag) (R := K)
    [δ, permLattice TwistTag.E6.perm δ] hnd hL
    (fun _ => (1 : K)) (fun _ => (0 : K)) hprod δ (by simp)
  exact one_ne_zero key

private theorem orderOf_twistedE6PairX_of_pos_of_ne_fixed [CharP K 2] (σ : K →+* K)
    {δ : Fin TwistTag.E6.tag.rank → ℤ} (hδ : IsRoot TwistTag.E6.tag δ)
    (hpos : 0 < height δ) (hρ : permLattice TwistTag.E6.perm δ ≠ δ) :
    orderOf (twistedE6PairX σ δ 1) = 2 := by
  have hsq := twistedE6PairX_sq (K := K) σ hδ
  have hne := twistedE6PairX_ne_one_of_pos_of_ne_fixed (K := K) σ hδ hpos hρ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime hsq hne

private theorem classV_s_sq [CharP K 2] {C0 : Subgroup (ModGL TwistTag.E6.tag K)} {s : C0}
    (hs : (s : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K twistedE6ClassRootB 1) :
    s * s = 1 := by
  rw [← sq]
  apply Subtype.ext
  change (s : ModGL TwistTag.E6.tag K) * (s : ModGL TwistTag.E6.tag K) = 1
  rw [hs, ← pow_two]
  exact pinnedX_one_sq_of_charTwo twistedE6ClassRootB

private theorem classV_sm_sq [CharP K 2] {C0 : Subgroup (ModGL TwistTag.E6.tag K)} {sm : C0}
    (hsm : (sm : ModGL TwistTag.E6.tag K) =
      pinnedX TwistTag.E6.tag K (-twistedE6ClassRootB) 1) :
    sm * sm = 1 := by
  rw [← sq]
  apply Subtype.ext
  change (sm : ModGL TwistTag.E6.tag K) * (sm : ModGL TwistTag.E6.tag K) = 1
  rw [hsm, ← pow_two]
  exact pinnedX_one_sq_of_charTwo (-twistedE6ClassRootB)

private theorem classV_pair_order [CharP K 2] (σ : K →+* K)
    {C0 : Subgroup (ModGL TwistTag.E6.tag K)} {s' : C0}
    (hs' : (s' : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K twistedE6ClassRootA 1 *
      pinnedX TwistTag.E6.tag K twistedE6ClassRootA' 1) :
    orderOf s' = 2 := by
  rw [← Subgroup.orderOf_coe s', hs']
  rw [show pinnedX TwistTag.E6.tag K twistedE6ClassRootA 1 *
      pinnedX TwistTag.E6.tag K twistedE6ClassRootA' 1 =
      twistedE6PairX σ twistedE6ClassRootA 1 from by
    rw [twistedE6PairX, map_one, permLattice_twistedE6ClassRootA]]
  exact orderOf_twistedE6PairX_of_pos_of_ne_fixed σ
    isRoot_twistedE6ClassRoots.2.2.1 (by decide) (by decide)

private theorem classV_pair_sq {C0 : Subgroup (ModGL TwistTag.E6.tag K)} {s' : C0}
    (h : orderOf s' = 2) : s' * s' = 1 := by
  rw [← sq, ← h]
  exact pow_orderOf_eq_one s'

private theorem classV_c_sq [CharP K 2] {C0 : Subgroup (ModGL TwistTag.E6.tag K)} {c : C0}
    {eps : Fin TwistTag.E6.tag.rank → ℤ}
    (hc : (c : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K eps 1 *
      pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm eps) 1)
    (hε : IsRoot TwistTag.E6.tag eps) : c * c = 1 := by
  rw [← sq]
  apply Subtype.ext
  change (c : ModGL TwistTag.E6.tag K) * (c : ModGL TwistTag.E6.tag K) = 1
  rw [hc, ← pow_two]
  rw [(commute_pinnedX_permLattice_twistedE6 (K := K) hε 1 1).mul_pow,
    pinnedX_one_sq_of_charTwo, pinnedX_one_sq_of_charTwo, one_mul]

private theorem classV_x_order [CharP K 2] (σ : K →+* K)
    {C0 : Subgroup (ModGL TwistTag.E6.tag K)} {x : C0}
    {eps : Fin TwistTag.E6.tag.rank → ℤ}
    (hx : (x : ModGL TwistTag.E6.tag K) =
      pinnedX TwistTag.E6.tag K (twistedE6ClassRootA + eps) 1 *
        pinnedX TwistTag.E6.tag K (twistedE6ClassRootA' +
          permLattice TwistTag.E6.perm eps) 1)
    (hα : IsRoot TwistTag.E6.tag (twistedE6ClassRootA + eps))
    (hpos : 0 < height (twistedE6ClassRootA + eps))
    (hρ : permLattice TwistTag.E6.perm (twistedE6ClassRootA + eps) ≠
      twistedE6ClassRootA + eps) :
    orderOf x = 2 := by
  rw [← Subgroup.orderOf_coe x, hx]
  rw [show pinnedX TwistTag.E6.tag K (twistedE6ClassRootA + eps) 1 *
      pinnedX TwistTag.E6.tag K (twistedE6ClassRootA' +
        permLattice TwistTag.E6.perm eps) 1 =
      twistedE6PairX σ (twistedE6ClassRootA + eps) 1 from by
    rw [twistedE6PairX, map_one, permLattice_add_twistedE6Classes,
      permLattice_twistedE6ClassRootA]]
  exact orderOf_twistedE6PairX_of_pos_of_ne_fixed σ hα hpos hρ

private theorem classV_x_sq {C0 : Subgroup (ModGL TwistTag.E6.tag K)} {x : C0}
    (h : orderOf x = 2) : x * x = 1 := by
  rw [← sq, ← h]
  exact pow_orderOf_eq_one x

section SectionClassVBetaConj
private theorem classV_beta_conj [CharP K 2] {C0 : Subgroup (ModGL TwistTag.E6.tag K)}
    {s sm : C0}
    (hs : (s : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K twistedE6ClassRootB 1)
    (hsm : (sm : ModGL TwistTag.E6.tag K) =
      pinnedX TwistTag.E6.tag K (-twistedE6ClassRootB) 1)
    (hs2 : s * s = 1) (hsm2 : sm * sm = 1) :
    orderOf (s * sm) = 3 ∧ (s * sm * s)⁻¹ * s * (s * sm * s) = sm := by
  have h3mod : orderOf (pinnedX TwistTag.E6.tag K twistedE6ClassRootB 1 *
      pinnedX TwistTag.E6.tag K (-twistedE6ClassRootB) 1) = 3 :=
    CFSG.SeitzReduction.EPilot.orderOf_pinnedX_mul_pinnedX_neg_one (τ := TwistTag.E6.tag)
      isRoot_twistedE6ClassRoots.2.2.2.2
  have h3sub : orderOf (s * sm) = 3 := by
    rw [← Subgroup.orderOf_coe (s * sm)]
    change orderOf ((s : ModGL TwistTag.E6.tag K) * (sm : ModGL TwistTag.E6.tag K)) = 3
    rw [hs, hsm]
    exact h3mod
  have h3 : (s * sm) ^ 3 = 1 := by
    rw [← h3sub]
    exact pow_orderOf_eq_one _
  have h2inv : (s * sm) ^ 2 = (s * sm)⁻¹ := by
    have h : (s * sm) ^ 2 * (s * sm) = 1 := by
      rw [← pow_succ]
      exact h3
    exact eq_inv_of_mul_eq_one_left h
  have hginv : (s * sm * s)⁻¹ = s * sm * s := by
    rw [mul_inv_rev, mul_inv_rev, inv_eq_of_mul_eq_one_right hs2,
      inv_eq_of_mul_eq_one_right hsm2]
    group
  refine ⟨h3sub, ?_⟩
  calc (s * sm * s)⁻¹ * s * (s * sm * s) = (s * sm * s) * s * (s * sm * s) := by rw [hginv]
    _ = s * sm * (s * s) * (s * sm * s) := by group
    _ = s * sm * (s * sm * s) := by rw [hs2, mul_one]
    _ = s * sm * s * sm * s := by group
    _ = (s * sm) ^ 2 * s := by rw [pow_two]; group
    _ = (s * sm)⁻¹ * s := by rw [h2inv]
    _ = sm * s * s := by rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hsm2,
      inv_eq_of_mul_eq_one_right hs2]
    _ = sm := by rw [mul_assoc, hs2, mul_one]

end SectionClassVBetaConj

section SectionClassVConjPairMod
private theorem classV_conj_pair_mod [CharP K 2] (σ : K →+* K)
    {eps : Fin TwistTag.E6.tag.rank → ℤ}
    (hs'2 : twistedE6PairX σ twistedE6ClassRootA 1 *
      twistedE6PairX σ twistedE6ClassRootA 1 = 1)
    (hc2 : twistedE6PairX σ eps 1 * twistedE6PairX σ eps 1 = 1)
    (hL1 : (commutatorElement (G := ModGL TwistTag.E6.tag K)).bracket
        (twistedE6PairX σ twistedE6ClassRootA 1) (twistedE6PairX σ eps 1) =
      twistedE6PairX σ (twistedE6ClassRootA + eps) 1) :
    (twistedE6PairX σ eps 1)⁻¹ * twistedE6PairX σ twistedE6ClassRootA 1 *
        twistedE6PairX σ eps 1 =
      twistedE6PairX σ twistedE6ClassRootA 1 *
        twistedE6PairX σ (twistedE6ClassRootA + eps) 1 := by
  have hs'inv : (twistedE6PairX σ twistedE6ClassRootA 1)⁻¹ =
      twistedE6PairX σ twistedE6ClassRootA 1 :=
    inv_eq_of_mul_eq_one_right hs'2
  have hcinv : (twistedE6PairX σ eps 1)⁻¹ = twistedE6PairX σ eps 1 :=
    inv_eq_of_mul_eq_one_right hc2
  calc (twistedE6PairX σ eps 1)⁻¹ * twistedE6PairX σ twistedE6ClassRootA 1 *
        twistedE6PairX σ eps 1
      = twistedE6PairX σ eps 1 * twistedE6PairX σ twistedE6ClassRootA 1 *
          twistedE6PairX σ eps 1 := by rw [hcinv]
    _ = (twistedE6PairX σ twistedE6ClassRootA 1 *
          twistedE6PairX σ twistedE6ClassRootA 1) *
          (twistedE6PairX σ eps 1 * twistedE6PairX σ twistedE6ClassRootA 1 *
            twistedE6PairX σ eps 1) := by rw [hs'2, one_mul]
    _ = twistedE6PairX σ twistedE6ClassRootA 1 *
          (twistedE6PairX σ twistedE6ClassRootA 1 * twistedE6PairX σ eps 1 *
            twistedE6PairX σ twistedE6ClassRootA 1 * twistedE6PairX σ eps 1) := by
        group
    _ = twistedE6PairX σ twistedE6ClassRootA 1 *
          (twistedE6PairX σ twistedE6ClassRootA 1 * twistedE6PairX σ eps 1 *
            (twistedE6PairX σ twistedE6ClassRootA 1)⁻¹ *
              (twistedE6PairX σ eps 1)⁻¹) := by rw [hs'inv, hcinv]
    _ = twistedE6PairX σ twistedE6ClassRootA 1 *
          (commutatorElement (G := ModGL TwistTag.E6.tag K)).bracket
            (twistedE6PairX σ twistedE6ClassRootA 1) (twistedE6PairX σ eps 1) := rfl
    _ = twistedE6PairX σ twistedE6ClassRootA 1 *
          twistedE6PairX σ (twistedE6ClassRootA + eps) 1 := by rw [hL1]
end SectionClassVConjPairMod

private theorem classV_pairX_eq_products [CharP K 2] (σ : K →+* K)
    {eps : Fin TwistTag.E6.tag.rank → ℤ} :
    twistedE6PairX σ twistedE6ClassRootA 1 =
        pinnedX TwistTag.E6.tag K twistedE6ClassRootA 1 *
          pinnedX TwistTag.E6.tag K twistedE6ClassRootA' 1 ∧
      twistedE6PairX σ eps 1 = pinnedX TwistTag.E6.tag K eps 1 *
          pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm eps) 1 ∧
      twistedE6PairX σ (twistedE6ClassRootA + eps) 1 =
        pinnedX TwistTag.E6.tag K (twistedE6ClassRootA + eps) 1 *
          pinnedX TwistTag.E6.tag K (twistedE6ClassRootA' +
            permLattice TwistTag.E6.perm eps) 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [twistedE6PairX, map_one, permLattice_twistedE6ClassRootA]
  · rw [twistedE6PairX, map_one]
  · rw [twistedE6PairX, map_one, permLattice_add_twistedE6Classes,
      permLattice_twistedE6ClassRootA]

section SectionClassVConjPairModProducts
private theorem classV_conj_pair_mod_products [CharP K 2] (σ : K →+* K)
    {eps : Fin TwistTag.E6.tag.rank → ℤ}
    (hs'2 : (pinnedX TwistTag.E6.tag K twistedE6ClassRootA 1 *
        pinnedX TwistTag.E6.tag K twistedE6ClassRootA' 1) *
      (pinnedX TwistTag.E6.tag K twistedE6ClassRootA 1 *
        pinnedX TwistTag.E6.tag K twistedE6ClassRootA' 1) = 1)
    (hc2 : (pinnedX TwistTag.E6.tag K eps 1 *
        pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm eps) 1) *
      (pinnedX TwistTag.E6.tag K eps 1 *
        pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm eps) 1) = 1)
    (hL1 : (commutatorElement (G := ModGL TwistTag.E6.tag K)).bracket
        (twistedE6PairX σ twistedE6ClassRootA 1) (twistedE6PairX σ eps 1) =
      twistedE6PairX σ (twistedE6ClassRootA + eps) 1) :
    (pinnedX TwistTag.E6.tag K eps 1 *
        pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm eps) 1)⁻¹ *
      (pinnedX TwistTag.E6.tag K twistedE6ClassRootA 1 *
        pinnedX TwistTag.E6.tag K twistedE6ClassRootA' 1) *
      (pinnedX TwistTag.E6.tag K eps 1 *
        pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm eps) 1) =
      (pinnedX TwistTag.E6.tag K twistedE6ClassRootA 1 *
        pinnedX TwistTag.E6.tag K twistedE6ClassRootA' 1) *
      (pinnedX TwistTag.E6.tag K (twistedE6ClassRootA + eps) 1 *
        pinnedX TwistTag.E6.tag K (twistedE6ClassRootA' +
          permLattice TwistTag.E6.perm eps) 1) := by
  obtain ⟨hpairA, hpairE, hpairX⟩ := classV_pairX_eq_products (K := K) σ (eps := eps)
  have hs'2' : twistedE6PairX σ twistedE6ClassRootA 1 *
      twistedE6PairX σ twistedE6ClassRootA 1 = 1 := by
    rw [hpairA]
    exact hs'2
  have hc2' : twistedE6PairX σ eps 1 * twistedE6PairX σ eps 1 = 1 := by
    rw [hpairE]
    exact hc2
  rw [← hpairA, ← hpairE, ← hpairX]
  exact classV_conj_pair_mod (K := K) σ hs'2' hc2' hL1
end SectionClassVConjPairModProducts

section SectionClassVConjPair
private theorem classV_conj_pair [CharP K 2] {C0 : Subgroup (ModGL TwistTag.E6.tag K)}
    {s' c x : C0} {eps : Fin TwistTag.E6.tag.rank → ℤ}
    (hs' : (s' : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K twistedE6ClassRootA 1 *
      pinnedX TwistTag.E6.tag K twistedE6ClassRootA' 1)
    (hc : (c : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K eps 1 *
      pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm eps) 1)
    (hx : (x : ModGL TwistTag.E6.tag K) =
      pinnedX TwistTag.E6.tag K (twistedE6ClassRootA + eps) 1 *
        pinnedX TwistTag.E6.tag K (twistedE6ClassRootA' +
          permLattice TwistTag.E6.perm eps) 1)
    (h : (pinnedX TwistTag.E6.tag K eps 1 *
        pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm eps) 1)⁻¹ *
      (pinnedX TwistTag.E6.tag K twistedE6ClassRootA 1 *
        pinnedX TwistTag.E6.tag K twistedE6ClassRootA' 1) *
      (pinnedX TwistTag.E6.tag K eps 1 *
        pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm eps) 1) =
      (pinnedX TwistTag.E6.tag K twistedE6ClassRootA 1 *
        pinnedX TwistTag.E6.tag K twistedE6ClassRootA' 1) *
      (pinnedX TwistTag.E6.tag K (twistedE6ClassRootA + eps) 1 *
        pinnedX TwistTag.E6.tag K (twistedE6ClassRootA' +
          permLattice TwistTag.E6.perm eps) 1)) :
    c⁻¹ * s' * c = s' * x := by
  apply Subtype.ext
  change (c : ModGL TwistTag.E6.tag K)⁻¹ * (s' : ModGL TwistTag.E6.tag K) *
      (c : ModGL TwistTag.E6.tag K) =
    (s' : ModGL TwistTag.E6.tag K) * (x : ModGL TwistTag.E6.tag K)
  rw [hs', hc, hx]
  exact h
end SectionClassVConjPair

private theorem commute_of_coe_eq [CharP K 2] {C0 : Subgroup (ModGL TwistTag.E6.tag K)}
    {a b : C0} {a₀ b₀ : ModGL TwistTag.E6.tag K}
    (ha : (a : ModGL TwistTag.E6.tag K) = a₀) (hb : (b : ModGL TwistTag.E6.tag K) = b₀)
    (h : Commute a₀ b₀) : Commute a b := by
  change a * b = b * a
  apply Subtype.ext
  change (a : ModGL TwistTag.E6.tag K) * (b : ModGL TwistTag.E6.tag K) =
    (b : ModGL TwistTag.E6.tag K) * (a : ModGL TwistTag.E6.tag K)
  rw [ha, hb]
  exact h.eq

private theorem classV_le_centralizer_pair {C0 : Subgroup (ModGL TwistTag.E6.tag K)}
    {s sm s' : C0} (hss' : Commute s s') (hsms' : Commute sm s') :
    Subgroup.closure ({s, sm} : Set C0) ≤ Subgroup.centralizer ({s'} : Set C0) := by
  rw [Subgroup.closure_le]
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl
  · exact Subgroup.mem_centralizer_singleton_iff.2 hss'.eq
  · exact Subgroup.mem_centralizer_singleton_iff.2 hsms'.eq

private theorem classV_le_centralizer_c {C0 : Subgroup (ModGL TwistTag.E6.tag K)}
    {s sm c : C0} (hcs : Commute c s) (hcsm : Commute c sm) :
    Subgroup.closure ({s, sm} : Set C0) ≤ Subgroup.centralizer ({c} : Set C0) := by
  rw [Subgroup.closure_le]
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl
  · exact Subgroup.mem_centralizer_singleton_iff.2 hcs.eq.symm
  · exact Subgroup.mem_centralizer_singleton_iff.2 hcsm.eq.symm

private theorem classV_exists_beta [CharP K 2] {σ : K →+* K} :
    ∃ s sm : graphFixedRootGroup TwistTag.E6 K σ,
      (s : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K twistedE6ClassRootB 1 ∧
      (sm : ModGL TwistTag.E6.tag K) =
        pinnedX TwistTag.E6.tag K (-twistedE6ClassRootB) 1 ∧
      s * s = 1 ∧ sm * sm = 1 := by
  have hB : IsRoot TwistTag.E6.tag twistedE6ClassRootB :=
    isRoot_twistedE6ClassRoots.2.2.2.2
  have hBneg : IsRoot TwistTag.E6.tag (-twistedE6ClassRootB) :=
    CFSG.LieType.Chevalley.IsRoot.neg hB
  have hBρneg : permLattice TwistTag.E6.perm (-twistedE6ClassRootB) = -twistedE6ClassRootB := by
    rw [show permLattice TwistTag.E6.perm (-twistedE6ClassRootB) =
        -permLattice TwistTag.E6.perm twistedE6ClassRootB from rfl,
      permLattice_twistedE6ClassRootB]
  refine ⟨⟨pinnedX TwistTag.E6.tag K twistedE6ClassRootB 1,
      pinnedX_mem_graphFixedRootGroup_of_fixed σ hB permLattice_twistedE6ClassRootB
        (map_one σ)⟩,
    ⟨pinnedX TwistTag.E6.tag K (-twistedE6ClassRootB) 1,
      pinnedX_mem_graphFixedRootGroup_of_fixed σ hBneg hBρneg (map_one σ)⟩, rfl, rfl, ?_, ?_⟩
  · exact classV_s_sq rfl
  · exact classV_sm_sq rfl

private theorem classV_exists_pair [CharP K 2] {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) :
    ∃ s' : graphFixedRootGroup TwistTag.E6 K σ,
      (s' : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K twistedE6ClassRootA 1 *
        pinnedX TwistTag.E6.tag K twistedE6ClassRootA' 1 ∧
      orderOf s' = 2 ∧ s' * s' = 1 := by
  have hA : IsRoot TwistTag.E6.tag twistedE6ClassRootA :=
    isRoot_twistedE6ClassRoots.2.2.1
  have hmem : pinnedX TwistTag.E6.tag K twistedE6ClassRootA 1 *
      pinnedX TwistTag.E6.tag K twistedE6ClassRootA' 1 ∈
        graphFixedRootGroup TwistTag.E6 K σ := by
    have h := twistedE6PairX_mem_graphFixedRootGroup hσσ hA 1
    rwa [twistedE6PairX, map_one, permLattice_twistedE6ClassRootA] at h
  refine ⟨⟨pinnedX TwistTag.E6.tag K twistedE6ClassRootA 1 *
      pinnedX TwistTag.E6.tag K twistedE6ClassRootA' 1, hmem⟩, rfl, ?_, ?_⟩
  · exact classV_pair_order σ rfl
  · exact classV_pair_sq (classV_pair_order σ rfl)

private theorem classV_exists_c [CharP K 2] {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c)
    {eps : Fin TwistTag.E6.tag.rank → ℤ} (hε : IsRoot TwistTag.E6.tag eps) :
    ∃ c : graphFixedRootGroup TwistTag.E6 K σ,
      (c : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K eps 1 *
        pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm eps) 1 ∧
      c * c = 1 := by
  have hmem : pinnedX TwistTag.E6.tag K eps 1 *
      pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm eps) 1 ∈
        graphFixedRootGroup TwistTag.E6 K σ := by
    have h := twistedE6PairX_mem_graphFixedRootGroup hσσ hε 1
    rwa [twistedE6PairX, map_one] at h
  refine ⟨⟨pinnedX TwistTag.E6.tag K eps 1 *
      pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm eps) 1, hmem⟩, rfl, ?_⟩
  exact classV_c_sq rfl hε

private theorem classV_exists_x [CharP K 2] {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c)
    {eps : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : IsRoot TwistTag.E6.tag (twistedE6ClassRootA + eps))
    (hpos : 0 < height (twistedE6ClassRootA + eps))
    (hρ : permLattice TwistTag.E6.perm (twistedE6ClassRootA + eps) ≠
      twistedE6ClassRootA + eps) :
    ∃ x : graphFixedRootGroup TwistTag.E6 K σ,
      (x : ModGL TwistTag.E6.tag K) =
        pinnedX TwistTag.E6.tag K (twistedE6ClassRootA + eps) 1 *
          pinnedX TwistTag.E6.tag K (twistedE6ClassRootA' +
            permLattice TwistTag.E6.perm eps) 1 ∧
      orderOf x = 2 ∧ x * x = 1 := by
  have hmem : pinnedX TwistTag.E6.tag K (twistedE6ClassRootA + eps) 1 *
      pinnedX TwistTag.E6.tag K (twistedE6ClassRootA' +
        permLattice TwistTag.E6.perm eps) 1 ∈ graphFixedRootGroup TwistTag.E6 K σ := by
    have h := twistedE6PairX_mem_graphFixedRootGroup hσσ hα 1
    rwa [twistedE6PairX, map_one, permLattice_add_twistedE6Classes,
      permLattice_twistedE6ClassRootA] at h
  refine ⟨⟨pinnedX TwistTag.E6.tag K (twistedE6ClassRootA + eps) 1 *
      pinnedX TwistTag.E6.tag K (twistedE6ClassRootA' +
        permLattice TwistTag.E6.perm eps) 1, hmem⟩, rfl, ?_, ?_⟩
  · exact classV_x_order σ rfl hα hpos hρ
  · exact classV_x_sq (classV_x_order σ rfl hα hpos hρ)

private theorem classV_commute_facts [CharP K 2]
    {C0 : Subgroup (ModGL TwistTag.E6.tag K)} {s sm s' c : C0}
    (hss : (s : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K twistedE6ClassRootB 1)
    (hsms : (sm : ModGL TwistTag.E6.tag K) =
      pinnedX TwistTag.E6.tag K (-twistedE6ClassRootB) 1)
    (hs's : (s' : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K twistedE6ClassRootA 1 *
      pinnedX TwistTag.E6.tag K twistedE6ClassRootA' 1)
    (hcs : (c : ModGL TwistTag.E6.tag K) =
      pinnedX TwistTag.E6.tag K (fun i : Fin TwistTag.E6.tag.rank =>
        (![-1, 0, -1, -1, 0, 0] : Fin 6 → ℤ) i) 1 *
      pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm
        (fun i : Fin TwistTag.E6.tag.rank => (![-1, 0, -1, -1, 0, 0] : Fin 6 → ℤ) i)) 1) :
    Commute s s' ∧ Commute c s ∧ Commute sm s' ∧ Commute c sm := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact commute_of_coe_eq hss hs's (commute_classV_pair_beta (K := K)).symm
  · exact commute_of_coe_eq hcs hss (commute_classV_c_beta (K := K))
  · exact commute_of_coe_eq hsms hs's (commute_classV_pair_neg_beta (K := K)).symm
  · exact commute_of_coe_eq hcs hsms (commute_classV_c_neg_beta (K := K))

section SectionClassVConjPairHmod
private theorem classV_conj_pair_hmod [CharP K 2] (σ : K →+* K)
    {C0 : Subgroup (ModGL TwistTag.E6.tag K)} {s' c : C0}
    {eps : Fin TwistTag.E6.tag.rank → ℤ}
    (hs's : (s' : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K twistedE6ClassRootA 1 *
      pinnedX TwistTag.E6.tag K twistedE6ClassRootA' 1)
    (hcs : (c : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K eps 1 *
      pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm eps) 1)
    (hs'2mul : s' * s' = 1) (hc2 : c * c = 1)
    (hL1 : (commutatorElement (G := ModGL TwistTag.E6.tag K)).bracket
        (twistedE6PairX σ twistedE6ClassRootA 1) (twistedE6PairX σ eps 1) =
      twistedE6PairX σ (twistedE6ClassRootA + eps) 1) :
    (pinnedX TwistTag.E6.tag K eps 1 *
        pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm eps) 1)⁻¹ *
      (pinnedX TwistTag.E6.tag K twistedE6ClassRootA 1 *
        pinnedX TwistTag.E6.tag K twistedE6ClassRootA' 1) *
      (pinnedX TwistTag.E6.tag K eps 1 *
        pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm eps) 1) =
      (pinnedX TwistTag.E6.tag K twistedE6ClassRootA 1 *
        pinnedX TwistTag.E6.tag K twistedE6ClassRootA' 1) *
      (pinnedX TwistTag.E6.tag K (twistedE6ClassRootA + eps) 1 *
        pinnedX TwistTag.E6.tag K (twistedE6ClassRootA' +
          permLattice TwistTag.E6.perm eps) 1) := by
  have hs'2prod : (pinnedX TwistTag.E6.tag K twistedE6ClassRootA 1 *
      pinnedX TwistTag.E6.tag K twistedE6ClassRootA' 1) *
      (pinnedX TwistTag.E6.tag K twistedE6ClassRootA 1 *
        pinnedX TwistTag.E6.tag K twistedE6ClassRootA' 1) = 1 := by
    simpa [hs's] using congrArg Subtype.val hs'2mul
  have hc2prod : (pinnedX TwistTag.E6.tag K eps 1 *
      pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm eps) 1) *
      (pinnedX TwistTag.E6.tag K eps 1 *
        pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm eps) 1) = 1 := by
    simpa [hcs] using congrArg Subtype.val hc2
  exact classV_conj_pair_mod_products (K := K) σ hs'2prod hc2prod hL1
end SectionClassVConjPairHmod

private theorem classV_hs'x [CharP K 2]
    {C0 : Subgroup (ModGL TwistTag.E6.tag K)} {s' x : C0}
    {eps : Fin TwistTag.E6.tag.rank → ℤ}
    (hs's : (s' : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K twistedE6ClassRootA 1 *
      pinnedX TwistTag.E6.tag K twistedE6ClassRootA' 1)
    (hxs : (x : ModGL TwistTag.E6.tag K) =
      pinnedX TwistTag.E6.tag K (twistedE6ClassRootA + eps) 1 *
        pinnedX TwistTag.E6.tag K (twistedE6ClassRootA' +
          permLattice TwistTag.E6.perm eps) 1)
    (hcorr : Commute (pinnedX TwistTag.E6.tag K twistedE6ClassRootA 1 *
        pinnedX TwistTag.E6.tag K twistedE6ClassRootA' 1)
      (pinnedX TwistTag.E6.tag K (twistedE6ClassRootA + eps) 1 *
        pinnedX TwistTag.E6.tag K (twistedE6ClassRootA' +
          permLattice TwistTag.E6.perm eps) 1)) :
    Commute s' x := by
  change s' * x = x * s'
  apply Subtype.ext
  change (s' : ModGL TwistTag.E6.tag K) * (x : ModGL TwistTag.E6.tag K) =
    (x : ModGL TwistTag.E6.tag K) * (s' : ModGL TwistTag.E6.tag K)
  rw [hs's, hxs]
  exact hcorr.eq

private theorem classV_v_eq [CharP K 2] {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c)
    {s s' : graphFixedRootGroup TwistTag.E6 K σ}
    (hss : (s : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K twistedE6ClassRootB 1)
    (hs's : (s' : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K twistedE6ClassRootA 1 *
      pinnedX TwistTag.E6.tag K twistedE6ClassRootA' 1)
    (hcomm : Commute s s') :
    s * s' = (⟨twistedE6ClassV K,
      twistedE6ClassV_mem_graphFixedRootGroup hσσ⟩ :
        graphFixedRootGroup TwistTag.E6 K σ) := by
  apply Subtype.ext
  change (s : ModGL TwistTag.E6.tag K) * (s' : ModGL TwistTag.E6.tag K) = twistedE6ClassV K
  rw [hss, hs's, twistedE6ClassV]
  have h := congrArg Subtype.val hcomm.eq
  change (s : ModGL TwistTag.E6.tag K) * (s' : ModGL TwistTag.E6.tag K) =
    (s' : ModGL TwistTag.E6.tag K) * (s : ModGL TwistTag.E6.tag K) at h
  rw [hss, hs's] at h
  exact h

private theorem classV_J_data {C0 : Subgroup (ModGL TwistTag.E6.tag K)}
    {s sm s' c : C0}
    (hJcent' : Subgroup.closure ({s, sm} : Set C0) ≤
      Subgroup.centralizer ({s'} : Set C0))
    (hJcentc : Subgroup.closure ({s, sm} : Set C0) ≤
      Subgroup.centralizer ({c} : Set C0)) :
    s ∈ Subgroup.closure ({s, sm} : Set C0) ∧
      sm ∈ Subgroup.closure ({s, sm} : Set C0) ∧
      s * sm * s ∈ Subgroup.closure ({s, sm} : Set C0) ∧
      (∀ j ∈ Subgroup.closure ({s, sm} : Set C0), s' * j = j * s') ∧
      (∀ j ∈ Subgroup.closure ({s, sm} : Set C0), c * j = j * c) := by
  have hsJ : s ∈ Subgroup.closure ({s, sm} : Set C0) := Subgroup.subset_closure (by simp)
  have hsmJ : sm ∈ Subgroup.closure ({s, sm} : Set C0) := Subgroup.subset_closure (by simp)
  refine ⟨hsJ, hsmJ, ?_, ?_, ?_⟩
  · exact (Subgroup.closure ({s, sm} : Set C0)).mul_mem
      ((Subgroup.closure ({s, sm} : Set C0)).mul_mem hsJ hsmJ) hsJ
  · intro j hj
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hJcent' hj)).symm
  · intro j hj
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hJcentc hj)).symm

private theorem classV_mul_conj_six [CharP K 2]
    {C0 : Subgroup (ModGL TwistTag.E6.tag K)} {s sm s' c g v : C0}
    (hs'2 : orderOf s' = 2) (h3 : orderOf (s * (g⁻¹ * s * g)) = 3)
    (hne : c⁻¹ * s' * c ≠ s')
    (hcomm : s' * (c⁻¹ * s' * c) = c⁻¹ * s' * c * s')
    (hsJ : s ∈ Subgroup.closure ({s, sm} : Set C0))
    (hgJ : g ∈ Subgroup.closure ({s, sm} : Set C0))
    (hs'J : ∀ j ∈ Subgroup.closure ({s, sm} : Set C0), s' * j = j * s')
    (hcJ : ∀ j ∈ Subgroup.closure ({s, sm} : Set C0), c * j = j * c)
    (hv : v = s * s') :
    ∃ h : C0, orderOf (v * (h⁻¹ * v * h)) = 6 := by
  have hmain := orderOf_mul_conj_eq_six (J := Subgroup.closure ({s, sm} : Set C0))
    (s := s) (s' := s') (g := g) (c := c) hsJ hgJ hs'J hcJ hs'2 h3 hne hcomm
  refine ⟨g * c, ?_⟩
  rw [hv]
  exact hmain

private theorem classV_correction_ne_commute {C0 : Subgroup (ModGL TwistTag.E6.tag K)}
    {s' c x : C0} (hs'2mul : s' * s' = 1) (hx2 : orderOf x = 2)
    (hs'x : Commute s' x) (hconj : c⁻¹ * s' * c = s' * x) :
    c⁻¹ * s' * c ≠ s' ∧ s' * (c⁻¹ * s' * c) = (c⁻¹ * s' * c) * s' := by
  constructor
  · rw [hconj]
    intro h
    have hx1 : x = 1 := by
      calc x = s' * (s' * x) := by rw [← mul_assoc, hs'2mul, one_mul]
        _ = s' * s' := by rw [h]
        _ = 1 := hs'2mul
    rw [hx1, orderOf_one] at hx2
    omega
  · rw [hconj]
    calc s' * (s' * x) = x := by rw [← mul_assoc, hs'2mul, one_mul]
      _ = s' * x * s' := by rw [hs'x.eq, mul_assoc, hs'2mul, mul_one]

theorem exists_orderOf_classV_mul_conj_eq_six [CharP K 2] {σ : K →+* K}
    (hσσ : ∀ c, σ (σ c) = c) :
    ∃ g : graphFixedRootGroup TwistTag.E6 K σ,
      orderOf ((⟨twistedE6ClassV K, twistedE6ClassV_mem_graphFixedRootGroup hσσ⟩ :
          graphFixedRootGroup TwistTag.E6 K σ) *
        (g⁻¹ * ⟨twistedE6ClassV K, twistedE6ClassV_mem_graphFixedRootGroup hσσ⟩ * g)) = 6 := by
  let eps : Fin TwistTag.E6.tag.rank → ℤ :=
    fun i : Fin TwistTag.E6.tag.rank => (![-1, 0, -1, -1, 0, 0] : Fin 6 → ℤ) i
  have hε : IsRoot TwistTag.E6.tag eps := by
    rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel
  have hα : IsRoot TwistTag.E6.tag (twistedE6ClassRootA + eps) := by
    rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel
  obtain ⟨s, sm, hss, hsms, hs2, hsm2⟩ := classV_exists_beta (σ := σ)
  obtain ⟨s', hs's, hs'2, hs'2mul⟩ := classV_exists_pair hσσ
  obtain ⟨c, hcs, hc2⟩ := classV_exists_c hσσ hε
  obtain ⟨x, hxs, hx2, _⟩ := classV_exists_x hσσ hα (by decide) (by decide)
  obtain ⟨hss', hcs', hsms', hcsm⟩ := classV_commute_facts hss hsms hs's hcs
  have hJcent' := classV_le_centralizer_pair hss' hsms'
  have hJcentc := classV_le_centralizer_c hcs' hcsm
  have hmod := classV_conj_pair_hmod σ hs's hcs hs'2mul hc2
    (commutator_classV_pair_eq (K := K) σ)
  have hconj := classV_conj_pair hs's hcs hxs hmod
  have hs'x := classV_hs'x hs's hxs (commute_classV_pair_correction (K := K))
  obtain ⟨hne, hcomm⟩ := classV_correction_ne_commute hs'2mul hx2 hs'x hconj
  obtain ⟨h3sub, hgconj⟩ := classV_beta_conj hss hsms hs2 hsm2
  obtain ⟨hsJ, hsmJ, hgJ, hs'J, hcJ⟩ := classV_J_data hJcent' hJcentc
  let g : graphFixedRootGroup TwistTag.E6 K σ := s * sm * s
  have h3 : orderOf (s * (g⁻¹ * s * g)) = 3 := by
    rw [show g = s * sm * s from rfl, hgconj]
    exact h3sub
  have hv : (⟨twistedE6ClassV K, twistedE6ClassV_mem_graphFixedRootGroup hσσ⟩ :
      graphFixedRootGroup TwistTag.E6 K σ) = s * s' :=
    (classV_v_eq hσσ hss hs's hss').symm
  exact classV_mul_conj_six hs'2 h3 hne hcomm hsJ hgJ hs'J hcJ hv

private instance twistedE6KLFusionNeZeroFolded : NeZero TwistTag.E6.foldedTag.rank :=
  ⟨by decide⟩
private instance twistedE6KLFusionNeZeroTag : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

section
private lemma twistedE6RelWeyl_conj_classU_eq {K : Type} [Field K] [CharP K 2] :
    twistedE6RelWeyl K [0, 1, 2, 1, 0] * twistedE6ClassU K *
        (twistedE6RelWeyl K [0, 1, 2, 1, 0])⁻¹ =
      pinnedX TwistTag.E6.tag K
          (permLattice TwistTag.E6.perm ![0, 1, 1, 1, 0, 0]) 1 *
        pinnedX TwistTag.E6.tag K ![0, 1, 1, 1, 0, 0] 1 := by
  set eps : Fin TwistTag.E6.tag.rank → ℤ := ![0, 1, 1, 1, 0, 0] with heps
  have hγ : IsRoot TwistTag.E6.tag twistedE6ClassRootU := isRoot_twistedE6ClassRoots.1
  have hγ' : IsRoot TwistTag.E6.tag twistedE6ClassRootU' := isRoot_twistedE6ClassRoots.2.1
  calc
    twistedE6RelWeyl K [0, 1, 2, 1, 0] * twistedE6ClassU K *
        (twistedE6RelWeyl K [0, 1, 2, 1, 0])⁻¹
        = (twistedE6RelWeyl K [0, 1, 2, 1, 0] * pinnedX TwistTag.E6.tag K
              twistedE6ClassRootU 1 *
            (twistedE6RelWeyl K [0, 1, 2, 1, 0])⁻¹) *
          (twistedE6RelWeyl K [0, 1, 2, 1, 0] * pinnedX TwistTag.E6.tag K
              twistedE6ClassRootU' 1 *
            (twistedE6RelWeyl K [0, 1, 2, 1, 0])⁻¹) := by
          rw [twistedE6ClassU]; group
    _ = pinnedX TwistTag.E6.tag K
          (twistedE6RelAct [0, 1, 2, 1, 0] twistedE6ClassRootU) 1 *
        pinnedX TwistTag.E6.tag K
          (twistedE6RelAct [0, 1, 2, 1, 0] twistedE6ClassRootU') 1 := by
          rw [twistedE6RelWeyl_conj_pinnedX _ hγ 1,
            twistedE6RelWeyl_conj_pinnedX _ hγ' 1]
    _ = pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm eps) 1 *
        pinnedX TwistTag.E6.tag K eps 1 := by
          rw [show twistedE6RelAct [0, 1, 2, 1, 0] twistedE6ClassRootU =
                permLattice TwistTag.E6.perm eps by
                ext j; fin_cases j <;> decide,
              show twistedE6RelAct [0, 1, 2, 1, 0] twistedE6ClassRootU' = eps by
                ext j; fin_cases j <;> decide]

end
section
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley in
private lemma rootChar_twistedE6TorusTuple_classU {K : Type} [Field K] [CharP K 2]
    (σ : K →+* K) (μ : Kˣ) (hσσ : ∀ c, σ (σ c) = c) :
    (rootChar (twistedE6TorusTuple σ 2 μ) ![0, 1, 1, 1, 0, 0] : K) =
        (μ : K) * (σ (μ : K))⁻¹ ∧
      (rootChar (twistedE6TorusTuple σ 2 μ)
        (permLattice TwistTag.E6.perm ![0, 1, 1, 1, 0, 0]) : K) =
        σ ((μ : K) * (σ (μ : K))⁻¹) := by
  set eps : Fin TwistTag.E6.tag.rank → ℤ := ![0, 1, 1, 1, 0, 0] with heps
  set lam : K := (μ : K) * (σ (μ : K))⁻¹ with hlam
  constructor
  · rw [rootChar_twistedE6TorusTuple]
    have h1 : coPair TwistTag.E6.tag 2 eps = 1 := by decide +kernel
    have h2 : coPair TwistTag.E6.tag (TwistTag.E6.perm 2) eps = -1 := by decide +kernel
    rw [h1, h2, zpow_one, zpow_neg_one]
    simp [Units.val_mul, Units.map, hlam]
  · rw [rootChar_twistedE6TorusTuple]
    have h1 : coPair TwistTag.E6.tag 2 (permLattice TwistTag.E6.perm eps) = -1 := by
      decide +kernel
    have h2 : coPair TwistTag.E6.tag (TwistTag.E6.perm 2)
        (permLattice TwistTag.E6.perm eps) = 1 := by decide +kernel
    rw [h1, h2, zpow_neg_one, zpow_one]
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map]
    rw [map_mul, map_inv₀, hσσ, mul_comm]
    rfl

end
section
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley in
private lemma rootDiagUnit_conj_classU_eq_twistedE6PairX {K : Type} [Field K] [CharP K 2]
    (σ : K →+* K) (μ : Kˣ) (lam : K) (eps : Fin TwistTag.E6.tag.rank → ℤ)
    (hε : IsRoot TwistTag.E6.tag eps)
    (hρε : IsRoot TwistTag.E6.tag (permLattice TwistTag.E6.perm eps))
    (hχeps : (rootChar (twistedE6TorusTuple σ 2 μ) eps : K) = lam)
    (hχρε : (rootChar (twistedE6TorusTuple σ 2 μ)
        (permLattice TwistTag.E6.perm eps) : K) = σ lam) :
    rootDiagUnit TwistTag.E6.tag (twistedE6TorusTuple σ 2 μ) *
      (pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm eps) 1 *
        pinnedX TwistTag.E6.tag K eps 1) *
      (rootDiagUnit TwistTag.E6.tag (twistedE6TorusTuple σ 2 μ))⁻¹ =
      twistedE6PairX σ eps lam := by
  calc
    rootDiagUnit TwistTag.E6.tag (twistedE6TorusTuple σ 2 μ) *
      (pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm eps) 1 *
        pinnedX TwistTag.E6.tag K eps 1) *
      (rootDiagUnit TwistTag.E6.tag (twistedE6TorusTuple σ 2 μ))⁻¹
        = (rootDiagUnit TwistTag.E6.tag (twistedE6TorusTuple σ 2 μ) *
              pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm eps) 1 *
              (rootDiagUnit TwistTag.E6.tag (twistedE6TorusTuple σ 2 μ))⁻¹) *
            (rootDiagUnit TwistTag.E6.tag (twistedE6TorusTuple σ 2 μ) *
              pinnedX TwistTag.E6.tag K eps 1 *
              (rootDiagUnit TwistTag.E6.tag (twistedE6TorusTuple σ 2 μ))⁻¹) := by
          group
    _ = pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm eps) (σ lam) *
        pinnedX TwistTag.E6.tag K eps lam := by
          rw [rootDiagUnit_conj_pinnedX (twistedE6TorusTuple σ 2 μ) hρε 1,
            rootDiagUnit_conj_pinnedX (twistedE6TorusTuple σ 2 μ) hε 1]
          rw [hχρε, hχeps]; simp
    _ = pinnedX TwistTag.E6.tag K eps lam *
        pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm eps) (σ lam) :=
          (commute_pinnedX_permLattice_twistedE6 (δ := eps) hε lam (σ lam)).eq.symm
    _ = twistedE6PairX σ eps lam := by
          rw [twistedE6PairX]

end
section
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley in
private lemma rootDiagUnit_conj_classU_eq_pairX {K : Type} [Field K] [CharP K 2]
    (σ : K →+* K) (μ : Kˣ) (hσσ : ∀ c, σ (σ c) = c) :
    rootDiagUnit TwistTag.E6.tag (twistedE6TorusTuple σ 2 μ) *
      (pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm ![0, 1, 1, 1, 0, 0]) 1 *
        pinnedX TwistTag.E6.tag K ![0, 1, 1, 1, 0, 0] 1) *
      (rootDiagUnit TwistTag.E6.tag (twistedE6TorusTuple σ 2 μ))⁻¹ =
      twistedE6PairX σ ![0, 1, 1, 1, 0, 0] ((μ : K) * (σ (μ : K))⁻¹) := by
  set eps : Fin TwistTag.E6.tag.rank → ℤ := ![0, 1, 1, 1, 0, 0] with heps
  set lam : K := (μ : K) * (σ (μ : K))⁻¹ with hlam
  obtain ⟨hχeps, hχρε⟩ := rootChar_twistedE6TorusTuple_classU σ μ hσσ
  have hε : IsRoot TwistTag.E6.tag eps := by
    rw [← RootOps.isRootB_iff]; decide +kernel
  have hρε : IsRoot TwistTag.E6.tag (permLattice TwistTag.E6.perm eps) :=
    hε.permLattice TwistTag.E6.cartan_perm
  exact rootDiagUnit_conj_classU_eq_twistedE6PairX σ μ lam eps hε hρε hχeps hχρε

end
section
open scoped commutatorElement in
private lemma commutator_classU_pairX_eq {K : Type} [Field K] [CharP K 2]
    (σ : K →+* K) (lam : K) :
    ⁅twistedE6ClassU K, twistedE6PairX σ ![0, 1, 1, 1, 0, 0] lam⁆ =
      pinnedX TwistTag.E6.tag K e6HighestRoot (lam + σ lam) := by
  set eps : Fin TwistTag.E6.tag.rank → ℤ := ![0, 1, 1, 1, 0, 0] with heps
  have hγ : IsRoot TwistTag.E6.tag twistedE6ClassRootU := isRoot_twistedE6ClassRoots.1
  have hε : IsRoot TwistTag.E6.tag eps := by
    rw [← RootOps.isRootB_iff]; decide +kernel
  have hγε : twistedE6ClassRootU + eps = e6HighestRoot := by
    ext j; fin_cases j <;> decide
  have hθ : IsRoot TwistTag.E6.tag (twistedE6ClassRootU + eps) := by
    rw [hγε]; exact isRoot_e6HighestRoot
  have hργ : permLattice TwistTag.E6.perm (twistedE6ClassRootU + eps) =
      twistedE6ClassRootU + eps := by rw [hγε]; exact permLattice_e6HighestRoot
  have hne : twistedE6ClassRootU ≠ eps := by
    intro h
    have := congrFun h 0
    norm_num [twistedE6ClassRootU, eps] at this
  have h1 : ¬IsRoot TwistTag.E6.tag
      (twistedE6ClassRootU + permLattice TwistTag.E6.perm eps) := by
    rw [← RootOps.isRootB_iff]; decide +kernel
  have h2 : twistedE6ClassRootU + permLattice TwistTag.E6.perm eps ≠ 0 := by
    decide +kernel
  have h3 : twistedE6ClassRootU ≠ permLattice TwistTag.E6.perm eps := by decide +kernel
  have h4 : ¬IsRoot TwistTag.E6.tag (twistedE6ClassRootU + eps + twistedE6ClassRootU) := by
    rw [← RootOps.isRootB_iff]; decide +kernel
  have h5 : ¬IsRoot TwistTag.E6.tag (twistedE6ClassRootU + eps + eps) := by
    rw [← RootOps.isRootB_iff]; decide +kernel
  have h6 : twistedE6ClassRootU + eps ≠ -twistedE6ClassRootU := by decide +kernel
  have h7 : twistedE6ClassRootU + eps ≠ -eps := by decide +kernel
  rw [twistedE6ClassU_eq_twistedE6PairX σ]
  rw [commutator_twistedE6PairX σ hγ hε hθ hργ hne h1 h2 h3 h4 h5 h6 h7 1 lam]
  rw [hγε]
  simp

end
section
private lemma twistedE6PairX_sq_classU {K : Type} [Field K] [CharP K 2]
    (σ : K →+* K) (lam : K) :
    twistedE6PairX σ ![0, 1, 1, 1, 0, 0] lam ^ 2 = 1 := by
  set eps : Fin TwistTag.E6.tag.rank → ℤ := ![0, 1, 1, 1, 0, 0] with heps
  rw [twistedE6PairX]
  have hε : IsRoot TwistTag.E6.tag eps := by
    rw [← RootOps.isRootB_iff]; decide +kernel
  have hc := commute_pinnedX_permLattice_twistedE6 (δ := eps) hε lam (σ lam)
  rw [hc.mul_pow]
  have h1 : pinnedX TwistTag.E6.tag K eps lam ^ 2 = 1 := by
    rw [sq, ← pinnedX_add, show lam + lam = 0 by rw [CharTwo.add_self_eq_zero],
      pinnedX_zero]
  have h2 : pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm eps) (σ lam) ^ 2 = 1 := by
    rw [sq, ← pinnedX_add, show σ lam + σ lam = 0 by rw [CharTwo.add_self_eq_zero],
      pinnedX_zero]
  rw [h1, h2, one_mul]

end
section
open scoped commutatorElement in
private lemma sq_classU_mul_pairX_eq {K : Type} [Field K] [CharP K 2]
    (σ : K →+* K) (lam : K) :
    (twistedE6ClassU K * twistedE6PairX σ ![0, 1, 1, 1, 0, 0] lam) ^ 2 =
      pinnedX TwistTag.E6.tag K e6HighestRoot (lam + σ lam) := by
  set eps : Fin TwistTag.E6.tag.rank → ℤ := ![0, 1, 1, 1, 0, 0] with heps
  have hu2 : twistedE6ClassU K ^ 2 = 1 := twistedE6ClassU_sq
  have hy2 : twistedE6PairX σ eps lam ^ 2 = 1 := twistedE6PairX_sq_classU σ lam
  have hcomm : ⁅twistedE6ClassU K, twistedE6PairX σ eps lam⁆ =
      pinnedX TwistTag.E6.tag K e6HighestRoot (lam + σ lam) :=
    commutator_classU_pairX_eq σ lam
  have hu_inv : (twistedE6ClassU K)⁻¹ = twistedE6ClassU K :=
    inv_eq_of_mul_eq_one_right (by rwa [pow_two] at hu2)
  have hy_inv : (twistedE6PairX σ eps lam)⁻¹ = twistedE6PairX σ eps lam :=
    inv_eq_of_mul_eq_one_right (by rwa [pow_two] at hy2)
  calc
    (twistedE6ClassU K * twistedE6PairX σ eps lam) ^ 2 =
        ⁅twistedE6ClassU K, twistedE6PairX σ eps lam⁆ := by
          rw [pow_two, commutatorElement_def, hu_inv, hy_inv]; group
    _ = pinnedX TwistTag.E6.tag K e6HighestRoot (lam + σ lam) := hcomm

end
section
private lemma orderOf_classU_mul_pairX_eq_four {K : Type} [Field K] [CharP K 2]
    (σ : K →+* K) (lam : K) (hadd : lam + σ lam ≠ 0) :
    orderOf (twistedE6ClassU K * twistedE6PairX σ ![0, 1, 1, 1, 0, 0] lam) = 4 ∧
      (twistedE6ClassU K * twistedE6PairX σ ![0, 1, 1, 1, 0, 0] lam) ^ 2 =
        pinnedX TwistTag.E6.tag K e6HighestRoot (lam + σ lam) := by
  have hx2 := sq_classU_mul_pairX_eq σ lam
  have hz2 : pinnedX TwistTag.E6.tag K e6HighestRoot (lam + σ lam) ^ 2 = 1 := by
    rw [sq, ← pinnedX_add, show (lam + σ lam) + (lam + σ lam) = 0 by
      rw [CharTwo.add_self_eq_zero], pinnedX_zero]
  have hz1 : pinnedX TwistTag.E6.tag K e6HighestRoot (lam + σ lam) ≠ 1 := by
    intro h
    apply hadd
    exact pinnedX_injective (τ := TwistTag.E6.tag) (R := K) e6HighestRoot
      (h.trans (pinnedX_zero TwistTag.E6.tag K e6HighestRoot).symm)
  have hnot : ¬ (twistedE6ClassU K * twistedE6PairX σ ![0, 1, 1, 1, 0, 0] lam) ^ 2 = 1 := by
    rw [hx2]; exact hz1
  have hfin : (twistedE6ClassU K * twistedE6PairX σ ![0, 1, 1, 1, 0, 0] lam) ^
      (2 ^ (1 + 1)) = 1 := by
    rw [show (2 : ℕ) ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, hx2, hz2]
  refine ⟨?_, hx2⟩
  have := orderOf_eq_prime_pow (p := 2) (n := 1) hnot hfin
  simpa using this

end
section
private lemma twistedE6TorusParam_add_apply_ne_zero {K : Type} [Field K] [CharP K 2]
    (σ : K →+* K) (μ : Kˣ) (hσσ : ∀ c, σ (σ c) = c) (hμ : σ (μ : K) ≠ (μ : K)) :
    ((μ : K) * (σ (μ : K))⁻¹) + σ ((μ : K) * (σ (μ : K))⁻¹) ≠ 0 := by
  set lam : K := (μ : K) * (σ (μ : K))⁻¹ with hlam
  have hlam0 : lam ≠ 0 := by
    rw [hlam]
    exact mul_ne_zero μ.ne_zero (inv_ne_zero ((map_ne_zero σ).2 μ.ne_zero))
  have hσlam : σ lam = lam⁻¹ := by
    rw [hlam, map_mul, map_inv₀, hσσ, mul_inv_rev, inv_inv]
  have hlam1 : lam ≠ 1 := by
    intro h
    apply hμ
    have h' : (μ : K) * (σ (μ : K))⁻¹ = 1 := by rwa [hlam] at h
    have hσne : σ (μ : K) ≠ 0 := (map_ne_zero σ).2 μ.ne_zero
    have := congrArg (fun x : K => x * σ (μ : K)) h'
    rw [mul_assoc, inv_mul_cancel₀ hσne, mul_one, one_mul] at this
    exact this.symm
  intro h0
  have hsq : lam ^ 2 = 1 := by
    have h := congrArg (fun x : K => x * lam) h0
    rw [add_mul, hσlam, inv_mul_cancel₀ hlam0, zero_mul] at h
    have h' : lam * lam = -1 := eq_neg_of_add_eq_zero_left h
    rw [CharTwo.neg_eq] at h'
    simpa [sq] using h'
  rcases sq_eq_one_iff.1 hsq with h | h
  · exact hlam1 h
  · rw [CharTwo.neg_eq] at h
    exact hlam1 h

end
section
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley in
private lemma torus_weyl_conj_classU_eq_pairX [CharP K 2]
    (σE : K ≃+* K) (μu : Kˣ) (hσσ : ∀ c, σE.toRingHom (σE.toRingHom c) = c)
    {n h : graphFixedRootGroup TwistTag.E6 K σE.toRingHom}
    (hn : (n : ModGL TwistTag.E6.tag K) = twistedE6RelWeyl K [0, 1, 2, 1, 0])
    (hh : (h : ModGL TwistTag.E6.tag K) =
      rootDiagUnit TwistTag.E6.tag (twistedE6TorusTuple σE.toRingHom 2 μu)) :
    (((h * n) * stdRepC hσσ 1 * (h * n)⁻¹ :
        graphFixedRootGroup TwistTag.E6 K σE.toRingHom) : ModGL TwistTag.E6.tag K) =
      twistedE6PairX σE.toRingHom ![0, 1, 1, 1, 0, 0]
        ((μu : K) * (σE (μu : K))⁻¹) := by
  calc
    (((h * n) * stdRepC hσσ 1 * (h * n)⁻¹ :
        graphFixedRootGroup TwistTag.E6 K σE.toRingHom) : ModGL TwistTag.E6.tag K)
        = (h : ModGL TwistTag.E6.tag K) *
            ((n : ModGL TwistTag.E6.tag K) *
              (stdRepC hσσ 1 : ModGL TwistTag.E6.tag K) *
              (n : ModGL TwistTag.E6.tag K)⁻¹) *
            (h : ModGL TwistTag.E6.tag K)⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
    _ = (h : ModGL TwistTag.E6.tag K) *
          (pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm ![0, 1, 1, 1, 0, 0]) 1 *
            pinnedX TwistTag.E6.tag K ![0, 1, 1, 1, 0, 0] 1) *
          (h : ModGL TwistTag.E6.tag K)⁻¹ := by
          rw [hn, show (stdRepC hσσ 1 : ModGL TwistTag.E6.tag K) = twistedE6ClassU K from rfl,
            twistedE6RelWeyl_conj_classU_eq]
    _ = twistedE6PairX σE.toRingHom ![0, 1, 1, 1, 0, 0]
          ((μu : K) * (σE (μu : K))⁻¹) := by
          rw [hh]
          exact rootDiagUnit_conj_classU_eq_pairX σE.toRingHom μu hσσ

end
section
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley in
private lemma exists_torus_weyl_conj_classU_eq_pairX [CharP K 2]
    (σE : K ≃+* K) (hσE : σE ^ TwistTag.E6.order = 1)
    (μu : Kˣ) (hσσ : ∀ c, σE.toRingHom (σE.toRingHom c) = c)
    (hμu : σE (μu : K) ≠ (μu : K)) :
    ∃ (g y : graphFixedRootGroup TwistTag.E6 K σE.toRingHom) (lam : K),
      g⁻¹ * stdRepC hσσ 1 * g = y ∧
      (y : ModGL TwistTag.E6.tag K) =
        twistedE6PairX σE.toRingHom ![0, 1, 1, 1, 0, 0] lam ∧
      lam + σE.toRingHom lam ≠ 0 := by
  let lam : K := (μu : K) * (σE (μu : K))⁻¹
  let n : graphFixedRootGroup TwistTag.E6 K σE.toRingHom :=
    relWeylC σE.toRingHom [0, 1, 2, 1, 0]
  let h : graphFixedRootGroup TwistTag.E6 K σE.toRingHom :=
    ⟨rootDiagUnit TwistTag.E6.tag (twistedE6TorusTuple σE.toRingHom 2 μu),
      rootDiagUnit_twistedE6TorusTuple_mem σE hσE (by decide) μu⟩
  let y : graphFixedRootGroup TwistTag.E6 K σE.toRingHom :=
    (h * n) * stdRepC hσσ 1 * (h * n)⁻¹
  have hn : (n : ModGL TwistTag.E6.tag K) =
      twistedE6RelWeyl K [0, 1, 2, 1, 0] := rfl
  have hh : (h : ModGL TwistTag.E6.tag K) =
      rootDiagUnit TwistTag.E6.tag (twistedE6TorusTuple σE.toRingHom 2 μu) := rfl
  have hyval : (y : ModGL TwistTag.E6.tag K) =
      twistedE6PairX σE.toRingHom ![0, 1, 1, 1, 0, 0] lam := by
    change (((h * n) * stdRepC hσσ 1 * (h * n)⁻¹ :
        graphFixedRootGroup TwistTag.E6 K σE.toRingHom) : ModGL TwistTag.E6.tag K) = _
    exact torus_weyl_conj_classU_eq_pairX σE μu hσσ hn hh
  exact ⟨(h * n)⁻¹, y, lam, by simp only [inv_inv, y], hyval,
    twistedE6TorusParam_add_apply_ne_zero σE.toRingHom μu hσσ hμu⟩

end
section
private lemma exists_conj_classU_eq_pairX [CharP K 2] (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ∃ (g y : graphFixedRootGroup TwistTag.E6 K σ) (lam : K),
      g⁻¹ * stdRepC (apply_apply_eq hK hσ) 1 * g = y ∧
      (y : ModGL TwistTag.E6.tag K) =
        twistedE6PairX σ ![0, 1, 1, 1, 0, 0] lam ∧
      lam + σ lam ≠ 0 := by
  classical
  obtain ⟨μ, hμ⟩ := exists_apply_ne hf hK hσ
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact hμ (by rw [hσ]; simp)
  obtain ⟨σE, rfl⟩ := @exists_ringEquiv_toRingHom_eq K _ (finite_of_card hK) σ
  let μu : Kˣ := Units.mk0 μ hμ0
  have hμu : σE (μu : K) ≠ (μu : K) := by
    simpa [μu] using hμ
  have hσσ : ∀ c, σE.toRingHom (σE.toRingHom c) = c := apply_apply_eq hK hσ
  have hσE : σE ^ TwistTag.E6.order = 1 :=
    @twistedE6_sigma_pow_order K _ f (finite_of_card hK) hK σE (fun c => hσ c)
  obtain ⟨g, y, lam, hgy, hyval, hadd⟩ :=
    exists_torus_weyl_conj_classU_eq_pairX σE hσE μu hσσ hμu
  exact ⟨g, y, lam, hgy, hyval, hadd⟩

end
section
private lemma centralizes_of_sylow_eq_posUnipotent [CharP K 2]
    (σE : K ≃+* K)
    {z : graphFixedRootGroup TwistTag.E6 K σE.toRingHom} {lam : K}
    (hz : (z : ModGL TwistTag.E6.tag K) =
      pinnedX TwistTag.E6.tag K e6HighestRoot (lam + σE.toRingHom lam))
    (P : Sylow 2 (graphFixedRootGroup TwistTag.E6 K σE.toRingHom))
    (hP : (P : Subgroup (graphFixedRootGroup TwistTag.E6 K σE.toRingHom)) =
      (graphFixedPosUnipotent TwistTag.E6 K σE.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σE.toRingHom)) :
    ∀ s ∈ (P : Subgroup (graphFixedRootGroup TwistTag.E6 K σE.toRingHom)), s * z = z * s := by
  intro s hs
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hz]
  have hsU : (s : ModGL TwistTag.E6.tag K) ∈
      graphFixedPosUnipotent TwistTag.E6 K σE.toRingHom := by
    rw [hP, mem_subgroupOf] at hs
    exact hs
  exact (commute_e6HighestRoot_of_mem_posUnipotent K (mem_inf.1 hsU).1
    (lam + σE.toRingHom lam)).eq
end

private noncomputable def sylowPosUnipotent [CharP K 2] (hfinK : Finite K) (σE : K ≃+* K) :
    { P : Sylow 2 (graphFixedRootGroup TwistTag.E6 K σE.toRingHom) //
      (P : Subgroup (graphFixedRootGroup TwistTag.E6 K σE.toRingHom)) =
        (graphFixedPosUnipotent TwistTag.E6 K σE.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.E6 K σE.toRingHom) } := by
  letI : Finite K := hfinK
  let w₀ : WeylGroup TwistTag.E6.tag :=
    Classical.choose (Finite.exists_max fun w : WeylGroup TwistTag.E6.tag =>
      (coxeterSystem TwistTag.E6.tag).length w)
  have hw₀ : ∀ w : WeylGroup TwistTag.E6.tag,
      (coxeterSystem TwistTag.E6.tag).length w ≤
        (coxeterSystem TwistTag.E6.tag).length w₀ :=
    Classical.choose_spec (Finite.exists_max fun w : WeylGroup TwistTag.E6.tag =>
      (coxeterSystem TwistTag.E6.tag).length w)
  let P : Sylow 2 (graphFixedRootGroup TwistTag.E6 K σE.toRingHom) :=
    Classical.choose (exceptional_fixed_Sylow_opposition TwistTag.E6 K 2 σE w₀ hw₀).1
  have hP : (P : Subgroup (graphFixedRootGroup TwistTag.E6 K σE.toRingHom)) =
      (graphFixedPosUnipotent TwistTag.E6 K σE.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σE.toRingHom) :=
    Classical.choose_spec (exceptional_fixed_Sylow_opposition TwistTag.E6 K 2 σE w₀ hw₀).1
  exact ⟨P, hP⟩

theorem exists_orderOf_classU_mul_conj_eq_four [CharP K 2] (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ∃ g : graphFixedRootGroup TwistTag.E6 K σ,
      orderOf (stdRepC (apply_apply_eq hK hσ) 1 *
        (g⁻¹ * stdRepC (apply_apply_eq hK hσ) 1 * g)) = 4 ∧
      ∃ S : Sylow 2 (graphFixedRootGroup TwistTag.E6 K σ),
        ∀ s ∈ (S : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)),
          s * (stdRepC (apply_apply_eq hK hσ) 1 *
              (g⁻¹ * stdRepC (apply_apply_eq hK hσ) 1 * g)) ^ 2 =
            (stdRepC (apply_apply_eq hK hσ) 1 *
              (g⁻¹ * stdRepC (apply_apply_eq hK hσ) 1 * g)) ^ 2 * s := by
  classical
  obtain ⟨σE, rfl⟩ := @exists_ringEquiv_toRingHom_eq K _ (finite_of_card hK) σ
  obtain ⟨g, y, lam, hgy, hyval, hadd⟩ := exists_conj_classU_eq_pairX hf hK hσ
  have hmain := orderOf_classU_mul_pairX_eq_four σE.toRingHom lam hadd
  have hu : (stdRepC (apply_apply_eq hK hσ) 1 : ModGL TwistTag.E6.tag K) =
      twistedE6ClassU K := rfl
  let hS := sylowPosUnipotent (finite_of_card hK) σE
  let P := hS.1
  have hP := hS.2
  refine ⟨g, ?_, ?_⟩
  · rw [hgy, ← Subgroup.orderOf_coe (stdRepC (apply_apply_eq hK hσ) 1 * y)]
    change orderOf ((stdRepC (apply_apply_eq hK hσ) 1 : ModGL TwistTag.E6.tag K) *
      (y : ModGL TwistTag.E6.tag K)) = 4
    rw [hu, hyval]
    exact hmain.1
  · rw [hgy]
    obtain ⟨P, hP⟩ := hS
    refine ⟨P, ?_⟩
    intro s hs
    have hz : (((stdRepC (apply_apply_eq hK hσ) 1 * y) ^ 2 :
        graphFixedRootGroup TwistTag.E6 K σE.toRingHom) : ModGL TwistTag.E6.tag K) =
        pinnedX TwistTag.E6.tag K e6HighestRoot (lam + σE.toRingHom lam) := by
      simp only [Subgroup.coe_pow, Subgroup.coe_mul]
      rw [hu, hyval]
      exact hmain.2
    exact centralizes_of_sylow_eq_posUnipotent σE hz P hP s hs
theorem exists_conj_eq_stdRepC_zero_of_isStrothInvolution [CharP K 2] (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {t : graphFixedRootGroup TwistTag.E6 K σ} {a : ℕ} (h : IsStrothInvolution t a) :
    ∃ g : graphFixedRootGroup TwistTag.E6 K σ, g * t * g⁻¹ = stdRepC (apply_apply_eq hK hσ) 0 := by
  have hσσ := apply_apply_eq hK hσ
  have hX : ∀ {x g : graphFixedRootGroup TwistTag.E6 K σ} {κ : Fin 2},
      ((g * x * g⁻¹ : graphFixedRootGroup TwistTag.E6 K σ) : ModGL TwistTag.E6.tag K) =
        repX K κ → IsConj x (stdRepC hσσ κ) := by
    intro x g κ hg
    obtain ⟨c, hc, hcx⟩ := isConj_stdRep_repX σ κ
    refine isConj_iff.2 ⟨⟨c, hc⟩⁻¹ * g, Subtype.ext ?_⟩
    have e : ((⟨c, hc⟩⁻¹ * g * x * (⟨c, hc⟩⁻¹ * g)⁻¹ : graphFixedRootGroup TwistTag.E6 K σ) :
        ModGL TwistTag.E6.tag K) = c⁻¹ *
          ((g * x * g⁻¹ : graphFixedRootGroup TwistTag.E6 K σ) : ModGL TwistTag.E6.tag K) * c := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
      group
    rw [e, hg, ← hcx]
    show _ = stdRep K κ
    group
  have hconj : ∀ {x : graphFixedRootGroup TwistTag.E6 K σ}
      (g : graphFixedRootGroup TwistTag.E6 K σ), IsConj x (g⁻¹ * x * g) :=
    fun g => isConj_iff.2 ⟨g⁻¹, by rw [inv_inv]⟩
  have ht2 : t ^ 2 = 1 := by
    rw [← h.orderOf_eq_two]
    exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := by
    intro h1
    have h3 := h.orderOf_eq_two
    rw [h1, orderOf_one] at h3
    omega
  obtain ⟨g, hg | hg | hg⟩ := exists_conj_repX_or_classV hf hK hσ ht2 ht1
  · exact isConj_iff.1 (hX hg)
  · obtain ⟨g₁, h4, S, hS⟩ := exists_orderOf_classU_mul_conj_eq_four hf hK hσ
    have hu := hX hg
    have hw := h.isConj_sq_of_orderOf_eq_four hu (hu.trans (hconj g₁)) h4
    have hw2 : orderOf ((stdRepC hσσ 1 * (g₁⁻¹ * stdRepC hσσ 1 * g₁)) ^ 2) = 2 := by
      obtain ⟨c, hc⟩ := hw
      exact (SemiconjBy.orderOf_eq _ hc).trans h.orderOf_eq_two
    obtain ⟨g₂, hg₂⟩ := (conj_repX_zero_iff_twoCentral hf hK hσ hw2).2 ⟨S, hS⟩
    exact isConj_iff.1 (hw.symm.trans (hX hg₂))
  · obtain ⟨g₁, h6⟩ := exists_orderOf_classV_mul_conj_eq_six (K := K) hσσ
    have hv : IsConj t ⟨twistedE6ClassV K, twistedE6ClassV_mem_graphFixedRootGroup hσσ⟩ :=
      isConj_iff.2 ⟨g, Subtype.ext hg⟩
    exact absurd h6 (h.orderOf_mul_ne_six hv (hv.trans (hconj g₁)))

end CFSG.SeitzReduction.TwistedE6Pilot

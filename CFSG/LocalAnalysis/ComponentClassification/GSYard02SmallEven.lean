module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard02Simple
public import Certificates.Certificate113
import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
import CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3Mat
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LieType.Ree.SuzukiUnipotentStructure
import CFSG.RankThree.SteinbergR3ESuzukiInvolutionCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OneComp
public import CFSG.LocalAnalysis.ComponentClassification.Sol76RankOneClassPoint
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import Certificates.Certificate7233Base

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Open
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Linear

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem sylowFourJoined_projectiveSL_two (h8 : 8 ≤ Nat.card F) :
    SylowFourJoined (projectiveSL 2 F) := by
  obtain ⟨S, hS⟩ := exists_sylow_projUnitriangular (K := F) 2 (n := 2) (by norm_num)
  refine sylowFourJoined_of_normal_elemAbelian S (A := projUnitriangular 2 F) ?_ ?_ ?_
  · rw [hS]
    exact Subgroup.le_normalizer
  · rintro _ ⟨g, hg, rfl⟩
    rw [← map_mul]
    have h10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hg.1 1 0 (by decide)
    have h00 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := hg.2 0
    have h11 : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := hg.2 1
    have hg2 : g * g = 1 := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, h10, h00, h11, CharTwo.add_self_eq_zero]
    rw [hg2, map_one]
  · rw [card_projUnitriangular]
    simpa using h8

local notation "heisTheta" => CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3.theta

open CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3 in
private def heisCol (F : Type) [Field F] : Subgroup (Heis F) where
  carrier := {x | x.a = 0}
  one_mem' := rfl
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [Heis.mul_a, hx, hy, add_zero]
  inv_mem' := fun {x} hx => by
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [Heis.inv_a, hx, neg_zero]

open CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3 in
theorem sylowFourJoined_projectiveSL_three (h8 : 8 ≤ Nat.card F * Nat.card F) :
    SylowFourJoined (projectiveSL 3 F) := by
  obtain ⟨S, hS⟩ := exists_sylow_projUnitriangular (K := F) 2 (n := 3) (by norm_num)
  have hinj : Function.Injective (heisTheta : Heis F →* projectiveSL 3 F) := fun x y h =>
    heisEquivBar.injective (Subtype.ext (by rw [heisEquivBar_apply, heisEquivBar_apply]; exact h))
  have hN : ∀ y : Heis F,
      y ∈ Subgroup.normalizer ((heisCol F : Subgroup (Heis F)) : Set (Heis F)) := by
    intro y
    rw [Subgroup.mem_normalizer_iff]
    intro h
    show (h.a = 0) ↔ ((y * h * y⁻¹).a = 0)
    simp only [Heis.mul_a, Heis.inv_a]
    constructor <;> intro hh <;> linear_combination hh
  refine sylowFourJoined_of_normal_elemAbelian S (A := (heisCol F).map heisTheta) ?_ ?_ ?_
  · intro s hs
    rw [hS] at hs
    obtain ⟨y, rfl⟩ := exists_theta_of_mem_bar hs
    exact Subgroup.le_normalizer_map heisTheta (Subgroup.mem_map_of_mem heisTheta (hN y))
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul]
    have ha : x.a = 0 := hx
    have hx2 : x * x = 1 := by
      ext
      · simp [ha]
      · simp [CharTwo.add_self_eq_zero]
      · simp [ha, CharTwo.add_self_eq_zero]
    rw [hx2, map_one]
  · have h1 : Nat.card (F × F) ≤ Nat.card ((heisCol F).map heisTheta) := by
      refine Nat.card_le_card_of_injective
        (fun p => ⟨heisTheta ⟨0, p.1, p.2⟩, Subgroup.mem_map_of_mem _
          (show (⟨0, p.1, p.2⟩ : Heis F).a = 0 from rfl)⟩) ?_
      intro p q hpq
      have h2 := hinj (congrArg Subtype.val hpq)
      exact Prod.ext (congrArg Heis.b h2) (congrArg Heis.c h2)
    rw [Nat.card_prod] at h1
    exact h8.trans h1

end Linear

section Suzuki

open CFSG.LieType.Ree

variable {K : Type} [Field K] [Finite K]

theorem sylowFourJoined_suzukiGroup_one (hK : Nat.card K = 2 ^ (2 * 1 + 1))
    [Finite (suzukiGroup 1 K)] : SylowFourJoined (suzukiGroup 1 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hZset, -, -, hcent, -⟩ := suzuki_unipotent_structure hK
  let P : Sylow 2 (suzukiGroup 1 K) := Sylow.ofCard (suzukiU 1 K) (RankThree.card_suzukiU_eq hK)
  have h2 : (2 : K) = 0 := (suzuki_frob_data 1 hK).1
  refine sylowFourJoined_of_normal_elemAbelian P (A := suzukiZ0 1 K) ?_ ?_ ?_
  · intro g hg
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact hcent z hz g hg
  · intro z hz
    obtain ⟨v, rfl⟩ := (mem_suzukiZ0_iff hK).1 hz
    rw [suzukiSElt_mul hK, ← suzukiSElt_zero_zero hK]
    refine suzukiSElt_inj.2 ⟨add_zero 0, ?_⟩
    linear_combination v * h2
  · have hcard : Nat.card (suzukiZ0 1 K) = Nat.card K := by
      rw [← SetLike.coe_sort_coe, hZset,
        Nat.card_range_of_injective (fun v w h => (suzukiSElt_inj.1 h).2)]
    rw [hcard, hK]
    norm_num

end Suzuki

private noncomputable def projEquiv (n : ℕ) (K : Type) [Field K] :
    projectiveSL n K ≃* StatedProj (StatedSL n K) :=
  (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center n K)).trans
    (projectiveSpecialLinearGroupEquivStatedProj n K)

private theorem sylowFourJoined_of_psl_two {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 3 ≤ f)
    (h : StatedClassicalModel X .PSL 2 2 f) : SylowFourJoined X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  let e' : projectiveSL 2 K ≃* X := (projEquiv 2 K).trans e.symm
  have : Finite (projectiveSL 2 K) := Finite.of_equiv X e'.symm.toEquiv
  refine SylowFourJoined.of_mulEquiv e' (sylowFourJoined_projectiveSL_two ?_)
  rw [hK]
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

private theorem sylowFourJoined_of_psl_three {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (h : StatedClassicalModel X .PSL 3 2 f) : SylowFourJoined X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  let e' : projectiveSL 3 K ≃* X := (projEquiv 3 K).trans e.symm
  have : Finite (projectiveSL 3 K) := Finite.of_equiv X e'.symm.toEquiv
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  refine SylowFourJoined.of_mulEquiv e' (sylowFourJoined_projectiveSL_three ?_)
  calc 8 ≤ 4 * 4 := by norm_num
    _ ≤ Nat.card K * Nat.card K := Nat.mul_le_mul h4 h4

private theorem sylowFourJoined_of_twistedB2 {X : Type} [Group X]
    [Finite X] (h : LieModel X .twistedB2 0 2 3) : SylowFourJoined X := by
  rcases h with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, -, a, ha, K, _, _, hf, hK, ⟨e⟩⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · obtain rfl : a = 1 := by omega
    have : Finite (suzukiGroup 1 K) := Finite.of_equiv X e.toEquiv
    exact SylowFourJoined.of_mulEquiv e.symm (sylowFourJoined_suzukiGroup_one (by rw [hK]))

theorem leafSmallEven_holds : LeafSmallEven := by
  intro X _ _ _ _ h
  rcases h with h | h | h | h
  · exact sylowFourJoined_of_psl_two (f := 3) le_rfl
      (h.statedClassicalModel_of_ne_zero (by norm_num))
  · exact sylowFourJoined_of_psl_two (f := 4) (by norm_num)
      (h.statedClassicalModel_of_ne_zero (by norm_num))
  · exact sylowFourJoined_of_psl_three (f := 2) le_rfl
      (h.statedClassicalModel_of_ne_zero (by norm_num))
  · exact sylowFourJoined_of_twistedB2 h

end CFSG.ComponentClassification.Sol76.Sig.GSYard02

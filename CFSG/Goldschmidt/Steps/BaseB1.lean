module

public import CFSG.Goldschmidt.StatementsH
import CFSG.Milestones.CL_LIT_Walter_abelian_Sylow_two_simple
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGoldschmidtBender
public import CFSG.Goldschmidt.Statements
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGoldschmidtBasic

public section

namespace CFSG.Goldschmidt

open CFSG.Open
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter sylowCenter_le
  benderBorel_sylowCenter normalizer_transitive_center)
open CFSG.ComponentClassification.AschbacherToolkit.BenderExt (benderData_of_isBenderGroup)
open CFSG.ComponentClassification.AschbacherToolkit.Goldschmidt (mem_sylowCenter_of_sq_eq_one)
open scoped MatrixGroups

namespace BaseB1

theorem goldschmidtSimpleType_of_psl2_even
    {L : Type} [Group L] {f : ℕ} (hf : 2 ≤ f)
    (e : L ≃* PSL(2, GaloisField 2 f)) : goldschmidtSimpleType L := by
  rcases Nat.lt_or_ge f 3 with hf3 | hf3
  · obtain rfl : f = 2 := by omega
    have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨e'⟩ := CFSG.Walter.nonempty_psl2_five_mulEquiv_psl2_four
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨5, 1, h5, ⟨2, rfl⟩, one_pos, by norm_num, Or.inr (by norm_num), ⟨e.trans e'.symm⟩⟩)))
  · exact Or.inl ⟨f, hf3, ⟨e⟩⟩

theorem goldschmidtSimpleType_of_isBenderGroup
    {L : Type} [Group L] (h : fusionIsBenderGroup L) :
    goldschmidtSimpleType L := by
  rcases h with ⟨f, hf, ⟨e⟩⟩ | hU | hSz
  · exact goldschmidtSimpleType_of_psl2_even hf e
  · exact Or.inr (Or.inr (Or.inl hU))
  · exact Or.inr (Or.inl hSz)

theorem goldschmidtSimpleType_of_isMulCommutative_sylow
    (G : Type) [Group G] [Finite G]
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (S : Sylow 2 G)
    (hS : IsMulCommutative (S : Subgroup G)) : goldschmidtSimpleType G := by
  rcases CFSG.Milestones.cl_lit_walter_abelian_sylow_two_simple G hnab S hS with
    ⟨f, hf, ⟨e⟩⟩ | hodd | hree | hJ
  · exact goldschmidtSimpleType_of_psl2_even hf e
  · exact Or.inr (Or.inr (Or.inr (Or.inl hodd)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hree))))
  · obtain ⟨e⟩ := hJ
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨e.trans (MulEquiv.subgroupCongr (show walterJ1 = goldschmidtJ1 from rfl))⟩))))

end BaseB1

theorem N29_of
    (h11a : S_N11a) (h11b : S_N11b) : S_N29 := by
  intro G _ _ _ hnab S hSab A hAS hA1 hAcl
  have hType := BaseB1.goldschmidtSimpleType_of_isMulCommutative_sylow G hnab S hSab
  have hΩS : Omega1 (S : Subgroup G) ≤ S := (Subgroup.closure_le _).mpr fun t ht => ht.1
  have hΩab : IsMulCommutative (Omega1 (S : Subgroup G)) := isMulCommutative_anti hΩS
  have helem : ∀ t ∈ (S : Subgroup G), t ^ 2 = 1 := (h11a G hType S hΩab).1 hSab
  have hΩ : Omega1 (S : Subgroup G) = S :=
    le_antisymm hΩS fun t ht => Subgroup.subset_closure ⟨ht, helem t ht⟩
  obtain ⟨-, htrans⟩ := h11b G hType S hΩab
  obtain ⟨⟨a, haA⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA1
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hSA : (S : Subgroup G) ≤ A := by
    intro s hs
    by_cases hs1 : s = 1
    · rw [hs1]
      exact A.one_mem
    obtain ⟨n, -, hn⟩ := htrans a (by rw [hΩ]; exact hAS haA) s (by rw [hΩ]; exact hs) ha1' hs1
    have h := hAcl a haA n (by rw [hn]; exact hs)
    rwa [hn] at h
  have hAeq : A = S := le_antisymm hAS hSA
  exact ⟨hType, hAeq, hAeq.trans hΩ.symm⟩

theorem N30 : S_N30 := by
  intro G _ _ hBen S _ A hAS hA1 _ hAcl
  have hD := benderData_of_isBenderGroup hBen
  obtain ⟨q, k, hq4, hBorel⟩ := hD.borel
  obtain ⟨hSE, hZ2, -, -⟩ := benderBorel_sylowCenter hBorel S
  have hinv : ∀ t ∈ (S : Subgroup G), t ^ 2 = 1 → t ∈ sylowCenter (S : Subgroup G) :=
    fun t ht ht2 => mem_sylowCenter_of_sq_eq_one hBorel (by omega) S ht ht2
  have hΩ : Omega1 (S : Subgroup G) = sylowCenter (S : Subgroup G) :=
    le_antisymm ((Subgroup.closure_le _).mpr fun t ht => hinv t ht.1 ht.2)
      fun z hz => Subgroup.subset_closure ⟨sylowCenter_le _ hz, hZ2 z hz⟩
  obtain ⟨a, ha⟩ : ∃ a : A, orderOf a = 2 := by
    refine exists_prime_orderOf_dvd_card' 2 ?_
    rcases (S.isPGroup'.to_le hAS).card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hA1
    · exact h
  have ha' : orderOf (a : G) = 2 := by rwa [Subgroup.orderOf_coe]
  have ha2 : (a : G) ^ 2 = 1 := by rw [← ha']; exact pow_orderOf_eq_one _
  have ha1 : (a : G) ≠ 1 := fun h => by rw [h, orderOf_one] at ha'; omega
  have haZ : (a : G) ∈ sylowCenter (S : Subgroup G) := hinv a (hAS a.2) ha2
  have hZA : sylowCenter (S : Subgroup G) ≤ A := by
    intro z hz
    by_cases hz1 : z = 1
    · rw [hz1]
      exact A.one_mem
    obtain ⟨n, -, hn⟩ := normalizer_transitive_center hSE hZ2 haZ hz ha1 hz1
    have h := hAcl a a.2 n (by rw [hn]; exact sylowCenter_le _ hz)
    rwa [hn] at h
  have hAZ : A ≤ sylowCenter (S : Subgroup G) := by
    intro x hx
    by_contra hxZ
    obtain ⟨n, hn, hpair⟩ := hD.cent S x (hAS hx) hxZ
    have hxn : n⁻¹ * x * n ∈ (S : Subgroup G) := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) x).mp (hAS hx)
      rwa [inv_inv] at this
    have hxnA : n⁻¹ * x * n ∈ A := hAcl x hx n hxn
    exact hxZ (hpair x (hAS hx) rfl (setLike_mul_comm hx hxnA))
  have hAeq : A = sylowCenter (S : Subgroup G) := le_antisymm hAZ hZA
  exact ⟨BaseB1.goldschmidtSimpleType_of_isBenderGroup hBen, hAeq.trans hΩ.symm, hAeq⟩

end CFSG.Goldschmidt

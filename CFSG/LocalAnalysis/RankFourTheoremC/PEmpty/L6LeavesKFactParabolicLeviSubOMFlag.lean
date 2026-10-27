module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusCuts
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDEvenIso
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubAbstract
public import CFSG.RankThree.PartOne.AUTSL.OmegaFamily

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPLeviSub

open CFSG.Open Subgroup CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

open scoped Pointwise in
theorem orthMinus_exists_eq_orthParab {r : ℕ} (hr : 3 ≤ r) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {K₀ : Subgroup ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))}
    (hB : (tailBorel r (minusTailForm K b c)).subgroupOf
      (orthElementaryGroup (quadTail r (minusTailForm K b c))) ≤ K₀) :
    ∃ (s : ℕ) (d : Fin (s + 1) → ℕ), OrthCuts r d ∧
      K₀ = orthParab r (minusTailForm K b c) d := by
  classical
  have hani := anisotropic_minusTailForm hirr
  set M := K₀.map (orthElementaryGroup (quadTail r (minusTailForm K b c))).subtype with hMdef
  have hMG : M ≤ orthElementaryGroup (quadTail r (minusTailForm K b c)) :=
    Subgroup.map_subtype_le _
  have hBM : tailBorel r (minusTailForm K b c) ≤ M := fun z hz =>
    ⟨⟨z, tailBorel_le hz⟩, hB (Subgroup.mem_subgroupOf.2 hz), rfl⟩
  have ha₀ : (Pi.single 0 1 : Fin 2 → K) ≠ 0 := fun h => by simpa using congrFun h 0
  have hM' := tail_overgroup_stabilizers hani ha₀ hMG hBM
  set Jf : Finset (Fin r) :=
    Finset.univ.filter (fun i => tailWeylElt r (minusTailForm K b c) (Pi.single 0 1) i ∉ M)
  set D : Finset ℕ := insert 0 (Jf.image fun i : Fin r => (i : ℕ) + 1) with hD
  have h0D : 0 ∈ D := Finset.mem_insert_self _ _
  obtain ⟨s, hs⟩ : ∃ s, D.card = s + 1 := ⟨D.card - 1, by
    have := Finset.card_pos.2 ⟨0, h0D⟩
    omega⟩
  set d : Fin (s + 1) → ℕ := fun k => D.orderEmbOfFin hs k with hd
  have hdmem : ∀ k, d k ∈ D := fun k => Finset.orderEmbOfFin_mem D hs k
  have hdrange : ∀ m ∈ D, ∃ k, d k = m := fun m hm => by
    have : m ∈ Set.range (D.orderEmbOfFin hs) := by rw [Finset.range_orderEmbOfFin]; exact hm
    obtain ⟨k, hk⟩ := this
    exact ⟨k, hk⟩
  have hDle : ∀ m ∈ D, m ≤ r := fun m hm => by
    rcases Finset.mem_insert.1 hm with rfl | hm
    · omega
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hm
      exact i.isLt
  have hcuts : OrthCuts r d := by
    refine ⟨(D.orderEmbOfFin hs).strictMono, ?_, hDle _ (hdmem _)⟩
    obtain ⟨k₀, hk₀⟩ := hdrange 0 h0D
    have := (D.orderEmbOfFin hs).monotone (Fin.zero_le k₀)
    change d 0 ≤ d k₀ at this
    omega
  refine ⟨s, d, hcuts, ?_⟩
  ext y
  rw [mem_orthParab, ← Subgroup.mem_map_iff_mem
    (orthElementaryGroup (quadTail r (minusTailForm K b c))).subtype_injective, ← hMdef, hM',
    Subgroup.mem_inf]
  simp only [Subgroup.mem_iInf, Submodule.mem_stabilizer_submodule_iff_map_eq]
  refine ⟨fun ⟨_, h⟩ k => ?_, fun h => ⟨y.2, fun i hi => ?_⟩⟩
  · rcases Finset.mem_insert.1 (hdmem k) with h0 | hk
    · rw [h0, tailFlag_zero, Submodule.map_bot]
    · obtain ⟨i, hi, hik⟩ := Finset.mem_image.1 hk
      rw [← hik]
      exact h i (Finset.mem_filter.1 hi).2
  · obtain ⟨k, hk⟩ := hdrange ((i : ℕ) + 1)
      (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩,
        rfl⟩))
    have := h k
    rwa [hk] at this

theorem orthMinus_leviSubAt_of_orthParab {r : ℕ} (hr : 3 ≤ r)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (h : ∀ (s : ℕ) (d : Fin (s + 1) → ℕ), OrthCuts r d → ∀ p : ℕ,
      LeviAt (orthParab r (minusTailForm K b c) d) p) :
    LeviSubAt ↥(orthElementaryGroup (quadTail r (minusTailForm K b c))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hani := anisotropic_minusTailForm hirr
  have hreg := nondegenerate_minusTailForm hirr
  obtain ⟨⟨U, hU⟩, hNU, -⟩ := orthogonal_geometry_tail_Sylow_flag_normalizer (p := 2) hr hani hreg
    (Or.inr finrank_fin_two_fun)
  refine leviSubAt_of_standard_sylow U fun K₀ p hN => ?_
  rw [hU, hNU] at hN
  obtain ⟨s, d, hd, rfl⟩ := orthMinus_exists_eq_orthParab hr hirr hN
  exact h s d hd p

end KPLeviSub

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

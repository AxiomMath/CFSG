module

public import CFSG.LocalAnalysis.AGLEmbedding.PhaseThreeBlockRank
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockBasic
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoDataAux

public section
namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem eq_top_of_perfect_of_index_le_four {W : Type*} [Group W] [Finite W]
    (hW : commutator W = ⊤) (St : Subgroup W) (h4 : St.index ≤ 4) : St = ⊤ := by
  classical
  set φ := MulAction.toPermHom W (W ⧸ St) with hφ
  have hsolv : Group.IsSolvable (Equiv.Perm (W ⧸ St)) := Equiv.Perm.isSolvable h4
  have hrange : ⁅φ.range, φ.range⁆ = φ.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def, hW]
  have hbot : φ.range = ⊥ := eq_bot_of_commutator_eq_self_of_le (Z := ⊤) le_top
    (Group.isSolvable_of_surjective (f := (Subgroup.topEquiv).symm.toMonoidHom)
      (MulEquiv.surjective _)) hrange
  rw [eq_top_iff]
  intro w _
  have h1 : φ w = 1 := by
    have : φ w ∈ φ.range := ⟨w, rfl⟩
    rw [hbot] at this
    exact Subgroup.mem_bot.mp this
  have h2 : w • ((1 : W) : W ⧸ St) = ((1 : W) : W ⧸ St) := by
    have := congrArg (fun σ : Equiv.Perm (W ⧸ St) => σ ((1 : W) : W ⧸ St)) h1
    simpa [hφ] using this
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq, mul_one] at h2
  simpa using St.inv_mem h2

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem D1PhaseThree.le_normalizer_barM_of_perfect (h : D1PhaseThree p P M H R)
    (hind : ∀ q ∈ GLBBetaFour G, q < p → D1At G q) (hp5 : 5 ≤ p)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    {D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hDK : D ≤ barM M (H ⊓ M)) (hD : ⁅D, D⁆ = D) :
    D ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  classical
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set St : Subgroup D := (Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).subgroupOf D
    with hSt
  have hDperf : commutator D = ⊤ := by
    apply Subgroup.map_injective D.subtype_injective
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      hD]
  have hidx : St.index ≤ 3 := by
    by_contra h4
    push Not at h4
    have hcard : Nat.card (Fin 4) ≤ Nat.card (D ⧸ St) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      exact h4
    have : Fintype (D ⧸ St) := Fintype.ofFinite _
    have hcard' : Fintype.card (Fin 4) ≤ Fintype.card (D ⧸ St) := by
      rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
      exact hcard
    obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcard'
    choose g hg using fun j => QuotientGroup.mk_surjective (f j)
    have hlift : ∀ j, ∃ k : G, k ∈ H ⊓ M ∧ ∃ hkM : k ∈ M, mk ⟨k, hkM⟩ = (g j : _) := by
      intro j
      obtain ⟨m, hm, hmg⟩ := hDK (g j).2
      exact ⟨m, Subgroup.mem_subgroupOf.mp hm, m.2, hmg⟩
    choose k hk hkM hkg using hlift
    have hinj : Function.Injective fun j => L.map (MulAut.conj (k j)).toMonoidHom := by
      intro i j hij
      have h1 : (barM M L).map (MulAut.conj (g i : ↥M ⧸ CFSG.pCore 2 ↥M)).toMonoidHom =
          (barM M L).map (MulAut.conj (g j : ↥M ⧸ CFSG.pCore 2 ↥M)).toMonoidHom := by
        rw [← hkg i, ← hkg j, ← barM_map_conj (hkM i), ← barM_map_conj (hkM j)]
        exact congrArg (barM M) hij
      have hmm : ∀ (a b : ↥M ⧸ CFSG.pCore 2 ↥M) (X : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)),
          X.map (MulAut.conj (a * b)).toMonoidHom =
            (X.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
        intro a b X
        rw [Subgroup.map_map]
        congr 1
        ext x
        simp [MulAut.conj_apply, mul_assoc]
      have h2' : (barM M L).map (MulAut.conj ((g j : ↥M ⧸ CFSG.pCore 2 ↥M)⁻¹ *
          (g i : ↥M ⧸ CFSG.pCore 2 ↥M))).toMonoidHom = barM M L := by
        rw [hmm, h1, ← hmm, inv_mul_cancel]
        ext x
        simp
      have h2 : ((g j)⁻¹ * g i : D) ∈ St := by
        rw [hSt, Subgroup.mem_subgroupOf, Subgroup.mem_normalizer_iff_map_conj_eq]
        push_cast
        exact h2'
      have h3 : f i = f j := by
        rw [← hg i, ← hg j, QuotientGroup.eq]
        have := St.inv_mem h2
        simpa using this
      exact f.injective h3
    have hle := h.le_pRank_three_of_injective_conj hB3 hL k hk hinj
    exact h.false_of_four_le_pRank' hind Nat.prime_three (by decide) (by omega) hle
  have htop := eq_top_of_perfect_of_index_le_four hDperf St (by omega)
  intro d hd
  have hmem : (⟨d, hd⟩ : D) ∈ St := htop ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp hmem

end CFSG.AGLEmbedding

module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeBlocksAux
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsII
import CFSG.Alternating.Multipliers.Main
import CFSG.GH74.Generic.GKFCover

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {M S L : Subgroup G}

omit [Finite G] in
theorem exists_noncomm_barM (hL : IsWeakSBlock M S L) :
    ∃ a b : ↥(barM M L), a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hZ : Subgroup.center ↥(barM M L) = ⊤ :=
    top_unique fun x _ => Subgroup.mem_center_iff.mpr fun y => h y x
  have := hL.component.2.2.2.toNontrivial
  obtain ⟨q, hq⟩ := exists_ne (1 : ↥(barM M L) ⧸ Subgroup.center ↥(barM M L))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  exact hq ((QuotientGroup.eq_one_iff x).mpr (hZ ▸ Subgroup.mem_top x))

omit [Finite G] in
theorem isPerfect_barM (hL : IsWeakSBlock M S L) : Group.IsPerfect ↥(barM M L) :=
  Group.isPerfect_def.mpr hL.component.2.2.1

theorem card_center_alt (hL : IsWeakSBlock M S L) {m : ℕ}
    (hm7 : m ≠ 7)
    (e : ↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin m))
    (hodd : Odd (Nat.card (Subgroup.center ↥(barM M L))))
    (h3 : 3 ∣ Nat.card (Subgroup.center ↥(barM M L))) :
    Nat.card (Subgroup.center ↥(barM M L)) = 3 ∧
      Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)) := by
  have := isPerfect_barM hL
  have := hL.component.2.2.2.toNontrivial
  have hm5 : 5 ≤ m := five_le_of_isPerfect_mulEquiv_alternatingGroup e
  have hdvd := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier inferInstance
    (CFSG.GH74.Generic.centralQuotientMap e)
    (CFSG.GH74.Generic.centralQuotientMap_surjective e)
    (CFSG.GH74.Generic.centralQuotientMap_ker e).le
  rw [CFSG.GH74.Generic.centralQuotientMap_ker e,
    (CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput m hm5).2] at hdvd
  by_cases hm : m = 6 ∨ m = 7
  · rw [ite_eq_left hm] at hdvd
    have hm6 : m = 6 := by omega
    subst hm6
    refine ⟨?_, ⟨e⟩⟩
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card ↥(Subgroup.center ↥(barM M L)) = z at hdvd hodd h3 hle ⊢
    interval_cases z <;> first | rfl | (exfalso; revert hodd h3 hdvd; decide)
  · rw [ite_eq_right hm] at hdvd
    exact absurd (h3.trans hdvd) (by norm_num)

theorem nineThreeTwo_of_center (hL : IsWeakSBlock M S L)
    (h93 : NineThreeConclusion M S L) (hX : ¬ InClassXBlock L)
    (h3A6 : ¬ (Nat.card (Subgroup.center ↥(barM M L)) = 3 ∧
      Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6))))
    (hodd : Odd (Nat.card (Subgroup.center ↥(barM M L))))
    (h3 : 3 ∣ Nat.card (Subgroup.center ↥(barM M L))) : NineThreeTwo M S L := by
  have hperf := isPerfect_barM hL
  have hnab := exists_noncomm_barM hL
  have hbot : Subgroup.center ↥(barM M L) = ⊥ → False := fun hZ => by
    rw [hZ, Subgroup.card_bot] at h3
    exact absurd h3 (by norm_num)
  rcases h93 with h1 | h2 | h3' | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hX
  · exact h2
  · exact (hbot (center_eq_bot_of_isOrthogonalTwo hperf hnab h3'.2.1)).elim
  · exact (h3A6 ⟨h4.2.1, h4.2.2.1⟩).elim
  · obtain ⟨-, ⟨e⟩, -⟩ := h5
    exact (hbot (center_eq_bot_of_mulEquiv_alternating hnab e)).elim
  · obtain ⟨-, n, ⟨e⟩, -⟩ := h6
    exact (h3A6 (card_center_alt hL (by omega) e hodd h3)).elim
  · obtain ⟨-, n, ⟨e⟩, -⟩ := h7
    exact (hbot (center_eq_bot_of_mulEquiv_alternating hnab e)).elim
  · obtain ⟨-, N, r, -, -, -, -, -, ⟨e⟩, -⟩ := h8
    exact (hbot (center_eq_bot_of_mulEquiv_alternating hnab e)).elim

end CFSG.HardMathSupport.Curtis.Coordinator

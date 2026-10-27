module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.Concat
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.GroupLemmas
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction
open CFSG.EvenSporadicStandard.HSStd

variable {G : Type} [Group G]

theorem _root_.CFSG.EvenSporadicStandard.Solomon78.IsCompIn.ne_bot {M X : Subgroup G}
    (h : IsCompIn M X) : M ≠ ⊥ :=
  (Subgroup.nontrivial_iff_ne_bot M).mp
    (CFSG.LocalCores.isQuasisimple_nontrivial h.isQuasisimple)

theorem isCompIn_top_top (hG : IsSimpleGroup G) (hna : ∃ a b : G, a * b ≠ b * a) :
    IsCompIn (⊤ : Subgroup G) ⊤ := by
  haveI := hG
  refine isCompIn_of_subnormal le_top ?_ ?_
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hna).1
  · rw [Subgroup.subgroupOf_self]
    exact Subgroup.IsSubnormal.top

theorem layerIn_top_eq_top (hG : IsSimpleGroup G) (hna : ∃ a b : G, a * b ≠ b * a) :
    layerIn (⊤ : Subgroup G) = ⊤ :=
  le_antisymm le_top (Junction.le_layerIn_of_isCompIn (isCompIn_top_top hG hna))

theorem conjClosure_top_eq_top (hG : IsSimpleGroup G) {X : Subgroup G} (hX : X ≠ ⊥) :
    conjClosure X ⊤ = ⊤ := by
  have hN : (conjClosure X ⊤).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (Junction.le_normalizer_conjClosure X ⊤))
  rcases hN.isSubnormal.eq_bot_or_top_of_isSimpleGroup hG with h | h
  · exfalso
    exact hX (le_bot_iff.mp (h ▸ Junction.le_conjClosure X ⊤))
  · exact h

section Last

variable [Finite G]

theorem tLinks_top (hG : IsSimpleGroup G) (hna : ∃ a b : G, a * b ≠ b * a) {X : Subgroup G}
    {z : G} (hz : orderOf z = 2) (hX : IsCompIn X (centralizer ({z} : Set G))) :
    TLinks G 1 (seq2 X ⊤) (seq2 (⊥ ⊔ zpowers z) ⊥) (seq2 1 z) := by
  have hcen : centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
    rw [Subgroup.coe_bot, Subgroup.centralizer_eq_top_iff_subset]
    simp
  have hKc : IsCompIn X (centralizer (((⊥ : Subgroup G) ⊔ zpowers z : Subgroup G) : Set G)) := by
    rw [bot_sup_eq, centralizer_zpowers_eq]
    exact hX
  have hu : z ∈ normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp [Subgroup.mem_bot]
  have hu2 : z ^ 2 ∈ (⊥ : Subgroup G) := by
    rw [pow_two, Zassenhaus.mul_self_eq_one_of_orderOf_eq_two hz]
    exact one_mem _
  have hM : IsCompIn (⊤ : Subgroup G) (centralizer ((⊥ : Subgroup G) : Set G)) := by
    rw [hcen]
    exact isCompIn_top_top hG hna
  have hlink : (⊤ : Subgroup G) = (⊤ : Subgroup G).map (MulAut.conj z).toMonoidHom :=
    (eq_top_iff.2 fun g _ => ⟨z⁻¹ * g * z, mem_top _, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group⟩).symm
  have hle : X ≤ (⊤ : Subgroup G) ⊔ (⊤ : Subgroup G).map (MulAut.conj z).toMonoidHom :=
    le_sup_of_le_left le_top
  have hcl : (⊤ : Subgroup G) ⊔ (⊤ : Subgroup G).map (MulAut.conj z).toMonoidHom =
      conjClosure X (layerIn (centralizer ((⊥ : Subgroup G) : Set G))) := by
    rw [← hlink, sup_idem, hcen, layerIn_top_eq_top hG hna, conjClosure_top_eq_top hG hX.ne_bot]
  exact tLinks_single IsPGroup.of_bot hu hu2 hKc hM (Or.inl hlink) hle hcl

theorem exists_tLinks_extend {a : ℕ} {L T : ℕ → Subgroup G} {s : ℕ → G}
    (h : TLinks G a L T s) (hT : ∀ i ≤ a, T i ≠ ⊥) {X : Subgroup G}
    (hX : X = L a ∨ Relation.TransGen LtF (L a) X) :
    ∃ c L' T' s', TLinks G c L' T' s' ∧ L' 0 = L 0 ∧ L' c = X ∧ ∀ i ≤ c, T' i ≠ ⊥ := by
  rcases hX with rfl | hX
  · exact ⟨a, L, T, s, h, rfl, rfl, hT⟩
  · obtain ⟨b, L', T', s', h', h0, hb, hT'⟩ := chain_of_transGen_ltF hX
    exact ⟨a + b, concat a L L', concat a T T', concat a s s', h.append h' h0,
      by rw [concat_of_le (Nat.zero_le a)],
      by rw [concat_add h0 b, hb],
      forall_le_concat (P := fun x => x ≠ ⊥) hT hT'⟩

theorem exists_inCG_of_tLinks_of_isCompIn (hG : IsSimpleGroup G)
    (hna : ∃ a b : G, a * b ≠ b * a) {c : ℕ} {L T : ℕ → Subgroup G} {s : ℕ → G}
    (h : TLinks G c L T s) (hT : ∀ i ≤ c, T i ≠ ⊥) {z : G} (hz : orderOf z = 2)
    (hX : IsCompIn (L c) (centralizer ({z} : Set G))) (hstd : StdBare (L c)) :
    ∃ m U TU sU, InCG G m U TU sU ∧ U 0 = L 0 := by
  have hjoin : (seq2 (L c) ⊤) 0 = L c := seq2_zero (L c) ⊤
  have h'' := h.append (tLinks_top hG hna hz hX) hjoin
  have hL''_top : concat c L (seq2 (L c) ⊤) (c + 1) = ⊤ := by
    rw [show c + 1 = c + (0 + 1) by omega, concat_add_succ, seq2_succ]
  have hlast : ∀ i < c + 1,
      concat c L (seq2 (L c) ⊤) i ≠ concat c L (seq2 (L c) ⊤) (c + 1) := by
    intro i hi
    rw [hL''_top, concat_of_le (show i ≤ c by omega)]
    exact fun hL => hT i (by omega) (TLinks.eq_bot_of_eq_top hG hna h (by omega) hL)
  obtain ⟨b, _hb_le, hb_one, L', T', s', hlinks, hL'0, hL'b, hL'last, hinj, _hmem⟩ :=
    TLinks.exists_inj_last h'' (by omega) hlast
  have hL''_c : concat c L (seq2 (L c) ⊤) ((c + 1) - 1) = L c := by
    rw [show (c + 1) - 1 = c by omega, concat_of_le le_rfl]
  refine ⟨b, L', T', s', ?_, ?_⟩
  · refine ⟨hb_one, ?_, hinj, hlinks, ?_⟩
    · rw [hL'b, hL''_top]
    · rw [hL'last, hL''_c]
      exact hstd
  · rw [hL'0, concat_of_le (Nat.zero_le c)]

end Last

end CFSG.EvenSporadicStandard.M12Std.Rbc

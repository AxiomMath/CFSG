module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma27
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {s : G}

theorem lemma2_4_30_core (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3)
    (hcfg : A3A3 T M H S L s) :
    (∀ x ∈ T, x ∉ S → pCoreOf 2 H ⊔ conjR (pCoreOf 2 H) x = baum S ∧ baum S = thompsonJ S) ∧
    IsGamma2 M H ∧
    (∀ x ∈ T, x ∉ S → ∀ B : Subgroup G, IsMaxElemAbelian (baum S) B →
      ((∀ g ∈ S, conjR B g = B) ↔ (B = pCoreOf 2 H ∨ B = conjR (pCoreOf 2 H) x))) := by
  have hcs := hcfg.cs
  have h3 := hcfg.a3
  have hne : conjJoin S L ≠ L := hcfg.conjJoin_ne
  obtain ⟨hidx, hbJ, hJT⟩ := h27_1 G T M H S L hcs h3 hne
  have hTN : T ≤ normalizer (S : Set G) := normalizer_of_relIndex_two hcs.le_T hidx
  obtain ⟨hU0, hDab, hbD, hQ, hQmax, -, hx⟩ := hD G T M H S L hcs h3 hne T hcs.le_T le_rfl hidx
  have hQ' : pCoreOf 2 H = blockD S L ⊔ blockU0 S L := by rw [← hbD]; exact hQ
  have hHN : H ≤ normalizer (pCoreOf 2 H : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have hSH : S ≤ H := hcs.sylow.le
  refine ⟨fun x hxT hxS => ?_, ?_, fun x hxT hxS B hB => ?_⟩
  · obtain ⟨-, hbaum, -⟩ := hx x hxT hxS
    exact ⟨(C56.baum_eq_sup_conj (hTN hxT) hQ hbaum).symm, hbJ⟩
  · have hcard : Nat.card T = 2 * Nat.card S := by
      have := C5.card_eq_card_mul_relIndex hcs.le_T
      rw [hidx] at this
      omega
    exact (hcs.gamma0.isGamma2_of_card_eq_two_mul hcs.setting hcs.sylow_inf hcard).1
  ·
    obtain ⟨-, -, -, -, hiii⟩ := hx x hxT hxS
    have hxNS : x ∈ normalizer (S : Set G) := hTN hxT
    have hAB : IsMaxElemAbelian (baum S) B ↔ IsMaxElemAbelian S B :=
      isMaxElemAbelian_iff_of_thompsonJ_le inf_le_left (C5.thompsonJ_le_baum' S)
    have hSB : IsMaxElemAbelian S B := hAB.mp hB
    have hbD' : baumD S L = blockD S L := hbD
    have hQinv : ∀ g ∈ S, conjR (pCoreOf 2 H) g = pCoreOf 2 H := fun g hg =>
      C5.conjSubgroup_eq_self (hHN (hSH hg))
    have hQxinv : ∀ g ∈ S, conjR (conjR (pCoreOf 2 H) x) g = conjR (pCoreOf 2 H) x := by
      intro g hg
      have hxg : x * g * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hxNS g).mp hg
      show conjSubgroup (conjSubgroup (pCoreOf 2 H) x) g = conjSubgroup (pCoreOf 2 H) x
      rw [conjSubgroup_conjSubgroup]
      have : x * g = (x * g * x⁻¹) * x := by group
      rw [this, ← conjSubgroup_conjSubgroup]
      have := hQinv _ hxg
      rw [show conjSubgroup (pCoreOf 2 H) (x * g * x⁻¹) = pCoreOf 2 H from this]
    have hne' : conjR (pCoreOf 2 H) x ≠ pCoreOf 2 H := by
      intro h
      apply C56.not_conj_le_of_mem_diff hcs hcs.le_T le_rfl hidx hxT hxS
      have hUU0 : blockU L ≤ blockU0 S L := C56.le_conjJoin (blockU L) (one_mem S)
      have hU0Q : blockU0 S L ≤ pCoreOf 2 H := by rw [hQ]; exact le_sup_right
      have h1 : conjSubgroup (blockU L) x ≤ conjSubgroup (pCoreOf 2 H) x :=
        C5.conjSubgroup_mono (hUU0.trans hU0Q) x
      have h2 : conjSubgroup (pCoreOf 2 H) x = pCoreOf 2 H := h
      rw [h2] at h1
      exact h1
    have hQx : conjR (pCoreOf 2 H) x = baumD S L ⊔ conjR (blockU0 S L) x := by
      have hQxA : IsMaxElemAbelian S (conjR (pCoreOf 2 H) x) :=
        C56.isMaxElemAbelian_conjSubgroup hQmax hxNS
      rcases (hiii hne _ hQxA).mp hQxinv with h | h
      · exact absurd (h.trans hQ.symm) hne'
      · exact h
    constructor
    · intro hinv
      rcases (hiii hne B hSB).mp hinv with h | h
      · exact Or.inl (h.trans hQ.symm)
      · exact Or.inr (h.trans hQx.symm)
    · rintro (h | h)
      · rw [h]; exact hQinv
      · rw [h]; exact hQxinv

theorem lemma2_4_30_four (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3) (hcfg : A3A3 T M H S L s) :
    ∀ x ∈ T, x ∉ S →
      baum S ⊔ conjJoin S L = blockD S L ⊔ (conjJoin S L ⊔ conjR (blockU0 S L) x) ∧
      blockD S L ⊓ (conjJoin S L ⊔ conjR (blockU0 S L) x) = ⊥ ∧
      (∀ d ∈ blockD S L, ∀ y ∈ conjJoin S L ⊔ conjR (blockU0 S L) x, d * y = y * d) ∧
      IsElemAbelian 2 (blockD S L) := by
  intro x hxT hxS
  have hcs := hcfg.cs
  have h3 := hcfg.a3
  have hne : conjJoin S L ≠ L := hcfg.conjJoin_ne
  obtain ⟨hidx, hbJ, hJT⟩ := h27_1 G T M H S L hcs h3 hne
  have hTN : T ≤ normalizer (S : Set G) := normalizer_of_relIndex_two hcs.le_T hidx
  obtain ⟨hU0, hDab, hbD, hQ, -, -, hx⟩ := hD G T M H S L hcs h3 hne T hcs.le_T le_rfl hidx
  have hQ' : pCoreOf 2 H = blockD S L ⊔ blockU0 S L := by rw [← hbD]; exact hQ
  obtain ⟨-, hbaum, -⟩ := hx x hxT hxS
  have hbaumeq : baum S = blockD S L ⊔ (blockU0 S L ⊔ conjR (blockU0 S L) x) := by
    have h1 : baum S = baumD S L ⊔ (blockU0 S L ⊔ conjR (blockU0 S L) x) :=
      hbaum.trans (sup_assoc _ _ _)
    rw [hbD] at h1
    exact h1
  have hinf := blockD_inf_sup_conj hD hcfg hU0 hQ' hcs.le_T le_rfl hidx hxT hxS
  have hUL : blockU L ≤ L := hcfg.isA4.le
  have hU0L : blockU0 S L ≤ conjJoin S L := iSup_mono fun g => Subgroup.map_mono hUL
  have hU0S : blockU0 S L ≤ S :=
    (by rw [hQ']; exact le_sup_right : blockU0 S L ≤ pCoreOf 2 H).trans hcs.sylow.pCoreOf_le
  have hU0xS : conjSubgroup (blockU0 S L) x ≤ S :=
    (C5.conjSubgroup_mono hU0S x).trans (le_of_eq (C5.conjSubgroup_eq_self (hTN hxT)))
  have hDle : blockD S L ≤ baum S := by rw [hbaumeq]; exact le_sup_left
  have hU0xB : conjSubgroup (blockU0 S L) x ≤ baum S := by
    rw [hbaumeq]; exact (le_sup_right : _ ≤ blockU0 S L ⊔ conjR (blockU0 S L) x).trans le_sup_right
  refine ⟨?_, ?_, ?_, hbD ▸ hDab⟩
  · refine le_antisymm (sup_le ?_ (le_sup_left.trans le_sup_right)) (sup_le (hDle.trans le_sup_left) ?_)
    · rw [hbaumeq]
      exact sup_le le_sup_left (sup_le (hU0L.trans (le_sup_left.trans le_sup_right))
        (le_sup_right.trans le_sup_right))
    · exact sup_le le_sup_right (hU0xB.trans le_sup_left)
  · rw [eq_bot_iff]
    rintro t ⟨htD, htY⟩
    have hU0xN : conjSubgroup (blockU0 S L) x ≤ normalizer (conjJoin S L : Set G) := fun g hg =>
      C56.S_le_normalizer_conjJoin L (hU0xS hg)
    have htY' : t ∈ ((conjSubgroup (blockU0 S L) x ⊔ conjJoin S L : Subgroup G) : Set G) := by
      rw [sup_comm]; exact htY
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hU0xN] at htY'
    obtain ⟨a, ha, l, hl, hal0⟩ := htY'
    have hal : a * l = t := hal0
    have hlS : l ∈ S ⊓ conjJoin S L := by
      refine ⟨?_, hl⟩
      have : l = a⁻¹ * t := by rw [← hal]; group
      rw [this]
      exact S.mul_mem (S.inv_mem (hU0xS ha)) htD.1
    rw [hcfg.inf_S_L0 hU0 hU0S] at hlS
    have htY2 : t ∈ blockU0 S L ⊔ conjR (blockU0 S L) x := by
      rw [← hal]
      exact mul_mem (mem_sup_right ha) (mem_sup_left hlS)
    have : t ∈ blockD S L ⊓ (blockU0 S L ⊔ conjR (blockU0 S L) x) := ⟨htD, htY2⟩
    rw [hinf.1] at this
    exact this
  · intro d hd y hy
    have hle : conjJoin S L ⊔ conjR (blockU0 S L) x ≤ centralizer ({d} : Set G) := by
      refine sup_le (fun l hl => ?_) (fun a ha => ?_)
      · exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
          rw [Set.mem_singleton_iff] at hh
          rw [hh]
          exact (Subgroup.mem_centralizer_iff.mp hd.2 l hl).symm
      · exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
          rw [Set.mem_singleton_iff] at hh
          rw [hh]
          exact hinf.2 d hd a (mem_sup_right ha)
    exact Subgroup.mem_centralizer_iff.mp (hle hy) d (Set.mem_singleton d)

@[expose] def Lemma2_4_30Iso : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G) (s : G), A3A3 T M H S L s →
    ∀ x ∈ T, x ∉ S →
      Nonempty (↥(conjJoin S L ⊔ conjR (blockU0 S L) x) ≃*
        (Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4)))

end CFSG.QuasithinUnique.DoubleA3

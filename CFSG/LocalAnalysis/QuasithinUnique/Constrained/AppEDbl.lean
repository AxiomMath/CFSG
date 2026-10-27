module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppEPerm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellCommuting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A3A3Perm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Conj

public section

namespace CFSG.QuasithinUnique.AppE

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3 Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

structure Dbl (T M H S L : Subgroup G) (n : ℕ) (t : G) : Prop where
  hcs : ConstrainedSetting G T M H S L
  hn : 2 ≤ n
  hlin : IsLin2Type L n
  ht : t ∈ S
  hne : conjR L t ≠ L
  hjoin : conjJoin S L = L ⊔ conjR L t
  hcomm : ⁅L, conjR L t⁆ = ⊥

theorem exists_dbl (hcs : ConstrainedSetting G T M H S L) {n : ℕ} (hn : 1 < n)
    (hlin : IsLin2Type L n) (hne : conjJoin S L ≠ L) : ∃ t : G, Nonempty (Dbl T M H S L n t) := by
  rcases hcs.blocks with h | ⟨t, ht, hne', hjoin, hcomm⟩
  · exact absurd h hne
  · have e : conjR L t⁻¹ = L.map (MulAut.conj t).toMonoidHom := by simp [conjR]
    refine ⟨t⁻¹, ⟨⟨hcs, hn, hlin, S.inv_mem ht, ?_, ?_, ?_⟩⟩⟩
    · rw [e]; exact hne'
    · rw [e]; exact hjoin
    · rw [e]; exact hcomm

@[expose] def R1 (S L : Subgroup G) : Subgroup G := S ⊓ normalizer (L : Set G)

omit [Finite G] in
theorem mem_R1_iff {g : G} : g ∈ R1 S L ↔ g ∈ S ∧ conjR L g = L :=
  and_congr_right fun _ => conjSubgroup_eq_iff_mem_normalizer.symm

omit [Finite G] in
theorem R1_le_S : R1 S L ≤ S := inf_le_left

omit [Finite G] in
theorem conjR_conjR (X : Subgroup G) (g h : G) : conjR (conjR X g) h = conjR X (g * h) :=
  conjSubgroup_conjSubgroup X g h

namespace Dbl

variable {n : ℕ} {t : G} (D : Dbl T M H S L n t)
include D

theorem hL : IsShort2 L := C56.isShort D.hcs

theorem hL₂ : IsShort2 (conjR L t) := (Lin2.isShort2_conjR_iff L t).2 D.hL

theorem hlin₂ : IsLin2Type (conjR L t) n := (Lin2.isLin2Type_conjR_iff L t n).2 D.hlin

theorem comm_elem : ∀ a ∈ L, ∀ b ∈ conjR L t, a * b = b * a := by
  intro a ha b hb
  have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp D.hcomm
  exact (Subgroup.mem_centralizer_iff.mp (this ha) b hb).symm

omit [Finite G] D in
theorem L_le_K : L ≤ conjJoin S L := C56.le_conjJoin L (one_mem _)

theorem L₂_le_K : conjR L t ≤ conjJoin S L := conjR_le_conjJoin' D.ht

theorem K_le_N_L : conjJoin S L ≤ normalizer (L : Set G) := by
  rw [D.hjoin]
  exact sup_le Subgroup.le_normalizer
    (C5.le_normalizer_of_commute (fun u hu a ha => (D.comm_elem a ha u hu).symm))

theorem K_le_N_conjR {g : G} (hg : g ∈ S) :
    conjJoin S L ≤ normalizer ((conjR L g : Subgroup G) : Set G) := by
  have h1 := C5.conjSubgroup_mono D.K_le_N_L g
  rw [C5.conjSubgroup_normalizer, C5.conjSubgroup_eq_self (C56.S_le_normalizer_conjJoin L hg)]
    at h1
  exact h1

omit D in
theorem card_conjR (g : G) : Nat.card ↥(conjR L g) = Nat.card ↥L := C5.card_conjSubgroup L g

theorem conjR_cases {g : G} (hg : g ∈ S) : conjR L g = L ∨ conjR L g = conjR L t := by
  refine conjR_cases_generic D.comm_elem ?_ ?_ (card_conjR (L := L) g) (card_conjR (L := L) t)
    (fun W hWL hn => normal_le_or_eq_lin2 D.hL D.hn D.hlin hWL hn)
    (fun W hWL hn => normal_le_or_eq_lin2 D.hL₂ D.hn D.hlin₂ hWL hn)
    (fun a ha h => mem_blockQ_of_comm_lin2 D.hn D.hlin ha h)
    (fun a ha h => mem_blockQ_of_comm_lin2 D.hn D.hlin₂ ha h)
    (three_dvd_card_lin2 D.hlin)
  · rw [← D.hjoin]; exact conjR_le_conjJoin' hg
  · rw [← D.hjoin]; exact D.K_le_N_conjR hg

theorem conjR_L₂_cases {g : G} (hg : g ∈ S) :
    (conjR L g = L ∧ conjR (conjR L t) g = conjR L t) ∨
      (conjR L g = conjR L t ∧ conjR (conjR L t) g = L) := by
  have hne := D.hne
  have h2 : conjR (conjR L t) g = conjR L (t * g) := conjR_conjR L t g
  have htg : t * g ∈ S := S.mul_mem D.ht hg
  have hinv : ∀ X : Subgroup G, ∀ a : G, conjR (conjR X a) a⁻¹ = X := fun X a => by
    rw [conjR_conjR, mul_inv_cancel]; exact conjSubgroup_one _
  rcases D.conjR_cases hg with h | h
  · left
    refine ⟨h, ?_⟩
    rcases D.conjR_cases htg with h' | h'
    · exfalso
      apply hne
      have h4 : conjR L g⁻¹ = L := by
        have := hinv L g
        rwa [h] at this
      have h3 := hinv (conjR L t) g
      rw [h2, h'] at h3
      exact h3.symm.trans h4
    · rw [h2]; exact h'
  · right
    refine ⟨h, ?_⟩
    rcases D.conjR_cases htg with h' | h'
    · rw [h2]; exact h'
    · exfalso
      apply hne
      have h5 : conjR (conjR L t) g = conjR L t := by rw [h2]; exact h'
      have h6 := hinv L g
      have h7 := hinv (conjR L t) g
      rw [h5, ← h] at h7
      exact h.symm.trans (h7.symm.trans h6)

theorem conjR_eq_t_of_not_mem {g : G} (hg : g ∈ S) (hn : g ∉ R1 S L) :
    conjR L g = conjR L t := by
  rcases D.conjR_cases hg with h | h
  · exact absurd (mem_R1_iff.2 ⟨hg, h⟩) hn
  · exact h

theorem R1_le_normalizer_L₂ : R1 S L ≤ normalizer ((conjR L t : Subgroup G) : Set G) := by
  intro g hg
  rw [← conjSubgroup_eq_iff_mem_normalizer]
  have hgN := mem_R1_iff.1 hg
  rcases D.conjR_L₂_cases hgN.1 with h | h
  · exact h.2
  · exact absurd hgN.2 (by rw [h.1]; exact D.hne)

theorem R1_normal {g s : G} (hg : g ∈ S) (hs : s ∈ R1 S L) : g * s * g⁻¹ ∈ R1 S L := by
  rw [mem_R1_iff]
  refine ⟨mul_mem (mul_mem hg (R1_le_S hs)) (inv_mem hg), ?_⟩
  have hsN : conjR L s = L := (mem_R1_iff.1 hs).2
  have hsN₂ : conjR (conjR L t) s = conjR L t :=
    conjSubgroup_eq_iff_mem_normalizer.2 (D.R1_le_normalizer_L₂ hs)
  have e : conjR L (g * s * g⁻¹) = conjR (conjR (conjR L g) s) g⁻¹ := by
    rw [conjR_conjR, conjR_conjR, mul_assoc]
  have hinv : ∀ X : Subgroup G, ∀ a : G, conjR (conjR X a) a⁻¹ = X := fun X a => by
    rw [conjR_conjR, mul_inv_cancel]; exact conjSubgroup_one _
  rw [e]
  rcases D.conjR_cases hg with h | h
  · rw [h, hsN]
    have := hinv L g
    rwa [h] at this
  · rw [h, hsN₂]
    rw [← h]
    exact hinv L g

theorem t_sq_mem : t * t ∈ R1 S L := by
  rw [mem_R1_iff]
  refine ⟨S.mul_mem D.ht D.ht, ?_⟩
  rcases D.conjR_L₂_cases D.ht with h | h
  · exact absurd h.1 D.hne
  · rw [← conjR_conjR]; exact h.2

theorem relIndex_R1 : (R1 S L).relIndex S = 2 := by
  show ((R1 S L).subgroupOf S).index = 2
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨t, D.ht⟩, fun b => ?_⟩
  have hb := b.2
  show Xor (b * ⟨t, D.ht⟩ ∈ (R1 S L).subgroupOf S) (b ∈ (R1 S L).subgroupOf S)
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  by_cases hbR : (b : G) ∈ R1 S L
  · have hbN := (mem_R1_iff.1 hbR).2
    have : (b : G) * t ∉ R1 S L := by
      intro h
      have := (mem_R1_iff.1 h).2
      rw [← conjR_conjR, hbN] at this
      exact D.hne this
    exact Or.inr ⟨hbR, this⟩
  · have hbN : conjR L b = conjR L t := D.conjR_eq_t_of_not_mem hb hbR
    have : (b : G) * t ∈ R1 S L := by
      rw [mem_R1_iff]
      refine ⟨S.mul_mem hb D.ht, ?_⟩
      rw [← conjR_conjR, hbN]
      rcases D.conjR_L₂_cases D.ht with h | h
      · exact absurd h.1 D.hne
      · exact h.2
    exact Or.inl ⟨this, hbR⟩

theorem thompsonJ_le_R1 : thompsonJ S ≤ R1 S L :=
  fun _ hy => ⟨GammaExtra.thompsonJ_le_self S hy,
    C56.le_normalizer_of_commutator_eq D.hcs.thompson hy⟩

theorem pCoreOf_le_R1 : pCoreOf 2 H ≤ R1 S L := by
  intro p hp
  refine ⟨C56.pCoreOf_le_S D.hcs hp, ?_⟩
  have hLH : L ≤ H := C56.le_H D.hcs
  have hHP : H ≤ normalizer ((pCoreOf 2 H : Subgroup G) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have := Setup.Campbell.signalizer_action_ambient hLH D.hcs.block.1.2.2 D.hL.1
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H)
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H) (fun x hx => hHP (hLH hx))
  exact this.1 hp

end Dbl

end CFSG.QuasithinUnique.AppE

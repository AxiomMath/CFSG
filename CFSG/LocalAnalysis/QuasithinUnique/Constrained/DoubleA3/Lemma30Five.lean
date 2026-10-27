module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma30
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {s : G}

theorem normalizer_eq_baum (hD : AppC.C56DoubleA3)
    (hcfg : A3A3 T M H S L s) (hU0 : blockU0 S L = pCoreOf 2 (conjJoin S L))
    (hbD : baumD S L = blockD S L) (hQ : pCoreOf 2 H = blockD S L ⊔ blockU0 S L)
    (hidx : S.relIndex T = 2) :
    S ⊓ normalizer (L : Set G) = baum S ∧
      Nat.card ↥(baum S) = 4 * Nat.card ↥(pCoreOf 2 H) := by
  have hcs := hcfg.cs
  have h3 := hcfg.a3
  have hA := hcfg.isA4
  have hAs := hcfg.isA4s
  obtain ⟨z₁, z₂, hz₁1, hz₂1, hz₁C, hz₂C, R1, R2⟩ := rank1_blocks hD hcfg
  obtain ⟨hBL, -⟩ := (C56.baumann_A3_cs hcs h3).2
  have hsB : s ∈ normalizer (baum S : Set G) := mem_normalizer_baum hcfg.s_mem
  have hB2 : IsPGroup 2 (baum S) := isPGroup_baum hcs
  have hBS : baum S ≤ S := inf_le_left
  have hU0eq : blockU0 S L = blockU L ⊔ blockU2 L s := hcfg.blockU0_eq hU0
  have hUL : blockU L ≤ L := hA.le
  have hU₂Ls : blockU2 L s ≤ conjR L s := hAs.le
  have hUB : blockU L ≤ baum S := blockU_le_baum hcs h3
  have hU₂B : blockU2 L s ≤ baum S := R1.conj_le_B hsB
  have hBN : baum S ≤ S ⊓ normalizer (L : Set G) := le_inf hBS hBL
  have hNS : S ⊓ normalizer (L : Set G) ≤ S := inf_le_left
  have hNL : S ⊓ normalizer (L : Set G) ≤ normalizer (L : Set G) := inf_le_right
  have hN2 : IsPGroup 2 ↥(S ⊓ normalizer (L : Set G)) := hcs.sylow.isPGroup.to_le hNS
  have hnU : S ⊓ normalizer (L : Set G) ≤ normalizer (blockU L : Set G) := fun g hg =>
    C1.mem_normalizer_blockU hg.2
  have hNLs : S ⊓ normalizer (L : Set G) ≤ normalizer (conjR L s : Set G) := by
    intro n hn
    rcases hcfg.conj_cases hU0 (S.mul_mem hcfg.s_mem hn.1) with ⟨-, h1⟩ | ⟨-, h1⟩
    · exfalso
      have hsn : s * n ∈ normalizer (L : Set G) := conjSubgroup_eq_iff_mem_normalizer.mp h1
      have hs' : s ∈ normalizer (L : Set G) := by
        have := mul_mem hsn (inv_mem hn.2)
        simpa using this
      exact hcfg.s_ne (conjSubgroup_eq_iff_mem_normalizer.mpr hs')
    · have e : conjSubgroup (conjSubgroup L s) n = conjSubgroup L (s * n) :=
        conjSubgroup_conjSubgroup L s n
      exact conjSubgroup_eq_iff_mem_normalizer.mp (e.trans h1)
  have hnU₂ : S ⊓ normalizer (L : Set G) ≤ normalizer (blockU2 L s : Set G) := fun g hg => by
    have e : blockU2 L s = blockU (conjR L s) := (blockU_conjR L s).symm
    rw [e]
    exact C1.mem_normalizer_blockU (hNLs hg)
  have hntU : ¬ S ⊓ normalizer (L : Set G) ≤ centralizer (blockU L : Set G) := fun hle => by
    have hB' : baum S ≤ centralizer (blockU L : Set G) := hBN.trans hle
    have := R1.idx_Q
    rw [inf_of_le_left hB', Subgroup.relIndex_self] at this
    omega
  have hntU₂ : ¬ S ⊓ normalizer (L : Set G) ≤ centralizer (blockU2 L s : Set G) := fun hle => by
    have hB' : baum S ≤ centralizer (blockU2 L s : Set G) := hBN.trans hle
    have := R2.idx_Q
    rw [inf_of_le_left hB', Subgroup.relIndex_self] at this
    omega
  obtain ⟨_, _, _, hrelU, -, -, -⟩ :=
    klein_structure hA.card_U hA.sq_U (hUB.trans hBN) hnU hN2 hntU
  obtain ⟨_, _, _, hrelU₂, -, -, -⟩ :=
    klein_structure hAs.card_U hAs.sq_U (hU₂B.trans hBN) hnU₂ hN2 hntU₂
  have hrelC : ((S ⊓ normalizer (L : Set G) ⊓ centralizer (blockU L : Set G)) ⊓
      (S ⊓ normalizer (L : Set G) ⊓ centralizer (blockU2 L s : Set G))).relIndex
        (S ⊓ normalizer (L : Set G)) ≤ 4 := by
    have := Subgroup.relIndex_inf_le
      (H := S ⊓ normalizer (L : Set G) ⊓ centralizer (blockU L : Set G))
      (K := S ⊓ normalizer (L : Set G) ⊓ centralizer (blockU2 L s : Set G))
      (L := S ⊓ normalizer (L : Set G))
    rw [hrelU, hrelU₂] at this
    omega
  have hCQ : (S ⊓ normalizer (L : Set G) ⊓ centralizer (blockU L : Set G)) ⊓
      (S ⊓ normalizer (L : Set G) ⊓ centralizer (blockU2 L s : Set G)) ≤ pCoreOf 2 H := by
    rintro g ⟨⟨hgN, hgCU⟩, -, hgCU₂⟩
    obtain ⟨u₁, hu₁U, hu₁⟩ := hA.exists_inner (hNL hgN)
      (fun u hu => (Subgroup.mem_centralizer_iff.mp hgCU u hu).symm)
    obtain ⟨u₂, hu₂U, hu₂⟩ := hAs.exists_inner (hNLs hgN)
      (fun u hu => (Subgroup.mem_centralizer_iff.mp hgCU₂ u hu).symm)
    have hu₁S : u₁ ∈ S := hBS (hUB hu₁U)
    have hu₂S : u₂ ∈ S := hBS (hU₂B hu₂U)
    have hu₁L : u₁ ∈ L := hUL hu₁U
    have hu₂Ls : u₂ ∈ conjR L s := hU₂Ls hu₂U
    have hc12 : u₁ * u₂ = u₂ * u₁ := hcfg.comm_elem u₁ hu₁L u₂ hu₂Ls
    obtain ⟨d, hd⟩ : ∃ d, d = (u₁ * u₂)⁻¹ * g := ⟨_, rfl⟩
    have hinv1 : (u₁ * u₂)⁻¹ = u₂⁻¹ * u₁⁻¹ := by group
    have hinv2 : (u₁ * u₂)⁻¹ = u₁⁻¹ * u₂⁻¹ := by rw [hc12]; group
    have hdL : ∀ l ∈ L, d * l = l * d := by
      intro l hl
      have e2 : u₂⁻¹ * l = l * u₂⁻¹ := by
        have h2 : u₂ * l = l * u₂ := (hcfg.comm_elem l hl u₂ hu₂Ls).symm
        calc u₂⁻¹ * l = u₂⁻¹ * (l * u₂) * u₂⁻¹ := by group
          _ = u₂⁻¹ * (u₂ * l) * u₂⁻¹ := by rw [← h2]
          _ = l * u₂⁻¹ := by group
      calc d * l = (u₁ * u₂)⁻¹ * (g * l * g⁻¹) * g := by rw [hd]; group
        _ = (u₁ * u₂)⁻¹ * (u₁ * l * u₁⁻¹) * g := by rw [hu₁ l hl]
        _ = (u₂⁻¹ * l) * u₁⁻¹ * g := by rw [hinv1]; group
        _ = (l * u₂⁻¹) * u₁⁻¹ * g := by rw [e2]
        _ = l * d := by rw [hd, hinv1]; group
    have hdLs : ∀ l ∈ conjR L s, d * l = l * d := by
      intro l hl
      have e1 : u₁⁻¹ * l = l * u₁⁻¹ := by
        have h2 : u₁ * l = l * u₁ := hcfg.comm_elem u₁ hu₁L l hl
        calc u₁⁻¹ * l = u₁⁻¹ * (l * u₁) * u₁⁻¹ := by group
          _ = u₁⁻¹ * (u₁ * l) * u₁⁻¹ := by rw [← h2]
          _ = l * u₁⁻¹ := by group
      calc d * l = (u₁ * u₂)⁻¹ * (g * l * g⁻¹) * g := by rw [hd]; group
        _ = (u₁ * u₂)⁻¹ * (u₂ * l * u₂⁻¹) * g := by rw [hu₂ l hl]
        _ = (u₁⁻¹ * l) * u₂⁻¹ * g := by rw [hinv2]; group
        _ = (l * u₁⁻¹) * u₂⁻¹ * g := by rw [e1]
        _ = l * d := by rw [hd, hinv2]; group
    have hdS : d ∈ S := by
      rw [hd]
      exact S.mul_mem (S.inv_mem (S.mul_mem hu₁S hu₂S)) hgN.1
    have hdC : d ∈ centralizer (conjJoin S L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [hcfg.join] at hy
      have hle : L ⊔ conjR L s ≤ centralizer ({d} : Set G) := by
        refine sup_le (fun l hl => ?_) (fun l hl => ?_)
        · refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
          rw [Set.mem_singleton_iff] at hh
          rw [hh]; exact hdL l hl
        · refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
          rw [Set.mem_singleton_iff] at hh
          rw [hh]; exact hdLs l hl
      exact (Subgroup.mem_centralizer_iff.mp (hle hy) d (Set.mem_singleton d)).symm
    have hu12 : u₁ * u₂ ∈ blockU0 S L := by
      rw [hU0eq]; exact mul_mem (mem_sup_left hu₁U) (mem_sup_right hu₂U)
    have hg : g = (u₁ * u₂) * d := by rw [hd]; group
    rw [hQ, hg]
    exact mul_mem (mem_sup_right hu12) (mem_sup_left ⟨hdS, hdC⟩)
  have hcardN : Nat.card ↥(S ⊓ normalizer (L : Set G)) ≤ 4 * Nat.card ↥(pCoreOf 2 H) := by
    have h1 := C5.card_eq_card_mul_relIndex
      (inf_le_left.trans inf_le_left : ((S ⊓ normalizer (L : Set G) ⊓ centralizer (blockU L : Set G)) ⊓
        (S ⊓ normalizer (L : Set G) ⊓ centralizer (blockU2 L s : Set G))) ≤
          S ⊓ normalizer (L : Set G))
    have h2 := Subgroup.card_le_of_le hCQ
    calc Nat.card ↥(S ⊓ normalizer (L : Set G)) = _ := h1
      _ ≤ Nat.card ↥(pCoreOf 2 H) * 4 := Nat.mul_le_mul h2 hrelC
      _ = 4 * Nat.card ↥(pCoreOf 2 H) := by ring
  have hDB : blockD S L ≤ baum S := by rw [← hbD]; exact inf_le_left
  have hQB : pCoreOf 2 H ≤ baum S := by
    rw [hQ]; exact sup_le hDB (by rw [hU0eq]; exact sup_le hUB hU₂B)
  have hQC : pCoreOf 2 H ≤ centralizer (blockU L : Set G) ⊓ centralizer (blockU2 L s : Set G) :=
    pCoreOf_le_centralizer hcfg hU0 hQ
  obtain ⟨x, hxT, hxS, hc1, hc0, -, -, -⟩ := exists_good_elt hD hcfg hcs.le_T le_rfl hidx
  have hxN : x ∈ normalizer (baum S : Set G) :=
    normalizer_le_normalizer_baum S (normalizer_of_relIndex_two hcs.le_T hidx hxT)
  have hUxB : conjSubgroup (blockU L) x ≤ baum S :=
    (C5.conjSubgroup_mono hUB x).trans (le_of_eq (C5.conjSubgroup_eq_self hxN))
  have hcc : ∀ a ∈ blockU L ⊔ conjR (blockU L) x, ∀ b ∈ blockU2 L s ⊔ conjR (blockU2 L s) x,
      a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc0) ha)
      b hb).symm
  have hUxC₂ : conjSubgroup (blockU L) x ≤ centralizer (blockU2 L s : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb =>
      (hcc a (mem_sup_right ha) b (mem_sup_left hb)).symm
  have hQ₁₂ : baum S ⊓ centralizer (blockU L : Set G) ≠
      baum S ⊓ centralizer (blockU2 L s : Set G) := by
    intro heq
    have h1 : conjSubgroup (blockU L) x ≤ baum S ⊓ centralizer (blockU2 L s : Set G) :=
      le_inf hUxB hUxC₂
    rw [← heq] at h1
    exact hc1 (h1.trans inf_le_right)
  have hQeq : pCoreOf 2 H = (baum S ⊓ centralizer (blockU L : Set G)) ⊓
      (baum S ⊓ centralizer (blockU2 L s : Set G)) := by
    refine le_antisymm (fun w hw => ⟨⟨hQB hw, (hQC hw).1⟩, hQB hw, (hQC hw).2⟩) ?_
    rintro w ⟨⟨hwB, hwCU⟩, -, hwCU₂⟩
    exact hCQ ⟨⟨hBN hwB, hwCU⟩, hBN hwB, hwCU₂⟩
  have hQ₁idx : (baum S ⊓ centralizer (blockU L : Set G)).relIndex (baum S) = 2 := R1.idx_Q
  have hQ₂idx : (baum S ⊓ centralizer (blockU2 L s : Set G)).relIndex (baum S) = 2 := R2.idx_Q
  have hne1 : ((baum S ⊓ centralizer (blockU L : Set G)) ⊓
      (baum S ⊓ centralizer (blockU2 L s : Set G))).relIndex
        (baum S ⊓ centralizer (blockU L : Set G)) ≠ 1 := by
    intro h1
    have hle := Subgroup.relIndex_eq_one.mp h1
    have hQ₁Q₂ : baum S ⊓ centralizer (blockU L : Set G) ≤
        baum S ⊓ centralizer (blockU2 L s : Set G) := hle.trans inf_le_right
    have hc1' := C5.card_eq_card_mul_relIndex
      (inf_le_left : baum S ⊓ centralizer (blockU L : Set G) ≤ baum S)
    have hc2' := C5.card_eq_card_mul_relIndex
      (inf_le_left : baum S ⊓ centralizer (blockU2 L s : Set G) ≤ baum S)
    rw [hQ₁idx] at hc1'
    rw [hQ₂idx] at hc2'
    have hcard : Nat.card ↥(baum S ⊓ centralizer (blockU2 L s : Set G)) ≤
        Nat.card ↥(baum S ⊓ centralizer (blockU L : Set G)) := by omega
    exact hQ₁₂ (Subgroup.eq_of_le_of_card_ge hQ₁Q₂ hcard)
  have hpos : 0 < ((baum S ⊓ centralizer (blockU L : Set G)) ⊓
      (baum S ⊓ centralizer (blockU2 L s : Set G))).relIndex
        (baum S ⊓ centralizer (blockU L : Set G)) :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite
      (H := ((baum S ⊓ centralizer (blockU L : Set G)) ⊓
        (baum S ⊓ centralizer (blockU2 L s : Set G))).subgroupOf
          (baum S ⊓ centralizer (blockU L : Set G))))
  have hrelQ : 4 ≤ ((baum S ⊓ centralizer (blockU L : Set G)) ⊓
      (baum S ⊓ centralizer (blockU2 L s : Set G))).relIndex (baum S) := by
    have := Subgroup.relIndex_mul_relIndex
      ((baum S ⊓ centralizer (blockU L : Set G)) ⊓ (baum S ⊓ centralizer (blockU2 L s : Set G)))
      (baum S ⊓ centralizer (blockU L : Set G)) (baum S) inf_le_left inf_le_left
    rw [hQ₁idx] at this
    omega
  have hBcard : 4 * Nat.card ↥(pCoreOf 2 H) ≤ Nat.card ↥(baum S) := by
    have h1 := C5.card_eq_card_mul_relIndex hQB
    rw [hQeq] at h1 ⊢
    calc 4 * Nat.card ↥((baum S ⊓ centralizer (blockU L : Set G)) ⊓
          (baum S ⊓ centralizer (blockU2 L s : Set G)))
        = Nat.card ↥((baum S ⊓ centralizer (blockU L : Set G)) ⊓
          (baum S ⊓ centralizer (blockU2 L s : Set G))) * 4 := by ring
      _ ≤ Nat.card ↥((baum S ⊓ centralizer (blockU L : Set G)) ⊓
          (baum S ⊓ centralizer (blockU2 L s : Set G))) *
          ((baum S ⊓ centralizer (blockU L : Set G)) ⊓
          (baum S ⊓ centralizer (blockU2 L s : Set G))).relIndex (baum S) :=
        Nat.mul_le_mul_left _ hrelQ
      _ = Nat.card ↥(baum S) := h1.symm
  have hEq : S ⊓ normalizer (L : Set G) = baum S :=
    (Subgroup.eq_of_le_of_card_ge hBN (le_trans hcardN hBcard)).symm
  refine ⟨hEq, le_antisymm ?_ hBcard⟩
  calc Nat.card ↥(baum S) = Nat.card ↥(S ⊓ normalizer (L : Set G)) := by rw [hEq]
    _ ≤ 4 * Nat.card ↥(pCoreOf 2 H) := hcardN

theorem lemma2_4_30_five (hD : AppC.C56DoubleA3)
    (h27_1 : Lemma2_4_27_1A3) :
    ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G) (s : G), A3A3 T M H S L s →
      (baum S).relIndex S = 2 ∧ S = baum S ⊔ Subgroup.zpowers s ∧
        Nat.card T = 4 * Nat.card (baum S) := by
  intro G _ _ T M H S L s hcfg
  have hcs := hcfg.cs
  have hs : s ∈ S := hcfg.s_mem
  have hne : conjJoin S L ≠ L := hcfg.conjJoin_ne
  obtain ⟨hidx, -, -⟩ := h27_1 G T M H S L hcs hcfg.a3 hne
  obtain ⟨hU0, -, hbD, hQ, -, -, -⟩ := hD G T M H S L hcs hcfg.a3 hne T hcs.le_T le_rfl hidx
  have hQ' : pCoreOf 2 H = blockD S L ⊔ blockU0 S L := by rw [← hbD]; exact hQ
  have hN := (normalizer_eq_baum hD hcfg hU0 hbD hQ' hidx).1
  obtain ⟨hBL, -⟩ := (C56.baumann_A3_cs hcs hcfg.a3).2
  have hs_nB : s ∉ baum S := fun h => hcfg.s_ne (conjSubgroup_eq_iff_mem_normalizer.mpr (hBL h))
  have hdich : ∀ g ∈ S, g ∈ baum S ∨ g * s⁻¹ ∈ baum S := by
    intro g hg
    rcases hcfg.conj_cases hU0 hg with ⟨-, h1⟩ | ⟨-, h1⟩
    · left
      have : g ∈ S ⊓ normalizer (L : Set G) := ⟨hg, conjSubgroup_eq_iff_mem_normalizer.mp h1⟩
      rw [hN] at this
      exact this
    · right
      have h1' : conjSubgroup L g = conjSubgroup L s := h1
      have h2 : conjSubgroup L (g * s⁻¹) = L := by
        have := congrArg (fun A => conjSubgroup A s⁻¹) h1'
        simp only [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at this
        exact this
      have : g * s⁻¹ ∈ S ⊓ normalizer (L : Set G) :=
        ⟨S.mul_mem hg (S.inv_mem hs), conjSubgroup_eq_iff_mem_normalizer.mp h2⟩
      rw [hN] at this
      exact this
  have hS : S = baum S ⊔ Subgroup.zpowers s := by
    refine le_antisymm (fun g hg => ?_) (sup_le inf_le_left (Subgroup.zpowers_le.mpr hs))
    rcases hdich g hg with h | h
    · exact mem_sup_left h
    · have : g = (g * s⁻¹) * s := by group
      rw [this]
      exact mul_mem (mem_sup_left h) (mem_sup_right (Subgroup.mem_zpowers s))
  have hsq : s * s ∈ baum S := by
    rcases hdich (s * s) (S.mul_mem hs hs) with h | h
    · exact h
    · exfalso
      apply hs_nB
      simpa using h
  have hrel : (baum S).relIndex S = 2 := by
    show ((baum S).subgroupOf S).index = 2
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨s, hs⟩, fun b => ?_⟩
    have hmem : ∀ c : S, c ∈ (baum S).subgroupOf S ↔ (c : G) ∈ baum S := fun c => Iff.rfl
    rw [hmem, hmem]
    have hcoe : ((b * ⟨s, hs⟩ : S) : G) = (b : G) * s := rfl
    rw [hcoe]
    rcases hdich b b.2 with hb | hb
    · refine Or.inr ⟨hb, fun h => hs_nB ?_⟩
      have := mul_mem (inv_mem hb) h
      simpa using this
    · refine Or.inl ⟨?_, fun h => hs_nB ?_⟩
      · have : (b : G) * s = (b * s⁻¹) * (s * s) := by group
        rw [this]
        exact mul_mem hb hsq
      · have h2 := mul_mem (inv_mem h) hb
        have : s = ((b : G)⁻¹ * ((b : G) * s⁻¹))⁻¹ := by group
        rw [this]
        exact inv_mem h2
  have hcardS : Nat.card ↥S = Nat.card ↥(baum S) * 2 := by
    have hBS' : baum S ≤ S := inf_le_left
    have := C5.card_eq_card_mul_relIndex hBS'
    rw [hrel] at this
    exact this
  have hcardT : Nat.card ↥T = Nat.card ↥S * 2 := by
    have := C5.card_eq_card_mul_relIndex hcs.le_T
    rw [hidx] at this
    exact this
  exact ⟨hrel, hS, by omega⟩

theorem lemma2_4_30_of_iso (hD : AppC.C56DoubleA3)
    (h27_1 : Lemma2_4_27_1A3) (hiso : Lemma2_4_30Iso) : Lemma2_4_30 := by
  intro G _ _ T M H S L s hcfg
  obtain ⟨h1, h2, h3⟩ := lemma2_4_30_core hD h27_1 hcfg
  refine ⟨h1, h2, h3, fun x hxT hxS => ?_,
    lemma2_4_30_five hD h27_1 G T M H S L s hcfg⟩
  obtain ⟨a, b, c, d⟩ := lemma2_4_30_four hD h27_1 hcfg x hxT hxS
  exact ⟨a, b, c, d, hiso G T M H S L s hcfg x hxT hxS⟩

end CFSG.QuasithinUnique.DoubleA3

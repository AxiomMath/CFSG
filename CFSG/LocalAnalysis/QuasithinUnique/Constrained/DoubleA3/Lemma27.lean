module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma27A
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L2_4_27
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppDK6

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {s : G}

theorem pCoreOf_le_centralizer (hcfg : A3A3 T M H S L s)
    (hU0 : blockU0 S L = pCoreOf 2 (conjJoin S L))
    (hQ : pCoreOf 2 H = blockD S L ⊔ blockU0 S L) :
    pCoreOf 2 H ≤ centralizer (blockU L : Set G) ⊓ centralizer (blockU2 L s : Set G) := by
  have hA := hcfg.isA4
  have hAs := hcfg.isA4s
  have hUL : blockU L ≤ L := hA.le
  have hU₂Ls : blockU2 L s ≤ conjR L s := hAs.le
  have hU0eq : blockU0 S L = blockU L ⊔ blockU2 L s := hcfg.blockU0_eq hU0
  have hUL0 : blockU L ≤ conjJoin S L := by rw [hcfg.join]; exact hUL.trans le_sup_left
  have hU₂L0 : blockU2 L s ≤ conjJoin S L := by rw [hcfg.join]; exact hU₂Ls.trans le_sup_right
  have hUC₁ : blockU L ≤ centralizer (blockU L : Set G) := fun u hu =>
    Subgroup.mem_centralizer_iff.mpr fun h hh => hA.comm_U h hh u hu
  have hUC₂ : blockU L ≤ centralizer (blockU2 L s : Set G) := fun u hu =>
    Subgroup.mem_centralizer_iff.mpr fun h hh => (hcfg.comm_elem u (hUL hu) h (hU₂Ls hh)).symm
  have hU₂C₁ : blockU2 L s ≤ centralizer (blockU L : Set G) := fun u hu =>
    Subgroup.mem_centralizer_iff.mpr fun h hh => hcfg.comm_elem h (hUL hh) u (hU₂Ls hu)
  have hU₂C₂ : blockU2 L s ≤ centralizer (blockU2 L s : Set G) := fun u hu =>
    Subgroup.mem_centralizer_iff.mpr fun h hh => hAs.comm_U h hh u hu
  have hle : blockD S L ⊔ blockU0 S L ≤
      centralizer (blockU L : Set G) ⊓ centralizer (blockU2 L s : Set G) := by
    refine sup_le (fun d hd => ⟨?_, ?_⟩) ?_
    · exact Subgroup.mem_centralizer_iff.mpr fun u hu =>
        Subgroup.mem_centralizer_iff.mp hd.2 u (hUL0 hu)
    · exact Subgroup.mem_centralizer_iff.mpr fun u hu =>
        Subgroup.mem_centralizer_iff.mp hd.2 u (hU₂L0 hu)
    · rw [hU0eq]
      exact sup_le (le_inf hUC₁ hUC₂) (le_inf hU₂C₁ hU₂C₂)
  rw [hQ]; exact hle

theorem blockD_inf_sup_conj (hD : AppC.C56DoubleA3)
    (hcfg : A3A3 T M H S L s) (hU0 : blockU0 S L = pCoreOf 2 (conjJoin S L))
    (hQ : pCoreOf 2 H = blockD S L ⊔ blockU0 S L)
    {M₀ : Subgroup G} (hSM : S ≤ M₀) (hMT : M₀ ≤ T) (hidx : S.relIndex M₀ = 2)
    {x : G} (hxM : x ∈ M₀) (hxS : x ∉ S) :
    blockD S L ⊓ (blockU0 S L ⊔ conjR (blockU0 S L) x) = ⊥ ∧
      ∀ d ∈ blockD S L, ∀ y ∈ blockU0 S L ⊔ conjR (blockU0 S L) x, d * y = y * d := by
  have hcs := hcfg.cs
  have hA := hcfg.isA4
  have hAs := hcfg.isA4s
  have hxNS : x ∈ normalizer (S : Set G) := normalizer_of_relIndex_two hSM hidx hxM
  have hU0eq : blockU0 S L = blockU L ⊔ blockU2 L s := hcfg.blockU0_eq hU0
  have hUL : blockU L ≤ L := hA.le
  have hU₂Ls : blockU2 L s ≤ conjR L s := hAs.le
  have hUL0 : blockU L ≤ conjJoin S L := by rw [hcfg.join]; exact hUL.trans le_sup_left
  have hU₂L0 : blockU2 L s ≤ conjJoin S L := by rw [hcfg.join]; exact hU₂Ls.trans le_sup_right
  have hU0L : blockU0 S L ≤ conjJoin S L := by rw [hU0eq]; exact sup_le hUL0 hU₂L0
  have hSU0 : S ≤ normalizer (blockU0 S L : Set G) := C56.S_le_normalizer_conjJoin (blockU L)
  have hSU0x : S ≤ normalizer (conjSubgroup (blockU0 S L) x : Set G) := by
    intro g hg
    have hg' : x * g * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hxNS g).mp hg
    have : g ∈ conjSubgroup (normalizer (blockU0 S L : Set G)) x := by
      rw [mem_conjSubgroup_iff]; exact hSU0 hg'
    rwa [C5.conjSubgroup_normalizer] at this
  have hDQ : blockD S L ≤ pCoreOf 2 H := by rw [hQ]; exact le_sup_left
  have hUQ : blockU0 S L ≤ pCoreOf 2 H := by rw [hQ]; exact le_sup_right
  have hU0S : blockU0 S L ≤ S := hUQ.trans hcs.sylow.pCoreOf_le
  have hU0xS : conjSubgroup (blockU0 S L) x ≤ S :=
    (C5.conjSubgroup_mono hU0S x).trans (le_of_eq (C5.conjSubgroup_eq_self hxNS))
  have hDU : blockD S L ⊓ blockU0 S L = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgD, hgU⟩
    have := hcfg.center_L0 g (hU0L hgU) (fun l hl =>
      (Subgroup.mem_centralizer_iff.mp hgD.2 l hl).symm)
    rw [this]; exact one_mem _
  have hQC : ∀ w ∈ pCoreOf 2 H, w ∈ centralizer (blockU L : Set G) ∧
      w ∈ centralizer (blockU2 L s : Set G) := fun w hw => pCoreOf_le_centralizer hcfg hU0 hQ hw
  have hnormS : S ≤ normalizer (blockD S L : Set G) := fun g hg =>
    C5.mem_normalizer_inf (Subgroup.le_normalizer hg)
      (C5.mem_normalizer_centralizer (C56.S_le_normalizer_conjJoin L hg))
  have hSY : S ≤ normalizer ((blockU0 S L ⊔ conjR (blockU0 S L) x : Subgroup G) : Set G) :=
    fun g hg => C1.mem_normalizer_sup (hSU0 hg) (hSU0x hg)
  have hYS : blockU0 S L ⊔ conjR (blockU0 S L) x ≤ S := sup_le hU0S hU0xS
  have hinf : blockD S L ⊓ (blockU0 S L ⊔ conjR (blockU0 S L) x) = ⊥ := by
    rw [eq_bot_iff]
    rintro t ⟨htD, htY⟩
    have htY' : t ∈ ((blockU0 S L ⊔ conjSubgroup (blockU0 S L) x : Subgroup G) : Set G) := htY
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hU0S.trans hSU0x)] at htY'
    obtain ⟨u, hu, u', hu', htu0⟩ := htY'
    have htu : u * u' = t := htu0
    have hu'Q : u' ∈ pCoreOf 2 H := by
      have : u' = u⁻¹ * t := by rw [← htu]; group
      rw [this]
      exact mul_mem (inv_mem (hUQ hu)) (hDQ htD)
    have hu'U : u' ∈ blockU0 S L :=
      inf_conj_blockU0 hD hcfg hU0 hSM hMT hidx hxM hxS hu' (hQC u' hu'Q).1
        (hQC u' hu'Q).2
    have htU : t ∈ blockU0 S L := by rw [← htu]; exact mul_mem hu hu'U
    have : t ∈ blockD S L ⊓ blockU0 S L := ⟨htD, htU⟩
    rw [hDU] at this
    exact this
  refine ⟨hinf, fun d hd y hy => ?_⟩
  have hdS : d ∈ S := hd.1
  have hyS : y ∈ S := hYS hy
  have hc1 : d * y * d⁻¹ * y⁻¹ = 1 := by
    have h1 : d * y * d⁻¹ ∈ blockU0 S L ⊔ conjR (blockU0 S L) x :=
      (Subgroup.mem_normalizer_iff.mp (hSY hdS) y).mp hy
    have h2 : y * d⁻¹ * y⁻¹ ∈ blockD S L :=
      (Subgroup.mem_normalizer_iff.mp (hnormS hyS) d⁻¹).mp (inv_mem hd)
    have hcY : d * y * d⁻¹ * y⁻¹ ∈ blockU0 S L ⊔ conjR (blockU0 S L) x :=
      mul_mem h1 (inv_mem hy)
    have hcD : d * y * d⁻¹ * y⁻¹ ∈ blockD S L := by
      have : d * y * d⁻¹ * y⁻¹ = d * (y * d⁻¹ * y⁻¹) := by group
      rw [this]; exact mul_mem hd h2
    have : d * y * d⁻¹ * y⁻¹ ∈ blockD S L ⊓ (blockU0 S L ⊔ conjR (blockU0 S L) x) := ⟨hcD, hcY⟩
    rw [hinf] at this
    exact this
  calc d * y = (d * y * d⁻¹ * y⁻¹) * y * d := by group
    _ = y * d := by rw [hc1]; group

theorem commutator_conjJoin_eq (hcfg : A3A3 T M H S L s)
    (hU0 : blockU0 S L = pCoreOf 2 (conjJoin S L))
    {Q₁ W₁ : Subgroup G} (R1h : C5.Rank1 (baum S) Q₁ (blockU L) W₁ 2) {y : G}
    (hyNS : y ∈ normalizer (S : Set G))
    (hc1 : ¬ conjSubgroup (blockU L) y ≤ centralizer (blockU L : Set G))
    (hc2 : ¬ conjSubgroup (blockU2 L s) y ≤ centralizer (blockU2 L s : Set G)) :
    ⁅conjJoin S L, conjR (blockU0 S L) y⁆ = conjJoin S L := by
  have hcs := hcfg.cs
  have h3 := hcfg.a3
  have hA := hcfg.isA4
  have hAs := hcfg.isA4s
  have hxN : y ∈ normalizer (baum S : Set G) := normalizer_le_normalizer_baum S hyNS
  obtain ⟨hBL, -⟩ := (C56.baumann_A3_cs hcs h3).2
  have hsB : s ∈ normalizer (baum S : Set G) := mem_normalizer_baum hcfg.s_mem
  have hUB : blockU L ≤ baum S := blockU_le_baum hcs h3
  have hU2B : blockU2 L s ≤ baum S := R1h.conj_le_B hsB
  have hUxB : conjSubgroup (blockU L) y ≤ baum S :=
    (C5.conjSubgroup_mono hUB y).trans (le_of_eq (C5.conjSubgroup_eq_self hxN))
  have hU2xB : conjSubgroup (blockU2 L s) y ≤ baum S :=
    (C5.conjSubgroup_mono hU2B y).trans (le_of_eq (C5.conjSubgroup_eq_self hxN))
  have hBLs : baum S ≤ normalizer (conjR L s : Set G) := C5.le_normalizer_conj hsB hBL
  have hB2 : IsPGroup 2 (baum S) := isPGroup_baum hcs
  have hU0eq : blockU0 S L = blockU L ⊔ blockU2 L s := hcfg.blockU0_eq hU0
  have hUU0 : blockU L ≤ blockU0 S L := by rw [hU0eq]; exact le_sup_left
  have hU₂U0 : blockU2 L s ≤ blockU0 S L := by rw [hU0eq]; exact le_sup_right
  have hL1 : ⁅L, conjSubgroup (blockU L) y⁆ = L :=
    hA.commutator_eq (hB2.to_le hUxB) (fun g hg => hBL (hUxB hg))
      (fun g hg => R1h.B_le_normU (hUxB hg)) hc1
  have hL2 : ⁅conjR L s, conjSubgroup (blockU2 L s) y⁆ = conjR L s :=
    hAs.commutator_eq (hB2.to_le hU2xB) (fun g hg => hBLs (hU2xB hg))
      (fun g hg => R1h.B_le_normU_conj hsB (hU2xB hg)) hc2
  have hU0S : blockU0 S L ≤ S := by
    rw [hU0eq]
    exact sup_le (hUB.trans inf_le_left) (hU2B.trans inf_le_left)
  have hU0xS : conjSubgroup (blockU0 S L) y ≤ S :=
    (C5.conjSubgroup_mono hU0S y).trans (le_of_eq (C5.conjSubgroup_eq_self hyNS))
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro l hl a ha
    have h1 : a * l⁻¹ * a⁻¹ ∈ conjJoin S L :=
      (Subgroup.mem_normalizer_iff.mp (C56.S_le_normalizer_conjJoin L (hU0xS ha)) l⁻¹).mp
        (inv_mem hl)
    have : ⁅l, a⁆ = l * (a * l⁻¹ * a⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact mul_mem hl h1
  · rw [hcfg.join]
    refine sup_le ?_ ?_
    · calc L = ⁅L, conjSubgroup (blockU L) y⁆ := hL1.symm
        _ ≤ ⁅L ⊔ conjR L s, conjR (blockU0 S L) y⁆ :=
          Subgroup.commutator_mono le_sup_left (C5.conjSubgroup_mono hUU0 y)
    · calc conjR L s = ⁅conjR L s, conjSubgroup (blockU2 L s) y⁆ := hL2.symm
        _ ≤ ⁅L ⊔ conjR L s, conjR (blockU0 S L) y⁆ :=
          Subgroup.commutator_mono le_sup_right (C5.conjSubgroup_mono hU₂U0 y)

theorem lemma2_4_27A3
    (h27_1 : Lemma2_4_27_1A3) : Lemma2_4_27A3 := by
  intro G _ _ T M H S L hcs h3 hne
  have hD : AppC.C56DoubleA3 := AppD.c56DoubleA3
  obtain ⟨s, hcfg⟩ := exists_A3A3 hcs h3 hne
  obtain ⟨hidx, hbJ, hJT⟩ := h27_1 G T M H S L hcs h3 hne
  have hTN : T ≤ normalizer (S : Set G) := normalizer_of_relIndex_two hcs.le_T hidx
  obtain ⟨hU0, hDab, hbD, hQ, -, -, hx⟩ := hD G T M H S L hcs h3 hne T hcs.le_T le_rfl hidx
  have hQ' : pCoreOf 2 H = blockD S L ⊔ blockU0 S L := by rw [← hbD]; exact hQ
  have hUL : blockU L ≤ L := hcfg.isA4.le
  have hUbot : blockU L ≠ ⊥ := fun h => by
    have := hcfg.isA4.card_U
    rw [h, Subgroup.card_bot] at this
    omega
  have hTC : blockTC T S L = blockD S L := blockTC_eq_blockD hcs hU0 hQ hUbot hUL
  have hDab' : IsElemAbelian 2 (blockD S L) := hbD ▸ hDab
  refine ⟨⟨hidx, hbJ, hJT⟩, ?_, ?_, ?_⟩
  ·
    intro x hxT hxS r hrS hrB
    obtain ⟨-, -, hC4, -, -⟩ := AppD.c61A3Double G T M H S L hcs h3 hne
    have hxN : x ∈ normT T S := ⟨hxT, hTN hxT⟩
    obtain ⟨A₁, hA₁, hAmax⟩ := hC4 (Or.inr ⟨h3, hne⟩) x hxN hxS r hrS (by rw [← hbJ]; exact hrB)
    refine ⟨A₁, hA₁, fun B => ?_⟩
    have hJle : thompsonJ T ≤ S := hJT ▸ thompsonJ_le_self S
    exact (isMaxElemAbelian_iff_of_thompsonJ_le hcs.le_T hJle).symm.trans (hAmax B)
  ·
    rw [hTC]
    refine ⟨hDab', hQ', ?_, ?_⟩
    · rw [eq_bot_iff]
      rintro g ⟨hgD, hgU⟩
      have hU0L : blockU0 S L ≤ conjJoin S L := iSup_mono fun g => Subgroup.map_mono hUL
      have := hcfg.center_L0 g (hU0L hgU) (fun l hl =>
        (Subgroup.mem_centralizer_iff.mp hgD.2 l hl).symm)
      rw [this]; exact one_mem _
    · intro x hxT hxS
      have := (hx x hxT hxS).1
      rwa [hbD] at this
  ·
    intro x hxT hxS
    rw [hTC]
    have hx' := hx x hxT hxS
    obtain ⟨hDD, hbaum, -⟩ := hx'
    have hinf := blockD_inf_sup_conj hD hcfg hU0 hQ' hcs.le_T le_rfl hidx hxT hxS
    refine ⟨?_, hinf.1, hinf.2, ?_⟩
    · have h1 : baum S = baumD S L ⊔ (blockU0 S L ⊔ conjR (blockU0 S L) x) :=
        hbaum.trans (sup_assoc _ _ _)
      rw [hbD] at h1
      exact h1
    ·
      obtain ⟨z₁, z₂, hz₁1, hz₂1, hz₁C, hz₂C, R1, R2⟩ := rank1_blocks hD hcfg
      obtain ⟨y, hyT, hyS, hc1, -, hc2, -, -⟩ :=
        exists_good_elt hD hcfg hcs.le_T le_rfl hidx
      have hSU0 : S ≤ normalizer (blockU0 S L : Set G) := C56.S_le_normalizer_conjJoin (blockU L)
      rw [conjR_eq_of_mem_diff hcs.le_T hidx hSU0 hyT hyS hxT hxS]
      exact commutator_conjJoin_eq hcfg hU0 R1 (hTN hyT) hc1 hc2

end CFSG.QuasithinUnique.DoubleA3

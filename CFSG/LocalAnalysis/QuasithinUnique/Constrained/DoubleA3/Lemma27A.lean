module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Commutation

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {s : G}

theorem isMaxElemAbelian_iff_of_thompsonJ_le {R S' B : Subgroup G} (hRS : R ≤ S')
    (hJ : thompsonJ S' ≤ R) : IsMaxElemAbelian R B ↔ IsMaxElemAbelian S' B := by
  have hbot : IsElemAbelian 2 (⊥ : Subgroup G) :=
    C5.isElemAbelian_two_iff.mpr ⟨fun a ha b _ => by
      rw [Subgroup.mem_bot.mp ha]; simp, fun a ha => by rw [Subgroup.mem_bot.mp ha]; simp⟩
  obtain ⟨B₀, ⟨hB₀S, hB₀e⟩, hB₀max⟩ := C5.exists_max_card
    (fun X : Subgroup G => X ≤ S' ∧ IsElemAbelian 2 X) ⟨bot_le, hbot⟩
  have hB₀A : IsMaxElemAbelian S' B₀ :=
    ⟨hB₀S, hB₀e, fun B' hB' hB'e => hB₀max B' ⟨hB', hB'e⟩⟩
  have hB₀R : B₀ ≤ R :=
    (le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian S' A) => A) B₀ hB₀A).trans hJ
  constructor
  · rintro ⟨hBR, hBe, hBmax⟩
    refine ⟨hBR.trans hRS, hBe, fun B' hB' hB'e => ?_⟩
    exact (hB₀max B' ⟨hB', hB'e⟩).trans (hBmax B₀ hB₀R hB₀e)
  · rintro ⟨hBS, hBe, hBmax⟩
    have hBJ : B ≤ thompsonJ S' :=
      le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian S' A) => A) B ⟨hBS, hBe, hBmax⟩
    exact ⟨hBJ.trans hJ, hBe, fun B' hB' hB'e => hBmax B' (hB'.trans hRS) hB'e⟩

omit [Finite G] in
theorem thompsonJ_le_self (S' : Subgroup G) : thompsonJ S' ≤ S' :=
  iSup₂_le fun _ hA => hA.1

theorem blockTC_eq_blockD (hcs : ConstrainedSetting G T M H S L)
    (hU0 : blockU0 S L = pCoreOf 2 (conjJoin S L)) (hQ : pCoreOf 2 H = baumD S L ⊔ blockU0 S L)
    (hU : blockU L ≠ ⊥) (hUL : blockU L ≤ L) : blockTC T S L = blockD S L := by
  have hUQ : blockU0 S L ≤ pCoreOf 2 H := by rw [hQ]; exact le_sup_right
  have hU0S : blockU0 S L ≤ S := hUQ.trans hcs.sylow.pCoreOf_le
  have hU0bot : blockU0 S L ≠ ⊥ := fun h =>
    hU (le_bot_iff.mp ((C56.le_conjJoin (blockU L) (one_mem S)).trans h.le))
  have hHN : H ≤ normalizer (blockU0 S L : Set G) := by
    rw [hcs.eq_join]
    refine sup_le ?_ (C56.S_le_normalizer_conjJoin (blockU L))
    rw [hU0]
    exact CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _
  have e := lemma244 G T M H S L hcs (blockU0 S L) hU0bot hU0S hHN
  have hU0L : blockU0 S L ≤ conjJoin S L :=
    iSup_mono fun g => Subgroup.map_mono hUL
  refine le_antisymm ?_ ?_
  · intro g hg
    have hn : g ∈ normalizer (blockU0 S L : Set G) := by
      have hc : ∀ v ∈ blockU0 S L, g * v = v * g := fun v hv =>
        (Subgroup.mem_centralizer_iff.mp hg.2 v (hU0L hv)).symm
      rw [Subgroup.mem_normalizer_iff]
      intro u
      constructor
      · intro hu
        have := hc u hu
        have e2 : g * u * g⁻¹ = u := by rw [this]; group
        rw [e2]; exact hu
      · intro hu
        have := hc _ hu
        have e2 : u = g⁻¹ * (g * u * g⁻¹) * g := by group
        have e3 : g⁻¹ * (g * u * g⁻¹) * g = g * u * g⁻¹ := by
          calc g⁻¹ * (g * u * g⁻¹) * g = g⁻¹ * ((g * u * g⁻¹) * g) := by group
            _ = g⁻¹ * (g * (g * u * g⁻¹)) := by rw [← this]
            _ = g * u * g⁻¹ := by group
        rw [e2, e3]; exact hu
    have hgS : g ∈ S := by
      rw [← e]; exact ⟨hg.1, hn⟩
    exact ⟨hgS, hg.2⟩
  · intro g hg
    exact ⟨hcs.le_T hg.1, hg.2⟩

theorem rank1_blocks (hD : AppC.C56DoubleA3)
    (hcfg : A3A3 T M H S L s) :
    ∃ z₁ z₂ : G, z₁ ≠ 1 ∧ z₂ ≠ 1 ∧
      blockU L ⊓ centralizer (baum S : Set G) = zpowers z₁ ∧
      blockU2 L s ⊓ centralizer (baum S : Set G) = zpowers z₂ ∧
      C5.Rank1 (baum S) (baum S ⊓ centralizer (blockU L : Set G)) (blockU L) (zpowers z₁) 2 ∧
      C5.Rank1 (baum S) (baum S ⊓ centralizer (blockU2 L s : Set G)) (blockU2 L s)
        (zpowers z₂) 2 := by
  have hcs := hcfg.cs
  have h3 := hcfg.a3
  have hs := hcfg.s_mem
  have hsB : s ∈ normalizer (baum S : Set G) := mem_normalizer_baum hs
  obtain ⟨M₀, hSM, hMT, hidx⟩ := C56.exists_index_two hcs
  obtain ⟨x, hxM, hxS, hc1, -, hc2, -, -⟩ := exists_good_elt hD hcfg hSM hMT hidx
  have hxN : x ∈ normalizer (baum S : Set G) :=
    normalizer_le_normalizer_baum S (normalizer_of_relIndex_two hSM hidx hxM)
  have hUB : blockU L ≤ baum S := blockU_le_baum hcs h3
  have hUxB : conjSubgroup (blockU L) x ≤ baum S :=
    (C5.conjSubgroup_mono hUB x).trans (le_of_eq (C5.conjSubgroup_eq_self hxN))
  have hnt₁ : ¬ baum S ≤ centralizer (blockU L : Set G) := fun h => hc1 (hUxB.trans h)
  obtain ⟨z₁, hz₁U, hz₁1, hz₁C, R1⟩ := rank1_block₁ hcs h3 hnt₁
  have hU2B : blockU2 L s ≤ baum S := R1.conj_le_B hsB
  have hnt₂ : ¬ baum S ≤ centralizer (blockU2 L s : Set G) := fun h =>
    hc2 (((C5.conjSubgroup_mono hU2B x).trans (le_of_eq (C5.conjSubgroup_eq_self hxN))).trans h)
  obtain ⟨z₂, hz₂U, hz₂1, hz₂C, R2⟩ := rank1_block₂ hcs h3 hs R1 hnt₂
  exact ⟨z₁, z₂, hz₁1, hz₂1, hz₁C, hz₂C, R1, R2⟩

theorem inf_conj_blockU0 (hD : AppC.C56DoubleA3)
    (hcfg : A3A3 T M H S L s) (hU0 : blockU0 S L = pCoreOf 2 (conjJoin S L))
    {M₀ : Subgroup G} (hSM : S ≤ M₀) (hMT : M₀ ≤ T) (hidx : S.relIndex M₀ = 2)
    {x : G} (hxM : x ∈ M₀) (hxS : x ∉ S) {w : G} (hw : w ∈ conjR (blockU0 S L) x)
    (hwC₁ : w ∈ centralizer (blockU L : Set G)) (hwC₂ : w ∈ centralizer (blockU2 L s : Set G)) :
    w ∈ blockU0 S L := by
  have hcs := hcfg.cs
  obtain ⟨z₁, z₂, hz₁1, hz₂1, hz₁C, hz₂C, R1, R2⟩ := rank1_blocks hD hcfg
  obtain ⟨y, hyM, hyS, hc1, hc0, hc2, hci1, hci2⟩ := exists_good_elt hD hcfg hSM hMT hidx
  have hSU0 : S ≤ normalizer (blockU0 S L : Set G) := C56.S_le_normalizer_conjJoin (blockU L)
  have hwy : w ∈ conjR (blockU0 S L) y := by
    rw [conjR_eq_of_mem_diff hSM hidx hSU0 hxM hxS hyM hyS]; exact hw
  clear hw hxM hxS
  have hxN : y ∈ normalizer (baum S : Set G) :=
    normalizer_le_normalizer_baum S (normalizer_of_relIndex_two hSM hidx hyM)
  have hU0eq : blockU0 S L = blockU L ⊔ blockU2 L s := hcfg.blockU0_eq hU0
  have hUB : blockU L ≤ baum S := blockU_le_baum hcs hcfg.a3
  have hsB : s ∈ normalizer (baum S : Set G) := mem_normalizer_baum hcfg.s_mem
  have hU2B : blockU2 L s ≤ baum S := R1.conj_le_B hsB
  have hUxB : conjSubgroup (blockU L) y ≤ baum S :=
    (C5.conjSubgroup_mono hUB y).trans (le_of_eq (C5.conjSubgroup_eq_self hxN))
  have hU2xB : conjSubgroup (blockU2 L s) y ≤ baum S :=
    (C5.conjSubgroup_mono hU2B y).trans (le_of_eq (C5.conjSubgroup_eq_self hxN))
  have hcc : ∀ a ∈ blockU L ⊔ conjR (blockU L) y, ∀ b ∈ blockU2 L s ⊔ conjR (blockU2 L s) y,
      a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc0) ha)
      b hb).symm
  have hUxN : conjSubgroup (blockU L) y ≤ normalizer (conjSubgroup (blockU2 L s) y : Set G) :=
    C5.le_normalizer_of_commute fun a ha b hb => hcc a (mem_sup_right ha) b (mem_sup_right hb)
  have hw' : w ∈ ((conjSubgroup (blockU L) y ⊔ conjSubgroup (blockU2 L s) y : Subgroup G) :
      Set G) := by
    rw [← C5.conjSubgroup_sup]
    rw [hU0eq] at hwy
    exact hwy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hUxN] at hw'
  obtain ⟨w₁, hw₁, w₂, hw₂, hw0⟩ := hw'
  have hww : w₁ * w₂ = w := hw0
  have hw₂C₁ : w₂ ∈ centralizer (blockU L : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun u hu => hcc u (mem_sup_left hu) w₂ (mem_sup_right hw₂)
  have hw₁C₂ : w₁ ∈ centralizer (blockU2 L s : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun u hu => (hcc w₁ (mem_sup_right hw₁) u (mem_sup_left hu)).symm
  have hw₁C₁ : w₁ ∈ centralizer (blockU L : Set G) := by
    have : w₁ = w * w₂⁻¹ := by rw [← hww]; group
    rw [this]; exact mul_mem hwC₁ (inv_mem hw₂C₁)
  have hw₂C₂ : w₂ ∈ centralizer (blockU2 L s : Set G) := by
    have : w₂ = w₁⁻¹ * w := by rw [← hww]; group
    rw [this]; exact mul_mem (inv_mem hw₁C₂) hwC₂
  have hx1 : ¬ conjSubgroup (blockU L) y ≤ baum S ⊓ centralizer (blockU L : Set G) :=
    fun h => hc1 (h.trans inf_le_right)
  have hx2 : ¬ conjSubgroup (blockU L) y⁻¹ ≤ baum S ⊓ centralizer (blockU L : Set G) :=
    fun h => hci1 (h.trans inf_le_right)
  have hx1' : ¬ conjSubgroup (blockU2 L s) y ≤ baum S ⊓ centralizer (blockU2 L s : Set G) :=
    fun h => hc2 (h.trans inf_le_right)
  have hx2' : ¬ conjSubgroup (blockU2 L s) y⁻¹ ≤ baum S ⊓ centralizer (blockU2 L s : Set G) :=
    fun h => hci2 (h.trans inf_le_right)
  have hw₁U : w₁ ∈ blockU L := by
    have h1 : w₁ ∈ conjSubgroup (blockU L) y ⊓ (baum S ⊓ centralizer (blockU L : Set G)) :=
      ⟨hw₁, hUxB hw₁, hw₁C₁⟩
    rw [R1.inf_Q_conj hxN hx2, R1.conj_W hxN hx1 hx2] at h1
    exact R1.W_le_U h1
  have hw₂U : w₂ ∈ blockU2 L s := by
    have h1 : w₂ ∈ conjSubgroup (blockU2 L s) y ⊓ (baum S ⊓ centralizer (blockU2 L s : Set G)) :=
      ⟨hw₂, hU2xB hw₂, hw₂C₂⟩
    rw [R2.inf_Q_conj hxN hx2', R2.conj_W hxN hx1' hx2'] at h1
    exact R2.W_le_U h1
  rw [hU0eq, ← hww]
  exact mul_mem (mem_sup_left hw₁U) (mem_sup_right hw₂U)

end CFSG.QuasithinUnique.DoubleA3

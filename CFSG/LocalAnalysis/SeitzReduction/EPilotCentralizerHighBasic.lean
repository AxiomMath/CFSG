module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotRootSL2Basic
public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairs
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCentralizerTUBasic

public section

namespace CFSG.SeitzReduction.EPilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open scoped Pointwise

variable {τ : Tag}

@[expose] def perpNodes (τ : Tag) : Set (Fin τ.rank) := {j | j ≠ highNode τ}

theorem parabolicRoots_perpNodes : parabolicRoots τ (perpNodes τ) = perpRoots τ := by
  ext γ
  simp only [parabolicRoots, perpNodes, Set.mem_ofPred_eq, ne_eq, not_not, forall_eq]
  rfl

section Roots


theorem mem_parabolicRadicalRoots_perpNodes {α : Fin τ.rank → ℤ} :
    α ∈ parabolicRadicalRoots τ (perpNodes τ) ↔ IsRoot τ α ∧ 0 < α (highNode τ) := by
  rw [parabolicRadicalRoots, parabolicPosRoots, parabolicRoots_perpNodes]
  constructor
  · rintro ⟨⟨hα, hpos⟩, hnot⟩
    refine ⟨hα, ?_⟩
    rcases ((IsRoot.height_pos_iff hα |>.1 hpos) (highNode τ)).lt_or_eq with h | h
    · exact h
    · exact absurd ⟨⟨hα, h.symm⟩, hα, hpos⟩ hnot
  · rintro ⟨hα, hpos⟩
    have hp : 0 < height α := by
      rcases IsRoot.height_pos_or_neg hα with h | h
      · exact h
      · exact absurd ((IsRoot.height_neg_iff hα |>.1 h) (highNode τ)) (not_le.2 hpos)
    exact ⟨⟨hα, hp⟩, fun h => by
      have := h.1.2
      change α (highNode τ) = 0 at this
      omega⟩

theorem mem_parabolicRadicalRoots_perpNodes_iff_iform (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {α : Fin τ.rank → ℤ} :
    α ∈ parabolicRadicalRoots τ (perpNodes τ) ↔ IsRoot τ α ∧ 0 < iform α (highRoot τ) := by
  rw [mem_parabolicRadicalRoots_perpNodes, iform_comm, iform_highRoot hτ]

theorem smul_apply_highNode_of_smul_highRoot (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {w : WeylGroup τ} (hw : w • highRoot τ = highRoot τ) (v : Fin τ.rank → ℤ) :
    (w • v) (highNode τ) = v (highNode τ) := by
  rw [← iform_highRoot hτ (w • v), ← iform_highRoot hτ v]
  conv_lhs => rw [← hw]
  exact iform_smul w _ _

theorem mem_parabolicWeylGroup_perpNodes (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {w : WeylGroup τ}
    (hw : w • highRoot τ = highRoot τ) : w ∈ parabolicWeylGroup τ (perpNodes τ) := by
  have h : w ∈ (parabolicWeylGroup τ (perpNodes τ) : Set (WeylGroup τ)) := by
    rw [(parabolic_Weyl_coordinate_stabilizer τ (perpNodes τ)).1]
    intro v i hi
    have hi0 : i = highNode τ := by simpa [perpNodes] using hi
    subst hi0
    exact smul_apply_highNode_of_smul_highRoot hτ hw v
  exact h

theorem smul_highRoot_of_mem_parabolicWeylGroup_perpNodes (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {w : WeylGroup τ} (hw : w ∈ parabolicWeylGroup τ (perpNodes τ)) :
    w • highRoot τ = highRoot τ := by
  have hfix : ∀ v : Fin τ.rank → ℤ, (w • v) (highNode τ) = v (highNode τ) := fun v =>
    (parabolic_Weyl_coordinate_stabilizer τ (perpNodes τ)).1.subset hw v (highNode τ)
      (by simp [perpNodes])
  refine F4Pilot.smul_eq_self_of_iform_smul_single fun j => ?_
  rw [iform_highRoot hτ, iform_highRoot hτ, hfix]

end Roots

section Bruhat

variable {K : Type} [Field K]


theorem exists_conj_pinnedX_highRoot_of_mem_borelGroup {b : ModGL τ K}
    (hb : b ∈ borelGroup τ K) {c : K} (hc : c ≠ 0) :
    ∃ d : K, d ≠ 0 ∧ b * pinnedX τ K (highRoot τ) c * b⁻¹ = pinnedX τ K (highRoot τ) d := by
  have h : b * pinnedX τ K (highRoot τ) c * b⁻¹ ∈ rootSubgroup τ K (highRoot τ) := by
    rw [← map_conj_highRoot_of_mem_borelGroup hb]
    exact ⟨_, mem_rootSubgroup.2 ⟨c, rfl⟩, rfl⟩
  obtain ⟨d, hd⟩ := mem_rootSubgroup.1 h
  refine ⟨d, fun hd0 => hc ?_, hd.symm⟩
  rw [hd0, pinnedX_zero, eq_comm, mul_inv_eq_one, mul_eq_left] at hd
  exact pinnedX_injective τ K _ (hd.trans (pinnedX_zero τ K _).symm)

theorem mem_parabolicSubgroup_perpNodes_of_conj (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {g : ModGL τ K} (hg : g ∈ adjointGroup τ K) {c e : K} (hc : c ≠ 0)
    (h : g * pinnedX τ K (highRoot τ) c * g⁻¹ = pinnedX τ K (highRoot τ) e) :
    g ∈ parabolicSubgroup τ K (perpNodes τ) := by
  obtain ⟨w, hw⟩ := exists_mem_bruhatCell_of_mem_adjointGroup hg
  have hw' := hw
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hw'
  set n := canonicalRep (coxeterSystem τ) K w with hn
  obtain ⟨d, hd0, hd⟩ := exists_conj_pinnedX_highRoot_of_mem_borelGroup hb' hc
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [pinnedX_zero, mul_inv_eq_one, mul_eq_left] at h
    exact hc (pinnedX_injective τ K _ (h.trans (pinnedX_zero τ K _).symm))
  obtain ⟨e', -, he'⟩ := exists_conj_pinnedX_highRoot_of_mem_borelGroup (inv_mem hb) he0
  have hnd : n * pinnedX τ K (highRoot τ) d * n⁻¹ = pinnedX τ K (highRoot τ) e' := by
    rw [← hd, ← he', ← h]
    group
  obtain ⟨ε, hε, hεc⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w (isRoot_highRoot τ)
  rw [hn, hεc] at hnd
  have hεd : ε * d ≠ 0 := mul_ne_zero (left_ne_zero_of_mul_eq_one hε) hd0
  have hwθ := F4Pilot.eq_of_pinnedX_eq_pinnedX (IsRoot.smul (isRoot_highRoot τ) w)
    ⟨isRoot_highRoot τ, height_highRoot_pos τ⟩ hεd hnd
  have hmem : b * n * b' ∈ (parabolicSubgroup τ K (perpNodes τ) : Set (ModGL τ K)) := by
    rw [(standard_parabolic_cells τ K).1 (perpNodes τ)]
    exact Set.mem_biUnion (mem_parabolicWeylGroup_perpNodes hτ hwθ) hw
  exact hmem

end Bruhat

section TorusFix

variable {K : Type} [Field K]

theorem conj_pinnedX_highRoot_one_of_commute {h : ModGL τ K} (hh : h ∈ torusGroup τ K) {c : K}
    (hc : c ≠ 0) (hθ : h * pinnedX τ K (highRoot τ) c = pinnedX τ K (highRoot τ) c * h) :
    h * pinnedX τ K (highRoot τ) 1 * h⁻¹ = pinnedX τ K (highRoot τ) 1 := by
  have h1 := conj_pinnedX_of_mem_torusGroup hh (isRoot_highRoot τ) c
  rw [hθ, mul_inv_cancel_right] at h1
  have h2 := pinnedX_injective τ K _ h1
  have hχ : torusRootChar h (highRoot τ) = 1 := by
    have h3 : (torusRootChar h (highRoot τ) - 1) * c = 0 := by linear_combination -h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact sub_eq_zero.1 h4
    · exact absurd h4 hc
  rw [conj_pinnedX_of_mem_torusGroup hh (isRoot_highRoot τ), hχ, one_mul]

end TorusFix

section Levi

variable {K : Type} [Field K]


theorem mem_parabolicRadical_sup_rootSpan_of_commute {J : Set (Fin τ.rank)} {z : ModGL τ K}
    (hQ : ∀ q ∈ parabolicRadical τ K J, q * z = z * q)
    (hL : ∀ l ∈ rootSpan τ K (parabolicRoots τ J), l * z = z * l)
    (hH : ∀ h ∈ torusGroup τ K, h * z = z * h → h ∈ rootSpan τ K (parabolicRoots τ J))
    {g : ModGL τ K} (hgP : g ∈ parabolicSubgroup τ K J) (hgz : g * z = z * g) :
    g ∈ parabolicRadical τ K J ⊔ rootSpan τ K (parabolicRoots τ J) := by
  obtain ⟨-, -, -, -, -, -, huniq, -⟩ := parabolic_root_radical_Levi_factors τ K J
  obtain ⟨⟨q, m⟩, ⟨hq, hm, rfl⟩, -⟩ := huniq g hgP
  have hm' : m ∈ (torusGroup τ K : Set (ModGL τ K)) *
      (rootSpan τ K (parabolicRoots τ J) : Set (ModGL τ K)) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _
      (torusGroup_le_normalizer_rootSpan (fun α hα => hα.1))]
    exact F4Pilot.parabolicLevi_le_torusGroup_sup J hm
  obtain ⟨h, hh, l, hl, rfl⟩ := hm'
  have hcq : Commute q z := hQ q hq
  have hcl : Commute l z := hL l hl
  have hcg : Commute (q * (h * l)) z := hgz
  have hch : Commute h z := by
    have e : h = q⁻¹ * (q * (h * l)) * l⁻¹ := by group
    rw [e]
    exact (hcq.inv_left.mul_left hcg).mul_left hcl.inv_left
  exact mul_mem (mem_sup_left hq) (mem_sup_right (mul_mem (hH h hh hch.eq) hl))

theorem mem_perpLevi_of_mem_torusGroup_of_commute (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {h : ModGL τ K} (hh : h ∈ torusGroup τ K) {c : K} (hc : c ≠ 0)
    (hθ : h * pinnedX τ K (highRoot τ) c = pinnedX τ K (highRoot τ) c * h) :
    h ∈ rootSpan τ K (perpRoots τ) :=
  mem_perpLevi_of_mem_torusGroup hτ hh (conj_pinnedX_highRoot_one_of_commute hh hc hθ)

theorem commute_pinnedX_highRoot_of_mem_parabolicRadical {J : Set (Fin τ.rank)}
    {q : ModGL τ K} (hq : q ∈ parabolicRadical τ K J) (c : K) :
    q * pinnedX τ K (highRoot τ) c = pinnedX τ K (highRoot τ) c * q :=
  (mem_centralizer_iff.1 (posUnipotent_le_centralizer_highRoot K
    (parabolicRadical_le_posUnipotent J hq)) _ (mem_rootSubgroup.2 ⟨c, rfl⟩)).symm

theorem commute_pinnedX_highRoot_of_mem_perpLevi (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {l : ModGL τ K} (hl : l ∈ rootSpan τ K (perpRoots τ)) (c : K) :
    l * pinnedX τ K (highRoot τ) c = pinnedX τ K (highRoot τ) c * l :=
  (mem_centralizer_iff.1 (rootSpan_perpRoots_le_centralizer hτ (isRoot_highRoot τ)
    (fun _ hγ => (iform_eq_zero_of_mem_perpRoots hτ hγ).1) hl) _
      (mem_rootSubgroup.2 ⟨c, rfl⟩)).symm

end Levi

end CFSG.SeitzReduction.EPilot

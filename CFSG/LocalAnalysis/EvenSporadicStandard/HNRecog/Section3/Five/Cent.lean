module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.FiveLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.NotConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.Generic.Klein
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.Generic.Sylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCongr

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem nonempty_mulEquiv_Gxy_of_conj {G : Type} [Group G] {a ρ g : G} (hg : g * ρ * g⁻¹ = ρ) :
    Nonempty (↥(Gxy a ρ) ≃* ↥(Gxy (g * a * g⁻¹) ρ)) := by
  let φ : G ≃* G := MulAut.conj g
  have hsymm_a : φ.symm (g * a * g⁻¹) = a := by
    show g⁻¹ * (g * a * g⁻¹) * g = a
    simp [mul_assoc]
  have hsymm_ρ : φ.symm ρ = ρ := by
    show g⁻¹ * ρ * g = ρ
    calc g⁻¹ * ρ * g = g⁻¹ * (g * ρ * g⁻¹) * g := by rw [hg]
      _ = ρ := by simp [mul_assoc]
  have himage1 : φ '' ({a, ρ} : Set G) = ({g * a * g⁻¹, ρ} : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hy with hy | hy
      · left; rw [hy]; rfl
      · right; rw [hy]; exact hg
    · intro hx
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · exact ⟨a, by simp, by rw [hx]; rfl⟩
      · exact ⟨ρ, by simp, by rw [hx]; exact hg⟩
  have himage2 : φ.symm '' ({g * a * g⁻¹, ρ} : Set G) = ({a, ρ} : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hy with hy | hy
      · left; rw [hy, hsymm_a]
      · right; rw [hy, hsymm_ρ]
    · intro hx
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · exact ⟨g * a * g⁻¹, by simp, by rw [hsymm_a, hx]⟩
      · exact ⟨ρ, by simp, by rw [hsymm_ρ, hx]⟩
  have hsub : (Gxy a ρ).map (φ : G →* G) = Gxy (g * a * g⁻¹) ρ := by
    apply le_antisymm
    · refine le_trans
        (Subgroup.map_centralizer_le_centralizer_image ({a, ρ} : Set G) (φ : G →* G)) ?_
      change Subgroup.centralizer (φ '' ({a, ρ} : Set G)) ≤ Gxy (g * a * g⁻¹) ρ
      rw [himage1]
    · intro x hx
      have hle : (Gxy (g * a * g⁻¹) ρ).map (φ.symm : G →* G) ≤ Gxy a ρ := by
        refine le_trans
          (Subgroup.map_centralizer_le_centralizer_image ({g * a * g⁻¹, ρ} : Set G)
            (φ.symm : G →* G)) ?_
        change Subgroup.centralizer (φ.symm '' ({g * a * g⁻¹, ρ} : Set G)) ≤ Gxy a ρ
        rw [himage2]
      have hx' : φ.symm x ∈ Gxy a ρ :=
        hle (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
      exact Subgroup.mem_map.mpr ⟨φ.symm x, hx', by simp⟩
  exact ⟨(φ.subgroupMap (Gxy a ρ)).trans (MulEquiv.subgroupCongr hsub)⟩

theorem five_cent (hI : TwoHSInterface) {G : Type} [Group G] [Finite G] {a z : G} (h : IsF5Type a z)
    (hSyl : FiveSylowFacts a z) : FiveCentFacts a z := by
  refine { hSyl with cent_five := ?_ }
  intro ρ hρa h5 hshape t htconj htρ
  let T0 : Sylow 2 ↥(Gxy a ρ) := Sylow.nonempty.some
  obtain ⟨z', hz'z, hz'az, hT0card, hT0map, hpadic⟩ := hSyl.sylow ρ hρa h5 hshape T0
  let T' : Subgroup G := Subgroup.closure ({a, z'} : Set G)
  have hmap : (T0 : Subgroup ↥(Gxy a ρ)).map (Gxy a ρ).subtype = T' := hT0map
  have ha2 : a * a = 1 := by
    have hpow := pow_orderOf_eq_one a
    rw [h.orderOf_a] at hpow
    simpa [pow_two] using hpow
  have hz'2 : z' * z' = 1 := by
    have h2 : orderOf z' = 2 := by
      obtain ⟨c, hc⟩ := hz'z
      rw [← SemiconjBy.orderOf_eq (c : G) hc, h.orderOf_z]
    have hpow := pow_orderOf_eq_one z'
    rw [h2] at hpow
    simpa [pow_two] using hpow
  have hT'le_xy : T' ≤ Gxy a ρ := by
    rw [← hmap]
    exact Subgroup.map_subtype_le _
  have hz'mem : z' ∈ Gxy a ρ := hT'le_xy (Subgroup.subset_closure (by right; rfl))
  have hcomm : a * z' = z' * a := mem_Gx.mp (mem_Gxy.mp hz'mem).1
  have hT'card : Nat.card ↥T' = 2 ^ padicValNat 2 (Nat.card ↥(Gx ρ)) := by
    rw [hpadic, ← hmap]
    rw [← Nat.card_congr (Subgroup.equivMapOfInjective (T0 : Subgroup ↥(Gxy a ρ))
      (Gxy a ρ).subtype Subtype.coe_injective).toEquiv, hT0card]
    norm_num
  have hT'le : T' ≤ Gx ρ := by
    rw [← hmap]
    refine le_trans (Subgroup.map_subtype_le (T0 : Subgroup ↥(Gxy a ρ))) ?_
    rw [Gxy_eq_inf]
    exact inf_le_right
  have ht2 : orderOf t = 2 := by
    obtain ⟨c, hc⟩ := htconj
    rw [← SemiconjBy.orderOf_eq (c : G) hc, h.orderOf_a]
  obtain ⟨g, hgK, hwT'⟩ := exists_conj_mem_of_card_eq (p := 2) hT'le hT'card htρ ht2
  have htw : IsConj t (g⁻¹ * t * g) := isConj_iff.mpr ⟨g⁻¹, by simp⟩
  have hwa : IsConj a (g⁻¹ * t * g) := htconj.trans htw
  have hwcl : g⁻¹ * t * g ∈ Subgroup.closure ({a, z'} : Set G) := hwT'
  have hw_cases := (mem_closure_pair_iff_of_involutions (x := a) (y := z') ha2 hz'2 hcomm).mp hwcl
  have ha_ne_one : a ≠ 1 := by
    intro h1
    have h2 := h.orderOf_a
    rw [h1, orderOf_one] at h2
    norm_num at h2
  have hw_eq_a : g⁻¹ * t * g = a := by
    rcases hw_cases with h1 | h2 | h3 | h4
    · exfalso
      have : IsConj a 1 := by rwa [h1] at hwa
      exact ha_ne_one (isConj_one_left.mp this)
    · exact h2
    · exfalso
      apply not_isConj_of_isF5Type hI h
      rw [h3] at hwa
      exact hwa.trans hz'z.symm
    · exfalso
      apply not_isConj_of_isF5Type hI h
      rw [h4] at hwa
      exact hwa.trans hz'az.symm
  have ht_eq : t = g * a * g⁻¹ := by
    have hcongr := congrArg (fun x => g * x * g⁻¹) hw_eq_a
    simpa [mul_assoc] using hcongr
  have hgρ : g * ρ * g⁻¹ = ρ := by
    rw [← mem_Gx.mp hgK]
    simp [mul_assoc]
  obtain ⟨e⟩ := nonempty_mulEquiv_Gxy_of_conj (a := a) (ρ := ρ) (g := g) hgρ
  rw [ht_eq]
  exact IsShapeCentralizerFiveB.of_mulEquiv e hshape

end CFSG.EvenSporadicStandard.HNRecog.Section3

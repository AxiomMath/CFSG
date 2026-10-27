module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpTheta
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.GammaCount
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVProof.TableVBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.U35Final

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'} {α : G → G'}
  {F : Fam a α} {θ : G → G'}

theorem cp_stab_mem (h : F5Std a z) (hα : IsIsoOn (Gx a) (Gx a') α) (hθ : IsTheta a F θ) {x : G}
    (hx : IsConj a x) {g : G} (hg : g ∈ Gxy a x) : α g ∈ Gxy a' (θ x) := by
  obtain ⟨hgG, hgx⟩ := mem_Gxy.mp hg
  have hgx' : g * x * g⁻¹ = x := by
    rw [← mem_Gx.mp hgx]
    group
  have heq := IsTheta.equivariant h hθ hgG hx
  rw [hgx'] at heq
  have hcomm : θ x * α g = α g * θ x := by
    conv_lhs => rw [heq]
    group
  exact mem_Gxy.mpr ⟨hα.mem g hgG, mem_Gx.mpr hcomm⟩

theorem cp_theta_of_mem_Gx (h : F5Std a z) (hθ : IsTheta a F θ) {x : G} (hx : IsConj a x)
    (hxG : x ∈ Gx a) : θ x = α x := by
  have hx2 : orderOf x = 2 := h.orderOf_eq_two (Or.inl hx)
  have hxGxy : x ∈ Gxy a x := mem_Gxy.mpr ⟨hxG, self_mem_Gx x⟩
  calc θ x = F.app x x := hθ.eq_app x hx x ⟨hxGxy, hx2⟩
    _ = α x := F.restrict x ⟨hxG, hx2⟩ x hxGxy

theorem cp_stab_eq_of_mem_Gx (h : F5Std a z) (hα : IsIsoOn (Gx a) (Gx a') α)
    (hθ : IsTheta a F θ) {x : G} (hx : IsConj a x) (hxG : x ∈ Gx a) :
    ∀ g' ∈ Gxy a' (θ x), ∃ g ∈ Gxy a x, α g = g' := by
  have hθx : θ x = α x := cp_theta_of_mem_Gx h hθ hx hxG
  intro g' hg'
  obtain ⟨hg'a', hg'θ⟩ := mem_Gxy.mp hg'
  obtain ⟨g, hgG, hαg⟩ := hα.surjOn g' hg'a'
  have hcomm : α x * g' = g' * α x := by
    have h1 : θ x * g' = g' * θ x := mem_Gx.mp hg'θ
    rwa [hθx] at h1
  refine ⟨g, mem_Gxy.mpr ⟨hgG, mem_Gx.mpr ?_⟩, hαg⟩
  have h2 : α (g * x) = α (x * g) := by
    rw [hα.map_mul g hgG x hxG, hα.map_mul x hxG g hgG, hαg]
    exact hcomm.symm
  exact (hα.injOn (g * x) ((Gx a).mul_mem hgG hxG) (x * g) ((Gx a).mul_mem hxG hgG)
    h2).symm

theorem cp_card_dvd (h : F5Std a z) (hα : IsIsoOn (Gx a) (Gx a') α) (hθ : IsTheta a F θ) {x : G}
    (hx : IsConj a x) : Nat.card ↥(Gxy a x) ∣ Nat.card ↥(Gxy a' (θ x)) := by
  let f : ↥(Gxy a x) →* ↥(Gxy a' (θ x)) :=
    MonoidHom.mk' (fun g => ⟨α g.1, cp_stab_mem h hα hθ hx g.2⟩)
      (fun g₁ g₂ => Subtype.ext
        (hα.map_mul g₁.1 (mem_Gxy.mp g₁.2).1 g₂.1 (mem_Gxy.mp g₂.2).1))
  exact Subgroup.card_dvd_of_injective f (fun g₁ g₂ hh => Subtype.ext
    (hα.injOn g₁.1 (mem_Gxy.mp g₁.2).1 g₂.1 (mem_Gxy.mp g₂.2).1
      (congrArg Subtype.val hh)))

theorem cp_surj_of_card_le (h : F5Std a z) (hα : IsIsoOn (Gx a) (Gx a') α) (hθ : IsTheta a F θ)
    {x : G} (hx : IsConj a x)
    (hc : Nat.card ↥(Gxy a' (θ x)) ≤ Nat.card ↥(Gxy a x)) :
    ∀ g' ∈ Gxy a' (θ x), ∃ g ∈ Gxy a x, α g = g' := by
  haveI : Finite ↥(Gx a') := by
    apply Nat.finite_of_card_ne_zero
    rw [← hα.natCard_eq, card_Gx_a h]
    norm_num
  have hle : Gxy a' (θ x) ≤ Gx a' := fun g hg => (mem_Gxy.mp hg).1
  haveI : Finite ↥(Gxy a' (θ x)) :=
    Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  let f : ↥(Gxy a x) → ↥(Gxy a' (θ x)) :=
    fun g => ⟨α g.1, cp_stab_mem h hα hθ hx g.2⟩
  have hf : Function.Injective f := fun g₁ g₂ hh => Subtype.ext
    (hα.injOn g₁.1 (mem_Gxy.mp g₁.2).1 g₂.1 (mem_Gxy.mp g₂.2).1 (congrArg Subtype.val hh))
  intro g' hg'
  obtain ⟨g, hg⟩ := (hf.bijective_of_nat_card_le hc).2 ⟨g', hg'⟩
  exact ⟨g.1, g.2, congrArg Subtype.val hg⟩

theorem cp_orderOf_mul_dvd_two (h : F5Std a z) {x : G} (hx : IsConj a x) (hxG : x ∈ Gx a) :
    orderOf (a * x) ∣ 2 := by
  have hax : a * x = x * a := mem_Gx.mp hxG
  have ha2 : a ^ 2 = 1 := by rw [← h.typ.orderOf_a]; exact pow_orderOf_eq_one a
  have hx2 : x ^ 2 = 1 := by
    rw [← h.orderOf_eq_two (Or.inl hx)]; exact pow_orderOf_eq_one x
  refine orderOf_dvd_of_pow_eq_one ?_
  rw [Commute.mul_pow hax 2, ha2, hx2, mul_one]

theorem cp_vertex_cases (h : F5Std a z) {x : G} (hx : IsConj a x) :
    x ∈ Gx a ∨ (orderOf (a * x) = 3 ∧ Nat.card ↥(Gxy a x) = 5040) ∨
      (orderOf (a * x) = 4 ∧ (Nat.card ↥(Gxy a x) = 640 ∨ Nat.card ↥(Gxy a x) = 1440)) ∨
      (orderOf (a * x) = 5 ∧ ((x ∈ orb5A a a ∧ Nat.card ↥(Gxy a x) = 126000) ∨
        (x ∈ orb5E a a ∧ Nat.card ↥(Gxy a x) = 500))) ∨
      (orderOf (a * x) = 6 ∧ Nat.card ↥(Gxy a x) = 240) := by
  have hxmem : x ∈ gammaSet a z a :=
    h.loc.gamma.self.eq_gamma a x (IsConj.refl a) hx
  simp only [gammaSet, Set.mem_union, Set.mem_singleton_iff] at hxmem
  rcases hxmem with
    (((((((hxa | hx2A) | hx2B) | hx3A) | hx4A) | hx4B) | hx5A) | hx5E) | hx6A
  · rw [hxa]
    exact Or.inl (self_mem_Gx a)
  · exact Or.inl (h.mem_Gx_of_orb2A (IsConj.refl a) hx2A)
  · exact Or.inl (h.mem_Gx_of_orb2B (IsConj.refl a) hx2B)
  · refine Or.inr (Or.inl ⟨hx3A.2.1, ?_⟩)
    rw [Gxy_eq_inf]
    exact h.loc.tableVII.self.card_3A x hx3A
  · have hc : Nat.card ↥(Gxy a x) = 640 := by
      rw [Gxy_eq_inf]
      have h1 := h.loc.tableV.self.card_stab 2 x (by simpa [tab5Set] using hx4A)
      simpa using h1
    exact Or.inr (Or.inr (Or.inl ⟨tableV_orderOf_orb4A h.typ hx4A, Or.inl hc⟩))
  · have hc : Nat.card ↥(Gxy a x) = 1440 := by
      rw [Gxy_eq_inf]
      have h1 := h.loc.tableV.self.card_stab 3 x (by simpa [tab5Set] using hx4B)
      simpa using h1
    exact Or.inr (Or.inr (Or.inl ⟨tableV_orderOf_orb4B h.typ hx4B, Or.inr hc⟩))
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hx5A.2.1, Or.inl ⟨hx5A, ?_⟩⟩)))
    exact u35Facts_holds.card_eq ↥(Gxy a x) (h.loc.tableVII.self.shape_5A x hx5A)
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hx5E.2.1, Or.inr ⟨hx5E, ?_⟩⟩)))
    exact card_eq_of_isShapeFiveCubeByTwoTwo (h.loc.five.self.five_E x hx5E)
  · have hc : Nat.card ↥(Gxy a x) = 240 := by
      rw [Gxy_eq_inf]
      have h1 := h.loc.tableV.self.card_stab 4 x (by simpa [tab5Set] using hx6A)
      simpa using h1
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hx6A.2.1, hc⟩)))

theorem cp_iso_isConj_z (h : F5Std a z) (h' : F5Std a' z') (hα : IsIsoOn (Gx a) (Gx a') α)
    {t : G} (htG : t ∈ Gx a) (htz : IsConj z t) : IsConj z' (α t) := by
  have ht2 : orderOf t = 2 := h.orderOf_eq_two (Or.inr htz)
  rcases inv_cover h ⟨htG, ht2⟩ with hta | ht2A | ht2B | ht2AB | ht2BB
  · exfalso
    exact h.not_isConj ((hta ▸ htz).symm)
  · exfalso
    exact h.not_isConj (ht2A.1.trans htz.symm)
  · exfalso
    exact h.not_isConj (ht2B.1.trans htz.symm)
  · exact (typing_2AB h h' hα ht2AB).1
  · exact (typing_2BB h h' hα ht2BB).1

theorem cp_five_E_not_five_A (h : F5Std a z) (h' : F5Std a' z') (hα : IsIsoOn (Gx a) (Gx a') α)
    (hθ : IsTheta a F θ) {x : G} (hx : x ∈ orb5E a a) (hθx : θ x ∈ orb5A a' a') : False := by
  obtain ⟨t, t', -, htz, -, -, ht'Gxy, -⟩ := h.loc.five.self.klein_E x hx
  have hxconj : IsConj a x := hx.1.1
  have ht'G : t' ∈ Gx a := (mem_Gxy.mp ht'Gxy).1
  have hαt'Gxy : α t' ∈ Gxy a' (θ x) := cp_stab_mem h hα hθ hxconj ht'Gxy
  have ht'2 : orderOf t' = 2 := h.orderOf_eq_two (Or.inr htz)
  have hαt'2 : orderOf (α t') = 2 := (hα.orderOf_eq ht'G).trans ht'2
  have hfiveA := (h'.loc.lines.self.five_A (θ x) hθx).2
  have hmem : α t' ∈ {u | u ∈ Gxy a' (θ x) ∧ orderOf u = 2} := ⟨hαt'Gxy, hαt'2⟩
  have h2B : α t' ∈ orb2B a' z' a' ∩ orb2B a' z' (θ x) := by
    rwa [hfiveA] at hmem
  have hA' : IsConj a' (α t') := ((Set.mem_inter_iff (α t') _ _).mp h2B).1.1
  have hz' : IsConj z' (α t') := cp_iso_isConj_z h h' hα ht'G htz
  exact h'.not_isConj (hA'.trans hz'.symm)

private theorem cp_not_dvd_two_of_not_mem (h : F5Std a z) {x : G} (hx : IsConj a x)
    (hxG : x ∉ Gx a) : ¬ orderOf (a * x) ∣ 2 := by
  intro hd
  have h2 : (a * x) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hd
  have h1 : (a * x)⁻¹ = a * x :=
    inv_eq_of_mul_eq_one_right (by rwa [pow_two] at h2)
  have ha : a⁻¹ = a := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_two, ← h.typ.orderOf_a]
    exact pow_orderOf_eq_one a
  have hx' : x⁻¹ = x := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_two, ← h.orderOf_eq_two (Or.inl hx)]
    exact pow_orderOf_eq_one x
  rw [mul_inv_rev, ha, hx'] at h1
  exact hxG (mem_Gx.mpr h1.symm)

private theorem cp_card_le_of_not_mem (h : F5Std a z) (h' : F5Std a' z')
    (hα : IsIsoOn (Gx a) (Gx a') α) (hθ : IsTheta a F θ) {x : G}
    (hx : IsConj a x) (hxG : x ∉ Gx a) :
    Nat.card ↥(Gxy a' (θ x)) ≤ Nat.card ↥(Gxy a x) := by
  have hθx : IsConj a' (θ x) := IsTheta.typed h h' hα hθ hx
  have hord : orderOf (a' * θ x) = orderOf (a * x) := IsTheta.orderOf_mul h h' hα hθ hx
  have hdvd : Nat.card ↥(Gxy a x) ∣ Nat.card ↥(Gxy a' (θ x)) := cp_card_dvd h hα hθ hx
  have hnot : θ x ∉ Gx a' := fun hθxG =>
    cp_not_dvd_two_of_not_mem h hx hxG (hord ▸ cp_orderOf_mul_dvd_two h' hθx hθxG)
  rcases cp_vertex_cases h hx with hxg | h3 | h4 | h5 | h6
  · exact absurd hxg hxG
  · rcases cp_vertex_cases h' hθx with hθxg | h3' | h4' | h5' | h6'
    · exact absurd hθxg hnot
    · exact le_of_eq (h3'.2.trans h3.2.symm)
    · omega
    · omega
    · omega
  · rcases h4.2 with hc4 | hc4
    · rcases cp_vertex_cases h' hθx with hθxg | h3' | h4' | h5' | h6'
      · exact absurd hθxg hnot
      · omega
      · rcases h4'.2 with hc4' | hc4'
        · exact le_of_eq (hc4'.trans hc4.symm)
        · rw [hc4, hc4'] at hdvd
          norm_num at hdvd
      · omega
      · omega
    · rcases cp_vertex_cases h' hθx with hθxg | h3' | h4' | h5' | h6'
      · exact absurd hθxg hnot
      · omega
      · rcases h4'.2 with hc4' | hc4'
        · rw [hc4, hc4'] at hdvd
          norm_num at hdvd
        · exact le_of_eq (hc4'.trans hc4.symm)
      · omega
      · omega
  · rcases h5.2 with ⟨hx5A, hc5⟩ | ⟨hx5E, hc5⟩
    · rcases cp_vertex_cases h' hθx with hθxg | h3' | h4' | h5' | h6'
      · exact absurd hθxg hnot
      · omega
      · omega
      · rcases h5'.2 with ⟨hθx5A, hc5'⟩ | ⟨hθx5E, hc5'⟩
        · exact le_of_eq (hc5'.trans hc5.symm)
        · rw [hc5, hc5'] at hdvd
          norm_num at hdvd
      · omega
    · rcases cp_vertex_cases h' hθx with hθxg | h3' | h4' | h5' | h6'
      · exact absurd hθxg hnot
      · omega
      · omega
      · rcases h5'.2 with ⟨hθx5A, hc5'⟩ | ⟨hθx5E, hc5'⟩
        · exact (cp_five_E_not_five_A h h' hα hθ hx5E hθx5A).elim
        · exact le_of_eq (hc5'.trans hc5.symm)
      · omega
  · rcases cp_vertex_cases h' hθx with hθxg | h3' | h4' | h5' | h6'
    · exact absurd hθxg hnot
    · omega
    · omega
    · omega
    · exact le_of_eq (h6'.2.trans h6.2.symm)

theorem cp_stab_eq (h : F5Std a z) (h' : F5Std a' z') (hα : IsIsoOn (Gx a) (Gx a') α)
    (hθ : IsTheta a F θ) {x : G} (hx : IsConj a x) :
    (∀ g ∈ Gxy a x, α g ∈ Gxy a' (θ x)) ∧ ∀ g' ∈ Gxy a' (θ x), ∃ g ∈ Gxy a x, α g = g' := by
  refine ⟨fun g hg => cp_stab_mem h hα hθ hx hg, ?_⟩
  intro g' hg'
  by_cases hxG : x ∈ Gx a
  · exact cp_stab_eq_of_mem_Gx h hα hθ hx hxG g' hg'
  · exact cp_surj_of_card_le h hα hθ hx
      (cp_card_le_of_not_mem h h' hα hθ hx hxG) g' hg'

theorem cp_theta_injOn (h : F5Std a z) (h' : F5Std a' z') (hα : IsIsoOn (Gx a) (Gx a') α)
    (hθ : IsTheta a F θ) {x y : G} (hx : IsConj a x) (hy : IsConj a y) (hxy : θ x = θ y) :
    x = y := by
  have hθx : IsConj a' (θ x) := IsTheta.typed h h' hα hθ hx
  obtain ⟨t', ht'inv⟩ := exists_inv_vertex h' hθx
  have ht'Gxy : t' ∈ Gxy a' (θ x) := ht'inv.1
  have ht'2 : orderOf t' = 2 := ht'inv.2
  have ht'Gxy_y : t' ∈ Gxy a' (θ y) := by
    rw [← hxy]
    exact ht'Gxy
  obtain ⟨t, htGxy, hαt⟩ := (cp_stab_eq h h' hα hθ hx).2 t' ht'Gxy
  obtain ⟨s, hsGxy, hαs⟩ := (cp_stab_eq h h' hα hθ hy).2 t' ht'Gxy_y
  have htG : t ∈ Gx a := (mem_Gxy.mp htGxy).1
  have hsG : s ∈ Gx a := (mem_Gxy.mp hsGxy).1
  have hts : t = s := hα.injOn t htG s hsG (hαt.trans hαs.symm)
  have hαt2 : orderOf (α t) = 2 := by
    rw [hαt]
    exact ht'2
  have ht2 : orderOf t = 2 := (hα.orderOf_eq htG).symm.trans hαt2
  have htGy : t ∈ Gx y := hts ▸ (mem_Gxy.mp hsGxy).2
  have hxt : x ∈ Gx t := mem_Gx.mpr (mem_Gx.mp (mem_Gxy.mp htGxy).2).symm
  have hyt : y ∈ Gx t := mem_Gx.mpr (mem_Gx.mp htGy).symm
  have htInvx : t ∈ InvIn (Gxy a x) := ⟨htGxy, ht2⟩
  have htInvy : t ∈ InvIn (Gxy a y) := ⟨mem_Gxy.mpr ⟨htG, htGy⟩, ht2⟩
  have hadj : F.app t x = F.app t y :=
    (hθ.eq_app x hx t htInvx).symm.trans (hxy.trans (hθ.eq_app y hy t htInvy))
  exact (F.iso t ⟨htG, ht2⟩).injOn x hxt y hyt hadj

end CFSG.EvenSporadicStandard.HNRecog.Section4

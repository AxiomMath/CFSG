module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1921Perm
public import CFSG.LocalAnalysis.GL83PartI.I_23_1

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95I1921

open Equiv Equiv.Perm

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem exists_restrict {U : Finset Ω} {g : Perm Ω} (hU : ∀ x, x ∉ U → g x = x) :
    ∃ σ : Perm ↥U, Perm.ofSubtype σ = g ∧
      ∀ (x : Ω) (hx : x ∈ U), ((σ ⟨x, hx⟩ : ↥U) : Ω) = g x := by
  have h₁ : ∀ x, g x ∈ U ↔ x ∈ U := by
    intro x
    constructor
    · intro hgx
      by_contra hx
      rw [hU x hx] at hgx
      exact hx hgx
    · intro hx
      by_contra hgx
      have h : g (g x) = g x := hU _ hgx
      have : g x = x := g.injective h
      rw [this] at hgx
      exact hgx hx
  refine ⟨g.subtypePerm h₁, Perm.ofSubtype_subtypePerm h₁ fun x hx => ?_, fun x hx => rfl⟩
  by_contra hxU
  exact hx (hU x hxU)

theorem mem_of_alternatingGroup_le {U : Finset Ω} {A : Subgroup (Perm Ω)}
    (h : alternatingGroup ↥U ≤ A.comap (Perm.ofSubtype : Perm ↥U →* Perm Ω)) {g : Perm Ω}
    (hg : sign g = 1) (hU : ∀ x, x ∉ U → g x = x) : g ∈ A := by
  obtain ⟨σ, hσ, -⟩ := exists_restrict hU
  have hσs : sign σ = 1 := by
    rw [← Perm.sign_ofSubtype σ, hσ]
    exact hg
  have := h (Perm.mem_alternatingGroup.2 hσs)
  rwa [Subgroup.mem_comap, hσ] at this

theorem isDT_swap_mul_swap {F : Finset Ω} {p q r t : Ω}
    (hF : ∀ x, x ∈ F ↔ x = p ∨ x = q ∨ x = r ∨ x = t)
    (hpq : p ≠ q) (hpr : p ≠ r) (hpt : p ≠ t) (hqr : q ≠ r) (hqt : q ≠ t) (hrt : r ≠ t) :
    IsDT F (swap p q * swap r t) := by
  refine ⟨fun x hx => ?_, ?_, fun x hx => ?_⟩
  · rw [hF] at hx
    grind [Perm.mul_apply]
  · have hc : Commute (swap p q) (swap r t) :=
      (Perm.disjoint_swap_swap (by simp [hpq, hpr, hpt, hqr, hqt, hrt])).commute
    rw [hc.symm.mul_mul_mul_comm, swap_mul_self, swap_mul_self, mul_one]
  · rw [hF] at hx
    grind [Perm.mul_apply]

theorem exists_seven_points {F₁ F₂ : Finset Ω} (h1 : F₁.card = 4) (h2 : F₂.card = 4)
    (hz : (F₁ ∩ F₂).card = 1) :
    ∃ z a b c d e f : Ω, F₁ = {z, a, b, c} ∧ F₂ = {z, d, e, f} ∧
      z ≠ a ∧ z ≠ b ∧ z ≠ c ∧ z ≠ d ∧ z ≠ e ∧ z ≠ f ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ a ≠ f ∧
      b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ b ≠ f ∧ c ≠ d ∧ c ≠ e ∧ c ≠ f ∧ d ≠ e ∧ d ≠ f ∧ e ≠ f := by
  obtain ⟨z, hzI⟩ := Finset.card_eq_one.1 hz
  have hzmem : z ∈ F₁ ∩ F₂ := by rw [hzI]; exact Finset.mem_singleton_self z
  have hz1 : z ∈ F₁ := (Finset.mem_inter.1 hzmem).1
  have hz2 : z ∈ F₂ := (Finset.mem_inter.1 hzmem).2
  have hc1 : (F₁.erase z).card = 3 := by rw [Finset.card_erase_of_mem hz1, h1]
  have hc2 : (F₂.erase z).card = 3 := by rw [Finset.card_erase_of_mem hz2, h2]
  obtain ⟨a, b, c, hab, hac, hbc, hE1⟩ := Finset.card_eq_three.1 hc1
  obtain ⟨d, e, f, hde, hdf, hef, hE2⟩ := Finset.card_eq_three.1 hc2
  have hF1 : F₁ = {z, a, b, c} := by rw [← Finset.insert_erase hz1, hE1]
  have hF2 : F₂ = {z, d, e, f} := by rw [← Finset.insert_erase hz2, hE2]
  have hdisj : Disjoint (F₁.erase z) (F₂.erase z) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have hx : x ∈ F₁ ∩ F₂ := Finset.mem_inter.2 ⟨Finset.mem_of_mem_erase hx1,
      Finset.mem_of_mem_erase hx2⟩
    rw [hzI, Finset.mem_singleton] at hx
    exact Finset.ne_of_mem_erase hx1 hx
  rw [hE1, hE2] at hdisj
  have hza : z ≠ a := fun h => Finset.ne_of_mem_erase (hE1 ▸ by simp : a ∈ F₁.erase z) h.symm
  have hzb : z ≠ b := fun h => Finset.ne_of_mem_erase (hE1 ▸ by simp : b ∈ F₁.erase z) h.symm
  have hzc : z ≠ c := fun h => Finset.ne_of_mem_erase (hE1 ▸ by simp : c ∈ F₁.erase z) h.symm
  have hzd : z ≠ d := fun h => Finset.ne_of_mem_erase (hE2 ▸ by simp : d ∈ F₂.erase z) h.symm
  have hze : z ≠ e := fun h => Finset.ne_of_mem_erase (hE2 ▸ by simp : e ∈ F₂.erase z) h.symm
  have hzf : z ≠ f := fun h => Finset.ne_of_mem_erase (hE2 ▸ by simp : f ∈ F₂.erase z) h.symm
  simp only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left, Finset.mem_insert,
    Finset.mem_singleton, not_or] at hdisj
  obtain ⟨⟨had, hae, haf⟩, ⟨hbd, hbe, hbf⟩, hcd, hce, hcf⟩ := hdisj
  exact ⟨z, a, b, c, d, e, f, hF1, hF2, hza, hzb, hzc, hzd, hze, hzf, hab, hac, had, hae, haf, hbc,
    hbd, hbe, hbf, hcd, hce, hcf, hde, hdf, hef⟩

theorem sq_swap_mul_swap {z a b c d e f : Ω} (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c)
    (hzd : z ≠ d) (hze : z ≠ e) (hzf : z ≠ f) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hae : a ≠ e) (haf : a ≠ f) (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f) (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f) :
    (swap z a * swap b c * (swap z d * swap e f)) ^ 2 = swap z d * swap z a := by
  set s : Perm Ω := swap z a * swap b c * (swap z d * swap e f) with hs
  have hsz : s z = d := by grind [Perm.mul_apply]
  have hsa : s a = z := by grind [Perm.mul_apply]
  have hsd : s d = a := by grind [Perm.mul_apply]
  have hsb : s b = c := by grind [Perm.mul_apply]
  have hsc : s c = b := by grind [Perm.mul_apply]
  have hse : s e = f := by grind [Perm.mul_apply]
  have hsf : s f = e := by grind [Perm.mul_apply]
  have hso : ∀ x, x ≠ z → x ≠ a → x ≠ b → x ≠ c → x ≠ d → x ≠ e → x ≠ f → s x = x := by
    intro x h1 h2 h3 h4 h5 h6 h7
    grind [Perm.mul_apply]
  ext x
  rw [pow_two, Perm.mul_apply]
  by_cases h1 : x = z
  · rw [h1, hsz, hsd]
    grind [Perm.mul_apply]
  by_cases h2 : x = a
  · rw [h2, hsa, hsz]
    grind [Perm.mul_apply]
  by_cases h3 : x = b
  · rw [h3, hsb, hsc]
    grind [Perm.mul_apply]
  by_cases h4 : x = c
  · rw [h4, hsc, hsb]
    grind [Perm.mul_apply]
  by_cases h5 : x = d
  · rw [h5, hsd, hsa]
    grind [Perm.mul_apply]
  by_cases h6 : x = e
  · rw [h6, hse, hsf]
    grind [Perm.mul_apply]
  by_cases h7 : x = f
  · rw [h7, hsf, hse]
    grind [Perm.mul_apply]
  rw [hso x h1 h2 h3 h4 h5 h6 h7, hso x h1 h2 h3 h4 h5 h6 h7]
  grind [Perm.mul_apply]

theorem alternatingGroup_le_comap_of_inter_one {F₁ F₂ : Finset Ω} (h1 : F₁.card = 4)
    (h2 : F₂.card = 4) (hz : (F₁ ∩ F₂).card = 1) {A : Subgroup (Perm Ω)}
    (hA1 : ∀ s, IsDT F₁ s → s ∈ A) (hA2 : ∀ s, IsDT F₂ s → s ∈ A) :
    alternatingGroup ↥(F₁ ∪ F₂) ≤
      A.comap (Perm.ofSubtype : Perm ↥(F₁ ∪ F₂) →* Perm Ω) := by
  obtain ⟨z, a, b, c, d, e, f, hF1, hF2, hza, hzb, hzc, hzd, hze, hzf, hab, hac, had, hae, haf,
    hbc, hbd, hbe, hbf, hcd, hce, hcf, hde, hdf, hef⟩ := exists_seven_points h1 h2 hz
  have hm1 : ∀ x, x ∈ F₁ ↔ x = z ∨ x = a ∨ x = b ∨ x = c := by
    intro x
    rw [hF1]
    simp
  have hm2 : ∀ x, x ∈ F₂ ↔ x = z ∨ x = d ∨ x = e ∨ x = f := by
    intro x
    rw [hF2]
    simp
  have hmU : ∀ x, x ∈ F₁ ∪ F₂ ↔ x = z ∨ x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e ∨ x = f := by
    intro x
    rw [Finset.mem_union, hm1, hm2]
    tauto
  have dtA : IsDT F₁ (swap z a * swap b c) :=
    isDT_swap_mul_swap hm1 hza hzb hzc hab hac hbc
  have dtB : IsDT F₁ (swap z b * swap a c) :=
    isDT_swap_mul_swap (fun x => by rw [hm1]; tauto) hzb hza hzc hab.symm hbc hac
  have dtC : IsDT F₁ (swap z c * swap a b) :=
    isDT_swap_mul_swap (fun x => by rw [hm1]; tauto) hzc hza hzb hac.symm hbc.symm hab
  have dtD : IsDT F₂ (swap z d * swap e f) :=
    isDT_swap_mul_swap hm2 hzd hze hzf hde hdf hef
  have dtE : IsDT F₂ (swap z e * swap d f) :=
    isDT_swap_mul_swap (fun x => by rw [hm2]; tauto) hze hzd hzf hde.symm hef hdf
  have dtF : IsDT F₂ (swap z f * swap d e) :=
    isDT_swap_mul_swap (fun x => by rw [hm2]; tauto) hzf hzd hze hdf.symm hef.symm hde
  set U := F₁ ∪ F₂
  set B := A.comap (Perm.ofSubtype : Perm ↥U →* Perm Ω) with hB
  have hzU : z ∈ U := (hmU z).2 (Or.inl rfl)
  have hfix1 : ∀ s, IsDT F₁ s → ∀ x, x ∉ U → s x = x := fun s hs x hx =>
    hs.1 x fun hxF => hx (Finset.mem_union_left _ hxF)
  have hfix2 : ∀ s, IsDT F₂ s → ∀ x, x ∉ U → s x = x := fun s hs x hx =>
    hs.1 x fun hxF => hx (Finset.mem_union_right _ hxF)
  have key : ∀ {s : Perm Ω}, s ∈ A → (∀ x, x ∉ U → s x = x) → ∀ y : ↥U, s z = (y : Ω) →
      ∃ g : B, g • (⟨z, hzU⟩ : ↥U) = y := by
    intro s hs hsU y hy
    obtain ⟨σ, hσ, hσx⟩ := exists_restrict hsU
    refine ⟨⟨σ, by rw [hB, Subgroup.mem_comap, hσ]; exact hs⟩, Subtype.ext ?_⟩
    show ((σ ⟨z, hzU⟩ : ↥U) : Ω) = y
    rw [hσx z hzU, hy]
  have hpre : MulAction.IsPretransitive ↥B ↥U := by
    rw [MulAction.isPretransitive_iff_base (⟨z, hzU⟩ : ↥U)]
    intro y
    rcases (hmU y.1).1 y.2 with h | h | h | h | h | h | h
    · exact ⟨1, Subtype.ext (by simp [h])⟩
    · exact key (hA1 _ dtA) (hfix1 _ dtA) y (by grind [Perm.mul_apply])
    · exact key (hA1 _ dtB) (hfix1 _ dtB) y (by grind [Perm.mul_apply])
    · exact key (hA1 _ dtC) (hfix1 _ dtC) y (by grind [Perm.mul_apply])
    · exact key (hA2 _ dtD) (hfix2 _ dtD) y (by grind [Perm.mul_apply])
    · exact key (hA2 _ dtE) (hfix2 _ dtE) y (by grind [Perm.mul_apply])
    · exact key (hA2 _ dtF) (hfix2 _ dtF) y (by grind [Perm.mul_apply])
  have hcard : Nat.card ↥U = 7 := by
    have h : U.card + (F₁ ∩ F₂).card = F₁.card + F₂.card :=
      Finset.card_union_add_card_inter F₁ F₂
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    omega
  have hprim : MulAction.IsPreprimitive ↥B ↥U :=
    MulAction.IsPreprimitive.of_prime_card (by rw [hcard]; decide)
  have hsq : (swap z a * swap b c * (swap z d * swap e f)) ^ 2 = swap z d * swap z a :=
    sq_swap_mul_swap hza hzb hzc hzd hze hzf hab hac had hae haf hbc hbd hbe hbf hcd hce hcf hde
      hdf hef
  have haU : a ∈ U := (hmU a).2 (Or.inr (Or.inl rfl))
  have hdU : d ∈ U := (hmU d).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : (swap (⟨z, hzU⟩ : ↥U) ⟨d, hdU⟩ * swap (⟨z, hzU⟩ : ↥U) ⟨a, haU⟩).IsThreeCycle :=
    isThreeCycle_swap_mul_swap_same
      (fun h => hzd (congrArg Subtype.val h)) (fun h => hza (congrArg Subtype.val h))
      (fun h => had.symm (congrArg Subtype.val h))
  have hmem : (swap (⟨z, hzU⟩ : ↥U) ⟨d, hdU⟩ * swap (⟨z, hzU⟩ : ↥U) ⟨a, haU⟩) ∈ B := by
    rw [hB, Subgroup.mem_comap, map_mul, Perm.ofSubtype_swap_eq, Perm.ofSubtype_swap_eq]
    show swap z d * swap z a ∈ A
    rw [← hsq]
    exact A.pow_mem (A.mul_mem (hA1 _ dtA) (hA2 _ dtD)) 2
  exact Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim h3 hmem

theorem star7 {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {F₁ F₂ : Finset Ω}
    (h1 : F₁.card = 4) (h2 : F₂.card = 4) (hz : (F₁ ∩ F₂).card = 1)
    {A : Subgroup (Perm Ω)} (hA1 : ∀ s, IsDT F₁ s → s ∈ A) (hA2 : ∀ s, IsDT F₂ s → s ∈ A) :
    ∀ g : Perm Ω, sign g = 1 → (∀ x, x ∉ F₁ ∪ F₂ → g x = x) → g ∈ A :=
  fun _ hg hU =>
    mem_of_alternatingGroup_le (alternatingGroup_le_comap_of_inter_one h1 h2 hz hA1 hA2) hg hU

theorem star_gen {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {ι : Type*} [Fintype ι] [Nonempty ι]
    (F₀ : Finset Ω) (G : ι → Finset Ω) (h0 : F₀.card = 4) (hG : ∀ i, (G i).card = 4)
    (hint : ∀ i, (F₀ ∩ G i).card = 1) {A : Subgroup (Perm Ω)}
    (hA0 : ∀ s, IsDT F₀ s → s ∈ A) (hAG : ∀ i s, IsDT (G i) s → s ∈ A) :
    ∀ g : Perm Ω, sign g = 1 → (∀ x, x ∉ F₀ ∪ Finset.univ.biUnion G → g x = x) → g ∈ A := by
  set U : Finset Ω := F₀ ∪ Finset.univ.biUnion G
  refine fun g hg hU => mem_of_alternatingGroup_le (U := U) ?_ hg hU
  let S : ι → Set ↥U := fun i => {x | (x : Ω) ∈ F₀ ∪ G i}
  have hF0U : ∀ x, x ∈ F₀ → x ∈ U := fun x hx => Finset.mem_union_left _ hx
  have hGU : ∀ i x, x ∈ G i → x ∈ U := fun i x hx =>
    Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, hx⟩)
  have hSU : ∀ i, F₀ ∪ G i ⊆ U := fun i x hx => by
    rcases Finset.mem_union.1 hx with h | h
    · exact hF0U x h
    · exact hGU i x h
  have hS3 : ∀ i, 3 ≤ (S i).ncard := by
    intro i
    have hc : (F₀ ∪ G i).card = 7 := by
      have h := Finset.card_union_add_card_inter F₀ (G i)
      rw [h0, hG i, hint i] at h
      omega
    have hS : S i = (Subtype.val : ↥U → Ω) ⁻¹' ((F₀ ∪ G i : Finset Ω) : Set Ω) := rfl
    have h7 : (S i).ncard = 7 := by
      rw [hS, Set.ncard_preimage_of_injective_subset_range Subtype.val_injective,
        Set.ncard_coe_finset, hc]
      intro x hx
      exact ⟨⟨x, hSU i hx⟩, rfl⟩
    omega
  obtain ⟨w, hw⟩ : F₀.Nonempty := Finset.card_pos.1 (by omega)
  have hcover : (⋃ i, S i) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    rcases Finset.mem_union.1 x.2 with h | h
    · obtain ⟨i⟩ := ‹Nonempty ι›
      exact Set.mem_iUnion.2 ⟨i, Finset.mem_union_left _ h⟩
    · obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 h
      exact Set.mem_iUnion.2 ⟨i, Finset.mem_union_right _ hi⟩
  have hconn : ∀ i j, Relation.ReflTransGen (fun a b => (S a ∩ S b).Nonempty) i j := fun i j =>
    Relation.ReflTransGen.single
      ⟨⟨w, hF0U w hw⟩, Finset.mem_union_left _ hw, Finset.mem_union_left _ hw⟩
  haveI : Nonempty ↥U := ⟨⟨w, hF0U w hw⟩⟩
  have hgen := GL83.iSup_altOn_eq_alternatingGroup hS3 hcover hconn
  rw [← hgen]
  refine iSup_le fun i h hh => ?_
  rw [Subgroup.mem_comap]
  obtain ⟨hAlt, hfix⟩ := GL83.mem_altOn.1 hh
  refine star7 h0 (hG i) (hint i) hA0 (hAG i) _ ?_ ?_
  · rw [Perm.sign_ofSubtype]
    exact Perm.mem_alternatingGroup.1 hAlt
  · intro x hx
    by_cases hxU : x ∈ U
    · rw [Perm.ofSubtype_apply_of_mem h hxU, hfix ⟨x, hxU⟩ hx]
    · exact Perm.ofSubtype_apply_of_not_mem h hxU

end CFSG.LocalAnalysis.GLTheoremB.Prop95I1921

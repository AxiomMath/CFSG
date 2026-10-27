module

public import CFSG.GF2Type.SmithTypeE.DMod.Gen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.DMod

open CFSG.SmithD6 CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial

theorem exists_moved_line :
    ∃ L : Finset V12, IsTsLine L ∧
      L.map (siegelEquiv (dec12 1) (dec12 2)).toEquiv.toEmbedding ≠ L := by
  have hq1 : qf 1 = false := by decide
  have hq2 : qf 2 = false := by decide
  have hb12 : bf 1 2 = false := by decide
  have hq4 : qf 4 = false := by decide
  have hq128 : qf 128 = false := by decide
  have hb4128 : bf 4 128 = false := by decide
  have hT' := tsPair_dec12 hq4 hq128 hb4128
  refine ⟨lineOfPair (dec12 4) (dec12 128), ⟨dec12 4, dec12 128,
    dec12_ne_zero (by norm_num) (by norm_num), dec12_ne_zero (by norm_num) (by norm_num),
    fun h => absurd (eq_of_dec12_eq (by norm_num) (by norm_num) h) (by norm_num), hT', rfl⟩, ?_⟩
  intro h
  rw [lineOfPair_map, siegelEquiv_dec12 hq1 hq2 hb12, siegelEquiv_dec12 hq1 hq2 hb12] at h
  have e1 : sgl 1 2 4 = 4 := by decide
  have e2 : sgl 1 2 128 = 129 := by decide
  rw [e1, e2] at h
  have hmem : dec12 129 ∈ lineOfPair (dec12 4) (dec12 128) := by
    rw [← h]
    simp [lineOfPair]
  simp only [lineOfPair, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h1 | h1 | h1
  · have := eq_of_dec12_eq (by norm_num) (by norm_num) h1
    omega
  · have := eq_of_dec12_eq (by norm_num) (by norm_num) h1
    omega
  · rw [← dec12_xor] at h1
    exact absurd (eq_of_dec12_eq (by norm_num) (by decide) h1) (by decide)

section Certified

@[expose] noncomputable def tvP (k : Fin 365211) : Equiv.Perm (Fin 365211) :=
  actPerm ⟨siegelK k.val, siegelK_mem_iso k.2⟩

theorem tvP_apply (k a : Fin 365211) : ((tvP k a : Fin 365211) : ℕ) = tvImg k.val a.val := by
  obtain ⟨hlt, hset⟩ := tvImg_spec k.2 a.2
  apply lineSet_injective (tvP k a).2 hlt
  rw [hset]
  exact lineSet_actPerm ⟨siegelK k.val, siegelK_mem_iso k.2⟩ a

@[expose] noncomputable def TD6 : Subgroup (Equiv.Perm (Fin 365211)) :=
  Subgroup.closure (Set.range tvP)

theorem tvP_mem (k : Fin 365211) : tvP k ∈ TD6 := Subgroup.subset_closure ⟨k, rfl⟩

theorem tvP_mul_self (k : Fin 365211) : tvP k * tvP k = 1 := by
  rw [tvP, ← map_mul]
  have : (⟨siegelK k.val, siegelK_mem_iso k.2⟩ * ⟨siegelK k.val, siegelK_mem_iso k.2⟩ : IsoGrp) =
      1 := Subtype.ext (siegelK_mul_self k.2)
  rw [this, map_one]

theorem omegaPlus_le_iso : CFSG.Open.timmesfeldOmegaPlus 6 ≤ IsoGrp := by
  rw [omegaPlus_eq_omegaGroup]
  show omegaGroup Q12 Q12_polarBilin_nondegenerate ≤ CFSG.Open.timmesfeldIsometries q12
  rw [isometries_eq_orthogonalGroup]
  exact omegaGroup_le Q12 Q12_polarBilin_nondegenerate

@[expose] noncomputable def omegaToPerm :
    ↥(CFSG.Open.timmesfeldOmegaPlus 6) →* Equiv.Perm (Fin 365211) :=
  actPerm.comp (Subgroup.inclusion omegaPlus_le_iso)

theorem omegaToPerm_apply (g : ↥(CFSG.Open.timmesfeldOmegaPlus 6)) :
    omegaToPerm g = actPerm ⟨g.1, omegaPlus_le_iso g.2⟩ := rfl

@[expose] noncomputable def siegel0 : ↥(CFSG.Open.timmesfeldOmegaPlus 6) :=
  ⟨siegelEquiv (dec12 1) (dec12 2),
    siegelEquiv_mem_omega (tsPair_dec12 (by decide) (by decide) (by decide))
      (dec12_ne_zero (by norm_num) (by norm_num))⟩

theorem omegaToPerm_siegel0_ne_one : omegaToPerm siegel0 ≠ 1 := by
  intro hmem
  obtain ⟨L, hL, hmove⟩ := exists_moved_line
  obtain ⟨k, hk⟩ := lineEquiv.surjective ⟨L, hL⟩
  have h1 := congrArg (fun σ : Equiv.Perm (Fin 365211) => lineEquiv (σ k)) hmem
  simp only [omegaToPerm_apply, lineEquiv_actPerm, Equiv.Perm.coe_one, id_eq, hk] at h1
  exact hmove (congrArg Subtype.val h1)

theorem omegaToPerm_injective : Function.Injective omegaToPerm := by
  haveI := isSimpleGroup_omegaPlus
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal omegaToPerm.ker with h | h
  · exact h
  · exfalso
    have hmem : siegel0 ∈ omegaToPerm.ker := by
      rw [h]
      trivial
    exact omegaToPerm_siegel0_ne_one (MonoidHom.mem_ker.mp hmem)

theorem omegaToPerm_range : omegaToPerm.range = TD6 := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    have hx : x.1 ∈ Subgroup.closure (Set.range fun k : Fin 365211 => siegelK k.val) :=
      omega_le_closure_siegelK (by rw [← omegaPlus_eq_omegaGroup]; exact x.2)
    let S' : Set IsoGrp :=
      Set.range fun k : Fin 365211 => (⟨siegelK k.val, siegelK_mem_iso k.2⟩ : IsoGrp)
    have hmap : (Subgroup.closure S').map IsoGrp.subtype =
        Subgroup.closure (Set.range fun k : Fin 365211 => siegelK k.val) := by
      rw [MonoidHom.map_closure]
      congr 1
      ext y
      simp [S']
    rw [← hmap] at hx
    obtain ⟨h, hh, hhx⟩ := hx
    have hxh : (⟨x.1, omegaPlus_le_iso x.2⟩ : IsoGrp) = h := Subtype.ext hhx.symm
    show actPerm ⟨x.1, omegaPlus_le_iso x.2⟩ ∈ TD6
    rw [hxh]
    have hmem : actPerm h ∈ (Subgroup.closure S').map actPerm := Subgroup.mem_map_of_mem _ hh
    rw [MonoidHom.map_closure] at hmem
    have himg : actPerm '' S' = Set.range tvP := by
      ext y
      simp [S', tvP]
    rwa [himg] at hmem
  · rw [TD6, Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨siegelK k.val, siegelK_mem_omega k.2⟩, rfl⟩

@[expose] noncomputable def omegaTD6 : ↥(CFSG.Open.timmesfeldOmegaPlus 6) ≃* ↥TD6 :=
  MulEquiv.ofBijective (omegaToPerm.codRestrict TD6 fun g => by
      rw [← omegaToPerm_range]
      exact ⟨g, rfl⟩)
    ⟨fun a b h => omegaToPerm_injective (congrArg Subtype.val h), fun g => by
      have hg : (g : Equiv.Perm (Fin 365211)) ∈ omegaToPerm.range := by
        rw [omegaToPerm_range]
        exact g.2
      obtain ⟨a, ha⟩ := hg
      exact ⟨a, Subtype.ext ha⟩⟩

theorem omegaTD6_siegelK (k : Fin 365211) :
    (omegaTD6 ⟨siegelK k.val, siegelK_mem_omega k.2⟩ : Equiv.Perm (Fin 365211)) = tvP k := rfl

theorem exists_omega_of_mem_TD6 {g : Equiv.Perm (Fin 365211)} (hg : g ∈ TD6) :
    ∃ x : ↥(CFSG.Open.timmesfeldOmegaPlus 6), omegaToPerm x = g := by
  rw [← omegaToPerm_range] at hg
  exact hg

theorem mul_tvP_mul_inv {g : Equiv.Perm (Fin 365211)} (hg : g ∈ TD6) (p : Fin 365211) :
    g * tvP p * g⁻¹ = tvP (g p) := by
  obtain ⟨x, rfl⟩ := exists_omega_of_mem_TD6 hg
  have hx : x.1 ∈ IsoGrp := omegaPlus_le_iso x.2
  have hx' : ∀ v, q12 (x.1 v) = q12 v := hx
  show actPerm ⟨x.1, hx⟩ * tvP p * (actPerm ⟨x.1, hx⟩)⁻¹ = tvP (actPerm ⟨x.1, hx⟩ p)
  rw [tvP, tvP, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact conj_siegelK hx' p.2 (actPerm ⟨x.1, hx⟩ p).2 (lineSet_actPerm ⟨x.1, hx⟩ p)

theorem isSimpleGroup_TD6 : IsSimpleGroup TD6 := by
  haveI := isSimpleGroup_omegaPlus
  exact omegaTD6.symm.isSimpleGroup

theorem siegelK_commSpace {k : ℕ} (hk : k < 365211) :
    commSpace (siegelK k) =
      Submodule.span (ZMod 2) {dec12 (linePair k).1, dec12 (linePair k).2} := by
  have hT := tsPair_linePair hk
  obtain ⟨hu, hw, huw⟩ := linePair_ne hk
  unfold siegelK
  rw [← eichler_eq_siegelEquiv hT]
  exact commSpace_eichler Q12_polarBilin_nondegenerate (by rw [Q12_apply]; exact hT.1)
    (by rw [polar_Q12]; exact hT.2.2) (OrthoF2.linearIndependent_pair_iff.mpr ⟨hu, hw, huw⟩)

theorem lineSet_subset_of_span_eq {k l : ℕ} (hk : k < 365211) (hl : l < 365211)
    (h : Submodule.span (ZMod 2) {dec12 (linePair k).1, dec12 (linePair k).2} =
      Submodule.span (ZMod 2) {dec12 (linePair l).1, dec12 (linePair l).2}) :
    lineSet k ⊆ lineSet l := by
  obtain ⟨hu, hw, huw⟩ := linePair_ne hk
  intro x hx
  simp only [lineSet, lineOfPair, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  have hu_mem : dec12 (linePair k).1 ∈ Submodule.span (ZMod 2)
      {dec12 (linePair l).1, dec12 (linePair l).2} := by
    rw [← h]
    exact Submodule.subset_span (by simp)
  have hw_mem : dec12 (linePair k).2 ∈ Submodule.span (ZMod 2)
      {dec12 (linePair l).1, dec12 (linePair l).2} := by
    rw [← h]
    exact Submodule.subset_span (by simp)
  have hx0 : x ≠ 0 := by
    rcases hx with rfl | rfl | rfl
    · exact hu
    · exact hw
    · exact fun h0 => huw (by
        calc dec12 (linePair k).1
            = dec12 (linePair k).1 + (dec12 (linePair k).2 + dec12 (linePair k).2) := by
              rw [add_self_V12, add_zero]
          _ = (dec12 (linePair k).1 + dec12 (linePair k).2) + dec12 (linePair k).2 := by
              rw [add_assoc]
          _ = dec12 (linePair k).2 := by rw [h0, zero_add])
  have hxs : x ∈ Submodule.span (ZMod 2) {dec12 (linePair l).1, dec12 (linePair l).2} := by
    rcases hx with rfl | rfl | rfl
    · exact hu_mem
    · exact hw_mem
    · exact Submodule.add_mem _ hu_mem hw_mem
  rcases S2.mem_span_pair_cases hxs with h0 | h1 | h2 | h3
  · exact absurd h0 hx0
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)

theorem siegelK_injective {k l : Fin 365211} (h : siegelK k.val = siegelK l.val) : k = l := by
  have hc := congrArg commSpace h
  rw [siegelK_commSpace k.2, siegelK_commSpace l.2] at hc
  have h1 := lineSet_subset_of_span_eq k.2 l.2 hc
  have h2 := lineSet_subset_of_span_eq l.2 k.2 hc.symm
  exact Fin.ext (lineSet_injective k.2 l.2 (Finset.Subset.antisymm h1 h2))

theorem tvP_injective : Function.Injective tvP := by
  intro k l h
  have h1 : omegaToPerm ⟨siegelK k.val, siegelK_mem_omega k.2⟩ =
      omegaToPerm ⟨siegelK l.val, siegelK_mem_omega l.2⟩ := h
  have h2 := omegaToPerm_injective h1
  exact siegelK_injective (congrArg Subtype.val h2)

end Certified

end CFSG.GF2Type.SmithTypeE.DMod

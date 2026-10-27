module

public import CFSG.GF2Type.Smith1979W3.CaseD.Irreducible

public section

namespace CFSG.GF2Type.Smith1979W3.CaseD

open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix Matrix Finset Equiv

variable {X : Subgroup (Perm (Fin 8))}

theorem apply_mem_of_mem_of_support_subset {T : Finset (Fin 8)} {σ : Perm (Fin 8)}
    (h : σ.support ⊆ T) {z : Fin 8} (hz : z ∈ T) : σ z ∈ T := by
  by_contra hz'
  have hnot : σ z ∉ σ.support := fun hmem => hz' (h hmem)
  have hfix : σ (σ z) = σ z := by
    by_contra hne
    exact hnot (Equiv.Perm.mem_support.mpr hne)
  have h2 : σ z = z := by
    have := congrArg (fun w => σ⁻¹ w) hfix
    simpa using this
  rw [h2] at hz'
  exact hz' hz

theorem mem_iff_apply_mem_of_support_subset {T : Finset (Fin 8)} {σ : Perm (Fin 8)}
    (h : σ.support ⊆ T) (z : Fin 8) : z ∈ T ↔ σ z ∈ T :=
  ⟨fun hz => apply_mem_of_mem_of_support_subset h hz, fun hz => by
    have := apply_mem_of_mem_of_support_subset (σ := σ⁻¹) (by rwa [Equiv.Perm.support_inv]) hz
    simpa using this⟩

theorem apply_mem_of_mem_of_support_subset_compl {T : Finset (Fin 8)} {σ : Perm (Fin 8)}
    (h : σ.support ⊆ Tᶜ) {z : Fin 8} (hz : z ∈ T) : σ z ∈ T := by
  by_contra hz'
  have hne : σ z ≠ z := by
    intro hfix
    apply hz'
    rw [hfix]
    exact hz
  have hzmem : z ∈ σ.support := Equiv.Perm.mem_support.mpr hne
  exact (Finset.mem_compl.mp (h hzmem)) hz

theorem mem_iff_apply_mem_of_support_subset_compl {T : Finset (Fin 8)} {σ : Perm (Fin 8)}
    (h : σ.support ⊆ Tᶜ) (z : Fin 8) : z ∈ T ↔ σ z ∈ T :=
  ⟨fun hz => apply_mem_of_mem_of_support_subset_compl h hz, fun hz => by
    have := apply_mem_of_mem_of_support_subset_compl (σ := σ⁻¹)
      (by rwa [Equiv.Perm.support_inv]) hz
    simpa using this⟩

theorem support_subset_of_forall_notMem {Ω : Finset (Fin 8)} {σ : Perm (Fin 8)}
    (h : ∀ x, x ∉ Ω → σ x = x) : σ.support ⊆ Ω := by
  intro x hx
  by_contra hxΩ
  exact (Equiv.Perm.mem_support.mp hx) (h x hxΩ)

theorem map_eq_self_of_support_subset {T : Finset (Fin 8)} {σ : Perm (Fin 8)}
    (h : σ.support ⊆ T) : T.map σ.toEmbedding = T := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨y, hyT, rfl⟩ := hx
    exact (mem_iff_apply_mem_of_support_subset h y).mp hyT
  · rw [Finset.card_map]

theorem even_of_le_four {n : ℕ} (h4 : n ≤ 4) (h1 : n ≠ 1) (h3 : n ≠ 3) : Even n := by
  interval_cases n
  · decide
  · exact absurd rfl h1
  · decide
  · exact absurd rfl h3
  · decide

theorem Irr8.exists_conj_inter_odd (h : Irr8 X) {t : Perm (Fin 8)} (htX : t ∈ X) (ht : IsDT t) :
    ∃ g ∈ X, (t.support ∩ (g * t * g⁻¹).support).card = 1 ∨
      (t.support ∩ (g * t * g⁻¹).support).card = 3 := by
  by_contra hcon
  let A : Set (ι6 → ZMod 2) := {v | ∃ g ∈ X, v = vS (g * t * g⁻¹).support}
  have hA : ∀ σ ∈ X, ∀ a ∈ A, Mm σ *ᵥ a ∈ A := by
    rintro σ hσ a ⟨g, hgX, rfl⟩
    refine ⟨σ * g, X.mul_mem hσ hgX, ?_⟩
    have hev : Even (g * t * g⁻¹).support.card := by
      rw [(ht.conj g).card_support]; norm_num
    rw [Mm_vS σ hev]
    have hsupp : ((g * t * g⁻¹).support).map σ.toEmbedding =
        ((σ * g) * t * (σ * g)⁻¹).support := by
      rw [← Equiv.Perm.support_conj]
      congr 1
    rw [hsupp]
  have haA : vS t.support ∈ A := ⟨1, X.one_mem, by simp⟩
  have ht_ev : Even t.support.card := by rw [ht.card_support]; norm_num
  have ha0 : vS t.support ≠ 0 := by
    intro h0
    rw [vS_eq_zero_iff ht_ev] at h0
    rcases h0 with h0 | h0
    · have := ht.card_support; rw [h0] at this; simp at this
    · have := ht.card_support; rw [h0] at this; simp at this
  refine Irr8.false_of_orth h hA haA ha0 ha0 ?_
  rintro a ⟨g, hgX, rfl⟩
  have hev1 : Even (g * t * g⁻¹).support.card := by rw [(ht.conj g).card_support]; norm_num
  rw [polar6_vS hev1 ht_ev]
  rw [ZMod.natCast_eq_zero_iff_even]
  have hle : ((g * t * g⁻¹).support ∩ t.support).card ≤ 4 := by
    rw [Finset.inter_comm]; exact ht.card_inter_le
  have hne1 : ((g * t * g⁻¹).support ∩ t.support).card ≠ 1 := by
    intro hc; exact hcon ⟨g, hgX, Or.inl (by rwa [Finset.inter_comm] at hc)⟩
  have hne3 : ((g * t * g⁻¹).support ∩ t.support).card ≠ 3 := by
    intro hc; exact hcon ⟨g, hgX, Or.inr (by rwa [Finset.inter_comm] at hc)⟩
  exact even_of_le_four hle hne1 hne3

theorem exists_conj_inter_one_of_five_cycle {Ω : Finset (Fin 8)}
    (hfix : ∀ σ ∈ X, ∀ x, x ∉ Ω → σ x = x)
    (hprim : MulAction.IsPreprimitive (resGroup X Ω) {x // x ∈ Ω}) {r : Perm (Fin 8)}
    (hrX : r ∈ X) (hr : r.IsCycle) (h5 : r.support.card = 5)
    (hcard : Ω.card = 7 ∨ Ω.card = 8) {T : Finset (Fin 8)} (hT : T ⊆ Ω) (hT4 : T.card = 4) :
    ∃ g ∈ X, (T ∩ T.map g.toEmbedding).card = 1 := by
  have hΩ6 : 6 < Ω.card := by rcases hcard with h | h <;> omega
  rcases hcard with h7 | h8
  ·
    have hFcard : (Ω \ T).card = 3 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hT, h7, hT4]
    obtain ⟨F', hF'sub, hF'card⟩ :=
      Finset.exists_subset_card_eq (s := T) (n := 3) (by omega)
    have hF'subΩ : F' ⊆ Ω := hF'sub.trans hT
    obtain ⟨g, hgX, hgmap⟩ := exists_map_eq_of_five_cycle (F := Ω \ T) (F' := F')
      hfix hprim hrX hr h5 hΩ6
      (Finset.sdiff_subset : Ω \ T ⊆ Ω) hF'subΩ (by omega) (by omega)
    have hgsupp : g.support ⊆ Ω := support_subset_of_forall_notMem (hfix g hgX)
    have hΩmap : Ω.map g.toEmbedding = Ω := map_eq_self_of_support_subset hgsupp
    have hTeq : T = Ω \ (Ω \ T) := (Finset.sdiff_sdiff_eq_self hT).symm
    have hTmap : T.map g.toEmbedding = Ω \ F' := by
      rw [hTeq, Finset.map_sdiff, hΩmap, hgmap]
    refine ⟨g, hgX, ?_⟩
    have hinter : T ∩ (Ω \ F') = T \ F' := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_sdiff]
      constructor
      · rintro ⟨hxT, _, hxF'⟩; exact ⟨hxT, hxF'⟩
      · rintro ⟨hxT, hxF'⟩; exact ⟨hxT, hT hxT, hxF'⟩
    rw [hTmap, hinter]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hF'sub, hT4, hF'card]
  ·
    have hΩuniv : Ω = Finset.univ := Finset.eq_univ_of_card Ω (by rw [h8, Fintype.card_fin])
    obtain ⟨a, haT⟩ := Finset.card_pos.mp (by rw [hT4]; norm_num : 0 < T.card)
    have hTcompl : Tᶜ.card = 4 := by rw [Finset.card_compl, hT4, Fintype.card_fin]
    obtain ⟨C, hCsub, hCcard⟩ :=
      Finset.exists_subset_card_eq (s := Tᶜ) (n := 3) (by omega)
    set F' : Finset (Fin 8) := insert a C with hF'def
    have haC : a ∉ C := by
      intro hac
      exact (Finset.mem_compl.mp (hCsub hac)) haT
    have hF'card : F'.card = 4 := by
      rw [hF'def, Finset.card_insert_of_notMem haC, hCcard]
    have hF'sub : F' ⊆ Ω := by rw [hΩuniv]; exact Finset.subset_univ _
    have hTinter : T ∩ F' = {a} := by
      rw [hF'def]
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hxT, hx | hxC⟩
        · exact hx
        · exact absurd hxT (Finset.mem_compl.mp (hCsub hxC))
      · rintro rfl
        exact ⟨haT, Or.inl rfl⟩
    obtain ⟨g, hgX, hgmap⟩ := exists_map_eq_of_five_cycle hfix hprim hrX hr h5 hΩ6 hT hF'sub
      (by omega) (by omega)
    refine ⟨g, hgX, ?_⟩
    rw [hgmap, hTinter, Finset.card_singleton]

theorem Irr8.exists_threeCycle_mem (h : Irr8 X) {t : Perm (Fin 8)} (htX : t ∈ X) (ht : IsDT t)
    {Ω : Finset (Fin 8)} (hcard : Ω.card = 7 ∨ Ω.card = 8)
    (hfix : ∀ σ ∈ X, ∀ x, x ∉ Ω → σ x = x)
    (hprim : MulAction.IsPreprimitive (resGroup X Ω) {x // x ∈ Ω}) :
    ∃ c ∈ X, c.IsThreeCycle := by
  obtain ⟨g, hgX, hg⟩ := Irr8.exists_conj_inter_odd h htX ht
  have ht'X : g * t * g⁻¹ ∈ X := X.mul_mem (X.mul_mem hgX htX) (X.inv_mem hgX)
  have ht'DT : IsDT (g * t * g⁻¹) := ht.conj g
  have htsupp : t.support ⊆ Ω := support_subset_of_forall_notMem (hfix t htX)
  rcases hg with hg1 | hg3
  · refine ⟨(t * (g * t * g⁻¹)) ^ 2, X.pow_mem (X.mul_mem htX ht'X) 2, ?_⟩
    exact table_one ht ht'DT hg1
  · rcases table_three ht ht'DT hg3 with h3 | ⟨hcyc, h5⟩
    · exact ⟨t * (g * t * g⁻¹), X.mul_mem htX ht'X, h3⟩
    · have hT4 : t.support.card = 4 := ht.card_support
      obtain ⟨g', hg'X, hg'map⟩ := exists_conj_inter_one_of_five_cycle hfix hprim
        (X.mul_mem htX ht'X) hcyc h5 hcard htsupp hT4
      have ht''X : g' * t * g'⁻¹ ∈ X := X.mul_mem (X.mul_mem hg'X htX) (X.inv_mem hg'X)
      have ht''DT : IsDT (g' * t * g'⁻¹) := ht.conj g'
      have hinter : (t.support ∩ (g' * t * g'⁻¹).support).card = 1 := by
        rw [Equiv.Perm.support_conj]
        exact hg'map
      refine ⟨(t * (g' * t * g'⁻¹)) ^ 2, X.pow_mem (X.mul_mem htX ht''X) 2, ?_⟩
      exact table_one ht ht''DT hinter

theorem exists_nine_of_threeCycles {Ω : Finset (Fin 8)} (hcard : 7 ≤ Ω.card)
    (hall : ∀ c : Perm (Fin 8), c.IsThreeCycle → c.support ⊆ Ω → c ∈ X) {T : Finset (Fin 8)}
    (hT : T.card = 4) :
    ∃ P : Subgroup (Perm (Fin 8)), P ≤ X ∧ Nat.card P = 9 ∧ ∀ σ ∈ P, T.map σ.toEmbedding = T := by
  have hcompl_card : Ωᶜ.card = 8 - Ω.card := by rw [Finset.card_compl, Fintype.card_fin]
  have hTO_le : (T \ Ω).card ≤ 1 := by
    calc (T \ Ω).card ≤ Ωᶜ.card := Finset.card_le_card (by
          intro x hx
          simp only [Finset.mem_sdiff, Finset.mem_compl] at hx ⊢
          exact hx.2)
      _ = 8 - Ω.card := hcompl_card
      _ ≤ 1 := by omega
  have hTinter : 3 ≤ (T ∩ Ω).card := by
    have hcs : (T \ Ω).card = T.card - (Ω ∩ T).card := Finset.card_sdiff
    have hle : (Ω ∩ T).card ≤ 4 := by
      calc (Ω ∩ T).card ≤ T.card := Finset.card_le_card Finset.inter_subset_right
        _ = 4 := hT
    have hcomm : (T ∩ Ω).card = (Ω ∩ T).card := by rw [Finset.inter_comm]
    omega
  have hOTinter : 3 ≤ (Ω \ T).card := by
    have hcs : (Ω \ T).card = Ω.card - (T ∩ Ω).card := Finset.card_sdiff
    have hle : (T ∩ Ω).card ≤ 4 := by
      calc (T ∩ Ω).card ≤ T.card := Finset.card_le_card Finset.inter_subset_left
        _ = 4 := hT
    omega
  obtain ⟨A, hA_sub, hAcard⟩ := Finset.exists_subset_card_eq (s := T ∩ Ω) (n := 3) (by omega)
  obtain ⟨A', hA'_sub, hA'card⟩ := Finset.exists_subset_card_eq (s := Ω \ T) (n := 3) (by omega)
  have hA_T : A ⊆ T := fun x hx => (Finset.mem_inter.mp (hA_sub hx)).1
  have hA_Ω : A ⊆ Ω := fun x hx => (Finset.mem_inter.mp (hA_sub hx)).2
  have hA'_compl : A' ⊆ Tᶜ :=
    fun x hx => Finset.mem_compl.mpr (Finset.mem_sdiff.mp (hA'_sub hx)).2
  obtain ⟨a1, a2, a3, ha12, ha13, ha23, hAeq⟩ := Finset.card_eq_three.mp hAcard
  obtain ⟨b1, b2, b3, hb12, hb13, hb23, hA'eq⟩ := Finset.card_eq_three.mp hA'card
  let c : Perm (Fin 8) := swap a1 a2 * swap a1 a3
  let c' : Perm (Fin 8) := swap b1 b2 * swap b1 b3
  have hc_cyc : c.IsThreeCycle := Equiv.Perm.isThreeCycle_swap_mul_swap_same ha12 ha13 ha23
  have hc'_cyc : c'.IsThreeCycle := Equiv.Perm.isThreeCycle_swap_mul_swap_same hb12 hb13 hb23
  have hc_suppA : c.support ⊆ ({a1, a2, a3} : Finset (Fin 8)) := by
    change (swap a1 a2 * swap a1 a3).support ⊆ _
    calc (swap a1 a2 * swap a1 a3).support
        ⊆ (swap a1 a2).support ∪ (swap a1 a3).support := Equiv.Perm.support_mul_le _ _
      _ = {a1, a2} ∪ {a1, a3} := by rw [Equiv.Perm.support_swap ha12, Equiv.Perm.support_swap ha13]
      _ = {a1, a2, a3} := by
          ext x; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
  have hc'_suppA' : c'.support ⊆ ({b1, b2, b3} : Finset (Fin 8)) := by
    change (swap b1 b2 * swap b1 b3).support ⊆ _
    calc (swap b1 b2 * swap b1 b3).support
        ⊆ (swap b1 b2).support ∪ (swap b1 b3).support := Equiv.Perm.support_mul_le _ _
      _ = {b1, b2} ∪ {b1, b3} := by rw [Equiv.Perm.support_swap hb12, Equiv.Perm.support_swap hb13]
      _ = {b1, b2, b3} := by
          ext x; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
  have hc_supp : c.support ⊆ Ω := by
    rw [← hAeq] at hc_suppA
    exact hc_suppA.trans hA_Ω
  have hc'_supp : c'.support ⊆ Ω := by
    rw [← hA'eq] at hc'_suppA'
    exact hc'_suppA'.trans (hA'_sub.trans Finset.sdiff_subset)
  have hc_T : c.support ⊆ T := by
    rw [← hAeq] at hc_suppA
    exact hc_suppA.trans hA_T
  have hc'_Tcompl : c'.support ⊆ Tᶜ := by
    rw [← hA'eq] at hc'_suppA'
    exact hc'_suppA'.trans hA'_compl
  have hcX : c ∈ X := hall c hc_cyc hc_supp
  have hc'X : c' ∈ X := hall c' hc'_cyc hc'_supp
  have hdisj : c.Disjoint c' := by
    rw [Equiv.Perm.disjoint_iff_disjoint_support]
    exact Finset.disjoint_left.mpr
      (fun x hxc hxc' => (Finset.mem_compl.mp (hc'_Tcompl hxc')) (hc_T hxc))
  refine ⟨Subgroup.closure ({c, c'} : Set (Perm (Fin 8))), ?_,
    card_closure_threeCycles hc_cyc hc'_cyc hdisj, ?_⟩
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hcX
    · exact hc'X
  · have key : ∀ σ ∈ Subgroup.closure ({c, c'} : Set (Perm (Fin 8))),
        ∀ z, z ∈ T ↔ σ z ∈ T := by
      intro σ hσ
      refine Subgroup.closure_induction (p := fun σ _ => ∀ z, z ∈ T ↔ σ z ∈ T)
        ?_ ?_ ?_ ?_ hσ
      · intro x hx z
        rcases hx with rfl | rfl
        · exact mem_iff_apply_mem_of_support_subset hc_T z
        · exact mem_iff_apply_mem_of_support_subset_compl hc'_Tcompl z
      · intro z; simp
      · intro x y hx hy ihx ihy z
        exact (ihy z).trans (ihx (y z))
      · intro x hx ih z
        have h := ih (x⁻¹ z)
        simpa using h.symm
    intro σ hσ
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [Finset.mem_map] at hx
      obtain ⟨y, hyT, rfl⟩ := hx
      exact (key σ hσ y).mp hyT
    · rw [Finset.card_map]

theorem exists_nine_le_stab_perm8 (h : Irr8 X) {t : Perm (Fin 8)} (htX : t ∈ X) (ht : IsDT t)
    {x : ι6 → ZMod 2} (hx0 : x ≠ 0) (hx : Q6 x = 0) :
    ∃ P : Subgroup (Perm (Fin 8)), P ≤ X ∧ Nat.card P = 9 ∧ ∀ σ ∈ P, Mm σ *ᵥ x = x := by
  obtain ⟨Ω, hcard, htrans, hfix⟩ := Irr8.exists_orbit h htX ht
  have hprim := Irr8.isPreprimitive_res h hcard htrans hfix
  obtain ⟨c0, hc0X, hc0⟩ := Irr8.exists_threeCycle_mem h htX ht hcard hfix hprim
  have hall : ∀ c : Perm (Fin 8), c.IsThreeCycle → c.support ⊆ Ω → c ∈ X :=
    fun c hc hsupp => threeCycle_mem_of_primitive hfix hprim hc0X hc0 hc hsupp
  obtain ⟨T, hT4, hxT⟩ := exists_vS_of_singular hx0 hx
  have hcard7 : 7 ≤ Ω.card := by rcases hcard with h | h <;> omega
  obtain ⟨P, hPX, hP9, hPT⟩ := exists_nine_of_threeCycles hcard7 hall hT4
  refine ⟨P, hPX, hP9, ?_⟩
  intro σ hσ
  rw [hxT, Mm_vS σ (S := T) (by rw [hT4]; norm_num), hPT σ hσ]

end CFSG.GF2Type.Smith1979W3.CaseD

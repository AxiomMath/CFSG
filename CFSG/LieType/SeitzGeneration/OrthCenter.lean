module

public import CFSG.LieType.SeitzGeneration.OrthRoot

public section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2 (orthDerived)

section Setup

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {p : ℕ}
  {E : Subgroup (orthDerived Q)}

theorem planeFixSpace_le_lineFixSpace (M : Subgroup E) : planeFixSpace E ≤ lineFixSpace M := by
  intro v hv g hg
  obtain ⟨g', ⟨m, hm, rfl⟩, rfl⟩ := hg
  exact hv _ ⟨((m : E) : orthDerived Q), (m : E).2, rfl⟩

theorem lineSpace_le_lineFixSpace (M : Subgroup E) : lineSpace M ≤ lineFixSpace M :=
  inf_le_left

theorem sup_le_lineFixSpace (M : Subgroup E) : planeFixSpace E ⊔ lineSpace M ≤ lineFixSpace M :=
  sup_le (planeFixSpace_le_lineFixSpace M) (lineSpace_le_lineFixSpace M)

theorem eichler_mem_span_of_mem_sup (hEΩ : elementaryGroup Q ≤ orthDerived Q) {M : Subgroup E}
    (hM : M ≠ ⊥) {e w : V} (he : e ∈ planeFixSpace E ⊔ lineSpace M)
    (hw : w ∈ planeFixSpace E ⊔ lineSpace M) : eichler Q e w ∈ orthCentralizerSpan Q E :=
  eichler_mem_span_of_lineFix hEΩ hM (sup_le_lineFixSpace M he) (sup_le_lineFixSpace M hw)

theorem regular_sup (hK : KernelLineData Q p E) {M : Subgroup E} (hM : Nat.card M = p) :
    (LinearMap.BilinForm.restrict (polarBilin Q)
      (planeFixSpace E ⊔ lineSpace M)).Nondegenerate := by
  classical
  have hne : (none : Option {M : Subgroup E // Nat.card M = p}) ≠ some ⟨M, hM⟩ := by simp
  have h01 : ∀ u ∈ planeFixSpace E, ∀ v ∈ lineSpace M, polar Q u v = 0 := fun u hu v hv => by
    have := hK.orth _ _ hne u hu v hv
    rwa [polarBilin_apply_apply] at this
  have h10 : ∀ v ∈ lineSpace M, ∀ u ∈ planeFixSpace E, polar Q v u = 0 := fun v hv u hu => by
    rw [polar_comm]; exact h01 u hu v hv
  rw [← polarBilin_comp_subtype]
  have hrefl : (polarBilin (Q.comp (planeFixSpace E ⊔ lineSpace M).subtype)).IsRefl :=
    (QuadraticMap.isSymm_polarBilin _).isRefl
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hrefl).mpr ?_
  intro x hx
  obtain ⟨x₀, hx₀, x₁, hx₁, hxx⟩ := Submodule.mem_sup.1 x.2
  have hp0 : ∀ y ∈ planeFixSpace E ⊔ lineSpace M, polar Q (x : V) y = 0 := fun y hy => by
    have := hx ⟨y, hy⟩
    rwa [polarBilin_apply_apply, polar_comp_subtype'] at this
  have h0 : x₀ = 0 := by
    have : ∀ z : planeFixSpace E, polarBilin (Q.comp (planeFixSpace E).subtype) ⟨x₀, hx₀⟩ z = 0 :=
      fun z => by
      rw [polarBilin_apply_apply, polar_comp_subtype']
      have h1 := hp0 z (Submodule.mem_sup_left z.2)
      rw [← hxx, polar_add_left, h10 x₁ hx₁ z z.2, add_zero] at h1
      exact h1
    rw [polarBilin_comp_subtype] at this
    exact congrArg Subtype.val ((hK.regular none).1 ⟨x₀, hx₀⟩ this)
  have h1 : x₁ = 0 := by
    have : ∀ z : lineSpace M, polarBilin (Q.comp (lineSpace M).subtype) ⟨x₁, hx₁⟩ z = 0 :=
      fun z => by
      rw [polarBilin_apply_apply, polar_comp_subtype']
      have h1 := hp0 z (Submodule.mem_sup_right z.2)
      rw [← hxx, polar_add_left, h01 x₀ hx₀ z z.2, zero_add] at h1
      exact h1
    rw [polarBilin_comp_subtype] at this
    exact congrArg Subtype.val ((hK.regular (some ⟨M, hM⟩)).1 ⟨x₁, hx₁⟩ this)
  exact Subtype.ext (by rw [← hxx, h0, h1, add_zero]; rfl)

end Setup

section Pivots

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {p : ℕ}
  {E : Subgroup (orthDerived Q)}

theorem polar_eq_zero_of_mem_sup (hK : KernelLineData Q p E) {N M : Subgroup E}
    (hN : Nat.card N = p) (hM : Nat.card M = p) (hMN : M ≠ N) {u v : V}
    (hu : u ∈ lineSpace M) (hv : v ∈ planeFixSpace E ⊔ lineSpace N) : polar Q u v = 0 := by
  classical
  have hne1 : (some ⟨M, hM⟩ : Option {M : Subgroup E // Nat.card M = p}) ≠ none := by simp
  have hne2 : (some ⟨M, hM⟩ : Option {M : Subgroup E // Nat.card M = p}) ≠ some ⟨N, hN⟩ :=
    fun h' => hMN (congrArg Subtype.val (Option.some.inj h'))
  obtain ⟨v₀, hv₀, v₁, hv₁, rfl⟩ := Submodule.mem_sup.1 hv
  have h0 := hK.orth _ _ hne1 u hu v₀ hv₀
  have h1 := hK.orth _ _ hne2 u hu v₁ hv₁
  rw [polarBilin_apply_apply] at h0 h1
  rw [polar_add_right, h0, h1, add_zero]

open _root_.Classical in
theorem isRootCenter_of_pivots (hK : KernelLineData Q p E)
    (hEΩ : elementaryGroup Q ≤ orthDerived Q) (hp : p.Prime) {N : Subgroup E}
    (hN : Nat.card N = p) {s : V} (hsN : s ∈ planeFixSpace E ⊔ lineSpace N) (hs0 : s ≠ 0)
    (hsQ : Q s = 0)
    (hpiv : ∀ M : Subgroup E, Nat.card M = p → M ≠ N →
      ∀ v ∈ lineSpace M, v ∈ rootSet Q (orthCentralizerSpan Q E) s) :
    IsRootCenter Q (orthCentralizerSpan Q E) s := by
  refine ⟨hs0, hsQ, fun w hw => ?_⟩
  have hN0 : N ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hN
    exact hp.one_lt.ne' hN.symm
  set T : Submodule K V := ⨆ (M : {M : Subgroup E // Nat.card M = p}) (_ : M.1 ≠ N),
    lineSpace M.1 with hT
  have htop : (⊤ : Submodule K V) ≤ (planeFixSpace E ⊔ lineSpace N) ⊔ T := by
    rw [← hK.internal.submodule_iSup_eq_top]
    refine iSup_le fun i => ?_
    rcases i with _ | ⟨M, hM⟩
    · exact le_sup_of_le_left le_sup_left
    · by_cases hMN : M = N
      · subst hMN
        exact le_sup_of_le_left le_sup_right
      · exact le_sup_of_le_right (le_iSup₂_of_le ⟨M, hM⟩ hMN le_rfl)
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (htop (Submodule.mem_top (x := w)))
  have hsT : polar Q s b = 0 := by
    refine Submodule.iSup_induction (fun M : {M : Subgroup E // Nat.card M = p} =>
      ⨆ (_ : M.1 ≠ N), lineSpace M.1) (motive := fun b => polar Q s b = 0) hb ?_ ?_ ?_
    · intro M b hb'
      refine Submodule.iSup_induction (fun _ : M.1 ≠ N => lineSpace M.1)
        (motive := fun b => polar Q s b = 0) hb' ?_ ?_ ?_
      · intro hMN b hb''
        rw [polar_comm]
        exact polar_eq_zero_of_mem_sup hK hN M.2 hMN hb'' hsN
      · exact polar_zero_right Q s
      · intro x y hx hy
        rw [polar_add_right, hx, hy, add_zero]
    · exact polar_zero_right Q s
    · intro x y hx hy
      rw [polar_add_right, hx, hy, add_zero]
  have hbR : b ∈ rootSet Q (orthCentralizerSpan Q E) s := by
    refine Submodule.iSup_induction (fun M : {M : Subgroup E // Nat.card M = p} =>
      ⨆ (_ : M.1 ≠ N), lineSpace M.1) (motive := fun b => b ∈ rootSet Q (orthCentralizerSpan Q E) s)
      hb ?_ (AddSubgroup.zero_mem _) (fun x y hx hy => AddSubgroup.add_mem _ hx hy)
    intro M b hb'
    refine Submodule.iSup_induction (fun _ : M.1 ≠ N => lineSpace M.1)
      (motive := fun b => b ∈ rootSet Q (orthCentralizerSpan Q E) s) hb' ?_
      (AddSubgroup.zero_mem _) (fun x y hx hy => AddSubgroup.add_mem _ hx hy)
    intro hMN b hb''
    exact hpiv M.1 M.2 hMN b hb''
  have haperp : polar Q s a = 0 := by
    rw [polar_add_right, hsT, add_zero] at hw
    exact hw
  have haR : a ∈ rootSet Q (orthCentralizerSpan Q E) s :=
    ⟨haperp, eichler_mem_span_of_mem_sup hEΩ hN0 hsN ha⟩
  exact ((rootSet Q (orthCentralizerSpan Q E) s).add_mem haR hbR).2

end Pivots

section Transport

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {p : ℕ}
  {E : Subgroup (orthDerived Q)}

theorem rootSet_ge_of_pivot (hK : KernelLineData Q p E)
    (hEΩ : elementaryGroup Q ≤ orthDerived Q) (hp : p.Prime) {N M : Subgroup E}
    (hN : Nat.card N = p) (hM : Nat.card M = p) (hMN : M ≠ N)
    (hPN : HasOrthPairs Q (planeFixSpace E ⊔ lineSpace N))
    (hPM : HasOrthPairs Q (planeFixSpace E ⊔ lineSpace M)) {s₀ : V}
    (hs₀N : s₀ ∈ lineSpace N) (hs₀0 : s₀ ≠ 0) (hs₀Q : Q s₀ = 0) {b : V} (hbM : b ∈ lineSpace M)
    (hb0 : b ≠ 0) (hbR : b ∈ rootSet Q (orthCentralizerSpan Q E) s₀) {s : V}
    (hsN : s ∈ planeFixSpace E ⊔ lineSpace N) (hs0 : s ≠ 0) (hsQ : Q s = 0) :
    ∀ v ∈ lineSpace M, v ∈ rootSet Q (orthCentralizerSpan Q E) s := by
  classical
  have hN0 : N ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hN
    exact hp.one_lt.ne' hN.symm
  have hM0 : M ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hM
    exact hp.one_lt.ne' hM.symm
  have hne1 : (some ⟨N, hN⟩ : Option {M : Subgroup E // Nat.card M = p}) ≠ none := by simp
  have hne2 : (some ⟨M, hM⟩ : Option {M : Subgroup E // Nat.card M = p}) ≠ some ⟨N, hN⟩ :=
    fun h' => hMN (congrArg Subtype.val (Option.some.inj h'))
  have hH : orthCentralizerSpan Q E ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthCentralizerSpan_le_orthogonalGroup E
  have hs₀perp : ∀ u ∈ planeFixSpace E ⊔ lineSpace M, polar Q s₀ u = 0 := fun u hu => by
    obtain ⟨u₀, hu₀, u₁, hu₁, rfl⟩ := Submodule.mem_sup.1 hu
    have h0 := hK.orth _ _ hne1 s₀ hs₀N u₀ hu₀
    have h1 := hK.orth _ _ hne2.symm s₀ hs₀N u₁ hu₁
    rw [polarBilin_apply_apply] at h0 h1
    rw [polar_add_right, h0, h1, add_zero]
  have hall : ∀ y ∈ planeFixSpace E ⊔ lineSpace M, y ∈ rootSet Q (orthCentralizerSpan Q E) s₀ := by
    refine mem_of_invariant (regular_sup hK hM) hPM (rootSet Q (orthCentralizerSpan Q E) s₀)
      (fun e he w hw a ha _ => ?_) hbR (Submodule.mem_sup_right hbM) hb0
    have hgH : eichler Q e w ∈ orthCentralizerSpan Q E :=
      eichler_mem_span_of_mem_sup hEΩ hM0 he hw
    have hfix : eichler Q e w s₀ = s₀ :=
      eichler_apply_of_polar_eq_zero (polar_comm Q e s₀ ▸ hs₀perp e he)
        (polar_comm Q w s₀ ▸ hs₀perp w hw)
    have := rootSet_map hH hgH ha
    rwa [hfix] at this
  obtain ⟨g, hg, hgs⟩ := exists_mem_eichlerGroupOn_apply_eq_of_pairs (regular_sup hK hN)
    hPN (Submodule.mem_sup_right hs₀N) hsN hs₀0 hs0 (by rw [hs₀Q, hsQ])
  have hgH : g ∈ orthCentralizerSpan Q E :=
    eichlerGroupOn_le (fun e he w hw => eichler_mem_span_of_mem_sup hEΩ hN0 he hw) hg
  intro v hv
  have hgv : g v = v := eichlerGroupOn_apply_of_orth hg
    (fun u hu => polar_eq_zero_of_mem_sup hK hN hM hMN hv hu)
  have := rootSet_map hH hgH (hall v (Submodule.mem_sup_right hv))
  rwa [hgv, hgs] at this

theorem elementaryGroup_le_span_of_pivots (hK : KernelLineData Q p E)
    (hEΩ : elementaryGroup Q ≤ orthDerived Q) (hp : p.Prime)
    (hQ : (polarBilin Q).Nondegenerate) {N : Subgroup E} (hN : Nat.card N = p)
    (hPN : HasOrthPairs Q (planeFixSpace E ⊔ lineSpace N))
    (hpiv : ∀ M : Subgroup E, Nat.card M = p → M ≠ N → lineSpace M ≠ ⊥ →
      HasOrthPairs Q (planeFixSpace E ⊔ lineSpace M) ∧ ∃ s₀ ∈ lineSpace N, s₀ ≠ 0 ∧ Q s₀ = 0 ∧
        ∃ b ∈ lineSpace M, b ≠ 0 ∧ b ∈ rootSet Q (orthCentralizerSpan Q E) s₀) :
    elementaryGroup Q ≤ orthCentralizerSpan Q E := by
  obtain ⟨a₁, f₁, a₂, f₂, ha₁, hf₁, -, -, hQa₁, hQf₁, -, -, h11, -⟩ := id hPN
  have center : ∀ s ∈ planeFixSpace E ⊔ lineSpace N, s ≠ 0 → Q s = 0 →
      IsRootCenter Q (orthCentralizerSpan Q E) s := by
    intro s hsN hs0 hsQ
    refine isRootCenter_of_pivots hK hEΩ hp hN hsN hs0 hsQ fun M hM hMN v hv => ?_
    by_cases hbot : lineSpace M = ⊥
    · rw [hbot, Submodule.mem_bot] at hv
      rw [hv]
      exact AddSubgroup.zero_mem _
    · obtain ⟨hPM, s₀, hs₀N, hs₀0, hs₀Q, b, hbM, hb0, hbR⟩ := hpiv M hM hMN hbot
      exact rootSet_ge_of_pivot hK hEΩ hp hN hM hMN hPN hPM hs₀N hs₀0 hs₀Q hbM hb0 hbR hsN hs0
        hsQ v hv
  have ha₁0 : a₁ ≠ 0 := fun h0 => by
    rw [h0, polar_zero_left] at h11
    exact zero_ne_one h11
  have hf₁0 : f₁ ≠ 0 := fun h0 => by
    rw [h0, polar_zero_right] at h11
    exact zero_ne_one h11
  exact elementaryGroup_le_of_hypPair hQ (orthCentralizerSpan_le_orthogonalGroup E)
    ⟨a₁, f₁, hQa₁, hQf₁, h11⟩ (center a₁ ha₁ ha₁0 hQa₁) (center f₁ hf₁ hf₁0 hQf₁)

end Transport

end CFSG.LieType.SeitzGeneration

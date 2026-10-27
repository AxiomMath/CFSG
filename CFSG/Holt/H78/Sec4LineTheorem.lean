module

public import CFSG.Holt.H78.Sec4LineCoord
import CFSG.Holt.H78.Sec4Toolkit

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Open Equiv
open scoped Pointwise

section Coord

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

variable (G) in
@[expose] def lineGroup (Λ : Set Ω) (L : Set Ω) : Subgroup G := ⨆ x ∈ L, lineKer G Λ x L

variable {Λ : Set Ω}

theorem lineKer_le_lineGroup {x : Ω} {L : Set Ω} (hx : x ∈ L) :
    lineKer G Λ x L ≤ lineGroup G Λ L :=
  le_iSup₂_of_le x hx le_rfl

theorem lineGroup_le_stabilizer {L : Set Ω} (hL : IsJClosed G Ω L) :
    lineGroup G Λ L ≤ stabilizer G L :=
  iSup₂_le fun _ hx => lineKer_le_closure.trans (closure_longInvAt_le_stabilizer hL hx)

theorem conj_mem_lineGroup {L : Set Ω} {m : G} (hm : m ∈ lineGroup G Λ L) (g : G) :
    g * m * g⁻¹ ∈ lineGroup G Λ (g • L) := by
  have h : (lineGroup G Λ L).map (MulAut.conj g).toMonoidHom ≤ lineGroup G Λ (g • L) := by
    rw [lineGroup, Subgroup.map_iSup]
    refine iSup_le fun x => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hx => ?_
    rintro _ ⟨k, hk, rfl⟩
    exact lineKer_le_lineGroup (Set.smul_mem_smul_set hx) (conj_mem_lineKer hk g)
  exact h ⟨m, hm, rfl⟩

theorem lineGroup_le_centralizer {L : Set Ω} {S : Set G}
    (h : ∀ x ∈ L, lineKer G Λ x L ≤ Subgroup.centralizer S) :
    lineGroup G Λ L ≤ Subgroup.centralizer S :=
  iSup₂_le h

end Coord

section CoordAlt

variable {G : Type*} [Group G] {Ω : Type*} [DecidableEq Ω] [MulAction G Ω] [Finite Ω]
  {Λ : Set Ω}

theorem lineGroup_exists_smul_eq (hΛ : IsLine G Λ) (hND : LineNonDiagonal G Λ) {L : Set Ω}
    (hL : ∃ g : G, g • Λ = L) {y z : Ω} (hy : y ∈ L) (hz : z ∈ L) :
    ∃ m ∈ lineGroup G Λ L, m • y = z := by
  rcases eq_or_ne y z with rfl | hyz
  · exact ⟨1, Subgroup.one_mem _, one_smul G y⟩
  have hLl : IsLine G L := by
    obtain ⟨g, rfl⟩ := hL
    exact hΛ.smul g
  obtain ⟨x, hx, -, -, hxy, hxz, -, -, -, -, -⟩ := exists_two_of_seven_le hLl.seven_le y z z
  obtain ⟨k, hk, hky⟩ := (realizes3_lineKer hΛ hND ⟨hL, hx⟩).exists_smul_eq hLl.seven_le hy hz
    (Ne.symm hxy) (Ne.symm hxz)
  exact ⟨k, lineKer_le_lineGroup hx hk, hky⟩

end CoordAlt

section Kappa

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω] [FaithfulSMul G Ω] {Λ : Set Ω}

theorem Sec4Setting.lineGroup_inf_fixingSubgroup_eq_bot (hS : Sec4Setting G Ω)
    (hΛ : IsLine G Λ) (hND : LineNonDiagonal G Λ) {L : Set Ω} (hL : ∃ g : G, g • Λ = L) :
    lineGroup G Λ L ⊓ fixingSubgroup G L = ⊥ := by
  have hLl : IsLine G L := by
    obtain ⟨g, rfl⟩ := hL
    exact hΛ.smul g
  have hnorm : ∀ g ∈ stabilizer G L, ∀ c ∈ lineGroup G Λ L ⊓ fixingSubgroup G L,
      g * c * g⁻¹ ∈ lineGroup G Λ L ⊓ fixingSubgroup G L := fun g hg c hc =>
    ⟨by simpa [mem_stabilizer_iff.mp hg] using conj_mem_lineGroup hc.1 g,
      conj_mem_fixingSubgroup hg hc.2⟩
  have hZ : ∀ x ∈ L, lineFix G Λ x = ⊥ := fun x hx => hS.lineFix_eq_bot hΛ hND ⟨hL, hx⟩
  have hKstab : ∀ {x : Ω} {L' : Set Ω}, L' ∈ linesThrough G Λ x → ∀ {k : G},
      k ∈ lineKer G Λ x L' → k ∈ stabilizer G L' := fun hL' _ hk =>
    lineKer_le_closure.trans (closure_longInvAt_le_stabilizer
      (hΛ.of_mem_linesThrough hL').jClosed hL'.2) hk
  have hcomm : ∀ x ∈ L, ∀ k ∈ lineKer G Λ x L, ∀ c ∈ lineGroup G Λ L ⊓ fixingSubgroup G L,
      k * c = c * k := by
    intro x hx k hk c hc
    have hcx : c • x = x := (mem_fixingSubgroup_iff G).mp hc.2 x hx
    have hcL := fixingSubgroup_le_stabilizer G L hc.2
    have hck : c * k * c⁻¹ ∈ lineKer G Λ x L := by
      simpa [hcx, mem_stabilizer_iff.mp hcL] using conj_mem_lineKer hk c
    have hd1 : k * c * k⁻¹ * c⁻¹ ∈ lineKer G Λ x L := by
      have h1 : k * c * k⁻¹ * c⁻¹ = k * (c * k * c⁻¹)⁻¹ := by group
      rw [h1]
      exact Subgroup.mul_mem _ hk (Subgroup.inv_mem _ hck)
    have hd2 : k * c * k⁻¹ * c⁻¹ ∈ fixingSubgroup G L :=
      Subgroup.mul_mem _ (hnorm k (hKstab ⟨hL, hx⟩ hk) c hc).2 (Subgroup.inv_mem _ hc.2)
    have hd := mem_lineFix_of_mem_lineKer hd1 hd2
    rw [hZ x hx, Subgroup.mem_bot] at hd
    calc k * c = (k * c * k⁻¹ * c⁻¹) * (c * k) := by group
      _ = c * k := by rw [hd, one_mul]
  have hκcomm : ∀ c ∈ lineGroup G Λ L ⊓ fixingSubgroup G L,
      ∀ c' ∈ lineGroup G Λ L ⊓ fixingSubgroup G L, c * c' = c' * c := by
    intro c hc c' hc'
    have hle : lineGroup G Λ L ≤ Subgroup.centralizer {c} := lineGroup_le_centralizer
      fun x hx k hk => Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx k hk c hc)
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hc'.1)).symm
  rw [eq_bot_iff]
  intro c hc
  obtain ⟨x, hx⟩ : L.Nonempty := Set.nonempty_of_ncard_ne_zero (by have := hLl.seven_le; omega)
  have hcx : c • x = x := (mem_fixingSubgroup_iff G).mp hc.2 x hx
  have hcL := fixingSubgroup_le_stabilizer G L hc.2
  have hstab : ∀ L' ∈ linesThrough G Λ x, c • L' = L' := by
    intro L' hL'
    by_contra hne
    have hL'l := hΛ.of_mem_linesThrough hL'
    have hL'L : L' ≠ L := fun h => hne (by rw [h]; exact mem_stabilizer_iff.mp hcL)
    have hK' := realizes3_lineKer hΛ hND hL'
    have hkL : ∀ {k : G}, k ∈ lineKer G Λ x L' → k ∈ stabilizer G L := fun hk =>
      fixingSubgroup_le_stabilizer G L ((mem_fixingSubgroup_iff G).mpr fun y hy =>
        lineKer_smul_eq hk ⟨hL, hx⟩ (Ne.symm hL'L) hy)
    have hdκ : ∀ {k : G}, k ∈ lineKer G Λ x L' →
        c * k⁻¹ * c⁻¹ * k ∈ lineGroup G Λ L ⊓ fixingSubgroup G L := by
      intro k hk
      have h1 : c * k⁻¹ * c⁻¹ * k = c * (k⁻¹ * c⁻¹ * k⁻¹⁻¹) := by group
      rw [h1]
      exact Subgroup.mul_mem _ hc (hnorm k⁻¹ (Subgroup.inv_mem _ (hkL hk)) c⁻¹
        (Subgroup.inv_mem _ hc))
    have hdact : ∀ {k : G}, k ∈ lineKer G Λ x L' → ∀ y ∈ L',
        (c * k⁻¹ * c⁻¹ * k) • y = k • y := by
      intro k hk y hy
      have hck : c * k⁻¹ * c⁻¹ ∈ lineKer G Λ x (c • L') := by
        simpa [hcx] using conj_mem_lineKer (Subgroup.inv_mem _ hk) c
      have hky : k • y ∈ L' := by
        rw [← mem_stabilizer_iff.mp (hKstab hL' hk)]
        exact Set.smul_mem_smul_set hy
      rw [mul_smul, lineKer_smul_eq hck hL' (Ne.symm hne) hky]
    obtain ⟨a, ha, b, hb, e, he, f, hf, hax, hbx, hex, hfx, hab, hae, haf, hbe, hbf, hef⟩ :=
      exists_four_of_seven_le hL'l.seven_le x
    obtain ⟨k₁, hk₁, h₁⟩ := hK' a ha b hb e he hax hbx hex hab hae hbe
    obtain ⟨k₂, hk₂, h₂⟩ := hK' a ha b hb f hf hax hbx hfx hab haf hbf
    have e1 : ((c * k₁⁻¹ * c⁻¹ * k₁) * (c * k₂⁻¹ * c⁻¹ * k₂)) • a = e := by
      rw [mul_smul, hdact hk₂ a ha, h₂ a ha, cyc3_apply_left hab haf, hdact hk₁ b hb, h₁ b hb,
        cyc3_apply_mid hae hbe]
    have e2 : ((c * k₂⁻¹ * c⁻¹ * k₂) * (c * k₁⁻¹ * c⁻¹ * k₁)) • a = f := by
      rw [mul_smul, hdact hk₁ a ha, h₁ a ha, cyc3_apply_left hab hae, hdact hk₂ b hb, h₂ b hb,
        cyc3_apply_mid haf hbf]
    rw [hκcomm _ (hdκ hk₁) _ (hdκ hk₂)] at e1
    exact hef (e1.symm.trans e2)
  have hfixL : ∀ L' ∈ linesThrough G Λ x, ∀ y ∈ L', c • y = y := by
    intro L' hL' y hy
    rcases eq_or_ne L' L with rfl | hL'L
    · exact (mem_fixingSubgroup_iff G).mp hc.2 y hy
    have hL'l := hΛ.of_mem_linesThrough hL'
    have hK' := realizes3_lineKer hΛ hND hL'
    have hkL : ∀ {k : G}, k ∈ lineKer G Λ x L' → k ∈ stabilizer G L := fun hk =>
      fixingSubgroup_le_stabilizer G L ((mem_fixingSubgroup_iff G).mpr fun z hz =>
        lineKer_smul_eq hk ⟨hL, hx⟩ (Ne.symm hL'L) hz)
    have hN := Realizes3.smul_eq_of_commute hL'l.seven_le hL'.2
      (fun k hk => hKstab hL' hk) hK'
      (N := lineKer G Λ x L' ⊓ (lineGroup G Λ L ⊓ fixingSubgroup G L))
      (fun n hn => hKstab hL' hn.1)
      (fun n hn => closure_longInvAt_le_stabilizer_point x (lineKer_le_closure hn.1))
      (fun k hk n hn => ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hn.1) (Subgroup.inv_mem _ hk),
        hnorm k (hkL hk) n hn.2⟩)
      (fun n hn n' hn' => hκcomm n hn.2 n' hn'.2)
    have hcomL' : ∀ k ∈ lineKer G Λ x L', ∀ w ∈ L', c • k • w = k • c • w := by
      intro k hk w hw
      have h1 : c * k * c⁻¹ ∈ lineKer G Λ x L' := by
        simpa [hcx, hstab L' hL'] using conj_mem_lineKer hk c
      have h2 : c * k * c⁻¹ * k⁻¹ ∈ lineKer G Λ x L' ⊓ (lineGroup G Λ L ⊓ fixingSubgroup G L) := by
        refine ⟨Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hk), ?_⟩
        have h3 : c * k * c⁻¹ * k⁻¹ = c * (k * c⁻¹ * k⁻¹) := by group
        rw [h3]
        exact Subgroup.mul_mem _ hc (hnorm k (hkL hk) c⁻¹ (Subgroup.inv_mem _ hc))
      have hcw : c • w ∈ L' := by
        rw [← hstab L' hL']
        exact Set.smul_mem_smul_set hw
      have hkcw : k • c • w ∈ L' := by
        rw [← mem_stabilizer_iff.mp (hKstab hL' hk)]
        exact Set.smul_mem_smul_set hcw
      have h4 := hN _ h2 _ hkcw
      have h5 : (c * k * c⁻¹ * k⁻¹) • k • c • w = c • k • w := by
        simp only [mul_smul, inv_smul_smul]
      rw [h5] at h4
      exact h4
    by_contra hcy
    have hyx : y ≠ x := fun h => hcy (h ▸ hcx)
    have hcyL' : c • y ∈ L' := by
      rw [← hstab L' hL']
      exact Set.smul_mem_smul_set hy
    have hcyx : c • y ≠ x := fun h => hyx (by rw [← hcx] at h; exact smul_left_cancel c h)
    obtain ⟨p, hp, q, hq, hpx, hpy, hpcy, hqx, hqy, hqcy, hpq⟩ :=
      exists_two_of_seven_le hL'l.seven_le x y (c • y)
    obtain ⟨k, hk, hky⟩ := hK' y hy p hp q hq hyx hpx hqx (Ne.symm hpy) (Ne.symm hqy) hpq
    have h6 := hcomL' k hk y hy
    rw [hky y hy, cyc3_apply_left (Ne.symm hpy) (Ne.symm hqy), hky _ hcyL',
      cyc3_apply_of_ne hcy (Ne.symm hpcy) (Ne.symm hqcy)] at h6
    exact hpy (smul_left_cancel c h6)
  have hmem : c ∈ lineFix G Λ x := mem_lineFix.mpr ⟨hcx, hfixL⟩
  rwa [hZ x hx] at hmem

end Kappa

section AxisSwap

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω] [FaithfulSMul G Ω] {Λ : Set Ω}

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem map_conj_lineKer (z : Ω) (L : Set Ω) (g : G) :
    (lineKer G Λ z L).map (MulAut.conj g).toMonoidHom = lineKer G Λ (g • z) (g • L) := by
  refine le_antisymm ?_ fun k hk => ⟨g⁻¹ * k * g⁻¹⁻¹, ?_, by simp [mul_assoc]⟩
  · rintro _ ⟨k, hk, rfl⟩
    exact conj_mem_lineKer hk g
  · simpa using conj_mem_lineKer hk g⁻¹

theorem Sec4Setting.commute_of_mem_lineGroup_of_mem_fixingSubgroup (hS : Sec4Setting G Ω)
    (hΛ : IsLine G Λ) (hND : LineNonDiagonal G Λ) {L : Set Ω} (hL : ∃ g : G, g • Λ = L)
    {m f : G} (hm : m ∈ lineGroup G Λ L) (hf : f ∈ fixingSubgroup G L) : m * f = f * m := by
  have hLl : IsLine G L := by
    obtain ⟨g, rfl⟩ := hL
    exact hΛ.smul g
  have hmL := lineGroup_le_stabilizer hLl.jClosed hm
  have hfL := fixingSubgroup_le_stabilizer G L hf
  have h1 : m * f * m⁻¹ * f⁻¹ ∈ lineGroup G Λ L := by
    have h2 : m * f * m⁻¹ * f⁻¹ = m * (f * m⁻¹ * f⁻¹) := by group
    rw [h2]
    refine Subgroup.mul_mem _ hm ?_
    simpa [mem_stabilizer_iff.mp hfL] using conj_mem_lineGroup (Subgroup.inv_mem _ hm) f
  have h3 : m * f * m⁻¹ * f⁻¹ ∈ fixingSubgroup G L :=
    Subgroup.mul_mem _ (conj_mem_fixingSubgroup hmL hf) (Subgroup.inv_mem _ hf)
  have h4 : m * f * m⁻¹ * f⁻¹ ∈ lineGroup G Λ L ⊓ fixingSubgroup G L := ⟨h1, h3⟩
  rw [hS.lineGroup_inf_fixingSubgroup_eq_bot hΛ hND hL, Subgroup.mem_bot] at h4
  calc m * f = (m * f * m⁻¹ * f⁻¹) * (f * m) := by group
    _ = f * m := by rw [h4, one_mul]

theorem Sec4Setting.commute_of_mem_lineKer (hS : Sec4Setting G Ω) (hΛ : IsLine G Λ)
    (hND : LineNonDiagonal G Λ) {y : Ω} {L L' : Set Ω} (hL : L ∈ linesThrough G Λ y)
    (hL' : L' ∈ linesThrough G Λ y) (hne : L ≠ L') {k k' : G} (hk : k ∈ lineKer G Λ y L)
    (hk' : k' ∈ lineKer G Λ y L') : k * k' = k' * k := by
  have hy : ∀ {u : G}, u ∈ lineKer G Λ y L → u • y = y := fun hu =>
    closure_longInvAt_le_stabilizer_point y (lineKer_le_closure hu)
  have hy' : ∀ {u : G}, u ∈ lineKer G Λ y L' → u • y = y := fun hu =>
    closure_longInvAt_le_stabilizer_point y (lineKer_le_closure hu)
  have hstab : ∀ {L'' : Set Ω}, L'' ∈ linesThrough G Λ y → ∀ {u : G},
      u ∈ Subgroup.closure (longInvAt G Ω y) → u • L'' = L'' := fun hL'' _ hu =>
    closure_longInvAt_le_stabilizer (hΛ.of_mem_linesThrough hL'').jClosed hL''.2 hu
  have h1 : k * k' * k⁻¹ * k'⁻¹ ∈ lineKer G Λ y L := by
    have h2 : k * k' * k⁻¹ * k'⁻¹ = k * (k' * k⁻¹ * k'⁻¹) := by group
    rw [h2]
    refine Subgroup.mul_mem _ hk ?_
    simpa [hy' hk', hstab hL (lineKer_le_closure hk')] using
      conj_mem_lineKer (Subgroup.inv_mem _ hk) k'
  have h3 : k * k' * k⁻¹ * k'⁻¹ ∈ lineKer G Λ y L' := by
    refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ hk')
    simpa [hy hk, hstab hL' (lineKer_le_closure hk)] using conj_mem_lineKer hk' k
  have h4 : k * k' * k⁻¹ * k'⁻¹ ∈ lineFix G Λ y :=
    mem_lineFix_of_mem_lineKer h1 ((mem_fixingSubgroup_iff G).mpr fun z hz =>
      lineKer_smul_eq h3 hL hne hz)
  rw [hS.lineFix_eq_bot hΛ hND hL, Subgroup.mem_bot] at h4
  calc k * k' = (k * k' * k⁻¹ * k'⁻¹) * (k' * k) := by group
    _ = k' * k := by rw [h4, one_mul]

theorem Sec4Setting.lineKer_smul_eq_lineKer (hS : Sec4Setting G Ω) (hΛ : IsLine G Λ)
    (hND : LineNonDiagonal G Λ) {y : Ω} {L L' : Set Ω} (hL : L ∈ linesThrough G Λ y)
    (hne : L' ≠ L) {m : G} (hm : m ∈ lineGroup G Λ L) :
    lineKer G Λ (m • y) (m • L') = lineKer G Λ y L' := by
  have hfix : ∀ {k : G}, k ∈ lineKer G Λ y L' → k ∈ fixingSubgroup G L := fun hk =>
    (mem_fixingSubgroup_iff G).mpr fun z hz => lineKer_smul_eq hk hL (Ne.symm hne) hz
  have hcomm : ∀ {k : G}, k ∈ lineKer G Λ y L' → m * k * m⁻¹ = k := fun hk => by
    rw [hS.commute_of_mem_lineGroup_of_mem_fixingSubgroup hΛ hND hL.1 hm (hfix hk),
      mul_inv_cancel_right]
  rw [← map_conj_lineKer]
  refine le_antisymm ?_ fun k hk => ⟨k, hk, hcomm hk⟩
  rintro _ ⟨k, hk, rfl⟩
  simpa [hcomm hk] using hk

theorem Sec4Setting.smul_eq_of_mem_normalizer (hS : Sec4Setting G Ω) (hΛ : IsLine G Λ)
    (hND : LineNonDiagonal G Λ) {x : Ω} {L₀ : Set Ω} (hL₀ : L₀ ∈ linesThrough G Λ x) {g : G}
    (hg : g ∈ Subgroup.normalizer
      ((⨆ L ∈ linesThrough G Λ x, lineKer G Λ x L : Subgroup G) : Set G)) : g • x = x := by
  have hpre := hS.preprimitive
  have htr := hS.star.isPretransitive
  set H : Subgroup G := ⨆ L ∈ linesThrough G Λ x, lineKer G Λ x L with hH
  have hGx : stabilizer G x ≤ Subgroup.normalizer (H : Set G) := by
    intro u hu
    have hux : u • x = x := hu
    have hmap : ∀ v : G, v • x = x → H.map (MulAut.conj v).toMonoidHom ≤ H := by
      intro v hv
      rw [hH, Subgroup.map_iSup]
      refine iSup_le fun L => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hL => ?_
      rw [map_conj_lineKer, hv]
      exact le_iSup₂_of_le (v • L) (by simpa [hv] using smul_mem_linesThrough hL v) le_rfl
    exact mem_normalizer_of_conj (fun z hz => hmap u hux ⟨z, hz, rfl⟩)
      (fun z hz => hmap u⁻¹ (by rw [inv_smul_eq_iff, hux]) ⟨z, hz, rfl⟩)
  by_contra hgx
  have hlt : stabilizer G x < Subgroup.normalizer (H : Set G) :=
    lt_of_le_of_ne hGx fun heq => hgx (heq ▸ hg : g ∈ stabilizer G x)
  have hL₀l := hΛ.of_mem_linesThrough hL₀
  obtain ⟨y, hy, -, -, -, -, -, -, hyx, -⟩ := exists_four_of_seven_le hL₀l.seven_le x
  have : Nontrivial Ω := ⟨⟨x, y, Ne.symm hyx⟩⟩
  have htop := (IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive G x).2 _ hlt
  have hHbot : H = ⊥ := eq_bot_of_normal_of_le_stabilizer
    (Subgroup.normalizer_eq_top_iff.mp htop) (iSup₂_le fun L _ =>
      lineKer_le_closure.trans (closure_longInvAt_le_stabilizer_point x))
  obtain ⟨k, hk, hky⟩ := (realizes3_lineKer hΛ hND hL₀).exists_smul_ne hL₀l.seven_le hy hyx
  have hle : lineKer G Λ x L₀ ≤ H := le_iSup₂_of_le L₀ hL₀ le_rfl
  have hkH : k ∈ H := hle hk
  rw [hHbot, Subgroup.mem_bot] at hkH
  exact hky (by rw [hkH, one_smul])

theorem Sec4Setting.smul_eq_of_forall_commute (hS : Sec4Setting G Ω) (hΛ : IsLine G Λ)
    (hND : LineNonDiagonal G Λ) {x : Ω} {L₀ : Set Ω} (hL₀ : L₀ ∈ linesThrough G Λ x) {g : G}
    (hg : ∀ L ∈ linesThrough G Λ x, ∀ k ∈ lineKer G Λ x L, k * g = g * k) : g • x = x := by
  have hle : (⨆ L ∈ linesThrough G Λ x, lineKer G Λ x L : Subgroup G) ≤
      Subgroup.centralizer {g} := iSup₂_le fun L hL k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hg L hL k hk)
  have hmem : g ∈ Subgroup.centralizer
      ((⨆ L ∈ linesThrough G Λ x, lineKer G Λ x L : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
  exact hS.smul_eq_of_mem_normalizer hΛ hND hL₀ (Subgroup.centralizer_le_normalizer _ hmem)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem smul_ne_of_mem_stabilizer {L L' : Set Ω} {m : G} (hm : m ∈ stabilizer G L)
    (hne : L' ≠ L) : m • L' ≠ L := fun h => hne (by
      rw [← mem_stabilizer_iff.mp hm] at h
      exact smul_left_cancel m h)

theorem Sec4Setting.lineKer_ne_lineKer (hS : Sec4Setting G Ω) (hΛ : IsLine G Λ)
    (hND : LineNonDiagonal G Λ) {x δ γ : Ω} {L₁ L₂ : Set Ω} (hL₁ : L₁ ∈ linesThrough G Λ x)
    (hL₂ : L₂ ∈ linesThrough G Λ x) (h12 : L₁ ≠ L₂) (hδ : δ ∈ L₁) (hδx : δ ≠ x) (hγ : γ ∈ L₂) :
    lineKer G Λ δ L₁ ≠ lineKer G Λ γ L₂ := by
  intro heq
  have hL₁l := hΛ.of_mem_linesThrough hL₁
  obtain ⟨m, hm, hmx⟩ := lineGroup_exists_smul_eq hΛ hND hL₁.1 hL₁.2 hδ
  obtain ⟨m', hm', hm'x⟩ := lineGroup_exists_smul_eq hΛ hND hL₂.1 hL₂.2 hγ
  have hmL := lineGroup_le_stabilizer hL₁l.jClosed hm
  have hm'L := lineGroup_le_stabilizer (hΛ.of_mem_linesThrough hL₂).jClosed hm'
  have hcomm : ∀ L ∈ linesThrough G Λ x, ∀ k ∈ lineKer G Λ x L, ∀ y ∈ lineKer G Λ δ L₁,
      k * y = y * k := by
    intro L hL k hk y hy
    by_cases h1 : L = L₁
    · subst h1
      have hT : lineKer G Λ γ (m' • L) = lineKer G Λ x L := by
        rw [← hm'x]
        exact hS.lineKer_smul_eq_lineKer hΛ hND hL₂ h12 hm'
      have hLγ : m' • L ∈ linesThrough G Λ γ := by
        simpa [hm'x] using smul_mem_linesThrough hL m'
      exact (hS.commute_of_mem_lineKer hΛ hND ⟨hL₂.1, hγ⟩ hLγ
        (Ne.symm (smul_ne_of_mem_stabilizer hm'L h12)) (heq ▸ hy) (hT ▸ hk)).symm
    · have hT : lineKer G Λ δ (m • L) = lineKer G Λ x L := by
        rw [← hmx]
        exact hS.lineKer_smul_eq_lineKer hΛ hND hL₁ h1 hm
      have hLδ : m • L ∈ linesThrough G Λ δ := by
        simpa [hmx] using smul_mem_linesThrough hL m
      exact (hS.commute_of_mem_lineKer hΛ hND ⟨hL₁.1, hδ⟩ hLδ
        (Ne.symm (smul_ne_of_mem_stabilizer hmL h1)) hy (hT ▸ hk)).symm
  obtain ⟨u, hu, hux⟩ := (realizes3_lineKer hΛ hND ⟨hL₁.1, hδ⟩).exists_smul_ne
    hL₁l.seven_le hL₁.2 (Ne.symm hδx)
  exact hux (hS.smul_eq_of_forall_commute hΛ hND hL₁ fun L hL k hk => hcomm L hL k hk u hu)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem exists_lift_line {L A : Set Ω} {x z : Ω} {m : G} (hm : m ∈ stabilizer G L)
    (hmx : m • x = z) (hA : A ∈ linesThrough G Λ z) (hne : A ≠ L) :
    ∃ B ∈ linesThrough G Λ x, B ≠ L ∧ m • B = A := by
  refine ⟨m⁻¹ • A, ?_, fun h => hne ?_, smul_inv_smul m A⟩
  · have h := smul_mem_linesThrough hA m⁻¹
    rwa [← hmx, inv_smul_smul] at h
  · rw [← smul_inv_smul m A, h, mem_stabilizer_iff.mp hm]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem map_conj_iSup_lineKer_le {x : Ω} {d : G}
    (h : ∀ L ∈ linesThrough G Λ x, ∃ L' ∈ linesThrough G Λ x,
      (lineKer G Λ x L).map (MulAut.conj d).toMonoidHom = lineKer G Λ x L') :
    (⨆ L ∈ linesThrough G Λ x, lineKer G Λ x L : Subgroup G).map (MulAut.conj d).toMonoidHom ≤
      ⨆ L ∈ linesThrough G Λ x, lineKer G Λ x L := by
  rw [Subgroup.map_iSup]
  refine iSup_le fun L => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hL => ?_
  obtain ⟨L', hL', hLL'⟩ := h L hL
  rw [hLL']
  exact le_iSup₂_of_le L' hL' le_rfl

theorem Sec4Setting.map_conj_lineKer_of_swap (hS : Sec4Setting G Ω) (hΛ : IsLine G Λ)
    (hND : LineNonDiagonal G Λ) {x δ γ : Ω} {L₁ L₂ : Set Ω} (hL₁ : L₁ ∈ linesThrough G Λ x)
    (hL₂ : L₂ ∈ linesThrough G Λ x) (h12 : L₁ ≠ L₂) (hδ : δ ∈ L₁) (hδx : δ ≠ x) (hγ : γ ∈ L₂)
    {d : G} (hd : d ∈ longInv G Ω) (hdγ : d • γ = δ) :
    (lineKer G Λ x L₁).map (MulAut.conj d).toMonoidHom = lineKer G Λ δ L₁ := by
  have hL₁l := hΛ.of_mem_linesThrough hL₁
  have hL₂l := hΛ.of_mem_linesThrough hL₂
  have hdd : d * d = 1 := mul_self_eq_one_of_mem_longInv hd
  have hdδ : d • δ = γ := by rw [← hdγ, ← mul_smul, hdd, one_smul]
  obtain ⟨m, hm, hmx⟩ := lineGroup_exists_smul_eq hΛ hND hL₁.1 hL₁.2 hδ
  obtain ⟨m', hm', hm'x⟩ := lineGroup_exists_smul_eq hΛ hND hL₂.1 hL₂.2 hγ
  have hmL := lineGroup_le_stabilizer hL₁l.jClosed hm
  have hm'L := lineGroup_le_stabilizer hL₂l.jClosed hm'
  have hf : ∀ z L, (lineKer G Λ z L).map (MulAut.conj d).toMonoidHom =
      lineKer G Λ (d • z) (d • L) := fun z L => map_conj_lineKer z L d
  have hff : ∀ X : Subgroup G, (X.map (MulAut.conj d).toMonoidHom).map
      (MulAut.conj d).toMonoidHom = X := by
    intro X
    rw [Subgroup.map_map]
    have hid : ((MulAut.conj d).toMonoidHom.comp (MulAut.conj d).toMonoidHom) =
        MonoidHom.id G := by
      ext g
      simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        MulAut.conj_apply, MonoidHom.id_apply]
      calc d * (d * g * d⁻¹) * d⁻¹ = (d * d) * g * (d * d)⁻¹ := by group
        _ = g := by rw [hdd, one_mul, inv_one, mul_one]
    rw [hid, Subgroup.map_id]
  have hT1 : ∀ L ∈ linesThrough G Λ x, L ≠ L₁ → lineKer G Λ δ (m • L) = lineKer G Λ x L :=
    fun L _ hne => by rw [← hmx]; exact hS.lineKer_smul_eq_lineKer hΛ hND hL₁ hne hm
  have hT2 : ∀ L ∈ linesThrough G Λ x, L ≠ L₂ → lineKer G Λ γ (m' • L) = lineKer G Λ x L :=
    fun L _ hne => by rw [← hm'x]; exact hS.lineKer_smul_eq_lineKer hΛ hND hL₂ hne hm'
  have hfixx : ∀ {L : Set Ω}, ∀ k ∈ lineKer G Λ x L, k • x = x := fun k hk =>
    closure_longInvAt_le_stabilizer_point x (lineKer_le_closure hk)
  obtain ⟨u, hu, hux⟩ := (realizes3_lineKer hΛ hND ⟨hL₁.1, hδ⟩).exists_smul_ne
    hL₁l.seven_le hL₁.2 (Ne.symm hδx)
  obtain ⟨v, hv, hvδ⟩ := (realizes3_lineKer hΛ hND hL₁).exists_smul_ne hL₁l.seven_le hδ hδx
  have hne_δx : ∀ {L : Set Ω}, lineKer G Λ x L ≠ lineKer G Λ δ L₁ := fun h =>
    hux (hfixx u (h ▸ hu))
  have hne_xx : ∀ {B : Set Ω}, B ∈ linesThrough G Λ x → B ≠ L₁ →
      lineKer G Λ x L₁ ≠ lineKer G Λ x B := fun hB hne h =>
    hvδ (lineKer_smul_eq (h ▸ hv) hL₁ (Ne.symm hne) hδ)
  have hmemγ : ∀ {L : Set Ω}, L ∈ linesThrough G Λ x → d • m' • L ∈ linesThrough G Λ δ :=
    fun hL => by
      have h := smul_mem_linesThrough (smul_mem_linesThrough hL m') d
      rwa [hm'x, hdγ] at h
  have hmemδ : ∀ {L : Set Ω}, L ∈ linesThrough G Λ x → d • m • L ∈ linesThrough G Λ γ :=
    fun hL => by
      have h := smul_mem_linesThrough (smul_mem_linesThrough hL m) d
      rwa [hmx, hdδ] at h
  have e1 : (lineKer G Λ x L₁).map (MulAut.conj d).toMonoidHom =
      lineKer G Λ δ (d • m' • L₁) := by rw [← hT2 L₁ hL₁ h12, hf, hdγ]
  by_contra hcon
  have hA1 : d • m' • L₁ ≠ L₁ := fun h => hcon (by rw [e1, h])
  obtain ⟨B, hB, hB1, hmB⟩ := exists_lift_line hmL hmx (hmemγ hL₁) hA1
  have e2 : (lineKer G Λ x L₁).map (MulAut.conj d).toMonoidHom = lineKer G Λ x B := by
    rw [e1, ← hmB, hT1 B hB hB1]
  by_cases hB2 : B = L₂
  · rw [hB2] at e2
    have e3 : (lineKer G Λ x L₂).map (MulAut.conj d).toMonoidHom = lineKer G Λ x L₁ := by
      rw [← e2, hff]
    have hmap : ∀ L ∈ linesThrough G Λ x, ∃ L' ∈ linesThrough G Λ x,
        (lineKer G Λ x L).map (MulAut.conj d).toMonoidHom = lineKer G Λ x L' := by
      intro L hL
      by_cases h1 : L = L₁
      · exact ⟨L₂, hL₂, by rw [h1, e2]⟩
      by_cases h2 : L = L₂
      · exact ⟨L₁, hL₁, by rw [h2, e3]⟩
      have e4 : (lineKer G Λ x L).map (MulAut.conj d).toMonoidHom =
          lineKer G Λ δ (d • m' • L) := by rw [← hT2 L hL h2, hf, hdγ]
      by_cases hA'1 : d • m' • L = L₁
      · exfalso
        have e5 : (lineKer G Λ x L).map (MulAut.conj d).toMonoidHom =
            lineKer G Λ γ (d • m • L) := by rw [← hT1 L hL h1, hf, hdδ]
        have e6 : lineKer G Λ δ L₁ = lineKer G Λ γ (d • m • L) := by rw [← hA'1, ← e4, e5]
        by_cases hA''2 : d • m • L = L₂
        · exact hS.lineKer_ne_lineKer hΛ hND hL₁ hL₂ h12 hδ hδx hγ (by rw [e6, hA''2])
        · obtain ⟨B', hB', hB'2, hm'B'⟩ := exists_lift_line hm'L hm'x (hmemδ hL) hA''2
          exact hne_δx (e6.trans (by rw [← hm'B', hT2 B' hB' hB'2])).symm
      · obtain ⟨B'', hB'', hB''1, hmB''⟩ := exists_lift_line hmL hmx (hmemγ hL) hA'1
        exact ⟨B'', hB'', by rw [e4, ← hmB'', hT1 B'' hB'' hB''1]⟩
    have hle := map_conj_iSup_lineKer_le hmap
    have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
    have hdx : d • x = x := hS.smul_eq_of_mem_normalizer hΛ hND hL₁
      (mem_normalizer_of_conj (fun z hz => hle ⟨z, hz, rfl⟩)
        (fun z hz => by rw [hdinv]; exact hle ⟨z, hz, rfl⟩))
    have hdL₂ : d • L₂ = L₂ := hL₂l.jClosed x hL₂.2 d ⟨hd, hdx⟩
    have hδL₂ : δ ∈ L₂ := by
      rw [← hdγ, ← hdL₂]
      exact Set.smul_mem_smul_set hγ
    exact h12 (hL₁l.eq_of_mem_of_mem hL₂l hL₁.2 hL₂.2 hδ hδL₂ (Ne.symm hδx))
  · have e8 : lineKer G Λ x L₁ = lineKer G Λ δ (d • m' • B) := by
      rw [← hff (lineKer G Λ x L₁), e2, ← hT2 B hB hB2, hf, hdγ]
    by_cases h3 : d • m' • B = L₁
    · exact hne_δx (h3 ▸ e8)
    · obtain ⟨B₃, hB₃, hB₃1, hmB₃⟩ := exists_lift_line hmL hmx (hmemγ hB) h3
      exact hne_xx hB₃ hB₃1 (e8.trans (by rw [← hmB₃, hT1 B₃ hB₃ hB₃1]))

theorem Sec4Setting.commute_of_mem_lineGroup (hS : Sec4Setting G Ω) (hΛ : IsLine G Λ)
    (hND : LineNonDiagonal G Λ) {x : Ω} {L₁ L₂ : Set Ω} (hL₁ : L₁ ∈ linesThrough G Λ x)
    (hL₂ : L₂ ∈ linesThrough G Λ x) (h12 : L₁ ≠ L₂) {a b : G} (ha : a ∈ lineGroup G Λ L₁)
    (hb : b ∈ lineGroup G Λ L₂) : a * b = b * a := by
  have hL₁l := hΛ.of_mem_linesThrough hL₁
  have hL₂l := hΛ.of_mem_linesThrough hL₂
  have hkk : ∀ δ ∈ L₁, ∀ γ ∈ L₂, ∀ k ∈ lineKer G Λ δ L₁, ∀ k' ∈ lineKer G Λ γ L₂,
      k * k' = k' * k := by
    intro δ hδ γ hγ k hk k' hk'
    obtain ⟨m, hm, hmx⟩ := lineGroup_exists_smul_eq hΛ hND hL₁.1 hL₁.2 hδ
    obtain ⟨m', hm', hm'x⟩ := lineGroup_exists_smul_eq hΛ hND hL₂.1 hL₂.2 hγ
    have hmL := lineGroup_le_stabilizer hL₁l.jClosed hm
    have hm'L := lineGroup_le_stabilizer hL₂l.jClosed hm'
    rcases eq_or_ne x δ with rfl | hδx <;> rcases eq_or_ne x γ with rfl | hγx
    · exact hS.commute_of_mem_lineKer hΛ hND hL₁ hL₂ h12 hk hk'
    · have hT : lineKer G Λ γ (m' • L₁) = lineKer G Λ x L₁ := by
        rw [← hm'x]
        exact hS.lineKer_smul_eq_lineKer hΛ hND hL₂ h12 hm'
      have hLγ : m' • L₁ ∈ linesThrough G Λ γ := by
        simpa [hm'x] using smul_mem_linesThrough hL₁ m'
      exact hS.commute_of_mem_lineKer hΛ hND hLγ ⟨hL₂.1, hγ⟩
        (smul_ne_of_mem_stabilizer hm'L h12) (hT ▸ hk) hk'
    · have hT : lineKer G Λ δ (m • L₂) = lineKer G Λ x L₂ := by
        rw [← hmx]
        exact hS.lineKer_smul_eq_lineKer hΛ hND hL₁ (Ne.symm h12) hm
      have hLδ : m • L₂ ∈ linesThrough G Λ δ := by
        simpa [hmx] using smul_mem_linesThrough hL₂ m
      exact hS.commute_of_mem_lineKer hΛ hND ⟨hL₁.1, hδ⟩ hLδ
        (Ne.symm (smul_ne_of_mem_stabilizer hmL (Ne.symm h12))) hk (hT ▸ hk')
    · obtain ⟨d, hd, hdγ⟩ := longInvSwap_nonempty hS.star γ δ
      have hdδ : d • δ = γ := by
        rw [← hdγ, ← mul_smul, mul_self_eq_one_of_mem_longInv hd, one_smul]
      have h1 := hS.map_conj_lineKer_of_swap hΛ hND hL₁ hL₂ h12 hδ (Ne.symm hδx) hγ hd hdγ
      have h2 := hS.map_conj_lineKer_of_swap hΛ hND hL₂ hL₁ (Ne.symm h12) hγ (Ne.symm hγx) hδ hd
        hdδ
      rw [← h1] at hk
      rw [← h2] at hk'
      obtain ⟨a, ha, rfl⟩ := hk
      obtain ⟨b, hb, rfl⟩ := hk'
      have hab := hS.commute_of_mem_lineKer hΛ hND hL₁ hL₂ h12 ha hb
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc d * a * d⁻¹ * (d * b * d⁻¹) = d * (a * b) * d⁻¹ := by group
        _ = d * (b * a) * d⁻¹ := by rw [hab]
        _ = d * b * d⁻¹ * (d * a * d⁻¹) := by group
  have hle : ∀ k ∈ lineGroup G Λ L₁, lineGroup G Λ L₂ ≤ Subgroup.centralizer {k} := by
    intro k hk
    refine lineGroup_le_centralizer fun γ hγ k' hk' => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hle1 : lineGroup G Λ L₁ ≤ Subgroup.centralizer {k'} :=
      lineGroup_le_centralizer fun δ hδ k'' hk'' => by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hkk δ hδ γ hγ k'' hk'' k' hk'
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle1 hk)).symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle a ha hb)).symm

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem map_conj_lineGroup (L : Set Ω) (g : G) :
    (lineGroup G Λ L).map (MulAut.conj g).toMonoidHom = lineGroup G Λ (g • L) := by
  refine le_antisymm ?_ fun k hk => ⟨g⁻¹ * k * g⁻¹⁻¹, ?_, by simp [mul_assoc]⟩
  · rintro _ ⟨k, hk, rfl⟩
    exact conj_mem_lineGroup hk g
  · simpa using conj_mem_lineGroup hk g⁻¹

end AxisSwap

section Endgame

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω] [FaithfulSMul G Ω] {Λ : Set Ω}

variable (G Λ) in
@[expose] def lineGroups (y : Ω) : Set (Subgroup G) :=
  {X | ∃ L ∈ linesThrough G Λ y, lineGroup G Λ L = X}

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem lineGroups_smul (g : G) (y : Ω) :
    lineGroups G Λ (g • y) = (fun X => X.map (MulAut.conj g).toMonoidHom) '' lineGroups G Λ y := by
  ext X
  constructor
  · rintro ⟨L, hL, rfl⟩
    refine ⟨lineGroup G Λ (g⁻¹ • L), ⟨g⁻¹ • L, by simpa using smul_mem_linesThrough hL g⁻¹, rfl⟩,
      ?_⟩
    simp only
    rw [map_conj_lineGroup, smul_inv_smul]
  · rintro ⟨_, ⟨L, hL, rfl⟩, rfl⟩
    exact ⟨g • L, smul_mem_linesThrough hL g, (map_conj_lineGroup L g).symm⟩

theorem Sec4Setting.lineGroups_subset (hS : Sec4Setting G Ω) (hΛ : IsLine G Λ)
    (hND : LineNonDiagonal G Λ) {L : Set Ω} (hL : ∃ g : G, g • Λ = L) {y z : Ω} (hy : y ∈ L)
    (hz : z ∈ L) : lineGroups G Λ y ⊆ lineGroups G Λ z := by
  rintro _ ⟨L', hL', rfl⟩
  obtain ⟨m, hm, hmy⟩ := lineGroup_exists_smul_eq hΛ hND hL hy hz
  rcases eq_or_ne L' L with rfl | hne
  · exact ⟨L', ⟨hL, hz⟩, rfl⟩
  refine ⟨m • L', by simpa [hmy] using smul_mem_linesThrough hL' m, ?_⟩
  rw [← map_conj_lineGroup]
  refine le_antisymm ?_ fun b hb => ⟨b, hb, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hS.commute_of_mem_lineGroup hΛ hND ⟨hL, hy⟩ hL' (Ne.symm hne) hm hb,
      mul_inv_cancel_right]
    exact hb
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hS.commute_of_mem_lineGroup hΛ hND ⟨hL, hy⟩ hL' (Ne.symm hne) hm hb,
      mul_inv_cancel_right]

theorem Sec4Setting.eq_univ_of_lineNonDiagonal (hS : Sec4Setting G Ω) (hΛ : IsLine G Λ)
    (hND : LineNonDiagonal G Λ) {α : Ω} (hα : α ∈ Λ) : Λ = Set.univ := by
  have hpre := hS.preprimitive
  have hinv : ∀ (g : G) {y z : Ω}, lineGroups G Λ y = lineGroups G Λ z →
      lineGroups G Λ (g • y) = lineGroups G Λ (g • z) := fun g y z h => by
    rw [lineGroups_smul, lineGroups_smul, h]
  set B : Set Ω := {y | lineGroups G Λ y = lineGroups G Λ α} with hBdef
  have hcoll : ∀ y ∈ Λ, y ∈ B := fun y hy => (hS.lineGroups_subset hΛ hND ⟨1, one_smul G Λ⟩
    hy hα).antisymm (hS.lineGroups_subset hΛ hND ⟨1, one_smul G Λ⟩ hα hy)
  have hblock : IsBlock G B := by
    rw [isBlock_iff_smul_eq_or_disjoint]
    intro g
    by_cases hdis : Disjoint (g • B) B
    · exact Or.inr hdis
    left
    obtain ⟨w, hwg, hwB⟩ := Set.not_disjoint_iff.mp hdis
    obtain ⟨y₀, hy₀, rfl⟩ := hwg
    have hsub : g • B ⊆ B := by
      rintro _ ⟨y, hy, rfl⟩
      show lineGroups G Λ (g • y) = lineGroups G Λ α
      rw [hinv g (hy.trans hy₀.symm)]
      exact hwB
    exact Set.eq_of_subset_of_ncard_le hsub (by rw [Set.ncard_smul_set]) (Set.toFinite B)
  have hB : B = Set.univ := by
    rcases IsPreprimitive.isTrivialBlock_of_isBlock hblock with h | h
    · exfalso
      obtain ⟨y, hy, -, -, -, -, -, -, hyα, -⟩ := exists_four_of_seven_le hΛ.seven_le α
      exact hyα (h (hcoll y hy) (hcoll α hα))
    · exact h
  have hnorm : ∀ t ∈ longInv G Ω, t ∈ Subgroup.normalizer (lineGroup G Λ Λ : Set G) := by
    intro t ht
    obtain ⟨y, hy⟩ := exists_mem_longInvAt ht
    have hyB : y ∈ B := hB ▸ Set.mem_univ y
    have hΛα : lineGroup G Λ Λ ∈ lineGroups G Λ α := ⟨Λ, ⟨⟨1, one_smul G Λ⟩, hα⟩, rfl⟩
    rw [← hyB] at hΛα
    obtain ⟨L, hL, hLΛ⟩ := hΛα
    have htL : t • L = L := (hΛ.of_mem_linesThrough hL).jClosed y hL.2 t hy
    have ht'L : t⁻¹ • L = L := by rw [inv_smul_eq_iff, htL]
    rw [← hLΛ]
    exact mem_normalizer_of_conj (fun z hz => by
        have h := conj_mem_lineGroup hz t
        rwa [htL] at h)
      (fun z hz => by
        have h := conj_mem_lineGroup hz t⁻¹
        rwa [ht'L] at h)
  have hN : (lineGroup G Λ Λ).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hS.jHull_eq_top, jHull,
      Subgroup.closure_le]
    exact hnorm
  have horbit : orbit (lineGroup G Λ Λ) α = Λ := by
    ext y
    constructor
    · rintro ⟨m, rfl⟩
      have hmΛ : (m : G) • Λ = Λ := lineGroup_le_stabilizer hΛ.jClosed m.2
      have h1 : (m : G) • α ∈ (m : G) • Λ := Set.smul_mem_smul_set hα
      rw [hmΛ] at h1
      exact h1
    · intro hy
      obtain ⟨m, hm, hmα⟩ := lineGroup_exists_smul_eq hΛ hND ⟨1, one_smul G Λ⟩ hα hy
      exact ⟨⟨m, hm⟩, hmα⟩
  have hΛblock : IsBlock G Λ := horbit ▸ IsBlock.orbit_of_normal α
  rcases IsPreprimitive.isTrivialBlock_of_isBlock hΛblock with h | h
  · exfalso
    obtain ⟨y, hy, -, -, -, -, -, -, hyα, -⟩ := exists_four_of_seven_le hΛ.seven_le α
    exact hyα (h hy hα)
  · exact h

end Endgame

section LineTheorem

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω]

omit [Finite G] in
theorem alternatingGroup_le_range_of_eq_univ {Λ : Set Ω} [DecidablePred (· ∈ Λ)]
    (hΛ : Λ = Set.univ) (hA : alternatingGroup Λ ≤ inducedPerm (stabilizer G Λ) Λ le_rfl) :
    alternatingGroup Ω ≤ (MulAction.toPermHom G Ω).range := by
  intro σ hσ
  have h₁ : ∀ y, σ y ∈ Λ ↔ y ∈ Λ := fun y => by simp [hΛ]
  have hσ' : Perm.subtypePerm σ h₁ ∈ alternatingGroup Λ := by
    rw [Perm.mem_alternatingGroup, Perm.sign_subtypePerm σ h₁ (fun y _ => by simp [hΛ])]
    exact hσ
  obtain ⟨g, -, hg⟩ := mem_inducedPerm.mp (hA hσ')
  refine ⟨g, Equiv.ext fun y => ?_⟩
  have h := hg ⟨y, by simp [hΛ]⟩
  simp only [Perm.subtypePerm_apply] at h
  exact h.symm

variable [FaithfulSMul G Ω]

theorem Sec4Setting.alternatingGroup_le_of_jClosed_of_lineNonDiagonal (hS : Sec4Setting G Ω)
    {α : Ω} {Λ : Set Ω} [DecidablePred (· ∈ Λ)]
    (hα : α ∈ Λ) (h7 : 7 ≤ Λ.ncard) (hJ : ∀ x ∈ Λ, ∀ t ∈ longInvAt G Ω x, t • Λ = Λ)
    (hA : alternatingGroup Λ ≤ inducedPerm (stabilizer G Λ) Λ le_rfl)
    (hND : LineNonDiagonal G Λ) :
    alternatingGroup Ω ≤ (MulAction.toPermHom G Ω).range := by
  by_cases hne : Λ = Set.univ
  · exact alternatingGroup_le_range_of_eq_univ hne hA
  exact absurd (hS.eq_univ_of_lineNonDiagonal (hS.isLine hα h7 hJ hA hne) hND hα) hne

end LineTheorem

section Preprimitive

theorem isPreprimitive_of_forall_exists_smul_eq {X Δ : Type*} [Group X] [MulAction X Δ]
    [Nontrivial Δ] (a : Δ) (htr : ∀ y : Δ, ∃ g : X, g • a = y)
    (hst : ∀ y z : Δ, y ≠ a → z ≠ a → ∃ g : X, g • a = a ∧ g • y = z) :
    IsPreprimitive X Δ := by
  have : IsPretransitive X Δ := ⟨fun y z => by
    obtain ⟨g₁, rfl⟩ := htr y
    obtain ⟨g₂, rfl⟩ := htr z
    exact ⟨g₂ * g₁⁻¹, by rw [mul_smul, inv_smul_smul]⟩⟩
  rw [← isCoatom_stabilizer_iff_preprimitive X a]
  refine ⟨fun htop => ?_, fun H hH => ?_⟩
  · obtain ⟨y, hy⟩ := exists_ne a
    obtain ⟨g, hg⟩ := htr y
    have hg' : g ∈ stabilizer X a := htop ▸ Subgroup.mem_top g
    exact hy (hg.symm.trans (mem_stabilizer_iff.mp hg'))
  obtain ⟨h, hhH, hh⟩ := IsConcreteLE.exists_of_lt hH
  rw [eq_top_iff]
  intro g _
  by_cases hga : g • a = a
  · exact hH.le hga
  obtain ⟨k, hka, hkh⟩ := hst (h • a) (g • a) hh hga
  have hk : k ∈ H := hH.le hka
  have hmem : (k * h)⁻¹ * g ∈ stabilizer X a := by
    rw [mem_stabilizer_iff, mul_smul, inv_smul_eq_iff, mul_smul, hkh]
  have := H.mul_mem (H.mul_mem hk hhH) (hH.le hmem)
  rwa [mul_inv_cancel_left] at this

end Preprimitive

section StepC

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] in
theorem smul_eq_of_smul_subset [Finite Ω] {S : Set Ω} {g : G} (h : g • S ⊆ S) : g • S = S :=
  Set.eq_of_subset_of_ncard_le h (by rw [Set.ncard_smul_set]) (Set.toFinite S)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] in
theorem exists_mem_longInvAt_smul_eq_of_two_transitive {α β : Ω} (hαβ : α ≠ β)
    (h2tr : ∀ δ₁ ∈ holtDelta G Ω α β, ∀ δ₂ ∈ holtDelta G Ω α β, ∀ δ₁' ∈ holtDelta G Ω α β,
      ∀ δ₂' ∈ holtDelta G Ω α β, δ₁ ≠ δ₂ → δ₁' ≠ δ₂' →
        ∃ g ∈ stabilizer G α ⊓ stabilizer G β, g • δ₁ = δ₁' ∧ g • δ₂ = δ₂')
    (hs : ∃ s ∈ longInvAt G Ω α, ∃ δ ∈ holtDelta G Ω α β, s • δ ∈ holtDelta G Ω α β) :
    ∀ δ ∈ holtDelta G Ω α β, ∀ δ' ∈ holtDelta G Ω α β, δ ≠ δ' →
      ∃ s ∈ longInvAt G Ω α, s • δ = δ' := by
  intro δ hδ δ' hδ' hne
  obtain ⟨s₀, hs₀, δ₀, hδ₀, hsδ₀⟩ := hs
  have hne₀ : δ₀ ≠ s₀ • δ₀ := fun h =>
    left_notMem_holtDelta hαβ (hs₀.1.2.unique h.symm hs₀.2 ▸ hδ₀)
  obtain ⟨g, hg, hgδ₀, hgs⟩ := h2tr δ₀ hδ₀ (s₀ • δ₀) hsδ₀ δ hδ δ' hδ' hne₀ hne
  have hgα : g • α = α := (Subgroup.mem_inf.mp hg).1
  refine ⟨g * s₀ * g⁻¹, by simpa [hgα] using conj_mem_longInvAt hs₀ g, ?_⟩
  calc (g * s₀ * g⁻¹) • δ = g • s₀ • g⁻¹ • g • δ₀ := by rw [← hgδ₀, mul_smul, mul_smul]
    _ = δ' := by rw [inv_smul_smul, hgs]

omit [DecidableEq Ω] in
theorem isJClosed_union_holtDelta (hG : IsStarGroup G Ω) {α β : Ω} (hαβ : α ≠ β)
    (h2tr : ∀ δ₁ ∈ holtDelta G Ω α β, ∀ δ₂ ∈ holtDelta G Ω α β, ∀ δ₁' ∈ holtDelta G Ω α β,
      ∀ δ₂' ∈ holtDelta G Ω α β, δ₁ ≠ δ₂ → δ₁' ≠ δ₂' →
        ∃ g ∈ stabilizer G α ⊓ stabilizer G β, g • δ₁ = δ₁' ∧ g • δ₂ = δ₂')
    (hΔ' : holtDelta' G Ω α β = holtDelta G Ω α β)
    (hs : ∃ s ∈ longInvAt G Ω α, ∃ δ ∈ holtDelta G Ω α β, s • δ ∈ holtDelta G Ω α β) :
    IsJClosed G Ω ({α, β} ∪ holtDelta G Ω α β) := by
  set Δ := holtDelta G Ω α β with hΔdef
  have hαΔ : α ∉ Δ := left_notMem_holtDelta hαβ
  have hβΔ : β ∉ Δ := right_notMem_holtDelta hαβ
  have hmemΛ : ∀ {y : Ω}, y ∈ ({α, β} ∪ Δ : Set Ω) ↔ y = α ∨ y = β ∨ y ∈ Δ := by
    intro y
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc]
  have hsβ : ∀ s ∈ longInvAt G Ω α, s • β ∈ Δ := fun s hs => hΔ' ▸ ⟨s, hs, rfl⟩
  have hβδ : ∀ δ ∈ Δ, ∃ s ∈ longInvAt G Ω α, s • β = δ := fun δ hδ => by
    rw [← hΔ'] at hδ
    exact hδ
  have hfix : ∀ {s : G}, s ∈ longInvAt G Ω α → ∀ {y : Ω}, s • y = y → y = α := fun hs _ hy =>
    hs.1.2.unique hy hs.2
  have hclique := exists_mem_longInvAt_smul_eq_of_two_transitive hαβ h2tr hs
  have hinv : ∀ {s : G}, s ∈ longInvAt G Ω α → ∀ y : Ω, s • s • y = y := fun hs y => by
    rw [← mul_smul, mul_self_eq_one_of_mem_longInv hs.1, one_smul]
  have hΔ'δ : ∀ δ ∈ Δ, holtDelta' G Ω α δ = insert β (Δ \ {δ}) := by
    intro δ hδ
    obtain ⟨s₁, hs₁, hs₁β⟩ := hβδ δ hδ
    have hcard : (holtDelta' G Ω α δ).ncard = Δ.ncard := by
      have h := smul_holtDelta' (G := G) s₁ α β
      rw [hs₁.2, hs₁β] at h
      rw [← h, Set.ncard_smul_set, hΔ']
    have hsub : insert β (Δ \ {δ}) ⊆ holtDelta' G Ω α δ := by
      rintro y (rfl | ⟨hy, hyδ⟩)
      · exact ⟨s₁, hs₁, by rw [← hs₁β, hinv hs₁]⟩
      · exact hclique δ hδ y hy (Ne.symm hyδ)
    refine (Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)).symm
    rw [hcard, Set.ncard_insert_of_notMem (fun h => hβΔ h.1),
      Set.ncard_sdiff_singleton_of_mem hδ]
    have : 0 < Δ.ncard := Set.ncard_pos (Set.toFinite _) |>.mpr ⟨δ, hδ⟩
    omega
  have hJα : ∀ s ∈ longInvAt G Ω α, s • ({α, β} ∪ Δ) = {α, β} ∪ Δ := by
    intro s hsα
    refine smul_eq_of_smul_subset ?_
    rintro _ ⟨y, hy, rfl⟩
    rcases hmemΛ.mp hy with h | h | hyΔ
    · rw [h]
      exact hmemΛ.mpr (Or.inl hsα.2)
    · rw [h]
      exact hmemΛ.mpr (Or.inr (Or.inr (hsβ s hsα)))
    · have hmem : s • y ∈ holtDelta' G Ω α y := ⟨s, hsα, rfl⟩
      rw [hΔ'δ y hyΔ] at hmem
      rcases hmem with h | ⟨h, -⟩
      · exact hmemΛ.mpr (Or.inr (Or.inl h))
      · exact hmemΛ.mpr (Or.inr (Or.inr h))
  obtain ⟨w, hw⟩ := longInvSwap_nonempty hG α β
  have hwβ : w • β = α := by rw [← hw.2, ← mul_smul, mul_self_eq_one_of_mem_longInv hw.1, one_smul]
  have hwΛ : w • ({α, β} ∪ Δ) = {α, β} ∪ Δ := by
    refine smul_eq_of_smul_subset ?_
    rintro _ ⟨y, hy, rfl⟩
    rcases hmemΛ.mp hy with h | h | hyΔ
    · rw [h]
      exact hmemΛ.mpr (Or.inr (Or.inl hw.2))
    · rw [h]
      exact hmemΛ.mpr (Or.inl hwβ)
    · have h := mem_stabilizer_holtDelta_of_mem_longInvSwap hw
      rw [mem_stabilizer_iff, ← hΔdef] at h
      have h2 : w • y ∈ w • Δ := Set.smul_mem_smul_set hyΔ
      rw [h] at h2
      exact hmemΛ.mpr (Or.inr (Or.inr h2))
  have hconj : ∀ {g t : G}, g • ({α, β} ∪ Δ) = {α, β} ∪ Δ →
      (g⁻¹ * t * g) • ({α, β} ∪ Δ) = {α, β} ∪ Δ → t • ({α, β} ∪ Δ) = {α, β} ∪ Δ := by
    intro g t hg ht
    have hg' : g⁻¹ • ({α, β} ∪ Δ) = {α, β} ∪ Δ := by rw [inv_smul_eq_iff, hg]
    calc t • ({α, β} ∪ Δ) = g • (g⁻¹ * t * g) • g⁻¹ • ({α, β} ∪ Δ) := by
          rw [smul_smul, smul_smul]; group
      _ = {α, β} ∪ Δ := by rw [hg', ht, hg]
  have hwβ' : w⁻¹ • β = α := by rw [inv_smul_eq_iff, hw.2]
  have hJβ : ∀ t ∈ longInvAt G Ω β, t • ({α, β} ∪ Δ) = {α, β} ∪ Δ := fun t ht =>
    hconj hwΛ (hJα _ (by simpa [hwβ'] using conj_mem_longInvAt ht w⁻¹))
  intro x hx t ht
  rcases hmemΛ.mp hx with h | h | hxΔ
  · rw [h] at ht
    exact hJα t ht
  · rw [h] at ht
    exact hJβ t ht
  · obtain ⟨s₁, hs₁, hs₁β⟩ := hβδ x hxΔ
    refine hconj (hJα s₁ hs₁) (hJβ _ ?_)
    have h := conj_mem_longInvAt ht s₁⁻¹
    rwa [← hs₁β, inv_smul_smul, inv_inv] at h

omit [Finite G] in
theorem alternatingGroup_le_inducedPerm_union {α β : Ω} (hαβ : α ≠ β) {Δ : Set Ω}
    [DecidablePred (· ∈ Δ)] [DecidablePred (· ∈ ({α, β} ∪ Δ : Set Ω))] (hαΔ : α ∉ Δ)
    (hβΔ : β ∉ Δ) (h3 : 3 ≤ Δ.ncard) (hle : stabilizer G α ⊓ stabilizer G β ≤ stabilizer G Δ)
    (hAlt : alternatingGroup Δ ≤ inducedPerm (stabilizer G α ⊓ stabilizer G β) Δ hle)
    (hJα : ∀ s ∈ longInvAt G Ω α, s ∈ stabilizer G ({α, β} ∪ Δ))
    (hw : ∃ w ∈ stabilizer G ({α, β} ∪ Δ), w • α = β)
    (hβδ : ∀ δ ∈ Δ, ∃ s ∈ longInvAt G Ω α, s • β = δ)
    (hclique : ∀ δ ∈ Δ, ∀ δ' ∈ Δ, δ ≠ δ' → ∃ s ∈ longInvAt G Ω α, s • δ = δ') :
    alternatingGroup ↥({α, β} ∪ Δ) ≤
      inducedPerm (stabilizer G ({α, β} ∪ Δ)) ({α, β} ∪ Δ) le_rfl := by
  have hαΛ : α ∈ ({α, β} ∪ Δ : Set Ω) := Or.inl (Or.inl rfl)
  have hβΛ : β ∈ ({α, β} ∪ Δ : Set Ω) := Or.inl (Or.inr rfl)
  have hΔΛ : ∀ {δ : Ω}, δ ∈ Δ → δ ∈ ({α, β} ∪ Δ : Set Ω) := fun h => Or.inr h
  have hmemΛ : ∀ {y : Ω}, y ∈ ({α, β} ∪ Δ : Set Ω) ↔ y = α ∨ y = β ∨ y ∈ Δ := by
    intro y
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc]
  let elt : ∀ g ∈ stabilizer G ({α, β} ∪ Δ),
      inducedPerm (stabilizer G ({α, β} ∪ Δ)) ({α, β} ∪ Δ) le_rfl := fun g hg =>
    ⟨inducedHom (stabilizer G ({α, β} ∪ Δ)) ({α, β} ∪ Δ) le_rfl ⟨g, hg⟩, ⟨g, hg⟩, rfl⟩
  have helt : ∀ g (hg : g ∈ stabilizer G ({α, β} ∪ Δ)) (y : ↥({α, β} ∪ Δ : Set Ω)),
      ((elt g hg • y : ↥({α, β} ∪ Δ : Set Ω)) : Ω) = g • (y : Ω) :=
    fun _ _ _ => rfl
  have hinv : ∀ {s : G}, s ∈ longInvAt G Ω α → ∀ y : Ω, s • s • y = y := fun hs y => by
    rw [← mul_smul, mul_self_eq_one_of_mem_longInv hs.1, one_smul]
  obtain ⟨w, hwΛ, hwα⟩ := hw
  have : Nontrivial ↥({α, β} ∪ Δ : Set Ω) :=
    ⟨⟨⟨α, hαΛ⟩, ⟨β, hβΛ⟩, fun h => hαβ (congrArg Subtype.val h)⟩⟩
  have hprim : IsPreprimitive (inducedPerm (stabilizer G ({α, β} ∪ Δ)) ({α, β} ∪ Δ) le_rfl)
      ↥({α, β} ∪ Δ : Set Ω) := by
    refine isPreprimitive_of_forall_exists_smul_eq ⟨α, hαΛ⟩ (fun y => ?_) (fun y z hy hz => ?_)
    · rcases hmemΛ.mp y.2 with h | h | hyΔ
      · exact ⟨1, Subtype.ext (by rw [one_smul]; exact h.symm)⟩
      · exact ⟨elt w hwΛ, Subtype.ext (by rw [helt]; exact hwα.trans h.symm)⟩
      · obtain ⟨s₁, hs₁, hs₁β⟩ := hβδ y hyΔ
        refine ⟨elt (s₁ * w) (Subgroup.mul_mem _ (hJα s₁ hs₁) hwΛ), Subtype.ext ?_⟩
        rw [helt, mul_smul]
        exact (congrArg (s₁ • ·) hwα).trans hs₁β
    · have hy' : (y : Ω) ≠ α := fun h => hy (Subtype.ext h)
      have hz' : (z : Ω) ≠ α := fun h => hz (Subtype.ext h)
      obtain ⟨g, hg, hgα, hgy⟩ : ∃ g ∈ stabilizer G ({α, β} ∪ Δ), g • α = α ∧ g • (y : Ω) = z := by
        rcases eq_or_ne (y : Ω) z with hyz | hyz
        · exact ⟨1, Subgroup.one_mem _, one_smul G α, by rw [one_smul, hyz]⟩
        rcases hmemΛ.mp y.2 with h | h | hyΔ
        · exact absurd h hy'
        · rcases hmemΛ.mp z.2 with h' | h' | hzΔ
          · exact absurd h' hz'
          · exact absurd (h.trans h'.symm) hyz
          · obtain ⟨s₁, hs₁, hs₁β⟩ := hβδ z hzΔ
            exact ⟨s₁, hJα s₁ hs₁, hs₁.2, by rw [h, hs₁β]⟩
        · rcases hmemΛ.mp z.2 with h' | h' | hzΔ
          · exact absurd h' hz'
          · obtain ⟨s₁, hs₁, hs₁β⟩ := hβδ y hyΔ
            exact ⟨s₁, hJα s₁ hs₁, hs₁.2, by rw [h', ← hs₁β, hinv hs₁]⟩
          · obtain ⟨s, hs, hsy⟩ := hclique y hyΔ z hzΔ hyz
            exact ⟨s, hJα s hs, hs.2, hsy⟩
      exact ⟨elt g hg, Subtype.ext (by rw [helt]; exact hgα), Subtype.ext (by rw [helt]; exact hgy)⟩
  obtain ⟨a, ha, -⟩ := exists_mem_notMem_of_card_lt_ncard (L := Δ) ∅
    (by rw [Finset.card_empty]; omega)
  obtain ⟨b, hb, hb'⟩ := exists_mem_notMem_of_card_lt_ncard (L := Δ) {a}
    (by rw [Finset.card_singleton]; omega)
  obtain ⟨c, hc, hc'⟩ := exists_mem_notMem_of_card_lt_ncard (L := Δ) {a, b}
    ((Finset.card_le_two).trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb' hc'
  have hab : a ≠ b := Ne.symm hb'
  have hac : a ≠ c := Ne.symm hc'.1
  have hbc : b ≠ c := Ne.symm hc'.2
  have hσΔ : swap (⟨a, ha⟩ : Δ) ⟨b, hb⟩ * swap ⟨a, ha⟩ ⟨c, hc⟩ ∈ alternatingGroup Δ := by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul,
      Perm.sign_swap (by simpa [Subtype.ext_iff] using hab),
      Perm.sign_swap (by simpa [Subtype.ext_iff] using hac)]
    rfl
  obtain ⟨g, hg, hgσ⟩ := mem_inducedPerm.mp (hAlt hσΔ)
  have hgα : g • α = α := (Subgroup.mem_inf.mp hg).1
  have hgβ : g • β = β := (Subgroup.mem_inf.mp hg).2
  have hgΔ : g • Δ = Δ := hle hg
  have hgΛ : g ∈ stabilizer G ({α, β} ∪ Δ) := by
    refine smul_eq_of_smul_subset ?_
    rintro _ ⟨y, hy, rfl⟩
    rcases hmemΛ.mp hy with h | h | hyΔ
    · show g • y ∈ _
      rw [h, hgα]
      exact hαΛ
    · show g • y ∈ _
      rw [h, hgβ]
      exact hβΛ
    · have h2 : g • y ∈ g • Δ := Set.smul_mem_smul_set hyΔ
      rw [hgΔ] at h2
      exact hΔΛ h2
  obtain ⟨a', ha'⟩ : ∃ a' : ↥({α, β} ∪ Δ : Set Ω), (a' : Ω) = a := ⟨⟨a, hΔΛ ha⟩, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b' : ↥({α, β} ∪ Δ : Set Ω), (b' : Ω) = b := ⟨⟨b, hΔΛ hb⟩, rfl⟩
  obtain ⟨c', hc'⟩ : ∃ c' : ↥({α, β} ∪ Δ : Set Ω), (c' : Ω) = c := ⟨⟨c, hΔΛ hc⟩, rfl⟩
  have hσΛ : (swap a' b' * swap a' c').IsThreeCycle :=
    Perm.isThreeCycle_swap_mul_swap_same (fun h => hab (by rw [← ha', ← hb', h]))
      (fun h => hac (by rw [← ha', ← hc', h])) (fun h => hbc (by rw [← hb', ← hc', h]))
  have hσmem : swap a' b' * swap a' c' ∈
      inducedPerm (stabilizer G ({α, β} ∪ Δ)) ({α, β} ∪ Δ) le_rfl := by
    refine mem_inducedPerm.mpr ⟨g, hgΛ, fun y => ?_⟩
    rw [Perm.mul_apply, coe_swap, coe_swap, ha', hb', hc']
    rcases hmemΛ.mp y.2 with h | h | hyΔ
    · have hya : (y : Ω) ≠ a := fun e => hαΔ (h ▸ e ▸ ha)
      have hyb : (y : Ω) ≠ b := fun e => hαΔ (h ▸ e ▸ hb)
      have hyc : (y : Ω) ≠ c := fun e => hαΔ (h ▸ e ▸ hc)
      rw [swap_apply_of_ne_of_ne hya hyc, swap_apply_of_ne_of_ne hya hyb, h, hgα]
    · have hya : (y : Ω) ≠ a := fun e => hβΔ (h ▸ e ▸ ha)
      have hyb : (y : Ω) ≠ b := fun e => hβΔ (h ▸ e ▸ hb)
      have hyc : (y : Ω) ≠ c := fun e => hβΔ (h ▸ e ▸ hc)
      rw [swap_apply_of_ne_of_ne hya hyc, swap_apply_of_ne_of_ne hya hyb, h, hgβ]
    · have h1 := hgσ ⟨y, hyΔ⟩
      rw [Perm.mul_apply, coe_swap_mk, coe_swap_mk] at h1
      exact h1
  exact Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim hσΛ hσmem

omit [Finite G] in
theorem two_transitive_of_alternatingGroup_le {α β : Ω} {Δ : Set Ω} [DecidablePred (· ∈ Δ)]
    (h4 : 4 ≤ Δ.ncard) (hle : stabilizer G α ⊓ stabilizer G β ≤ stabilizer G Δ)
    (hAlt : alternatingGroup Δ ≤ inducedPerm (stabilizer G α ⊓ stabilizer G β) Δ hle) :
    ∀ δ₁ ∈ Δ, ∀ δ₂ ∈ Δ, ∀ δ₁' ∈ Δ, ∀ δ₂' ∈ Δ, δ₁ ≠ δ₂ → δ₁' ≠ δ₂' →
      ∃ g ∈ stabilizer G α ⊓ stabilizer G β, g • δ₁ = δ₁' ∧ g • δ₂ = δ₂' := by
  intro δ₁ h₁ δ₂ h₂ δ₁' h₁' δ₂' h₂' h12 h12'
  have hcard : 4 ≤ Fintype.card Δ := by rwa [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hne : ∀ {u v : Δ}, (u : Ω) ≠ v → u ≠ v := fun h h' => h (congrArg Subtype.val h')
  obtain ⟨σ₁, hσ₁, hσ₁δ⟩ : ∃ σ ∈ alternatingGroup Δ, σ ⟨δ₁, h₁⟩ = ⟨δ₁', h₁'⟩ := by
    rcases eq_or_ne δ₁ δ₁' with h | h
    · exact ⟨1, Subgroup.one_mem _, Subtype.ext h⟩
    obtain ⟨z, hz, hz'⟩ := exists_mem_notMem_of_card_lt_ncard (L := Δ) {δ₁, δ₁'}
      ((Finset.card_le_two).trans_lt (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz'
    obtain ⟨σ, hσ, -, hσz⟩ := exists_mem_alternatingGroup_fix_apply_eq hcard
      (α := ⟨z, hz⟩) (γ := ⟨δ₁, h₁⟩) (δ := ⟨δ₁', h₁'⟩) (hne (Ne.symm hz'.1))
      (hne (Ne.symm hz'.2))
    exact ⟨σ, hσ, hσz⟩
  have hσ₁δ₂ : σ₁ ⟨δ₂, h₂⟩ ≠ ⟨δ₁', h₁'⟩ := fun h =>
    h12 (congrArg Subtype.val (σ₁.injective (h.trans hσ₁δ.symm))).symm
  obtain ⟨σ₂, hσ₂, hσ₂δ₁', hσ₂δ₂⟩ := exists_mem_alternatingGroup_fix_apply_eq hcard
    (α := ⟨δ₁', h₁'⟩) (γ := σ₁ ⟨δ₂, h₂⟩) (δ := ⟨δ₂', h₂'⟩) hσ₁δ₂ (hne (Ne.symm h12'))
  obtain ⟨g, hg, hgσ⟩ := mem_inducedPerm.mp (hAlt (Subgroup.mul_mem _ hσ₂ hσ₁))
  refine ⟨g, hg, ?_, ?_⟩
  · rw [← hgσ ⟨δ₁, h₁⟩, Perm.mul_apply, hσ₁δ, hσ₂δ₁']
  · rw [← hgσ ⟨δ₂, h₂⟩, Perm.mul_apply, hσ₂δ₂]

variable [FaithfulSMul G Ω]

theorem Sec4Setting.false_of_stepC (hS : Sec4Setting G Ω) {α β : Ω} (hαβ : α ≠ β)
    [DecidablePred (· ∈ holtDelta G Ω α β)] (h5 : 5 ≤ (holtDelta G Ω α β).ncard)
    (hAlt : alternatingGroup (holtDelta G Ω α β) ≤
      inducedPerm (stabilizer G α ⊓ stabilizer G β) (holtDelta G Ω α β)
        ((stabilizer_inf_le_stabilizer_pair α β).trans (stabilizer_pair_le α β)))
    (hΔ' : holtDelta' G Ω α β = holtDelta G Ω α β)
    (hs : ∃ s ∈ longInvAt G Ω α, ∃ δ ∈ holtDelta G Ω α β, s • δ ∈ holtDelta G Ω α β)
    (hND : LineNonDiagonal G ({α, β} ∪ holtDelta G Ω α β)) : False := by
  classical
  have hαΔ : α ∉ holtDelta G Ω α β := left_notMem_holtDelta hαβ
  have hβΔ : β ∉ holtDelta G Ω α β := right_notMem_holtDelta hαβ
  have hαΛ : α ∈ ({α, β} ∪ holtDelta G Ω α β : Set Ω) := Or.inl (Or.inl rfl)
  have h2tr := two_transitive_of_alternatingGroup_le (by omega) _ hAlt
  have hJ := isJClosed_union_holtDelta hS.star hαβ h2tr hΔ' hs
  have hclique := exists_mem_longInvAt_smul_eq_of_two_transitive hαβ h2tr hs
  have hβδ : ∀ δ ∈ holtDelta G Ω α β, ∃ s ∈ longInvAt G Ω α, s • β = δ := fun δ hδ => by
    rw [← hΔ'] at hδ
    exact hδ
  obtain ⟨w, hw⟩ := longInvSwap_nonempty hS.star α β
  obtain ⟨δw, hδw, -⟩ := hw.1.2
  have hwΛ : w ∈ stabilizer G ({α, β} ∪ holtDelta G Ω α β) :=
    hJ δw (Or.inr ⟨w, hw, hδw⟩) w ⟨hw.1, hδw⟩
  have hA := alternatingGroup_le_inducedPerm_union hαβ hαΔ hβΔ (by omega) _ hAlt
    (fun s hs => hJ α hαΛ s hs) ⟨w, hwΛ, hw.2⟩ hβδ hclique
  have h7 : 7 ≤ ({α, β} ∪ holtDelta G Ω α β : Set Ω).ncard := by
    rw [Set.ncard_union_eq (Set.disjoint_left.mpr fun y hy hyΔ => by
      rcases hy with rfl | rfl
      exacts [hαΔ hyΔ, hβΔ hyΔ]), Set.ncard_pair hαβ]
    omega
  have hAltΩ : alternatingGroup Ω ≤ (MulAction.toPermHom G Ω).range := by
    refine hS.alternatingGroup_le_of_jClosed_of_lineNonDiagonal
      (Λ := {α, β} ∪ holtDelta G Ω α β) hαΛ h7 ?_ ?_ ?_
    · exact hJ
    · convert hA
    · exact hND
  exact hS.not_conclusion (Or.inl hAltΩ)

end StepC

section StepCW

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω] [FaithfulSMul G Ω]

omit [Finite G] [Fintype Ω] [MulAction G Ω] [FaithfulSMul G Ω] in
theorem swap_mul_swap_mul_self {X : Type*} [DecidableEq X] {a b c d : X} (hab : a ≠ b)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    swap a b * swap c d * (swap a b * swap c d) = 1 := by
  ext y
  simp only [Perm.mul_apply, Perm.one_apply]
  by_cases h1 : y = a
  · subst h1; simp [swap_apply_of_ne_of_ne, *]
  by_cases h2 : y = b
  · subst h2; simp [swap_apply_of_ne_of_ne, *]
  by_cases h3 : y = c
  · subst h3; simp [swap_apply_of_ne_of_ne, *, Ne.symm]
  by_cases h4 : y = d
  · subst h4; simp [swap_apply_of_ne_of_ne, *, Ne.symm]
  simp [swap_apply_of_ne_of_ne, *]

theorem Sec4Setting.exists_smul_mem_holtDelta_of_fixSet (hS : Sec4Setting G Ω) {α β : Ω}
    (hαβ : α ≠ β) {W : Subgroup G} (hW : IsPGroup 2 W) {δ₁ δ₂ δ₃ : Ω}
    (h₁ : δ₁ ∈ holtDelta G Ω α β) (h₂ : δ₂ ∈ holtDelta G Ω α β) (h₃ : δ₃ ∈ holtDelta G Ω α β)
    (h12 : δ₁ ≠ δ₂) (h13 : δ₁ ≠ δ₃) (h23 : δ₂ ≠ δ₃) (hF : fixSet Ω W = {α, β, δ₁, δ₂, δ₃})
    [DecidablePred (· ∈ fixSet Ω W)]
    (hA5 : alternatingGroup (fixSet Ω W) ≤ centralizerImage Ω W) :
    ∃ s ∈ longInvAt G Ω α, ∃ δ ∈ holtDelta G Ω α β, s • δ ∈ holtDelta G Ω α β := by
  have hαΔ : ∀ {δ : Ω}, δ ∈ holtDelta G Ω α β → α ≠ δ := fun hδ h =>
    left_notMem_holtDelta hαβ (by subst h; exact hδ)
  have hβΔ : ∀ {δ : Ω}, δ ∈ holtDelta G Ω α β → β ≠ δ := fun hδ h =>
    right_notMem_holtDelta hαβ (by subst h; exact hδ)
  have hmem : ∀ {y : Ω}, y ∈ fixSet Ω W ↔ y = α ∨ y = β ∨ y = δ₁ ∨ y = δ₂ ∨ y = δ₃ := by
    intro y
    rw [hF]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hα : α ∈ fixSet Ω W := hmem.mpr (Or.inl rfl)
  have hβ : β ∈ fixSet Ω W := hmem.mpr (Or.inr (Or.inl rfl))
  have hd₁ : δ₁ ∈ fixSet Ω W := hmem.mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hd₂ : δ₂ ∈ fixSet Ω W := hmem.mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hd₃ : δ₃ ∈ fixSet Ω W := hmem.mpr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  have hne : ∀ {u v : Ω} (hu : u ∈ fixSet Ω W) (hv : v ∈ fixSet Ω W), u ≠ v →
      (⟨u, hu⟩ : fixSet Ω W) ≠ ⟨v, hv⟩ := fun _ _ h h' => h (congrArg Subtype.val h')
  set π : Perm (fixSet Ω W) := swap ⟨β, hβ⟩ ⟨δ₁, hd₁⟩ * swap ⟨δ₂, hd₂⟩ ⟨δ₃, hd₃⟩ with hπ
  have hπA : π ∈ alternatingGroup (fixSet Ω W) := by
    rw [Perm.mem_alternatingGroup, hπ, Perm.sign_mul, Perm.sign_swap (hne _ _ (hβΔ h₁)),
      Perm.sign_swap (hne _ _ h23)]
    rfl
  have hππ : π * π = 1 := swap_mul_swap_mul_self (hne _ _ (hβΔ h₁)) (hne _ _ (hβΔ h₂))
    (hne _ _ (hβΔ h₃)) (hne _ _ h12) (hne _ _ h13) (hne _ _ h23)
  have hπfix : ∀ ε : fixSet Ω W, π ε = ε ↔ ε = ⟨α, hα⟩ := by
    rintro ⟨y, hy⟩
    constructor
    · intro h
      have h' := congrArg Subtype.val h
      rw [hπ, Perm.mul_apply, coe_swap, coe_swap] at h'
      simp only at h'
      rcases hmem.mp hy with rfl | rfl | rfl | rfl | rfl
      · rfl
      · exfalso
        rw [swap_apply_of_ne_of_ne (hβΔ h₂) (hβΔ h₃), swap_apply_left] at h'
        exact hβΔ h₁ h'.symm
      · exfalso
        rw [swap_apply_of_ne_of_ne h12 h13, swap_apply_right] at h'
        exact hβΔ h₁ h'
      · exfalso
        rw [swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm (hβΔ h₃)) (Ne.symm h13)] at h'
        exact h23 h'.symm
      · exfalso
        rw [swap_apply_right, swap_apply_of_ne_of_ne (Ne.symm (hβΔ h₂)) (Ne.symm h12)] at h'
        exact h23 h'
    · rintro ⟨⟩
      apply Subtype.ext
      rw [hπ, Perm.mul_apply, coe_swap, coe_swap]
      simp only
      rw [swap_apply_of_ne_of_ne (hαΔ h₂) (hαΔ h₃), swap_apply_of_ne_of_ne hαβ (hαΔ h₁)]
  have hπJ : (⟨π, hA5 hπA⟩ : centralizerImage Ω W) ∈
      longInvAt (centralizerImage Ω W) (fixSet Ω W) ⟨α, hα⟩ :=
    mem_longInvAt_of_mul_self (Subtype.ext hππ) (fun ε => hπfix ε)
      ⟨⟨β, hβ⟩, hne _ _ (Ne.symm hαβ)⟩
  have h3 : 3 ≤ Nat.card (fixSet Ω W) := by
    rw [Nat.card_coe_set_eq]
    calc 3 = ({α, β, δ₁} : Set Ω).ncard := by
          rw [Set.ncard_eq_three.mpr ⟨α, β, δ₁, hαβ, hαΔ h₁, hβΔ h₁, rfl⟩]
      _ ≤ (fixSet Ω W).ncard := Set.ncard_le_ncard (by
          rintro y (rfl | rfl | rfl)
          exacts [hα, hβ, hd₁]) (Set.toFinite _)
  obtain ⟨c, hc, -, hcπ⟩ := (hS.mem_longInvAt_centralizerImage_iff hW h3 _).mp hπJ
  refine ⟨c, hc, δ₂, h₂, ?_⟩
  have h := hcπ ⟨δ₂, hd₂⟩
  rw [← h]
  simp only [hπ, Perm.mul_apply, coe_swap, swap_apply_left]
  rw [swap_apply_of_ne_of_ne (Ne.symm (hβΔ h₃)) (Ne.symm h13)]
  exact h₃

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem sq_mem_stabilizer_inf_of_mem_stabilizer_pair {α β : Ω} (hαβ : α ≠ β) {g : G}
    (hg : g ∈ stabilizer G ({α, β} : Set Ω)) : g ^ 2 ∈ stabilizer G α ⊓ stabilizer G β := by
  have hmem : ∀ {y : Ω}, y ∈ ({α, β} : Set Ω) → g • y ∈ ({α, β} : Set Ω) := fun hy => by
    rw [← mem_stabilizer_iff.mp hg]
    exact Set.smul_mem_smul_set hy
  have hgα := hmem (Or.inl rfl : α ∈ ({α, β} : Set Ω))
  have hgβ := hmem (Or.inr rfl : β ∈ ({α, β} : Set Ω))
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgα hgβ
  rw [Subgroup.mem_inf, mem_stabilizer_iff, mem_stabilizer_iff, pow_two, mul_smul, mul_smul]
  rcases hgα with h1 | h1 <;> rcases hgβ with h2 | h2
  · exact absurd (smul_left_cancel g (h1.trans h2.symm)) hαβ
  · exact ⟨by rw [h1, h1], by rw [h2, h2]⟩
  · exact ⟨by rw [h1, h2], by rw [h2, h1]⟩
  · exact absurd (smul_left_cancel g (h1.trans h2.symm)) hαβ

omit [Finite G] [FaithfulSMul G Ω] in
theorem alternatingGroup_le_inducedPerm_inf {α β : Ω} (hαβ : α ≠ β)
    [DecidablePred (· ∈ holtDelta G Ω α β)]
    (h : alternatingGroup (holtDelta G Ω α β) ≤ twoPointSection G Ω α β) :
    alternatingGroup (holtDelta G Ω α β) ≤
      inducedPerm (stabilizer G α ⊓ stabilizer G β) (holtDelta G Ω α β)
        ((stabilizer_inf_le_stabilizer_pair α β).trans (stabilizer_pair_le α β)) := by
  rw [← Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
  intro c hc
  have hcA : c ∈ alternatingGroup (holtDelta G Ω α β) := by
    rw [← Perm.closure_three_cycles_eq_alternating]
    exact Subgroup.subset_closure hc
  obtain ⟨g, hg, hgc⟩ := mem_inducedPerm.mp (h hcA)
  have hc4 : c = c ^ 4 := by
    have h3 : c ^ 3 = 1 := by rw [← hc.orderOf]; exact pow_orderOf_eq_one c
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, h3, one_mul]
  have hg4 : g ^ 4 ∈ stabilizer G α ⊓ stabilizer G β := by
    rw [show g ^ 4 = (g ^ 2) ^ 2 by rw [← pow_mul]]
    exact Subgroup.pow_mem _ (sq_mem_stabilizer_inf_of_mem_stabilizer_pair hαβ hg) 2
  refine mem_inducedPerm.mpr ⟨g ^ 4, hg4, fun ω => ?_⟩
  rw [hc4]
  clear hc4
  induction (4 : ℕ) generalizing ω with
  | zero => simp
  | succ n ih => rw [pow_succ, Perm.mul_apply, ih, pow_succ, mul_smul, hgc]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem AltConfig.exists_bijective_coord {α β : Ω} (C : AltConfig G Ω α β)
    (hr : Fintype.card C.D.ι = 1) :
    ∃ i₀ : C.D.ι, Function.Bijective fun δ : holtDelta G Ω α β => C.D.coord δ i₀ := by
  obtain ⟨i₀, hi₀⟩ := Fintype.card_eq_one_iff.mp hr
  refine ⟨i₀, fun δ δ' h => ?_, fun b => C.D.exists_coord_apply_eq i₀ b⟩
  have hcoord : C.D.coord δ = C.D.coord δ' := funext fun i => by
    rw [hi₀ i]
    exact h
  have h' := (C.D.coord_eq_iff δ δ').mp hcoord
  rw [orbit_jOddCore_eq_singleton C.oddCore_eq_bot] at h'
  exact (Set.mem_singleton_iff.mp h').symm

omit [Finite G] [FaithfulSMul G Ω] in
theorem AltConfig.alternatingGroup_le_twoPointSection {α β : Ω} (C : AltConfig G Ω α β)
    (hr : Fintype.card C.D.ι = 1) [DecidablePred (· ∈ holtDelta G Ω α β)] :
    alternatingGroup (holtDelta G Ω α β) ≤ twoPointSection G Ω α β := by
  obtain ⟨i₀, he⟩ := C.exists_bijective_coord hr
  let e : holtDelta G Ω α β → C.D.Ψc i₀ := fun δ => C.D.coord δ i₀
  have he_inj : Function.Injective e := he.1
  let E := Equiv.ofBijective e he
  intro σ hσ
  have hσ' : E.permCongr σ ∈ alternatingGroup (C.D.Ψc i₀) := by
    rw [Perm.mem_alternatingGroup, Perm.sign_permCongr]
    exact hσ
  rw [← C.alt i₀] at hσ'
  obtain ⟨h, -, hhσ⟩ := (mem_factorImage).mp hσ'
  have hσh : ((h : twoPointSection G Ω α β) : Perm (holtDelta G Ω α β)) = σ := by
    ext δ
    apply congrArg Subtype.val
    apply he_inj
    show C.D.coord ((h : twoPointSection G Ω α β) • δ) i₀ = C.D.coord (σ δ) i₀
    rw [C.D.coord_smul h δ i₀, hhσ, Equiv.permCongr_apply]
    show E (σ (E.symm (E δ))) = E (σ δ)
    rw [E.symm_apply_apply]
  rw [← hσh]
  exact (h : twoPointSection G Ω α β).2

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem AltConfig.five_le_ncard_holtDelta {α β : Ω} (C : AltConfig G Ω α β)
    (hr : Fintype.card C.D.ι = 1) : 5 ≤ (holtDelta G Ω α β).ncard := by
  obtain ⟨i₀, he⟩ := C.exists_bijective_coord hr
  rw [← Nat.card_coe_set_eq, Nat.card_congr (Equiv.ofBijective _ he), Nat.card_eq_fintype_card]
  exact C.D.five_le_card i₀

theorem Sec4Setting.false_of_altConfig_of_card_ι_eq_one (hS : Sec4Setting G Ω) {α β : Ω}
    (hαβ : α ≠ β) (C : AltConfig G Ω α β) (hr : Fintype.card C.D.ι = 1)
    (hΔ' : holtDelta' G Ω α β = holtDelta G Ω α β) {W : Subgroup G} (hW : IsPGroup 2 W)
    {δ₁ δ₂ δ₃ : Ω} (h₁ : δ₁ ∈ holtDelta G Ω α β) (h₂ : δ₂ ∈ holtDelta G Ω α β)
    (h₃ : δ₃ ∈ holtDelta G Ω α β) (h12 : δ₁ ≠ δ₂) (h13 : δ₁ ≠ δ₃) (h23 : δ₂ ≠ δ₃)
    (hF : fixSet Ω W = {α, β, δ₁, δ₂, δ₃}) [DecidablePred (· ∈ fixSet Ω W)]
    (hA5 : alternatingGroup (fixSet Ω W) ≤ centralizerImage Ω W)
    (hND : LineNonDiagonal G ({α, β} ∪ holtDelta G Ω α β)) : False := by
  classical
  exact hS.false_of_stepC hαβ (C.five_le_ncard_holtDelta hr)
    (alternatingGroup_le_inducedPerm_inf hαβ (C.alternatingGroup_le_twoPointSection hr)) hΔ'
    (hS.exists_smul_mem_holtDelta_of_fixSet hαβ hW h₁ h₂ h₃ h12 h13 h23 hF hA5) hND

end StepCW

end CFSG.Holt.H78

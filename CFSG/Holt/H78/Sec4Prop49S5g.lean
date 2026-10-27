module

public import CFSG.Holt.H78.Sec4LineTheorem

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open
open scoped Pointwise

section CoordLine

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω]

variable (G) in
structure IsCoordLine (Λ : Set Ω) : Prop where
  jClosed : ∀ g : G, IsJClosed G Ω (g • Λ)
  eq_of_mem_of_mem : ∀ {A B : Set Ω}, (∃ g : G, g • Λ = A) → (∃ g : G, g • Λ = B) →
    ∀ {x y : Ω}, x ∈ A → x ∈ B → y ∈ A → y ∈ B → x ≠ y → A = B
  lineFix_eq_bot : ∀ x : Ω, lineFix G Λ x = ⊥
  exists_smul_ne : ∀ {x : Ω} {A : Set Ω}, A ∈ linesThrough G Λ x → ∀ {y : Ω}, y ∈ A → y ≠ x →
    ∃ k ∈ lineKer G Λ x A, k • y ≠ y
  exists_smul_eq : ∀ {A : Set Ω}, (∃ g : G, g • Λ = A) → ∀ {y z : Ω}, y ∈ A → z ∈ A →
    ∃ m ∈ lineGroup G Λ A, m • y = z
  exists_ne : ∀ {x : Ω} {A : Set Ω}, A ∈ linesThrough G Λ x → ∃ y ∈ A, y ≠ x

namespace IsCoordLine

variable {Λ : Set Ω}

theorem jClosed_of_mem (hΛ : IsCoordLine G Λ) {x : Ω} {A : Set Ω}
    (hA : A ∈ linesThrough G Λ x) : IsJClosed G Ω A := by
  obtain ⟨⟨g, rfl⟩, -⟩ := hA
  exact hΛ.jClosed g

theorem commute_of_mem_lineGroup_of_mem_fixingSubgroup (hΛ : IsCoordLine G Λ) {A : Set Ω}
    (hA : ∃ g : G, g • Λ = A) {m f : G} (hm : m ∈ lineGroup G Λ A)
    (hf : f ∈ fixingSubgroup G A) : m * f = f * m := by
  have hAJ : IsJClosed G Ω A := by
    obtain ⟨g, rfl⟩ := hA
    exact hΛ.jClosed g
  have hfA : f ∈ stabilizer G A := fixingSubgroup_le_stabilizer G A hf
  have hgen : ∀ x ∈ A, lineKer G Λ x A ≤ Subgroup.centralizer {f} := by
    intro x hx k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hfx : f • x = x := (mem_fixingSubgroup_iff G).mp hf x hx
    have hkA : k ∈ stabilizer G A :=
      closure_longInvAt_le_stabilizer hAJ hx (lineKer_le_closure hk)
    have h1 : f * k * f⁻¹ ∈ lineKer G Λ x A := by
      simpa [hfx, mem_stabilizer_iff.mp hfA] using conj_mem_lineKer hk f
    have hc : f * k * f⁻¹ * k⁻¹ ∈ lineKer G Λ x A := mul_mem h1 (inv_mem hk)
    have hcA : f * k * f⁻¹ * k⁻¹ ∈ fixingSubgroup G A := by
      have e : f * k * f⁻¹ * k⁻¹ = f * (k * f⁻¹ * k⁻¹) := by group
      rw [e]
      exact mul_mem hf (conj_mem_fixingSubgroup hkA (inv_mem hf))
    have h2 := mem_lineFix_of_mem_lineKer hc hcA
    rw [hΛ.lineFix_eq_bot x, Subgroup.mem_bot] at h2
    calc k * f = (f * k * f⁻¹ * k⁻¹)⁻¹ * (f * k) := by group
      _ = f * k := by rw [h2, inv_one, one_mul]
  have := lineGroup_le_centralizer (Λ := Λ) hgen hm
  exact Subgroup.mem_centralizer_singleton_iff.mp this

theorem commute_of_mem_lineKer (hΛ : IsCoordLine G Λ) {y : Ω} {L L' : Set Ω}
    (hL : L ∈ linesThrough G Λ y) (hL' : L' ∈ linesThrough G Λ y) (hne : L ≠ L') {k k' : G}
    (hk : k ∈ lineKer G Λ y L) (hk' : k' ∈ lineKer G Λ y L') : k * k' = k' * k := by
  have hy : ∀ {u : G}, u ∈ lineKer G Λ y L → u • y = y := fun hu =>
    closure_longInvAt_le_stabilizer_point y (lineKer_le_closure hu)
  have hy' : ∀ {u : G}, u ∈ lineKer G Λ y L' → u • y = y := fun hu =>
    closure_longInvAt_le_stabilizer_point y (lineKer_le_closure hu)
  have hstab : ∀ {L'' : Set Ω}, L'' ∈ linesThrough G Λ y → ∀ {u : G},
      u ∈ Subgroup.closure (longInvAt G Ω y) → u • L'' = L'' := fun hL'' _ hu =>
    closure_longInvAt_le_stabilizer (hΛ.jClosed_of_mem hL'') hL''.2 hu
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
  rw [hΛ.lineFix_eq_bot y, Subgroup.mem_bot] at h4
  calc k * k' = (k * k' * k⁻¹ * k'⁻¹) * (k' * k) := by group
    _ = k' * k := by rw [h4, one_mul]

theorem lineKer_smul_eq_lineKer (hΛ : IsCoordLine G Λ) {y : Ω} {L L' : Set Ω}
    (hL : L ∈ linesThrough G Λ y) (hne : L' ≠ L) {m : G} (hm : m ∈ lineGroup G Λ L) :
    lineKer G Λ (m • y) (m • L') = lineKer G Λ y L' := by
  have hfix : ∀ {k : G}, k ∈ lineKer G Λ y L' → k ∈ fixingSubgroup G L := fun hk =>
    (mem_fixingSubgroup_iff G).mpr fun z hz => lineKer_smul_eq hk hL (Ne.symm hne) hz
  have hcomm : ∀ {k : G}, k ∈ lineKer G Λ y L' → m * k * m⁻¹ = k := fun hk => by
    rw [hΛ.commute_of_mem_lineGroup_of_mem_fixingSubgroup hL.1 hm (hfix hk),
      mul_inv_cancel_right]
  rw [← map_conj_lineKer]
  refine le_antisymm ?_ fun k hk => ⟨k, hk, hcomm hk⟩
  rintro _ ⟨k, hk, rfl⟩
  simpa [hcomm hk] using hk

end IsCoordLine

end CoordLine

section CoordLineS

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω] [FaithfulSMul G Ω]

namespace IsCoordLine

variable {Λ : Set Ω}

theorem smul_eq_of_mem_normalizer (hS : Sec4Setting G Ω) (hΛ : IsCoordLine G Λ) {x : Ω}
    {L₀ : Set Ω} (hL₀ : L₀ ∈ linesThrough G Λ x) {g : G}
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
  obtain ⟨y, hy, hyx⟩ := hΛ.exists_ne hL₀
  have : Nontrivial Ω := ⟨⟨x, y, Ne.symm hyx⟩⟩
  have htop := (IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive G x).2 _ hlt
  have hHbot : H = ⊥ := eq_bot_of_normal_of_le_stabilizer
    (Subgroup.normalizer_eq_top_iff.mp htop) (iSup₂_le fun L _ =>
      lineKer_le_closure.trans (closure_longInvAt_le_stabilizer_point x))
  obtain ⟨k, hk, hky⟩ := hΛ.exists_smul_ne hL₀ hy hyx
  have hle : lineKer G Λ x L₀ ≤ H := le_iSup₂_of_le L₀ hL₀ le_rfl
  have hkH : k ∈ H := hle hk
  rw [hHbot, Subgroup.mem_bot] at hkH
  exact hky (by rw [hkH, one_smul])

theorem smul_eq_of_forall_commute (hS : Sec4Setting G Ω) (hΛ : IsCoordLine G Λ) {x : Ω}
    {L₀ : Set Ω} (hL₀ : L₀ ∈ linesThrough G Λ x) {g : G}
    (hg : ∀ L ∈ linesThrough G Λ x, ∀ k ∈ lineKer G Λ x L, k * g = g * k) : g • x = x := by
  have hle : (⨆ L ∈ linesThrough G Λ x, lineKer G Λ x L : Subgroup G) ≤
      Subgroup.centralizer {g} := iSup₂_le fun L hL k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hg L hL k hk)
  have hmem : g ∈ Subgroup.centralizer
      ((⨆ L ∈ linesThrough G Λ x, lineKer G Λ x L : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
  exact smul_eq_of_mem_normalizer hS hΛ hL₀ (Subgroup.centralizer_le_normalizer _ hmem)

theorem lineKer_ne_lineKer (hS : Sec4Setting G Ω) (hΛ : IsCoordLine G Λ) {x δ γ : Ω}
    {L₁ L₂ : Set Ω} (hL₁ : L₁ ∈ linesThrough G Λ x) (hL₂ : L₂ ∈ linesThrough G Λ x)
    (h12 : L₁ ≠ L₂) (hδ : δ ∈ L₁) (hδx : δ ≠ x) (hγ : γ ∈ L₂) :
    lineKer G Λ δ L₁ ≠ lineKer G Λ γ L₂ := by
  intro heq
  obtain ⟨m, hm, hmx⟩ := hΛ.exists_smul_eq hL₁.1 hL₁.2 hδ
  obtain ⟨m', hm', hm'x⟩ := hΛ.exists_smul_eq hL₂.1 hL₂.2 hγ
  have hmL := lineGroup_le_stabilizer (hΛ.jClosed_of_mem hL₁) hm
  have hm'L := lineGroup_le_stabilizer (hΛ.jClosed_of_mem hL₂) hm'
  have hcomm : ∀ L ∈ linesThrough G Λ x, ∀ k ∈ lineKer G Λ x L, ∀ y ∈ lineKer G Λ δ L₁,
      k * y = y * k := by
    intro L hL k hk y hy
    by_cases h1 : L = L₁
    · subst h1
      have hT : lineKer G Λ γ (m' • L) = lineKer G Λ x L := by
        rw [← hm'x]
        exact hΛ.lineKer_smul_eq_lineKer hL₂ h12 hm'
      have hLγ : m' • L ∈ linesThrough G Λ γ := by
        simpa [hm'x] using smul_mem_linesThrough hL m'
      exact (hΛ.commute_of_mem_lineKer ⟨hL₂.1, hγ⟩ hLγ
        (Ne.symm (smul_ne_of_mem_stabilizer hm'L h12)) (heq ▸ hy) (hT ▸ hk)).symm
    · have hT : lineKer G Λ δ (m • L) = lineKer G Λ x L := by
        rw [← hmx]
        exact hΛ.lineKer_smul_eq_lineKer hL₁ h1 hm
      have hLδ : m • L ∈ linesThrough G Λ δ := by
        simpa [hmx] using smul_mem_linesThrough hL m
      exact (hΛ.commute_of_mem_lineKer ⟨hL₁.1, hδ⟩ hLδ
        (Ne.symm (smul_ne_of_mem_stabilizer hmL h1)) hy (hT ▸ hk)).symm
  obtain ⟨u, hu, hux⟩ := hΛ.exists_smul_ne ⟨hL₁.1, hδ⟩ hL₁.2 (Ne.symm hδx)
  exact hux (smul_eq_of_forall_commute hS hΛ hL₁ fun L hL k hk => hcomm L hL k hk u hu)

theorem map_conj_lineKer_of_swap (hS : Sec4Setting G Ω) (hΛ : IsCoordLine G Λ) {x δ γ : Ω}
    {L₁ L₂ : Set Ω} (hL₁ : L₁ ∈ linesThrough G Λ x) (hL₂ : L₂ ∈ linesThrough G Λ x)
    (h12 : L₁ ≠ L₂) (hδ : δ ∈ L₁) (hδx : δ ≠ x) (hγ : γ ∈ L₂) {d : G} (hd : d ∈ longInv G Ω)
    (hdγ : d • γ = δ) :
    (lineKer G Λ x L₁).map (MulAut.conj d).toMonoidHom = lineKer G Λ δ L₁ := by
  have hdd : d * d = 1 := mul_self_eq_one_of_mem_longInv hd
  have hdδ : d • δ = γ := by rw [← hdγ, ← mul_smul, hdd, one_smul]
  obtain ⟨m, hm, hmx⟩ := hΛ.exists_smul_eq hL₁.1 hL₁.2 hδ
  obtain ⟨m', hm', hm'x⟩ := hΛ.exists_smul_eq hL₂.1 hL₂.2 hγ
  have hmL := lineGroup_le_stabilizer (hΛ.jClosed_of_mem hL₁) hm
  have hm'L := lineGroup_le_stabilizer (hΛ.jClosed_of_mem hL₂) hm'
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
    fun L _ hne => by rw [← hmx]; exact hΛ.lineKer_smul_eq_lineKer hL₁ hne hm
  have hT2 : ∀ L ∈ linesThrough G Λ x, L ≠ L₂ → lineKer G Λ γ (m' • L) = lineKer G Λ x L :=
    fun L _ hne => by rw [← hm'x]; exact hΛ.lineKer_smul_eq_lineKer hL₂ hne hm'
  have hfixx : ∀ {L : Set Ω}, ∀ k ∈ lineKer G Λ x L, k • x = x := fun k hk =>
    closure_longInvAt_le_stabilizer_point x (lineKer_le_closure hk)
  obtain ⟨u, hu, hux⟩ := hΛ.exists_smul_ne ⟨hL₁.1, hδ⟩ hL₁.2 (Ne.symm hδx)
  obtain ⟨w, hw, hwδ⟩ := hΛ.exists_smul_ne hL₁ hδ hδx
  have hne_δx : ∀ {L : Set Ω}, lineKer G Λ x L ≠ lineKer G Λ δ L₁ := fun h =>
    hux (hfixx u (h ▸ hu))
  have hne_xx : ∀ {B : Set Ω}, B ∈ linesThrough G Λ x → B ≠ L₁ →
      lineKer G Λ x L₁ ≠ lineKer G Λ x B := fun hB hne h =>
    hwδ (lineKer_smul_eq (h ▸ hw) hL₁ (Ne.symm hne) hδ)
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
        · exact lineKer_ne_lineKer hS hΛ hL₁ hL₂ h12 hδ hδx hγ (by rw [e6, hA''2])
        · obtain ⟨B', hB', hB'2, hm'B'⟩ := exists_lift_line hm'L hm'x (hmemδ hL) hA''2
          exact hne_δx (e6.trans (by rw [← hm'B', hT2 B' hB' hB'2])).symm
      · obtain ⟨B'', hB'', hB''1, hmB''⟩ := exists_lift_line hmL hmx (hmemγ hL) hA'1
        exact ⟨B'', hB'', by rw [e4, ← hmB'', hT1 B'' hB'' hB''1]⟩
    have hle := map_conj_iSup_lineKer_le hmap
    have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
    have hdx : d • x = x := smul_eq_of_mem_normalizer hS hΛ hL₁
      (mem_normalizer_of_conj (fun z hz => hle ⟨z, hz, rfl⟩)
        (fun z hz => by rw [hdinv]; exact hle ⟨z, hz, rfl⟩))
    have hdL₂ : d • L₂ = L₂ := (hΛ.jClosed_of_mem hL₂) x hL₂.2 d ⟨hd, hdx⟩
    have hδL₂ : δ ∈ L₂ := by
      rw [← hdγ, ← hdL₂]
      exact Set.smul_mem_smul_set hγ
    exact h12 (hΛ.eq_of_mem_of_mem hL₁.1 hL₂.1 hL₁.2 hL₂.2 hδ hδL₂ (Ne.symm hδx))
  · have e8 : lineKer G Λ x L₁ = lineKer G Λ δ (d • m' • B) := by
      rw [← hff (lineKer G Λ x L₁), e2, ← hT2 B hB hB2, hf, hdγ]
    by_cases h3 : d • m' • B = L₁
    · exact hne_δx (h3 ▸ e8)
    · obtain ⟨B₃, hB₃, hB₃1, hmB₃⟩ := exists_lift_line hmL hmx (hmemγ hB) h3
      exact hne_xx hB₃ hB₃1 (e8.trans (by rw [← hmB₃, hT1 B₃ hB₃ hB₃1]))

theorem commute_of_mem_lineGroup (hS : Sec4Setting G Ω) (hΛ : IsCoordLine G Λ) {x : Ω}
    {L₁ L₂ : Set Ω} (hL₁ : L₁ ∈ linesThrough G Λ x) (hL₂ : L₂ ∈ linesThrough G Λ x)
    (h12 : L₁ ≠ L₂) {a b : G} (ha : a ∈ lineGroup G Λ L₁) (hb : b ∈ lineGroup G Λ L₂) :
    a * b = b * a := by
  have hkk : ∀ δ ∈ L₁, ∀ γ ∈ L₂, ∀ k ∈ lineKer G Λ δ L₁, ∀ k' ∈ lineKer G Λ γ L₂,
      k * k' = k' * k := by
    intro δ hδ γ hγ k hk k' hk'
    obtain ⟨m, hm, hmx⟩ := hΛ.exists_smul_eq hL₁.1 hL₁.2 hδ
    obtain ⟨m', hm', hm'x⟩ := hΛ.exists_smul_eq hL₂.1 hL₂.2 hγ
    have hmL := lineGroup_le_stabilizer (hΛ.jClosed_of_mem hL₁) hm
    have hm'L := lineGroup_le_stabilizer (hΛ.jClosed_of_mem hL₂) hm'
    rcases eq_or_ne x δ with rfl | hδx <;> rcases eq_or_ne x γ with rfl | hγx
    · exact hΛ.commute_of_mem_lineKer hL₁ hL₂ h12 hk hk'
    · have hT : lineKer G Λ γ (m' • L₁) = lineKer G Λ x L₁ := by
        rw [← hm'x]
        exact hΛ.lineKer_smul_eq_lineKer hL₂ h12 hm'
      have hLγ : m' • L₁ ∈ linesThrough G Λ γ := by
        simpa [hm'x] using smul_mem_linesThrough hL₁ m'
      exact hΛ.commute_of_mem_lineKer hLγ ⟨hL₂.1, hγ⟩
        (smul_ne_of_mem_stabilizer hm'L h12) (hT ▸ hk) hk'
    · have hT : lineKer G Λ δ (m • L₂) = lineKer G Λ x L₂ := by
        rw [← hmx]
        exact hΛ.lineKer_smul_eq_lineKer hL₁ (Ne.symm h12) hm
      have hLδ : m • L₂ ∈ linesThrough G Λ δ := by
        simpa [hmx] using smul_mem_linesThrough hL₂ m
      exact hΛ.commute_of_mem_lineKer ⟨hL₁.1, hδ⟩ hLδ
        (Ne.symm (smul_ne_of_mem_stabilizer hmL (Ne.symm h12))) hk (hT ▸ hk')
    · obtain ⟨d, hd, hdγ⟩ := longInvSwap_nonempty hS.star γ δ
      have hdδ : d • δ = γ := by
        rw [← hdγ, ← mul_smul, mul_self_eq_one_of_mem_longInv hd, one_smul]
      have h1 := map_conj_lineKer_of_swap hS hΛ hL₁ hL₂ h12 hδ (Ne.symm hδx) hγ hd hdγ
      have h2 := map_conj_lineKer_of_swap hS hΛ hL₂ hL₁ (Ne.symm h12) hγ (Ne.symm hγx) hδ hd
        hdδ
      rw [← h1] at hk
      rw [← h2] at hk'
      obtain ⟨a, ha, rfl⟩ := hk
      obtain ⟨b, hb, rfl⟩ := hk'
      have hab := hΛ.commute_of_mem_lineKer hL₁ hL₂ h12 ha hb
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

theorem lineGroups_subset (hS : Sec4Setting G Ω) (hΛ : IsCoordLine G Λ) {L : Set Ω}
    (hL : ∃ g : G, g • Λ = L) {y z : Ω} (hy : y ∈ L) (hz : z ∈ L) :
    lineGroups G Λ y ⊆ lineGroups G Λ z := by
  rintro _ ⟨L', hL', rfl⟩
  obtain ⟨m, hm, hmy⟩ := hΛ.exists_smul_eq hL hy hz
  rcases eq_or_ne L' L with rfl | hne
  · exact ⟨L', ⟨hL, hz⟩, rfl⟩
  refine ⟨m • L', by simpa [hmy] using smul_mem_linesThrough hL' m, ?_⟩
  rw [← map_conj_lineGroup]
  refine le_antisymm ?_ fun b hb => ⟨b, hb, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [commute_of_mem_lineGroup hS hΛ ⟨hL, hy⟩ hL' (Ne.symm hne) hm hb,
      mul_inv_cancel_right]
    exact hb
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [commute_of_mem_lineGroup hS hΛ ⟨hL, hy⟩ hL' (Ne.symm hne) hm hb,
      mul_inv_cancel_right]

theorem eq_univ (hS : Sec4Setting G Ω) (hΛ : IsCoordLine G Λ) {α : Ω} (hα : α ∈ Λ) :
    Λ = Set.univ := by
  have hpre := hS.preprimitive
  have hΛ1 : ∃ g : G, g • Λ = Λ := ⟨1, one_smul G Λ⟩
  have hΛJ : IsJClosed G Ω Λ := by simpa using hΛ.jClosed 1
  obtain ⟨y₀, hy₀, hy₀α⟩ := hΛ.exists_ne ⟨hΛ1, hα⟩
  have hinv : ∀ (g : G) {y z : Ω}, lineGroups G Λ y = lineGroups G Λ z →
      lineGroups G Λ (g • y) = lineGroups G Λ (g • z) := fun g y z h => by
    rw [lineGroups_smul, lineGroups_smul, h]
  set B : Set Ω := {y | lineGroups G Λ y = lineGroups G Λ α} with hBdef
  have hcoll : ∀ y ∈ Λ, y ∈ B := fun y hy => (lineGroups_subset hS hΛ hΛ1 hy hα).antisymm
    (lineGroups_subset hS hΛ hΛ1 hα hy)
  have hblock : IsBlock G B := by
    rw [isBlock_iff_smul_eq_or_disjoint]
    intro g
    by_cases hdis : Disjoint (g • B) B
    · exact Or.inr hdis
    left
    obtain ⟨w, hwg, hwB⟩ := Set.not_disjoint_iff.mp hdis
    obtain ⟨y₁, hy₁, rfl⟩ := hwg
    have hsub : g • B ⊆ B := by
      rintro _ ⟨y, hy, rfl⟩
      show lineGroups G Λ (g • y) = lineGroups G Λ α
      rw [hinv g (hy.trans hy₁.symm)]
      exact hwB
    exact Set.eq_of_subset_of_ncard_le hsub (by rw [Set.ncard_smul_set]) (Set.toFinite B)
  have hB : B = Set.univ := by
    rcases IsPreprimitive.isTrivialBlock_of_isBlock hblock with h | h
    · exact absurd (h (hcoll y₀ hy₀) (hcoll α hα)) hy₀α
    · exact h
  have hnorm : ∀ t ∈ longInv G Ω, t ∈ Subgroup.normalizer (lineGroup G Λ Λ : Set G) := by
    intro t ht
    obtain ⟨y, hy⟩ := exists_mem_longInvAt ht
    have hyB : y ∈ B := hB ▸ Set.mem_univ y
    have hΛα : lineGroup G Λ Λ ∈ lineGroups G Λ α := ⟨Λ, ⟨hΛ1, hα⟩, rfl⟩
    rw [← hyB] at hΛα
    obtain ⟨L, hL, hLΛ⟩ := hΛα
    have htL : t • L = L := (hΛ.jClosed_of_mem hL) y hL.2 t hy
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
      have hmΛ : (m : G) • Λ = Λ := lineGroup_le_stabilizer hΛJ m.2
      have h1 : (m : G) • α ∈ (m : G) • Λ := Set.smul_mem_smul_set hα
      rw [hmΛ] at h1
      exact h1
    · intro hy
      obtain ⟨m, hm, hmα⟩ := hΛ.exists_smul_eq hΛ1 hα hy
      exact ⟨⟨m, hm⟩, hmα⟩
  have hΛblock : IsBlock G Λ := horbit ▸ IsBlock.orbit_of_normal α
  rcases IsPreprimitive.isTrivialBlock_of_isBlock hΛblock with h | h
  · exact absurd (h hy₀ hα) hy₀α
  · exact h

end IsCoordLine

end CoordLineS

end CFSG.Holt.H78

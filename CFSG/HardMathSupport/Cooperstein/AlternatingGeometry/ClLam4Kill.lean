module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClClean
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClKlein
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClR2
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClR3

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm MulAction



section Move

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem eq_swap_mul_swap {a b c d : Ω} {g : Perm Ω} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (h1 : g a = b) (h2 : g b = a) (h3 : g c = d)
    (h4 : g d = c) (hoff : ∀ x, x ≠ a → x ≠ b → x ≠ c → x ≠ d → g x = x) :
    g = swap a b * swap c d := by
  ext x
  by_cases hxa : x = a
  · subst hxa
    rw [h1, Perm.mul_apply, swap_apply_of_ne_of_ne hac had, swap_apply_left]
  by_cases hxb : x = b
  · subst hxb
    rw [h2, Perm.mul_apply, swap_apply_of_ne_of_ne hbc hbd, swap_apply_right]
  by_cases hxc : x = c
  · subst hxc
    rw [h3, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne had.symm hbd.symm]
  by_cases hxd : x = d
  · subst hxd
    rw [h4, Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne hac.symm hbc.symm]
  rw [hoff x hxa hxb hxc hxd, Perm.mul_apply, swap_apply_of_ne_of_ne hxc hxd,
    swap_apply_of_ne_of_ne hxa hxb]

theorem exists_D_of_move (σ : Perm Ω) (hσ1 : ∀ x, σ x ≠ x) (hσ2 : ∀ x, σ (σ x) = x)
    (c : Ω → Bool) (hc : ∀ x, c (σ x) = c x) (Ss W : Subgroup (Perm Ω)) (hWS : W ≤ Ss)
    (hWpp : W ≤ pairPres σ hσ1 hσ2) (hWsw : ∀ x, c x = false → swap x (σ x) ∈ W)
    (hnormW : ∀ s ∈ Ss, ∀ w ∈ W, s * w * s⁻¹ ∈ W)
    (z y : Ω) (hcz : c z = true) (hcy : c y = true) (hyz : y ≠ z) (hyσz : y ≠ σ z)
    (hD1 : swap z (σ z) * swap y (σ y) ∈ W)
    (hΛ : ∀ x, c x = true → x = z ∨ x = σ z ∨ x = y ∨ x = σ y)
    (htsw : ∀ x, c x = true → swap x (σ x) ∈ Ss)
    (hFix : ∀ s ∈ Ss, ∀ x, c x = false → s x = x ∨ s x = σ x)
    (hmove : ∃ s ∈ Ss, ∃ y0, s y0 ≠ y0 ∧ s y0 ≠ σ y0) :
    ∃ z' y'' : Ω, c z' = true ∧ c y'' = true ∧ y'' ≠ z' ∧ y'' ≠ σ z' ∧
      swap z' y'' * swap (σ z') (σ y'') ∈ Ss := by
  classical
  obtain ⟨s, hs, y0, hy1, hy2⟩ := hmove
  have hy0 : c y0 = true := by
    by_contra h
    have h' : c y0 = false := by simpa using h
    rcases hFix s hs y0 h' with e | e
    · exact hy1 e
    · exact hy2 e
  have hclosed : ∀ g ∈ Ss, ∀ x, c x = true → c (g x) = true := by
    intro g hg x hx
    by_contra h
    have h' : c (g x) = false := by simpa using h
    rcases hFix g⁻¹ (Ss.inv_mem hg) (g x) h' with e | e
    · have e0 : g⁻¹ (g x) = x := by simp
      rw [e0] at e; rw [e] at hx; rw [h'] at hx; simp at hx
    · have e0 : g⁻¹ (g x) = x := by simp
      rw [e0] at e; rw [e, hc] at hx; rw [h'] at hx; simp at hx
  obtain ⟨g0, hg0, hg0F, hg0off⟩ := exists_clean σ (fun x => c x = false) (fun x _ => hσ1 x) (fun x _ => hσ2 x)
    (fun x hx => by simp only [hc]; exact hx) Ss (fun x hx => hWS (hWsw x hx)) s hs (hFix s hs)
  have hg0T : ∀ x, c x = true → g0 x = s x := fun x hx => hg0off x (by simp [hx])
  have hyσy : y ≠ σ y := (hσ1 y).symm
  have hzσz : z ≠ σ z := (hσ1 z).symm
  have hσyz : σ y ≠ z := fun h => hyσz (by have := congrArg σ h; rwa [hσ2] at this)
  have hσyσz : σ y ≠ σ z := fun h => hyz (σ.injective h)
  have hcσz : c (σ z) = true := by rw [hc]; exact hcz
  have hcσy : c (σ y) = true := by rw [hc]; exact hcy
  set D1 : Perm Ω := swap z (σ z) * swap y (σ y) with hD1def
  have hD1σ : ∀ x, c x = true → D1 x = σ x := by
    intro x hx
    rcases hΛ x hx with h | h | h | h <;> rw [h]
    · simp only [hD1def, Perm.mul_apply]
      rw [swap_apply_of_ne_of_ne hyz.symm hσyz.symm, swap_apply_left]
    · simp only [hD1def, Perm.mul_apply]
      rw [swap_apply_of_ne_of_ne hyσz.symm hσyσz.symm, swap_apply_right, hσ2]
    · simp only [hD1def, Perm.mul_apply]
      rw [swap_apply_left y (σ y), swap_apply_of_ne_of_ne hσyz hσyσz]
    · simp only [hD1def, Perm.mul_apply]
      rw [swap_apply_right y (σ y), swap_apply_of_ne_of_ne hyz hyσz, hσ2]
  have hD1F : ∀ x, c x = false → D1 x = x := by
    intro x hx
    have h1 : x ≠ z := fun h => by rw [h, hcz] at hx; simp at hx
    have h2 : x ≠ σ z := fun h => by rw [h, hcσz] at hx; simp at hx
    have h3 : x ≠ y := fun h => by rw [h, hcy] at hx; simp at hx
    have h4 : x ≠ σ y := fun h => by rw [h, hcσy] at hx; simp at hx
    simp only [hD1def, Perm.mul_apply]
    rw [swap_apply_of_ne_of_ne h3 h4, swap_apply_of_ne_of_ne h1 h2]
  have hcomm : ∀ u, c u = true → g0 (σ u) = σ (g0 u) := by
    intro u hu
    have hw : g0 * D1 * g0⁻¹ ∈ W := hnormW g0 hg0 D1 hD1
    have hgu : c (g0 u) = true := hclosed g0 hg0 u hu
    have h0 : g0⁻¹ (g0 u) = u := by simp
    have hwx : (g0 * D1 * g0⁻¹) (g0 u) = σ (g0 u) := by
      rcases hWpp hw (g0 u) with e | e
      · exfalso
        simp only [Perm.mul_apply, h0, hD1σ u hu] at e
        exact hσ1 u (g0.injective (by simpa using e))
      · exact e
    simpa [Perm.mul_apply, h0, hD1σ u hu] using hwx
  set y' := g0 y0 with hy'
  have hy'T : c y' = true := hclosed g0 hg0 y0 hy0
  have hy'y0 : y' ≠ y0 := by rw [hy', hg0T y0 hy0]; exact hy1
  have hy'σy0 : y' ≠ σ y0 := by rw [hy', hg0T y0 hy0]; exact hy2
  have hσy' : g0 (σ y0) = σ y' := hcomm y0 hy0
  have hcσy0 : c (σ y0) = true := by rw [hc]; exact hy0
  have hcσy' : c (σ y') = true := by rw [hc]; exact hy'T
  have hσy'y0 : σ y' ≠ y0 := fun h => hy'σy0 (by have := congrArg σ h; rwa [hσ2] at this)
  have hσy'σy0 : σ y' ≠ σ y0 := fun h => hy'y0 (σ.injective h)
  have hy0σ : y0 ≠ σ y0 := (hσ1 y0).symm
  have hy'σ : y' ≠ σ y' := (hσ1 y').symm
  have hset : ∀ x, c x = true → x = y0 ∨ x = σ y0 ∨ x = y' ∨ x = σ y' := by
    have hsub : ({y0, σ y0, y', σ y'} : Finset Ω) ⊆ Finset.univ.filter fun x => c x = true := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    have hcard4 : ({y0, σ y0, y', σ y'} : Finset Ω).card = 4 := by
      have n1 : σ y0 ∉ ({y', σ y'} : Finset Ω) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hy'σy0.symm, hσy'σy0.symm⟩
      have n2 : y0 ∉ ({σ y0, y', σ y'} : Finset Ω) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hy0σ, hy'y0.symm, hσy'y0.symm⟩
      rw [Finset.card_insert_of_notMem n2, Finset.card_insert_of_notMem n1, Finset.card_pair hy'σ]
    have hle : (Finset.univ.filter fun x => c x = true).card ≤ 4 := by
      refine (Finset.card_le_card (t := ({z, σ z, y, σ y} : Finset Ω)) ?_).trans Finset.card_le_four
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact hΛ x hx
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard4]; exact hle)
    intro x hx
    have : x ∈ ({y0, σ y0, y', σ y'} : Finset Ω) := by rw [heq]; simp [hx]
    simpa [or_assoc] using this
  have hg0y' : g0 y' = y0 ∨ g0 y' = σ y0 := by
    have hT : c (g0 y') = true := hclosed g0 hg0 y' hy'T
    rcases hset _ hT with e | e | e | e
    · exact Or.inl e
    · exact Or.inr e
    · exact absurd (g0.injective (e.trans (hy'.symm))) hy'y0
    · exfalso
      have : g0 y' = g0 (σ y0) := by rw [hσy', e]
      exact hy'σy0 (g0.injective this)
  have hg0σy' : g0 (σ y') = σ (g0 y') := hcomm y' hy'T
  have hoffF : ∀ x, x ≠ y0 → x ≠ σ y0 → x ≠ y' → x ≠ σ y' → c x = false := by
    intro x h1 h2 h3 h4
    by_contra h
    have h' : c x = true := by simpa using h
    rcases hset x h' with e | e | e | e
    · exact h1 e
    · exact h2 e
    · exact h3 e
    · exact h4 e
  rcases hg0y' with h | h
  · refine ⟨y0, y', hy0, hy'T, hy'y0, hy'σy0, ?_⟩
    have hg := eq_swap_mul_swap (g := g0) hy'y0.symm hy0σ hσy'y0.symm hy'σy0 hy'σ hσy'σy0.symm rfl h
      hσy' (hg0σy'.trans (by rw [h])) (fun x h1 h2 h3 h4 => hg0F x (hoffF x h1 h3 h2 h4))
    rw [← hg]; exact hg0
  · refine ⟨y0, σ y', hy0, hcσy', hσy'y0, hσy'σy0, ?_⟩
    have hg1mem : g0 * swap y0 (σ y0) ∈ Ss := Ss.mul_mem hg0 (htsw y0 hy0)
    have hg := eq_swap_mul_swap (g := g0 * swap y0 (σ y0)) (a := y0) (b := σ y') (c := σ y0) (d := y')
      hσy'y0.symm hy0σ hy'y0.symm hσy'σy0 hy'σ.symm hy'σy0.symm
      (by rw [Perm.mul_apply, swap_apply_left, hσy'])
      (by rw [Perm.mul_apply, swap_apply_of_ne_of_ne hσy'y0 hσy'σy0, hg0σy', h, hσ2])
      (by rw [Perm.mul_apply, swap_apply_right])
      (by rw [Perm.mul_apply, swap_apply_of_ne_of_ne hy'y0 hy'σy0, h])
      (fun x h1 h2 h3 h4 => by
        rw [Perm.mul_apply, swap_apply_of_ne_of_ne h1 h3]
        exact hg0F x (hoffF x h1 h3 h4 h2))
    have : swap y0 (σ y') * swap (σ y0) y' ∈ Ss := hg ▸ hg1mem
    rw [hσ2]; exact this

end Move

section FourClass

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem true_class_of_four (σ : Perm Ω) (hσ1 : ∀ x, σ x ≠ x) (hσ2 : ∀ x, σ (σ x) = x)
    (c : Ω → Bool) (hc : ∀ x, c (σ x) = c x)
    (hcard : (Finset.univ.filter fun x => c x = true).card = 4) {p q : Ω} (hp : c p = true)
    (hq : c q = true) (hqp : q ≠ p) (hqσp : q ≠ σ p) :
    ∀ x, c x = true → x = p ∨ x = σ p ∨ x = q ∨ x = σ q := by
  classical
  have hσqp : σ q ≠ p := fun h => hqσp (by have := congrArg σ h; rwa [hσ2] at this)
  have hσqσp : σ q ≠ σ p := fun h => hqp (σ.injective h)
  have hcσp : c (σ p) = true := by rw [hc]; exact hp
  have hcσq : c (σ q) = true := by rw [hc]; exact hq
  have hsub : ({p, σ p, q, σ q} : Finset Ω) ⊆ Finset.univ.filter fun x => c x = true := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hcard4 : ({p, σ p, q, σ q} : Finset Ω).card = 4 := by
    have n1 : σ p ∉ ({q, σ q} : Finset Ω) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hqσp.symm, hσqσp.symm⟩
    have n2 : p ∉ ({σ p, q, σ q} : Finset Ω) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(hσ1 p).symm, hqp.symm, hσqp.symm⟩
    rw [Finset.card_insert_of_notMem n2, Finset.card_insert_of_notMem n1,
      Finset.card_pair (hσ1 q).symm]
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard4, hcard])
  intro x hx
  have : x ∈ ({p, σ p, q, σ q} : Finset Ω) := by rw [heq]; simp [hx]
  simpa [or_assoc] using this

end FourClass

namespace Classif.Pre

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {W : Subgroup (Perm Ω)} {ι : Type*}
  {E : ι → Subgroup (Perm Ω)} (P : Pre W E)

theorem le_pairPres_of_blockData_four {i₀ : ι} {σ : Perm Ω} {c : Ω → Bool}
    (hB : BlockData (E i₀) σ c)
    (hΛ : ∀ y, partner P.twoGroup y = y ↔ c y = true)
    (h4 : (Finset.univ.filter fun y => c y = true).card = 4) {z y : Ω} (hcz : c z = true)
    (hcy : c y = true) (hyz : y ≠ z) (hyσz : y ≠ σ z)
    (hnoD : ∀ z y : Ω, c z = true → c y = true → y ≠ z → y ≠ σ z →
      swap z y * swap (σ z) (σ y) ∉ W) (i : ι) :
    E i ≤ pairPres σ hB.1 hB.2.1 := by
  classical
  obtain ⟨hσ1, hσ2, hg0, hc0, hcol0, hdbl0⟩ := hB
  have hex : ∃ z, partner P.twoGroup z = z := ⟨z, (hΛ z).2 hcz⟩
  have hmatched : ∀ y, c y = false → σ y = partner P.twoGroup y := by
    intro y hy
    have hsw : swap y (σ y) ∈ E i₀ := by
      by_contra h
      have := (hcol0 y).2 h
      rw [hy] at this; exact absurd this (by simp)
    exact (partner_eq_of_swap_mem P.twoGroup (hσ1 y).symm (P.le i₀ hsw)).symm
  have hWsw : ∀ x, c x = false → swap x (σ x) ∈ W := fun x hx => P.le i₀ (by
    by_contra h
    have := (hcol0 x).2 h
    rw [hx] at this
    exact absurd this (by simp))
  have hΛset := true_class_of_four σ hσ1 hσ2 c hc0 h4 hcz hcy hyz hyσz
  have hcσ : ∀ x, c (σ x) = c x := hc0
  rcases shape_cases (P.shape i) with hsw | ⟨x, hx⟩ | hall
  · refine (Offender.le_closure_swaps_of_swapType hsw).trans ?_
    rw [Subgroup.closure_le]
    rintro t ⟨htE, a, b, hab, rfl⟩
    have hpb : partner P.twoGroup a = b := partner_eq_of_swap_mem P.twoGroup hab (P.le i htE)
    have hca : c a = false := by
      by_contra h
      have h' : c a = true := by simpa using h
      have := (hΛ a).2 h'
      rw [hpb] at this
      exact hab this.symm
    rw [← hpb, ← hmatched a hca]
    exact swap_mem_pairPres hσ1 hσ2 a
  · exfalso
    have hΛorb : ∀ w, c w = true → w ∈ orbit (E i) x := fun w hw =>
      unmatched_mem_orbit_of_fourOrbit P.twoGroup (P.le i) (P.exp i) (P.shape i) hx ((hΛ w).2 hw)
    set e0 : Fin 4 → Ω := ![z, y, σ z, σ y] with he0
    have hσzy : σ z ≠ y := fun h => hyσz h.symm
    have hσyz : σ y ≠ z := fun h => hyσz (by have := congrArg σ h; rwa [hσ2] at this)
    have hσyσz : σ y ≠ σ z := fun h => hyz (σ.injective h)
    have hzσz : z ≠ σ z := (hσ1 z).symm
    have hyσy : y ≠ σ y := (hσ1 y).symm
    have hinj : Function.Injective e0 := by
      intro i j hij
      have n1 := hzσz; have n2 := hyz.symm; have n3 := hσyz.symm; have n4 := hyσz
      have n5 := hyσy; have n6 := hσyσz.symm
      have m1 := hzσz.symm; have m2 := hyz; have m3 := hσyz; have m4 := hyσz.symm
      have m5 := hyσy.symm; have m6 := hσyσz
      fin_cases i <;> fin_cases j <;> simp only [he0] at hij <;>
        first | rfl | (exfalso; simp at hij; exact absurd hij ‹_›)
    have hrange : ∀ w, c w = true ↔ w ∈ Set.range e0 := by
      intro w
      constructor
      · intro hw
        rcases hΛset w hw with h | h | h | h
        · exact ⟨0, by simp [he0, h]⟩
        · exact ⟨2, by simp [he0, h]⟩
        · exact ⟨1, by simp [he0, h]⟩
        · exact ⟨3, by simp [he0, h]⟩
      · rintro ⟨k, rfl⟩
        fin_cases k <;> simp [he0, hcz, hcy, hc0]
    have horbeq : ∀ w, w ∈ orbit (E i) (e0 0) ↔ w ∈ Set.range e0 := by
      intro w
      have hsub : (Set.range e0) ⊆ orbit (E i) x := fun w hw => hΛorb w ((hrange w).2 hw)
      have hcardr : (Set.range e0).ncard = 4 := by
        rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj]; simp
      have hseq : Set.range e0 = orbit (E i) x :=
        Set.eq_of_subset_of_ncard_le hsub (by
          rw [hcardr, ← Nat.card_coe_set_eq, hx]) (Set.toFinite _)
      have h0 : e0 0 ∈ orbit (E i) x := hsub ⟨0, rfl⟩
      rw [orbit_eq_iff.2 h0, ← hseq]
    have hyorb : y ∈ orbit (E i) (e0 0) := (horbeq y).2 ⟨1, rfl⟩
    obtain ⟨⟨ε, hεE⟩, hεy⟩ := hyorb
    have hεz : ε z = y := hεy
    have h23 := klein_other (P.exp i) hinj horbeq hεE (j := 1) (by decide) hεz (k := 2) (l := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide)
    have hεσz : ε (σ z) = σ y := h23
    have hεyz : ε y = z := by
      have := klein_involution (P.exp i) hεE z
      rwa [hεz] at this
    have hεσyσz : ε (σ y) = σ z := by
      have := klein_involution (P.exp i) hεE (σ z)
      rwa [hεσz] at this
    have hεW : ε ∈ W := P.le i hεE
    obtain ⟨g0, hg0, hg0F, hg0off⟩ := exists_clean σ (fun x => c x = false) (fun x _ => hσ1 x) (fun x _ => hσ2 x)
      (fun x hx => by simp only [hc0]; exact hx) W (fun x hx => hWsw x hx) ε hεW (fun x hx => by
        have hpσ : partner P.twoGroup x = σ x := (hmatched x hx).symm
        have hne : partner P.twoGroup x ≠ x := by rw [hpσ]; exact hσ1 x
        have := P.blockTrivial_of_unmatched hex ε hεW x hne
        rwa [hpσ] at this)
    have hgD := eq_swap_mul_swap (g := g0) (a := z) (b := y) (c := σ z) (d := σ y) hyz.symm
      hzσz hσyz.symm hyσz hyσy hσyσz.symm
      (by rw [hg0off z (by simp [hcz]), hεz])
      (by rw [hg0off y (by simp [hcy]), hεyz])
      (by rw [hg0off (σ z) (by simp [hc0, hcz]), hεσz])
      (by rw [hg0off (σ y) (by simp [hc0, hcy]), hεσyσz])
      (fun x h1 h2 h3 h4 => hg0F x (by
        by_contra h
        have h' : c x = true := by simpa using h
        rcases hΛset x h' with e | e | e | e
        · exact h1 e
        · exact h3 e
        · exact h2 e
        · exact h4 e))
    exact hnoD z y hcz hcy hyz hyσz (hgD ▸ hg0)
  · obtain ⟨σ', c', hbd'⟩ := blockData_of_shape hall.1 hall.2
    obtain ⟨hs1, hs2, hg, hc, hcol, hdbl⟩ := hbd'
    have hbd' : BlockData (E i) σ' c' := ⟨hs1, hs2, hg, hc, hcol, hdbl⟩
    have hmatched' : ∀ y, c' y = false → σ' y = partner P.twoGroup y := by
      intro y hy
      have hsw : swap y (σ' y) ∈ E i := by
        by_contra h
        have := (hcol y).2 h
        rw [hy] at this; exact absurd this (by simp)
      exact (partner_eq_of_swap_mem P.twoGroup (hs1 y).symm (P.le i hsw)).symm
    have hΛc' : ∀ y, partner P.twoGroup y = y → c' y = true := by
      intro y hy
      by_contra h
      have h' : c' y = false := by simpa using h
      exact hs1 y ((hmatched' y h').trans hy)
    have h3' : 3 ≤ (Finset.univ.filter fun y => c' y = true).card := by
      have hsub : (Finset.univ.filter fun y => c y = true) ⊆ Finset.univ.filter fun y => c' y = true := by
        intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        exact hΛc' y ((hΛ y).2 hy)
      have := Finset.card_le_card hsub
      omega
    have hΛ' := unmatched_iff_true P.twoGroup (P.le i) hbd' h3' hex
    by_cases hσeq : σ = σ'
    · subst hσeq
      intro g hg' w
      exact hg g hg' w
    · exfalso
      obtain ⟨p, hp⟩ : ∃ p, σ p ≠ σ' p := by
        by_contra h
        push Not at h
        exact hσeq (Equiv.ext h)
      have hpm : partner P.twoGroup p = p := by
        by_contra hne
        have hcf : c p = false := by
          by_contra h
          exact hne ((hΛ p).2 (by simpa using h))
        have hcf' : c' p = false := by
          by_contra h
          exact hne ((hΛ' p).2 (by simpa using h))
        exact hp ((hmatched p hcf).trans (hmatched' p hcf').symm)
      have hcp : c p = true := (hΛ p).1 hpm
      have hcp' : c' p = true := (hΛ' p).1 hpm
      have hy'' : c (σ' p) = true := by
        have : c' (σ' p) = true := by rw [hc]; exact hcp'
        have hpm' : partner P.twoGroup (σ' p) = σ' p := (hΛ' _).2 this
        exact (hΛ _).1 hpm'
      have hy''p : σ' p ≠ p := hs1 p
      have hy''σp : σ' p ≠ σ p := fun h => hp h.symm
      have hset := true_class_of_four σ hσ1 hσ2 c hc0 h4 hcp hy'' hy''p hy''σp
      have hσpT : c' (σ p) = true := by
        have : c (σ p) = true := by rw [hc0]; exact hcp
        have hpm' : partner P.twoGroup (σ p) = σ p := (hΛ _).2 this
        exact (hΛ' _).1 hpm'
      have hσ'σp : σ' (σ p) = σ (σ' p) := by
        have hT' : c (σ' (σ p)) = true := by
          have : c' (σ' (σ p)) = true := by rw [hc]; exact hσpT
          exact (hΛ _).1 ((hΛ' _).2 this)
        rcases hset _ hT' with e | e | e | e
        · exfalso
          apply hy''σp
          have := congrArg σ' e
          rw [hs2] at this
          exact this.symm
        · exact absurd e (hs1 (σ p))
        · exact absurd (σ'.injective e) (hσ1 p)
        · exact e
      have hD' : swap p (σ' p) * swap (σ p) (σ' (σ p)) ∈ dblGroup σ' c' :=
        Subgroup.subset_closure ⟨p, σ p, hσ1 p, hy''σp.symm, hσpT.trans hcp'.symm, rfl⟩
      rw [hσ'σp] at hD'
      exact hnoD p (σ' p) hcp hy'' hy''p hy''σp (P.le i (hdbl hD'))

end Classif.Pre

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

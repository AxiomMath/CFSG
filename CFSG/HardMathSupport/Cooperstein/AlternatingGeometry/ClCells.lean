module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClPartner
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffendersDichotomy

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm MulAction

namespace Classif

open Offender

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {W : Subgroup (Perm Ω)}

theorem swap_mem_of_bijective {E : Subgroup (Perm Ω)} (hE : IsExp2 E)
    (hb : Function.Bijective (evalOrb E E le_orbitStab)) {z z' : Ω}
    (hc : Nat.card (orbit E z) = 2) (hz' : z' ∈ orbit E z) (hne : z ≠ z') : swap z z' ∈ E := by
  classical
  have horb : ∀ y ∈ orbit E z, y = z ∨ y = z' := fun y hy =>
    eq_of_mem_of_ncard_le (Set.toFinite _) (by rw [← Nat.card_coe_set_eq]; exact hc.le)
      (mem_orbit_self z) hz' hne hy
  obtain ⟨O, hO⟩ : ∃ O : Orb E, O = Quotient.mk'' z := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = O.out := ⟨_, rfl⟩
  have hzr : z ∈ orbit E r := by rw [hr, hO]; exact mem_orbit_out z
  have hrz : r ∈ orbit E z := by
    have : orbit E z = orbit E r := orbit_eq_iff.2 hzr
    rw [this]; exact mem_orbit_self r
  have hor_eq : orbit E r = orbit E z := (orbit_eq_iff.2 hzr).symm
  obtain ⟨r', hrr'⟩ : ∃ r', (r = z ∧ r' = z') ∨ (r = z' ∧ r' = z) := by
    rcases horb r hrz with h | h
    · exact ⟨z', Or.inl ⟨h, rfl⟩⟩
    · exact ⟨z, Or.inr ⟨h, rfl⟩⟩
  have hrne : r ≠ r' := by
    rcases hrr' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hne
    · rw [h1, h2]; exact Ne.symm hne
  have hor : ∀ y ∈ orbit E r, y = r ∨ y = r' := by
    intro y hy
    rw [hor_eq] at hy
    rcases horb y hy with h | h <;> rcases hrr' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h, h1, h2]
  have hr'mem : r' ∈ orbit E r := by
    rw [hor_eq]
    rcases hrr' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2]; exact hz'
    · rw [h2]; exact mem_orbit_self z
  have hq : ∀ y ∈ orbit E r, (Quotient.mk'' y : Orb E) = O := by
    intro y hy
    have h1 : (Quotient.mk'' y : Orb E) = Quotient.mk'' r :=
      Quotient.sound' (orbitRel_apply.2 hy)
    rw [h1, hr]
    exact Quotient.out_eq' O
  let t : ∀ ω' : Orb E, orbit E ω'.out := fun ω' =>
    ⟨if ω' = O then r' else ω'.out, by
      by_cases h : ω' = O
      · simp only [h, ↓reduceIte]; rw [← hr]; exact hr'mem
      · simp only [h, ↓reduceIte]; exact mem_orbit_self _⟩
  obtain ⟨e, he⟩ := hb.2 t
  have hev : ∀ ω' : Orb E, (e : Perm Ω) ω'.out = (t ω').1 := fun ω' =>
    congrArg Subtype.val (congrFun he ω')
  have her : (e : Perm Ω) r = r' := by
    have h1 := hev O
    have h2 : (t O).1 = r' := by simp [t]
    rw [hr]; exact h1.trans h2
  have heother : ∀ ω' : Orb E, ω' ≠ O → (e : Perm Ω) ω'.out = ω'.out := by
    intro ω' h
    rw [hev ω']; simp [t, h]
  have hsm : ∀ (g : E) (x : Ω), g • x = (g : Perm Ω) x := fun g x => rfl
  have hstable : ∀ (g : E) (x : Ω), x ∈ orbit E r → (g : Perm Ω) x ∈ orbit E r := by
    intro g x hx
    obtain ⟨g1, hg1⟩ := hx
    refine ⟨g * g1, ?_⟩
    have h0 : (g1 : Perm Ω) r = x := hg1
    show (g : Perm Ω) ((g1 : Perm Ω) r) = (g : Perm Ω) x
    rw [h0]
  have hall : ∀ y, (e : Perm Ω) y = swap r r' y := by
    intro y
    obtain ⟨h, hh⟩ := mem_orbit_out (E := E) y
    obtain ⟨r0, hr0⟩ : ∃ r0, r0 = (Quotient.mk'' y : Orb E).out := ⟨_, rfl⟩
    rw [← hr0] at hh
    have hh' : (h : Perm Ω) r0 = y := hh
    have hcomm : (e : Perm Ω) * h = h * e := hE.comm e.2 h.2
    have hey : (e : Perm Ω) y = (h : Perm Ω) ((e : Perm Ω) r0) := by
      rw [← hh']
      exact congrArg (fun f : Perm Ω => f r0) hcomm
    by_cases hy : (Quotient.mk'' y : Orb E) = O
    · have hy' : r0 = r := by rw [hr0, hy, hr]
      rw [hy'] at hey hh'
      rw [hey, her]
      have hyr : y ∈ orbit E r := ⟨h, hh'⟩
      have hr'h : (h : Perm Ω) r' ∈ orbit E r := hstable h r' hr'mem
      rcases hor y hyr with h1 | h1
      · rw [h1, swap_apply_left]
        rw [h1] at hh'
        rcases hor _ hr'h with h2 | h2
        · exfalso
          have := (h : Perm Ω).injective (h2.trans hh'.symm)
          exact hrne this.symm
        · exact h2
      · rw [h1, swap_apply_right]
        rw [h1] at hh'
        rcases hor _ hr'h with h2 | h2
        · exact h2
        · exfalso
          have := (h : Perm Ω).injective (h2.trans hh'.symm)
          exact hrne this.symm
    · have h0 := heother _ hy
      rw [← hr0] at h0
      rw [h0, hh'] at hey
      rw [hey]
      symm
      refine swap_apply_of_ne_of_ne ?_ ?_
      · intro h1; apply hy; rw [h1]; exact hq r (mem_orbit_self r)
      · intro h1; apply hy; rw [h1]; exact hq r' hr'mem
  have hsw : swap r r' ∈ E := by
    have : swap r r' = (e : Perm Ω) := Equiv.ext fun y => (hall y).symm
    rw [this]; exact e.2
  rcases hrr' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2] at hsw; exact hsw
  · rw [h1, h2, swap_comm] at hsw; exact hsw

@[expose] def CellConcl (ω : Perm Ω) (E : Subgroup (Perm Ω)) : Prop :=
  (∀ e ∈ E, ∀ z, ω z ≠ z → e z = z ∨ e z = ω z) ∨
  ∃ F : Finset Ω, F.card = 4 ∧ (∀ z, ω z ≠ z) ∧ (∀ z ∈ F, ω z ∈ F) ∧
    (∀ e ∈ E, ∀ z ∈ F, e z ∈ F) ∧ (∀ e ∈ E, ∀ z, z ∉ F → e z = z ∨ e z = ω z) ∧
    ∃ e ∈ E, ∃ z ∈ F, e z ≠ z ∧ e z ≠ ω z

theorem swap_mem_orbitStab {E : Subgroup (Perm Ω)} {e : Perm Ω} (he : e ∈ E) (z : Ω) : swap z (e z) ∈ orbitStab E := by
  intro i
  have hz : e z ∈ orbit E z := ⟨⟨e, he⟩, rfl⟩
  have hz' : z ∈ orbit E (e z) := ⟨⟨e⁻¹, E.inv_mem he⟩, by simp⟩
  by_cases h1 : i = z
  · subst h1
    rw [swap_apply_left]; exact hz
  · by_cases h2 : i = e z
    · subst h2
      rw [swap_apply_right]; exact hz'
    · rw [swap_apply_of_ne_of_ne h1 h2]; exact mem_orbit_self i

theorem cell_swapType (hW : IsPGroup 2 W) {E : Subgroup (Perm Ω)} (hEW : E ≤ W) (hS : SwapType E) :
    ∀ e ∈ E, ∀ z, e z = z ∨ e z = partner hW z := by
  intro e he z
  by_cases h : e z = z
  · exact Or.inl h
  · right
    have hm : swap z (e z) ∈ E := by
      rw [hS.2]; exact swap_mem_orbitStab he z
    exact (partner_eq_of_swap_mem hW (Ne.symm h) (hEW hm)).symm

theorem cell_blockData (hW : IsPGroup 2 W) {E : Subgroup (Perm Ω)} (hEW : E ≤ W) {σ : Perm Ω}
    {c : Ω → Bool} (hB : BlockData E σ c) : CellConcl (partner hW) E := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hB
  set ω := partner hW with hω
  have hcomm : ∀ e ∈ E, ∀ x, ω (e x) = e (ω x) := fun e he x => partner_comm hW (hEW he) x
  have hωω : ∀ x, ω (ω x) = x := partner_partner hW
  have hωinj : ∀ {x y}, ω x = ω y → x = y := fun {x y} h => by
    have := congrArg ω h
    rwa [hωω, hωω] at this
  have hF1 : ∀ x, c x = false → ω x = σ x := by
    intro x hx
    have hm : swap x (σ x) ∈ E := by
      by_contra hn
      have := (h5 x).2 hn
      rw [hx] at this; exact Bool.false_ne_true this
    exact partner_eq_of_swap_mem hW (Ne.symm (h1 x)) (hEW hm)
  by_cases hnot : ∀ e ∈ E, ∀ z, ω z ≠ z → e z = z ∨ e z = ω z
  · exact Or.inl hnot
  right
  push Not at hnot
  obtain ⟨e, he, z, hz, hez1, hez2⟩ := hnot
  obtain ⟨a, ha⟩ : ∃ a, ω z = a := ⟨_, rfl⟩
  obtain ⟨z', hz'⟩ : ∃ z', σ z = z' := ⟨_, rfl⟩
  have hez : e z = z' := hz' ▸ (h3 e he z).resolve_left hez1
  have haz : ω a = z := by rw [← ha, hωω]
  have hσz' : σ z' = z := by rw [← hz', h2]
  have hz'z : z' ≠ z := hz' ▸ h1 z
  have haz' : z' ≠ a := fun h => hez2 (by rw [hez, ha, h])
  have haz0 : a ≠ z := ha ▸ hz
  have hcz : c z = true := by
    by_contra hn
    have hn' : c z = false := by simpa using hn
    exact hez2 (by rw [hez, ha, ← hz', ← hF1 z hn', ha])
  have hb : ω z' = e a := by rw [← hez, hcomm e he z, ha]
  have hea : e a = σ a := by
    rcases h3 e he a with h | h
    · exfalso
      have : ω z' = ω z := by rw [hb, h, ha]
      exact hz'z (hωinj this)
    · exact h
  obtain ⟨b, hbdef⟩ : ∃ b, ω z' = b := ⟨_, rfl⟩
  have hσa : σ a = b := by rw [← hea, ← hb, hbdef]
  have hbz' : ω b = z' := by rw [← hbdef, hωω]
  have hσb : σ b = a := by rw [← hσa, h2]
  have hba : b ≠ a := fun h => hz'z (hωinj (by rw [hbdef, h, ha]))
  have hbz : b ≠ z := fun h => haz' (by rw [← hbz', h, ha]) |>.elim
  have hbz'' : b ≠ z' := by
    intro h
    have h' : e a = e z := by rw [← hb, hbdef, h, hez]
    exact haz0 (e.injective h')
  have hca : c a = true := by
    by_contra hn
    have hn' : c a = false := by simpa using hn
    have h8 : ω a = σ a := hF1 a hn'
    rw [haz, hσa] at h8
    exact hbz h8.symm
  have hcz' : c z' = true := by
    have := h4 z; rw [hz'] at this; rw [this, hcz]
  have hcb : c b = true := by
    have := h4 a; rw [hσa] at this; rw [this, hca]
  have hσF : ∀ y, y ∈ ({z, a, z', b} : Finset Ω) → σ y ∈ ({z, a, z', b} : Finset Ω) := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
    rcases hy with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl hz'))
    · exact Or.inr (Or.inr (Or.inr hσa))
    · exact Or.inl hσz'
    · exact Or.inr (Or.inl hσb)
  have htrue : ∀ y, c y = true → y ∈ ({z, a, z', b} : Finset Ω) := by
    intro y hy
    by_contra hyF
    have hσyF : σ y ∉ ({z, a, z', b} : Finset Ω) := fun h => hyF (by simpa [h2] using hσF _ h)
    have hyne : y ≠ z := fun h => hyF (by simp [h])
    have hyne' : y ≠ σ z := fun h => hyF (by rw [h, hz']; simp)
    have hdbl : swap z (σ z) * swap y (σ y) ∈ E :=
      h6 (Subgroup.subset_closure ⟨z, y, hyne, hyne', by rw [hy, hcz], rfl⟩)
    have hdz : (swap z (σ z) * swap y (σ y)) z = z' := by
      have : swap y (σ y) z = z := swap_apply_of_ne_of_ne (Ne.symm hyne) (fun h => hσyF (by simp [← h]))
      rw [Perm.mul_apply, this, hz', swap_apply_left]
    have hda : (swap z (σ z) * swap y (σ y)) a = a := by
      have h1' : swap y (σ y) a = a := swap_apply_of_ne_of_ne
        (fun h => hyF (by simp [← h])) (fun h => hσyF (by simp [← h]))
      rw [Perm.mul_apply, h1', swap_apply_of_ne_of_ne haz0 (by rw [hz']; exact Ne.symm haz')]
    have := hcomm _ hdbl z
    rw [hdz, ha, hda] at this
    rw [hbdef] at this
    exact hbz'' |>.elim <| by
      have h9 : ω z' = ω z := by rw [hbdef, this, ha]
      exact absurd (hωinj h9) hz'z
  have hmatched : ∀ y, ω y ≠ y := by
    intro y
    by_cases hy : c y = true
    · have := htrue y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl | rfl | rfl
      · rw [ha]; exact haz0
      · rw [haz]; exact haz0.symm
      · rw [hbdef]; exact hbz''
      · rw [hbz']; exact hbz''.symm
    · have hy' : c y = false := by simpa using hy
      rw [hF1 y hy']; exact h1 y
  refine ⟨{z, a, z', b}, ?_, hmatched, ?_, ?_, ?_, e, he, z, by simp, hez1, by rw [hez, ha]; exact haz'⟩
  · rw [Finset.card_insert_of_notMem (by simp [haz0.symm, hz'z.symm, hbz.symm]),
      Finset.card_insert_of_notMem (by simp [haz'.symm, hba.symm]),
      Finset.card_insert_of_notMem (by simp [hbz''.symm]), Finset.card_singleton]
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
    rcases hy with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl ha)
    · exact Or.inl haz
    · exact Or.inr (Or.inr (Or.inr hbdef))
    · exact Or.inr (Or.inr (Or.inl hbz'))
  · intro e' he' y hy
    rcases h3 e' he' y with h | h
    · rw [h]; exact hy
    · rw [h]; exact hσF y hy
  · intro e' he' y hy
    have hy' : c y = false := by
      by_contra hn
      exact hy (htrue y (by simpa using hn))
    rcases h3 e' he' y with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h, hF1 y hy'])

theorem fourOrbit_matched_off (hW : IsPGroup 2 W) {E : Subgroup (Perm Ω)} (hEW : E ≤ W)
    (hE : IsExp2 E) (hall : ∀ i : Ω, Nat.card (orbit E i) = 2 ∨ Nat.card (orbit E i) = 4)
    (hone : ∀ i j : Ω, Nat.card (orbit E i) = 4 → Nat.card (orbit E j) = 4 → j ∈ orbit E i)
    (hbij : Function.Bijective (evalOrb E E le_orbitStab)) {x₀ : Ω}
    (h4 : Nat.card (orbit E x₀) = 4) {y : Ω} (hy : y ∉ orbit E x₀) : partner hW y ≠ y := by
  classical
  have hc2 : Nat.card (orbit E y) = 2 := by
    rcases hall y with h | h
    · exact h
    · exact absurd (hone x₀ y h4 h) hy
  have hswap : ∀ y', y' ∈ orbit E y → y ≠ y' → partner hW y = y' := fun y' hy' hne =>
    partner_eq_of_swap_mem hW hne (hEW (swap_mem_of_bijective hE hbij hc2 hy' hne))
  have hfin : (orbit E y : Set Ω).Finite := Set.toFinite _
  have hlt : 1 < (orbit E y : Set Ω).ncard := by
    rw [← Nat.card_coe_set_eq, hc2]; norm_num
  obtain ⟨a, ha, b, hb, hab⟩ := (Set.one_lt_ncard hfin).1 hlt
  by_cases hay : y = a
  · have hyb : y ≠ b := hay ▸ hab
    rw [hswap b hb hyb]; exact hyb.symm
  · rw [hswap a ha hay]; exact Ne.symm hay

theorem cell_fourOrbit (hW : IsPGroup 2 W) {E : Subgroup (Perm Ω)} (hEW : E ≤ W) (hE : IsExp2 E)
    (hall : ∀ i : Ω, Nat.card (orbit E i) = 2 ∨ Nat.card (orbit E i) = 4)
    (hone : ∀ i j : Ω, Nat.card (orbit E i) = 4 → Nat.card (orbit E j) = 4 → j ∈ orbit E i)
    (hbij : Function.Bijective (evalOrb E E le_orbitStab)) {x₀ : Ω}
    (h4 : Nat.card (orbit E x₀) = 4) : CellConcl (partner hW) E := by
  classical
  obtain ⟨ω, hω⟩ : ∃ ω, ω = partner hW := ⟨_, rfl⟩
  rw [← hω]
  have hcomm : ∀ e ∈ E, ∀ x, ω (e x) = e (ω x) := fun e he x => by
    rw [hω]; exact partner_comm hW (hEW he) x
  have hωω : ∀ x, ω (ω x) = x := fun x => by rw [hω]; exact partner_partner hW x
  have hωinj : ∀ {x y}, ω x = ω y → x = y := fun {x y} h => by
    have := congrArg ω h
    rwa [hωω, hωω] at this
  have hsm : ∀ (g : E) (x : Ω), (g • x : Ω) = (g : Perm Ω) x := fun g x => rfl
  have hP : ∀ y, y ∉ orbit E x₀ → (∀ e ∈ E, e y = y ∨ e y = ω y) ∧ ω y ≠ y := by
    intro y hy
    have hc2 : Nat.card (orbit E y) = 2 := by
      rcases hall y with h | h
      · exact h
      · exact absurd (hone x₀ y h4 h) hy
    have hswap : ∀ y', y' ∈ orbit E y → y ≠ y' → ω y = y' := by
      intro y' hy' hne
      rw [hω]
      exact partner_eq_of_swap_mem hW hne (hEW (swap_mem_of_bijective hE hbij hc2 hy' hne))
    refine ⟨fun e he => ?_, ?_⟩
    · by_cases h : e y = y
      · exact Or.inl h
      · exact Or.inr (hswap _ ⟨⟨e, he⟩, rfl⟩ (Ne.symm h)).symm
    · have hfin : (orbit E y : Set Ω).Finite := Set.toFinite _
      have hlt : 1 < (orbit E y : Set Ω).ncard := by
        rw [← Nat.card_coe_set_eq, hc2]; norm_num
      obtain ⟨a, ha, b, hb, hab⟩ := (Set.one_lt_ncard hfin).1 hlt
      by_cases hay : y = a
      · have hyb : y ≠ b := hay ▸ hab
        rw [hswap b hb hyb]; exact hyb.symm
      · rw [hswap a ha hay]; exact Ne.symm hay
  have hstable : ∀ (g : E) (z : Ω), z ∈ orbit E x₀ → (g : Perm Ω) z ∈ orbit E x₀ := by
    intro g z hz
    obtain ⟨g1, hg1⟩ := hz
    refine ⟨g * g1, ?_⟩
    have h0 : (g1 : Perm Ω) x₀ = z := hg1
    show (g : Perm Ω) ((g1 : Perm Ω) x₀) = (g : Perm Ω) z
    rw [h0]
  have hωΔ : ω x₀ ∈ orbit E x₀ := by
    have hset : orbit E (ω x₀) = ω '' orbit E x₀ := by
      ext y
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨(g : Perm Ω) x₀, ⟨g, rfl⟩, by
          show ω ((g : Perm Ω) x₀) = (g : Perm Ω) (ω x₀)
          rw [hcomm g g.2 x₀]⟩
      · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
        exact ⟨g, by
          show (g : Perm Ω) (ω x₀) = ω ((g : Perm Ω) x₀)
          rw [hcomm g g.2 x₀]⟩
    have hcard : Nat.card (orbit E (ω x₀)) = 4 := by
      rw [Nat.card_coe_set_eq, hset, Set.ncard_image_of_injective _ (fun x y h => hωinj h),
        ← Nat.card_coe_set_eq]
      exact h4
    exact hone x₀ (ω x₀) h4 hcard
  by_cases hfix : ω x₀ = x₀
  · left
    intro e he z hz
    by_cases hzΔ : z ∈ orbit E x₀
    · exfalso
      obtain ⟨g, hg⟩ := hzΔ
      have hg' : (g : Perm Ω) x₀ = z := hg
      apply hz
      rw [← hg', hcomm g g.2, hfix]
    · exact (hP z hzΔ).1 e he
  right
  obtain ⟨r, hr⟩ := hωΔ
  have hr' : (r : Perm Ω) x₀ = ω x₀ := hr
  have hωr : ∀ z ∈ orbit E x₀, ω z = (r : Perm Ω) z := by
    intro z hz
    obtain ⟨g, hg⟩ := hz
    have hg' : (g : Perm Ω) x₀ = z := hg
    rw [← hg', hcomm g g.2, ← hr']
    have := hE.comm r.2 g.2
    exact congrArg (fun f : Perm Ω => f x₀) this.symm
  have hωne : ∀ z ∈ orbit E x₀, ω z ≠ z := by
    intro z hz hωz
    obtain ⟨g, hg⟩ := hz
    have hg' : (g : Perm Ω) x₀ = z := hg
    apply hfix
    have h1 : (r : Perm Ω) z = z := by rw [← hωr z ⟨g, hg⟩]; exact hωz
    have h3 : (g : Perm Ω) ((r : Perm Ω) x₀) = (r : Perm Ω) ((g : Perm Ω) x₀) :=
      congrArg (fun f : Perm Ω => f x₀) (hE.comm g.2 r.2)
    have h2 : (g : Perm Ω) (ω x₀) = (g : Perm Ω) x₀ := by
      rw [← hr', h3, hg']; exact h1
    exact (g : Perm Ω).injective h2
  have hmatched : ∀ y, ω y ≠ y := by
    intro y
    by_cases hy : y ∈ orbit E x₀
    · exact hωne y hy
    · exact (hP y hy).2
  have hFmem : ∀ y, y ∈ Finset.univ.filter (fun z => z ∈ orbit E x₀) ↔ y ∈ orbit E x₀ := by
    intro y; simp
  have hFcard : (Finset.univ.filter (fun z => z ∈ orbit E x₀)).card = 4 := by
    rw [← h4, Nat.card_eq_fintype_card, Fintype.card_subtype]
  obtain ⟨w, hwF, hwn⟩ : ∃ w, w ∈ Finset.univ.filter (fun z => z ∈ orbit E x₀) ∧
      w ∉ ({x₀, ω x₀} : Finset Ω) := by
    apply Finset.exists_mem_notMem_of_card_lt_card
    rw [hFcard]
    exact lt_of_le_of_lt Finset.card_le_two (by norm_num)
  obtain ⟨g, hg⟩ := (hFmem w).1 hwF
  have hg' : (g : Perm Ω) x₀ = w := hg
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hwn
  refine ⟨Finset.univ.filter (fun z => z ∈ orbit E x₀), hFcard, hmatched, ?_, ?_, ?_,
    g, g.2, x₀, (hFmem x₀).2 (mem_orbit_self x₀), ?_, ?_⟩
  · intro y hy
    have hy' := (hFmem y).1 hy
    exact (hFmem _).2 (by rw [hωr y hy']; exact hstable r y hy')
  · intro e he y hy
    exact (hFmem _).2 (hstable ⟨e, he⟩ y ((hFmem y).1 hy))
  · intro e he y hy
    exact (hP y (fun h => hy ((hFmem y).2 h))).1 e he
  · rw [hg']; exact fun h => hwn.1 h
  · rw [hg']; exact fun h => hwn.2 h

theorem cell_of_offender (hW : IsPGroup 2 W) {E : Subgroup (Perm Ω)} (hEW : E ≤ W) (hE : IsExp2 E)
    (h : OffenderShapeConcl E) : CellConcl (partner hW) E := by
  by_cases hf : ∃ p, ∀ g ∈ E, g p = p
  · left
    intro e he z _
    exact cell_swapType hW hEW (h.1 hf) e he z
  · rcases h.2 hf with ⟨hall, hord⟩ | ⟨⟨x₀, hx₀⟩, hall, hone, hbij⟩
    · obtain ⟨σ, c, hB⟩ := blockData_of_shape hall hord
      exact cell_blockData hW hEW hB
    · exact cell_fourOrbit hW hEW hE hall hone hbij hx₀

end Classif

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

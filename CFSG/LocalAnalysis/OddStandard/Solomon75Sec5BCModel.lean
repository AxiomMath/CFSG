module

public import CFSG.LocalAnalysis.OddStandard.Solomon75StdPermLift
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5Defs

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement
open AhatData

private theorem fixCount_add_card_support {n : ℕ} (σ : Perm (Fin n)) :
    fixCount σ + σ.support.card = n := by
  unfold fixCount
  have h : (Finset.univ.filter fun i => σ i = i) = Finset.univ \ σ.support := by
    ext i
    simp [Equiv.Perm.mem_support]
  rw [h, Finset.card_univ_sdiff, Fintype.card_fin]
  have : σ.support.card ≤ n := by
    simpa using Finset.card_le_univ σ.support
  omega

private theorem exists_four_fixed {n : ℕ} {σ : Perm (Fin n)} (h : fixCount σ = 4) :
    ∃ a b c d : Fin n, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      ∀ x, σ x = x ↔ x = a ∨ x = b ∨ x = c ∨ x = d := by
  set F : Finset (Fin n) := Finset.univ.filter fun i => σ i = i with hFdef
  have hcard : F.card = 4 := h
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd⟩ :=
    exists_four_distinct F (by omega)
  refine ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, fun x => ?_⟩
  have hsub : ({a, b, c, d} : Finset (Fin n)) ⊆ F := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl <;> assumption
  have hc4 : ({a, b, c, d} : Finset (Fin n)).card = 4 := by
    simp [Finset.card_insert_of_notMem, *]
  have heq : ({a, b, c, d} : Finset (Fin n)) = F :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  constructor
  · intro hx
    have hxF : x ∈ F := by simp [hFdef, hx]
    rw [← heq] at hxF
    simpa using hxF
  · intro hx
    have hxs : x ∈ ({a, b, c, d} : Finset (Fin n)) := by simpa using hx
    rw [heq] at hxs
    simpa [hFdef] using hxs

section KleinGroup

variable {G : Type*} [Group G]

private theorem klein_table {x y z : G} (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = z)
    (hyx : y * x = z) :
    x * z = y ∧ z * x = y ∧ y * z = x ∧ z * y = x := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hxy, ← mul_assoc, hx, one_mul]
  · rw [← hyx, mul_assoc, hx, mul_one]
  · rw [← hyx, ← mul_assoc, hy, one_mul]
  · rw [← hxy, mul_assoc, hy, mul_one]

private def kleinSub (x y z : G) (hx : x * x = 1) (hy : y * y = 1) (hz : z * z = 1)
    (hxy : x * y = z) (hyx : y * x = z) : Subgroup G where
  carrier := {g | g = 1 ∨ g = x ∨ g = y ∨ g = z}
  mul_mem' := by
    obtain ⟨h1, h2, h3, h4⟩ := klein_table hx hy hxy hyx
    intro g h hg hh
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    rcases hg with rfl | rfl | rfl | rfl <;> rcases hh with rfl | rfl | rfl | rfl <;>
      simp [hx, hy, hz, hxy, hyx, h1, h2, h3, h4]
  one_mem' := Or.inl rfl
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at hg ⊢
    rcases hg with rfl | rfl | rfl | rfl
    · simp
    · exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hx))
    · exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hy)))
    · exact Or.inr (Or.inr (Or.inr (inv_eq_of_mul_eq_one_right hz)))

private theorem mem_kleinSub {x y z : G} {hx : x * x = 1} {hy : y * y = 1} {hz : z * z = 1}
    {hxy : x * y = z} {hyx : y * x = z} {g : G} :
    g ∈ kleinSub x y z hx hy hz hxy hyx ↔ g = 1 ∨ g = x ∨ g = y ∨ g = z := Iff.rfl

private theorem card_kleinSub {x y z : G} (hx : x * x = 1) (hy : y * y = 1) (hz : z * z = 1)
    (hxy : x * y = z) (hyx : y * x = z) (h1x : x ≠ 1) (h1y : y ≠ 1) (h1z : z ≠ 1) (hxy' : x ≠ y)
    (hxz : x ≠ z) (hyz : y ≠ z) : Nat.card (kleinSub x y z hx hy hz hxy hyx) = 4 := by
  have hset : ((kleinSub x y z hx hy hz hxy hyx : Subgroup G) : Set G) = {1, x, y, z} := by
    ext g
    simp [mem_kleinSub, SetLike.mem_coe]
  show Nat.card ((kleinSub x y z hx hy hz hxy hyx : Subgroup G) : Set G) = 4
  rw [Nat.card_coe_set_eq, hset,
    Set.ncard_insert_of_notMem (by simp [h1x.symm, h1y.symm, h1z.symm]),
    Set.ncard_insert_of_notMem (by simp [hxy', hxz]), Set.ncard_pair hyz]

end KleinGroup

section FourPoints

variable {n : ℕ}

private def IsFpf (σ g : Perm (Fin n)) : Prop :=
  (∀ x, σ x ≠ x → g x = x) ∧ g * g = 1 ∧ ∀ x, σ x = x → g x ≠ x

private theorem eq_dbl_of_apply {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) {g : Perm (Fin n)}
    (hout : ∀ x, x ≠ a → x ≠ b → x ≠ c → x ≠ d → g x = x)
    (e1 : g a = b) (e2 : g b = a) (e3 : g c = d) (e4 : g d = c) :
    g = swap a b * swap c d := by
  have := hab.symm
  have := hac.symm
  have := had.symm
  have := hbc.symm
  have := hbd.symm
  have := hcd.symm
  ext x
  by_cases hx1 : x = a
  · subst hx1
    simp [Perm.mul_apply, swap_apply_def, *]
  by_cases hx2 : x = b
  · subst hx2
    simp [Perm.mul_apply, swap_apply_def, *]
  by_cases hx3 : x = c
  · subst hx3
    simp [Perm.mul_apply, swap_apply_def, *]
  by_cases hx4 : x = d
  · subst hx4
    simp [Perm.mul_apply, swap_apply_def, *]
  rw [hout x hx1 hx2 hx3 hx4]
  simp [Perm.mul_apply, swap_apply_def, *]

private theorem eq_dbl_of_isFpf {σ g : Perm (Fin n)} {a b c d : Fin n} (hab : a ≠ b)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hF : ∀ x, σ x = x ↔ x = a ∨ x = b ∨ x = c ∨ x = d) (hg : IsFpf σ g) :
    g = swap a b * swap c d ∨ g = swap a c * swap b d ∨ g = swap a d * swap b c := by
  obtain ⟨h0, h2, h3⟩ := hg
  have hinv : ∀ x, g (g x) = x := fun x => by
    simpa using congrArg (fun p : Perm (Fin n) => p x) h2
  have hfa : g a ≠ a := h3 a ((hF a).2 (Or.inl rfl))
  have hfb : g b ≠ b := h3 b ((hF b).2 (Or.inr (Or.inl rfl)))
  have hfc : g c ≠ c := h3 c ((hF c).2 (Or.inr (Or.inr (Or.inl rfl))))
  have hout : ∀ x, x ≠ a → x ≠ b → x ≠ c → x ≠ d → g x = x := fun x hxa hxb hxc hxd =>
    h0 x (fun hx => by
      rcases (hF x).1 hx with rfl | rfl | rfl | rfl <;> contradiction)
  have hcl : ∀ x, g x ≠ x → g x = a ∨ g x = b ∨ g x = c ∨ g x = d := by
    intro x hx
    by_contra hcon
    push Not at hcon
    have h' := hout (g x) hcon.1 hcon.2.1 hcon.2.2.1 hcon.2.2.2
    rw [hinv x] at h'
    exact hx h'.symm
  rcases hcl a hfa with ha | ha | ha | ha
  · exact absurd ha hfa
  · left
    have hb' : g b = a := by rw [← ha]; exact hinv a
    have hc' : g c = d := by
      rcases hcl c hfc with hc | hc | hc | hc
      · have := hinv c
        rw [hc, ha] at this
        exact absurd this hbc
      · have := hinv c
        rw [hc, hb'] at this
        exact absurd this hac
      · exact absurd hc hfc
      · exact hc
    have hd' : g d = c := by rw [← hc']; exact hinv c
    exact eq_dbl_of_apply hab hac had hbc hbd hcd hout ha hb' hc' hd'
  · right; left
    have hc' : g c = a := by rw [← ha]; exact hinv a
    have hb' : g b = d := by
      rcases hcl b hfb with hb | hb | hb | hb
      · have := hinv b
        rw [hb, ha] at this
        exact absurd this.symm hbc
      · exact absurd hb hfb
      · have := hinv b
        rw [hb, hc'] at this
        exact absurd this hab
      · exact hb
    have hd' : g d = b := by rw [← hb']; exact hinv b
    exact eq_dbl_of_apply (a := a) (b := c) (c := b) (d := d) hac hab had hbc.symm hcd hbd
      (fun x h1 h2 h3 h4 => hout x h1 h3 h2 h4) ha hc' hb' hd'
  · right; right
    have hd' : g d = a := by rw [← ha]; exact hinv a
    have hb' : g b = c := by
      rcases hcl b hfb with hb | hb | hb | hb
      · have := hinv b
        rw [hb, ha] at this
        exact absurd this.symm hbd
      · exact absurd hb hfb
      · exact hb
      · have := hinv b
        rw [hb, hd'] at this
        exact absurd this hab
    have hc' : g c = b := by rw [← hb']; exact hinv b
    exact eq_dbl_of_apply (a := a) (b := d) (c := b) (d := c) had hab hac hbd.symm hcd.symm hbc
      (fun x h1 h2 h3 h4 => hout x h1 h3 h4 h2) ha hd' hb' hc'

private theorem isFpf_dbl {σ : Perm (Fin n)} {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hF : ∀ x, σ x = x ↔ x = a ∨ x = b ∨ x = c ∨ x = d) : IsFpf σ (swap a b * swap c d) := by
  have := hab.symm
  have := hac.symm
  have := had.symm
  have := hbc.symm
  have := hbd.symm
  have := hcd.symm
  refine ⟨fun x hx => ?_, dbl_mul_self hab hac had hbc hbd hcd, fun x hx => ?_⟩
  · have hxa : x ≠ a := fun e => hx ((hF x).2 (Or.inl e))
    have hxb : x ≠ b := fun e => hx ((hF x).2 (Or.inr (Or.inl e)))
    have hxc : x ≠ c := fun e => hx ((hF x).2 (Or.inr (Or.inr (Or.inl e))))
    have hxd : x ≠ d := fun e => hx ((hF x).2 (Or.inr (Or.inr (Or.inr e))))
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hxc hxd, swap_apply_of_ne_of_ne hxa hxb]
  · rcases (hF x).1 hx with rfl | rfl | rfl | rfl <;>
      simp [Perm.mul_apply, swap_apply_def, *]

private theorem isFpf_conj {σ g ν : Perm (Fin n)} (hν : ν * σ = σ * ν) (hg : IsFpf σ g) :
    IsFpf σ (ν * g * ν⁻¹) := by
  have hcomm : ∀ x, σ (ν x) = ν (σ x) := fun x => by
    have := congrArg (fun e : Perm (Fin n) => e x) hν.symm
    simpa [Perm.mul_apply] using this
  have hfix' : ∀ y, σ (ν y) = ν y ↔ σ y = y := fun y => by
    rw [hcomm]
    exact ν.injective.eq_iff
  have hfix : ∀ x, σ (ν⁻¹ x) = ν⁻¹ x ↔ σ x = x := fun x => by
    have := hfix' (ν⁻¹ x)
    simpa using this.symm
  obtain ⟨h0, h2, h3⟩ := hg
  refine ⟨fun x hx => ?_, ?_, fun x hx => ?_⟩
  · have hx' : σ (ν⁻¹ x) ≠ ν⁻¹ x := fun h => hx ((hfix x).1 h)
    show ν (g (ν⁻¹ x)) = x
    rw [h0 _ hx']
    simp
  · calc ν * g * ν⁻¹ * (ν * g * ν⁻¹) = ν * (g * g) * ν⁻¹ := by group
      _ = 1 := by rw [h2]; group
  · have hx' : σ (ν⁻¹ x) = ν⁻¹ x := (hfix x).2 hx
    intro h
    apply h3 _ hx'
    apply ν.injective
    have h' : ν (g (ν⁻¹ x)) = x := h
    rw [h']
    simp

private def kleinOn (a b c d : Fin n) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : Subgroup (Perm (Fin n)) :=
  kleinSub (swap a b * swap c d) (swap a c * swap b d) (swap a d * swap b c)
    (dbl_mul_self hab hac had hbc hbd hcd) (dbl_mul_self hac hab had hbc.symm hcd hbd)
    (dbl_mul_self had hab hac hbd.symm hcd.symm hbc)
    (by rw [swap_mul_eq hac hab had hbc.symm hcd hbd, swap_comm c b])
    (swap_mul_eq hab hac had hbc hbd hcd)

private theorem mem_kleinOn_iff {a b c d : Fin n} {hab : a ≠ b} {hac : a ≠ c} {had : a ≠ d}
    {hbc : b ≠ c} {hbd : b ≠ d} {hcd : c ≠ d} {g : Perm (Fin n)} :
    g ∈ kleinOn a b c d hab hac had hbc hbd hcd ↔
      g = 1 ∨ g = swap a b * swap c d ∨ g = swap a c * swap b d ∨ g = swap a d * swap b c :=
  Iff.rfl

private theorem dbl_apply_left {a b c d : Fin n} (hac : a ≠ c) (had : a ≠ d) :
    (swap a b * swap c d) a = b := by
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne hac had, swap_apply_left]

private theorem card_kleinOn {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Nat.card (kleinOn a b c d hab hac had hbc hbd hcd) = 4 := by
  have e1 : swap a b * swap c d ≠ 1 := fun h => hab (by
    have := Equiv.Perm.ext_iff.1 h a
    rw [dbl_apply_left hac had, Perm.one_apply] at this
    exact this.symm)
  have e2 : swap a c * swap b d ≠ 1 := fun h => hac (by
    have := Equiv.Perm.ext_iff.1 h a
    rw [dbl_apply_left hab had, Perm.one_apply] at this
    exact this.symm)
  have e3 : swap a d * swap b c ≠ 1 := fun h => had (by
    have := Equiv.Perm.ext_iff.1 h a
    rw [dbl_apply_left hab hac, Perm.one_apply] at this
    exact this.symm)
  have e12 : swap a b * swap c d ≠ swap a c * swap b d := fun h => hbc (by
    have := Equiv.Perm.ext_iff.1 h a
    rwa [dbl_apply_left hac had, dbl_apply_left hab had] at this)
  have e13 : swap a b * swap c d ≠ swap a d * swap b c := fun h => hbd (by
    have := Equiv.Perm.ext_iff.1 h a
    rwa [dbl_apply_left hac had, dbl_apply_left hab hac] at this)
  have e23 : swap a c * swap b d ≠ swap a d * swap b c := fun h => hcd (by
    have := Equiv.Perm.ext_iff.1 h a
    rwa [dbl_apply_left hab had, dbl_apply_left hab hac] at this)
  exact card_kleinSub _ _ _ _ _ e1 e2 e3 e12 e13 e23

private theorem sign_of_mem_kleinOn {a b c d : Fin n} {hab : a ≠ b} {hac : a ≠ c} {had : a ≠ d}
    {hbc : b ≠ c} {hbd : b ≠ d} {hcd : c ≠ d} {g : Perm (Fin n)}
    (hg : g ∈ kleinOn a b c d hab hac had hbc hbd hcd) : sign g = 1 := by
  rcases mem_kleinOn_iff.1 hg with rfl | rfl | rfl | rfl
  · exact Perm.sign_one
  · exact AhatData.sign_swap_mul_swap hab hcd
  · exact AhatData.sign_swap_mul_swap hac hbd
  · exact AhatData.sign_swap_mul_swap had hbc

private theorem mul_self_of_mem_kleinOn {a b c d : Fin n} {hab : a ≠ b} {hac : a ≠ c}
    {had : a ≠ d} {hbc : b ≠ c} {hbd : b ≠ d} {hcd : c ≠ d} {g : Perm (Fin n)}
    (hg : g ∈ kleinOn a b c d hab hac had hbc hbd hcd) : g * g = 1 := by
  rcases mem_kleinOn_iff.1 hg with rfl | rfl | rfl | rfl
  · exact mul_one 1
  · exact dbl_mul_self hab hac had hbc hbd hcd
  · exact dbl_mul_self hac hab had hbc.symm hcd hbd
  · exact dbl_mul_self had hab hac hbd.symm hcd.symm hbc

private theorem isFpf_of_mem_kleinOn {σ g : Perm (Fin n)} {a b c d : Fin n} (hab : a ≠ b)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hF : ∀ x, σ x = x ↔ x = a ∨ x = b ∨ x = c ∨ x = d)
    (hg : g ∈ kleinOn a b c d hab hac had hbc hbd hcd) (hg1 : g ≠ 1) : IsFpf σ g := by
  have hF2 : ∀ x, σ x = x ↔ x = a ∨ x = c ∨ x = b ∨ x = d := fun x => by
    rw [hF x]; tauto
  have hF3 : ∀ x, σ x = x ↔ x = a ∨ x = d ∨ x = b ∨ x = c := fun x => by
    rw [hF x]; tauto
  rcases mem_kleinOn_iff.1 hg with rfl | rfl | rfl | rfl
  · exact absurd rfl hg1
  · exact isFpf_dbl hab hac had hbc hbd hcd hF
  · exact isFpf_dbl hac hab had hbc.symm hcd hbd hF2
  · exact isFpf_dbl had hab hac hbd.symm hcd.symm hbc hF3

private theorem kleinOn_le_altFixOf {σ : Perm (Fin n)} {a b c d : Fin n} (hab : a ≠ b)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hF : ∀ x, σ x = x ↔ x = a ∨ x = b ∨ x = c ∨ x = d) :
    kleinOn a b c d hab hac had hbc hbd hcd ≤ altFixOf σ := by
  intro g hg
  refine mem_altFixOf.2 ⟨?_, sign_of_mem_kleinOn hg⟩
  by_cases hg1 : g = 1
  · rw [hg1]
    exact fun x _ => rfl
  · exact (isFpf_of_mem_kleinOn hab hac had hbc hbd hcd hF hg hg1).1

private theorem kleinOn_conj {σ : Perm (Fin n)} {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hF : ∀ x, σ x = x ↔ x = a ∨ x = b ∨ x = c ∨ x = d) {ν g : Perm (Fin n)}
    (hν : ν * σ = σ * ν) (hg : g ∈ kleinOn a b c d hab hac had hbc hbd hcd) :
    ν * g * ν⁻¹ ∈ kleinOn a b c d hab hac had hbc hbd hcd := by
  by_cases hg1 : g = 1
  · rw [hg1]
    exact mem_kleinOn_iff.2 (Or.inl (by simp))
  · exact mem_kleinOn_iff.2 (Or.inr (eq_dbl_of_isFpf hab hac had hbc hbd hcd hF
      (isFpf_conj hν (isFpf_of_mem_kleinOn hab hac had hbc hbd hcd hF hg hg1))))

private theorem comm_cycle_dbl_false {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h : (swap a b * swap a c) * (swap a b * swap c d) =
      (swap a b * swap c d) * (swap a b * swap a c)) : False := by
  have h3 := Equiv.Perm.ext_iff.1 h a
  simp [Perm.mul_apply, swap_apply_def, hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm,
    had.symm, hbc.symm, hbd.symm, hcd.symm] at h3

end FourPoints

section Model

variable {n : ℕ} {K : Type} [Group K]

private theorem card_comap_ρ (C : AhatData.CoverSetup n K) {E : Subgroup (Perm (Fin n))}
    (hE : E ≤ alternatingGroup (Fin n)) : Nat.card (E.comap C.ρ) = 2 * Nat.card E := by
  set B : Subgroup K := E.comap C.ρ with hB
  let Mρ : ↥B →* Perm (Fin n) := C.ρ.comp B.subtype
  have hrange : Mρ.range = E := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact C.map_comap_eq_of_le hE
  have hker : Nat.card Mρ.ker = 2 := by
    have hZE : center K ≤ B := fun x hx => by
      rw [hB, Subgroup.mem_comap, (C.ρ_eq_one_iff).2 hx]
      exact E.one_mem
    have hk : Mρ.ker = (center K).subgroupOf B := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← C.ρ_eq_one_iff]
      rfl
    rw [hk, ← C.center_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZE).toEquiv
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Mρ.ker
  have h3 : Nat.card ↥Mρ.range = Nat.card ↥E := by rw [hrange]
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange Mρ).toEquiv, h3, hker] at h1
  omega

theorem exists_quat_model [Finite K] (C : AhatData.CoverSetup n K)
    (hn : 8 ≤ n) {α : MulAut K} {σ : Perm (Fin n)} (hα : C.Induces α σ) (hσ : σ * σ = 1)
    (hfix : fixCount σ = 4) :
    ∃ (Qb : Subgroup K) (xb ab : K), Qb ≤ AhatData.fixSub α ∧ Nat.card Qb = 8 ∧
      (∀ q ∈ Qb, q ≠ 1 → ∃ k : ℕ, q ^ k ∈ center K ∧ q ^ k ≠ 1) ∧
      xb ∈ AhatData.fixSub α ∧ ab ∈ AhatData.fixSub α ∧ ab * ab ∈ center K ∧ ab * ab ≠ 1 ∧
      xb * ab = ab * xb ∧ xb ^ 3 = 1 ∧ (∀ q ∈ Qb, xb * q * xb⁻¹ ∈ Qb) ∧
      (∃ q ∈ Qb, xb * q * xb⁻¹ ≠ q) ∧
      ∀ (β : MulAut K) (ν : Perm (Fin n)), C.Induces β ν → ν * σ = σ * ν →
        Qb.map β.toMonoidHom = Qb := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hF⟩ := exists_four_fixed hfix
  have hsupp : σ.support.card + 4 = n := by
    have := fixCount_add_card_support σ
    omega
  set V : Subgroup (Perm (Fin n)) := kleinOn a b c d hab hac had hbc hbd hcd
  have hVA : V ≤ alternatingGroup (Fin n) := fun g hg =>
    Perm.mem_alternatingGroup.2 (sign_of_mem_kleinOn hg)
  have hVD : V ≤ altFixOf σ := kleinOn_le_altFixOf hab hac had hbc hbd hcd hF
  have hDle : (altFixOf σ).comap C.ρ ≤ fixSub α := altFixOf_comap_le_fixSub C hn hα hsupp.le
  obtain ⟨m, hm⟩ : 2 ∣ σ.support.card :=
    Equiv.Perm.two_dvd_card_support (by rw [pow_two]; exact hσ)
  have hm2 : 2 ≤ m := by omega
  obtain ⟨r, hr⟩ := exists_isPairLift C hσ hm hm2
  have hc3 : (swap a b * swap a c).IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc
  obtain ⟨xb, hxbρ, hxb3⟩ := exists_lift_pow_three C hc3
  have hc3A : swap a b * swap a c ∈ altFixOf σ := by
    refine mem_altFixOf.2 ⟨fun x hx => ?_, hc3.sign⟩
    have hxa : x ≠ a := fun e => hx ((hF x).2 (Or.inl e))
    have hxb : x ≠ b := fun e => hx ((hF x).2 (Or.inr (Or.inl e)))
    have hxc : x ≠ c := fun e => hx ((hF x).2 (Or.inr (Or.inr (Or.inl e))))
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hxa hxc, swap_apply_of_ne_of_ne hxa hxb]
  have hxbD : xb ∈ (altFixOf σ).comap C.ρ := by
    rw [Subgroup.mem_comap, hxbρ]
    exact hc3A
  have hc3σ : (swap a b * swap a c) * σ = σ * (swap a b * swap a c) :=
    comm_of_forall_fixed hc3A.1
  refine ⟨V.comap C.ρ, xb, r, ?_, ?_, ?_, hDle hxbD, mem_fixSub.2 (hr.apply_eq hα),
    hr.sq_mem_center, hr.sq_ne_one hn, hr.comm_of_mem_altFixOf_comap hn hsupp.le hxbD, hxb3,
    ?_, ?_, ?_⟩
  · exact fun x hx => hDle (Subgroup.comap_mono hVD hx)
  · rw [card_comap_ρ C hVA, card_kleinOn hab hac had hbc hbd hcd]
  · intro q hq hq1
    have hqV : C.ρ q ∈ V := hq
    by_cases hqc : q ∈ center K
    · exact ⟨1, by simpa using hqc, by simpa using hq1⟩
    · have hρ1 : C.ρ q ≠ 1 := fun h => hqc ((C.ρ_eq_one_iff).1 h)
      have hρ2 : C.ρ q * C.ρ q = 1 := mul_self_of_mem_kleinOn hqV
      refine ⟨2, ?_, ?_⟩
      · rw [pow_two]
        exact C.sq_mem_center hρ2
      · rw [pow_two]
        rcases mem_kleinOn_iff.1 hqV with h | h | h | h
        · exact absurd h hρ1
        · exact C.sq_dbl_ne_one hn hab hac had hbc hbd hcd h
        · exact C.sq_dbl_ne_one hn hac hab had hbc.symm hcd hbd h
        · exact C.sq_dbl_ne_one hn had hab hac hbd.symm hcd.symm hbc h
  · intro q hq
    have hqV : C.ρ q ∈ V := hq
    show C.ρ (xb * q * xb⁻¹) ∈ V
    rw [map_mul, map_mul, map_inv, hxbρ]
    exact kleinOn_conj hab hac had hbc hbd hcd hF hc3σ hqV
  · have hd1 : swap a b * swap c d ∈ V := mem_kleinOn_iff.2 (Or.inr (Or.inl rfl))
    obtain ⟨q, hq⟩ := C.exists_ρ_eq (sign_of_mem_kleinOn hd1)
    refine ⟨q, show C.ρ q ∈ V by rw [hq]; exact hd1, fun h => ?_⟩
    have h1 : xb * q = q * xb := by
      calc xb * q = (xb * q * xb⁻¹) * xb := by group
        _ = q * xb := by rw [h]
    have h2 := congrArg C.ρ h1
    rw [map_mul, map_mul, hxbρ, hq] at h2
    exact comm_cycle_dbl_false hab hac had hbc hbd hcd h2
  · intro β ν hβ hν
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨q, hq, rfl⟩
      have hqV : C.ρ q ∈ V := hq
      show C.ρ (β q) ∈ V
      rw [hβ.map_ρ q]
      exact kleinOn_conj hab hac had hbc hbd hcd hF hν hqV
    · rw [Subgroup.card_map_of_injective β.injective]

end Model

end CFSG.OddStandard.Solomon75

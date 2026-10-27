module

public import CFSG.GH74.Generic.S45.LAltDefs
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms

public section

namespace CFSG.GH74.Generic.S45.LAlt

open Equiv Equiv.Perm Subgroup
open scoped commutatorElement

variable {n : ℕ}

section Flip

variable {σ : Perm (Fin n)}

@[expose] def flipGrp (σ : Perm (Fin n)) (hσ : σ * σ = 1) : Subgroup (Perm (Fin n)) where
  carrier := {f | ∀ x, f x = x ∨ f x = σ x}
  mul_mem' := by
    intro f g hf hg x
    rcases hg x with h | h
    · rw [Perm.mul_apply, h]
      exact hf x
    · rw [Perm.mul_apply, h]
      rcases hf (σ x) with h' | h'
      · exact Or.inr h'
      · exact Or.inl (h'.trans (sigma_sq_apply hσ x))
  one_mem' := fun x => Or.inl rfl
  inv_mem' := by
    intro f hf x
    have hu : f (f⁻¹ x) = x := by simp
    rcases hf (f⁻¹ x) with h | h
    · exact Or.inl (h.symm.trans hu)
    · refine Or.inr ?_
      have h2 : x = σ (f⁻¹ x) := hu.symm.trans h
      calc f⁻¹ x = σ (σ (f⁻¹ x)) := (sigma_sq_apply hσ _).symm
        _ = σ x := congrArg σ h2.symm

theorem mem_flipGrp {hσ : σ * σ = 1} {f : Perm (Fin n)} :
    f ∈ flipGrp σ hσ ↔ ∀ x, f x = x ∨ f x = σ x := Iff.rfl

theorem flip_apply_sigma {hσ : σ * σ = 1} {f : Perm (Fin n)} (hf : f ∈ flipGrp σ hσ) (x : Fin n) :
    f (σ x) = σ (f x) := by
  rcases hf x with h | h
  · rw [h]
    rcases hf (σ x) with h' | h'
    · exact h'
    · rw [sigma_sq_apply hσ] at h'
      have : σ x = x := f.injective (by rw [h', h])
      rw [h', this]
  · rw [h, sigma_sq_apply hσ]
    rcases hf (σ x) with h' | h'
    · have : σ x = x := f.injective (by rw [h', h])
      rw [h', this]
    · exact h'.trans (by rw [sigma_sq_apply hσ])

theorem flip_comm_sigma {hσ : σ * σ = 1} {f : Perm (Fin n)} (hf : f ∈ flipGrp σ hσ) :
    f * σ = σ * f :=
  Equiv.ext fun x => flip_apply_sigma hf x

theorem flip_mul_comm {hσ : σ * σ = 1} {f g : Perm (Fin n)} (hf : f ∈ flipGrp σ hσ)
    (hg : g ∈ flipGrp σ hσ) : f * g = g * f := by
  ext x
  rw [Perm.mul_apply, Perm.mul_apply]
  rcases hg x with h | h
  · rw [h]
    rcases hf x with h' | h'
    · rw [h', h]
    · rw [h', flip_apply_sigma hg, h]
  · rw [h, flip_apply_sigma hf]
    rcases hf x with h' | h'
    · rw [h', h]
    · rw [h', sigma_sq_apply hσ, flip_apply_sigma hg, h, sigma_sq_apply hσ]

theorem flip_mul_self {hσ : σ * σ = 1} {f : Perm (Fin n)} (hf : f ∈ flipGrp σ hσ) : f * f = 1 := by
  ext x
  rw [Perm.mul_apply]
  rcases hf x with h | h
  · rw [h, h]
    rfl
  · rw [h, flip_apply_sigma hf, h, sigma_sq_apply hσ]
    rfl

theorem conj_mem_flipGrp {hσ : σ * σ = 1} {l f : Perm (Fin n)} (hl : l * σ = σ * l)
    (hf : f ∈ flipGrp σ hσ) : l * f * l⁻¹ ∈ flipGrp σ hσ := by
  intro x
  have hlσ : ∀ y, l (σ y) = σ (l y) := fun y => congrArg (fun p : Perm (Fin n) => p y) hl
  have e : (l * f * l⁻¹) x = l (f (l⁻¹ x)) := by simp
  rw [e]
  rcases hf (l⁻¹ x) with h | h
  · left
    rw [h]
    simp
  · right
    rw [h, hlσ]
    simp

theorem swap_mem_flipGrp (hσ : σ * σ = 1) (x : Fin n) : swap x (σ x) ∈ flipGrp σ hσ := by
  intro y
  by_cases h1 : y = x
  · right
    rw [h1, swap_apply_left]
  · by_cases h2 : y = σ x
    · right
      rw [h2, swap_apply_right, sigma_sq_apply hσ]
    · left
      exact swap_apply_of_ne_of_ne h1 h2

end Flip

section Moves

variable {σ : Perm (Fin n)}

theorem moves_of_commute {l : Perm (Fin n)} (hl : l * σ = σ * l) {x : Fin n} (hx : σ x ≠ x) :
    σ (l x) ≠ l x := by
  have hlσ : l (σ x) = σ (l x) := congrArg (fun p : Perm (Fin n) => p x) hl
  rw [← hlσ]
  exact fun h => hx (l.injective h)

theorem fixes_of_preserves_pairs {Lb : Subgroup (Perm (Fin n))}
    (hLb : ∀ l ∈ Lb, l * σ = σ * l) (hperf : ⁅Lb, Lb⁆ = Lb)
    (hpair : ∀ l ∈ Lb, ∀ x, σ x ≠ x → l x = x ∨ l x = σ x) :
    ∀ l ∈ Lb, ∀ x, σ x ≠ x → l x = x := by
  let S : Subgroup (Perm (Fin n)) :=
    { carrier := {g | ∀ x, σ x ≠ x → g x = x}
      mul_mem' := fun {a b} ha hb x hx => by
        rw [Perm.mul_apply, hb x hx, ha x hx]
      one_mem' := fun x _ => rfl
      inv_mem' := fun {a} ha x hx => by
        have := ha x hx
        exact a.injective (by simpa using this.symm) }
  have hcomm : ∀ l ∈ Lb, ∀ m ∈ Lb, ∀ y, σ y ≠ y → l (m y) = m (l y) := by
    intro l hl m hm y hy
    have hlσ : ∀ z, l (σ z) = σ (l z) := fun z => congrArg (fun p : Perm (Fin n) => p z) (hLb l hl)
    have hmσ : ∀ z, m (σ z) = σ (m z) := fun z => congrArg (fun p : Perm (Fin n) => p z) (hLb m hm)
    rcases hpair l hl y hy with h1 | h1 <;> rcases hpair m hm y hy with h2 | h2
    · rw [h2, h1, h2]
    · rw [h2, hlσ, h1, h2]
    · rw [h2, h1, hmσ, h2]
    · rw [h2, hlσ, h1, hmσ, h2]
  have hle : ⁅Lb, Lb⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro l hl m hm x hx
    have hl' : l⁻¹ ∈ Lb := Lb.inv_mem hl
    have hm' : m⁻¹ ∈ Lb := Lb.inv_mem hm
    have hz : σ (l⁻¹ (m⁻¹ x)) ≠ l⁻¹ (m⁻¹ x) :=
      moves_of_commute (hLb l⁻¹ hl') (moves_of_commute (hLb m⁻¹ hm') hx)
    have key := hcomm l hl m hm _ hz
    have e : (⁅l, m⁆ : Perm (Fin n)) x = l (m (l⁻¹ (m⁻¹ x))) := by
      simp [commutatorElement_def]
    rw [e, key]
    simp
  intro l hl x hx
  have hl2 : l ∈ ⁅Lb, Lb⁆ := by rw [hperf]; exact hl
  exact hle hl2 x hx

end Moves

section Main

variable {σ : Perm (Fin n)}

theorem exists_pair_moved {Lb : Subgroup (Perm (Fin n))}
    (hLb : ∀ l ∈ Lb, l * σ = σ * l) (hperf : ⁅Lb, Lb⁆ = Lb)
    (hmove : ∃ l ∈ Lb, ∃ x, σ x ≠ x ∧ l x ≠ x) :
    ∃ l ∈ Lb, ∃ x, σ x ≠ x ∧ l x ≠ x ∧ l x ≠ σ x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨l, hl, x, hx, hlx⟩ := hmove
  have := fixes_of_preserves_pairs hLb hperf (fun l hl x hx => by
    by_cases h : l x = x
    · exact Or.inl h
    · exact Or.inr (hcon l hl x hx h)) l hl x hx
  exact hlx this

theorem exists_noncomm (hσ : σ * σ = 1) {Lb : Subgroup (Perm (Fin n))}
    (hLb : ∀ l ∈ Lb, l * σ = σ * l) (hperf : ⁅Lb, Lb⁆ = Lb)
    (hsimple : ∀ N : Subgroup (Perm (Fin n)), N ≤ Lb → (∀ g ∈ Lb, ∀ h ∈ N, g * h * g⁻¹ ∈ N) →
      N = ⊥ ∨ N = Lb)
    {v₀ : Perm (Fin n)} (hv₀ : v₀ ∈ Lb) (hv₀1 : v₀ ≠ 1)
    (hmove : ∃ l ∈ Lb, ∃ x, σ x ≠ x ∧ l x ≠ x ∧ l x ≠ σ x) :
    ∃ f ∈ flipGrp σ hσ, ∃ l ∈ Lb, v₀ * ⁅f, l⁆ ≠ ⁅f, l⁆ * v₀ := by
  by_contra hcon
  push Not at hcon
  set F := flipGrp σ hσ with hF
  let Wset : Set (Perm (Fin n)) := {w | ∃ f ∈ F, ∃ l ∈ Lb, w = ⁅f, l⁆}
  let C : Subgroup (Perm (Fin n)) := Lb ⊓ centralizer Wset
  have hCle : C ≤ Lb := inf_le_left
  have hCnorm : ∀ g ∈ Lb, ∀ h ∈ C, g * h * g⁻¹ ∈ C := by
    intro g hg h hh
    refine Subgroup.mem_inf.2 ⟨Lb.mul_mem (Lb.mul_mem hg (Subgroup.mem_inf.1 hh).1) (Lb.inv_mem hg), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro w ⟨f, hf, l, hl, rfl⟩
    have hgi : g⁻¹ ∈ Lb := Lb.inv_mem hg
    have hf' : g⁻¹ * f * g ∈ F := by
      have := conj_mem_flipGrp (hLb g⁻¹ hgi) hf
      simpa using this
    have hl' : g⁻¹ * l * g ∈ Lb := Lb.mul_mem (Lb.mul_mem hgi hl) hg
    have hh' := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hh).2 ⁅g⁻¹ * f * g, g⁻¹ * l * g⁆
      ⟨_, hf', _, hl', rfl⟩
    calc ⁅f, l⁆ * (g * h * g⁻¹) = g * (⁅g⁻¹ * f * g, g⁻¹ * l * g⁆ * h) * g⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = g * (h * ⁅g⁻¹ * f * g, g⁻¹ * l * g⁆) * g⁻¹ := by rw [hh']
      _ = (g * h * g⁻¹) * ⁅f, l⁆ := by simp only [commutatorElement_def]; group
  have hv₀C : v₀ ∈ C := by
    refine Subgroup.mem_inf.2 ⟨hv₀, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro w ⟨f, hf, l, hl, rfl⟩
    exact (hcon f hf l hl).symm
  have hC : C = Lb := by
    rcases hsimple C hCle hCnorm with h | h
    · exact absurd (by simpa [h] using hv₀C) hv₀1
    · exact h
  have hWc : ∀ c ∈ Lb, ∀ f ∈ F, ∀ l ∈ Lb, ⁅f, l⁆ * c = c * ⁅f, l⁆ := by
    intro c hc f hf l hl
    have : c ∈ C := hC ▸ hc
    exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 this).2 _ ⟨f, hf, l, hl, rfl⟩
  have hFmem : ∀ f ∈ F, ∀ l ∈ Lb, ⁅f, l⁆ ∈ F := by
    intro f hf l hl
    have h1 := conj_mem_flipGrp (hLb l hl) (F.inv_mem hf)
    have e : ⁅f, l⁆ = f * (l * f⁻¹ * l⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact F.mul_mem hf h1
  have hcentF : ∀ f ∈ F, ∀ l ∈ Lb, f * l = l * f := by
    intro f hf
    have : Group.IsPerfect ↥Lb := Subgroup.isPerfect_iff.2 hperf
    have : IsMulCommutative ↥F := ⟨⟨fun a b => Subtype.ext (flip_mul_comm a.2 b.2)⟩⟩
    let φ : ↥Lb →* ↥F :=
      { toFun := fun l => ⟨⁅f, (l : Perm (Fin n))⁆, hFmem f hf l l.2⟩
        map_one' := by
          apply Subtype.ext
          simp [commutatorElement_def]
        map_mul' := by
          intro a b
          apply Subtype.ext
          have hc : (a : Perm (Fin n)) * ⁅f, (b : Perm (Fin n))⁆ =
              ⁅f, (b : Perm (Fin n))⁆ * (a : Perm (Fin n)) :=
            (hWc a a.2 f hf b b.2).symm
          have e : (⁅f, (a : Perm (Fin n)) * (b : Perm (Fin n))⁆ : Perm (Fin n)) =
              ⁅f, (a : Perm (Fin n))⁆ * ((a : Perm (Fin n)) * ⁅f, (b : Perm (Fin n))⁆ *
                (a : Perm (Fin n))⁻¹) := by
            simp only [commutatorElement_def]; group
          show (⁅f, (a : Perm (Fin n)) * (b : Perm (Fin n))⁆ : Perm (Fin n)) = _
          rw [e, hc]
          simp }
    have h1 := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_one_of_commutative φ
    intro l hl
    have h2 := congrArg (fun ψ : ↥Lb →* ↥F => ((ψ ⟨l, hl⟩ : ↥F) : Perm (Fin n))) h1
    have h3 : (⁅f, l⁆ : Perm (Fin n)) = 1 := h2
    have h4 := (commutatorElement_eq_one_iff_commute.1 h3)
    exact h4.eq
  obtain ⟨l, hl, x, hx, hlx1, hlx2⟩ := hmove
  have hswap := hcentF (swap x (σ x)) (swap_mem_flipGrp hσ x) l hl
  have hconj : swap (l x) (l (σ x)) = l * swap x (σ x) * l⁻¹ := swap_apply_apply l x (σ x)
  have hlσ : l (σ x) = σ (l x) := congrArg (fun p : Perm (Fin n) => p x) (hLb l hl)
  rw [hlσ] at hconj
  have hconj2 : swap (l x) (σ (l x)) = swap x (σ x) := by
    rw [hconj, ← hswap]
    simp
  have hx3 : x ≠ σ (l x) := by
    intro h
    apply hlx2
    have := congrArg σ h
    rw [sigma_sq_apply hσ] at this
    exact this.symm
  have h5 : swap (l x) (σ (l x)) x = swap x (σ x) x := congrArg (fun p : Perm (Fin n) => p x) hconj2
  rw [swap_apply_of_ne_of_ne (Ne.symm hlx1) hx3, swap_apply_left] at h5
  exact hx h5.symm

theorem badCent_of_moves (hσ : σ * σ = 1) {Lb : Subgroup (Perm (Fin n))} (hLb : Lb ≤ centAlt σ)
    (hperf : ⁅Lb, Lb⁆ = Lb)
    (hsimple : ∀ N : Subgroup (Perm (Fin n)), N ≤ Lb → (∀ g ∈ Lb, ∀ h ∈ N, g * h * g⁻¹ ∈ N) →
      N = ⊥ ∨ N = Lb)
    {v₀ : Perm (Fin n)} (hv₀ : v₀ ∈ Lb) (hv₀2 : orderOf v₀ = 2)
    (hmove : ∃ l ∈ Lb, ∃ x, σ x ≠ x ∧ l x ≠ x) : BadCent σ := by
  have hLb' : ∀ l ∈ Lb, l * σ = σ * l := fun l hl => (mem_centAlt.1 (hLb hl)).2
  have hmove' := exists_pair_moved hLb' hperf hmove
  have hv₀1 : v₀ ≠ 1 := by
    rintro rfl
    simp at hv₀2
  obtain ⟨f, hf, l, hl, hnc⟩ := exists_noncomm hσ hLb' hperf hsimple hv₀ hv₀1 hmove'
  set F := flipGrp σ hσ with hF
  have hfσ : f * σ = σ * f := flip_comm_sigma hf
  set cf : Perm (Fin n) →* Perm (Fin n) := (MulAut.conj f).toMonoidHom with hcf
  have hconjle : Lb.map cf ≤ centAlt σ := by
    rintro _ ⟨g, hg, rfl⟩
    rw [mem_centAlt]
    obtain ⟨hg1, hg2⟩ := mem_centAlt.1 (hLb hg)
    refine ⟨?_, ?_⟩
    · have := (inferInstance : (alternatingGroup (Fin n)).Normal).conj_mem g hg1 f
      simpa [hcf] using this
    · have c1 : Commute f σ := hfσ
      have c2 : Commute g σ := hg2
      have := ((c1.mul_left c2).mul_left c1.inv_left).eq
      simpa [hcf] using this
  set N : Subgroup (Perm (Fin n)) := Lb ⊔ Lb.map cf with hN
  have hNle : N ≤ centAlt σ := sup_le hLb hconjle
  have hNperf : ⁅N, N⁆ = N := by
    apply le_antisymm (Subgroup.commutator_le_self N)
    apply sup_le
    · calc Lb = ⁅Lb, Lb⁆ := hperf.symm
        _ ≤ ⁅N, N⁆ := Subgroup.commutator_mono le_sup_left le_sup_left
    · calc Lb.map cf = (⁅Lb, Lb⁆).map cf := by rw [hperf]
        _ = ⁅Lb.map cf, Lb.map cf⁆ := Subgroup.map_commutator _ _ _
        _ ≤ ⁅N, N⁆ := Subgroup.commutator_mono le_sup_right le_sup_right
  have hwN : (⁅f, l⁆ : Perm (Fin n)) ∈ N := by
    have h1 : f * l * f⁻¹ ∈ N := Subgroup.mem_sup_right ⟨l, hl, by simp [hcf]⟩
    have h2 : l⁻¹ ∈ N := Subgroup.mem_sup_left (Lb.inv_mem hl)
    have := N.mul_mem h1 h2
    simpa [commutatorElement_def] using this
  have hv₀N : v₀ ∈ N := Subgroup.mem_sup_left hv₀
  have hwF : (⁅f, l⁆ : Perm (Fin n)) ∈ F := by
    have h1 := conj_mem_flipGrp (hLb' l hl) (F.inv_mem hf)
    have e : ⁅f, l⁆ = f * (l * f⁻¹ * l⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact F.mul_mem hf h1
  generalize (⁅f, l⁆ : Perm (Fin n)) = w at hnc hwN hwF
  have hgN : w * v₀ ∈ N := N.mul_mem hwN hv₀N
  have hv₀sq : v₀ * v₀ = 1 := by
    have := pow_orderOf_eq_one v₀
    rw [hv₀2, pow_two] at this
    exact this
  have hw2 : w * w = 1 := flip_mul_self hwF
  have hw'F : v₀ * w * v₀⁻¹ ∈ F := conj_mem_flipGrp (hLb' v₀ hv₀) hwF
  have hsq : (w * v₀) * (w * v₀) = w * (v₀ * w * v₀⁻¹) := by
    have e : (w * v₀) * (w * v₀) = w * (v₀ * w * v₀⁻¹) * (v₀ * v₀) := by group
    rw [e, hv₀sq, mul_one]
  have hsqF : (w * v₀) * (w * v₀) ∈ F := by
    rw [hsq]
    exact F.mul_mem hwF hw'F
  have hord : orderOf (w * v₀) = 4 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h1 : ¬ (w * v₀) ^ 2 ^ 1 = 1 := by
      intro h
      rw [pow_one, pow_two, hsq] at h
      apply hnc
      have h' : v₀ * w * v₀⁻¹ = w :=
        (eq_inv_of_mul_eq_one_right h).trans (eq_inv_of_mul_eq_one_left hw2).symm
      calc v₀ * w = (v₀ * w * v₀⁻¹) * v₀ := by group
        _ = w * v₀ := by rw [h']
    have h2 : (w * v₀) ^ 2 ^ (1 + 1) = 1 := by
      have : (w * v₀) ^ 2 ^ (1 + 1) = ((w * v₀) * (w * v₀)) * ((w * v₀) * (w * v₀)) := by
        rw [show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul, pow_two, pow_two]
      rw [this]
      exact flip_mul_self hsqF
    have := orderOf_eq_prime_pow h1 h2
    simpa using this
  exact ⟨⟨w * v₀, hNle hgN, hord⟩, N, hNle, hNperf, w * v₀, hgN, Or.inl hord⟩

end Main

end CFSG.GH74.Generic.S45.LAlt

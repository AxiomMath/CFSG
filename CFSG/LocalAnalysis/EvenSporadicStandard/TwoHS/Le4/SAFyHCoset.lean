module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyHThetaAux

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open CFSG.Permutation.SymmetricCoxeter

namespace FyCosetAux

variable {G : Type*} [Group G] (L : Subgroup G) (f : G)

def Gr (g : G) (s : ℤˣ) : Prop := (s = 1 ∧ g ∈ L) ∨ (s = -1 ∧ ∃ c ∈ L, g = c * f)

variable {L f}

theorem Gr.of_mem {g : G} (hg : g ∈ L) : Gr L f g 1 := Or.inl ⟨rfl, hg⟩

theorem Gr.one : Gr L f (1 : G) 1 := Gr.of_mem L.one_mem

theorem Gr.self : Gr L f f (-1) := Or.inr ⟨rfl, 1, L.one_mem, (one_mul f).symm⟩

theorem Gr.mul (hfL : ∀ l ∈ L, l * f = f * l) (hf2 : f ^ 2 ∈ L) {g g' : G} {s s' : ℤˣ}
    (h : Gr L f g s) (h' : Gr L f g' s') : Gr L f (g * g') (s * s') := by
  rcases h with ⟨rfl, hg⟩ | ⟨rfl, c, hc, rfl⟩ <;>
    rcases h' with ⟨rfl, hg'⟩ | ⟨rfl, c', hc', rfl⟩
  · exact Or.inl ⟨rfl, L.mul_mem hg hg'⟩
  · exact Or.inr ⟨one_mul _, g * c', L.mul_mem hg hc', (mul_assoc _ _ _).symm⟩
  · refine Or.inr ⟨mul_one _, c * g', L.mul_mem hc hg', ?_⟩
    rw [mul_assoc, ← hfL g' hg', ← mul_assoc]
  · refine Or.inl ⟨by decide, ?_⟩
    have e : c * f * (c' * f) = c * c' * f ^ 2 :=
      calc c * f * (c' * f) = c * (f * c') * f := by simp only [mul_assoc]
        _ = c * (c' * f) * f := by rw [hfL c' hc']
        _ = c * c' * f ^ 2 := by simp only [mul_assoc, pow_two]
    rw [e]
    exact L.mul_mem (L.mul_mem hc hc') hf2

theorem Gr.inv (hfL : ∀ l ∈ L, l * f = f * l) (hf2 : f ^ 2 ∈ L) {g : G} {s : ℤˣ}
    (h : Gr L f g s) : Gr L f g⁻¹ s := by
  rcases h with ⟨rfl, hg⟩ | ⟨rfl, c, hc, rfl⟩
  · exact Gr.of_mem (L.inv_mem hg)
  · refine Or.inr ⟨rfl, c⁻¹ * (f ^ 2)⁻¹, L.mul_mem (L.inv_mem hc) (L.inv_mem hf2), ?_⟩
    have hcomm : c⁻¹ * f⁻¹ = f⁻¹ * c⁻¹ :=
      (show Commute c⁻¹ f from hfL _ (L.inv_mem hc)).inv_right.eq
    calc (c * f)⁻¹ = f⁻¹ * c⁻¹ := mul_inv_rev c f
      _ = c⁻¹ * f⁻¹ := hcomm.symm
      _ = c⁻¹ * (f ^ 2)⁻¹ * f := by group

theorem Gr.pow_f (hfL : ∀ l ∈ L, l * f = f * l) (hf2 : f ^ 2 ∈ L) (n : ℕ) :
    Gr L f (f ^ n) ((-1 : ℤˣ) ^ n) := by
  induction n with
  | zero => simpa using Gr.one
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul hfL hf2 Gr.self

theorem Gr.mem_of_le {Q : Subgroup G} (hLQ : L ≤ Q) (hfQ : f ∈ Q) {g : G} {s : ℤˣ}
    (h : Gr L f g s) : g ∈ Q := by
  rcases h with ⟨-, hg⟩ | ⟨-, c, hc, rfl⟩
  · exact hLQ hg
  · exact Q.mul_mem (hLQ hc) hfQ

theorem Gr.mul_mem_iff {P : Subgroup G} (hLP : L ≤ P) (hfP : f ∈ P → f ∈ L) (hfnot : f ∉ L)
    {g z : G} {s : ℤˣ} (h : Gr L f g s) (hz : z ∈ P) : g * z ∈ P ↔ s = 1 := by
  constructor
  · intro hmem
    have hg : g ∈ P := by
      have := P.mul_mem hmem (P.inv_mem hz)
      rwa [mul_inv_cancel_right] at this
    rcases h with ⟨hs, -⟩ | ⟨-, c, hc, rfl⟩
    · exact hs
    · exfalso
      refine hfnot (hfP ?_)
      have := P.mul_mem (P.inv_mem (hLP hc)) hg
      rwa [inv_mul_cancel_left] at this
  · rintro rfl
    rcases h with ⟨-, hg⟩ | ⟨hs, -⟩
    · exact P.mul_mem (hLP hg) hz
    · exact absurd hs (by decide)

theorem Gr.mem_iff {P : Subgroup G} (hLP : L ≤ P) (hfP : f ∈ P → f ∈ L) (hfnot : f ∉ L)
    {g : G} {s : ℤˣ} (h : Gr L f g s) : g ∈ P ↔ s = 1 := by
  simpa using h.mul_mem_iff hLP hfP hfnot P.one_mem

theorem gr_perm {x : ℕ → G} (ΘS : Equiv.Perm (Fin 5) →* G) (hfL : ∀ l ∈ L, l * f = f * l)
    (hf2 : f ^ 2 ∈ L) (hΘx : ∀ i < 4, ΘS (adjSwap 4 i) = x i)
    (hx : ∀ i < 4, ∃ c ∈ L, x i = c * f) (σ : Equiv.Perm (Fin 5)) :
    Gr L f (ΘS σ) (Equiv.Perm.sign σ) := by
  have hσ : σ ∈ Subgroup.closure (adjSwap 4 '' Set.Iio 4) := by
    rw [closure_adjSwap]
    exact Subgroup.mem_top σ
  refine Subgroup.closure_induction (p := fun σ _ => Gr L f (ΘS σ) (Equiv.Perm.sign σ))
    ?_ ?_ ?_ ?_ hσ
  · rintro _ ⟨i, hi, rfl⟩
    have hi' : i < 4 := hi
    obtain ⟨c, hc, hxc⟩ := hx i hi'
    exact Or.inr ⟨ThetaHom.sign_adjSwap hi', c, hc, by rw [hΘx i hi', hxc]⟩
  · simpa using Gr.one
  · intro a b _ _ iha ihb
    rw [map_mul, map_mul]
    exact iha.mul hfL hf2 ihb
  · intro a _ iha
    rw [map_inv, Equiv.Perm.sign_inv]
    exact iha.inv hfL hf2

end FyCosetAux

open FyCosetAux

theorem fyCoset_of_theta {G : Type} [Group G] (L : Subgroup G) (f y yr r : G) (x : ℕ → G)
    (Θ : HModel →* G)
    (hΘr : ∀ k : ZMod 4, Θ (DihedralGroup.r k, 1, 1) = f ^ k.val)
    (hΘsr : ∀ k : ZMod 4, Θ (DihedralGroup.sr k, 1, 1) = (f ^ k.val)⁻¹ * yr)
    (hΘc : ∀ c : Z3, Θ (1, c, 1) = r ^ (Multiplicative.toAdd c).val)
    (hΘx : ∀ i < 4, Θ (1, 1, adjSwap 4 i) = x i)
    (hfL : ∀ l ∈ L, l * f = f * l) (hf2 : f ^ 2 ∈ L) (hfnot : f ∉ L)
    (hrL : r ∈ L) (hx : ∀ i < 4, ∃ c ∈ L, x i = c * f)
    (hyr : ∃ a ∈ L, yr = a * y)
    (hyf : y ∉ L ⊔ Subgroup.zpowers f)
    (hzL : ∀ k : ℤ, f ^ k ∈ L ⊔ Subgroup.zpowers y → f ^ k ∈ L) :
    FyCoset L f y Θ := by
  obtain ⟨a, ha, hya⟩ := hyr
  have hdec : ∀ (d : DihedralGroup 4) (c : Z3) (σ : Equiv.Perm (Fin 5)),
      Θ (d, c, σ) = Θ (1, c, 1) * Θ (1, 1, σ) * Θ (d, 1, 1) := by
    intro d c σ
    rw [← map_mul, ← map_mul]
    simp
  have hgrS : ∀ σ : Equiv.Perm (Fin 5), Gr L f (Θ (1, 1, σ)) (Equiv.Perm.sign σ) := fun σ =>
    gr_perm (Θ.comp ((MonoidHom.inr (DihedralGroup 4) (Z3 × Equiv.Perm (Fin 5))).comp
      (MonoidHom.inr Z3 (Equiv.Perm (Fin 5))))) hfL hf2 hΘx hx σ
  have hgrC : ∀ c : Z3, Gr L f (Θ (1, c, 1)) 1 := fun c => by
    refine Gr.of_mem ?_
    rw [hΘc]
    exact L.pow_mem hrL _
  have hLQ : L ≤ L ⊔ Subgroup.zpowers f := le_sup_left
  have hfQ : f ∈ L ⊔ Subgroup.zpowers f := Subgroup.mem_sup_right (Subgroup.mem_zpowers f)
  have hLP : L ≤ L ⊔ Subgroup.zpowers y := le_sup_left
  have hyrP : yr ∈ L ⊔ Subgroup.zpowers y := by
    rw [hya]
    exact (L ⊔ Subgroup.zpowers y).mul_mem (hLP ha)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
  have hfP : f ∈ L ⊔ Subgroup.zpowers y → f ∈ L := fun h => by
    simpa using hzL 1 (by simpa using h)
  have hgs : ∀ (c : Z3) (σ : Equiv.Perm (Fin 5)),
      Gr L f (Θ (1, c, 1) * Θ (1, 1, σ)) (Equiv.Perm.sign σ) := fun c σ => by
    simpa using (hgrC c).mul hfL hf2 (hgrS σ)
  refine ⟨fun d c σ => ?_, fun d c σ => ?_⟩
  · have hg : Θ (1, c, 1) * Θ (1, 1, σ) ∈ L ⊔ Subgroup.zpowers f :=
      ((hgs c σ).mem_of_le hLQ hfQ)
    rw [hdec]
    rcases d with k | k
    · rw [hΘr]
      exact iff_of_true ((L ⊔ Subgroup.zpowers f).mul_mem hg
        ((L ⊔ Subgroup.zpowers f).pow_mem hfQ _)) ⟨k, rfl⟩
    · rw [hΘsr]
      refine iff_of_false ?_ ?_
      · intro hmem
        refine hyf ?_
        have hu : f ^ k.val ∈ L ⊔ Subgroup.zpowers f := (L ⊔ Subgroup.zpowers f).pow_mem hfQ _
        have h1 := (L ⊔ Subgroup.zpowers f).mul_mem
          ((L ⊔ Subgroup.zpowers f).mul_mem hu ((L ⊔ Subgroup.zpowers f).inv_mem hg)) hmem
        have e : f ^ k.val * (Θ (1, c, 1) * Θ (1, 1, σ))⁻¹ *
            (Θ (1, c, 1) * Θ (1, 1, σ) * ((f ^ k.val)⁻¹ * yr)) = yr := by group
        rw [e] at h1
        have hy : y = a⁻¹ * yr := by rw [hya]; group
        rw [hy]
        exact (L ⊔ Subgroup.zpowers f).mul_mem ((L ⊔ Subgroup.zpowers f).inv_mem (hLQ ha)) h1
      · rintro ⟨k', hk'⟩
        cases hk'
  · rw [hdec]
    rcases d with k | k
    · rw [hΘr]
      refine (Gr.mem_iff hLP hfP hfnot ((hgs c σ).mul hfL hf2 (Gr.pow_f hfL hf2 k.val))).trans ?_
      rw [dihChar_r, mul_comm]
    · rw [hΘsr, ← mul_assoc]
      refine (Gr.mul_mem_iff hLP hfP hfnot
        ((hgs c σ).mul hfL hf2 ((Gr.pow_f hfL hf2 k.val).inv hfL hf2)) hyrP).trans ?_
      rw [dihChar_sr, one_mul, mul_comm]

end CFSG.EvenSporadicStandard.TwoHS

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.Ext2B

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'}

theorem cp_exists_rep_with (K : Subgroup G) (t₀ : G) :
    ∃ rep : G → G, rep t₀ = t₀ ∧ (∀ t, ConjIn K (rep t) t) ∧
      ∀ t₁ t₂, ConjIn K t₁ t₂ → rep t₁ = rep t₂ := by
  classical
  have hrefl : ∀ x, ConjIn K x x := fun x => ⟨1, K.one_mem, by simp⟩
  have hsymm : ∀ {x y}, ConjIn K x y → ConjIn K y x := by
    rintro x y ⟨k, hk, rfl⟩
    exact ⟨k⁻¹, K.inv_mem hk, by group⟩
  have htrans : ∀ {x y w}, ConjIn K x y → ConjIn K y w → ConjIn K x w := by
    rintro x y w ⟨k, hk, rfl⟩ ⟨m, hm, rfl⟩
    exact ⟨m * k, K.mul_mem hm hk, by group⟩
  let s : Setoid G := ⟨fun x y => ConjIn K x y, ⟨hrefl, hsymm, htrans⟩⟩
  refine ⟨fun t => if ConjIn K t₀ t then t₀ else Quotient.out (Quotient.mk s t), ?_, ?_, ?_⟩
  · simp [hrefl]
  · intro t
    by_cases ht : ConjIn K t₀ t
    · simpa [ht] using ht
    · show ConjIn K (if ConjIn K t₀ t then t₀ else Quotient.out (Quotient.mk s t)) t
      rw [if_neg ht]
      exact Quotient.mk_out (s := s) t
  · intro t₁ t₂ h12
    by_cases h1 : ConjIn K t₀ t₁
    · have h2 : ConjIn K t₀ t₂ := htrans h1 h12
      simp [h1, h2]
    · have h2 : ¬ ConjIn K t₀ t₂ := fun h2 => h1 (htrans h2 (hsymm h12))
      have hq : Quotient.mk s t₁ = Quotient.mk s t₂ := Quotient.sound h12
      simp [h1, h2, hq]

theorem cp_mem_inv_of_conjIn {K : Subgroup G} {r t : G} (hc : ConjIn K r t) (ht : t ∈ InvIn K) :
    r ∈ InvIn K := by
  obtain ⟨k, hk, rfl⟩ := hc
  refine ⟨?_, ?_⟩
  · have := K.mul_mem (K.mul_mem (K.inv_mem hk) ht.1) hk
    simpa [mul_assoc] using this
  · have h2 : orderOf ((MulAut.conj k) r) = 2 := by simpa [MulAut.conj_apply] using ht.2
    rwa [MulEquiv.orderOf_eq] at h2

theorem cp_exists_iso_inv (h : F5Std a z) (h' : F5Std a' z') {b : G} (hb : IsConj a b) {β : G → G'}
    (hb' : IsConj a' (β b)) (hβ : IsIsoOn (Gx b) (Gx (β b)) β) {r : G} (hr : r ∈ InvIn (Gx b)) :
    ∃ ψ : G → G', IsIsoOn (Gx r) (Gx (β r)) ψ ∧ ∀ x ∈ Gxy b r, ψ x = β x := by
  have hB : F5Std b z := h.of_isConj hb (IsConj.refl z)
  have hB' : F5Std (β b) z' := h'.of_isConj hb' (IsConj.refl z')
  rcases inv_cover hB hr with rfl | h2A | h2B | h2AB | h2BB
  · exact ⟨β, hβ, fun x _ => rfl⟩
  · exact exists_iso_2A hB hB' hβ h2A
  · exact exists_iso_2B hB hB' hβ h2B
  · exact exists_iso_2AB hB hB' hβ h2AB
  · exact exists_iso_2BB hB hB' hβ h2BB

@[expose] def cpForm (β ψ : G → G') (k x : G) : G' := β k * ψ (k⁻¹ * x * k) * (β k)⁻¹

variable {b : G} {β : G → G'}

theorem cpForm_indep (hβ : IsIsoOn (Gx b) (Gx (β b)) β) {r : G} {ψ : G → G'}
    (hψ : IsIsoOn (Gx r) (Gx (β r)) ψ) (hres : ∀ x ∈ Gxy b r, ψ x = β x) {k₁ k₂ : G}
    (hk₁ : k₁ ∈ Gx b) (hk₂ : k₂ ∈ Gx b) (hk : k₁ * r * k₁⁻¹ = k₂ * r * k₂⁻¹) {x : G}
    (hx : x ∈ Gx (k₁ * r * k₁⁻¹)) : cpForm β ψ k₁ x = cpForm β ψ k₂ x := by
  set h : G := k₂⁻¹ * k₁ with hh
  have hhGx : h ∈ Gx b := by
    rw [hh]; exact (Gx b).mul_mem ((Gx b).inv_mem hk₂) hk₁
  have hhGxr : h ∈ Gx r := by
    rw [mem_Gx, hh]
    calc r * (k₂⁻¹ * k₁) = k₂⁻¹ * (k₂ * r * k₂⁻¹) * k₁ := by group
      _ = k₂⁻¹ * (k₁ * r * k₁⁻¹) * k₁ := by rw [← hk]
      _ = k₂⁻¹ * k₁ * r := by group
  have hhGxy : h ∈ Gxy b r := mem_Gxy.mpr ⟨hhGx, hhGxr⟩
  have hy : k₁⁻¹ * x * k₁ ∈ Gx r := (cp_isIsoOn_conj_cent_inv k₁ r).mem x hx
  have hψh : ψ h = β h := hres h hhGxy
  have hmul : ψ (h * (k₁⁻¹ * x * k₁) * h⁻¹)
      = ψ h * ψ (k₁⁻¹ * x * k₁) * (ψ h)⁻¹ := hψ.map_conj hhGxr hy
  have hβmul : β (k₂ * h) = β k₂ * β h := hβ.map_mul k₂ hk₂ h hhGx
  have hyx : k₂⁻¹ * x * k₂ = h * (k₁⁻¹ * x * k₁) * h⁻¹ := by
    rw [hh]; group
  have hk₂h : k₂ * h = k₁ := by rw [hh]; group
  have hmain : cpForm β ψ k₂ x = β (k₂ * h) * ψ (k₁⁻¹ * x * k₁) * (β (k₂ * h))⁻¹ := by
    simp only [cpForm]
    rw [hyx, hmul, hψh, hβmul]
    group
  rw [hmain, hk₂h]
  simp only [cpForm]

theorem cpForm_iso (hβ : IsIsoOn (Gx b) (Gx (β b)) β) {r : G} (hr : r ∈ Gx b) {ψ : G → G'}
    (hψ : IsIsoOn (Gx r) (Gx (β r)) ψ) {k : G} (hk : k ∈ Gx b) :
    IsIsoOn (Gx (k * r * k⁻¹)) (Gx (β (k * r * k⁻¹))) (cpForm β ψ k) := by
  have hconj_β : β (k * r * k⁻¹) = β k * β r * (β k)⁻¹ := hβ.map_conj hk hr
  have hcomp : IsIsoOn (Gx (k * r * k⁻¹)) (Gx (β (k * r * k⁻¹)))
      ((fun u => β k * u * (β k)⁻¹) ∘ ψ ∘ (fun x => k⁻¹ * x * k)) := by
    rw [hconj_β]
    exact (cp_isIsoOn_conj_cent_inv k r).comp (hψ.comp (cp_isIsoOn_conj_cent (β k) (β r)))
  refine hcomp.congr fun x hx => ?_
  simp [cpForm, Function.comp]

theorem cpForm_restrict (hβ : IsIsoOn (Gx b) (Gx (β b)) β) {r : G} (hr : r ∈ Gx b) {ψ : G → G'}
    (hres : ∀ x ∈ Gxy b r, ψ x = β x) {k : G} (hk : k ∈ Gx b) {x : G}
    (hx : x ∈ Gxy b (k * r * k⁻¹)) : cpForm β ψ k x = β x := by
  rw [mem_Gxy] at hx
  obtain ⟨hxb, hxk⟩ := hx
  have hyb : k⁻¹ * x * k ∈ Gx b :=
    (Gx b).mul_mem ((Gx b).mul_mem ((Gx b).inv_mem hk) hxb) hk
  have hyr : k⁻¹ * x * k ∈ Gx r := (cp_isIsoOn_conj_cent_inv k r).mem x hxk
  have hψy : ψ (k⁻¹ * x * k) = β (k⁻¹ * x * k) := hres _ (mem_Gxy.mpr ⟨hyb, hyr⟩)
  have hconj : k * (k⁻¹ * x * k) * k⁻¹ = x := by group
  simp only [cpForm]
  rw [hψy, ← hβ.map_conj hk hyb, hconj]

theorem cpForm_equivariant (hβ : IsIsoOn (Gx b) (Gx (β b)) β) {ψ : G → G'} {k g : G}
    (hk : k ∈ Gx b) (hg : g ∈ Gx b) (x : G) :
    cpForm β ψ (g * k) (g * x * g⁻¹) = β g * cpForm β ψ k x * (β g)⁻¹ := by
  have hβmul : β (g * k) = β g * β k := hβ.map_mul g hg k hk
  have e : (g * k)⁻¹ * (g * x * g⁻¹) * (g * k) = k⁻¹ * x * k := by group
  simp only [cpForm]
  rw [hβmul, e]
  group

theorem cp_exists_app_of_reps (hβ : IsIsoOn (Gx b) (Gx (β b)) β) {rep : G → G}
    (hrep : ∀ t ∈ InvIn (Gx b), ConjIn (Gx b) (rep t) t)
    (hconst : ∀ t₁ ∈ InvIn (Gx b), ∀ t₂ ∈ InvIn (Gx b), ConjIn (Gx b) t₁ t₂ → rep t₁ = rep t₂)
    {ψ : G → G → G'} (hψ : ∀ r ∈ InvIn (Gx b), IsIsoOn (Gx r) (Gx (β r)) (ψ r))
    (hres : ∀ r ∈ InvIn (Gx b), ∀ x ∈ Gxy b r, ψ r x = β x) :
    ∃ app : G → G → G',
      (∀ t ∈ InvIn (Gx b), IsIsoOn (Gx t) (Gx (β t)) (app t)) ∧
      (∀ t ∈ InvIn (Gx b), ∀ x ∈ Gxy b t, app t x = β x) ∧
      (∀ t ∈ InvIn (Gx b), ∀ g ∈ Gx b, ∀ x ∈ Gx t,
        app (g * t * g⁻¹) (g * x * g⁻¹) = β g * app t x * (β g)⁻¹) ∧
      ∀ t ∈ InvIn (Gx b), rep t = t → ∀ x ∈ Gx t, app t x = ψ t x := by
  classical
  have hκ0 : ∀ t : G, ∃ k : G, t ∈ InvIn (Gx b) → k ∈ Gx b ∧ k * rep t * k⁻¹ = t := by
    intro t
    by_cases ht : t ∈ InvIn (Gx b)
    · obtain ⟨k, hk, hkt⟩ := hrep t ht
      exact ⟨k, fun _ => ⟨hk, hkt⟩⟩
    · exact ⟨1, fun h => absurd h ht⟩
  choose κ hκ using hκ0
  refine ⟨fun t => cpForm β (ψ (rep t)) (κ t), ?_, ?_, ?_, ?_⟩
  · intro t ht
    have hrt : rep t ∈ InvIn (Gx b) := cp_mem_inv_of_conjIn (hrep t ht) ht
    have h := cpForm_iso (b := b) hβ hrt.1 (hψ (rep t) hrt) (hκ t ht).1
    change IsIsoOn (Gx t) (Gx (β t)) (cpForm β (ψ (rep t)) (κ t))
    rwa [(hκ t ht).2] at h
  · intro t ht x hx
    have hrt : rep t ∈ InvIn (Gx b) := cp_mem_inv_of_conjIn (hrep t ht) ht
    have hx' : x ∈ Gxy b (κ t * rep t * (κ t)⁻¹) := by rw [(hκ t ht).2]; exact hx
    have h := cpForm_restrict (b := b) hβ hrt.1 (hres (rep t) hrt) (hκ t ht).1 (x := x) hx'
    change cpForm β (ψ (rep t)) (κ t) x = β x
    exact h
  · intro t ht g hg x hx
    set t' : G := g * t * g⁻¹ with ht'_def
    have ht'_mem : t' ∈ Gx b := by
      rw [ht'_def]
      exact (Gx b).mul_mem ((Gx b).mul_mem hg ht.1) ((Gx b).inv_mem hg)
    have ht'_inv : t' ∈ InvIn (Gx b) := by
      refine ⟨ht'_mem, ?_⟩
      rw [ht'_def, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact ht.2
    have hrt : rep t ∈ InvIn (Gx b) := cp_mem_inv_of_conjIn (hrep t ht) ht
    have hconj_t' : ConjIn (Gx b) t t' := ⟨g, hg, by rw [ht'_def]⟩
    have hrepeq : rep t' = rep t := (hconst t ht t' ht'_inv hconj_t').symm
    have hκt' : κ t' * rep t * (κ t')⁻¹ = t' := by
      have := (hκ t' ht'_inv).2
      rwa [hrepeq] at this
    have hκt : κ t * rep t * (κ t)⁻¹ = t := (hκ t ht).2
    have hconj_eq : κ t' * rep t * (κ t')⁻¹ = (g * κ t) * rep t * (g * κ t)⁻¹ := by
      rw [hκt']
      calc t' = g * t * g⁻¹ := ht'_def
        _ = g * (κ t * rep t * (κ t)⁻¹) * g⁻¹ := by rw [hκt]
        _ = (g * κ t) * rep t * (g * κ t)⁻¹ := by group
    have hxg : g * x * g⁻¹ ∈ Gx (κ t' * rep t * (κ t')⁻¹) := by
      rw [hκt', ht'_def]
      exact (cp_isIsoOn_conj_cent g t).mem x hx
    have hindep := cpForm_indep (b := b) hβ (hψ (rep t) hrt) (hres (rep t) hrt)
      (hκ t' ht'_inv).1 ((Gx b).mul_mem hg (hκ t ht).1) hconj_eq hxg
    have heq : cpForm β (ψ (rep t)) (g * κ t) (g * x * g⁻¹)
        = β g * cpForm β (ψ (rep t)) (κ t) x * (β g)⁻¹ :=
      cpForm_equivariant (b := b) hβ (hκ t ht).1 hg x
    change cpForm β (ψ (rep t')) (κ t') (g * x * g⁻¹)
      = β g * cpForm β (ψ (rep t)) (κ t) x * (β g)⁻¹
    rw [hrepeq, hindep, heq]
  · intro t ht hrept x hx
    have hrt : rep t ∈ InvIn (Gx b) := cp_mem_inv_of_conjIn (hrep t ht) ht
    have hκt : κ t * rep t * (κ t)⁻¹ = t := (hκ t ht).2
    have hk₁eq : κ t * rep t * (κ t)⁻¹ = 1 * rep t * 1⁻¹ := by
      rw [hκt, hrept]; group
    have hx' : x ∈ Gx (κ t * rep t * (κ t)⁻¹) := by rw [hκt]; exact hx
    have hindep := cpForm_indep (b := b) hβ (hψ (rep t) hrt) (hres (rep t) hrt)
      (hκ t ht).1 (Gx b).one_mem hk₁eq hx'
    change cpForm β (ψ (rep t)) (κ t) x = ψ t x
    rw [hindep]
    simp [cpForm, hβ.map_one, hrept]

end CFSG.EvenSporadicStandard.HNRecog.Section4

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpFamBuild
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpFamTyped

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'}

structure Fam (b : G) (β : G → G') where
  app : G → G → G'
  iso : ∀ t ∈ InvIn (Gx b), IsIsoOn (Gx t) (Gx (β t)) (app t)
  restrict : ∀ t ∈ InvIn (Gx b), ∀ x ∈ Gxy b t, app t x = β x
  equivariant : ∀ t ∈ InvIn (Gx b), ∀ g ∈ Gx b, ∀ x ∈ Gx t,
    app (g * t * g⁻¹) (g * x * g⁻¹) = β g * app t x * (β g)⁻¹

theorem exists_fam (h : F5Std a z) (h' : F5Std a' z') {b : G} (hb : IsConj a b) {β : G → G'}
    (hb' : IsConj a' (β b)) (hβ : IsIsoOn (Gx b) (Gx (β b)) β) : Nonempty (Fam b β) := by
  classical
  obtain ⟨rep, -, hrep, hconst⟩ := cp_exists_rep_with (Gx b) b
  have hex : ∀ r, ∃ ψ : G → G', r ∈ InvIn (Gx b) → IsIsoOn (Gx r) (Gx (β r)) ψ ∧
      ∀ x ∈ Gxy b r, ψ x = β x := by
    intro r
    by_cases hr : r ∈ InvIn (Gx b)
    · obtain ⟨ψ, h1, h2⟩ := cp_exists_iso_inv h h' hb hb' hβ hr
      exact ⟨ψ, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨fun _ => 1, fun hr' => absurd hr' hr⟩
  choose ψ hψ using hex
  obtain ⟨app, h1, h2, h3, -⟩ := cp_exists_app_of_reps hβ (rep := rep) (fun t _ => hrep t)
    (fun t₁ _ t₂ _ hc => hconst t₁ t₂ hc) (fun r hr => (hψ r hr).1) (fun r hr => (hψ r hr).2)
  exact ⟨⟨app, h1, h2, h3⟩⟩

theorem exists_fam_extending (h : F5Std a z) (h' : F5Std a' z') {b : G} (hb : IsConj a b)
    {β : G → G'} (hb' : IsConj a' (β b)) (hβ : IsIsoOn (Gx b) (Gx (β b)) β) {t : G}
    (ht : t ∈ InvIn (Gx b)) {ψ : G → G'} (hψ : IsIsoOn (Gx t) (Gx (β t)) ψ)
    (hres : ∀ x ∈ Gxy b t, ψ x = β x) : ∃ F : Fam b β, ∀ x ∈ Gx t, F.app t x = ψ x := by
  classical
  obtain ⟨rep, hrt, hrep, hconst⟩ := cp_exists_rep_with (Gx b) t
  have hex : ∀ r, ∃ ψ' : G → G', r ∈ InvIn (Gx b) → IsIsoOn (Gx r) (Gx (β r)) ψ' ∧
      ∀ x ∈ Gxy b r, ψ' x = β x := by
    intro r
    by_cases hr : r ∈ InvIn (Gx b)
    · obtain ⟨ψ', h1, h2⟩ := cp_exists_iso_inv h h' hb hb' hβ hr
      exact ⟨ψ', fun _ => ⟨h1, h2⟩⟩
    · exact ⟨fun _ => 1, fun hr' => absurd hr' hr⟩
  choose ψ₀ hψ₀ using hex
  let Ψ : G → G → G' := fun r => if r = t then ψ else ψ₀ r
  have hΨ : ∀ r ∈ InvIn (Gx b), IsIsoOn (Gx r) (Gx (β r)) (Ψ r) := by
    intro r hr
    by_cases hrt' : r = t
    · subst hrt'
      simpa [Ψ] using hψ
    · simpa [Ψ, hrt'] using (hψ₀ r hr).1
  have hΨres : ∀ r ∈ InvIn (Gx b), ∀ x ∈ Gxy b r, Ψ r x = β x := by
    intro r hr x hx
    by_cases hrt' : r = t
    · subst hrt'
      simpa [Ψ] using hres x hx
    · simpa [Ψ, hrt'] using (hψ₀ r hr).2 x hx
  obtain ⟨app, h1, h2, h3, h4⟩ := cp_exists_app_of_reps hβ (rep := rep) (fun t _ => hrep t)
    (fun t₁ _ t₂ _ hc => hconst t₁ t₂ hc) hΨ hΨres
  refine ⟨⟨app, h1, h2, h3⟩, fun x hx => ?_⟩
  simpa [Ψ] using h4 t ht hrt x hx

theorem Fam.typed (h : F5Std a z) (h' : F5Std a' z') {b : G} (hb : IsConj a b) {β : G → G'}
    (hb' : IsConj a' (β b)) (hβ : IsIsoOn (Gx b) (Gx (β b)) β) (F : Fam b β) {t : G}
    (ht : t ∈ InvIn (Gx b)) {x : G} (hx : x ∈ Gx t) (hxA : IsConj a x) :
    IsConj a' (F.app t x) :=
  cp_typed_of_iso h h' hb hb' hβ ht (F.iso t ht) (F.restrict t ht) hx hxA

theorem Fam.conj_vals {b : G} {β : G → G'} (F : Fam b β) {x t₁ t₂ : G}
    (ht₁ : t₁ ∈ InvIn (Gxy b x)) (ht₂ : t₂ ∈ InvIn (Gxy b x)) (hc : ConjIn (Gxy b x) t₂ t₁) :
    ∃ g ∈ Gxy b x, F.app t₁ x = β g * F.app t₂ x * (β g)⁻¹ := by
  obtain ⟨k, hk, rfl⟩ := hc
  have hk' := mem_Gxy.1 hk
  have ht₂b : t₂ ∈ InvIn (Gx b) := ⟨(mem_Gxy.1 ht₂.1).1, ht₂.2⟩
  have hxt₂ : x ∈ Gx t₂ := mem_Gx.2 (mem_Gx.1 (mem_Gxy.1 ht₂.1).2).symm
  have hkx : k * x * k⁻¹ = x := by
    rw [← mem_Gx.1 hk'.2, mul_assoc, mul_inv_cancel, mul_one]
  have := F.equivariant t₂ ht₂b k hk'.1 x hxt₂
  rw [hkx] at this
  exact ⟨k, hk, this⟩

theorem Fam.conj_vals_eq {b : G} {β : G → G'} (F : Fam b β) {x t₁ t₂ : G}
    (ht₁ : t₁ ∈ InvIn (Gxy b x)) (ht₂ : t₂ ∈ InvIn (Gxy b x)) (hc : ConjIn (Gxy b x) t₂ t₁)
    (hle : ∀ g ∈ Gxy b x, β g ∈ Gx (F.app t₂ x)) : F.app t₁ x = F.app t₂ x := by
  obtain ⟨g, hg, h⟩ := F.conj_vals ht₁ ht₂ hc
  rw [h, ← mem_Gx.1 (hle g hg), mul_assoc, mul_inv_cancel, mul_one]

open Classical in
@[expose] noncomputable def Fam.twist {b : G} {β : G → G'} (F : Fam b β) (S : Set G)
    (hS : ∀ g ∈ Gx b, ∀ t ∈ S, g * t * g⁻¹ ∈ S) : Fam b β where
  app t x := if t ∈ S then F.app t (b * x * b⁻¹) else F.app t x
  iso := by
    intro t ht
    by_cases htS : t ∈ S
    · have hbt : b ∈ Gx t := mem_Gx.2 (mem_Gx.1 ht.1).symm
      have h1 := (isIsoOn_conj (K := Gx t) hbt).comp (F.iso t ht)
      exact h1.congr (fun x _ => by simp [htS])
    · have h1 := F.iso t ht
      exact h1.congr (fun x _ => by simp [htS])
  restrict := by
    intro t ht x hx
    have hxb : b * x = x * b := mem_Gx.1 (mem_Gxy.1 hx).1
    by_cases htS : t ∈ S
    · have e : b * x * b⁻¹ = x := by rw [hxb, mul_assoc, mul_inv_cancel, mul_one]
      simp only [htS, if_true, e]
      exact F.restrict t ht x hx
    · simp only [htS, if_false]
      exact F.restrict t ht x hx
  equivariant := by
    intro t ht g hg x hx
    have hS' : g * t * g⁻¹ ∈ S ↔ t ∈ S := by
      constructor
      · intro h1
        have h2 := hS g⁻¹ ((Gx b).inv_mem hg) _ h1
        have e : g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t := by group
        rwa [e] at h2
      · exact hS g hg t
    by_cases htS : t ∈ S
    · have hbt : b ∈ Gx t := mem_Gx.2 (mem_Gx.1 ht.1).symm
      have hx' : b * x * b⁻¹ ∈ Gx t :=
        (Gx t).mul_mem ((Gx t).mul_mem hbt hx) ((Gx t).inv_mem hbt)
      have e : b * (g * x * g⁻¹) * b⁻¹ = g * (b * x * b⁻¹) * g⁻¹ :=
        calc b * (g * x * g⁻¹) * b⁻¹ = (b * g) * x * (b * g)⁻¹ := by group
          _ = (g * b) * x * (g * b)⁻¹ := by rw [mem_Gx.1 hg]
          _ = g * (b * x * b⁻¹) * g⁻¹ := by group
      simp only [htS, hS'.2 htS, if_true, e]
      exact F.equivariant t ht g hg (b * x * b⁻¹) hx'
    · have hS'' : g * t * g⁻¹ ∉ S := fun h1 => htS (hS'.1 h1)
      simp only [htS, hS'', if_false]
      exact F.equivariant t ht g hg x hx

theorem Fam.twist_app_of_mem {b : G} {β : G → G'} (F : Fam b β) {S : Set G}
    (hS : ∀ g ∈ Gx b, ∀ t ∈ S, g * t * g⁻¹ ∈ S) {t : G} (ht : t ∈ S) (x : G) :
    (F.twist S hS).app t x = F.app t (b * x * b⁻¹) := by
  simp [Fam.twist, ht]

theorem Fam.twist_app_of_not_mem {b : G} {β : G → G'} (F : Fam b β) {S : Set G}
    (hS : ∀ g ∈ Gx b, ∀ t ∈ S, g * t * g⁻¹ ∈ S) {t : G} (ht : t ∉ S) (x : G) :
    (F.twist S hS).app t x = F.app t x := by
  simp [Fam.twist, ht]

end CFSG.EvenSporadicStandard.HNRecog.Section4

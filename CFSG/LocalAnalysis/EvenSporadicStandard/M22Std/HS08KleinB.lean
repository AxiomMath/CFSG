module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08KleinA
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08Main3

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] {L : Subgroup G} {t : G}

theorem index_two_mul_mem {H : Subgroup G} (hrel : L.relIndex H = 2) {a b : G} (ha : a ∈ H)
    (hb : b ∈ H) (haL : a ∉ L) (hbL : b ∉ L) : a * b ∈ L := by
  have := (Subgroup.mul_mem_iff_of_index_two (H := L.subgroupOf H) hrel (a := ⟨a, ha⟩)
    (b := ⟨b, hb⟩)).2 (iff_of_false (by rwa [Subgroup.mem_subgroupOf])
      (by rwa [Subgroup.mem_subgroupOf]))
  rwa [Subgroup.mem_subgroupOf] at this

theorem sq_mul_of_comm {c l : G} (hc2 : c * c = 1) (hcl : c * l = l * c) :
    (c * l) * (c * l) = l * l := by
  calc c * l * (c * l) = c * (l * c) * l := by group
    _ = c * (c * l) * l := by rw [← hcl]
    _ = (c * c) * (l * l) := by group
    _ = l * l := by rw [hc2, one_mul]

theorem hs08_isolated_klein
    [Finite G]
    [Group.IsPerfect L] (htL : t ∈ L) (hcov : IsM22Cover ↥L ⟨t, htL⟩)
    (hrel : L.relIndex (centralizer ({t} : Set G)) = 2) {c : G}
    (hcC : c ∈ centralizer (L : Set G)) (hcL : c ∉ L) (hc2 : c * c = 1) :
    ∀ g : G, g * t * g⁻¹ ∈ centralizer ({t} : Set G) → g * t * g⁻¹ = t := by
  obtain ⟨F⟩ := hcov.nonempty_twFacts
  have ht2 : t * t = 1 := by simpa using congrArg Subtype.val hcov.mul_self_t
  have hLH : L ≤ centralizer ({t} : Set G) := fun l hl =>
    mem_centralizer_singleton_iff.2 (congrArg Subtype.val (hcov.t_central ⟨l, hl⟩)).symm
  have hcH : c ∈ centralizer ({t} : Set G) :=
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hcC t htL).symm
  have hcP : ∀ x ∈ (F.S0.comap F.φ).map L.subtype, c * x = x * c := by
    rintro _ ⟨l, -, rfl⟩
    exact (mem_centralizer_iff.1 hcC (l : G) l.2).symm
  have hsqP : SqData t ((F.S0.comap F.φ).map L.subtype) ((F.w₁ * F.w₁ : ↥L) : G)
      ((F.w₂ * F.w₂ : ↥L) : G) := F.sqData.map L.subtype L.subtype_injective
  set T : Subgroup G := cExt ((F.S0.comap F.φ).map L.subtype) c hc2 hcP with hT
  have hsqT : SqData t T ((F.w₁ * F.w₁ : ↥L) : G) ((F.w₂ * F.w₂ : ↥L) : G) := hsqP.cExt
  have hPT : (F.S0.comap F.φ).map L.subtype ≤ T := le_cExt
  have hcT : c ∈ T := c_mem_cExt
  have hTH : T ≤ centralizer ({t} : Set G) := by
    rintro x (⟨l, -, rfl⟩ | ⟨y, ⟨l, -, rfl⟩, rfl⟩)
    · exact hLH l.2
    · exact (centralizer ({t} : Set G)).mul_mem (hLH l.2) hcH
  have hTp : IsPGroup 2 T := isPGroup_cExt ((F.isPGroup_comap hcov).map L.subtype)
  have hmem : ∀ P₂ : Subgroup G, IsPGroup 2 P₂ → T ≤ P₂ → ∀ x : ↥L, (x : G) ∈ P₂ →
      F.φ x ∈ F.S0 := fun P₂ hP₂ hTP₂ x hx =>
    F.mem_of_isPGroup (hP₂.comap_of_injective L.subtype L.subtype_injective)
      (fun l hl => (hPT.trans hTP₂) ⟨l, hl, rfl⟩) hx
  have hTmax : ∀ P₂ : Subgroup G, P₂ ≤ centralizer ({t} : Set G) → IsPGroup 2 P₂ → T ≤ P₂ →
      P₂ = T := by
    intro P₂ hP₂H hP₂p hTP₂
    refine le_antisymm (fun x hx => ?_) hTP₂
    by_cases hxL : x ∈ L
    · exact hPT ⟨⟨x, hxL⟩, hmem P₂ hP₂p hTP₂ ⟨x, hxL⟩ hx, rfl⟩
    · have hcxL : c * x ∈ L := index_two_mul_mem hrel hcH (hP₂H hx) hcL hxL
      have hcxP₂ : c * x ∈ P₂ := P₂.mul_mem (hTP₂ hcT) hx
      have hcxP : c * x ∈ (F.S0.comap F.φ).map L.subtype :=
        ⟨⟨c * x, hcxL⟩, hmem P₂ hP₂p hTP₂ ⟨c * x, hcxL⟩ hcxP₂, rfl⟩
      refine Or.inr ⟨c * x, hcxP, ?_⟩
      calc x = c * (c * x) := by rw [← mul_assoc, hc2, one_mul]
        _ = (c * x) * c := hcP _ hcxP
  have hL_inv : ∀ l : ↥L, l * l = 1 → ∃ h : ↥L, h * l * h⁻¹ = 1 ∨
      h * l * h⁻¹ = ⟨t, htL⟩ ∨ h * l * h⁻¹ = F.w₁ * F.w₁ ∨ h * l * h⁻¹ = F.w₂ * F.w₂ := by
    intro l hl2
    by_cases hl1 : l = 1
    · exact ⟨1, Or.inl (by simp [hl1])⟩
    by_cases hlt : l = ⟨t, htL⟩
    · exact ⟨1, Or.inr (Or.inl (by simp [hlt]))⟩
    have hφ : F.φ l ≠ 1 := by
      intro h1
      rcases (F.ker_iff l).1 h1 with h2 | h2
      · exact hl1 h2
      · exact hlt h2
    obtain ⟨c', hc'⟩ := F.conj l hl2 hφ
    refine ⟨c'⁻¹, Or.inr (Or.inr ?_)⟩
    rcases hc' with h | h
    · left; rw [h]; group
    · right; rw [h]; group
  have hcentT : ∀ w : G, (w = 1 ∨ w = t ∨ w = ((F.w₁ * F.w₁ : ↥L) : G) ∨
      w = ((F.w₂ * F.w₂ : ↥L) : G)) → ∀ x ∈ T, w * x = x * w := by
    rintro w (rfl | rfl | rfl | rfl) x hx
    · simp
    · exact hsqT.t_central x hx
    · exact hsqT.z_central x hx
    · exact hsqT.z'_central x hx
  have hLw : ∀ l : ↥L, ∀ h : ↥L, (h * l * h⁻¹ = 1 ∨ h * l * h⁻¹ = ⟨t, htL⟩ ∨
      h * l * h⁻¹ = F.w₁ * F.w₁ ∨ h * l * h⁻¹ = F.w₂ * F.w₂) →
      (((h * l * h⁻¹ : ↥L) : G) = 1 ∨ ((h * l * h⁻¹ : ↥L) : G) = t ∨
        ((h * l * h⁻¹ : ↥L) : G) = ((F.w₁ * F.w₁ : ↥L) : G) ∨
        ((h * l * h⁻¹ : ↥L) : G) = ((F.w₂ * F.w₂ : ↥L) : G)) := by
    rintro l h (h1 | h1 | h1 | h1)
    · exact Or.inl (congrArg Subtype.val h1)
    · exact Or.inr (Or.inl (congrArg Subtype.val h1))
    · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h1)))
    · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h1)))
  have hkey : ∀ s : G, s ∈ centralizer ({t} : Set G) → s * s = 1 →
      ∃ h ∈ L, ∃ w : G, (∀ x ∈ T, w * x = x * w) ∧ h * s * h⁻¹ = w := by
    intro s hsH hs2
    by_cases hsL : s ∈ L
    · obtain ⟨h, hh⟩ := hL_inv ⟨s, hsL⟩ (Subtype.ext hs2)
      exact ⟨h, h.2, ((h * ⟨s, hsL⟩ * h⁻¹ : ↥L) : G), hcentT _ (hLw _ _ hh), rfl⟩
    · have hcsL : c * s ∈ L := index_two_mul_mem hrel hcH hsH hcL hsL
      have hcl : c * (c * s) = (c * s) * c := (mem_centralizer_iff.1 hcC (c * s) hcsL).symm
      have hs_eq : s = c * (c * s) := by rw [← mul_assoc, hc2, one_mul]
      have hl2 : (c * s) * (c * s) = 1 := by
        have h1 := sq_mul_of_comm hc2 hcl
        rw [← hs_eq, hs2] at h1
        exact h1.symm
      obtain ⟨h, hh⟩ := hL_inv ⟨c * s, hcsL⟩ (Subtype.ext hl2)
      have hch : c * (h : G) = h * c := (mem_centralizer_iff.1 hcC (h : G) h.2).symm
      refine ⟨h, h.2, c * ((h * ⟨c * s, hcsL⟩ * h⁻¹ : ↥L) : G),
        central_mul (fun x hx => c_central_cExt x hx) (hcentT _ (hLw _ _ hh)), ?_⟩
      show (h : G) * s * (h : G)⁻¹ = c * ((h : G) * (c * s) * (h : G)⁻¹)
      calc (h : G) * s * (h : G)⁻¹ = (h : G) * (c * (c * s)) * (h : G)⁻¹ := by rw [← hs_eq]
        _ = ((h : G) * c) * (c * s) * (h : G)⁻¹ := by simp only [mul_assoc]
        _ = (c * (h : G)) * (c * s) * (h : G)⁻¹ := by rw [← hch]
        _ = c * ((h : G) * (c * s) * (h : G)⁻¹) := by group
  intro g hg
  have hs2 : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
    calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  obtain ⟨h, hhL, w, hw, hhw⟩ := hkey _ hg hs2
  obtain ⟨P_G, hP_G⟩ := hsqT.exists_sylow hTp hTH hTmax
  have h1 := hsqT.eq_of_conj P_G hP_G (g := h * g) (fun x hx => by
    have e : (h * g) * t * (h * g)⁻¹ = w := by rw [← hhw]; group
    rw [e]
    exact hw x hx)
  have hht : h * t = t * h := mem_centralizer_singleton_iff.1 (hLH hhL)
  have h2 : (h * g) * t * (h * g)⁻¹ = h * (g * t * g⁻¹) * h⁻¹ := by group
  rw [h2] at h1
  calc g * t * g⁻¹ = h⁻¹ * (h * (g * t * g⁻¹) * h⁻¹) * h := by group
    _ = h⁻¹ * t * h := by rw [h1]
    _ = t := by rw [mul_assoc, ← hht]; group

end CFSG.EvenSporadicStandard.M22Std

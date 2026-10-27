module

public import CFSG.ClassicalInvolution.Generic.Frame

public section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G]

theorem isUniqueInvolution_central {L : Subgroup G} {z : G} (h : IsUniqueInvolution L z) {r : G}
    (hr : r ∈ L) : z * r = r * z := by
  have hy : r * z * r⁻¹ ∈ L := L.mul_mem (L.mul_mem hr h.mem) (L.inv_mem hr)
  have hy2 : (r * z * r⁻¹) * (r * z * r⁻¹) = 1 := by
    calc r * z * r⁻¹ * (r * z * r⁻¹) = r * (z * z) * r⁻¹ := by group
      _ = 1 := by rw [h.sq]; group
  rcases h.unique _ hy hy2 with h1 | h1
  · exact absurd (by simpa using h1) h.ne_one
  · calc z * r = r * z * r⁻¹ * r := by rw [h1]
      _ = r * z := by group

theorem isUniqueInvolution_comap {H : Type} [Group H] {ψ : H →* G}
    (hinj : Function.Injective ψ) {R : Subgroup H} {z : G}
    (hz : IsUniqueInvolution (R.map ψ) z) : ∃ c : H, ψ c = z ∧ IsUniqueInvolution R c := by
  obtain ⟨c, hcR, hcz⟩ := hz.mem
  refine ⟨c, hcz, ⟨hcR, fun h => hz.ne_one ?_, hinj ?_, fun y hy hy2 => ?_⟩⟩
  · rw [← hcz, h, map_one]
  · rw [map_mul, map_one, hcz]
    exact hz.sq
  · have h1 : ψ y * ψ y = 1 := by rw [← map_mul, hy2, map_one]
    rcases hz.unique (ψ y) ⟨y, hy, rfl⟩ h1 with h | h
    · exact Or.inl (hinj (by rw [h, map_one]))
    · exact Or.inr (hinj (by rw [h, hcz]))

@[expose] def conjStabilizer (S : Set (Subgroup G)) : Subgroup G where
  carrier := {g | ∀ J : Subgroup G, conjSub g J ∈ S ↔ J ∈ S}
  one_mem' := fun J => by simp
  mul_mem' := fun {a b} ha hb J => by rw [conjSub_mul, ha, hb]
  inv_mem' := fun {a} ha J => by
    rw [← ha (conjSub a⁻¹ J), conjSub_conjSub_inv]

theorem mem_conjStabilizer_iff {S : Set (Subgroup G)} {g : G} :
    g ∈ conjStabilizer S ↔ ∀ J : Subgroup G, conjSub g J ∈ S ↔ J ∈ S := Iff.rfl

theorem normalizer_iff_conjSub_eq {n : G} {K : Subgroup G} :
    n ∈ Subgroup.normalizer (K : Set G) ↔ conjSub n K = K := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h
    ext x
    rw [mem_conjSub_iff]
    have := h (n⁻¹ * x * n)
    rw [show n * (n⁻¹ * x * n) * n⁻¹ = x by group] at this
    exact this
  · intro h x
    have h1 : n * x * n⁻¹ ∈ conjSub n K ↔ x ∈ K := by
      rw [mem_conjSub_iff, show n⁻¹ * (n * x * n⁻¹) * n = x by group]
    rw [h] at h1
    exact h1.symm

theorem edgeless_or_connected_of_coatom {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω)
    (htrans : ∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J)
    (hcoatom : ∀ K ∈ Ω, IsCoatom (Subgroup.normalizer (K : Set G)))
    {r : Subgroup G → Subgroup G → Prop}
    (hr : ∀ (g : G) (K J : Subgroup G), r K J → r (conjSub g K) (conjSub g J))
    (hsymm : ∀ K J : Subgroup G, r K J → r J K) (hirr : ∀ K J : Subgroup G, r K J → K ≠ J) :
    (∀ K ∈ Ω, ∀ J ∈ Ω, ¬ r K J) ∨
      ∀ K ∈ Ω, ∀ J ∈ Ω, Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ r M N) K J := by
  by_cases hedge : ∃ K₀ ∈ Ω, ∃ J₀ ∈ Ω, r K₀ J₀
  · right
    obtain ⟨K₀, hK₀, J₀, hJ₀, hrJ⟩ := hedge
    set R : Subgroup G → Subgroup G → Prop := fun M N => N ∈ Ω ∧ r M N with hR
    set S : Set (Subgroup G) := {J | Relation.ReflTransGen R K₀ J} with hS
    have path_conj : ∀ (g : G) {A B : Subgroup G}, Relation.ReflTransGen R A B →
        Relation.ReflTransGen R (conjSub g A) (conjSub g B) := by
      intro g A B h
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hbc ih => exact ih.tail ⟨hΩ g _ hbc.1, hr g _ _ hbc.2⟩
    have path_rev : ∀ {A B : Subgroup G}, A ∈ Ω → Relation.ReflTransGen R A B →
        B ∈ Ω ∧ Relation.ReflTransGen R B A := by
      intro A B hA h
      induction h with
      | refl => exact ⟨hA, Relation.ReflTransGen.refl⟩
      | tail _ hbc ih =>
        exact ⟨hbc.1, Relation.ReflTransGen.head ⟨ih.1, hsymm _ _ hbc.2⟩ ih.2⟩
    have hSΩ : ∀ J ∈ S, J ∈ Ω := fun J hJ => (path_rev hK₀ hJ).1
    have mapS : ∀ g : G, conjSub g K₀ ∈ S → ∀ J ∈ S, conjSub g J ∈ S :=
      fun g hg J hJ => hg.trans (path_conj g hJ)
    have mem_stab : ∀ g : G, conjSub g K₀ ∈ S → conjSub g⁻¹ K₀ ∈ S → g ∈ conjStabilizer S := by
      intro g hg hg' J
      refine ⟨fun h => ?_, fun h => mapS g hg J h⟩
      have := mapS g⁻¹ hg' _ h
      rwa [conjSub_inv_conjSub] at this
    have hK₀S : K₀ ∈ S := Relation.ReflTransGen.refl
    have hN : Subgroup.normalizer (K₀ : Set G) ≤ conjStabilizer S := by
      intro n hn
      have h1 : conjSub n K₀ = K₀ := normalizer_iff_conjSub_eq.mp hn
      have h2 : conjSub n⁻¹ K₀ = K₀ := normalizer_iff_conjSub_eq.mp (Subgroup.inv_mem _ hn)
      exact mem_stab n (by rw [h1]; exact hK₀S) (by rw [h2]; exact hK₀S)
    rcases (hcoatom K₀ hK₀).le_iff.mp hN with htop | hnorm
    · have hall : ∀ J ∈ Ω, J ∈ S := by
        intro J hJ
        obtain ⟨g, hg⟩ := htrans K₀ hK₀ J hJ
        have hgS : g ∈ conjStabilizer S := by rw [htop]; exact Subgroup.mem_top g
        rw [← hg]
        exact (hgS K₀).mpr hK₀S
      intro K hK J hJ
      exact (path_rev hK₀ (hall K hK)).2.trans (hall J hJ)
    · exfalso
      have hJ₀S : J₀ ∈ S := Relation.ReflTransGen.single ⟨hJ₀, hrJ⟩
      obtain ⟨g, hg⟩ := htrans K₀ hK₀ J₀ hJ₀
      have hg1 : conjSub g K₀ ∈ S := hg ▸ hJ₀S
      have hg2 : conjSub g⁻¹ K₀ ∈ S := by
        have h1 := path_conj g⁻¹ (path_rev hK₀ hJ₀S).2
        rw [← hg, conjSub_inv_conjSub] at h1
        exact h1
      have hgs : g ∈ conjStabilizer S := mem_stab g hg1 hg2
      rw [hnorm] at hgs
      have h3 : conjSub g K₀ = K₀ := normalizer_iff_conjSub_eq.mp hgs
      exact hirr K₀ J₀ hrJ (h3.symm.trans hg)
  · left
    push Not at hedge
    exact fun K hK J hJ h => hedge K hK J hJ h

end CFSG.ClassicalInvolution.G2D4Models

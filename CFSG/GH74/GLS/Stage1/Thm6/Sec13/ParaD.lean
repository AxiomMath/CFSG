module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.ParaB
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Statements

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem cj_eq_map (m : G) (P : Subgroup G) : cj m P = P.map (MulAut.conj m).toMonoidHom := rfl

theorem Hzero_cj (m : G) (H : Subgroup G) (f : G) :
    Hzero (cj m H) (m * f * m⁻¹) = cj m (Hzero H f) := by
  unfold Hzero
  rw [cj_eq_map, cj_eq_map, Subgroup.map_commutator, MonoidHom.map_zpowers]
  rfl

theorem cj_sup (m : G) (P Q : Subgroup G) : cj m (P ⊔ Q) = cj m P ⊔ cj m Q :=
  Subgroup.map_sup _ _ _

theorem zpowers_cj {m x : G} (hmx : m * x * m⁻¹ = x) : cj m (zpowers x) = zpowers x := by
  rw [cj_eq_map, MonoidHom.map_zpowers]
  show zpowers (m * x * m⁻¹) = zpowers x
  rw [hmx]

theorem h0Type_cj {H₀ : Subgroup G} (h : H0Type H₀) (m : G) : H0Type (cj m H₀) := by
  have e : ↥(cj m H₀) ≃* ↥H₀ :=
    (Subgroup.equivMapOfInjective H₀ (MulAut.conj m).toMonoidHom (MulAut.conj m).injective).symm
  rcases h with h1 | ⟨n, hn, h2⟩ | h3 | h4
  · exact Or.inl (h1.map e.trans)
  · exact Or.inr (Or.inl ⟨n, hn, h2.map e.trans⟩)
  · exact Or.inr (Or.inr (Or.inl (h3.map e.trans)))
  · exact Or.inr (Or.inr (Or.inr (h4.map e.trans)))

namespace Lemma13_1Conc

theorem conj [Finite G] {x : G} {V H : Subgroup G} {f : G} (hc : Lemma13_1Conc x V H f) {m : G}
    (hmN : m ∈ normalizer (V : Set G)) (hmx : m * x * m⁻¹ = x) :
    Lemma13_1Conc x V (cj m H) (m * f * m⁻¹) := by
  have hmC : ∀ m' ∈ normalizer (V : Set G), ∀ n ∈ centralizer (V : Set G),
      m' * n * m'⁻¹ ∈ centralizer (V : Set G) := fun _ hm _ hn => conj_mem_cent hm hn
  have hmN' : m⁻¹ ∈ normalizer (V : Set G) := (normalizer (V : Set G)).inv_mem hmN
  have hf'N : m * f * m⁻¹ ∈ normalizer (V : Set G) :=
    (normalizer (V : Set G)).mul_mem ((normalizer (V : Set G)).mul_mem hmN hc.f_mem) hmN'
  have hHz := Hzero_cj m H f
  have hzx := zpowers_cj hmx
  refine ⟨sylowIn_cj (p := 2) hc.sylow hmC hmN, ?_, hf'N, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hc.f3
    refine ⟨k, ?_⟩
    rw [conj_pow, hk]
    group
  · intro hfc
    apply hc.f_not
    have := conj_mem_cent hmN' hfc
    have e : m⁻¹ * (m * f * m⁻¹) * m⁻¹⁻¹ = f := by group
    rwa [e] at this
  · rw [mem_normalizer_iff]
    intro g
    have hfH : ∀ u, u ∈ H ↔ f * u * f⁻¹ ∈ H := fun u => mem_normalizer_iff.1 hc.a_norm u
    rw [mem_cj, mem_cj]
    have e : m⁻¹ * (m * f * m⁻¹ * g * (m * f * m⁻¹)⁻¹) * m = f * (m⁻¹ * g * m) * f⁻¹ := by group
    rw [e]
    exact hfH _
  · ext g
    constructor
    · rintro ⟨hg1, hg2⟩
      have hg1' : m⁻¹ * g * m ∈ H := mem_cj.1 hg1
      have hg2' : m⁻¹ * g * m ∈ centralizer ({f} : Set G) := by
        rw [mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        have := mem_centralizer_iff.1 hg2 (m * f * m⁻¹) rfl
        calc f * (m⁻¹ * g * m) = m⁻¹ * ((m * f * m⁻¹) * g) * m := by group
          _ = m⁻¹ * (g * (m * f * m⁻¹)) * m := by rw [this]
          _ = (m⁻¹ * g * m) * f := by group
      have : m⁻¹ * g * m ∈ zpowers x := by
        rw [← hc.a_cent]; exact ⟨hg1', hg2'⟩
      rw [← hzx]
      exact mem_cj.2 this
    · intro hg
      rw [← hzx] at hg
      have hg' : m⁻¹ * g * m ∈ zpowers x := mem_cj.1 hg
      rw [← hc.a_cent] at hg'
      refine ⟨mem_cj.2 hg'.1, ?_⟩
      show g ∈ centralizer ({m * f * m⁻¹} : Set G)
      rw [mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have := mem_centralizer_iff.1 hg'.2 f rfl
      calc (m * f * m⁻¹) * g = m * (f * (m⁻¹ * g * m)) * m⁻¹ := by group
        _ = m * ((m⁻¹ * g * m) * f) * m⁻¹ := by rw [this]
        _ = g * (m * f * m⁻¹) := by group
  · rw [hHz, ← hzx, ← cj_sup, ← hc.b_eq]
  · rw [hHz]
    intro hxm
    apply hc.b_not
    have := mem_cj.1 hxm
    have e : m⁻¹ * x * m = x := by
      calc m⁻¹ * x * m = m⁻¹ * (m * x * m⁻¹) * m := by rw [hmx]
        _ = x := by group
    rwa [e] at this
  · rw [hHz]
    exact h0Type_cj hc.c_type m

end Lemma13_1Conc

end CFSG.GH74.GLS.Stage1.Thm6.Sec13

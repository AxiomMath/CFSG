module

public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics

public section

namespace CFSG.HardMathSupport.Timmesfeld.Proving

open CFSG.Open

variable {G : Type*} [Group G]

theorem GLAPPrimeCoreOf_conj_mem_of_mem_normalizer {p : ℕ} [Finite G] (hp : p.Prime)
    {C : Subgroup G} {y : G} (hy : y ∈ Subgroup.normalizer (C : Set G)) :
    ∀ x ∈ GLAPPrimeCoreOf p C, y * x * y⁻¹ ∈ GLAPPrimeCoreOf p C := by
  intro x hx
  have hyC : ∀ c ∈ C, y * c * y⁻¹ ∈ C := fun c hc => (Subgroup.mem_normalizer_iff.1 hy c).1 hc
  have hy'C : ∀ c ∈ C, y⁻¹ * c * y ∈ C := fun c hc => by
    have h := (Subgroup.mem_normalizer_iff.1 (inv_mem hy) c).1 hc
    simpa using h
  have hS : (GLAPPrimeCoreOf p C).map (MulAut.conj y).toMonoidHom ≤ GLAPPrimeCoreOf p C := by
    refine le_GLAPPrimeCoreOf_of_normal ?_ ?_ ?_
    · intro w hw
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hw
      exact hyC z (GLAPPrimeCoreOf_le C hz)
    · intro g hg t ht
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 ht
      have hconj := GLAPPrimeCoreOf_conj_mem (y⁻¹ * g * y) (hy'C g hg) z hz
      rw [show g * (MulAut.conj y).toMonoidHom z * g⁻¹ =
          (MulAut.conj y).toMonoidHom ((y⁻¹ * g * y) * z * (y⁻¹ * g * y)⁻¹) by
        simp [MulAut.conj_apply]; group]
      exact Subgroup.mem_map.2 ⟨_, hconj, rfl⟩
    · rw [Subgroup.card_map_of_injective (f := (MulAut.conj y).toMonoidHom) (MulAut.conj y).injective]
      exact coprime_card_GLAPPrimeCoreOf hp C
  exact hS (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)

theorem conj_mem_centralizer_of_mem_normalizer {A : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (A : Set G)) :
    ∀ c ∈ Subgroup.centralizer (A : Set G), y * c * y⁻¹ ∈ Subgroup.centralizer (A : Set G) := by
  intro c hc
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro a ha
  have ha' : y⁻¹ * a * y ∈ A := by
    have h := (Subgroup.mem_normalizer_iff.1 (inv_mem hy) a).1 ha
    simpa using h
  have hc' := hc (y⁻¹ * a * y) ha'
  have e1 : a * (y * c * y⁻¹) = y * ((y⁻¹ * a * y) * c) * y⁻¹ := by group
  have e2 : (y * c * y⁻¹) * a = y * (c * (y⁻¹ * a * y)) * y⁻¹ := by group
  rw [e1, e2, hc']

theorem mem_normalizer_centralizer_of_mem_normalizer {A : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (A : Set G)) :
    y ∈ Subgroup.normalizer ((Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · exact conj_mem_centralizer_of_mem_normalizer hy c
  · intro hc
    have h := conj_mem_centralizer_of_mem_normalizer (inv_mem hy) _ hc
    have e : y⁻¹ * (y * c * y⁻¹) * y⁻¹⁻¹ = c := by group
    rw [e] at h
    exact h

theorem centralizes_of_isCoatom {P A : Subgroup G}
    (hcoat : IsCoatom (A.subgroupOf P)) {n : G} (hnP : n ∈ P) (hnA : n ∉ A) {s : G}
    (hsA : ∀ a ∈ A, a * s = s * a) (hns : n * s = s * n) :
    ∀ x ∈ P, x * s = s * x := by
  have hlt : A.subgroupOf P < A.subgroupOf P ⊔ Subgroup.zpowers (⟨n, hnP⟩ : P) := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro h
    apply hnA
    have hm' : (⟨n, hnP⟩ : P) ∈ A.subgroupOf P := by
      rw [h]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    exact Subgroup.mem_subgroupOf.1 hm'
  have hTop := hcoat.2 _ hlt
  have hA'H : A.subgroupOf P ≤ (Subgroup.centralizer ({s} : Set G)).subgroupOf P := by
    intro a ha
    exact Subgroup.mem_subgroupOf.2
      (Subgroup.mem_centralizer_singleton_iff.2 (hsA _ (Subgroup.mem_subgroupOf.1 ha)))
  have hmH : (⟨n, hnP⟩ : P) ∈ (Subgroup.centralizer ({s} : Set G)).subgroupOf P :=
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_centralizer_singleton_iff.2 hns)
  have hle : A.subgroupOf P ⊔ Subgroup.zpowers (⟨n, hnP⟩ : P) ≤
      (Subgroup.centralizer ({s} : Set G)).subgroupOf P :=
    sup_le hA'H (Subgroup.zpowers_le.2 hmH)
  intro x hx
  have hxH : (⟨x, hx⟩ : P) ∈ (Subgroup.centralizer ({s} : Set G)).subgroupOf P :=
    hle (by rw [hTop]; exact Subgroup.mem_top _)
  exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_subgroupOf.1 hxH)

end CFSG.HardMathSupport.Timmesfeld.Proving

end

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Data

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup

theorem LayerZeroInvolution.of_mulEquiv {Y H : Type*} [Group Y] [Group H] (ε : Y ≃* H) {z : Y}
    (h : LayerZeroInvolution H (ε z)) : LayerZeroInvolution Y z := by
  have hc : ∀ x : Y, x ∈ centralizer ({z} : Set Y) ↔ ε x ∈ centralizer ({ε z} : Set H) := by
    intro x
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact ε.injective.eq_iff.symm
  have hψ : ∀ (φ : MulAut Y) (x : Y), (MulAut.congr ε φ) (ε x) = ε (φ x) := by
    intro φ x
    simp [MulAut.congr_apply]
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun φ hφ => ?_, ?_⟩
  · have := h1 (MulAut.congr ε φ) (fun y hy => by
      obtain ⟨x, rfl⟩ := ε.surjective y
      rw [hψ, hφ x ((hc x).2 hy)])
    rw [← map_mul] at this
    exact (map_eq_one_iff _ (MulEquiv.injective _)).1 this
  · rcases h2 with ⟨P, hP, hPP, hzP⟩ | h2
    · refine Or.inl ⟨P.map ε.symm.toMonoidHom, ?_, ?_, ⟨ε z, hzP, by simp⟩⟩
      · rintro _ ⟨p, hp, rfl⟩
        show ε.symm p ∈ centralizer ({z} : Set Y)
        rw [hc]
        simpa using hP hp
      · rw [← Subgroup.map_commutator, hPP]
    · refine Or.inr fun φ hφ => ?_
      have := h2 (MulAut.congr ε φ) (fun y hy hodd => by
        obtain ⟨x, rfl⟩ := ε.surjective y
        rw [hψ, hφ x ((hc x).2 hy) (by rwa [MulEquiv.orderOf_eq] at hodd)])
      rw [← map_mul] at this
      exact (map_eq_one_iff _ (MulEquiv.injective _)).1 this

theorem LayerZeroInvolution.conj {H : Type*} [Group H] {z : H} (h : LayerZeroInvolution H z)
    (g : H) : LayerZeroInvolution H (g * z * g⁻¹) := by
  refine LayerZeroInvolution.of_mulEquiv (MulAut.conj g⁻¹) ?_
  have : (MulAut.conj g⁻¹) (g * z * g⁻¹) = z := by simp; group
  rwa [this]

@[expose] def CentralizerPerfect {G : Type*} [Group G] (S : Subgroup G) : Prop :=
  ∃ z : G, orderOf z = 2 ∧ centralizer (S : Set G) = zpowers z ∧
    ∃ P : Subgroup G, P ≤ centralizer ({z} : Set G) ∧ ⁅P, P⁆ = P ∧ z ∈ P

theorem CentralizerPerfect.map {Y H : Type*} [Group Y] [Group H] (ε : Y ≃* H) {S : Subgroup Y}
    (h : CentralizerPerfect S) : CentralizerPerfect (S.map ε.toMonoidHom) := by
  obtain ⟨z, hz2, hSz, P, hP, hPP, hzP⟩ := h
  have hc : ∀ x : Y, x ∈ centralizer ({z} : Set Y) ↔ ε x ∈ centralizer ({ε z} : Set H) := by
    intro x
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact ε.injective.eq_iff.symm
  refine ⟨ε z, by rwa [MulEquiv.orderOf_eq], ?_, P.map ε.toMonoidHom, ?_, ?_, ⟨z, hzP, rfl⟩⟩
  · ext y
    obtain ⟨x, rfl⟩ := ε.surjective y
    rw [mem_centralizer_iff, mem_zpowers_iff]
    constructor
    · intro hy
      have hx : x ∈ centralizer (S : Set Y) := by
        rw [mem_centralizer_iff]
        intro s hs
        have := hy (ε s) ⟨s, hs, rfl⟩
        rw [← map_mul, ← map_mul] at this
        exact ε.injective this
      rw [hSz, mem_zpowers_iff] at hx
      obtain ⟨k, rfl⟩ := hx
      exact ⟨k, by simp⟩
    · rintro ⟨k, hk⟩ _ ⟨s, hs, rfl⟩
      have hx : x = z ^ k := ε.injective (by simpa using hk.symm)
      have hx' : x ∈ centralizer (S : Set Y) := by
        rw [hSz, hx]
        exact zpow_mem_zpowers z k
      rw [mem_centralizer_iff] at hx'
      show ε s * ε x = ε x * ε s
      rw [← map_mul, ← map_mul, hx' s hs]
  · rintro _ ⟨p, hp, rfl⟩
    show ε p ∈ centralizer ({ε z} : Set H)
    rw [← hc]
    exact hP hp
  · rw [← Subgroup.map_commutator, hPP]

theorem CentralizerPerfect.of_map {Y H : Type*} [Group Y] [Group H] (ε : Y ≃* H)
    {S : Subgroup Y} (h : CentralizerPerfect (S.map ε.toMonoidHom)) : CentralizerPerfect S := by
  have := h.map ε.symm
  rwa [Subgroup.map_map, show ε.symm.toMonoidHom.comp ε.toMonoidHom = MonoidHom.id Y from ?_,
    Subgroup.map_id] at this
  ext
  simp

theorem CentralizerPerfect.of_sylow {Y H : Type*} [Group Y] [Group H] [Finite Y] (ε : Y ≃* H)
    (T : Sylow 2 H) (hT : CentralizerPerfect (T : Subgroup H)) (R : Sylow 2 Y) :
    CentralizerPerfect (R : Subgroup Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite H := Finite.of_equiv Y ε
  let S : Sylow 2 H := R.mapSurjective (f := ε.toMonoidHom) ε.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H T S
  have hS : (S : Subgroup H) = (T : Subgroup H).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    rfl
  apply CentralizerPerfect.of_map ε
  have h2 : (S : Subgroup H) = (R : Subgroup Y).map ε.toMonoidHom := rfl
  rw [← h2, hS]
  exact hT.map (MulAut.conj g)

end CFSG.EvenSporadicStandard.HSStd

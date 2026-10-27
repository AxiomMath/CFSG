module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S

open Subgroup

variable {G : Type*} [Group G]

theorem relIndex_sup_sup_of_inf_eq_bot [Finite G] {D F₁ F₂ : Subgroup G} [D.Normal]
    (h : F₁ ≤ F₂) (hF : F₂ ⊓ D = ⊥) :
    (D ⊔ F₁).relIndex (D ⊔ F₂) = F₁.relIndex F₂ := by
  have key : ∀ F : Subgroup G, F ⊓ D = ⊥ → D.relIndex (D ⊔ F) = Nat.card F := by
    intro F hF'
    rw [relIndex_sup_left, ← inf_relIndex_right, inf_comm, hF', relIndex_bot_left]
  have h1 := key F₂ hF
  have h2 := key F₁ (eq_bot_iff.2 ((inf_le_inf_right D h).trans hF.le))
  have h3 := relIndex_mul_relIndex D (D ⊔ F₁) (D ⊔ F₂) le_sup_left (sup_le_sup_left h D)
  rw [h1, h2] at h3
  have h4 := relIndex_mul_card F₁ F₂
  rw [inf_eq_left.2 h] at h4
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h3.trans (h4.symm.trans (mul_comm _ _)))

theorem relIndex_sup_sup_of_le [Finite G] {N D F : Subgroup G} [N.Normal] [D.Normal]
    (hND : N ≤ D) (hF : F ⊓ D = ⊥) :
    (N ⊔ F).relIndex (D ⊔ F) = N.relIndex D := by
  have key : ∀ M : Subgroup G, [M.Normal] → F ⊓ M = ⊥ → M.relIndex (M ⊔ F) = Nat.card F := by
    intro M _ hF'
    rw [relIndex_sup_left, ← inf_relIndex_right, inf_comm, hF', relIndex_bot_left]
  have hFN : F ⊓ N = ⊥ := eq_bot_iff.2 ((inf_le_inf_left F hND).trans hF.le)
  have h1 := key D hF
  have h2 := key N hFN
  have h3 := relIndex_mul_relIndex N (N ⊔ F) (D ⊔ F) le_sup_left (sup_le_sup_right hND F)
  have h4 := relIndex_mul_relIndex N D (D ⊔ F) hND le_sup_left
  rw [h2] at h3
  rw [h1] at h4
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h3.trans (h4.symm.trans (mul_comm _ _)))

theorem exists_complement_in_sylow [Finite G] {p : ℕ} [Fact p.Prime] (N : Subgroup G) [N.Normal]
    (R : Subgroup G) (hRp : IsPGroup p R) (hRN : R ⊓ N = ⊥) (hidx : ¬ p ∣ (N ⊔ R).index)
    (S : Sylow p G) :
    ∃ R' : Subgroup G, R' ≤ (S : Subgroup G) ∧ R' ⊓ N = ⊥ ∧
      ((S : Subgroup G) ⊓ N) ⊔ R' = (S : Subgroup G) := by
  classical
  set M : Subgroup G := N ⊔ R with hM
  have hRM : R ≤ M := le_sup_right
  have hRp' : IsPGroup p (R.subgroupOf M) := hRp.comap_of_injective M.subtype M.subtype_injective
  obtain ⟨T', hT'⟩ := hRp'.exists_le_sylow
  set T : Subgroup G := (T' : Subgroup M).map M.subtype with hT
  have hTM : T ≤ M := map_subtype_le _
  have hRT : R ≤ T := fun r hr =>
    ⟨⟨r, hRM hr⟩, hT' (by simpa [mem_subgroupOf] using hr), rfl⟩
  have hTp : IsPGroup p T := T'.isPGroup'.map M.subtype
  have hTidx : ¬ p ∣ T.index := by
    have h1 : T.relIndex M * M.index = T.index := relIndex_mul_index hTM
    have h2 : T.relIndex M = (T' : Subgroup M).index := by
      have : T.subgroupOf M = (T' : Subgroup M) :=
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
      rw [Subgroup.relIndex, this]
    rw [← h1]
    intro hd
    rcases (Nat.Prime.dvd_mul Fact.out).1 hd with hd | hd
    · exact T'.not_dvd_index (h2 ▸ hd)
    · exact hidx hd
  let T0 : Sylow p G := hTp.toSylow hTidx
  haveI : Finite (Sylow p G) :=
    Finite.of_injective (fun P : Sylow p G => (P : Subgroup G)) fun P Q h => Sylow.ext h
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T0 S
  have hTS : ∀ t ∈ T, g * t * g⁻¹ ∈ (S : Subgroup G) := by
    intro t ht
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul t (MulAut.conj g) _ ht
  have hST : ∀ x ∈ (S : Subgroup G), ∃ t ∈ T, g * t * g⁻¹ = x := by
    intro x hx
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    exact ⟨t, ht, rfl⟩
  refine ⟨R.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨r, hr, rfl⟩
    exact hTS r (hRT hr)
  · rw [eq_bot_iff]
    rintro _ ⟨⟨r, hr, rfl⟩, hrN⟩
    have h1 : r ∈ N := by
      have := (inferInstance : N.Normal).conj_mem' _ hrN g
      simpa [MulAut.conj_apply, mul_assoc] using this
    have h2 : r ∈ R ⊓ N := ⟨hr, h1⟩
    rw [hRN, mem_bot] at h2
    subst h2
    simp
  · refine le_antisymm (sup_le inf_le_left ?_) fun x hx => ?_
    · rintro _ ⟨r, hr, rfl⟩
      exact hTS r (hRT hr)
    · obtain ⟨t, ht, rfl⟩ := hST x hx
      obtain ⟨n, hn, r, hr, hnr⟩ := mem_sup_of_normal_left.1 (hTM ht)
      have hnT : n ∈ T := by
        have : n = t * r⁻¹ := by rw [← hnr]; group
        rw [this]
        exact T.mul_mem ht (T.inv_mem (hRT hr))
      have hx : g * t * g⁻¹ = (g * n * g⁻¹) * (g * r * g⁻¹) := by
        rw [← hnr]; group
      rw [hx]
      refine mul_mem_sup ⟨hTS n hnT, ?_⟩ ⟨r, hr, by simp [MulAut.conj_apply]⟩
      simpa [MulAut.conj_apply, mul_assoc] using (inferInstance : N.Normal).conj_mem n hn g

theorem exists_lift_of_chain [Finite G] {p : ℕ} [Fact p.Prime] {N D F : Subgroup G} [N.Normal]
    [D.Normal] (hND : N ≤ D) (hF : F ⊓ D = ⊥) (hD : ¬ p ∣ N.relIndex D)
    (hFD : ¬ p ∣ (D ⊔ F).index) :
    ∃ R : Subgroup G, IsPGroup p R ∧ R ⊓ N = ⊥ ∧ ¬ p ∣ (N ⊔ R).index := by
  classical
  obtain ⟨P⟩ : Nonempty (Sylow p F) := inferInstance
  set R : Subgroup G := (P : Subgroup F).map F.subtype with hR
  have hRF : R ≤ F := map_subtype_le _
  have hFN : F ⊓ N = ⊥ := eq_bot_iff.2 ((inf_le_inf_left F hND).trans hF.le)
  refine ⟨R, P.isPGroup'.map F.subtype, eq_bot_iff.2 ((inf_le_inf_right N hRF).trans hFN.le), ?_⟩
  have h1 : R.relIndex F = (P : Subgroup F).index := by
    have : R.subgroupOf F = (P : Subgroup F) :=
      Subgroup.comap_map_eq_self_of_injective F.subtype_injective _
    rw [Subgroup.relIndex, this]
  have h2 : (N ⊔ R).relIndex (N ⊔ F) = R.relIndex F :=
    relIndex_sup_sup_of_inf_eq_bot hRF hFN
  have h3 : (N ⊔ F).relIndex (D ⊔ F) = N.relIndex D := relIndex_sup_sup_of_le hND hF
  have h4 := relIndex_mul_relIndex (N ⊔ R) (N ⊔ F) (D ⊔ F) (sup_le_sup_left hRF N)
    (sup_le_sup_right hND F)
  have h5 := relIndex_mul_relIndex (N ⊔ R) (D ⊔ F) ⊤
    ((sup_le_sup_left hRF N).trans (sup_le_sup_right hND F)) le_top
  rw [relIndex_top_right, relIndex_top_right] at h5
  rw [← h5, ← h4, h2, h3, h1]
  intro hd
  rcases (Nat.Prime.dvd_mul Fact.out).1 hd with hd | hd
  · rcases (Nat.Prime.dvd_mul Fact.out).1 hd with hd | hd
    · exact P.not_dvd_index hd
    · exact hD hd
  · exact hFD hd

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S

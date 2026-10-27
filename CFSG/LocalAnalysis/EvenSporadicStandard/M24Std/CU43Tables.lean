module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Cover
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Aut

public section

namespace CFSG.EvenSporadicStandard.M24Std.CU43

open Subgroup CFSG.Sporadic.SmallOddCore

theorem inner_card_centralizer
    {β : Equiv.Perm (Fin 820)} (hβ : β ∈ P) (h2 : β * β = 1) (h1 : β ≠ 1) :
    Nat.card ↥(P ⊓ centralizer ({β} : Set (Equiv.Perm (Fin 820)))) = 1152 := by
  obtain ⟨j, hj, ⟨c, hc, rfl⟩, g, hg, hβg⟩ := involution_data (P_le_R hβ) h2 h1
  have e1 := coset_index_of_mem hj (repCoset_eq_zero_of_mem hβ hj hg hβg)
  subst e1
  rw [card_inf_centralizer_conj hc, card_inf_centralizer_rP hj]
  decide

variable {X : Type*} [Group X] (E : Subgroup X) [E.Normal] (θ : E ≃* P)

@[expose] noncomputable def emb :
    X →* Equiv.Perm (Fin 820) :=
  autModel.embed E θ

theorem emb_mem
    (x : X) : emb E θ x ∈ R :=
  autModel.embed_mem E θ x

theorem emb_coe
    (s : E) : emb E θ s = θ s :=
  autModel.embed_coe E θ s

theorem emb_injective
    (hC : centralizer (E : Set X) = ⊥) :
    Function.Injective (emb E θ) :=
  autModel.embed_injective E θ hC

theorem emb_mem_P_iff
    (hC : centralizer (E : Set X) = ⊥) {t : X} :
    emb E θ t ∈ P ↔ t ∈ E := by
  constructor
  · intro h
    have h1 : emb E θ ((θ.symm ⟨_, h⟩ : E) : X) = emb E θ t := by
      rw [emb_coe, MulEquiv.apply_symm_apply]
    exact (emb_injective E θ hC h1) ▸ (θ.symm ⟨_, h⟩).2
  · intro h
    have := emb_coe E θ ⟨t, h⟩
    rw [show (((⟨t, h⟩ : E)) : X) = t from rfl] at this
    rw [this]
    exact (θ ⟨t, h⟩).2

theorem emb_mul_self
    {t : X} (h : t * t = 1) : emb E θ t * emb E θ t = 1 := by
  rw [← map_mul, h, map_one]

theorem card_inf_centralizer_emb
    (hC : centralizer (E : Set X) = ⊥) (t : X) :
    Nat.card ↥(E ⊓ centralizer ({t} : Set X)) =
      Nat.card ↥(P ⊓ centralizer ({emb E θ t} : Set (Equiv.Perm (Fin 820)))) :=
  Nat.card_congr (autModel.centralizerEquiv E θ hC t).toEquiv


include θ in
theorem card_inf_centralizer_inner
    (hC : centralizer (E : Set X) = ⊥) {t : X} (ht : t ∈ E)
    (h2 : t * t = 1) (h1 : t ≠ 1) : Nat.card ↥(E ⊓ centralizer ({t} : Set X)) = 1152 := by
  rw [card_inf_centralizer_emb E θ hC]
  have h1' : emb E θ t ≠ 1 := fun h => h1 (emb_injective E θ hC (by rw [h, map_one]))
  exact inner_card_centralizer ((emb_mem_P_iff E θ hC).2 ht) (emb_mul_self E θ h2) h1'

include θ in
theorem card_inf_centralizer_outer
    (hC : centralizer (E : Set X) = ⊥) {t : X} (ht : t ∉ E)
    (h2 : t * t = 1) :
    Nat.card ↥(E ⊓ centralizer ({t} : Set X)) = 576 ∨
      Nat.card ↥(E ⊓ centralizer ({t} : Set X)) = 720 ∨
      Nat.card ↥(E ⊓ centralizer ({t} : Set X)) = 6048 ∨
      Nat.card ↥(E ⊓ centralizer ({t} : Set X)) = 25920 := by
  rw [card_inf_centralizer_emb E θ hC]
  exact outer_card_centralizer (emb_mem E θ t) (fun h => ht ((emb_mem_P_iff E θ hC).1 h))
    (emb_mul_self E θ h2)

theorem exists_emb_eq
    {c₀ : Equiv.Perm (Fin 820)} (hc₀ : c₀ ∈ P) :
    ∃ c ∈ E, emb E θ c = c₀ :=
  ⟨(θ.symm ⟨c₀, hc₀⟩ : E), (θ.symm ⟨c₀, hc₀⟩).2, by
    rw [emb_coe, MulEquiv.apply_symm_apply]⟩

include θ in
theorem inner_conj
    (hC : centralizer (E : Set X) = ⊥) {s s' : X} (hs : s ∈ E)
    (hs' : s' ∈ E) (h2 : s * s = 1) (h2' : s' * s' = 1) (h1 : s ≠ 1) (h1' : s' ≠ 1) :
    ∃ c ∈ E, s' = c * s * c⁻¹ := by
  have hne : ∀ {u : X}, u ≠ 1 → emb E θ u ≠ 1 := fun hu h =>
    hu (emb_injective E θ hC (by rw [h, map_one]))
  obtain ⟨c₀, hc₀, hc⟩ := inner_involutions_conj ((emb_mem_P_iff E θ hC).2 hs)
    ((emb_mem_P_iff E θ hC).2 hs') (emb_mul_self E θ h2) (emb_mul_self E θ h2') (hne h1)
    (hne h1')
  obtain ⟨c, hcE, rfl⟩ := exists_emb_eq E θ hc₀
  refine ⟨c, hcE, emb_injective E θ hC ?_⟩
  rw [map_mul, map_mul, map_inv]
  exact hc

include θ in
theorem same_coset_conj'
    (hC : centralizer (E : Set X) = ⊥) {t t' : X} (ht : t ∉ E)
    (h2 : t * t = 1) (h2' : t' * t' = 1) (hcos : t' * t⁻¹ ∈ E)
    (hc : Nat.card ↥(E ⊓ centralizer ({t} : Set X)) = 720)
    (hc' : Nat.card ↥(E ⊓ centralizer ({t'} : Set X)) = 720) : ∃ c ∈ E, t' = c * t * c⁻¹ := by
  rw [card_inf_centralizer_emb E θ hC] at hc hc'
  have hβP : emb E θ t' * (emb E θ t)⁻¹ ∈ P := by
    rw [← map_inv, ← map_mul]
    exact (emb_mem_P_iff E θ hC).2 hcos
  obtain ⟨c₀, hc₀, hcc⟩ := same_coset_conj (emb_mem E θ t)
    (fun h => ht ((emb_mem_P_iff E θ hC).1 h)) (emb_mul_self E θ h2) (emb_mem E θ t')
    (emb_mul_self E θ h2') hβP hc hc'
  obtain ⟨c, hcE, rfl⟩ := exists_emb_eq E θ hc₀
  refine ⟨c, hcE, emb_injective E θ hC ?_⟩
  rw [map_mul, map_mul, map_inv]
  exact hcc

include θ in
theorem card_dvd_eight_mul
    [Finite X] (hC : centralizer (E : Set X) = ⊥) :
    Nat.card X ∣ 8 * Nat.card E := by
  have hinj := emb_injective E θ hC
  have h1 : Nat.card X = Nat.card (emb E θ).range :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have h2 : (emb E θ).range ≤ R := by
    rintro _ ⟨x, rfl⟩
    exact emb_mem E θ x
  have h3 : Nat.card (emb E θ).range ∣ Nat.card R := Subgroup.card_dvd_of_le h2
  rw [card_R, ← Nat.card_congr θ.toEquiv] at h3
  rwa [h1]

include θ in
theorem card_quotient_dvd_eight
    [Finite X] (hC : centralizer (E : Set X) = ⊥) :
    Nat.card (X ⧸ E) ∣ 8 := by
  have h1 := card_dvd_eight_mul E θ hC
  have h2 := E.card_eq_card_quotient_mul_card_subgroup
  have hpos : 0 < Nat.card E := Nat.card_pos
  rw [h2, mul_comm (Nat.card (X ⧸ E)), mul_comm 8] at h1
  exact (Nat.mul_dvd_mul_iff_left hpos).1 h1

end CFSG.EvenSporadicStandard.M24Std.CU43

module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Cover
public import Certificates.Certificate9321

public section

namespace CFSG.ClassicalInvolution.Hat2A7

open Equiv Equiv.Perm

theorem D8list_nodup : D8list.Nodup := by decide

theorem mem_D8_of_mem_D8list {d : A7} (h : d ∈ D8list) : d ∈ D8 := by
  have hs := sD_mem_D8
  have ht := tD_mem_D8
  simp only [D8list, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact D8.one_mem
  · exact hs
  · exact ht
  · exact D8.mul_mem hs ht
  · exact D8.mul_mem ht hs
  · exact D8.mul_mem (D8.mul_mem hs ht) hs
  · exact D8.mul_mem (D8.mul_mem ht hs) ht
  · exact D8.mul_mem (D8.mul_mem (D8.mul_mem hs ht) hs) ht

theorem mem_D8_iff {d : A7} : d ∈ D8 ↔ d ∈ D8list := by
  refine ⟨fun hd => ?_, mem_D8_of_mem_D8list⟩
  let f : Fin D8list.length → ↥D8 := fun k =>
    ⟨D8list.get k, mem_D8_of_mem_D8list (List.get_mem _ _)⟩
  have hf : Function.Injective f := fun k l hkl =>
    (D8list_nodup.get_inj_iff).mp (congrArg Subtype.val hkl)
  have hlen : D8list.length = 8 := rfl
  have hbij : Function.Bijective f := by
    apply hf.bijective_of_nat_card_le
    rw [card_D8, Nat.card_eq_fintype_card, Fintype.card_fin, hlen]
  obtain ⟨k, hk⟩ := hbij.2 ⟨d, hd⟩
  have hkd : D8list.get k = d := congrArg Subtype.val hk
  rw [← hkd]
  exact List.get_mem _ _

theorem four_le_filter_D8list : ∀ σ : Perm (Fin 7), σ * σ = 1 →
    σ * (sD : Perm (Fin 7)) * σ⁻¹ ∈ D8list.map (fun d : A7 => (d : Perm (Fin 7))) →
    σ * (tD : Perm (Fin 7)) * σ⁻¹ ∈ D8list.map (fun d : A7 => (d : Perm (Fin 7))) →
      4 ≤ (D8list.filter (fun d : A7 => decide ((d : Perm (Fin 7)) * σ = σ * d))).length :=
  Certificates.certificate9321

theorem four_le_card_D8 {σ : Perm (Fin 7)} (hσ : σ * σ = 1)
    (hs : ∃ d ∈ D8, (d : Perm (Fin 7)) = σ * (sD : Perm (Fin 7)) * σ⁻¹)
    (ht : ∃ d ∈ D8, (d : Perm (Fin 7)) = σ * (tD : Perm (Fin 7)) * σ⁻¹) :
    4 ≤ Nat.card ↥(D8 ⊓ evenCentralizer σ) := by
  have hmem : ∀ {p : Perm (Fin 7)}, (∃ d ∈ D8, (d : Perm (Fin 7)) = p) →
      p ∈ D8list.map (fun d : A7 => (d : Perm (Fin 7))) := by
    rintro p ⟨d, hd, rfl⟩
    exact List.mem_map.mpr ⟨d, mem_D8_iff.mp hd, rfl⟩
  have h4 := four_le_filter_D8list σ hσ (hmem hs) (hmem ht)
  set S := D8list.filter (fun d : A7 => decide ((d : Perm (Fin 7)) * σ = σ * d)) with hS
  have hSnd : S.Nodup := D8list_nodup.filter _
  have hSmem : ∀ d ∈ S, d ∈ D8 ⊓ evenCentralizer σ := by
    intro d hd
    rw [hS, List.mem_filter, decide_eq_true_iff] at hd
    exact ⟨mem_D8_of_mem_D8list hd.1, hd.2⟩
  let f : Fin S.length → ↥(D8 ⊓ evenCentralizer σ) := fun k =>
    ⟨S.get k, hSmem _ (List.get_mem _ _)⟩
  have hf : Function.Injective f := fun k l hkl =>
    (hSnd.get_inj_iff).mp (congrArg Subtype.val hkl)
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

theorem four_le_card_of_normalizes {D : Subgroup A7}
    (hD : Nat.card D = 8) {σ : Perm (Fin 7)} (hσ : σ * σ = 1)
    (hN : ∀ d ∈ D, ∃ d' ∈ D, (d' : Perm (Fin 7)) = σ * d * σ⁻¹) :
    4 ≤ Nat.card ↥(D ⊓ evenCentralizer σ) := by
  have hcard : ∀ P : Subgroup A7, Nat.card P = 8 →
      Nat.card P = 2 ^ (Nat.card A7).factorization 2 := by
    intro P hP
    rw [hP, card_A7, Nat.factorization_def _ Nat.prime_two]
    decide +kernel
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P₀ : Sylow 2 A7 := Sylow.ofCard D8 (hcard D8 card_D8)
  let Q : Sylow 2 A7 := Sylow.ofCard D (hcard D hD)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A7 P₀ Q
  have hDmem : ∀ d : A7, d ∈ D ↔ ∃ y ∈ D8, g * y * g⁻¹ = d := by
    intro d
    have h1 : d ∈ (Q : Subgroup A7) ↔ ∃ y ∈ (P₀ : Subgroup A7), g * y * g⁻¹ = d := by
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      constructor
      · rintro ⟨y, hy, hyd⟩
        exact ⟨y, hy, by simpa [MulAut.conj_apply] using hyd⟩
      · rintro ⟨y, hy, hyd⟩
        exact ⟨y, hy, by simpa [MulAut.conj_apply] using hyd⟩
    exact h1
  set gP : Perm (Fin 7) := (g : Perm (Fin 7)) with hgP
  set σ₀ : Perm (Fin 7) := gP⁻¹ * σ * gP with hσ₀def
  have hσ₀ : σ₀ * σ₀ = 1 := by
    calc σ₀ * σ₀ = gP⁻¹ * (σ * σ) * gP := by rw [hσ₀def]; group
      _ = 1 := by rw [hσ]; group
  have hconj : ∀ d₀ : A7, ((g * d₀ * g⁻¹ : A7) : Perm (Fin 7)) = gP * d₀ * gP⁻¹ := fun d₀ => rfl
  have hnorm : ∀ d₀ ∈ D8, ∃ d₀' ∈ D8, (d₀' : Perm (Fin 7)) = σ₀ * d₀ * σ₀⁻¹ := by
    intro d₀ hd₀
    have hdD : g * d₀ * g⁻¹ ∈ D := (hDmem _).mpr ⟨d₀, hd₀, rfl⟩
    obtain ⟨d', hd'D, hd'⟩ := hN _ hdD
    obtain ⟨d₀', hd₀', hd'eq⟩ := (hDmem d').mp hd'D
    refine ⟨d₀', hd₀', ?_⟩
    rw [← hd'eq, hconj, hconj] at hd'
    have h2 : gP * (d₀' : Perm (Fin 7)) * gP⁻¹ = σ * (gP * d₀ * gP⁻¹) * σ⁻¹ := hd'
    calc (d₀' : Perm (Fin 7)) = gP⁻¹ * (gP * (d₀' : Perm (Fin 7)) * gP⁻¹) * gP := by group
      _ = gP⁻¹ * (σ * (gP * d₀ * gP⁻¹) * σ⁻¹) * gP := by rw [h2]
      _ = σ₀ * d₀ * σ₀⁻¹ := by rw [hσ₀def]; group
  have h4 := four_le_card_D8 hσ₀ (hnorm sD sD_mem_D8) (hnorm tD tD_mem_D8)
  have hle : (D8 ⊓ evenCentralizer σ₀).map (MulAut.conj g).toMonoidHom ≤ D ⊓ evenCentralizer σ := by
    rintro _ ⟨y, ⟨hyD8, hyC⟩, rfl⟩
    refine ⟨(hDmem _).mpr ⟨y, hyD8, by simp [MulAut.conj_apply]⟩, ?_⟩
    have hyC' : (y : Perm (Fin 7)) * σ₀ = σ₀ * y := hyC
    show (((MulAut.conj g) y : A7) : Perm (Fin 7)) * σ =
      σ * (((MulAut.conj g) y : A7) : Perm (Fin 7))
    have e : (((MulAut.conj g) y : A7) : Perm (Fin 7)) = gP * y * gP⁻¹ := rfl
    rw [e]
    have hσe : σ = gP * σ₀ * gP⁻¹ := by rw [hσ₀def]; group
    calc gP * (y : Perm (Fin 7)) * gP⁻¹ * σ = gP * ((y : Perm (Fin 7)) * σ₀) * gP⁻¹ := by
          rw [hσe]; group
      _ = gP * (σ₀ * y) * gP⁻¹ := by rw [hyC']
      _ = σ * (gP * (y : Perm (Fin 7)) * gP⁻¹) := by rw [hσe]; group
  have hcardle := Subgroup.card_le_of_le hle
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective] at hcardle
  omega

end CFSG.ClassicalInvolution.Hat2A7

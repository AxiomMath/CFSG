module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65Ext2

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip

variable {G : Type} [Group G] [Finite G]

theorem extremal_syl {z u : G} {S : Subgroup G} (hStop : M.Syl2In S ⊤) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hzS : z ∈ S) (hzc : ∀ s ∈ S, z * s = s * z)
    (hd : ∃ S' : Sylow 2 G, ∀ g : G, (g ∈ (S' : Subgroup G) ∧
      (∀ s ∈ (S' : Subgroup G), s * g = g * s) ∧ g ^ 2 = 1) ↔ g ∈ zpowers z)
    (huS : u ∈ S) (hu2 : u * u = 1) (hu1 : u ≠ 1) (huz : u ≠ z)
    (hnorm : ∀ s ∈ S, s * u * s⁻¹ = u ∨ s * u * s⁻¹ = u * z) (hnc : ¬ IsConj z u) :
    M.Syl2In (S ⊓ centralizer ({u} : Set G)) (centralizer ({u} : Set G)) ∧
      Nat.card ↥S = 2 * Nat.card ↥(S ⊓ centralizer ({u} : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C₀ : Subgroup G := S ⊓ centralizer ({u} : Set G) with hC₀
  have hC₀S : C₀ ≤ S := inf_le_left
  have hC₀c : C₀ ≤ centralizer ({u} : Set G) := inf_le_right
  have hmemC : ∀ s ∈ S, s ∈ C₀ ↔ s * u * s⁻¹ = u := by
    intro s hs
    constructor
    · intro hs'
      have := Subgroup.mem_centralizer_singleton_iff.1 hs'.2
      calc s * u * s⁻¹ = u * s * s⁻¹ := by rw [this]
        _ = u := by group
    · intro h
      refine ⟨hs, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      calc s * u = (s * u * s⁻¹) * s := by group
        _ = u * s := by rw [h]
  have hznc : ∃ s ∈ S, s * u * s⁻¹ = u * z := by
    by_contra hcon
    push Not at hcon
    have hcen : ∀ s ∈ S, u * s = s * u := by
      intro s hs
      rcases hnorm s hs with h1 | h1
      · calc u * s = (s * u * s⁻¹) * s := by rw [h1]
          _ = s * u := by group
      · exact absurd h1 (hcon s hs)
    rcases IVK.Lifted.z_central_inv hz2 hz1 hzS hzc hStop hd huS (fun s hs => hcen s hs) hu2 with h | h
    · exact hu1 h
    · exact huz h
  obtain ⟨s₀, hs₀S, hs₀⟩ := hznc
  have hzu : ∀ s ∈ S, s * (u * z) * s⁻¹ = (s * u * s⁻¹) * z := by
    intro s hs
    have := hzc s hs
    calc s * (u * z) * s⁻¹ = s * u * (z * s⁻¹) := by group
      _ = s * u * (s⁻¹ * z) := by
        have : z * s⁻¹ = s⁻¹ * z := hzc _ (S.inv_mem hs)
        rw [this]
      _ = (s * u * s⁻¹) * z := by group
  have hne : u * z ≠ u := fun h => hz1 (mul_left_cancel (h.trans (mul_one u).symm))
  have huzz : (u * z) * z = u := by rw [mul_assoc, hz2, mul_one]
  have hindex : (C₀.subgroupOf S).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨s₀, hs₀S⟩, fun b => ?_⟩
    have hb := b.2
    have hbmem : b ∈ C₀.subgroupOf S ↔ (b : G) * u * (b : G)⁻¹ = u := by
      rw [Subgroup.mem_subgroupOf]; exact hmemC _ hb
    have hbsmem : b * ⟨s₀, hs₀S⟩ ∈ C₀.subgroupOf S ↔
        (b : G) * s₀ * u * ((b : G) * s₀)⁻¹ = u := by
      rw [Subgroup.mem_subgroupOf]
      have := hmemC ((b : G) * s₀) (S.mul_mem hb hs₀S)
      simpa [mul_assoc] using this
    have hkey : (b : G) * s₀ * u * ((b : G) * s₀)⁻¹ = (b : G) * (s₀ * u * s₀⁻¹) * (b : G)⁻¹ := by
      group
    have hkey' : (b : G) * s₀ * u * ((b : G) * s₀)⁻¹ = ((b : G) * u * (b : G)⁻¹) * z := by
      rw [hkey, hs₀, hzu _ hb]
    rcases hnorm b hb with h1 | h1
    · have h2 : (b : G) * s₀ * u * ((b : G) * s₀)⁻¹ = u * z := by rw [hkey', h1]
      right
      exact ⟨hbmem.2 h1, fun hx => hne (h2.symm.trans (hbsmem.1 hx))⟩
    · have h2 : (b : G) * s₀ * u * ((b : G) * s₀)⁻¹ = u := by rw [hkey', h1, huzz]
      left
      exact ⟨hbsmem.2 h2, fun hx => hne (h1.symm.trans (hbmem.1 hx))⟩
  have hcard : Nat.card ↥S = 2 * Nat.card ↥C₀ := by
    have h1 := Subgroup.card_mul_index (C₀.subgroupOf S)
    rw [hindex] at h1
    have h2 : Nat.card ↥(C₀.subgroupOf S) = Nat.card ↥C₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC₀S).toEquiv
    rw [h2] at h1
    omega
  refine ⟨?_, hcard⟩
  have hC₀p : IsPGroup 2 ↥C₀ := hStop.2.1.to_inf_left
  obtain ⟨T, hT, hle⟩ := M.exists_syl2In_ge hC₀p hC₀c
  have huC₀ : u ∈ C₀ := ⟨huS, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hTeq : T = C₀ := by
    by_contra hne
    have hdvd : Nat.card ↥C₀ ∣ Nat.card ↥T := Subgroup.card_dvd_of_le hle
    have hlt : Nat.card ↥C₀ ≠ Nat.card ↥T := fun h =>
      hne (Subgroup.eq_of_le_of_card_ge hle (le_of_eq h.symm)).symm
    obtain ⟨m, hm⟩ := hdvd
    have hpos : 0 < Nat.card ↥C₀ := Nat.card_pos
    have hm2 : 2 ≤ m := by
      by_contra hm2
      have : m = 0 ∨ m = 1 := by omega
      rcases this with h0 | h1
      · rw [h0, mul_zero] at hm
        have : 0 < Nat.card ↥T := Nat.card_pos
        omega
      · rw [h1, mul_one] at hm
        exact hlt hm.symm
    have hTS : Nat.card ↥S ≤ Nat.card ↥T := by
      rw [hcard, hm]
      nlinarith
    obtain ⟨S₂, hS₂, hTS₂⟩ := M.exists_syl2In_ge hT.2.1 (le_top : T ≤ ⊤)
    have hcard₂ : Nat.card ↥S₂ = Nat.card ↥S := hS₂.card_eq hStop
    have hTeq₂ : T = S₂ := Subgroup.eq_of_le_of_card_ge hTS₂ (by omega)
    obtain ⟨c, -, hc⟩ := hStop.exists_conj hS₂
    have huT : u ∈ T := hle huC₀
    have hcu : c * u * c⁻¹ ∈ S := by
      have : u ∈ M.cj S c := by rw [← hc, ← hTeq₂]; exact huT
      exact (M.mem_cj).1 this
    have hcen : ∀ s ∈ S, (c * u * c⁻¹) * s = s * (c * u * c⁻¹) := by
      intro s hs
      have hmem : c⁻¹ * s * c ∈ T := by
        rw [hTeq₂, hc]
        rw [M.mem_cj]
        have e : c * (c⁻¹ * s * c) * c⁻¹ = s := by group
        rw [e]; exact hs
      have h1 : (c⁻¹ * s * c) * u = u * (c⁻¹ * s * c) :=
        Subgroup.mem_centralizer_singleton_iff.1 (hT.1 hmem)
      calc (c * u * c⁻¹) * s = c * (u * (c⁻¹ * s * c)) * c⁻¹ := by group
        _ = c * ((c⁻¹ * s * c) * u) * c⁻¹ := by rw [h1]
        _ = s * (c * u * c⁻¹) := by group
    have hsq : (c * u * c⁻¹) * (c * u * c⁻¹) = 1 := by
      calc (c * u * c⁻¹) * (c * u * c⁻¹) = c * (u * u) * c⁻¹ := by group
        _ = 1 := by rw [hu2]; group
    rcases IVK.Lifted.z_central_inv hz2 hz1 hzS hzc hStop hd hcu (fun s hs => hcen s hs) hsq with h1 | h1
    · apply hu1
      have : u = c⁻¹ * (c * u * c⁻¹) * c := by group
      rw [this, h1]; group
    · apply hnc
      refine isConj_iff.2 ⟨c⁻¹, ?_⟩
      have : u = c⁻¹ * (c * u * c⁻¹) * c := by group
      rw [this, h1]; group
  rw [hTeq] at hT
  exact hT

section Cfg65Facts

variable {z : G} {S K₁ K₂ : Subgroup G} {t : G}

namespace Cfg65

variable (h : Cfg65 G z S K₁ K₂ t)

include h in
theorem hd_clause : ∃ S' : Sylow 2 G, ∀ g : G, (g ∈ (S' : Subgroup G) ∧
    (∀ s ∈ (S' : Subgroup G), s * g = g * s) ∧ g ^ 2 = 1) ↔ g ∈ zpowers z := by
  obtain ⟨t₀, ht₀C, ht₀z, ht₀n⟩ := h.std.thm2
  exact (h.std.classical.2 t₀ ht₀C ht₀z ht₀n).2.2.2.1

variable {a b : G} (hAB : AB65 S K₁ a b)

include h hAB

theorem z_comm_a_sq (hII : II4_4_4_center) : z * a ^ 2 = a ^ 2 * z := by
  have hc := (h.m4 hII).S_syl.1 (pow_mem hAB.ha.1 2)
  exact (Subgroup.mem_centralizer_singleton_iff.1 hc).symm

theorem z_comm_aTwo_sq (hII : II4_4_4_center) : z * (aTwo t a) ^ 2 = (aTwo t a) ^ 2 * z := by
  have hc := (h.m4 hII).S_syl.1 (pow_mem (h.a₂_mem hAB).1 2)
  exact (Subgroup.mem_centralizer_singleton_iff.1 hc).symm

theorem inv_a_sq (hII : II4_4_4_center) : (a ^ 2)⁻¹ = a ^ 2 * z := by
  have h1 : a ^ 2 * a ^ 2 = z := h.a_sq_sq hAB hII
  have hz : z * a ^ 2 = a ^ 2 * z := h.z_comm_a_sq hAB hII
  have : (a ^ 2 * z) * a ^ 2 = 1 := by
    calc (a ^ 2 * z) * a ^ 2 = a ^ 2 * (z * a ^ 2) := by group
      _ = a ^ 2 * (a ^ 2 * z) := by rw [hz]
      _ = (a ^ 2 * a ^ 2) * z := by group
      _ = 1 := by rw [h1]; exact h.z_sq
  exact (eq_inv_of_mul_eq_one_left this).symm

theorem inv_aTwo_sq (hII : II4_4_4_center) : ((aTwo t a) ^ 2)⁻¹ = (aTwo t a) ^ 2 * z := by
  have h1 : (aTwo t a) ^ 2 * (aTwo t a) ^ 2 = z := h.aTwo_sq_sq hAB hII
  have hz : z * (aTwo t a) ^ 2 = (aTwo t a) ^ 2 * z := h.z_comm_aTwo_sq hAB hII
  have : ((aTwo t a) ^ 2 * z) * (aTwo t a) ^ 2 = 1 := by
    calc ((aTwo t a) ^ 2 * z) * (aTwo t a) ^ 2 = (aTwo t a) ^ 2 * (z * (aTwo t a) ^ 2) := by group
      _ = (aTwo t a) ^ 2 * ((aTwo t a) ^ 2 * z) := by rw [hz]
      _ = ((aTwo t a) ^ 2 * (aTwo t a) ^ 2) * z := by group
      _ = 1 := by rw [h1]; exact h.z_sq
  exact (eq_inv_of_mul_eq_one_left this).symm

theorem conj_u_of_mem_P (hII : II4_4_4_center) {p : G} (hp : p ∈ Pz S z) :
    p * uElt t a * p⁻¹ = uElt t a ∨ p * uElt t a * p⁻¹ = uElt t a * z := by
  rw [h.Pz_eq_sup hII] at hp
  obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := M.mem_sup_of_commute (h.P_comm hII) hp
  have hA1 : a ^ 2 ∈ Pof S K₁ := pow_mem hAB.ha 2
  have hA2 : (aTwo t a) ^ 2 ∈ Pof S K₂ := pow_mem (h.a₂_mem hAB) 2
  have hc1 : p₂ * a ^ 2 = a ^ 2 * p₂ := (h.P_comm hII _ hA1 _ hp₂).symm
  have hc2 : p₁ * (aTwo t a) ^ 2 = (aTwo t a) ^ 2 * p₁ := h.P_comm hII _ hp₁ _ hA2
  have hY2 : p₂ * (aTwo t a) ^ 2 * p₂⁻¹ ∈ Pof S K₂ :=
    ⟨S.mul_mem (S.mul_mem hp₂.1 hA2.1) (S.inv_mem hp₂.1), (h.m4 hII).conj_comp₂ (mem_sup_right hp₂.2) hA2.2⟩
  have hc3 : p₁ * (p₂ * (aTwo t a) ^ 2 * p₂⁻¹) = (p₂ * (aTwo t a) ^ 2 * p₂⁻¹) * p₁ :=
    h.P_comm hII _ hp₁ _ hY2
  have hprod : p₁ * p₂ * uElt t a * (p₁ * p₂)⁻¹ =
      (p₁ * a ^ 2 * p₁⁻¹) * (p₂ * (aTwo t a) ^ 2 * p₂⁻¹) := by
    unfold uElt
    calc p₁ * p₂ * (a ^ 2 * (aTwo t a) ^ 2) * (p₁ * p₂)⁻¹
        = p₁ * ((p₂ * a ^ 2) * (aTwo t a) ^ 2 * p₂⁻¹) * p₁⁻¹ := by group
      _ = p₁ * ((a ^ 2 * p₂) * (aTwo t a) ^ 2 * p₂⁻¹) * p₁⁻¹ := by rw [hc1]
      _ = p₁ * (a ^ 2 * (p₂ * (aTwo t a) ^ 2 * p₂⁻¹)) * p₁⁻¹ := by group
      _ = (p₁ * a ^ 2) * (p₂ * (aTwo t a) ^ 2 * p₂⁻¹) * p₁⁻¹ := by group
      _ = (p₁ * a ^ 2) * (p₁⁻¹ * (p₁ * (p₂ * (aTwo t a) ^ 2 * p₂⁻¹))) * p₁⁻¹ := by group
      _ = (p₁ * a ^ 2) * (p₁⁻¹ * ((p₂ * (aTwo t a) ^ 2 * p₂⁻¹) * p₁)) * p₁⁻¹ := by rw [hc3]
      _ = (p₁ * a ^ 2 * p₁⁻¹) * (p₂ * (aTwo t a) ^ 2 * p₂⁻¹) := by group
  have hX : p₁ * a ^ 2 * p₁⁻¹ = a ^ 2 ∨ p₁ * a ^ 2 * p₁⁻¹ = a ^ 2 * z := by
    have e : p₁ * a ^ 2 * p₁⁻¹ = (p₁ * a * p₁⁻¹) ^ 2 := by rw [conj_pow]
    rcases hAB.conj p₁ hp₁ with h1 | h1
    · left; rw [e, h1]
    · right; rw [e, h1, inv_pow, h.inv_a_sq hAB hII]
  have hY : p₂ * (aTwo t a) ^ 2 * p₂⁻¹ = (aTwo t a) ^ 2 ∨
      p₂ * (aTwo t a) ^ 2 * p₂⁻¹ = (aTwo t a) ^ 2 * z := by
    have e : p₂ * (aTwo t a) ^ 2 * p₂⁻¹ = (p₂ * aTwo t a * p₂⁻¹) ^ 2 := by rw [conj_pow]
    rcases h.conj_a₂ hAB hp₂ with h1 | h1
    · left; rw [e]; unfold aTwo; rw [h1]
    · right; rw [e]; unfold aTwo; rw [h1, inv_pow]; exact h.inv_aTwo_sq hAB hII
  have hzA := h.z_comm_a_sq hAB hII
  have hzB := h.z_comm_aTwo_sq hAB hII
  have hzz := h.z_sq
  rw [hprod]
  unfold uElt
  rcases hX with hx | hx <;> rcases hY with hy | hy <;> rw [hx, hy]
  · left; rfl
  · right; group
  · right
    calc a ^ 2 * z * (aTwo t a) ^ 2 = a ^ 2 * (z * (aTwo t a) ^ 2) := by group
      _ = a ^ 2 * ((aTwo t a) ^ 2 * z) := by rw [hzB]
      _ = a ^ 2 * (aTwo t a) ^ 2 * z := by group
  · left
    calc a ^ 2 * z * ((aTwo t a) ^ 2 * z) = a ^ 2 * (z * (aTwo t a) ^ 2) * z := by group
      _ = a ^ 2 * ((aTwo t a) ^ 2 * z) * z := by rw [hzB]
      _ = a ^ 2 * (aTwo t a) ^ 2 * (z * z) := by group
      _ = a ^ 2 * (aTwo t a) ^ 2 := by rw [hzz, mul_one]

theorem conj_u (hII : II4_4_4_center) (h4hij : IVK_1_4hij_outer) {s : G} (hs : s ∈ S) :
    s * uElt t a * s⁻¹ = uElt t a ∨ s * uElt t a * s⁻¹ = uElt t a * z := by
  rcases h.S_cases hII h4hij hs with hP | hP
  · exact h.conj_u_of_mem_P hAB hII hP
  · have e : s * uElt t a * s⁻¹ = (s * t) * (t⁻¹ * uElt t a * t) * (s * t)⁻¹ := by group
    have ht : t⁻¹ * uElt t a * t = uElt t a := by
      have e2 : t⁻¹ * uElt t a * t = t * uElt t a * t⁻¹ := by rw [h.t_inv]
      rw [e2]; exact h.t_u hAB hII
    rw [e, ht]
    exact h.conj_u_of_mem_P hAB hII hP

theorem u_extremal (hII : II4_4_4_center) (h4hij : IVK_1_4hij_outer) (hrec : Bg.B_reciprocity) :
    M.Syl2In (S ⊓ centralizer ({uElt t a} : Set G)) (centralizer ({uElt t a} : Set G)) ∧
      Nat.card ↥S = 2 * Nat.card ↥(S ⊓ centralizer ({uElt t a} : Set G)) := by
  have hM := h.m4 hII
  exact extremal_syl hM.S_top h.z_sq h.z_ne hM.z_mem_S
    (fun s hs => (M.centralizer_comm (hM.S_syl.1 hs)).symm) h.hd_clause (h.u_mem_S hAB hII)
    (h.u_sq hAB hII) (h.u_ne_one hAB hII) (h.u_ne_z hAB hII) (fun s hs => h.conj_u hAB hII h4hij hs)
    (h.u_not_conj hAB hII hrec)

end Cfg65

end Cfg65Facts

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65

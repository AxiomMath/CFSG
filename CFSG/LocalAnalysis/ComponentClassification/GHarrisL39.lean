module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL32a
public import CFSG.GroupTheory.ThompsonIndexTwo
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL31c

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

@[expose] def SCert.dS2 (d : Fin 8) : Prop := d = 0 ∨ d = 1 ∨ d = 6 ∨ d = 7

instance (d : Fin 8) : Decidable (SCert.dS2 d) := by unfold SCert.dS2; infer_instance

theorem SCert.dS2_mul : ∀ d e : Fin 8, dS2 d → dS2 e → dS2 (dmul d e) := by decide

theorem SCert.dS2_inv : ∀ d : Fin 8, dS2 d → dS2 (dinv d) := by decide

theorem SCert.dS2_conj : ∀ d e : Fin 8, dS2 e → dS2 (dmul (dmul (dinv d) e) d) := by decide

@[expose] def SCert.SE.S2sub : Subgroup SE where
  carrier := {s | dS2 s.d}
  mul_mem' {s t} hs ht := dS2_mul s.d t.d hs ht
  one_mem' := Or.inl rfl
  inv_mem' {s} hs := dS2_inv s.d hs

theorem SCert.SE.mem_S2sub {s : SE} : s ∈ SE.S2sub ↔ dS2 s.d := Iff.rfl

theorem SCert.SE.invRepCent_of_dS2 : ∀ i : Fin 9, dS2 (invRep i).d → 64 ≤ invRepCent i := by
  decide

theorem SCert.SE.invRepCent_of_not_dS2 : ∀ i : Fin 9, ¬ dS2 (invRep i).d → invRepCent i = 32 := by
  decide

theorem SCert.SE.card_S2sub : Nat.card SE.S2sub = 256 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun s => SE.mem_S2sub (s := s)),
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

variable {G : Type} [Group G] [Finite G]

namespace GHSylow

variable (D : GHSylow G)

abbrev S2 : Subgroup G := SE.S2sub.map D.toG

omit [Finite G] in
theorem toG_mem_S2_iff {s : SE} : D.toG s ∈ D.S2 ↔ dS2 s.d := D.mem_map_toG

omit [Finite G] in
theorem S2_le_S : D.S2 ≤ (D.S : Subgroup G) := by
  rintro _ ⟨s, -, rfl⟩
  exact D.toG_mem s

omit [Finite G] in
theorem conj_mem_S2 {c w : G} (hc : c ∈ (D.S : Subgroup G)) (hw : w ∈ D.S2) :
    c⁻¹ * w * c ∈ D.S2 := by
  obtain ⟨c₀, rfl⟩ := D.exists_toG hc
  obtain ⟨w₀, hw₀, rfl⟩ := hw
  rw [← map_inv, ← map_mul, ← map_mul, D.toG_mem_S2_iff]
  exact dS2_conj c₀.d w₀.d hw₀

omit [Finite G] in
theorem relIndex_S2 : D.S2.relIndex (D.S : Subgroup G) = 2 := by
  have h := relIndex_mul_card D.S2 (D.S : Subgroup G)
  rw [inf_of_le_left D.S2_le_S, D.card_S_eq,
    show Nat.card D.S2 = 256 by
      rw [← SE.card_S2sub]
      exact (Nat.card_congr (equivMapOfInjective _ _ D.toG_injective).toEquiv).symm] at h
  omega

omit [Finite G] in
theorem card_inf_centralizer_S2 {w : G}
    (hw : w ∈ (D.S : Subgroup G)) (hw2 : w * w = 1) (hw1 : w ≠ 1) :
    (w ∈ D.S2 → 64 ≤ Nat.card ↥((D.S : Subgroup G) ⊓ centralizer ({w} : Set G))) ∧
      (w ∉ D.S2 → Nat.card ↥((D.S : Subgroup G) ⊓ centralizer ({w} : Set G)) = 32) := by
  obtain ⟨i, c, hcS, hc⟩ := D.exists_conj_invRep_G hw hw2 hw1
  have hcard := D.card_inf_centralizer_conj hcS w
  rw [hc, D.card_centralizer_invRep_G] at hcard
  have hmem : w ∈ D.S2 ↔ dS2 (SE.invRep i).d := by
    rw [← D.toG_mem_S2_iff, ← hc]
    constructor
    · exact D.conj_mem_S2 hcS
    · intro h
      have := D.conj_mem_S2 (inv_mem hcS) h
      rwa [show c⁻¹⁻¹ * (c⁻¹ * w * c) * c⁻¹ = w by group] at this
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← hcard]
    exact SE.invRepCent_of_dS2 i (hmem.mp h)
  · rw [← hcard]
    exact SE.invRepCent_of_not_dS2 i (fun h' => h (hmem.mpr h'))

theorem not_isSylowOf_of_not_mem_S2
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) {u : G} (hu : u ∈ (D.S : Subgroup G))
    (hu2 : u * u = 1) (hu1 : u ≠ 1) (huS : u ∉ D.S2) :
    ¬ IsSylowOf 2 ((D.S : Subgroup G) ⊓ centralizer ({u} : Set G)) (centralizer ({u} : Set G)) := by
  intro hext
  have hu32 := (D.card_inf_centralizer_S2 hu hu2 hu1).2 huS
  have hconj : ∀ g : G, g⁻¹ * u * g ∉ D.S2 := by
    intro g hg
    set w := g⁻¹ * u * g with hw
    have hwS := D.S2_le_S hg
    have hw2 : w * w = 1 := by
      rw [hw, show g⁻¹ * u * g * (g⁻¹ * u * g) = g⁻¹ * (u * u) * g by group, hu2]; group
    have hw1 : w ≠ 1 := fun h => hu1 (by
      calc u = g * w * g⁻¹ := by rw [hw]; group
        _ = 1 := by rw [h]; group)
    have h64 := (D.card_inf_centralizer_S2 hwS hw2 hw1).1 hg
    set Q := ((D.S : Subgroup G) ⊓ centralizer ({w} : Set G)).map (MulAut.conj g).toMonoidHom
    have hQK : Q ≤ centralizer ({u} : Set G) := by
      rintro _ ⟨c, hc, rfl⟩
      have hcw := mem_centralizer_singleton_iff.mp (mem_inf.mp hc).2
      rw [mem_centralizer_singleton_iff]
      change g * c * g⁻¹ * u = u * (g * c * g⁻¹)
      calc g * c * g⁻¹ * u = g * (c * w) * g⁻¹ := by rw [hw]; group
        _ = g * (w * c) * g⁻¹ := by rw [hcw]
        _ = u * (g * c * g⁻¹) := by rw [hw]; group
    have hQ2 : IsPGroup 2 Q :=
      (D.S.isPGroup'.to_le inf_le_left).map _
    obtain ⟨c, -, hc⟩ := exists_conj_le_of_isSylowOf hext hQK hQ2
    have hle : Q.map (MulAut.conj c).toMonoidHom ≤
        (D.S : Subgroup G) ⊓ centralizer ({u} : Set G) := by
      rintro _ ⟨q, hq, rfl⟩
      exact hc q hq
    have hcard := card_le_of_le hle
    rw [card_map_of_injective (MulAut.conj c).injective,
      card_map_of_injective (MulAut.conj g).injective, hu32] at hcard
    omega
  obtain ⟨N, hN, hN2⟩ := ThompsonIndexTwo.exists_normal_index_two_of_thompson D.S.isPGroup'
    D.S.not_dvd_index D.S2_le_S D.relIndex_S2 hu huS (fun y hy hyS => by
      have hy1 : y ≠ 1 := fun h => hyS (h ▸ one_mem _)
      have h2 : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
      rw [h2]
      have hpos : 0 < orderOf y := orderOf_pos y
      have hne : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.mp h)
      omega) hconj
  exact hidx N hN hN2

end GHSylow

end CFSG.ComponentClassification.GHarris

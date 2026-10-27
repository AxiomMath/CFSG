module

public import CFSG.GH74.Generic.S1.Exo.Nb3Defs
public import CFSG.GH74.Generic.S1.Exo.NbQ8
public import CFSG.GH74.Generic.S1.Exo.NbLoc
public import CFSG.GH74.Generic.S1.CompIdent
public import CFSG.GH74.Generic.S1.SL2Facts
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.GH74 CFSG.GH74.GLS Subgroup CFSG.GH74.Filter.ClassicalOdd CFSG.LocalCores
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {c y : H} {JA JB : Subgroup H}

theorem q8_pow_four : ∀ g : Q8, g ^ 4 = 1 := by decide

theorem q8_z_sq : (QuaternionGroup.a 2 : Q8) * QuaternionGroup.a 2 = 1 := by decide

theorem q8_z_ne : (QuaternionGroup.a 2 : Q8) ≠ 1 := by decide

theorem pCore_two_le_centralizer_layer : CFSG.pCore 2 H ≤ Subgroup.centralizer (layer H : Set H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsolv : Group.IsSolvable (CFSG.pCore 2 H) := by
    have := IsPGroup.isNilpotent (CFSG.pCore_isPGroup (p := 2) (G := H))
    infer_instance
  have h := (component_solvable_centralizer hsolv
    (CFSG.pCore_normal (p := 2) (G := H)).isSubnormal).2
  exact Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)

theorem Nbhd3Hyp.q8A (h : Nbhd3Hyp H c y JA JB) :
    ∃ ψ : Q8 →* H, Function.Injective ψ ∧ (∀ g, ψ g ∈ JA) ∧ ψ (QuaternionGroup.a 2) = c := by
  obtain ⟨ψ, hψi, hψm⟩ := exists_q8_of_hasSL2Model (by decide : Odd 3) h.sl2A
  obtain ⟨t, -, -, ht, -⟩ := sl2_involution_facts (by decide : Odd 3) h.sl2A
  have hct : c = t := (ht c h.c_mem h.c_sq).resolve_left h.c_ne_one
  refine ⟨ψ, hψi, hψm, ?_⟩
  have hsq : ψ (QuaternionGroup.a 2) * ψ (QuaternionGroup.a 2) = 1 := by
    rw [← map_mul, q8_z_sq, map_one]
  rcases ht _ (hψm _) hsq with h1 | h1
  · exact absurd (hψi (h1.trans (map_one ψ).symm)) q8_z_ne
  · rw [h1, hct]

theorem Nbhd3Hyp.q8B (h : Nbhd3Hyp H c y JA JB) :
    ∃ ψ : Q8 →* H, Function.Injective ψ ∧ (∀ g, ψ g ∈ JB) ∧ ψ (QuaternionGroup.a 2) = y := by
  obtain ⟨ψ, hψi, hψm⟩ := exists_q8_of_hasSL2Model (by decide : Odd 3) h.sl2B
  obtain ⟨t, -, -, ht, -⟩ := sl2_involution_facts (by decide : Odd 3) h.sl2B
  have hyt : y = t := (ht y h.y_mem h.y_sq).resolve_left h.y_ne_one
  refine ⟨ψ, hψi, hψm, ?_⟩
  have hsq : ψ (QuaternionGroup.a 2) * ψ (QuaternionGroup.a 2) = 1 := by
    rw [← map_mul, q8_z_sq, map_one]
  rcases ht _ (hψm _) hsq with h1 | h1
  · exact absurd (hψi (h1.trans (map_one ψ).symm)) q8_z_ne
  · rw [h1, hyt]

omit [Finite H] in
theorem two_elt_q8 {ψ : Q8 →* H} (g : Q8) : ∃ k : ℕ, (ψ g) ^ (2 ^ k) = 1 :=
  ⟨2, by rw [← map_pow]; exact (by rw [show (2 : ℕ) ^ 2 = 4 from rfl, q8_pow_four g, map_one])⟩

theorem Nbhd3Hyp.mem_cent_iff (h : Nbhd3Hyp H c y JA JB) (g : H) :
    g ∈ centralizer ({c * y} : Set H) ↔ g * y = y * g := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have e1 : c * y * g = c * (y * g) := by rw [mul_assoc]
  have e2 : g * (c * y) = c * (g * y) := by rw [← mul_assoc, h.c_central g, mul_assoc]
  rw [e1, e2]
  exact ⟨fun h' => mul_left_cancel h', fun h' => by rw [h']⟩

theorem Nbhd3Hyp.comp_eq_of_mem (h : Nbhd3Hyp H c y JA JB) {N K : Subgroup H} (hN : IsComponent N)
    (hK : IsComponent K) (hy : y ∈ N) : K = N := by
  by_contra hne
  have hcomm : ∀ a ∈ K, ∀ b ∈ N, a * b = b * a :=
    nb_comm_of_commutator_eq_bot ((distinct_components_commute hK hN).resolve_left hne)
  have hKc : K ≤ centralizer ({c * y} : Set H) := fun a ha => (h.mem_cent_iff a).2 (hcomm a ha y hy)
  have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hK.1.1
  have hbot := h.perfect_free K hperf hKc
  have hnt : Nontrivial ↥K := isQuasisimple_nontrivial hK.1
  exact (Subgroup.nontrivial_iff_ne_bot K).1 hnt hbot

structure Q3Red (H : Type) [Group H] [Finite H] (c y : H) (JA JB N : Subgroup H) (ψA ψB : Q8 →* H) : Prop where
  comp : IsComponent N
  only : ∀ K : Subgroup H, IsComponent K → K = N
  layer_eq : layer H = N
  injA : Function.Injective ψA
  injB : Function.Injective ψB
  zA : ψA (QuaternionGroup.a 2) = c
  zB : ψB (QuaternionGroup.a 2) = y
  comm : ∀ g g' : Q8, ψA g * ψB g' = ψB g' * ψA g
  B_mem : ∀ g, ψB g ∈ N
  mem_JA : ∀ g, ψA g ∈ JA
  mem_JB : ∀ g, ψB g ∈ JB

theorem Nbhd3Hyp.reduce (h : Nbhd3Hyp H c y JA JB) {P : Subgroup H} (hPl : P ≤ layer H) (hP1 : P ≠ ⊥) :
    ∃ (N : Subgroup H) (ψA ψB : Q8 →* H), Q3Red H c y JA JB N ψA ψB ∧
      ((∀ g, ψA g ∈ CFSG.pCore 2 H) ∨
        ((∀ g ∈ JA, (∃ k : ℕ, g ^ (2 ^ k) = 1) → g ∈ N) ∧
          (∀ g ∈ JB, (∃ k : ℕ, g ^ (2 ^ k) = 1) → g ∈ N))) := by
  obtain ⟨ψA, hAi, hAm, hAz⟩ := h.q8A
  obtain ⟨ψB, hBi, hBm, hBz⟩ := h.q8B
  have hcomm : ∀ g g' : Q8, ψA g * ψB g' = ψB g' * ψA g := fun g g' => h.comm _ (hAm g) _ (hBm g')
  rcases h.balB with hB | ⟨N, hN, hBraw⟩
  · exfalso
    have hy : y ∈ CFSG.pCore 2 H := hBz ▸ hB _ (hBm _) (two_elt_q8 _)
    have hlay : layer H ≤ centralizer ({c * y} : Set H) := by
      intro g hg
      rw [h.mem_cent_iff]
      exact Subgroup.mem_centralizer_iff.1 (pCore_two_le_centralizer_layer hy) g hg
    have hbot := h.perfect_free _ layer_perfect hlay
    exact hP1 (le_bot_iff.mp (hbot ▸ hPl))
  · have hBN : ∀ g, ψB g ∈ N := fun g => hBraw _ (hBm g) (two_elt_q8 g)
    have hyN : y ∈ N := hBz ▸ hBN _
    have only : ∀ K, IsComponent K → K = N := fun K hK => h.comp_eq_of_mem hN hK hyN
    have hlayer : layer H = N := by
      have := nb_layer_eq_of_components hN hN (fun K hK => Or.inl (only K hK))
      rwa [sup_idem] at this
    refine ⟨N, ψA, ψB, ⟨hN, only, hlayer, hAi, hBi, hAz, hBz, hcomm, hBN, hAm, hBm⟩, ?_⟩
    rcases h.balA with hA | ⟨N', hN', hAraw⟩
    · exact Or.inl fun g => hA _ (hAm g) (two_elt_q8 g)
    · have : N' = N := only N' hN'
      exact Or.inr ⟨this ▸ hAraw, hBraw⟩

end CFSG.GH74.Generic.S1.Exo

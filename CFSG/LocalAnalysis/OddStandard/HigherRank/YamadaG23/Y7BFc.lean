module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54Card
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3A2

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : Setting3 G L}
  {e : Setting3.Ext s}

private theorem perm3_centralizer :
    ∀ a g : Equiv.Perm (Fin 3), a * a = 1 → a ≠ 1 → g * a = a * g → g = 1 ∨ g = a := by
  decide

private theorem normalizer_perm3_eq_self (H : Subgroup (Equiv.Perm (Fin 3)))
    (hcard : Nat.card ↥H = 2) : Subgroup.normalizer (H : Set (Equiv.Perm (Fin 3))) = H := by
  refine le_antisymm ?_ Subgroup.le_normalizer
  obtain ⟨b, hb1, hb⟩ := (Nat.card_eq_two_iff' (1 : ↥H)).mp hcard
  intro g hg
  have hbne : (b : Equiv.Perm (Fin 3)) ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hbsq : (b : Equiv.Perm (Fin 3)) * (b : Equiv.Perm (Fin 3)) = 1 := by
    have hord : orderOf b ∣ 2 := by
      have h := orderOf_dvd_natCard b
      rwa [hcard] at h
    have hne : orderOf b ≠ 1 := by
      intro h
      exact hbne (Subtype.ext_iff.mp (orderOf_eq_one_iff.mp h))
    rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
    · exact absurd h hne
    · have hpow := pow_orderOf_eq_one b
      rw [h] at hpow
      simpa [pow_two] using congrArg (fun z : ↥H => ((z : Equiv.Perm (Fin 3)))) hpow
  have hconj : g * (b : Equiv.Perm (Fin 3)) * g⁻¹ ∈ H :=
    (Subgroup.mem_normalizer_iff.mp hg (b : Equiv.Perm (Fin 3))).mp b.2
  have hconj' : g * (b : Equiv.Perm (Fin 3)) * g⁻¹ = (b : Equiv.Perm (Fin 3)) := by
    have hne1 : (⟨g * (b : Equiv.Perm (Fin 3)) * g⁻¹, hconj⟩ : ↥H) ≠ 1 := by
      intro h1
      apply hbne
      have hval : g * (b : Equiv.Perm (Fin 3)) * g⁻¹ = 1 := by
        have h := congrArg (fun z : ↥H => ((z : Equiv.Perm (Fin 3)))) h1
        simpa using h
      calc (b : Equiv.Perm (Fin 3)) =
          g⁻¹ * (g * (b : Equiv.Perm (Fin 3)) * g⁻¹) * g := by group
        _ = 1 := by rw [hval]; group
    exact congrArg (fun z : ↥H => ((z : Equiv.Perm (Fin 3)))) (hb ⟨_, hconj⟩ hne1)
  have hcomm : g * (b : Equiv.Perm (Fin 3)) = (b : Equiv.Perm (Fin 3)) * g := by
    calc g * (b : Equiv.Perm (Fin 3)) =
        (g * (b : Equiv.Perm (Fin 3)) * g⁻¹) * g := by group
      _ = (b : Equiv.Perm (Fin 3)) * g := by rw [hconj']
  rcases perm3_centralizer (b : Equiv.Perm (Fin 3)) g hbsq hbne hcomm with h | h
  · rw [h]; exact H.one_mem
  · rw [h]; exact b.2

theorem y7b_NL_S (hH : F33Hyp s e) : normIn L s.fr.S = s.fr.S := by
  classical
  have hzL : zL L = ⊥ := f3_zL_eq_bot hH
  have hperm3 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hB_le_N : s.fr.B ≤ normIn L s.fr.B := by
    rw [normIn]
    exact le_inf ((s3_B_le_S s).trans (s3_S_le_L s)) Subgroup.le_normalizer
  have hS_le_N : s.fr.S ≤ normIn L s.fr.B := by
    rw [normIn]
    exact le_inf (s3_S_le_L s) (fun x hx => f3_B_char hH x (Subgroup.le_normalizer hx))
  have hSec : SecProp (normIn L s.fr.B) (s.fr.B)
      (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) := by
    have h := hH.hLF.fact18.2.1.2.2.1
    simpa only [hzL, bot_sup_eq] using h
  obtain ⟨hBn, ⟨iso⟩⟩ := hSec
  haveI := hBn
  let π : ↥(normIn L s.fr.B) →* Equiv.Perm (Fin 3) :=
    iso.toMonoidHom.comp (QuotientGroup.mk' (s.fr.B.subgroupOf (normIn L s.fr.B)))
  have hπsurj : Function.Surjective π := by
    intro σ
    obtain ⟨q, hq⟩ := iso.surjective σ
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨y, by simpa [π] using hq⟩
  have hker : π.ker = s.fr.B.subgroupOf (normIn L s.fr.B) := by
    ext y
    simp [π, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have hcard_B : Nat.card ↥(s.fr.B.subgroupOf (normIn L s.fr.B)) = 32 := by
    rw [← Subgroup.card_subtype (normIn L s.fr.B)
        (s.fr.B.subgroupOf (normIn L s.fr.B)),
      Subgroup.map_subgroupOf_eq_of_le hB_le_N, y54_card_B hH]
  have hcard_S : Nat.card ↥(s.fr.S.subgroupOf (normIn L s.fr.B)) = 64 := by
    rw [← Subgroup.card_subtype (normIn L s.fr.B)
        (s.fr.S.subgroupOf (normIn L s.fr.B)),
      Subgroup.map_subgroupOf_eq_of_le hS_le_N, y54_card_S hH]
  have hq : Nat.card (↥(normIn L s.fr.B) ⧸ s.fr.B.subgroupOf (normIn L s.fr.B)) = 6 := by
    rw [Nat.card_congr iso.toEquiv, hperm3]
  have hcard_N : Nat.card ↥(normIn L s.fr.B) = 192 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (s.fr.B.subgroupOf (normIn L s.fr.B)), hq, hcard_B]
  have hidx_S : (s.fr.S.subgroupOf (normIn L s.fr.B)).index = 3 := by
    have h := Subgroup.card_mul_index (s.fr.S.subgroupOf (normIn L s.fr.B))
    rw [hcard_S, hcard_N] at h
    omega
  have hker_le : π.ker ≤ s.fr.S.subgroupOf (normIn L s.fr.B) := by
    rw [hker]
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (s3_B_le_S s (Subgroup.mem_subgroupOf.mp hx))
  have hTcard : Nat.card ↥((s.fr.S.subgroupOf (normIn L s.fr.B)).map π) = 2 := by
    have hidx : ((s.fr.S.subgroupOf (normIn L s.fr.B)).map π).index = 3 := by
      rw [Subgroup.index_map_eq (s.fr.S.subgroupOf (normIn L s.fr.B)) hπsurj hker_le, hidx_S]
    have h := Subgroup.card_mul_index ((s.fr.S.subgroupOf (normIn L s.fr.B)).map π)
    rw [hidx, hperm3] at h
    omega
  have hself : Subgroup.normalizer
      (((s.fr.S.subgroupOf (normIn L s.fr.B)).map π : Subgroup (Equiv.Perm (Fin 3))) :
        Set (Equiv.Perm (Fin 3))) = (s.fr.S.subgroupOf (normIn L s.fr.B)).map π :=
    normalizer_perm3_eq_self _ hTcard
  refine le_antisymm ?_ ?_
  · intro n hn
    rw [normIn, Subgroup.mem_inf] at hn
    have hnL : n ∈ L := hn.1
    have hnNorm : n ∈ Subgroup.normalizer (s.fr.S : Set G) := hn.2
    have hnN : n ∈ normIn L s.fr.B := by
      rw [normIn]
      exact Subgroup.mem_inf.mpr ⟨hnL, f3_B_char hH n hnNorm⟩
    let X : ↥(normIn L s.fr.B) := ⟨n, hnN⟩
    have hX_norm : X ∈ Subgroup.normalizer (s.fr.S.subgroupOf (normIn L s.fr.B)) := by
      have hle : (normIn L s.fr.S).subgroupOf (normIn L s.fr.B) ≤
          Subgroup.normalizer (s.fr.S.subgroupOf (normIn L s.fr.B)) := by
        rw [← Subgroup.subgroupOf_normalizer_eq hS_le_N]
        exact Subgroup.subgroupOf_mono _ (by rw [normIn]; exact inf_le_right)
      exact hle (Subgroup.mem_subgroupOf.mpr (by
        rw [normIn, Subgroup.mem_inf]
        exact ⟨hnL, hnNorm⟩))
    have hπX_norm : π X ∈ Subgroup.normalizer
        (((s.fr.S.subgroupOf (normIn L s.fr.B)).map π : Subgroup (Equiv.Perm (Fin 3))) :
          Set (Equiv.Perm (Fin 3))) :=
      Subgroup.le_normalizer_map π (Subgroup.mem_map.mpr ⟨X, hX_norm, rfl⟩)
    rw [hself] at hπX_norm
    obtain ⟨t, ht, hφt⟩ := Subgroup.mem_map.mp hπX_norm
    have hker_mem : t⁻¹ * X ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hφt, inv_mul_cancel]
    rw [hker] at hker_mem
    have htS : (t : G) ∈ s.fr.S := Subgroup.mem_subgroupOf.mp ht
    have hb : (t : G)⁻¹ * n ∈ s.fr.B := by
      simpa [X] using Subgroup.mem_subgroupOf.mp hker_mem
    have hn_eq : n = (t : G) * ((t : G)⁻¹ * n) := by group
    rw [hn_eq]
    exact s.fr.S.mul_mem htS (s3_B_le_S s hb)
  · intro x hx
    rw [normIn]
    exact Subgroup.mem_inf.mpr ⟨s3_S_le_L s hx, Subgroup.le_normalizer hx⟩

end CFSG.OddStandard.HigherRank.YamadaG23

module

public import CFSG.LocalAnalysis.EvenBN.U4.LayersTwoGMS
public import CFSG.LocalAnalysis.EvenBN.U4.Layers
import CFSG.LocalAnalysis.EvenBN.GMSK.ConsumerSections
import CFSG.LocalAnalysis.EvenBN.Common.SL2Center

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped MatrixGroups

@[expose] noncomputable def miyamotoM2G {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    {G : Type} [Group G] (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K)) (t : G)
    (Q : Subgroup G) : Subgroup G :=
  (normalClosure (((miyamotoN2G h L η).subgroupOf (miyamotoH2G h L η t Q) :
    Subgroup (miyamotoH2G h L η t Q)) : Set (miyamotoH2G h L η t Q))).map
      (miyamotoH2G h L η t Q).subtype

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem sec3_12_two (hS : Setting h L η t Q T) :
    miyamotoM2G h L η t Q ≤ miyamotoH2G h L η t Q ∧
      miyamotoH2G h L η t Q ≤ normalizer (miyamotoM2G h L η t Q : Set G) ∧
      miyamotoN2G h L η ≤ miyamotoM2G h L η t Q ∧
      ⁅miyamotoM2G h L η t Q, miyamotoM2G h L η t Q⁆ = miyamotoM2G h L η t Q ∧
      miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G) ≤ miyamotoM2G h L η t Q ∧
      Odd (Nat.card (center (miyamotoM2G h L η t Q))) ∧
      Xor
        (∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = 2 ^ f ∧
          ∃ (ψ : miyamotoM2G h L η t Q ⧸ center (miyamotoM2G h L η t Q) ≃* SL(2, k) × SL(2, k))
            (α : miyamotoN2G h L η ≃* SL(2, k)),
            (∀ (a : miyamotoN2G h L η) (x : miyamotoM2G h L η t Q), (x : G) = a →
              ψ (x : miyamotoM2G h L η t Q ⧸ center (miyamotoM2G h L η t Q)) = (α a, α a)) ∧
            ∀ (x y : miyamotoM2G h L η t Q) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
              ψ (x : miyamotoM2G h L η t Q ⧸ center (miyamotoM2G h L η t Q)) = (y₁, y₂) →
                ψ (y : miyamotoM2G h L η t Q ⧸ center (miyamotoM2G h L η t Q)) = (y₂, y₁))
        (∃ (k₂ : Type) (_ : Field k₂) (_ : Fintype k₂), Fintype.card k₂ = (2 ^ f) ^ 2 ∧
          ∃ ψ : miyamotoM2G h L η t Q ⧸ center (miyamotoM2G h L η t Q) ≃* SL(2, k₂),
            (∀ x y : miyamotoM2G h L η t Q, (y : G) = t⁻¹ * x * t →
              ((ψ (y : miyamotoM2G h L η t Q ⧸ center (miyamotoM2G h L η t Q)) : SL(2, k₂)) :
                Matrix (Fin 2) (Fin 2) k₂) =
                (ψ (x : miyamotoM2G h L η t Q ⧸ center (miyamotoM2G h L η t Q)) :
                  Matrix (Fin 2) (Fin 2) k₂).map (fun c => c ^ 2 ^ f)) ∧
            ∀ g : SL(2, k₂),
              g ∈ (((miyamotoN2G h L η).subgroupOf (miyamotoM2G h L η t Q)).map
                  (QuotientGroup.mk' (center (miyamotoM2G h L η t Q)))).map ψ.toMonoidHom ↔
                ∀ i j, (g : Matrix (Fin 2) (Fin 2) k₂) i j ^ 2 ^ f =
                  (g : Matrix (Fin 2) (Fin 2) k₂) i j) ∧
      Odd (Nat.card (miyamotoH2G h L η t Q ⊓
        centralizer (miyamotoM2G h L η t Q : Set G) : Subgroup G)) := by
  have : CharP K 2 := h.charP
  set Hs := miyamotoH2G h L η t Q with hHs
  have hNH : miyamotoN2G h L η ≤ Hs := hS.N2G_le_H2
  have key := GMS.gms_linear_local_normal_closure_of_fieldBound
    hS.gmsLinearLocalApplication_tupleTwo hS.localFieldBound_tupleTwo
  obtain ⟨-, -, -, -, -, hCX, hperf, hZ, -, hXor, -⟩ := key
  set A : Subgroup Hs := (miyamotoN2G h L η).subgroupOf Hs with hA
  set X : Subgroup Hs := normalClosure (A : Set Hs) with hX
  set R := CFSG.Open.standardComponentOddCore Hs with hR
  have hM : miyamotoM2G h L η t Q = X.map Hs.subtype := rfl
  have hRodd : Odd (Nat.card R) := GMSK.odd_card_standardComponentOddCore Hs
  have hMH : miyamotoM2G h L η t Q ≤ Hs := by
    rw [hM]
    exact map_subtype_le X
  have hHN : Hs ≤ normalizer (miyamotoM2G h L η t Q : Set G) := by
    intro g hg
    refine mem_normalizer_fintype fun m hm => ?_
    rw [SetLike.mem_coe, hM] at hm ⊢
    obtain ⟨x, hx, rfl⟩ := hm
    refine ⟨⟨g, hg⟩ * x * ⟨g, hg⟩⁻¹,
      (normalClosure_normal (s := (A : Set Hs))).conj_mem x hx ⟨g, hg⟩, ?_⟩
    simp
  have hNM : miyamotoN2G h L η ≤ miyamotoM2G h L η t Q := by
    intro n hn
    rw [hM]
    exact ⟨⟨n, hNH hn⟩, subset_normalClosure (mem_subgroupOf.2 hn), rfl⟩
  have hXX : ⁅X, X⁆ = X := by
    have h1 : commutator X = ⊤ := hperf.commutator_eq_top
    have h2 := congrArg (Subgroup.map X.subtype) h1
    rwa [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at h2
  have hMM : ⁅miyamotoM2G h L η t Q, miyamotoM2G h L η t Q⁆ = miyamotoM2G h L η t Q := by
    rw [hM, ← map_commutator, hXX]
  have hVM : miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G) ≤
      miyamotoM2G h L η t Q :=
    hS.V2_le_of_le (hS.rootB_le_N2G.trans hNM) (hS.IN2G_le_N2G.trans hNM)
      (hS.V2_le_H2.trans hHN)
  let e₀ : X ≃* miyamotoM2G h L η t Q :=
    Subgroup.equivMapOfInjective X Hs.subtype Hs.subtype_injective
  have hZodd : Odd (Nat.card (center (miyamotoM2G h L η t Q))) := by
    rw [← Nat.card_congr (Subgroup.centerCongr e₀).toEquiv,
      ← card_map_of_injective X.subtype_injective, hZ]
    exact Odd.of_dvd_nat hRodd (card_dvd_of_le inf_le_right)
  have hXor' := xor_map_subtype (X := X) hNH hS.t_mem_H2 (n := f) (by have := hS.two_le; omega)
    hXor.or
  have hCodd : Odd (Nat.card (Hs ⊓ centralizer (miyamotoM2G h L η t Q : Set G) :
      Subgroup G)) := by
    have hsub : (miyamotoM2G h L η t Q).subgroupOf Hs = X := by
      rw [hM]
      exact comap_map_eq_self_of_injective Hs.subtype_injective X
    rw [← card_subgroupOf_of_le (inf_le_left : Hs ⊓ centralizer
      (miyamotoM2G h L η t Q : Set G) ≤ Hs), inf_subgroupOf_left, ← centralizer_subgroupOf hMH,
      hsub, hCX]
    exact hRodd
  exact ⟨hMH, hHN, hNM, hMM, hVM, hZodd, hXor', hCodd⟩

theorem sec3_12_two_center (hS : Setting h L η t Q T) (hf : 3 ≤ f) :
    center (miyamotoM2G h L η t Q) = ⊥ := by
  obtain ⟨-, -, -, hMM, -, -, hXor, -⟩ := hS.sec3_12_two
  have : Group.IsPerfect (miyamotoM2G h L η t Q) := by
    refine ⟨?_⟩
    apply Subgroup.map_injective (miyamotoM2G h L η t Q).subtype_injective
    rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype, hMM]
  have h8 : 8 ≤ 2 ^ f := (Nat.pow_le_pow_right (by norm_num) hf).trans_eq' (by norm_num)
  have hev : ∀ m : ℕ, 1 ≤ m → (2 ^ f) ^ m ≠ 9 := fun m hm e => by
    have : Even ((2 ^ f) ^ m) :=
      Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, by omega⟩, by omega⟩
    rw [e] at this
    exact absurd this (by decide)
  rcases hXor.or with ⟨k, _, _, hk, ψ, -⟩ | ⟨k₂, _, _, hk₂, ψ, -⟩
  · refine Common.center_eq_bot_of_sl2_prod ?_ ?_ ψ <;> rw [Nat.card_eq_fintype_card, hk]
    · omega
    · simpa using hev 1 le_rfl
  · refine Common.center_eq_bot_of_sl2 ?_ ?_ ψ <;> rw [Nat.card_eq_fintype_card, hk₂]
    · nlinarith
    · exact hev 2 (by norm_num)

end Setting

end CFSG.LocalAnalysis.EvenBN.U4

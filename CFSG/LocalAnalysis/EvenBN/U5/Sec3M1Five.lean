module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3M1Four
public import CFSG.LocalAnalysis.EvenBN.U4.Layers
import CFSG.LocalAnalysis.EvenBN.Common.SL2Center

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.U5K.Hyp
open scoped MatrixGroups

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

@[expose] noncomputable def M₁ (d : Data G h) : Subgroup G :=
  (normalClosure ((d.N₁.subgroupOf (centralizer (d.I₁ : Set G)) :
    Subgroup (centralizer (d.I₁ : Set G))) : Set (centralizer (d.I₁ : Set G)))).map
    (centralizer (d.I₁ : Set G)).subtype

section Certified

theorem Hyp.sec3_5_three (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hf : 3 ≤ f) :
    d.M₁ ≤ centralizer (d.I₁ : Set G) ∧
      centralizer (d.I₁ : Set G) ≤ normalizer (d.M₁ : Set G) ∧
      d.N₁ ≤ d.M₁ ∧ ⁅d.M₁, d.M₁⁆ = d.M₁ ∧
      Odd (Nat.card (center d.M₁)) ∧ center d.M₁ = ⊥ ∧
      Xor
        (∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = (2 ^ f) ^ 2 ∧
          ∃ (ψ : d.M₁ ⧸ center d.M₁ ≃* SL(2, k) × SL(2, k)) (α : d.N₁ ≃* SL(2, k)),
            (∀ (a : d.N₁) (x : d.M₁), (x : G) = a →
              ψ (x : d.M₁ ⧸ center d.M₁) = (α a, α a)) ∧
            ∀ (x y : d.M₁) (y₁ y₂ : SL(2, k)), (y : G) = d.t⁻¹ * x * d.t →
              ψ (x : d.M₁ ⧸ center d.M₁) = (y₁, y₂) → ψ (y : d.M₁ ⧸ center d.M₁) = (y₂, y₁))
        (∃ (k₂ : Type) (_ : Field k₂) (_ : Fintype k₂), Fintype.card k₂ = ((2 ^ f) ^ 2) ^ 2 ∧
          ∃ ψ : d.M₁ ⧸ center d.M₁ ≃* SL(2, k₂),
            (∀ x y : d.M₁, (y : G) = d.t⁻¹ * x * d.t →
              ((ψ (y : d.M₁ ⧸ center d.M₁) : SL(2, k₂)) : Matrix (Fin 2) (Fin 2) k₂) =
                (ψ (x : d.M₁ ⧸ center d.M₁) : Matrix (Fin 2) (Fin 2) k₂).map
                  (fun c => c ^ (2 ^ f) ^ 2)) ∧
            ∀ g : SL(2, k₂),
              g ∈ ((d.N₁.subgroupOf d.M₁).map (QuotientGroup.mk' (center d.M₁))).map
                  ψ.toMonoidHom ↔
                ∀ i j, (g : Matrix (Fin 2) (Fin 2) k₂) i j ^ (2 ^ f) ^ 2 =
                  (g : Matrix (Fin 2) (Fin 2) k₂) i j) ∧
      Odd (Nat.card (centralizer (d.I₁ : Set G) ⊓ centralizer (d.M₁ : Set G) : Subgroup G)) := by
  have : CharP K 2 := h.charP
  set Hs := centralizer (d.I₁ : Set G) with hHs
  have hNH : d.N₁ ≤ Hs := d.N₁_le_centralizer_I₁
  have key := GMS.gms_linear_local_normal_closure_of_fieldBound
    (hd.gmsLinearLocalApplication_one hGMS) (hd.localFieldBound_one hf)
  obtain ⟨-, -, -, -, -, hCX, hperf, hZ, -, hXor, -⟩ := key
  set A : Subgroup Hs := d.N₁.subgroupOf Hs with hA
  set X : Subgroup Hs := normalClosure (A : Set Hs) with hX
  set R := CFSG.Open.standardComponentOddCore Hs with hR
  have hM : d.M₁ = X.map Hs.subtype := rfl
  have hRodd : Odd (Nat.card R) := GMSK.odd_card_standardComponentOddCore Hs
  have hMH : d.M₁ ≤ Hs := by
    rw [hM]
    exact map_subtype_le X
  have hHN : Hs ≤ normalizer (d.M₁ : Set G) := by
    intro g hg
    refine mem_normalizer_fintype fun m hm => ?_
    rw [SetLike.mem_coe, hM] at hm ⊢
    obtain ⟨x, hx, rfl⟩ := hm
    refine ⟨⟨g, hg⟩ * x * ⟨g, hg⟩⁻¹,
      (normalClosure_normal (s := (A : Set Hs))).conj_mem x hx ⟨g, hg⟩, ?_⟩
    simp
  have hNM : d.N₁ ≤ d.M₁ := by
    intro n hn
    rw [hM]
    exact ⟨⟨n, hNH hn⟩, subset_normalClosure (mem_subgroupOf.2 hn), rfl⟩
  have hXX : ⁅X, X⁆ = X := by
    have h1 : commutator X = ⊤ := hperf.commutator_eq_top
    have h2 := congrArg (Subgroup.map X.subtype) h1
    rwa [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at h2
  have hMM : ⁅d.M₁, d.M₁⁆ = d.M₁ := by
    rw [hM, ← map_commutator, hXX]
  let e₀ : X ≃* d.M₁ := Subgroup.equivMapOfInjective X Hs.subtype Hs.subtype_injective
  have : Group.IsPerfect d.M₁ :=
    Group.IsPerfect.ofSurjective (f := e₀.toMonoidHom) e₀.surjective
  have hZodd : Odd (Nat.card (center d.M₁)) := by
    rw [← Nat.card_congr (Subgroup.centerCongr e₀).toEquiv,
      ← card_map_of_injective X.subtype_injective, hZ]
    exact Odd.of_dvd_nat hRodd (card_dvd_of_le inf_le_right)
  have hXor' := U4.xor_map_subtype (X := X) hNH hd.t_mem_centralizer_I₁ (n := 2 * f)
    (by have := hd.two_le; omega) hXor.or
  rw [show (2 : ℕ) ^ (2 * f) = (2 ^ f) ^ 2 by ring] at hXor'
  have hcard : ∀ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = (2 ^ f) ^ 2 ∨
      Fintype.card k = ((2 ^ f) ^ 2) ^ 2 → 5 ≤ Nat.card k ∧ Nat.card k ≠ 9 := by
    intro k _ _ hk
    have h4 := hd.four_le
    have hev : ∀ m : ℕ, Even ((2 ^ f) ^ m) → (2 ^ f) ^ m ≠ 9 := fun m hm e => by
      rw [e] at hm
      exact absurd hm (by decide)
    have h16 : 16 ≤ (2 ^ f) ^ 2 := by
      rw [sq]
      exact (Nat.mul_le_mul h4 h4).trans_eq' (by norm_num)
    have h256 : 16 ≤ ((2 ^ f) ^ 2) ^ 2 := by
      rw [sq ((2 ^ f) ^ 2)]
      exact h16.trans (Nat.le_mul_of_pos_right _ (by omega))
    rw [Nat.card_eq_fintype_card]
    rcases hk with hk | hk <;> rw [hk]
    · refine ⟨by omega, hev 2 ((Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two,
        by have := hd.two_le; omega⟩, by norm_num⟩))⟩
    · refine ⟨by omega, ?_⟩
      rw [← pow_mul]
      exact hev _ (Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, by have := hd.two_le; omega⟩,
        by norm_num⟩)
  have hZbot : center d.M₁ = ⊥ := by
    rcases hXor'.or with ⟨k, _, _, hk, ψ, -⟩ | ⟨k₂, _, _, hk₂, ψ, -⟩
    · obtain ⟨h5, h9⟩ := hcard k inferInstance inferInstance (Or.inl hk)
      exact Common.center_eq_bot_of_sl2_prod h5 h9 ψ
    · obtain ⟨h5, h9⟩ := hcard k₂ inferInstance inferInstance (Or.inr hk₂)
      exact Common.center_eq_bot_of_sl2 h5 h9 ψ
  have hCodd : Odd (Nat.card (Hs ⊓ centralizer (d.M₁ : Set G) : Subgroup G)) := by
    have hsub : d.M₁.subgroupOf Hs = X := by
      rw [hM]
      exact comap_map_eq_self_of_injective Hs.subtype_injective X
    rw [← U4.card_subgroupOf_of_le (inf_le_left : Hs ⊓ centralizer
      (d.M₁ : Set G) ≤ Hs), inf_subgroupOf_left, ← U4.centralizer_subgroupOf hMH, hsub, hCX]
    exact hRodd
  exact ⟨hMH, hHN, hNM, hMM, hZodd, hZbot, hXor', hCodd⟩

end Certified

end Data

end CFSG.LocalAnalysis.EvenBN.U5

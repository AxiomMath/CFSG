module

public import CFSG.LocalAnalysis.EvenBN.U4.LayersGMS
public import CFSG.LocalAnalysis.EvenBN.GMS.NormalClosure
import CFSG.LocalAnalysis.EvenBN.GMSK.ConsumerSections
import CFSG.LocalAnalysis.EvenBN.Common.SL2Center

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped MatrixGroups

@[expose] noncomputable def miyamotoM1G {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    {G : Type} [Group G] (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K)) (t : G) :
    Subgroup G :=
  (normalClosure (((miyamotoN1G h L η).subgroupOf (miyamotoH1G h L η t) :
    Subgroup (miyamotoH1G h L η t)) : Set (miyamotoH1G h L η t))).map
      (miyamotoH1G h L η t).subtype

section Transport

variable {G : Type*} [Group G] {Hs B : Subgroup G} {X : Subgroup Hs} {t : G} {n : ℕ}

theorem xor_map_subtype (hB : B ≤ Hs) (ht : t ∈ Hs) (hn : 1 ≤ n)
    (hor : (∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = 2 ^ n ∧
        ∃ (ψ : X ⧸ center X ≃* SL(2, k) × SL(2, k)) (α : B.subgroupOf Hs ≃* SL(2, k)),
          (∀ (a : B.subgroupOf Hs) (x : X), (x : Hs) = a →
            ψ (x : X ⧸ center X) = (α a, α a)) ∧
          ∀ (x y : X) (y₁ y₂ : SL(2, k)), (y : Hs) = (⟨t, ht⟩ : Hs)⁻¹ * x * ⟨t, ht⟩ →
            ψ (x : X ⧸ center X) = (y₁, y₂) → ψ (y : X ⧸ center X) = (y₂, y₁)) ∨
      (∃ (k₂ : Type) (_ : Field k₂) (_ : Fintype k₂), Fintype.card k₂ = (2 ^ n) ^ 2 ∧
        ∃ ψ : X ⧸ center X ≃* SL(2, k₂),
          (∀ x y : X, (y : Hs) = (⟨t, ht⟩ : Hs)⁻¹ * x * ⟨t, ht⟩ →
            ((ψ (y : X ⧸ center X) : SL(2, k₂)) : Matrix (Fin 2) (Fin 2) k₂) =
              (ψ (x : X ⧸ center X) : Matrix (Fin 2) (Fin 2) k₂).map (fun c => c ^ 2 ^ n)) ∧
          ∀ g : SL(2, k₂),
            g ∈ (((B.subgroupOf Hs).subgroupOf X).map (QuotientGroup.mk' (center X))).map
                ψ.toMonoidHom ↔
              ∀ i j, (g : Matrix (Fin 2) (Fin 2) k₂) i j ^ 2 ^ n =
                (g : Matrix (Fin 2) (Fin 2) k₂) i j)) :
    Xor
      (∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = 2 ^ n ∧
        ∃ (ψ : X.map Hs.subtype ⧸ center (X.map Hs.subtype) ≃* SL(2, k) × SL(2, k))
          (α : B ≃* SL(2, k)),
          (∀ (a : B) (x : X.map Hs.subtype), (x : G) = a →
            ψ (x : X.map Hs.subtype ⧸ center (X.map Hs.subtype)) = (α a, α a)) ∧
          ∀ (x y : X.map Hs.subtype) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
            ψ (x : X.map Hs.subtype ⧸ center (X.map Hs.subtype)) = (y₁, y₂) →
              ψ (y : X.map Hs.subtype ⧸ center (X.map Hs.subtype)) = (y₂, y₁))
      (∃ (k₂ : Type) (_ : Field k₂) (_ : Fintype k₂), Fintype.card k₂ = (2 ^ n) ^ 2 ∧
        ∃ ψ : X.map Hs.subtype ⧸ center (X.map Hs.subtype) ≃* SL(2, k₂),
          (∀ x y : X.map Hs.subtype, (y : G) = t⁻¹ * x * t →
            ((ψ (y : X.map Hs.subtype ⧸ center (X.map Hs.subtype)) : SL(2, k₂)) :
              Matrix (Fin 2) (Fin 2) k₂) =
              (ψ (x : X.map Hs.subtype ⧸ center (X.map Hs.subtype)) :
                Matrix (Fin 2) (Fin 2) k₂).map (fun c => c ^ 2 ^ n)) ∧
          ∀ g : SL(2, k₂),
            g ∈ ((B.subgroupOf (X.map Hs.subtype)).map
                (QuotientGroup.mk' (center (X.map Hs.subtype)))).map ψ.toMonoidHom ↔
              ∀ i j, (g : Matrix (Fin 2) (Fin 2) k₂) i j ^ 2 ^ n =
                (g : Matrix (Fin 2) (Fin 2) k₂) i j) := by
  set M := X.map Hs.subtype with hMdef
  let e₀ : X ≃* M := Subgroup.equivMapOfInjective X Hs.subtype Hs.subtype_injective
  have he₀ : ∀ x : X, ((e₀ x : M) : G) = ((x : Hs) : G) := fun _ => rfl
  have he₀s : ∀ y : M, (((e₀.symm y : X) : Hs) : G) = (y : G) := fun y => by
    rw [← he₀, MulEquiv.apply_symm_apply]
  let q : X ⧸ center X ≃* M ⧸ center M :=
    QuotientGroup.congr (center X) (center M) e₀ (map_center_eq e₀)
  have hqs : ∀ y : M, q.symm (y : M ⧸ center M) = (e₀.symm y : X ⧸ center X) := fun y => by
    rw [MulEquiv.symm_apply_eq, QuotientGroup.congr_mk, MulEquiv.apply_symm_apply]
  have htrel : ∀ x y : M, (y : G) = t⁻¹ * x * t →
      ((e₀.symm y : X) : Hs) = (⟨t, ht⟩ : Hs)⁻¹ * (e₀.symm x : X) * ⟨t, ht⟩ := by
    intro x y hxy
    apply Subtype.ext
    simp only [coe_mul, coe_inv, he₀s]
    exact hxy
  have hBrel : ∀ (a : B) (x : M), (x : G) = a →
      ((e₀.symm x : X) : Hs) = ((subgroupOfEquivOfLe hB).symm a : B.subgroupOf Hs) := by
    intro a x hxa
    apply Subtype.ext
    rw [he₀s, hxa]
    rfl
  have hsub : ((B.subgroupOf Hs).subgroupOf X).map e₀.toMonoidHom = B.subgroupOf M := by
    ext y
    rw [mem_map_equiv, mem_subgroupOf, mem_subgroupOf, mem_subgroupOf, he₀s]
  have hcomp : q.toMonoidHom.comp (QuotientGroup.mk' (center X)) =
      (QuotientGroup.mk' (center M)).comp e₀.toMonoidHom := by
    ext x
    exact QuotientGroup.congr_mk (center X) (center M) e₀ (map_center_eq e₀) x
  have hsubq : (((B.subgroupOf Hs).subgroupOf X).map (QuotientGroup.mk' (center X))).map
      q.toMonoidHom = (B.subgroupOf M).map (QuotientGroup.mk' (center M)) := by
    rw [map_map, hcomp, ← map_map, hsub]
  have hexcl : ∀ (k : Type) (_ : Field k) (_ : Fintype k) (k₂ : Type) (_ : Field k₂)
      (_ : Fintype k₂), Fintype.card k₂ = (2 ^ n) ^ 2 →
      (M ⧸ center M ≃* SL(2, k) × SL(2, k)) → (M ⧸ center M ≃* SL(2, k₂)) → False := by
    intro k _ _ k₂ _ _ hk₂ ψ₁ ψ₂
    have hk₂' : Nat.card k₂ = 2 ^ (2 * n) := by
      rw [Nat.card_eq_fintype_card, hk₂, ← pow_mul, mul_comm]
    exact (GMS.isEmpty_mulEquiv_sl2_prod (k := k) (by omega) hk₂').false (ψ₂.symm.trans ψ₁)
  rcases hor with ⟨k, _, _, hk, ψ, α, hψA, hψt⟩ | ⟨k₂, _, _, hk₂, ψ, hψt, hψA⟩
  · refine Or.inl ⟨⟨k, inferInstance, inferInstance, hk, q.symm.trans ψ,
      (subgroupOfEquivOfLe hB).symm.trans α, fun a x hxa => ?_, fun x y y₁ y₂ hxy hx => ?_⟩, ?_⟩
    · rw [MulEquiv.trans_apply, hqs, MulEquiv.trans_apply]
      exact hψA _ _ (hBrel a x hxa)
    · rw [MulEquiv.trans_apply, hqs] at hx ⊢
      exact hψt _ _ y₁ y₂ (htrel x y hxy) hx
    · rintro ⟨k₂, _, _, hk₂, ψ₂, -⟩
      exact hexcl k inferInstance inferInstance k₂ inferInstance inferInstance hk₂
        (q.symm.trans ψ) ψ₂
  · refine Or.inr ⟨⟨k₂, inferInstance, inferInstance, hk₂, q.symm.trans ψ,
      fun x y hxy => ?_, fun g => ?_⟩, ?_⟩
    · rw [MulEquiv.trans_apply, hqs, MulEquiv.trans_apply, hqs]
      exact hψt _ _ (htrel x y hxy)
    · rw [← hψA g, ← hsubq, map_map]
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨z, hz, ?_⟩
        simp
      · rintro ⟨z, hz, rfl⟩
        refine ⟨z, hz, ?_⟩
        simp
    · rintro ⟨k, _, _, -, ψ₁, -⟩
      exact hexcl k inferInstance inferInstance k₂ inferInstance inferInstance hk₂ ψ₁
        (q.symm.trans ψ)

end Transport

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}


theorem sec3_12_one (hS : Setting h L η t Q T) :
    miyamotoM1G h L η t ≤ miyamotoH1G h L η t ∧
      miyamotoH1G h L η t ≤ normalizer (miyamotoM1G h L η t : Set G) ∧
      miyamotoN1G h L η ≤ miyamotoM1G h L η t ∧
      ⁅miyamotoM1G h L η t, miyamotoM1G h L η t⁆ = miyamotoM1G h L η t ∧
      miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G) ≤ miyamotoM1G h L η t ∧
      Odd (Nat.card (center (miyamotoM1G h L η t))) ∧ center (miyamotoM1G h L η t) = ⊥ ∧
      Xor
        (∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = (2 ^ f) ^ 2 ∧
          ∃ (ψ : miyamotoM1G h L η t ⧸ center (miyamotoM1G h L η t) ≃* SL(2, k) × SL(2, k))
            (α : miyamotoN1G h L η ≃* SL(2, k)),
            (∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
              ψ (x : miyamotoM1G h L η t ⧸ center (miyamotoM1G h L η t)) = (α a, α a)) ∧
            ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
              ψ (x : miyamotoM1G h L η t ⧸ center (miyamotoM1G h L η t)) = (y₁, y₂) →
                ψ (y : miyamotoM1G h L η t ⧸ center (miyamotoM1G h L η t)) = (y₂, y₁))
        (∃ (k₂ : Type) (_ : Field k₂) (_ : Fintype k₂), Fintype.card k₂ = ((2 ^ f) ^ 2) ^ 2 ∧
          ∃ ψ : miyamotoM1G h L η t ⧸ center (miyamotoM1G h L η t) ≃* SL(2, k₂),
            (∀ x y : miyamotoM1G h L η t, (y : G) = t⁻¹ * x * t →
              ((ψ (y : miyamotoM1G h L η t ⧸ center (miyamotoM1G h L η t)) : SL(2, k₂)) :
                Matrix (Fin 2) (Fin 2) k₂) =
                (ψ (x : miyamotoM1G h L η t ⧸ center (miyamotoM1G h L η t)) :
                  Matrix (Fin 2) (Fin 2) k₂).map (fun c => c ^ (2 ^ f) ^ 2)) ∧
            ∀ g : SL(2, k₂),
              g ∈ (((miyamotoN1G h L η).subgroupOf (miyamotoM1G h L η t)).map
                  (QuotientGroup.mk' (center (miyamotoM1G h L η t)))).map ψ.toMonoidHom ↔
                ∀ i j, (g : Matrix (Fin 2) (Fin 2) k₂) i j ^ (2 ^ f) ^ 2 =
                  (g : Matrix (Fin 2) (Fin 2) k₂) i j) ∧
      Odd (Nat.card (miyamotoH1G h L η t ⊓
        centralizer (miyamotoM1G h L η t : Set G) : Subgroup G)) := by
  have : CharP K 2 := h.charP
  set Hs := miyamotoH1G h L η t with hHs
  have hNH : miyamotoN1G h L η ≤ Hs := hS.N1G_le_H1
  have key := GMS.gms_linear_local_normal_closure_of_fieldBound
    hS.gmsLinearLocalApplication_tupleOne hS.localFieldBound_tupleOne
  obtain ⟨-, -, -, -, -, hCX, hperf, hZ, -, hXor, -⟩ := key
  set A : Subgroup Hs := (miyamotoN1G h L η).subgroupOf Hs with hA
  set X : Subgroup Hs := normalClosure (A : Set Hs) with hX
  set R := CFSG.Open.standardComponentOddCore Hs with hR
  have hM : miyamotoM1G h L η t = X.map Hs.subtype := rfl
  have hRodd : Odd (Nat.card R) := GMSK.odd_card_standardComponentOddCore Hs
  have hMH : miyamotoM1G h L η t ≤ Hs := by
    rw [hM]
    exact map_subtype_le X
  have hHN : Hs ≤ normalizer (miyamotoM1G h L η t : Set G) := by
    intro g hg
    refine mem_normalizer_fintype fun m hm => ?_
    rw [SetLike.mem_coe, hM] at hm ⊢
    obtain ⟨x, hx, rfl⟩ := hm
    refine ⟨⟨g, hg⟩ * x * ⟨g, hg⟩⁻¹,
      (normalClosure_normal (s := (A : Set Hs))).conj_mem x hx ⟨g, hg⟩, ?_⟩
    simp
  have hNM : miyamotoN1G h L η ≤ miyamotoM1G h L η t := by
    intro n hn
    rw [hM]
    exact ⟨⟨n, hNH hn⟩, subset_normalClosure (mem_subgroupOf.2 hn), rfl⟩
  have hXX : ⁅X, X⁆ = X := by
    have h1 : commutator X = ⊤ := hperf.commutator_eq_top
    have h2 := congrArg (Subgroup.map X.subtype) h1
    rwa [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at h2
  have hMM : ⁅miyamotoM1G h L η t, miyamotoM1G h L η t⁆ = miyamotoM1G h L η t := by
    rw [hM, ← map_commutator, hXX]
  have hWM : miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G) ≤
      miyamotoM1G h L η t :=
    hS.W_le_of_le (hS.rootA_le_N1G.trans hNM) (hS.DG_le_N1G.trans hNM)
      (hS.W_le_H1.trans hHN)
  let e₀ : X ≃* miyamotoM1G h L η t :=
    Subgroup.equivMapOfInjective X Hs.subtype Hs.subtype_injective
  have : Group.IsPerfect (miyamotoM1G h L η t) :=
    Group.IsPerfect.ofSurjective (f := e₀.toMonoidHom) e₀.surjective
  have hZodd : Odd (Nat.card (center (miyamotoM1G h L η t))) := by
    rw [← Nat.card_congr (Subgroup.centerCongr e₀).toEquiv,
      ← card_map_of_injective X.subtype_injective, hZ]
    exact Odd.of_dvd_nat hRodd (card_dvd_of_le inf_le_right)
  have hXor' := xor_map_subtype (X := X) hNH hS.t_mem_H1 (n := 2 * f) (by have := hS.two_le; omega)
    hXor.or
  rw [show (2 : ℕ) ^ (2 * f) = (2 ^ f) ^ 2 by ring] at hXor'
  have hcard : ∀ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = (2 ^ f) ^ 2 ∨
      Fintype.card k = ((2 ^ f) ^ 2) ^ 2 → 5 ≤ Nat.card k ∧ Nat.card k ≠ 9 := by
    intro k _ _ hk
    have h4 := hS.four_le
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
        by have := hS.two_le; omega⟩, by norm_num⟩))⟩
    · refine ⟨by omega, ?_⟩
      rw [← pow_mul]
      exact hev _ (Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, by have := hS.two_le; omega⟩,
        by norm_num⟩)
  have hZbot : center (miyamotoM1G h L η t) = ⊥ := by
    rcases hXor'.or with ⟨k, _, _, hk, ψ, -⟩ | ⟨k₂, _, _, hk₂, ψ, -⟩
    · obtain ⟨h5, h9⟩ := hcard k inferInstance inferInstance (Or.inl hk)
      exact Common.center_eq_bot_of_sl2_prod h5 h9 ψ
    · obtain ⟨h5, h9⟩ := hcard k₂ inferInstance inferInstance (Or.inr hk₂)
      exact Common.center_eq_bot_of_sl2 h5 h9 ψ
  have hCodd : Odd (Nat.card (Hs ⊓ centralizer (miyamotoM1G h L η t : Set G) : Subgroup G)) := by
    have hsub : (miyamotoM1G h L η t).subgroupOf Hs = X := by
      rw [hM]
      exact comap_map_eq_self_of_injective Hs.subtype_injective X
    rw [← card_subgroupOf_of_le (inf_le_left : Hs ⊓ centralizer
      (miyamotoM1G h L η t : Set G) ≤ Hs), inf_subgroupOf_left, ← centralizer_subgroupOf hMH,
      hsub, hCX]
    exact hRodd
  exact ⟨hMH, hHN, hNM, hMM, hWM, hZodd, hZbot, hXor', hCodd⟩

theorem sec3_12_one_iso (hS : Setting h L η t Q T) :
    Xor
      (∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = (2 ^ f) ^ 2 ∧
        ∃ (ψ : miyamotoM1G h L η t ≃* SL(2, k) × SL(2, k))
          (α : miyamotoN1G h L η ≃* SL(2, k)),
          (∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
            ψ x = (α a, α a)) ∧
          ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
            ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
      (∃ (k₂ : Type) (_ : Field k₂) (_ : Fintype k₂), Fintype.card k₂ = ((2 ^ f) ^ 2) ^ 2 ∧
        ∃ ψ : miyamotoM1G h L η t ≃* SL(2, k₂),
          (∀ x y : miyamotoM1G h L η t, (y : G) = t⁻¹ * x * t →
            ((ψ y : SL(2, k₂)) : Matrix (Fin 2) (Fin 2) k₂) =
              (ψ x : Matrix (Fin 2) (Fin 2) k₂).map (fun c => c ^ (2 ^ f) ^ 2)) ∧
          ∀ g : SL(2, k₂),
            g ∈ ((miyamotoN1G h L η).subgroupOf (miyamotoM1G h L η t)).map ψ.toMonoidHom ↔
              ∀ i j, (g : Matrix (Fin 2) (Fin 2) k₂) i j ^ (2 ^ f) ^ 2 =
                (g : Matrix (Fin 2) (Fin 2) k₂) i j) := by
  obtain ⟨-, -, -, -, -, -, hZ, hXor, -⟩ := hS.sec3_12_one
  set M := miyamotoM1G h L η t with hMdef
  let c : M ≃* M ⧸ center M :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  have hc : ∀ x : M, c x = (x : M ⧸ center M) := fun x =>
    (MulEquiv.symm_apply_eq _).2 rfl
  have hcm : c.toMonoidHom = QuotientGroup.mk' (center M) := MonoidHom.ext hc
  have hexcl : ∀ (k : Type) (_ : Field k) (_ : Fintype k) (k₂ : Type) (_ : Field k₂)
      (_ : Fintype k₂), Fintype.card k₂ = ((2 ^ f) ^ 2) ^ 2 →
      (M ⧸ center M ≃* SL(2, k) × SL(2, k)) → (M ≃* SL(2, k₂)) → False := by
    intro k _ _ k₂ _ _ hk₂ ψ₁ ψ₂
    have hk₂' : Nat.card k₂ = 2 ^ (4 * f) := by
      rw [Nat.card_eq_fintype_card, hk₂, ← pow_mul, ← pow_mul]
      ring_nf
    exact (GMS.isEmpty_mulEquiv_sl2_prod (k := k) (by have := hS.two_le; omega) hk₂').false
      ((ψ₂.symm.trans c).trans ψ₁)
  rcases hXor with ⟨⟨k, _, _, hk, ψ, α, hψA, hψt⟩, -⟩ | ⟨⟨k₂, _, _, hk₂, ψ, hψt, hψA⟩, -⟩
  · refine Or.inl ⟨⟨k, inferInstance, inferInstance, hk, c.trans ψ, α, fun a x hxa => ?_,
      fun x y y₁ y₂ hxy hx => ?_⟩, ?_⟩
    · rw [MulEquiv.trans_apply, hc]
      exact hψA a x hxa
    · rw [MulEquiv.trans_apply, hc] at hx ⊢
      exact hψt x y y₁ y₂ hxy hx
    · rintro ⟨k₂, _, _, hk₂, ψ₂, -⟩
      exact hexcl k inferInstance inferInstance k₂ inferInstance inferInstance hk₂ ψ ψ₂
  · refine Or.inr ⟨⟨k₂, inferInstance, inferInstance, hk₂, c.trans ψ, fun x y hxy => ?_,
      fun g => ?_⟩, ?_⟩
    · rw [MulEquiv.trans_apply, hc, MulEquiv.trans_apply, hc]
      exact hψt x y hxy
    · rw [← hψA g, ← hcm, map_map]
      rfl
    · rintro ⟨k, _, _, -, ψ₁, -⟩
      exact hexcl k inferInstance inferInstance k₂ inferInstance inferInstance hk₂
        (c.symm.trans ψ₁) (c.trans ψ)

end Setting

end CFSG.LocalAnalysis.EvenBN.U4

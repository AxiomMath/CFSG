module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightLAgreeTwist
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightLAgreeCT

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem permSp_mem_spBlock_of_fix {N : ℕ} {π : Equiv.Perm (Fin N)} {R : Finset (Fin N)}
    (hπ : ∀ i, i ∉ R → π i = i) : permSp K π ∈ spBlock K R := by
  rw [mem_spBlock]
  intro a b hab
  rw [mat_permSp, spIncl_apply, Matrix.one_apply]
  have hp : ∀ c : Fin N ⊕ Fin N, planeOf (Sum.map π π c) = π (planeOf c) := fun c => by
    rcases c with i | i <;> rfl
  have hfix : ∀ c : Fin N ⊕ Fin N, c ∉ planeCoords R → Sum.map π π c = c := fun c hc => by
    rw [mem_planeCoords] at hc
    rcases c with i | i
    · simp only [Sum.map_inl, hπ i hc]
    · simp only [Sum.map_inr, hπ i hc]
  by_cases hb : b ∈ planeCoords R
  · have ha : a ∉ planeCoords R := fun ha => hab ⟨ha, hb⟩
    have h1 : a ≠ Sum.map π π b := by
      rintro rfl
      apply ha
      rw [mem_planeCoords] at hb ⊢
      rw [hp]
      by_contra hc
      have h2 := hπ _ hc
      exact hc (by rwa [π.injective h2])
    have h2 : a ≠ b := fun h => ha (h ▸ hb)
    rw [ite_eq_right h1, ite_eq_right h2]
  · rw [hfix b hb]

theorem commute_q2Embed_of_mem_spBlock {N ε : ℕ} (hK : Nat.card K = 2) {R : Finset (Fin N)}
    {y : StatedSp N K} (hy : y ∈ spBlock K R) {x : SpecialLinearGroup (Fin (2 * N + ε)) K}
    (hx : x ∈ q2Block ε K R) : Commute (q2Embed ε hK y) x :=
  LinearPilot.commute_blockSpecialLinear_of_disjoint disjoint_compl_right
    (q2Embed_mem_blockSpecialLinear_planeCoordsQ2 hK hy) hx

theorem permSp_swap_zero_mem_spBlock (k : Fin 4) :
    permSp K (Equiv.swap (0 : Fin 4) k) ∈ spBlock K ({0, k} : Finset (Fin 4)) :=
  permSp_mem_spBlock_of_fix fun i hi => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact Equiv.swap_apply_of_ne_of_ne hi.1 hi.2

theorem permSp_swap_mem_spBlock_compl_zero {k l : Fin 4} (hk : k ≠ 0) (hl : l ≠ 0) :
    permSp K (Equiv.swap k l) ∈ spBlock K ({0} : Finset (Fin 4))ᶜ :=
  permSp_mem_spBlock_of_fix fun i hi => by
    simp only [Finset.mem_compl, Finset.mem_singleton, not_not] at hi
    subst hi
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hk) (Ne.symm hl)

theorem swap_conj_relation : ∀ j : Fin 4, j ≠ 0 →
    Equiv.swap (1 : Fin 4) j * Equiv.swap 0 1 * (Equiv.swap (1 : Fin 4) j)⁻¹ =
      Equiv.swap 0 j := by
  decide

theorem swap_triangle_relation₁ : ∀ k l : Fin 4, k ≠ 0 → l ≠ 0 → k ≠ l →
    (Equiv.swap (0 : Fin 4) l)⁻¹ * Equiv.swap 0 k = Equiv.swap 0 k * Equiv.swap k l := by
  decide

theorem swap_triangle_relation₂ : ∀ k l : Fin 4, k ≠ 0 → l ≠ 0 → k ≠ l →
    (Equiv.swap (0 : Fin 4) k)⁻¹ * Equiv.swap 0 l * Equiv.swap k l = Equiv.swap 0 l := by
  decide

section Swaps

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem conj_permSp_swap_zero_overlap_eq [CharP K 2] (hset : SeitzSetting G L)
    (hK : Nat.card K = 2) {e : L ≃* StatedSp 4 K} {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hkind : ∀ k : Fin 4, NsKindSp e t k .linearEven)
    (P₀ : NsLinParam hK 0 e 0) {j : Fin 4} (hj : j ≠ 0)
    (x : SpecialLinearGroup (Fin (2 * 4 + 0)) K) (hx : x ∈ q2Block 0 K ({0, j} : Finset (Fin 4))) :
    ((e.symm (permSp K (Equiv.swap (0 : Fin 4) j)) : L) : G) *
        P₀.Φ ⟨x, q2Block_pair_le_left 0 j hx⟩ *
      ((e.symm (permSp K (Equiv.swap (0 : Fin 4) j)) : L) : G)⁻¹ =
      P₀.Φ ⟨x, q2Block_pair_le_left 0 j hx⟩ := by
  set σ : Equiv.Perm (Fin 4) := Equiv.swap 1 j with hσ
  have hσ0 : σ 0 = 0 := Equiv.swap_apply_of_ne_of_ne (by decide) (Ne.symm hj)
  have hσ1 : σ 1 = j := Equiv.swap_apply_left 1 j
  set Qσ := q2Embed 0 hK (permSp K σ) with hQσ
  set wσ : G := ((e.symm (permSp K σ) : L) : G) with hwσ
  set x' := Qσ⁻¹ * x * Qσ with hx'def
  have hx'0 : x' ∈ q2Block 0 K ({0} : Finset (Fin 4)) :=
    q2Embed_permSp_inv_conj_mem hK σ (by rw [hσ0]; exact q2Block_pair_le_left 0 j hx)
  have hx'1 : x' ∈ q2Block 0 K ({1} : Finset (Fin 4)) :=
    q2Embed_permSp_inv_conj_mem hK σ (by rw [hσ1]; exact q2Block_pair_le_right 0 j hx)
  have hx' : x' ∈ q2Block 0 K ({0, 1} : Finset (Fin 4)) := mem_q2Block_pair hx'0 hx'1
  have hσmem : permSp K σ ∈ spBlock K ({0} : Finset (Fin 4))ᶜ :=
    permSp_swap_mem_spBlock_compl_zero (by decide) hj
  have hQσ0 : Qσ ∈ q2Block 0 K ({0} : Finset (Fin 4)) := (q2Embed_mem_q2Block_iff hK).2 hσmem
  have hΦσ : P₀.Φ ⟨Qσ, hQσ0⟩ = wσ := P₀.N1 _ hσmem
  have hxx : (⟨x, q2Block_pair_le_left 0 j hx⟩ : q2Block 0 K ({0} : Finset (Fin 4))) =
      ⟨Qσ, hQσ0⟩ * ⟨x', hx'0⟩ * ⟨Qσ, hQσ0⟩⁻¹ := by
    apply Subtype.ext
    change x = Qσ * (Qσ⁻¹ * x * Qσ) * Qσ⁻¹
    group
  have hΦx : P₀.Φ ⟨x, q2Block_pair_le_left 0 j hx⟩ = wσ * P₀.Φ ⟨x', hx'0⟩ * wσ⁻¹ := by
    rw [hxx, map_mul, map_mul, map_inv, hΦσ]
  have hw : ((e.symm (permSp K (Equiv.swap (0 : Fin 4) j)) : L) : G) =
      wσ * ((e.symm (permSp K (Equiv.swap (0 : Fin 4) 1)) : L) : G) * wσ⁻¹ := by
    rw [← swap_conj_relation j hj, permSp_mul, permSp_mul, permSp_inv, map_mul, map_mul, map_inv,
      L.coe_mul, L.coe_mul, L.coe_inv]
  have hF2 := conj_permSp_swap_overlap_eq hset hK htC ht hkind P₀ x' hx'
  rw [hΦx, hw]
  calc wσ * ((e.symm (permSp K (Equiv.swap (0 : Fin 4) 1)) : L) : G) * wσ⁻¹ *
        (wσ * P₀.Φ ⟨x', hx'0⟩ * wσ⁻¹) *
        (wσ * ((e.symm (permSp K (Equiv.swap (0 : Fin 4) 1)) : L) : G) * wσ⁻¹)⁻¹ =
      wσ * (((e.symm (permSp K (Equiv.swap (0 : Fin 4) 1)) : L) : G) *
        P₀.Φ ⟨x', q2Block_pair_le_left 0 1 hx'⟩ *
        ((e.symm (permSp K (Equiv.swap (0 : Fin 4) 1)) : L) : G)⁻¹) * wσ⁻¹ := by group
    _ = wσ * P₀.Φ ⟨x', hx'0⟩ * wσ⁻¹ := by rw [hF2]

theorem exists_nsLinParamAgree_eight_even [CharP K 2] (hset : SeitzSetting G L)
    (hK : Nat.card K = 2) {e : L ≃* StatedSp 4 K} {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hkind : ∀ k : Fin 4, NsKindSp e t k .linearEven)
    (P₀ : NsLinParam hK 0 e 0) :
    ∃ P : ∀ k : Fin 4, NsLinParam hK 0 e k, NsLinParamAgree P := by
  classical
  set w : Fin 4 → G := fun k => ((e.symm (permSp K (Equiv.swap (0 : Fin 4) k)) : L) : G) with hw
  set Q : Fin 4 → SpecialLinearGroup (Fin (2 * 4 + 0)) K :=
    fun k => q2Embed 0 hK (permSp K (Equiv.swap (0 : Fin 4) k)) with hQ
  have hQinv : ∀ k, (Q k)⁻¹ = Q k := fun k => by
    simp only [hQ]
    rw [← map_inv, ← permSp_inv, Equiv.swap_inv]
  have hval : ∀ (k : Fin 4) (x : SpecialLinearGroup (Fin (2 * 4 + 0)) K)
      (hx : x ∈ q2Block 0 K ({k} : Finset (Fin 4))) (hy : (Q k)⁻¹ * x * Q k ∈ q2Block 0 K {0}),
      (P₀.transport (Equiv.swap 0 k) k (Equiv.swap_apply_left 0 k)).Φ ⟨x, hx⟩ =
        w k * P₀.Φ ⟨(Q k)⁻¹ * x * Q k, hy⟩ * (w k)⁻¹ := by
    intro k x hx hy
    have hc : q2BlockPermConj 0 hK (Equiv.swap 0 k) 0 k (Equiv.swap_apply_left 0 k) ⟨x, hx⟩ =
        ⟨(Q k)⁻¹ * x * Q k, hy⟩ := Subtype.ext (coe_q2BlockPermConj hK _ _ _ _ _)
    rw [NsLinParam.transport_apply, hc]
  have hmem : ∀ (k : Fin 4) (x : SpecialLinearGroup (Fin (2 * 4 + 0)) K),
      x ∈ q2Block 0 K ({k} : Finset (Fin 4)) → (Q k)⁻¹ * x * Q k ∈ q2Block 0 K {0} :=
    fun k x hx => q2Embed_permSp_inv_conj_mem hK (Equiv.swap 0 k) (by
      rw [Equiv.swap_apply_left]
      exact hx)
  have hzero : ∀ (k : Fin 4) (x : SpecialLinearGroup (Fin (2 * 4 + 0)) K)
      (hxk : x ∈ q2Block 0 K ({k} : Finset (Fin 4))) (hx0 : x ∈ q2Block 0 K ({0} : Finset (Fin 4))),
      (P₀.transport (Equiv.swap 0 k) k (Equiv.swap_apply_left 0 k)).Φ ⟨x, hxk⟩ =
        P₀.Φ ⟨x, hx0⟩ := by
    intro k x hxk hx0
    rw [hval k x hxk (hmem k x hxk)]
    have hx0k : x ∈ q2Block 0 K ({0, k} : Finset (Fin 4)) := mem_q2Block_pair hx0 hxk
    have hc : (Q k)⁻¹ * x * Q k = x := by
      rw [hQinv, mul_assoc, ← (commute_q2Embed_of_mem_spBlock hK
        (permSp_swap_zero_mem_spBlock k) hx0k).eq, ← mul_assoc, ← hQinv k, inv_mul_cancel,
        one_mul]
    have hc' : (⟨(Q k)⁻¹ * x * Q k, hmem k x hxk⟩ : q2Block 0 K ({0} : Finset (Fin 4))) =
        ⟨x, hx0⟩ := Subtype.ext hc
    rw [hc']
    by_cases hk : k = 0
    · subst hk
      have hw0 : w 0 = 1 := by
        simp only [hw, Equiv.swap_self, ← Equiv.Perm.one_def, permSp_one, map_one, L.coe_one]
      rw [hw0, one_mul, inv_one, mul_one]
    · exact conj_permSp_swap_zero_overlap_eq hset hK htC ht hkind P₀ hk x hx0k
  refine ⟨fun k => P₀.transport (Equiv.swap 0 k) k (Equiv.swap_apply_left 0 k),
    fun k l x hx hx' => ?_⟩
  change (P₀.transport (Equiv.swap 0 k) k (Equiv.swap_apply_left 0 k)).Φ ⟨x, hx⟩ =
    (P₀.transport (Equiv.swap 0 l) l (Equiv.swap_apply_left 0 l)).Φ ⟨x, hx'⟩
  by_cases hkl : k = l
  · subst hkl
    rfl
  by_cases hk0 : k = 0
  · subst hk0
    rw [hzero 0 x hx hx, hzero l x hx' hx]
  by_cases hl0 : l = 0
  · subst hl0
    rw [hzero k x hx hx', hzero 0 x hx' hx']
  set y := (Q k)⁻¹ * x * Q k with hydef
  have hy0 : y ∈ q2Block 0 K ({0} : Finset (Fin 4)) := hmem k x hx
  have hyl : y ∈ q2Block 0 K ({l} : Finset (Fin 4)) :=
    q2Embed_permSp_inv_conj_mem hK (Equiv.swap 0 k) (by
      rw [Equiv.swap_apply_of_ne_of_ne hl0 (Ne.symm hkl)]
      exact hx')
  set R := q2Embed 0 hK (permSp K (Equiv.swap k l)) with hR
  set v : G := ((e.symm (permSp K (Equiv.swap k l)) : L) : G) with hv
  have hRmem : permSp K (Equiv.swap k l) ∈ spBlock K ({0} : Finset (Fin 4))ᶜ :=
    permSp_swap_mem_spBlock_compl_zero hk0 hl0
  have hR0 : R ∈ q2Block 0 K ({0} : Finset (Fin 4)) := (q2Embed_mem_q2Block_iff hK).2 hRmem
  have hRinv : R⁻¹ = R := by
    rw [hR, ← map_inv, ← permSp_inv, Equiv.swap_inv]
  have hRy0 : R * y * R⁻¹ ∈ q2Block 0 K ({0} : Finset (Fin 4)) :=
    mul_mem (mul_mem hR0 hy0) (inv_mem hR0)
  have hRyk : R * y * R⁻¹ ∈ q2Block 0 K ({k} : Finset (Fin 4)) := by
    have h := map_conj_q2Embed_permSp_q2Block (ε := 0) (K := K) hK (Equiv.swap k l) l
    rw [Equiv.swap_apply_right] at h
    rw [← h]
    exact ⟨y, hyl, rfl⟩
  have hz : (Q l)⁻¹ * x * Q l = R * y * R⁻¹ := by
    have hQQ : (Q l)⁻¹ * Q k = Q k * R := by
      simp only [hQ, hR]
      rw [← map_inv, ← map_mul, ← map_mul, ← permSp_inv, ← permSp_mul, ← permSp_mul,
        swap_triangle_relation₁ k l hk0 hl0 hkl]
    have hx_eq : x = Q k * y * (Q k)⁻¹ := by rw [hydef]; group
    have hcomm := commute_q2Embed_of_mem_spBlock hK (permSp_swap_zero_mem_spBlock k)
      (mem_q2Block_pair hRy0 hRyk)
    calc (Q l)⁻¹ * x * Q l = ((Q l)⁻¹ * Q k) * y * ((Q l)⁻¹ * Q k)⁻¹ := by rw [hx_eq]; group
      _ = Q k * (R * y * R⁻¹) * (Q k)⁻¹ := by rw [hQQ]; group
      _ = R * y * R⁻¹ := by
          rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
  rw [hval k x hx hy0, hval l x hx' (hmem l x hx')]
  have hz' : (⟨(Q l)⁻¹ * x * Q l, hmem l x hx'⟩ : q2Block 0 K ({0} : Finset (Fin 4))) =
      ⟨R, hR0⟩ * ⟨y, hy0⟩ * ⟨R, hR0⟩⁻¹ := Subtype.ext hz
  have hΦR : P₀.Φ ⟨R, hR0⟩ = v := P₀.N1 _ hRmem
  rw [hz', map_mul, map_mul, map_inv, hΦR]
  have hwv : (w k)⁻¹ * w l * v = w l := by
    simp only [hw, hv]
    rw [← L.coe_inv, ← L.coe_mul, ← L.coe_mul, ← map_inv, ← map_mul, ← map_mul, ← permSp_inv,
      ← permSp_mul, ← permSp_mul, swap_triangle_relation₂ k l hk0 hl0 hkl]
  have hC7 := conj_permSp_swap_zero_overlap_eq hset hK htC ht hkind P₀ hl0 y
    (mem_q2Block_pair hy0 hyl)
  show w k * P₀.Φ ⟨y, hy0⟩ * (w k)⁻¹ = w l * (v * P₀.Φ ⟨y, hy0⟩ * v⁻¹) * (w l)⁻¹
  calc w k * P₀.Φ ⟨y, hy0⟩ * (w k)⁻¹ =
      w k * (w l * P₀.Φ ⟨y, hy0⟩ * (w l)⁻¹) * (w k)⁻¹ := by
        rw [show w l * P₀.Φ ⟨y, hy0⟩ * (w l)⁻¹ = P₀.Φ ⟨y, hy0⟩ from hC7]
    _ = w k * ((w k)⁻¹ * w l * v) * P₀.Φ ⟨y, hy0⟩ * ((w k)⁻¹ * w l * v)⁻¹ * (w k)⁻¹ := by
        rw [hwv]
        group
    _ = w l * (v * P₀.Φ ⟨y, hy0⟩ * v⁻¹) * (w l)⁻¹ := by group

end Swaps

section Inputs

theorem spTwoLinearEvenEightAlignInput_holds : SpTwoLinearEvenEightAlignInput := by
  intro G _ _ L hset K _ _ _ hK e t ht hKt hroot
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  obtain ⟨P₀⟩ := nonempty_nsLinParam (m := 3) hset hK zero_le_one le_rfl e htC ht 0
    (Or.inl ⟨rfl, rfl⟩) (hroot 0)
  exact exists_nsLinParamAgree_eight_even hset hK htC ht hroot P₀

theorem spTwoLinearEvenEightAgreeInput_holds : SpTwoLinearEvenEightAgreeInput :=
  spTwoLinearEvenEightAgreeInput_of_align spTwoLinearEvenEightAlignInput_holds

end Inputs

end CFSG.SeitzReduction.SymplecticPilot

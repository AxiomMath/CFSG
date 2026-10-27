module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphParam

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

variable {K : Type} [Field K] {N ε : ℕ}

theorem permSp_mul (π ρ : Equiv.Perm (Fin N)) :
    permSp K (π * ρ) = permSp K π * permSp K ρ := by
  apply mat_injective
  rw [map_mul, mat_permSp, mat_permSp, mat_permSp]
  ext a b
  rw [spIncl_apply, Matrix.mul_apply, Finset.sum_eq_single (Sum.map ρ ρ b)]
  · rw [spIncl_apply, spIncl_apply, ite_eq_left rfl, mul_one]
    rcases b with j | j <;> rfl
  · intro c _ hc
    rw [spIncl_apply (σ := (ρ : Fin N → Fin N)) c b, ite_eq_right hc, mul_zero]
  · simp

theorem permSp_one : permSp K (1 : Equiv.Perm (Fin N)) = 1 := by
  apply mat_injective
  rw [mat_permSp, map_one]
  ext a b
  rw [spIncl_apply, Matrix.one_apply]
  rcases b with j | j <;> rfl

theorem permSp_inv (π : Equiv.Perm (Fin N)) : permSp K π⁻¹ = (permSp K π)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← permSp_mul, inv_mul_cancel, permSp_one]

theorem blockComplProj_mul_q2Embed_permSp (hK : Nat.card K = 2) (ρ : Equiv.Perm (Fin N))
    (l : Fin N) :
    LinearPilot.blockComplProj (planeCoordsQ2 ε ({ρ l} : Finset (Fin N)))ᶜ *
        ((q2Embed ε hK (permSp K ρ) : SpecialLinearGroup (Fin (2 * N + ε)) K) :
          Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) =
      ((q2Embed ε hK (permSp K ρ) : SpecialLinearGroup (Fin (2 * N + ε)) K) :
          Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) *
        LinearPilot.blockComplProj (planeCoordsQ2 ε ({l} : Finset (Fin N)))ᶜ := by
  ext a b
  rw [LinearPilot.blockComplProj, LinearPilot.blockComplProj, diagonal_mul, mul_diagonal]
  obtain ⟨w, rfl⟩ := (q2Coord N ε).surjective a
  obtain ⟨w', rfl⟩ := (q2Coord N ε).surjective b
  rw [q2Embed_apply_q2Coord]
  simp only [Finset.mem_compl, q2Coord_mem_planeCoordsQ2]
  rcases w with u | i <;> rcases w' with v | j
  · rw [fromBlocks_apply₁₁, mat_permSp, spIncl_apply]
    simp only [inPlanes_inl, Finset.mem_singleton]
    by_cases huv : u = Sum.map ρ ρ v
    · subst huv
      have hp : planeOf (Sum.map ρ ρ v) = ρ (planeOf v) := by rcases v with v | v <;> rfl
      simp [hp, mul_comm]
    · simp [huv]
  · simp
  · simp
  · simp

theorem map_conj_q2Embed_permSp_q2Block (hK : Nat.card K = 2) (ρ : Equiv.Perm (Fin N))
    (l : Fin N) :
    (q2Block ε K ({l} : Finset (Fin N))).map
        (MulAut.conj (q2Embed ε hK (permSp K ρ))).toMonoidHom =
      q2Block ε K ({ρ l} : Finset (Fin N)) :=
  LinearPilot.map_conj_blockSpecialLinear_of_mul_eq _ (blockComplProj_mul_q2Embed_permSp hK ρ l)

theorem q2Embed_permSp_inv_conj_mem (hK : Nat.card K = 2) (π : Equiv.Perm (Fin N)) {k : Fin N}
    {x : SpecialLinearGroup (Fin (2 * N + ε)) K} (hx : x ∈ q2Block ε K {π k}) :
    (q2Embed ε hK (permSp K π))⁻¹ * x * q2Embed ε hK (permSp K π) ∈ q2Block ε K {k} := by
  have h := map_conj_q2Embed_permSp_q2Block (ε := ε) (K := K) hK π⁻¹ (π k)
  rw [show π⁻¹ (π k) = k by simp] at h
  rw [← h]
  refine ⟨x, hx, ?_⟩
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, permSp_inv, map_inv, inv_inv]

section Transport

variable (ε) in
@[expose] noncomputable def q2BlockPermConj (hK : Nat.card K = 2) (π : Equiv.Perm (Fin N))
    (k l : Fin N) (hl : π k = l) : q2Block ε K {l} →* q2Block ε K {k} :=
  ((MulAut.conj (q2Embed ε hK (permSp K π))⁻¹).toMonoidHom.comp
    (q2Block ε K {l}).subtype).codRestrict _ fun x => by
      simpa only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, coe_subtype, Function.comp_apply,
        MulAut.conj_apply, inv_inv] using q2Embed_permSp_inv_conj_mem hK π (hl ▸ x.2)

theorem coe_q2BlockPermConj (hK : Nat.card K = 2) (π : Equiv.Perm (Fin N)) (k l : Fin N)
    (hl : π k = l) (x : q2Block ε K {l}) :
    ((q2BlockPermConj ε hK π k l hl x : q2Block ε K {k}) :
      SpecialLinearGroup (Fin (2 * N + ε)) K) =
      (q2Embed ε hK (permSp K π))⁻¹ * x * q2Embed ε hK (permSp K π) := by
  change (q2Embed ε hK (permSp K π))⁻¹ * x * (q2Embed ε hK (permSp K π))⁻¹⁻¹ = _
  rw [inv_inv]

theorem q2BlockPermConj_injective (hK : Nat.card K = 2) (π : Equiv.Perm (Fin N)) (k l : Fin N)
    (hl : π k = l) : Function.Injective (q2BlockPermConj ε hK π k l hl) := fun x y h => by
  apply Subtype.ext
  have h' := congrArg Subtype.val h
  rw [coe_q2BlockPermConj, coe_q2BlockPermConj] at h'
  simpa using h'

theorem q2BlockPermConj_surjective (hK : Nat.card K = 2) (π : Equiv.Perm (Fin N)) (k l : Fin N)
    (hl : π k = l) : Function.Surjective (q2BlockPermConj ε hK π k l hl) := by
  intro z
  have hz : MulAut.conj (q2Embed ε hK (permSp K π)) (z : SpecialLinearGroup (Fin (2 * N + ε)) K) ∈
      q2Block ε K {l} := by
    rw [← hl, ← map_conj_q2Embed_permSp_q2Block hK π k]
    exact ⟨z, z.2, rfl⟩
  refine ⟨⟨_, hz⟩, Subtype.ext ?_⟩
  rw [coe_q2BlockPermConj]
  simp [MulAut.conj_apply, mul_assoc]

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {hK : Nat.card K = 2}
  {e : L ≃* StatedSp N K}

@[expose] noncomputable def NsLinParam.transport {k : Fin N} (P : NsLinParam hK ε e k)
    (π : Equiv.Perm (Fin N)) (l : Fin N) (hl : π k = l) : NsLinParam hK ε e l where
  Φ := (MulAut.conj ((e.symm (permSp K π) : L) : G)).toMonoidHom.comp
    (P.Φ.comp (q2BlockPermConj ε hK π k l hl))
  injective := (MulAut.conj _).injective.comp
    (P.injective.comp (q2BlockPermConj_injective hK π k l hl))
  range_eq := by
    rw [MonoidHom.range_comp, MonoidHom.range_comp,
      MonoidHom.range_eq_top.2 (q2BlockPermConj_surjective hK π k l hl), ← MonoidHom.range_eq_map,
      P.range_eq, F4Pilot.map_centralizerPerfectCore (MulAut.conj ((e.symm (permSp K π) : L) : G)),
      ← UnitaryPilot.modelToG_map_conj, map_conj_permSp_nsTorusSp, hl]
  N1 y hy := by
    set Pπ := permSp K π with hPπ
    have hy' : Pπ⁻¹ * y * Pπ ∈ spBlock K ({k} : Finset (Fin N))ᶜ := by
      have h := map_conj_permSp_complSp (K := K) π⁻¹ (π k)
      rw [show π⁻¹ (π k) = k by simp, hl] at h
      rw [spBlock_compl_singleton] at hy ⊢
      rw [← h]
      refine ⟨y, hy, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, permSp_inv, inv_inv]
    have hc : q2BlockPermConj ε hK π k l hl ⟨q2Embed ε hK y, (q2Embed_mem_q2Block_iff hK).2 hy⟩ =
        ⟨q2Embed ε hK (Pπ⁻¹ * y * Pπ), (q2Embed_mem_q2Block_iff hK).2 hy'⟩ := by
      apply Subtype.ext
      rw [coe_q2BlockPermConj]
      change _ = q2Embed ε hK (Pπ⁻¹ * y * Pπ)
      rw [map_mul, map_mul, map_inv]
    change ((e.symm Pπ : L) : G) * P.Φ (q2BlockPermConj ε hK π k l hl
      ⟨q2Embed ε hK y, (q2Embed_mem_q2Block_iff hK).2 hy⟩) * ((e.symm Pπ : L) : G)⁻¹ = _
    rw [hc, P.N1 _ hy', ← L.coe_inv, ← map_inv, ← L.coe_mul, ← L.coe_mul, ← map_mul, ← map_mul]
    congr 2
    group

theorem NsLinParam.transport_apply {k : Fin N} (P : NsLinParam hK ε e k) (π : Equiv.Perm (Fin N))
    (l : Fin N) (hl : π k = l) (x : q2Block ε K {l}) :
    (P.transport π l hl).Φ x = ((e.symm (permSp K π) : L) : G) *
      P.Φ (q2BlockPermConj ε hK π k l hl x) * ((e.symm (permSp K π) : L) : G)⁻¹ :=
  rfl

end Transport

end CFSG.SeitzReduction.SymplecticPilot

module

public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoL3A
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915T2
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoS1
public import CFSG.ClassicalInvolution.Q3.TL4MF163L3Y

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.ExitTwo

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic Matrix
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Q5GL2
  CFSG.ClassicalInvolution.Q3.TA3.Q5L3
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

namespace L3

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]

theorem eq_of_inv (h4 : 4 ≤ Nat.card K) (hodd : Odd (Nat.card K)) {N : Subgroup G} [N.Normal]
    (hC : Subgroup.centralizer (N : Set G) = ⊥) (e : ↥N ≃* projectiveSL 3 K)
    {Δ : Set (Subgroup G)} (hΔ : PhilipHall.Frame.Thm4Twin.TwinT4Hyp 3 G Δ) {w : G}
    (hwN : w ∈ N) {M M' : Subgroup G} (hM : M ∈ Δ) (hM' : M' ∈ Δ)
    (hMw : IsUniqueInvolution M w) (hM'w : IsUniqueInvolution M' w) : M = M' := by
  have hw2 : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hMw.sq) hMw.ne_one
  obtain ⟨Q, π, hrange, hk, hπ1, hπ⟩ := exists_frame hodd e hwN hw2
  let e' : ↥N ≃* projectiveSL 3 K := e.trans (conjAut 3 K Q)⁻¹
  have hπN : ∀ A, π A ∈ N := fun A => by rw [hπ A]; exact (e.symm _).2
  have hπe : ∀ A, e' ⟨π A, hπN A⟩ = proj 3 K (blkP 1 (A : GL (Fin 2) K)) := fun A => by
    have h1 : (⟨π A, hπN A⟩ : N) = e.symm (proj 3 K (blkP Q A)) := Subtype.ext (hπ A)
    show (conjAut 3 K Q)⁻¹ (e ⟨π A, hπN A⟩) = _
    rw [h1, MulEquiv.apply_symm_apply, MF163.L3.conjAut_inv_proj_blkP]
  obtain ⟨A, ⟨c, hc⟩, hAM, hA4⟩ :=
    exists_scalar_four h4 hC e' hrange hk hπ1 hπN hπe hΔ hM hMw
  obtain ⟨A', ⟨c', hc'⟩, hA'M, hA'4⟩ :=
    exists_scalar_four h4 hC e' hrange hk hπ1 hπN hπe hΔ hM' hM'w
  have hsq : ∀ {L : Subgroup G} {x : G}, IsUniqueInvolution L w → x ∈ L → orderOf x = 4 →
      x * x = w := by
    intro L x hL hx hx4
    have hx2 : x * x * (x * x) = 1 := by
      rw [← sq, ← sq, ← pow_mul, show 2 * 2 = orderOf x by rw [hx4], pow_orderOf_eq_one]
    rcases hL.unique _ (L.mul_mem hx hx) hx2 with h0 | h0
    · exfalso
      have := orderOf_dvd_of_pow_eq_one (show x ^ 2 = 1 by rw [sq]; exact h0)
      rw [hx4] at this
      norm_num at this
    · exact h0
  set s := π A with hs
  set s' := π A' with hs'
  have hw : s * s = w := hsq hMw hAM hA4
  have hw' : s' * s' = w := hsq hM'w hA'M hA'4
  have hcomm : s⁻¹ * s' = s' * s⁻¹ := by
    have h1 : s * s' = s' * s := by
      rw [hs, hs', ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hc, scalar_mul_comm]
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, h1, mul_assoc, mul_inv_cancel, mul_one]
  have hBs : ((A' * A⁻¹ : (⊤ : Subgroup (GL (Fin 2) K))) : GL (Fin 2) K) =
      GeneralLinearGroup.scalar (Fin 2) (c' * c⁻¹) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hc, hc', map_mul, map_inv]
  have hBB : π (A' * A⁻¹) * π (A' * A⁻¹) = 1 := by
    rw [map_mul, map_inv, ← hs, ← hs',
      show s' * s⁻¹ * (s' * s⁻¹) = s' * (s⁻¹ * s') * s⁻¹ by group, hcomm,
      show s' * (s' * s⁻¹) * s⁻¹ = s' * s' * (s * s)⁻¹ by group, hw, hw', mul_inv_cancel]
  have hsM' : s ∈ M' := by
    rcases eq_or_of_scalar_sq hk (N1 := ⟨-1, Subgroup.mem_top _⟩) rfl hBs hBB with h1 | h1
    · rw [map_mul, map_inv, ← hs, ← hs', mul_inv_eq_one] at h1
      exact h1 ▸ hA'M
    · rw [map_mul, map_inv, ← hs, ← hs', hπ1, mul_inv_eq_iff_eq_mul] at h1
      have h2 : s = w * s' := by
        rw [h1, ← mul_assoc, hMw.sq, one_mul]
      exact h2 ▸ M'.mul_mem hM'w.mem hA'M
  exact eq_of_orderOf_eq_four hΔ.hyp hM hM' hAM hsM' hA4

omit [Finite G] in
theorem exists_conj_of_psl (hodd : Odd (Nat.card K)) {N : Subgroup G}
    (e : ↥N ≃* projectiveSL 3 K) {x y : G} (hx : x ∈ N) (hy : y ∈ N) (hx2 : x * x = 1)
    (hy2 : y * y = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : ∃ n ∈ N, n * x * n⁻¹ = y := by
  have key : ∀ {z : G} (hz : z ∈ N), z * z = 1 → z ≠ 1 → ∃ g : projectiveSL 3 K,
      g * proj 3 K GH74.GLS.Stage2.Bender.Thm2.L915.t3 * g⁻¹ = e ⟨z, hz⟩ := by
    intro z hz hz2 hz1
    refine GH74.GLS.Stage2.Bender.Thm2.L915.exists_conj_t3 hodd ?_ ?_
    · rw [← map_mul, show (⟨z, hz⟩ : N) * ⟨z, hz⟩ = 1 from Subtype.ext hz2, map_one]
    · intro h
      apply hz1
      have h1 : (⟨z, hz⟩ : N) = 1 := e.injective (h.trans (map_one e).symm)
      exact congrArg Subtype.val h1
  obtain ⟨g₁, hg₁⟩ := key hx hx2 hx1
  obtain ⟨g₂, hg₂⟩ := key hy hy2 hy1
  refine ⟨(e.symm (g₂ * g₁⁻¹) : G), (e.symm _).2, ?_⟩
  have h1 : e.symm (g₂ * g₁⁻¹) * ⟨x, hx⟩ * (e.symm (g₂ * g₁⁻¹))⁻¹ = ⟨y, hy⟩ := e.injective (by
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← hg₁, ← hg₂]
    group)
  exact congrArg Subtype.val h1

end L3

theorem socleTransitive_l3Ge5 : SocleTransitive IsL3Ge5 := by
  intro G _ _ N _ _ _ hC hP Δ hΔ hN J hJ L hL
  obtain ⟨p, f, hp, hp2, h5, hLie⟩ := hP
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hLie
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have h4 : 4 ≤ Nat.card K := by rw [hK]; omega
  obtain ⟨⟨t, ht⟩, -⟩ := hΔ.hyp.omega1 J hJ
  have htN := hN J hJ t ht
  refine transitive_of_eq_at hΔ.hyp (t := t) (fun M hM z hz => ?_)
    (fun M hM M' hM' h1 h2 => L3.eq_of_inv h4 hodd hC e hΔ htN hM hM' h1 h2) J hJ L hL
  obtain ⟨n, -, hn⟩ :=
    L3.exists_conj_of_psl hodd e (hN M hM z hz) htN hz.sq ht.sq hz.ne_one ht.ne_one
  exact ⟨n, hn⟩

end CFSG.ClassicalInvolution.Q3.TL4.ExitTwo

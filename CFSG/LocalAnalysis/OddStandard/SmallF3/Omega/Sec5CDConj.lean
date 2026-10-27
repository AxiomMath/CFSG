module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CDPhi

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
  [FiniteDimensional (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

namespace Sec5CDAbs

variable {L B : Subgroup G} {r : G} {i : Fin 6} {fr : NFrame Q (Fin 6) 1}
  {φc : ↥L →* omegaGroup hQ} (h : Sec5CDAbs L B r i fr φc)

include h

theorem conj_lift {g : ↥L} {σ : Equiv.Perm (Fin 6)} {K : Finset (Fin 6)}
    (hg : (φc g : OGroup Q) = fr.permOrth σ * fr.signChange K) {J : Finset (Fin 6)}
    (hJ : Even J.card) :
    (g : G) * (sec5c_liftL L B φc (fr.signChange J) : G) * (g : G)⁻¹ =
      (sec5c_liftL L B φc (fr.signChange (J.map σ.toEmbedding)) : G) := by
  let b0 : ↥L := sec5c_liftL L B φc (fr.signChange J)
  let b1 : ↥L := sec5c_liftL L B φc (fr.signChange (J.map σ.toEmbedding))
  have hJ' : Even (J.map σ.toEmbedding).card := by rw [Finset.card_map]; exact hJ
  have hb0sq : b0 * b0 = 1 := h.liftL_sq (signChange_mem_ffB0 fr hJ)
  have hb1sq : b1 * b1 = 1 := h.liftL_sq (signChange_mem_ffB0 fr hJ')
  have hb0map : (φc b0 : OGroup Q) = fr.signChange J := h.map_liftL (signChange_mem_ffB0 fr hJ)
  have hb1map : (φc b1 : OGroup Q) = fr.signChange (J.map σ.toEmbedding) :=
    h.map_liftL (signChange_mem_ffB0 fr hJ')
  let x : ↥L :=
    ⟨(g : G) * (b0 : G) * (g : G)⁻¹, L.mul_mem (L.mul_mem g.2 b0.2) (L.inv_mem g.2)⟩
  have hx_eq : x = g * b0 * g⁻¹ := Subtype.ext rfl
  have hxx : x * x = 1 := by
    rw [hx_eq]
    calc (g * b0 * g⁻¹) * (g * b0 * g⁻¹) = g * (b0 * b0) * g⁻¹ := by group
      _ = g * 1 * g⁻¹ := by rw [hb0sq]
      _ = 1 := by group
  have hphi : (φc x : OGroup Q) = (φc b1 : OGroup Q) := by
    rw [hx_eq, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      hb0map, hb1map, hg]
    exact ffMono_conj_signChange fr σ K J
  have hx_eq_b1 : x = b1 := h.cover.eq_of_mul_self_eq_one hxx hb1sq (Subtype.ext hphi)
  change (x : G) = (b1 : G)
  exact congrArg Subtype.val hx_eq_b1

theorem conj_phi {g : ↥L} {σ : Equiv.Perm (Fin 6)} {K : Finset (Fin 6)}
    (hg : (φc g : OGroup Q) = fr.permOrth σ * fr.signChange K)
    (hA : (g : G) * r * (g : G)⁻¹ ∈ zpowers r ⊔ B) (v : Fin 6 → ZMod 2) :
    (g : G) * sec5c_phi L B r i fr φc v * (g : G)⁻¹ =
      sec5c_phi L B r i fr φc (permVec σ v) := by
  have even_conj : ∀ u : Fin 6 → ZMod 2, IsEvenVec u →
      (g : G) * sec5c_phi L B r i fr φc u * (g : G)⁻¹ =
        sec5c_phi L B r i fr φc (permVec σ u) := by
    intro u hu
    rw [h.phi_even hu]
    have hu' : IsEvenVec (permVec σ u) := by
      change ∑ j, permVec σ u j = 0
      rw [sec5c_sum_perm]
      exact hu
    rw [h.phi_even hu', sec5c_supp_perm]
    exact h.conj_lift hg ((sec5c_isEvenVec_iff u).mp hu)
  by_cases hv : IsEvenVec v
  · exact even_conj v hv
  · have hv1 : ∑ j, v j = 1 := by
      have hv' : ∑ j, v j ≠ 0 := hv
      generalize ∑ j, v j = a at hv'
      revert a
      decide
    have hw_even : IsEvenVec (v + Pi.single i 1) := by
      change ∑ j, ((v + Pi.single i 1 : Fin 6 → ZMod 2)) j = 0
      have hmm : (v + Pi.single i 1 : Fin 6 → ZMod 2) =
          v + (∑ j, v j) • Pi.single i 1 := by rw [hv1, one_smul]
      rw [hmm]
      exact sec5c_sum_ev i v
    have hwe : (v + Pi.single i 1) + Pi.single i 1 = v := by
      funext j
      simp only [Pi.add_apply]
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    have hr_conj : (g : G) * r * (g : G)⁻¹ =
        sec5c_phi L B r i fr φc (Pi.single (σ i) 1) := by
      have hl'_mem : r * (g : G)⁻¹ * r⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp h.r_norm (g⁻¹ : G)).mp (Subgroup.inv_mem L g.2)
      let l' : ↥L := ⟨r * (g : G)⁻¹ * r⁻¹, hl'_mem⟩
      have hl'_val : (l' : G) = r * (g : G)⁻¹ * r⁻¹ := rfl
      let uL : ↥L := g * l'
      have huL_val : (uL : G) = (g : G) * r * (g : G)⁻¹ * r⁻¹ := by
        change (g : G) * (l' : G) = (g : G) * r * (g : G)⁻¹ * r⁻¹
        rw [hl'_val]
        group
      have huA : (uL : G) ∈ zpowers r ⊔ B := by
        rw [huL_val]
        exact Subgroup.mul_mem _ hA
          (Subgroup.inv_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers r)))
      have huB : (uL : G) ∈ B := h.A_inf_L huA uL.2
      have hphi_l' : (φc l' : OGroup Q) =
          fr.signChange {i} * (φc g⁻¹ : OGroup Q) * (fr.signChange {i})⁻¹ :=
        h.r_act (g⁻¹) l' (by rw [hl'_val, Subgroup.coe_inv])
      have hphi_uL : (φc uL : OGroup Q) = fr.signChange (symmDiff {σ i} {i}) := by
        have huL_eq : uL = g * l' := rfl
        have hginv : (φc g⁻¹ : OGroup Q) = (fr.permOrth σ * fr.signChange K)⁻¹ := by
          rw [map_inv, Subgroup.coe_inv, hg]
        have hTinv : (fr.signChange {i})⁻¹ = fr.signChange {i} :=
          inv_eq_of_mul_eq_one_right (fr.signChange_mul_self {i})
        rw [huL_eq, map_mul, Subgroup.coe_mul, hg, hphi_l', hginv]
        calc (fr.permOrth σ * fr.signChange K) *
              (fr.signChange {i} * (fr.permOrth σ * fr.signChange K)⁻¹ * (fr.signChange {i})⁻¹)
            = ((fr.permOrth σ * fr.signChange K) * fr.signChange {i} *
                (fr.permOrth σ * fr.signChange K)⁻¹) * (fr.signChange {i})⁻¹ := by group
          _ = fr.signChange (Finset.map σ.toEmbedding ({i} : Finset (Fin 6))) *
                (fr.signChange {i})⁻¹ := by
                rw [ffMono_conj_signChange fr σ K {i}]
          _ = fr.signChange {σ i} * (fr.signChange {i})⁻¹ := by
                rw [Finset.map_singleton, Equiv.toEmbedding_apply]
          _ = fr.signChange {σ i} * fr.signChange {i} := by rw [hTinv]
          _ = fr.signChange (symmDiff {σ i} {i}) := fr.signChange_mul {σ i} {i}
      have hsupp : sec5c_supp (Pi.single (σ i) 1 + Pi.single i 1) = symmDiff {σ i} {i} := by
        rw [sec5c_supp_add, sec5c_supp_single, sec5c_supp_single]
      have heven_vec : IsEvenVec (Pi.single (σ i) 1 + Pi.single i 1) := by
        change ∑ j, (Pi.single (σ i) 1 + Pi.single i 1 : Fin 6 → ZMod 2) j = 0
        rw [sec5c_sum_add]
        have h1 : ∑ j, (Pi.single (σ i) (1 : ZMod 2) : Fin 6 → ZMod 2) j = 1 := by
          simp [Finset.sum_pi_single']
        have h2 : ∑ j, (Pi.single i (1 : ZMod 2) : Fin 6 → ZMod 2) j = 1 := by
          simp [Finset.sum_pi_single']
        rw [h1, h2]
        decide
      have hu_eq_phi : (uL : G) =
          sec5c_phi L B r i fr φc (Pi.single (σ i) 1 + Pi.single i 1) := by
        have hlift : uL = sec5c_liftL L B φc (φc uL : OGroup Q) :=
          (h.liftL_unique huB).symm
        rw [hlift, hphi_uL, ← hsupp]
        exact (h.phi_even heven_vec).symm
      calc (g : G) * r * (g : G)⁻¹
          = (uL : G) * r := by rw [huL_val]; group
        _ = sec5c_phi L B r i fr φc (Pi.single (σ i) 1 + Pi.single i 1) *
              sec5c_phi L B r i fr φc (Pi.single i 1) := by
              rw [hu_eq_phi, h.phi_single]
        _ = sec5c_phi L B r i fr φc ((Pi.single (σ i) 1 + Pi.single i 1) +
              Pi.single i 1) :=
              (h.phi_add (Pi.single (σ i) 1 + Pi.single i 1) (Pi.single i 1)).symm
        _ = sec5c_phi L B r i fr φc (Pi.single (σ i) 1) := by
              congr 1
              funext j
              simp only [Pi.add_apply]
              rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    have hpv : sec5c_phi L B r i fr φc v =
        sec5c_phi L B r i fr φc (v + Pi.single i 1) * r := by
      have h1 : sec5c_phi L B r i fr φc ((v + Pi.single i 1) + Pi.single i 1) =
          sec5c_phi L B r i fr φc (v + Pi.single i 1) * r := by
        rw [h.phi_add, h.phi_single]
      rwa [hwe] at h1
    have hpσv : sec5c_phi L B r i fr φc (permVec σ v) =
        sec5c_phi L B r i fr φc (permVec σ (v + Pi.single i 1)) *
          sec5c_phi L B r i fr φc (Pi.single (σ i) 1) := by
      have h1 : sec5c_phi L B r i fr φc (permVec σ ((v + Pi.single i 1) + Pi.single i 1)) =
          sec5c_phi L B r i fr φc (permVec σ (v + Pi.single i 1)) *
            sec5c_phi L B r i fr φc (Pi.single (σ i) 1) := by
        rw [sec5c_permVec_add, sec5c_permVec_single, h.phi_add]
      rwa [hwe] at h1
    rw [hpv, hpσv]
    calc (g : G) * (sec5c_phi L B r i fr φc (v + Pi.single i 1) * r) * (g : G)⁻¹
        = ((g : G) * sec5c_phi L B r i fr φc (v + Pi.single i 1) * (g : G)⁻¹) *
            ((g : G) * r * (g : G)⁻¹) := by group
      _ = sec5c_phi L B r i fr φc (permVec σ (v + Pi.single i 1)) *
            sec5c_phi L B r i fr φc (Pi.single (σ i) 1) := by
            rw [even_conj (v + Pi.single i 1) hw_even, hr_conj]

end Sec5CDAbs

end CFSG.OddStandard.SmallF3.Omega

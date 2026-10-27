module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109A2Idx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109AInputs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem asc82Step109AOuter_of (h3 : Asc82Sec3Res10) (h : Asc82Res10a) (hf : Asc82Facts10)
    (hb : Asc82Basic10) : Asc82Step109AOuter := by
  intro G _ _ t L S z K1 K2 hctx g hgN hgM hg2 hgt hgz
  have hctxA : Sec10A2Ctx G t L S z K1 K2 g :=
    { toSec10Ctx := hctx
      norm := hgN
      not_M := hgM
      two := hg2
      swap_t := hgt
      fix_z := hgz }
  obtain ⟨f, hfs⟩ := sec10A2_exists_act h3 h hf hb hctxA
  have hpsp : IsPSp43 L := (hb G t L S z hctx.toSec10Z).1
  have hcomm : ⁅K1, K2⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    exact Subgroup.mem_centralizer_iff.mpr fun b hb' =>
      (sec10Z_comm hf.pockets5 hpsp hctx a ha b hb').symm
  obtain ⟨e1, e2⟩ := sec10KS_equiv hf.pockets5 hf.centZ5 hpsp hctx
  obtain ⟨ψ, hψΦ, hψΨ, hψ2, hψ1, hψK2, hψout⟩ := hf.autK5 G K1 K2 hcomm
    (sec10KS_card_sup hf.pockets5 hf.centZ5 hpsp hctx) e1 e2 f.range
    (Sec10A2Psi S g K1 K2 f) sec10A2_Psi_le (sec10A2_Phi_pgroup hctxA)
    (sec10A2_Psi_relIndex h3 h hf hb hctxA hfs) (sec10A2_Psi_card h3 h hf hb hctxA hfs)
    (sec10A2_Psi_inner h3 h hf hb hctxA hfs) (sec10A2_Psi_swap h3 h hf hb hctxA hfs)
  obtain ⟨y, rfl⟩ := hψΦ
  have hyS : (y : G) ∉ S := fun hy => hψΨ (sec10A2_mem_Psi hy)
  have hs : g⁻¹ * (y : G) ∈ S := (sec10A2_T_cases hb hctxA y y.2).resolve_left hyS
  refine ⟨g⁻¹ * (y : G), hs, ?_⟩
  rw [mul_inv_cancel_left]
  have hD := sec10A2_split h3 h hf hb hctx
  have hOC := sec10L104_oddK0_le_centralizer h.lK0 h3.l36 hf.pockets5 hf.centZ5 hb hctx
  have hKcomm : ∀ a ∈ K1, ∀ b ∈ oddCoreIn (secK0 t z), a * b = b * a := fun a ha b hb' =>
    Subgroup.mem_centralizer_iff.mp (hOC hb') a (hctx.pocket1.2.1 ha).1
  refine ⟨⟨?_, ?_⟩, ?_, sec10A2_sq_cent h3 h hf hb hctxA hfs hψ2⟩
  · refine sec10A2_mem_normalizer_of_map_le fun a ha => ?_
    refine sec10A2_conj_sup_le (fun k hk => ?_) (fun n hn => ?_) a ha
    · obtain ⟨n, hn, hkn⟩ := hfs y ⟨k, Subgroup.mem_sup_left hk⟩
      rw [hkn]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hn)
        (Subgroup.mem_sup_left (hψ1 ⟨k, Subgroup.mem_sup_left hk⟩ hk))
    · exact Subgroup.mem_sup_right (sec10A2_conj_N0 h hb hctxA y y.2 n hn)
  · rintro ⟨k, hk, hkprop⟩
    obtain ⟨a, ha, n0, hn0, rfl⟩ := exists_mul_of_mem_sup_of_commute hKcomm hk
    refine hψout ⟨⟨a, Subgroup.mem_sup_left ha⟩, ha, fun w hw => ?_⟩
    obtain ⟨n, hn, hnw⟩ := hfs y w
    have hprop := hkprop (w : G) (Subgroup.mem_sup_left hw)
    have hconj : (a * n0) * (w : G) * (a * n0)⁻¹ = a * (w : G) * a⁻¹ := by
      have hc := hKcomm (w : G) hw n0 hn0
      calc (a * n0) * (w : G) * (a * n0)⁻¹ = a * (n0 * (w : G)) * n0⁻¹ * a⁻¹ := by group
        _ = a * ((w : G) * n0) * n0⁻¹ * a⁻¹ := by rw [← hc]
        _ = a * (w : G) * a⁻¹ := by group
    rw [hnw, hconj] at hprop
    have h1 : ((f y w : ↥(K1 ⊔ K2)) : G) * (a * (w : G) * a⁻¹)⁻¹ ∈
        oddCoreIn (secK0 t z) := by
      have := (oddCoreIn (secK0 t z)).mul_mem ((oddCoreIn (secK0 t z)).inv_mem hn) hprop
      have e : n⁻¹ * (n * ((f y w : ↥(K1 ⊔ K2)) : G) * (a * (w : G) * a⁻¹)⁻¹) =
          ((f y w : ↥(K1 ⊔ K2)) : G) * (a * (w : G) * a⁻¹)⁻¹ := by group
      rwa [e] at this
    have hwK : a * (w : G) * a⁻¹ ∈ K1 ⊔ K2 :=
      Subgroup.mem_sup_left (K1.mul_mem (K1.mul_mem ha hw) (K1.inv_mem ha))
    have h2 : ((f y w : ↥(K1 ⊔ K2)) : G) * (a * (w : G) * a⁻¹)⁻¹ ∈ K1 ⊔ K2 :=
      (K1 ⊔ K2).mul_mem (f y w).2 ((K1 ⊔ K2).inv_mem hwK)
    exact mul_inv_eq_one.mp (hD.disj _ h1 h2)
  · intro k hk
    obtain ⟨n, hn, hnk⟩ := hfs y ⟨k, Subgroup.mem_sup_right hk⟩
    have hfix : ((f y ⟨k, Subgroup.mem_sup_right hk⟩ : ↥(K1 ⊔ K2)) : G) = k :=
      congrArg Subtype.val (hψK2 ⟨k, Subgroup.mem_sup_right hk⟩ hk)
    rw [hfix] at hnk
    have e : (y : G) * k * (y : G)⁻¹ * k⁻¹ = n := by rw [hnk]; group
    rw [e]
    exact hn

end CFSG.OddStandard.SmallF3.Omega

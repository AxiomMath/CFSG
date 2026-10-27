module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeIdentOrbit
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeXTransport

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup MulAction CFSG.Quasithin
open CFSG.Quasithin.H (congrHom congrHom_injective)

structure CocodeX (V : Type) [CommGroup V] [Finite V] (H : Subgroup (MulAut V)) (t z : V) :
    Prop where
  card_Ctz : Nat.card ↥(H ⊓ centSub (zpowers z) ⊓ centSub (zpowers t)) = 2 ^ 8 * 3 * 5
  card_NV : Nat.card ↥(H ⊓ stabSub (closure {t, z})) = 2 ^ 9 * 3 * 5
  swap : ∃ g ∈ H ⊓ stabSub (closure {t, z}), g t = t * z
  card_P : Nat.card ↥(TwoFi22.O2In (H ⊓ centSub (zpowers z))) = 2 ^ 6
  O2_NV : TwoFi22.O2In (H ⊓ stabSub (closure {t, z})) = TwoFi22.O2In (H ⊓ centSub (zpowers z))
  P_comm : ∀ a ∈ TwoFi22.O2In (H ⊓ centSub (zpowers z)),
    ∀ b ∈ TwoFi22.O2In (H ⊓ centSub (zpowers z)), a * b = b * a
  P_sq : ∀ a ∈ TwoFi22.O2In (H ⊓ centSub (zpowers z)), a ^ 2 = 1
  lattice : ∀ U : Subgroup V, (∀ g ∈ H ⊓ centSub (zpowers z), ∀ u ∈ U, g u ∈ U) →
    U = ⊥ ∨ U = zpowers z ∨ Nat.card ↥U = 2 ^ 7 ∨ U = ⊤
  P_irred : ∀ S : Subgroup (MulAut V), S ≤ TwoFi22.O2In (H ⊓ centSub (zpowers z)) →
    (∀ g ∈ H ⊓ centSub (zpowers z), ∀ s ∈ S, g * s * g⁻¹ ∈ S) →
    S = ⊥ ∨ S = TwoFi22.O2In (H ⊓ centSub (zpowers z))
  comm_ne : commV (TwoFi22.O2In (H ⊓ centSub (zpowers z))) ≠ zpowers z
  card_O23 : Nat.card ↥(TwoFi22.O23In (H ⊓ centSub (zpowers z))) = 3 * 2 ^ 6
  r_fpf : ∀ r ∈ TwoFi22.O23In (H ⊓ centSub (zpowers z)), orderOf r = 3 →
    ∀ p ∈ TwoFi22.O2In (H ⊓ centSub (zpowers z)), r * p * r⁻¹ * p⁻¹ = 1 → p = 1
  r_E : ∀ r ∈ TwoFi22.O23In (H ⊓ centSub (zpowers z)), orderOf r = 3 →
    ∀ U : Subgroup V, (∀ g ∈ H ⊓ centSub (zpowers z), ∀ u ∈ U, g u ∈ U) →
      Nat.card ↥U = 2 ^ 7 → ∀ v : V, r v * v⁻¹ ∈ U
  exists_A : ∃ A : Subgroup (MulAut V), A ≤ H ⊓ stabSub (closure {t, z}) ∧
    (∀ a ∈ A, ∀ r ∈ TwoFi22.O23In (H ⊓ centSub (zpowers z)), orderOf r = 3 →
      a * r * a⁻¹ * r⁻¹ ∈ TwoFi22.O2In (H ⊓ centSub (zpowers z))) ∧
    ∀ U : Subgroup V, (∀ g ∈ H ⊓ centSub (zpowers z), ∀ u ∈ U, g u ∈ U) →
      Nat.card ↥U = 2 ^ 7 → HomVanishX A (TwoFi22.O2In (H ⊓ centSub (zpowers z))) U
  exists_sextet : ∀ U : Subgroup V, (∀ g ∈ H ⊓ centSub (zpowers z), ∀ u ∈ U, g u ∈ U) →
    Nat.card ↥U = 2 ^ 7 → ∃ z' ∈ U, z' ≠ z ∧ z' ∈ orbit ↥H z
  exists_perfect : ∃ Y : Subgroup (MulAut V), Y ≤ H ⊓ centSub (zpowers z) ∧ ⁅Y, Y⁆ = Y ∧
    commV Y = ⊤ ∧ Nat.card ↥Y = 2 ^ 9 * 3 ^ 3 * 5
  normal_card : ∀ M : Subgroup (MulAut V), M ≤ H ⊓ centSub (zpowers z) →
    TwoFi22.O2In (H ⊓ centSub (zpowers z)) ≤ M →
    (∀ g ∈ H ⊓ centSub (zpowers z), ∀ m ∈ M, g * m * g⁻¹ ∈ M) →
    Nat.card ↥M = 2 ^ 6 ∨ Nat.card ↥M = 3 * 2 ^ 6 ∨ Nat.card ↥M = 1080 * 2 ^ 6 ∨
      Nat.card ↥M = 2160 * 2 ^ 6

section Map

variable {V W : Type} [CommGroup V] [CommGroup W] [Finite V] [Finite W]

theorem CocodeX.of_map (e : V ≃* W) {H : Subgroup (MulAut V)} {t z : V}
    (h : CocodeX W (H.map (congrHom e)) (e t) (e z)) : CocodeX V H t z := by
  have hc : Function.Injective (congrHom e) := congrHom_injective e
  have hcs : Function.Surjective (congrHom e) := (MulAut.congr e).surjective
  have hTz : (H ⊓ centSub (zpowers z)).map (congrHom e) =
      H.map (congrHom e) ⊓ centSub (zpowers (e z)) :=
    Quasithin.H.ZTrans.inf_centSub_map_congrHom e H z
  have hTzt : (H ⊓ centSub (zpowers z) ⊓ centSub (zpowers t)).map (congrHom e) =
      H.map (congrHom e) ⊓ centSub (zpowers (e z)) ⊓ centSub (zpowers (e t)) := by
    rw [Subgroup.map_inf _ _ _ hc, hTz, centSub_zpowers_map e t]
  have hTV : (H ⊓ stabSub (closure {t, z})).map (congrHom e) =
      H.map (congrHom e) ⊓ stabSub (closure {e t, e z}) := by
    rw [Subgroup.map_inf _ _ _ hc, stabSub_closure_pair_map e t z]
  have hP : (TwoFi22.O2In (H ⊓ centSub (zpowers z))).map (congrHom e) =
      TwoFi22.O2In (H.map (congrHom e) ⊓ centSub (zpowers (e z))) := by
    rw [← hTz]
    exact (Quasithin.H.ZTrans.pCoreOf_map_congrHom e _).symm
  have hPV : (TwoFi22.O2In (H ⊓ stabSub (closure {t, z}))).map (congrHom e) =
      TwoFi22.O2In (H.map (congrHom e) ⊓ stabSub (closure {e t, e z})) := by
    rw [← hTV]
    exact (Quasithin.H.ZTrans.pCoreOf_map_congrHom e _).symm
  have hO23 : (TwoFi22.O23In (H ⊓ centSub (zpowers z))).map (congrHom e) =
      TwoFi22.O23In (H.map (congrHom e) ⊓ centSub (zpowers (e z))) := by
    rw [← hTz]
    exact (O23In_map_of_injective _ hc _).symm
  have memP : ∀ a ∈ TwoFi22.O2In (H ⊓ centSub (zpowers z)),
      congrHom e a ∈ TwoFi22.O2In (H.map (congrHom e) ⊓ centSub (zpowers (e z))) :=
    fun a ha => hP ▸ Subgroup.mem_map_of_mem _ ha
  have memO : ∀ r ∈ TwoFi22.O23In (H ⊓ centSub (zpowers z)),
      congrHom e r ∈ TwoFi22.O23In (H.map (congrHom e) ⊓ centSub (zpowers (e z))) :=
    fun r hr => hO23 ▸ Subgroup.mem_map_of_mem _ hr
  have memU : ∀ U : Subgroup V, (∀ g ∈ H ⊓ centSub (zpowers z), ∀ u ∈ U, g u ∈ U) →
      ∀ g ∈ H.map (congrHom e) ⊓ centSub (zpowers (e z)), ∀ u ∈ U.map e.toMonoidHom,
        g u ∈ U.map e.toMonoidHom := fun U hU => hTz ▸ invariant_map e hU
  have hord : ∀ r : MulAut V, orderOf r = 3 → orderOf (congrHom e r) = 3 := fun r hr =>
    (orderOf_injective (congrHom e) hc r).trans hr
  have hcard : ∀ A : Subgroup (MulAut V), Nat.card ↥(A.map (congrHom e)) = Nat.card ↥A :=
    Quasithin.H.card_map_congrHom e
  have hcardU : ∀ U : Subgroup V, Nat.card ↥(U.map e.toMonoidHom) = Nat.card ↥U := fun U =>
    Subgroup.card_map_of_injective e.injective
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [← hcard, hTzt]
    exact h.card_Ctz
  ·
    rw [← hcard, hTV]
    exact h.card_NV
  ·
    obtain ⟨g, hg, hgt⟩ := h.swap
    rw [← hTV] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    rw [congrHom_apply_equiv, ← map_mul] at hgt
    exact ⟨g', hg', e.injective hgt⟩
  ·
    rw [← hcard, hP]
    exact h.card_P
  ·
    apply Subgroup.map_injective hc
    rw [hPV, hP]
    exact h.O2_NV
  ·
    intro a ha b hb
    exact hc (by rw [map_mul, map_mul]; exact h.P_comm _ (memP a ha) _ (memP b hb))
  ·
    intro a ha
    exact hc (by rw [map_pow, map_one]; exact h.P_sq _ (memP a ha))
  ·
    intro U hU
    rcases h.lattice (U.map e.toMonoidHom) (memU U hU) with h1 | h1 | h1 | h1
    · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h1)
    · refine Or.inr (Or.inl (Subgroup.map_injective (f := e.toMonoidHom) e.injective ?_))
      rw [h1, MonoidHom.map_zpowers]
      rfl
    · exact Or.inr (Or.inr (Or.inl (by rwa [← hcardU])))
    · exact Or.inr (Or.inr (Or.inr ((Quasithin.H.map_mulEquiv_eq_top_iff e).1 h1)))
  ·
    intro S hS hSinv
    have h1 := h.P_irred (S.map (congrHom e)) (hP ▸ Subgroup.map_mono hS)
      (hTz ▸ conj_invariant_map e hSinv)
    rcases h1 with h1 | h1
    · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective _ hc).1 h1)
    · exact Or.inr (Subgroup.map_injective hc (h1.trans hP.symm))
  ·
    intro hEq
    apply h.comm_ne
    rw [← hP, Quasithin.H.ZTrans.commV_map_congrHom e, hEq, MonoidHom.map_zpowers]
    rfl
  ·
    rw [← hcard, hO23]
    exact h.card_O23
  ·
    intro r hr hr3 p hp hcomm
    have h1 := h.r_fpf (congrHom e r) (memO r hr) (hord r hr3) (congrHom e p) (memP p hp)
      (by rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hcomm, map_one])
    exact hc (h1.trans (map_one _).symm)
  ·
    intro r hr hr3 U hU hUc v
    have h1 := h.r_E (congrHom e r) (memO r hr) (hord r hr3) (U.map e.toMonoidHom) (memU U hU)
      (by rwa [hcardU]) (e v)
    rw [congrHom_apply_equiv, ← map_inv, ← map_mul] at h1
    exact (Subgroup.mem_map_iff_mem e.injective).1 h1
  ·
    obtain ⟨A, hA, hAr, hAU⟩ := h.exists_A
    have hAc : (A.comap (congrHom e)).map (congrHom e) = A :=
      Subgroup.map_comap_eq_self_of_surjective hcs A
    refine ⟨A.comap (congrHom e), ?_, ?_, ?_⟩
    · have h1 := Subgroup.comap_mono (f := congrHom e) hA
      rw [← hTV, Subgroup.comap_map_eq_self_of_injective hc] at h1
      exact h1
    · intro a ha r hr hr3
      have h1 := hAr (congrHom e a) ha (congrHom e r) (memO r hr) (hord r hr3)
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← hP] at h1
      exact (Subgroup.mem_map_iff_mem hc).1 h1
    · intro U hU hUc
      refine HomVanishX.of_map e ?_
      have h1 := hAU (U.map e.toMonoidHom) (memU U hU) (by rwa [hcardU])
      rwa [← hAc, ← hP] at h1
  ·
    intro U hU hUc
    obtain ⟨w, hwU, hwne, hworb⟩ := h.exists_sextet (U.map e.toMonoidHom) (memU U hU)
      (by rwa [hcardU])
    obtain ⟨z', hz'U, rfl⟩ := hwU
    refine ⟨z', hz'U, fun heq => hwne (by rw [heq]; rfl), ?_⟩
    have h1 := (mem_orbit_map_congrHom_iff e H z (e z')).1 hworb
    rwa [MulEquiv.symm_apply_apply] at h1
  ·
    obtain ⟨Y, hYle, hY1, hY2, hYc⟩ := h.exists_perfect
    have hYm : (Y.comap (congrHom e)).map (congrHom e) = Y :=
      Subgroup.map_comap_eq_self_of_surjective hcs Y
    refine ⟨Y.comap (congrHom e), ?_, ?_, ?_, ?_⟩
    · have h1 := Subgroup.comap_mono (f := congrHom e) hYle
      rw [← hTz, Subgroup.comap_map_eq_self_of_injective hc] at h1
      exact h1
    · apply Subgroup.map_injective hc
      rw [Subgroup.map_commutator, hYm]
      exact hY1
    · rw [← (Quasithin.H.map_mulEquiv_eq_top_iff e), ← Quasithin.H.ZTrans.commV_map_congrHom e,
        hYm]
      exact hY2
    · rw [← hcard, hYm]
      exact hYc
  ·
    intro M hM hPM hMinv
    have h1 := h.normal_card (M.map (congrHom e))
      (hTz ▸ Subgroup.map_mono hM) (hP ▸ Subgroup.map_mono hPM)
      (hTz ▸ conj_invariant_map e hMinv)
    rwa [hcard] at h1

end Map

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup
open CFSG.FeitThompson (IsTIWithNormalizer)
open CFSG.FeitThompson (fittingIn satSet mem_satSet_iff)
open CFSG.FeitThompson.Prep05 (IsMinimalSimpleOdd fittingOf hallCoreOf)

universe u

variable {G : Type*} [Group G]

theorem fittingIn_eq_fittingOf [Finite G] (M : Subgroup G) : fittingIn M = fittingOf M := (rfl)

theorem centralizer_singleton_le_of_isTIWithNormalizer
    {D : Set G} {L : Subgroup G} (h : IsTIWithNormalizer D L) {y : G} (hy : y ∈ D) :
    centralizer {y} ≤ L := by
  intro c hc
  by_contra hcL
  refine Set.disjoint_left.1 (h.disjoint_conj_image c hcL) hy ⟨y, hy, ?_⟩
  have hcy : c * y = y * c := mem_centralizer_singleton_iff.1 hc
  simp only [MulAut.conj_apply]
  rw [hcy, mul_inv_cancel_right]

theorem FCH_paired_fitting_saturations_disjoint
    (h₁ : Statements.FNI_type_p_elementary_core_structure.{u}) :
    Statements.FCH_paired_fitting_saturations_disjoint.{u} := by
  intro G _ _ hG M U W₁ W₂ hM hcM H F C hH hF hC p q u hp hq hu N V₀ hN hNM hV₀N hcN
    HN FN DN hHN hFN hDN v hv
  subst hF hFN
  have hG' : IsMinimalSimpleOdd G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨-, hpp, hqp, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hTIF⟩ :=
    h₁ G hG' M U W₁ W₂ hM hcM p q hp hq
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hcardHN, -, -, -, -, -, -, -, habN, -, -⟩ :=
    h₁ G hG' N V₀ W₂ W₁ hN hcN q p hq hp
  have habN' : IsMulCommutative ↥(fittingIn N) := habN
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨⟨hxF, hx1⟩, hxFN, -⟩
  obtain ⟨g, y, hyF, hgy⟩ := mem_satSet_iff.1 hxF
  obtain ⟨h, y', hy'FN, hhy⟩ := mem_satSet_iff.1 hxFN
  simp only at hgy hhy
  have hy1 : y ∉ ({1} : Set G) := by
    intro hy
    refine hx1 ?_
    rw [Set.mem_singleton_iff] at hy ⊢
    rw [← hgy, hy]
    group
  set k : G := g * h⁻¹ with hk
  have hyconj : y = MulAut.conj k y' := by
    have hgh : g⁻¹ * y * g = h⁻¹ * y' * h := by rw [hgy, hhy]
    have hy' : y = g * (h⁻¹ * y' * h) * g⁻¹ := by rw [← hgh]; group
    simp only [MulAut.conj_apply, hk]
    rw [hy']; group
  set K : Subgroup G := (fittingIn N).map (MulAut.conj k).toMonoidHom with hK
  have hKcent : K ≤ centralizer {y} := by
    intro w hw
    obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.1 hw
    rw [mem_centralizer_singleton_iff, hyconj]
    have hcomm : w₀ * y' = y' * w₀ := setLike_mul_comm hw₀ hy'FN
    calc (MulAut.conj k).toMonoidHom w₀ * MulAut.conj k y'
        = MulAut.conj k (w₀ * y') := by simp [map_mul]
      _ = MulAut.conj k (y' * w₀) := by rw [hcomm]
      _ = MulAut.conj k y' * (MulAut.conj k).toMonoidHom w₀ := by simp [map_mul]
  have hKM : K ≤ M :=
    hKcent.trans (centralizer_singleton_le_of_isTIWithNormalizer hTIF
      ⟨(fittingIn_eq_fittingOf M) ▸ hyF, hy1⟩)
  have hcardK : Nat.card ↥K = Nat.card ↥(fittingIn N) :=
    Subgroup.card_map_of_injective (fun a b hab => (MulAut.conj k).injective hab)
  have hFNdvd : Nat.card ↥(fittingIn N) ∣ Nat.card ↥M := by
    rw [← hcardK]; exact Subgroup.card_dvd_of_le hKM
  have hHNdvd : Nat.card ↥(hallCoreOf N) ∣ Nat.card ↥(fittingIn N) :=
    Subgroup.card_dvd_of_le hcN.hallCore_le_fittingRaw_map
  have hqpow : q ^ p ∣ Nat.card ↥M := by
    rw [← hcardHN]; exact hHNdvd.trans hFNdvd
  have hMcard : Nat.card ↥M = Nat.card (⁅M, M⁆ : Subgroup G) * q := by
    rw [hcM.natCard_M_eq, hq]
  have hcop : Nat.Coprime q (Nat.card (⁅M, M⁆ : Subgroup G)) := by
    rw [hq]; exact hcM.coprime_natCard_W₁_natCard_commutator
  have hstep : q ^ (p - 1) ∣ Nat.card (⁅M, M⁆ : Subgroup G) := by
    refine (Nat.mul_dvd_mul_iff_right hqp.pos).1 ?_
    rw [← pow_succ, Nat.sub_add_cancel hpp.one_lt.le, ← hMcard]
    exact hqpow
  have hqdvd : q ∣ Nat.card (⁅M, M⁆ : Subgroup G) :=
    (dvd_pow_self q (Nat.sub_ne_zero_of_lt hpp.one_lt)).trans hstep
  exact hqp.one_lt.ne' (hcop.eq_one_of_dvd hqdvd)

end

end CFSG.FeitThompson.Proofs

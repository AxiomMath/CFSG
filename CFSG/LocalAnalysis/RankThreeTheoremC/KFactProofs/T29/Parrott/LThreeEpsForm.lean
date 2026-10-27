module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsLift
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26AutBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open Subgroup
open CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts (centerDescend centerDescend_mk psuConj psuField
  psuField_mem_range_psuConj_iff)
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.LocalBalance (IsInnDiagThree IsFieldAutThree)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (conjAut fieldAut linearAutGroup
  conjAut_mem_linearAutGroup)

namespace LModel

variable {X : Type} [Group X] {L : Subgroup X} [L.Normal] {π : Bool} {p f : ℕ} {K : Type}
  [Field K] {ν : ↥(slPi π 3 (p ^ f) K) →* ↥L}

theorem conj_eq_of_congr (M : LModel L π p f K ν) {g : X} {ζ : MulAut ↥(slPi π 3 (p ^ f) K)}
    (h : MulAut.congr M.barEquiv.symm (centerDescend ↥L (MulAut.conjNormal g)) =
      centerDescend _ ζ) (s : ↥(slPi π 3 (p ^ f) K)) :
    g * ((ν s : ↥L) : X) * g⁻¹ = ((ν (ζ s) : ↥L) : X) := by
  haveI := M.isPerfect
  have key : ∀ s : ↥(slPi π 3 (p ^ f) K),
      ((ν.comp ζ.toMonoidHom) s)⁻¹ * ((MulAut.conjNormal g).toMonoidHom.comp ν) s ∈
        Subgroup.center ↥L := by
    intro s
    have h1 := congrArg (fun φ : MulAut (↥(slPi π 3 (p ^ f) K) ⧸
      Subgroup.center ↥(slPi π 3 (p ^ f) K)) => φ (QuotientGroup.mk s)) h
    change M.barEquiv.symm (centerDescend ↥L (MulAut.conjNormal g)
      (M.barEquiv (QuotientGroup.mk s))) = centerDescend _ ζ (QuotientGroup.mk s) at h1
    rw [M.barEquiv_mk, centerDescend_mk, centerDescend_mk] at h1
    have h2 : (QuotientGroup.mk (MulAut.conjNormal g (ν s)) : ↥L ⧸ Subgroup.center ↥L) =
        QuotientGroup.mk (ν (ζ s)) := by
      rw [← M.barEquiv_mk, ← h1, MulEquiv.apply_symm_apply]
    exact QuotientGroup.eq.1 h2.symm
  have h3 := eq_of_inv_mul_mem_center _ _ key s
  have h4 := congrArg Subtype.val h3
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conjNormal_apply] at h4
  exact h4

theorem congr_of_isLiftAt (M : LModel L π p f K ν) {g : X} {y : GL (Fin 3) K}
    (hg : IsLiftAt ν g y) :
    MulAut.congr M.barEquiv.symm (centerDescend ↥L (MulAut.conjNormal g)) =
      centerDescend _ (M.conjBy hg.mem) := by
  ext z
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective z
  change M.barEquiv.symm (centerDescend ↥L (MulAut.conjNormal g)
    (M.barEquiv (QuotientGroup.mk s))) = centerDescend _ (M.conjBy hg.mem) (QuotientGroup.mk s)
  rw [M.barEquiv_mk, centerDescend_mk, centerDescend_mk, MulEquiv.symm_apply_eq, M.barEquiv_mk]
  congr 1
  apply Subtype.ext
  rw [MulAut.conjNormal_apply]
  exact hg.act s _ (M.coe_conjBy hg.mem s)

theorem congr_of_isFieldAt (M : LModel L π p f K ν) {g : X} {σ : K ≃+* K} {H : GL (Fin 3) K}
    (hg : IsFieldAt ν g σ H) :
    MulAut.congr M.barEquiv.symm (centerDescend ↥L (MulAut.conjNormal g)) =
      centerDescend _ (M.fieldBy σ hg.mem) := by
  ext z
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective z
  change M.barEquiv.symm (centerDescend ↥L (MulAut.conjNormal g)
    (M.barEquiv (QuotientGroup.mk s))) = centerDescend _ (M.fieldBy σ hg.mem) (QuotientGroup.mk s)
  rw [M.barEquiv_mk, centerDescend_mk, centerDescend_mk, MulEquiv.symm_apply_eq, M.barEquiv_mk]
  congr 1
  apply Subtype.ext
  rw [MulAut.conjNormal_apply]
  exact hg.act s _ (M.coe_fieldBy σ hg.mem s)

theorem exists_conjBy_of_mem_inndiag (M : LModel L π p f K ν) (pkg : EtaPkg M.piField M.two_lt)
    {κ : MulAut pkg.M} (hκ : κ ∈ pkg.P.inndiag) :
    ∃ (H : GL (Fin 3) K) (hH : H ∈ glPi π 3 (p ^ f) K),
      MulAut.congr pkg.η.symm κ = centerDescend _ (M.conjBy hH) := by
  obtain ⟨H, hH, hHs⟩ := pkg.conj_of_inndiag κ hκ
  refine ⟨H, hH, ?_⟩
  ext z
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective z
  rw [centerDescend_mk]
  exact hHs s _ (M.coe_conjBy hH s)

theorem dichotomy (M : LModel L π p f K ν) {g : X} (hg : g ^ 3 = 1) :
    (∃ y, IsLiftAt ν g y) ∨ ∃ σ H, IsFieldAt ν g σ H := by
  obtain ⟨pkg⟩ := exists_etaPkg M.piField M.two_lt
  set β := centerDescend ↥L (MulAut.conjNormal g) with hβ
  set τ := MulAut.congr (M.barEquiv.symm.trans pkg.η) β with hτ
  have hτ3 : τ ^ 3 = 1 := by
    rw [hτ, hβ, ← map_pow, ← map_pow, ← map_pow, hg, map_one, map_one, map_one]
  have hτ' : MulAut.congr pkg.η.symm τ = MulAut.congr M.barEquiv.symm β := by
    rw [hτ, congr_trans', congr_symm_congr]
  rcases pkg.dich τ hτ3 with hin | ⟨σ, hσ, κ, hκ, hτκ⟩
  · obtain ⟨y, hy, hyeq⟩ := M.exists_conjBy_of_mem_inndiag pkg hin
    rw [hτ'] at hyeq
    refine Or.inl ⟨y, hy, fun s t ht => ?_⟩
    rw [M.conj_eq_of_congr hyeq s]
    congr 2
    exact Subtype.ext ((M.coe_conjBy hy s).trans ht.symm)
  · obtain ⟨H, hH, hHeq⟩ := M.exists_conjBy_of_mem_inndiag pkg hκ
    have heq : MulAut.congr M.barEquiv.symm β = centerDescend _ (M.fieldBy σ hH) := by
      rw [← hτ', hτκ, map_mul, map_mul, map_inv, hHeq, congr_symm_congr, fieldBy, map_mul,
        map_mul, map_inv]
    refine Or.inr ⟨σ, H, hσ, hH, fun s t ht => ?_⟩
    rw [M.conj_eq_of_congr heq s]
    congr 2
    exact Subtype.ext ((M.coe_fieldBy σ hH s).trans ht.symm)

theorem congr_etaTrue_fieldBy {L : Subgroup X} {p f : ℕ} {K : Type} [Field K]
    {ν : ↥(slPi true 3 (p ^ f) K) →* ↥L} (M : LModel L true p f K ν) (σ : K ≃+* K)
    {H : GL (Fin 3) K} (hH : H ∈ glPi true 3 (p ^ f) K) :
    MulAut.congr (etaTrue (p ^ f) K) (centerDescend _ (M.fieldBy σ hH)) =
      conjAut 3 K H * fieldAut 3 K σ * (conjAut 3 K H)⁻¹ := by
  rw [fieldBy, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv,
    congr_etaTrue_conj (p ^ f) (M.conjBy hH) (M.coe_conjBy hH),
    congr_etaTrue_frob M.piField σ]

theorem congr_etaFalse_fieldBy {L : Subgroup X} {p f : ℕ} {K : Type} [Field K]
    {ν : ↥(slPi false 3 (p ^ f) K) →* ↥L} (M : LModel L false p f K ν) (σ : K ≃+* K)
    {H : GL (Fin 3) K} (hH : H ∈ glPi false 3 (p ^ f) K) :
    MulAut.congr (etaFalse M.piField M.two_lt) (centerDescend _ (M.fieldBy σ hH)) =
      psuConj M.piField.unitary ⟨H, CFSG.RankThree.PartTwo.KFacts.mem_unitaryIsom3.2
          ((mem_glPi_false M.piField.unitary).1 hH)⟩ * psuField M.piField.unitary σ *
        (psuConj M.piField.unitary ⟨H, CFSG.RankThree.PartTwo.KFacts.mem_unitaryIsom3.2
          ((mem_glPi_false M.piField.unitary).1 hH)⟩)⁻¹ := by
  rw [fieldBy, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv,
    congr_eta_false_conj M.piField M.two_lt (M.conjBy hH) hH (M.coe_conjBy hH),
    congr_eta_false_frob M.piField M.two_lt σ]

theorem not_isLiftAt_of_isFieldAt (M : LModel L π p f K ν) {g : X} {σ : K ≃+* K}
    {H y : GL (Fin 3) K} (hf : IsFieldAt ν g σ H) (hl : IsLiftAt ν g y) : False := by
  have heq : centerDescend _ (M.conjBy hl.mem) = centerDescend _ (M.fieldBy σ hf.mem) := by
    rw [← M.congr_of_isLiftAt hl, ← M.congr_of_isFieldAt hf]
  have hσ1 : σ ≠ 1 := by
    intro h1
    have := hf.order
    rw [h1, orderOf_one] at this
    omega
  have := M.piField.finite
  cases π
  · have h1 := congrArg (MulAut.congr (etaFalse M.piField M.two_lt)) heq
    rw [congr_etaFalse_fieldBy M σ hf.mem,
      congr_eta_false_conj M.piField M.two_lt (M.conjBy hl.mem) hl.mem (M.coe_conjBy hl.mem)] at h1
    apply hσ1
    refine (psuField_mem_range_psuConj_iff (h := M.piField.unitary)).1 ?_
    set A := psuConj M.piField.unitary ⟨H, CFSG.RankThree.PartTwo.KFacts.mem_unitaryIsom3.2
      ((mem_glPi_false M.piField.unitary).1 hf.mem)⟩
    set B := psuConj M.piField.unitary ⟨y, CFSG.RankThree.PartTwo.KFacts.mem_unitaryIsom3.2
      ((mem_glPi_false M.piField.unitary).1 hl.mem)⟩
    have : psuField M.piField.unitary σ = A⁻¹ * B * A := by
      rw [h1]; group
    rw [this]
    refine mul_mem (mul_mem (inv_mem ⟨_, rfl⟩) ⟨_, rfl⟩) ⟨_, rfl⟩
  · have h1 := congrArg (MulAut.congr (etaTrue (p ^ f) K)) heq
    rw [congr_etaTrue_fieldBy M σ hf.mem,
      congr_etaTrue_conj (p ^ f) (M.conjBy hl.mem) (M.coe_conjBy hl.mem)] at h1
    have h3 : 3 ∣ Nat.card K - 1 := by
      have hc : Nat.card K = p ^ f := M.piField.card
      have hm : p ^ f % 3 = 1 := M.modThree
      omega
    apply hσ1
    refine (CFSG.Quasithin.A318P.l3FrameLinear h3).fld_inter σ ?_
    change fieldAut 3 K σ ∈ linearAutGroup 3 K
    have : fieldAut 3 K σ = (conjAut 3 K H)⁻¹ * conjAut 3 K y * conjAut 3 K H := by
      rw [h1]; group
    rw [this]
    exact mul_mem (mul_mem (inv_mem (conjAut_mem_linearAutGroup H))
      (conjAut_mem_linearAutGroup y)) (conjAut_mem_linearAutGroup H)

theorem not_mem_centralizer_of_isFieldAt (M : LModel L π p f K ν) {g : X} {σ : K ≃+* K}
    {H : GL (Fin 3) K} (hf : IsFieldAt ν g σ H) : g ∉ centralizer (L : Set X) :=
  fun hc => M.not_isLiftAt_of_isFieldAt hf (isLiftAt_one_of_mem_centralizer hc)

theorem not_mem_of_isFieldAt (M : LModel L π p f K ν) {g : X} {σ : K ≃+* K}
    {H : GL (Fin 3) K} (hf : IsFieldAt ν g σ H) : g ∉ L := by
  intro hgL
  obtain ⟨s, hs⟩ := M.surj ⟨g, hgL⟩
  have hl := isLiftAt_of_mem M s
  rw [hs] at hl
  exact M.not_isLiftAt_of_isFieldAt hf hl

theorem isInnDiagThree_of_isLiftAt (M : LModel L π p f K ν) {g : X} {y : GL (Fin 3) K}
    (hg : IsLiftAt ν g y) : IsInnDiagThree (MulAut.conjNormal g : MulAut ↥L) := by
  have := M.piField.finite
  cases π
  · refine Or.inr (isInnDiagPSU3_of_model M.piField.unitary
      (M.barEquiv.symm.trans (etaFalse M.piField M.two_lt)) ?_)
    rw [congr_trans', M.congr_of_isLiftAt hg,
      congr_eta_false_conj M.piField M.two_lt (M.conjBy hg.mem) hg.mem (M.coe_conjBy hg.mem)]
    exact ⟨_, rfl⟩
  · refine Or.inl (isInnDiagPSL3_of_model (M.barEquiv.symm.trans (etaTrue (p ^ f) K)) ?_)
    rw [congr_trans', M.congr_of_isLiftAt hg,
      congr_etaTrue_conj (p ^ f) (M.conjBy hg.mem) (M.coe_conjBy hg.mem)]
    exact conjAut_mem_linearAutGroup y

theorem isFieldAutThree_of_isFieldAt (M : LModel L π p f K ν) {g : X} {σ : K ≃+* K}
    {H : GL (Fin 3) K} (hg : IsFieldAt ν g σ H) :
    IsFieldAutThree (MulAut.conjNormal g : MulAut ↥L) := by
  have := M.piField.finite
  cases π
  · refine Or.inr (Or.inr (CFSG.HardMathSupport.Solomon.LocalBalance.AutL3.isFieldAutPSU3_of_model
      M.piField.unitary (M.barEquiv.symm.trans (etaFalse M.piField M.two_lt)) σ
      (by rw [hg.order]; decide)
      (psuConj M.piField.unitary ⟨H, CFSG.RankThree.PartTwo.KFacts.mem_unitaryIsom3.2
        ((mem_glPi_false M.piField.unitary).1 hg.mem)⟩) ?_))
    rw [congr_trans', M.congr_of_isFieldAt hg, congr_etaFalse_fieldBy M σ hg.mem]
  · refine Or.inr (Or.inl (CFSG.HardMathSupport.Solomon.LocalBalance.AutL3.isFieldAutPSL3_of_model
      (M.barEquiv.symm.trans (etaTrue (p ^ f) K)) σ (conjAut 3 K H) ?_))
    rw [congr_trans', M.congr_of_isFieldAt hg, congr_etaTrue_fieldBy M σ hg.mem]

end LModel

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

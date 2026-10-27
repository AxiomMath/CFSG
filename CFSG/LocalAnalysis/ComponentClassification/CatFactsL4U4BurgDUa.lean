module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBCoverU
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBSU4Lift

public section

namespace CFSG.ComponentClassification.CatFactsL4U4.BurgD

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification CFSG.ComponentClassification.Burgoyne
open CFSG.ComponentClassification.Burgoyne.B CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.U
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.UnbalancingLocal
open scoped MatrixGroups

variable {p f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F)

@[expose] noncomputable def negOneSU : StatedSU 4 (p ^ f) F :=
  uSUmk h (-1) (by rw [det_neg, det_one, Fintype.card_fin]; norm_num)
    (by
      have hm : (-1 : Matrix (Fin 4) (Fin 4) F).map h.bar = -1 := by
        rw [Matrix.map_neg (M := (1 : Matrix (Fin 4) (Fin 4) F)) h.bar
          (fun a => map_neg h.bar a), Matrix.map_one _ (map_zero h.bar) (map_one h.bar)]
      rw [hm, transpose_neg, transpose_one, neg_mul_neg, Matrix.one_mul])

theorem coe_negOneSU :
    (((negOneSU h : StatedSU 4 (p ^ f) F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = -1 :=
  rfl

theorem exists_su4_transport {J : Type} [Group J] [Finite J] {K : Subgroup J} [K.Normal]
    {t : J} {Y : Subgroup J} {c : K ⧸ pPrimeCore 2 K} (hH : PropBHyp J K t Y c) (hp2 : p ≠ 2)
    (θ : GeneralizedFitting.subgroup (rhoZ K).range ≃* StatedProj (StatedSU 4 (p ^ f) F))
    {A : uU h 4} (hA : socleAction θ ((rhoZ K).rangeRestrict t) = uConjAut h (by norm_num) A)
    {H : uU h 4} {J₀ : Finset (Fin 4)} {l : F} (hl0 : l ≠ 0)
    (hHA : (((H : GL (Fin 4) F)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        ((H : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = l • PSL.signMat F J₀) :
    ∃ (e : StatedSU 4 (p ^ f) F ≃* (K ⧸ pPrimeCore 2 K))
      (ψ' : (rhoZ K).range →* MulAut (StatedProj (StatedSU 4 (p ^ f) F))),
      Function.Injective ψ' ∧
      (MulAut.conj : StatedProj (StatedSU 4 (p ^ f) F) →*
        MulAut (StatedProj (StatedSU 4 (p ^ f) F))).range ≤ ψ'.range ∧
      ψ' ((rhoZ K).rangeRestrict t) = uConjAut h (by norm_num) (uSign h J₀) ∧
      e (negOneSU h) = c ∧
      ∀ (j : J) (g : StatedSU 4 (p ^ f) F), projH _ (e.symm (phiO K j (e g))) =
        ψ' ((rhoZ K).rangeRestrict j) (projH _ g) := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  obtain ⟨hq, hM4, -, -, -, s, hs2, -, -, Q, hQs, hQc, hQiso, hcZ, hcQ, hc2, -⟩ := id hH
  have hII : PropBHypII (K ⧸ pPrimeCore 2 K) c := ⟨s, hs2, Q, hQs, hQc, hQiso, hcZ, hcQ, hc2⟩
  obtain ⟨hsimple, hnab, -, -, -⟩ := hM4
  set ψ := socleAction θ with hψdef
  have hψ := socleAction_injective hsimple hnab θ
  have hInn : (MulAut.conj : StatedProj (StatedSU 4 (p ^ f) F) →*
      MulAut (StatedProj (StatedSU 4 (p ^ f) F))).range ≤ ψ.range := by
    rintro _ ⟨x, rfl⟩
    exact conj_mem_range_socleAction θ x
  have hinj := PSL.conj_injective_of_mulEquiv hsimple hnab θ
  obtain ⟨ψ', hψ', hInn', hψ't, hpre⟩ := exists_uconj_transfer' h (by norm_num) hψ hInn hA H
    hl0 (A' := uSign h J₀) (by rw [coe_uSign]; exact hHA)
  have hsocle : ∀ x : (rhoZ K).range, x ∈ GeneralizedFitting.subgroup (rhoZ K).range ↔
      ψ' x ∈ (MulAut.conj : StatedProj (StatedSU 4 (p ^ f) F) →*
        MulAut (StatedProj (StatedSU 4 (p ^ f) F))).range :=
    fun x => by rw [hpre, mem_socle_iff hsimple hnab θ]
  set β : StatedSU 4 (p ^ f) F →* (rhoZ K).range :=
    factorHom hψ' (conjProjH (StatedSU 4 (p ^ f) F)) (fun g => hInn' ⟨_, rfl⟩) with hβ
  have hrange := liftHom_range_eq K hq hsimple hnab
  have hβr : β.range = (liftHom K).range := by
    rw [hrange]
    ext x
    rw [hsocle]
    constructor
    · rintro ⟨g, rfl⟩
      rw [factorHom_spec]
      exact ⟨_, rfl⟩
    · rintro ⟨y, hy⟩
      obtain ⟨g, rfl⟩ := projH_surjective y
      refine ⟨g, hψ' ?_⟩
      rw [factorHom_spec]
      exact hy
  obtain ⟨α, hαβ, hαs, -⟩ := exists_cover K
    (statedSU_central_two_splitting h.card_eq_sq hp2 (by norm_num)) hq hβr
  have hcα : α (negOneSU h) = c :=
    (burgoynePropBSU4CoverInput p f F h hp2 _ α hαs c hII (negOneSU h) rfl).symm
  have key : ∀ y : StatedSU 4 (p ^ f) F,
      MulAut.conj (projH (StatedSU 4 (p ^ f) F) y) = ψ' (liftHom K (α y)) := fun y => by
    rw [hαβ, factorHom_spec]
    rfl
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc2
    exact absurd hc2 (by norm_num)
  have hαinj : Function.Injective α := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    rw [mem_bot]
    have hpg : projH (StatedSU 4 (p ^ f) F) g = 1 := by
      apply hinj
      rw [map_one, key g, hg, map_one, map_one]
    have hgs : (g : GL (Fin 4) F) ∈ StatedScalars (Fin 4) F :=
      (QuotientGroup.eq_one_iff g).1 hpg
    obtain ⟨r, hr⟩ := hgs
    have hgm : ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = (r : F) • 1 := by
      rw [← hr, GeneralLinearGroup.coe_scalar, scalar_apply, smul_one_eq_diagonal]
    have hdet := CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU g.2
    rw [hgm, det_smul, det_one, mul_one, Fintype.card_fin] at hdet
    have hr4' : ((r : F) ^ 2 - 1) * ((r : F) ^ 2 + 1) = 0 := by linear_combination hdet
    rcases mul_eq_zero.1 hr4' with h1 | h1
    · have h1' : ((r : F) - 1) * ((r : F) + 1) = 0 := by linear_combination h1
      rcases mul_eq_zero.1 h1' with h3 | h3
      · apply Subtype.ext
        apply Units.ext
        rw [hgm, sub_eq_zero.1 h3, one_smul]
        rfl
      · exfalso
        apply hc1
        have hgn : g = negOneSU h := by
          apply Subtype.ext
          apply Units.ext
          rw [hgm, eq_neg_of_add_eq_zero_left h3, coe_negOneSU, neg_one_smul]
        rw [← hcα, ← hgn, hg]
    · exfalso
      apply hc1
      have hgg : g * g = negOneSU h := by
        apply Subtype.ext
        apply Units.ext
        rw [Subgroup.coe_mul, Units.val_mul, hgm, coe_negOneSU, smul_mul_smul, Matrix.one_mul,
          ← pow_two, eq_neg_of_add_eq_zero_left h1, neg_one_smul]
      rw [← hcα, ← hgg, map_mul, hg, mul_one]
  set e : StatedSU 4 (p ^ f) F ≃* (K ⧸ pPrimeCore 2 K) :=
    MulEquiv.ofBijective α ⟨hαinj, hαs⟩ with he
  have heα : ∀ g, e g = α g := fun g => rfl
  refine ⟨e, ψ', hψ', hInn', hψ't, hcα, fun j g => ?_⟩
  apply hinj
  rw [key, ← PSL.mul_conj_mul_inv, key, ← heα, e.apply_symm_apply, heα, liftHom_conj, map_mul,
    map_mul, map_inv]

end CFSG.ComponentClassification.CatFactsL4U4.BurgD

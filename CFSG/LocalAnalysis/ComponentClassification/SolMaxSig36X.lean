module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36W
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitTheta
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36Q

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem exists_coreQuot_of_sup' [Finite X] {M L : Subgroup X} (hLM : L ≤ M)
    (hsup : L ⊔ (pPrimeCore 2 ↥M).map M.subtype = M) {r : ℕ}
    (θL : ↥L ⧸ pPrimeCore 2 ↥L ≃* alternatingGroup (Fin r)) :
    ∃ θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r),
      ∀ x : ↥L, θ ((⟨x, hLM x.2⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) =
        θL (x : ↥L ⧸ pPrimeCore 2 ↥L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := L.subgroupOf M with hYdef
  have hY : Function.Surjective ((QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp Y.subtype) := by
    have h1 : Y ⊔ pPrimeCore 2 ↥M = ⊤ := by
      have h2 : (L ⊔ (pPrimeCore 2 ↥M).map M.subtype).subgroupOf M = ⊤ := by
        rw [hsup]
        exact subgroupOf_self M
      rwa [subgroupOf_sup hLM (map_subtype_le _), subgroupOf_map_subtype_self] at h2
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, range_subtype]
    have h2 := congrArg (Subgroup.map (QuotientGroup.mk' (pPrimeCore 2 ↥M))) h1
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
  obtain ⟨φ, hφ⟩ := UnbalancedGS.FixedPrimeLayer.exists_quotient_mulEquiv Y hY
  let ψ : ↥L ⧸ pPrimeCore 2 ↥L ≃* Y ⧸ pPrimeCore 2 Y :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLM).symm (pPrimeCore_map_iso 2 _)
  refine ⟨φ.symm.trans (ψ.symm.trans θL), fun x => ?_⟩
  have h1 : ψ (x : ↥L ⧸ pPrimeCore 2 ↥L) =
      (((subgroupOfEquivOfLe hLM).symm x : Y) : Y ⧸ pPrimeCore 2 Y) :=
    QuotientGroup.congr_mk _ _ _ _ _
  have h2 : φ (ψ (x : ↥L ⧸ pPrimeCore 2 ↥L)) =
      ((⟨x, hLM x.2⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) := by
    rw [h1, hφ]
    rfl
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, ← h2, MulEquiv.symm_apply_apply,
    MulEquiv.symm_apply_apply]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem normalizer_le_of_le_Q (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hJM : J ≤ M)
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M)
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)} (hρ : IsPermAction θ ρ)
    (hA : ∀ (x : X) (hx : x ∈ M), x * x = 1 → (ρ ⟨x, le_normalizer hx⟩).support.card = 4 →
      centralizer ({x} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    {Q : Subgroup X}
    (hQH : Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hQK : Q ≤ UnbalancedLayer.coreActionKernel M) (hQ2 : IsPGroup 2 Q) (htQ : t ∈ Q)
    {T : Subgroup X} (hTQ : T ≤ Q) (hT1 : T ≠ ⊥) :
    normalizer (T : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hn9 := S.nine_le
  have hJH : J ≤ H := S.le_normalizer_completion h33 h35
  set L := GSLit.fixedLayer M Q with hLdef
  obtain ⟨hLJ, hLC, hpc, θL, hθL⟩ :=
    S.layer_facts_of_sup h33 h35 hT13 hML hSch hMH hMpc hHN θ hsup hQH hQK hQ2 htQ
  set Y := normalizer (T : Set X) with hYdef
  have hT2 : IsPGroup 2 T := hQ2.to_le hTQ
  have hQ1 : Q ≠ ⊥ := by
    intro h
    have h1 := htQ
    rw [h, mem_bot] at h1
    have h2 := S.pair.1.1
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by decide)
  have hLT : L ≤ centralizer (T : Set X) := hLC.trans (centralizer_le hTQ)
  have hLY : L ≤ Y := hLT.trans (Subgroup.centralizer_le_normalizer _)
  have hnorm := Sol78H.le_normalizer_core_sup_of_thm13 hT13 hML hSch S.nonab S.kProper S.unbal
    S.notU S.pair.2.1 S.pair.2.2.1 ⟨t, J, S.pair.1⟩ S.pair.2.2.2.1 hQ1 hQ2 ⟨hLC, hpc⟩ ⟨θL⟩ hT1
    hT2 hLT (Subgroup.centralizer_le_normalizer _) (le_refl Y)
  set O := GH74.GLS.pPrimeCoreOf 2 Y with hOdef
  set Z : Subgroup X := O ⊔ L with hZdef
  obtain ⟨F, hFL, hFk, DF, hDF, hFs⟩ := exists_four_subgroup_of_alt L (by omega) θL
  have hFJ : F ≤ J := hFL.trans hLJ
  have hFsJ : ∀ x : J, (x : X) ∈ F → ∀ ω ∉ DF,
      ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Perm (Fin n)) ω = ω := by
    intro x hx ω hω
    have h1 := hFs ⟨x, hFL hx⟩ hx ω hω
    rwa [hθL ⟨x, hFL hx⟩ x.2] at h1
  have hFW := S.completion_eq_of_four h33 h35 hFJ hFk hDF hFsJ
  have hFH : normalizer (F : Set X) ≤ H := by
    have h1 := normalizer_le_normalizer_signalizerCompletion_self F
    rwa [hFW] at h1
  obtain ⟨hF4, hF2⟩ := card_sq_of_klein hFk
  have hFsq : ∀ x ∈ F, x * x = 1 := fun x hx => by rw [← sq]; exact hF2 x hx
  have hOH : O ≤ H := by
    refine FooteLit.le_of_isKleinFour_inf_centralizer_le (isKleinFour_of_card_four hF4 hFsq)
      (fun f hf => le_normalizer_pPrimeCore (le_normalizer (hLY (hFL hf)))) ?_ ?_
    · rw [hOdef, GH74.GLS.pPrimeCoreOf, card_map_of_injective Y.subtype_injective]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    · intro w hwF hw1
      refine inf_le_right.trans ?_
      have hwJ : w ∈ J := hFJ hwF
      have hw4 : (ρ ⟨w, le_normalizer (hJM hwJ)⟩).support.card = 4 := by
        have h1 := card_support_rho_eq_of_sup (by omega) e hJM hsup hρ hwJ
        rw [card_support_coreImage_of_four e hwJ (hFsq w hwF) hw1 hDF
          (fun ω hω => hFsJ ⟨w, hwJ⟩ hwF ω hω)] at h1
        exact h1
      exact hA w (hJM hwJ) (hFsq w hwF) hw4
  have hLH : L ≤ H := hLJ.trans hJH
  have hZH : Z ≤ H := sup_le hOH hLH
  have hOY : O ≤ Y := map_subtype_le _
  have hZY : Z ≤ Y := sup_le hOY hLY
  have hLZ : L ≤ Z := le_sup_right
  have hOZ : O ≤ (pPrimeCore 2 ↥Z).map Z.subtype := by
    refine le_pPrimeCore_map le_sup_left
      (fun z hz => le_normalizer_pPrimeCore (le_normalizer (hZY hz))) ?_
    rw [hOdef, GH74.GLS.pPrimeCoreOf, card_map_of_injective Y.subtype_injective]
    exact pPrimeCore_coprime_card
  have hsupZ : L ⊔ (pPrimeCore 2 ↥Z).map Z.subtype = Z := by
    exact le_antisymm (sup_le hLZ (map_subtype_le _))
      (sup_le (hOZ.trans le_sup_right) le_sup_left)
  obtain ⟨θZ, hθZ⟩ := exists_coreQuot_of_sup' hLZ hsupZ θL
  have hFZ : F ≤ Z := hFL.trans hLZ
  have hFsZ : ∀ x : ↥Z, (x : X) ∈ F → ∀ ω ∉ DF,
      ((θZ (x : ↥Z ⧸ pPrimeCore 2 ↥Z) : alternatingGroup (Fin n)) : Perm (Fin n)) ω = ω := by
    intro x hx ω hω
    have h1 := hθZ ⟨x, hFL hx⟩
    have h2 : (⟨(⟨(x : X), hFL hx⟩ : ↥L), hLZ (hFL hx)⟩ : ↥Z) = x := Subtype.ext rfl
    rw [h2] at h1
    rw [h1]
    exact hFs ⟨x, hFL hx⟩ hx ω hω
  intro y hy
  have hyZ : y ∈ normalizer (Z : Set X) := hnorm hy
  obtain ⟨hFyZ, D', hD', hFys⟩ := exists_support_conj (by omega) θZ hFZ hDF hFsZ hyZ
  have hFy4 : Nat.card (F.map (MulAut.conj y).toMonoidHom) = 4 := by
    rw [card_map_of_injective (MulAut.conj y).injective, hF4]
  have hFysq : ∀ x ∈ F.map (MulAut.conj y).toMonoidHom, x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hFsq x hx, map_one]
  obtain ⟨j, hjZ, hj⟩ := exists_conj_four_subgroup (by omega) θZ hFyZ hFZ hFy4 hF4 hFysq hFsq
    hD' hDF hFys hFsZ
  have hjy : j * y ∈ normalizer (F : Set X) := by
    rw [mem_normalizer_iff_map_conj_eq]
    calc F.map (MulAut.conj (j * y)).toMonoidHom =
        (F.map (MulAut.conj y).toMonoidHom).map (MulAut.conj j).toMonoidHom := by
          rw [Subgroup.map_map]
          congr 1
          ext z
          simp [MulAut.conj_apply, mul_assoc]
      _ = F := hj
  have h1 := mul_mem (inv_mem (hZH hjZ)) (hFH hjy)
  rwa [inv_mul_cancel_left] at h1

end Sig36

end CFSG.ComponentClassification.SolMax

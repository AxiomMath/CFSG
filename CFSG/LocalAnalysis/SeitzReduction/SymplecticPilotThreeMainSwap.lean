module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotUniqueSwap
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeCTSwap
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotEndSwap
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotFourOrth
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParamMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeOrthSwap

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.UnitaryPilot (modelToG mem_modelToG OddCentralSplit)
open CFSG.Quasithin (perfectCore)

section Pair

variable {n f : ℕ} {K : Type} [Field K]

theorem false_of_involution_pair_sp_of_three_le [Finite K] [CharP K 2] (hn : 3 ≤ n)
    (hK : Nat.card K = 2 ^ f) {θ₁ θ₂ : MulAut (StatedSp n K)} (h₁ : θ₁ * θ₁ = 1)
    (h₂ : θ₂ * θ₂ = 1)
    (hC1 : (Nat.card (fixedSubgroup θ₁)).factorization 2 +
      (Nat.card (fixedSubgroup θ₂)).factorization 2 ≤ f * n ^ 2 + 1 + f.factorization 2)
    (hC3 : Nat.card (perfectCore (fixedSubgroup θ₁)) * Nat.card (perfectCore (fixedSubgroup θ₂)) ∣
      Nat.card (StatedSp n K)) : False := by
  have hf : 1 ≤ f := F4Pilot.one_le_of_natCard_eq_two_pow hK
  have hvf : f.factorization 2 < f := Nat.factorization_lt 2 (by omega)
  have hnn : n * (n + 1) / 2 * 2 = n * (n + 1) :=
    Nat.div_mul_cancel (Nat.even_mul_succ_self n).two_dvd
  have hmixed : ∀ f' : ℕ, 2 * f' = f → 1 ≤ f' →
      f * (n * (n + 1) / 2) + f' * n ^ 2 ≤ f * n ^ 2 + 1 + f.factorization 2 → False := by
    intro f' hf'2 hf'1 h
    have hvf' : f.factorization 2 = 1 + f'.factorization 2 := by
      rw [← hf'2, Nat.factorization_mul two_ne_zero (by omega), Finsupp.add_apply,
        Nat.Prime.factorization_self Nat.prime_two]
    have hvf'' : f'.factorization 2 < f' := Nat.factorization_lt 2 (by omega)
    have h5 : f * (n * (n + 1) / 2) = f' * n ^ 2 + f' * n := by
      rw [← hf'2]
      calc 2 * f' * (n * (n + 1) / 2) = f' * (n * (n + 1) / 2 * 2) := by ring
        _ = f' * n ^ 2 + f' * n := by rw [hnn]; ring
    have h6 : f * n ^ 2 = 2 * (f' * n ^ 2) := by rw [← hf'2]; ring
    have h4 : 3 * f' ≤ f' * n := by nlinarith
    omega
  rcases involution_dichotomy_sp hn hK h₁ with hi₁ | ⟨k₁, hk₁, hc₁, hp₁⟩ <;>
    rcases involution_dichotomy_sp hn hK h₂ with hi₂ | ⟨k₂, hk₂, hc₂, hp₂⟩
  ·
    have h4 : 2 * f ≤ f * n := by nlinarith
    have h5 : f * (n * (n + 1) / 2) * 2 = f * n ^ 2 + f * n := by
      calc f * (n * (n + 1) / 2) * 2 = f * (n * (n + 1) / 2 * 2) := by ring
        _ = f * n ^ 2 + f * n := by rw [hnn]; ring
    omega
  ·
    obtain ⟨f', hf'2, hf'1, -, hv⟩ := exists_card_subfield_of_sq (n := n) (by omega) hK k₂ hk₂
    rw [hc₂, hv] at hC1
    exact hmixed f' hf'2 hf'1 (by omega)
  ·
    obtain ⟨f', hf'2, hf'1, -, hv⟩ := exists_card_subfield_of_sq (n := n) (by omega) hK k₁ hk₁
    rw [hc₁, hv] at hC1
    exact hmixed f' hf'2 hf'1 (by omega)
  ·
    obtain ⟨f₁, -, -, hk₁c, -⟩ := exists_card_subfield_of_sq (n := n) (by omega) hK k₁ hk₁
    have hk₁₂ : Nat.card k₁ = Nat.card k₂ :=
      Nat.pow_left_injective two_ne_zero (hk₁.trans hk₂.symm)
    have hSp : Nat.card (StatedSp n k₂) = Nat.card (StatedSp n k₁) := by
      rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp,
        CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hk₁₂]
    rw [hp₁, hp₂, hc₁, hc₂, hSp, ← sq] at hC3
    exact not_sq_card_statedSp_dvd (by omega) hk₁c hk₁.symm hC3

end Pair

section Unique

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_mem_normalizer_factors_of_three_le (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 3 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f)
    (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {A : Subgroup G}
    {φ : A →* L} (hφs : Function.Surjective φ) (hφZ : φ.ker ≤ center A)
    (hoddA : Odd (Nat.card (center A))) (g : G)
    (hAB : A.map (MulAut.conj g).toMonoidHom ≤ centralizer (A : Set G))
    (htA : t ∈ normalizer (A : Set G))
    (htB : t ∈ normalizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) : False := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hOut : Group.IsSolvable (Outer L) :=
    isSolvable_outer_of_isCyclic (isCyclic_outer_of_mulEquiv_statedSp hn e)
  have hZL : center L = ⊥ := hset.center_eq_bot
  set B := A.map (MulAut.conj g).toMonoidHom with hB
  obtain ⟨φB, hφBs, hφBZ⟩ := LinearPilot.exists_surjective_map_conj hφs hφZ g
  have hoddB : Odd (Nat.card (center B)) := by
    let E : A ≃* B := A.equivMapOfInjective _ (MulAut.conj g).injective
    rw [← map_center_eq E, card_map_of_injective E.injective]
    exact hoddA
  obtain ⟨θA, hθA2, hcA, hpA⟩ := exists_factorAut_of_odd hZL e hφs hφZ hoddA htt htA
  obtain ⟨θB, hθB2, hcB, hpB⟩ := exists_factorAut_of_odd hZL e hφBs hφBZ hoddB htt htB
  have hBA : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    mem_centralizer_iff.1 (hAB hy) x hx
  have hIZ : A ⊓ B ≤ (center A).map A.subtype := by
    rintro x ⟨hxA, hxB⟩
    refine ⟨⟨x, hxA⟩, mem_center_iff.2 fun y => Subtype.ext (hBA y y.2 x hxB), rfl⟩
  set CA := A ⊓ centralizer ({t} : Set G) with hCA
  set CB := B ⊓ centralizer ({t} : Set G) with hCB
  have hcomm : ∀ x ∈ CA, ∀ y ∈ CB, x * y = y * x := fun x hx y hy => hBA x hx.1 y hy.1
  have hIZC : CA ⊓ CB ≤ (center A).map A.subtype := fun x hx => hIZ ⟨hx.1.1, hx.2.1⟩
  have hC1 : Nat.card (fixedSubgroup θA) * Nat.card (fixedSubgroup θB) ∣
      Nat.card (CA ⊔ CB : Subgroup G) :=
    LinearPilot.mul_dvd_card_sup_of_commute hcomm hIZC hcA ⟨_, hcB⟩
  have hDt : CA ⊔ CB ≤ centralizer ({t} : Set G) := sup_le inf_le_right inf_le_right
  have hv := factorization_card_le_of_le_centralizer_sp hset.standardSetting.standard hn
    hKc e ht hKt hDt
  have hv1 : (Nat.card (fixedSubgroup θA)).factorization 2 +
      (Nat.card (fixedSubgroup θB)).factorization 2 ≤ f * n ^ 2 + 1 + f.factorization 2 := by
    have h1 := (Nat.factorization_le_iff_dvd (mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne')
      Nat.card_pos.ne').2 hC1 2
    rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply] at h1
    omega
  set PA := perfectCore CA with hPA
  set PB := perfectCore CB with hPB
  have hPAL : PA ≤ L := std_perfect_le hset.standardSetting hOut htC ht
    (CFSG.Quasithin.perfectCore_perfect _) ((CFSG.Quasithin.perfectCore_le _).trans inf_le_right)
  have hPBL : PB ≤ L := std_perfect_le hset.standardSetting hOut htC ht
    (CFSG.Quasithin.perfectCore_perfect _) ((CFSG.Quasithin.perfectCore_le _).trans inf_le_right)
  have hPcomm : ∀ x ∈ PA, ∀ y ∈ PB, x * y = y * x := fun x hx y hy =>
    hcomm x (CFSG.Quasithin.perfectCore_le _ hx) y (CFSG.Quasithin.perfectCore_le _ hy)
  have hPIZ : PA ⊓ PB ≤ (center A).map A.subtype := fun x hx =>
    hIZC ⟨CFSG.Quasithin.perfectCore_le _ hx.1, CFSG.Quasithin.perfectCore_le _ hx.2⟩
  have hC3 : Nat.card (perfectCore (fixedSubgroup θA)) *
      Nat.card (perfectCore (fixedSubgroup θB)) ∣ Nat.card (PA ⊔ PB : Subgroup G) :=
    LinearPilot.mul_dvd_card_sup_of_commute hPcomm hPIZ hpA ⟨_, hpB⟩
  have hPL : Nat.card (PA ⊔ PB : Subgroup G) ∣ Nat.card (StatedSp n K) := by
    rw [← Nat.card_congr e.toEquiv]
    exact Subgroup.card_dvd_of_le (sup_le hPAL hPBL)
  exact false_of_involution_pair_sp_of_three_le hn hKc hθA2 hθB2 hv1 (hC3.trans hPL)

theorem unique_of_swapFactors_of_three_le (hset : SeitzSetting G L) {n f : ℕ} (hn : 3 ≤ n)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {G₁ : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple G₁)
    (h₁₂ : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hglob : spGlobal e ≤ G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom)
    (hδ : ∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) (hsurj : ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y) :
    ∀ g : G, g⁻¹ * t * g ∈
        normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) →
      g ∈ normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have hOut : Group.IsSolvable (Outer L) :=
    isSolvable_outer_of_isCyclic (isCyclic_outer_of_mulEquiv_statedSp hn e)
  have hcard₁ := LinearPilot.card_quotient_center_eq_of_swapFactors hset.center_eq_bot h₁₂ hδ
    hsurj
  have hodd₁ := odd_card_center_of_swapFactors ht hKt hq h₁₂ hsurj
  refine F4Pilot.unique_of_forall_conjugate_eq fun h htM => ?_
  have hM : CFSG.conjugate (G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom) h =
      CFSG.conjugate G₁ h ⊔ CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) h :=
    Subgroup.map_sup _ _ _
  rw [hM] at htM
  have hqA := LinearPilot.isQuasisimple_conjugate hq h
  have hqB := LinearPilot.isQuasisimple_conjugate (LinearPilot.isQuasisimple_map_conj hq t) h
  have hAB := LinearPilot.conjugate_le_centralizer_of_le_centralizer h₁₂ h
  have hBA := le_centralizer_iff.1 hAB
  obtain ⟨hpA, hbA, hnA⟩ := F4Pilot.perfect_ne_bot_dichotomy_of_isQuasisimple hqA
  obtain ⟨hpB, hbB, hnB⟩ := F4Pilot.perfect_ne_bot_dichotomy_of_isQuasisimple hqB
  rcases F4Pilot.map_conj_eq_or_eq_of_perfect hAB hpA hbA hnA hnB htM with hAA | hswap
  ·
    exfalso
    rcases F4Pilot.map_conj_eq_or_eq_of_perfect hBA hpB hbB hnB hnA
        (by rw [sup_comm]; exact htM) with hBB | hBA'
    ·
      have hBconj := LinearPilot.map_conj_conjugate_eq (A := G₁) h t
      have hoddA : Odd (Nat.card (center (CFSG.conjugate G₁ h))) := by
        let E : G₁ ≃* CFSG.conjugate G₁ h := LinearPilot.conjugateEquiv G₁ h
        rw [← map_center_eq E, card_map_of_injective E.injective]
        exact hodd₁
      obtain ⟨φA, hφAs, hφAZ⟩ :=
        LinearPilot.exists_surjective_conjugate_of_linearSwapDiag h₁₂ hδ hsurj h
      refine false_of_mem_normalizer_factors_of_three_le hset hn hKc e ht hKt hφAs hφAZ hoddA
        (h⁻¹ * t * h) ?_ (F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom.2 hAA) ?_
      · rw [hBconj]
        exact hAB
      · rw [hBconj]
        exact F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom.2 hBB
    ·
      have hAB' : CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) h = CFSG.conjugate G₁ h :=
        F4Pilot.map_conj_toMonoidHom_inj.1 (hBA'.trans hAA.symm)
      rw [hAB'] at hAB
      exact hbA (by rw [← hpA, commutator_eq_bot_iff_le_centralizer.2 hAB])
  ·
    have hA : (CFSG.conjugate G₁ h).map (MulAut.conj t).toMonoidHom ≤
        centralizer (CFSG.conjugate G₁ h : Set G) := by
      rw [hswap]
      exact hAB
    have hcardA : Nat.card L ≤
        Nat.card (CFSG.conjugate G₁ h ⧸ center (CFSG.conjugate G₁ h)) := by
      rw [← Nat.card_congr (LinearPilot.conjugateQuotientCenterEquiv G₁ h).toEquiv, hcard₁]
    have hAle : CFSG.conjugate G₁ h ≤ G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom :=
      (le_spGlobal_of_swap hset.standardSetting hOut (by omega) hK4 e htC ht hqA hA
        hcardA).trans hglob
    have htG₀ : t ∈ normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) :
        Set G) := F4Pilot.mem_normalizer_sup_of_map_conj_eq htt rfl
    have hBle : CFSG.conjugate (G₁.map (MulAut.conj t).toMonoidHom) h ≤
        G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom := by
      rw [← hswap]
      calc (CFSG.conjugate G₁ h).map (MulAut.conj t).toMonoidHom
          ≤ (G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom :=
            map_mono hAle
        _ = G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom :=
            F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom.1 htG₀
    have hle : CFSG.conjugate (G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom) h ≤
        G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom := by
      rw [hM]
      exact sup_le hAle hBle
    exact Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective).ge

end Unique

section SwapRow

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem false_of_swapRow_three_of_siegel (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp 3 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hparam : ∀ k : Fin 3, Nonempty (SwapNeighbourParam e t k)) (S : SiegelSwapParam e t) :
    False := by
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hcomm := commute_pieceCore_zero_two_swap_three hset hK4 e htC ht (k := 0) (by decide)
    (hparam 0).some (hparam 2).some
  obtain ⟨G₁, hq, h₁₂, hsup, hδ, hsurj⟩ :=
    exists_swapFactors_three_of_siegel hK4 e (hparam 0).some S hcomm
  have : IsSimpleGroup G := hset.1
  exact LinearPilot.false_of_simple_of_swapFactors ht hq h₁₂ rfl
    (unique_of_swapFactors_of_three_le hset le_rfl hKc hf e ht hKt hq h₁₂ hsup.ge hδ hsurj)

theorem nonempty_siegelSwapParam_of_swapNeighbourParam {n : ℕ}
    (hcat : LinearPilot.SLmCatalogueClausesAt n) (hdet : LinearPilot.SLmEvenTypeDetAt n)
    (hsplit : OddCentralSplit (siegelLevi K n)) (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hn : 3 ≤ n) (e : L ≃* StatedSp n K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (P : SwapNeighbourParam e t ⟨2, by omega⟩) : Nonempty (SiegelSwapParam e t) := by
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  obtain ⟨F, _, _, ι, σ, hσ, hfix⟩ := exists_quadraticExtension K
  obtain ⟨hσ1, hσσ⟩ := ne_one_and_mul_self_of_orderOf_eq_two hσ
  have hF : Nat.card F = Nat.card K ^ 2 := by
    rw [LinearPilot.natCard_eq_two_pow_of_fixedField hKc ι hσ1 hσσ hfix, hKc, ← pow_mul,
      mul_comm]
  rcases siegel_normal_or_fieldParam_or_swapParam hcat hdet hset hKc hf hn e htC ht hsplit ι hσ1
    hσσ hfix with ⟨htX, hnorm⟩ | hP | hS
  · exact (false_of_swapNeighbourParam_of_siegel_normal hset hKc hf hn e htC ht P
      (j := ⟨0, by omega⟩) (by simp; omega) (by simp [Fin.ext_iff]) (by simp) htX hnorm).elim
  · exact hP.elim fun S => (false_of_swapNeighbourParam_of_siegelFieldParam hq hn hF P S).elim
  · exact hS

theorem false_of_swapRow_three (hcat : LinearPilot.SLmCatalogueClausesAt 3)
    (hdet : LinearPilot.SLmEvenTypeDetAt 3) (hsplit : OddCentralSplit (siegelLevi K 3))
    (hset : SeitzSetting G L) {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 3 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hparam : ∀ k : Fin 3, Nonempty (SwapNeighbourParam e t k)) : False := by
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  obtain ⟨S⟩ := nonempty_siegelSwapParam_of_swapNeighbourParam hcat hdet hsplit hset hKc hf
    le_rfl e htC ht (hparam 2).some
  exact false_of_swapRow_three_of_siegel hset hKc hf e ht hKt hparam S

end SwapRow

end CFSG.SeitzReduction.SymplecticPilot

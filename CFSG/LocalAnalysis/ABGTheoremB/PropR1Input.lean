module

public import CFSG.LocalAnalysis.ABGTheoremB.V56Inputs
public import CFSG.LocalAnalysis.ABGTheoremB.R1NFacts
public import CFSG.LocalAnalysis.ABGTheoremB.IVNFacts
import CFSG.LocalAnalysis.ABGTheoremB.ZJCovering
import CFSG.LocalAnalysis.ABGTheoremB.V3
import CFSG.LocalAnalysis.ABGTheoremB.V5Tools
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.ABGTheoremB.V4Defs

public section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools
open scoped Pointwise

universe u

section General

variable {G : Type u} [Group G] [Finite G]

private theorem r1i_le_sup_of_isSylowOf {p : ℕ} [Fact p.Prime] {N C S : Subgroup G}
    (hCN : C ≤ N) (hS : IsSylowOf p S N) {n : ℕ} (hn : C.relIndex N = p ^ n) : N ≤ S ⊔ C := by
  have hBN : S ⊔ C ≤ N := sup_le hS.le hCN
  have h1 := Subgroup.relIndex_mul_relIndex C (S ⊔ C) N le_sup_right hBN
  have h2 := Subgroup.relIndex_mul_relIndex S (S ⊔ C) N le_sup_left hBN
  have hdvd : (S ⊔ C).relIndex N ∣ p ^ n := by
    rw [← hn, ← h1]
    exact Dvd.intro_left _ rfl
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd
  have hS' := (isSylowOf_iff.mp hS).2.2
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · rw [pow_zero] at hk
    exact Subgroup.relIndex_eq_one.mp hk
  · exfalso
    apply hS'
    rw [← h2, hk]
    exact Dvd.dvd.mul_left (dvd_pow_self p hkpos.ne') _

private theorem r1i_pCoreIn_ne_bot {p : ℕ} [Fact p.Prime] {Y : Subgroup G}
    (hY : Odd (Nat.card Y)) (hpp : pPrimeCoreIn p Y = ⊥) (hY1 : Y ≠ ⊥) : pCoreIn p Y ≠ ⊥ := by
  have hsolv : Group.IsSolvable Y := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hY
  have hcon : IsPConstrained p Y := isPConstrained_of_isSolvable hsolv
  have hpp' : CFSG.pPrimeCore p Y = ⊥ := V56.pPrimeCoreIn_eq_bot_iff.mp hpp
  intro hbot
  have hpc : CFSG.pCore p Y = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective).mp hbot
  have hE : CFSG.Op_p'p p Y = ⊥ := by
    have hle : CFSG.Op_p'p p Y ≤ CFSG.pCore p Y := by
      apply le_sSup
      refine ⟨inferInstance, ?_⟩
      intro x
      obtain ⟨k, hk⟩ := exists_pow_mem_pPrimeCore_of_mem_Op_p'p x.2
      rw [hpp', Subgroup.mem_bot] at hk
      exact ⟨k, Subtype.ext hk⟩
    rw [hpc] at hle
    exact le_bot_iff.mp hle
  obtain ⟨P, hP⟩ := exists_isSylowOf p (CFSG.Op_p'p p Y)
  have hP1 : P = ⊥ := le_bot_iff.mp (hE ▸ hP.le)
  have hC := hcon P hP
  rw [hP1, hE] at hC
  apply hY1
  rw [eq_bot_iff]
  intro g hg
  have hmem : (⟨g, hg⟩ : Y) ∈ Subgroup.centralizer ((⊥ : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hh
    rw [hh, one_mul, mul_one]
  have h1 := hC hmem
  rw [Subgroup.mem_bot] at h1 ⊢
  exact congrArg Subtype.val h1

private theorem r1i_le_normalizer_thompsonCenter {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {U W : Subgroup G} (hUp : IsPGroup p U) (hU1 : U ≠ ⊥) (hWp : ¬ p ∣ Nat.card W)
    (hWodd : Odd (Nat.card W)) (hUW : (U : Set G) * W = W * U)
    (hcore : pPrimeCoreIn p (U ⊔ W) = ⊥) :
    W ≤ Subgroup.normalizer (CFSG.thompsonCenter U : Set G) := by
  have hYodd : Odd (Nat.card (U ⊔ W : Subgroup G)) := by
    rw [V56.card_sup_pPrime Fact.out hUp hWp hUW]
    exact (V56.odd_card_of_isPGroup Fact.out hp2 hUp).mul hWodd
  have hUY : IsSylowOf p U (U ⊔ W) := V56.isSylowOf_sup_pPrime Fact.out hUp hWp hUW
  have hB := r1i_pCoreIn_ne_bot hYodd hcore
    (fun h => hU1 (le_bot_iff.mp (h ▸ (le_sup_left : U ≤ U ⊔ W))))
  have hUinf : U ⊓ (U ⊔ W) = U := inf_eq_left.mpr le_sup_left
  obtain ⟨-, -, hfac⟩ := zjCovering_sup hp2 (K := U ⊔ W) (O := U ⊔ W) le_rfl
    Subgroup.le_normalizer hYodd le_sup_left hUp (by rw [hUinf]; exact hUY) hB
    (V56.isPGroup_pCoreIn p _) (pCoreIn_le p _) (V56.le_normalizer_pCoreIn p _)
  rw [hcore, bot_sup_eq, sup_eq_left.mpr (le_sup_left : U ≤ U ⊔ W)] at hfac
  exact le_sup_right.trans (inf_eq_left.mp hfac)

end General

namespace Setting

variable {G : Type u} [Group G] [Finite G] (σ : Setting G)

private theorem r1i_isSylowOf_sup (hσ : σ.IsValid) {K U : Subgroup G} (hDK : σ.D ≤ K)
    (hU : U ∈ maximals (signalizers K σ.D σ.p)) :
    IsSylowOf σ.p U (oddCoreIn K ⊔ U) := by
  have : Fact σ.p.Prime := ⟨hσ.p_prime⟩
  obtain ⟨⟨hUK, hUp, hDU, -⟩, hmax⟩ := hU
  have hD2 : IsPGroup 2 σ.D := σ.S.isPGroup'.to_le σ.D_le_S
  have hKO : K ≤ Subgroup.normalizer ((oddCoreIn K : Subgroup G) : Set G) :=
    le_normalizer_oddCoreIn K
  have hYodd : Odd (Nat.card (oddCoreIn K ⊔ U : Subgroup G)) :=
    odd_card_sup_of_le_normalizer_of_odd (hUK.trans hKO) (odd_card_oddCoreIn K)
      (V56.odd_card_of_isPGroup hσ.p_prime hσ.p_ne_two hUp)
  have hDY : σ.D ≤ Subgroup.normalizer ((oddCoreIn K ⊔ U : Subgroup G) : Set G) :=
    (le_inf (hDK.trans hKO) hDU).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  obtain ⟨R, hR, hUR, hDR⟩ := exists_isSylowOf_normalized_ge_of_odd hσ.p_prime hD2 hDY hYodd
    le_sup_right hUp hDU
  have hRK : R ≤ K := hR.le.trans (sup_le (oddCoreIn_le K) hUK)
  have hRU := hmax R ⟨hRK, hR.isPGroup, hDR,
    V56.inf_eq_bot_of_isPGroup_of_two hσ.p_prime hσ.p_ne_two hR.isPGroup hD2⟩ hUR
  rwa [hRU] at hR

private theorem r1i_exists_X (hσ : σ.IsValid) {K U : Subgroup G} (hDK : σ.D ≤ K)
    (hfac : oddCoreIn K ⊔ (K ⊓ σ.N) = K) (hUK : U ≤ K) (hUp : IsPGroup σ.p U)
    (hDU : σ.D ≤ Subgroup.normalizer (U : Set G)) :
    ∃ X : Subgroup G, X ≤ σ.N ∧ X ≤ K ∧ IsPGroup σ.p X ∧
      σ.D ≤ Subgroup.normalizer (X : Set G) ∧ X ⊔ oddCoreIn K = oddCoreIn K ⊔ U := by
  have : Fact σ.p.Prime := ⟨hσ.p_prime⟩
  set O := oddCoreIn K with hO
  have hKO : K ≤ Subgroup.normalizer (O : Set G) := le_normalizer_oddCoreIn K
  have hYK : O ⊔ U ≤ K := sup_le (oddCoreIn_le K) hUK
  have hYodd : Odd (Nat.card (O ⊔ U : Subgroup G)) :=
    odd_card_sup_of_le_normalizer_of_odd (hUK.trans hKO) (odd_card_oddCoreIn K)
      (V56.odd_card_of_isPGroup hσ.p_prime hσ.p_ne_two hUp)
  have hD2 : IsPGroup 2 σ.D := σ.S.isPGroup'.to_le σ.D_le_S
  have hDY : σ.D ≤ Subgroup.normalizer ((O ⊔ U : Subgroup G) : Set G) :=
    (le_inf (hDK.trans hKO) hDU).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hDB : σ.D ≤ Subgroup.normalizer (((O ⊔ U) ⊓ σ.N : Subgroup G) : Set G) :=
    (le_inf hDY ((σ.D_le_N hσ).trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hBodd : Odd (Nat.card ((O ⊔ U) ⊓ σ.N : Subgroup G)) :=
    hYodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  obtain ⟨X, hX, hDX⟩ := exists_isSylowOf_normalized_of_odd hσ.p_prime hD2 hDB hBodd
  have hXB : X ≤ (O ⊔ U) ⊓ σ.N := hX.le
  refine ⟨X, hXB.trans inf_le_right, hXB.trans (inf_le_left.trans hYK), hX.isPGroup, hDX, ?_⟩
  apply le_antisymm (sup_le (hXB.trans inf_le_left) le_sup_left)
  have hYOB : O ⊔ U ≤ O ⊔ ((O ⊔ U) ⊓ σ.N) := by
    intro y hy
    have hyK : y ∈ ((O ⊔ (K ⊓ σ.N) : Subgroup G) : Set G) := by
      rw [hfac]
      exact hYK hy
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (inf_le_left.trans hKO)] at hyK
    obtain ⟨o, ho, k, hk, rfl⟩ := hyK
    have hkY : k ∈ O ⊔ U := by
      have := (O ⊔ U).mul_mem ((O ⊔ U).inv_mem ((le_sup_left : O ≤ O ⊔ U) ho)) hy
      simpa using this
    exact Subgroup.mul_mem_sup ho ⟨hkY, hk.2⟩
  have hBO : (O ⊔ U) ⊓ σ.N ≤ Subgroup.normalizer (O : Set G) := inf_le_left.trans (hYK.trans hKO)
  have hBY : (O ⊔ U) ⊓ σ.N ⊔ O = O ⊔ U :=
    le_antisymm (sup_le inf_le_left le_sup_left) (hYOB.trans (sup_comm _ _).le)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ((O ⊔ U) ⊓ σ.N ⊓ O).relIndex ((O ⊔ U) ⊓ σ.N) = σ.p ^ n := by
    have h1 : ((O ⊔ U) ⊓ σ.N ⊓ O).relIndex ((O ⊔ U) ⊓ σ.N) = O.relIndex U := by
      rw [inf_comm, Subgroup.inf_relIndex_right, ← relIndex_sup_right_of_le_normalizer hBO, hBY,
        sup_comm, relIndex_sup_right_of_le_normalizer (hUK.trans hKO)]
    rw [h1]
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hUp
    have hdvd : O.relIndex U ∣ σ.p ^ a := ha ▸ Subgroup.relIndex_dvd_card O U
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hσ.p_prime).mp hdvd
    exact ⟨k, hk⟩
  have hBle := r1i_le_sup_of_isSylowOf (inf_le_left : (O ⊔ U) ⊓ σ.N ⊓ O ≤ (O ⊔ U) ⊓ σ.N) hX hn
  calc O ⊔ U ≤ O ⊔ ((O ⊔ U) ⊓ σ.N) := hYOB
    _ ≤ O ⊔ (X ⊔ ((O ⊔ U) ⊓ σ.N ⊓ O)) := sup_le_sup_left hBle _
    _ ≤ X ⊔ O := sup_le le_sup_right (sup_le le_sup_left (inf_le_right.trans le_sup_right))

theorem propR1Input_of (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hN : σ.IVNFacts)
    (hR1N : ∀ J : Subgroup G, σ.IsV21Layer J → σ.R1NFacts J) :
    ∀ J : Subgroup G, σ.IsV21Layer J → V56.PropR1Input σ J := by
  intro J hJ hr W hW P hP _hPD K hK hWK U hUperm hU hPU hcore
  have : Fact σ.p.Prime := ⟨hσ.p_prime⟩
  have hp2 : σ.p ≠ 2 := hσ.p_ne_two
  have hR := hR1N J hJ
  obtain ⟨-, hV31⟩ := σ.lemmaV31 hσ hII hJ.le hJ.pCore_le hJ.sup_eq hJ.inf_eq hJ.normal
    hJ.commutator_le hJ.sl2 hN.oddCore_C_inf_L₀_cyclic hN.oddCore_C_inf_L₀_coprime
    hN.oddCore_C_inf_L₀_centralized hN.oddCore_C_inf_L₀_inverted
  obtain ⟨-, hWp, hWodd, -⟩ := hV31 W hW
  obtain ⟨-, hfac, -, -, ⟨hOKN, hONK⟩, -⟩ :=
    σ.familyL_properties hσ hII hr.prime hr.dvd_ON hK
  have hDK : σ.D ≤ K := hK.2.2.1
  have hcovK : (σ.L₀ : Set G) ⊆ (K : Set G) * (σ.ON : Set G) := hK.2.1
  have hUK : U ≤ K := hU.1.1
  have hUp : IsPGroup σ.p U := hU.1.2.1
  have hDU : σ.D ≤ Subgroup.normalizer (U : Set G) := hU.1.2.2.1
  set O := oddCoreIn K with hO
  have hKO : K ≤ Subgroup.normalizer (O : Set G) := le_normalizer_oddCoreIn K
  have hUY := σ.r1i_isSylowOf_sup hσ hDK hU
  have hUO : IsSylowOf σ.p (U ⊓ O) O :=
    hUY.inf_of_le_normalizer le_sup_left (sup_le Subgroup.le_normalizer (hUK.trans hKO))
  have hU1 : U ≠ ⊥ := fun h => V56.ne_bot_of_isSylowOf hσ.p_prime hP
    (hr.dvd_CL.trans (Subgroup.card_dvd_of_le inf_le_left)) (le_bot_iff.mp (h ▸ hPU))
  have hWZ := r1i_le_normalizer_thompsonCenter hp2 hUp hU1 hWp hWodd hUperm.1.2 hcore
  obtain ⟨X, hXN, hXK, hXp, hDX, hXO⟩ := σ.r1i_exists_X hσ hDK hfac hUK hUp hDU
  have hWN : W ≤ σ.N := V56.le_N_of_mem_familyW hσ hJ hW
  have hNON : σ.N ≤ Subgroup.normalizer (σ.ON : Set G) := σ.N_le_normalizer_ON
  refine σ.propR1 hσ (L₁ := K) (E₁ := ⊥) (X₁ := K ⊓ Subgroup.normalizer
    ((O ⊔ U : Subgroup G) : Set G)) hK hU hUO hWK hWZ hWp ?_ ?_ le_sup_left bot_le le_rfl ?_
  ·
    have hXW := hR.normalizes W hW X hXN hXp hDX
    have hXW' : X ≤ Subgroup.normalizer ((W ⊔ O : Subgroup G) : Set G) := by
      apply V56.le_normalizer_of_conj_mem
      intro x hx a ha
      have haWO : a ∈ ((W ⊔ O : Subgroup G) : Set G) := ha
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hWK.trans hKO)] at haWO
      obtain ⟨w, hw, o, ho, rfl⟩ := haWO
      have h1 : x * w * x⁻¹ ∈ ((W ⊔ σ.ON : Subgroup G) : Set G) :=
        (Subgroup.mem_normalizer_iff.mp (hXW hx) w).mp (Subgroup.mem_sup_left hw)
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hWN.trans hNON)] at h1
      obtain ⟨w', hw', m, hm, hwm⟩ := h1
      have hwm' : w' * m = x * w * x⁻¹ := hwm
      have hmK : m ∈ K := by
        have e : m = w'⁻¹ * (x * w * x⁻¹) := by rw [← hwm']; group
        rw [e]
        exact K.mul_mem (K.inv_mem (hWK hw'))
          (K.mul_mem (K.mul_mem (hXK hx) (hWK hw)) (K.inv_mem (hXK hx)))
      have hmO : m ∈ O := hONK ⟨hm, hmK⟩
      have hxo : x * o * x⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp (hKO (hXK hx)) o).mp ho
      have e : x * (w * o) * x⁻¹ = w' * (m * (x * o * x⁻¹)) := by
        calc x * (w * o) * x⁻¹ = (x * w * x⁻¹) * (x * o * x⁻¹) := by group
          _ = w' * m * (x * o * x⁻¹) := by rw [← hwm']
          _ = w' * (m * (x * o * x⁻¹)) := by group
      rw [e]
      exact Subgroup.mul_mem_sup hw' (O.mul_mem hmO hxo)
    have hOW : O ≤ Subgroup.normalizer ((W ⊔ O : Subgroup G) : Set G) :=
      (le_sup_right : O ≤ W ⊔ O).trans Subgroup.le_normalizer
    calc U ≤ O ⊔ U := le_sup_right
      _ = X ⊔ O := hXO.symm
      _ ≤ _ := sup_le hXW' hOW
  ·
    intro y hy hyW
    have hyXO : y ∈ ((X ⊔ O : Subgroup G) : Set G) := by
      rw [hXO]
      exact (le_sup_right : U ≤ O ⊔ U) hy
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hXK.trans hKO)] at hyXO
    obtain ⟨x, hx, o, ho, rfl⟩ := hyXO
    have hxON : x ∈ σ.ON := by
      refine hR.centralizer W hW X hXN hXp hDX x hx fun w hw => hOKN ⟨?_, ?_⟩
      · have hwK : w ∈ K := hWK hw
        have hxoK : x * o ∈ K := K.mul_mem (hXK hx) (oddCoreIn_le K ho)
        have hc : o⁻¹ * w * o * w⁻¹ ∈ O := by
          have h1 : w * o * w⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp (hKO hwK) o).mp ho
          have := O.mul_mem (O.inv_mem ho) h1
          simpa [mul_assoc] using this
        have hc' : x * o * (o⁻¹ * w * o * w⁻¹) * (x * o)⁻¹ ∈ O :=
          (Subgroup.mem_normalizer_iff.mp (hKO hxoK) _).mp hc
        have e : x * w * x⁻¹ * w⁻¹ = (x * o * (o⁻¹ * w * o * w⁻¹) * (x * o)⁻¹) *
            (x * o * w * (x * o)⁻¹ * w⁻¹) := by group
        rw [e]
        exact O.mul_mem hc' (hyW w hw)
      · exact σ.N.mul_mem (σ.N.mul_mem (σ.N.mul_mem (hXN hx) (hWN hw)) (σ.N.inv_mem (hXN hx)))
          (σ.N.inv_mem (hWN hw))
    exact O.mul_mem (hONK ⟨hxON, hXK hx⟩) ho
  ·
    have hKNON : K ⊓ σ.N ≤ Subgroup.normalizer (σ.ON : Set G) := inf_le_right.trans hNON
    have hMcoe : (((K ⊓ σ.N) ⊔ σ.ON : Subgroup G) : Set G) =
        ((K ⊓ σ.N : Subgroup G) : Set G) * σ.ON :=
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ hKNON
    have hLM : σ.L ≤ (K ⊓ σ.N) ⊔ σ.ON := by
      intro l hl
      have h := σ.L_subset_inf_N_mul_ON_of_cover hσ hII hDK hcovK hl
      rw [← hMcoe] at h
      exact h
    have hMN : (K ⊓ σ.N) ⊔ σ.ON ≤ σ.N := sup_le inf_le_right σ.ON_le_N
    have hgen := hR.generates W hW X hXN hXp hDX _ hLM hMN
    have hR₀N : W ⊔ σ.D ⊔ (K ⊓ σ.N ⊓ Subgroup.normalizer ((O ⊔ U : Subgroup G) : Set G)) ≤
        σ.N := sup_le (sup_le hWN (σ.D_le_N hσ)) (inf_le_left.trans inf_le_right)
    have hR₀K : W ⊔ σ.D ⊔ (K ⊓ σ.N ⊓ Subgroup.normalizer ((O ⊔ U : Subgroup G) : Set G)) ≤
        K := sup_le (sup_le hWK hDK) (inf_le_left.trans inf_le_left)
    have hc1 : K ⊓ σ.N ⊓ Subgroup.normalizer ((σ.ON ⊔ X : Subgroup G) : Set G) ≤
        Subgroup.normalizer ((O ⊔ U : Subgroup G) : Set G) := by
      rw [← hXO]
      apply V56.le_normalizer_of_conj_mem
      intro k hk a ha
      have hkK : k ∈ K := hk.1.1
      have haXO : a ∈ ((X ⊔ O : Subgroup G) : Set G) := ha
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hXK.trans hKO)] at haXO
      obtain ⟨x, hx, o, ho, rfl⟩ := haXO
      have h1 : k * x * k⁻¹ ∈ ((σ.ON ⊔ X : Subgroup G) : Set G) :=
        (Subgroup.mem_normalizer_iff.mp hk.2 x).mp (Subgroup.mem_sup_right hx)
      rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (hXN.trans hNON)] at h1
      obtain ⟨m, hm, x', hx', hmx⟩ := h1
      have hmx' : m * x' = k * x * k⁻¹ := hmx
      have hmK : m ∈ K := by
        have e : m = k * x * k⁻¹ * x'⁻¹ := by rw [← hmx']; group
        rw [e]
        exact K.mul_mem (K.mul_mem (K.mul_mem hkK (hXK hx)) (K.inv_mem hkK)) (K.inv_mem (hXK hx'))
      have hmO : m ∈ O := hONK ⟨hm, hmK⟩
      have hko : k * o * k⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp (hKO hkK) o).mp ho
      have e : k * (x * o) * k⁻¹ = m * x' * (k * o * k⁻¹) := by
        calc k * (x * o) * k⁻¹ = (k * x * k⁻¹) * (k * o * k⁻¹) := by group
          _ = m * x' * (k * o * k⁻¹) := by rw [← hmx']
      rw [e]
      exact (X ⊔ O).mul_mem ((X ⊔ O).mul_mem (Subgroup.mem_sup_right hmO)
        (Subgroup.mem_sup_left hx')) (Subgroup.mem_sup_right hko)
    have hc2 : ((K ⊓ σ.N) ⊔ σ.ON) ⊓ Subgroup.normalizer ((σ.ON ⊔ X : Subgroup G) : Set G) ≤
        W ⊔ σ.D ⊔ (K ⊓ σ.N ⊓ Subgroup.normalizer ((O ⊔ U : Subgroup G) : Set G)) ⊔ σ.ON := by
      intro m hm
      have hm' : m ∈ (((K ⊓ σ.N) ⊔ σ.ON : Subgroup G) : Set G) := hm.1
      rw [hMcoe] at hm'
      obtain ⟨k, hk, n, hn, rfl⟩ := hm'
      have hkN : k ∈ Subgroup.normalizer ((σ.ON ⊔ X : Subgroup G) : Set G) := by
        have h1 : n⁻¹ ∈ Subgroup.normalizer ((σ.ON ⊔ X : Subgroup G) : Set G) :=
          Subgroup.le_normalizer (Subgroup.mem_sup_left (σ.ON.inv_mem hn))
        have := (Subgroup.normalizer _).mul_mem hm.2 h1
        simpa using this
      exact Subgroup.mul_mem_sup (Subgroup.mem_sup_right ⟨hk, hc1 ⟨hk, hkN⟩⟩) hn
    have hMle : (K ⊓ σ.N) ⊔ σ.ON ≤
        W ⊔ σ.D ⊔ (K ⊓ σ.N ⊓ Subgroup.normalizer ((O ⊔ U : Subgroup G) : Set G)) ⊔ σ.ON :=
      hgen.trans (sup_le (sup_le (sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left))
        (le_sup_right.trans (le_sup_left.trans le_sup_left))) hc2) le_sup_right)
    intro k hk
    have hk' : k ∈ ((O ⊔ (K ⊓ σ.N) : Subgroup G) : Set G) := by
      rw [hfac]
      exact hk
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (inf_le_left.trans hKO)] at hk'
    obtain ⟨o, ho, k', hk'', rfl⟩ := hk'
    have h : k' ∈ ((W ⊔ σ.D ⊔ (K ⊓ σ.N ⊓ Subgroup.normalizer ((O ⊔ U : Subgroup G) : Set G)) ⊔
        σ.ON : Subgroup G) : Set G) := hMle (Subgroup.mem_sup_left hk'')
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hR₀N.trans hNON)] at h
    obtain ⟨r, hr', n, hn, hrn⟩ := h
    have hrn' : r * n = k' := hrn
    have hnK : n ∈ K := by
      have e : n = r⁻¹ * k' := by rw [← hrn']; group
      rw [e]
      exact K.mul_mem (K.inv_mem (hR₀K hr')) hk''.1
    have hnO : n ∈ O := hONK ⟨hn, hnK⟩
    have hR₀T : W ⊔ σ.D ⊔ (K ⊓ σ.N ⊓ Subgroup.normalizer ((O ⊔ U : Subgroup G) : Set G)) ≤
        W ⊔ σ.D ⊔ (K ⊓ Subgroup.normalizer ((O ⊔ U : Subgroup G) : Set G)) ⊔ O :=
      (sup_le_sup_left (inf_le_inf_right _ inf_le_left) _).trans le_sup_left
    rw [← hrn']
    exact Subgroup.mul_mem _ ((le_sup_right : O ≤ _) ho)
      (Subgroup.mul_mem _ (hR₀T hr') ((le_sup_right : O ≤ _) hnO))

end Setting

end CFSG.ABGTheoremB

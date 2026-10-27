module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210ThmA

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.Open

variable {X : Type} [Group X] [Finite X] {A : Subgroup X}

private theorem goldschmidtOddCore_eq_pPrimeCore_local (H : Type*) [Group H] :
    goldschmidtOddCore H = CFSG.pPrimeCore 2 H := by
  unfold goldschmidtOddCore CFSG.pPrimeCore
  congr 1
  ext N
  simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]

private lemma normal_map_subtype_of_characteristic {M : Subgroup X} [M.Normal]
    {O : Subgroup ↥M} (hO : O.Characteristic) : (O.map M.subtype).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hn
  refine Subgroup.mem_map.mpr ⟨(MulAut.conjNormal g) m, ?_, ?_⟩
  · have hmap := Subgroup.characteristic_iff_map_eq.mp hO (MulAut.conjNormal g)
    have hmem : (MulAut.conjNormal g) m ∈ O.map (MulAut.conjNormal g).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨m, hm, rfl⟩
    rwa [hmap] at hmem
  · exact MulAut.conjNormal_apply g m

theorem goldschmidtOddCore_eq_bot_of_normal {M : Subgroup X} [M.Normal]
    (hodd : ∀ P : Subgroup X, P.Normal → Odd (Nat.card P) → P = ⊥) :
    goldschmidtOddCore ↥M = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : (goldschmidtOddCore ↥M).Characteristic := by
    rw [goldschmidtOddCore_eq_pPrimeCore_local]
    infer_instance
  have hoddO : Odd (Nat.card (goldschmidtOddCore ↥M)) := by
    rw [goldschmidtOddCore_eq_pPrimeCore_local]
    exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥M))
  have hnorm : ((goldschmidtOddCore ↥M).map M.subtype).Normal :=
    normal_map_subtype_of_characteristic (M := M) (O := goldschmidtOddCore ↥M) hchar
  have hoddMap : Odd (Nat.card ((goldschmidtOddCore ↥M).map M.subtype)) := by
    rw [Subgroup.card_map_of_injective M.subtype_injective]
    exact hoddO
  have hbot := hodd _ hnorm hoddMap
  exact (Subgroup.map_eq_bot_iff_of_injective (goldschmidtOddCore ↥M)
    M.subtype_injective).mp hbot

theorem pCoreOf_normal {M : Subgroup X} [M.Normal] : (pCoreOf 2 M).Normal := by
  exact normal_map_subtype_of_characteristic (M := M) (O := CFSG.pCore 2 ↥M) inferInstance

theorem isPGroup_pCoreOf (M : Subgroup X) : IsPGroup 2 (pCoreOf 2 M) := by
  exact (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).map M.subtype

theorem L210_thmA_involutions (hGold : GoldschmidtTheoremA) (S : Sylow 2 X)
    (hAS : A ≤ (S : Subgroup X)) (hAb : IsMulCommutative A)
    (hclosed : ∀ a ∈ A, ∀ g : X, g⁻¹ * a * g ∈ (S : Subgroup X) → g⁻¹ * a * g ∈ A)
    (hO : goldschmidtOddCore ↥(Subgroup.normalClosure (A : Set X)) = ⊥)
    (hP : pCoreOf 2 (Subgroup.normalClosure (A : Set X)) = ⊥) :
    ∀ q ∈ (S : Subgroup X) ⊓ Subgroup.normalClosure (A : Set X), q * q = 1 → q ∈ A := by
  intro q hq hq2
  let M : Subgroup X := Subgroup.normalClosure (A : Set X)
  let O : Subgroup ↥M := goldschmidtOddCore ↥M
  let π : ↥M →* ↥M ⧸ O := QuotientGroup.mk' O
  have hObot : O = ⊥ := hO
  have hpcmap : (CFSG.pCore 2 ↥M).map M.subtype = ⊥ := by
    simpa only [pCoreOf] using hP
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hπker : π.ker = O := QuotientGroup.ker_mk' O
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, hπker]
    exact hObot
  have hQ : CFSG.pCore 2 (↥M ⧸ O) = ⊥ := by
    let Q : Subgroup (↥M ⧸ O) := CFSG.pCore 2 (↥M ⧸ O)
    let Q' : Subgroup ↥M := Q.comap π
    change Q = ⊥
    have hQ'normal : Q'.Normal := by
      show (Q.comap π).Normal
      exact Subgroup.Normal.comap CFSG.pCore_normal π
    have hQ'p : IsPGroup 2 Q' := by
      show IsPGroup 2 (Q.comap π)
      exact (CFSG.pCore_isPGroup (p := 2) (G := ↥M ⧸ O)).comap_of_injective π hπinj
    have hQ'le : Q' ≤ CFSG.pCore 2 ↥M := by
      show Q.comap π ≤ CFSG.pCore 2 ↥M
      exact le_sSup ⟨hQ'normal, hQ'p⟩
    have hpcm : CFSG.pCore 2 ↥M = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective (CFSG.pCore 2 ↥M)
        M.subtype_injective).mp hpcmap
    have hQ'bot : Q' = ⊥ := le_bot_iff.mp (hQ'le.trans (le_of_eq hpcm))
    have hmap : Q'.map π = Q := by
      show (Q.comap π).map π = Q
      exact Subgroup.map_comap_eq_self_of_surjective hπsurj Q
    rw [← hmap, hQ'bot, Subgroup.map_bot]
  obtain ⟨ha, hb, -⟩ := hGold X S A hAS hAb hclosed
  rw [hQ, bot_sup_eq] at ha
  rw [hQ, bot_sup_eq] at hb
  have hqS : q ∈ (S : Subgroup X) := hq.1
  have hqM : q ∈ M := hq.2
  let qM : ↥M := ⟨q, hqM⟩
  have hqM_S : qM ∈ (S : Subgroup X).subgroupOf M := by
    rw [Subgroup.mem_subgroupOf]
    exact hqS
  have hqM2 : qM * qM = 1 := by
    apply Subtype.ext
    exact hq2
  have hπqM2 : (π qM) ^ 2 = 1 := by
    rw [pow_two, ← map_mul, hqM2, map_one]
  have hπqM_T : π qM ∈ ((S : Subgroup X).subgroupOf M).map π ⊓
      goldschmidtLayer (↥M ⧸ O) :=
    ⟨Subgroup.mem_map.mpr ⟨qM, hqM_S, rfl⟩, by rw [ha]; trivial⟩
  have hπqM_cl : π qM ∈
      Subgroup.closure {t : ↥M ⧸ O | t ∈ ((S : Subgroup X).subgroupOf M).map π ⊓
        goldschmidtLayer (↥M ⧸ O) ∧ t ^ 2 = 1} :=
    Subgroup.subset_closure ⟨hπqM_T, hπqM2⟩
  have hπqM_map : π qM ∈ (A.subgroupOf M).map π := by
    rw [hb]
    exact hπqM_cl
  obtain ⟨a, haA, haeq⟩ := Subgroup.mem_map.mp hπqM_map
  have haqM : a = qM := hπinj haeq
  have haA' : (a : X) ∈ A := by
    simpa only [Subgroup.mem_subgroupOf] using haA
  have hval : (a : X) = q := by rw [haqM]
  simpa [hval] using haA'

end CFSG.EvenSporadicStandard.HNRecog.Harada

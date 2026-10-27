module

public import CFSG.Quasithin.Background.F7Basic
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Pair4

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Assembly CFSG.Quasithin.H13.F431.U42 U42F431

theorem not_Vsub_le_pCoreOf_P1 :
    ¬ Vsub ≤ pCoreOf 2 P1 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hVR
  let g : Y := ⟨wordP [1, 0, 2, 0, 1], wordP_mem _⟩
  have hg : g ∈ P1 := by
    rw [mem_P1_iff]
    apply Fin.ext
    change ((wordP [1, 0, 2, 0, 1]) (0 : Fin 45) : ℕ) = 0
    rw [applyW_eq]
    decide +kernel
  have hg15 : ((g : Y) : P45) (15 : Fin 45) = 34 := by
    apply Fin.ext
    change ((wordP [1, 0, 2, 0, 1]) (15 : Fin 45) : ℕ) = 34
    rw [applyW_eq]
    decide +kernel
  have hv : sY (15 : Fin 45) ∈ pCoreOf 2 P1 :=
    hVR (Subgroup.subset_closure ⟨15, by
      show (15 : ℕ) ∈ L0
      decide +kernel, rfl⟩)
  have hv' : sY (34 : Fin 45) ∈ pCoreOf 2 P1 := by
    have hconj := (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P1 hg) (sY (15 : Fin 45))).mp hv
    rw [sY_conj, hg15] at hconj
    exact hconj
  let a : Y := sY (15 : Fin 45) * sY (34 : Fin 45)
  have haR : a ∈ pCoreOf 2 P1 := Subgroup.mul_mem _ hv hv'
  have hl (i : Fin 45) : CFSG.Quasithin.RepL (tpTab.getD i []) ((sY i : Y) : P45) := by
    rw [tpTab_getD i i.2]
    exact repL_sT i
  let A : List ℕ := [0, 38, 42, 28, 10, 22, 32, 13, 18, 31, 19, 5, 33, 17, 8, 34, 25, 7, 14, 4, 30, 21, 11, 23, 26, 35, 44, 2, 37, 1, 36, 43, 39, 41, 40, 16, 20, 3, 29, 6, 15, 12, 27, 9, 24]
  have hAlit : CFSG.Quasithin.compL (tpTab.getD 15 []) (tpTab.getD 34 []) = A := by
    decide +kernel
  have ha : CFSG.Quasithin.RepL A ((a : Y) : P45) := by
    rw [← hAlit]
    exact CFSG.Quasithin.repL_mul (hl 15) (hl 34)
  have ha3 : a ^ 3 = 1 := by
    have hcomp : CFSG.Quasithin.compL (CFSG.Quasithin.compL A A) A = List.range 45 := by
      decide +kernel
    have hrep := CFSG.Quasithin.repL_mul (CFSG.Quasithin.repL_mul ha ha) ha
    have hrep1 : CFSG.Quasithin.RepL
        (CFSG.Quasithin.compL (CFSG.Quasithin.compL A A) A) (1 : P45) := by
      rw [hcomp]
      exact CFSG.Quasithin.repL_one 45
    have hcube := CFSG.Quasithin.eq_of_repL hrep hrep1
    have hthree (z : Y) : z ^ 3 = (z * z) * z :=
      (pow_succ z 2).trans (congrArg (fun t : Y => t * z) (pow_two z))
    exact (hthree a).trans (Subtype.ext hcube)
  have hane : a ≠ 1 := by
    have hA : A ≠ List.range 45 := by decide +kernel
    have hne := CFSG.Quasithin.ne_of_repL_ne ha (CFSG.Quasithin.repL_one 45) hA
    exact fun h => hne (congrArg Subtype.val h)
  have hord : orderOf a = 3 := orderOf_eq_prime ha3 hane
  have hp : IsPGroup 2 (pCoreOf 2 P1) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P1
  obtain ⟨n, hn⟩ := hp ⟨a, haR⟩
  have hpow : a ^ (2 ^ n) = 1 := congrArg (fun z : ↥(pCoreOf 2 P1) => (z : Y)) hn
  have hd := orderOf_dvd_of_pow_eq_one hpow
  rw [hord] at hd
  have hbad : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hd
  norm_num at hbad

theorem card_pCoreOf_P1 :
    Nat.card ↥(pCoreOf 2 P1) = 32 := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let B : Subgroup P1 := B0.subgroupOf P1
  have hBi : B.index = 3 := relIndex_B0_P1
  have hKi : B.normalCore.index ≤ 6 := by
    rw [Subgroup.normalCore_eq_ker, Subgroup.index_ker]
    calc
      Nat.card ↥(MulAction.toPermHom P1 (P1 ⧸ B)).range ≤
          Nat.card (Equiv.Perm (P1 ⧸ B)) := Subgroup.card_le_card_group _
      _ = 6 := by rw [Nat.card_perm, ← Subgroup.index_eq_card, hBi]; norm_num
  have hKc' : 96 ≤ Nat.card ↥B.normalCore := by
    have h := Subgroup.card_mul_index B.normalCore
    rw [card_P1] at h
    nlinarith
  let K : Subgroup Y := B.normalCore.map P1.subtype
  have hKc : 96 ≤ Nat.card K := by
    rw [show Nat.card K = Nat.card ↥B.normalCore from
      Subgroup.card_map_of_injective P1.subtype_injective]
    exact hKc'
  have hKB : K ≤ B0 := by
    rintro _ ⟨y, hy, rfl⟩
    exact B.normalCore_le hy
  have hKP : K ≤ P1 := hKB.trans B0_le_P1
  have hKsub : K.subgroupOf P1 = B.normalCore := by
    change (B.normalCore.map P1.subtype).comap P1.subtype = B.normalCore
    exact Subgroup.comap_map_eq_self_of_injective P1.subtype_injective _
  have hKN : P1 ≤ Subgroup.normalizer (K : Set Y) := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hKP).1
    rw [hKsub]
    infer_instance
  have hTi : T.relIndex B0 = 3 := by
    have h := Subgroup.relIndex_mul_card (H := T) (K := B0)
    rw [inf_eq_left.mpr T_le_B0, card_T, card_B0] at h
    omega
  letI : (T.subgroupOf B0).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer T_le_B0).2 B0_le_normalizer_T
  have hRi : T.relIndex K ≤ 3 := by
    have h := Subgroup.relIndex_dvd_index_of_normal
      (H := T.subgroupOf B0) (K := K.subgroupOf B0)
    rw [Subgroup.relIndex_subgroupOf hKB] at h
    change T.relIndex K ∣ T.relIndex B0 at h
    rw [hTi] at h
    exact Nat.le_of_dvd (by norm_num) h
  have hRc : 32 ≤ Nat.card ↥(T ⊓ K) := by
    have h := Subgroup.relIndex_mul_card (H := T) (K := K)
    nlinarith
  have hRp : IsPGroup 2 ↥(T ⊓ K) := isSylow_T.2.1.to_le inf_le_left
  have hRK : T ⊓ K ≤ pCoreOf 2 K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
      (CFSG.Quasithin.F7.le_normalizer_inf (hKB.trans B0_le_normalizer_T) Subgroup.le_normalizer) hRp
  have hRcore : T ⊓ K ≤ pCoreOf 2 P1 := hRK.trans
    (CFSG.Quasithin.F7.pCoreOf_mono_of_le_normalizer hKP hKN)
  have hcoreGe : 32 ≤ Nat.card ↥(pCoreOf 2 P1) :=
    hRc.trans (Subgroup.card_le_of_le hRcore)
  have hSyl : CFSG.QuasithinUnique.IsSylowTwoOf T P1 :=
    ⟨T_le_B0.trans B0_le_P1, isSylow_T.2.1, by
      show ¬ 2 ∣ T.relIndex P1
      have h := Subgroup.relIndex_mul_card (H := T) (K := P1)
      rw [inf_eq_left.mpr (T_le_B0.trans B0_le_P1), card_T, card_P1] at h
      have : T.relIndex P1 = 9 := by omega
      rw [this]
      norm_num⟩
  have hcoreT : pCoreOf 2 P1 ≤ T :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hSyl
  have hcoreLe : Nat.card ↥(pCoreOf 2 P1) ≤ 64 := by
    simpa only [card_T] using Subgroup.card_le_of_le hcoreT
  obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P1).exists_card_eq
  have hnle : n ≤ 6 := by
    by_contra h
    have hp : 2 ^ 7 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hn] at hp
    omega
  have hne64 : Nat.card ↥(pCoreOf 2 P1) ≠ 64 := by
    intro h
    have heq : pCoreOf 2 P1 = T := Subgroup.eq_of_le_of_card_ge hcoreT (by rw [h, card_T])
    exact not_Vsub_le_pCoreOf_P1 (by rw [heq]; exact Vsub_le_T)
  interval_cases n <;> norm_num only [Nat.reducePow] at hn <;> omega

end CFSG.GH74.QTGen4.U42

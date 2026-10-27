module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.TC
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Defs
public import CFSG.Quasithin.Background.A1cBridge

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action

theorem swap_conj_prod : ∀ τ : Equiv.Perm (Fin 5), τ 4 = 4 → τ ^ 3 = 1 → τ ≠ 1 →
    (Equiv.swap 0 1 * (τ * Equiv.swap 0 1 * τ⁻¹)) ^ 3 = 1 ∧
      Equiv.swap 0 1 * (τ * Equiv.swap 0 1 * τ⁻¹) ≠ 1 := by
  decide +kernel

@[expose] def c3 : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 1 2

theorem c3_mem_alt : c3 ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem c3_four : c3 4 = 4 := by decide +kernel

theorem c3_cube : c3 ^ 3 = 1 := by decide +kernel

theorem c3_ne : c3 ≠ 1 := by decide +kernel

namespace StdCfg

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

omit [Finite G] in
theorem borelK_le (M L : Subgroup G) : borelK M L ≤ M ⊓ L := by
  rintro k ⟨y, -, rfl⟩
  exact y.2

theorem borelK_le_H (C : StdCfg T M H S L) : borelK M L ≤ H :=
  (borelK_le M L).trans (inf_le_right.trans (C56.le_H C.hcs))

theorem mem_M_of_pi_mem (C : StdCfg T M H S L) (h : ↥H) (hπ : C.D.π h ∈ S4std) :
    (h : G) ∈ M := by
  obtain ⟨Khat, hKH, hKmem⟩ := C.exists_Khat
  have hKhatM : Khat ≤ M := by
    apply C.hcs.maxInf Khat
    · intro s hs
      exact (hKmem ⟨s, C.hcs.sylow.le hs⟩).mpr (by
        rw [mem_S4std]
        exact Dset_le_S4 _ ((mem_Dstd _).mp (C.pi_mem_Dstd hs)))
    · refine lt_of_le_of_ne hKH ?_
      intro heq
      obtain ⟨k, hk⟩ := C.hsurj (Equiv.swap 0 4)
      have hkK : (k : G) ∈ Khat := heq ▸ k.2
      have := (hKmem k).mp hkK
      rw [hk, mem_S4std] at this
      simp at this
  exact hKhatM ((hKmem h).mpr hπ)

theorem exists_three_elt (C : StdCfg T M H S L) :
    ∃ (k : G) (hk : k ∈ H), k ∈ borelK M L ∧ (C.D.π ⟨k, hk⟩) ^ 3 = 1 ∧
      C.D.π ⟨k, hk⟩ ≠ 1 ∧ C.D.π ⟨k, hk⟩ 4 = 4 := by
  obtain ⟨l, hl⟩ := C.D.hα ⟨c3, c3_mem_alt⟩
  have hlH : (l : G) ∈ H := C.D.hLH l.2
  have hπl : C.D.π ⟨l, hlH⟩ = c3 := by
    have := C.D.hπL l l.2
    rw [hl] at this
    exact this
  have hlM : (l : G) ∈ M :=
    C.mem_M_of_pi_mem ⟨l, hlH⟩ (by rw [hπl, mem_S4std]; exact c3_four)
  obtain ⟨e, he⟩ := exists_pow_mem_opResidual (p := 2) (A := M ⊓ L) (x := (l : G)) ⟨hlM, l.2⟩
  have hk : (l : G) ^ 2 ^ e ∈ borelK M L := opResidual_le_pResidualOf (M ⊓ L) he
  have hkH : (l : G) ^ 2 ^ e ∈ H := H.pow_mem hlH _
  have hπpow : C.D.π ⟨(l : G) ^ 2 ^ e, hkH⟩ = c3 ^ 2 ^ e := by
    have : (⟨(l : G) ^ 2 ^ e, hkH⟩ : ↥H) = (⟨l, hlH⟩ : ↥H) ^ 2 ^ e := by
      apply Subtype.ext
      simp
    rw [this, map_pow, hπl]
  refine ⟨(l : G) ^ 2 ^ e, hkH, hk, ?_, ?_, ?_⟩
  · rw [hπpow, ← pow_mul, mul_comm, pow_mul, c3_cube, one_pow]
  · intro h1
    rw [hπpow] at h1
    have h2 := pow_gcd_eq_one.mpr ⟨h1, c3_cube⟩
    have hg : Nat.gcd (2 ^ e) 3 = 1 := Nat.Coprime.pow_left e (by decide)
    rw [hg, pow_one] at h2
    exact c3_ne h2
  · rw [hπpow]
    exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self c3_four _

theorem exists_Ux_swap (C : StdCfg T M H S L) {x : G} (hxT : x ∈ T) (hxS : x ∉ S) :
    ∃ (u : G) (hu : u ∈ H), u ∈ conjR (blockU L) x ∧ C.D.π ⟨u, hu⟩ = Equiv.swap 0 1 := by
  have hsw : Equiv.swap (0 : Fin 5) 1 ∈ Estd := by
    show Equiv.swap (0 : Fin 5) 1 ∈ Eset
    decide +kernel
  obtain ⟨r, hr, hπr⟩ := C.hRE' _ hsw
  have hrR := hr
  rw [C.F.R_eq x hxT hxS, ← sup_assoc, ← C.F.Q_eq] at hrR
  have hUxR : conjR (blockU L) x ≤ baum S := by
    rw [C.F.R_eq x hxT hxS]
    exact le_sup_of_le_right le_sup_right
  have hUxH : conjR (blockU L) x ≤ H := hUxR.trans (baum_le_H C.hcs)
  have hnorm : conjR (blockU L) x ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    hUxH.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H)
  have hrR' : r ∈ conjR (blockU L) x ⊔ pCoreOf 2 H := by rwa [sup_comm] at hrR
  obtain ⟨a, ha, b, hb, hab⟩ := C5.mem_sup_of_le_normalizer (x := r) hnorm hrR'
  have haH : a ∈ H := hUxH ha
  have hbH : b ∈ H := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H hb
  refine ⟨a, haH, ha, ?_⟩
  have h1 : C.D.π ⟨b, hbH⟩ = 1 := (C.hker ⟨b, hbH⟩).mpr hb
  have h2 : (⟨r, baum_le_H C.hcs hr⟩ : ↥H) = ⟨a, haH⟩ * ⟨b, hbH⟩ := Subtype.ext hab
  rw [← hπr, h2, map_mul, h1, mul_one]

theorem U_not_le_O2_M1 (C : StdCfg T M H S L) :
    ¬ blockU L ≤ pCoreOf 2 (T ⊔ borelK M L) := by
  intro hU
  obtain ⟨x, hxT, hxS⟩ := C.exists_mem_T_sdiff
  obtain ⟨k, hkH, hkK, hk3, hk1, hk4⟩ := C.exists_three_elt
  obtain ⟨u, huH, huUx, hπu⟩ := C.exists_Ux_swap hxT hxS
  have hnorm : T ⊔ borelK M L ≤
      Subgroup.normalizer (pCoreOf 2 (T ⊔ borelK M L) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _
  have hxM1 : x ∈ T ⊔ borelK M L := Subgroup.mem_sup_left hxT
  have hkM1 : k ∈ T ⊔ borelK M L := Subgroup.mem_sup_right hkK
  have huO : u ∈ pCoreOf 2 (T ⊔ borelK M L) := by
    have hu0 : x * u * x⁻¹ ∈ blockU L :=
      (mem_conjSubgroup_iff (A := blockU L) (g := x) (x := u)).mp huUx
    have h1 : x * u * x⁻¹ ∈ pCoreOf 2 (T ⊔ borelK M L) := hU hu0
    have h2 := (Subgroup.mem_normalizer_iff.mp (hnorm (inv_mem hxM1)) (x * u * x⁻¹)).mp h1
    have h3 : x⁻¹ * (x * u * x⁻¹) * (x⁻¹)⁻¹ = u := by group
    rwa [h3] at h2
  have hkuO : k * u * k⁻¹ ∈ pCoreOf 2 (T ⊔ borelK M L) :=
    (Subgroup.mem_normalizer_iff.mp (hnorm hkM1) u).mp huO
  have hwO : u * (k * u * k⁻¹) ∈ pCoreOf 2 (T ⊔ borelK M L) := mul_mem huO hkuO
  have hwH : u * (k * u * k⁻¹) ∈ H :=
    mul_mem huH (mul_mem (mul_mem hkH huH) (inv_mem hkH))
  have hπw : C.D.π ⟨u * (k * u * k⁻¹), hwH⟩ =
      Equiv.swap 0 1 * (C.D.π ⟨k, hkH⟩ * Equiv.swap 0 1 * (C.D.π ⟨k, hkH⟩)⁻¹) := by
    have : (⟨u * (k * u * k⁻¹), hwH⟩ : ↥H) =
        ⟨u, huH⟩ * (⟨k, hkH⟩ * ⟨u, huH⟩ * ⟨k, hkH⟩⁻¹) := rfl
    rw [this, map_mul, map_mul, map_mul, map_inv, hπu]
  obtain ⟨n, hn⟩ := (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2
    (T ⊔ borelK M L)) ⟨_, hwO⟩
  have hn' : (u * (k * u * k⁻¹)) ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have hπn : (C.D.π ⟨u * (k * u * k⁻¹), hwH⟩) ^ 2 ^ n = 1 := by
    rw [← map_pow]
    have : (⟨u * (k * u * k⁻¹), hwH⟩ : ↥H) ^ 2 ^ n = 1 := by
      apply Subtype.ext
      simpa using hn'
    rw [this, map_one]
  obtain ⟨h3, h1'⟩ := swap_conj_prod _ hk4 hk3 hk1
  rw [← hπw] at h3 h1'
  have h2 := pow_gcd_eq_one.mpr ⟨hπn, h3⟩
  have hg : Nat.gcd (2 ^ n) 3 = 1 := Nat.Coprime.pow_left n (by decide)
  rw [hg, pow_one] at h2
  exact h1' h2

theorem M1_cent_z (C : StdCfg T M H S L) (hne : blockTC T S L ≠ ⊥) {m : G}
    (hm : m ∈ T ⊔ borelK M L) : C.zU * m = m * C.zU := by
  have hle : T ⊔ borelK M L ≤ Subgroup.centralizer ({C.zU} : Set G) := by
    refine sup_le ?_ ?_
    · intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      have := C.zU_central_T hne hy
      calc C.zU * y = (y * C.zU * y⁻¹) * y := by rw [this]
        _ = y * C.zU := by group
    · intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      have hkM : k ∈ M := (borelK_le M L hk).1
      have hkH : k ∈ H := C.borelK_le_H hk
      have hπ := C.pi_MH ⟨k, hkH⟩ hkM
      have hk' : k * C.zU * k⁻¹ = C.zU :=
        (C.conj_zU_iff ⟨k, hkH⟩).mpr (z0_fixed _ ((mem_S4std _).mp hπ))
      calc C.zU * k = (k * C.zU * k⁻¹) * k := by rw [hk']
        _ = k * C.zU := by group
  exact Subgroup.mem_centralizer_iff.mp (hle hm) C.zU (Set.mem_singleton _)

theorem T_normalizes_N (C : StdCfg T M H S L) (hne : blockTC T S L ≠ ⊥) {t : G}
    (ht : t ∈ blockTC T S L) (hxt : ∀ x ∈ T, x ∉ S → x⁻¹ * t * x = t * C.zU) {y : G}
    (hy : y ∈ T) (n : G)
    (hn : n ∈ (T ⊔ borelK M L) ⊓ Subgroup.centralizer ({t} : Set G)) :
    y * n * y⁻¹ ∈ (T ⊔ borelK M L) ⊓ Subgroup.centralizer ({t} : Set G) := by
  obtain ⟨hnM1, hnC⟩ := Subgroup.mem_inf.mp hn
  have hnt : t * n = n * t := Subgroup.mem_centralizer_iff.mp hnC t (Set.mem_singleton t)
  have hnz : C.zU * n = n * C.zU := C.M1_cent_z hne hnM1
  refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (Subgroup.mem_sup_left hy) hnM1)
    (inv_mem (Subgroup.mem_sup_left hy)), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  rw [hh]
  have ht'' : y⁻¹ * t * y = t ∨ y⁻¹ * t * y = t * C.zU := by
    by_cases hyS : y ∈ S
    · left
      have h1 : t * y = y * t := C.TC_comm_H ht (C.hcs.sylow.le hyS)
      calc y⁻¹ * t * y = y⁻¹ * (t * y) := by group
        _ = y⁻¹ * (y * t) := by rw [h1]
        _ = t := by group
    · right
      exact hxt y hy hyS
  have hcomm : n * (y⁻¹ * t * y) = (y⁻¹ * t * y) * n := by
    rcases ht'' with h' | h'
    · rw [h']
      exact hnt.symm
    · rw [h']
      calc n * (t * C.zU) = (n * t) * C.zU := by group
        _ = (t * n) * C.zU := by rw [hnt]
        _ = t * (n * C.zU) := by group
        _ = t * (C.zU * n) := by rw [hnz]
        _ = (t * C.zU) * n := by group
  calc t * (y * n * y⁻¹) = y * ((y⁻¹ * t * y) * n) * y⁻¹ := by group
    _ = y * (n * (y⁻¹ * t * y)) * y⁻¹ := by rw [hcomm]
    _ = (y * n * y⁻¹) * t := by group

theorem M1_le_normalizer_N (C : StdCfg T M H S L) (hne : blockTC T S L ≠ ⊥) {t : G}
    (ht : t ∈ blockTC T S L) (hxt : ∀ x ∈ T, x ∉ S → x⁻¹ * t * x = t * C.zU) :
    T ⊔ borelK M L ≤ Subgroup.normalizer
      (((T ⊔ borelK M L) ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G) := by
  refine sup_le ?_ ?_
  · intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact C.T_normalizes_N hne ht hxt hy n hn
    · intro hn
      have := C.T_normalizes_N hne ht hxt (inv_mem hy) _ hn
      have e : y⁻¹ * (y * n * y⁻¹) * y⁻¹⁻¹ = n := by group
      rwa [e] at this
  · intro k hk
    have hkN : k ∈ (T ⊔ borelK M L) ⊓ Subgroup.centralizer ({t} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_right hk, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact C.TC_comm_H ht (C.borelK_le_H hk)
    exact Subgroup.le_normalizer hkN

theorem U_not_le_O2_cent (C : StdCfg T M H S L) (hne : blockTC T S L ≠ ⊥) {t : G}
    (ht : t ∈ blockTC T S L) (hxt : ∀ x ∈ T, x ∉ S → x⁻¹ * t * x = t * C.zU) :
    ¬ blockU L ≤ pCoreOf 2 (Subgroup.centralizer ({t} : Set G)) := by
  intro hU
  have hnormN := C.M1_le_normalizer_N hne ht hxt
  set M1 : Subgroup G := T ⊔ borelK M L with hM1
  set Cc : Subgroup G := Subgroup.centralizer ({t} : Set G) with hCc
  set N : Subgroup G := M1 ⊓ Cc with hN
  have hUN : blockU L ≤ N := by
    refine le_inf ?_ ?_
    · exact (blockU_le_S C.hcs C.hj).trans (C.hcs.le_T.trans le_sup_left)
    · intro u hu
      rw [hCc, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact C.TC_comm_H ht (C.blockU_le_H hu)
  have hW : pCoreOf 2 Cc ⊓ N ≤ pCoreOf 2 N := by
    refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 (pCoreOf 2 Cc ⊓ N) N
      inf_le_right ?_ ?_
    · rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
      intro n hn
      have h1 : n ∈ Subgroup.normalizer (pCoreOf 2 Cc : Set G) :=
        (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 Cc) hn.2
      have h2 : n ∈ Subgroup.normalizer (N : Set G) := Subgroup.le_normalizer hn
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h1, h2⟩
    · exact (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 Cc).to_le inf_le_left
  have hO : pCoreOf 2 N ≤ pCoreOf 2 M1 := by
    have hincl : pCoreOf 2 N ≤ M1 :=
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 N).trans inf_le_left
    refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 (pCoreOf 2 N) M1
      hincl ?_ ?_
    · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hincl]
      exact hnormN.trans
        (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_localGroup_le_normalizer_pCoreOf 2 N)
    · exact CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 N
  exact C.U_not_le_O2_M1 fun u hu => hO (hW ⟨hU hu, hUN hu⟩)

end StdCfg

end CFSG.QuasithinUnique.A5

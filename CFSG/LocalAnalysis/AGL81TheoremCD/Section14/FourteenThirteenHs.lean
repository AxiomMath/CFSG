module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenThirteenSylow
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A11TwoSetPerm
import CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6CentralizingBase
import CFSG.RankThree.PartOne.S11d.FinalLemmas
import CFSG.RankThree.PartOne.S12.Sec1511Y2Quot
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.Quasithin.Background.C126A5ExtractAux

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem twoResidual_sup_of_isPGroup_two {J T : Subgroup G} (hT : IsPGroup 2 T)
    (hTJ : T ≤ Subgroup.normalizer (J : Set G)) :
    CFSG.Quasithin.twoResidual (J ⊔ T) = CFSG.Quasithin.twoResidual J := by
  classical
  refine le_antisymm ?_ (CFSG.Quasithin.E1.twoResidual_mono le_sup_left)
  refine CFSG.Quasithin.twoResidual_le_of_isTwoQuotient
    ((CFSG.Quasithin.twoResidual_le J).trans le_sup_left) ?_ ?_
  · refine sup_le (CFSG.Quasithin.le_normalizer_twoResidual J) ?_
    intro t ht
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hJt : J.map (MulAut.conj t).toMonoidHom = J :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTJ ht)
    have hmap := CFSG.Quasithin.E1.map_twoResidual (MulAut.conj t).toMonoidHom J
    rw [hJt] at hmap
    exact hmap
  · intro y hy
    have hy' : y ∈ ((J ⊔ T : Subgroup G) : Set G) := hy
    rw [Subgroup.coe_mul_of_right_le_normalizer_left J T hTJ] at hy'
    obtain ⟨j, hj, t, ht, rfl⟩ := Set.mem_mul.mp hy'
    obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
    have hk' : t ^ 2 ^ k = 1 := congrArg Subtype.val hk
    obtain ⟨j', hj', hpow⟩ := CFSG.Quasithin.A4.exists_pow_mul_eq hj (hTJ ht) (2 ^ k)
    obtain ⟨l, hl⟩ := CFSG.Quasithin.twoResidual_isTwoQuotient J j' hj'
    refine ⟨k + l, ?_⟩
    have hsplit : (j * t) ^ 2 ^ (k + l) = ((j * t) ^ 2 ^ k) ^ 2 ^ l := by
      rw [pow_add, pow_mul]
    rw [hsplit, hpow, hk', mul_one]
    exact hl

private theorem le_normalizer_inf_of_le_of_normalizer {K M H T : Subgroup G}
    (hTH : T ≤ H) (hTM : T ≤ M) (hKH : H ≤ Subgroup.normalizer (K : Set G)) :
    T ≤ Subgroup.normalizer (K ⊓ M : Set G) := by
  intro t ht
  have htK : t ∈ Subgroup.normalizer (K : Set G) := hKH (hTH ht)
  have htM : t ∈ Subgroup.normalizer (M : Set G) := Subgroup.le_normalizer (hTM ht)
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨htK, htM⟩

private theorem range_actPerm_le_centralizer {K M J Y : Subgroup G}
    (e : threeStar K ≃* alternatingGroup (Fin 11)) {i j : Fin 11} (hij : i ≠ j)
    (hI : (((K ⊓ M).subgroupOf K).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))).map e.toMonoidHom = a11TwoSetStab i j)
    (hJ : J = K ⊓ M) (hJY : J ≤ Y)
    (hYJ : Y ≤ Subgroup.normalizer (J : Set G))
    (hYN : Y ≤ Subgroup.normalizer (K : Set G)) :
    ((actPerm e).comp (Subgroup.inclusion hYN)).range ≤
      Subgroup.centralizer ({Equiv.swap i j} : Set (Equiv.Perm (Fin 11))) ∧
    (a11TwoSetStab i j).map (alternatingGroup (Fin 11)).subtype ≤
      ((actPerm e).comp (Subgroup.inclusion hYN)).range := by
  classical
  let ψ : ↥Y →* Equiv.Perm (Fin 11) := (actPerm e).comp (Subgroup.inclusion hYN)
  have hψK : (J.subgroupOf Y).map ψ =
      (a11TwoSetStab i j).map (alternatingGroup (Fin 11)).subtype := by
    change ((J.subgroupOf Y).map ((actPerm e).comp (Subgroup.inclusion hYN))) = _
    rw [← Subgroup.map_map, CFSG.AGLEmbedding.map_inclusion_subgroupOf hJY hYN, hJ]
    exact map_actPerm_subgroupOf_eq_twoSet e hI
  have hge : (a11TwoSetStab i j).map (alternatingGroup (Fin 11)).subtype ≤ ψ.range := by
    rw [← hψK]
    exact Subgroup.map_le_range ψ (J.subgroupOf Y)
  have htopNorm : (⊤ : Subgroup ↥Y) ≤
      Subgroup.normalizer ((J.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := by
    intro y _
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp (hYJ y.2) (x : G)
  have hle : ψ.range ≤
      Subgroup.centralizer ({Equiv.swap i j} : Set (Equiv.Perm (Fin 11))) := by
    have h1 : ψ.range ≤ Subgroup.normalizer
        (((J.subgroupOf Y).map ψ : Subgroup (Equiv.Perm (Fin 11))) :
          Set (Equiv.Perm (Fin 11))) := by
      rw [MonoidHom.range_eq_map]
      exact (Subgroup.map_mono htopNorm).trans (Subgroup.le_normalizer_map ψ)
    rw [hψK] at h1
    exact h1.trans (normalizer_a11TwoSetStab_le hij)
  exact ⟨by simpa [ψ] using hle, by simpa [ψ] using hge⟩

private theorem le_ker_fold_of_maxInvariant {K M J R H Y : Subgroup G}
    (e : threeStar K ≃* alternatingGroup (Fin 11)) {i j : Fin 11} (hij : i ≠ j)
    (hI : (((K ⊓ M).subgroupOf K).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))).map e.toMonoidHom = a11TwoSetStab i j)
    (hJ : J = K ⊓ M) (hR : IsMaxInvariantTwoIn J R H) (hRY : R ≤ Y)
    (hYN : Y ≤ Subgroup.normalizer (K : Set G))
    (hRK : R ≤ Subgroup.normalizer (K : Set G))
    {φ : ↥Y →* ↥(a11TwoSetStab i j)}
    (hφ1 : ∀ y, φ y = 1 ↔
      (actPerm e (Subgroup.inclusion hYN y) = 1 ∨
        actPerm e (Subgroup.inclusion hYN y) = Equiv.swap i j)) :
    R.subgroupOf Y ≤ φ.ker := by
  intro y hy
  have hr : (y : G) ∈ R := Subgroup.mem_subgroupOf.mp hy
  rw [MonoidHom.mem_ker, hφ1]
  have hswap := actPerm_eq_one_or_swap e hij hI hR.2.1 (hJ ▸ hR.2.2.1) hRK
    (n := ⟨(y : G), hRK hr⟩) hr
  rw [show Subgroup.inclusion hYN y = ⟨(y : G), hRK hr⟩ from Subtype.ext rfl]
  exact hswap

private theorem exists_pow_mem_pCore_of_mem_ker_fold {K J Y : Subgroup G}
    (hJY : J ≤ Y) (hJleK : J ≤ K)
    (hYN : Y ≤ Subgroup.normalizer (K : Set G))
    (hJeq : CFSG.Quasithin.twoResidual Y = CFSG.Quasithin.twoResidual J)
    (hO2K : CFSG.Open.pCoreOf 2 K = (CFSG.pPrimeCore 3 ↥K).map K.subtype)
    (e : threeStar K ≃* alternatingGroup (Fin 11)) {i j : Fin 11}
    {φ : ↥Y →* ↥(a11TwoSetStab i j)}
    (hφ1 : ∀ y, φ y = 1 ↔
      (actPerm e (Subgroup.inclusion hYN y) = 1 ∨
        actPerm e (Subgroup.inclusion hYN y) = Equiv.swap i j))
    {y : ↥Y} (hy : y ∈ φ.ker) :
    ∃ k : ℕ, (y : G) ^ 2 ^ (k + 1) ∈ J ∧
      (y : G) ^ 2 ^ (k + 1) ∈ CFSG.Open.pCoreOf 2 K := by
  classical
  let ψ : ↥Y →* Equiv.Perm (Fin 11) := (actPerm e).comp (Subgroup.inclusion hYN)
  have hφ1' : ∀ y, φ y = 1 ↔ (ψ y = 1 ∨ ψ y = Equiv.swap i j) := by
    intro y
    simpa [ψ] using hφ1 y
  have hyφ : φ y = 1 := hy
  have hψy : ψ y = 1 ∨ ψ y = Equiv.swap i j := (hφ1' y).mp hyφ
  have hψy2 : ψ y ^ 2 = 1 := by
    rcases hψy with h1 | h1
    · rw [h1, one_pow]
    · rw [h1, pow_two, Equiv.swap_mul_self]
  obtain ⟨k, hk⟩ := CFSG.Quasithin.twoResidual_isTwoQuotient Y y y.2
  have hkJ : (y : G) ^ 2 ^ k ∈ J := by
    rw [hJeq] at hk
    exact CFSG.Quasithin.twoResidual_le J hk
  let w : G := (y : G) ^ 2 ^ (k + 1)
  have hwJ : w ∈ J := by
    have hstep : w = ((y : G) ^ 2 ^ k) ^ 2 := by
      dsimp [w]
      rw [pow_succ, pow_mul]
    rw [hstep, pow_two]
    exact J.mul_mem hkJ hkJ
  have hψw : ψ ⟨w, hJY hwJ⟩ = 1 := by
    have hcoe : (⟨w, hJY hwJ⟩ : ↥Y) = y ^ 2 ^ (k + 1) := Subtype.ext rfl
    have hpow : (ψ y) ^ 2 ^ (k + 1) = ((ψ y) ^ 2) ^ 2 ^ k := by
      rw [pow_succ, mul_comm, pow_mul]
    rw [hcoe, map_pow, hpow, hψy2, one_pow]
  have hψw' : actPerm e (Subgroup.inclusion hYN ⟨w, hJY hwJ⟩) = 1 := by
    simpa [ψ] using hψw
  have hwK : w ∈ K := hJleK hwJ
  have hew : e (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨w, hwK⟩) = 1 := by
    refine Subtype.ext ?_
    rw [← actPerm_of_mem e ⟨w, hYN (hJY hwJ)⟩ hwK]
    exact hψw'
  have hq : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨w, hwK⟩ = 1 := by
    apply e.injective
    rw [map_one]
    exact hew
  have hwP : (⟨w, hwK⟩ : ↥K) ∈ CFSG.pPrimeCore 3 ↥K :=
    (QuotientGroup.eq_one_iff (N := CFSG.pPrimeCore 3 ↥K) _).mp hq
  have hwO : w ∈ CFSG.Open.pCoreOf 2 K := by
    rw [hO2K]
    exact Subgroup.mem_map_of_mem K.subtype hwP
  exact ⟨k, hwJ, hwO⟩

private theorem exists_twoPow_eq_one_of_mem_ker_fold {K J Y : Subgroup G}
    (hJY : J ≤ Y) (hJleK : J ≤ K)
    (hYN : Y ≤ Subgroup.normalizer (K : Set G))
    (hJeq : CFSG.Quasithin.twoResidual Y = CFSG.Quasithin.twoResidual J)
    (hO2K : CFSG.Open.pCoreOf 2 K = (CFSG.pPrimeCore 3 ↥K).map K.subtype)
    (e : threeStar K ≃* alternatingGroup (Fin 11)) {i j : Fin 11}
    {φ : ↥Y →* ↥(a11TwoSetStab i j)}
    (hφ1 : ∀ y, φ y = 1 ↔
      (actPerm e (Subgroup.inclusion hYN y) = 1 ∨
        actPerm e (Subgroup.inclusion hYN y) = Equiv.swap i j))
    {y : ↥Y} (hy : y ∈ φ.ker) :
    ∃ k : ℕ, (y : G) ^ 2 ^ k = 1 := by
  classical
  obtain ⟨k, hwJ, hwO⟩ :=
    exists_pow_mem_pCore_of_mem_ker_fold hJY hJleK hYN hJeq hO2K e hφ1 hy
  let w : G := (y : G) ^ 2 ^ (k + 1)
  obtain ⟨b, hb⟩ := (isPGroup_iff_pow_pow_eq_one.mp
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)) ⟨w, hwO⟩
  have hb' : w ^ 2 ^ b = 1 := by
    have := congrArg Subtype.val hb
    simpa using this
  refine ⟨k + 1 + b, ?_⟩
  have hsplit : (y : G) ^ 2 ^ (k + 1 + b) = w ^ 2 ^ b := by
    have hexp : 2 ^ (k + 1 + b) = 2 ^ (k + 1) * 2 ^ b := by
      rw [Nat.add_assoc, pow_add, pow_add, pow_add, mul_assoc]
    dsimp [w]
    rw [hexp, pow_mul]
  exact hsplit.trans hb'

private theorem isPGroup_map_ker_fold {K J Y : Subgroup G}
    (hJY : J ≤ Y) (hJleK : J ≤ K)
    (hYN : Y ≤ Subgroup.normalizer (K : Set G))
    (hJeq : CFSG.Quasithin.twoResidual Y = CFSG.Quasithin.twoResidual J)
    (hO2K : CFSG.Open.pCoreOf 2 K = (CFSG.pPrimeCore 3 ↥K).map K.subtype)
    (e : threeStar K ≃* alternatingGroup (Fin 11)) {i j : Fin 11}
    {φ : ↥Y →* ↥(a11TwoSetStab i j)}
    (hφ1 : ∀ y, φ y = 1 ↔
      (actPerm e (Subgroup.inclusion hYN y) = 1 ∨
        actPerm e (Subgroup.inclusion hYN y) = Equiv.swap i j)) :
    IsPGroup 2 ((φ.ker).map Y.subtype) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro z
  obtain ⟨y, hy, hzy⟩ := Subgroup.mem_map.mp z.2
  obtain ⟨k, hk⟩ := exists_twoPow_eq_one_of_mem_ker_fold hJY hJleK hYN hJeq hO2K e hφ1 hy
  refine ⟨k, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, ← hzy]
  exact hk

private theorem le_normalizer_map_ker {Y : Subgroup G} {i j : Fin 11}
    {φ : ↥Y →* ↥(a11TwoSetStab i j)} :
    Y ≤ Subgroup.normalizer (((φ.ker).map Y.subtype) : Set G) := by
  have hsub : (((φ.ker).map Y.subtype).subgroupOf Y) = φ.ker := by
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective Y.subtype_injective]
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp ?_
  rw [hsub]
  exact MonoidHom.normal_ker φ

theorem S14Choice.exists_twoSetFold_ker_eq {M H E Q R T : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (h2 : CaseTwo M H) (hK : KNormalAt M)
    (hU : NineNineOneAt M) (hL : PLayerNotLeAt M) (hKF : KFactA11GammaTwoSet)
    (hR : IsMaxInvariantTwoIn (kSub 3 M H ⊓ M) R H) (hT : IsPGroup 2 T) (hTHM : T ≤ H ⊓ M)
    (hRT : R ≤ T) :
    ∃ (i j : Fin 11) (φ : ↥((kSub 3 M H ⊓ M) ⊔ T) →* ↥(a11TwoSetStab i j)), i ≠ j ∧
      Function.Surjective φ ∧ φ.ker = R.subgroupOf ((kSub 3 M H ⊓ M) ⊔ T) := by
  classical
  let K : Subgroup G := kSub 3 M H
  let J : Subgroup G := K ⊓ M
  let Y : Subgroup G := J ⊔ T
  let N : Subgroup G := Subgroup.normalizer (K : Set G)
  obtain ⟨e, i, j, hij, hI⟩ := h.exists_twoSet h2 hK hU hL hKF
  have hKH : K ≤ H := kSub_le 3 M H
  have hKHN : H ≤ N := hK 3 E H h.hypCGen
  have hJH : J ≤ H := inf_le_left.trans hKH
  have hTH : T ≤ H := hTHM.trans inf_le_left
  have hTM : T ≤ M := hTHM.trans inf_le_right
  have hYH : Y ≤ H := sup_le hJH hTH
  have hYN : Y ≤ N := hYH.trans hKHN
  have hJY : J ≤ Y := le_sup_left
  have hTY : T ≤ Y := le_sup_right
  have hYJ : Y ≤ Subgroup.normalizer (J : Set G) :=
    sup_le Subgroup.le_normalizer
      (le_normalizer_inf_of_le_of_normalizer (K := K) (M := M) hTH hTM hKHN)
  let ψ : ↥Y →* Equiv.Perm (Fin 11) := (actPerm e).comp (Subgroup.inclusion hYN)
  have hψdata := range_actPerm_le_centralizer e hij hI rfl hJY hYJ hYN
  have hle : ψ.range ≤
      Subgroup.centralizer ({Equiv.swap i j} : Set (Equiv.Perm (Fin 11))) := by
    simpa [ψ] using hψdata.1
  have hge : (a11TwoSetStab i j).map (alternatingGroup (Fin 11)).subtype ≤ ψ.range := by
    simpa [ψ] using hψdata.2
  obtain ⟨φ, hφsurj, hφ1⟩ := exists_twoSetFold hij ψ hle hge
  have hφ1' : ∀ y, φ y = 1 ↔
      (actPerm e (Subgroup.inclusion hYN y) = 1 ∨
        actPerm e (Subgroup.inclusion hYN y) = Equiv.swap i j) := by
    intro y
    simpa [ψ] using hφ1 y
  have hRker : R.subgroupOf Y ≤ φ.ker :=
    le_ker_fold_of_maxInvariant e hij hI rfl hR (hRT.trans hTY) hYN (hR.1.trans hKHN) hφ1'
  have hTJ : T ≤ Subgroup.normalizer (J : Set G) := hTY.trans hYJ
  have hJeq : CFSG.Quasithin.twoResidual Y = CFSG.Quasithin.twoResidual J := by
    simpa [Y] using twoResidual_sup_of_isPGroup_two (J := J) (T := T) hT hTJ
  have hO2K : CFSG.Open.pCoreOf 2 K = (CFSG.pPrimeCore 3 ↥K).map K.subtype := by
    simpa [K] using h.pCoreOf_two_kSub_eq_caseTwo h2
  have hZ2 : IsPGroup 2 ((φ.ker).map Y.subtype) :=
    isPGroup_map_ker_fold hJY inf_le_left hYN hJeq hO2K e hφ1'
  have hZleH : (φ.ker).map Y.subtype ≤ H := (Subgroup.map_subtype_le _).trans hYH
  have hYZ := le_normalizer_map_ker (φ := φ)
  have hJZ : J ≤ Subgroup.normalizer (((φ.ker).map Y.subtype) : Set G) := hJY.trans hYZ
  have hRZ : R ≤ (φ.ker).map Y.subtype := fun r hr =>
    Subgroup.mem_map.mpr ⟨⟨r, hTY (hRT hr)⟩,
      hRker (Subgroup.mem_subgroupOf.mpr hr), rfl⟩
  have hZeq : (φ.ker).map Y.subtype = R := hR.2.2.2 _ hZleH hZ2 hJZ hRZ
  refine ⟨i, j, φ, hij, hφsurj, ?_⟩
  refine le_antisymm ?_ hRker
  intro y hy
  exact Subgroup.mem_subgroupOf.mpr (hZeq ▸ Subgroup.mem_map_of_mem Y.subtype hy)

private theorem ker_le_ker_of_not_three_dvd {Y X : Type} [Group Y] [Finite Y] [Group X]
    {i j : Fin 11} (hij : i ≠ j) {φ : Y →* ↥(a11TwoSetStab i j)}
    (hφ : Function.Surjective φ) {π : Y →* X} (hπ : ¬ 3 ∣ Nat.card π.ker) :
    π.ker ≤ φ.ker := by
  classical
  let D : Subgroup (alternatingGroup (Fin 11)) :=
    (π.ker.map φ).map (a11TwoSetStab i j).subtype
  have hD3 : ¬ 3 ∣ Nat.card D := by
    intro h3
    apply hπ
    have hcard : Nat.card D = Nat.card (π.ker.map φ) :=
      Subgroup.card_map_of_injective (K := π.ker.map φ)
        (a11TwoSetStab i j).subtype_injective
    rw [hcard] at h3
    exact h3.trans (Subgroup.card_map_dvd π.ker φ)
  have hDS : D ≤ a11TwoSetStab i j := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hDnorm : (π.ker.map φ).Normal := (MonoidHom.normal_ker π).map φ hφ
  have hN : ⁅a11TwoSetStab i j, a11TwoSetStab i j⁆ ≤
      Subgroup.normalizer (D : Set (alternatingGroup (Fin 11))) := by
    have htop : (⊤ : Subgroup ↥(a11TwoSetStab i j)) ≤
        Subgroup.normalizer ((π.ker.map φ) : Set ↥(a11TwoSetStab i j)) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hDnorm]
    have hmap := Subgroup.map_mono (f := (a11TwoSetStab i j).subtype) htop
    have htopmap : (⊤ : Subgroup ↥(a11TwoSetStab i j)).map
        (a11TwoSetStab i j).subtype = a11TwoSetStab i j := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    rw [htopmap] at hmap
    refine (show ⁅a11TwoSetStab i j, a11TwoSetStab i j⁆ ≤ a11TwoSetStab i j from
      ?_).trans (hmap.trans (Subgroup.le_normalizer_map (a11TwoSetStab i j).subtype))
    simpa using Subgroup.commutator_le_sup (a11TwoSetStab i j) (a11TwoSetStab i j)
  have hDbot : D = ⊥ := a11TwoSetStab_threePrime_eq_bot hij hD3 hDS hN
  have hmapbot : π.ker.map φ = ⊥ := by
    apply Subgroup.map_injective (a11TwoSetStab i j).subtype_injective
    rw [Subgroup.map_bot]
    exact hDbot
  intro x hx
  have hxmap : φ x ∈ π.ker.map φ := Subgroup.mem_map_of_mem φ hx
  rw [hmapbot] at hxmap
  exact Subgroup.mem_bot.mp hxmap

private theorem map_ker_le_pCoreOf {Y X : Type} [Group Y] [Finite Y] [Group X]
    {i j : Fin 11} {φ : Y →* ↥(a11TwoSetStab i j)} (hφ : Function.Surjective φ)
    (hker : IsPGroup 2 φ.ker) (π : Y →* X) :
    φ.ker.map π ≤ CFSG.Open.pCoreOf 2 π.range := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf 2 (Subgroup.map_le_range π φ.ker) ?_ (hker.map π)
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_le_range π φ.ker)).mpr ?_
  have htop : (⊤ : Subgroup Y) ≤ Subgroup.normalizer (φ.ker : Set Y) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr (MonoidHom.normal_ker φ)]
  have h := Subgroup.map_mono (f := π) htop
  have hrange : (⊤ : Subgroup Y).map π = π.range := (MonoidHom.range_eq_map π).symm
  rw [hrange] at h
  exact h.trans (Subgroup.le_normalizer_map π)

private theorem isPGroup_map_comap_pCore {Y X : Type} [Group Y] [Finite Y] [Group X]
    {i j : Fin 11} {φ : Y →* ↥(a11TwoSetStab i j)} {π : Y →* X}
    (hle : π.ker ≤ φ.ker) :
    IsPGroup 2 (((CFSG.pCore 2 ↥π.range).comap π.rangeRestrict).map φ) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isPGroup_iff_pow_pow_eq_one]
  intro z
  obtain ⟨y, hy, hzy⟩ := Subgroup.mem_map.mp z.2
  obtain ⟨k, hk⟩ := (isPGroup_iff_pow_pow_eq_one.mp
    (CFSG.pCore_isPGroup (p := 2) (G := ↥π.range))) ⟨π.rangeRestrict y, hy⟩
  have hk' : (π y) ^ 2 ^ k = 1 := by
    have h3 : (π.rangeRestrict y) ^ 2 ^ k = 1 := by
      have h := congrArg (fun z : ↥(CFSG.pCore 2 ↥π.range) => (z : ↥π.range)) hk
      simpa using h
    have h4 := congrArg (fun z : ↥π.range => (z : X)) h3
    simpa using h4
  have hmemker : y ^ 2 ^ k ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    simpa using hk'
  have hφy : φ (y ^ 2 ^ k) = 1 := hle hmemker
  refine ⟨k, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, ← hzy]
  simpa [map_pow] using hφy

private theorem map_comap_pCore_eq_bot {Y X : Type} [Group Y] [Finite Y] [Group X]
    {i j : Fin 11} (hij : i ≠ j) {φ : Y →* ↥(a11TwoSetStab i j)}
    (hφ : Function.Surjective φ) {π : Y →* X} (hle : π.ker ≤ φ.ker) :
    ((CFSG.pCore 2 ↥π.range).comap π.rangeRestrict).map φ = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup Y := (CFSG.pCore 2 ↥π.range).comap π.rangeRestrict
  have hNnormal : N.Normal :=
    (CFSG.pCore_normal (p := 2) (G := ↥π.range)).comap π.rangeRestrict
  have hN2 : IsPGroup 2 (N.map φ) := isPGroup_map_comap_pCore hle
  let D : Subgroup (alternatingGroup (Fin 11)) :=
    (N.map φ).map (a11TwoSetStab i j).subtype
  have hD2 : IsPGroup 2 D := hN2.map (a11TwoSetStab i j).subtype
  have hDnorm : (N.map φ).Normal := hNnormal.map φ hφ
  have hN' : ⁅a11TwoSetStab i j, a11TwoSetStab i j⁆ ≤
      Subgroup.normalizer (D : Set (alternatingGroup (Fin 11))) := by
    have htop : (⊤ : Subgroup ↥(a11TwoSetStab i j)) ≤
        Subgroup.normalizer ((N.map φ) : Set ↥(a11TwoSetStab i j)) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hDnorm]
    have hmap := Subgroup.map_mono (f := (a11TwoSetStab i j).subtype) htop
    have htopmap : (⊤ : Subgroup ↥(a11TwoSetStab i j)).map
        (a11TwoSetStab i j).subtype = a11TwoSetStab i j := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    rw [htopmap] at hmap
    refine (show ⁅a11TwoSetStab i j, a11TwoSetStab i j⁆ ≤ a11TwoSetStab i j from
      ?_).trans (hmap.trans (Subgroup.le_normalizer_map (a11TwoSetStab i j).subtype))
    simpa using Subgroup.commutator_le_sup (a11TwoSetStab i j) (a11TwoSetStab i j)
  have hDbot : D = ⊥ := a11TwoSetStab_twoSubgroup_eq_bot hij hD2 hN'
  have hNbot : N.map φ = ⊥ := by
    apply Subgroup.map_injective (a11TwoSetStab i j).subtype_injective
    rw [Subgroup.map_bot]
    exact hDbot
  simpa [N] using hNbot

private theorem pCoreOf_le_map_ker {Y X : Type} [Group Y] [Finite Y] [Group X]
    {i j : Fin 11} (hij : i ≠ j) {φ : Y →* ↥(a11TwoSetStab i j)}
    (hφ : Function.Surjective φ) {π : Y →* X} (hle : π.ker ≤ φ.ker) :
    CFSG.Open.pCoreOf 2 π.range ≤ φ.ker.map π := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let πr : Y →* ↥π.range := π.rangeRestrict
  let N : Subgroup Y := (CFSG.pCore 2 ↥π.range).comap πr
  have hNbot : N.map φ = ⊥ := by
    simpa [N, πr] using map_comap_pCore_eq_bot hij hφ hle
  have hNleker : N ≤ φ.ker := by
    intro y hy
    have hyφ : φ y ∈ N.map φ := Subgroup.mem_map_of_mem φ hy
    rw [hNbot] at hyφ
    exact Subgroup.mem_bot.mp hyφ
  intro x hx
  have hxrange : x ∈ π.range := CFSG.openPCoreOf_le 2 π.range hx
  rw [MonoidHom.range_eq_map] at hxrange
  obtain ⟨y, -, hxy⟩ := Subgroup.mem_map.mp hxrange
  have hycore : πr y ∈ CFSG.pCore 2 ↥π.range := by
    rw [← CFSG.openPCoreOf_subgroupOf 2 π.range]
    refine Subgroup.mem_subgroupOf.mpr ?_
    show (πr y : X) ∈ CFSG.Open.pCoreOf 2 π.range
    simpa [πr, hxy] using hx
  have hyN : y ∈ N := Subgroup.mem_comap.mpr hycore
  exact Subgroup.mem_map.mpr ⟨y, hNleker hyN, hxy⟩

theorem exists_quotient_pCore_two_mulEquiv_perm_nine {Y X : Type} [Group Y] [Finite Y]
    [Group X] {i j : Fin 11} (hij : i ≠ j) (φ : Y →* ↥(a11TwoSetStab i j))
    (hφ : Function.Surjective φ) (hker : IsPGroup 2 φ.ker) (π : Y →* X)
    (hπ : ¬ 3 ∣ Nat.card π.ker) :
    π.ker ≤ φ.ker ∧ CFSG.Open.pCoreOf 2 π.range = φ.ker.map π ∧
      Nonempty (↥π.range ⧸ CFSG.pCore 2 ↥π.range ≃* Equiv.Perm (Fin 9)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : π.ker ≤ φ.ker := ker_le_ker_of_not_three_dvd hij hφ hπ
  have hmap_le : φ.ker.map π ≤ CFSG.Open.pCoreOf 2 π.range :=
    map_ker_le_pCoreOf hφ hker π
  have hcore_le : CFSG.Open.pCoreOf 2 π.range ≤ φ.ker.map π :=
    pCoreOf_le_map_ker hij hφ hle
  have hO2 : CFSG.Open.pCoreOf 2 π.range = φ.ker.map π := le_antisymm hcore_le hmap_le
  let πr : Y →* ↥π.range := π.rangeRestrict
  have hπrsurj : Function.Surjective πr := π.rangeRestrict_surjective
  have hπrker : πr.ker = π.ker := MonoidHom.ker_rangeRestrict π
  have hle' : πr.ker ≤ φ.ker := by rw [hπrker]; exact hle
  let f : ↥π.range →* ↥(a11TwoSetStab i j) :=
    MonoidHom.liftOfRightInverse πr (Function.surjInv hπrsurj)
      (Function.rightInverse_surjInv hπrsurj) ⟨φ, hle'⟩
  have hf_apply : ∀ y : Y, f (πr y) = φ y := fun y =>
    MonoidHom.liftOfRightInverse_comp_apply πr (Function.surjInv hπrsurj)
      (Function.rightInverse_surjInv hπrsurj) ⟨φ, hle'⟩ y
  have hfker : f.ker = (CFSG.Open.pCoreOf 2 π.range).subgroupOf π.range := by
    rw [hO2]
    refine le_antisymm ?_ ?_
    · intro z hz
      obtain ⟨y, rfl⟩ := hπrsurj z
      have hφy : φ y = 1 := by
        rw [← hf_apply y]
        exact hz
      refine Subgroup.mem_subgroupOf.mpr ?_
      simpa [πr] using Subgroup.mem_map_of_mem π (show y ∈ φ.ker from hφy)
    · intro z hz
      have hzmap : (z : X) ∈ φ.ker.map π := Subgroup.mem_subgroupOf.mp hz
      obtain ⟨y, hy, hzy⟩ := Subgroup.mem_map.mp hzmap
      have hzy' : z = πr y := Subtype.ext hzy.symm
      rw [hzy', MonoidHom.mem_ker, hf_apply y]
      exact hy
  have hfkercore : f.ker = CFSG.pCore 2 ↥π.range :=
    hfker.trans (CFSG.openPCoreOf_subgroupOf 2 π.range)
  have hf : Function.Surjective f := by
    intro s
    obtain ⟨y, hy⟩ := hφ s
    exact ⟨πr y, by rw [hf_apply y, hy]⟩
  obtain ⟨e9⟩ := nonempty_a11TwoSetStab_mulEquiv hij
  exact ⟨hle, hO2, ⟨(QuotientGroup.quotientMulEquivOfEq hfkercore.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective f hf).trans e9)⟩⟩

private theorem not_three_dvd_card_ker_mk'_comp {M Y : Subgroup G} (hYM : Y ≤ M)
    {O : Subgroup ↥M} [O.Normal] (hO3 : ¬ 3 ∣ Nat.card O) :
    ¬ 3 ∣ Nat.card ((QuotientGroup.mk' O).comp (Subgroup.inclusion hYM)).ker := by
  have hker_map : (((QuotientGroup.mk' O).comp (Subgroup.inclusion hYM)).ker).map
      (Subgroup.inclusion hYM) = O ⊓ Y.subgroupOf M := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, ?_⟩
      · have hy1 : QuotientGroup.mk (s := O) (Subgroup.inclusion hYM y : ↥M) = 1 := by
          simpa [MonoidHom.comp_apply, QuotientGroup.mk'_apply] using hy
        exact (QuotientGroup.eq_one_iff (N := O)
          (Subgroup.inclusion hYM y)).mp hy1
      · exact Subgroup.mem_subgroupOf.mpr y.2
    · rintro ⟨hxO, hxY⟩
      refine ⟨⟨(x : M), Subgroup.mem_subgroupOf.mp hxY⟩, ?_, rfl⟩
      have hq : QuotientGroup.mk (s := O) (x : ↥M) = 1 :=
        (QuotientGroup.eq_one_iff (N := O) (x : ↥M)).mpr hxO
      simpa [MonoidHom.comp_apply, Subgroup.inclusion, QuotientGroup.mk'_apply] using hq
  have hcard : Nat.card ((QuotientGroup.mk' O).comp (Subgroup.inclusion hYM)).ker =
      Nat.card ↥(O ⊓ Y.subgroupOf M) := by
    rw [← hker_map]
    exact (Subgroup.card_map_of_injective (Subgroup.inclusion_injective hYM)).symm
  have hdvd : Nat.card ((QuotientGroup.mk' O).comp (Subgroup.inclusion hYM)).ker ∣
      Nat.card O := by
    rw [hcard]
    exact Subgroup.card_dvd_of_le inf_le_left
  exact fun h3 => hO3 (h3.trans hdvd)

private theorem twoResidual_range_mk'_comp {M Y : Subgroup G} (hYM : Y ≤ M) :
    CFSG.Quasithin.twoResidual
        (((QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)).comp (Subgroup.inclusion hYM)).range) =
      ((CFSG.Quasithin.twoResidual Y).subgroupOf M).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)) := by
  haveI : (CFSG.pPrimeCore 3 ↥M).Normal := CFSG.pPrimeCore_normal
  let π : ↥M →* (↥M ⧸ CFSG.pPrimeCore 3 ↥M) := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)
  let πY : ↥Y →* (↥M ⧸ CFSG.pPrimeCore 3 ↥M) := π.comp (Subgroup.inclusion hYM)
  have h1 := CFSG.Quasithin.E1.map_twoResidual πY (⊤ : Subgroup ↥Y)
  have htop : (⊤ : Subgroup ↥Y).map πY = πY.range :=
    (MonoidHom.range_eq_map πY).symm
  rw [htop] at h1
  rw [← h1]
  have h3 : CFSG.Quasithin.twoResidual (⊤ : Subgroup ↥Y) =
      (CFSG.Quasithin.twoResidual Y).subgroupOf Y := by
    calc CFSG.Quasithin.twoResidual (⊤ : Subgroup ↥Y)
        = (((CFSG.Quasithin.twoResidual (⊤ : Subgroup ↥Y)).map Y.subtype).subgroupOf Y) := by
          rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective Y.subtype_injective]
      _ = (CFSG.Quasithin.twoResidual Y).subgroupOf Y := by
          rw [CFSG.Quasithin.E1.twoResidual_eq_map_top Y]
  rw [h3]
  rw [show πY = π.comp (Subgroup.inclusion hYM) from rfl, ← Subgroup.map_map,
    CFSG.AGLEmbedding.map_inclusion_subgroupOf (CFSG.Quasithin.twoResidual_le Y) hYM]

private theorem isSylowOf_map_mk'_of_sylow {M T : Subgroup G} (O : Subgroup ↥M) [O.Normal]
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    CFSG.ABGLocalTools.IsSylowOf 2 ((T.subgroupOf M).map (QuotientGroup.mk' O)) ⊤ := by
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 (T.subgroupOf M) ⊤ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff M]
    simpa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hT.le,
      Subgroup.map_top, Subgroup.range_subtype] using hT
  have h1 : CFSG.RankThree.PartOne.IsSylowOf 2 (T.subgroupOf M) ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_iff.mp hTsyl
  have h2 : CFSG.RankThree.PartOne.IsSylowOf 2
      ((T.subgroupOf M).map (QuotientGroup.mk' O)) ⊤ :=
    CFSG.RankThree.PartOne.Sec1511.isSylowOf_map_mk' (p := 2) (O := O) h1
  exact CFSG.ABGLocalTools.isSylowOf_iff.mpr h2

private theorem image_normalizer_le_normalizer_twoResidual {M H Y : Subgroup G}
    (O : Subgroup ↥M) [O.Normal] (π : ↥M →* (↥M ⧸ O))
    (Hs : Subgroup (↥M ⧸ O)) (hYM : Y ≤ M)
    (hHM : H ⊓ M ≤ Subgroup.normalizer (CFSG.Quasithin.twoResidual Y : Set G))
    (htwoResHs : CFSG.Quasithin.twoResidual Hs =
      ((CFSG.Quasithin.twoResidual Y).subgroupOf M).map π) :
    ((H ⊓ M).subgroupOf M).map π ≤
      Subgroup.normalizer (CFSG.Quasithin.twoResidual Hs : Set (↥M ⧸ O)) := by
  have hHMnorms : (H ⊓ M).subgroupOf M ≤
      Subgroup.normalizer (((CFSG.Quasithin.twoResidual Y).subgroupOf M) : Set ↥M) := by
    rw [← Subgroup.subgroupOf_normalizer_eq ((CFSG.Quasithin.twoResidual_le Y).trans hYM)]
    exact Subgroup.subgroupOf_mono M hHM
  have hmap := Subgroup.map_mono (f := π) hHMnorms
  have h := hmap.trans (Subgroup.le_normalizer_map π)
  rwa [← htwoResHs] at h

private theorem exists_maxInvariantTwoIn_sylow {M H E Q : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (hA : ¬ TypeA M H) (h2 : CaseTwo M H)
    (hpre : PreambleTypes M) (hK : KNormalAt M) (hU : NineNineOneAt M) (hL : PLayerNotLeAt M)
    (hKF : KFactA11GammaTwoSet) (h514 : FiveFourteenA11Use)
    (h525 : FiveTwentyFiveS11Use) (hX : CFSG.AGLEmbeddingD2.NoXBlockFor G) :
    ∃ R T : Subgroup G,
      IsMaxInvariantTwoIn (kSub 3 M H ⊓ M) R H ∧
      Subgroup.normalizer (R : Set G) ≤ H ∧ R ≤ M ∧
      CFSG.ABGLocalTools.IsSylowOf 2 T (H ⊓ M) ∧ R ≤ T ∧
      CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K : Subgroup G := kSub 3 M H
  let J : Subgroup G := K ⊓ M
  obtain ⟨R, -, hR⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6.exists_isMaxInvariantTwoIn_ge
      (B := J) (S₀ := ⊥) (Y := H) bot_le (IsPGroup.of_bot (p := 2))
      (by
        rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (⊥ : Subgroup G).Normal)]
        exact le_top)
  obtain ⟨hNRH, hRMmax⟩ := h.normalizer_R_le hA h2 hpre hK hU hL hKF h525 hX hR
  have hRM : R ≤ M := hRMmax.1
  obtain ⟨T, hTHMsyl, hRT⟩ :=
    CFSG.RankThree.PartOne.exists_isSylowOf_ge (K := H ⊓ M) (Q := R)
      (le_inf hR.1 hRM) hR.2.1
  have hTtop := h.isSylowOf_two_top hA h2 hpre hK hU hL hKF h514 hX hTHMsyl
  exact ⟨R, T, hR, hNRH, hRM, hTHMsyl, hRT, hTtop⟩

private theorem exists_quotient_data {M H E Q R T : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (h2 : CaseTwo M H) (hK : KNormalAt M)
    (hU : NineNineOneAt M) (hL : PLayerNotLeAt M) (hKF : KFactA11GammaTwoSet)
    (hR : IsMaxInvariantTwoIn (kSub 3 M H ⊓ M) R H) (hT : IsPGroup 2 T)
    (hTHM : T ≤ H ⊓ M) (hRT : R ≤ T)
    (hTtop : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) :
    ∃ Hs T' : Subgroup (↥M ⧸ CFSG.pPrimeCore 3 ↥M),
      CFSG.ABGLocalTools.IsSylowOf 2 T' ⊤ ∧ T' ≤ Hs ∧
      Nonempty (↥Hs ⧸ CFSG.pCore 2 ↥Hs ≃* Equiv.Perm (Fin 9)) ∧
      CFSG.Open.pCoreOf 2 Hs =
        (R.subgroupOf M).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)) ∧
      CFSG.Quasithin.twoResidual Hs =
        ((CFSG.Quasithin.twoResidual ((kSub 3 M H ⊓ M) ⊔ T)).subgroupOf M).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (CFSG.pPrimeCore 3 ↥M).Normal := CFSG.pPrimeCore_normal
  let K : Subgroup G := kSub 3 M H
  let J : Subgroup G := K ⊓ M
  let Y : Subgroup G := J ⊔ T
  let O : Subgroup ↥M := CFSG.pPrimeCore 3 ↥M
  let π : ↥M →* (↥M ⧸ O) := QuotientGroup.mk' O
  have hJH : J ≤ H := inf_le_left.trans (kSub_le 3 M H)
  have hTH : T ≤ H := hTHM.trans inf_le_left
  have hTM : T ≤ M := hTHM.trans inf_le_right
  have hYH : Y ≤ H := sup_le hJH hTH
  have hYM : Y ≤ M := sup_le inf_le_right hTM
  obtain ⟨i, j, φ, hij, hφsurj, hφker⟩ :=
    h.exists_twoSetFold_ker_eq h2 hK hU hL hKF hR hT hTHM hRT
  let πY : ↥Y →* (↥M ⧸ O) := π.comp (Subgroup.inclusion hYM)
  let Hs : Subgroup (↥M ⧸ O) := πY.range
  let T' : Subgroup (↥M ⧸ O) := (T.subgroupOf M).map π
  have hO3 : ¬ 3 ∣ Nat.card O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hπYker3 : ¬ 3 ∣ Nat.card πY.ker := by
    simpa [πY, O, π] using not_three_dvd_card_ker_mk'_comp (O := O) hYM hO3
  have hφ2 : IsPGroup 2 φ.ker := hφker ▸ hR.2.1.comap_subtype
  obtain ⟨-, hO2eq, ⟨e9⟩⟩ :=
    exists_quotient_pCore_two_mulEquiv_perm_nine hij φ hφsurj hφ2 πY hπYker3
  have hT'syl : CFSG.ABGLocalTools.IsSylowOf 2 T' ⊤ :=
    isSylowOf_map_mk'_of_sylow O (hTtop.of_le hTM le_top)
  have hT'leHs : T' ≤ Hs := by
    rintro x ⟨t, ht, rfl⟩
    exact MonoidHom.mem_range.mpr
      ⟨⟨(t : G), Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp ht)⟩, rfl⟩
  have hO2Hs : CFSG.Open.pCoreOf 2 Hs =
      (R.subgroupOf M).map π := by
    change CFSG.Open.pCoreOf 2 πY.range = (R.subgroupOf M).map π
    rw [hO2eq, hφker]
    change (R.subgroupOf Y).map πY = (R.subgroupOf M).map π
    rw [show πY = π.comp (Subgroup.inclusion hYM) from rfl, ← Subgroup.map_map,
      CFSG.AGLEmbedding.map_inclusion_subgroupOf (hRT.trans le_sup_right) hYM]
  have htwoResHs : CFSG.Quasithin.twoResidual Hs =
      ((CFSG.Quasithin.twoResidual Y).subgroupOf M).map π := by
    simpa [Hs, πY, π] using twoResidual_range_mk'_comp (M := M) (Y := Y) hYM
  exact ⟨Hs, T', hT'syl, hT'leHs, ⟨e9⟩, hO2Hs, htwoResHs⟩

theorem S14Choice.exists_sevenThreeData {M H E Q : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (hA : ¬ TypeA M H) (h2 : CaseTwo M H)
    (hpre : PreambleTypes M) (hK : KNormalAt M) (hU : NineNineOneAt M) (hL : PLayerNotLeAt M)
    (hKF : KFactA11GammaTwoSet) (h514 : FiveFourteenA11Use) (h525 : FiveTwentyFiveS11Use)
    (hX : CFSG.AGLEmbeddingD2.NoXBlockFor G) :
    ∃ T Hs : Subgroup (↥M ⧸ CFSG.pPrimeCore 3 ↥M),
      CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ ∧ T ≤ Hs ∧
      Nonempty (↥Hs ⧸ CFSG.pCore 2 ↥Hs ≃* Equiv.Perm (Fin 9)) ∧
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 Hs : Set (↥M ⧸ CFSG.pPrimeCore 3 ↥M)) ≤
        Subgroup.normalizer (CFSG.Quasithin.twoResidual Hs :
          Set (↥M ⧸ CFSG.pPrimeCore 3 ↥M)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (CFSG.pPrimeCore 3 ↥M).Normal := CFSG.pPrimeCore_normal
  let K : Subgroup G := kSub 3 M H
  let J : Subgroup G := K ⊓ M
  let O : Subgroup ↥M := CFSG.pPrimeCore 3 ↥M
  let π : ↥M →* (↥M ⧸ O) := QuotientGroup.mk' O
  obtain ⟨R, T, hR, hNRH, hRM, hTHMsyl, hRT, hTtop⟩ :=
    exists_maxInvariantTwoIn_sylow h hA h2 hpre hK hU hL hKF h514 h525 hX
  obtain ⟨Hs, T', hT'syl, hT'leHs, e9, hO2Hs, htwoResHs⟩ :=
    exists_quotient_data h h2 hK hU hL hKF hR hTHMsyl.isPGroup hTHMsyl.le hRT hTtop
  have hTH : T ≤ H := hTHMsyl.le.trans inf_le_left
  have hTM : T ≤ M := hTHMsyl.le.trans inf_le_right
  have hTJ : T ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_inf_of_le_of_normalizer (K := K) (M := M) hTH hTM
      (hK 3 E H h.hypCGen)
  have hYres : CFSG.Quasithin.twoResidual (J ⊔ T) = CFSG.Quasithin.twoResidual J := by
    simpa [J] using twoResidual_sup_of_isPGroup_two (J := J) (T := T) hTHMsyl.isPGroup hTJ
  have hYM : J ⊔ T ≤ M := sup_le inf_le_right hTM
  have hJNormHM : H ⊓ M ≤ Subgroup.normalizer (J : Set G) := by
    intro x hx
    have hxK : x ∈ Subgroup.normalizer (K : Set G) := (hK 3 E H h.hypCGen) hx.1
    have hxM : x ∈ Subgroup.normalizer (M : Set G) := Subgroup.le_normalizer hx.2
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hxK, hxM⟩
  have hHMnormY : H ⊓ M ≤
      Subgroup.normalizer (CFSG.Quasithin.twoResidual (J ⊔ T) : Set G) := by
    have h := hJNormHM.trans (CFSG.Quasithin.C126.A5.normalizer_le_normalizer_twoResidual J)
    rwa [← hYres] at h
  have hNRle : Subgroup.normalizer (((R.subgroupOf M).map π :
      Subgroup (↥M ⧸ O)) : Set (↥M ⧸ O)) ≤ ((H ⊓ M).subgroupOf M).map π := by
    simpa [π, O] using h.normalizer_map_R_le hA h2 hpre hK hU hL hKF h525 hX hR
  have hHbarNorm := image_normalizer_le_normalizer_twoResidual O π Hs hYM hHMnormY htwoResHs
  refine ⟨T', Hs, hT'syl, hT'leHs, e9, ?_⟩
  intro x hx
  rw [hO2Hs] at hx
  exact hHbarNorm (hNRle hx)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14

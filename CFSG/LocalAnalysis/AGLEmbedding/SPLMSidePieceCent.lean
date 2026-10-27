module

public import CFSG.LocalAnalysis.AGLEmbedding.SPLMSidePieces
import CFSG.LocalAnalysis.AGLEmbedding.SPLMSidePieceCentAux
import CFSG.LocalAnalysis.AGLEmbedding.SPLMSideOrbit
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroPerf
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem D1SPLPairData.czCore_le (D : D1SPLPairData p P M H R Rbar K z) :
    GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≤ M :=
  intersecting_local_primeCore_le p D.data.cfg.red.prime P D.data.cfg.ext.sylow_le
    D.data.cfg.ext.weakCore_le (D.data.cfg.ext.three_le_pRank.trans
      (pRank_mono p D.data.cfg.red.prime
        (le_inf (D.data.le_centralizer_czElt D.czElt) D.data.cfg.ext.le_M)))

theorem D1SPLPairData.odd_card_czCore (D : D1SPLPairData p P M H R Rbar K z) :
    Odd (Nat.card (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)))) := by
  obtain ⟨-, -, -, -, hodd⟩ := D.data.odd_card_primeCore_cz D.czElt D.sp
  exact hodd

theorem D1SPLPairData.splBar_pow_eq_one (D : D1SPLPairData p P M H R Rbar K z) (hzM : z ∈ M) :
    splBar hzM ^ p = 1 := by
  have hzp : z ^ p = 1 := by
    rw [← D.czElt.2.1]
    exact pow_orderOf_eq_one z
  have h : (⟨z, hzM⟩ : M) ^ p = 1 := Subtype.ext (by simp [hzp])
  unfold splBar
  rw [← map_pow, h, map_one]

theorem D1SPLPairData.exists_lift_of_mem_centralizer (D : D1SPLPairData p P M H R Rbar K z)
    (hzM : z ∈ M) {g : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hg : g ∈ Subgroup.centralizer ({splBar hzM} : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    ∃ m : M, (m : G) ∈ Subgroup.centralizer ({z} : Set G) ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) m = g := by
  have hp := D.data.cfg.red.prime
  have hp2 := D.data.cfg.red.ne_two
  have hzMp : orderOf (⟨z, hzM⟩ : M) = p := by
    rw [← Subgroup.orderOf_coe]
    exact D.czElt.2.1
  have hcop : p.Coprime (Nat.card (CFSG.pCore 2 ↥M)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
    rw [hk]
    exact ((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow_right k
  have : (CFSG.pCore 2 ↥M).Normal := CFSG.pCore_normal
  obtain ⟨m, hm, hmg⟩ := exists_mem_centralizer_mk_eq (e := ⟨z, hzM⟩) hp _ hcop
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzMp, pow_one])) hg
  exact ⟨m, Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hm)), hmg⟩

theorem D1SPLPairData.le_czCore_of_normal (D : D1SPLPairData p P M H R Rbar K z)
    {P' : Sylow p G} {Pbar : Sylow p (D1CzQuot p z)} {KC : Subgroup (D1CzQuot p z)}
    (hRC : D1ReducedCentralizer p P' M z Pbar KC) (hP'M : (P' : Subgroup G) ≤ M)
    (hCt : SPLCtildeFacts p M z Pbar KC) {N : Subgroup G}
    (hNle : N ≤ Subgroup.centralizer ({z} : Set G) ⊓ M)
    (hNn : ∀ g ∈ Subgroup.centralizer ({z} : Set G) ⊓ M, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hNp : p.Coprime (Nat.card N)) :
    N ≤ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) := by
  have : Fact p.Prime := ⟨D.data.cfg.red.prime⟩
  set C := Subgroup.centralizer ({z} : Set G)
  set π := QuotientGroup.mk' (primeComplementCore (G := C) p)
  have hord : ∀ n ∈ N, p.Coprime (orderOf n) := fun n hn =>
    Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard N hn) hNp
  intro x hx
  have hxC : x ∈ C := (hNle hx).1
  have hxX : π ⟨x, hxC⟩ ∈ splXt0 p M z := ⟨⟨x, hxC⟩, hNle hx, rfl⟩
  have hcomm : ∀ t ∈ (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC,
      π ⟨x, hxC⟩ * t = t * π ⟨x, hxC⟩ := by
    intro t ht
    have htP : t ∈ (Pbar : Subgroup (D1CzQuot p z)) := ht.1
    rw [hRC.sylow_eq] at htP
    obtain ⟨y, hy, rfl⟩ := htP
    have hyCM : (y : G) ∈ C ⊓ M := ⟨y.2, hP'M hy⟩
    have hc : x * ((y : G) * x⁻¹ * (y : G)⁻¹) ∈ N := N.mul_mem hx (hNn _ hyCM _ (N.inv_mem hx))
    have hT : π ⟨x, hxC⟩ * π y * (π ⟨x, hxC⟩)⁻¹ * (π y)⁻¹ ∈
        (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC :=
      Subgroup.mul_mem _ (hCt.norm _ hxX _ ht) (Subgroup.inv_mem _ ht)
    obtain ⟨k, hk⟩ := (Pbar.isPGroup'.to_le inf_le_left) ⟨_, hT⟩
    have e : π ⟨x, hxC⟩ * π y * (π ⟨x, hxC⟩)⁻¹ * (π y)⁻¹ =
        π ⟨x * ((y : G) * x⁻¹ * (y : G)⁻¹), C.mul_mem hxC (C.mul_mem (C.mul_mem y.2
          (C.inv_mem hxC)) (C.inv_mem y.2))⟩ := by
      simp only [← map_inv, ← map_mul]
      congr 1
      exact Subtype.ext (by simp [mul_assoc])
    have hcop : p.Coprime (orderOf (π ⟨x, hxC⟩ * π y * (π ⟨x, hxC⟩)⁻¹ * (π y)⁻¹)) := by
      rw [e]
      exact Nat.Coprime.coprime_dvd_right (orderOf_map_dvd π _)
        (by rw [Subgroup.orderOf_mk]; exact hord _ hc)
    have h1 := SPLMSide.eq_one_of_pow_of_coprime
      (by simpa using congrArg Subtype.val hk) hcop
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  obtain ⟨k, hk⟩ := hCt.cent_p _ hxX hcomm
  have hcop : p.Coprime (orderOf (π ⟨x, hxC⟩)) :=
    Nat.Coprime.coprime_dvd_right (orderOf_map_dvd π _)
      (by rw [Subgroup.orderOf_mk]; exact hord x hx)
  have h1 := SPLMSide.eq_one_of_pow_of_coprime hk hcop
  have hker : (⟨x, hxC⟩ : C) ∈ primeComplementCore (G := C) p := by
    rw [← QuotientGroup.ker_mk' (primeComplementCore (G := C) p), MonoidHom.mem_ker]
    exact h1
  exact (mem_primeComplementCore_iff_mem_glbPrimeCore p _).mp hker

theorem D1SPLPairData.twoCore_inf_centralizer_eq_bot (D : D1SPLPairData p P M H R Rbar K z)
    {P' : Sylow p G} {Pbar : Sylow p (D1CzQuot p z)} {KC : Subgroup (D1CzQuot p z)}
    (hRC : D1ReducedCentralizer p P' M z Pbar KC) (hP'M : (P' : Subgroup G) ≤ M)
    (hCt : SPLCtildeFacts p M z Pbar KC) :
    pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) = ⊥ := by
  have hp := D.data.cfg.red.prime
  have hp2 := D.data.cfg.red.ne_two
  set C := Subgroup.centralizer ({z} : Set G)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
    ((RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M).to_le
      (inf_le_left : pCoreOf 2 M ⊓ C ≤ pCoreOf 2 M))
  have hle : pCoreOf 2 M ⊓ C ≤ GLBPrimeCore p C := D.le_czCore_of_normal hRC hP'M hCt
    (fun x hx => ⟨hx.2, RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M hx.1⟩)
    (fun g hg n hn => ⟨(Subgroup.mem_normalizer_iff.mp
      (localGroup_le_normalizer_pCoreOf 2 M hg.2) n).mp hn.1,
        C.mul_mem (C.mul_mem hg.1 hn.2) (C.inv_mem hg.1)⟩)
    (by rw [hk]; exact ((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow_right k)
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hk] at hdvd
  have hk0 : k = 0 := by
    by_contra hk0
    exact (Nat.not_even_iff_odd.mpr D.odd_card_czCore)
      (even_iff_two_dvd.mpr ((dvd_pow_self 2 hk0).trans hdvd))
  exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, hk0, pow_zero])

theorem D1SPLPairData.centralizer_splBar_eq (D : D1SPLPairData p P M H R Rbar K z)
    (hzM : z ∈ M) :
    Subgroup.centralizer ({splBar hzM} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) =
      ((Subgroup.centralizer ({z} : Set G) ⊓ M).subgroupOf M).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨m, hmC, rfl⟩ := D.exists_lift_of_mem_centralizer hzM hg
    exact ⟨m, ⟨hmC, m.2⟩, rfl⟩
  · rintro _ ⟨m, hm, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    unfold splBar
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hm.1)

theorem D1SPLPairData.card_lt_of_elemAbelian (D : D1SPLPairData p P M H R Rbar K z)
    (hzM : z ∈ M) {Pbar : Sylow p (D1CzQuot p z)} {KC : Subgroup (D1CzQuot p z)}
    (hCt : SPLCtildeFacts p M z Pbar KC) {A : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hA : A ≤ Subgroup.centralizer ({splBar hzM} : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hAe : IsElemAbelian p A) : Nat.card A < p ^ 6 := by
  have hp := D.data.cfg.red.prime
  have hp2 := D.data.cfg.red.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have hAp : IsPGroup p A := fun g => ⟨1, Subtype.ext (by simpa using hAe.2 g g.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hAp
  have hkle : k ≤ Open.pRank p (Subgroup.centralizer ({splBar hzM} : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :=
    le_csSup (pRank_bddAbove p hp _) ⟨A, hA, hAe, hk⟩
  have hcop2 : p.Coprime (Nat.card (CFSG.pCore 2 ↥M)) := by
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
    rw [hj]
    exact ((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow_right j
  have : (CFSG.pCore 2 ↥M).Normal := CFSG.pCore_normal
  rw [D.centralizer_splBar_eq hzM, pRank_map_mk_eq_pRank_map_subtype hp _ hcop2,
    Subgroup.subgroupOf_map_subtype, inf_assoc, inf_idem] at hkle
  have hX : Open.pRank p (splXt0 p M z) =
      Open.pRank p (Subgroup.centralizer ({z} : Set G) ⊓ M) := by
    unfold splXt0
    rw [pRank_map_mk_eq_pRank_map_subtype hp _ (primeComplementCore_coprime p),
      Subgroup.subgroupOf_map_subtype, inf_right_comm, inf_idem]
  have h5 : Open.pRank p (splXt0 p M z) ≤ 5 := by
    obtain ⟨E, hE, hEe, hEc⟩ := pRank_attained p hp (splXt0 p M z)
    have h := hCt.rank E hE hEe
    rw [hEc] at h
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h
  rw [hk]
  exact Nat.pow_lt_pow_right hp.one_lt (by omega)

theorem D1SPLPairData.isSolvable_centralizer_inf (D : D1SPLPairData p P M H R Rbar K z)
    {Pbar : Sylow p (D1CzQuot p z)} {KC : Subgroup (D1CzQuot p z)}
    (hCt : SPLCtildeFacts p M z Pbar KC) :
    Group.IsSolvable ↥(Subgroup.centralizer ({z} : Set G) ⊓ M) := by
  set C := Subgroup.centralizer ({z} : Set G)
  let f : ↥(C ⊓ M) →* D1CzQuot p z :=
    (QuotientGroup.mk' (primeComplementCore (G := C) p)).comp (Subgroup.inclusion inf_le_left)
  have hOle : GLBPrimeCore p C ≤ C ⊓ M := le_inf (glbPrimeCore_le p C) D.czCore_le
  have hker : f.ker = (GLBPrimeCore p C).subgroupOf (C ⊓ M) := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change QuotientGroup.mk' _ (Subgroup.inclusion inf_le_left y) = 1 ↔ _
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', mem_primeComplementCore_iff_mem_glbPrimeCore]
    rfl
  refine SPLMSide.isSolvable_of_odd_card_ker f hCt.solv ?_ ?_
  · rintro _ ⟨y, rfl⟩
    exact ⟨Subgroup.inclusion inf_le_left y, y.2, rfl⟩
  · rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOle).toEquiv]
    exact D.odd_card_czCore

theorem D1SPLPairData.isSolvable_centralizer_splBar (D : D1SPLPairData p P M H R Rbar K z)
    (hzM : z ∈ M) {Pbar : Sylow p (D1CzQuot p z)} {KC : Subgroup (D1CzQuot p z)}
    (hCt : SPLCtildeFacts p M z Pbar KC) :
    Group.IsSolvable ↥(Subgroup.centralizer ({splBar hzM} : Set (↥M ⧸ CFSG.pCore 2 ↥M))) := by
  have := D.isSolvable_centralizer_inf hCt
  have : Group.IsSolvable ↥((Subgroup.centralizer ({z} : Set G) ⊓ M).subgroupOf M) :=
    Group.isSolvable_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe inf_le_right).symm.toMonoidHom) (MulEquiv.surjective _)
  rw [D.centralizer_splBar_eq hzM]
  exact Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective _ _)

theorem d1SPLPieceCentralizer_holds : D1SPLPieceCentralizer := by
  intro G _ _ p P M H R Rbar K z D hzM P' Pbar KC hRC _ hP'M hCt
  have hsolv := D.isSolvable_centralizer_splBar hzM hCt
  exact
    { core_le := D.czCore_le
      core_odd := D.odd_card_czCore
      twoCore_inf := D.twoCore_inf_centralizer_eq_bot hRC hP'M hCt
      lift := fun _ hg => D.exists_lift_of_mem_centralizer hzM hg
      normal_le := fun _ h1 h2 h3 => D.le_czCore_of_normal hRC hP'M hCt h1 h2 h3
      rank := fun _ hA hAe => D.card_lt_of_elemAbelian hzM hCt hA hAe
      u_norm := fun _ hΛ => SPLMSide.mem_normalizer_of_isSolvable_centralizer
        D.data.cfg.red.prime (D.splBar_pow_eq_one hzM) hsolv hΛ
      u_noncent := fun _ hΛ => SPLMSide.not_mem_centralizer_of_isSolvable_centralizer hsolv hΛ
      solv := hsolv }

end CFSG.AGLEmbedding

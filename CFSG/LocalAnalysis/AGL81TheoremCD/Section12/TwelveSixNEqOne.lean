module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixIData
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixICommX
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKInterSylow
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKFacts
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixALeMTools
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSevenSylow
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourOneProof

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} {d : ℕ}
  {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}

private theorem orderOf_eq_three_of_mem_of_ne_one {W : Subgroup G} (hW : Nat.card W = 3)
    {x : G} (hx : x ∈ W) (hx1 : x ≠ 1) : orderOf x = 3 := by
  have hdvd := Subgroup.orderOf_dvd_natCard W hx
  rw [hW] at hdvd
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hx1
  · exact h

private theorem exists_mem_orderOf_eq_three_of_card {W : Subgroup G}
    (hW : Nat.card W = 3) : ∃ w ∈ W, w ≠ 1 ∧ orderOf w = 3 := by
  haveI : Finite W := Nat.finite_of_card_ne_zero (by rw [hW]; norm_num)
  haveI : Nontrivial W := by
    rw [← Finite.one_lt_card_iff_nontrivial, hW]
    norm_num
  obtain ⟨w, hwW, hw1⟩ := Subgroup.exists_ne_one_of_nontrivial W
  exact ⟨w, hwW, hw1, orderOf_eq_three_of_mem_of_ne_one hW hwW hw1⟩

private theorem kbarConj_ne_one_of_orderOf_prime
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) (hXM : xSub p M H ≤ M)
    (hKH : ((kSub p M H).subgroupOf H).Normal)
    (hK : IsTwoPrimeComponentIn (kSub p M H) H)
    (hZ : center (modTwoCore (kSub p M H)) = ⊥)
    {I L : Subgroup G} {n r : ℕ} (hL : L ∈ weakBlockSet M H) (hI : I ≤ H ⊓ L)
    (hn2 : 2 ≤ n) (htype : IsPSLType 2 (GaloisField 2 n) (modTwoCore I))
    {y : ↥I} (hr : r.Prime) (hyord : orderOf y = r) (hr2 : r ≠ 2) :
    kbarConj hKH ⟨(y : G), hI.trans inf_le_left y.2⟩ ≠ 1 := by
  intro hφy
  have hX3 : ¬ 3 ∣ Nat.card (xSub p M H) := hc.not_three_dvd_card_xSub D hXM
  have hyker : (⟨(y : G), hI.trans inf_le_left y.2⟩ : ↥H) ∈ (kbarConj hKH).ker :=
    MonoidHom.mem_ker.mpr hφy
  rw [TwelveCtx.ker_kbarConj hc.ctx hKH hK hZ] at hyker
  have hyX : (y : G) ∈ xSub p M H := Subgroup.mem_subgroupOf.mp hyker
  have hI_NX : I ≤ Subgroup.normalizer (xSub p M H : Set G) :=
    hI.trans (inf_le_left.trans (xSub_normal_of_kSub_normal hKH))
  have hIN : I ≤ Subgroup.normalizer ((I ⊓ xSub p M H : Subgroup G) : Set G) :=
    (le_inf Subgroup.le_normalizer hI_NX).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hN3 : ¬ 3 ∣ Nat.card (I ⊓ xSub p M H : Subgroup G) := by
    intro h3
    exact hX3 (h3.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hNle : (I ⊓ xSub p M H : Subgroup G) ≤ pCoreOf 2 I :=
    le_pCoreOf_two_of_isPSLType hn2 htype inf_le_left hIN hN3
  have hyP : (y : G) ∈ pCoreOf 2 I := hNle ⟨y.2, hyX⟩
  have hP2 : IsPGroup 2 ↥(pCoreOf 2 I) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP2) ⟨(y : G), hyP⟩
  have hyGord : orderOf (y : G) = r := (Subgroup.orderOf_coe y).trans hyord
  have hpow : orderOf (y : G) = 2 ^ k :=
    (Subgroup.orderOf_coe (⟨(y : G), hyP⟩ : ↥(pCoreOf 2 I))).trans hk
  have hEq : r = 2 ^ k := hyGord.symm.trans hpow
  have hdvd2 : r ∣ 2 := by
    have hd : r ∣ 2 ^ k := by rw [← hEq]
    exact hr.dvd_of_dvd_pow hd
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp hdvd2)

private theorem kbarConj_commute
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (hKH : ((kSub p M H).subgroupOf H).Normal)
    (hK : IsTwoPrimeComponentIn (kSub p M H) H)
    (hZ : center (modTwoCore (kSub p M H)) = ⊥)
    {L L' I W : Subgroup G} (hL : L ∈ weakBlockSet M H) (hL' : L' ∈ weakBlockSet M H)
    (hne : L ≠ L') (hI : I ≤ H ⊓ L) (hW : W ≤ H ⊓ L') (y : ↥I) (w : ↥H)
    (hwW : (w : G) ∈ W) :
    kbarConj hKH ⟨(y : G), hI.trans inf_le_left y.2⟩ * kbarConj hKH w =
      kbarConj hKH w * kbarConj hKH ⟨(y : G), hI.trans inf_le_left y.2⟩ := by
  have hcommX : ⁅(y : G), (w : G)⁆ ∈ xSub p M H :=
    hc.commutator_le_xSub hL hL' hne hI hW
      (Subgroup.commutator_mem_commutator y.2 hwW)
  have hcommKer : ⁅(⟨(y : G), hI.trans inf_le_left y.2⟩ : ↥H), w⁆ ∈ (kbarConj hKH).ker := by
    rw [TwelveCtx.ker_kbarConj hc.ctx hKH hK hZ]
    have hcommX' : (y : G) * (w : G) * (y : G)⁻¹ * (w : G)⁻¹ ∈ xSub p M H := by
      simpa [commutatorElement_def] using hcommX
    exact Subgroup.mem_subgroupOf.mpr (by
      simpa [commutatorElement_def] using hcommX')
  have h1 : ⁅kbarConj hKH ⟨(y : G), hI.trans inf_le_left y.2⟩, kbarConj hKH w⁆ = 1 := by
    rw [← map_commutatorElement]
    exact MonoidHom.mem_ker.mp hcommKer
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

private theorem prime_eq_two_or_three_or_five_of_mulAut {Y : Type} [Group Y] [Finite Y]
    (hty : LieModel Y .PSp 2 3 1 ∨ Nonempty (Y ≃* alternatingGroup (Fin 9)))
    {φ ψ : MulAut Y} {r : ℕ} (hr : r.Prime) (hφ : orderOf φ = r) (hψ : orderOf ψ = 3)
    (hcomm : φ * ψ = ψ * φ) : r = 2 ∨ r = 3 ∨ r = 5 := by
  have hdvdAut : r ∣ Nat.card (MulAut Y) := by
    rw [← hφ]
    exact orderOf_dvd_natCard φ
  rcases hty with hpsp | hA9
  · exact prime_dvd_card_mulAut_of_lieModel_psp43 hpsp hr hdvdAut
  · obtain ⟨e⟩ := hA9
    let eAut : MulAut (alternatingGroup (Fin 9)) ≃* Equiv.Perm (Fin 9) :=
      (MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 9)))
        (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 9
          (by norm_num) (by norm_num))).symm
    let θ : MulAut Y ≃* Equiv.Perm (Fin 9) := (MulAut.congr e).trans eAut
    let σ : Equiv.Perm (Fin 9) := θ ψ
    let τ : Equiv.Perm (Fin 9) := θ φ
    have hσ : orderOf σ = 3 := by
      dsimp [σ]
      rw [MulEquiv.orderOf_eq, hψ]
    have hτ : orderOf τ = r := by
      dsimp [τ]
      rw [MulEquiv.orderOf_eq, hφ]
    have hcommθ : τ * σ = σ * τ := by
      dsimp [τ, σ]
      rw [← map_mul, ← map_mul, hcomm]
    have hτmem : τ ∈ Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 9))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact hcommθ.symm
    have hdvdCent : r ∣
        Nat.card (Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 9)))) := by
      have h := Subgroup.orderOf_dvd_natCard
        (Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 9)))) hτmem
      rwa [hτ] at h
    exact prime_dvd_card_centralizer_perm_nine hσ hr hdvdCent

private theorem exists_kbarConj_orderOf_three
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (hKH : ((kSub p M H).subgroupOf H).Normal)
    (hK : IsTwoPrimeComponentIn (kSub p M H) H)
    (hZ : center (modTwoCore (kSub p M H)) = ⊥)
    {L' W : Subgroup G} (hL' : L' ∈ weakBlockSet M H) (hW : W ≤ H ⊓ L')
    (hW3 : Nat.card W = 3) :
    ∃ wH : ↥H, (wH : G) ∈ W ∧ wH ≠ 1 ∧ orderOf (kbarConj hKH wH) = 3 := by
  obtain ⟨w, hwW, hw1, hword⟩ := exists_mem_orderOf_eq_three_of_card hW3
  have hWXbot : W ⊓ xSub p M H = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    by_contra hx1
    have hxord : orderOf x = 3 := orderOf_eq_three_of_mem_of_ne_one hW3 hx.1 hx1
    have hWeq : W = Subgroup.zpowers x := by
      refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx.1) ?_).symm
      rw [Nat.card_zpowers, hxord, hW3]
    exact hc.not_le_xSub hL' hW3 (hW.trans inf_le_right) (by
      rw [hWeq]
      exact Subgroup.zpowers_le.mpr hx.2)
  let wH : ↥H := ⟨w, hW.trans inf_le_left hwW⟩
  have hφw_ne : kbarConj hKH wH ≠ 1 := by
    intro h
    have hwker : wH ∈ (kbarConj hKH).ker := MonoidHom.mem_ker.mpr h
    rw [TwelveCtx.ker_kbarConj hc.ctx hKH hK hZ] at hwker
    have hwX : w ∈ xSub p M H := Subgroup.mem_subgroupOf.mp hwker
    have hmemW : w ∈ W ⊓ xSub p M H := ⟨hwW, hwX⟩
    rw [hWXbot] at hmemW
    exact hw1 (Subgroup.mem_bot.mp hmemW)
  have hwH3 : wH ^ 3 = 1 := by
    refine Subtype.ext ?_
    change w ^ 3 = 1
    rw [← orderOf_dvd_iff_pow_eq_one, hword]
  have hφw_ord : orderOf (kbarConj hKH wH) = 3 := by
    haveI : Fact (Nat.Prime 3) := Nat.fact_prime_three
    exact orderOf_eq_prime (by rw [← map_pow, hwH3, map_one]) hφw_ne
  exact ⟨wH, by simpa [wH] using hwW, fun h => hw1 (congrArg Subtype.val h), hφw_ord⟩

private theorem block_prime_eq_two_or_three_or_five
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) (hXM : xSub p M H ≤ M)
    (hKH : ((kSub p M H).subgroupOf H).Normal)
    (hK : IsTwoPrimeComponentIn (kSub p M H) H)
    (hty : LieModel (modTwoCore (kSub p M H)) .PSp 2 3 1 ∨
      Nonempty (modTwoCore (kSub p M H) ≃* alternatingGroup (Fin 9)))
    {L L' I W : Subgroup G} {n : ℕ} (hL : L ∈ weakBlockSet M H)
    (hL' : L' ∈ weakBlockSet M H) (hne : L ≠ L') (hI : I ≤ H ⊓ L) (hW : W ≤ H ⊓ L')
    (hW3 : Nat.card W = 3) (hn2 : 2 ≤ n)
    (htype : IsPSLType 2 (GaloisField 2 n) (modTwoCore I)) :
    ∀ r : ℕ, r.Prime → r ∣ Nat.card (modTwoCore I) → r = 2 ∨ r = 3 ∨ r = 5 := by
  have hZ : center (modTwoCore (kSub p M H)) = ⊥ := center_eq_bot_of_kbarType hty
  intro r hr hdvd
  by_contra hmem
  have hr2 : r ≠ 2 := fun h => hmem (Or.inl h)
  have hdvdI : r ∣ Nat.card ↥I :=
    hdvd.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥I))
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' (G := ↥I) r hdvdI
  have hyGord : orderOf (y : G) = r := (Subgroup.orderOf_coe y).trans hyord
  let yH : ↥H := ⟨(y : G), hI.trans inf_le_left y.2⟩
  have hφy_ne : kbarConj hKH yH ≠ 1 :=
    kbarConj_ne_one_of_orderOf_prime hc D hXM hKH hK hZ hL hI hn2 htype
      (y := y) hr hyord hr2
  obtain ⟨wH, hwW, -, hφw_ord⟩ :=
    exists_kbarConj_orderOf_three hc hKH hK hZ hL' hW hW3
  have hyHr : yH ^ r = 1 := by
    refine Subtype.ext ?_
    change (y : G) ^ r = 1
    rw [← orderOf_dvd_iff_pow_eq_one, hyGord]
  have hφy_ord : orderOf (kbarConj hKH yH) = r :=
    orderOf_eq_prime (by rw [← map_pow, hyHr, map_one]) hφy_ne
  have hcomm : kbarConj hKH yH * kbarConj hKH wH =
      kbarConj hKH wH * kbarConj hKH yH :=
    kbarConj_commute hc hKH hK hZ hL hL' hne hI hW y wH hwW
  exact hmem (prime_eq_two_or_three_or_five_of_mulAut hty hr hφy_ord hφw_ord hcomm)

private theorem block_n_eq_one
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) (hXM : xSub p M H ≤ M)
    (hKH : ((kSub p M H).subgroupOf H).Normal)
    (hK : IsTwoPrimeComponentIn (kSub p M H) H)
    (hty : LieModel (modTwoCore (kSub p M H)) .PSp 2 3 1 ∨
      Nonempty (modTwoCore (kSub p M H) ≃* alternatingGroup (Fin 9)))
    {L L' I W : Subgroup G} {n : ℕ} (hL : L ∈ weakBlockSet M H)
    (hL' : L' ∈ weakBlockSet M H) (hne : L ≠ L') (hI : I ≤ H ⊓ L) (hW : W ≤ H ⊓ L')
    (hW3 : Nat.card W = 3) (hn : Odd n)
    (htype : IsPSLType 2 (GaloisField 2 n) (modTwoCore I)) : n = 1 := by
  by_cases hn1 : n = 1
  · exact hn1
  have hn2 : 2 ≤ n := by
    obtain ⟨k, hk⟩ := hn
    omega
  exact eq_one_of_isPSLType_two_of_primes hn htype
    (block_prime_eq_two_or_three_or_five hc D hXM hKH hK hty hL hL' hne hI hW hW3 hn2 htype)

theorem TwelveSixKCtx.n_eq_one_of_kbarType
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) (hXM : xSub p M H ≤ M)
    (hKH : ((kSub p M H).subgroupOf H).Normal)
    (hK : IsTwoPrimeComponentIn (kSub p M H) H)
    (hty : LieModel (modTwoCore (kSub p M H)) .PSp 2 3 1 ∨
      Nonempty (modTwoCore (kSub p M H) ≃* alternatingGroup (Fin 9))) :
    n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1 := by
  have hne := TwelveFiveData.pairwise_ne hc.data hc.hcard
  refine ⟨?_, ?_, ?_⟩
  · exact block_n_eq_one hc D hXM hKH hK hty hc.data.mem₁ hc.data.mem₂ hne.1
      D.le_inf₁ (D.le₂.trans D.le_inf₂) D.cfg.card₂ hc.data.odd₁ D.type₁
  · exact block_n_eq_one hc D hXM hKH hK hty hc.data.mem₂ hc.data.mem₃ hne.2.2
      D.le_inf₂ (D.le₃.trans D.le_inf₃) D.cfg.card₃ hc.data.odd₂ D.type₂
  · exact block_n_eq_one hc D hXM hKH hK hty hc.data.mem₃ hc.data.mem₁ hne.2.1.symm
      D.le_inf₃ (D.le₁.trans D.le_inf₁) D.cfg.card₁ hc.data.odd₃ D.type₃

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end

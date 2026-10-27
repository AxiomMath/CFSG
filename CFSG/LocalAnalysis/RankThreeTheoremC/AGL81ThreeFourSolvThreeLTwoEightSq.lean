module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeToolsGen
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeTargets
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourOneOf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoLTwoEight
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoTools
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoLocalL28
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L28AutThree
import CFSG.LocalAnalysis.AGLEmbedding.SUPairCommute
import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusFive

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.KFactProofs.L28Local Subgroup
open CFSG.Quasithin.F6.L28Res
open scoped commutatorElement

namespace SolvNone

private theorem mul_conj_mul_inv_l28 {K : Type*} [Group K] (φ : MulAut K) (k : K) :
    φ * MulAut.conj k * φ⁻¹ = MulAut.conj (φ k) := by
  ext z
  simp [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply]

private theorem exists_pow_orderOf_three_l28 {K : Type*} [Group K] {t : K} (ht : t ^ 9 = 1)
    (ht1 : t ≠ 1) : ∃ n : ℕ, orderOf (t ^ n) = 3 ∧ t ^ n ≠ 1 := by
  have hdvd : orderOf t ∣ 3 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using ht)
  obtain ⟨i, hi, hti⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases i
  · exact absurd (orderOf_eq_one_iff.mp (by simpa using hti)) ht1
  · refine ⟨1, by simpa using hti, by simpa using ht1⟩
  · refine ⟨3, ?_, ?_⟩
    · rw [orderOf_pow' t (by norm_num), hti]
      norm_num
    · intro h
      have := orderOf_dvd_of_pow_eq_one h
      rw [hti] at this
      norm_num at this

theorem exists_mem_sylow_orderOf_nine_of_l28 {q : TauCeti.PrimePower}
    {d : TauCeti.ValidLieTypeIndex} (hq2 : q.p = 2) (hq3 : q.exponent = 3) (hd : d.1 = .A 1 q)
    {K : Type} [Group K] [Finite K] (hKX : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (T : Sylow 3 K) : ∃ t ∈ (T : Subgroup K), orderOf t = 9 := by
  obtain ⟨eK⟩ := hKX
  have hKc : IsCaseTwoGroup 3 K := ⟨d, Or.inl ⟨rfl, q, hq2, hq3, hd⟩, ⟨eK⟩⟩
  obtain ⟨ε₀⟩ := nonempty_equiv_G8 hKc
  have hE : Nat.card ((T : Subgroup K).map ε₀.toMonoidHom) = 9 := by
    rw [← card_sylow_three ε₀ T]
    exact (Nat.card_congr (ε₀.subgroupMap (T : Subgroup K)).toEquiv).symm
  obtain ⟨g, hg⟩ := exists_conj_of_card_nine CFSG.Quasithin.F6.L28Res.card_G8 hE card_T0
  set y := g⁻¹ * g9 * g with hy
  have hy1 : y ∈ (T : Subgroup K).map ε₀.toMonoidHom := by
    rw [hg, hy]
    have : g * (g⁻¹ * g9 * g) * g⁻¹ = g9 := by group
    rw [this]
    exact Subgroup.mem_zpowers g9
  obtain ⟨t, ht, hty⟩ := Subgroup.mem_map.mp hy1
  refine ⟨t, ht, ?_⟩
  have h1 : orderOf (ε₀ t) = orderOf t := MulEquiv.orderOf_eq ε₀ t
  have h2 : orderOf y = 9 := by
    rw [hy, show g⁻¹ * g9 * g = MulAut.conj g⁻¹ g9 by simp [MulAut.conj_apply],
      MulEquiv.orderOf_eq, orderOf_g9]
  have hty' : ε₀ t = y := hty
  rw [← h1, hty']
  exact h2

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_sylow_of_l28 {q : TauCeti.PrimePower} {d : TauCeti.ValidLieTypeIndex}
    (hq2 : q.p = 2) (hq3 : q.exponent = 3) (hd : d.1 = .A 1 q) {N Y₀ J : Subgroup G} [N.Normal]
    (hNX : Nonempty (N ≃* (TauCeti.CFSGIndex.lie d).Group)) (T : Sylow 3 N)
    (hTY₀ : (T : Subgroup N).map N.subtype ≤ Y₀) (hJs : IsSubnormal J Y₀)
    (hJ3 : ∀ x ∈ J, x ^ 3 ∈ centralizer (N : Set G)) (hJC : ¬ J ≤ centralizer (N : Set G)) :
    Y₀ ≤ normalizer (((T : Subgroup N).map N.subtype : Subgroup G) : Set G) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨eK⟩ := hNX
  have hKc : IsCaseTwoGroup 3 ↥N := ⟨d, Or.inl ⟨rfl, q, hq2, hq3, hd⟩, ⟨eK⟩⟩
  obtain ⟨ε₀⟩ := nonempty_equiv_G8 hKc
  have hdT : L28Data ↥N (T : Subgroup ↥N) := l28Data_of_equiv ε₀ T
  have hcardA : Nat.card (MulAut ↥N) = 1512 := card_mulAut_of_isCaseTwoGroup_three hKc
  haveI : Finite (MulAut ↥N) := Nat.finite_of_card_ne_zero (by rw [hcardA]; norm_num)
  set θ : G →* (MulAut ↥N) := MulAut.conjNormal with hθ
  set C := centralizer (N : Set G) with hC
  set ι : ↥N →* (MulAut ↥N) := MulAut.conj with hι
  have hθker : ∀ y : G, θ y = 1 ↔ y ∈ C := by
    intro y
    refine ⟨fun h => mem_centralizer_iff.mpr fun m hm => ?_, fun h => ?_⟩
    · have := congrArg Subtype.val (DFunLike.congr_fun h ⟨m, hm⟩)
      simp only [hθ, MulAut.conjNormal_apply, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.mp this).symm
    · refine MulEquiv.ext fun m => Subtype.ext ?_
      simp only [hθ, MulAut.conjNormal_apply, MulAut.one_apply]
      rw [(mem_centralizer_iff.mp h m m.2).symm, mul_inv_cancel_right]
  have hθι : ∀ k : ↥N, θ k = ι k := fun k => MulAut.conjNormal_val
  have hιinj : Function.Injective ι := hdT.conj_injective
  have hTY₀' : ∀ t ∈ (T : Subgroup ↥N), ι t ∈ Y₀.map θ := fun t ht =>
    ⟨t, hTY₀ ⟨t, ht, rfl⟩, hθι t⟩
  have hθJ1 : J.map θ ≠ ⊥ := by
    intro h
    refine hJC fun x hx => (hθker x).mp ?_
    have : θ x ∈ J.map θ := Subgroup.mem_map_of_mem θ hx
    rwa [h, Subgroup.mem_bot] at this
  have hθJ3 : ∀ y ∈ J.map θ, y ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    exact (hθker _).mpr (hJ3 x hx)
  have hθJp : IsPGroup 3 (J.map θ) := fun y => ⟨1, Subtype.ext (by simpa using hθJ3 y y.2)⟩
  set W := pCoreOf 3 (Y₀.map θ) with hW
  have hJW : J.map θ ≤ W :=
    CFSG.AGLEmbedding.SubnormalCommute.le_pCoreOf_of_isSubnormal (hJs.map θ) hθJp
  have hWnorm : Y₀.map θ ≤ normalizer (W : Set (MulAut ↥N)) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 3 _
  set W₀ : Subgroup ↥N := W.comap ι with hW₀
  have hW₀p : IsPGroup 3 W₀ :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 3 _).comap_of_injective ι hιinj
  have hTW₀ : (T : Subgroup ↥N) ≤ normalizer (W₀ : Set ↥N) := by
    intro t ht
    rw [mem_normalizer_iff]
    intro w
    have hn := mem_normalizer_iff.mp (hWnorm (hTY₀' t ht)) (ι w)
    simp only [hW₀, Subgroup.mem_comap, map_mul, map_inv]
    exact hn
  have hW₀T : W₀ ≤ (T : Subgroup ↥N) := by
    have hp : IsPGroup 3 (W₀ ⊔ (T : Subgroup ↥N) : Subgroup ↥N) :=
      hW₀p.to_sup_of_normal_left' T.isPGroup' hTW₀
    exact le_sup_left.trans (T.is_maximal' hp le_sup_right).le
  obtain ⟨k, hkW₀, hk1⟩ : ∃ k ∈ W₀, k ≠ 1 := by
    by_contra hne
    push Not at hne
    obtain ⟨w, hwJ, hw1⟩ : ∃ w ∈ J.map θ, w ≠ 1 := by
      by_contra h
      push Not at h
      exact hθJ1 (eq_bot_iff.mpr fun w hw => (Subgroup.mem_bot).mpr (h w hw))
    have hwW : w ∈ W := hJW hwJ
    have hfix : ∀ t ∈ (T : Subgroup ↥N), w t = t := by
      intro t ht
      have hc : ι (w t * t⁻¹) ∈ W := by
        rw [map_mul, map_inv, ← mul_conj_mul_inv_l28]
        have h1 : ι t * w⁻¹ * (ι t)⁻¹ ∈ W :=
          (mem_normalizer_iff.mp (hWnorm (hTY₀' t ht)) w⁻¹).mp (W.inv_mem hwW)
        have h2 : w * ι t * w⁻¹ * (ι t)⁻¹ = w * (ι t * w⁻¹ * (ι t)⁻¹) := by group
        rw [h2]
        exact W.mul_mem hwW h1
      exact mul_inv_eq_one.mp (hne _ hc)
    obtain ⟨t₀, -, hwt₀⟩ := hdT.aut w hfix
    have ht₀W : t₀ ∈ W₀ := by
      show ι t₀ ∈ W
      have : ι t₀ = w := hwt₀.symm
      rw [this]
      exact hwW
    apply hw1
    rw [hwt₀, hne t₀ ht₀W, map_one]
  have hYT : ∀ y ∈ Y₀.map θ, ∀ t ∈ (T : Subgroup ↥N), y t ∈ (T : Subgroup ↥N) := by
    intro y hy t ht
    have hyk : y k ∈ W₀ := by
      show ι (y k) ∈ W
      rw [← mul_conj_mul_inv_l28]
      exact (mem_normalizer_iff.mp (hWnorm hy) (ι k)).mp hkW₀
    have hykT : y k ∈ (T : Subgroup ↥N) := hW₀T hyk
    have hyk1 : y k ≠ 1 := fun h => hk1 (by simpa using congrArg y.symm h)
    have hcomm : y t * y k = y k * y t := by
      rw [← map_mul, ← map_mul, hdT.commute t ht k (hW₀T hkW₀)]
    exact hdT.centralizer_le _ hykT hyk1 _ hcomm
  intro y hy
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  obtain ⟨t, ht, rfl⟩ := hx
  refine ⟨θ y t, hYT (θ y) ⟨y, hy, rfl⟩ t ht, ?_⟩
  simp [hθ, MulAut.conjNormal_apply]

theorem le_centralizer_of_l28 {q : TauCeti.PrimePower} {d : TauCeti.ValidLieTypeIndex}
    (hq2 : q.p = 2) (hq3 : q.exponent = 3) (hd : d.1 = .A 1 q) {N Y₀ : Subgroup G} [N.Normal]
    (hNX : Nonempty (N ≃* (TauCeti.CFSGIndex.lie d).Group)) (T : Sylow 3 N)
    (hTY₀ : (T : Subgroup N).map N.subtype ≤ Y₀) {I₀ : Type} [Group I₀] [Finite I₀]
    (σ : I₀ →* G) (hσY : σ.range ≤ Y₀) (hσs : IsSubnormal σ.range Y₀)
    (hb : IsSymThreeOrSUThreeTwo (I₀ ⧸ CFSG.pCore 2 I₀))
    (hO2 : (CFSG.pCore 2 I₀).map σ ≤ centralizer (N : Set G)) :
    (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ ≤
      centralizer (N : Set G) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set J := (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ with hJ
  set D := σ.range with hD
  by_contra hJC
  have hJ3 : ∀ x ∈ J, x ^ 3 ∈ centralizer (N : Set G) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [← map_pow]
    exact hO2 (Subgroup.mem_map_of_mem σ (cube_mem_pCore_two hb g hg))
  have hJs : IsSubnormal J Y₀ := isSubnormal_oUpperTwo_map σ hσs
  have hY₀T := le_normalizer_sylow_of_l28 hq2 hq3 hd hNX T hTY₀ hJs hJ3 hJC
  obtain ⟨eK⟩ := hNX
  have hKc : IsCaseTwoGroup 3 ↥N := ⟨d, Or.inl ⟨rfl, q, hq2, hq3, hd⟩, ⟨eK⟩⟩
  obtain ⟨ε₀⟩ := nonempty_equiv_G8 hKc
  have hdata : ∀ T : Sylow 3 ↥N, L28Data ↥N (T : Subgroup ↥N) := fun T => l28Data_of_equiv ε₀ T
  have hdT := hdata T
  have hcardA : Nat.card (MulAut ↥N) = 1512 := card_mulAut_of_isCaseTwoGroup_three hKc
  haveI : Finite (MulAut ↥N) := Nat.finite_of_card_ne_zero (by rw [hcardA]; norm_num)
  set θ : G →* (MulAut ↥N) := MulAut.conjNormal with hθ
  set C := centralizer (N : Set G) with hC
  set ι : ↥N →* (MulAut ↥N) := MulAut.conj with hι
  have hθker : ∀ y : G, θ y = 1 ↔ y ∈ C := by
    intro y
    refine ⟨fun h => mem_centralizer_iff.mpr fun m hm => ?_, fun h => ?_⟩
    · have := congrArg Subtype.val (DFunLike.congr_fun h ⟨m, hm⟩)
      simp only [hθ, MulAut.conjNormal_apply, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.mp this).symm
    · refine MulEquiv.ext fun m => Subtype.ext ?_
      simp only [hθ, MulAut.conjNormal_apply, MulAut.one_apply]
      rw [(mem_centralizer_iff.mp h m m.2).symm, mul_inv_cancel_right]
  have hθι : ∀ k : ↥N, θ k = ι k := fun k => MulAut.conjNormal_val
  have hιinj : Function.Injective ι := hdT.conj_injective
  have hTY₀' : ∀ t ∈ (T : Subgroup ↥N), ι t ∈ Y₀.map θ := fun t ht =>
    ⟨t, hTY₀ ⟨t, ht, rfl⟩, hθι t⟩
  have hθJ1 : J.map θ ≠ ⊥ := by
    intro h
    refine hJC fun x hx => (hθker x).mp ?_
    have : θ x ∈ J.map θ := Subgroup.mem_map_of_mem θ hx
    rwa [h, Subgroup.mem_bot] at this
  have hθJ3 : ∀ y ∈ J.map θ, y ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    exact (hθker _).mpr (hJ3 x hx)
  have hθJp : IsPGroup 3 (J.map θ) := fun y => ⟨1, Subtype.ext (by simpa using hθJ3 y y.2)⟩
  have hYT : ∀ y ∈ Y₀.map θ, ∀ t ∈ (T : Subgroup ↥N), y t ∈ (T : Subgroup ↥N) := by
    rintro _ ⟨y, hy, rfl⟩ t ht
    obtain ⟨t', ht', ht't⟩ := (mem_normalizer_iff.mp (hY₀T hy) (t : G)).mp ⟨t, ht, rfl⟩
    have : θ y t = t' := by
      apply Subtype.ext
      change ((θ y t : N) : G) = N.subtype t'
      rw [ht't]
      simp [hθ, MulAut.conjNormal_apply]
    rw [this]
    exact ht'
  have hDcl : D.map θ = Subgroup.closure ((θ.comp σ) '' {x : I₀ | ∃ k : ℕ, x ^ 2 ^ k = 1}) := by
    rw [hD, MonoidHom.range_eq_map, ← closure_twoElements_eq_top hb, Subgroup.map_map,
      MonoidHom.map_closure]
  have hD2 : D.map θ ≤ Subgroup.closure {x | x ∈ D.map θ ∧ ∃ k : ℕ, x ^ 2 ^ k = 1} := by
    rw [hDcl]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨i, ⟨k, hk⟩, rfl⟩
    refine ⟨?_, k, ?_⟩
    · rw [← hDcl]
      exact Subgroup.mem_map_of_mem θ (MonoidHom.mem_range.mpr ⟨i, rfl⟩)
    · rw [MonoidHom.comp_apply, ← map_pow, ← map_pow, hk, map_one, map_one]
  have hJD : J ≤ D := Subgroup.map_le_range σ _
  set Tb : Subgroup (MulAut ↥N) := (T : Subgroup ↥N).map ι with hTb
  have hTbY₀ : Tb ≤ Y₀.map θ := by
    rintro _ ⟨t, ht, rfl⟩
    exact hTY₀' t ht
  have hTbnorm : Y₀.map θ ≤ normalizer (Tb : Set (MulAut ↥N)) := by
    intro y hy
    rw [mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨y t, hYT y hy t ht, ?_⟩
      rw [mul_conj_mul_inv_l28]
    · rintro ⟨t, ht, hzt⟩
      have hy' : y⁻¹ ∈ Y₀.map θ := Subgroup.inv_mem _ hy
      refine ⟨y⁻¹ t, hYT y⁻¹ hy' t ht, ?_⟩
      have h1 := mul_conj_mul_inv_l28 y⁻¹ t
      rw [hzt, inv_inv] at h1
      rw [← h1]
      group
  have hpow : ∀ z ∈ D.map θ, ∃ a : ℕ, z ^ 2 ^ a ∈ J.map θ := by
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    obtain ⟨a, ha⟩ := CFSG.AGLEmbedding.SUPair.exists_two_pow_mem (T := (⊤ : Subgroup I₀))
      (Subgroup.mem_top i)
    refine ⟨a, ?_⟩
    rw [← map_pow, ← map_pow]
    exact Subgroup.mem_map_of_mem θ (Subgroup.mem_map_of_mem σ ha)
  obtain ⟨x, hxD, hx2, hxC⟩ : ∃ x ∈ D.map θ, (∃ k : ℕ, x ^ 2 ^ k = 1) ∧
      x ∉ centralizer ((J.map θ : Subgroup (MulAut ↥N)) : Set (MulAut ↥N)) := by
    by_contra h
    push Not at h
    exact hθJ1 (eq_bot_of_twoElements_le_centralizer hD2 (Subgroup.map_mono hJD) hθJp hpow h)
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hxC (Subgroup.one_mem _)
  have hfix : ∀ z ∈ Tb, x * z * x⁻¹ = z → z = 1 := by
    rintro _ ⟨t, ht, rfl⟩ hxt
    by_contra ht1
    have ht1' : t ≠ 1 := by rintro rfl; exact ht1 (map_one ι)
    have hxt' : x t = t := by
      apply hιinj
      rw [← mul_conj_mul_inv_l28]
      exact hxt
    obtain ⟨n, hn3, -⟩ := exists_pow_orderOf_three_l28 (hdT.pow_nine_eq_one ht) ht1'
    have hstab : x ∈ MulAction.stabilizer (MulAut ↥N) (t ^ n) := by
      rw [MulAction.mem_stabilizer_iff]
      show x (t ^ n) = t ^ n
      rw [map_pow, hxt']
    obtain ⟨m, hm⟩ := L28Data.isPGroup_stabilizer hdata hcardA hn3 ⟨x, hstab⟩
    have hm' : x ^ 3 ^ m = 1 := by simpa using congrArg Subtype.val hm
    obtain ⟨k, hk⟩ := hx2
    have hcop : Nat.Coprime (3 ^ m) (2 ^ k) := Nat.Coprime.pow _ _ (by norm_num)
    exact hx1 (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one hm') (orderOf_dvd_of_pow_eq_one hk)))
  have hTbD : Tb ≤ D.map θ :=
    le_of_isSubnormal_of_fixedPointFree (hσs.map θ) hTbY₀ hTbnorm hxD hfix
  have hTbJ : Tb ≤ J.map θ := by
    intro z hz
    obtain ⟨a, ha⟩ := hpow z (hTbD hz)
    obtain ⟨t, ht, rfl⟩ := hz
    have h9 : (ι t) ^ 9 = 1 := by rw [← map_pow, hdT.pow_nine_eq_one ht, map_one]
    have hcop : Nat.Coprime (2 ^ a) (orderOf (ι t)) :=
      Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one h9)
        (Nat.Coprime.pow_left _ (by norm_num))
    obtain ⟨c, hc⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hc]
    exact Subgroup.pow_mem _ ha c
  obtain ⟨t, ht, ht9⟩ := exists_mem_sylow_orderOf_nine_of_l28 hq2 hq3 hd ⟨eK⟩ T
  have h3 : ι (t ^ 3) = 1 := by
    rw [map_pow]
    exact hθJ3 _ (hTbJ ⟨t, ht, rfl⟩)
  have h3' : t ^ 3 = 1 := hιinj (by rw [h3, map_one])
  have := orderOf_dvd_of_pow_eq_one h3'
  rw [ht9] at this
  norm_num at this

theorem eq_range_inl_or_inr {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    (hZ : center X = ⊥) {M : Subgroup (X × X)} (hM : M.Normal) (hMc : Nat.card M = Nat.card X) :
    M = (MonoidHom.inl X X).range ∨ M = (MonoidHom.inr X X).range := by
  have h1 : Nat.card X ≠ 1 := (Finite.one_lt_card (α := X)).ne'
  rcases CFSG.LocalAnalysis.EvenBN.Common.normal_prod_eq_of_isSimpleGroup hZ hZ hM with
    h | h | h | h
  · rw [h, Subgroup.card_bot] at hMc
    exact absurd hMc.symm h1
  · left
    rw [h]
    ext ⟨a, b⟩
    simp only [Subgroup.mem_prod, Subgroup.mem_top, Subgroup.mem_bot, true_and,
      MonoidHom.mem_range, MonoidHom.inl_apply, Prod.mk.injEq]
    exact ⟨fun hb => ⟨a, rfl, hb.symm⟩, fun ⟨_, _, hb⟩ => hb.symm⟩
  · right
    rw [h]
    ext ⟨a, b⟩
    simp only [Subgroup.mem_prod, Subgroup.mem_top, Subgroup.mem_bot, and_true,
      MonoidHom.mem_range, MonoidHom.inr_apply, Prod.mk.injEq]
    exact ⟨fun ha => ⟨b, ha.symm, rfl⟩, fun ⟨_, ha, _⟩ => ha.symm⟩
  · rw [h, Subgroup.card_top, Nat.card_prod] at hMc
    have hpos : 0 < Nat.card X := Nat.card_pos
    have : Nat.card X = 1 := by
      have h2 : Nat.card X * Nat.card X = Nat.card X * 1 := by rw [mul_one]; exact hMc
      exact Nat.eq_of_mul_eq_mul_left hpos h2
    exact absurd this h1

private theorem map_conj_eq_of_mem_normalizer_l28 {Y : Type*} [Group Y] {H : Subgroup Y} {n : Y}
    (hn : n ∈ normalizer (H : Set Y)) : H.map (MulAut.conj n).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact (mem_normalizer_iff.mp hn j).mp hj
  · intro hx
    refine ⟨n⁻¹ * x * n, (mem_normalizer_iff.mp hn _).mpr (by simpa [mul_assoc] using hx), ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

private theorem map_conj_mul_l28 {Y : Type*} [Group Y] (H : Subgroup Y) (a b : Y) :
    H.map (MulAut.conj (a * b)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem mem_normalizer_of_map_conj_eq {Y : Type*} [Group Y] [Finite Y] {H : Subgroup Y}
    {n : Y} (h : H.map (MulAut.conj n).toMonoidHom = H) : n ∈ normalizer (H : Set Y) :=
  Subgroup.mem_normalizer_fintype fun x hx => by
    rw [← h]
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩

variable {Y : Type} [Group Y] [Finite Y]

theorem factor_normalizes_of_l28 {q : TauCeti.PrimePower} {d : TauCeti.ValidLieTypeIndex}
    (hq2 : q.p = 2) (hq3 : q.exponent = 3) (hd : d.1 = .A 1 q) {L Y₁ Y₀ J : Subgroup Y}
    (hLY₁ : L ≤ Y₁) (hY₁L : Y₁ ≤ normalizer (L : Set Y))
    (hLX : Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group)) (R : Sylow 3 Y)
    (hRY₁ : (R : Subgroup Y) ≤ Y₁) (hRY₀ : (R : Subgroup Y) ≤ Y₀) (hJY₁ : J ≤ Y₁)
    (hJs : IsSubnormal J Y₀) (hJ3 : ∀ x ∈ J, x ^ 3 ∈ centralizer (L : Set Y))
    (hJC : ¬ J ≤ centralizer (L : Set Y)) :
    (∀ y ∈ Y₀ ⊓ Y₁, ∀ t ∈ (R : Subgroup Y) ⊓ L, y * t * y⁻¹ ∈ (R : Subgroup Y) ⊓ L) ∧
      ∃ τ ∈ (R : Subgroup Y) ⊓ L, orderOf τ = 9 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup ↥Y₁ := L.subgroupOf Y₁ with hN
  haveI : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLY₁).mpr hY₁L
  have hNX : Nonempty (N ≃* (TauCeti.CFSGIndex.lie d).Group) := by
    obtain ⟨f⟩ := hLX
    exact ⟨(Subgroup.subgroupOfEquivOfLe hLY₁).trans f⟩
  obtain ⟨T, hT⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal (R.subtype hRY₁) N
  have hmemT : ∀ g : ↥Y₁, g ∈ (T : Subgroup N).map N.subtype ↔ (g : Y) ∈ (R : Subgroup Y) ⊓ L := by
    intro g
    rw [hT, Sylow.coe_subtype, Subgroup.mem_inf, Subgroup.mem_subgroupOf, hN,
      Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  have hTY₀ : (T : Subgroup N).map N.subtype ≤ Y₀.subgroupOf Y₁ := fun g hg =>
    Subgroup.mem_subgroupOf.mpr (hRY₀ ((hmemT g).mp hg).1)
  have hJs' : IsSubnormal (J.subgroupOf Y₁) (Y₀.subgroupOf Y₁) := hJs.comap Y₁.subtype
  have hJ3' : ∀ x ∈ J.subgroupOf Y₁, x ^ 3 ∈ centralizer (N : Set ↥Y₁) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro n hn
    apply Subtype.ext
    simpa using mem_centralizer_iff.mp (hJ3 _ (Subgroup.mem_subgroupOf.mp hx)) (n : Y) hn
  have hJC' : ¬ J.subgroupOf Y₁ ≤ centralizer (N : Set ↥Y₁) := by
    intro h
    apply hJC
    intro x hx
    rw [mem_centralizer_iff]
    intro l hl
    have h1 := mem_centralizer_iff.mp
      (h (show (⟨x, hJY₁ hx⟩ : ↥Y₁) ∈ J.subgroupOf Y₁ from Subgroup.mem_subgroupOf.mpr hx))
      ⟨l, hLY₁ hl⟩ (Subgroup.mem_subgroupOf.mpr hl)
    exact congrArg Subtype.val h1
  have hnorm := le_normalizer_sylow_of_l28 hq2 hq3 hd hNX T hTY₀ hJs' hJ3' hJC'
  refine ⟨fun y hy t ht => ?_, ?_⟩
  · have hyN := hnorm (show (⟨y, hy.2⟩ : ↥Y₁) ∈ Y₀.subgroupOf Y₁ from
      Subgroup.mem_subgroupOf.mpr hy.1)
    have htT : (⟨t, hRY₁ ht.1⟩ : ↥Y₁) ∈ (T : Subgroup N).map N.subtype := (hmemT _).mpr ht
    exact (hmemT _).mp ((mem_normalizer_iff.mp hyN _).mp htT)
  · obtain ⟨t, ht, ht9⟩ := exists_mem_sylow_orderOf_nine_of_l28 hq2 hq3 hd hNX T
    refine ⟨((t : ↥Y₁) : Y), (hmemT _).mp ⟨t, ht, rfl⟩, ?_⟩
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, ht9]

theorem factor_le_centralizer_of_l28 {q : TauCeti.PrimePower} {d : TauCeti.ValidLieTypeIndex}
    (hq2 : q.p = 2) (hq3 : q.exponent = 3) (hd : d.1 = .A 1 q) {L Y₁ Y₀ : Subgroup Y}
    (hLY₁ : L ≤ Y₁) (hY₁L : Y₁ ≤ normalizer (L : Set Y))
    (hLX : Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group)) (R : Sylow 3 Y)
    (hRY₁ : (R : Subgroup Y) ≤ Y₁) (hRY₀ : (R : Subgroup Y) ≤ Y₀) {I₀ : Type} [Group I₀]
    [Finite I₀] (σ : I₀ →* Y) (hσY₁ : σ.range ≤ Y₁) (hσY : σ.range ≤ Y₀)
    (hσs : IsSubnormal σ.range Y₀) (hb : IsSymThreeOrSUThreeTwo (I₀ ⧸ CFSG.pCore 2 I₀))
    (hO2 : (CFSG.pCore 2 I₀).map σ ≤ centralizer (L : Set Y)) :
    (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ ≤
      centralizer (L : Set Y) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup ↥Y₁ := L.subgroupOf Y₁ with hN
  haveI : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLY₁).mpr hY₁L
  have hNX : Nonempty (N ≃* (TauCeti.CFSGIndex.lie d).Group) := by
    obtain ⟨f⟩ := hLX
    exact ⟨(Subgroup.subgroupOfEquivOfLe hLY₁).trans f⟩
  obtain ⟨T, hT⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal (R.subtype hRY₁) N
  have hTY₀ : (T : Subgroup N).map N.subtype ≤ Y₀.subgroupOf Y₁ := by
    rw [hT]
    intro g hg
    obtain ⟨h1, -⟩ := Subgroup.mem_inf.mp hg
    rw [Sylow.coe_subtype] at h1
    exact Subgroup.mem_subgroupOf.mpr (hRY₀ (Subgroup.mem_subgroupOf.mp h1))
  set σ₁ : I₀ →* ↥Y₁ := σ.codRestrict Y₁ (fun i => hσY₁ ⟨i, rfl⟩) with hσ₁
  have hrange : σ₁.range = σ.range.subgroupOf Y₁ := by
    ext g
    constructor
    · rintro ⟨i, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr ⟨i, rfl⟩
    · intro hg
      obtain ⟨i, hi⟩ := Subgroup.mem_subgroupOf.mp hg
      exact ⟨i, Subtype.ext hi⟩
  have hσY' : σ₁.range ≤ Y₀.subgroupOf Y₁ := by
    rw [hrange]
    intro g hg
    exact Subgroup.mem_subgroupOf.mpr (hσY (Subgroup.mem_subgroupOf.mp hg))
  have hσs' : IsSubnormal σ₁.range (Y₀.subgroupOf Y₁) := by
    rw [hrange]
    exact hσs.comap Y₁.subtype
  have hO2' : (CFSG.pCore 2 I₀).map σ₁ ≤ centralizer (N : Set ↥Y₁) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [mem_centralizer_iff]
    intro n hn
    apply Subtype.ext
    exact mem_centralizer_iff.mp (hO2 ⟨g, hg, rfl⟩) (n : Y) hn
  have h := le_centralizer_of_l28 hq2 hq3 hd hNX T hTY₀ σ₁ hσY' hσs' hb hO2'
  rintro _ ⟨g, hg, rfl⟩
  rw [mem_centralizer_iff]
  intro l hl
  have h1 := mem_centralizer_iff.mp (h ⟨g, hg, rfl⟩) ⟨l, hLY₁ hl⟩ (Subgroup.mem_subgroupOf.mpr hl)
  exact congrArg Subtype.val h1

end SolvNone

open SolvNone

theorem threeFourSolvThreeLTwoEightSq_holds : ThreeFourSolvThreeLTwoEightSq := by
  intro q d hq2 hq3 hd Y _ _ K Y₀ E R I₀ _ _ σ hKn hKX _ _ _ _ _ hER hE hEc hcore hO2 _ hσY hσs
    hb _ _
  classical
  haveI := hKn
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hs, hnab, -⟩ := lTwoEight_catalog_facts hq2 hq3 hd
  haveI := hs
  haveI := finite_lTwoEight hq2 hq3 hd
  have hZX : center (TauCeti.CFSGIndex.lie d).Group = ⊥ :=
    CFSG.ComponentClassification.Helpers.center_eq_bot _ hnab
  obtain ⟨e⟩ := hKX
  set X := (TauCeti.CFSGIndex.lie d).Group with hXdef
  set C := centralizer (K : Set Y) with hCdef
  set J := (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ with hJdef
  have hRY₀ : (R : Subgroup Y) ≤ Y₀ :=
    (sylow_le_threeFourCore Nat.prime_three R hER hE hEc).trans hcore
  set g : X × X →* Y := K.subtype.comp e.symm.toMonoidHom with hgdef
  have hg : Function.Injective g := K.subtype_injective.comp e.symm.injective
  have hinl : Function.Injective (MonoidHom.inl X X) := fun a b h => congrArg Prod.fst h
  have hinr : Function.Injective (MonoidHom.inr X X) := fun a b h => congrArg Prod.snd h
  set K₁ : Subgroup Y := (MonoidHom.inl X X).range.map g with hK₁
  set K₂ : Subgroup Y := (MonoidHom.inr X X).range.map g with hK₂
  have hmem₁ : ∀ y : Y, y ∈ K₁ ↔ ∃ a : X, g (a, 1) = y := by
    intro y
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨(a, 1), ⟨a, rfl⟩, rfl⟩
  have hmem₂ : ∀ y : Y, y ∈ K₂ ↔ ∃ b : X, g (1, b) = y := by
    intro y
    constructor
    · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
      exact ⟨b, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨(1, b), ⟨b, rfl⟩, rfl⟩
  have hgl : Function.Injective (g.comp (MonoidHom.inl X X)) := fun a b h => hinl (hg h)
  have hgr : Function.Injective (g.comp (MonoidHom.inr X X)) := fun a b h => hinr (hg h)
  have hK₁X : Nonempty (K₁ ≃* X) := by
    refine ⟨(MulEquiv.subgroupCongr ?_).trans (MonoidHom.ofInjective hgl).symm⟩
    rw [MonoidHom.range_comp]
  have hK₂X : Nonempty (K₂ ≃* X) := by
    refine ⟨(MulEquiv.subgroupCongr ?_).trans (MonoidHom.ofInjective hgr).symm⟩
    rw [MonoidHom.range_comp]
  have hcomm₁₂ : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨x, rfl⟩ := (hmem₁ a).mp ha
    obtain ⟨z, rfl⟩ := (hmem₂ b).mp hb
    rw [← map_mul, ← map_mul]
    congr 1
    ext <;> simp
  have hinf₁₂ : ∀ a ∈ K₁, a ∈ K₂ → a = 1 := by
    intro a ha hb
    obtain ⟨x, rfl⟩ := (hmem₁ a).mp ha
    obtain ⟨z, hz⟩ := (hmem₂ _).mp hb
    have h1 := congrArg Prod.fst (hg hz)
    simp only at h1
    rw [← h1]
    exact map_one g
  have hgK : ∀ k : K, g (e k) = k := fun k => by simp [hgdef]
  have hdec : ∀ k ∈ K, ∃ a ∈ K₁, ∃ b ∈ K₂, k = a * b := by
    intro k hk
    refine ⟨g ((e ⟨k, hk⟩).1, 1), (hmem₁ _).mpr ⟨_, rfl⟩, g (1, (e ⟨k, hk⟩).2),
      (hmem₂ _).mpr ⟨_, rfl⟩, ?_⟩
    rw [← map_mul]
    have : (((e ⟨k, hk⟩).1, 1) * (1, (e ⟨k, hk⟩).2) : X × X) = e ⟨k, hk⟩ := by ext <;> simp
    rw [this, hgK]
  have hC₁₂ : ∀ c : Y, c ∈ centralizer (K₁ : Set Y) → c ∈ centralizer (K₂ : Set Y) → c ∈ C := by
    intro c h1 h2
    rw [mem_centralizer_iff]
    intro k hk
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec k hk
    have e1 := mem_centralizer_iff.mp h1 a ha
    have e2 := mem_centralizer_iff.mp h2 b hb
    calc a * b * c = a * (b * c) := by group
      _ = a * (c * b) := by rw [e2]
      _ = (a * c) * b := by group
      _ = (c * a) * b := by rw [e1]
      _ = c * (a * b) := by group
  have hK₁K : K₁ ≤ K := by
    rintro _ ⟨p, -, rfl⟩
    exact (e.symm p).2
  have hK₂K : K₂ ≤ K := by
    rintro _ ⟨p, -, rfl⟩
    exact (e.symm p).2
  have hCK₁ : C ≤ centralizer (K₁ : Set Y) := Subgroup.centralizer_le hK₁K
  have hCK₂ : C ≤ centralizer (K₂ : Set Y) := Subgroup.centralizer_le hK₂K
  set ψ : Y → MulAut (X × X) := fun y => (e.symm.trans (MulAut.conjNormal y)).trans e with hψ
  have hgψ : ∀ (y : Y) (p : X × X), (MulAut.conj y) (g p) = g (ψ y p) := by
    intro y p
    simp [hgdef, hψ, MulAut.conjNormal_apply, MulAut.conj_apply]
  have hmapg : ∀ (y : Y) (A : Subgroup (X × X)),
      (A.map g).map (MulAut.conj y).toMonoidHom = (A.map (ψ y).toMonoidHom).map g := by
    intro y A
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext p
    exact hgψ y p
  have hinlN : (MonoidHom.inl X X).range.Normal :=
    ⟨fun n hn x => by
      obtain ⟨a, rfl⟩ := hn
      exact ⟨x.1 * a * x.1⁻¹, by ext <;> simp⟩⟩
  have hinrN : (MonoidHom.inr X X).range.Normal :=
    ⟨fun n hn x => by
      obtain ⟨b, rfl⟩ := hn
      exact ⟨x.2 * b * x.2⁻¹, by ext <;> simp⟩⟩
  have hcardinl : Nat.card (MonoidHom.inl X X).range = Nat.card X :=
    (Nat.card_congr (MonoidHom.ofInjective hinl).toEquiv).symm
  have hcardinr : Nat.card (MonoidHom.inr X X).range = Nat.card X :=
    (Nat.card_congr (MonoidHom.ofInjective hinr).toEquiv).symm
  have hcases : ∀ (A : Subgroup (X × X)), A.Normal → Nat.card A = Nat.card X → ∀ y : Y,
      (A.map g).map (MulAut.conj y).toMonoidHom = K₁ ∨
        (A.map g).map (MulAut.conj y).toMonoidHom = K₂ := by
    intro A hA hAc y
    have hMn : (A.map (ψ y).toMonoidHom).Normal := hA.map _ (ψ y).surjective
    have hMc : Nat.card (A.map (ψ y).toMonoidHom) = Nat.card X := by
      rw [Subgroup.card_map_of_injective (ψ y).injective, hAc]
    rw [hmapg]
    rcases eq_range_inl_or_inr hZX hMn hMc with h | h
    · left
      rw [h]
    · right
      rw [h]
  have hcase₁ : ∀ y : Y, K₁.map (MulAut.conj y).toMonoidHom = K₁ ∨
      K₁.map (MulAut.conj y).toMonoidHom = K₂ := hcases _ hinlN hcardinl
  have hcase₂ : ∀ y : Y, K₂.map (MulAut.conj y).toMonoidHom = K₁ ∨
      K₂.map (MulAut.conj y).toMonoidHom = K₂ := hcases _ hinrN hcardinr
  have hK₁₂ : K₁ ≠ K₂ := by
    intro h
    obtain ⟨a, ha⟩ : ∃ a : X, a ≠ 1 := exists_ne 1
    have h1 : g (a, 1) ∈ K₁ := (hmem₁ _).mpr ⟨a, rfl⟩
    have h2 : g (a, 1) ∈ K₂ := h ▸ h1
    have h3 := hinf₁₂ _ h1 h2
    have h4 : ((a, 1) : X × X) = 1 := hg (by rw [h3, map_one])
    exact ha (congrArg Prod.fst h4)
  have hmapinj : ∀ (y : Y) {A B : Subgroup Y}, A.map (MulAut.conj y).toMonoidHom =
      B.map (MulAut.conj y).toMonoidHom → A = B := fun y A B h =>
    Subgroup.map_injective (MulAut.conj y).injective h
  set Y₁ : Subgroup Y := normalizer (K₁ : Set Y) with hY₁
  have hY₁iff : ∀ y : Y, y ∈ Y₁ ↔ K₁.map (MulAut.conj y).toMonoidHom = K₁ := fun y =>
    ⟨map_conj_eq_of_mem_normalizer_l28, mem_normalizer_of_map_conj_eq⟩
  have hswap : ∀ y : Y, y ∉ Y₁ → K₁.map (MulAut.conj y).toMonoidHom = K₂ ∧
      K₂.map (MulAut.conj y).toMonoidHom = K₁ := by
    intro y hy
    have h1 : K₁.map (MulAut.conj y).toMonoidHom = K₂ :=
      (hcase₁ y).resolve_left fun h => hy ((hY₁iff y).mpr h)
    refine ⟨h1, (hcase₂ y).resolve_right fun h2 => hK₁₂ (hmapinj y (h1.trans h2.symm))⟩
  have hY₁K₂ : ∀ y ∈ Y₁, K₂.map (MulAut.conj y).toMonoidHom = K₂ := by
    intro y hy
    refine (hcase₂ y).resolve_left fun h2 => hK₁₂ (hmapinj y ?_)
    rw [h2, (hY₁iff y).mp hy]
  have hsq : ∀ y : Y, y ∉ Y₁ → y ^ 2 ∈ Y₁ := by
    intro y hy
    rw [hY₁iff, pow_two, map_conj_mul_l28, (hswap y hy).1, (hswap y hy).2]
  have h3Y₁ : ∀ y : Y, (∃ n : ℕ, y ^ 3 ^ n = 1) → y ∈ Y₁ := by
    rintro y ⟨n, hn⟩
    by_contra hy
    obtain ⟨m, hm⟩ : Odd (3 ^ n) := Odd.pow (by decide)
    have h1 : (y ^ 2) ^ m ∈ Y₁ := Y₁.pow_mem (hsq y hy) m
    have h2 : y = ((y ^ 2) ^ m)⁻¹ * y ^ 3 ^ n := by
      rw [hm, ← pow_mul, pow_succ, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hn, mul_one] at h2
    exact hy (h2 ▸ Y₁.inv_mem h1)
  have hRY₁ : (R : Subgroup Y) ≤ Y₁ := fun r hr => h3Y₁ r (by
    obtain ⟨n, hn⟩ := R.isPGroup' ⟨r, hr⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩)
  have hJY₁ : J ≤ Y₁ := oUpperTwo_map_le_of_odd σ fun y hy hodd =>
    h3Y₁ y ⟨1, by rw [pow_one]; exact pow_three_eq_one_of_mem_range_of_odd σ hb hy hodd⟩
  have hK₁Y₁ : K₁ ≤ Y₁ := Subgroup.le_normalizer
  have hK₂Y₁ : K₂ ≤ Y₁ := fun b hb => Subgroup.mem_normalizer_fintype fun a ha => by
    rw [← hcomm₁₂ a ha b hb, mul_inv_cancel_right]
    exact ha
  have hY₁N₂ : Y₁ ≤ normalizer (K₂ : Set Y) := fun y hy =>
    mem_normalizer_of_map_conj_eq (hY₁K₂ y hy)
  have hO2σ : (CFSG.pCore 2 I₀).map σ ≤ C := (map_pCore_two_le_pCoreOf σ hσs).trans hO2
  have hJ3 : ∀ x ∈ J, x ^ 3 ∈ C := cube_mem_of_pCoreOf_le σ hσs hO2 hb
  by_cases hD : σ.range ≤ Y₁
  ·
    have h₁ := factor_le_centralizer_of_l28 hq2 hq3 hd hK₁Y₁ le_rfl hK₁X R hRY₁ hRY₀ σ hD hσY
      hσs hb (hO2σ.trans hCK₁)
    have h₂ := factor_le_centralizer_of_l28 hq2 hq3 hd hK₂Y₁ hY₁N₂ hK₂X R hRY₁ hRY₀ σ hD hσY
      hσs hb (hO2σ.trans hCK₂)
    exact fun x hx => hC₁₂ x (h₁ hx) (h₂ hx)
  obtain ⟨s, hsD, ⟨k₂, hk₂⟩, hsY₁⟩ : ∃ s ∈ σ.range, (∃ k : ℕ, s ^ 2 ^ k = 1) ∧ s ∉ Y₁ := by
    by_contra h
    push Not at h
    apply hD
    rw [MonoidHom.range_eq_map, ← closure_twoElements_eq_top hb, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨x, ⟨k, hk⟩, rfl⟩
    exact h (σ x) ⟨x, rfl⟩ ⟨k, by rw [← map_pow, hk, map_one]⟩
  obtain ⟨hs₁, hs₂⟩ := hswap s hsY₁
  by_contra hJC
  have hJn : ∀ x ∈ J, ∀ u ∈ σ.range, u * x * u⁻¹ ∈ J := fun x hx u hu =>
    (Subgroup.normal_subgroupOf_iff (Subgroup.map_le_range σ _)).mp
      (normal_map_subgroupOf_range σ normal_oUpperTwo_top) x u hx hu
  have hJ₁ : ¬ J ≤ centralizer (K₁ : Set Y) := by
    intro h₁
    apply hJC
    refine fun x hx => hC₁₂ x (h₁ hx) ?_
    rw [mem_centralizer_iff]
    intro b hb
    rw [← hs₁] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    have hx' : s⁻¹ * x * s⁻¹⁻¹ ∈ J := hJn x hx s⁻¹ (σ.range.inv_mem hsD)
    have h1 := mem_centralizer_iff.mp (h₁ hx') a ha
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1 ⊢
    calc s * a * s⁻¹ * x = s * (a * (s⁻¹ * x * s)) * s⁻¹ := by group
      _ = s * ((s⁻¹ * x * s) * a) * s⁻¹ := by rw [h1]
      _ = x * (s * a * s⁻¹) := by group
  obtain ⟨hN₁, τ, hτ, hτ9⟩ := factor_normalizes_of_l28 hq2 hq3 hd hK₁Y₁ le_rfl hK₁X R hRY₁ hRY₀
    hJY₁ (isSubnormal_oUpperTwo_map σ hσs) (fun x hx => hCK₁ (hJ3 x hx)) hJ₁
  set T₁ : Subgroup Y := (R : Subgroup Y) ⊓ K₁ with hT₁
  set T₂ : Subgroup Y := T₁.map (MulAut.conj s).toMonoidHom with hT₂
  set T : Subgroup Y := T₁ ⊔ T₂ with hTdef
  have hsY₀ : s ∈ Y₀ := hσY hsD
  have hT₁Y₀ : T₁ ≤ Y₀ := inf_le_left.trans hRY₀
  have hT₂K₂ : T₂ ≤ K₂ := by
    rw [← hs₁]
    exact Subgroup.map_mono inf_le_right
  have hs2T₁ : T₁.map (MulAut.conj (s * s)).toMonoidHom = T₁ := by
    apply map_conj_eq_of_mem_normalizer_l28
    refine Subgroup.mem_normalizer_fintype fun t ht => hN₁ (s * s) ⟨Y₀.mul_mem hsY₀ hsY₀, ?_⟩ t ht
    rw [← pow_two]
    exact hsq s hsY₁
  have hsT : T.map (MulAut.conj s).toMonoidHom = T := by
    rw [hTdef, Subgroup.map_sup, ← hT₂, hT₂, ← map_conj_mul_l28, hs2T₁, sup_comm]
  have hsN : Subgroup.zpowers s ≤ normalizer (T : Set Y) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_of_map_conj_eq hsT)
  have hT₁p : IsPGroup 3 T₁ := R.isPGroup'.to_le inf_le_left
  have hT₂p : IsPGroup 3 T₂ := hT₁p.map _
  have hT₂N : T₂ ≤ normalizer (T₁ : Set Y) := fun b hb => Subgroup.mem_normalizer_fintype
    fun a ha => by
      rw [(hcomm₁₂ a ha.2 b (hT₂K₂ hb)).symm, mul_inv_cancel_right]
      exact ha
  have hTp : IsPGroup 3 T := hT₁p.to_sup_of_normal_left' hT₂p hT₂N
  have hT2 : ¬ 2 ∣ Nat.card T := by
    obtain ⟨n, hn⟩ := hTp.exists_card_eq
    rw [hn]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two Nat.prime_three).mp
      (Nat.prime_two.dvd_of_dvd_pow h)
    omega
  have hs2p : IsPGroup 2 (Subgroup.zpowers s) := by
    have hdvd : orderOf s ∣ 2 ^ k₂ := orderOf_dvd_of_pow_eq_one hk₂
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hidem := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 2
    Nat.prime_two (Subgroup.zpowers s) T hs2p hT2 hsN
  set V : Subgroup Y := ⁅T, Subgroup.zpowers s⁆ with hV
  have hVT : V ≤ T := Subgroup.le_normalizer_iff_commutator_le_left.mp hsN
  have hTY₀ : T ≤ Y₀ := sup_le hT₁Y₀ (by
    rintro _ ⟨t, ht, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact Y₀.mul_mem (Y₀.mul_mem hsY₀ (hT₁Y₀ ht)) (Y₀.inv_mem hsY₀))
  have hVD : V ≤ σ.range := by
    obtain ⟨n, hn⟩ := exists_iterate_commutator_le_of_isSubnormal hσs (hVT.trans hTY₀)
    have hstep : V ≤ ⁅V, σ.range⁆ := by
      calc V = ⁅V, Subgroup.zpowers s⁆ := hidem.symm
        _ ≤ ⁅V, σ.range⁆ := Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hsD)
    have hiter : ∀ m : ℕ, V ≤ (fun X : Subgroup Y => ⁅X, σ.range⁆)^[m] V := by
      intro m
      induction m with
      | zero => exact le_rfl
      | succ m ih =>
        rw [Function.iterate_succ_apply']
        exact hstep.trans (Subgroup.commutator_mono ih le_rfl)
    exact (hiter n).trans hn
  have hcV : ⁅τ, s⁆ ∈ V :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_sup_left hτ) (Subgroup.mem_zpowers s)
  set u : Y := s * τ⁻¹ * s⁻¹ with hu
  have huK₂ : u ∈ K₂ := by
    rw [← hs₁]
    exact ⟨τ⁻¹, K₁.inv_mem hτ.2, by simp [hu, MulAut.conj_apply]⟩
  have hτu : Commute τ u := hcomm₁₂ τ hτ.2 u huK₂
  have hcτ : ⁅τ, s⁆ = τ * u := by
    rw [commutatorElement_def, hu]
    group
  have hpowc : ∀ n : ℕ, ⁅τ, s⁆ ^ n = τ ^ n * (s * τ⁻¹ ^ n * s⁻¹) := by
    intro n
    rw [hcτ, hτu.mul_pow, hu, conj_pow, inv_pow]
  have hτ9' : τ ^ 9 = 1 := by
    rw [← hτ9]
    exact pow_orderOf_eq_one τ
  have hc9 : ⁅τ, s⁆ ^ 9 = 1 := by
    rw [hpowc, hτ9', inv_pow, hτ9', inv_one, mul_one, mul_inv_cancel, one_mul]
  have hodd : Odd (orderOf ⁅τ, s⁆) :=
    Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hc9)
  have hc3 := pow_three_eq_one_of_mem_range_of_odd σ hb (hVD hcV) hodd
  rw [hpowc] at hc3
  have hτ3K₂ : τ ^ 3 ∈ K₂ := by
    have h1 : τ ^ 3 = (s * τ⁻¹ ^ 3 * s⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hc3
    rw [h1]
    refine K₂.inv_mem ?_
    rw [← hs₁]
    exact ⟨τ⁻¹ ^ 3, K₁.pow_mem (K₁.inv_mem hτ.2) 3, by simp [MulAut.conj_apply]⟩
  have hτ31 := hinf₁₂ _ (K₁.pow_mem hτ.2 3) hτ3K₂
  have := orderOf_dvd_of_pow_eq_one hτ31
  rw [hτ9] at this
  norm_num at this

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

end

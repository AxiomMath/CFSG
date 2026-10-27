module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPCz
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPOmega
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPTransvect

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section Cyclic

variable {X : Type*} [Group X] [Finite X]

theorem commute_of_mem_normalizer_zpowers_of_coprime {p : ℕ} (hp : p.Prime) {x w : X} {N : ℕ}
    (hN : x ^ N = 1) (hpN : ¬ p ∣ N) (hwp : orderOf w = p) (hxw : Commute x w) :
    ∀ m : ℕ, ∀ g : X, orderOf g = p ^ (m + 1) → w ∈ Subgroup.zpowers g →
      x ∈ Subgroup.normalizer (Subgroup.zpowers g : Set X) → Commute x g := by
  have : Fact p.Prime := ⟨hp⟩
  intro m
  induction m with
  | zero =>
    intro g hg hwg _
    have heq : Subgroup.zpowers w = Subgroup.zpowers g :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hwg)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hg, hwp, zero_add, pow_one])
    have hgw : g ∈ Subgroup.zpowers w := heq ▸ Subgroup.mem_zpowers g
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hgw
    exact hxw.zpow_right k
  | succ m ih =>
    intro g hg hwg hxN
    have hg' : orderOf (g ^ p) = p ^ (m + 1) := by
      rw [orderOf_pow_of_dvd hp.ne_zero (by rw [hg]; exact dvd_pow_self p (by omega)), hg,
        pow_succ, Nat.mul_div_cancel _ hp.pos]
    have hcyc : IsCyclic (Subgroup.zpowers g) := Subgroup.isCyclic_zpowers g
    have hdvd : p ^ (m + 1) ∣ orderOf g := by
      rw [hg]
      exact pow_dvd_pow p (by omega)
    have hgq : orderOf (g ^ p ^ (m + 1)) = p := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) hdvd, hg, pow_succ,
        Nat.mul_div_cancel_left _ (pow_pos hp.pos _)]
    have hw1 : w ∈ Subgroup.zpowers (g ^ p ^ (m + 1)) :=
      mem_zpowers_of_orderOf_eq_of_isCyclic hwg
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers g) _) (by rw [hwp, hgq])
    have hw' : w ∈ Subgroup.zpowers (g ^ p) := by
      refine (Subgroup.zpowers_le.mpr ?_) hw1
      rw [pow_succ', pow_mul]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
    obtain ⟨r, hr⟩ := Subgroup.mem_zpowers_iff.mp
      ((Subgroup.mem_normalizer_iff.mp hxN g).mp (Subgroup.mem_zpowers g))
    have hxN' : x ∈ Subgroup.normalizer (Subgroup.zpowers (g ^ p) : Set X) := by
      apply mem_normalizer_zpowers_of_mem_zpowers
      rw [← conj_pow, ← hr]
      have : (g ^ r) ^ p = (g ^ p) ^ r := by
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
      rw [this]
      exact Subgroup.zpow_mem_zpowers _ r
    have hxgp := ih (g ^ p) hg' hw' hxN'
    set h := g ^ (r - 1) with hh
    have hxg : x * g * x⁻¹ = g * h := by
      rw [← hr, hh, ← zpow_one_add, add_sub_cancel]
    have hhg : h ∈ Subgroup.zpowers g := Subgroup.zpow_mem_zpowers g _
    have hhp : h ^ p = 1 := by
      have h1 : (x * g * x⁻¹) ^ p = g ^ p := by rw [conj_pow, hxgp.eq, mul_inv_cancel_right]
      rw [hxg, (Commute.self_zpow g (r - 1)).mul_pow] at h1
      have h2 : g ^ p * h ^ p = g ^ p * 1 := by
        rw [mul_one]
        exact h1
      exact mul_left_cancel h2
    have hhw : h ∈ Subgroup.zpowers w := mem_zpowers_of_pow_eq_one hp hwg hwp hhg hhp
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hhw
    have hxh : x * h * x⁻¹ = h := by
      rw [← hk, (hxw.zpow_right k).eq, mul_inv_cancel_right]
    have hNg := conj_pow_eq_mul_pow hxg hxh N
    rw [hN, one_mul, inv_one, mul_one] at hNg
    have hhN : h ^ N = 1 := by
      have h2 : g * h ^ N = g * 1 := by
        rw [mul_one]
        exact hNg.symm
      exact mul_left_cancel h2
    have hord : orderOf h = 1 := by
      rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hhp) with h1 | h1
      · exact h1
      · exact absurd (h1 ▸ orderOf_dvd_of_pow_eq_one hhN) hpN
    have hh1 : h = 1 := orderOf_eq_one_iff.mp hord
    show x * g = g * x
    calc x * g = x * g * x⁻¹ * x := by group
      _ = g * x := by rw [hxg, hh1, mul_one]

end Cyclic

section Cz

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M : Subgroup G} {z : G}
  {T : Sylow p (Subgroup.centralizer ({z} : Set G))} {Pbar : Sylow p (D1CzQuot p z)}
  {K : Subgroup (D1CzQuot p z)}

theorem D1CzReduced.eq_one_of_mem_centralizer (hc : D1CzReduced p M z T Pbar K)
    (hzK : d1CzElt p z ∉ K) {x : D1CzQuot p z}
    (hxC : x ∈ Subgroup.centralizer (K : Set (D1CzQuot p z))) {k : ℕ}
    (hxk : x ^ 2 ^ k = 1) : x = 1 := by
  have hp := hc.red.prime
  have hp2 := hc.red.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have hKn := hc.normal
  obtain ⟨hZ, -⟩ := hc.red.center_eq_bot_and_rankOne_of_not_mem hc.center hc.order hc.comp hzK
  have hOc : IsCyclic (CFSG.pCore p (D1CzQuot p z)) := hc.red.isCyclic_pCore_of_component hc.comp
  have hOp : IsPGroup p (CFSG.pCore p (D1CzQuot p z)) := CFSG.pCore_isPGroup
  have hOn : (CFSG.pCore p (D1CzQuot p z)).Normal := CFSG.pCore_normal
  have hzO : d1CzElt p z ∈ CFSG.pCore p (D1CzQuot p z) := mem_pCore_of_mem_center hc.center hc.order
  obtain ⟨g, hg⟩ := hOc.exists_generator
  have hOeq : CFSG.pCore p (D1CzQuot p z) = Subgroup.zpowers (g : D1CzQuot p z) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simpa using congrArg Subtype.val hn⟩
    · exact Subgroup.zpowers_le.mpr g.2
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hOp
  have hgO : orderOf (g : D1CzQuot p z) = p ^ n := by rw [← Nat.card_zpowers, ← hOeq, hn]
  have hn0 : n ≠ 0 := by
    rintro rfl
    have h1 : Nat.card (CFSG.pCore p (D1CzQuot p z)) = 1 := by rw [hn, pow_zero]
    have h2 := Subgroup.eq_bot_of_card_eq _ h1
    rw [h2, Subgroup.mem_bot] at hzO
    have h3 := hc.order
    rw [hzO, orderOf_one] at h3
    exact hp.one_lt.ne h3
  have hxN : x ∈ Subgroup.normalizer (Subgroup.zpowers (g : D1CzQuot p z) : Set _) := by
    rw [← hOeq, Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top x
  have hxz : Commute x (d1CzElt p z) := Subgroup.mem_center_iff.mp hc.center x
  have h2N : ¬ p ∣ 2 ^ k := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have hcomm := commute_of_mem_normalizer_zpowers_of_coprime hp hxk h2N hc.order hxz (n - 1)
    (g : D1CzQuot p z) (by rw [hgO]; congr 1; omega) (hOeq ▸ hzO) hxN
  have hlayer : CFSG.layer (D1CzQuot p z) ≤ K :=
    sSup_le fun L hL => (hc.unique L ((CFSG.isComponent_iff_open L).mp hL)).le
  have hF : CFSG.fittingSubgroup (D1CzQuot p z) = CFSG.pCore p (D1CzQuot p z) :=
    CFSG.Fitting_eq_pcore _ p hc.red.core_eq_bot
  have hxF : x ∈ Subgroup.centralizer (CFSG.generalizedFitting (D1CzQuot p z) : Set _) := by
    have hle : CFSG.generalizedFitting (D1CzQuot p z) ≤
        Subgroup.centralizer ((Subgroup.zpowers x : Subgroup _) : Set (D1CzQuot p z)) := by
      refine sup_le ?_ (hlayer.trans ?_)
      · rw [hF, hOeq, Subgroup.zpowers_le]
        refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact (hcomm.zpow_left j).eq
      · intro y hy
        refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
        have hxy : Commute x y := (Subgroup.mem_centralizer_iff.mp hxC y hy).symm
        exact (hxy.zpow_left j).eq
    exact Subgroup.le_centralizer_iff.mp hle (Subgroup.mem_zpowers x)
  have hxFs := CFSG.centralizer_generalizedFitting_le _ hxF
  have hFle : CFSG.generalizedFitting (D1CzQuot p z) ≤ CFSG.pCore p (D1CzQuot p z) ⊔ K :=
    sup_le (hF ▸ le_sup_left) (hlayer.trans le_sup_right)
  have hxOK := hFle hxFs
  rw [← SetLike.mem_coe, Subgroup.mul_normal] at hxOK
  obtain ⟨o, ho, k', hk', hok⟩ := Set.mem_mul.mp hxOK
  have hKl : K ≤ CFSG.layer (D1CzQuot p z) :=
    le_sSup (show K ∈ {K : Subgroup (D1CzQuot p z) | CFSG.IsComponent K} from
      (CFSG.isComponent_iff_open K).mpr hc.comp)
  have hOK : ∀ y ∈ K, Commute o y := by
    intro y hy
    have hmem : ⁅o, y⁆ ∈ ⁅CFSG.fittingSubgroup (D1CzQuot p z), CFSG.layer (D1CzQuot p z)⁆ :=
      Subgroup.commutator_mem_commutator (hF ▸ ho) (hKl hy)
    rw [CFSG.LocalCores.fitting_layer_commute (G := D1CzQuot p z), Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp hmem
  have hk'eq : k' = o⁻¹ * x := by rw [← hok, inv_mul_cancel_left]
  have hk'Z : (⟨k', hk'⟩ : K) ∈ Subgroup.center K := by
    refine Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_
    have hxy : Commute x y := (Subgroup.mem_centralizer_iff.mp hxC y y.2).symm
    have h1 : Commute (o⁻¹ * x) y := ((hOK y y.2).inv_left).mul_left hxy
    show (y : D1CzQuot p z) * k' = k' * y
    rw [hk'eq]
    exact h1.eq.symm
  rw [hZ, Subgroup.mem_bot] at hk'Z
  have hk'1 : k' = 1 := congrArg Subtype.val hk'Z
  have hxo : x = o := by rw [← hok, hk'1, mul_one]
  obtain ⟨j, hj⟩ := hOp ⟨o, ho⟩
  have hoj : o ^ p ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hcop : Nat.Coprime (2 ^ k) (p ^ j) :=
    Nat.Coprime.pow k j ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  rw [hxo] at hxk ⊢
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hxk)
    (orderOf_dvd_of_pow_eq_one hoj))

end Cz

end CFSG.AGLEmbedding

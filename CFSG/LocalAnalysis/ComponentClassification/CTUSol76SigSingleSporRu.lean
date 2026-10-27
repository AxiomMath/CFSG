module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporRu
public import CFSG.Sporadic.Schreier.RuMix
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleSporD

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit

theorem mem_of_isSubnormal_of_orderOf_prime {L : Type*} [Group L] [Finite L] {p : ℕ}
    (hp : p.Prime) (hp2 : ¬ p ^ 2 ∣ Nat.card L) {K : Subgroup L} (hK : K.IsSubnormal)
    (hpK : p ∣ Nat.card K) {y : L} (hy : orderOf y = p) : y ∈ K := by
  revert hpK
  induction hK with
  | top => exact fun _ => mem_top y
  | step H M hHM _ hN ih =>
    intro hpH
    have hyM : y ∈ M := ih (hpH.trans (Subgroup.card_dvd_of_le hHM))
    have : (H.subgroupOf M).Normal := hN
    have hM2 : ¬ p ^ 2 ∣ Nat.card M := fun h => hp2 (h.trans (Subgroup.card_subgroup_dvd_card M))
    have hHp : p ∣ Nat.card (H.subgroupOf M) := by
      rwa [Nat.card_congr (subgroupOfEquivOfLe hHM).toEquiv]
    have hy' : orderOf (⟨y, hyM⟩ : M) = p := by rw [Subgroup.orderOf_mk, hy]
    exact Subgroup.mem_subgroupOf.mp
      (Sporadic.RuSchreier.mem_of_orderOf_prime_of_normal hp hM2 (H.subgroupOf M) hHp hy')

theorem seven_dvd_card_quot_center_of_isComponent {L : Type*} [Group L] [Finite L]
    (hL : Nat.card L = 116480) {a b c d : L} (ha : orderOf a = 13) (hb : orderOf b = 13)
    (hab : orderOf (a * b) = 7) (hc : orderOf c = 5) (hd : orderOf d = 5)
    (hcd : orderOf (c * d) = 13) {K : Subgroup L} (hK : CFSG.IsComponent K) :
    7 ∣ Nat.card (↥K ⧸ center ↥K) := by
  obtain ⟨hq, hsub⟩ := hK
  have hKL : Nat.card K ∣ 116480 := hL ▸ Subgroup.card_subgroup_dvd_card K
  have hmem : ∀ {p : ℕ}, p.Prime → ¬ p ^ 2 ∣ 116480 → p ∣ Nat.card K → ∀ {y : L},
      orderOf y = p → y ∈ K := fun hp hp2 hpK _ hy =>
    mem_of_isSubnormal_of_orderOf_prime hp (hL ▸ hp2) hsub hpK hy
  have hdvd : ∀ {y : L} (hy : y ∈ K), orderOf y ∣ Nat.card K := fun {y} hy => by
    rw [← Subgroup.orderOf_mk y hy]
    exact orderOf_dvd_natCard _
  have h13 : 13 ∣ Nat.card K := by
    by_contra h13
    have h5 : ¬ 5 ∣ Nat.card K := fun h5 =>
      h13 (hcd ▸ hdvd (K.mul_mem (hmem (by norm_num) (by norm_num) h5 hc)
        (hmem (by norm_num) (by norm_num) h5 hd)))
    have hcop : Nat.Coprime (Nat.card K) 65 :=
      Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h5).symm
        ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h13).symm
    exact not_card_dvd_prime_pow_mul_prime_pow (q := 2) (r := 7) (a := 8) (b := 1) hq
      Nat.prime_two (by norm_num) (by norm_num) (hcop.dvd_of_dvd_mul_right (by norm_num; exact hKL))
  have haK := hmem (by norm_num) (by norm_num) h13 ha
  have hbK := hmem (by norm_num) (by norm_num) h13 hb
  let x : K := ⟨a * b, K.mul_mem haK hbK⟩
  have hx1 : (x : ↥K ⧸ center ↥K) ≠ 1 := by
    intro h1
    rw [QuotientGroup.eq_one_iff] at h1
    have hcomm := congrArg Subtype.val ((Subgroup.mem_center_iff.mp h1) ⟨a, haK⟩)
    simp only [Subgroup.coe_mul, x] at hcomm
    have hab' : Commute a b := by
      calc a * b = a⁻¹ * (a * (a * b)) := by group
        _ = a⁻¹ * (a * b * a) := by rw [hcomm]
        _ = b * a := by group
    have h13' : (a * b) ^ 13 = 1 := by
      have h1 : a ^ 13 = 1 := ha ▸ pow_orderOf_eq_one a
      have h2 : b ^ 13 = 1 := hb ▸ pow_orderOf_eq_one b
      rw [hab'.mul_pow, h1, h2, one_mul]
    have h7 := orderOf_dvd_of_pow_eq_one h13'
    rw [hab] at h7
    norm_num at h7
  have hx7 : (x : ↥K ⧸ center ↥K) ^ 7 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : x ^ 7 = 1 := Subtype.ext (by
      simp only [Subgroup.coe_pow, x, OneMemClass.coe_one]
      rw [← hab]
      exact pow_orderOf_eq_one _)
    rw [this, QuotientGroup.mk_one]
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime hx7 hx1 ▸ orderOf_dvd_natCard _

open Sporadic.RuSchreier in
theorem ruL_comps_seven :
    RestrictedStd.Spor.CompsSatisfy ruL fun Y _ => Nat.card (Y ⧸ center Y) ∈ {n : ℕ | 7 ∣ n} := by
  intro Y hY
  have hconj : ∀ p : ℕ, orderOf (ruLGen 1 * ruYp p * (ruLGen 1)⁻¹) = orderOf (ruYp p) := fun p => by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
  have hmemL : ∀ p : ℕ, ruLGen 1 * ruYp p * (ruLGen 1)⁻¹ ∈ ruL := fun p =>
    ruL.mul_mem (ruL.mul_mem (ruLGen_memL 1) (ruYp_memL p)) (ruL.inv_mem (ruLGen_memL 1))
  exact seven_dvd_card_quot_center_of_isComponent card_ruL
    (a := ⟨ruYp 13, ruYp_memL 13⟩)
    (b := ⟨ruLGen 1 * ruYp 13 * (ruLGen 1)⁻¹, hmemL 13⟩)
    (c := ⟨ruYp 5, ruYp_memL 5⟩)
    (d := ⟨ruLGen 1 * ruYp 5 * (ruLGen 1)⁻¹, hmemL 5⟩)
    (by rw [Subgroup.orderOf_mk, orderOf_ruYp (by decide)])
    (by rw [Subgroup.orderOf_mk, hconj, orderOf_ruYp (by decide)])
    (by rw [← Subgroup.orderOf_coe]; exact orderOf_ruMix_thirteen)
    (by rw [Subgroup.orderOf_mk, orderOf_ruYp (by decide)])
    (by rw [Subgroup.orderOf_mk, hconj, orderOf_ruYp (by decide)])
    (by rw [← Subgroup.orderOf_coe]; exact orderOf_ruMix_five) hY

open Sporadic.RuSchreier in
theorem ruC_comps_seven :
    RestrictedStd.Spor.CompsSatisfy ruC fun Y _ => Nat.card (Y ⧸ center Y) ∈ {n : ℕ | 7 ∣ n} := by
  intro Y hY
  exfalso
  have h3 : ¬ 3 ∣ Nat.card Y := RestrictedStd.Spor.ruC_comps Y hY
  have hYC : Nat.card Y ∣ 245760 := card_ruC ▸ Subgroup.card_subgroup_dvd_card Y
  exact not_card_dvd_prime_pow_mul_prime_pow (a := 14) (b := 1) hY.1 Nat.prime_two
    Nat.prime_five (by norm_num)
    (((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).symm.dvd_of_dvd_mul_left
      (by norm_num; exact hYC))

open Sporadic.RuSchreier Sporadic.Schreier in
theorem ru_centralizerIn_comps_seven :
    ∀ u ∈ ruP, orderOf u = 2 → RestrictedStd.Spor.CompsSatisfy (centralizerIn ruP u)
      fun Y _ => Nat.card (Y ⧸ center Y) ∈ {n : ℕ | 7 ∣ n} := by
  intro u hu ho
  have hmem : u ∈ {t | t ∈ ruP ∧ orderOf t = 2} := ⟨hu, ho⟩
  rw [ruInvolutions_eq] at hmem
  rcases hmem with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩
  · rw [centralizerIn_conj ruP hg, centralizerIn, ← ruC_eq_centralizer]
    exact RestrictedStd.Spor.CompsSatisfy.of_mulEquiv
      (RestrictedStd.Spor.isoInvariant_card_quotient_center _)
      (RestrictedStd.Spor.conjEquiv ruC g).symm ruC_comps_seven
  · rw [centralizerIn_conj ruP hg, centralizerIn, ruCentralizer_a]
    exact RestrictedStd.Spor.CompsSatisfy.of_mulEquiv
      (RestrictedStd.Spor.isoInvariant_card_quotient_center _)
      (RestrictedStd.Spor.conjEquiv ruL g).symm ruL_comps_seven

theorem singleComponentCleanAt_Ru :
    SingleComponentCleanAt (fun T _ => Blueprint.NativeSporadic.IsSporadic T .Ru) := by
  refine singleComponentCleanAt_of_primePow 7 1 fun T _ _ hT hP =>
    ⟨fun y K hy2 hK hq _ => ?_, ?_⟩
  · obtain ⟨e⟩ := hP
    have e' : T ≃* ↥Sporadic.RuSchreier.ruP := e.trans Sporadic.RuSchreier.ruEquivP
    have h : Nat.card (↥(K.subgroupOf (centralizer ({y} : Set T))) ⧸
        center ↥(K.subgroupOf (centralizer ({y} : Set T)))) ∈ {n : ℕ | 7 ∣ n} :=
      RestrictedStd.Spor.compsSatisfy_centralizer_of_mulEquiv _
        (RestrictedStd.Spor.isoInvariant_card_quotient_center _) ru_centralizerIn_comps_seven e' y
        hy2 _ (isComponent_subgroupOf_of_isTwoComponentIn hK hq)
    rw [pow_one, ← card_quot_center_subgroupOf hK.1]
    exact h
  · obtain ⟨e⟩ := hP
    rw [Nat.card_congr e.toEquiv]
    change ¬ 7 ^ (2 * 1) ∣ Nat.card Blueprint.NativeSporadic.Ru
    rw [Sporadic.Ru.card_Ru]
    norm_num

end CFSG.ComponentClassification.Sol76.Sig

module

public import CFSG.LargeExtraspecial.S14C13A
public import CFSG.LargeExtraspecial.S14C13SpinGen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem exists_lift_orderOf_five (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O}
    {ε : Vt S g t ≃ₗ[ZMod 2] Vt S g t} (hεR : ε ∈ RmodN S g t) (hε5 : orderOf ε = 5) :
    ∃ r : Rbar S g t, orderOf r = 5 ∧ resV haQ t r ∈ Subgroup.zpowers ε := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h1 := exists_resV_eq haQ hεR
  rcases h1 with ⟨r₁, hr₁⟩
  let K : Subgroup (Rbar S g t) := (Subgroup.zpowers ε).comap (resV haQ t)
  let φ : K →* Subgroup.zpowers ε :=
    ((resV haQ t).comp K.subtype).codRestrict _ (fun k => k.2)
  have hφ : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hmem : r₁ ^ i ∈ K := by
      show resV haQ t (r₁ ^ i) ∈ Subgroup.zpowers ε
      rw [map_zpow, hr₁]
      exact Subgroup.zpow_mem_zpowers ε i
    refine ⟨⟨r₁ ^ i, hmem⟩, Subtype.ext ?_⟩
    show resV haQ t (r₁ ^ i) = ε ^ i
    rw [map_zpow, hr₁]
  have hdvd : 5 ∣ Nat.card K := by
    have := Subgroup.card_dvd_of_surjective hφ
    rwa [Nat.card_zpowers, hε5] at this
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' 5 hdvd
  exact ⟨k, (Subgroup.orderOf_coe k).trans hk, k.2⟩

theorem apply_eq_of_mem_zpowers {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    {e ε : M ≃ₗ[ZMod 2] M} (hε : ε ∈ Subgroup.zpowers e) {v : M} (hv : e v = v) : ε v = v := by
  have hs : e ∈ MulAction.stabilizer (M ≃ₗ[ZMod 2] M) v := hv
  exact (Subgroup.zpowers_le.mpr hs) hε

theorem not_mem_Nbar_of_orderOf_five {t : S.O} (hN2 : IsPGroup 2 (Nbar S g t)) {r : S.O}
    (hr5 : orderOf r = 5) : r ∉ Nbar S g t := fun h => by
  obtain ⟨k, hk⟩ := hN2 ⟨r, h⟩
  have h1 : orderOf r ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
  rw [hr5] at h1
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_five h1) (by norm_num)

theorem spin13Stmt_of (hCE : CentralExtInput.{0}) : Spin13Stmt := by
  intro G _ _ _ S g t hSt hocc hext h7
  have haQ := hSt.hyp4.conj_mem
  have hN : NQHyp S g t := nqHyp_of_occurs hCE hSt hocc
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ hSt.mem
  have htN := S6.self_mem_Nbar hSt.hyp4 hSt.mem
  have hdata := sp_data hCE hSt hocc hocc.1
  rcases hdata with ⟨H, C, ht, ht1, hVQ, hSp, p₁, hdimV, hβ, hcomp⟩
  have hβa := beta_isAlt H C ht ht1 hVQ
  have hβn := beta_nondegenerate H C ht ht1 hVQ
  have hY := hSp.eq_sp
  have hε0 := exists_orderOf_five_fix_pair hβa hβn hdimV (e := p₁) (p := aV ht) hβ
  rcases hε0 with ⟨ε, hεβ, hε5, hεp, hεa⟩
  have hεR : ε ∈ RmodN S g t := by rw [hY]; exact hεβ
  have hr0 := exists_lift_orderOf_five haQ hεR hε5
  rcases hr0 with ⟨r, hr5, hrε⟩
  have hr5' : orderOf (r : S.O) = 5 := by rw [Subgroup.orderOf_coe]; exact hr5
  have hrN := not_mem_Nbar_of_orderOf_five hext.1 hr5'
  have hε'R : resV haQ t r ∈ RmodN S g t := by rw [← range_resV haQ t]; exact ⟨r, rfl⟩
  have hε'β : resV haQ t r ∈ TauCeti.BilinForm.isometryGroup (beta H C ht ht1 hVQ) := by
    rw [← hY]; exact hε'R
  have hε'a : resV haQ t r (aV ht) = aV ht := apply_eq_of_mem_zpowers hrε hεa
  have hε'p : resV haQ t r p₁ = p₁ := apply_eq_of_mem_zpowers hrε hεp
  let xε : TauCeti.BilinForm.isometryGroup (beta H C ht ht1 hVQ) := ⟨resV haQ t r, hε'β⟩
  have hx5 : xε ^ 5 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    show resV haQ t r ^ 5 = 1
    rw [← map_pow, ← hr5, pow_orderOf_eq_one, map_one]
  have hfact : ∀ n : Nbar S g t, nqRep S g t hY xε (nqMk n) = nqMk (nConj r n) := fun n =>
    nqRep_apply hY (x := r) rfl n
  have hf1 : ∃ v, nqRep S g t hY xε v ≠ v := by
    by_contra hcon
    push Not at hcon
    refine hrN (h7.1 r (Rbar_le_Mbar r.2) fun n hn => ?_)
    have h1 := (hfact ⟨n, hn⟩).symm.trans (hcon _)
    exact (nqMk_nConj_eq_iff r ⟨n, hn⟩).mp h1
  have hM : Nat.card (NQ S g t) = 256 := by
    have h1 := finrank_NQ_eq_of_card hSt.ne_one htt htN (e := 8) hocc.2.2
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), h1, Nat.card_zmod]
    norm_num
  have : Finite (NQ S g t) := Nat.finite_of_card_ne_zero (by rw [hM]; norm_num)
  have hfree := fixfree_of_orderOf_five hM hβa (nqRep S g t hY) hβ hcomp xε hx5 hε'a hε'p hf1
  refine ⟨r, r.2, hr5', fun n hn hcond => ?_⟩
  have hnt : n * t = t * n := commute_of_mem_Rbar haQ (Nbar_le_Rbar hn)
  have hmem : (r : S.O) * n * (r : S.O)⁻¹ * n⁻¹ ∈ Subgroup.zpowers t := by
    rcases hcond with h | h
    · rw [h, mul_inv_cancel]
      exact one_mem _
    · rw [h, hnt, mul_inv_cancel_right]
      exact Subgroup.mem_zpowers t
  have hfix : nqRep S g t hY xε (nqMk ⟨n, hn⟩) = nqMk ⟨n, hn⟩ := by
    rw [hfact]
    exact (nqMk_nConj_eq_iff r ⟨n, hn⟩).mpr hmem
  have h0 := hfree _ hfix
  exact S8.eq_one_or_eq_of_mem_zpowers htt ((nqMk_eq_zero_iff ⟨n, hn⟩).mp h0)

theorem claim14_13A_of_inputs (hCE : CentralExtInput.{0}) : Claim14_13A :=
  claim14_13A_of hCE (spin13Stmt_of hCE)

end CFSG.LargeExtraspecial.S14

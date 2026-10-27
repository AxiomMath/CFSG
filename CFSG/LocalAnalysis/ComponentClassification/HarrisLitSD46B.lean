module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitSD46A
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46c
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitClassical
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitL219A
public import CFSG.LieType.SteinbergBRTwoRankBound

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.GH74.GLS.TwoThin CFSG.ABGLocalTools
open Standing.Setup42

namespace SD46

theorem mem_of_mem_sup_of_odd {G : Type*} [Group G] {X N : Subgroup G}
    (hN : Odd (Nat.card ↥N)) (hNX : N ≤ normalizer (X : Set G)) {g : G} (hg : g ∈ X ⊔ N)
    (hg2 : g ^ 2 = 1) : g ∈ X := by
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left X N hNX] at hg
  obtain ⟨x, hx, m, hm, rfl⟩ := hg
  have hg2' : x * m * (x * m) = 1 := by
    simp only at hg2
    rw [← sq]
    exact hg2
  have hm2 : m ^ 2 ∈ X := by
    have h4 : m * x * m = x⁻¹ := eq_inv_of_mul_eq_one_right (by rw [← hg2']; group)
    have h2 : m * x * m⁻¹ ∈ X := (mem_normalizer_iff.mp (hNX hm) x).mp hx
    have h3 : m ^ 2 = (m * x * m⁻¹)⁻¹ * x⁻¹ := by
      rw [sq]
      calc m * m = (m * x * m⁻¹)⁻¹ * (m * x * m) := by group
        _ = (m * x * m⁻¹)⁻¹ * x⁻¹ := by rw [h4]
    rw [h3]
    exact mul_mem (inv_mem h2) (inv_mem hx)
  have hodd : Odd (orderOf m) := hN.of_dvd_nat (by
    rw [← Subgroup.orderOf_mk m hm]
    exact orderOf_dvd_natCard _)
  obtain ⟨k, hk⟩ := hodd
  have hmk : m = (m ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = orderOf m + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [hmk]
  exact mul_mem hx (pow_mem hm2 _)

end SD46

theorem harris46Semidihedral_of_classical
    (hCI : GSLit.ClassicalInvolutionInput) : Harris46SemidihedralInput := by
  intro X _ _ _ hnonab _ hcat t L p f S w z V i j hs i' j' hSyl J hJ hJK _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set β := w ^ (orderOf w / 2) * t ^ i' * z ^ j' with hβ
  set M := centralizer ({β} : Set X) with hM
  set Cb := centralizer ((KBar L β : Subgroup (MBar β)) : Set (MBar β)) with hCb
  have hβ2' : β ^ 2 = 1 := hs.setup.sq_eq_one_of_mem_X (beta_mem_X i' j')
  have hb1 : betaBar β ≠ 1 := hs.setup.betaBar_ne_one i' j'
  have hb2 : orderOf (betaBar β) = 2 := by
    refine orderOf_eq_prime ?_ hb1
    rw [betaBar, ← QuotientGroup.mk_pow]
    have : (⟨β, mem_centralizer_singleton_iff.mpr rfl⟩ : ↥M) ^ 2 = 1 := Subtype.ext hβ2'
    rw [this, QuotientGroup.mk_one]
  have hbZ := betaBar_mem_center β
  have hbC : betaBar β ∈ Cb := by
    rw [mem_centralizer_iff]
    intro y _
    exact mem_center_iff.mp hbZ y
  have hbCZ : (⟨betaBar β, hbC⟩ : ↥Cb) ∈ center ↥Cb := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_center_iff.mp hbZ y)
  have hbC2 : orderOf (⟨betaBar β, hbC⟩ : ↥Cb) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hb2
  have hSD : ∀ R : Sylow 2 ↥Cb, ∃ n, 4 ≤ n ∧
      Nonempty (↥(R : Subgroup ↥Cb) ≃* Open.SemidihedralGroup n) := by
    intro R
    obtain ⟨n, hn, ⟨e⟩⟩ := hSyl ((R : Subgroup ↥Cb).map Cb.subtype) ⟨R, rfl⟩
    exact ⟨n, hn, ⟨((R : Subgroup ↥Cb).equivMapOfInjective _ Cb.subtype_injective).trans e⟩⟩
  have hJperf : Group.IsPerfect ↥J := hJ.1.1
  have : Nontrivial ↥J := LocalCores.isQuasisimple_nontrivial hJ.1
  have hJ'perf : Group.IsPerfect ↥(J.subgroupOf Cb) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hJK).symm.toMonoidHom) (MulEquiv.surjective _)
  have : Nontrivial ↥(J.subgroupOf Cb) := (subgroupOfEquivOfLe hJK).surjective.nontrivial
  have hbJ : betaBar β ∈ J := SD46.mem_of_perfect hbCZ hbC2 hSD hJ'perf
  have hinvJ : ∀ x ∈ J, orderOf x = 2 → x = betaBar β := by
    intro x hx hx2
    have h := SD46.eq_of_orderOf_eq_two_of_perfect hbCZ hbC2 hSD hJ'perf
      (x := ⟨x, hJK hx⟩) hx (by rw [Subgroup.orderOf_mk]; exact hx2)
    exact congrArg Subtype.val h
  obtain ⟨Jh, hJh, hJhmap⟩ := LocalAnalysis.ComponentInitial.exists_isPComponent_of_isComponent 2 hJ
  set b' : ↥M := ⟨β, mem_centralizer_singleton_iff.mpr rfl⟩ with hb'
  have hb'2 : b' ^ 2 = 1 := Subtype.ext hβ2'
  have hb'Z : ∀ y : ↥M, y * b' = b' * y := fun y =>
    Subtype.ext (mem_centralizer_singleton_iff.mp y.2)
  have hOodd : Odd (Nat.card ↥(pPrimeCore 2 ↥M)) := odd_card_pPrimeCore _
  have hb'J : b' ∈ Jh := by
    have hON : pPrimeCore 2 ↥M ≤ normalizer (Jh : Set ↥M) :=
      L219.pPrimeCore_le_normalizer ((CatalogueBAlternating.pComponent_two_iff Jh).mp hJh)
    refine SD46.mem_of_mem_sup_of_odd hOodd hON ?_ hb'2
    have hbm : QuotientGroup.mk' (pPrimeCore 2 ↥M) b' ∈ Jh.map (QuotientGroup.mk' _) := by
      rw [hJhmap]
      exact hbJ
    obtain ⟨y, hy, hyb⟩ := hbm
    have hk : y⁻¹ * b' ∈ pPrimeCore 2 ↥M := QuotientGroup.eq.mp hyb
    have : b' = y * (y⁻¹ * b') := by group
    rw [this]
    exact mul_mem (mem_sup_left hy) (mem_sup_right hk)
  set Jx := Jh.map M.subtype with hJx
  have hJxM : Jx ≤ M := map_subtype_le _
  have hJxcomp : IsPComponent 2 (Jx.subgroupOf M) := by
    rw [show Jx.subgroupOf M = Jh from comap_map_eq_self_of_injective M.subtype_injective Jh]
    exact hJh
  have hβJx : β ∈ Jx := ⟨b', hb'J, rfl⟩
  have key : ∀ y ∈ Jx, y ^ 2 = 1 → y = 1 ∨ y = β := by
    rintro _ ⟨y', hy', rfl⟩ hy2
    have hy2' : y' ^ 2 = 1 := Subtype.ext hy2
    have hyJ : QuotientGroup.mk' (pPrimeCore 2 ↥M) y' ∈ J := by
      rw [← hJhmap]
      exact mem_map_of_mem _ hy'
    by_cases hy1 : QuotientGroup.mk' (pPrimeCore 2 ↥M) y' = 1
    · left
      have hO : y' ∈ pPrimeCore 2 ↥M := (QuotientGroup.eq_one_iff _).mp hy1
      rw [SD46.eq_one_of_mem_of_odd hOodd hO hy2']
      rfl
    · right
      have hyord : orderOf (QuotientGroup.mk' (pPrimeCore 2 ↥M) y') = 2 :=
        orderOf_eq_prime (by rw [← map_pow, hy2', map_one]) hy1
      have hyb := hinvJ _ hyJ hyord
      have hk : y'⁻¹ * b' ∈ pPrimeCore 2 ↥M := QuotientGroup.eq.mp hyb
      have hk2 : (y'⁻¹ * b') ^ 2 = 1 := by
        have hc : Commute y'⁻¹ b' := (hb'Z y'⁻¹)
        rw [hc.mul_pow, inv_pow, hy2', inv_one, one_mul, hb'2]
      have h1 := SD46.eq_one_of_mem_of_odd hOodd hk hk2
      have hyb' : y' = b' := (inv_mul_eq_one.mp h1)
      rw [hyb']
      rfl
  have hβord : orderOf β = 2 := by
    refine orderOf_eq_prime hβ2' fun h1 => hb1 ?_
    rw [betaBar]
    have : (⟨β, mem_centralizer_singleton_iff.mpr rfl⟩ : ↥M) = 1 := Subtype.ext h1
    rw [this, QuotientGroup.mk_one]
  have hrank : CFSG.pRank 2 ↥Jx ≤ 1 := by
    refine CFSG.LieType.SteinbergBR.pRank_le_of_card_le (by norm_num) fun A hA => ?_
    have hAle : A.map Jx.subtype ≤ zpowers β := by
      rintro _ ⟨a, ha, rfl⟩
      have ha2 : (a : X) ^ 2 = 1 := by
        have h := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) a ha
        exact congrArg Subtype.val h
      rcases key (a : X) a.2 ha2 with h | h
      · rw [Subgroup.coe_subtype, h]
        exact one_mem _
      · rw [Subgroup.coe_subtype, h]
        exact mem_zpowers β
    calc Nat.card ↥A = Nat.card ↥(A.map Jx.subtype) :=
          (card_map_of_injective Jx.subtype_injective).symm
      _ ≤ Nat.card ↥(zpowers β) := Subgroup.card_le_of_le hAle
      _ = 2 ^ 1 := by rw [Nat.card_zpowers, hβord, pow_one]
  exact hcat (catalog_of_oddLieType
    (FooteLit.oddLieType_of_classical_twoComponent hCI hnonab hβord hJxM hJxcomp hβJx hrank))

end CFSG.ComponentClassification.HarrisLit

module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.RootQa
public import CFSG.LocalAnalysis.EvenBN.TwoF4.RootAh

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup CFSG.Open
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (torusPair)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace LevelOneData

variable {h : Setup G} (d : LevelOneData h)

abbrev NA : Subgroup G := normalizer (d.A : Set G)

abbrev AN : Subgroup d.NA := d.A.subgroupOf d.NA

instance normal_AN : d.AN.Normal := normal_subgroupOf_of_le_normalizer le_rfl

abbrev Xb : Type := d.NA ⧸ d.AN

abbrev piA : d.NA →* d.Xb := QuotientGroup.mk' d.AN

abbrev bar (M : Subgroup G) : Subgroup d.Xb := (M.subgroupOf d.NA).map d.piA

abbrev tN : d.NA := ⟨h.t, d.J_le_normalizer_A h.t_mem_J⟩

abbrev tb : d.Xb := d.piA d.tN

theorem piA_eq_one_iff (x : d.NA) : d.piA x = 1 ↔ (x : G) ∈ d.A := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]

theorem piA_eq_iff (x y : d.NA) : d.piA x = d.piA y ↔ (x : G)⁻¹ * y ∈ d.A := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf,
    Subgroup.coe_mul, Subgroup.coe_inv]

theorem J_le_NA : h.J ≤ d.NA := d.J_le_normalizer_A

theorem mem_R_of_mem_A_of_mem_L {x : G} (hxA : x ∈ d.A) (hxL : x ∈ h.L) : x ∈ h.R :=
  d.mem_R_of_mem_A_of_comm hxA (commutatorElement_eq_one_iff_mul_comm.2 (h.mul_t_comm hxL))

theorem injective_bar {M : Subgroup G} (hML : M ≤ h.L) (hMR : M ⊓ h.R = ⊥) :
    Function.Injective (d.piA.comp (M.subgroupOf d.NA).subtype) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxA : ((x : d.NA) : G) ∈ d.A := (d.piA_eq_one_iff _).1 hx
  have hxM : ((x : d.NA) : G) ∈ M := mem_subgroupOf.1 x.2
  have : ((x : d.NA) : G) ∈ M ⊓ h.R := mem_inf.2 ⟨hxM, d.mem_R_of_mem_A_of_mem_L hxA (hML hxM)⟩
  rw [hMR, mem_bot] at this
  exact Subtype.ext (Subtype.ext this)

noncomputable def barEquiv {M : Subgroup G} (hMA : M ≤ d.NA) (hML : M ≤ h.L) (hMR : M ⊓ h.R = ⊥) :
    M ≃* d.bar M :=
  (subgroupOfEquivOfLe hMA).symm.trans ((MonoidHom.ofInjective (d.injective_bar hML hMR)).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, range_subtype])))

theorem N1_le_NA : h.N .i1 ≤ d.NA := (h.N1_le_J).trans d.J_le_NA

theorem _root_.CFSG.LocalAnalysis.EvenBN.TwoF4.Setup.N1_inf_R (h : Setup G) :
    h.N .i1 ⊓ h.R = ⊥ := by
  rw [inf_comm]; exact h.centralizer_e_f.2.1

theorem lieModel_N1b : LieModel (d.bar (h.N .i1)) .twistedB2 0 2 (2 * h.a + 1) := by
  obtain ⟨e⟩ := h.nonempty_N_equiv_suzuki (i := .i1) rfl
  have e' : d.bar (h.N .i1) ≃* CFSG.Blueprint.suzukiGroup h.a h.K :=
    (d.barEquiv d.N1_le_NA (h.N_le_L _) h.N1_inf_R).symm.trans e
  exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, h.a, h.one_le_a, h.K, inferInstance, inferInstance,
    rfl, h.card_K, ⟨e'⟩⟩))

theorem orderOf_tb : orderOf d.tb = 2 := by
  have htN : d.tN * d.tN = 1 := Subtype.ext h.t_mul_t
  refine orderOf_eq_prime ?_ fun h1 => d.t_not_mem_A ((d.piA_eq_one_iff _).1 h1)
  rw [pow_two, ← map_mul, htN, map_one]

theorem tb_mem_centralizer_N1b : d.tb ∈ centralizer (d.bar (h.N .i1) : Set d.Xb) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨n, hn, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (h.t_commute_L (h.N_le_L _ (mem_subgroupOf.1 hn))).symm

theorem N1b_le_centralizer_tb : d.bar (h.N .i1) ≤ centralizer ({d.tb} : Set d.Xb) := fun n hn =>
  mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 d.tb_mem_centralizer_N1b n hn)

theorem exists_C_of_commute_tb {x : d.NA} (hx : d.piA x * d.tb = d.tb * d.piA x) :
    ∃ j : d.NA, (j : G) ∈ h.C ∧ d.piA j = d.piA x := by
  rw [← map_mul, ← map_mul, d.piA_eq_iff] at hx
  have hxt : h.t⁻¹ * (x : G)⁻¹ * h.t * x ∈ d.A := by
    simpa [mul_assoc] using hx
  have hsec : (x : G) ∈ sectionCentralizer (zpowers h.t ⊔ d.A) d.A :=
    (mem_sectionCentralizer_zpowers_sup_iff (d.J_le_normalizer_A h.t_mem_J)).2 ⟨x.2, hxt⟩
  rw [d.miyamoto_1_3_A.2] at hsec
  have hsec' : (x : G) ∈ ((d.A ⊔ (normalizer (d.A : Set G) ⊓ centralizer ({h.t} : Set G)) :
      Subgroup G) : Set G) := hsec
  rw [coe_mul_of_right_le_normalizer_left d.A _ inf_le_left, Set.mem_mul] at hsec'
  obtain ⟨a, ha, j, hj, haj⟩ := hsec'
  refine ⟨⟨j, hj.1⟩, hj.2, ?_⟩
  rw [d.piA_eq_iff]
  show j⁻¹ * x ∈ d.A
  rw [← haj, ← mul_assoc]
  have := (mem_normalizer_iff.1 (inv_mem hj.1) a).1 ha
  rw [inv_inv] at this
  simpa [mul_assoc] using this

theorem normal_N1b : ((d.bar (h.N .i1)).subgroupOf (centralizer ({d.tb} : Set d.Xb))).Normal := by
  refine (normal_subgroupOf_iff_le_normalizer d.N1b_le_centralizer_tb).2 ?_
  have key : ∀ xb ∈ centralizer ({d.tb} : Set d.Xb), ∀ nb ∈ d.bar (h.N .i1),
      xb * nb * xb⁻¹ ∈ d.bar (h.N .i1) := by
    intro xb hxb nb hnb
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective d.AN xb
    obtain ⟨j, hjC, hjx⟩ := d.exists_C_of_commute_tb (mem_centralizer_singleton_iff.1 hxb)
    have hjJ : (j : G) ∈ h.J := d.normalizer_A_inf_C_le_J ⟨j.2, hjC⟩
    obtain ⟨n, hn, rfl⟩ := hnb
    have hmem := h.conj_J_mem_R_sup_N1 hjJ (mem_subgroupOf.1 hn)
    obtain ⟨r, hr, m, hm, hrm⟩ := h.exists_mul_of_mem_R_sup_N1 hmem
    refine ⟨⟨m, d.N1_le_NA hm⟩, mem_subgroupOf.2 hm, ?_⟩
    rw [← hjx, ← map_inv, ← map_mul, ← map_mul, d.piA_eq_iff]
    show m⁻¹ * ((j : G) * n * (j : G)⁻¹) ∈ d.A
    rw [hrm]
    have hrA : r ∈ d.A := d.R_le_A hr
    have := (mem_normalizer_iff.1 (inv_mem (d.N1_le_NA hm)) r).1 hrA
    rw [inv_inv] at this
    simpa [mul_assoc] using this
  intro xb hxb
  refine mem_normalizer_of_conj_mem (key xb hxb) fun nb hnb => ?_
  have := key xb⁻¹ (inv_mem hxb) nb hnb
  rwa [inv_inv] at this

theorem mem_zpowers_tb {xb : d.Xb} (hxN : xb ∈ centralizer (d.bar (h.N .i1) : Set d.Xb))
    (hxt : xb * d.tb = d.tb * xb) {k : ℕ} (hxk : xb ^ 2 ^ k = 1) : xb ∈ zpowers d.tb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective d.AN xb
  set x' : G := (x : G) with hx'
  have htA := d.J_le_normalizer_A h.t_mem_J
  have hxkA : x' ^ 2 ^ k ∈ d.A := by
    have := (d.piA_eq_one_iff (x ^ 2 ^ k)).1 (by rw [map_pow]; exact hxk)
    simpa using this
  obtain ⟨m, hm⟩ := d.isPGroup_A ⟨_, hxkA⟩
  have hxm : x' ^ 2 ^ (k + m) = 1 := by
    have := congrArg Subtype.val hm
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
    rw [pow_add, pow_mul, this]
  have hxt' : h.t⁻¹ * x'⁻¹ * h.t * x' ∈ d.A := by
    have := (d.piA_eq_iff (x * d.tN) (d.tN * x)).1 (by rw [map_mul, map_mul]; exact hxt)
    simpa [mul_assoc] using this
  have hy : h.t⁻¹ * (x' * h.t * x'⁻¹) ∈ d.A := by
    have e : h.t⁻¹ * (x' * h.t * x'⁻¹) = x' * (h.t⁻¹ * x'⁻¹ * h.t * x')⁻¹ * x'⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.1 x.2 _).1 (inv_mem hxt')
  have hinv : x' * h.t * x'⁻¹ ∈
      {y | (∃ z ∈ d.A, y = h.t * z) ∧ orderOf y = 2} := by
    refine ⟨⟨_, hy, by group⟩, ?_⟩
    rw [show x' * h.t * x'⁻¹ = MulAut.conj x' h.t by rfl, MulEquiv.orderOf_eq, h.ht]
  rw [d.miyamoto_1_3_A.1] at hinv
  obtain ⟨a, ha, hxa⟩ := hinv
  set j : G := a * x' with hj
  have hjN : j ∈ d.NA := mul_mem (le_normalizer ha) x.2
  have hjC : j ∈ h.C := by
    rw [mem_centralizer_singleton_iff]
    calc j * h.t = a * (x' * h.t * x'⁻¹) * x' := by rw [hj]; group
      _ = a * (a⁻¹ * h.t * a) * x' := by rw [hxa]
      _ = h.t * j := by rw [hj]; group
  have hjJ : j ∈ h.J := d.normalizer_A_inf_C_le_J ⟨hjN, hjC⟩
  have hz2 : IsPGroup 2 (zpowers x') := by
    rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := mem_zpowers_iff.1 hy
    refine ⟨k + m, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxm, one_zpow]
  have hAx2 : IsPGroup 2 (d.A ⊔ zpowers x' : Subgroup G) :=
    d.isPGroup_A.to_sup_of_normal_left' hz2 (zpowers_le.2 x.2)
  obtain ⟨n, hn⟩ := hAx2 ⟨j, mul_mem (mem_sup_left ha) (mem_sup_right (mem_zpowers _))⟩
  have hjn : j ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hpij : d.piA ⟨j, hjN⟩ = d.piA x := by
    rw [d.piA_eq_iff]
    show (a * x')⁻¹ * x' ∈ d.A
    have := (mem_normalizer_iff.1 (inv_mem x.2) a⁻¹).1 (inv_mem ha)
    rw [inv_inv] at this
    simpa [mul_assoc] using this
  have hjR : ∀ c ∈ h.N .i1, ⁅j, c⁆ ∈ h.R := by
    intro c hc
    have hcN := d.N1_le_NA hc
    have hcomm : d.piA x * d.piA ⟨c, hcN⟩ = d.piA ⟨c, hcN⟩ * d.piA x :=
      (mem_centralizer_iff.1 hxN (d.piA ⟨c, hcN⟩) ⟨⟨c, hcN⟩, mem_subgroupOf.2 hc, rfl⟩).symm
    have h1 : d.piA ⁅(⟨j, hjN⟩ : d.NA), (⟨c, hcN⟩ : d.NA)⁆ = 1 := by
      rw [map_commutatorElement, hpij, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm
    have hA : ⁅j, c⁆ ∈ d.A := by
      have := (d.piA_eq_one_iff _).1 h1
      simpa [commutatorElement_def] using this
    have hL : ⁅j, c⁆ ∈ h.L := by
      have hjL : j ∈ normalizer (h.L : Set G) := h.centralizer_le_normalizer hjC
      rw [commutatorElement_def]
      exact mul_mem ((mem_normalizer_iff.1 hjL c).1 (h.N_le_L _ hc)) (inv_mem (h.N_le_L _ hc))
    exact d.mem_R_of_mem_A_of_mem_L hA hL
  have hjRt := h.mem_R_sup_t_of_comm_mem_R hjJ hjn hjR
  have htR : zpowers h.t ≤ normalizer (h.R : Set G) := zpowers_le.2 (mem_inf.1 h.t_mem_J).2
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ htR, Set.mem_mul] at hjRt
  obtain ⟨r, hr, c, hc, hrc⟩ := hjRt
  obtain ⟨e, rfl⟩ := mem_zpowers_iff.1 hc
  have hpi : d.piA x = d.tb ^ e := by
    rw [← hpij, ← map_zpow, d.piA_eq_iff]
    show j⁻¹ * (h.t ^ e) ∈ d.A
    rw [← hrc]
    have hte : h.t ^ e ∈ normalizer (d.A : Set G) := zpow_mem htA e
    have := (mem_normalizer_iff.1 (inv_mem hte) r⁻¹).1 (inv_mem (d.R_le_A hr))
    rw [inv_inv] at this
    simpa [mul_assoc] using this
  show d.piA x ∈ zpowers d.tb
  rw [hpi]
  exact zpow_mem_zpowers _ _

theorem rank_N1b (P : Subgroup d.Xb) (hP : P ≤ centralizer (d.bar (h.N .i1) : Set d.Xb))
    (hP2 : IsPGroup 2 P) : Nat.card P ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y : Subgroup d.Xb := centralizer (d.bar (h.N .i1) : Set d.Xb) with hY
  have htt : d.tb * d.tb = 1 := by
    rw [← pow_two, ← d.orderOf_tb, pow_orderOf_eq_one]
  have htY : zpowers d.tb ≤ Y := zpowers_le.2 d.tb_mem_centralizer_N1b
  have hz2 : IsPGroup 2 (zpowers d.tb) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, d.orderOf_tb, pow_one])
  obtain ⟨S, hSY, hPS⟩ := exists_isSylowOf_ge hP hP2
  obtain ⟨S', hS'Y, htS'⟩ := exists_isSylowOf_ge htY hz2
  have hS'le : S' ≤ zpowers d.tb := by
    refine le_zpowers_of_inf_centralizer_le hS'Y.isPGroup htt (htS' (mem_zpowers _)) ?_
    rintro x ⟨hxS', hxt⟩
    obtain ⟨k, hk⟩ := hS'Y.isPGroup ⟨x, hxS'⟩
    exact d.mem_zpowers_tb (hS'Y.le hxS') (mem_centralizer_singleton_iff.1 hxt) (k := k)
      (by simpa using congrArg Subtype.val hk)
  calc Nat.card P ≤ Nat.card S := Subgroup.card_le_of_le hPS
    _ = Nat.card S' := by rw [hSY.card_eq, hS'Y.card_eq]
    _ ≤ Nat.card (zpowers d.tb) := Subgroup.card_le_of_le hS'le
    _ = 2 := by rw [Nat.card_zpowers, d.orderOf_tb]

end LevelOneData

end CFSG.LocalAnalysis.EvenBN.TwoF4

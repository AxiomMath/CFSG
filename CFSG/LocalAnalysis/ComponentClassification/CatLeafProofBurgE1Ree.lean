module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1Glue
public import CFSG.LieType.Ree.SmallReeOuterThreeKernel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSmallReeTorus
public import CFSG.Walter.Ree.Model.Fusion

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.Walter.Ree.Model
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem pPrimeCore_eq_bot_of_sup_simple {C : Type*} [Group C] [Finite C] {N : Subgroup C}
    [hNn : N.Normal] [IsSimpleGroup N] (hnab : ∃ x y : N, x * y ≠ y * x) {h : C}
    (hh : h ∈ Subgroup.center C) (hh2 : h ^ 2 = 1) (hsup : Subgroup.zpowers h ⊔ N = ⊤) :
    pPrimeCore 2 C = ⊥ := by
  have hOn : (pPrimeCore 2 C).Normal := pPrimeCore_normal
  have hOodd : Odd (Nat.card (pPrimeCore 2 C)) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hZN : Subgroup.center N = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center N) with hc | hc
    · exact hc
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnab
      exact hxy (Subgroup.mem_center_iff.mp (hc ▸ Subgroup.mem_top y) x)
  have hdis : Disjoint (pPrimeCore 2 C) N := by
    have := hOn.subgroupOf N
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((pPrimeCore 2 C).subgroupOf N) with hM | hM
    · exact Subgroup.subgroupOf_eq_bot.1 hM
    · exfalso
      have hNO : N ≤ pPrimeCore 2 C := Subgroup.subgroupOf_eq_top.1 hM
      have hNodd : Odd (Nat.card N) := Odd.of_dvd_nat hOodd (Subgroup.card_dvd_of_le hNO)
      have hsolv : Group.IsSolvable N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hNodd
      obtain ⟨x, y, hxy⟩ := hnab
      exact hxy (IsSimpleGroup.comm_iff_isSolvable.2 hsolv x y)
  have hle : pPrimeCore 2 C ≤ Subgroup.zpowers h := by
    intro o ho
    have hoC : o ∈ (Subgroup.zpowers h ⊔ N : Subgroup C) := hsup ▸ Subgroup.mem_top o
    rw [← SetLike.mem_coe, Subgroup.mul_normal] at hoC
    obtain ⟨x, hx, n, hn, rfl⟩ := hoC
    dsimp only at ho ⊢
    have hxZ : x ∈ Subgroup.center C := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact Subgroup.zpow_mem _ hh k
    have hnZ : (⟨n, hn⟩ : N) ∈ Subgroup.center N := by
      rw [Subgroup.mem_center_iff]
      intro m
      refine Subtype.ext ?_
      change (m : C) * n = n * m
      have h1 : x * n * m = m * (x * n) :=
        (Subgroup.commute_of_normal_of_disjoint _ _ hOn hNn hdis (x * n) m ho m.2).eq
      have h2 : (m : C) * (x * n) = x * (m * n) := by
        rw [← mul_assoc, Subgroup.mem_center_iff.1 hxZ m, mul_assoc]
      exact (mul_left_cancel ((mul_assoc x n m).symm.trans (h1.trans h2))).symm
    rw [hZN, Subgroup.mem_bot] at hnZ
    have hn1 : n = 1 := congrArg Subtype.val hnZ
    rw [hn1, mul_one]
    exact hx
  have hdvd : Nat.card (pPrimeCore 2 C) ∣ 2 := by
    refine (Subgroup.card_dvd_of_le hle).trans ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hh2
  have h1 : Nat.card (pPrimeCore 2 C) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact h
    · rw [h] at hOodd
      exact absurd hOodd (by decide)
  exact Subgroup.eq_bot_of_card_eq _ h1

theorem map_fixedSubgroup_conj {M : Type*} [Group M] (Γ : Subgroup M) (t : Γ) :
    (fixedSubgroup (MulAut.conj t)).map Γ.subtype = Γ ⊓ Subgroup.centralizer {(t : M)} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine Subgroup.mem_inf.2 ⟨x.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : t * x * t⁻¹ = x := hx
    have h2 : (t : M) * x * (t : M)⁻¹ = x := congrArg Subtype.val h1
    calc ((x : M) * t) = (t : M) * x * (t : M)⁻¹ * t := by rw [h2]
      _ = t * x := by group
  · intro hy
    obtain ⟨hyΓ, hyc⟩ := Subgroup.mem_inf.1 hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hyc
    refine ⟨⟨y, hyΓ⟩, ?_, rfl⟩
    change t * ⟨y, hyΓ⟩ * t⁻¹ = ⟨y, hyΓ⟩
    refine Subtype.ext ?_
    change (t : M) * y * (t : M)⁻¹ = y
    rw [← hyc, mul_inv_cancel_right]

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime] {a : ℕ}

theorem pPrimeCore_smallReeInvCentralizer
    (ha : 1 ≤ a) (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    pPrimeCore 2 (smallReeInvCentralizer a K) = ⊥ := by
  classical
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  set C := smallReeInvCentralizer a K with hCdef
  set h := smallReeH a K (-1) with hh
  obtain ⟨ψ, hψC, -, -, -, -, -, ⟨hsup, -, hcent⟩, e, -⟩ :=
    small_Ree_involution_centralizer_PSL2_structure a K hK w₀ hw₀
  rw [← hh, ← hCdef] at hsup
  rw [← hh] at hcent
  simp only [← hCdef] at hψC
  have hLC : ψ.range ≤ C := by
    rintro _ ⟨x, rfl⟩
    exact hψC x
  have htC : h ∈ C := hsup ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers h)
  set N := ψ.range.subgroupOf C with hNdef
  have hNn : N.Normal := by
    rw [hNdef, Subgroup.normal_subgroupOf_iff_le_normalizer hLC, ← hsup]
    exact sup_le (hcent.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  have hT : Subgroup.zpowers (⟨h, htC⟩ : C) ⊔ N = ⊤ := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hNdef, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hLC, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hsup
  have hq27 : 27 ≤ Nat.card K := by
    rw [hK]
    calc 27 = 3 ^ (2 * 1 + 1) := by norm_num
      _ ≤ 3 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hK2 : Nat.card K ≠ 2 := by omega
  have hK3 : Nat.card K ≠ 3 := by omega
  let e' : N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    (Subgroup.subgroupOfEquivOfLe hLC).trans e.symm
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.projectiveSpecialLinear_simple 2 K
      le_rfl (Or.inr hK2) (Or.inr hK3)
  have : IsSimpleGroup N := e'.isSimpleGroup
  have hnc : ∃ x y : N, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ :=
      CFSG.ComponentClassification.CatalogueBSmallRee.projectiveSpecialLinear_two_nonabelian K
        hK2 hK3
    refine ⟨e'.symm x, e'.symm y, fun hc => hxy ?_⟩
    simpa using congrArg e' hc
  have hhZ : (⟨h, htC⟩ : C) ∈ Subgroup.center C := by
    rw [Subgroup.mem_center_iff]
    intro c
    refine Subtype.ext ?_
    have hc := (Subgroup.mem_inf.1 c.2).2
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    exact hc
  have hh2 : (⟨h, htC⟩ : C) ^ 2 = 1 := by
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, sq]
    exact smallReeH_neg_one_mul_self
  exact pPrimeCore_eq_bot_of_sup_simple hnc hhZ hh2 hT

theorem exists_eq_conj_of_orderOf_eq_two_reeGamma
    (ha : 1 ≤ a) (hK : Nat.card K = 3 ^ (2 * a + 1))
    (α : MulAut (ReeTag.G2.reeGamma K a)) (hα : orderOf α = 2) :
    ∃ t : ReeTag.G2.reeGamma K a, orderOf t = 2 ∧ α = MulAut.conj t := by
  obtain ⟨-, -, -, -, hodd, -⟩ := small_Ree_outer_three_kernel_field_complement a ha K hK
  have hZ := ReeTag.center_reeGamma_G2_eq_bot (K := K) (a := a) hK
  have hinj : Function.Injective (MulAut.conj : ReeTag.G2.reeGamma K a →*
      MulAut (ReeTag.G2.reeGamma K a)) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgZ : g ∈ Subgroup.center (ReeTag.G2.reeGamma K a) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h3 := congrArg (fun φ : MulAut (ReeTag.G2.reeGamma K a) => φ x) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      calc x * g = g * x * g⁻¹ * g := by rw [h3]
        _ = g * x := by group
    rw [hZ, Subgroup.mem_bot] at hgZ
    exact hgZ
  have : Finite (Outer (ReeTag.G2.reeGamma K a)) := Nat.finite_of_card_ne_zero hodd.pos.ne'
  set α' : Outer (ReeTag.G2.reeGamma K a) := QuotientGroup.mk α with hα'
  have h1 : orderOf α' ∣ 2 := by
    rw [← hα]
    exact orderOf_map_dvd (QuotientGroup.mk' _) α
  have h2 : orderOf α' ∣ Nat.card (Outer (ReeTag.G2.reeGamma K a)) := orderOf_dvd_natCard α'
  have h3 : orderOf α' = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact h
    · rw [h] at h2
      exact absurd (Odd.of_dvd_nat hodd h2) (by decide)
  rw [orderOf_eq_one_iff, hα', QuotientGroup.eq_one_iff] at h3
  obtain ⟨t, rfl⟩ := h3
  exact ⟨t, (orderOf_injective _ hinj t).symm.trans hα, rfl⟩

theorem burgOddCoreRow_reeGamma
    (ha : 1 ≤ a) (hK : Nat.card K = 3 ^ (2 * a + 1))
    (hpw : ∀ t : ReeTag.G2.reeGamma K a, orderOf t = 2 →
      ∀ β : MulAut (ReeTag.G2.reeGamma K a), Odd (orderOf β) →
        MulAut.conj t * β = β * MulAut.conj t →
          (∀ x ∈ fixedSubgroup (MulAut.conj t), β x = x) → β = 1) :
    BurgOddCoreRow (ReeTag.G2.reeGamma K a) := by
  intro α hα
  obtain ⟨t, ht, rfl⟩ := exists_eq_conj_of_orderOf_eq_two_reeGamma ha hK α hα
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  have ht' : orderOf (t : ModGL ReeTag.G2.tag K) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact ht
  obtain ⟨g, hgΓ, hgt⟩ :=
    (small_Ree_prime_field_involution_fusion a K hK w₀ hw₀).2.2.2.2.2 t t.2 ht'
  set g' : ReeTag.G2.reeGamma K a := ⟨g, hgΓ⟩
  have hh₀ : smallReeH a K (-1) ∈ ReeTag.G2.reeGamma K a :=
    hgt ▸ mul_mem (mul_mem hgΓ t.2) (inv_mem hgΓ)
  set h₀ : ReeTag.G2.reeGamma K a := ⟨smallReeH a K (-1), hh₀⟩
  have hgh : MulAut.conj g' t = h₀ := Subtype.ext hgt
  have hconj : MulAut.conj g' * MulAut.conj t * (MulAut.conj g')⁻¹ = MulAut.conj h₀ := by
    rw [← map_inv, ← map_mul, ← map_mul, ← hgh, MulAut.conj_apply]
  refine burgOddCoreFor_of_conj (MulAut.conj g') (MulAut.conj t) ?_
  rw [hconj]
  refine ⟨?_, hpw h₀ ?_⟩
  · let e : fixedSubgroup (MulAut.conj h₀) ≃* smallReeInvCentralizer a K :=
      ((fixedSubgroup (MulAut.conj h₀)).equivMapOfInjective _
        (ReeTag.G2.reeGamma K a).subtype_injective).trans
        (MulEquiv.subgroupCongr (map_fixedSubgroup_conj _ h₀))
    have h1 := pPrimeCore_map_iso 2 e.symm
    rw [pPrimeCore_smallReeInvCentralizer ha hK, Subgroup.map_bot] at h1
    exact h1.symm
  · rw [← hgh, MulEquiv.orderOf_eq]
    exact ht

end CFSG.ComponentClassification.CatLeafProof

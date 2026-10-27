module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcCore
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcTw
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeOuter
public import CFSG.Sporadic.Schreier.J4SSylowBase

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.Walter.Ree.Model

theorem pPrimeCore_smallReeInvCentralizer
    {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]
    (hK : Nat.card K = 3 ^ (2 * a + 1)) : pPrimeCore 2 (smallReeInvCentralizer a K) = ⊥ := by
  classical
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  obtain ⟨ψ, hψC, -, -, -, -, -, hd, e, -⟩ :=
    small_Ree_involution_centralizer_PSL2_structure a K hK w₀ hw₀
  set C := smallReeInvCentralizer a K with hCdef
  set h := smallReeH a K (-1) with hh
  have hLC : ψ.range ≤ C := by
    rintro _ ⟨x, rfl⟩
    exact hψC x
  have hq27 : 27 ≤ Nat.card K := by
    rw [hK]
    calc 27 = 3 ^ (2 * 1 + 1) := by norm_num
      _ ≤ 3 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  have hLs : IsSimpleGroup ψ.range := e.symm.isSimpleGroup
  have hLnc : ∃ x y : ψ.range, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ :=
      CatalogueBSmallRee.projectiveSpecialLinear_two_nonabelian K (by omega) (by omega)
    exact ⟨e x, e y, fun hc => hxy (e.injective (by rw [map_mul, map_mul, hc]))⟩
  have hZL : ∀ z ∈ ψ.range, (∀ y ∈ ψ.range, z * y = y * z) → z = 1 := by
    intro z hz hzc
    have hcen := center_eq_bot_of_simple' hLnc
    have hzZ : (⟨z, hz⟩ : ψ.range) ∈ center ψ.range :=
      mem_center_iff.2 fun y => Subtype.ext (hzc y y.2).symm
    rw [hcen, mem_bot] at hzZ
    exact congrArg Subtype.val hzZ
  have hOL : pPrimeCore 2 ψ.range = ⊥ := pPrimeCore_eq_bot_of_isSimpleGroup hLnc
  have hd' : Walter.JT.IsInternalDirectProduct ψ.range (zpowers h) C :=
    ⟨by rw [sup_comm]; exact hd.1, hd.2.1.symm, Subgroup.le_centralizer_iff.1 hd.2.2⟩
  have hh2 : h ^ 2 = 1 := by
    rw [sq]
    exact smallReeH_neg_one_mul_self
  rw [pPrimeCore_eq_bot_iff]
  intro N hN hNodd
  have hNodd' : Odd (Nat.card N) := Nat.coprime_two_left.1 hNodd
  have hNC : ∀ c ∈ C, ∀ y ∈ N.map C.subtype, c * y * c⁻¹ ∈ N.map C.subtype := by
    rintro c hc _ ⟨n, hn, rfl⟩
    exact ⟨⟨c, hc⟩ * n * ⟨c, hc⟩⁻¹, hN.conj_mem n hn _, rfl⟩
  have hNL : ∀ x : ModGL ReeTag.G2.tag K, x ∈ N.map C.subtype → x ∈ ψ.range → x = 1 := by
    intro x hxN hxL
    set M := (N.map C.subtype ⊓ ψ.range).subgroupOf ψ.range with hM
    have hMn : M.Normal := ⟨fun m hm l => by
      rw [hM, Subgroup.mem_subgroupOf] at hm ⊢
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mem_inf.2 ⟨hNC _ (hLC l.2) _ (Subgroup.mem_inf.1 hm).1,
        mul_mem (mul_mem l.2 (Subgroup.mem_inf.1 hm).2) (inv_mem l.2)⟩⟩
    have hMcard : Nat.Coprime 2 (Nat.card M) := by
      have h1 : Nat.card M = Nat.card (N.map C.subtype ⊓ ψ.range : Subgroup _) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
      have h2 : Nat.card (N.map C.subtype ⊓ ψ.range : Subgroup _) ∣
          Nat.card (N.map C.subtype) := Subgroup.card_dvd_of_le inf_le_left
      have h3 : Nat.card (N.map C.subtype) = Nat.card N :=
        Subgroup.card_map_of_injective C.subtype_injective
      rw [h1]
      exact hNodd.coprime_dvd_right (h3 ▸ h2)
    have hM0 := (pPrimeCore_eq_bot_iff.1 hOL) M hMn hMcard
    have hxM : (⟨x, hxL⟩ : ψ.range) ∈ M := by
      rw [hM, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_inf.2 ⟨hxN, hxL⟩
    rw [hM0, Subgroup.mem_bot] at hxM
    exact congrArg Subtype.val hxM
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  have hnN : (n : ModGL ReeTag.G2.tag K) ∈ N.map C.subtype := ⟨n, hn, rfl⟩
  have hcomm : ∀ y ∈ ψ.range, (n : ModGL ReeTag.G2.tag K) * y = y * n := by
    intro y hy
    have h1 : (n : ModGL ReeTag.G2.tag K) * y * (n : ModGL ReeTag.G2.tag K)⁻¹ * y⁻¹ = 1 := by
      refine hNL _ ?_ ?_
      · have e1 : (n : ModGL ReeTag.G2.tag K) * y * (n : ModGL ReeTag.G2.tag K)⁻¹ * y⁻¹ =
            (n : ModGL ReeTag.G2.tag K) * (y * (n : ModGL ReeTag.G2.tag K)⁻¹ * y⁻¹) := by group
        rw [e1]
        exact mul_mem hnN (hNC y (hLC hy) _ (inv_mem hnN))
      · exact mul_mem (hd'.conj_mem_left n.2 hy) (inv_mem hy)
    calc (n : ModGL ReeTag.G2.tag K) * y =
        ((n : ModGL ReeTag.G2.tag K) * y * (n : ModGL ReeTag.G2.tag K)⁻¹ * y⁻¹) * (y * n) := by
          group
      _ = y * n := by rw [h1, one_mul]
  have hnh := hd'.mem_right_of_centralizes hZL n.2 hcomm
  have hno : Odd (orderOf (n : ModGL ReeTag.G2.tag K)) := by
    rw [Subgroup.orderOf_coe]
    exact odd_orderOf_of_mem hNodd' hn
  exact Subtype.ext (Exc.eq_one_of_odd_of_mem_zpowers hh2 hnh hno)

theorem smallReeInnerCoreInput :
    SmallReeInnerCoreInput := by
  intro a ha K _ _ _ hK t ht2 ht1
  classical
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  have hZ : center (ReeTag.G2.reeGamma K a) = ⊥ := (small_Ree_fixed_group_center_trivial a K hK).1
  have hto : orderOf (t : ModGL ReeTag.G2.tag K) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime ht2 ht1
  obtain ⟨g, hgΓ, hgt⟩ :=
    (small_Ree_prime_field_involution_fusion a K hK w₀ hw₀).2.2.2.2.2 t t.2 hto
  have hhΓ : smallReeH a K (-1) ∈ ReeTag.G2.reeGamma K a := by
    rw [← hgt]
    exact mul_mem (mul_mem hgΓ t.2) (inv_mem hgΓ)
  have hψ : MulAut.conj (⟨g, hgΓ⟩ : ReeTag.G2.reeGamma K a) * MulAut.conj t *
      (MulAut.conj (⟨g, hgΓ⟩ : ReeTag.G2.reeGamma K a))⁻¹ =
        MulAut.conj (⟨smallReeH a K (-1), hhΓ⟩ : ReeTag.G2.reeGamma K a) := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hgt
  refine outerCoreAt_of_conj hψ ?_
  have hCΓ : smallReeInvCentralizer a K ≤ ReeTag.G2.reeGamma K a := inf_le_left
  refine outerCoreAt_of_pPrimeCore hZ
    (F := (smallReeInvCentralizer a K).subgroupOf (ReeTag.G2.reeGamma K a)) (fun s => ?_)
    (pPrimeCore_eq_bot_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hCΓ)
      (pPrimeCore_smallReeInvCentralizer ha hK))
    fun a' b' _ _ => commutator_mem_range_conj_of_forall
      (φ := LiteratureLocal.SmallRee.frobeniusΓ)
      (fun c => LiteratureLocal.SmallRee.exists_eq_conj_mul_frobeniusΓ_pow ha hK c) a' b'
  rw [Subgroup.mem_subgroupOf, MulAut.conj_apply, ← Subtype.coe_inj, smallReeInvCentralizer,
    Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, mul_inv_eq_iff_eq_mul]
  exact ⟨fun h => ⟨s.2, h.symm⟩, fun h => h.2.symm⟩

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc

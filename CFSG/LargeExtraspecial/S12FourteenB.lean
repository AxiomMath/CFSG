module

public import CFSG.LargeExtraspecial.S12Fourteen
public import CFSG.LargeExtraspecial.S12Elim

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

universe u

namespace Setting

variable {G : Type u} [Group G] [Finite G] (S : Setting G)

@[expose] noncomputable def innerSp12 (g : G) : Submodule (ZMod 2) S.Qt :=
  S.clSub (S.QG ⊓ S.Qa g) ⊔ Submodule.span (ZMod 2) {S.cl (g * S.z * g⁻¹)}

@[expose] noncomputable def unipSub12 (g : G) : Subgroup S.O where
  carrier := {y | (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) ∧
    ∀ w ∈ S.innerSp12 g, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈
      Submodule.span (ZMod 2) {S.cl (g * S.z * g⁻¹)}}
  mul_mem' {x y} hx hy := by
    refine ⟨?_, fun w hw => ?_⟩
    · change ((x * y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) _ = _
      rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hy.1, hx.1]
    · change ((x * y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ _
      rw [Subgroup.coe_mul, LinearEquiv.mul_apply]
      have hyw := hy.2 w hw
      have hyW : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ S.innerSp12 g := by
        have := (S.innerSp12 g).add_mem hw ((le_sup_right : _ ≤ S.innerSp12 g) hyw)
        rwa [add_sub_cancel] at this
      have h1 := hx.2 _ hyW
      have : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) w) - w =
          ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) w) -
            (y : S.Qt ≃ₗ[ZMod 2] S.Qt) w) + ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) := by abel
      rw [this]
      exact Submodule.add_mem _ h1 hyw
  one_mem' := ⟨rfl, fun w _ => by
    change w - w ∈ _
    rw [sub_self]
    exact Submodule.zero_mem _⟩
  inv_mem' {x} hx := by
    have hxa := hx.1
    have hinv : ∀ v, ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
        (x : S.Qt ≃ₗ[ZMod 2] S.Qt).symm v := fun v => rfl
    refine ⟨?_, fun w hw => ?_⟩
    · rw [hinv]
      conv_lhs => rw [← hxa]
      exact (x : S.Qt ≃ₗ[ZMod 2] S.Qt).symm_apply_apply _
    · rw [hinv]
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hx.2 w hw)
      have e : (x : S.Qt ≃ₗ[ZMod 2] S.Qt).symm w - w = -(c • S.cl (g * S.z * g⁻¹)) := by
        have h1 := congrArg (x : S.Qt ≃ₗ[ZMod 2] S.Qt).symm hc
        rw [map_smul, map_sub, LinearEquiv.symm_apply_apply] at h1
        have h2 : (x : S.Qt ≃ₗ[ZMod 2] S.Qt).symm (S.cl (g * S.z * g⁻¹)) =
            S.cl (g * S.z * g⁻¹) := by
          conv_lhs => rw [← hxa]
          exact (x : S.Qt ≃ₗ[ZMod 2] S.Qt).symm_apply_apply _
        rw [h2] at h1
        rw [h1]
        abel
      rw [e]
      exact Submodule.neg_mem _ (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _))

variable {S}

omit [Finite G] in
theorem innerSp12_eq {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) :
    S.innerSp12 g = S.clSub (S.QG ⊓ S.Qa g) := by
  refine sup_eq_left.mpr ?_
  rw [Submodule.span_singleton_le_iff_mem]
  exact S.s12_cl_a_mem_clSub haQ

theorem mem_unipSub12_of_mem_Ebar12 {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {t : S.O} (hS : S.S12Standing g t)
    (hline : ∀ u ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt), u ≠ 0 →
      ∃ h : S.M, ((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = u)
    (hinter : ∀ h : S.M, ((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ∈
      S.clSub (S.QG ⊓ S.Qa g) →
      ((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹))
    {τ : S.O} (hτ : τ ∈ S.Ebar12 g) (hτN : τ ∈ normalizer (S.Lbar g : Set S.O)) :
    τ ∈ S.unipSub12 g := by
  have hτM := Ebar12_subset_Mbar hτ
  have hfix := (mem_normalizer_Lbar_iff_fix haQ hne hn hτM).mp hτN
  refine ⟨hfix, fun w hw => ?_⟩
  rw [innerSp12_eq haQ] at hw
  obtain ⟨hτ', rfl⟩ := hτM
  have hτw := rho_mem_clSub_of_fix haQ hne hτ' hfix hw
  set u := ((S.ρ hτ' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w with hu
  by_cases hu0 : u = 0
  · rw [hu0]
    exact Submodule.zero_mem _
  have huW : u ∈ S.clSub (S.QG ⊓ S.Qa g) := Submodule.sub_mem _ hτw hw
  have huc : u ∈ commSpace ((S.ρ hτ' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := sub_mem_commSpace _ _
  obtain ⟨x, hx, hxe⟩ := hS.cls _ hτ
  rw [hxe, s12_coe_conj, commSpace_conj] at huc
  obtain ⟨u', hu', hu'e⟩ := Submodule.mem_map.mp huc
  have hu'0 : u' ≠ 0 := by
    rintro rfl
    exact hu0 (by rw [← hu'e]; exact map_zero _)
  obtain ⟨h, hh⟩ := hline u' hu' hu'0
  obtain ⟨hx', hx'e⟩ := Xbar12_le_Mbar hx
  have hue : u = ((S.ρ (hx' * h) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := by
    rw [map_mul, Subgroup.coe_mul, LinearEquiv.mul_apply, hh, ← hu'e, hx'e]
    rfl
  have := hinter (hx' * h) (hue ▸ huW)
  rw [← hue] at this
  rw [this]
  exact Submodule.mem_span_singleton_self _

theorem fix_of_mem_unipSub12 {g : G} {y : S.O} (hy : y ∈ S.unipSub12 g)
    (hodd : Odd (orderOf y)) {w : S.Qt} (hw : w ∈ S.innerSp12 g) :
    (y : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hy.2 w hw)
  have hy1 : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w + c • S.cl (g * S.z * g⁻¹) := by
    rw [hc]
    abel
  have hy2 : ((y ^ 2 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
    rw [pow_two, Subgroup.coe_mul, LinearEquiv.mul_apply, hy1, map_add, map_smul, hy.1, hy1,
      add_assoc, ← add_smul, OrthoF2.zmod2_add_self c, zero_smul, add_zero]
  have hpow : ∀ k : ℕ, ((y ^ (2 * k) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add, Subgroup.coe_mul,
        LinearEquiv.mul_apply, hy2, ih]
  obtain ⟨k, hk⟩ := hodd
  have h1 : y ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one y
  have := hpow k
  calc (y : S.Qt ≃ₗ[ZMod 2] S.Qt) w
      = (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (((y ^ (2 * k) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) := by
        rw [this]
    _ = ((y ^ (2 * k + 1) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w := by
        rw [pow_succ', Subgroup.coe_mul, LinearEquiv.mul_apply]
    _ = w := by rw [h1]; rfl

structure S12Case2Data (S : Setting G) (g : G) (t : S.O) : Prop where
  line : ∀ u ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt), u ≠ 0 →
    ∃ h : S.M, ((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = u
  rank : S.S12RankThree g
  normalizer_gen : S.Xbar12 g ⊓ normalizer (S.Lbar g : Set S.O) ≤
    closure (S.Ebar12 g ∩ normalizer (S.Lbar g : Set S.O))
  odd_gen : S.Lbar g ≤
    closure {y | y ∈ S.Xbar12 g ⊓ normalizer (S.Lbar g : Set S.O) ∧ Odd (orderOf y)}

theorem mem_QG_inf_Qa_of_case2 {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {t : S.O} (hS : S.S12Standing g t)
    (hD : S.S12Case2Data g t) (hirr : ¬ S.IsReducible12) {w : G} (hw : w ∈ S.QG ⊓ S.Qa g) :
    w = 1 ∨ w = g * S.z * g⁻¹ ∨ w = S.z ∨ w = S.z * (g * S.z * g⁻¹) := by
  have hinter := timmesfeld_12_14_inter haQ hne hirr hD.rank
  have hU : S.Xbar12 g ⊓ normalizer (S.Lbar g : Set S.O) ≤ S.unipSub12 g := by
    refine hD.normalizer_gen.trans ((closure_le _).mpr fun τ hτ => ?_)
    exact mem_unipSub12_of_mem_Ebar12 haQ hne hn hS hD.line hinter hτ.1 hτ.2
  have hL : S.Lbar g ≤ S.fixSub12 (S.innerSp12 g) := by
    refine hD.odd_gen.trans ((closure_le _).mpr fun y hy => ?_)
    exact fun v hv => fix_of_mem_unipSub12 (hU hy.1) hy.2 hv
  refine S.mem_of_cl_fixed_by_L0 haQ hne hw fun y hy => ?_
  have hyL : S.ρ ⟨y, S.L0_le_M g hy⟩ ∈ S.Lbar g := S.s12_mem_Lbar.mpr ⟨y, hy, rfl⟩
  have hwW : S.cl w ∈ S.innerSp12 g := by
    rw [innerSp12_eq haQ]
    exact S.cl_mem_clSub hw hw.1
  rw [← S.ρ_cl ⟨y, S.L0_le_M g hy⟩ hw.1]
  exact hL hyL _ hwW

theorem card_Lbar_of_case2 {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {t : S.O} (hS : S.S12Standing g t)
    (hD : S.S12Case2Data g t) (hirr : ¬ S.IsReducible12) :
    Nat.card (S.Lbar g) = 2 ^ (2 * S.width - 2) := by
  classical
  set a := g * S.z * g⁻¹ with ha
  have hzQa : S.z ∈ S.Qa g := S.z_mem_Qa_of_mem_QG rfl haQ hne
  have haQa : a ∈ S.Qa g := (S.conjBy g).z_mem_QG
  have ha1 : a ≠ 1 := S.s12_conj_z_ne_one g
  have hz1 : S.z ≠ 1 := S.z_ne_one
  have hset : ((S.QG ⊓ S.Qa g : Subgroup G) : Set G) = ↑({1, a, S.z, S.z * a} : Finset G) := by
    ext w
    simp only [SetLike.mem_coe, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · intro hw
      exact mem_QG_inf_Qa_of_case2 haQ hne hn hS hD hirr hw
    · rintro (rfl | rfl | rfl | rfl)
      · exact one_mem _
      · exact ⟨haQ, haQa⟩
      · exact ⟨S.z_mem_QG, hzQa⟩
      · exact ⟨S.QG.mul_mem S.z_mem_QG haQ, (S.Qa g).mul_mem hzQa haQa⟩
  have hcard4 : Nat.card (S.QG ⊓ S.Qa g : Subgroup G) = 4 := by
    rw [← SetLike.coe_sort_coe, hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
    have h1 : (1 : G) ∉ ({a, S.z, S.z * a} : Finset G) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨Ne.symm ha1, Ne.symm hz1, fun h => ?_⟩
      apply hne
      calc a = S.z⁻¹ * (S.z * a) := by group
        _ = S.z := by rw [← h, mul_one, inv_eq_of_mul_eq_one_right S.z_mul_z]
    have h2 : a ∉ ({S.z, S.z * a} : Finset G) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨hne, fun h => hz1 ?_⟩
      calc S.z = S.z * a * a⁻¹ := by group
        _ = 1 := by rw [← h, mul_inv_cancel]
    have h3 : S.z ∉ ({S.z * a} : Finset G) := by
      simp only [Finset.mem_singleton]
      intro h
      apply ha1
      calc a = S.z⁻¹ * (S.z * a) := by group
        _ = 1 := by rw [← h, inv_mul_cancel]
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_insert_of_notMem h3, Finset.card_singleton]
  have h := S.card_Lbar_mul g
  rw [hcard4, S.card_L0 haQ hne] at h
  have h2 : 2 ^ (2 * S.width) = 2 ^ (2 * S.width - 2) * 4 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  rw [h2] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h

end Setting

end CFSG.LargeExtraspecial

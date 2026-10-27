module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialParameterSumLocal
public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicSylowComplement
public import CFSG.LocalAnalysis.SectionRank.Ccomm.LinearTwo

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage

namespace CaseIData

variable {G : Type} [Group G] [Finite G] {t s₀ d d₁ : G} {J : Subgroup G} {q : ℕ}
  {F' : Type} [Field F'] [Finite F']
  {φ : torusH G t s₀ ⧸ CFSG.pPrimeCore 2 (torusH G t s₀) ≃* CFSG.GorensteinWalter.PGL2 F'}
  (h : CaseIData G t s₀ d d₁ J q F' φ)
include h

omit [Finite G] [Field F'] [Finite F'] h in
theorem v_mem_centralizer_torusU :
    s₀ * d ∈ Subgroup.centralizer (torusU G t s₀ d : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact Subgroup.mem_centralizer_singleton_iff.mp (U_le_centralizer hu)

omit [Finite G] [Field F'] [Finite F'] h in
theorem not_scalar_of_odd {F : Type} [Field F] [Finite F]
    (ι : J ≃* Matrix.SpecialLinearGroup (Fin 2) F) {x : J} (hx1 : x ≠ 1)
    (hodd : Odd (orderOf x)) :
    ¬ ∃ c : F, ((ι x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      c • (1 : Matrix (Fin 2) (Fin 2) F) := by
  rintro ⟨c, hc⟩
  have hdet := (ι x).2
  rw [hc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
  have hsq : ι x * ι x = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, hc, Matrix.SpecialLinearGroup.coe_one, smul_mul_smul,
      mul_one, ← pow_two, hdet, one_smul]
  have hsq' : x * x = 1 := by
    apply ι.injective
    rw [map_mul, hsq, map_one]
  exact hx1 (eq_one_of_mul_self_eq_one_of_odd hodd hsq')

theorem eq_of_commute_of_mem_centralizer
    (hne : Nat.card (torusU G t s₀ d) ≠ Nat.card (torusW G t s₀)) {a b : G}
    (ha : a ∈ Subgroup.centralizer (torusU G t s₀ d : Set G))
    (hb : b ∈ Subgroup.centralizer (torusU G t s₀ d : Set G))
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) (hc : a * b = b * a) : a = b := by
  by_contra hab
  apply hne
  refine h.card_torusU_eq_of_commute ha2 hb2 hab hc ?_ ?_
  · intro u hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp ha u hu
  · intro u hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hb u hu

theorem isCyclic_of_isPGroup_le_centralizer_torusU
    (hne : Nat.card (torusU G t s₀ d) ≠ Nat.card (torusW G t s₀)) (P : Subgroup G)
    (hP2 : IsPGroup 2 P) (hPU : P ≤ Subgroup.centralizer (torusU G t s₀ d : Set G))
    (hvP : s₀ * d ∈ P) : IsCyclic P := by
  classical
  have hL := h.localData
  let vP : P := ⟨s₀ * d, hvP⟩
  have hvP2 : orderOf vP = 2 := by rw [Subgroup.orderOf_mk, h.v_orderOf]
  have hcomm2 : ∀ x y : P, orderOf x = 2 → orderOf y = 2 → x * y = y * x → x = y := by
    intro x y hx hy hxy
    rw [← Subgroup.orderOf_coe] at hx hy
    exact Subtype.ext (h.eq_of_commute_of_mem_centralizer hne (hPU x.2) (hPU y.2) hx hy
      (congrArg Subtype.val hxy))
  have : Nontrivial P := by
    refine ⟨⟨vP, 1, ?_⟩⟩
    intro h1
    rw [h1, orderOf_one] at hvP2
    exact absurd hvP2 (by decide)
  obtain ⟨z, hz2, hzc⟩ :=
    CFSG.TwoRankLowerBound.Helpers.exists_central_involution_of_two_group P hP2
  have hzv : z = vP := hcomm2 z vP hz2 hvP2 (Subgroup.mem_center_iff.mp hzc vP).symm
  have huniq : ∀ x : P, orderOf x = 2 → x = vP := by
    intro x hx
    rw [← hzv]
    exact hcomm2 x z hx hz2 (Subgroup.mem_center_iff.mp hzc x)
  have hrank := CFSG.Semidihedral.CharacteristicSL2Layer.twoRank_le_one_of_unique_involution
    vP hvP2 huniq
  rcases CFSG.TwoRankLowerBound.Helpers.rank_one_two_group_cyclic_or_quaternion P hP2 hrank with
    hcyc | ⟨k, hk, ⟨e⟩⟩
  · exact hcyc
  exfalso
  have hm2 : 2 ≤ 2 ^ (k - 2) :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (k - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : NeZero (2 ^ (k - 2)) := ⟨by omega⟩
  have hPv : ∀ x : P, (x : G) * (s₀ * d) = s₀ * d * x := by
    intro x
    have h1 : orderOf (x * vP * x⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hvP2]
    have h2 := huniq _ h1
    have h3 : x * vP = vP * x := by
      calc x * vP = x * vP * x⁻¹ * x := by group
        _ = vP * x := by rw [h2]
    exact congrArg Subtype.val h3
  obtain ⟨c, hc⟩ := isConj_iff.mp (h.conj_t (s₀ * d) h.v_orderOf)
  have hPC : ∀ x : P, c * (x : G) * c⁻¹ ∈ C t := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff, ← hc]
    calc c * (x : G) * c⁻¹ * (c * (s₀ * d) * c⁻¹) = c * ((x : G) * (s₀ * d)) * c⁻¹ := by group
      _ = c * ((s₀ * d) * (x : G)) * c⁻¹ := by rw [hPv x]
      _ = c * (s₀ * d) * c⁻¹ * (c * (x : G) * c⁻¹) := by group
  have hPJ4 : ∀ x : P, orderOf x = 4 → c * (x : G) * c⁻¹ ∈ J := by
    intro x hx
    apply h.four_mem _ (hPC x)
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hx]
  have hPJ : ∀ x : P, c * (x : G) * c⁻¹ ∈ J := by
    intro x
    have hxe : x = e.symm (e x) := (e.symm_apply_apply x).symm
    rcases hex : e x with i | i
    · rw [hxe, hex, quaternion_a_eq_xa_mul_xa, map_mul]
      have h1 := hPJ4 (e.symm (QuaternionGroup.xa 0))
        (by rw [MulEquiv.orderOf_eq, QuaternionGroup.orderOf_xa])
      have h2 := hPJ4
        (e.symm (QuaternionGroup.xa (i - ((2 ^ (k - 2) : ℕ) : ZMod (2 * 2 ^ (k - 2))))))
        (by rw [MulEquiv.orderOf_eq, QuaternionGroup.orderOf_xa])
      have h3 := J.mul_mem h1 h2
      have e3 : c * ((e.symm (QuaternionGroup.xa 0) * e.symm (QuaternionGroup.xa
          (i - ((2 ^ (k - 2) : ℕ) : ZMod (2 * 2 ^ (k - 2)))))) : P) * c⁻¹ =
          c * (e.symm (QuaternionGroup.xa 0) : G) * c⁻¹ * (c * (e.symm (QuaternionGroup.xa
            (i - ((2 ^ (k - 2) : ℕ) : ZMod (2 * 2 ^ (k - 2))))) : G) * c⁻¹) := by
        rw [Subgroup.coe_mul]; group
      rw [e3]
      exact h3
    · rw [hxe, hex]
      exact hPJ4 _ (by rw [MulEquiv.orderOf_eq, QuaternionGroup.orderOf_xa])
  have hg : c⁻¹ * t * c⁻¹⁻¹ = s₀ * d := by rw [← hc]; group
  have hUJ := h.torusU_le_map_conj hg
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.U_ne_bot
  obtain ⟨us, husJ, hus⟩ := hUJ u.2
  have hus' : c⁻¹ * us * c = u := by simpa [MulAut.conj_apply] using hus
  have hus1 : (⟨us, husJ⟩ : J) ≠ 1 := by
    intro h1
    apply hu1
    apply Subtype.ext
    have h2 : us = 1 := congrArg Subtype.val h1
    rw [← hus', h2, mul_one, inv_mul_cancel, Subgroup.coe_one]
  have husodd : Odd (orderOf (⟨us, husJ⟩ : J)) := by
    rw [Subgroup.orderOf_mk]
    have h1 : us = MulAut.conj c (u : G) := by rw [← hus', MulAut.conj_apply]; group
    rw [h1, MulEquiv.orderOf_eq]
    exact odd_orderOf_of_mem_U u.2
  obtain ⟨F, _, _, -, ⟨ι⟩⟩ := h.sl2
  have hns := not_scalar_of_odd ι hus1 husodd
  have hPus : ∀ x : P, c * (x : G) * c⁻¹ * us = us * (c * (x : G) * c⁻¹) := by
    intro x
    have h1 := Subgroup.mem_centralizer_iff.mp (hPU x.2) u u.2
    rw [← hus'] at h1
    calc c * (x : G) * c⁻¹ * us = c * ((x : G) * (c⁻¹ * us * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * us * c) * (x : G)) * c⁻¹ := by rw [h1]
      _ = us * (c * (x : G) * c⁻¹) := by group
  have hab : ∀ x y : P, x * y = y * x := by
    intro x y
    let X : J := ⟨c * (x : G) * c⁻¹, hPJ x⟩
    let Y : J := ⟨c * (y : G) * c⁻¹, hPJ y⟩
    let A : J := ⟨us, husJ⟩
    have hXA : X * A = A * X := Subtype.ext (hPus x)
    have hYA : Y * A = A * Y := Subtype.ext (hPus y)
    have hmat : ∀ Z : J, Z * A = A * Z →
        ((ι A : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          (ι Z : Matrix (Fin 2) (Fin 2) F) =
        (ι Z : Matrix (Fin 2) (Fin 2) F) * (ι A : Matrix (Fin 2) (Fin 2) F) := by
      intro Z hZ
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, ← map_mul,
        ← map_mul, hZ]
    have hXY := CFSG.SectionRank.Ccomm.commute_of_commute_nonscalar hns (hmat X hXA)
      (hmat Y hYA)
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, ← map_mul,
      ← map_mul] at hXY
    have hXY' : X * Y = Y * X := ι.injective (Subtype.ext hXY)
    have h1 : c * ((x : G) * (y : G)) * c⁻¹ = c * ((y : G) * (x : G)) * c⁻¹ := by
      have h2 := congrArg Subtype.val hXY'
      calc c * ((x : G) * (y : G)) * c⁻¹ = c * (x : G) * c⁻¹ * (c * (y : G) * c⁻¹) := by group
        _ = c * (y : G) * c⁻¹ * (c * (x : G) * c⁻¹) := h2
        _ = c * ((y : G) * (x : G)) * c⁻¹ := by group
    apply Subtype.ext
    simpa using h1
  apply quaternion_xa_mul_a_ne hm2
  apply e.symm.injective
  rw [map_mul, map_mul, hab]

theorem exists_oddPart_centralizer_torusU
    (hne : Nat.card (torusU G t s₀ d) ≠ Nat.card (torusW G t s₀)) :
    ∃ R : Subgroup G, ∀ x : G,
      x ∈ R ↔ x ∈ Subgroup.centralizer (torusU G t s₀ d : Set G) ∧ Odd (orderOf x) := by
  classical
  have hvC : s₀ * d ∈ Subgroup.centralizer (torusU G t s₀ d : Set G) :=
    v_mem_centralizer_torusU
  have hvp : IsPGroup 2 (Subgroup.zpowers
      (⟨s₀ * d, hvC⟩ : Subgroup.centralizer (torusU G t s₀ d : Set G))) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, h.v_orderOf,
      pow_one])
  obtain ⟨S₀, hS₀⟩ := hvp.exists_le_sylow
  have hvS := hS₀ (Subgroup.mem_zpowers _)
  let ι₀ := (S₀ : Subgroup (Subgroup.centralizer (torusU G t s₀ d : Set G))).equivMapOfInjective
    (Subgroup.centralizer (torusU G t s₀ d : Set G)).subtype (Subgroup.subtype_injective _)
  have hcycG := h.isCyclic_of_isPGroup_le_centralizer_torusU hne
    ((S₀ : Subgroup (Subgroup.centralizer (torusU G t s₀ d : Set G))).map
      (Subgroup.centralizer (torusU G t s₀ d : Set G)).subtype)
    (S₀.isPGroup'.map _) (Subgroup.map_subtype_le _) ⟨_, hvS, rfl⟩
  have hcyc : IsCyclic (S₀ : Subgroup (Subgroup.centralizer (torusU G t s₀ d : Set G))) :=
    isCyclic_of_surjective ι₀.symm.toMonoidHom ι₀.symm.surjective
  obtain ⟨N, -, -, -, -, hmem, -⟩ :=
    CFSG.Semidihedral.Principal.cyclicSylowTwo_normal_odd_complement S₀ hcyc
  refine ⟨N.map (Subgroup.centralizer (torusU G t s₀ d : Set G)).subtype, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
    exact (hmem y).mp hy
  · rintro ⟨hx, hodd⟩
    refine ⟨⟨x, hx⟩, (hmem _).mpr (by rwa [Subgroup.orderOf_mk]), rfl⟩

end CaseIData

end CFSG.Semidihedral.FixedCoreNontrivial

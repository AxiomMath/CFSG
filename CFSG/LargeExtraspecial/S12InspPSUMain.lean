module

public import CFSG.LargeExtraspecial.S12InspPSULoc
public import CFSG.LargeExtraspecial.S12InspPSUGen
public import CFSG.LargeExtraspecial.S12InspFamTools
public import CFSG.LargeExtraspecial.S12InspFamDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Matrix CFSG.RankThree.OrthogonalInvolutions CFSG.Open
  CFSG.Fischer.Classification CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary
open CFSG.Blueprint.Fischer (K)

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem exists_psu_mulEquiv {g : G} {m : ℕ}
    (hmod : fischerCentralQuotientModel (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g))
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 m (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 m x y)
      (fischerTransvections (fischerHermitianF4 m)
        fun v => v ≠ 0 ∧ fischerHermitianF4 m v v = 0)) :
    ∃ ψ : S.Xbar12 g ≃* PG m, ∀ x : S.Xbar12 g, (x : S.O) ∈ S.Ebar12 g ↔ ψ x ∈ DG m := by
  obtain ⟨φ, hφ⟩ := fischerCentralQuotientModel_iff_U2.1 hmod
  refine ⟨φ.trans (u2Equiv m), fun x => ?_⟩
  rw [MulEquiv.trans_apply, ← image_DU, (u2Equiv m).injective.mem_set_image, ← hφ,
    φ.injective.mem_set_image]
  rfl

theorem conj_mem_DG {m : ℕ} (c : SUid frob m) {q : PG m} (hq : q ∈ DG m) :
    (QuotientGroup.mk c : PG m) * q * (QuotientGroup.mk c)⁻¹ ∈ DG m := by
  obtain ⟨v, hv0, hv, rfl⟩ := hq
  exact ⟨c • v, (smul_ne_zero_iff_ne c).2 hv0, by rw [herm_smul_smul, hv], (conj_tq c hv).symm⟩

theorem exists_psu_mulEquiv_v₀ {g : G} {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) {k : ℕ} (hk : 1 ≤ k)
    (hmod : fischerCentralQuotientModel (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g))
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 (k + 2) (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 (k + 2) x y)
      (fischerTransvections (fischerHermitianF4 (k + 2))
        fun v => v ≠ 0 ∧ fischerHermitianF4 (k + 2) v v = 0)) :
    ∃ ψ : S.Xbar12 g ≃* PG (k + 2),
      (∀ x : S.Xbar12 g, (x : S.O) ∈ S.Ebar12 g ↔ ψ x ∈ DG (k + 2)) ∧
        ψ ⟨t, subset_Xbar12 (mem_Ebar12_of_mem_Lbar ht htA)⟩ = tq (v₀ k) := by
  obtain ⟨ψ₀, hψ₀⟩ := exists_psu_mulEquiv hmod
  set t' : S.Xbar12 g := ⟨t, subset_Xbar12 (mem_Ebar12_of_mem_Lbar ht htA)⟩
  obtain ⟨e, he0, he, hte⟩ := (hψ₀ t').1 (mem_Ebar12_of_mem_Lbar ht htA)
  obtain ⟨c, -, hc⟩ := exists_mem_T_smul_eq_of_iso isUnitaryInvolution_frob (by omega) he0 he
    v₀_ne_zero herm_v₀_v₀
  refine ⟨ψ₀.trans (MulAut.conj (QuotientGroup.mk c : PG (k + 2))), fun x => ?_, ?_⟩
  · rw [hψ₀ x, MulEquiv.trans_apply, MulAut.conj_apply]
    constructor
    · exact conj_mem_DG c
    · intro h
      have := conj_mem_DG c⁻¹ h
      rwa [QuotientGroup.mk_inv, inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul,
        mul_assoc, inv_mul_cancel, mul_one] at this
  · rw [MulEquiv.trans_apply, MulAut.conj_apply, ← hte, conj_tq c he, hc]

theorem sq_mem_fixSub12 {t γ : S.O} (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    (hγt : γ * t = t * γ) (hγ4 : γ ^ 4 = 1) :
    γ ^ 2 ∈ S.fixSub12 (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  have hγt' : γ⁻¹ * t = t * γ⁻¹ := by
    calc γ⁻¹ * t = γ⁻¹ * (t * γ) * γ⁻¹ := by group
      _ = γ⁻¹ * (γ * t) * γ⁻¹ := by rw [hγt]
      _ = t * γ⁻¹ := by group
  have h6 := s12_pow_six_apply htA.2.2.2.1 (x := (γ : S.Qt ≃ₗ[ZMod 2] S.Qt))
    (fun w hw => apply_mem_commSpace_of_commute hγt hw)
    (fun w hw => apply_mem_commSpace_of_commute hγt' hw)
  have e : γ ^ 2 = γ ^ 6 := by
    rw [show 6 = 4 + 2 from rfl, pow_add, hγ4, one_mul]
  intro w hw
  rw [e, Subgroup.coe_pow]
  exact h6 w hw

theorem false_of_order_three_mem_fixSub12 {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) {y : S.O} (hyM : y ∈ S.Mbar)
    (hyX : y ∈ S.Xbar12 g) (hyK : y ∈ S.fixSub12 (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)))
    (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (hcomm : ∀ x ∈ S.Xbar12 g, x ∈ S.Lbar g →
      x ∈ S.fixSub12 (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) → x * y = y * x) : False := by
  set K₀ := S.fixSub12 (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) with hK₀
  have haW := (S.timmesfeld_12_6 haQ hne ht htA).1
  have hcommL : ∀ {x : S.O}, x ∈ S.Lbar g → x * t = t * x := fun {x} hx =>
    congrArg Subtype.val ((S.isElementaryAbelian_Lbar haQ).is_comm.comm ⟨x, hx⟩ ⟨t, ht⟩)
  have hyN : y ∈ normalizer (S.Lbar g : Set S.O) :=
    (mem_normalizer_Lbar_iff_fix haQ hne hn hyM).mpr (hyK _ haW)
  have hyC : y ∈ S.Mbar ⊓ centralizer (S.Lbar g : Set S.O) := by
    refine ⟨hyM, mem_centralizer_iff.mpr fun ℓ hℓ => ?_⟩
    have hℓM := S.Lbar_le_Mbar g hℓ
    have hcL : ℓ * y * ℓ⁻¹ * y⁻¹ ∈ S.Lbar g := by
      have h1 : y * ℓ⁻¹ * y⁻¹ ∈ S.Lbar g :=
        (mem_normalizer_iff.mp hyN ℓ⁻¹).mp ((S.Lbar g).inv_mem hℓ)
      have h2 := (S.Lbar g).mul_mem hℓ h1
      rwa [show ℓ * (y * ℓ⁻¹ * y⁻¹) = ℓ * y * ℓ⁻¹ * y⁻¹ by group] at h2
    have hcK : ℓ * y * ℓ⁻¹ * y⁻¹ ∈ K₀ :=
      K₀.mul_mem (conj_mem_fixSub12 (hcommL hℓ) hyK) (K₀.inv_mem hyK)
    have hcX : ℓ * y * ℓ⁻¹ * y⁻¹ ∈ S.Xbar12 g := (S.Xbar12 g).mul_mem
      ((mem_normalizer_iff.mp (Mbar_le_normalizer_Xbar12 hℓM) y).mp hyX)
      ((S.Xbar12 g).inv_mem hyX)
    set c := ℓ * y * ℓ⁻¹ * y⁻¹ with hcdef
    have hcy : Commute c y := hcomm c hcX hcL hcK
    have hc2 : c * c = 1 := by
      have := S.isElementaryAbelian_Lbar haQ
      have h2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := S.Lbar g) c hcL
      rw [← sq]
      simpa using h2
    have e : ℓ * y * ℓ⁻¹ = c * y := by rw [hcdef, inv_mul_cancel_right]
    have h3 : (ℓ * y * ℓ⁻¹) ^ 3 = 1 := by rw [conj_pow, hy3, mul_one, mul_inv_cancel]
    rw [e, hcy.mul_pow, hy3, mul_one, show (3 : ℕ) = 1 + 2 from rfl, pow_add, pow_one, sq,
      hc2, mul_one] at h3
    rw [hcdef, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
    exact h3
  obtain ⟨j, hj⟩ := S.timmesfeld_12_4_2 haQ hne hn ⟨y, hyC⟩
  have hyj : y ^ 2 ^ j = 1 := by
    have := congrArg Subtype.val hj
    simpa using this
  have hord : orderOf y ∣ Nat.gcd (2 ^ j) 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hyj) (orderOf_dvd_of_pow_eq_one hy3)
  rw [show Nat.gcd (2 ^ j) 3 = 1 from Nat.Coprime.pow_left _ (by norm_num), Nat.dvd_one,
    orderOf_eq_one_iff] at hord
  exact hy1 hord

theorem false_of_psu_ge_five {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hn : 3 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) {m : ℕ} (hm : 5 ≤ m)
    (hmod : fischerCentralQuotientModel (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g))
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 m (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 m x y)
      (fischerTransvections (fischerHermitianF4 m)
        fun v => v ≠ 0 ∧ fischerHermitianF4 m v v = 0)) : False := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hk : 3 ≤ k := by omega
  have hk2 : 2 ≤ k := by omega
  obtain ⟨ψ, -, hψt⟩ := exists_psu_mulEquiv_v₀ ht htA (by omega : 1 ≤ k) hmod
  obtain ⟨χ, hχ⟩ : ∃ χ : PG (k + 2) →* S.O,
      χ = (S.Xbar12 g).subtype.comp ψ.symm.toMonoidHom := ⟨_, rfl⟩
  have hχX : ∀ q, χ q ∈ S.Xbar12 g := fun q => by rw [hχ]; exact (ψ.symm q).2
  have hχM : ∀ q, χ q ∈ S.Mbar := fun q => Xbar12_le_Mbar (hχX q)
  have hχinj : Function.Injective χ := by
    rw [hχ]
    exact (S.Xbar12 g).subtype_injective.comp ψ.symm.injective
  have hχψ : ∀ x : S.Xbar12 g, χ (ψ x) = x := fun x => by rw [hχ]; simp
  have hχt : χ (tq (v₀ k)) = t := by rw [← hψt, hχψ]
  have hχc : ∀ q, q * tq (v₀ k) = tq (v₀ k) * q → χ q * t = t * χ q := by
    intro q hq
    rw [← hχt, ← map_mul, ← map_mul, hq]
  have hιz0 : ∀ z : Fin k → K, z ≠ 0 → ι k z ≠ 0 := fun z hz h =>
    hz (ι_injective (by rw [h, map_zero]))
  have hιc : ∀ z : Fin k → K, z ≠ 0 → herm frob z z = 0 →
      tq (ι k z) * tq (v₀ k) = tq (v₀ k) * tq (ι k z) := fun z hz0 hz =>
    (tq_commute_iff (by omega) (hιz0 z hz0) (by rw [herm_ι_ι, hz]) v₀_ne_zero herm_v₀_v₀).2
      (herm_ι_v₀ z)
  set K₀ := S.fixSub12 (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) with hK₀
  have haW := (S.timmesfeld_12_6 haQ hne ht htA).1
  have hδK : ∀ z : Fin k → K, z ≠ 0 → herm frob z z = 0 → χ (tq (ι k z)) ∈ K₀ := by
    intro z hz0 hz
    have hz' : herm frob (ι k z) (ι k z) = 0 := by rw [herm_ι_ι, hz]
    obtain ⟨c, hcv, hcc⟩ := S12InspPSU.exists_sq_eq_tvU hk hz0 hz
    have hct : (QuotientGroup.mk c : PG (k + 2)) * tq (v₀ k) =
        tq (v₀ k) * QuotientGroup.mk c := by
      have h := conj_tq c herm_v₀_v₀
      rw [hcv] at h
      exact mul_inv_eq_iff_eq_mul.mp h
    have hc2 : (QuotientGroup.mk c : PG (k + 2)) ^ 2 = tq (ι k z) := by
      rw [sq, ← QuotientGroup.mk_mul, hcc]
    have hc4 : (QuotientGroup.mk c : PG (k + 2)) ^ 4 = 1 := by
      rw [show 4 = 2 * 2 from rfl, pow_mul, hc2, sq, tq_mul_self hz']
    have h := sq_mem_fixSub12 htA (hχc _ hct) (by rw [← map_pow, hc4, map_one])
    rwa [← map_pow, hc2] at h
  have hK₀L : ∀ y : S.O, y ∈ S.Mbar → y ∈ K₀ → y ∈ normalizer (S.Lbar g : Set S.O) :=
    fun y hyM hyK => (mem_normalizer_Lbar_iff_fix haQ hne hn hyM).mpr (hyK _ haW)
  have hEA := S.isElementaryAbelian_Lbar haQ
  have hL2 : ∀ x ∈ S.Lbar g, x * x = 1 := by
    intro x hx
    have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := S.Lbar g) x hx
    rw [← sq]
    simpa using this
  have hcommL : ∀ {x : S.O}, x ∈ S.Lbar g → x * t = t * x := fun {x} hx =>
    congrArg Subtype.val (hEA.is_comm.comm ⟨x, hx⟩ ⟨t, ht⟩)
  have hNsmall := S12InspPSU.eq_one_or_eq_tq_of_normalized hk (N := (S.Lbar g ⊓ K₀).comap χ)
    (fun a ha b hb => hχinj (by
      rw [map_mul, map_mul]
      exact congrArg Subtype.val (hEA.is_comm.comm ⟨χ a, ha.1⟩ ⟨χ b, hb.1⟩)))
    (fun a ha => hχinj (by
      rw [map_mul, map_one]
      exact hL2 _ ha.1))
    (fun a ha => hχinj (by
      rw [map_mul, map_mul, hχt]
      exact hcommL ha.1))
    (fun z hz0 hz a ha => by
      have hz' : herm frob (ι k z) (ι k z) = 0 := by rw [herm_ι_ι, hz]
      have hδM := hχM (tq (ι k z))
      have hδK' := hδK z hz0 hz
      have hδinv : (χ (tq (ι k z)))⁻¹ = χ (tq (ι k z)) := by
        rw [← map_inv, inv_eq_of_mul_eq_one_right (tq_mul_self hz')]
      refine ⟨?_, ?_⟩
      · rw [map_mul, map_mul]
        have := (mem_normalizer_iff.mp (hK₀L _ hδM hδK') (χ a)).mp ha.1
        rwa [hδinv] at this
      · rw [map_mul, map_mul]
        exact K₀.mul_mem (K₀.mul_mem hδK' ha.2) hδK')
  have hsmall : ∀ x ∈ S.Xbar12 g, x ∈ S.Lbar g → x ∈ K₀ → x = 1 ∨ x = t := by
    intro x hxX hxL hxK
    have hq : χ (ψ ⟨x, hxX⟩) = x := hχψ _
    rcases hNsmall (ψ ⟨x, hxX⟩) (by
      show χ (ψ ⟨x, hxX⟩) ∈ S.Lbar g ⊓ K₀
      rw [hq]
      exact ⟨hxL, hxK⟩) with h | h
    · left
      rw [← hq, h, map_one]
    · right
      rw [← hq, h, hχt]
  obtain ⟨z₂, hz₂0, hz₂, hz₁₂⟩ := exists_partner_frob (isoVec_ne_zero hk2) (isoVec_isotropic hk2)
  have hz₁0 := isoVec_ne_zero hk2
  have hz₁ := isoVec_isotropic hk2
  have hι₁ : herm frob (ι k (isoVec hk2)) (ι k (isoVec hk2)) = 0 := by rw [herm_ι_ι, hz₁]
  have hι₂ : herm frob (ι k z₂) (ι k z₂) = 0 := by rw [herm_ι_ι, hz₂]
  have hι₁₂ : herm frob (ι k (isoVec hk2)) (ι k z₂) ≠ 0 := by
    rw [herm_ι_ι, hz₁₂]
    exact one_ne_zero
  have hq3 : (tq (ι k (isoVec hk2)) * tq (ι k z₂)) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, tvU_mul_tvU_pow_three hι₁ hι₂ hι₁₂,
      QuotientGroup.mk_one]
  have hq1 : tq (ι k (isoVec hk2)) * tq (ι k z₂) ≠ 1 := by
    intro h
    have h2 : tq (ι k (isoVec hk2)) = tq (ι k z₂) := by
      calc tq (ι k (isoVec hk2)) = tq (ι k (isoVec hk2)) * (tq (ι k z₂) * tq (ι k z₂)) := by
            rw [tq_mul_self hι₂, mul_one]
        _ = tq (ι k z₂) := by rw [← mul_assoc, h, one_mul]
    exact hι₁₂ ((tq_commute_iff (by omega) (hιz0 _ hz₁0) hι₁ (hιz0 _ hz₂0) hι₂).1 (by rw [h2]))
  have hyt : χ (tq (ι k (isoVec hk2)) * tq (ι k z₂)) * t =
      t * χ (tq (ι k (isoVec hk2)) * tq (ι k z₂)) := by
    refine hχc _ ?_
    rw [mul_assoc, hιc _ hz₂0 hz₂, ← mul_assoc, hιc _ hz₁0 hz₁, mul_assoc]
  refine false_of_order_three_mem_fixSub12 haQ hne hn ht htA (y := χ (tq (ι k (isoVec hk2)) *
    tq (ι k z₂))) (hχM _) (hχX _) ?_ ?_ ?_ ?_
  · rw [map_mul]
    exact K₀.mul_mem (hδK _ hz₁0 hz₁) (hδK _ hz₂0 hz₂)
  · rw [← map_pow, hq3, map_one]
  · intro h
    exact hq1 (hχinj (by rw [h, map_one]))
  · intro x hxX hxL hxK
    rcases hsmall x hxX hxL hxK with rfl | rfl
    · rw [one_mul, mul_one]
    · exact hyt.symm

theorem isReducible12_of_psu_four (hn : 5 ≤ S.width) {g : G}
    (hmod : fischerCentralQuotientModel (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g))
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 4 (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 4 x y)
      (fischerTransvections (fischerHermitianF4 4)
        fun v => v ≠ 0 ∧ fischerHermitianF4 4 v v = 0)) : S.IsReducible12 := by
  obtain ⟨ψ, hψE⟩ := exists_psu_mulEquiv hmod
  obtain ⟨χ, hχ⟩ : ∃ χ : PG 4 →* S.O, χ = (S.Xbar12 g).subtype.comp ψ.symm.toMonoidHom :=
    ⟨_, rfl⟩
  have hχE : ∀ i, χ (tq (S12InspPSU.gen4 i)) ∈ S.Ebar12 g := by
    intro i
    have h := (hψE (ψ.symm (tq (S12InspPSU.gen4 i)))).2 (by
      rw [MulEquiv.apply_symm_apply]
      exact ⟨_, S12InspPSU.gen4_ne_zero i, S12InspPSU.herm_gen4_self i, rfl⟩)
    rw [hχ]
    exact h
  set d : Fin 5 → S.O := fun i => χ (tq (S12InspPSU.gen4 i)) with hd
  have hdA : ∀ i, IsTypeA S.q (d i : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 := fun i =>
    isTypeA_of_mem_Ebar12 (hχE i)
  have hcomm : ∀ i j : Fin 5, i.val < 3 → j.val < 3 →
      (d i : S.Qt ≃ₗ[ZMod 2] S.Qt) * (d j : S.Qt ≃ₗ[ZMod 2] S.Qt) =
        (d j : S.Qt ≃ₗ[ZMod 2] S.Qt) * (d i : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    intro i j hi hj
    have h := (tq_commute_iff (by norm_num) (S12InspPSU.gen4_ne_zero i)
      (S12InspPSU.herm_gen4_self i) (S12InspPSU.gen4_ne_zero j)
      (S12InspPSU.herm_gen4_self j)).2 (S12InspPSU.herm_gen4_gen4 hi hj)
    have h' : d i * d j = d j * d i := by
      simp only [hd]
      rw [← map_mul, ← map_mul, h]
    exact congrArg Subtype.val h'
  have hgen : S.Xbar12 g = closure (Set.range d) := by
    have e : Set.range d = χ '' Set.range fun i => tq (S12InspPSU.gen4 i) := by
      rw [← Set.range_comp]
      rfl
    rw [e, ← MonoidHom.map_closure, S12InspPSU.closure_gen4, ← MonoidHom.range_eq_map, hχ,
      MonoidHom.range_comp, MonoidHom.range_eq_top.2 ψ.symm.surjective, ← MonoidHom.range_eq_map,
      range_subtype]
  set A := commSpace (d 0 : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊔ commSpace (d 1 : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊔
    commSpace (d 2 : S.Qt ≃ₗ[ZMod 2] S.Qt) with hA
  set B := commSpace (d 3 : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊔ commSpace (d 4 : S.Qt ≃ₗ[ZMod 2] S.Qt)
    with hB
  have hle : S.commSub12 (S.Xbar12 g) ≤ A ⊔ B := by
    rw [hgen]
    refine (commSub12_closure_le _).trans (commSubSet12_le ?_)
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact le_sup_of_le_left (le_sup_of_le_left le_sup_left)
    · exact le_sup_of_le_left (le_sup_of_le_left le_sup_right)
    · exact le_sup_of_le_left le_sup_right
    · exact le_sup_of_le_right le_sup_left
    · exact le_sup_of_le_right le_sup_right
  have hA3 : finrank (ZMod 2) A ≤ S.width :=
    finrank_sup_three_le_width hn (hdA 0) (hdA 1) (hdA 2) (hcomm 0 1 (by decide) (by decide))
      (hcomm 0 2 (by decide) (by decide)) (hcomm 1 2 (by decide) (by decide))
  have hB4 : finrank (ZMod 2) B ≤ 4 := by
    have := Submodule.finrank_add_le_finrank_add_finrank (commSpace (d 3 : S.Qt ≃ₗ[ZMod 2] S.Qt))
      (commSpace (d 4 : S.Qt ≃ₗ[ZMod 2] S.Qt))
    rw [(hdA 3).2.2.2.1, (hdA 4).2.2.2.1] at this
    exact this
  have hdim : finrank (ZMod 2) (S.commSub12 (S.Xbar12 g)) ≤ S.width + 4 :=
    (Submodule.finrank_mono hle).trans
      ((Submodule.finrank_add_le_finrank_add_finrank A B).trans (by omega))
  have hd0X : d 0 ∈ S.Xbar12 g := subset_Xbar12 (hχE 0)
  have hd01 : d 0 ≠ 1 := fun h => (hdA 0).2.1 (by rw [h]; rfl)
  refine S.s12_isReducible12_of_finrank_lt Mbar_le_normalizer_Xbar12 hd0X hd01 ?_
  rw [S.finrank_Qt_eq_two_mul_width]
  omega

end Setting

theorem inspPSU : InspPSU := by
  intro G _ _ _ S g t haQ hne hn ht htA hS hred h
  obtain ⟨-, m, hm, hmod⟩ := h
  exfalso
  rcases Nat.lt_or_ge m 5 with hm5 | hm5
  · obtain rfl : m = 4 := by omega
    exact hred (Setting.isReducible12_of_psu_four hn hmod)
  · exact Setting.false_of_psu_ge_five haQ hne (by omega) ht htA hm5 hmod

end CFSG.LargeExtraspecial

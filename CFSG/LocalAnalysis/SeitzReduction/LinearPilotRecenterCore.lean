module

public import CFSG.RankThree.PartOne.KC.LinearSubfieldFixedPoints
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotPositionB
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIYComponent
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRigidityStd
public import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect)
open CFSG.RankThree.PartOne (linearSubfieldInclusion
  simple_nonabelian_range_linearSubfieldInclusion)
open CFSG.RankThree.PartOne.KCLinearSubfield (fixed_points_eq_range root_descent_of_not_dvd)
open CFSG.ComponentClassification.CatalogueBHigherLinearField (fixedField mem_fixedField)

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem autFixSubgroup_fieldAut_eq_range {f : ℕ} (hK : Nat.card K = 2 ^ f) (hn : 0 < n)
    (σ : K ≃+* K) (hσ : σ ^ 2 = 1) :
    autFixSubgroup (fieldAut n K σ) = (linearSubfieldInclusion n (fixedField K σ)).range := by
  have hk : ∀ x, x ∈ fixedField K σ ↔ σ x = x := fun x => mem_fixedField K σ x
  have hodd : ¬ 2 ∣ Nat.card Kˣ := by
    have : Fintype K := Fintype.ofFinite K
    rw [Nat.card_units, hK]
    have hf : 0 < f := by
      rcases Nat.eq_zero_or_pos f with h0 | h
      · have h1 := Finite.one_lt_card (α := K)
        rw [hK, h0, pow_zero] at h1
        exact absurd h1 (lt_irrefl 1)
      · exact h
    have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 hf.ne'
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    omega
  have h := fixed_points_eq_range (n := n) hk hn
    (root_descent_of_not_dvd Nat.prime_two hk hσ hodd)
  ext x
  have hx := congrArg (fun s : Set (projectiveSL n K) => x ∈ s) h
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe] at hx
  rw [mem_autFixSubgroup, hx]

theorem perfectCore_autFixSubgroup_fieldAut {f : ℕ} (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n)
    (σ : K ≃+* K) (hσ : σ ^ 2 = 1) :
    perfectCore (autFixSubgroup (fieldAut n K σ)) =
      (linearSubfieldInclusion n (fixedField K σ)).range := by
  rw [autFixSubgroup_fieldAut_eq_range hK (by omega) σ hσ]
  obtain ⟨hsimple, hnc⟩ := simple_nonabelian_range_linearSubfieldInclusion (K := K) hn
    (fixedField K σ)
  exact le_antisymm (perfectCore_le _) (le_perfectCore_of_perfect le_rfl
    (CFSG.ComponentClassification.RankTwoHypIIY.commutator_eq_self_of_isSimpleGroup hsimple hnc))

theorem isSimpleGroup_perfectCore_autFixSubgroup_fieldAut {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hn : 3 ≤ n) (σ : K ≃+* K) (hσ : σ ^ 2 = 1) :
    IsSimpleGroup (perfectCore (autFixSubgroup (fieldAut n K σ))) := by
  rw [perfectCore_autFixSubgroup_fieldAut hK hn σ hσ]
  exact (simple_nonabelian_range_linearSubfieldInclusion (K := K) hn (fixedField K σ)).1

omit [Finite K] in
theorem false_of_map_eq_of_isSimpleGroup {A Γ : Type*} [Group A] [Group Γ] {φ₁ φ₂ : A →* Γ}
    (hφ₁ : Function.Injective φ₁) (hφ₂ : Function.Injective φ₂) {X Y Q : Subgroup A}
    (hX : IsSimpleGroup X) (hXY : X.map φ₁ = Y.map φ₂) (hQY : Q ≤ Y)
    (hYQ : Y ≤ normalizer (Q : Set A)) (hQ1 : Q ≠ ⊥) (hQY' : Q ≠ Y) : False := by
  have hZs : IsSimpleGroup (Y.map φ₂) := by
    rw [← hXY]
    exact (X.equivMapOfInjective φ₁ hφ₁).symm.isSimpleGroup
  have hQZ : Q.map φ₂ ≤ Y.map φ₂ := map_mono hQY
  have hnorm : ((Q.map φ₂).subgroupOf (Y.map φ₂)).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hQZ]
    exact (map_mono hYQ).trans (le_normalizer_map φ₂)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Q.map φ₂).subgroupOf (Y.map φ₂)) with h | h
  · rw [subgroupOf_eq_bot, disjoint_of_le_iff_left_eq_bot hQZ] at h
    exact hQ1 ((map_eq_bot_iff_of_injective Q hφ₂).1 h)
  · rw [subgroupOf_eq_top] at h
    exact hQY' (le_antisymm hQY ((map_le_map_iff_of_injective hφ₂).1 h))

variable [CharP K 2]

theorem map_perfectCore_fieldAut_ne_inner {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (hn : 3 ≤ n) (σ : K ≃+* K) (hσ : σ ^ 2 = 1) {k : ℕ}
    (P : InvPlacement n k) (hk : 0 < k) (hJ : 2 ≤ P.free.card) {Γ : Type*} [Group Γ]
    {φ₁ φ₂ : projectiveSL n K →* Γ} (hφ₁ : Function.Injective φ₁)
    (hφ₂ : Function.Injective φ₂) :
    (perfectCore (autFixSubgroup (fieldAut n K σ))).map φ₁ ≠
      (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K)))).map φ₂ := by
  intro hXY
  obtain ⟨-, hΛeq, hdisj, hMN, -⟩ := P.centralizer_inv_perfectCore hq (P.card_free ▸ hJ)
  have hQΛ : P.radicalP K ≤ perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))) := by
    rw [hΛeq]
    exact le_sup_left
  have hΛN : perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))) ≤
      normalizer (P.radicalP K : Set (projectiveSL n K)) := by
    rw [hΛeq]
    exact sup_le le_normalizer hMN
  have hQ1 : P.radicalP K ≠ ⊥ := by
    intro h
    have hne : P.u ⟨0, hk⟩ ≠ P.w ⟨0, hk⟩ := P.u_ne_w _ _
    have hmem : proj n K (Matrix.SpecialLinearGroup.transvection hne (1 : K)) ∈ P.radicalP K :=
      mem_map_of_mem _ (P.transvection_mem_radical hne (by rw [P.level_u, P.level_w]; omega) 1)
    rw [h, mem_bot] at hmem
    exact proj_transvection_ne_one hne one_ne_zero hmem
  have hQΛ' : P.radicalP K ≠
      perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))) := by
    intro h
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (show 1 < P.free.card by omega)
    have hmem : proj n K (Matrix.SpecialLinearGroup.transvection hab (1 : K)) ∈
        blockSL (K := K) P.free := proj_transvection_mem_blockSL hab ha hb 1
    have hmemQ : proj n K (Matrix.SpecialLinearGroup.transvection hab (1 : K)) ∈
        P.radicalP K := by
      rw [h, hΛeq]
      exact mem_sup_right (mem_sup_right hmem)
    have h1 := disjoint_def.1 hdisj hmemQ (mem_sup_right hmem)
    exact proj_transvection_ne_one hab one_ne_zero h1
  exact false_of_map_eq_of_isSimpleGroup hφ₁ hφ₂
    (isSimpleGroup_perfectCore_autFixSubgroup_fieldAut hK hn σ hσ) hXY hQΛ hΛN hQ1 hQΛ'

omit [Finite K] in
theorem InvPlacement.centralizer_elt_le_normalizer_radicalP {k : ℕ} (P : InvPlacement n k) :
    centralizer ({P.elt K} : Set (projectiveSL n K)) ≤
      normalizer (P.radicalP K : Set (projectiveSL n K)) := by
  rw [P.centralizer_elt]
  exact (map_mono (P.centralizer_le_parabolic.trans P.parabolic_le_normalizer_radical)).trans
    (le_normalizer_map _)

omit [Finite K] in
theorem InvPlacement.leviOne_transvection_not_commute {k : ℕ} (P : InvPlacement n k)
    (hk : 2 ≤ k) :
    proj n K (P.leviOneHom K (Matrix.SpecialLinearGroup.transvection
        (show (⟨0, by omega⟩ : Fin k) ≠ ⟨1, by omega⟩ by simp [Fin.ext_iff]) (1 : K))) *
      proj n K (Matrix.SpecialLinearGroup.transvection (P.u_ne_w ⟨1, hk⟩ ⟨1, hk⟩) (1 : K)) ≠
    proj n K (Matrix.SpecialLinearGroup.transvection (P.u_ne_w ⟨1, hk⟩ ⟨1, hk⟩) (1 : K)) *
      proj n K (P.leviOneHom K (Matrix.SpecialLinearGroup.transvection
        (show (⟨0, by omega⟩ : Fin k) ≠ ⟨1, by omega⟩ by simp [Fin.ext_iff]) (1 : K))) := by
  intro h
  set a0 : Fin k := ⟨0, by omega⟩
  set a1 : Fin k := ⟨1, hk⟩
  have h01 : a0 ≠ a1 := by simp [a0, a1, Fin.ext_iff]
  set B := P.leviOneHom K (Matrix.SpecialLinearGroup.transvection h01 (1 : K)) with hB
  set A := Matrix.SpecialLinearGroup.transvection (P.u_ne_w a1 a1) (1 : K) with hA
  have hcomm : B * A = A * B :=
    InvPlacement.commute_of_proj_commute (InvPlacement.transvection_mul_self _ _) h
  have h1 := congrFun (congrFun (congrArg (fun X : Matrix.SpecialLinearGroup (Fin n) K =>
    (X : Matrix (Fin n) (Fin n) K)) hcomm) (P.u a0)) (P.w a1)
  have hu : P.u a0 ≠ P.u a1 := fun h' => h01 (P.u_injective h')
  simp only [Matrix.SpecialLinearGroup.coe_mul, hA, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply,
    Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne _ _ _ _ _ hu, mul_one,
    add_zero] at h1
  have h2 : (B : Matrix (Fin n) (Fin n) K) (P.u a0) (P.u a1) = 1 := by
    rw [hB, P.leviOneHom_apply_u_u, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.add_apply, Matrix.one_apply_ne h01, Matrix.single_apply_same, zero_add]
  rw [h2] at h1
  exact one_ne_zero (add_eq_left.1 h1)

theorem map_perfectCore_fieldAut_ne_inner_of_two_le {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (hn : 3 ≤ n) (σ : K ≃+* K) (hσ : σ ^ 2 = 1) {k : ℕ}
    (P : InvPlacement n k) (hk : 2 ≤ k) {Γ : Type*} [Group Γ]
    {φ₁ φ₂ : projectiveSL n K →* Γ} (hφ₁ : Function.Injective φ₁)
    (hφ₂ : Function.Injective φ₂) :
    (perfectCore (autFixSubgroup (fieldAut n K σ))).map φ₁ ≠
      (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K)))).map φ₂ := by
  intro hXY
  set C := centralizer ({P.elt K} : Set (projectiveSL n K)) with hC
  set Λ := perfectCore C with hΛ
  set Q := P.radicalP K with hQ
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin k) K) :=
    InvPlacement.isPerfect_specialLinearGroup_of_four_le hq (Fin k)
  have hM₁p : ⁅P.leviOneP K, P.leviOneP K⁆ = P.leviOneP K := by
    have : Group.IsPerfect (P.leviOne K) := Group.IsPerfect.range _
    rw [InvPlacement.leviOneP, ← Subgroup.map_commutator, Subgroup.commutator_eq_self]
  have hM₁C : P.leviOneP K ≤ C := by
    rw [hC, P.centralizer_elt]
    exact map_mono P.leviOne_le_centralizer
  have hM₁Λ : P.leviOneP K ≤ Λ := le_perfectCore_of_perfect hM₁C hM₁p
  have hΛC : Λ ≤ C := perfectCore_le C
  have hCN : C ≤ normalizer (Q : Set (projectiveSL n K)) := P.centralizer_elt_le_normalizer_radicalP
  have hCΛ : C ≤ normalizer (Λ : Set (projectiveSL n K)) :=
    le_normalizer.trans (CFSG.Quasithin.normalizer_le_normalizer_perfectCore C)
  set a0 : Fin k := ⟨0, by omega⟩
  set a1 : Fin k := ⟨1, hk⟩
  have h01 : a0 ≠ a1 := by simp [a0, a1, Fin.ext_iff]
  set m := proj n K (P.leviOneHom K (Matrix.SpecialLinearGroup.transvection h01 (1 : K)))
    with hm
  set r := proj n K (Matrix.SpecialLinearGroup.transvection (P.u_ne_w a1 a1) (1 : K)) with hr
  have hmM : m ∈ P.leviOneP K := mem_map_of_mem _ ⟨_, rfl⟩
  have hrQ : r ∈ Q := mem_map_of_mem _
    (P.transvection_mem_radical _ (by rw [P.level_u, P.level_w]; omega) 1)
  have hrC : r ∈ C := by
    rw [hC, P.centralizer_elt]
    exact mem_map_of_mem _ (P.radical_le_centralizer
      (P.transvection_mem_radical _ (by rw [P.level_u, P.level_w]; omega) 1))
  have hnc : m * r ≠ r * m := P.leviOne_transvection_not_commute (K := K) hk
  have hQ₀N : Λ ≤ normalizer ((Λ ⊓ Q : Subgroup (projectiveSL n K)) : Set (projectiveSL n K)) := by
    intro x hx
    rw [mem_normalizer_iff]
    intro y
    have h1 := (mem_normalizer_iff.1 (hCΛ (hΛC hx))) y
    have h2 := (mem_normalizer_iff.1 (hCN (hΛC hx))) y
    rw [mem_inf, mem_inf]
    exact ⟨fun hy => ⟨h1.1 hy.1, h2.1 hy.2⟩, fun hy => ⟨h1.2 hy.1, h2.2 hy.2⟩⟩
  have hcm : m * r * m⁻¹ * r⁻¹ ∈ Λ ⊓ Q := by
    refine mem_inf.2 ⟨?_, ?_⟩
    · have hrm : r * m⁻¹ * r⁻¹ ∈ Λ :=
        (mem_normalizer_iff.1 (hCΛ hrC) m⁻¹).1 (inv_mem (hM₁Λ hmM))
      have e1 : m * r * m⁻¹ * r⁻¹ = m * (r * m⁻¹ * r⁻¹) := by group
      rw [e1]
      exact mul_mem (hM₁Λ hmM) hrm
    · have hmr : m * r * m⁻¹ ∈ Q := (mem_normalizer_iff.1 (hCN (hM₁C hmM)) r).1 hrQ
      exact mul_mem hmr (inv_mem hrQ)
  have hQ₀1 : (Λ ⊓ Q : Subgroup (projectiveSL n K)) ≠ ⊥ := by
    intro h
    rw [h, mem_bot] at hcm
    apply hnc
    have e1 : m * r = m * r * m⁻¹ * r⁻¹ * (r * m) := by group
    rw [e1, hcm, one_mul]
  have hQ₀Λ : (Λ ⊓ Q : Subgroup (projectiveSL n K)) ≠ Λ := by
    intro h
    have hmΛQ : m ∈ Λ ⊓ Q := by
      rw [h]
      exact hM₁Λ hmM
    have hmQ : m ∈ Q := (mem_inf.1 hmΛQ).2
    have hm1 : m = 1 :=
      disjoint_def.1 P.disjoint_radicalP hmQ (mem_sup_left hmM)
    apply hnc
    rw [hm1, one_mul, mul_one]
  exact false_of_map_eq_of_isSimpleGroup hφ₁ hφ₂
    (isSimpleGroup_perfectCore_autFixSubgroup_fieldAut hK hn σ hσ) hXY inf_le_left hQ₀N hQ₀1
    hQ₀Λ

theorem map_perfectCore_fieldAut_ne_inner_of_four_le {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n) (σ : K ≃+* K) (hσ : σ ^ 2 = 1) {k : ℕ}
    (P : InvPlacement n k) (hk : 0 < k) {Γ : Type*} [Group Γ]
    {φ₁ φ₂ : projectiveSL n K →* Γ} (hφ₁ : Function.Injective φ₁)
    (hφ₂ : Function.Injective φ₂) :
    (perfectCore (autFixSubgroup (fieldAut n K σ))).map φ₁ ≠
      (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K)))).map φ₂ := by
  rcases (by omega : k = 1 ∨ 2 ≤ k) with rfl | hk2
  · have hJ : 2 ≤ P.free.card := by
      rw [P.card_free]
      omega
    exact map_perfectCore_fieldAut_ne_inner hK hq (by omega) σ hσ P hk hJ hφ₁ hφ₂
  · exact map_perfectCore_fieldAut_ne_inner_of_two_le hK hq (by omega) σ hσ P hk2 hφ₁ hφ₂

theorem map_perfectCore_field_ne_inner {f : ℕ} (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (hn : 4 ≤ n) (A : GL (Fin n) K) (σ : K ≃+* K) (hσ : σ ≠ 1)
    (hα : (conjAut n K A * fieldAut n K σ) ^ 2 = 1) (B : GL (Fin n) K)
    (hβ : conjAut n K B ^ 2 = 1) (hβ1 : conjAut n K B ≠ 1) {Γ : Type*} [Group Γ]
    {φ₁ φ₂ : projectiveSL n K →* Γ} (hφ₁ : Function.Injective φ₁)
    (hφ₂ : Function.Injective φ₂) :
    (perfectCore (autFixSubgroup (conjAut n K A * fieldAut n K σ))).map φ₁ ≠
      (perfectCore (autFixSubgroup (conjAut n K B))).map φ₂ := by
  have hn3 : 3 ≤ n := by omega
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h1
    · have h1 := Finite.one_lt_card (α := K)
      rw [hK, h0, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · exact h1
  have hσ2 : σ ^ 2 = 1 := by
    have h := congrArg (ProjectivePlane.linearFieldPart K hn3) hα
    rwa [map_pow, map_one, show conjAut n K A * fieldAut n K σ =
      conjAut n K A * fieldAut n K σ * dualAut n K ^ 0 by rw [pow_zero, mul_one],
      ProjectivePlane.linearFieldPart_eq hn3 (Nat.zero_le 1)] at h
  obtain ⟨-, -, H, hH⟩ := even_linear_field_involution_descent hf hK hn3 A σ hσ hα
  have hX : perfectCore (autFixSubgroup (conjAut n K A * fieldAut n K σ)) =
      (perfectCore (autFixSubgroup (fieldAut n K σ))).map (conjAut n K H).toMonoidHom := by
    rw [hH, perfectCore_autFixSubgroup_conj]
  obtain ⟨y, hyy, hy⟩ := exists_conjAut_eq_mulAut_conj hn3 B hβ
  obtain ⟨k, P, c, hc⟩ := exists_conj_eq_elt hyy
  have hy' : MulAut.conj y =
      MulAut.conj c⁻¹ * MulAut.conj (P.elt K) * (MulAut.conj c⁻¹)⁻¹ := by
    rw [← hc, ← map_inv, ← map_mul, ← map_mul, inv_inv]
    congr 1
    group
  have hY : perfectCore (autFixSubgroup (conjAut n K B)) =
      (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K)))).map
        (MulAut.conj c⁻¹).toMonoidHom := by
    rw [hy, hy', perfectCore_autFixSubgroup_conj, autFixSubgroup_mulAut_conj]
  have hk : 0 < k := by
    refine Nat.pos_of_ne_zero fun h0 => hβ1 ?_
    have h1 : P.elt K = 1 := P.elt_eq_one_of_eq_zero h0
    have hy1 : y = 1 := by
      have e1 : y = c⁻¹ * (c * y * c⁻¹) * c := by group
      rw [e1, hc, h1]
      group
    rw [hy, hy1, map_one]
  intro hXY
  rw [hX, hY, Subgroup.map_map, Subgroup.map_map] at hXY
  have hi₁ : Function.Injective (φ₁.comp (conjAut n K H).toMonoidHom) :=
    hφ₁.comp (conjAut n K H).injective
  have hi₂ : Function.Injective (φ₂.comp (MulAut.conj c⁻¹).toMonoidHom) :=
    hφ₂.comp (MulAut.conj c⁻¹).injective
  exact map_perfectCore_fieldAut_ne_inner_of_four_le hK hq hn σ hσ2 P hk hi₁ hi₂ hXY

end CFSG.SeitzReduction.LinearPilot

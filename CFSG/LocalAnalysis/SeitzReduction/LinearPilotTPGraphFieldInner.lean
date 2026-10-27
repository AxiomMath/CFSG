module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRecenterCore

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect)

variable {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem map_ne_perfectCore_centralizer_of_isSimpleGroup (hq : 4 ≤ Nat.card K)
    {X : Subgroup (projectiveSL n K)} (hX : IsSimpleGroup X) {k : ℕ} (P : InvPlacement n k)
    (hk : 0 < k) (hJ : 2 ≤ P.free.card) {Γ : Type*} [Group Γ] {φ₁ φ₂ : projectiveSL n K →* Γ}
    (hφ₁ : Function.Injective φ₁) (hφ₂ : Function.Injective φ₂) :
    X.map φ₁ ≠ (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K)))).map φ₂ := by
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
  exact false_of_map_eq_of_isSimpleGroup hφ₁ hφ₂ hX hXY hQΛ hΛN hQ1 hQΛ'

theorem map_ne_perfectCore_centralizer_of_isSimpleGroup_of_two_le (hq : 4 ≤ Nat.card K)
    {X : Subgroup (projectiveSL n K)} (hX : IsSimpleGroup X) {k : ℕ} (P : InvPlacement n k)
    (hk : 2 ≤ k) {Γ : Type*} [Group Γ] {φ₁ φ₂ : projectiveSL n K →* Γ}
    (hφ₁ : Function.Injective φ₁) (hφ₂ : Function.Injective φ₂) :
    X.map φ₁ ≠ (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K)))).map φ₂ := by
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
  exact false_of_map_eq_of_isSimpleGroup hφ₁ hφ₂ hX hXY inf_le_left hQ₀N hQ₀1 hQ₀Λ

theorem map_ne_perfectCore_centralizer_of_isSimpleGroup_of_four_le (hq : 4 ≤ Nat.card K)
    (hn : 4 ≤ n) {X : Subgroup (projectiveSL n K)} (hX : IsSimpleGroup X) {k : ℕ}
    (P : InvPlacement n k) (hk : 0 < k) {Γ : Type*} [Group Γ] {φ₁ φ₂ : projectiveSL n K →* Γ}
    (hφ₁ : Function.Injective φ₁) (hφ₂ : Function.Injective φ₂) :
    X.map φ₁ ≠ (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K)))).map φ₂ := by
  rcases (by omega : k = 1 ∨ 2 ≤ k) with rfl | hk2
  · have hJ : 2 ≤ P.free.card := by
      rw [P.card_free]
      omega
    exact map_ne_perfectCore_centralizer_of_isSimpleGroup hq hX P hk hJ hφ₁ hφ₂
  · exact map_ne_perfectCore_centralizer_of_isSimpleGroup_of_two_le hq hX P hk2 hφ₁ hφ₂

theorem map_ne_perfectCore_conjAut_of_isSimpleGroup (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n)
    {X : Subgroup (projectiveSL n K)} (hX : IsSimpleGroup X) (B : GL (Fin n) K)
    (hβ : conjAut n K B ^ 2 = 1) (hβ1 : conjAut n K B ≠ 1) {Γ : Type*} [Group Γ]
    {φ₁ φ₂ : projectiveSL n K →* Γ} (hφ₁ : Function.Injective φ₁)
    (hφ₂ : Function.Injective φ₂) :
    X.map φ₁ ≠ (perfectCore (autFixSubgroup (conjAut n K B))).map φ₂ := by
  have hn3 : 3 ≤ n := by omega
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
  rw [hY, Subgroup.map_map] at hXY
  have hi₂ : Function.Injective (φ₂.comp (MulAut.conj c⁻¹).toMonoidHom) :=
    hφ₂.comp (MulAut.conj c⁻¹).injective
  exact map_ne_perfectCore_centralizer_of_isSimpleGroup_of_four_le hq hn hX P hk hφ₁ hi₂ hXY

end CFSG.SeitzReduction.LinearPilot

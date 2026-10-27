module

public import CFSG.GH74.GLS.Stage4.T2Cent
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Stage4.T2SL2B

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2

section SL

variable {F : Type} [Field F]

theorem t2C_center_sl2 (A : SL2 F) : A ∈ Subgroup.center (SL2 F) ↔ A = 1 ∨ A = negOne F := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff, Fintype.card_fin]
  constructor
  · rintro ⟨r, hr, hA⟩
    rcases sq_eq_one_iff.1 hr with rfl | rfl
    · left
      apply Subtype.ext
      rw [← hA]
      simp
    · right
      apply Subtype.ext
      rw [← hA]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
  · rintro (rfl | rfl)
    · exact ⟨1, one_pow 2, by simp⟩
    · refine ⟨-1, by norm_num, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]

theorem t2C_negOne_ne_one (h2 : (2 : F) ≠ 0) : negOne F ≠ 1 := by
  intro h
  have h00 := congrArg (fun A : SL2 F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp at h00
  apply h2
  linear_combination -h00

theorem t2C_sl2U_ne (h2 : (2 : F) ≠ 0) : sl2U (1 : F) ≠ 1 ∧ sl2U (1 : F) ≠ negOne F := by
  constructor
  · intro h
    have : sl2U (1 : F) = sl2U 0 := by rw [h, sl2U_zero]
    exact one_ne_zero (sl2U_injective this)
  · intro h
    have h00 := congrArg (fun A : SL2 F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp [sl2U] at h00
    apply h2
    linear_combination h00

theorem t2C_normal_le_center_or_top {Q : Type*} [Group Q] (hperf : Group.IsPerfect Q)
    (hs : IsSimpleGroup (Q ⧸ Subgroup.center Q)) (N : Subgroup Q) [N.Normal] :
    N ≤ Subgroup.center Q ∨ N = ⊤ := by
  have := hperf
  have := hs
  let quotient := QuotientGroup.mk' (Subgroup.center Q)
  have hnormal : (N.map quotient).Normal :=
    Subgroup.Normal.map inferInstance quotient (QuotientGroup.mk'_surjective _)
  rcases hnormal.eq_bot_or_eq_top with hbot | htop
  · left
    have hkernel : N ≤ quotient.ker := N.map_eq_bot_iff.mp hbot
    change N ≤ (QuotientGroup.mk' (Subgroup.center Q)).ker at hkernel
    simpa only [QuotientGroup.ker_mk'] using hkernel
  · right
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have hcomap := Subgroup.comap_map_eq quotient N
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcomap
      exact hcomap.symm
    have hderived : commutator Q ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    rw [Group.IsPerfect.commutator_eq_top] at hderived
    exact top_unique hderived

theorem t2C_normal_sl2 [Finite F] (h4 : 4 ≤ Nat.card F) (N : Subgroup (SL2 F)) [N.Normal] :
    N ≤ Subgroup.center (SL2 F) ∨ N = ⊤ :=
  t2C_normal_le_center_or_top
    (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F h4)
    (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4) N

theorem t2C_card_sl2 [Finite F] :
    Nat.card (SL2 F) = Nat.card F * (Nat.card F ^ 2 - 1) :=
  CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F

theorem t2C_isSquare_of_slConj_eq_inner (g : GL (Fin 2) F) (a : SL2 F)
    (h : ∀ x : SL2 F, slConj g x = a * x * a⁻¹) :
    IsSquare ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) := by
  have hg : ∀ x : SL2 F, slConj (Matrix.SpecialLinearGroup.toGL a⁻¹ * g) x = x := by
    intro x
    rw [slConj_mul, h x, t2B_slConj_toGL]
    group
  obtain ⟨c, hc⟩ := eq_scalar_of_slConj_eq _ hg
  have hdet := congrArg Matrix.det hc
  rw [Units.val_mul, Matrix.det_mul] at hdet
  simp at hdet
  refine ⟨c, ?_⟩
  rw [Matrix.GeneralLinearGroup.val_det_apply, hdet, sq]

end SL

section Transport

variable {F : Type} [Field F] {G : Type} [Group G] {z : G} {K : Subgroup G}

theorem t2C_Z_of_sl2 (e : ↥K ≃* SL2 F) (hz1 : z ≠ 1) (hzK : z ∈ K) (hzc : ∀ k ∈ K, k * z = z * k) :
    e ⟨z, hzK⟩ = negOne F ∧
      ∀ k ∈ K, (∀ k' ∈ K, k * k' = k' * k) → k ∈ Subgroup.zpowers z := by
  have hz : e ⟨z, hzK⟩ ∈ Subgroup.center (SL2 F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hzc y y.2)
  have hne : e ⟨z, hzK⟩ ≠ 1 := by
    intro h
    apply hz1
    have : (⟨z, hzK⟩ : ↥K) = 1 := e.injective (by rw [h, map_one])
    simpa using congrArg Subtype.val this
  have hzeq : e ⟨z, hzK⟩ = negOne F := by
    rcases (t2C_center_sl2 _).1 hz with h | h
    · exact absurd h hne
    · exact h
  refine ⟨hzeq, fun k hk hkc => ?_⟩
  have hkz : e ⟨k, hk⟩ ∈ Subgroup.center (SL2 F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hkc y y.2).symm
  rcases (t2C_center_sl2 _).1 hkz with h | h
  · have : (⟨k, hk⟩ : ↥K) = 1 := e.injective (by rw [h, map_one])
    have hk1 : k = 1 := by simpa using congrArg Subtype.val this
    rw [hk1]; exact Subgroup.one_mem _
  · have : (⟨k, hk⟩ : ↥K) = ⟨z, hzK⟩ := e.injective (by rw [h, hzeq])
    have hkz' : k = z := by simpa using congrArg Subtype.val this
    rw [hkz']; exact Subgroup.mem_zpowers z

theorem t2C_Q_of_sl2 [Finite F] (h4 : 4 ≤ Nat.card F) (e : ↥K ≃* SL2 F) (hzK : z ∈ K)
    (hze : e ⟨z, hzK⟩ = negOne F) :
    ∀ N : Subgroup G, N ≤ K → (∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N) →
      N ≤ Subgroup.zpowers z ∨ K ≤ N := by
  intro N hNK hNnorm
  have hN'norm : (N.subgroupOf K).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hNnorm g g.2 n hn
  let M : Subgroup (SL2 F) := (N.subgroupOf K).map e.toMonoidHom
  have hMnorm : M.Normal :=
    Subgroup.Normal.map hN'norm e.toMonoidHom e.surjective
  rcases t2C_normal_sl2 h4 M with hM | hM
  · left
    intro n hn
    have hmem : e ⟨n, hNK hn⟩ ∈ M := ⟨⟨n, hNK hn⟩, Subgroup.mem_subgroupOf.2 hn, rfl⟩
    rcases (t2C_center_sl2 _).1 (hM hmem) with h | h
    · have : (⟨n, hNK hn⟩ : ↥K) = 1 := e.injective (by rw [h, map_one])
      have hn1 : n = 1 := by simpa using congrArg Subtype.val this
      rw [hn1]; exact Subgroup.one_mem _
    · have : (⟨n, hNK hn⟩ : ↥K) = ⟨z, hzK⟩ := e.injective (by rw [h, hze])
      have hnz : n = z := by simpa using congrArg Subtype.val this
      rw [hnz]; exact Subgroup.mem_zpowers z
  · right
    intro k hk
    have hmem : e ⟨k, hk⟩ ∈ M := by rw [hM]; trivial
    obtain ⟨n', hn', hn'e⟩ := hmem
    have : n' = ⟨k, hk⟩ := e.injective hn'e
    rw [this] at hn'
    exact Subgroup.mem_subgroupOf.1 hn'

theorem t2C_nab_of_sl2 (h2 : (2 : F) ≠ 0) (hzz : z * z = 1) (e : ↥K ≃* SL2 F) (hzK : z ∈ K)
    (hze : e ⟨z, hzK⟩ = negOne F) : ¬ K ≤ Subgroup.zpowers z := by
  intro hle
  set x : ↥K := e.symm (sl2U (1 : F)) with hx
  have hxz := hle x.2
  have hxe : e x = sl2U (1 : F) := by simp [hx]
  rcases t2C_zpowers_cases hzz hxz with h | h
  · have : x = 1 := Subtype.ext (by simpa using h)
    exact (t2C_sl2U_ne h2).1 (by rw [← hxe, this, map_one])
  · have : x = ⟨z, hzK⟩ := Subtype.ext h
    exact (t2C_sl2U_ne h2).2 (by rw [← hxe, this, hze])

end Transport

section Gen

variable {G : Type} [Group G]

theorem t2C_gen_odd {K X X' : Subgroup G} {q : ℕ} (hq : Odd q) (hK : K = X ⊔ X')
    (hX : ∀ x ∈ X, x ^ q.minFac = 1) (hX' : ∀ x ∈ X', x ^ q.minFac = 1) :
    K ≤ Subgroup.closure {x | x ∈ K ∧ Odd (orderOf x)} := by
  have hodd : Odd q.minFac := Odd.of_dvd_nat hq (Nat.minFac_dvd q)
  have key : ∀ Y : Subgroup G, Y ≤ K → (∀ x ∈ Y, x ^ q.minFac = 1) →
      Y ≤ Subgroup.closure {x | x ∈ K ∧ Odd (orderOf x)} := by
    intro Y hYK hY x hx
    exact Subgroup.subset_closure ⟨hYK hx, Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one (hY x hx))⟩
  exact hK.le.trans (sup_le (key X (hK ▸ le_sup_left) hX) (key X' (hK ▸ le_sup_right) hX'))

end Gen


end CFSG.GH74.GLS.Stage4.Rest

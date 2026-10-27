module

public import CFSG.LieType.Steinberg.CentralExt.Model
public import CFSG.LieType.Steinberg.CentralExt.Families
public import CFSG.LieType.Steinberg.CentralExt.PerfectCover

public section

namespace CFSG.LieType.Steinberg

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem isCyclic_center_specialLinearGroup (n : ℕ) (K : Type*) [Field K] :
    IsCyclic (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K)) := by
  have : NeZero (max (Fintype.card (Fin n)) 1) := ⟨by omega⟩
  exact isCyclic_of_surjective
    (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin n) (R := K)).symm
    (MulEquiv.surjective _)

theorem card_center_specialLinearGroup_dvd {n : ℕ} (hn : 1 ≤ n) (K : Type*) [Field K]
    [Finite K] :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K)) ∣
      Nat.gcd n (Nat.card K - 1) := by
  have hmax : max (Fintype.card (Fin n)) 1 = n := by
    rw [Fintype.card_fin]
    omega
  have : NeZero n := ⟨by omega⟩
  rw [Nat.card_congr
    (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin n) (R := K)).toEquiv, hmax]
  refine Nat.dvd_gcd ?_ ?_
  · have := rootsOfUnity.isCyclic K n
    rw [← IsCyclic.exponent_eq_card]
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext ?_
    simpa using (mem_rootsOfUnity n (g : Kˣ)).1 g.2
  · rw [← Nat.card_units K]
    exact Subgroup.card_subgroup_dvd_card _

theorem odd_field_higher_linear_perfect_central_two_kernel_cyclic {p f n : ℕ} (hp2 : p ≠ 2)
    {P Q : Type} [Group P] [Group Q] [Finite P] (hP : Group.IsPerfect P) {η : P →* Q}
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center P) (h2 : IsPGroup 2 η.ker)
    (hQ : LieModel Q .PSL n p f) :
    IsCyclic η.ker ∧ Nat.card η.ker ∣ Nat.gcd n (p ^ f - 1) := by
  have := hP
  obtain ⟨⟨hp, -, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := statedClassicalModel_of_lieModel (by decide) hQ
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hk : ringChar K ≠ 2 := ringChar_ne_two_of_card_eq_pow hp hp2 hK
  let φ := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL (m + 1) K
  let β : Matrix.SpecialLinearGroup (Fin (m + 1)) K →* Q :=
    (e.symm.toMonoidHom.comp (QuotientGroup.mk' _)).comp φ.toMonoidHom
  have hβ : Function.Surjective β :=
    (e.symm.surjective.comp (QuotientGroup.mk'_surjective _)).comp φ.surjective
  have hker : β.ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) K) := by
    ext x
    have h1 : x ∈ β.ker ↔
        φ x ∈ (StatedScalars (Fin (m + 1)) K).subgroupOf (StatedSL (m + 1) K) := by
      rw [← ker_comp_mk' _ e.symm]
      rfl
    rw [h1, ← CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars]
    exact ⟨fun ⟨y, hy, hxy⟩ => (φ.injective hxy) ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  have hsplit : ∀ (E : Type) [Group E] [Finite E]
      (π : E →* Matrix.SpecialLinearGroup (Fin (m + 1)) K), Function.Surjective π →
        π.ker ≤ Subgroup.center E → IsPGroup 2 π.ker →
          ∃ σ : Matrix.SpecialLinearGroup (Fin (m + 1)) K →* E, ∀ x, π (σ x) = x :=
    fun E _ _ π hπ hcen h2 =>
      (sl_central_two_extension_splitting m hk hπ hcen h2).imp fun _ h => h.1
  have : IsCyclic β.ker := hker ▸ isCyclic_center_specialLinearGroup (m + 1) K
  refine ⟨isCyclic_ker_of_isPerfect hsplit hβ hη hC h2,
    (card_ker_dvd_of_isPerfect hsplit hβ hη hC h2).trans ?_⟩
  rw [hker, ← hK]
  exact card_center_specialLinearGroup_dvd (by omega) K

theorem odd_linear_two_perfect_central_two_kernel_order_at_most_two {p f : ℕ} (hp2 : p ≠ 2)
    {P Q : Type} [Group P] [Group Q] [Finite P] (hP : Group.IsPerfect P) {η : P →* Q}
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center P) (h2 : IsPGroup 2 η.ker)
    (hQ : LieModel Q .PSL 2 p f) : Nat.card η.ker ≤ 2 :=
  (Nat.le_of_dvd (by norm_num) ((odd_field_higher_linear_perfect_central_two_kernel_cyclic hp2 hP
    hη hC h2 hQ).2.trans (Nat.gcd_dvd_left 2 _)))

end CFSG.LieType.Steinberg

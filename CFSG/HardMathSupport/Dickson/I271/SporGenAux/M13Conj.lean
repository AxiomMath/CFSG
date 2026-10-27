module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.CentGenPair

public section

namespace CFSG.HardMathSupport.Dickson.I271.M13

open CFSG.HardMathSupport.Dickson.I271

variable {G : Type*} [Group G]

theorem closure_pair_eq (u v : G) :
    Subgroup.closure ({u, v} : Set G) = Subgroup.zpowers u ⊔ Subgroup.zpowers v := by
  rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
    ← Subgroup.zpowers_eq_closure]

theorem zpowers_pow_eq {u : G} (hu : orderOf u = 13) {n : ℕ} (hn : n % 13 ≠ 0) :
    Subgroup.zpowers (u ^ n) = Subgroup.zpowers u := by
  apply le_antisymm
  · rw [Subgroup.zpowers_le]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers u) n
  · rw [Subgroup.zpowers_le]
    have hcop : Nat.Coprime n 13 := by
      have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
      exact (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2
        (fun h => hn (Nat.mod_eq_zero_of_dvd h)) |>.symm
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by norm_num)
    have h13 : u ^ 13 = 1 := hu ▸ pow_orderOf_eq_one u
    have h : u = (u ^ n) ^ m := by
      rw [← pow_mul, pow_eq_pow_mod (n * m) h13, hm, pow_one]
    have h' := Subgroup.pow_mem (Subgroup.zpowers (u ^ n)) (Subgroup.mem_zpowers (u ^ n)) m
    rwa [← h] at h'

theorem map_conj_plane (W u v : G) :
    (Subgroup.zpowers u ⊔ Subgroup.zpowers v).map (MulAut.conj W).toMonoidHom =
      Subgroup.zpowers (W * u * W⁻¹) ⊔ Subgroup.zpowers (W * v * W⁻¹) := by
  rw [Subgroup.map_sup, MonoidHom.map_zpowers (MulAut.conj W).toMonoidHom u,
    MonoidHom.map_zpowers (MulAut.conj W).toMonoidHom v]
  simp [MulAut.conj_apply]

theorem conj_plane_eq {W u v t₁ t₂ : G} (h₁ : orderOf t₁ = 13) (h₂ : orderOf t₂ = 13) {a b : ℕ}
    (ha : a % 13 ≠ 0) (hb : b % 13 ≠ 0) (hu : W * u * W⁻¹ = t₁ ^ a) (hv : W * v * W⁻¹ = t₂ ^ b) :
    (Subgroup.zpowers u ⊔ Subgroup.zpowers v).map (MulAut.conj W).toMonoidHom =
      Subgroup.zpowers t₁ ⊔ Subgroup.zpowers t₂ := by
  rw [map_conj_plane, hu, hv, zpowers_pow_eq h₁ ha, zpowers_pow_eq h₂ hb]

theorem closure_centSet_of_map_eq (φ : G ≃* G) {P Q : Subgroup G} (h : P.map φ.toMonoidHom = Q)
    (hQ : Subgroup.closure (centSet Q) = ⊤) : Subgroup.closure (centSet P) = ⊤ := by
  have := closure_centSet_map φ.symm hQ
  have hP : Q.map φ.symm.toMonoidHom = P := by
    rw [← h, Subgroup.map_map]
    ext x
    simp
  rw [hP] at this
  exact this

end CFSG.HardMathSupport.Dickson.I271.M13

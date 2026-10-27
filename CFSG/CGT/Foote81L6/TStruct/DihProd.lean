module

public import CFSG.CGT.Foote81L6.TStruct.OddAut
public import CFSG.CGT.Foote81L6.TStruct.DihSub
public import CFSG.GroupTheory.DihedralSubgroups

public section

namespace CFSG.CGT.Foote81L6.TStruct

open Subgroup DihedralGroup

variable {G : Type*} [Group G]

private theorem not_isCyclic_of_four {K : Type*} [Group K] {V W : Subgroup K} (hWV : W ≤ V)
    (hW2 : ∀ x ∈ W, x * x = 1) (hW4 : Nat.card W = 4) : ¬ IsCyclic V := by
  intro hV
  haveI : IsCyclic W := Subgroup.isCyclic_of_le hWV
  have hexp : Monoid.exponent W ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one fun g => by
    rw [pow_two]
    exact Subtype.ext (hW2 g g.2)
  rw [IsCyclic.exponent_eq_card, hW4] at hexp
  norm_num at hexp

theorem exists_dihedral_of_four {H V W : Subgroup G} {k : ℕ} (e : H ≃* DihedralGroup (2 ^ k))
    (hVH : V ≤ H) (hW : IsFourIn H W) (hWV : W ≤ V) :
    ∃ j, 1 ≤ j ∧ Nonempty (V ≃* DihedralGroup (2 ^ j)) := by
  have hWV' : lowerSub e W ≤ lowerSub e V :=
    map_mono fun x hx => mem_subgroupOf.2 (hWV (mem_subgroupOf.1 hx))
  have hnc : ¬ IsCyclic (lowerSub e V) :=
    not_isCyclic_of_four hWV' (mul_self_lowerSub e hW.2.1) (by rw [card_lowerSub e hW.1, hW.2.2])
  obtain ⟨j, hj, -, ⟨φ⟩⟩ := CFSG.GorensteinWalter.noncyclic_subgroup_dihedral_two_pow _ hnc
  exact ⟨j, hj, ⟨((subgroupOfEquivOfLe hVH).symm.trans
    ((V.subgroupOf H).equivMapOfInjective e.toMonoidHom e.injective)).trans φ⟩⟩

section Prod3

variable {H₀ H₁ H₂ : Subgroup G} {a : Fin 3 → ℕ}
  (e₀ : H₀ ≃* DihedralGroup (2 ^ a 0)) (e₁ : H₁ ≃* DihedralGroup (2 ^ a 1))
  (e₂ : H₂ ≃* DihedralGroup (2 ^ a 2))
  (h01 : ∀ x ∈ H₀, ∀ y ∈ H₁, x * y = y * x) (h02 : ∀ x ∈ H₀, ∀ y ∈ H₂, x * y = y * x)
  (h12 : ∀ x ∈ H₁, ∀ y ∈ H₂, x * y = y * x)

private theorem mul3_mul3 {u₀ v₀ u₁ v₁ u₂ v₂ : G} (c₁ : v₀ * u₁ = u₁ * v₀)
    (c₂ : v₀ * u₂ = u₂ * v₀) (c₃ : v₁ * u₂ = u₂ * v₁) :
    u₀ * v₀ * (u₁ * v₁ * (u₂ * v₂)) = u₀ * (u₁ * u₂) * (v₀ * (v₁ * v₂)) := by
  calc u₀ * v₀ * (u₁ * v₁ * (u₂ * v₂)) = u₀ * (v₀ * u₁) * (v₁ * u₂) * v₂ := by
        simp only [mul_assoc]
    _ = u₀ * u₁ * (v₀ * u₂) * v₁ * v₂ := by rw [c₁, c₃]; simp only [mul_assoc]
    _ = u₀ * (u₁ * u₂) * (v₀ * (v₁ * v₂)) := by rw [c₂]; simp only [mul_assoc]

private def prod3 : PX a →* G where
  toFun p := ((e₀.symm (p 0) : H₀) : G) * (((e₁.symm (p 1) : H₁) : G) * ((e₂.symm (p 2) : H₂) : G))
  map_one' := by simp
  map_mul' p q := by
    simp only [Pi.mul_apply, map_mul, Subgroup.coe_mul]
    exact mul3_mul3 (h01 _ (e₀.symm (q 0)).2 _ (e₁.symm (p 1)).2)
      (h02 _ (e₀.symm (q 0)).2 _ (e₂.symm (p 2)).2) (h12 _ (e₁.symm (q 1)).2 _ (e₂.symm (p 2)).2)

private theorem prod3_apply (p : PX a) : prod3 e₀ e₁ e₂ h01 h02 h12 p =
    ((e₀.symm (p 0) : H₀) : G) * (((e₁.symm (p 1) : H₁) : G) * ((e₂.symm (p 2) : H₂) : G)) := rfl

private theorem prod3_mulSingle₀ (d : DihedralGroup (2 ^ a 0)) :
    prod3 e₀ e₁ e₂ h01 h02 h12 (Pi.mulSingle 0 d) = ((e₀.symm d : H₀) : G) := by
  rw [prod3_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (by decide : (1 : Fin 3) ≠ 0),
    Pi.mulSingle_eq_of_ne (by decide : (2 : Fin 3) ≠ 0)]
  simp

private theorem prod3_mulSingle₁ (d : DihedralGroup (2 ^ a 1)) :
    prod3 e₀ e₁ e₂ h01 h02 h12 (Pi.mulSingle 1 d) = ((e₁.symm d : H₁) : G) := by
  rw [prod3_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (by decide : (0 : Fin 3) ≠ 1),
    Pi.mulSingle_eq_of_ne (by decide : (2 : Fin 3) ≠ 1)]
  simp

private theorem prod3_mulSingle₂ (d : DihedralGroup (2 ^ a 2)) :
    prod3 e₀ e₁ e₂ h01 h02 h12 (Pi.mulSingle 2 d) = ((e₂.symm d : H₂) : G) := by
  rw [prod3_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (by decide : (0 : Fin 3) ≠ 2),
    Pi.mulSingle_eq_of_ne (by decide : (1 : Fin 3) ≠ 2)]
  simp

private theorem prod3_injective (hi0 : H₀ ⊓ (H₁ ⊔ H₂) = ⊥) (hi1 : H₁ ⊓ H₂ = ⊥) :
    Function.Injective (prod3 e₀ e₁ e₂ h01 h02 h12) := by
  rw [injective_iff_map_eq_one]
  intro p hp
  rw [prod3_apply] at hp
  have hx0 : ((e₀.symm (p 0) : H₀) : G) = 1 := by
    have hmem : ((e₀.symm (p 0) : H₀) : G) ∈ H₀ ⊓ (H₁ ⊔ H₂) := by
      refine mem_inf.2 ⟨(e₀.symm (p 0)).2, ?_⟩
      rw [eq_inv_of_mul_eq_one_left hp]
      exact inv_mem (mul_mem (mem_sup_left (e₁.symm (p 1)).2) (mem_sup_right (e₂.symm (p 2)).2))
    rw [hi0] at hmem
    exact mem_bot.1 hmem
  rw [hx0, one_mul] at hp
  have hx1 : ((e₁.symm (p 1) : H₁) : G) = 1 := by
    have hmem : ((e₁.symm (p 1) : H₁) : G) ∈ H₁ ⊓ H₂ := by
      refine mem_inf.2 ⟨(e₁.symm (p 1)).2, ?_⟩
      rw [eq_inv_of_mul_eq_one_left hp]
      exact inv_mem (e₂.symm (p 2)).2
    rw [hi1] at hmem
    exact mem_bot.1 hmem
  rw [hx1, one_mul] at hp
  have h0 : p 0 = 1 := by simpa using congrArg e₀ (Subtype.ext hx0 : e₀.symm (p 0) = 1)
  have h1 : p 1 = 1 := by simpa using congrArg e₁ (Subtype.ext hx1 : e₁.symm (p 1) = 1)
  have h2 : p 2 = 1 := by simpa using congrArg e₂ (Subtype.ext hp : e₂.symm (p 2) = 1)
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

private theorem prod3_range : (prod3 e₀ e₁ e₂ h01 h02 h12).range = H₀ ⊔ (H₁ ⊔ H₂) := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    rw [prod3_apply]
    exact mul_mem (mem_sup_left (e₀.symm (p 0)).2)
      (mem_sup_right (mul_mem (mem_sup_left (e₁.symm (p 1)).2) (mem_sup_right (e₂.symm (p 2)).2)))
  · refine sup_le (fun u hu => ⟨Pi.mulSingle 0 (e₀ ⟨u, hu⟩), ?_⟩)
      (sup_le (fun u hu => ⟨Pi.mulSingle 1 (e₁ ⟨u, hu⟩), ?_⟩)
        (fun u hu => ⟨Pi.mulSingle 2 (e₂ ⟨u, hu⟩), ?_⟩))
    · rw [prod3_mulSingle₀, MulEquiv.symm_apply_apply]
    · rw [prod3_mulSingle₁, MulEquiv.symm_apply_apply]
    · rw [prod3_mulSingle₂, MulEquiv.symm_apply_apply]

include e₂ h01 h02 h12 in
theorem comm_central_or_conj_zc (hi0 : H₀ ⊓ (H₁ ⊔ H₂) = ⊥) (hi1 : H₁ ⊓ H₂ = ⊥) {y : G}
    (hy : (H₀ ⊔ (H₁ ⊔ H₂)).map (MulAut.conj y).toMonoidHom = H₀ ⊔ (H₁ ⊔ H₂)) {N : ℕ}
    (hN : Odd N) (hyN : y ^ N = 1) :
    (∀ x ∈ H₀ ⊔ (H₁ ⊔ H₂), ∀ z ∈ H₀ ⊔ (H₁ ⊔ H₂),
        z * (x⁻¹ * (y * x * y⁻¹)) = (x⁻¹ * (y * x * y⁻¹)) * z) ∨
      ((∀ i, 2 ≤ a i) ∧ ∃ m : ℕ, y ^ m * ((e₀.symm (zc (a 0)) : H₀) : G) * (y ^ m)⁻¹ =
        ((e₁.symm (zc (a 1)) : H₁) : G)) := by
  set Φ := prod3 e₀ e₁ e₂ h01 h02 h12 with hΦdef
  have hinj : Function.Injective Φ := prod3_injective e₀ e₁ e₂ h01 h02 h12 hi0 hi1
  have hrange : Φ.range = H₀ ⊔ (H₁ ⊔ H₂) := prod3_range e₀ e₁ e₂ h01 h02 h12
  have hmap : Φ.range.map (MulAut.conj y).toMonoidHom = Φ.range := by rw [hrange]; exact hy
  let Φ' : PX a ≃* Φ.range := MonoidHom.ofInjective hinj
  let ψ : Φ.range ≃* Φ.range :=
    ((MulAut.conj y).subgroupMap Φ.range).trans (MulEquiv.subgroupCongr hmap)
  let y' : MulAut (PX a) := (Φ'.trans ψ).trans Φ'.symm
  have hy' : ∀ p, Φ (y' p) = y * Φ p * y⁻¹ := by
    intro p
    have h1 : ((Φ' (y' p) : Φ.range) : G) = Φ (y' p) := MonoidHom.ofInjective_apply hinj
    rw [← h1]
    show ((Φ' (Φ'.symm (ψ (Φ' p))) : Φ.range) : G) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hpow : ∀ m p, Φ ((y' ^ m) p) = y ^ m * Φ p * (y ^ m)⁻¹ := by
    intro m
    induction m with
    | zero => intro p; simp
    | succ m ih =>
      intro p
      rw [mulAut_pow_apply_succ, hy', ih, pow_succ']
      group
  have hy'N : y' ^ N = 1 := by
    refine MulEquiv.ext fun p => hinj ?_
    rw [hpow, hyN, MulAut.one_apply]
    group
  rcases comm_central_or_transitive y' hN hy'N with h | ⟨hall, htr⟩
  · left
    intro x hx z hz
    rw [← hrange] at hx hz
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨q, rfl⟩ := hz
    have e : (Φ p)⁻¹ * (y * Φ p * y⁻¹) = Φ (p⁻¹ * y' p) := by rw [map_mul, map_inv, hy']
    rw [e, ← map_mul, ← map_mul, h p q]
  · right
    refine ⟨hall, ?_⟩
    obtain ⟨m, hm⟩ := htr 0 1
    have hzz : ∀ j : Fin 3, zz a j = Pi.mulSingle j (zc (a j)) := by
      intro j
      ext k
      by_cases hk : k = j
      · subst hk; rw [Pi.mulSingle_eq_same, zz_apply_same]
      · rw [Pi.mulSingle_eq_of_ne hk, zz_apply_ne hk]
    refine ⟨m, ?_⟩
    have := congrArg Φ hm
    rwa [hpow, hzz, hzz, prod3_mulSingle₀, prod3_mulSingle₁] at this

end Prod3

end CFSG.CGT.Foote81L6.TStruct

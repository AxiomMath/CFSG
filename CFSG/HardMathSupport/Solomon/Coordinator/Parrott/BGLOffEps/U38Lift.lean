module

public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.U38

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

variable {K Q : Type*} [Group K] [Group Q]

@[expose] def fixJoin (bf bx : MulAut Q) : Subgroup Q :=
  ⨆ (i : ℕ) (_ : i < 3), ⁅fixSubgroup (bf * bx ^ i), fixSubgroup (bf * bx ^ i)⁆

theorem map_pow_apply (π : K →* Q) {α : MulAut K} {β : MulAut Q}
    (h : ∀ k, π (α k) = β (π k)) (i : ℕ) (k : K) : π ((α ^ i) k) = (β ^ i) (π k) := by
  induction i generalizing k with
  | zero => rfl
  | succ n ih => rw [pow_succ, MulAut.mul_apply, ih, h, pow_succ, MulAut.mul_apply]

theorem commutator_fixSubgroup_le_map (π : K →* Q) (hker : π.ker ≤ Subgroup.center K)
    (hπ : Function.Surjective π) (α : MulAut K) (β : MulAut Q)
    (hαβ : ∀ k, π (α k) = β (π k)) :
    ⁅fixSubgroup β, fixSubgroup β⁆ ≤ (fixSubgroup α).map π := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨k₁, rfl⟩ := hπ a
  obtain ⟨k₂, rfl⟩ := hπ b
  exact ⟨⁅k₁, k₂⁆, comm_mem_fixSubgroup π hker α β hαβ ha hb, map_commutatorElement _ _ _⟩

theorem top_le_of_fixJoin (π : K →* Q) (hker : π.ker ≤ Subgroup.center K)
    (hπ : Function.Surjective π) (hK : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤)
    (f x : MulAut K) (bf bx : MulAut Q) (hf : ∀ k, π (f k) = bf (π k))
    (hx : ∀ k, π (x k) = bx (π k)) (hQ : (⊤ : Subgroup Q) ≤ fixJoin bf bx) :
    (⊤ : Subgroup K) ≤ Lemma512Ns.fixedSub x ⊔
      ⨆ (i : ℕ) (_ : i < 3), Lemma512Ns.fixedSub (f * x ^ i) := by
  set M := Lemma512Ns.fixedSub x ⊔ ⨆ (i : ℕ) (_ : i < 3), Lemma512Ns.fixedSub (f * x ^ i)
    with hM
  have hfi : ∀ (i : ℕ) (k : K), π ((f * x ^ i) k) = (bf * bx ^ i) (π k) := fun i k => by
    rw [MulAut.mul_apply, MulAut.mul_apply, hf, map_pow_apply π hx]
  have hmap : M.map π = ⊤ := by
    rw [eq_top_iff]
    refine hQ.trans (iSup₂_le fun i hi => ?_)
    refine (commutator_fixSubgroup_le_map π hker hπ _ _ (hfi i)).trans (Subgroup.map_mono ?_)
    exact le_sup_of_le_right (le_iSup₂_of_le i hi le_rfl)
  have hMZ : M ⊔ π.ker = ⊤ := by
    have h2 := Subgroup.comap_map_eq π M
    rw [hmap, Subgroup.comap_top] at h2
    exact h2.symm
  rw [← hK, Subgroup.commutator_le]
  intro k₁ _ k₂ _
  have hk₁ : k₁ ∈ M ⊔ π.ker := by rw [hMZ]; trivial
  have hk₂ : k₂ ∈ M ⊔ π.ker := by rw [hMZ]; trivial
  obtain ⟨m₁, hm₁, z₁, hz₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hk₁
  obtain ⟨m₂, hm₂, z₂, hz₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hk₂
  rw [commutatorElement_mul_mul' (Commute.symm (Subgroup.mem_center_iff.1 (hker hz₁) m₂))
    (Commute.symm (Subgroup.mem_center_iff.1 (hker hz₁) z₂))
    (Commute.symm (Subgroup.mem_center_iff.1 (hker hz₂) m₁))]
  exact M.mul_mem (M.mul_mem (M.mul_mem hm₁ hm₂) (M.inv_mem hm₁)) (M.inv_mem hm₂)

theorem fixSubgroup_inv (β : MulAut Q) : fixSubgroup β⁻¹ = fixSubgroup β := by
  ext y
  rw [mem_fixSubgroup, mem_fixSubgroup]
  constructor
  · intro h
    calc β y = β (β⁻¹ y) := by rw [h]
      _ = y := MulAut.apply_inv_self _ β y
  · intro h
    calc β⁻¹ y = β⁻¹ (β y) := by rw [h]
      _ = y := MulAut.inv_apply_self _ β y

theorem fixSubgroup_conj (κ β : MulAut Q) :
    fixSubgroup (κ * β * κ⁻¹) = (fixSubgroup β).map κ.toMonoidHom := by
  ext y
  rw [mem_fixSubgroup, Subgroup.mem_map]
  constructor
  · intro h
    refine ⟨κ⁻¹ y, ?_, MulAut.apply_inv_self _ κ y⟩
    rw [mem_fixSubgroup]
    have h1 : κ (β (κ⁻¹ y)) = y := h
    calc β (κ⁻¹ y) = κ⁻¹ (κ (β (κ⁻¹ y))) := (MulAut.inv_apply_self _ κ _).symm
      _ = κ⁻¹ y := by rw [h1]
  · rintro ⟨z, hz, rfl⟩
    rw [mem_fixSubgroup] at hz
    change κ (β (κ⁻¹ (κ z))) = κ z
    rw [MulAut.inv_apply_self, hz]

theorem fixJoin_conj (κ bf bx : MulAut Q) :
    fixJoin (κ * bf * κ⁻¹) (κ * bx * κ⁻¹) = (fixJoin bf bx).map κ.toMonoidHom := by
  simp only [fixJoin, Subgroup.map_iSup]
  refine iSup_congr fun i => iSup_congr fun _ => ?_
  have e : κ * bf * κ⁻¹ * (κ * bx * κ⁻¹) ^ i = κ * (bf * bx ^ i) * κ⁻¹ := by
    rw [conj_pow]
    group
  rw [e, fixSubgroup_conj, Subgroup.map_commutator]

theorem fixJoin_inv_le (bf bx : MulAut Q) (hc : bf * bx = bx * bf) (h3 : bx ^ 3 = 1) :
    fixJoin bf⁻¹ bx ≤ fixJoin bf bx := by
  refine iSup₂_le fun i hi => ?_
  have key : ∀ j : ℕ, j < 3 → bf⁻¹ * bx ^ i = (bf * bx ^ j)⁻¹ → ⁅fixSubgroup (bf⁻¹ * bx ^ i),
      fixSubgroup (bf⁻¹ * bx ^ i)⁆ ≤ fixJoin bf bx := by
    intro j hj e
    rw [e, fixSubgroup_inv]
    exact le_iSup₂_of_le j hj le_rfl
  have hcp : ∀ n : ℕ, bf * bx ^ n = bx ^ n * bf := fun n => (Commute.pow_right hc n).eq
  interval_cases i
  · exact key 0 (by norm_num) (by simp)
  · refine key 2 (by norm_num) (eq_inv_of_mul_eq_one_right ?_)
    calc bf * bx ^ 2 * (bf⁻¹ * bx ^ 1) = bx ^ 2 * bf * (bf⁻¹ * bx ^ 1) := by rw [hcp 2]
      _ = bx ^ 3 := by group
      _ = 1 := h3
  · refine key 1 (by norm_num) (eq_inv_of_mul_eq_one_right ?_)
    calc bf * bx ^ 1 * (bf⁻¹ * bx ^ 2) = bx ^ 1 * bf * (bf⁻¹ * bx ^ 2) := by rw [hcp 1]
      _ = bx ^ 3 := by group
      _ = 1 := h3

end CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.U38

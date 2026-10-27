module

public import CFSG.LargeExtraspecial.S14SMKGram
public import CFSG.LargeExtraspecial.SMod20Rho
public import CFSG.LargeExtraspecial.SMod20UaRank

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.SMK

open Subgroup CFSG.Open CFSG.Fischer CFSG.SmithE CFSG.LargeExtraspecial.SMod20 QuadraticMap

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem ncard_wPlane_inter {i j : ℕ} (hi : i < 891)
    (hj : j < 891) : (wPlane i ∩ wPlane j).ncard = meetCard i j := by
  rw [wPlane_eq_planeSet hi, wPlane_eq_planeSet hj, ← Finset.coe_inter, Set.ncard_coe_finset,
    meetCard_eq_card hi]

theorem meetCard_eq_of_distB_eq {i j i' j' : ℕ} (hi : i < 891)
    (hj : j < 891) (hi' : i' < 891) (hj' : j' < 891) (h : distB i j = distB i' j') :
    meetCard i j = meetCard i' j' := by
  rcases (dist_parts hi hj).1 with h1 | h1 | h1 | h1 <;>
    rcases (dist_parts hi' hj').1 with h2 | h2 | h2 | h2 <;>
    simp [distB, h1, h2] at h ⊢

theorem distB_self {i : ℕ} (hi : i < 891) : distB i i = 0 := by
  have h : meetCard i i = 21 := by rw [meetCard_eq_card hi, Finset.inter_self, card_planeSet hi]
  simp [distB, h]

theorem exists_relMask (Γ : ℕ → ℕ → ZMod 2)
    (hconst : ∀ i j i' j' : Fin 891, distB i j = distB i' j' → Γ i j = Γ i' j')
    (h0 : ∀ i : Fin 891, Γ i i = 0) :
    ∃ R : ℕ, R < 16 ∧ R % 2 = 0 ∧ ∀ i j, i < 891 → j < 891 → Γ i j = bit (relB R i j) := by
  set r : ℕ → ZMod 2 := fun d => Classical.epsilon fun v : ZMod 2 =>
    ∃ i j : Fin 891, distB i j = d ∧ Γ i j = v with hrdef
  have hr : ∀ i j : Fin 891, Γ i j = r (distB i j) := by
    intro i j
    obtain ⟨i', j', hd, hv⟩ := Classical.epsilon_spec
      (p := fun v : ZMod 2 => ∃ i' j' : Fin 891, distB i' j' = distB i j ∧ Γ i' j' = v)
      ⟨Γ i j, i, j, rfl, rfl⟩
    rw [hrdef]
    exact (hconst i j i' j' hd.symm).trans hv
  have hr0 : r 0 = 0 := by
    rw [← distB_self (show (0 : ℕ) < 891 by norm_num), ← h0 ⟨0, by norm_num⟩]
    exact (hr ⟨0, by norm_num⟩ ⟨0, by norm_num⟩).symm
  have hval : ∀ a b c : ZMod 2,
      (a.val * 2 + b.val * 4 + c.val * 8 < 16 ∧ (a.val * 2 + b.val * 4 + c.val * 8) % 2 = 0) ∧
      bit ((a.val * 2 + b.val * 4 + c.val * 8).testBit 0) = 0 ∧
      bit ((a.val * 2 + b.val * 4 + c.val * 8).testBit 1) = a ∧
      bit ((a.val * 2 + b.val * 4 + c.val * 8).testBit 2) = b ∧
      bit ((a.val * 2 + b.val * 4 + c.val * 8).testBit 3) = c := by decide
  obtain ⟨⟨h16, h2⟩, b0, b1, b2, b3⟩ := hval (r 1) (r 2) (r 3)
  refine ⟨_, h16, h2, fun i j hi hj => ?_⟩
  rw [show Γ i j = r (distB i j) from hr ⟨i, hi⟩ ⟨j, hj⟩, relB]
  have hd := distB_le i j
  interval_cases h : distB i j
  · rw [b0, hr0]
  · rw [b1]
  · rw [b2]
  · rw [b3]

@[expose] noncomputable def gram
    (S : Setting G) (ψ : Mbar0 S ≃* T46) (i j : ℕ) : ZMod 2 :=
  polar S.q (xcl S ψ i) (xcl S ψ j)

section Gram

variable
  [IsSimpleGroup G] (I : Inputs10) (ψ : Mbar0 S ≃* T46)

omit
  [IsSimpleGroup G] in
theorem gram_self (i : ℕ) : gram S ψ i i = 0 := by
  rw [gram, polar_self]
  generalize S.q (xcl S ψ i) = a
  revert a
  decide

include I in
theorem gram_planeHom (hw : S.width = 10) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (m : S.M) (i j : Fin 891) :
    gram S ψ (planeHom S ψ (rhoM S m) i) (planeHom S ψ (rhoM S m) j) = gram S ψ i j := by
  rw [gram, gram, ← ρ_xcl I ψ hw haQ hne m i, ← ρ_xcl I ψ hw haQ hne m j]
  exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (S.ρ m).2 _ _

include I in
theorem exists_gram_eq_zero (hw : S.width = 10) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (i j : Fin 891) :
    ∃ j₀ : Fin 891, gram S ψ i j = gram S ψ 0 j₀ ∧
      (wPlane 0 ∩ wPlane j₀).ncard = (wPlane i ∩ wPlane j).ncard := by
  obtain ⟨x, hx, hxW⟩ := exists_image_wPlane_zero i.2
  obtain ⟨m, hm⟩ := exists_piM_rhoM ψ (T46.inv_mem hx)
  have h0 : planeHom S ψ (rhoM S m) i = 0 := by
    rw [planeHom_eq_iff, hm]
    exact image_wPlane_inv hxW
  refine ⟨planeHom S ψ (rhoM S m) j, ?_, ?_⟩
  · rw [← gram_planeHom I ψ hw haQ hne m i j, h0]
    rfl
  · have e0 : wPlane (0 : ℕ) = ⇑(piM S ψ (rhoM S m)) '' wPlane i := by
      rw [image_wPlane_piM, h0]
      rfl
    rw [e0, ← image_wPlane_piM, ← Set.image_inter (Equiv.injective _),
      Set.ncard_image_of_injective _ (Equiv.injective _)]

include I in
theorem gram_eq_of_ncard_eq (hw : S.width = 10) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) {i j i' j' : Fin 891}
    (h : (wPlane i ∩ wPlane j).ncard = (wPlane i' ∩ wPlane j').ncard) :
    gram S ψ i j = gram S ψ i' j' := by
  obtain ⟨j₀, e1, n1⟩ := exists_gram_eq_zero I ψ hw haQ hne i j
  obtain ⟨j₁, e2, n2⟩ := exists_gram_eq_zero I ψ hw haQ hne i' j'
  obtain ⟨t, ht, htW⟩ := exists_PA_image (i := 0) (by norm_num) j₀.2 j₁.2 (by rw [n1, n2, h])
  obtain ⟨m, hm⟩ := exists_piM_rhoM ψ (mem_inf.1 ht).1
  have h0 : planeHom S ψ (rhoM S m) 0 = 0 := by
    rw [planeHom_eq_iff, hm]
    exact mem_stabilizer_wPlane.1 (mem_inf.1 ht).2
  have h1 : planeHom S ψ (rhoM S m) j₀ = j₁ := by
    rw [planeHom_eq_iff, hm]
    exact htW
  have e3 := gram_planeHom I ψ hw haQ hne m 0 j₀
  rw [h0, h1] at e3
  rw [e1, e2]
  exact e3.symm

include I in
theorem gram_eq_of_distB_eq (hw : S.width = 10) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) {i j i' j' : Fin 891}
    (h : distB i j = distB i' j') : gram S ψ i j = gram S ψ i' j' :=
  gram_eq_of_ncard_eq I ψ hw haQ hne (by
    rw [ncard_wPlane_inter i.2 j.2, ncard_wPlane_inter i'.2 j'.2]
    exact meetCard_eq_of_distB_eq i.2 j.2 i'.2 j'.2 h)

include I in
theorem gram_eq_bit_eight
    (hw : S.width = 10) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    {i j : ℕ} (hi : i < 891) (hj : j < 891) : gram S ψ i j = bit (relB 8 i j) := by
  obtain ⟨R, h16, h2, hR⟩ := exists_relMask (gram S ψ)
    (fun i j i' j' h => gram_eq_of_distB_eq I ψ hw haQ hne h) (fun i => gram_self ψ i)
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hdim : Module.finrank (ZMod 2) S.Qt ≤ 20 := by
    rw [S.finrank_Qt_eq_two_mul_width, hw]
  rcases rel_eq_of_gram h16 h2 hdim S.q.polarBilin (xcl S ψ)
      (fun i j hi hj => by rw [polarBilin_apply_apply]; exact hR i j hi hj) with rfl | rfl
  · exfalso
    have hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6) := ⟨ψ.trans tpsuT46.symm⟩
    apply irreducible I.hDW hw hU haQ hne
    refine SmithQ.isReducible_of_commute S (by omega) (isConj_iff.mpr ⟨g, rfl⟩) haQ hne
      fun x y hx hxQ hy hyQ => ?_
    by_contra hxy
    obtain ⟨c, rfl⟩ := isConj_iff.mp hx
    obtain ⟨d, rfl⟩ := isConj_iff.mp hy
    have hxz : c * S.z * c⁻¹ ≠ S.z := fun h => hxy (by rw [h]; exact (S.z_comm_QG hyQ).symm)
    have hyz : d * S.z * d⁻¹ ≠ S.z := fun h => hxy (by rw [h]; exact S.z_comm_QG hxQ)
    have h1 := (S.polar_cl_eq_one_iff hxQ hyQ).mpr hxy
    rw [cl_eq_xcl I ψ hw hxQ hxz, cl_eq_xcl I ψ hw hyQ hyz] at h1
    have h3 := hR _ _ (planeOf S ψ c).2 (planeOf S ψ d).2
    rw [gram, h1] at h3
    simp [relB, bit] at h3
  · exact hR i j hi hj

open Classical in
include I in
theorem gram_eq_opp
    (hw : S.width = 10) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    {i j : ℕ} (hi : i < 891) (hj : j < 891) :
    polar S.q (xcl S ψ i) (xcl S ψ j) = if Opp i j then 1 else 0 := by
  rw [← gram, gram_eq_bit_eight I ψ hw haQ hne hi hj]
  by_cases h : Opp i j
  · rw [(relB_eight_iff hi hj).2 h]
    simp [h, bit]
  · have h' : relB 8 i j = false := by
      cases h' : relB 8 i j
      · rfl
      · exact absurd ((relB_eight_iff hi hj).1 h') h
    rw [h']
    simp [h, bit]

include I in
theorem commute_iff_not_opp
    (hw : S.width = 10) {g h k : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hbQ : h * S.z * h⁻¹ ∈ S.QG) (hbne : h * S.z * h⁻¹ ≠ S.z) (hcQ : k * S.z * k⁻¹ ∈ S.QG)
    (hcne : k * S.z * k⁻¹ ≠ S.z) :
    h * S.z * h⁻¹ * (k * S.z * k⁻¹) = k * S.z * k⁻¹ * (h * S.z * h⁻¹) ↔
      ¬ Opp (planeOf S ψ h) (planeOf S ψ k) := by
  classical
  rw [← S.polar_cl_eq_zero_iff hbQ hcQ, cl_eq_xcl I ψ hw hbQ hbne, cl_eq_xcl I ψ hw hcQ hcne,
    gram_eq_opp I ψ hw haQ hne (planeOf S ψ h).2 (planeOf S ψ k).2]
  by_cases ho : Opp (planeOf S ψ h) (planeOf S ψ k)
  · simp [ho]
  · simp [ho]

end Gram

end CFSG.LargeExtraspecial.S14.SMK

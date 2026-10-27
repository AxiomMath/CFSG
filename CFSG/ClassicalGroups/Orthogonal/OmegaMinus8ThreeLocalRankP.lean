module

public import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalPlanes

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal

open Module QuadraticMap CFSG.GroupTheory.WeirSylow CFSG.ClassicalGroups.Orthogonal
open CFSG.Open (pRank)

variable {K : Type} [Field K] {b c : K}

theorem planeExtend_commute_planeExtend_of_ne {i j : Fin 3} (hij : i ≠ j)
    (g h : (K × K) ≃ₗ[K] (K × K)) : Commute (planeExtend K i g) (planeExtend K j h) := by
  refine LinearEquiv.ext fun x => Prod.ext (funext fun k => ?_) rfl
  simp only [LinearEquiv.mul_apply, planeExtend_apply]
  by_cases hki : k = i
  · subst hki
    simp [Function.update_of_ne hij]
  · by_cases hkj : k = j
    · subst hkj
      simp [Function.update_of_ne hki]
    · simp [Function.update_of_ne hki, Function.update_of_ne hkj]

theorem planeExtend_zpow_apply_planeVec_of_ne {i j : Fin 3} (hji : j ≠ i)
    (g : (K × K) ≃ₗ[K] (K × K)) (k : ℤ) (p : K × K) :
    (planeExtend K i g ^ k) (planeVec j p) = planeVec j p := by
  rw [← map_zpow, planeExtend_apply_planeVec_of_ne hji]

theorem planeExtend_not_mem_zpowers_of_ne {i j : Fin 3} (hij : i ≠ j)
    (g : (K × K) ≃ₗ[K] (K × K)) {h : (K × K) ≃ₗ[K] (K × K)} (hh : h ≠ 1) :
    planeExtend K j h ∉ Subgroup.zpowers (planeExtend K i g) := by
  rintro ⟨k, hk⟩
  apply hh
  refine LinearEquiv.ext fun p => ?_
  have h1 := congrArg (fun e => e (planeVec j p)) hk
  simp only [planeExtend_zpow_apply_planeVec_of_ne hij.symm, planeExtend_apply_planeVec_self] at h1
  have h2 := congrArg (fun x : ModelSpace K => x.1 j) h1
  simpa [planeVec] using h2.symm

theorem exists_pair_centralizer_c₀_range [Finite K] (h3 : (3 : K) ≠ 0)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpd : p ∣ minusPi (Nat.card K)) :
    ∃ x y : ModelSpace K ≃ₗ[K] ModelSpace K, x ∈ modelOmega b c ∧ y ∈ modelOmega b c ∧
      orderOf x = p ∧ orderOf y = p ∧ Commute x y ∧ y ∉ Subgroup.zpowers x ∧
      ∀ v : Fin 3 → ZMod 3, Commute x (cmEquiv K v) ∧ Commute y (cmEquiv K v) := by
  obtain ⟨g, hg, hgo⟩ := exists_orderOf_eq_mem_orthogonalGroup_rotForm h3 hp hpd
  have hodd : Odd (orderOf g) := by rw [hgo]; exact hp.odd_of_ne_two hp2
  have hcomm : Commute g (rotLE K) := commute_rotLE_of_odd_orderOf h3 hg hodd
  have hg1 : g ≠ 1 := fun h => by
    rw [h, orderOf_one] at hgo
    exact hp.one_lt.ne hgo
  refine ⟨planeExtend K 0 g, planeExtend K 1 g,
    planeExtend_mem_modelOmega_of_odd h3 hbc 0 hg hodd,
    planeExtend_mem_modelOmega_of_odd h3 hbc 1 hg hodd, ?_, ?_,
    planeExtend_commute_planeExtend_of_ne (by decide) g g,
    planeExtend_not_mem_zpowers_of_ne (by decide) g hg1,
    fun v => ⟨planeExtend_commute_cmEquiv 0 hcomm v, planeExtend_commute_cmEquiv 1 hcomm v⟩⟩
  · rw [orderOf_planeExtend, hgo]
  · rw [orderOf_planeExtend, hgo]

theorem two_le_pRank_centralizer_c₀_range [Finite K] (h3 : (3 : K) ≠ 0)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpd : p ∣ minusPi (Nat.card K)) :
    2 ≤ pRank p (Subgroup.centralizer ((c₀ h3 hbc).range : Set ↥(omegaMinus8 K b c))) := by
  obtain ⟨x, y, hx, hy, hxo, hyo, hxy, hyx, hc⟩ :=
    exists_pair_centralizer_c₀_range h3 hbc hp hp2 hpd
  have := two_le_pRank_centralizer_c₀_of_model h3 hbc hp Set.univ hx hy hxo hyo hxy hyx
    (fun s _ => (hc _).1) (fun s _ => (hc _).2)
  rwa [Set.image_univ, ← MonoidHom.coe_range] at this

end CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal

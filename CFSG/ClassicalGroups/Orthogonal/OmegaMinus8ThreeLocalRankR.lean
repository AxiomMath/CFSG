module

public import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalFrame
import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalRealizers

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal

open Module QuadraticMap CFSG.GroupTheory.WeirSylow CFSG.ClassicalGroups.Orthogonal
open CFSG.Open (pRank)

variable {K : Type} [Field K] {b c : K}

section Generic

variable {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eichler_zpow {s w : V} (hw : polar Q s w = 0) (k : ℤ) :
    eichler Q s w ^ k = eichler Q s (k • w) := by
  have hz : ∀ m : ℤ, polar Q s (m • w) = 0 := fun m => by
    rw [← Int.cast_smul_eq_zsmul K, polar_smul_right_eq, hw, mul_zero]
  induction k using Int.induction_on with
  | zero => simp [eichler_zero_right]
  | succ k ih =>
    rw [zpow_add_one, ih, add_smul, one_smul, eichler_mul (hz k) hw]
  | pred k ih =>
    rw [zpow_sub_one, ih, sub_smul, one_smul, sub_eq_add_neg, eichler_inv hw,
      eichler_mul (hz _) (by rw [polar_neg_right, hw, neg_zero])]

theorem eichler_eq_one_iff (hQ : (polarBilin Q).Nondegenerate) {s w : V} (hs : Q s = 0)
    (hs0 : s ≠ 0) (hw : polar Q s w = 0) : eichler Q s w = 1 ↔ ∃ a : K, w = a • s := by
  constructor
  · intro h
    have : ∃ x, polar Q x s ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hs0 (hQ.2 s fun x => by simpa [polarBilin_apply_apply] using hcon x)
    obtain ⟨x, hx⟩ := this
    have h1 : eichler Q s w x = x := congrArg (fun e => e x) h
    rw [eichler_apply hs hw] at h1
    refine ⟨(polar Q x s)⁻¹ * (polar Q x w + Q w * polar Q x s), ?_⟩
    have h2 : polar Q x s • w = (polar Q x w + Q w * polar Q x s) • s := by
      have := h1
      rw [add_sub_assoc, add_eq_left, sub_eq_zero] at this
      exact this
    calc w = (polar Q x s)⁻¹ • (polar Q x s • w) := by rw [smul_smul, inv_mul_cancel₀ hx, one_smul]
      _ = _ := by rw [h2, smul_smul]
  · rintro ⟨a, rfl⟩
    have := eichler_add_smul_self hs (0 : V) a
    rw [zero_add, eichler_zero_right] at this
    exact this

theorem orderOf_eichler_of_charP {p : ℕ} (hp : p.Prime) [CharP K p]
    (hQ : (polarBilin Q).Nondegenerate) {s w : V} (hs : Q s = 0) (hs0 : s ≠ 0)
    (hw : polar Q s w = 0) (hws : ∀ a : K, w ≠ a • s) : orderOf (eichler Q s w) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine orderOf_eq_prime ?_ ?_
  · have h := eichler_zpow hw (p : ℤ)
    rw [zpow_natCast] at h
    rw [h]
    have : ((p : ℤ) • w) = 0 := by
      rw [← Int.cast_smul_eq_zsmul K]
      simp
    rw [this, eichler_zero_right]
  · intro h1
    obtain ⟨a, ha⟩ := (eichler_eq_one_iff hQ hs hs0 hw).1 h1
    exact hws a ha

theorem commute_eichler_left {s v w : V} (hv : polar Q s v = 0) (hw : polar Q s w = 0) :
    Commute (eichler Q s v) (eichler Q s w) := by
  rw [commute_iff_eq, eichler_mul hv hw, eichler_mul hw hv, add_comm]

theorem commute_eichler_of_apply_eq {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {s w : V} (hs : g s = s) (hw : g w = w) :
    Commute (eichler Q s w) g := by
  have h := eichler_conj hg s w
  rw [hs, hw, mul_inv_eq_iff_eq_mul] at h
  exact (commute_iff_eq _ _).2 h.symm

theorem eichler_not_mem_zpowers (hQ : (polarBilin Q).Nondegenerate) {s w₁ w₂ : V} (hs : Q s = 0)
    (h₁ : polar Q s w₁ = 0) (h₂ : polar Q s w₂ = 0)
    (hind : ∀ a b₁ b₂ : K, a • s + b₁ • w₁ + b₂ • w₂ = 0 → a = 0 ∧ b₁ = 0 ∧ b₂ = 0) :
    eichler Q s w₂ ∉ Subgroup.zpowers (eichler Q s w₁) := by
  have hs0 : s ≠ 0 := fun h => by
    have := (hind 1 0 0 (by simp [h])).1
    exact one_ne_zero this
  rintro ⟨k, hk⟩
  have hk' : eichler Q s (k • w₁) = eichler Q s w₂ := by
    rw [← eichler_zpow h₁ k]
    exact hk
  have hz : polar Q s (k • w₁) = 0 := by
    rw [← Int.cast_smul_eq_zsmul K, polar_smul_right_eq, h₁, mul_zero]
  have h3 : eichler Q s (w₂ + -(k • w₁)) = 1 := by
    rw [← eichler_mul h₂ (by rw [polar_neg_right, hz, neg_zero]), ← eichler_inv hz, hk',
      ← hk', mul_inv_cancel]
  have hperp : polar Q s (w₂ + -(k • w₁)) = 0 := by
    rw [polar_add_right, h₂, polar_neg_right, hz, neg_zero, add_zero]
  obtain ⟨a, ha⟩ := (eichler_eq_one_iff hQ hs hs0 hperp).1 h3
  have := (hind (-a) (-(k : K)) 1 (by
    have h5 : (k • w₁) = (k : K) • w₁ := (Int.cast_smul_eq_zsmul K k w₁).symm
    rw [h5] at ha
    rw [neg_smul, neg_smul, one_smul]
    rw [← sub_eq_zero] at ha
    rw [← ha]
    abel)).2.2
  exact one_ne_zero this

end Generic

theorem modelForm_planeVec (b c : K) (i : Fin 3) (p : K × K) :
    modelForm b c (planeVec i p) = rotForm K p := by
  rw [modelForm_apply]
  have hsum : (∑ j, rotForm K ((planeVec i p).1 j)) = rotForm K p := by
    rw [Fintype.sum_eq_single i (fun j hj => by simp [planeVec, Pi.single_apply, hj])]
    simp [planeVec]
  rw [hsum]
  simp [planeVec]

theorem polar_modelForm_planeVec_wVec (b c : K) (i : Fin 3) (p w : K × K) :
    polar (modelForm b c) (planeVec i p) (wVec w) = 0 := by
  have hx : planeVec i p + wVec w = (Pi.single i p, w) := by
    ext k <;> simp [planeVec, wVec]
  have h1 : modelForm b c (Pi.single i p, w) = rotForm K p + wForm b c w := by
    rw [modelForm_apply]
    have hsum : (∑ j, rotForm K ((Pi.single i p : Fin 3 → K × K) j)) = rotForm K p := by
      rw [Fintype.sum_eq_single i (fun j hj => by simp [Pi.single_apply, hj])]
      simp
    rw [hsum]
  rw [polar, hx, h1, modelForm_planeVec, modelForm_wVec]
  ring

theorem polar_modelForm_planeVec_planeVec_of_ne (b c : K) {i j : Fin 3} (hij : i ≠ j)
    (p p' : K × K) : polar (modelForm b c) (planeVec i p) (planeVec j p') = 0 := by
  have hx : planeVec i p + planeVec j p' =
      (Pi.single i p + Pi.single j p', (0 : K × K)) := by
    ext k <;> simp [planeVec]
  have h1 : modelForm b c (Pi.single i p + Pi.single j p', (0 : K × K)) =
      rotForm K p + rotForm K p' := by
    rw [modelForm_apply]
    have hsum : (∑ k, rotForm K ((Pi.single i p + Pi.single j p' : Fin 3 → K × K) k)) =
        rotForm K p + rotForm K p' := by
      rw [Fin.sum_univ_three]
      fin_cases i <;> fin_cases j <;>
        simp_all [Pi.single_apply, add_comm, add_left_comm, add_assoc]
    rw [hsum]
    simp
  rw [polar, hx, h1, modelForm_planeVec, modelForm_planeVec]
  ring

theorem exists_eichler_triple_of_isSplit (b c : K) (h : IsSplit K) :
    ∃ s w₁ w₂ : ModelSpace K, modelForm b c s = 0 ∧ polar (modelForm b c) s w₁ = 0 ∧
      polar (modelForm b c) s w₂ = 0 ∧
      (∀ a b₁ b₂ : K, a • s + b₁ • w₁ + b₂ • w₂ = 0 → a = 0 ∧ b₁ = 0 ∧ b₂ = 0) ∧
      ∀ t : Fin 3 → ZMod 3, t 2 = 0 →
        cmEquiv K t s = s ∧ cmEquiv K t w₁ = w₁ ∧ cmEquiv K t w₂ = w₂ := by
  obtain ⟨ω, hω⟩ := h
  refine ⟨planeVec 2 (-ω, 1), wVec (1, 0), wVec (0, 1), ?_, ?_, ?_, ?_, ?_⟩
  · rw [modelForm_planeVec, rotForm_apply]
    linear_combination hω
  · exact polar_modelForm_planeVec_wVec b c 2 (-ω, 1) (1, 0)
  · exact polar_modelForm_planeVec_wVec b c 2 (-ω, 1) (0, 1)
  · intro a b₁ b₂ h
    have hb : b₁ • ((1 : K), (0 : K)) + b₂ • ((0 : K), (1 : K)) = 0 := by
      have := congrArg Prod.snd h
      simpa [planeVec, wVec] using this
    have hb₁ : b₁ = 0 := by
      have := congrArg Prod.fst hb; simpa using this
    have hb₂ : b₂ = 0 := by
      have := congrArg Prod.snd hb; simpa using this
    refine ⟨?_, hb₁, hb₂⟩
    have hs : a • planeVec 2 (-ω, 1) = 0 := by
      rw [hb₁, hb₂] at h
      simpa using h
    have h3 : (a • planeVec 2 (-ω, 1)).1 2 = 0 := by rw [hs]; rfl
    have h4 : (a • (-ω, 1) : K × K) = 0 := by simpa [planeVec] using h3
    have := congrArg Prod.snd h4
    simpa using this
  · intro t ht
    refine ⟨?_, cmEquiv_apply_wVec t (1, 0), cmEquiv_apply_wVec t (0, 1)⟩
    rw [cmEquiv_apply_planeVec, ht, rotPow_zero]
    simp

theorem exists_eichler_triple_of_not_isSplit (b c : K) (h : ¬ IsSplit K) :
    ∃ s w₁ w₂ : ModelSpace K, modelForm b c s = 0 ∧ polar (modelForm b c) s w₁ = 0 ∧
      polar (modelForm b c) s w₂ = 0 ∧
      (∀ a b₁ b₂ : K, a • s + b₁ • w₁ + b₂ • w₂ = 0 → a = 0 ∧ b₁ = 0 ∧ b₂ = 0) ∧
      ∀ t : Fin 3 → ZMod 3, t 2 = 0 →
        cmEquiv K t s = s ∧ cmEquiv K t w₁ = w₁ ∧ cmEquiv K t w₂ = w₂ := by
  refine ⟨wVec (0, 1), planeVec 2 (1, 0), planeVec 2 (0, 1), ?_, ?_, ?_, ?_, ?_⟩
  · rw [modelForm_wVec, wForm_of_not_isSplit h, binForm_apply]
    ring
  · rw [polar_comm]
    exact polar_modelForm_planeVec_wVec b c 2 (1, 0) (0, 1)
  · rw [polar_comm]
    exact polar_modelForm_planeVec_wVec b c 2 (0, 1) (0, 1)
  · intro a b₁ b₂ h
    have ha : a = 0 := by
      have h1 : a • ((0 : K), (1 : K)) = 0 := by
        have := congrArg Prod.snd h
        simpa [planeVec, wVec] using this
      have := congrArg Prod.snd h1
      simpa using this
    have hb : b₁ • ((1 : K), (0 : K)) + b₂ • ((0 : K), (1 : K)) = 0 := by
      have h1 := congrArg (fun x : ModelSpace K => x.1 2) h
      simpa [planeVec, wVec] using h1
    have hb₁ : b₁ = 0 := by
      have := congrArg Prod.fst hb; simpa using this
    have hb₂ : b₂ = 0 := by
      have := congrArg Prod.snd hb; simpa using this
    exact ⟨ha, hb₁, hb₂⟩
  · intro t ht
    refine ⟨cmEquiv_apply_wVec t (0, 1), ?_, ?_⟩
    · rw [cmEquiv_apply_planeVec, ht, rotPow_zero]; simp
    · rw [cmEquiv_apply_planeVec, ht, rotPow_zero]; simp

theorem exists_eichler_triple (b c : K) :
    ∃ s w₁ w₂ : ModelSpace K, modelForm b c s = 0 ∧ polar (modelForm b c) s w₁ = 0 ∧
      polar (modelForm b c) s w₂ = 0 ∧
      (∀ a b₁ b₂ : K, a • s + b₁ • w₁ + b₂ • w₂ = 0 → a = 0 ∧ b₁ = 0 ∧ b₂ = 0) ∧
      ∀ t : Fin 3 → ZMod 3, t 2 = 0 →
        cmEquiv K t s = s ∧ cmEquiv K t w₁ = w₁ ∧ cmEquiv K t w₂ = w₂ := by
  by_cases h : IsSplit K
  · exact exists_eichler_triple_of_isSplit b c h
  · exact exists_eichler_triple_of_not_isSplit b c h

theorem exists_eichler_pair_model [Finite K] (h3 : (3 : K) ≠ 0)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime) [CharP K p] :
    ∃ x y : ModelSpace K ≃ₗ[K] ModelSpace K, x ∈ modelOmega b c ∧ y ∈ modelOmega b c ∧
      orderOf x = p ∧ orderOf y = p ∧ Commute x y ∧ y ∉ Subgroup.zpowers x ∧
      ∀ t : Fin 3 → ZMod 3, t 2 = 0 → Commute x (cmEquiv K t) ∧ Commute y (cmEquiv K t) := by
  obtain ⟨s, w₁, w₂, hs, hw₁, hw₂, hind, hfix⟩ := exists_eichler_triple b c
  have hs0 : s ≠ 0 := fun h => by
    have := (hind 1 0 0 (by simp [h])).1
    exact one_ne_zero this
  have hws₁ : ∀ a : K, w₁ ≠ a • s := by
    intro a ha
    exact one_ne_zero (hind (-a) 1 0 (by
      rw [ha, one_smul, zero_smul, add_zero, ← add_smul, neg_add_cancel, zero_smul])).2.1
  have hws₂ : ∀ a : K, w₂ ≠ a • s := by
    intro a ha
    exact one_ne_zero (hind (-a) 0 1 (by
      rw [ha, one_smul, zero_smul, add_zero, ← add_smul, neg_add_cancel, zero_smul])).2.2
  have hQ := nondegenerate_polarBilin_modelForm h3 hbc
  refine ⟨eichler (modelForm b c) s w₁, eichler (modelForm b c) s w₂,
    eichler_mem_modelOmega h3 hbc s w₁, eichler_mem_modelOmega h3 hbc s w₂, ?_, ?_, ?_, ?_, ?_⟩
  · exact orderOf_eichler_of_charP hp hQ hs hs0 hw₁ hws₁
  · exact orderOf_eichler_of_charP hp hQ hs hs0 hw₂ hws₂
  · exact commute_eichler_left hw₁ hw₂
  · exact eichler_not_mem_zpowers hQ hs hw₁ hw₂ hind
  · intro t ht
    have hf := hfix t ht
    exact ⟨commute_eichler_of_apply_eq (cm_mem_modelO b c (Multiplicative.ofAdd t)) hf.1 hf.2.1,
      commute_eichler_of_apply_eq (cm_mem_modelO b c (Multiplicative.ofAdd t)) hf.1 hf.2.2⟩

theorem two_le_pRank_centralizer_c₀_of_toAdd_two_eq_zero [Finite K] (h3 : (3 : K) ≠ 0)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime) [CharP K p]
    (S : Set (Multiplicative (Fin 3 → ZMod 3)))
    (hS : ∀ s ∈ S, Multiplicative.toAdd s 2 = 0) :
    2 ≤ pRank p (Subgroup.centralizer (c₀ h3 hbc '' S : Set ↥(omegaMinus8 K b c))) := by
  obtain ⟨x, y, hx, hy, hxo, hyo, hxy, hyx, hcomm⟩ := exists_eichler_pair_model h3 hbc hp
  exact two_le_pRank_centralizer_c₀_of_model h3 hbc hp S hx hy hxo hyo hxy hyx
    (fun s hs => (hcomm (Multiplicative.toAdd s) (hS s hs)).1)
    (fun s hs => (hcomm (Multiplicative.toAdd s) (hS s hs)).2)

theorem two_le_pRank_centralizer_c₀_point [Finite K] (h3 : (3 : K) ≠ 0)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime) [CharP K p]
    (v : Multiplicative (Fin 3 → ZMod 3)) (hv : Multiplicative.toAdd v 2 = 0) :
    2 ≤ pRank p (Subgroup.centralizer ({c₀ h3 hbc v} : Set ↥(omegaMinus8 K b c))) := by
  have := two_le_pRank_centralizer_c₀_of_toAdd_two_eq_zero h3 hbc hp ({v} : Set _) (by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    exact hv)
  rwa [Set.image_singleton] at this

theorem two_le_pRank_centralizer_c₀_pair [Finite K] (h3 : (3 : K) ≠ 0)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime) [CharP K p]
    (v₁ v₂ : Multiplicative (Fin 3 → ZMod 3)) (h₁ : Multiplicative.toAdd v₁ 2 = 0)
    (h₂ : Multiplicative.toAdd v₂ 2 = 0) :
    2 ≤ pRank p (Subgroup.centralizer
      ({c₀ h3 hbc v₁, c₀ h3 hbc v₂} : Set ↥(omegaMinus8 K b c))) := by
  have := two_le_pRank_centralizer_c₀_of_toAdd_two_eq_zero h3 hbc hp ({v₁, v₂} : Set _) (by
    intro s hs
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact h₁
    · exact h₂)
  rwa [Set.image_pair] at this

end CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal

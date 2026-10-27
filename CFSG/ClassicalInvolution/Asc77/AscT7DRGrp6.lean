module

public import CFSG.ClassicalInvolution.Asc77.AscT7DRGrp

public section

namespace CFSG.ClassicalInvolution.Asc77.T7DR

open CFSG.ClassicalInvolution.Asc77.T7C2

section Omega6

variable {S : Type*} [Group S] [Finite S]

theorem genLE_four_of_omega6 {a b s t : S} (hS : Subgroup.closure ({a, b, s, t} : Set S) = ⊤)
    (hbab : b * a * b⁻¹ = a⁻¹) (hb2 : ∃ k : ℤ, b * b = a ^ k) (ht2 : t * t = 1)
    (hs2 : s * s = 1) (hst : s * t = t * s) (hsa : s * a * s⁻¹ = a⁻¹)
    (hsb : s * b * s⁻¹ = b * a)
    (h5a : a * (t * a * t⁻¹) = (t * a * t⁻¹) * a)
    (h5b : a * (t * b * t⁻¹) = (t * b * t⁻¹) * a)
    (h5c : b * (t * a * t⁻¹) = (t * a * t⁻¹) * b)
    (h5d : b * (t * b * t⁻¹) = (t * b * t⁻¹) * b)
    (h6 : t * (b * b) * t⁻¹ = b * b) (H : Subgroup S) : GenLE H 4 := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have F1 : b * a = a⁻¹ * b := mul_inv_eq_iff_eq_mul.mp hbab
  have F2 : b * a⁻¹ = a * b := by
    have : b * a⁻¹ * b⁻¹ = a := by
      have h := congrArg (fun x => x⁻¹) hbab
      simpa [mul_assoc] using h
    exact mul_inv_eq_iff_eq_mul.mp this
  have F3 : s * a = a⁻¹ * s := mul_inv_eq_iff_eq_mul.mp hsa
  have F4 : s * a⁻¹ = a * s := by
    have : s * a⁻¹ * s⁻¹ = a := by
      have h := congrArg (fun x => x⁻¹) hsa
      simpa [mul_assoc] using h
    exact mul_inv_eq_iff_eq_mul.mp this
  have F5 : s * b = b * a * s := mul_inv_eq_iff_eq_mul.mp hsb
  set a' : S := t * a * t⁻¹ with ha'
  set b' : S := t * b * t⁻¹ with hb'
  have hat : a' = t * a * t := by rw [ha', htinv]
  have hbt : b' = t * b * t := by rw [hb', htinv]
  have ha'inv : a'⁻¹ = t * a⁻¹ * t := by
    rw [hat]
    simp [mul_inv_rev, htinv, mul_assoc]
  have F8 : s * a' = a'⁻¹ * s := by
    calc s * a' = s * (t * a * t) := by rw [hat]
      _ = (s * t) * a * t := by group
      _ = (t * s) * a * t := by rw [hst]
      _ = t * (s * a) * t := by group
      _ = t * (a⁻¹ * s) * t := by rw [F3]
      _ = t * a⁻¹ * (s * t) := by group
      _ = t * a⁻¹ * (t * s) := by rw [hst]
      _ = (t * a⁻¹ * t) * s := by group
      _ = a'⁻¹ * s := by rw [ha'inv]
  have F8' : s * a'⁻¹ = a' * s := by
    have : s * a'⁻¹ * s⁻¹ = a' := by
      have h := congrArg (fun x => x⁻¹) (mul_inv_eq_iff_eq_mul.mpr F8 : s * a' * s⁻¹ = a'⁻¹)
      simpa [mul_assoc] using h
    exact mul_inv_eq_iff_eq_mul.mp this
  have F9 : s * b' = b' * a' * s := by
    calc s * b' = s * (t * b * t) := by rw [hbt]
      _ = (s * t) * b * t := by group
      _ = (t * s) * b * t := by rw [hst]
      _ = t * (s * b) * t := by group
      _ = t * (b * a * s) * t := by rw [F5]
      _ = t * b * a * (s * t) := by group
      _ = t * b * a * (t * s) := by rw [hst]
      _ = (t * b * t) * (t * a * t) * s := by
          calc t * b * a * (t * s) = t * b * (t * t) * a * (t * s) := by rw [ht2]; group
            _ = (t * b * t) * (t * a * t) * s := by group
      _ = b' * a' * s := by rw [hbt, hat]
  have F11 : b' * a⁻¹ = a⁻¹ * b' := by
    calc b' * a⁻¹ = a⁻¹ * (a * b') * a⁻¹ := by group
      _ = a⁻¹ * (b' * a) * a⁻¹ := by rw [h5b]
      _ = a⁻¹ * b' := by group
  obtain ⟨k, hk⟩ := hb2
  have hz0a : (b * b) * a = a * (b * b) := by
    rw [hk]
    exact (Commute.zpow_left (Commute.refl a) k).eq
  have hz0sq : (b * b) * (b * b) = 1 := by
    have h1 : b * (b * b) * b⁻¹ = b * b := by group
    have h2 : b * (b * b) * b⁻¹ = (b * b)⁻¹ := by
      rw [hk, ← conj_zpow, hbab, inv_zpow]
    exact eq_inv_iff_mul_eq_one.mp (h1.symm.trans h2)
  have F12 : b' * b' = b * b := by
    have : b' * b' = t * (b * b) * t⁻¹ := by rw [hb']; group
    exact this.trans h6
  set e : S := b * b' * s with he
  have hA : e * a = a * e := by
    calc e * a = b * b' * (s * a) := by rw [he]; group
      _ = b * b' * (a⁻¹ * s) := by rw [F3]
      _ = b * (b' * a⁻¹) * s := by group
      _ = b * (a⁻¹ * b') * s := by rw [F11]
      _ = (b * a⁻¹) * b' * s := by group
      _ = (a * b) * b' * s := by rw [F2]
      _ = a * e := by rw [he]; group
  have hB : e * e = a * a' := by
    have hsb' : s * (b * b' * s) = b * a * b' * a' := by
      calc s * (b * b' * s) = (s * b) * b' * s := by group
        _ = (b * a * s) * b' * s := by rw [F5]
        _ = b * a * (s * b') * s := by group
        _ = b * a * (b' * a' * s) * s := by rw [F9]
        _ = b * a * b' * a' * (s * s) := by group
        _ = b * a * b' * a' := by rw [hs2, mul_one]
    calc e * e = b * b' * (s * (b * b' * s)) := by rw [he]; group
      _ = b * b' * (b * a * b' * a') := by rw [hsb']
      _ = b * (b' * b) * a * b' * a' := by group
      _ = b * (b * b') * a * b' * a' := by rw [← h5d]
      _ = (b * b) * (b' * a) * b' * a' := by group
      _ = (b * b) * (a * b') * b' * a' := by rw [← h5b]
      _ = (b * b) * a * (b' * b') * a' := by group
      _ = (b * b) * a * (b * b) * a' := by rw [F12]
      _ = a * (b * b) * (b * b) * a' := by rw [hz0a]
      _ = a * ((b * b) * (b * b)) * a' := by group
      _ = a * a' := by rw [hz0sq]; group
  set W : Subgroup S := Subgroup.closure ({a, e} : Set S) with hW
  have haW : a ∈ W := Subgroup.subset_closure (by simp)
  have heW : e ∈ W := Subgroup.subset_closure (by simp)
  have ha'W : a' = a⁻¹ * (e * e) := by rw [hB]; group
  have hconjB : b * e * b⁻¹ = a⁻¹ * e := by
    apply mul_inv_eq_iff_eq_mul.mpr
    calc b * e = (b * b) * b' * s := by rw [he]; group
      _ = (a⁻¹ * (a * (b * b))) * b' * s := by group
      _ = (a⁻¹ * ((b * b) * a)) * b' * s := by rw [hz0a]
      _ = a⁻¹ * (b * b) * (a * b') * s := by group
      _ = a⁻¹ * (b * b) * (b' * a) * s := by rw [h5b]
      _ = a⁻¹ * b * (b * b') * a * s := by group
      _ = a⁻¹ * b * (b' * b) * a * s := by rw [h5d]
      _ = a⁻¹ * b * b' * (b * a * s) := by group
      _ = a⁻¹ * b * b' * (s * b) := by rw [F5]
      _ = a⁻¹ * e * b := by rw [he]; group
  have hconjS : s * e * s⁻¹ = e⁻¹ := by
    have key : s * e * s = b * b' * (a * a') * s := by
      calc s * e * s = s * b * b' * (s * s) := by rw [he]; group
        _ = (s * b) * b' := by rw [hs2, mul_one]
        _ = b * a * (s * b') := by rw [F5]; group
        _ = b * a * (b' * a' * s) := by rw [F9]
        _ = b * (a * b') * a' * s := by group
        _ = b * (b' * a) * a' * s := by rw [h5b]
        _ = b * b' * (a * a') * s := by group
    have key2 : e * (a * a')⁻¹ = b * b' * (a * a') * s := by
      have h1 : s * (a * a')⁻¹ = (a * a') * s := by
        calc s * (a * a')⁻¹ = s * a'⁻¹ * a⁻¹ := by group
          _ = a' * s * a⁻¹ := by rw [F8']
          _ = a' * (s * a⁻¹) := by group
          _ = a' * (a * s) := by rw [F4]
          _ = (a' * a) * s := by group
          _ = (a * a') * s := by rw [h5a]
      calc e * (a * a')⁻¹ = b * b' * (s * (a * a')⁻¹) := by rw [he]; group
        _ = b * b' * ((a * a') * s) := by rw [h1]
        _ = b * b' * (a * a') * s := by group
    rw [hsinv, key, ← key2, ← hB]
    group
  have hconjT : t * e * t⁻¹ = e := by
    have h1 : t * b' * t⁻¹ = b := by
      rw [hb', htinv]
      calc t * (t * b * t) * t = (t * t) * b * (t * t) := by group
        _ = b := by rw [ht2]; group
    have h2 : t * s * t⁻¹ = s := by
      calc t * s * t⁻¹ = s * t * t⁻¹ := by rw [hst]
        _ = s := by group
    calc t * e * t⁻¹ = (t * b * t⁻¹) * (t * b' * t⁻¹) * (t * s * t⁻¹) := by rw [he]; group
      _ = b' * b * s := by rw [← hb', h1, h2]
      _ = b * b' * s := by rw [← h5d]
      _ = e := by rw [he]
  have hnormal : W.Normal := by
    refine normal_of_conj_gens hS ?_
    intro g hg
    rcases hg with rfl | rfl | rfl | rfl
    · refine conj_mem_closure_pair ?_ ?_
      · simpa using haW
      · rw [← hA]
        simpa using heW
    · refine conj_mem_closure_pair ?_ ?_
      · rw [hbab]
        exact Subgroup.inv_mem _ haW
      · rw [hconjB]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ haW) heW
    · refine conj_mem_closure_pair ?_ ?_
      · rw [hsa]
        exact Subgroup.inv_mem _ haW
      · rw [hconjS]
        exact Subgroup.inv_mem _ heW
    · refine conj_mem_closure_pair ?_ ?_
      · have : g * a * g⁻¹ = a' := by rw [ha']
        rw [this, ha'W]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ haW) (Subgroup.mul_mem _ heW heW)
      · rw [hconjT]
        exact heW
  have hb2W : b * b ∈ W := by
    rw [hk]
    exact Subgroup.zpow_mem _ haW k
  have ht2W : t * t ∈ W := by
    rw [ht2]
    exact Subgroup.one_mem _
  refine genLE_four_of_normal_two_gen haW heW hA.symm hW.symm hb2W ht2W ?_ H
  rw [eq_top_iff, ← hS, Subgroup.closure_le]
  have hsmem : s ∈ Subgroup.closure ((W : Set S) ∪ {b, t}) := by
    have hb'mem : b' ∈ Subgroup.closure ((W : Set S) ∪ {b, t}) := by
      have hb1 : b ∈ Subgroup.closure ((W : Set S) ∪ {b, t}) :=
        Subgroup.subset_closure (Or.inr (by simp))
      have ht1 : t ∈ Subgroup.closure ((W : Set S) ∪ {b, t}) :=
        Subgroup.subset_closure (Or.inr (by simp))
      rw [hb']
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ht1 hb1) (Subgroup.inv_mem _ ht1)
    have hb1 : b ∈ Subgroup.closure ((W : Set S) ∪ {b, t}) :=
      Subgroup.subset_closure (Or.inr (by simp))
    have he1 : e ∈ Subgroup.closure ((W : Set S) ∪ {b, t}) :=
      Subgroup.subset_closure (Or.inl heW)
    have : s = (b * b')⁻¹ * e := by rw [he]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ hb1 hb'mem)) he1
  intro g hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact Subgroup.subset_closure (Or.inl haW)
  · exact Subgroup.subset_closure (Or.inr (by simp))
  · exact hsmem
  · exact Subgroup.subset_closure (Or.inr (by simp))

end Omega6

end CFSG.ClassicalInvolution.Asc77.T7DR

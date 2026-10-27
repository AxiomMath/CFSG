module

public import CFSG.CGT.Timmesfeld75.Sec77Model

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups Matrix commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n m : ℕ}

theorem Sec6Ctx.mul_mem_classD_of_data (h66 : Sec66) (h62 : Sec62) (h63 : Sec63)
    (hc : Sec6Ctx T T₁ n m) [(T.subgroupOf (hSub T (normIn T₁ T))).Normal]
    (M : TModel T T₁ n m) {a a' : G} (ha : a ∈ normD T) (ha' : a' ∈ normD T)
    (ha'T : a' ∉ T) (haa' : a * a' = a' * a)
    {f f' : Module.Dual (GaloisField 2 m) (Fin n → GaloisField 2 m)}
    {v : Fin n → GaloisField 2 m} (hv : v ≠ 0) (hfv : f v = 0) (hf'v : f' v = 0)
    (hind : ∀ r s : GaloisField 2 m, r • f + s • f' = 0 → r = 0 ∧ s = 0)
    (hda : ∀ w, sact (ubar M.ε a) w = w + f w • v)
    (hda' : ∀ w, sact (ubar M.ε a') w = w + f' w • v) : a * a' ∈ classD T := by
  have := hc.finite
  have hTab := hc.hy.pair.wc.1
  have hf0 : f ≠ 0 := fun h0 => one_ne_zero (hind 1 0 (by rw [h0]; simp)).1
  have hf'0 : f' ≠ 0 := fun h0 => one_ne_zero (hind 0 1 (by rw [h0]; simp)).2
  have hh0 : f + f' ≠ 0 := by
    intro h0
    exact one_ne_zero (hind 1 1 (by simpa using h0)).1
  obtain ⟨p, hfp, hf'p⟩ := exists_vec_eq_one hind
  have hp0 : p ≠ 0 := by
    rintro rfl
    simp at hfp
  have hhp : (f + f') p = 0 := by
    simp only [LinearMap.add_apply, hfp, hf'p, CharTwo.add_self_eq_zero]
  obtain ⟨ub, hub, hubact⟩ := exists_sl_transvection hhp hh0 hp0
  obtain ⟨b, hb, hbT, hbub⟩ := hc.exists_lift M hub
  have hbb : b * b = 1 := mul_self_eq_one_of_mem_classD hTab hb.1
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have haa : a * a = 1 := mul_self_eq_one_of_mem_classD hTab ha.1
  have ha'a' : a' * a' = 1 := mul_self_eq_one_of_mem_classD hTab ha'.1
  have haH := M.mem_H ha
  have ha'H := M.mem_H ha'
  have hbH := M.mem_H hb
  have hTH : T ≤ hSub T (normIn T₁ T) := left_le_hSub
  have hconj : ubar M.ε b * ubar M.ε a * ubar M.ε b = ubar M.ε a' := by
    rw [hbub]
    exact conj_of_data (fun x => rfl) hfv hf'v hfp hf'p hda hda' hubact
  have ha''D : b * a * b ∈ classD T := by
    have := classD_conj_mul ha.1 b
    rwa [hbi] at this
  have ha''H : b * a * b ∈ hSub T (normIn T₁ T) :=
    (hSub T (normIn T₁ T)).mul_mem ((hSub T (normIn T₁ T)).mul_mem hbH haH) hbH
  have hu'' : ubar M.ε a' = ubar M.ε (b * a * b) := by
    rw [ubar_mul M.ε ((hSub T (normIn T₁ T)).mul_mem hbH haH) hbH, ubar_mul M.ε hbH haH, hconj]
  obtain ⟨t, htT, hta⟩ : ∃ t ∈ T, b * a * b = a' * t := by
    refine ⟨a'⁻¹ * (b * a * b), (ubar_eq_iff M.ε ha'H ha''H).1 hu'', ?_⟩
    group
  obtain ⟨r, hr⟩ := (hc.mem_classD_mul_iff h62 h63 M ha' ha'T hf'0 hda' htT).1
    (by rw [← hta]; exact ha''D)
  have ha'aN : a * a' ∈ Subgroup.normalizer (T : Set G) :=
    (Subgroup.normalizer (T : Set G)).mul_mem ha.2 ha'.2
  have hm₀H : a * a' ∈ hSub T (normIn T₁ T) := (hSub T (normIn T₁ T)).mul_mem haH ha'H
  have hm₀2 : (a * a') * (a * a') = 1 := by
    calc a * a' * (a * a') = a * (a' * a) * a' := by group
      _ = a * (a * a') * a' := by rw [haa']
      _ = (a * a) * (a' * a') := by group
      _ = 1 := by rw [haa, ha'a', one_mul]
  have hubm₀ : ubar M.ε (a * a') = ubar M.ε a * ubar M.ε a' := ubar_mul M.ε haH ha'H
  have hm₀t : a * a' * t = t * (a * a') := by
    have hmem : a * a' * t * (a * a')⁻¹ ∈ T := conj_mem_of_mem_normalizer ha'aN htT
    have h1 := M.toAdd_phi_conj hm₀H htT hmem
    have h2 : sact (ubar M.ε (a * a')) (Multiplicative.toAdd (M.φ ⟨t, htT⟩)) =
        Multiplicative.toAdd (M.φ ⟨t, htT⟩) := by
      rw [hr, hubm₀, sact_mul, hda', hda]
      simp only [map_smul, smul_eq_mul, hf'v, hfv, mul_zero, zero_smul, add_zero]
    rw [h2] at h1
    have h3 : (⟨a * a' * t * (a * a')⁻¹, hmem⟩ : ↥T) = ⟨t, htT⟩ :=
      M.φ.injective (Multiplicative.toAdd.injective h1)
    have h4 : a * a' * t * (a * a')⁻¹ = t := congrArg Subtype.val h3
    calc a * a' * t = (a * a' * t * (a * a')⁻¹) * (a * a') := by group
      _ = t * (a * a') := by rw [h4]
  have htt : t * t = 1 := elemAbelian_mul_self hTab htT
  have hab2 : (a * b) ^ 2 = a * a' * t := by
    have e1 : (a * b) ^ 2 = a * (b * a * b) := by
      rw [pow_two]
      group
    rw [e1, hta]
    group
  have hubne : ubar M.ε (a * a') ≠ 1 := by
    intro h1
    rw [hubm₀] at h1
    have hff : f = f' := (data_mul_eq_one_iff hfv hv hda hda').1 h1
    have h2 : (1 : GaloisField 2 m) • f + (1 : GaloisField 2 m) • f' = 0 := by
      rw [← hff]
      ext w
      simp [CharTwo.add_self_eq_zero]
    exact one_ne_zero (hind 1 1 h2).1
  have hTH' : t ∈ hSub T (normIn T₁ T) := hTH htT
  have hubt : ubar M.ε t = 1 := ubar_of_mem_T M.ε hTH htT
  have hubE : ubar M.ε (a * a' * t) = ubar M.ε a * ubar M.ε a' := by
    rw [ubar_mul M.ε hm₀H hTH', hubt, mul_one, hubm₀]
  have hE1 : a * a' * t ≠ 1 := by
    intro h1
    apply hubne
    have h2 : ubar M.ε (a * a' * t) = 1 := by
      rw [h1]
      exact (ubar_eq_one_iff M.ε (Subgroup.one_mem _)).2 (Subgroup.one_mem _)
    rw [hubE] at h2
    rw [hubm₀]
    exact h2
  have hEE : (a * a' * t) * (a * a' * t) = 1 := by
    calc a * a' * t * (a * a' * t) = a * a' * (t * (a * a')) * t := by group
      _ = a * a' * (a * a' * t) * t := by rw [hm₀t]
      _ = ((a * a') * (a * a')) * (t * t) := by group
      _ = 1 := by rw [hm₀2, htt, one_mul]
  have hord : orderOf (a * b) = 4 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h4 : (a * b) ^ 2 ^ (1 + 1) = 1 := by
      rw [show (2 : ℕ) ^ (1 + 1) = 2 + 2 by norm_num, pow_add, hab2]
      exact hEE
    have h1' : ¬ (a * b) ^ 2 ^ 1 = 1 := by
      rw [pow_one, hab2]
      exact hE1
    have := orderOf_eq_prime_pow (p := 2) (n := 1) h1' h4
    simpa using this
  have hED : a * a' * t ∈ classD T := by
    have := h66 G T T₁ n m hc a ha.1 b hb.1 hord
    rwa [hab2] at this
  have hEN : a * a' * t ∈ normD T :=
    ⟨hED, (Subgroup.normalizer (T : Set G)).mul_mem ha'aN (Subgroup.le_normalizer htT)⟩
  have hET : a * a' * t ∉ T := by
    intro h1
    apply hubne
    have h2 : ubar M.ε (a * a' * t) = 1 :=
      (ubar_eq_one_iff M.ε ((hSub T (normIn T₁ T)).mul_mem hm₀H hTH')).2 h1
    rw [hubE] at h2
    rw [hubm₀]
    exact h2
  have hdE : ∀ w, sact (ubar M.ε (a * a' * t)) w = w + (f + f') w • v := by
    intro w
    rw [hubE]
    exact sact_mul_of_data hfv hda hda' w
  have hmain := (hc.mem_classD_mul_iff h62 h63 M hEN hET hh0 hdE htT).2 ⟨r, hr⟩
  have e2 : a * a' * t * t = a * a' := by rw [mul_assoc _ t t, htt, mul_one]
  rwa [e2] at hmain

end CFSG.CGT.Timmesfeld75

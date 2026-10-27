module

public import CFSG.GH74.Tits83.OctField
public import CFSG.GH74.Tits83.Section4C
public import CFSG.GH74.Tits83.Section3E

public section

namespace CFSG.GH74.Tits83

open CFSG.GH74.BNPair

open scoped commutatorElement Pointwise

universe u

variable {G : Type u} [Group G]

theorem sigma_mul_self_bijective {K : Type*} [Field K] (σ : K →+* K)
    (hσ : ∀ t, σ (σ t) = t ^ 2) : Function.Bijective (fun t => σ t * t) := by
  have hσinj : Function.Injective σ := by
    intro a b hab
    have h0 : σ (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have hsq : (a - b) ^ 2 = 0 := by rw [← hσ (a - b), h0, map_zero]
    have hmul : (a - b) * (a - b) = 0 := by simpa [pow_two] using hsq
    exact sub_eq_zero.mp (mul_self_eq_zero.mp hmul)
  have hzero : ∀ t : K, σ t = 0 ↔ t = 0 := fun t => by
    constructor
    · intro h
      have hsq : t ^ 2 = 0 := by rw [← hσ t, h, map_zero]
      have hmul : t * t = 0 := by simpa [pow_two] using hsq
      exact mul_self_eq_zero.mp hmul
    · intro h
      rw [h, map_zero]
  let φ : K → K := fun u => σ u / u
  have hleft : Function.LeftInverse φ (fun t => σ t * t) := by
    intro t
    by_cases ht : t = 0
    · subst ht
      simp [φ]
    · have hσt : σ t ≠ 0 := fun h => ht ((hzero t).mp h)
      have hft : σ t * t ≠ 0 := mul_ne_zero hσt ht
      simp only [φ]
      rw [map_mul, hσ t]
      field_simp [ht, hσt, hft]
  have hright : Function.RightInverse φ (fun t => σ t * t) := by
    intro u
    by_cases hu : u = 0
    · subst hu
      simp [φ]
    · have hσu : σ u ≠ 0 := fun h => hu ((hzero u).mp h)
      simp only [φ]
      rw [map_div₀, hσ u]
      field_simp [hu, hσu]
  exact Function.bijective_iff_has_inverse.mpr ⟨φ, hleft, hright⟩

namespace OctFrame

variable {T : TitsSystem G 8} (F : OctFrame T)

open Classical in
noncomputable def xs (j : ℤ) (x : F.K) : G :=
  if x = 0 then 1 else T.nu' (j + 8) (F.xp (j + 8) ((F.sigma x * x)⁻¹).val)

theorem xs_zero (j : ℤ) : F.xs j 0 = 1 := by
  classical
  simp [xs]

theorem xp_ne_one_of_ne_zero {j : ℤ} (hj : Even j) {t : F.K} (ht : t ≠ 0) :
    F.xp j t.val ≠ 1 := by
  intro h
  have h0mem : (0 : F.K).val ∈ T.U 1 := by
    rw [F.val_zero]
    exact (T.U 1).one_mem
  have h0 : F.xp j (0 : F.K).val = 1 := by
    rw [F.val_zero, F.xp_one_eq]
  have hinj := (F.xp_bijOn hj).injOn t.mem h0mem
  have hval : t.val = (0 : F.K).val := hinj (by rw [h, h0])
  exact ht ((F.val_eq_one_iff).mp (by simpa [F.val_zero] using hval))

theorem xs_ne_one {j : ℤ} (hj : Even j) {x : F.K} (hx : x ≠ 0) : F.xs j x ≠ 1 := by
  classical
  have hj8 : Even (j + 8) := hj.add (show Even (8 : ℤ) from ⟨4, by norm_num⟩)
  have hσx : F.sigma x ≠ 0 := by
    intro h
    have hsq : x ^ 2 = 0 := by rw [← F.sigma_sigma x, h, map_zero]
    exact hx (mul_self_eq_zero.mp (by simpa [pow_two] using hsq))
  have harg : ((F.sigma x * x)⁻¹) ≠ 0 := inv_ne_zero (mul_ne_zero hσx hx)
  have hmem : F.xp (j + 8) ((F.sigma x * x)⁻¹).val ∈ T.U (j + 8) :=
    T.Uprime_le (j + 8) (F.xp_mem hj8 ((F.sigma x * x)⁻¹).mem)
  rw [xs, if_neg hx]
  exact T.nu'_ne_one (by norm_num : 3 ≤ 8) hmem (F.xp_ne_one_of_ne_zero hj8 harg)

theorem xs_mem {j : ℤ} (hj : Even j) (x : F.K) : F.xs j x ∈ T.Usec j := by
  classical
  by_cases hx : x = 0
  · rw [hx, F.xs_zero]
    exact Or.inl rfl
  · have hj8 : Even (j + 8) := hj.add (show Even (8 : ℤ) from ⟨4, by norm_num⟩)
    have hσx : F.sigma x ≠ 0 := by
      intro h
      have hsq : x ^ 2 = 0 := by rw [← F.sigma_sigma x, h, map_zero]
      exact hx (mul_self_eq_zero.mp (by simpa [pow_two] using hsq))
    have harg : ((F.sigma x * x)⁻¹) ≠ 0 := inv_ne_zero (mul_ne_zero hσx hx)
    rw [xs, if_neg hx]
    refine Or.inr ⟨F.xp (j + 8) ((F.sigma x * x)⁻¹).val, ?_, ?_, ?_⟩
    · have hmem := F.xp_mem hj8 ((F.sigma x * x)⁻¹).mem
      have hUp : T.Uprime (j + 8) = T.Uprime (j - 8) := by
        rw [show j + 8 = (j - 8) + 16 * 1 by ring, T.Uprime_add_two_mul]
      rwa [hUp] at hmem
    · exact F.xp_ne_one_of_ne_zero hj8 harg
    · have h := T.nu'_add_two_mul (by norm_num : 3 ≤ 8) (i := j - 8) (k := 1)
          (F.xp (j + 8) ((F.sigma x * x)⁻¹).val)
      simpa only [show (j - 8) + 2 * ((8 : ℕ) : ℤ) * 1 = j + 8 by ring] using h

theorem xs_mem_U {j : ℤ} (hj : Even j) (x : F.K) : F.xs j x ∈ T.U j :=
  T.Usec_subset j (F.xs_mem hj x)

theorem xs_of_ne_zero {j : ℤ} {x : F.K} (hx : x ≠ 0) :
    F.xs j x = T.nu' (j + 8) (F.xp (j + 8) ((F.sigma x * x)⁻¹).val) := by
  rw [xs, if_neg hx]

theorem a_conj_xs {j : ℤ} (hj : Even j) (x : F.K) :
    F.a * F.xs j x * F.a⁻¹ = F.xs (10 - j) x := by
  classical
  by_cases hx : x = 0
  · rw [hx, F.xs_zero, F.xs_zero]
    group
  · have hj8 : Even (j + 8) := hj.add (show Even (8 : ℤ) from ⟨4, by norm_num⟩)
    have hσx : F.sigma x ≠ 0 := by
      intro h
      have hsq : x ^ 2 = 0 := by rw [← F.sigma_sigma x, h, map_zero]
      exact hx (mul_self_eq_zero.mp (by simpa [pow_two] using hsq))
    have harg : ((F.sigma x * x)⁻¹) ≠ 0 := inv_ne_zero (mul_ne_zero hσx hx)
    have hmem : F.xp (j + 8) ((F.sigma x * x)⁻¹).val ∈ T.U (j + 8) :=
      T.Uprime_le (j + 8) (F.xp_mem hj8 ((F.sigma x * x)⁻¹).mem)
    have hne : F.xp (j + 8) ((F.sigma x * x)⁻¹).val ≠ 1 :=
      F.xp_ne_one_of_ne_zero hj8 harg
    have hmoves : T.Moves F.a (fun k => (-1 : ℤ) * k + 10) := by
      intro k
      simpa only [neg_one_mul, sub_eq_add_neg, add_comm] using F.moves_a k
    have hmc := (T.mu_conj (by norm_num : 3 ≤ 8) (g := F.a) (ε := -1) (c := 10)
      (Or.inr rfl) hmoves (i := j + 8) (u := F.xp (j + 8) ((F.sigma x * x)⁻¹).val)
      hmem hne).2.2
    have hxp : F.xp (2 - j) ((F.sigma x * x)⁻¹).val =
        F.a * F.xp (j + 8) ((F.sigma x * x)⁻¹).val * F.a⁻¹ := by
      rw [show 2 - j = 10 - (j + 8) by ring,
        F.a_conj_xp hj8 ((F.sigma x * x)⁻¹).mem]
    rw [show (-1 : ℤ) * (j + 8) + 10 = 2 - j by ring] at hmc
    rw [← hxp] at hmc
    simp only [xs, if_neg hx]
    have hnu : T.nu' (2 - j) (F.xp (2 - j) ((F.sigma x * x)⁻¹).val) =
        T.nu' (10 - j + 8) (F.xp (10 - j + 8) ((F.sigma x * x)⁻¹).val) := by
      have h := T.nu'_add_two_mul (by norm_num : 3 ≤ 8) (i := 2 - j) (k := 1)
        (F.xp (2 - j) ((F.sigma x * x)⁻¹).val)
      rw [show (2 - j) + 2 * ((8 : ℕ) : ℤ) * 1 = 10 - j + 8 by ring] at h
      have h3 : F.xp (10 - j + 8) ((F.sigma x * x)⁻¹).val =
          F.xp (2 - j) ((F.sigma x * x)⁻¹).val := by
        have h16 := F.xp_add_sixteen (2 - j) ((F.sigma x * x)⁻¹).val
        rwa [show (2 - j) + 16 = 10 - j + 8 by ring] at h16
      rw [h3]
      exact h.symm
    rw [hnu] at hmc
    exact hmc.symm

theorem xs_bijective {j : ℤ} (hj : Even j) :
    Function.Bijective (fun x : F.K => (⟨F.xs j x, F.xs_mem hj x⟩ : T.Usec j)) := by
  classical
  have hj8 : Even (j + 8) := hj.add (show Even (8 : ℤ) from ⟨4, by norm_num⟩)
  have hσne : ∀ {x : F.K}, x ≠ 0 → F.sigma x * x ≠ 0 := by
    intro x hx
    refine mul_ne_zero ?_ hx
    intro h
    have hsq : x ^ 2 = 0 := by rw [← F.sigma_sigma x, h, map_zero]
    exact hx (mul_self_eq_zero.mp (by simpa [pow_two] using hsq))
  have hargne : ∀ {x : F.K}, x ≠ 0 → ((F.sigma x * x)⁻¹) ≠ 0 := by
    intro x hx
    exact inv_ne_zero (hσne hx)
  constructor
  · intro x x' h
    have hxs : F.xs j x = F.xs j x' := congrArg Subtype.val h
    by_cases hx : x = 0
    · subst hx
      by_cases hx' : x' = 0
      · rw [hx']
      · exfalso
        have h1 : F.xs j 0 = 1 := F.xs_zero j
        have h2 : F.xs j x' ≠ 1 := F.xs_ne_one hj hx'
        exact h2 (hxs.symm.trans h1)
    · by_cases hx' : x' = 0
      · subst hx'
        exfalso
        have h1 : F.xs j x ≠ 1 := F.xs_ne_one hj hx
        have h2 : F.xs j 0 = 1 := F.xs_zero j
        exact h1 (hxs.trans h2)
      · have hu : F.xp (j + 8) ((F.sigma x * x)⁻¹).val ∈ T.Uprime (j + 8) :=
          F.xp_mem hj8 ((F.sigma x * x)⁻¹).mem
        have hu' : F.xp (j + 8) ((F.sigma x' * x')⁻¹).val ∈ T.Uprime (j + 8) :=
          F.xp_mem hj8 ((F.sigma x' * x')⁻¹).mem
        have hu1 : F.xp (j + 8) ((F.sigma x * x)⁻¹).val ≠ 1 :=
          F.xp_ne_one_of_ne_zero hj8 (hargne hx)
        have hu1' : F.xp (j + 8) ((F.sigma x' * x')⁻¹).val ≠ 1 :=
          F.xp_ne_one_of_ne_zero hj8 (hargne hx')
        have heq : T.nu' (j + 8) (F.xp (j + 8) ((F.sigma x * x)⁻¹).val) =
            T.nu' (j + 8) (F.xp (j + 8) ((F.sigma x' * x')⁻¹).val) := by
          rw [← F.xs_of_ne_zero hx, ← F.xs_of_ne_zero hx']
          exact hxs
        have hnu := T.mu_nu' (by norm_num : 3 ≤ 8) (T.Uprime_le (j + 8) hu) hu1
        have hnu' := T.mu_nu' (by norm_num : 3 ≤ 8) (T.Uprime_le (j + 8) hu') hu1'
        have hmain : F.xp (j + 8) ((F.sigma x * x)⁻¹).val =
            F.xp (j + 8) ((F.sigma x' * x')⁻¹).val := by
          rw [← hnu.2, ← hnu'.2]
          exact congrArg (T.nu ((j + 8) + 8)) heq
        have hval_eq : ((F.sigma x * x)⁻¹).val = ((F.sigma x' * x')⁻¹).val :=
          (F.xp_bijOn hj8).injOn ((F.sigma x * x)⁻¹).mem
            ((F.sigma x' * x')⁻¹).mem hmain
        have ht_eq : ((F.sigma x * x)⁻¹) = ((F.sigma x' * x')⁻¹) :=
          OctFrame.K.ext hval_eq
        have hmul : F.sigma x * x = F.sigma x' * x' := inv_injective ht_eq
        exact (sigma_mul_self_bijective F.sigma F.sigma_sigma).1 hmul
  · intro y
    have hy : y.val ∈ T.Usec j := y.2
    simp only [TitsSystem.Usec, Set.mem_setOf_eq] at hy
    rcases hy with hone | ⟨u, hu, hu1, heq⟩
    · exact ⟨0, Subtype.ext (by change F.xs j 0 = y.val; rw [F.xs_zero, hone])⟩
    · have hU : T.Uprime (j + 8) = T.Uprime (j - 8) := by
        rw [show j + 8 = (j - 8) + 16 * 1 by ring, T.Uprime_add_two_mul]
      have hu8 : u ∈ T.Uprime (j + 8) := by rw [hU]; exact hu
      obtain ⟨s, hs_mem, hs_eq⟩ := (F.xp_bijOn hj8).surjOn hu8
      let sK : F.K := ⟨s, hs_mem⟩
      have hsK_ne : sK ≠ 0 := by
        intro h0
        have hs1 : s = 1 := by
          have h := congrArg (fun z : F.K => z.val) h0
          simpa [sK, F.val_zero] using h
        have hone : F.xp (j + 8) s = 1 := by rw [hs1, F.xp_one_eq]
        exact hu1 (hs_eq.symm.trans hone)
      obtain ⟨x, hx_eq⟩ := (sigma_mul_self_bijective F.sigma F.sigma_sigma).2 (sK⁻¹)
      change F.sigma x * x = sK⁻¹ at hx_eq
      have hx_ne : x ≠ 0 := by
        intro h0
        have hzero : F.sigma x * x = 0 := by rw [h0]; simp
        rw [hx_eq] at hzero
        exact (inv_ne_zero hsK_ne) hzero
      refine ⟨x, Subtype.ext ?_⟩
      change F.xs j x = y.val
      have harg : ((F.sigma x * x)⁻¹) = sK := by rw [hx_eq, inv_inv]
      rw [F.xs_of_ne_zero hx_ne, harg, heq]
      change T.nu' (j + 8) (F.xp (j + 8) s) = T.nu' (j - 8) u
      rw [hs_eq]
      have h := T.nu'_add_two_mul (by norm_num : 3 ≤ 8) (i := j - 8) (k := 1) u
      rw [show (j - 8) + 2 * ((8 : ℕ) : ℤ) * 1 = j + 8 by ring] at h
      exact h

theorem xs_mul_xp_bijective {j : ℤ} (hj : Even j) :
    Function.Bijective (fun p : F.K × F.K =>
      (⟨F.xs j p.1 * F.xp j p.2.val, (T.U j).mul_mem (F.xs_mem_U hj p.1)
        (T.Uprime_le j (F.xp_mem hj p.2.mem))⟩ : T.U j)) := by
  classical
  constructor
  · rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have hval : F.xs j a * F.xp j b.val = F.xs j a' * F.xp j b'.val :=
      congrArg Subtype.val h
    have hb : F.xp j b.val ∈ T.Uprime j := F.xp_mem hj b.mem
    have hb' : F.xp j b'.val ∈ T.Uprime j := F.xp_mem hj b'.mem
    have ha : F.xs j a ∈ T.Usec j := F.xs_mem hj a
    have ha' : F.xs j a' ∈ T.Usec j := F.xs_mem hj a'
    have hcomm : F.xs j a * F.xp j b.val = F.xp j b.val * F.xs j a := by
      have h := T.Uprime_comm (j := j) (k := j) (by omega) (by omega) hb
        (T.Usec_subset j ha)
      exact h.symm
    have hcomm' : F.xs j a' * F.xp j b'.val = F.xp j b'.val * F.xs j a' := by
      have h := T.Uprime_comm (j := j) (k := j) (by omega) (by omega) hb'
        (T.Usec_subset j ha')
      exact h.symm
    have hmain : F.xp j b.val * F.xs j a = F.xp j b'.val * F.xs j a' := by
      rw [← hcomm, hval, hcomm']
    have hdec := TitsSystem.Uprime_mul_Usec_inj (T := T) F.hT hj hb hb' ha ha' hmain
    have hb_eq : b = b' := by
      exact OctFrame.K.ext ((F.xp_bijOn hj).injOn b.mem b'.mem hdec.1)
    have ha_eq : a = a' := by
      have h2 : (⟨F.xs j a, F.xs_mem hj a⟩ : T.Usec j) =
          ⟨F.xs j a', F.xs_mem hj a'⟩ := Subtype.ext hdec.2
      exact (F.xs_bijective hj).1 h2
    rw [ha_eq, hb_eq]
  · intro y
    obtain ⟨p, hp, q, hq, hy⟩ :=
      TitsSystem.mem_Uprime_mul_Usec (T := T) F.hT hj y.2
    obtain ⟨bp, hbp_mem, hbp_eq⟩ := (F.xp_bijOn hj).surjOn hp
    obtain ⟨a, ha_eq⟩ := (F.xs_bijective hj).2 ⟨q, hq⟩
    let b : F.K := ⟨bp, hbp_mem⟩
    refine ⟨(a, b), Subtype.ext ?_⟩
    change F.xs j a * F.xp j b.val = y.val
    rw [hy]
    have hbval : F.xp j b.val = p := hbp_eq
    have haval : F.xs j a = q := congrArg Subtype.val ha_eq
    rw [hbval, haval]
    exact (T.Uprime_comm (j := j) (k := j) (by omega) (by omega) hp
      (T.Usec_subset j hq)).symm

noncomputable def X (j : ℤ) (t : F.K) : G := if Even j then F.xs j t else F.xo j t.val

@[expose] noncomputable def X' (j : ℤ) (t : F.K) : G := F.xp j t.val

theorem X'_def (j : ℤ) (t : F.K) : F.X' j t = F.xp j t.val := rfl

theorem X_of_odd {j : ℤ} (hj : Odd j) (t : F.K) : F.X j t = F.xo j t.val := by
  simp [X, Int.not_even_iff_odd.mpr hj]

theorem X_of_even {j : ℤ} (hj : Even j) (t : F.K) : F.X j t = F.xs j t := by
  simp [X, hj]

theorem X_mem (j : ℤ) (t : F.K) : F.X j t ∈ T.U j := by
  by_cases hj : Even j
  · rw [F.X_of_even hj]
    exact F.xs_mem_U hj t
  · have ho : Odd j := Int.not_even_iff_odd.mp hj
    rw [F.X_of_odd ho]
    exact F.xo_mem ho t.mem

theorem X'_mem {j : ℤ} (hj : Even j) (t : F.K) : F.X' j t ∈ T.Uprime j :=
  F.xp_mem hj t.mem

theorem bij_odd_X {j : ℤ} (hj : Odd j) :
    Function.Bijective (fun t : F.K => (⟨F.X j t, F.X_mem j t⟩ : T.U j)) := by
  have hfun : (fun t : F.K => (⟨F.X j t, F.X_mem j t⟩ : T.U j)) =
      (fun t : F.K => (⟨F.xo j t.val, F.xo_mem hj t.mem⟩ : T.U j)) := by
    funext t
    exact Subtype.ext (F.X_of_odd hj t)
  rw [hfun]
  constructor
  · intro a b hab
    have hval : a.val = b.val :=
      (F.xo_bijOn hj).injOn a.mem b.mem (congrArg Subtype.val hab)
    exact OctFrame.K.ext hval
  · intro y
    obtain ⟨x, hxmem, hxy⟩ := (F.xo_bijOn hj).surjOn y.2
    exact ⟨⟨x, hxmem⟩, Subtype.ext hxy⟩

theorem bij_even_X {j : ℤ} (hj : Even j) :
    Function.Bijective (fun p : F.K × F.K => (⟨F.X j p.1 * F.X' j p.2,
      (T.U j).mul_mem (F.X_mem j p.1) (T.Uprime_le j (F.X'_mem hj p.2))⟩ : T.U j)) := by
  have hfun : (fun p : F.K × F.K => (⟨F.X j p.1 * F.X' j p.2,
        (T.U j).mul_mem (F.X_mem j p.1) (T.Uprime_le j (F.X'_mem hj p.2))⟩ : T.U j)) =
      (fun p : F.K × F.K => (⟨F.xs j p.1 * F.xp j p.2.val,
        (T.U j).mul_mem (F.xs_mem_U hj p.1)
          (T.Uprime_le j (F.xp_mem hj p.2.mem))⟩ : T.U j)) := by
    funext p
    apply Subtype.ext
    change F.X j p.1 * F.X' j p.2 = F.xs j p.1 * F.xp j p.2.val
    rw [F.X_of_even hj]
    rfl
  rw [hfun]
  exact F.xs_mul_xp_bijective hj

end OctFrame

noncomputable def OctFrame.toOctField {T : TitsSystem G 8} (F : OctFrame T) : OctField T.U where
  K := F.K
  σ := F.sigma
  σ_sq := F.sigma_sigma
  X := F.X
  X' := F.X'
  X_mem := F.X_mem
  X'_mem _ _ hj := T.Uprime_le _ (F.X'_mem hj _)
  bij_odd _ hj := F.bij_odd_X hj
  bij_even _ hj := F.bij_even_X hj

theorem exists_octField (T : TitsSystem G 8) (hT : T.Normalized) : Nonempty (OctField T.U) :=
  ⟨(Classical.choice (exists_octFrame hT)).toOctField⟩

end CFSG.GH74.Tits83

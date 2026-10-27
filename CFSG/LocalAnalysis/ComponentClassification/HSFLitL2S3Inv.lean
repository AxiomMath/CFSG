module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2S3Odd
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Skeleton

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

theorem field_mul_R8_eq_k8 : ∀ u : (ZMod 8)ˣ, ∀ b : ZMod 8, dbit8 b = 0 → fbit8 u = 1 →
    ∃ u' : (ZMod 8)ˣ, ∃ c : ZMod 8, (u' = 1 ∨ u' = -1) ∧ aff8 u b * aff8 u' (2 * c) = k8 := by
  decide

theorem k8_comm_R8 : ∀ u : (ZMod 8)ˣ, ∀ c : ZMod 8, (u = 1 ∨ u = -1) →
    k8 * aff8 u (2 * c) = aff8 u (2 * c) * k8 := by
  decide

theorem k8_mul_k8 : k8 * k8 = 1 := by decide

theorem k8_not_mem_R8 : k8 ∉ R8 := by decide

theorem x8_mul_y8_ne : x8 * y8 ≠ y8 * x8 := by decide

theorem fbit8_eq_zero_iff : ∀ u : (ZMod 8)ˣ, fbit8 u = 0 ↔ (u = 1 ∨ u = -1) := by decide

@[expose] def CentR8Odd (u : (ZMod 8)ˣ) (b : ZMod 8) (u' : (ZMod 8)ˣ) (b' : ZMod 8) : Prop :=
  dbit8 b' = 1 → aff8 u b * x8 = x8 * aff8 u b → aff8 u b * y8 = y8 * aff8 u b →
    aff8 u b * aff8 u' b' = aff8 u' b' * aff8 u b → aff8 u b = 1 ∨ aff8 u b = z8

instance (u b u' b') : Decidable (CentR8Odd u b u' b') := by unfold CentR8Odd; infer_instance

theorem cent_R8_odd : ∀ u b u' b', CentR8Odd u b u' b' := by decide

@[expose] def SqrtZ8Cent (u : (ZMod 8)ˣ) (b : ZMod 8) (u' : (ZMod 8)ˣ) (b' : ZMod 8) : Prop :=
  (u = 1 ∨ u = -1) → aff8 u b * aff8 u b = z8 → (u' = 1 ∨ u' = -1) →
    aff8 u' b' * aff8 u' b' = 1 → aff8 u b * aff8 u' b' = aff8 u' b' * aff8 u b →
    aff8 u' b' = 1 ∨ aff8 u' b' = z8

instance (u b u' b') : Decidable (SqrtZ8Cent u b u' b') := by unfold SqrtZ8Cent; infer_instance

theorem sqrt_z8_cent : ∀ u b u' b', SqrtZ8Cent u b u' b' := by decide

theorem dbit8_eq_one_of_not_mem_R8 {u : (ZMod 8)ˣ} {b : ZMod 8} (hu : u = 1 ∨ u = -1)
    (h : aff8 u b ∉ R8) : dbit8 b = 1 := by
  have hf : fbit8 u = 0 := (fbit8_eq_zero_iff u).mpr hu
  rcases zmod2_cases (dbit8 b) with h0 | h1
  · exact absurd ((type8_eq_one_iff_aux u b).mp ⟨h0, hf⟩) h
  · exact h1

theorem mem_zpowers_of_orderOf_eq_four {G : Type*} [Group G] {c g : G} (hc : orderOf c = 4)
    (hg : g ∈ zpowers c) : g = 1 ∨ g = c ∨ g = c ^ 2 ∨ g = c ^ 3 := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
  rw [← zpow_mod_orderOf, hc]
  have h0 : 0 ≤ k % ((4 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
  have h4 : k % ((4 : ℕ) : ℤ) < 4 := Int.emod_lt_of_pos _ (by norm_num)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k % ((4 : ℕ) : ℤ) = m := ⟨_, (Int.toNat_of_nonneg h0).symm⟩
  rw [hm] at h4 ⊢
  have hm4 : m < 4 := by omega
  interval_cases m <;> simp

namespace L2Data

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} (A : L2Data t L)

theorem commute_R_of_ψ_comm {g r : X} (hg : g ∈ A.T) (hr : r ∈ A.R)
    (h : A.ψ ⟨g, hg⟩ * A.ψ ⟨r, hr.1⟩ = A.ψ ⟨r, hr.1⟩ * A.ψ ⟨g, hg⟩) : g * r = r * g := by
  have hm : g * r * g⁻¹ ∈ A.R :=
    mem_inf.mpr ⟨mul_mem (mul_mem hg (mem_inf.mp hr).1) (inv_mem hg),
      (mem_normalizer_iff.mp (A.config.le_normalizer (A.T_le_centralizer hg)) r).mp
        (mem_inf.mp hr).2⟩
  have heq := A.eq_of_ψ_eq hm hr (by
    have e : (⟨g * r * g⁻¹, hm.1⟩ : A.T) = ⟨g, hg⟩ * ⟨r, hr.1⟩ * (⟨g, hg⟩ : A.T)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, h, mul_inv_cancel_right])
  calc g * r = g * r * g⁻¹ * g := by group
    _ = r * g := by rw [heq]

omit [Finite X] in
theorem ψ_sq {g : X} (hg : g ∈ A.T) :
    A.ψ ⟨g ^ 2, pow_mem hg 2⟩ = A.ψ ⟨g, hg⟩ * A.ψ ⟨g, hg⟩ := by
  rw [← map_mul]
  congr 1
  exact Subtype.ext (pow_two g)

omit [Finite X] in
theorem sq_mem_K {g : X} (hg : g ∈ A.T) (h : A.ψ ⟨g, hg⟩ * A.ψ ⟨g, hg⟩ = 1) : g ^ 2 ∈ A.K := by
  rw [A.mem_K_iff (pow_mem hg 2), A.ψ_sq hg, h]

omit [Finite X] in
theorem mul_inv_mem_R8 {g h : X} (hg : g ∈ A.T) (hh : h ∈ A.T) {u u' : (ZMod 8)ˣ}
    {b b' : ZMod 8} (hub : A.ψ ⟨g, hg⟩ = aff8 u b) (hub' : A.ψ ⟨h, hh⟩ = aff8 u' b')
    (hd : dbit8 b = dbit8 b') (hf : fbit8 u = fbit8 u') :
    A.ψ ⟨g * h⁻¹, mul_mem hg (inv_mem hh)⟩ ∈ R8 := by
  have e1 : A.ψ ⟨g * h⁻¹, mul_mem hg (inv_mem hh)⟩ = A.ψ ⟨g, hg⟩ * (A.ψ ⟨h, hh⟩)⁻¹ := by
    rw [← map_inv, ← map_mul]
    rfl
  rw [e1, hub, hub', aff8_inv, aff8_mul]
  obtain ⟨h₁, h₂⟩ := type8_mul_aux u u'⁻¹ b (-(↑u'⁻¹ * b'))
  refine (type8_eq_one_iff_aux _ _).mp ⟨?_, ?_⟩
  · rw [h₁, dbit8_neg_mul u' b', hd]
    exact CharTwo.add_self_eq_zero _
  · rw [h₂, fbit8_inv u', hf]
    exact CharTwo.add_self_eq_zero _

theorem commute_of_ψ_eq_one_or_z8 {z j : X} (hz : z ∈ A.R) (hψz : A.ψ ⟨z, hz.1⟩ = z8)
    (hz2 : z ^ 2 = 1) (hj : j ∈ A.T) (hj2 : j ^ 2 = 1)
    (hψj : A.ψ ⟨j, hj⟩ = 1 ∨ A.ψ ⟨j, hj⟩ = z8) {h : X} (hh : h ∈ A.T) : h * j = j * h := by
  have hht : h * t = t * h := A.commute_t hh
  have hhz : h * z = z * h := A.commute_z hz hψz hh
  rcases hψj with h1 | h1
  · rcases A.eq_one_or_eq_t ((A.mem_K_iff hj).mpr h1) hj2 with h2 | h2
    · rw [h2, mul_one, one_mul]
    · rw [h2]
      exact hht
  · have hm : z⁻¹ * j ∈ A.T := mul_mem (inv_mem hz.1) hj
    have hκ : z⁻¹ * j ∈ A.K := by
      rw [A.mem_K_iff hm]
      have : (⟨z⁻¹ * j, hm⟩ : A.T) = (⟨z, hz.1⟩ : A.T)⁻¹ * ⟨j, hj⟩ := rfl
      rw [this, map_mul, map_inv, hψz, h1, inv_mul_cancel]
    have hjz : j * z = z * j := A.commute_z hz hψz hj
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hz2])
    have hκ2 : (z⁻¹ * j) ^ 2 = 1 := by
      rw [hzi, pow_two]
      calc z * j * (z * j) = z * (j * z) * j := by group
        _ = z * (z * j) * j := by rw [hjz]
        _ = z ^ 2 * j ^ 2 := by rw [pow_two, pow_two]; group
        _ = 1 := by rw [hz2, hj2, one_mul]
    rcases A.eq_one_or_eq_t hκ hκ2 with h2 | h2
    · have : j = z := by
        calc j = z * (z⁻¹ * j) := by group
          _ = z := by rw [h2, mul_one]
      rw [this]
      exact hhz
    · have : j = z * t := by
        calc j = z * (z⁻¹ * j) := by group
          _ = z * t := by rw [h2]
      rw [this]
      calc h * (z * t) = h * z * t := by group
        _ = z * (h * t) := by rw [hhz]; group
        _ = z * t * h := by rw [hht]; group

theorem exists_field (hH : HaradaInput) (hnot : ¬ SectRank4 X) :
    ∃ (g : A.T) (u : (ZMod 8)ˣ) (b : ZMod 8), aff8 u b = A.ψ g ∧ dbit8 b = 0 ∧ fbit8 u = 1 := by
  by_contra h
  exact hnot (A.gen4_of_no_field hH fun g u b hub hc => h ⟨g, u, b, hub, hc.1, hc.2⟩)

theorem exists_k8 (hH : HaradaInput) (hnot : ¬ SectRank4 X) :
    ∃ k, ∃ hk : k ∈ A.T, A.ψ ⟨k, hk⟩ = k8 := by
  obtain ⟨⟨g, hg⟩, u, b, hub, hd, hf⟩ := A.exists_field hH hnot
  obtain ⟨u', c, hu', hc⟩ := field_mul_R8_eq_k8 u b hd hf
  obtain ⟨r, hr, hψr⟩ := A.exists_mem_R_ψ_eq (σ := aff8 u' (2 * c)) ⟨u', c, hu', rfl⟩
  refine ⟨g * r, mul_mem hg hr.1, ?_⟩
  rw [A.ψ_mul hg hr.1, hψr, ← hc, hub]

theorem exists_inv_not_mem_R8 (hH : HaradaInput) (hnot : ¬ SectRank4 X) :
    ∃ d, ∃ hd : d ∈ A.T, d ^ 2 = 1 ∧ A.ψ ⟨d, hd⟩ ∉ R8 := by
  by_contra hall
  push Not at hall
  apply hnot
  suffices h : ∃ g ∈ A.T, g ^ 2 = t ∧ ∀ i ∈ A.T, i ^ 2 = 1 → g * i = i * g by
    obtain ⟨g, hg, hgt, hgc⟩ := h
    exact A.gen4_of_fix (A.fix_of_sq hg hgt hgc)
  by_cases hK : Nat.card A.K = 2
  · obtain ⟨k, hk, hψk⟩ := A.exists_k8 hH hnot
    have hk2 : k ^ 2 ∈ A.K := A.sq_mem_K hk (by rw [hψk]; exact k8_mul_k8)
    refine ⟨k, hk, ?_, fun i hi hi2 => ?_⟩
    · rcases A.eq_one_or_eq_t_of_card hK hk2 with h | h
      · exact absurd (hψk ▸ hall k hk h) k8_not_mem_R8
      · exact h
    · obtain ⟨r, hr, κ, hκ, rfl⟩ := A.exists_eq_mul_of_mem_R8 hi (hall i hi hi2)
      have hkr : k * r = r * k := A.commute_R_of_ψ_comm hk hr (by
        rw [hψk]
        obtain ⟨u, c, hu, hc⟩ := A.ψ_mem_R8' hr
        rw [← hc]
        exact k8_comm_R8 u c hu)
      have hkt : k * t = t * k := A.commute_t hk
      rcases A.eq_one_or_eq_t_of_card hK hκ with h | h
      · rw [h, mul_one]
        exact hkr
      · rw [h]
        calc k * (r * t) = k * r * t := by group
          _ = r * (k * t) := by rw [hkr]; group
          _ = r * t * k := by rw [hkt]; group
  · obtain ⟨c, hcK, -, hc2⟩ := A.exists_sq_eq_t hK
    refine ⟨c, (mem_inf.mp hcK).1, hc2, fun i hi hi2 => ?_⟩
    obtain ⟨r, hr, κ, hκ, rfl⟩ := A.exists_eq_mul_of_mem_R8 hi (hall i hi hi2)
    exact (A.commute_K_of_mem_RK hr hκ hcK).symm

theorem conj_eq_or_eq_inv {c g : X} (hcK : c ∈ A.K) (hco : orderOf c = 4) (hc2 : c ^ 2 = t)
    (hg : g ∈ A.T) : g * c * g⁻¹ = c ∨ g * c * g⁻¹ = c⁻¹ := by
  have ht1 : t ≠ 1 := fun h => by
    have := A.orderOf_t
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have hgco : orderOf (g * c * g⁻¹) = 4 := by
    rw [← hco]
    exact (SemiconjBy.orderOf_eq g (by unfold SemiconjBy; group)).symm
  have hmem : g * c * g⁻¹ ∈ zpowers c :=
    A.mem_zpowers_of_sq_ne_one (A.conj_mem_K hg hcK) hgco hcK (by rw [hc2]; exact ht1)
  have hsq : (g * c * g⁻¹) ^ 2 = t := by
    rw [conj_pow, hc2]
    calc g * t * g⁻¹ = t * g * g⁻¹ := by rw [A.commute_t hg]
      _ = t := by group
  have hc4 : c ^ 4 = 1 := by rw [← hco, pow_orderOf_eq_one]
  rcases mem_zpowers_of_orderOf_eq_four hco hmem with h | h | h | h
  · rw [h, one_pow] at hsq
    exact absurd hsq.symm ht1
  · exact Or.inl h
  · have h4 : (c ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hc4
    rw [h, h4] at hsq
    exact absurd hsq.symm ht1
  · right
    rw [h]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hc4)

theorem card_K_of_inv_D16 (hH : HaradaInput) (hnot : ¬ SectRank4 X)
    (hinv : ∀ g : A.T, (g : X) ^ 2 = 1 → A.ψ g ∈ D16) : Nat.card A.K = 2 := by
  by_contra hK
  obtain ⟨c, hcK, hco, hc2⟩ := A.exists_sq_eq_t hK
  have hcT : c ∈ A.T := (mem_inf.mp hcK).1
  obtain ⟨d, hd, hd2, hdR⟩ := A.exists_inv_not_mem_R8 hH hnot
  obtain ⟨u, b, hu, hub⟩ := hinv ⟨d, hd⟩ hd2
  have hdb : dbit8 b = 1 := dbit8_eq_one_of_not_mem_R8 hu (by rw [hub]; exact hdR)
  apply hnot
  rcases A.conj_eq_or_eq_inv hcK hco hc2 hd with hdc | hdc
  ·
    have hcd : c * d = d * c := by
      calc c * d = d * c * d⁻¹ * d := by rw [hdc]
        _ = d * c := by group
    refine A.gen4_of_fix (A.fix_of_sq hcT hc2 fun i hi hi2 => ?_)
    by_cases hiR : A.ψ ⟨i, hi⟩ ∈ R8
    · obtain ⟨r, hr, κ, hκ, rfl⟩ := A.exists_eq_mul_of_mem_R8 hi hiR
      exact (A.commute_K_of_mem_RK hr hκ hcK).symm
    · obtain ⟨u', b', hu', hub'⟩ := hinv ⟨i, hi⟩ hi2
      have hib : dbit8 b' = 1 := dbit8_eq_one_of_not_mem_R8 hu' (by rw [hub']; exact hiR)
      have hid := A.mul_inv_mem_R8 hi hd hub'.symm hub.symm (hib.trans hdb.symm)
        (((fbit8_eq_zero_iff u').mpr hu').trans ((fbit8_eq_zero_iff u).mpr hu).symm)
      obtain ⟨r, hr, κ, hκ, hrκ⟩ := A.exists_eq_mul_of_mem_R8 _ hid
      have hi' : i = r * κ * d := by
        calc i = i * d⁻¹ * d := by group
          _ = r * κ * d := by rw [hrκ]
      have h1 := A.commute_K_of_mem_RK hr hκ hcK
      rw [hi']
      calc c * (r * κ * d) = c * (r * κ) * d := by group
        _ = r * κ * c * d := by rw [← h1]
        _ = r * κ * (c * d) := by group
        _ = r * κ * (d * c) := by rw [hcd]
        _ = r * κ * d * c := by group
  ·
    obtain ⟨z, hz, y, hy, hz', hy', hψz, hψy⟩ := A.exists_z_y
    obtain ⟨x, hx, hψx⟩ := A.exists_mem_R_ψ_eq (σ := x8) ⟨1, 1, Or.inl rfl, by decide⟩
    have hz2 : z ^ 2 = 1 := A.sq_eq_one_of_mem_R hz (by rw [hψz]; decide)
    have hy2 : y ^ 2 = 1 := A.sq_eq_one_of_mem_R hy (by rw [hψy]; decide)
    have hxy : x * y ≠ y * x := fun h => x8_mul_y8_ne (by
      rw [← hψx, ← hψy, ← A.ψ_mul hx.1 hy.1, ← A.ψ_mul hy.1 hx.1]
      congr 1
      exact Subtype.ext h)
    set U : Subgroup X := closure {i | i ∈ A.T ∧ i ^ 2 = 1} with hU
    have hUT : U ≤ A.T := (closure_le _).mpr fun i hi => hi.1
    have hUD : ∀ g (hg : g ∈ U), A.ψ ⟨g, hUT hg⟩ ∈ D16 := by
      have hle : U ≤ (D16.comap A.ψ).map A.T.subtype :=
        (closure_le _).mpr fun i hi => ⟨⟨i, hi.1⟩, hinv ⟨i, hi.1⟩ hi.2, rfl⟩
      intro g hg
      obtain ⟨g', hg', hgg'⟩ := hle hg
      have : (⟨g, hUT hg⟩ : A.T) = g' := Subtype.ext hgg'.symm
      rw [this]
      exact hg'
    have hUw : ∀ w ∈ normalizer (A.T : Set X), ∀ g ∈ U, w * g * w⁻¹ ∈ U := by
      intro w hw g hg
      have hle : U ≤ U.comap (MulAut.conj w).toMonoidHom := (closure_le _).mpr fun i hi => by
        show w * i * w⁻¹ ∈ U
        refine subset_closure ⟨A.conj_mem_T hw hi.1, ?_⟩
        rw [conj_pow, hi.2, mul_one, mul_inv_cancel]
      exact hle hg
    have hcy : c * y ∈ U := by
      have hcd2 : (c * d) ^ 2 = 1 := by
        calc (c * d) ^ 2 = c * (d * c * d⁻¹) * (d * d) := by rw [pow_two]; group
          _ = 1 := by rw [hdc, ← pow_two, hd2]; group
      have h1 : c * d ∈ U := subset_closure ⟨mul_mem hcT hd, hcd2⟩
      have h2 : d ∈ U := subset_closure ⟨hd, hd2⟩
      have h3 : y ∈ U := subset_closure ⟨hy.1, hy2⟩
      have : c * y = c * d * d⁻¹ * y := by group
      rw [this]
      exact mul_mem (mul_mem h1 (inv_mem h2)) h3
    have hcyc : c * y = y * c := (A.commute_of_mem_R_of_mem_K hy hcK).symm
    have hcy2 : (c * y) ^ 2 = t := by
      calc (c * y) ^ 2 = c * (y * c) * y := by rw [pow_two]; group
        _ = c ^ 2 * y ^ 2 := by rw [← hcyc, pow_two, pow_two]; group
        _ = t := by rw [hc2, hy2, mul_one]
    refine A.gen4_of_fix fun w hw => ?_
    have heT : w * t * w⁻¹ ∈ A.T := A.conj_mem_T hw A.t_mem_T
    have hecent : ∀ g ∈ A.T, g * (w * t * w⁻¹) = w * t * w⁻¹ * g := by
      intro g hg
      have h1 := A.commute_t (A.conj_inv_mem_T hw hg)
      calc g * (w * t * w⁻¹) = w * (w⁻¹ * g * w * t) * w⁻¹ := by group
        _ = w * (t * (w⁻¹ * g * w)) * w⁻¹ := by rw [h1]
        _ = w * t * w⁻¹ * g := by group
    obtain ⟨u₀, b₀, hub₀⟩ := A.exists_aff8 ⟨w * t * w⁻¹, heT⟩
    have hψe : A.ψ ⟨w * t * w⁻¹, heT⟩ = 1 ∨ A.ψ ⟨w * t * w⁻¹, heT⟩ = z8 := by
      rw [← hub₀]
      refine cent_R8_odd u₀ b₀ u b hdb ?_ ?_ ?_
      · rw [hub₀, ← hψx, ← A.ψ_mul heT hx.1, ← A.ψ_mul hx.1 heT]
        congr 1
        exact Subtype.ext (hecent x hx.1).symm
      · rw [hub₀, ← hψy, ← A.ψ_mul heT hy.1, ← A.ψ_mul hy.1 heT]
        congr 1
        exact Subtype.ext (hecent y hy.1).symm
      · rw [hub₀, hub, ← A.ψ_mul heT hd, ← A.ψ_mul hd heT]
        congr 1
        exact Subtype.ext (hecent d hd).symm
    rcases hψe with h1 | h1
    · exact A.eq_t_of_mem_K ((A.mem_K_iff heT).mpr h1) (A.conj_t_sq w) (A.conj_t_ne_one w)
    · exfalso
      have hgU : w * (c * y) * w⁻¹ ∈ U := hUw w hw _ hcy
      have hjT : w * y * w⁻¹ ∈ A.T := A.conj_mem_T hw hy.1
      have hj2 : (w * y * w⁻¹) ^ 2 = 1 := by rw [conj_pow, hy2]; group
      have hgj : w * (c * y) * w⁻¹ * (w * y * w⁻¹) = w * y * w⁻¹ * (w * (c * y) * w⁻¹) := by
        calc w * (c * y) * w⁻¹ * (w * y * w⁻¹) = w * (c * y * y) * w⁻¹ := by group
          _ = w * (y * c * y) * w⁻¹ := by rw [hcyc]
          _ = w * y * w⁻¹ * (w * (c * y) * w⁻¹) := by group
      have hg2 : (w * (c * y) * w⁻¹) ^ 2 = w * t * w⁻¹ := by rw [conj_pow, hcy2]
      obtain ⟨u₁, b₁, hu₁, hub₁⟩ := hUD _ hgU
      obtain ⟨u₂, b₂, hu₂, hub₂⟩ := hinv ⟨w * y * w⁻¹, hjT⟩ hj2
      have key := sqrt_z8_cent u₁ b₁ u₂ b₂ hu₁ ?_ hu₂ ?_ ?_
      · have hjc := A.commute_of_ψ_eq_one_or_z8 hz hψz hz2 hjT hj2 (by rw [← hub₂]; exact key)
          (A.conj_mem_T hw hx.1)
        apply hxy
        have h3 : w * (x * y) * w⁻¹ = w * (y * x) * w⁻¹ := by
          calc w * (x * y) * w⁻¹ = w * x * w⁻¹ * (w * y * w⁻¹) := by group
            _ = w * y * w⁻¹ * (w * x * w⁻¹) := hjc
            _ = w * (y * x) * w⁻¹ := by group
        exact mul_left_cancel (mul_right_cancel h3)
      · rw [hub₁, ← A.ψ_sq (hUT hgU)]
        have : (⟨(w * (c * y) * w⁻¹) ^ 2, pow_mem (hUT hgU) 2⟩ : A.T) = ⟨w * t * w⁻¹, heT⟩ :=
          Subtype.ext hg2
        rw [this, h1]
      · rw [hub₂, ← A.ψ_sq hjT]
        have : (⟨(w * y * w⁻¹) ^ 2, pow_mem hjT 2⟩ : A.T) = 1 := Subtype.ext hj2
        rw [this, map_one]
      · rw [hub₁, hub₂, ← A.ψ_mul (hUT hgU) hjT, ← A.ψ_mul hjT (hUT hgU)]
        congr 1
        exact Subtype.ext hgj

end L2Data

end CFSG.ComponentClassification.HSFLit

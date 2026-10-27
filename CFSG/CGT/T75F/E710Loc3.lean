module

public import CFSG.CGT.T75F.E710Loc1
public import CFSG.CGT.Timmesfeld75.Sec78Linear

public section

namespace CFSG.CGT.T75F

open CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped MatrixGroups Matrix commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G} {m : ℕ}
  [(T.subgroupOf (hSub T (normIn T₁ T))).Normal]

theorem mem_hSub_of_mem_normIn₁ (M : TModel T T₁ 3 m) (hc : Sec6Ctx T T₁ 3 m) {e : G}
    (he : e ∈ normIn T₁ T) : e ∈ hSub T (normIn T₁ T) := by
  by_cases he1 : e = 1
  · rw [he1]; exact Subgroup.one_mem _
  · exact M.mem_H (mem_normD_of_mem_normIn₁ hc he he1).1

theorem exists_vec_normIn₁ (M : TModel T T₁ 3 m) (h63 : Sec63) (hc : Sec6Ctx T T₁ 3 m)
    {f : Module.Dual (GaloisField 2 m) (Fin 3 → GaloisField 2 m)} (hf : f ≠ 0)
    (hLz : ∀ (t : G) (ht : t ∈ T),
      t ∈ normIn T T₁ ↔ f (Multiplicative.toAdd (M.φ ⟨t, ht⟩)) = 0)
    {e : G} (he : e ∈ normIn T₁ T) :
    ∃ v' : Fin 3 → GaloisField 2 m, f v' = 0 ∧ ∀ w, sact (ubar M.ε e) w = w + f w • v' := by
  by_cases he1 : e = 1
  · refine ⟨0, map_zero f, fun w => ?_⟩
    rw [he1, ubar_of_mem_T M.ε left_le_hSub (Subgroup.one_mem T), sact_one]
    simp
  obtain ⟨fe, ve, hfe, hve, hfev, hdatae, hLe⟩ := exists_data_normIn₁ M h63 hc he he1
  obtain ⟨w₀, hw₀⟩ := exists_dual_apply_eq_one hf
  have hker : ∀ w, f w = 0 → fe w = 0 := by
    intro w hw
    set t : ↥T := M.φ.symm (Multiplicative.ofAdd w) with ht
    have h1 : Multiplicative.toAdd (M.φ ⟨(t : G), t.2⟩) = w := by
      have : (⟨(t : G), t.2⟩ : ↥T) = t := rfl
      rw [this, ht, M.φ.apply_symm_apply]
      rfl
    have h2 : (t : G) ∈ normIn T T₁ := (hLz _ t.2).2 (by rw [h1]; exact hw)
    have := (hLe _ t.2).1 h2
    rwa [h1] at this
  have hfe' := apply_eq_mul_of_ker_le hker hw₀
  set c := fe w₀ with hc0
  have hc : c ≠ 0 := by
    intro h0
    apply hfe
    refine LinearMap.ext fun w => ?_
    rw [hfe' w, h0, mul_zero]
    rfl
  refine ⟨c • ve, ?_, fun w => ?_⟩
  · have h1 : fe ve = f ve * c := hfe' ve
    rw [hfev] at h1
    have h2 : f ve = 0 := by
      rcases mul_eq_zero.1 h1.symm with h | h
      · exact h
      · exact absurd h hc
    rw [map_smul, h2]
    exact smul_zero c
  · rw [hdatae, hfe' w, mul_smul]

theorem exists_normIn₁_of_vec (M : TModel T T₁ 3 m) (h63 : Sec63) (hc : Sec6Ctx T T₁ 3 m)
    {f : Module.Dual (GaloisField 2 m) (Fin 3 → GaloisField 2 m)} (hf : f ≠ 0)
    (hLz : ∀ (t : G) (ht : t ∈ T),
      t ∈ normIn T T₁ ↔ f (Multiplicative.toAdd (M.φ ⟨t, ht⟩)) = 0)
    {v₀ : Fin 3 → GaloisField 2 m} (hv₀ : f v₀ = 0) :
    ∃ e ∈ normIn T₁ T, ∀ w, sact (ubar M.ε e) w = w + f w • v₀ := by
  have := hc.finite
  have hcfg := hc.sec3.cfg
  obtain ⟨w₀, hw₀⟩ := exists_dual_apply_eq_one hf
  have hvec : ∀ e : ↥(normIn T₁ T), ∃ v' : Fin 3 → GaloisField 2 m, f v' = 0 ∧
      ∀ w, sact (ubar M.ε (e : G)) w = w + f w • v' := fun e =>
    exists_vec_normIn₁ M h63 hc hf hLz e.2
  choose Φ hΦ using hvec
  have hinj : Function.Injective (fun e : ↥(normIn T₁ T) =>
      (⟨Φ e, LinearMap.mem_ker.2 (hΦ e).1⟩ : LinearMap.ker f)) := by
    intro e e' hee
    have h1 : Φ e = Φ e' := congrArg Subtype.val hee
    have h2 : ubar M.ε (e : G) = ubar M.ε (e' : G) := by
      apply eq_of_sact
      intro w
      rw [(hΦ e).2 w, (hΦ e').2 w, h1]
    rw [ubar_eq_iff M.ε (mem_hSub_of_mem_normIn₁ M hc e.2) (mem_hSub_of_mem_normIn₁ M hc e'.2)]
      at h2
    have h3 : (e : G)⁻¹ * e' ∈ T ⊓ T₁ :=
      ⟨h2, T₁.mul_mem (T₁.inv_mem (normIn_le _ _ e.2)) (normIn_le _ _ e'.2)⟩
    rw [hcfg.inf, Subgroup.mem_bot] at h3
    exact Subtype.ext (inv_mul_eq_one.1 h3)
  have hm0 : m ≠ 0 := by
    rintro rfl
    have := hc.hy.card
    rw [hc.hT] at this
    simp at this
  have hcardF : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m hm0
  have hker : Nat.card (LinearMap.ker f) = (2 ^ m) ^ 2 := by
    have h1 := Module.Dual.finrank_ker_add_one_of_ne_zero hf
    have h3 : Module.finrank (GaloisField 2 m) (Fin 3 → GaloisField 2 m) = 3 := by simp
    have h4 : Module.finrank (GaloisField 2 m) (LinearMap.ker f) = 2 := by omega
    rw [Module.natCard_eq_pow_finrank (K := GaloisField 2 m), h4, hcardF]
  have hbij := hinj.bijective_of_nat_card_le (by
    rw [hker]
    exact le_of_eq (card_normIn₁_three hc).symm)
  obtain ⟨e, he⟩ := hbij.2 ⟨v₀, LinearMap.mem_ker.2 hv₀⟩
  have h1 : Φ e = v₀ := congrArg Subtype.val he
  exact ⟨e, e.2, fun w => by rw [(hΦ e).2 w, h1]⟩

theorem comm_mem_normIn (M : TModel T T₁ 3 m) (h63 : Sec63) (hc : Sec6Ctx T T₁ 3 m) {e s : G}
    (he : e ∈ normIn T₁ T) (hs : s ∈ T) : ⁅e, s⁆ ∈ normIn T T₁ := by
  by_cases he1 : e = 1
  · rw [he1, commutatorElement_def]
    simp [(normIn T T₁).one_mem]
  obtain ⟨hD, hT⟩ := mem_normD_of_mem_normIn₁ hc he he1
  obtain ⟨f, v, hf, hv, hfv, hdata, hL⟩ := exists_data_normIn₁ M h63 hc he he1
  have hmem : ⁅e, s⁆ ∈ T := comm_mem_of_mem_normalizer hD.2 hs
  rw [hL _ hmem, M.toAdd_phi_comm_eq hD hdata hs, map_smul, hfv, smul_zero]

theorem conj_mem_cfgM (M : TModel T T₁ 3 m) (h63 : Sec63) (hc : Sec6Ctx T T₁ 3 m) {s a : G}
    (hs : s ∈ T) (ha : a ∈ cfgM T T₁) : s * a * s⁻¹ ∈ cfgM T T₁ := by
  have hcfg := hc.sec3.cfg
  obtain ⟨l, hl, e, he, rfl⟩ := hcfg.mem_cfgM_iff.1 ha
  have hcomm := comm_mem_normIn M h63 hc he hs
  have h1 : s * (l * e) * s⁻¹ = (l * (⁅e, s⁆)⁻¹) * e := by
    have hlc : s * l = l * s := elemAbelian_mul_comm hc.hy.pair.wc.1 hs (normIn_le _ _ hl)
    rw [commutatorElement_def]
    calc s * (l * e) * s⁻¹ = (s * l) * (e * s⁻¹) := by group
      _ = (l * s) * (e * s⁻¹) := by rw [hlc]
      _ = (l * (e * s * e⁻¹ * s⁻¹)⁻¹) * e := by group
  rw [h1]
  exact hcfg.mem_cfgM_iff.2 ⟨l * (⁅e, s⁆)⁻¹, (normIn T T₁).mul_mem hl ((normIn T T₁).inv_mem hcomm),
    e, he, rfl⟩

end CFSG.CGT.T75F

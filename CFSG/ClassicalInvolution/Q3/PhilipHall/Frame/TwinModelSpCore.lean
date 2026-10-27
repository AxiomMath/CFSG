module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.BorelTits.FormFlag

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinModel

open CFSG.LieType.BorelTits

variable {K : Type} {V : Type} {H : Type} [Field K] [AddCommGroup V] [Module K V] [Group H]

section Core

variable (F : ReflForm K V) (ρ : H →* Module.End K V)

@[expose] def IsTrans (h : H) (b : V) : Prop :=
  ∀ v, ρ h v = v + F.β b v • b

variable {F ρ}

theorem two_eq_zero (hK : ∀ c : K, c = 0 ∨ c = 1) : (2 : K) = 0 := by
  have h1 : (1 : K) + 1 = 0 := by
    rcases hK (1 + 1) with h | h
    · exact h
    · exact absurd (by linear_combination h : (1 : K) = 0) one_ne_zero
  linear_combination h1

theorem conj_isTrans (hρ : IsIsometric F ρ) {h : H} {b : V} (ht : IsTrans F ρ h b) (g : H) :
    IsTrans F ρ (g * h * g⁻¹) (ρ g b) := by
  intro v
  have h1 : F.β b (ρ g⁻¹ v) = F.β (ρ g b) v := by
    rw [← hρ g b (ρ g⁻¹ v), rep_apply_inv_apply]
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ht, map_add, map_smul,
    rep_apply_inv_apply, h1]

theorem isTrans_unique (hinj : Function.Injective ρ) {h h' : H} {b : V}
    (ht : IsTrans F ρ h b) (ht' : IsTrans F ρ h' b) : h = h' :=
  hinj (LinearMap.ext fun v => by rw [ht, ht'])

theorem isTrans_mul_self (halt : ∀ v, F.β v v = 0) (hK : ∀ c : K, c = 0 ∨ c = 1)
    (hinj : Function.Injective ρ) {h : H} {b : V} (ht : IsTrans F ρ h b) : h * h = 1 := by
  apply hinj
  ext1 v
  have h1 : ρ h (ρ h v) = ρ h v + F.β b (ρ h v) • b := ht (ρ h v)
  have h2 : F.β b (ρ h v) = F.β b v := by
    rw [ht v, F.add_right, F.smul_right, halt, mul_zero, add_zero]
  rw [map_mul, Module.End.mul_apply, h1, h2, ht v, map_one, Module.End.one_apply]
  have := two_eq_zero hK
  calc v + F.β b v • b + F.β b v • b = v + (2 : K) • (F.β b v • b) := by
        rw [two_smul]; abel
    _ = v := by rw [this, zero_smul, add_zero]

theorem isTrans_comm (hinj : Function.Injective ρ) {h h' : H} {b b' : V}
    (ht : IsTrans F ρ h b) (ht' : IsTrans F ρ h' b') (hbb : F.β b b' = 0) :
    h * h' = h' * h := by
  have hbb' : F.β b' b = 0 := F.refl _ _ hbb
  apply hinj
  ext1 v
  have e1 : ρ h (ρ h' v) = ρ h' v + F.β b (ρ h' v) • b := ht _
  have e2 : ρ h' (ρ h v) = ρ h v + F.β b' (ρ h v) • b' := ht' _
  have e3 : F.β b (ρ h' v) = F.β b v := by
    rw [ht' v, F.add_right, F.smul_right, hbb, mul_zero, add_zero]
  have e4 : F.β b' (ρ h v) = F.β b' v := by
    rw [ht v, F.add_right, F.smul_right, hbb', mul_zero, add_zero]
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e1, e2, e3, e4, ht v, ht' v]
  abel

theorem isTrans_inj_aux (hK : ∀ c : K, c = 0 ∨ c = 1) {h : H} {b b' : V}
    (ht : IsTrans F ρ h b) (ht' : IsTrans F ρ h b') (hb : b ≠ 0) : b = b' := by
  obtain ⟨v, hv⟩ : ∃ v, F.β b v ≠ 0 := by
    by_contra! hcon
    exact hb (F.nondeg b hcon)
  have h1 : F.β b v = 1 := (hK _).resolve_left hv
  have h2 := ht v
  rw [ht' v, h1, one_smul] at h2
  have h3 : F.β b' v • b' = b := by
    have := h2
    rw [add_right_inj] at this
    exact this
  have h4 : F.β b' v ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at h3
    exact hb h3.symm
  rw [(hK _).resolve_left h4, one_smul] at h3
  exact h3.symm

theorem isTrans_inj (hK : ∀ c : K, c = 0 ∨ c = 1) {h : H} {b b' : V}
    (ht : IsTrans F ρ h b) (ht' : IsTrans F ρ h b') : b = b' := by
  by_cases hb : b = 0
  · by_cases hb' : b' = 0
    · rw [hb, hb']
    · exact absurd ((isTrans_inj_aux hK ht' ht hb').trans hb) hb'
  · exact isTrans_inj_aux hK ht ht' hb

theorem fixes_of_isotropic (halt : ∀ v, F.β v v = 0) (hK : ∀ c : K, c = 0 ∨ c = 1)
    (hρ : IsIsometric F ρ) (hinj : Function.Injective ρ) [Finite H] (N : Subgroup H)
    (hodd : Odd (Nat.card N)) {t : H} {b : V} (ht : IsTrans F ρ t b)
    (htn : ∀ x ∈ N, t * x * t⁻¹ ∈ N) {x : H} (hx : x ∈ N) (hβ : F.β b (ρ x b) = 0) :
    ρ x b = b := by
  have ht' : IsTrans F ρ (x * t * x⁻¹) (ρ x b) := conj_isTrans hρ ht x
  have htt : t * t = 1 := isTrans_mul_self halt hK hinj ht
  have htt' : (x * t * x⁻¹) * (x * t * x⁻¹) = 1 := isTrans_mul_self halt hK hinj ht'
  have hcomm : t * (x * t * x⁻¹) = (x * t * x⁻¹) * t := isTrans_comm hinj ht ht' hβ
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hy : t * (x * t * x⁻¹) ∈ N := by
    have : t * (x * t * x⁻¹) = (t * x * t⁻¹) * x⁻¹ := by rw [htinv]; group
    rw [this]
    exact N.mul_mem (htn x hx) (N.inv_mem hx)
  have hy2 : (t * (x * t * x⁻¹)) * (t * (x * t * x⁻¹)) = 1 := by
    calc (t * (x * t * x⁻¹)) * (t * (x * t * x⁻¹))
        = t * ((x * t * x⁻¹) * t) * (x * t * x⁻¹) := by group
      _ = t * (t * (x * t * x⁻¹)) * (x * t * x⁻¹) := by rw [hcomm]
      _ = (t * t) * ((x * t * x⁻¹) * (x * t * x⁻¹)) := by group
      _ = 1 := by rw [htt, htt', one_mul]
  have hord : orderOf (t * (x * t * x⁻¹)) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hy2)
  have hord2 : orderOf (t * (x * t * x⁻¹)) ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hy
  have hodd' : Odd (orderOf (t * (x * t * x⁻¹))) := Odd.of_dvd_nat hodd hord2
  have h1 : orderOf (t * (x * t * x⁻¹)) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
    · exact h
    · rw [h] at hodd'; exact absurd hodd' (by decide)
  have hy1 : t * (x * t * x⁻¹) = 1 := orderOf_eq_one_iff.mp h1
  have heq : x * t * x⁻¹ = t := by
    have := congrArg (t * ·) hy1
    simp only [mul_one] at this
    have h2 : x * t * x⁻¹ = t⁻¹ := eq_inv_of_mul_eq_one_right hy1
    rw [h2, htinv]
  have ht'' : IsTrans F ρ t (ρ x b) := heq ▸ ht'
  exact (isTrans_inj hK ht ht'').symm

@[expose] def fixedV (ρ : H →* Module.End K V) (N : Subgroup H) : Submodule K V where
  carrier := {v | ∀ x ∈ N, ρ x v = v}
  add_mem' := fun ha hb x hx => by rw [map_add, ha x hx, hb x hx]
  zero_mem' := fun x _ => map_zero _
  smul_mem' := fun c v hv x hx => by rw [map_smul, hv x hx]

@[expose] def commV (ρ : H →* Module.End K V) (N : Subgroup H) : Submodule K V :=
  Submodule.span K {w | ∃ x ∈ N, ∃ u, w = ρ x u - u}

theorem sub_mem_commV {N : Subgroup H} {x : H} (hx : x ∈ N) (u : V) : ρ x u - u ∈ commV ρ N :=
  Submodule.subset_span ⟨x, hx, u, rfl⟩

theorem fixedV_inf_commV (hK : ∀ c : K, c = 0 ∨ c = 1) (N : Subgroup H) [Finite N]
    (hodd : Odd (Nat.card N)) : fixedV ρ N ⊓ commV ρ N = ⊥ := by
  classical
  have : Fintype N := Fintype.ofFinite N
  let e : Module.End K V := ∑ x : N, ρ (x : H)
  have hcomm : commV ρ N ≤ LinearMap.ker e := by
    refine Submodule.span_le.mpr ?_
    rintro w ⟨x, hx, u, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    simp only [e, LinearMap.sum_apply, map_sub]
    rw [sub_eq_zero]
    refine Fintype.sum_equiv (Equiv.mulRight (⟨x, hx⟩ : N)) _ _ fun y => ?_
    simp [← Module.End.mul_apply, ← map_mul]
  have hfix : ∀ v ∈ fixedV ρ N, e v = v := by
    intro v hv
    simp only [e, LinearMap.sum_apply]
    rw [Finset.sum_congr rfl (fun (y : N) _ => hv (y : H) y.2), Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card]
    obtain ⟨k, hk⟩ := hodd
    have h2 := two_eq_zero hK
    rw [hk, ← Nat.cast_smul_eq_nsmul K, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat,
      h2]
    simp
  rw [eq_bot_iff]
  intro v ⟨hv1, hv2⟩
  have := hfix v hv1
  rw [LinearMap.mem_ker.mp (hcomm hv2)] at this
  exact (Submodule.mem_bot K).mpr this.symm

theorem map_mem_commV {N : Subgroup H} {h : H} (hh : ∀ x ∈ N, h * x * h⁻¹ ∈ N) {v : V}
    (hv : v ∈ commV ρ N) : ρ h v ∈ commV ρ N := by
  have : commV ρ N ≤ (commV ρ N).comap (ρ h) := by
    refine Submodule.span_le.mpr ?_
    rintro w ⟨x, hx, u, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, map_sub]
    have e : ρ h (ρ x u) = ρ (h * x * h⁻¹) (ρ h u) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      congr 2
      group
    rw [e]
    exact sub_mem_commV (hh x hx) _
  exact this hv

theorem eq_bot_of_normalized_odd (halt : ∀ v, F.β v v = 0) (hK : ∀ c : K, c = 0 ∨ c = 1)
    (hρ : IsIsometric F ρ) (hinj : Function.Injective ρ)
    (htrans : ∀ x : V, ∃ h : H, IsTrans F ρ h x) [Finite H] [FiniteDimensional K V]
    {s : H} (hs2 : s * s = 1) (hs1 : s ≠ 1) (N : Subgroup H)
    (hNC : N ≤ Subgroup.centralizer ({s} : Set H))
    (hNn : ∀ c ∈ Subgroup.centralizer ({s} : Set H), ∀ x ∈ N, c * x * c⁻¹ ∈ N)
    (hodd : Odd (Nat.card N)) : N = ⊥ := by
  have h2 := two_eq_zero hK
  have hss : ∀ u, ρ s (ρ s u) = u := fun u => by
    rw [← Module.End.mul_apply, ← map_mul, hs2, map_one, Module.End.one_apply]
  let W : Submodule K V := LinearMap.range (ρ s - 1)
  have hWmem : ∀ w, w ∈ W ↔ ∃ u, w = ρ s u - u := fun w => by
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, by simp⟩
    · rintro ⟨u, rfl⟩
      exact ⟨u, by simp⟩
  have hneg : ∀ v : V, -v = v := fun v =>
    neg_eq_of_add_eq_zero_right (by rw [← two_smul K v, h2, zero_smul])
  have hsW : ∀ w ∈ W, ρ s w = w := by
    intro w hw
    obtain ⟨u, rfl⟩ := (hWmem w).mp hw
    rw [map_sub, hss, ← neg_sub, hneg]
  have hWiso : ∀ w ∈ W, ∀ w' ∈ W, F.β w w' = 0 := by
    intro w hw w' hw'
    obtain ⟨u, rfl⟩ := (hWmem w).mp hw
    obtain ⟨u', rfl⟩ := (hWmem w').mp hw'
    have e1 : F.β u (ρ s u') = F.β (ρ s u) u' := by
      rw [← hρ s u (ρ s u'), hss]
    have e2 : F.β (ρ s u) (ρ s u') = F.β u u' := hρ s u u'
    rw [F.β_sub_left, F.β_sub_right, F.β_sub_right, e2, e1]
    linear_combination (F.β u u' - F.β (ρ s u) u') * h2
  have hcs : ∀ c ∈ Subgroup.centralizer ({s} : Set H), ∀ u, ρ c (ρ s u) = ρ s (ρ c u) := by
    intro c hc u
    have := Subgroup.mem_centralizer_iff.mp hc s rfl
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, this]
  have hWinv : ∀ c ∈ Subgroup.centralizer ({s} : Set H), ∀ w ∈ W, ρ c w ∈ W := by
    intro c hc w hw
    obtain ⟨u, rfl⟩ := (hWmem w).mp hw
    exact (hWmem _).mpr ⟨ρ c u, by rw [map_sub, hcs c hc]⟩
  have hperp : ∀ b ∈ F.perp W, ρ s b = b := by
    intro b hb
    have h0 : ρ s b - b = 0 := by
      apply F.nondeg
      intro w
      have hw : ρ s w - w ∈ W := (hWmem _).mpr ⟨w, rfl⟩
      have e1 : F.β (ρ s b) w = F.β b (ρ s w) := by
        calc F.β (ρ s b) w = F.β (ρ s b) (ρ s (ρ s w)) := by rw [hss]
          _ = F.β b (ρ s w) := hρ s b (ρ s w)
      have e2 : F.β b (ρ s w - w) = 0 := F.refl _ _ (hb _ hw)
      rw [F.β_sub_left, e1, ← sub_eq_zero.mp (by rw [← F.β_sub_right]; exact e2 :
        F.β b (ρ s w) - F.β b w = 0)]
      exact sub_self _
    exact sub_eq_zero.mp h0
  have hTrC : ∀ b, ρ s b = b → ∀ h, IsTrans F ρ h b → h ∈ Subgroup.centralizer ({s} : Set H) := by
    intro b hb h ht
    have h1 := conj_isTrans hρ ht s
    rw [hb] at h1
    have h3 := isTrans_unique hinj h1 ht
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    calc g * h = g * h * g⁻¹ * g := by group
      _ = h * g := by rw [h3]
  have hfixW : ∀ x ∈ N, ∀ b ∈ W, ρ x b = b := by
    intro x hx b hb
    obtain ⟨t, ht⟩ := htrans b
    have htC := hTrC b (hsW b hb) t ht
    exact fixes_of_isotropic halt hK hρ hinj N hodd ht (fun y hy => hNn t htC y hy) hx
      (hWiso b hb _ (hWinv x (hNC hx) b hb))
  have hWV1 : W ≤ fixedV ρ N := fun w hw x hx => hfixW x hx w hw
  have hinf : fixedV ρ N ⊓ commV ρ N = ⊥ := by
    have : Finite N := inferInstance
    exact fixedV_inf_commV hK N hodd
  have hV2inv : ∀ c ∈ Subgroup.centralizer ({s} : Set H), ∀ v ∈ commV ρ N,
      ρ c v ∈ commV ρ N := fun c hc v hv => map_mem_commV (fun x hx => hNn c hc x hx) hv
  have hV2 : commV ρ N = ⊥ := by
    by_contra hne
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hex : ∃ b ∈ F.perp W, F.β b v = 1 := by
      by_contra hcon
      simp only [not_exists, not_and] at hcon
      have hvW : v ∈ W := by
        rw [← F.perp_perp W]
        intro b hb
        exact (hK _).resolve_right (hcon b hb)
      have : v ∈ fixedV ρ N ⊓ commV ρ N := ⟨hWV1 hvW, hv⟩
      rw [hinf] at this
      exact hv0 ((Submodule.mem_bot K).mp this)
    obtain ⟨b0, hb0, hb0v⟩ := hex
    have hone : ∀ b ∈ F.perp W, F.β b v = 1 → b ∈ commV ρ N := by
      intro b hb hbv
      obtain ⟨t, ht⟩ := htrans b
      have htC := hTrC b (hperp b hb) t ht
      have h1 := hV2inv t htC v hv
      rw [ht v, hbv, one_smul] at h1
      have := Submodule.sub_mem _ h1 hv
      rwa [add_sub_cancel_left] at this
    have hb0V2 : b0 ∈ commV ρ N := hone b0 hb0 hb0v
    have hU : ∀ c ∈ F.perp W, c ∈ commV ρ N := by
      intro c hc
      rcases hK (F.β c v) with h | h
      · have hcb : c + b0 ∈ F.perp W := Submodule.add_mem _ hc hb0
        have : F.β (c + b0) v = 1 := by rw [F.add_left, h, hb0v, zero_add]
        have h1 := hone _ hcb this
        have := Submodule.sub_mem _ h1 hb0V2
        rwa [add_sub_cancel_right] at this
      · exact hone c hc h
    have hWU : W ≤ F.perp W := fun w hw w' hw' => hWiso w' hw' w hw
    have hWbot : W = ⊥ := by
      rw [eq_bot_iff, ← hinf]
      exact le_inf hWV1 (fun w hw => hU w (hWU hw))
    apply hs1
    apply hinj
    ext1 u
    have : ρ s u - u ∈ W := (hWmem _).mpr ⟨u, rfl⟩
    rw [hWbot, Submodule.mem_bot, sub_eq_zero] at this
    rw [map_one, Module.End.one_apply, this]
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  apply hinj
  ext1 u
  have := sub_mem_commV (ρ := ρ) hx u
  rw [hV2, Submodule.mem_bot, sub_eq_zero] at this
  rw [map_one, Module.End.one_apply, this]

end Core

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinModel


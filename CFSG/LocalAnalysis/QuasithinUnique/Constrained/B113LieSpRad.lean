module

public import CFSG.LieType.BorelTits.OrthogonalSingular

public section

namespace CFSG.QuasithinUnique.B113Lie.Sp

open CFSG.LieType.BorelTits

universe u v w

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V] {H : Type w} [Group H]
variable {F : ReflForm K V} {ρ : H →* Module.End K V}

variable (F ρ) in
@[expose] def rad (W : Submodule K V) (hW : F.IsTotallyIsotropic W) : Subgroup H where
  carrier := {g | (∀ w ∈ W, ρ g w = w) ∧ ∀ v ∈ F.perp W, ρ g v - v ∈ W}
  one_mem' := ⟨fun w _ => by simp, fun v _ => by simp⟩
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨fun w hw => ?_, fun v hv => ?_⟩
    · rw [map_mul, Module.End.mul_apply, hh1 w hw, hg1 w hw]
    · have hhv : ρ h v ∈ F.perp W := by
        have h' : ρ h v = (ρ h v - v) + v := by abel
        rw [h']
        exact add_mem (hW (hh2 v hv)) hv
      have : ρ (g * h) v - v = (ρ g (ρ h v) - ρ h v) + (ρ h v - v) := by
        rw [map_mul, Module.End.mul_apply]
        abel
      rw [this]
      exact add_mem (hg2 _ hhv) (hh2 v hv)
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    have hinv : ∀ w ∈ W, ρ g⁻¹ w = w := fun w hw => by
      have h1 : ρ g⁻¹ (ρ g w) = ρ g⁻¹ w := by rw [hg1 w hw]
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h1
      exact h1.symm
    refine ⟨hinv, fun v hv => ?_⟩
    have h1 := hinv _ (hg2 v hv)
    rw [map_sub, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at h1
    have h2 : ρ g⁻¹ v - v = -(ρ g v - v) := by
      rw [← h1]
      abel
    rw [h2]
    exact neg_mem (hg2 v hv)

theorem mem_rad {W : Submodule K V} {hW : F.IsTotallyIsotropic W} {g : H} :
    g ∈ rad F ρ W hW ↔ (∀ w ∈ W, ρ g w = w) ∧ ∀ v ∈ F.perp W, ρ g v - v ∈ W :=
  Iff.rfl

theorem rad_conj_mem (hρ : IsIsometric F ρ) {W : Submodule K V} {hW : F.IsTotallyIsotropic W}
    {q : H} (hq : ∀ w ∈ W, ρ q w ∈ W) (hq' : ∀ w ∈ W, ρ q⁻¹ w ∈ W) {g : H}
    (hg : g ∈ rad F ρ W hW) : q * g * q⁻¹ ∈ rad F ρ W hW := by
  obtain ⟨hg1, hg2⟩ := hg
  refine ⟨fun w hw => ?_, fun v hv => ?_⟩
  · rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hg1 _ (hq' w hw),
      rep_apply_inv_apply]
  · have hv' : ρ q⁻¹ v ∈ F.perp W :=
      hρ.apply_mem_perp_of_forall (fun w hw => by simpa using hq w hw) hv
    have : ρ (q * g * q⁻¹) v - v = ρ q (ρ g (ρ q⁻¹ v) - ρ q⁻¹ v) := by
      rw [map_sub, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
        rep_apply_inv_apply]
    rw [this]
    exact hq _ (hg2 _ hv')

theorem rad_isPGroup (hρ : IsIsometric F ρ) (hinj : Function.Injective ρ) (p : ℕ) [Fact p.Prime]
    [CharP K p] {W : Submodule K V} (hW : F.IsTotallyIsotropic W) :
    IsPGroup p (rad F ρ W hW) := by
  set X : ℕ → Submodule K V := fun k => if k = 0 then ⊥ else W with hX
  have hX0 : X 0 = ⊥ := by simp [hX]
  have hX1 : X 1 = W := by simp [hX]
  have hle : rad F ρ W hW ≤ flagKernel ρ (isoCompletion F X 1) := by
    refine le_flagKernel_isoCompletion ρ hρ hX0 ?_ ?_ ?_
    · refine le_flagStab_isoCompletion ρ hρ 1 ?_
      intro h hh k v hv
      by_cases hk : k = 0
      · have : v = 0 := by simpa [hX, hk] using hv
        rw [this, map_zero]
        exact Submodule.zero_mem _
      · have hv' : v ∈ W := by simpa [hX, hk] using hv
        have : X k = W := by simp [hX, hk]
        rw [this, hh.1 v hv']
        exact hv'
    · intro k hk g hg v hv
      have hk0 : k = 0 := by omega
      subst hk0
      rw [hX1] at hv
      rw [hg.1 v hv, sub_self, hX0]
      exact Submodule.zero_mem _
    · intro g hg v hv
      rw [hX1] at hv ⊢
      exact hg.2 v hv
  exact (isPGroup_flagKernel ρ p hinj (isoCompletion_zero hX0 1) (isoCompletion_top hX0 1)).to_le
    hle

theorem transvection_mem_rad {W : Submodule K V} {hW : F.IsTotallyIsotropic W} {x : V}
    (hx : x ∈ W) {t : H} (ht : ∀ v, ρ t v = v + F.β x v • x) : t ∈ rad F ρ W hW := by
  refine ⟨fun w hw => ?_, fun v hv => ?_⟩
  · rw [ht, F.refl _ _ (hW hx w hw), zero_smul, add_zero]
  · rw [ht, add_sub_cancel_left, hv x hx, zero_smul]
    exact Submodule.zero_mem _

theorem siegel_mem_rad {W : Submodule K V} {hW : F.IsTotallyIsotropic W} {x y : V} (hx : x ∈ W)
    (hy : y ∈ F.perp W) {s : H} (hs : ∀ v, ρ s v = v + F.β x v • y + F.β y v • x) :
    s ∈ rad F ρ W hW := by
  refine ⟨fun w hw => ?_, fun v hv => ?_⟩
  · rw [hs, F.refl _ _ (hW hx w hw), F.refl _ _ (hy w hw), zero_smul, zero_smul, add_zero,
      add_zero]
  · rw [hs, add_assoc, add_sub_cancel_left, hv x hx, zero_smul, zero_add]
    exact Submodule.smul_mem _ _ hx

theorem rep_conj_apply (hρ : IsIsometric F ρ) {h : H} {x a y b : V}
    (hh : ∀ v, ρ h v = v + F.β x v • a + F.β y v • b) (g : H) (v : V) :
    ρ (g * h * g⁻¹) v = v + F.β (ρ g x) v • ρ g a + F.β (ρ g y) v • ρ g b := by
  have hβ : ∀ z, F.β z (ρ g⁻¹ v) = F.β (ρ g z) v := fun z => by
    rw [← hρ g z (ρ g⁻¹ v), rep_apply_inv_apply]
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hh, map_add, map_add,
    map_smul, map_smul, rep_apply_inv_apply, hβ, hβ]

theorem eq_of_commute {h g : H} (hgh : g * h = h * g) : g * h * g⁻¹ = h := by
  rw [hgh, mul_inv_cancel_right]

theorem exists_β_eq_one {u : V} (hu : u ≠ 0) : ∃ v, F.β u v = 1 := by
  by_contra! h
  refine hu (F.nondeg u fun v => ?_)
  by_contra hv
  exact h ((F.β u v)⁻¹ • v) (by rw [F.smul_right, inv_mul_cancel₀ hv])

theorem eq_one_of_mul_self_eq_one [CharP K 2] {l : K} (h : l * l = 1) : l = 1 := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have : (l - 1) * (l - 1) = 0 := by linear_combination h + (1 - l) * h2
  exact sub_eq_zero.mp (mul_self_eq_zero.mp this)

theorem fix_of_commute_transvection [CharP K 2] (hσ : F.σ = RingEquiv.refl K)
    (hρ : IsIsometric F ρ) {u : V} (hu : u ≠ 0) {t g : H}
    (ht : ∀ v, ρ t v = v + F.β u v • u) (hgt : g * t = t * g) : ρ g u = u := by
  have key : ∀ v, F.β (ρ g u) v • ρ g u = F.β u v • u := by
    intro v
    have h1 := rep_conj_apply hρ (x := u) (a := u) (y := u) (b := 0)
      (fun v => by rw [ht, smul_zero, add_zero]) g v
    rw [eq_of_commute hgt, ht, map_zero, smul_zero, add_zero] at h1
    exact (add_left_cancel h1).symm
  have hu' : ρ g u ≠ 0 := fun h0 => hu (by
    have := congrArg (ρ g⁻¹) h0
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
      map_zero] at this)
  have hsm : ∀ (c : K) (a b : V), F.β (c • a) b = c * F.β a b := fun c a b => by
    rw [F.smul_left, hσ]
    rfl
  obtain ⟨v₀, hv₀⟩ := exists_β_eq_one (F := F) hu
  obtain ⟨v₁, hv₁⟩ := exists_β_eq_one (F := F) hu'
  have hl : u = F.β (ρ g u) v₀ • ρ g u := by
    have := key v₀
    rw [hv₀, one_smul] at this
    exact this.symm
  set l := F.β (ρ g u) v₀ with hldef
  have h2 := key v₁
  rw [hv₁, one_smul] at h2
  have h3 : ρ g u = (l * l) • ρ g u := by
    conv_lhs => rw [h2, hl]
    rw [hsm, hv₁, mul_one, smul_smul]
  have h4 : (l * l - 1) • ρ g u = 0 := by rw [sub_smul, ← h3, one_smul, sub_self]
  have h5 : l * l = 1 := by
    rcases smul_eq_zero.mp h4 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hu'
  rw [eq_one_of_mul_self_eq_one h5, one_smul] at hl
  exact hl.symm

theorem sub_mem_span_of_commute_siegel (hρ : IsIsometric F ρ) {e u : V} (he : e ≠ 0) {g s : H}
    (hge : ρ g e = e) (hs : ∀ v, ρ s v = v + F.β e v • u + F.β u v • e) (hgs : g * s = s * g) :
    ρ g u - u ∈ K ∙ e := by
  obtain ⟨v₀, hv₀⟩ := exists_β_eq_one (F := F) he
  have h1 := rep_conj_apply hρ hs g v₀
  rw [eq_of_commute hgs, hs, hge, hv₀, one_smul, one_smul] at h1
  rw [Submodule.mem_span_singleton]
  refine ⟨F.β u v₀ - F.β (ρ g u) v₀, ?_⟩
  have h2 : u + F.β u v₀ • e = ρ g u + F.β (ρ g u) v₀ • e := by
    rw [add_assoc, add_assoc] at h1
    exact add_left_cancel h1
  rw [sub_smul, sub_eq_sub_iff_add_eq_add, add_comm (F.β u v₀ • e) u]
  exact h2

theorem isTotallyIsotropic_span_singleton (halt : ∀ v, F.β v v = 0) (e : V) :
    F.IsTotallyIsotropic (K ∙ e) := by
  intro v hv w hw
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [F.smul_left, F.smul_right, halt, mul_zero, mul_zero]

theorem mem_rad_of_commute_point [CharP K 2] (hσ : F.σ = RingEquiv.refl K)
    (hρ : IsIsometric F ρ) (htrans : ∀ x : V, ∃ h : H, ∀ v, ρ h v = v + F.β x v • x)
    (hsiegel : ∀ x y : V, F.β x y = 0 →
      ∃ h : H, ∀ v, ρ h v = v + F.β x v • y + F.β y v • x)
    {e : V} (he : e ≠ 0) (hW : F.IsTotallyIsotropic (K ∙ e)) {g : H}
    (hg : ∀ q ∈ rad F ρ (K ∙ e) hW, g * q = q * g) : g ∈ rad F ρ (K ∙ e) hW := by
  obtain ⟨t, ht⟩ := htrans e
  have hge : ρ g e = e :=
    fix_of_commute_transvection hσ hρ he ht
      (hg t (transvection_mem_rad (Submodule.mem_span_singleton_self e) ht))
  refine ⟨fun w hw => ?_, fun v hv => ?_⟩
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_smul, hge]
  · have hev : F.β e v = 0 := hv e (Submodule.mem_span_singleton_self e)
    obtain ⟨s, hs⟩ := hsiegel e v hev
    exact sub_mem_span_of_commute_siegel hρ he hge hs
      (hg s (siegel_mem_rad (Submodule.mem_span_singleton_self e) hv hs))

theorem mem_rad_of_commute_lagrangian [CharP K 2] (hσ : F.σ = RingEquiv.refl K)
    (hρ : IsIsometric F ρ) (htrans : ∀ x : V, ∃ h : H, ∀ v, ρ h v = v + F.β x v • x)
    {W : Submodule K V} (hW : F.perp W = W) {g : H}
    (hg : ∀ q ∈ rad F ρ W hW.ge, g * q = q * g) : g ∈ rad F ρ W hW.ge := by
  have hfix : ∀ u ∈ W, ρ g u = u := by
    intro u hu
    by_cases hu0 : u = 0
    · rw [hu0, map_zero]
    · obtain ⟨t, ht⟩ := htrans u
      exact fix_of_commute_transvection hσ hρ hu0 ht (hg t (transvection_mem_rad hu ht))
  refine ⟨hfix, fun v hv => ?_⟩
  rw [hW] at hv
  rw [hfix v hv, sub_self]
  exact Submodule.zero_mem _

end CFSG.QuasithinUnique.B113Lie.Sp

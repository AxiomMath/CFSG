module

public import CFSG.LieType.BorelTits.FormFlag

public section

namespace CFSG.LieType.BorelTits

universe u v w

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
variable {H : Type w} [Group H] (F : ReflForm K V) (ρ : H →* Module.End K V)

@[expose] noncomputable def isoCompletion (X : ℕ → Submodule K V) (m k : ℕ) : Submodule K V :=
  if k ≤ m then X k else if k ≤ 2 * m + 1 then F.perp (X (2 * m + 1 - k)) else ⊤

variable {F}

theorem isoCompletion_of_le {X : ℕ → Submodule K V} {m k : ℕ} (hk : k ≤ m) :
    isoCompletion F X m k = X k := by
  simp [isoCompletion, hk]

theorem isoCompletion_zero {X : ℕ → Submodule K V} (hX0 : X 0 = ⊥) (m : ℕ) :
    isoCompletion F X m 0 = ⊥ := by
  rw [isoCompletion_of_le (Nat.zero_le m), hX0]

theorem isoCompletion_perp {X : ℕ → Submodule K V} {m k : ℕ} (hk : k ≤ m) :
    isoCompletion F X m (2 * m + 1 - k) = F.perp (X k) := by
  unfold isoCompletion
  split_ifs with h1 h2
  · omega
  · congr 2
    omega
  · omega

theorem isoCompletion_top {X : ℕ → Submodule K V} (hX0 : X 0 = ⊥) (m : ℕ) :
    isoCompletion F X m (2 * m + 1) = ⊤ := by
  have := isoCompletion_perp (F := F) (X := X) (Nat.zero_le m)
  rw [Nat.sub_zero, hX0, F.perp_bot] at this
  exact this

theorem isoCompletion_of_lt {X : ℕ → Submodule K V} {m j : ℕ} (hj : 2 * m + 1 < j) :
    isoCompletion F X m j = ⊤ := by
  unfold isoCompletion
  split_ifs <;> first | omega | rfl

theorem isoCompletion_le_succ {X : ℕ → Submodule K V} (hXmono : Monotone X)
    (hXiso : ∀ k, F.IsTotallyIsotropic (X k)) (m j : ℕ) :
    isoCompletion F X m j ≤ isoCompletion F X m (j + 1) := by
  unfold isoCompletion
  split_ifs with h1 h2 h3 h4 h5 h6 <;> try omega
  · exact hXmono (Nat.le_succ j)
  · have : j = m := by omega
    subst this
    have h : 2 * j + 1 - (j + 1) = j := by omega
    rw [h]
    exact hXiso j
  · exact F.perp_antitone (hXmono (by omega))
  · exact le_top
  · exact le_top

theorem mem_flagKernel_isoCompletion [FiniteDimensional K V] {X : ℕ → Submodule K V}
    (hXmono : Monotone X) (hXiso : ∀ k, F.IsTotallyIsotropic (X k)) {m k : ℕ} (hk : k < m)
    {x y a : V} (hx : x ∈ X (k + 1)) (hy : y ∈ F.perp (X (k + 1)))
    (ha : a ∈ F.perp (X (k + 1))) (c : K) {g : H}
    (hg : ∀ v, ρ g v = v + F.β x v • a + (c * F.β y v) • x) :
    g ∈ flagKernel ρ (isoCompletion F X m) := by
  have hxm : x ∈ X m := hXmono (by omega) hx
  have hxperp : ∀ i ≤ m, x ∈ F.perp (X i) := fun i hi =>
    F.perp_antitone (hXmono hi) (hXiso m hxm)
  have hβxu : ∀ i, k + 1 ≤ i → ∀ u ∈ F.perp (X i), F.β x u = 0 := fun i hi u hu =>
    hu x (hXmono hi hx)
  have hβyu : ∀ u ∈ X (k + 1), F.β y u = 0 := fun u hu => F.refl _ _ (hy u hu)
  have hdiff : ∀ v, ρ g v - v = F.β x v • a + (c * F.β y v) • x := fun v => by
    rw [hg]
    abel
  have hlow : ∀ j, ∀ v ∈ isoCompletion F X m (j + 1), ρ g v - v ∈ isoCompletion F X m j := by
    intro j v hv
    rw [hdiff]
    rcases Nat.lt_or_ge j m with hjm | hjm
    ·
      rw [isoCompletion_of_le (by omega)] at hv
      rw [isoCompletion_of_le hjm.le]
      have hxv : F.β x v = 0 := hXiso m (hXmono (by omega) hv) x hxm
      rw [hxv, zero_smul, zero_add]
      rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
      · rw [hβyu v (hXmono (by omega) hv), mul_zero, zero_smul]
        exact Submodule.zero_mem _
      · exact Submodule.smul_mem _ _ (hXmono hjk hx)
    rcases Nat.lt_or_ge j (2 * m + 1) with hj2 | hj2
    · rcases Nat.eq_or_lt_of_le hjm with hjm' | hjm'
      ·
        have hjeq : j = m := hjm'.symm
        rw [hjeq] at hv ⊢
        have h1 : isoCompletion F X m (m + 1) = F.perp (X m) := by
          have := isoCompletion_perp (F := F) (X := X) (m := m) (le_refl m)
          rwa [show 2 * m + 1 - m = m + 1 by omega] at this
        rw [h1] at hv
        rw [isoCompletion_of_le le_rfl]
        rw [hv x hxm, zero_smul, zero_add]
        exact Submodule.smul_mem _ _ hxm
      ·
        set i := 2 * m - j with hi
        have h1 : isoCompletion F X m (j + 1) = F.perp (X i) := by
          have := isoCompletion_perp (F := F) (X := X) (m := m) (k := i) (by omega)
          rwa [show 2 * m + 1 - i = j + 1 by omega] at this
        have h2 : isoCompletion F X m j = F.perp (X (i + 1)) := by
          have := isoCompletion_perp (F := F) (X := X) (m := m) (k := i + 1) (by omega)
          rwa [show 2 * m + 1 - (i + 1) = j by omega] at this
        rw [h1] at hv
        rw [h2]
        have hxi : x ∈ F.perp (X (i + 1)) := hxperp (i + 1) (by omega)
        rcases Nat.lt_or_ge i (k + 1) with hik | hik
        · have hai : a ∈ F.perp (X (i + 1)) := F.perp_antitone (hXmono (by omega)) ha
          exact add_mem (Submodule.smul_mem _ _ hai) (Submodule.smul_mem _ _ hxi)
        · rw [hβxu i hik v hv, zero_smul, zero_add]
          exact Submodule.smul_mem _ _ hxi
    · rcases Nat.eq_or_lt_of_le hj2 with hj2' | hj2'
      ·
        subst hj2'
        have h2 : isoCompletion F X m (2 * m + 1) = F.perp (X 0) := by
          have := isoCompletion_perp (F := F) (X := X) (m := m) (k := 0) (Nat.zero_le m)
          rwa [Nat.sub_zero] at this
        rw [h2]
        have hx0 : x ∈ F.perp (X 0) := hxperp 0 (Nat.zero_le m)
        have ha0 : a ∈ F.perp (X 0) := F.perp_antitone (hXmono (Nat.zero_le _)) ha
        exact add_mem (Submodule.smul_mem _ _ ha0) (Submodule.smul_mem _ _ hx0)
      · rw [isoCompletion_of_lt hj2']
        exact Submodule.mem_top
  have hY : Monotone (isoCompletion F X m) :=
    monotone_nat_of_le_succ (isoCompletion_le_succ hXmono hXiso m)
  have hstab : ∀ j, ∀ v ∈ isoCompletion F X m j, ρ g v ∈ isoCompletion F X m j := by
    intro j v hv
    rcases j with _ | j
    · rw [isoCompletion_of_le (Nat.zero_le m)] at hv ⊢
      have hv' : v ∈ X (k + 1) := hXmono (Nat.zero_le _) hv
      rw [hg, hXiso m (hXmono (Nat.zero_le _) hv) x hxm, hβyu v hv', zero_smul, mul_zero,
        zero_smul, add_zero, add_zero]
      exact hv
    · have := hlow j v hv
      have h := add_mem hv (hY (Nat.le_succ j) this)
      simpa using h
  refine ⟨fun j v hv => ⟨hstab j v hv, ?_⟩, hlow⟩
  let f : isoCompletion F X m j →ₗ[K] isoCompletion F X m j :=
    (ρ g).restrict fun w hw => hstab j w hw
  have hfinj : Function.Injective f := by
    intro w w' hww'
    have := congrArg (fun z : isoCompletion F X m j => ρ g⁻¹ (z : V)) hww'
    simp only [f, LinearMap.restrict_apply] at this
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
      ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this
    exact Subtype.ext this
  obtain ⟨w, hw⟩ := (LinearMap.injective_iff_surjective.mp hfinj) ⟨v, hv⟩
  have hw' : ρ g (w : V) = v := congrArg Subtype.val hw
  rw [← hw', ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  exact w.2

end CFSG.LieType.BorelTits

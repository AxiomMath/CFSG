module

public import CFSG.HardMathSupport.Timmesfeld.RootAut.Linear

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.RootAut

section Orbits

variable {τ : Tag}
  {Ψ : Set (Fin τ.rank → ℤ)} {f : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ}

theorem outerRoots_isIsometry_iterate (hf : IsIsometry Ψ f) : ∀ n : ℕ, IsIsometry Ψ (f^[n])
  | 0 => ⟨Set.bijOn_id Ψ, fun _ _ _ _ => rfl, fun _ _ => rfl⟩
  | n + 1 => by
    have ih := outerRoots_isIsometry_iterate hf n
    refine ⟨?_, fun γ hγ δ hδ => ?_, fun γ hγ => ?_⟩
    · rw [Function.iterate_succ]
      exact ih.bijOn.comp hf.bijOn
    · rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        ih.iform_eq _ (hf.bijOn.mapsTo hγ) _ (hf.bijOn.mapsTo hδ), hf.iform_eq γ hγ δ hδ]
    · rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hf.neg γ hγ,
        ih.neg _ (hf.bijOn.mapsTo hγ)]

theorem outerRoots_iterate_mem (hf : IsIsometry Ψ f) (n : ℕ) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ Ψ) : f^[n] γ ∈ Ψ :=
  (outerRoots_isIsometry_iterate hf n).bijOn.mapsTo hγ

theorem outerRoots_iterate_mem_posRoots (hpos : ∀ γ ∈ posRoots Ψ, f γ ∈ posRoots Ψ) :
    ∀ (n : ℕ) (γ : Fin τ.rank → ℤ), γ ∈ posRoots Ψ → f^[n] γ ∈ posRoots Ψ
  | 0, _, hγ => hγ
  | n + 1, γ, hγ => by
    rw [Function.iterate_succ_apply]
    exact outerRoots_iterate_mem_posRoots hpos n _ (hpos γ hγ)

theorem outerRoots_iterate_mem_negRoots (hΨ : IsRootComponent Ψ) (hf : IsIsometry Ψ f)
    (hpos : ∀ γ ∈ posRoots Ψ, f γ ∈ posRoots Ψ) (n : ℕ) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ negRoots Ψ) : f^[n] γ ∈ negRoots Ψ :=
  (outerRoots_isIsometry_iterate hf n).mem_negRoots hΨ
    (outerRoots_iterate_mem_posRoots hpos n) hγ

theorem outerRoots_iterate_add (hf : IsIsometry Ψ f) (n : ℕ) {x y : Fin τ.rank → ℤ}
    (hx : x ∈ Ψ) (hy : y ∈ Ψ) (hxy : x + y ∈ Ψ) : f^[n] (x + y) = f^[n] x + f^[n] y :=
  (eq_add_iff_of_iform (outerRoots_isIsometry_iterate hf n).iform_eq hx hy hxy).2 rfl

theorem outerRoots_iterate_sub (hf : IsIsometry Ψ f) (n : ℕ) {x y : Fin τ.rank → ℤ}
    (hx : x ∈ Ψ) (hy : y ∈ Ψ) (hxy : x - y ∈ Ψ) : f^[n] (x - y) = f^[n] x - f^[n] y := by
  have h := (eq_add_iff_of_iform (outerRoots_isIsometry_iterate hf n).iform_eq hxy hy hx).2
    (sub_add_cancel x y).symm
  rw [h, add_sub_cancel_right]

theorem outerRoots_mem_periodicPts (hΨ : IsRootComponent Ψ) (hf : IsIsometry Ψ f)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ Ψ) : γ ∈ Function.periodicPts f := by
  have hfin : Ψ.Finite := (finite_setOf_isRoot τ).subset fun δ hδ => hΨ.isRoot δ hδ
  have : Finite Ψ := hfin.to_subtype
  set e : Equiv.Perm Ψ := hf.bijOn.equiv f with he
  have hcoe : ∀ (n : ℕ) (x : Ψ), (((e ^ n) x : Ψ) : Fin τ.rank → ℤ) = f^[n] (x : _) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ', Equiv.Perm.mul_apply, Function.iterate_succ_apply', ← ih x]
      rfl
  have hord : 0 < orderOf e := orderOf_pos e
  refine Function.mk_mem_periodicPts hord ?_
  have h1 : (e ^ orderOf e) ⟨γ, hγ⟩ = ⟨γ, hγ⟩ := by rw [pow_orderOf_eq_one]; rfl
  have h2 := congrArg Subtype.val h1
  rw [hcoe] at h2
  exact h2

theorem outerRoots_minimalPeriod_pos (hΨ : IsRootComponent Ψ) (hf : IsIsometry Ψ f)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ Ψ) : 0 < Function.minimalPeriod f γ :=
  Function.minimalPeriod_pos_of_mem_periodicPts (outerRoots_mem_periodicPts hΨ hf hγ)

theorem outerRoots_not_isRoot_sub (hΨ : IsRootComponent Ψ) (hf : IsIsometry Ψ f)
    (hpos : ∀ γ ∈ posRoots Ψ, f γ ∈ posRoots Ψ) {γ : Fin τ.rank → ℤ} (hγ : γ ∈ Ψ) (n : ℕ) :
    ¬ IsRoot τ (γ - f^[n] γ) := by
  intro hr
  set m := Function.minimalPeriod f γ with hmdef
  have hm : 0 < m := outerRoots_minimalPeriod_pos hΨ hf hγ
  have hfm : f^[m] γ = γ := Function.iterate_minimalPeriod
  have hnγ : f^[n] γ ∈ Ψ := outerRoots_iterate_mem hf n hγ
  have hδ : γ - f^[n] γ ∈ Ψ := by
    rw [sub_eq_add_neg] at hr ⊢
    exact hΨ.add_mem _ hγ _ (hΨ.neg_mem _ hnγ) hr
  have hu : ∀ l, f^[n * l] (γ - f^[n] γ) = f^[n * l] γ - f^[n * (l + 1)] γ := by
    intro l
    rw [outerRoots_iterate_sub hf (n * l) hγ hnγ hδ, ← Function.iterate_add_apply]
    rfl
  have hsum : ∑ l ∈ Finset.range m, f^[n * l] (γ - f^[n] γ) = 0 := by
    simp_rw [hu]
    rw [Finset.sum_range_sub' (fun l => f^[n * l] γ) m]
    simp only [mul_zero, Function.iterate_zero, id_eq]
    rw [mul_comm, Function.iterate_mul, Function.iterate_fixed hfm, sub_self]
  have hheight : ∑ l ∈ Finset.range m, height (f^[n * l] (γ - f^[n] γ)) = 0 := by
    rw [← height_finset_sum, hsum]
    simp [height]
  have hne : (Finset.range m).Nonempty := ⟨0, Finset.mem_range.2 hm⟩
  rcases mem_posRoots_or_mem_negRoots hΨ hδ with hp | hneg
  · have : 0 < ∑ l ∈ Finset.range m, height (f^[n * l] (γ - f^[n] γ)) :=
      Finset.sum_pos (fun l _ => (outerRoots_iterate_mem_posRoots hpos _ _ hp).2) hne
    omega
  · have : ∑ l ∈ Finset.range m, height (f^[n * l] (γ - f^[n] γ)) < 0 :=
      Finset.sum_neg (fun l _ => ((mem_negRoots_iff hΨ).1
        (outerRoots_iterate_mem_negRoots hΨ hf hpos _ hneg)).2) hne
    omega

theorem outerRoots_not_isRoot_add_of_iform_eq_zero (hΨ : IsRootComponent Ψ)
    (hf : IsIsometry Ψ f) (hpos : ∀ γ ∈ posRoots Ψ, f γ ∈ posRoots Ψ) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ Ψ) (n : ℕ) (h0 : iform γ (f^[n] γ) = 0) : ¬ IsRoot τ (γ + f^[n] γ) := by
  intro hr
  have hnγ : f^[n] γ ∈ Ψ := outerRoots_iterate_mem hf n hγ
  have hδr : IsRoot τ (f^[n] γ) := hΨ.isRoot _ hnγ
  have hpair : corootPair (f^[n] γ) (γ + f^[n] γ) = 2 := by
    have hpos' := iform_self_pos_of_isRoot hδr
    have h := corootPair_mul hδr (γ + f^[n] γ)
    rw [iform_add_right, iform_comm (f^[n] γ) γ, h0, zero_add] at h
    exact mul_right_cancel₀ hpos'.ne' (h.trans (by ring))
  have hrefl : rootReflection (f^[n] γ) • (γ + f^[n] γ) = γ - f^[n] γ := by
    rw [rootReflection_smul hδr, hpair]
    abel
  exact outerRoots_not_isRoot_sub hΨ hf hpos hγ n (hrefl ▸ IsRoot.smul hr _)

theorem outerRoots_two_mul_iform (hΨ : IsRootComponent Ψ) (hf : IsIsometry Ψ f)
    (hpos : ∀ γ ∈ posRoots Ψ, f γ ∈ posRoots Ψ) {γ : Fin τ.rank → ℤ} (hγ : γ ∈ Ψ) {n : ℕ}
    (hne : f^[n] γ ≠ γ) (hne' : f^[n] γ ≠ -γ) :
    2 * iform γ (f^[n] γ) = -iform γ γ ∨ iform γ (f^[n] γ) = 0 := by
  have hγr : IsRoot τ γ := hΨ.isRoot γ hγ
  have hnγ : f^[n] γ ∈ Ψ := outerRoots_iterate_mem hf n hγ
  have hδr : IsRoot τ (f^[n] γ) := hΨ.isRoot _ hnγ
  have hℓ : iform (f^[n] γ) (f^[n] γ) = iform γ γ :=
    (outerRoots_isIsometry_iterate hf n).iform_eq γ hγ γ hγ
  have hlt := iform_sq_lt hγr hδr (Ne.symm hne) (fun h => hne' (neg_eq_iff_eq_neg.mp h.symm))
  rw [hℓ] at hlt
  obtain ⟨t, ht⟩ := iform_dvd_of_isRoot hγr (f^[n] γ)
  have hpos0 : 0 < iform γ γ := iform_self_pos_of_isRoot hγr
  have ht2 : t ^ 2 < 4 := by
    have h1 : (2 * iform γ (f^[n] γ)) ^ 2 < 4 * (iform γ γ * iform γ γ) := by nlinarith
    rw [ht] at h1
    have h2 : (iform γ γ) ^ 2 * t ^ 2 < (iform γ γ) ^ 2 * 4 := by nlinarith
    exact lt_of_mul_lt_mul_left h2 (by positivity)
  have hcases : t = -1 ∨ t = 0 ∨ t = 1 := by
    have h1 : -2 < t := by nlinarith
    have h2 : t < 2 := by nlinarith
    omega
  rcases hcases with rfl | rfl | rfl
  · left
    rw [ht]
    ring
  · right
    have : 2 * iform γ (f^[n] γ) = 0 := by rw [ht]; ring
    omega
  · exfalso
    have hpos1 : 0 < iform γ (f^[n] γ) := by
      have : 2 * iform γ (f^[n] γ) = iform γ γ := by rw [ht]; ring
      omega
    exact outerRoots_not_isRoot_sub hΨ hf hpos hγ n
      (isRoot_sub_of_iform_pos hγr hδr (Ne.symm hne) hpos1)

theorem outerRoots_dichotomy (hΨ : IsRootComponent Ψ) (hf : IsIsometry Ψ f)
    (hpos : ∀ γ ∈ posRoots Ψ, f γ ∈ posRoots Ψ) {γ : Fin τ.rank → ℤ} (hγ : γ ∈ posRoots Ψ) :
    (∀ n, 0 < n → n < Function.minimalPeriod f γ → iform γ (f^[n] γ) = 0) ∨
    ∃ k, 0 < k ∧ Function.minimalPeriod f γ = 2 * k ∧ 2 * iform γ (f^[k] γ) = -iform γ γ ∧
      ∀ n, 0 < n → n < Function.minimalPeriod f γ → n ≠ k → iform γ (f^[n] γ) = 0 := by
  classical
  have hγΨ : γ ∈ Ψ := hγ.1
  set m := Function.minimalPeriod f γ with hmdef
  have hm : 0 < m := outerRoots_minimalPeriod_pos hΨ hf hγΨ
  have : NeZero m := ⟨hm.ne'⟩
  have hmod : ∀ n, f^[n % m] γ = f^[n] γ := fun n => Function.iterate_mod_minimalPeriod_eq
  have hℓ : 0 < iform γ γ := iform_self_pos_of_isRoot (hΨ.isRoot γ hγΨ)
  set c : ZMod m → ℤ := fun d => iform γ (f^[d.val] γ) with hc
  have hshift : ∀ a b : ZMod m, iform (f^[a.val] γ) (f^[b.val] γ) = c (b - a) := by
    intro a b
    have hidx : (a.val + (b - a).val) % m = b.val := by rw [← ZMod.val_add, add_sub_cancel]
    have e : f^[b.val] γ = f^[a.val] (f^[(b - a).val] γ) := by
      rw [← Function.iterate_add_apply, ← hmod (a.val + (b - a).val), hidx]
    rw [e, (outerRoots_isIsometry_iterate hf a.val).iform_eq γ hγΨ _
      (outerRoots_iterate_mem hf _ hγΨ)]
  have hS : ∀ a : ZMod m, iform (∑ d : ZMod m, f^[d.val] γ) (f^[a.val] γ) =
      ∑ d : ZMod m, c d := by
    intro a
    rw [iform_finset_sum_left]
    have h1 : ∀ d : ZMod m, iform (f^[d.val] γ) (f^[a.val] γ) = c (a - d) := fun d => hshift d a
    simp_rw [h1]
    exact Fintype.sum_equiv (Equiv.subLeft a) _ _ (fun d => rfl)
  have hSS : iform (∑ d : ZMod m, f^[d.val] γ) (∑ d : ZMod m, f^[d.val] γ) =
      (m : ℤ) * ∑ d : ZMod m, c d := by
    rw [iform_finset_sum_right]
    simp_rw [hS]
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have hSne : (∑ d : ZMod m, f^[d.val] γ) ≠ 0 := by
    intro h0
    have h1 := congrArg height h0
    rw [height_finset_sum] at h1
    have hp : 0 < ∑ d : ZMod m, height (f^[d.val] γ) :=
      Finset.sum_pos (fun d _ => (outerRoots_iterate_mem_posRoots hpos _ _ hγ).2)
        Finset.univ_nonempty
    have h0' : height (0 : Fin τ.rank → ℤ) = 0 := by simp [height]
    omega
  have hCpos : 0 < ∑ d : ZMod m, c d := by
    have h1 := iform_self_pos hSne
    rw [hSS] at h1
    exact pos_of_mul_pos_right h1 (by positivity)
  have hc0 : c 0 = iform γ γ := by simp [hc]
  have hcval : ∀ d : ZMod m, d ≠ 0 → 2 * c d = -iform γ γ ∨ c d = 0 := by
    intro d hd
    have hne : f^[d.val] γ ≠ γ := by
      intro h
      have h0 : d.val = 0 := Function.iterate_injOn_Iio_minimalPeriod (ZMod.val_lt d) hm
        (h.trans (Function.iterate_zero_apply f γ).symm)
      exact hd ((ZMod.val_eq_zero d).1 h0)
    have hne' : f^[d.val] γ ≠ -γ := by
      intro h
      have h1 := outerRoots_iterate_mem_posRoots hpos d.val γ hγ
      rw [h] at h1
      exact not_mem_negRoots_of_mem_posRoots hγ h1
    exact outerRoots_two_mul_iform hΨ hf hpos hγΨ hne hne'
  have hsymm : ∀ d : ZMod m, c (-d) = c d := by
    intro d
    have h1 := hshift d 0
    have h2 := hshift 0 d
    simp only [ZMod.val_zero, Function.iterate_zero, id_eq, zero_sub, sub_zero] at h1 h2
    rw [← h1, ← h2, iform_comm]
  have huniq : ∀ d₁ d₂ : ZMod m, d₁ ≠ 0 → d₂ ≠ 0 → c d₁ ≠ 0 → c d₂ ≠ 0 → d₁ = d₂ := by
    intro d₁ d₂ h1 h2 hc1 hc2
    by_contra h12
    have e1 : 2 * c d₁ = -iform γ γ := (hcval d₁ h1).resolve_right hc1
    have e2 : 2 * c d₂ = -iform γ γ := (hcval d₂ h2).resolve_right hc2
    set T : Finset (ZMod m) := {0, d₁, d₂} with hT
    have hle : ∑ d : ZMod m, 2 * c d ≤ ∑ d ∈ T, 2 * c d := by
      rw [← Finset.sum_sdiff (Finset.subset_univ T)]
      have : ∑ d ∈ Finset.univ \ T, 2 * c d ≤ 0 := Finset.sum_nonpos fun d hd => by
        have hd0 : d ≠ 0 := by
          intro h
          rw [Finset.mem_sdiff] at hd
          exact hd.2 (by rw [hT, h]; simp)
        rcases hcval d hd0 with h | h
        · rw [h]
          exact neg_nonpos.2 hℓ.le
        · rw [h]
          norm_num
      linarith
    have hTs : ∑ d ∈ T, 2 * c d = 2 * c 0 + 2 * c d₁ + 2 * c d₂ := by
      rw [hT, Finset.sum_insert (by simp [Ne.symm h1, Ne.symm h2]),
        Finset.sum_insert (by simp [h12]), Finset.sum_singleton]
      ring
    have hpos2 : 0 < ∑ d : ZMod m, 2 * c d := by
      rw [← Finset.mul_sum]
      linarith
    rw [hTs, hc0, e1, e2] at hle
    linarith
  by_cases hall : ∀ d : ZMod m, d ≠ 0 → c d = 0
  · left
    intro n hn hnm
    have hn0 : (n : ZMod m) ≠ 0 := by
      intro h
      rw [ZMod.natCast_eq_zero_iff] at h
      exact Nat.not_dvd_of_pos_of_lt hn hnm h
    have h1 := hall (n : ZMod m) hn0
    simpa [hc, ZMod.val_natCast, Nat.mod_eq_of_lt hnm] using h1
  · right
    push Not at hall
    obtain ⟨d₀, hd₀, hcd₀⟩ := hall
    have hneg : -d₀ = d₀ :=
      huniq (-d₀) d₀ (neg_ne_zero.2 hd₀) hd₀ (by rw [hsymm]; exact hcd₀) hcd₀
    have hv0 : 0 < d₀.val := Nat.pos_of_ne_zero fun h => hd₀ ((ZMod.val_eq_zero d₀).1 h)
    have hvlt : d₀.val < m := ZMod.val_lt d₀
    have h2 : d₀.val + d₀.val = m := by
      have hdd : d₀ + d₀ = 0 := by
        calc d₀ + d₀ = d₀ + -d₀ := by rw [hneg]
          _ = 0 := add_neg_cancel d₀
      have hv := ZMod.val_add d₀ d₀
      rw [hdd, ZMod.val_zero] at hv
      obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero hv.symm
      have ht1 : t = 1 := by
        rcases t with _ | _ | t
        · omega
        · rfl
        · nlinarith
      rw [ht1, mul_one] at ht
      exact ht
    refine ⟨d₀.val, hv0, by omega, (hcval d₀ hd₀).resolve_right hcd₀, fun n hn hnm hnk => ?_⟩
    by_contra hcn
    have hn0 : (n : ZMod m) ≠ 0 := by
      intro h
      rw [ZMod.natCast_eq_zero_iff] at h
      exact Nat.not_dvd_of_pos_of_lt hn hnm h
    have hcn' : c (n : ZMod m) ≠ 0 := by
      simpa [hc, ZMod.val_natCast, Nat.mod_eq_of_lt hnm] using hcn
    have e := huniq (n : ZMod m) d₀ hn0 hd₀ hcn' hcd₀
    apply hnk
    rw [← e, ZMod.val_natCast, Nat.mod_eq_of_lt hnm]

structure OuterBlock (f : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ) (γ : Fin τ.rank → ℤ) (k : ℕ) :
    Prop where
  pos : 0 < k
  period : Function.minimalPeriod f γ = 2 * k
  pair : 2 * iform γ (f^[k] γ) = -iform γ γ
  orth : ∀ n, 0 < n → n < 2 * k → n ≠ k → iform γ (f^[n] γ) = 0

theorem outerRoots_iform_iterate (hf : IsIsometry Ψ f) {γ : Fin τ.rank → ℤ} (hγ : γ ∈ Ψ)
    {a b : ℕ} (hab : a ≤ b) : iform (f^[a] γ) (f^[b] γ) = iform γ (f^[b - a] γ) := by
  have e : f^[b] γ = f^[a] (f^[b - a] γ) := by
    rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hab]
  rw [e, (outerRoots_isIsometry_iterate hf a).iform_eq γ hγ _ (outerRoots_iterate_mem hf _ hγ)]

theorem outerRoots_block_mem (hΨ : IsRootComponent Ψ) (hpos : ∀ γ ∈ posRoots Ψ, f γ ∈ posRoots Ψ)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ posRoots Ψ) {k : ℕ} (hb : OuterBlock f γ k) :
    γ + f^[k] γ ∈ posRoots Ψ := by
  have hγΨ : γ ∈ Ψ := hγ.1
  have hkγ := outerRoots_iterate_mem_posRoots hpos k γ hγ
  have hℓ : 0 < iform γ γ := iform_self_pos_of_isRoot (hΨ.isRoot γ hγΨ)
  have hck := hb.pair
  have hr : IsRoot τ (γ + f^[k] γ) := isRoot_add_of_iform_neg (hΨ.isRoot γ hγΨ)
    (hΨ.isRoot _ hkγ.1) (fun h => by
      have h1 : γ ∈ negRoots Ψ := by
        show -γ ∈ posRoots Ψ
        rw [h, neg_neg]
        exact hkγ
      exact not_mem_negRoots_of_mem_posRoots hγ h1) (by omega)
  refine ⟨hΨ.add_mem _ hγΨ _ hkγ.1 hr, ?_⟩
  rw [height_add]
  have := hγ.2
  have := hkγ.2
  omega

theorem outerRoots_block_iterate (hΨ : IsRootComponent Ψ) (hf : IsIsometry Ψ f)
    (hpos : ∀ γ ∈ posRoots Ψ, f γ ∈ posRoots Ψ) {γ : Fin τ.rank → ℤ} (hγ : γ ∈ posRoots Ψ)
    {k : ℕ} (hb : OuterBlock f γ k) (j : ℕ) :
    f^[j] (γ + f^[k] γ) = f^[j] γ + f^[j + k] γ := by
  rw [outerRoots_iterate_add hf j hγ.1 (outerRoots_iterate_mem hf k hγ.1)
    (outerRoots_block_mem hΨ hpos hγ hb).1, Function.iterate_add_apply]

theorem outerRoots_block_fixed (hΨ : IsRootComponent Ψ) (hf : IsIsometry Ψ f)
    (hpos : ∀ γ ∈ posRoots Ψ, f γ ∈ posRoots Ψ) {γ : Fin τ.rank → ℤ} (hγ : γ ∈ posRoots Ψ)
    {k : ℕ} (hb : OuterBlock f γ k) : f^[k] (γ + f^[k] γ) = γ + f^[k] γ := by
  rw [outerRoots_block_iterate hΨ hf hpos hγ hb, ← two_mul, ← hb.period,
    Function.iterate_minimalPeriod, add_comm]

theorem outerRoots_block_iform_self (hf : IsIsometry Ψ f) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ Ψ) {k : ℕ} (hb : OuterBlock f γ k) :
    iform (γ + f^[k] γ) (γ + f^[k] γ) = iform γ γ := by
  have h1 : iform (f^[k] γ) (f^[k] γ) = iform γ γ :=
    (outerRoots_isIsometry_iterate hf k).iform_eq γ hγ γ hγ
  have hck := hb.pair
  rw [iform_add_left, iform_add_right, iform_add_right, h1, iform_comm (f^[k] γ) γ]
  linarith

theorem outerRoots_block_iform_iterate (hf : IsIsometry Ψ f) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ Ψ) {k : ℕ} (hb : OuterBlock f γ k) {j : ℕ} (hj : 0 < j) (hjk : j < k) :
    iform (γ + f^[k] γ) (f^[j] γ) = 0 := by
  have hper : f^[2 * k] γ = γ := by rw [← hb.period]; exact Function.iterate_minimalPeriod
  have e : f^[j] γ = f^[k] (f^[j + k] γ) := by
    rw [← Function.iterate_add_apply, show k + (j + k) = j + 2 * k by ring,
      Function.iterate_add_apply, hper]
  have h1 : iform (f^[k] γ) (f^[j] γ) = iform γ (f^[j + k] γ) := by
    rw [e, (outerRoots_isIsometry_iterate hf k).iform_eq γ hγ _ (outerRoots_iterate_mem hf _ hγ)]
  rw [iform_add_left, h1, hb.orth j hj (by omega) (by omega),
    hb.orth (j + k) (by omega) (by omega) (by omega)]
  ring

theorem outerRoots_block_orthogonal (hΨ : IsRootComponent Ψ) (hf : IsIsometry Ψ f)
    (hpos : ∀ γ ∈ posRoots Ψ, f γ ∈ posRoots Ψ) {γ : Fin τ.rank → ℤ} (hγ : γ ∈ posRoots Ψ)
    {k : ℕ} (hb : OuterBlock f γ k) {j : ℕ} (hj : 0 < j) (hjk : j < k) :
    iform (γ + f^[k] γ) (f^[j] (γ + f^[k] γ)) = 0 := by
  rw [outerRoots_block_iterate hΨ hf hpos hγ hb, iform_add_right,
    outerRoots_block_iform_iterate hf hγ.1 hb hj hjk, zero_add, iform_add_left]
  have h1 : iform (f^[k] γ) (f^[j + k] γ) = iform γ (f^[j] γ) := by
    rw [outerRoots_iform_iterate hf hγ.1 (by omega : k ≤ j + k), Nat.add_sub_cancel]
  rw [h1, hb.orth j hj (by omega) (by omega), hb.orth (j + k) (by omega) (by omega) (by omega)]
  ring

theorem outerRoots_block_reflection (hΨ : IsRootComponent Ψ) (hf : IsIsometry Ψ f)
    (hpos : ∀ γ ∈ posRoots Ψ, f γ ∈ posRoots Ψ) {γ : Fin τ.rank → ℤ} (hγ : γ ∈ posRoots Ψ)
    {k : ℕ} (hb : OuterBlock f γ k) : rootReflection (γ + f^[k] γ) • f^[k] γ = -γ := by
  have hσ := outerRoots_block_mem hΨ hpos hγ hb
  have hσr : IsRoot τ (γ + f^[k] γ) := hΨ.isRoot _ hσ.1
  have hσσ := outerRoots_block_iform_self hf hγ.1 hb
  have h1 : iform (f^[k] γ) (f^[k] γ) = iform γ γ :=
    (outerRoots_isIsometry_iterate hf k).iform_eq γ hγ.1 γ hγ.1
  have hℓ : 0 < iform γ γ := iform_self_pos_of_isRoot (hΨ.isRoot γ hγ.1)
  have hck := hb.pair
  have hpair : corootPair (γ + f^[k] γ) (f^[k] γ) = 1 := by
    have h := corootPair_mul hσr (f^[k] γ)
    rw [hσσ, iform_add_left, h1] at h
    have h2 : corootPair (γ + f^[k] γ) (f^[k] γ) * iform γ γ = 1 * iform γ γ := by
      rw [h]
      linarith
    exact mul_right_cancel₀ hℓ.ne' h2
  rw [rootReflection_smul hσr, hpair, one_smul]
  abel

theorem outerRoots_block_reflection_fix (hΨ : IsRootComponent Ψ) (hf : IsIsometry Ψ f)
    (hpos : ∀ γ ∈ posRoots Ψ, f γ ∈ posRoots Ψ) {γ : Fin τ.rank → ℤ} (hγ : γ ∈ posRoots Ψ)
    {k : ℕ} (hb : OuterBlock f γ k) {j : ℕ} (hj : 0 < j) (hjk : j < k) :
    rootReflection (γ + f^[k] γ) • f^[j] γ = f^[j] γ :=
  rootReflection_smul_of_iform_eq_zero (hΨ.isRoot _ (outerRoots_block_mem hΨ hpos hγ hb).1)
    (outerRoots_block_iform_iterate hf hγ.1 hb hj hjk)


theorem outerRoots_exists_orth (hΨ : IsRootComponent Ψ) (hf : IsIsometry Ψ f)
    (hpos : ∀ γ ∈ posRoots Ψ, f γ ∈ posRoots Ψ) {γ : Fin τ.rank → ℤ} (hγ : γ ∈ Ψ) :
    ∃ δ ∈ posRoots Ψ, ∃ m, 0 < m ∧ f^[m] δ = δ ∧ ∀ n, 0 < n → n < m → iform δ (f^[n] δ) = 0 := by
  have key : ∀ γ ∈ posRoots Ψ, ∃ δ ∈ posRoots Ψ, ∃ m, 0 < m ∧ f^[m] δ = δ ∧
      ∀ n, 0 < n → n < m → iform δ (f^[n] δ) = 0 := by
    intro γ hγ
    rcases outerRoots_dichotomy hΨ hf hpos hγ with horth | ⟨k, hk, hper, hpair, horth⟩
    · exact ⟨γ, hγ, _, outerRoots_minimalPeriod_pos hΨ hf hγ.1, Function.iterate_minimalPeriod,
        horth⟩
    · have hb : OuterBlock f γ k :=
        ⟨hk, hper, hpair, fun n hn hn2 hnk => horth n hn (by rw [hper]; exact hn2) hnk⟩
      exact ⟨_, outerRoots_block_mem hΨ hpos hγ hb, k, hk, outerRoots_block_fixed hΨ hf hpos hγ hb,
        fun n hn hnk => outerRoots_block_orthogonal hΨ hf hpos hγ hb hn hnk⟩
  rcases mem_posRoots_or_mem_negRoots hΨ hγ with h | h
  · exact key γ h
  · exact key (-γ) h

end Orbits

end CFSG.HardMathSupport.Timmesfeld.LangTorus

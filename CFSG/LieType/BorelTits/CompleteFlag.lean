module

public import CFSG.LieType.BorelTits.Flag

public section

namespace CFSG.LieType.BorelTits

universe u v w

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

structure IsCompleteFlag (C : ℕ → Submodule K V) : Prop where
  zero : C 0 = ⊥
  succ : ∀ i, ∃ u : V, C (i + 1) = C i ⊔ K ∙ u
  exists_eq_top : ∃ M, C M = ⊤

namespace IsCompleteFlag

variable {C : ℕ → Submodule K V}

theorem monotone (hC : IsCompleteFlag C) : Monotone C :=
  monotone_nat_of_le_succ fun i => by
    obtain ⟨u, hu⟩ := hC.succ i
    rw [hu]
    exact le_sup_left

theorem le_total (hC : IsCompleteFlag C) (i j : ℕ) : C i ≤ C j ∨ C j ≤ C i :=
  (Nat.le_total i j).imp (fun h => hC.monotone h) fun h => hC.monotone h

theorem succ_le_sup_span (hC : IsCompleteFlag C) {i : ℕ} {w : V} (hw : w ∈ C (i + 1))
    (hw' : w ∉ C i) : C (i + 1) ≤ C i ⊔ K ∙ w := by
  obtain ⟨u, hu⟩ := hC.succ i
  have hspan : ∀ y : V, Submodule.span K (insert y (C i : Set V)) = C i ⊔ K ∙ y := fun y => by
    rw [Submodule.span_insert, Submodule.span_eq, sup_comm]
  rw [hu] at hw ⊢
  refine sup_le le_sup_left ((Submodule.span_singleton_le_iff_mem _ _).mpr ?_)
  rw [← hspan] at hw ⊢
  exact mem_span_insert_exchange hw (by rwa [Submodule.span_eq])

end IsCompleteFlag

theorem exists_isCompleteFlag_forall_exists_eq [FiniteDimensional K V] {F : ℕ → Submodule K V}
    (hF : Monotone F) (htop : ∃ m, F m = ⊤) :
    ∃ C : ℕ → Submodule K V, IsCompleteFlag C ∧ ∀ k, ∃ i, F k = C i := by
  classical
  have hnext : ∀ W : Submodule K V, ∃ u : V,
      ∀ h : ∃ k, ¬F k ≤ W, u ∈ F (Nat.find h) ∧ u ∉ W := by
    intro W
    by_cases h : ∃ k, ¬F k ≤ W
    · obtain ⟨u, hu, hu'⟩ := IsConcreteLE.not_le_iff_exists.mp (Nat.find_spec h)
      exact ⟨u, fun _ => ⟨hu, hu'⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose next hnext using hnext
  let C : ℕ → Submodule K V := fun i => (fun W => W ⊔ K ∙ next W)^[i] ⊥
  have hCs : ∀ i, C (i + 1) = C i ⊔ K ∙ next (C i) := fun i =>
    Function.iterate_succ_apply' _ i ⊥
  have hmono : Monotone C := monotone_nat_of_le_succ fun i => (hCs i).symm ▸ le_sup_left
  have hstep : ∀ i k, ¬F k ≤ C i → C i ≤ F k → C (i + 1) ≤ F k := by
    intro i k hk hle
    rw [hCs]
    refine sup_le hle ((Submodule.span_singleton_le_iff_mem _ _).mpr ?_)
    exact hF (Nat.find_min' ⟨k, hk⟩ hk) (hnext (C i) ⟨k, hk⟩).1
  have hcomp : ∀ i k, F k ≤ C i ∨ C i ≤ F k := by
    intro i
    induction i with
    | zero => exact fun k => Or.inr bot_le
    | succ i ih =>
      intro k
      by_cases hk : F k ≤ C i
      · exact Or.inl (hk.trans (hmono (Nat.le_succ i)))
      · exact Or.inr (hstep i k hk ((ih k).resolve_left hk))
  obtain ⟨m, hm⟩ := htop
  have hCtop : ∃ M, C M = ⊤ := by
    obtain ⟨M, hM⟩ := monotone_stabilizes_iff_noetherian.mpr
      (inferInstance : IsNoetherian K V) ⟨C, hmono⟩
    refine ⟨M, ?_⟩
    by_contra hne
    have h : ∃ k, ¬F k ≤ C M := ⟨m, by rwa [hm, top_le_iff]⟩
    have hmem : next (C M) ∈ C (M + 1) := by
      rw [hCs]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    have hMM : C M = C (M + 1) := hM (M + 1) (Nat.le_succ M)
    exact (hnext (C M) h).2 (hMM ▸ hmem)
  refine ⟨C, ⟨rfl, fun i => ⟨next (C i), hCs i⟩, hCtop⟩, fun k => ?_⟩
  obtain ⟨M, hM⟩ := hCtop
  have hex : ∃ i, F k ≤ C i := ⟨M, hM ▸ le_top⟩
  obtain ⟨i, hi⟩ : ∃ i, Nat.find hex = i := ⟨_, rfl⟩
  have hle : F k ≤ C i := hi ▸ Nat.find_spec hex
  cases i with
  | zero => exact ⟨0, le_antisymm hle bot_le⟩
  | succ j =>
    have hnle : ¬F k ≤ C j := Nat.find_min hex (by omega)
    exact ⟨j + 1, le_antisymm hle (hstep j k hnle ((hcomp j k).resolve_left hnle))⟩

variable {H : Type w} [Group H] (ρ : H →* Module.End K V)

theorem flagStab_le_flagStab {F C : ℕ → Submodule K V} (h : ∀ k, ∃ i, F k = C i) :
    flagStab ρ C ≤ flagStab ρ F := by
  intro g hg k v hv
  obtain ⟨i, hi⟩ := h k
  rw [hi] at hv ⊢
  exact hg i v hv

theorem IsCompleteFlag.exists_sylow_normalizer_le_flagStab [Finite V] (p : ℕ) [Fact p.Prime]
    [CharP K p] (hρ : Function.Injective ρ) {C : ℕ → Submodule K V} (hC : IsCompleteFlag C)
    (huni : ∀ W : Submodule K V, (∀ h ∈ flagKernel ρ C, ∀ v ∈ W, ρ h v ∈ W) → ∃ i, W = C i) :
    ∃ S : Sylow p H, Subgroup.normalizer ((S : Subgroup H) : Set H) ≤ flagStab ρ C := by
  classical
  obtain ⟨M, hM⟩ := hC.exists_eq_top
  obtain ⟨S, hS⟩ := (isPGroup_flagKernel ρ p hρ hC.zero hM).exists_le_sylow
  refine ⟨S, ?_⟩
  have hinv : ∀ W : Submodule K V, (∀ g ∈ (S : Subgroup H), ∀ v ∈ W, ρ g v ∈ W) →
      ∃ i, W = C i :=
    fun W hW => huni W fun h hh => hW h (hS hh)
  have hCinv : ∀ i, ∀ g ∈ (S : Subgroup H), ∀ v ∈ C i, ρ g v ∈ C i := by
    intro i
    by_cases hCi : C i = ⊤
    · intro g _ v _
      rw [hCi]
      exact Submodule.mem_top
    obtain ⟨m, hm⟩ := exists_fixFlag_eq_top ρ p (S : Subgroup H) S.isPGroup'
    have hex : ∃ k, ¬fixFlag ρ (S : Subgroup H) k ≤ C i := ⟨m, by rwa [hm, top_le_iff]⟩
    obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k := ⟨_, rfl⟩
    have hnle : ¬fixFlag ρ (S : Subgroup H) k ≤ C i := hk ▸ Nat.find_spec hex
    cases k with
    | zero => exact absurd bot_le hnle
    | succ k =>
      have hle : fixFlag ρ (S : Subgroup H) k ≤ C i := not_not.mp (Nat.find_min hex (by omega))
      obtain ⟨j, hj⟩ := hinv (fixFlag ρ (S : Subgroup H) (k + 1)) fun g hg v hv =>
        flagStab_apply_mem ρ
          (normalizer_le_flagStab_fixFlag ρ _ (Subgroup.le_normalizer hg)) hv
      have hCij : C i ≤ fixFlag ρ (S : Subgroup H) (k + 1) := by
        rw [hj]
        exact (hC.le_total i j).resolve_right fun h => hnle (hj ▸ h)
      intro g hg v hv
      have := hle ((mem_fixFlag_succ ρ).mp (hCij hv) g hg)
      simpa using add_mem this hv
  have key : ∀ g ∈ Subgroup.normalizer ((S : Subgroup H) : Set H), ∀ i, ∀ v ∈ C i,
      ρ g v ∈ C i := by
    intro g hg i v hv
    have hinj : Function.Injective (ρ g) := by
      intro a b hab
      have := congrArg (ρ g⁻¹) hab
      rwa [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply, Module.End.one_apply] at this
    obtain ⟨j, hj⟩ := hinv ((C i).map (ρ g)) (by
      rintro s hs _ ⟨w, hw, rfl⟩
      have hs' : g⁻¹ * s * g ∈ (S : Subgroup H) := by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) s).mp hs
        simpa using this
      refine ⟨ρ (g⁻¹ * s * g) w, hCinv i _ hs' w hw, ?_⟩
      simp only [map_mul, Module.End.mul_apply]
      rw [← Module.End.mul_apply (ρ g) (ρ g⁻¹), ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply])
    have hrank : Module.finrank K (C j) = Module.finrank K (C i) := by
      rw [← hj]
      exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj (C i))).symm
    have hji : C j = C i := by
      rcases hC.le_total i j with h | h
      · exact (Submodule.eq_of_le_of_finrank_eq h hrank.symm).symm
      · exact Submodule.eq_of_le_of_finrank_eq h hrank
    rw [← hji, ← hj]
    exact Submodule.mem_map_of_mem hv
  intro g hg k v hv
  exact ⟨key g hg k v hv, key g⁻¹ (inv_mem hg) k v hv⟩

theorem exists_dual_eq_one_of_notMem {W : Submodule K V} {w : V} (hw : w ∉ W) :
    ∃ φ : Module.Dual K V, φ w = 1 ∧ ∀ v ∈ W, φ v = 0 := by
  obtain ⟨f, hf, hle⟩ := Submodule.exists_le_ker_of_notMem hw
  refine ⟨(f w)⁻¹ • f, by simp [hf], fun v hv => ?_⟩
  simp [LinearMap.mem_ker.mp (hle hv)]

@[expose] def ContainsTransvections : Prop :=
  ∀ (x : V) (φ : Module.Dual K V), φ x = 0 → ∃ h : H, ∀ v, ρ h v = v + φ v • x

theorem apply_inv_of_transvection {h : H} {x : V} {φ : Module.Dual K V} (hφ : φ x = 0)
    (hh : ∀ v, ρ h v = v + φ v • x) (v : V) : ρ h⁻¹ v = v - φ v • x := by
  have h1 : ρ h (v - φ v • x) = v := by
    rw [hh]
    simp [hφ]
  calc ρ h⁻¹ v = ρ h⁻¹ (ρ h (v - φ v • x)) := by rw [h1]
    _ = v - φ v • x := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem mem_flagKernel_of_transvection {C : ℕ → Submodule K V} (hC : Monotone C) {h : H} {x : V}
    {φ : Module.Dual K V} {j : ℕ} (hx : x ∈ C j) (hφ : ∀ v ∈ C j, φ v = 0)
    (hh : ∀ v, ρ h v = v + φ v • x) : h ∈ flagKernel ρ C := by
  have hmem : ∀ k, ∀ v ∈ C k, φ v • x ∈ C k := by
    intro k v hv
    rcases Nat.le_total k j with hkj | hjk
    · rw [hφ v (hC hkj hv), zero_smul]
      exact zero_mem _
    · exact Submodule.smul_mem _ _ (hC hjk hx)
  refine ⟨fun k v hv => ⟨?_, ?_⟩, fun k v hv => ?_⟩
  · rw [hh]
    exact add_mem hv (hmem k v hv)
  · rw [apply_inv_of_transvection ρ (hφ x hx) hh]
    exact sub_mem hv (hmem k v hv)
  · rw [hh, add_sub_cancel_left]
    rcases Nat.lt_or_ge k j with hkj | hjk
    · rw [hφ v (hC hkj hv), zero_smul]
      exact zero_mem _
    · exact Submodule.smul_mem _ _ (hC hjk hx)

namespace ContainsTransvections

variable {ρ}

theorem exists_apply_notMem (hρ : ContainsTransvections ρ) {W : Submodule K V} (h0 : W ≠ ⊥)
    (h1 : W ≠ ⊤) : ∃ h : H, ∃ w ∈ W, ρ h w ∉ W := by
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  obtain ⟨v, -, hv⟩ := IsConcreteLE.not_le_iff_exists.mp fun h => h1 (top_le_iff.mp h)
  obtain ⟨φ, hφw, -⟩ := exists_dual_eq_one_of_notMem (W := (⊥ : Submodule K V)) (by simpa using hw0)
  obtain ⟨h, hh⟩ := hρ (v - φ v • w) φ (by simp [hφw])
  refine ⟨h, w, hw, fun hmem => hv ?_⟩
  rw [hh, hφw, one_smul] at hmem
  have hx : v - φ v • w ∈ W := by simpa using sub_mem hmem hw
  simpa using add_mem hx (W.smul_mem (φ v) hw)

theorem flagStab_ne_top (hρ : ContainsTransvections ρ) {F : ℕ → Submodule K V} {k : ℕ}
    (h0 : F k ≠ ⊥) (h1 : F k ≠ ⊤) : flagStab ρ F ≠ ⊤ := by
  obtain ⟨h, w, hw, hhw⟩ := hρ.exists_apply_notMem h0 h1
  intro htop
  exact hhw (flagStab_apply_mem ρ (htop ▸ Subgroup.mem_top h) hw)

theorem exists_eq_of_flagKernel_invariant (hρ : ContainsTransvections ρ)
    {C : ℕ → Submodule K V} (hC : IsCompleteFlag C) {W : Submodule K V}
    (hW : ∀ h ∈ flagKernel ρ C, ∀ v ∈ W, ρ h v ∈ W) : ∃ i, W = C i := by
  classical
  obtain ⟨M, hM⟩ := hC.exists_eq_top
  have hex : ∃ i, W ≤ C i := ⟨M, hM ▸ le_top⟩
  obtain ⟨i, hi⟩ : ∃ i, Nat.find hex = i := ⟨_, rfl⟩
  have hle : W ≤ C i := hi ▸ Nat.find_spec hex
  cases i with
  | zero => exact ⟨0, le_antisymm hle (hC.zero ▸ bot_le)⟩
  | succ j =>
    have hnle : ¬W ≤ C j := Nat.find_min hex (by omega)
    obtain ⟨w, hwW, hwC⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
    obtain ⟨φ, hφw, hφ⟩ := exists_dual_eq_one_of_notMem hwC
    have hCW : C j ≤ W := by
      intro x hx
      obtain ⟨h, hh⟩ := hρ x φ (hφ x hx)
      have hmem := hW h (mem_flagKernel_of_transvection ρ hC.monotone hx hφ hh) w hwW
      rw [hh, hφw, one_smul] at hmem
      simpa using sub_mem hmem hwW
    refine ⟨j + 1, le_antisymm hle ?_⟩
    exact (hC.succ_le_sup_span (hle hwW) hwC).trans
      (sup_le hCW ((Submodule.span_singleton_le_iff_mem _ _).mpr hwW))

end ContainsTransvections

theorem holds_of_containsTransvections [Finite H] [Finite V] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hρinj : Function.Injective ρ) (hρ : ContainsTransvections ρ) : Holds H p := by
  refine holds_of_flags ρ p hρinj (fun R => fixFlag ρ R) (fun R _ _ => fixFlag_zero ρ R)
    (fun R _ hR => exists_fixFlag_eq_top ρ p R hR) (fun R _ _ => normalizer_le_flagStab_fixFlag ρ R)
    (fun R _ _ => le_flagKernel_fixFlag ρ R) ?_ ?_
  ·
    intro R hR hRp
    have hfix : ∀ v : V, v ∈ fixFlag ρ R 1 ↔ ∀ g ∈ R, ρ g v = v := fun v => by
      simp [mem_fixFlag_succ ρ (k := 0), sub_eq_zero]
    have h1 : fixFlag ρ R 1 ≠ ⊤ := by
      intro htop
      refine hR ((Subgroup.eq_bot_iff_forall R).mpr fun g hg => hρinj ?_)
      ext v
      rw [map_one, Module.End.one_apply]
      exact (hfix v).mp (htop ▸ Submodule.mem_top) g hg
    have : Nontrivial V := by
      by_contra hV
      rw [not_nontrivial_iff_subsingleton] at hV
      exact h1 (Subsingleton.elim _ _)
    refine hρ.flagStab_ne_top (k := 1) ?_ h1
    obtain ⟨v, hv0, hv⟩ := exists_fixed_ne_zero ρ p R hRp
    exact fun hbot => hv0 ((Submodule.mem_bot K).mp (hbot ▸ (hfix v).mpr hv))
  ·
    intro R _ hRp
    obtain ⟨C, hC, hFC⟩ :=
      exists_isCompleteFlag_forall_exists_eq (fixFlag_mono ρ R) (exists_fixFlag_eq_top ρ p R hRp)
    obtain ⟨S, hS⟩ := hC.exists_sylow_normalizer_le_flagStab ρ p hρinj fun W hW =>
      hρ.exists_eq_of_flagKernel_invariant hC hW
    exact ⟨S, hS.trans (flagStab_le_flagStab ρ hFC)⟩

end CFSG.LieType.BorelTits

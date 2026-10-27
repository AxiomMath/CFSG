module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S172A.GL (fixSp comSp ds ds_apply mem_fixSp mem_comSp
  eq_zero_of_mem_comSp_fixed inv_apply_of_fix cent_fix e_mem_comSp)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem frame_iSup_eq_top {E : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ}
    {x : Fin r → V ≃ₗ[ZMod 2] V} {P : Fin r → Submodule (ZMod 2) V} {V0 : Submodule (ZMod 2) V}
    (hF : LinTwoStdFrame E x P V0) : V0 ⊔ (⨆ j, P j) = ⊤ := by
  have h := hF.2.1.submodule_iSup_eq_top
  rwa [iSup_option_elim V0 P] at h

private theorem frame_ext {E : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ}
    {x : Fin r → V ≃ₗ[ZMod 2] V} {P : Fin r → Submodule (ZMod 2) V} {V0 : Submodule (ZMod 2) V}
    (hF : LinTwoStdFrame E x P V0) {f g : V ≃ₗ[ZMod 2] V}
    (h0 : ∀ v ∈ V0, f v = g v) (hP : ∀ j, ∀ v ∈ P j, f v = g v) : f = g := by
  apply LinearEquiv.ext
  intro v
  have hv : v ∈ ⨆ o : Option (Fin r), o.elim V0 P := by
    rw [hF.2.1.submodule_iSup_eq_top]
    trivial
  refine Submodule.iSup_induction (fun o : Option (Fin r) => o.elim V0 P)
    (motive := fun x => f x = g x) hv ?_ ?_ ?_
  · rintro (_ | j) w hw
    · exact h0 w hw
    · exact hP j w hw
  · simp
  · intro a b ha hb
    rw [map_add, map_add, ha, hb]

private theorem frame_x_mem_P {E : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ}
    {x : Fin r → V ≃ₗ[ZMod 2] V} {P : Fin r → Submodule (ZMod 2) V} {V0 : Submodule (ZMod 2) V}
    (hF : LinTwoStdFrame E x P V0) (j : Fin r) {v : V} (hv : v ∈ P j) :
    x j v ∈ P j := by
  have hc : comSp (x j) = P j := hF.2.2.2.2.1 j
  rw [← hc] at hv ⊢
  exact e_mem_comSp hv

private theorem frame_x_pow_mem_P {E : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ}
    {x : Fin r → V ≃ₗ[ZMod 2] V} {P : Fin r → Submodule (ZMod 2) V} {V0 : Submodule (ZMod 2) V}
    (hF : LinTwoStdFrame E x P V0) (j : Fin r) (k : ℕ) {v : V} (hv : v ∈ P j) :
    (x j ^ k) v ∈ P j := by
  induction k with
  | zero => simpa using hv
  | succ k ih =>
    rw [pow_succ', LinearEquiv.mul_apply]
    exact frame_x_mem_P hF j ih

private theorem frame_x_pow_fixed_V0 {E : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ}
    {x : Fin r → V ≃ₗ[ZMod 2] V} {P : Fin r → Submodule (ZMod 2) V} {V0 : Submodule (ZMod 2) V}
    (hF : LinTwoStdFrame E x P V0) (j : Fin r) (k : ℕ) {v : V} (hv : v ∈ V0) :
    (x j ^ k) v = v := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', LinearEquiv.mul_apply, ih, hF.2.2.2.2.2.1 j v hv]

private theorem frame_x_pow_fixed_P {E : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ}
    {x : Fin r → V ≃ₗ[ZMod 2] V} {P : Fin r → Submodule (ZMod 2) V} {V0 : Submodule (ZMod 2) V}
    (hF : LinTwoStdFrame E x P V0) {i j : Fin r} (hij : i ≠ j) (k : ℕ) {v : V}
    (hv : v ∈ P j) : (x i ^ k) v = v := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', LinearEquiv.mul_apply, ih, hF.2.2.2.2.2.2 i j hij v hv]

private theorem frame_x_pow_eq_one_of_dvd {E : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ}
    {x : Fin r → V ≃ₗ[ZMod 2] V} {P : Fin r → Submodule (ZMod 2) V} {V0 : Submodule (ZMod 2) V}
    (hF : LinTwoStdFrame E x P V0) (j : Fin r) {k : ℕ} (h : 3 ∣ k) :
    ∀ v ∈ P j, (x j ^ k) v = v := by
  obtain ⟨m, rfl⟩ := h
  intro v _
  rw [pow_mul, hF.2.2.2.1 j, one_pow]
  rfl

private theorem frame_x_pow_eq_self_imp {E : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ}
    {x : Fin r → V ≃ₗ[ZMod 2] V} {P : Fin r → Submodule (ZMod 2) V} {V0 : Submodule (ZMod 2) V}
    (hF : LinTwoStdFrame E x P V0) (j : Fin r) (k : ℕ) (hk : ¬ 3 ∣ k) :
    ∀ v ∈ P j, (x j ^ k) v = v → v = 0 := by
  intro v hv hfix
  have h3 : x j ^ 3 = 1 := hF.2.2.2.1 j
  have hvcom : v ∈ comSp (x j) := by rw [hF.2.2.2.2.1 j]; exact hv
  have hmod : k % 3 = 1 ∨ k % 3 = 2 := by
    have hlt : k % 3 < 3 := Nat.mod_lt k (by norm_num)
    have hne : k % 3 ≠ 0 := fun h => hk (Nat.dvd_of_mod_eq_zero h)
    omega
  have hpow : x j ^ k = x j ^ (k % 3) := pow_eq_pow_mod k h3
  rw [hpow] at hfix
  rcases hmod with h1 | h2
  · rw [h1, pow_one] at hfix
    exact eq_zero_of_mem_comSp_fixed h3 hvcom hfix
  · rw [h2] at hfix
    have hx : x j v = v := by
      have h1 : (x j * x j ^ 2) v = x j v := by
        simpa only [LinearEquiv.mul_apply] using congrArg (fun w => x j w) hfix
      rw [← pow_succ', h3] at h1
      simpa using h1.symm
    exact eq_zero_of_mem_comSp_fixed h3 hvcom hx

private theorem zpow_eq_nat_pow {f : V ≃ₗ[ZMod 2] V} (h3 : f ^ 3 = 1) (m : ℤ) :
    ∃ k : ℕ, f ^ m = f ^ k := by
  have hEm : f ^ m = f ^ (m % 3) := zpow_eq_zpow_emod' (x := f) (n := 3) m h3
  have hcast : ((m % 3).toNat : ℤ) = m % 3 :=
    Int.toNat_of_nonneg (Int.emod_nonneg m (by norm_num))
  refine ⟨(m % 3).toNat, ?_⟩
  rw [hEm, ← zpow_natCast (f) (m % 3).toNat, hcast]

private theorem zpow_apply_eq_self {f : V ≃ₗ[ZMod 2] V} {v : V} (hv : f v = v) (m : ℤ) :
    (f ^ m) v = v :=
  zpow_induction_right (g := f) (P := fun a => a v = v) rfl
    (fun a ha => by rw [LinearEquiv.mul_apply, hv, ha])
    (fun a ha => by rw [LinearEquiv.mul_apply, inv_apply_of_fix hv, ha])
    m

private theorem frame_P_le_comSp_of_not_dvd {E : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ}
    {x : Fin r → V ≃ₗ[ZMod 2] V} {P : Fin r → Submodule (ZMod 2) V} {V0 : Submodule (ZMod 2) V}
    (hF : LinTwoStdFrame E x P V0) {g : V ≃ₗ[ZMod 2] V} (j : Fin r) {k : ℕ}
    (hact : ∀ v ∈ P j, g v = (x j ^ k) v) (hk : ¬ 3 ∣ k) : P j ≤ comSp g := by
  intro v hv
  have hgmem : ∀ w ∈ P j, ds g w ∈ P j := fun w hw => by
    rw [ds_apply]
    exact (P j).sub_mem (by rw [hact w hw]; exact frame_x_pow_mem_P hF j k hw) hw
  let f : P j →ₗ[ZMod 2] P j := (ds g).restrict hgmem
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    apply Subtype.ext
    have h0 : ds g ((x : P j) : V) = 0 := by
      have := congrArg Subtype.val hx
      simpa only [f, LinearMap.coe_restrict_apply, Submodule.coe_zero] using this
    have hfix : g ((x : P j) : V) = ((x : P j) : V) := by
      have h1 : g ((x : P j) : V) - ((x : P j) : V) = 0 := by
        rwa [← ds_apply]
      exact sub_eq_zero.1 h1
    have hzV : ((x : P j) : V) = 0 := by
      refine frame_x_pow_eq_self_imp hF j k hk ((x : P j) : V) x.2 ?_
      simpa [hact _ x.2] using hfix
    simpa [Submodule.coe_zero] using hzV
  have hsurj : Function.Surjective f := LinearMap.injective_iff_surjective.mp hinj
  obtain ⟨w, hw⟩ := hsurj ⟨v, hv⟩
  refine mem_comSp.2 ⟨(w : P j), ?_⟩
  have hwv : ((ds g).restrict hgmem w : V) = v := congrArg Subtype.val hw
  rw [LinearMap.coe_restrict_apply] at hwv
  rw [← ds_apply]
  exact hwv

private theorem frame_finrank {E : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ}
    {x : Fin r → V ≃ₗ[ZMod 2] V} {P : Fin r → Submodule (ZMod 2) V} {V0 : Submodule (ZMod 2) V}
    (hF : LinTwoStdFrame E x P V0) :
    Module.finrank (ZMod 2) V = Module.finrank (ZMod 2) V0 + 2 * r := by
  classical
  let A : Option (Fin r) → Submodule (ZMod 2) V := fun o => o.elim V0 P
  let b := hF.2.1.collectedBasis (fun o => Module.finBasis (ZMod 2) (A o))
  have hb := Module.finrank_eq_card_basis b
  rw [hb, Fintype.card_sigma, Fintype.sum_option]
  simp only [Fintype.card_fin]
  rw [show Module.finrank (ZMod 2) (A none) = Module.finrank (ZMod 2) V0 from rfl]
  have hsum : (∑ i : Fin r, Module.finrank (ZMod 2) (A (some i))) = 2 * r := by
    have h1 : (∑ i : Fin r, Module.finrank (ZMod 2) (A (some i)))
        = ∑ _i : Fin r, (2 : ℕ) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hF.2.2.1 i
    rw [h1]
    rw [Finset.sum_const_nat (s := Finset.univ) (m := 2) (f := fun _ => (2 : ℕ))
      (fun _ _ => rfl)]
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  rw [hsum]

private theorem frame_mul_comm_of_action {E : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ}
    {x : Fin r → V ≃ₗ[ZMod 2] V} {P : Fin r → Submodule (ZMod 2) V} {V0 : Submodule (ZMod 2) V}
    (hF : LinTwoStdFrame E x P V0) {g : V ≃ₗ[ZMod 2] V} (k : Fin r → ℕ)
    (hact : ∀ j, ∀ v ∈ P j, g v = (x j ^ k j) v) (hgV0 : ∀ v ∈ V0, g v = v) (i : Fin r) :
    x i * g = g * x i := by
  apply frame_ext hF
  · intro v hv
    show x i (g v) = g (x i v)
    rw [hF.2.2.2.2.2.1 i v hv, hgV0 v hv]
    exact hF.2.2.2.2.2.1 i v hv
  · intro j v hv
    show x i (g v) = g (x i v)
    by_cases hji : j = i
    · rw [hji] at hv
      have hv' : x i v ∈ P i := frame_x_mem_P hF i hv
      rw [hact i v hv, hact i (x i v) hv']
      have hc : x i * x i ^ k i = x i ^ k i * x i :=
        ((Commute.refl (x i)).pow_right (k i)).eq
      simp only [← LinearEquiv.mul_apply]
      rw [hc]
    · have hij : i ≠ j := Ne.symm hji
      have hxv : x i v = v := hF.2.2.2.2.2.2 i j hij v hv
      have hgv : g v ∈ P j := by
        rw [hact j v hv]
        exact frame_x_pow_mem_P hF j (k j) hv
      rw [hxv]
      exact hF.2.2.2.2.2.2 i j hij (g v) hgv

private theorem eq_zero_of_mem_iSup_of_sub_eq_zero {ι : Type*} {A : ι → Submodule (ZMod 2) V}
    (hind : iSupIndep A) {g : V ≃ₗ[ZMod 2] V}
    (hA : ∀ i, ∀ x ∈ A i, g x - x ∈ A i)
    (hinj : ∀ i, ∀ x ∈ A i, g x - x = 0 → x = 0)
    {v : V} (hv : v ∈ ⨆ i, A i) (hgv : g v - v = 0) : v = 0 := by
  classical
  obtain ⟨s, hs⟩ := Submodule.exists_finset_of_mem_iSup A hv
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum A v).mp hs
  have hsum : ∑ i ∈ s, (g ((μ i : V)) - (μ i : V)) = 0 := by
    rw [Finset.sum_sub_distrib]
    have hmap : ∑ i ∈ s, g ((μ i : V)) = g v := by
      rw [← map_sum, hμ]
    rw [hmap, hμ]
    exact hgv
  have hzero : ∀ i ∈ s, g ((μ i : V)) - (μ i : V) = 0 :=
    (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero A).mp hind s
      (fun i => g ((μ i : V)) - (μ i : V))
      (fun i _ => hA i (μ i) (μ i).2) hsum
  have hμ0 : ∀ i ∈ s, (μ i : V) = 0 := fun i hi =>
    hinj i (μ i) (μ i).2 (hzero i hi)
  rw [← hμ]
  exact Finset.sum_eq_zero fun i hi => by rw [hμ0 i hi]

theorem lin_two_frame_action {E : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ}
    {x : Fin r → V ≃ₗ[ZMod 2] V} {P : Fin r → Submodule (ZMod 2) V} {V0 : Submodule (ZMod 2) V}
    (hF : LinTwoStdFrame E x P V0) {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ E) :
    (∀ v ∈ V0, g v = v) ∧ ∀ j, ∃ k : ℕ, ∀ v ∈ P j, g v = (x j ^ k) v := by
  classical
  have hgen : ∀ i : Fin r, ∀ y ∈ Subgroup.zpowers (x i),
      (∀ v ∈ V0, y v = v) ∧ ∀ j, ∃ k : ℕ, ∀ v ∈ P j, y v = (x j ^ k) v := by
    intro i y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨?_, ?_⟩
    · intro v hv
      obtain ⟨k, hk⟩ := zpow_eq_nat_pow (hF.2.2.2.1 i) n
      rw [hk]
      exact frame_x_pow_fixed_V0 hF i k hv
    · intro j
      by_cases hji : j = i
      · rw [hji]
        obtain ⟨k, hk⟩ := zpow_eq_nat_pow (hF.2.2.2.1 i) n
        exact ⟨k, fun v _ => by rw [hk]⟩
      · exact ⟨0, fun v hv => by
          obtain ⟨k, hk⟩ := zpow_eq_nat_pow (hF.2.2.2.1 i) n
          rw [hk, pow_zero]
          simpa using frame_x_pow_fixed_P hF (Ne.symm hji) k hv⟩
  have hone : (∀ v ∈ V0, (1 : V ≃ₗ[ZMod 2] V) v = v) ∧
      ∀ j, ∃ k : ℕ, ∀ v ∈ P j, (1 : V ≃ₗ[ZMod 2] V) v = (x j ^ k) v :=
    ⟨fun v _ => rfl, fun j => ⟨0, fun v _ => by simp⟩⟩
  have hmul : ∀ (a b : V ≃ₗ[ZMod 2] V),
      ((∀ v ∈ V0, a v = v) ∧ ∀ j, ∃ k : ℕ, ∀ v ∈ P j, a v = (x j ^ k) v) →
      ((∀ v ∈ V0, b v = v) ∧ ∀ j, ∃ k : ℕ, ∀ v ∈ P j, b v = (x j ^ k) v) →
      ((∀ v ∈ V0, (a * b) v = v) ∧ ∀ j, ∃ k : ℕ, ∀ v ∈ P j, (a * b) v = (x j ^ k) v) := by
    rintro a b ⟨ha0, ha⟩ ⟨hb0, hb⟩
    refine ⟨fun v hv => by rw [LinearEquiv.mul_apply, hb0 v hv, ha0 v hv], fun j => ?_⟩
    obtain ⟨ka, hka⟩ := ha j
    obtain ⟨kb, hkb⟩ := hb j
    refine ⟨ka + kb, fun v hv => ?_⟩
    rw [LinearEquiv.mul_apply, hkb v hv, hka _ (frame_x_pow_mem_P hF j kb hv)]
    rw [← LinearEquiv.mul_apply, pow_add]
  exact Subgroup.iSup_induction (S := fun i => Subgroup.zpowers (x i))
    (C := fun y : V ≃ₗ[ZMod 2] V =>
      (∀ v ∈ V0, y v = v) ∧ ∀ j, ∃ k : ℕ, ∀ v ∈ P j, y v = (x j ^ k) v)
    (hF.1 ▸ hg) hgen hone hmul

theorem lin_two_frame_weightOne {E : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ}
    {x : Fin r → V ≃ₗ[ZMod 2] V} {P : Fin r → Submodule (ZMod 2) V} {V0 : Submodule (ZMod 2) V}
    (hF : LinTwoStdFrame E x P V0) {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ E)
    (h2 : Module.finrank (ZMod 2) (comSp g) = 2) :
    ∃ (j : Fin r) (k : ℕ), g = x j ^ k := by
  classical
  obtain ⟨hgV0, hgact⟩ := lin_two_frame_action hF hg
  choose k hk using hgact
  have hind : iSupIndep P := hF.2.1.submodule_iSupIndep.comp (Option.some_injective _)
  have h_atMost : ∀ j₁ j₂ : Fin r, j₁ ≠ j₂ → 3 ∣ k j₁ ∨ 3 ∣ k j₂ := by
    intro j₁ j₂ hj
    by_contra hcon
    push Not at hcon
    obtain ⟨hnd1, hnd2⟩ := hcon
    have hle1 : P j₁ ≤ comSp g := frame_P_le_comSp_of_not_dvd hF j₁ (hk j₁) hnd1
    have hle2 : P j₂ ≤ comSp g := frame_P_le_comSp_of_not_dvd hF j₂ (hk j₂) hnd2
    have hsup : P j₁ ⊔ P j₂ ≤ comSp g := sup_le hle1 hle2
    have hd : Disjoint (P j₁) (P j₂) := by
      rw [Submodule.disjoint_def]
      intro x hx1 hx2
      have hdis := iSupIndep_def.mp hind j₁
      rw [Submodule.disjoint_def] at hdis
      exact hdis x hx1
        (Submodule.mem_iSup_of_mem j₂ (Submodule.mem_iSup_of_mem (Ne.symm hj) hx2))
    have hfr : Module.finrank (ZMod 2) ↥(P j₁ ⊔ P j₂) = 4 := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq (P j₁) (P j₂)
      rw [hd.eq_bot, finrank_bot, add_zero, hF.2.2.1 j₁, hF.2.2.1 j₂] at h
      omega
    have hle := Submodule.finrank_mono hsup
    rw [hfr, h2] at hle
    omega
  have h_exists : ∃ j : Fin r, ¬ 3 ∣ k j := by
    by_contra hcon
    push Not at hcon
    have hg1 : g = 1 := by
      apply frame_ext hF
      · intro v hv
        rw [hgV0 v hv]
        rfl
      · intro j v hv
        rw [hk j v hv, frame_x_pow_eq_one_of_dvd hF j (hcon j) v hv]
        rfl
    have hzero : Module.finrank (ZMod 2) (comSp g) = 0 := by
      rw [hg1]
      have hds : ds (1 : V ≃ₗ[ZMod 2] V) = 0 := by
        apply LinearMap.ext
        intro x
        simp [ds]
      have hbot : comSp (1 : V ≃ₗ[ZMod 2] V) = ⊥ := by
        rw [comSp, hds]
        exact LinearMap.range_zero
      rw [hbot, finrank_bot]
    omega
  obtain ⟨j₀, hk₀⟩ := h_exists
  refine ⟨j₀, k j₀, ?_⟩
  apply frame_ext hF
  · intro v hv
    rw [hgV0 v hv]
    exact (frame_x_pow_fixed_V0 hF j₀ (k j₀) hv).symm
  · intro j v hv
    by_cases hjj : j = j₀
    · rw [hjj] at hv
      exact hk j₀ v hv
    · have hdiv : 3 ∣ k j := by
        rcases h_atMost j j₀ hjj with h | h
        · exact h
        · exact absurd h hk₀
      rw [hk j v hv, frame_x_pow_eq_one_of_dvd hF j hdiv v hv]
      exact (frame_x_pow_fixed_P hF (Ne.symm hjj) (k j₀) hv).symm

theorem lin_two_outside_plane
    {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    {x : Fin (Module.finrank (ZMod 2) V / 2) → V ≃ₗ[ZMod 2] V}
    {P : Fin (Module.finrank (ZMod 2) V / 2) → Submodule (ZMod 2) V} {V0 : Submodule (ZMod 2) V}
    (hF : LinTwoStdFrame E x P V0) {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ E) (hg3 : g ^ 3 = 1)
    (hfix : 2 ≤ Module.finrank (ZMod 2) (fixSp g)) :
    ∃ y ∈ E, y ∉ Subgroup.zpowers g ∧ (∀ v ∈ comSp g, y v = v) ∧
      ∀ v ∈ fixSp g, y v ∈ fixSp g := by
  classical
  obtain ⟨hgV0, hgact⟩ := lin_two_frame_action hF hg
  choose k hk using hgact
  have hind : iSupIndep P := hF.2.1.submodule_iSupIndep.comp (Option.some_injective _)
  have hex : ∃ j : Fin (Module.finrank (ZMod 2) V / 2), 3 ∣ k j := by
    by_contra hcon
    push Not at hcon
    have hfixV0 : fixSp g = V0 := by
      apply le_antisymm
      · intro v hv
        have hgv : g v = v := mem_fixSp.1 hv
        have htop := frame_iSup_eq_top hF
        have hvtop : v ∈ V0 ⊔ (⨆ j, P j) := by rw [htop]; trivial
        obtain ⟨v0, hv0, v', hv', hv0v'⟩ := Submodule.mem_sup.1 hvtop
        have hgv' : g v' = v' := by
          have h1 : g (v0 + v') = v0 + v' := by rw [hv0v']; exact hgv
          rw [map_add, hgV0 v0 hv0] at h1
          exact add_left_cancel h1
        have hz : v' = 0 := by
          refine eq_zero_of_mem_iSup_of_sub_eq_zero (A := P) (g := g) hind
            (fun j x hx => ?_) (fun j x hx h0 => ?_) hv' ?_
          · rw [hk j x hx]
            exact (P j).sub_mem (frame_x_pow_mem_P hF j (k j) hx) hx
          · exact frame_x_pow_eq_self_imp hF j (k j) (hcon j) x hx
              (by rw [← hk j x hx]; exact sub_eq_zero.1 h0)
          · rw [hgv', sub_self]
        rw [← hv0v', hz, add_zero]
        exact hv0
      · intro v hv
        exact mem_fixSp.2 (hgV0 v hv)
    have hfr : Module.finrank (ZMod 2) V0 ≤ 1 := by
      have h := frame_finrank hF
      have hdm := Nat.div_add_mod (Module.finrank (ZMod 2) V) 2
      have hlt : Module.finrank (ZMod 2) V % 2 < 2 := Nat.mod_lt _ (by norm_num)
      omega
    rw [hfixV0] at hfix
    omega
  obtain ⟨j₀, hk₀⟩ := hex
  have hgP : ∀ v ∈ P j₀, g v = v := by
    intro v hv
    rw [hk j₀ v hv]
    exact frame_x_pow_eq_one_of_dvd hF j₀ hk₀ v hv
  refine ⟨x j₀, ?_, ?_, ?_, ?_⟩
  · rw [hF.1]
    exact Subgroup.mem_iSup_of_mem j₀ (Subgroup.mem_zpowers (x j₀))
  · intro hy
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hne : comSp (x j₀) ≠ ⊥ := by
      intro hbot
      have hfr : Module.finrank (ZMod 2) (comSp (x j₀)) = 2 := by
        rw [hF.2.2.2.2.1 j₀, hF.2.2.1 j₀]
      rw [hbot, finrank_bot] at hfr
      omega
    obtain ⟨v, hv, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hvP : v ∈ P j₀ := by rw [← hF.2.2.2.2.1 j₀]; exact hv
    have hxv : x j₀ v ≠ v := fun h =>
      hvne (eq_zero_of_mem_comSp_fixed (hF.2.2.2.1 j₀) hv h)
    exact hxv (by rw [← hm]; exact zpow_apply_eq_self (hgP v hvP) m)
  · intro w hw
    obtain ⟨v, hv⟩ := mem_comSp.1 hw
    rw [← hv]
    have htop := frame_iSup_eq_top hF
    have hvtop : v ∈ V0 ⊔ (⨆ j, P j) := by rw [htop]; trivial
    obtain ⟨v0, hv0, v', hv', hv0v'⟩ := Submodule.mem_sup.1 hvtop
    have hgg : g v - v = g v' - v' := by
      rw [← hv0v', map_add, hgV0 v0 hv0]
      abel
    rw [hgg]
    refine Submodule.iSup_induction P hv'
      (motive := fun z => x j₀ (g z - z) = g z - z) ?_ ?_ ?_
    · intro j p hp
      by_cases hjj : j = j₀
      · rw [hjj] at hp
        rw [hgP p hp, sub_self, map_zero]
      · have hgp : g p ∈ P j := by
          rw [hk j p hp]
          exact frame_x_pow_mem_P hF j (k j) hp
        have hmem : g p - p ∈ P j := (P j).sub_mem hgp hp
        exact hF.2.2.2.2.2.2 j₀ j (Ne.symm hjj) (g p - p) hmem
    · simp
    · intro a b ha hb
      have hsplit : g (a + b) - (a + b) = (g a - a) + (g b - b) := by
        rw [map_add]
        abel
      rw [hsplit, map_add, ha, hb]
  · intro v hv
    exact cent_fix (frame_mul_comm_of_action hF k hk hgV0 j₀) hv

theorem lin_two_frame_full_support
    {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    {x : Fin (Module.finrank (ZMod 2) V / 2) → V ≃ₗ[ZMod 2] V}
    {P : Fin (Module.finrank (ZMod 2) V / 2) → Submodule (ZMod 2) V} {V0 : Submodule (ZMod 2) V}
    (hF : LinTwoStdFrame E x P V0) (hodd : Odd (Module.finrank (ZMod 2) V))
    {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ E) (hg3 : g ^ 3 = 1)
    (hfix : Module.finrank (ZMod 2) (fixSp g) = 1) :
    fixSp g = V0 ∧ comSp g = ⨆ j, P j := by
  classical
  obtain ⟨hgV0, hgact⟩ := lin_two_frame_action hF hg
  choose k hk using hgact
  have hfr : Module.finrank (ZMod 2) V0 = 1 := by
    have h := frame_finrank hF
    have hodd' : Module.finrank (ZMod 2) V % 2 = 1 := Nat.odd_iff.mp hodd
    have hdm := Nat.div_add_mod (Module.finrank (ZMod 2) V) 2
    omega
  have hfixV0 : fixSp g = V0 := by
    have hle : V0 ≤ fixSp g := fun v hv => mem_fixSp.2 (hgV0 v hv)
    have hfin : Module.finrank (ZMod 2) V0 = Module.finrank (ZMod 2) (fixSp g) := by
      rw [hfix, hfr]
    exact (Submodule.eq_of_le_of_finrank_eq hle hfin).symm
  have hcom_le : comSp g ≤ ⨆ j, P j := by
    intro w hw
    obtain ⟨v, hv⟩ := mem_comSp.1 hw
    rw [← hv]
    have htop := frame_iSup_eq_top hF
    have hvtop : v ∈ V0 ⊔ (⨆ j, P j) := by rw [htop]; trivial
    obtain ⟨v0, hv0, v', hv', hv0v'⟩ := Submodule.mem_sup.1 hvtop
    have hgg : g v - v = g v' - v' := by
      rw [← hv0v', map_add, hgV0 v0 hv0]
      abel
    rw [hgg]
    have hgv' : g v' ∈ ⨆ j, P j := by
      refine Submodule.iSup_induction P hv'
        (motive := fun z => g z ∈ ⨆ j, P j) ?_ ?_ ?_
      · intro j p hp
        rw [hk j p hp]
        exact Submodule.mem_iSup_of_mem j (frame_x_pow_mem_P hF j (k j) hp)
      · simp
      · intro a b ha hb
        rw [map_add]
        exact Submodule.add_mem _ ha hb
    exact Submodule.sub_mem _ hgv' hv'
  have hle : (⨆ j, P j) ≤ comSp g := by
    refine iSup_le (fun j => ?_)
    by_cases hk3 : 3 ∣ k j
    · intro p hp
      have hgp : g p = p := by
        rw [hk j p hp]
        exact frame_x_pow_eq_one_of_dvd hF j hk3 p hp
      have hpV0 : p ∈ V0 := by
        rw [← hfixV0]
        exact mem_fixSp.2 hgp
      have hdisj : Disjoint V0 (P j) :=
        hF.2.1.submodule_iSupIndep.pairwiseDisjoint (Option.some_ne_none j).symm
      have hpbot : p ∈ (⊥ : Submodule (ZMod 2) V) := by
        rw [← hdisj.eq_bot]
        exact Submodule.mem_inf.2 ⟨hpV0, hp⟩
      rw [Submodule.mem_bot] at hpbot
      rw [hpbot]
      exact (comSp g).zero_mem
    · exact frame_P_le_comSp_of_not_dvd hF j (hk j) hk3
  exact ⟨hfixV0, le_antisymm hcom_le hle⟩

end CFSG.LocalAnalysis.GLTheoremA.T173A

end

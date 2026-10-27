module

public import CFSG.ClassicalGroups.Orthogonal.Derived
public import CFSG.ClassicalGroups.Orthogonal.Restrict

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

attribute [local simp] HypPair.Q_e HypPair.Q_f HypPair.polar_ef HypPair.polar_fe
  HypPair.polar_ee HypPair.polar_ff

@[expose] def tailSpace (P : ℕ → HypPair Q) : ℕ → Submodule K V
  | 0 => ⊤
  | j + 1 => tailSpace P j ⊓ (P j).perp

theorem tailSpace_succ (P : ℕ → HypPair Q) (j : ℕ) :
    tailSpace P (j + 1) = tailSpace P j ⊓ (P j).perp :=
  rfl

theorem mem_tailSpace {P : ℕ → HypPair Q} {j : ℕ} {x : V} :
    x ∈ tailSpace P j ↔ ∀ i < j, polar Q (P i).e x = 0 ∧ polar Q (P i).f x = 0 := by
  induction j with
  | zero => simp [tailSpace]
  | succ j ih =>
    rw [tailSpace_succ, Submodule.mem_inf, ih, HypPair.mem_perp]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h1 i hi
      · exact h2
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h j (Nat.lt_succ_self j)⟩

section Family

variable {P : ℕ → HypPair Q} {r : ℕ} (hP : ∀ i j, i < r → j < r → i ≠ j → (P i).Orth (P j))

include hP in
theorem e_mem_tailSpace {j k : ℕ} (hjk : j ≤ k) (hk : k < r) : (P k).e ∈ tailSpace P j :=
  mem_tailSpace.mpr fun i hi =>
    ⟨(hP i k (by omega) hk (by omega)).ee, (hP i k (by omega) hk (by omega)).fe⟩

include hP in
theorem f_mem_tailSpace {j k : ℕ} (hjk : j ≤ k) (hk : k < r) : (P k).f ∈ tailSpace P j :=
  mem_tailSpace.mpr fun i hi =>
    ⟨(hP i k (by omega) hk (by omega)).ef, (hP i k (by omega) hk (by omega)).ff⟩

include hP in
theorem polarNondegOn_tailSpace (hQ : (polarBilin Q).Nondegenerate) {j : ℕ} (hj : j ≤ r) :
    PolarNondegOn Q (tailSpace P j) := by
  induction j with
  | zero => exact polarNondegOn_top hQ
  | succ j ih =>
    exact (ih (by omega)).inf_perp (P j) (e_mem_tailSpace hP le_rfl (by omega))
      (f_mem_tailSpace hP le_rfl (by omega))

theorem apply_mem_tailSpace {j : ℕ} {h : V ≃ₗ[K] V}
    (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hfix : ∀ i < j, h (P i).e = (P i).e ∧ h (P i).f = (P i).f) {x : V}
    (hx : x ∈ tailSpace P j) : h x ∈ tailSpace P j := by
  rw [mem_tailSpace] at hx ⊢
  intro i hi
  rw [← (hfix i hi).1, ← (hfix i hi).2, polar_map_of_mem hh, polar_map_of_mem hh]
  exact hx i hi

theorem polar_e_tailSpace {i j : ℕ} (hij : i < j) {x : V} (hx : x ∈ tailSpace P j) :
    polar Q (P i).e x = 0 :=
  (mem_tailSpace.mp hx i hij).1

theorem polar_f_tailSpace {i j : ℕ} (hij : i < j) {x : V} (hx : x ∈ tailSpace P j) :
    polar Q (P i).f x = 0 :=
  (mem_tailSpace.mp hx i hij).2

include hP in
theorem eq_one_of_fix (h : V ≃ₗ[K] V)
    (hfix : ∀ i < r, h (P i).e = (P i).e ∧ h (P i).f = (P i).f)
    (hA : ∀ x ∈ tailSpace P r, h x = x) : h = 1 := by
  have key : ∀ n j, j + n = r → ∀ x ∈ tailSpace P j, h x = x := by
    intro n
    induction n with
    | zero => intro j hj x hx; rw [add_zero] at hj; subst hj; exact hA x hx
    | succ n ih =>
      intro j hj x hx
      have hjr : j < r := by omega
      have hproj : (P j).proj x ∈ tailSpace P (j + 1) := by
        rw [tailSpace_succ]
        refine ⟨?_, (P j).proj_mem_perp x⟩
        rw [HypPair.proj]
        exact Submodule.sub_mem _ (Submodule.sub_mem _ hx (Submodule.smul_mem _ _
          (e_mem_tailSpace hP le_rfl hjr))) (Submodule.smul_mem _ _ (f_mem_tailSpace hP le_rfl hjr))
      rw [(P j).eq_add_proj x, map_add, map_add, map_smul, map_smul, (hfix j hjr).1,
        (hfix j hjr).2, ih (j + 1) (by omega) _ hproj]
  exact LinearEquiv.ext fun x => key r 0 (zero_add r) x (Submodule.mem_top)

include hP in
theorem exists_mem_elementaryGroup_fix_succ (hQ : (polarBilin Q).Nondegenerate) {j : ℕ}
    (hj : j + 1 < r) {h : V ≃ₗ[K] V} (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hfix : ∀ i < j, h (P i).e = (P i).e ∧ h (P i).f = (P i).f) :
    ∃ b ∈ elementaryGroup Q, ∀ i < j + 1, (b * h) (P i).e = (P i).e ∧
      (b * h) (P i).f = (P i).f := by
  set W := tailSpace P j
  have hW : PolarNondegOn Q W := polarNondegOn_tailSpace hP hQ (by omega)
  have heW : (P j).e ∈ W := e_mem_tailSpace hP le_rfl (by omega)
  have hfW : (P j).f ∈ W := f_mem_tailSpace hP le_rfl (by omega)
  have he'W : (P (j + 1)).e ∈ W := e_mem_tailSpace hP (by omega) hj
  have hf'W : (P (j + 1)).f ∈ W := f_mem_tailSpace hP (by omega) hj
  have horth : (P j).Orth (P (j + 1)) := hP j (j + 1) (by omega) hj (by omega)
  have hxW : h (P j).e ∈ W := apply_mem_tailSpace hh hfix heW
  have hx0 : h (P j).e ≠ 0 := fun h0 => (P j).e_ne_zero (h.map_eq_zero_iff.mp h0)
  obtain ⟨b₁, hb₁, hb₁x, hb₁W, hb₁fix⟩ := exists_mem_elementaryGroup_apply_eq_of_mem hW horth heW
    hfW he'W hf'W hxW heW hx0 (P j).e_ne_zero (by rw [map_of_mem hh, (P j).Q_e])
  have hb₁O := elementaryGroup_le_orthogonalGroup Q hb₁
  set y := b₁ (h (P j).f) with hy
  have hyW : y ∈ W := hb₁W _ (apply_mem_tailSpace hh hfix hfW)
  have hQy : Q y = 0 := by rw [hy, map_of_mem hb₁O, map_of_mem hh, (P j).Q_f]
  have hey : polar Q (P j).e y = 1 := by
    rw [hy, ← hb₁x, polar_map_of_mem hb₁O, polar_map_of_mem hh, (P j).polar_ef]
  set b₂ := eichler Q (P j).e ((1 : K)⁻¹ • ((P j).f - y)) with hb₂
  have hb₂y : b₂ y = (P j).f :=
    eichler_apply_eq_of_polar_eq (P j).Q_e (by rw [hQy, (P j).Q_f]) hey (P j).polar_ef one_ne_zero
  have hperp : ∀ i < j, ∀ z, (z = (P i).e ∨ z = (P i).f) → ∀ w ∈ W, polar Q z w = 0 := by
    rintro i hi z (rfl | rfl) w hw
    · exact polar_e_tailSpace hi hw
    · exact polar_f_tailSpace hi hw
  have hb₂fix : ∀ i < j, ∀ z, (z = (P i).e ∨ z = (P i).f) → b₂ z = z := by
    intro i hi z hz
    apply eichler_apply_of_polar_eq_zero
    · exact hperp i hi z hz _ heW
    · rw [polar_smul_right_eq, polar_sub_right, hperp i hi z hz _ hfW, hperp i hi z hz _ hyW,
        sub_zero, mul_zero]
  refine ⟨b₂ * b₁, mul_mem (eichler_mem_elementaryGroup Q _ _) hb₁, fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply, (hfix i hi).1, (hfix i hi).2,
      hb₁fix _ fun w hw => hperp i hi _ (Or.inl rfl) w hw,
      hb₁fix _ fun w hw => hperp i hi _ (Or.inr rfl) w hw, hb₂fix i hi _ (Or.inl rfl),
      hb₂fix i hi _ (Or.inr rfl)]
    exact ⟨rfl, rfl⟩
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply, hb₁x, ← hy, hb₂y, hb₂, eichler_apply_self]
    exact ⟨rfl, rfl⟩

include hP in
theorem exists_mem_elementaryGroup_fix (hQ : (polarBilin Q).Nondegenerate) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {j : ℕ} (hj : j + 1 ≤ r) :
    ∃ a ∈ elementaryGroup Q, ∀ i < j, (a * g) (P i).e = (P i).e ∧ (a * g) (P i).f = (P i).f := by
  induction j with
  | zero => exact ⟨1, Subgroup.one_mem _, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ j ih =>
    obtain ⟨a, ha, hafix⟩ := ih (by omega)
    obtain ⟨b, hb, hbfix⟩ := exists_mem_elementaryGroup_fix_succ hP hQ (j := j) (by omega)
      (mul_mem (elementaryGroup_le_orthogonalGroup Q ha) hg) hafix
    exact ⟨b * a, mul_mem hb ha, fun i hi => by rw [mul_assoc]; exact hbfix i hi⟩

theorem neg_eq_self_of_two_eq_zero (h2 : (2 : K) = 0) (x : V) : -x = x := by
  rw [neg_eq_iff_add_eq_zero, ← two_smul K x, h2, zero_smul]

theorem reflect_mem_closure (v : V) : reflect Q v ∈ Subgroup.closure (Set.range (reflect Q)) :=
  Subgroup.subset_closure ⟨v, rfl⟩

section Tail

variable (hQ : (polarBilin Q).Nondegenerate) (h2 : (2 : K) = 0)
  (hA : ∀ x ∈ tailSpace P r, Q x = 0 → x = 0)
  (hA' : ∀ x ∈ tailSpace P r, x ≠ 0 → ∀ y ∈ tailSpace P r, polar Q x y = 0 → ∃ c : K, y = c • x)

include hP hQ h2 hA hA' in
theorem mem_closure_reflect_of_fix_all {h : V ≃ₗ[K] V}
    (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hfix : ∀ i < r, h (P i).e = (P i).e ∧ h (P i).f = (P i).f) :
    h ∈ Subgroup.closure (Set.range (reflect Q)) := by
  set A := tailSpace P r
  set R := Subgroup.closure (Set.range (reflect Q))
  have hreflfix : ∀ v ∈ A, ∀ i < r, reflect Q v (P i).e = (P i).e ∧
      reflect Q v (P i).f = (P i).f := fun v hv i hi =>
    ⟨reflect_apply_of_polar_eq_zero (by rw [polar_comm]; exact polar_e_tailSpace hi hv),
      reflect_apply_of_polar_eq_zero (by rw [polar_comm]; exact polar_f_tailSpace hi hv)⟩
  by_cases hA0 : ∀ x ∈ A, x = 0
  · rw [eq_one_of_fix hP h hfix fun x hx => by rw [hA0 x hx, map_zero]]
    exact R.one_mem
  push Not at hA0
  obtain ⟨x, hxA, hx0⟩ := hA0
  have hQx : Q x ≠ 0 := fun h0 => hx0 (hA x hxA h0)
  set y := h x with hy
  have hyA : y ∈ A := apply_mem_tailSpace hh hfix hxA
  have hQy : Q y = Q x := map_of_mem hh x
  obtain ⟨ρ₁, hρ₁, hρ₁y, hρ₁O, hρ₁fix⟩ : ∃ ρ₁ ∈ R, ρ₁ y = x ∧
      ρ₁ ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      ∀ i < r, ρ₁ (P i).e = (P i).e ∧ ρ₁ (P i).f = (P i).f := by
    by_cases hxy : polar Q x y = 0
    · obtain ⟨c, hc⟩ := hA' x hxA hx0 y hyA hxy
      have hc1 : c = 1 := by
        have h1 : c ^ 2 * Q x = Q x := by rw [← map_smul_eq_sq, ← hc, hQy]
        have h3 : (c - 1) ^ 2 = 0 := by
          have : c ^ 2 = 1 := by
            have := mul_right_cancel₀ hQx (h1.trans (one_mul _).symm)
            exact this
          linear_combination this - c * h2 + h2
        exact sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h3)
      refine ⟨1, R.one_mem, by rw [hc, hc1, one_smul]; rfl, Subgroup.one_mem _,
        fun i _ => ⟨rfl, rfl⟩⟩
    · set v := x + y with hv
      have hvA : v ∈ A := A.add_mem hxA hyA
      have hQv : Q v = polar Q x y := by
        rw [hv, QuadraticMap.map_add Q, hQy, ← two_mul, h2, zero_mul, zero_add]
      refine ⟨reflect Q v, reflect_mem_closure v, ?_, reflect_mem_orthogonalGroup Q v,
        hreflfix v hvA⟩
      rw [reflect_apply (by rwa [hQv]), hQv, hv, polar_add_left, polar_self_eq_two_mul, hQy,
        h2, zero_mul, add_zero, div_self hxy, one_smul, show y - (x + y) = -x by abel]
      exact neg_eq_self_of_two_eq_zero h2 x
  set h' := ρ₁ * h with hh'
  have hh'O : h' ∈ TauCeti.QuadraticMap.orthogonalGroup Q := mul_mem hρ₁O hh
  have hh'x : h' x = x := by rw [hh', LinearEquiv.mul_apply, ← hy, hρ₁y]
  have hh'fix : ∀ i < r, h' (P i).e = (P i).e ∧ h' (P i).f = (P i).f := fun i hi => by
    rw [hh', LinearEquiv.mul_apply, LinearEquiv.mul_apply, (hfix i hi).1, (hfix i hi).2]
    exact hρ₁fix i hi
  have hAnd : PolarNondegOn Q A := polarNondegOn_tailSpace hP hQ le_rfl
  obtain ⟨t₀, ht₀A, ht₀⟩ := hAnd.exists_polar_ne_zero hxA hx0
  set t := (polar Q x t₀)⁻¹ • t₀ with ht
  have htA : t ∈ A := A.smul_mem _ ht₀A
  have hxt : polar Q x t = 1 := by rw [ht, polar_smul_right_eq, inv_mul_cancel₀ ht₀]
  have hspan : ∀ a ∈ A, ∃ γ : K, a = γ • x + polar Q x a • t := by
    intro a ha
    have hperp : polar Q x (a - polar Q x a • t) = 0 := by
      rw [polar_sub_right, polar_smul_right_eq, hxt, mul_one, sub_self]
    obtain ⟨γ, hγ⟩ := hA' x hxA hx0 _ (A.sub_mem ha (A.smul_mem _ htA)) hperp
    exact ⟨γ, by rw [← hγ]; abel⟩
  have hh'tA : h' t ∈ A := apply_mem_tailSpace hh'O hh'fix htA
  obtain ⟨α, hα⟩ := hspan _ hh'tA
  have hxh't : polar Q x (h' t) = 1 := by
    have := polar_map_of_mem hh'O x t
    rw [hh'x] at this
    rw [this, hxt]
  rw [hxh't, one_smul] at hα
  have hαeq : α * (1 + α * Q x) = 0 := by
    have hQt : Q (h' t) = Q t := map_of_mem hh'O t
    rw [hα, QuadraticMap.map_add Q, map_smul_eq_sq, polar_smul_left_eq, hxt] at hQt
    linear_combination hQt
  have hone : ∀ k : V ≃ₗ[K] V, (∀ i < r, k (P i).e = (P i).e ∧ k (P i).f = (P i).f) →
      k x = x → k t = t → k = 1 := by
    intro k hkfix hkx hkt
    refine eq_one_of_fix hP k hkfix fun a ha => ?_
    obtain ⟨γ, hγ⟩ := hspan a ha
    rw [hγ, map_add, map_smul, map_smul, hkx, hkt]
  have hh'R : h' ∈ R := by
    rcases mul_eq_zero.mp hαeq with hα0 | hα1
    · rw [hone h' hh'fix hh'x (by rw [hα, hα0, zero_smul, zero_add])]
      exact R.one_mem
    · have hαx : α = (Q x)⁻¹ := eq_inv_of_mul_eq_one_left (by linear_combination hα1 - h2)
      have hsx : reflect Q x * h' = 1 := by
        apply hone
        · intro i hi
          rw [LinearEquiv.mul_apply (reflect Q x) h', LinearEquiv.mul_apply (reflect Q x) h',
            (hh'fix i hi).1, (hh'fix i hi).2]
          exact hreflfix x hxA i hi
        · rw [LinearEquiv.mul_apply (reflect Q x) h', hh'x, reflect_apply hQx,
            polar_self_eq_two_mul, h2, zero_mul, zero_div, zero_smul, sub_zero]
        · rw [LinearEquiv.mul_apply (reflect Q x) h', hα, map_add, map_smul, reflect_apply hQx,
            polar_self_eq_two_mul, h2, zero_mul, zero_div, zero_smul, sub_zero, reflect_apply hQx,
            hxt, hαx, one_div]
          abel
      rw [eq_inv_of_mul_eq_one_right hsx, reflect_inv]
      exact reflect_mem_closure x
  have : h = ρ₁⁻¹ * h' := by rw [hh', inv_mul_cancel_left]
  rw [this]
  exact R.mul_mem (R.inv_mem hρ₁) hh'R

include hP h2 hA in
theorem exists_mem_closure_reflect_fix_all (hr : 1 ≤ r) {k : V ≃ₗ[K] V}
    (hk : k ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hfix : ∀ i < r - 1, k (P i).e = (P i).e ∧ k (P i).f = (P i).f) :
    ∃ ρ ∈ Subgroup.closure (Set.range (reflect Q)),
      ρ ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧
        ∀ i < r, (ρ * k) (P i).e = (P i).e ∧ (ρ * k) (P i).f = (P i).f := by
  set m := r - 1 with hm
  have hmr : m < r := by omega
  have hrm : r = m + 1 := by omega
  set R := Subgroup.closure (Set.range (reflect Q))
  set U := tailSpace P m
  have heU : (P m).e ∈ U := e_mem_tailSpace hP le_rfl hmr
  have hfU : (P m).f ∈ U := f_mem_tailSpace hP le_rfl hmr
  have hreflfix : ∀ v ∈ U, ∀ i < m, reflect Q v (P i).e = (P i).e ∧
      reflect Q v (P i).f = (P i).f := fun v hv i hi =>
    ⟨reflect_apply_of_polar_eq_zero (by rw [polar_comm]; exact polar_e_tailSpace hi hv),
      reflect_apply_of_polar_eq_zero (by rw [polar_comm]; exact polar_f_tailSpace hi hv)⟩
  have hprojA : ∀ y ∈ U, (P m).proj y ∈ tailSpace P r := by
    intro y hy
    rw [hrm, tailSpace_succ]
    refine ⟨?_, (P m).proj_mem_perp y⟩
    rw [HypPair.proj]
    exact U.sub_mem (U.sub_mem hy (U.smul_mem _ heU)) (U.smul_mem _ hfU)
  have hQdecomp : ∀ y, Q y = polar Q y (P m).f * polar Q y (P m).e + Q ((P m).proj y) := by
    intro y
    have hpe : polar Q (P m).e ((P m).proj y) = 0 :=
      (HypPair.mem_perp.mp ((P m).proj_mem_perp y)).1
    have hpf : polar Q (P m).f ((P m).proj y) = 0 :=
      (HypPair.mem_perp.mp ((P m).proj_mem_perp y)).2
    conv_lhs => rw [(P m).eq_add_proj y]
    rw [QuadraticMap.map_add Q (polar Q y (P m).f • (P m).e + polar Q y (P m).e • (P m).f),
      QuadraticMap.map_add Q (polar Q y (P m).f • (P m).e), map_smul_eq_sq, map_smul_eq_sq,
      polar_add_left, polar_smul_left_eq, polar_smul_left_eq, polar_smul_left_eq,
      polar_smul_right_eq, (P m).Q_e, (P m).Q_f, (P m).polar_ef, hpe, hpf]
    ring
  set y := k (P m).e with hy
  have hyU : y ∈ U := apply_mem_tailSpace hk hfix heU
  have hQy : Q y = 0 := by rw [hy, map_of_mem hk, (P m).Q_e]
  have hy0 : y ≠ 0 := fun h0 => (P m).e_ne_zero (k.map_eq_zero_iff.mp h0)
  obtain ⟨ρ₁, hρ₁, hρ₁O, hρ₁y, hρ₁fix⟩ : ∃ ρ₁ ∈ R, ρ₁ ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      ρ₁ y = (P m).e ∧ ∀ i < m, ρ₁ (P i).e = (P i).e ∧ ρ₁ (P i).f = (P i).f := by
    by_cases hb : polar Q y (P m).e = 0
    · have hQw : Q ((P m).proj y) = 0 := by
        have := hQdecomp y
        rw [hb, mul_zero, zero_add, hQy] at this
        exact this.symm
      have hw : (P m).proj y = 0 := hA _ (hprojA y hyU) hQw
      set a := polar Q y (P m).f with ha
      have hya : y = a • (P m).e := by
        have := (P m).eq_add_proj y
        rw [hb, zero_smul, add_zero, hw, add_zero] at this
        exact this
      have ha0 : a ≠ 0 := by
        intro h0
        rw [h0, zero_smul] at hya
        exact hy0 hya
      have hQv₁ : Q (y + (P m).f) = a := by
        rw [QuadraticMap.map_add Q, hQy, (P m).Q_f, zero_add, zero_add]
      have hQv₂ : Q ((P m).e + (P m).f) = 1 := by
        rw [QuadraticMap.map_add Q, (P m).Q_e, (P m).Q_f, (P m).polar_ef, zero_add, zero_add]
      have h1 : reflect Q (y + (P m).f) y = -(P m).f := by
        have hp : polar Q (y + (P m).f) y = a := by
          rw [polar_add_left, polar_self_eq_zero hQy, polar_comm Q (P m).f y, zero_add]
        rw [reflect_apply (by rw [hQv₁]; exact ha0), hQv₁, hp, div_self ha0, one_smul]
        abel
      have h2' : reflect Q ((P m).e + (P m).f) (-(P m).f) = (P m).e := by
        have hp : polar Q ((P m).e + (P m).f) (P m).f = 1 := by
          rw [polar_add_left, (P m).polar_ef, (P m).polar_ff, add_zero]
        rw [map_neg, reflect_apply (by rw [hQv₂]; exact one_ne_zero), hQv₂, hp, div_one, one_smul]
        abel
      have hv₁U : y + (P m).f ∈ U := U.add_mem hyU hfU
      have hv₂U : (P m).e + (P m).f ∈ U := U.add_mem heU hfU
      refine ⟨reflect Q ((P m).e + (P m).f) * reflect Q (y + (P m).f),
        R.mul_mem (reflect_mem_closure _) (reflect_mem_closure _),
        mul_mem (reflect_mem_orthogonalGroup Q _) (reflect_mem_orthogonalGroup Q _),
        by rw [LinearEquiv.mul_apply, h1, h2'], fun i hi => ?_⟩
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, (hreflfix _ hv₁U i hi).1,
        (hreflfix _ hv₁U i hi).2, (hreflfix _ hv₂U i hi).1, (hreflfix _ hv₂U i hi).2]
      exact ⟨rfl, rfl⟩
    · have hQv : Q ((P m).e + y) = polar Q y (P m).e := by
        rw [QuadraticMap.map_add Q, (P m).Q_e, hQy, zero_add, zero_add, polar_comm]
      have hvU : (P m).e + y ∈ U := U.add_mem heU hyU
      refine ⟨reflect Q ((P m).e + y), reflect_mem_closure _, reflect_mem_orthogonalGroup Q _, ?_,
        hreflfix _ hvU⟩
      have hp : polar Q ((P m).e + y) y = polar Q y (P m).e := by
        rw [polar_add_left, polar_self_eq_zero hQy, add_zero, polar_comm]
      rw [reflect_apply (by rwa [hQv]), hQv, hp, div_self hb, one_smul,
        show y - ((P m).e + y) = -(P m).e by abel]
      exact neg_eq_self_of_two_eq_zero h2 _
  set h₁ := ρ₁ * k with hh₁
  have hh₁O : h₁ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := mul_mem hρ₁O hk
  have hh₁e : h₁ (P m).e = (P m).e := by rw [hh₁, LinearEquiv.mul_apply, ← hy, hρ₁y]
  have hh₁fix : ∀ i < m, h₁ (P i).e = (P i).e ∧ h₁ (P i).f = (P i).f := fun i hi => by
    rw [hh₁, LinearEquiv.mul_apply, LinearEquiv.mul_apply, (hfix i hi).1, (hfix i hi).2]
    exact hρ₁fix i hi
  set z := h₁ (P m).f with hz
  have hzU : z ∈ U := apply_mem_tailSpace hh₁O hh₁fix hfU
  have hQz : Q z = 0 := by rw [hz, map_of_mem hh₁O, (P m).Q_f]
  have hez : polar Q z (P m).e = 1 := by
    have := polar_map_of_mem hh₁O (P m).f (P m).e
    rw [hh₁e, (P m).polar_fe] at this
    exact this
  obtain ⟨ρ₂, hρ₂, hρ₂O, hρ₂e, hρ₂z, hρ₂fix⟩ : ∃ ρ₂ ∈ R,
      ρ₂ ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ ρ₂ (P m).e = (P m).e ∧ ρ₂ z = (P m).f ∧
        ∀ i < m, ρ₂ (P i).e = (P i).e ∧ ρ₂ (P i).f = (P i).f := by
    have hwA : (P m).proj z ∈ tailSpace P r := hprojA z hzU
    have hQzd := hQdecomp z
    rw [hez, mul_one, hQz] at hQzd
    by_cases hw0 : (P m).proj z = 0
    · have ha : polar Q z (P m).f = 0 := by
        rw [hw0, QuadraticMap.map_zero, add_zero] at hQzd
        exact hQzd.symm
      have hzf : z = (P m).f := by
        have := (P m).eq_add_proj z
        rw [ha, hez, zero_smul, zero_add, one_smul, hw0, add_zero] at this
        exact this
      exact ⟨1, R.one_mem, Subgroup.one_mem _, rfl, hzf, fun i _ => ⟨rfl, rfl⟩⟩
    · have hQw : Q ((P m).proj z) ≠ 0 := fun h0 => hw0 (hA _ hwA h0)
      have hv₃U : z - (P m).f ∈ U := U.sub_mem hzU hfU
      have hQv₃ : Q (z - (P m).f) = Q ((P m).proj z) := by
        rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, polar_neg_right, hQz,
          (P m).Q_f]
        linear_combination hQzd
      have hv₃e : polar Q (z - (P m).f) (P m).e = 0 := by
        rw [polar_sub_left, hez, (P m).polar_fe, sub_self]
      have hv₃z : polar Q (z - (P m).f) z = Q ((P m).proj z) := by
        rw [polar_sub_left, polar_self_eq_zero hQz, polar_comm Q (P m).f z]
        linear_combination hQzd
      refine ⟨reflect Q (z - (P m).f), reflect_mem_closure _, reflect_mem_orthogonalGroup Q _,
        reflect_apply_of_polar_eq_zero hv₃e, ?_, hreflfix _ hv₃U⟩
      rw [reflect_apply (by rwa [hQv₃]), hv₃z, hQv₃, div_self hQw, one_smul, sub_sub_cancel]
  refine ⟨ρ₂ * ρ₁, R.mul_mem hρ₂ hρ₁, mul_mem hρ₂O hρ₁O, fun i hi => ?_⟩
  rw [mul_assoc, ← hh₁]
  rcases Nat.lt_succ_iff_lt_or_eq.mp (show i < m + 1 by omega) with hi' | hi'
  · rw [LinearEquiv.mul_apply ρ₂ h₁, LinearEquiv.mul_apply ρ₂ h₁, (hh₁fix i hi').1,
      (hh₁fix i hi').2]
    exact hρ₂fix i hi'
  · rw [hi', LinearEquiv.mul_apply ρ₂ h₁, LinearEquiv.mul_apply ρ₂ h₁, hh₁e, ← hz, hρ₂e, hρ₂z]
    exact ⟨rfl, rfl⟩

include hP hQ h2 hA hA' in
theorem orthogonalGroup_le_closure_of_two_eq_zero (hr : 1 ≤ r) :
    TauCeti.QuadraticMap.orthogonalGroup Q ≤
      Subgroup.closure (Set.range (reflect Q) ∪ elementaryGroup Q) := by
  intro g hg
  obtain ⟨a, ha, hafix⟩ := exists_mem_elementaryGroup_fix hP hQ hg (j := r - 1) (by omega)
  have haO := elementaryGroup_le_orthogonalGroup Q ha
  obtain ⟨ρ, hρ, hρO, hρfix⟩ :=
    exists_mem_closure_reflect_fix_all hP h2 hA hr (mul_mem haO hg) hafix
  have hk := mem_closure_reflect_of_fix_all hP hQ h2 hA hA' (mul_mem hρO (mul_mem haO hg)) hρfix
  have hle : Subgroup.closure (Set.range (reflect Q)) ≤
      Subgroup.closure (Set.range (reflect Q) ∪ elementaryGroup Q) :=
    Subgroup.closure_mono Set.subset_union_left
  have hEle : elementaryGroup Q ≤ Subgroup.closure (Set.range (reflect Q) ∪ elementaryGroup Q) :=
    fun x hx => Subgroup.subset_closure (Or.inr hx)
  have hg' : g = a⁻¹ * ρ⁻¹ * (ρ * (a * g)) := by group
  rw [hg']
  exact mul_mem (mul_mem (hEle (inv_mem ha)) (hle (inv_mem hρ))) (hle hk)

include hP hQ h2 hA hA' in
theorem commutator_orthogonalGroup_eq_of_two_eq_zero (hr : 3 ≤ r) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q :=
  commutator_orthogonalGroup_eq_of_le_closure hQ (hP 0 1 (by omega) (by omega) (by omega))
    (hP 0 2 (by omega) (by omega) (by omega)) (hP 1 2 (by omega) (by omega) (by omega))
    (orthogonalGroup_le_closure_of_two_eq_zero hP hQ h2 hA hA' (by omega))

end Tail

end Family

end CFSG.ClassicalGroups.Orthogonal

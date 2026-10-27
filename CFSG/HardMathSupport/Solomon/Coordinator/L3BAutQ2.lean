module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BAutAbstract
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BAutHeis

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut)

set_option linter.unusedSectionVars false

variable {M : Type*} [Group M] [Finite M]

@[expose] def heisR (X P : M) : Subgroup M := Subgroup.closure {X, P}

theorem X_mem_heisR (X P : M) : X ∈ heisR X P := Subgroup.subset_closure (by simp)

theorem P_mem_heisR (X P : M) : P ∈ heisR X P := Subgroup.subset_closure (by simp)

structure HeisData (M : Type*) [Group M] (X P w F : M) : Prop where
  card : Nat.card M = 216
  w_central : ∀ g : M, w * g = g * w
  w_pow : w ^ 3 = 1
  w_ne : w ≠ 1
  X_pow : X ^ 3 = 1
  P_pow : P ^ 3 = 1
  XP : X * P = w * (P * X)
  FP : F * P * F⁻¹ = X
  FX : F * X * F⁻¹ = P⁻¹
  F_pow : F ^ 4 = 1
  F_sq : F ^ 2 ≠ 1
  cent : ∀ y : M, y * X = X * y → y * P = P * y → y ∈ Subgroup.center M
  center_le : ∀ z ∈ Subgroup.center M, z ∈ Subgroup.zpowers w

namespace HeisData

variable {X P w F : M} (H : HeisData M X P w F)

include H

theorem orderOf_F : orderOf F = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := F) (by simpa using H.F_sq)
    (by simpa using H.F_pow)
  simpa using h

theorem w_eq : w = X * P * X⁻¹ * P⁻¹ := by
  have h := H.XP
  calc w = w * (P * X) * (P * X)⁻¹ := by group
    _ = X * P * (P * X)⁻¹ := by rw [← h]
    _ = X * P * X⁻¹ * P⁻¹ := by group

theorem w_mem : w ∈ heisR X P := by
  rw [H.w_eq]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (X_mem_heisR X P) (P_mem_heisR X P))
    (Subgroup.inv_mem _ (X_mem_heisR X P))) (Subgroup.inv_mem _ (P_mem_heisR X P))

theorem isPGroup_R : IsPGroup 3 (heisR X P) :=
  isPGroup_closure_heis H.w_central H.w_pow H.X_pow H.P_pow H.XP

theorem card_R : Nat.card (heisR X P) = 27 := by
  obtain ⟨k, hk⟩ := (H.isPGroup_R).exists_card_eq
  have hdvd : Nat.card (heisR X P) ∣ 216 := by
    rw [← H.card]
    exact Subgroup.card_subgroup_dvd_card _
  rw [hk] at hdvd
  have hk3 : k ≤ 3 := by
    by_contra hlt
    push Not at hlt
    have : 3 ^ 4 ∣ 216 := (pow_dvd_pow 3 hlt).trans hdvd
    norm_num at this
  have hnc : ¬ (X * P = P * X) := by
    intro h
    apply H.w_ne
    have h2 : w * (P * X) = 1 * (P * X) := by rw [← H.XP, h, one_mul]
    simpa using mul_right_cancel h2
  have hcomm : ∀ a b : heisR X P, a * b = b * a → k ≤ 3 → True := fun _ _ _ _ => trivial
  clear hcomm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  interval_cases k
  · exfalso
    apply hnc
    have h1 : Nat.card (heisR X P) = 1 := by simpa using hk
    have : Subsingleton (heisR X P) := (Nat.card_eq_one_iff_unique.1 h1).1
    have := Subsingleton.elim (⟨X, X_mem_heisR X P⟩ : heisR X P) ⟨P, P_mem_heisR X P⟩
    have hXP' : X = P := congrArg Subtype.val this
    rw [hXP']
  · exfalso
    apply hnc
    have : IsCyclic (heisR X P) := isCyclic_of_prime_card (p := 3) (by simpa using hk)
    have := (IsCyclic.isMulCommutative (α := heisR X P)).is_comm.comm
      (⟨X, X_mem_heisR X P⟩ : heisR X P) ⟨P, P_mem_heisR X P⟩
    exact congrArg Subtype.val this
  · exfalso
    apply hnc
    have := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := heisR X P) hk).is_comm.comm
      (⟨X, X_mem_heisR X P⟩ : heisR X P) ⟨P, P_mem_heisR X P⟩
    exact congrArg Subtype.val this
  · simpa using hk

theorem F_normalizes : F ∈ (Subgroup.normalizer (heisR X P : Set M)) := by
  apply Subgroup.mem_normalizer_fintype
  intro n hn
  have hle : heisR X P ≤ (heisR X P).comap (MulAut.conj F).toMonoidHom := by
    rw [heisR, Subgroup.closure_le]
    intro g hg
    rcases hg with h | h
    · rw [h]
      simp only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [H.FX]
      exact Subgroup.inv_mem _ (P_mem_heisR X P)
    · rw [Set.mem_singleton_iff.1 h]
      simp only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [H.FP]
      exact X_mem_heisR X P
  have := hle hn
  simpa using this

theorem index_dvd_two (T : Subgroup M) (hRT : heisR X P ≤ T) (hF : F ∈ T) : T.index ∣ 2 := by
  have h27 : 27 ∣ Nat.card T := H.card_R ▸ Subgroup.card_dvd_of_le hRT
  have h4 : 4 ∣ Nat.card T := H.orderOf_F ▸ Subgroup.orderOf_dvd_natCard T hF
  have h108 : 108 ∣ Nat.card T :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 27 4) h27 h4
  have hmul := T.card_mul_index
  rw [H.card] at hmul
  obtain ⟨c, hc⟩ := h108
  rw [hc] at hmul
  have h2 : c * T.index = 2 := by
    have : 108 * (c * T.index) = 108 * 2 := by rw [← mul_assoc, hmul]
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  exact Dvd.intro_left c h2

theorem normal_R : (heisR X P).Normal := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac : (Nat.card M).factorization 3 = 3 := by
    rw [H.card]
    have h : (216 : ℕ) = 2 ^ 3 * 3 ^ 3 := by norm_num
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Nat.Prime.factorization_pow Nat.prime_three]
    simp
  let Rs : Sylow 3 M := Sylow.ofCard (heisR X P) (by rw [H.card_R, hfac]; norm_num)
  have hmod := card_sylow_modEq_one 3 M
  have hidx : Nat.card (Sylow 3 M) = (Subgroup.normalizer (heisR X P : Set M)).index :=
    Sylow.card_eq_index_normalizer Rs
  have hdvd := H.index_dvd_two (Subgroup.normalizer (heisR X P : Set M)) Subgroup.le_normalizer H.F_normalizes
  have h1 : (Subgroup.normalizer (heisR X P : Set M)).index = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact h
    · exfalso
      rw [hidx, h] at hmod
      exact absurd hmod (by decide)
  rw [← Subgroup.normalizer_eq_top_iff]
  exact Subgroup.index_eq_one.1 h1

theorem eq_one_of_central (a : MulAut M) (h : ∀ x, x⁻¹ * a x ∈ Subgroup.center M) : a = 1 := by
  let φ : M →* Subgroup.center M :=
    { toFun := fun x => ⟨x⁻¹ * a x, h x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        show (x * y)⁻¹ * a (x * y) = (x⁻¹ * a x) * (y⁻¹ * a y)
        have hc := Subgroup.mem_center_iff.1 (h x) y⁻¹
        calc (x * y)⁻¹ * a (x * y) = y⁻¹ * (x⁻¹ * a x) * a y := by rw [map_mul]; group
          _ = (x⁻¹ * a x) * y⁻¹ * a y := by rw [hc]
          _ = (x⁻¹ * a x) * (y⁻¹ * a y) := by rw [mul_assoc] }
  have hz3 : ∀ z : Subgroup.center M, z ^ 3 = 1 := by
    intro z
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (H.center_le z.1 z.2)
    apply Subtype.ext
    show (z : M) ^ 3 = 1
    rw [← hn, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast,
      H.w_pow, _root_.one_zpow]
  have hcomm : ∀ a b : Subgroup.center M, a * b = b * a := fun a b =>
    Subtype.ext (Subgroup.mem_center_iff.1 b.2 a)
  have hPX : φ X = φ P := by
    rw [← H.FP, map_mul, map_mul, map_inv, hcomm (φ F) (φ P), mul_assoc, mul_inv_cancel, mul_one]
  have hXP' : φ P⁻¹ = φ X := by
    rw [← H.FX, map_mul, map_mul, map_inv, hcomm (φ F) (φ X), mul_assoc, mul_inv_cancel, mul_one]
  have hP1 : φ P = 1 := by
    have h1 : (φ P)⁻¹ = φ P := by rw [← map_inv, hXP', hPX]
    have h2 : φ P ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [← h1]
      exact inv_mul_cancel _
    have h3 : φ P ^ 3 = 1 := by rw [← map_pow, H.P_pow, map_one]
    calc φ P = φ P ^ 3 * (φ P ^ 2)⁻¹ := by group
      _ = 1 := by rw [h2, h3]; simp
  have hX1 : φ X = 1 := by rw [hPX, hP1]
  have hF1 : φ F = 1 := by
    have h3 : φ F ^ 3 = 1 := hz3 _
    have h4 : φ F ^ 4 = 1 := by rw [← map_pow, H.F_pow, map_one]
    calc φ F = φ F ^ 4 * (φ F ^ 3)⁻¹ := by group
      _ = 1 := by rw [h3, h4]; simp
  set K' : Subgroup M := heisR X P ⊔ Subgroup.zpowers F with hK'
  have hK'le : K' ≤ φ.ker := by
    refine sup_le ?_ (Subgroup.zpowers_le.2 (MonoidHom.mem_ker.2 hF1))
    rw [heisR, Subgroup.closure_le]
    intro g hg
    rcases hg with h | h
    · rw [h]; exact MonoidHom.mem_ker.2 hX1
    · rw [Set.mem_singleton_iff.1 h]; exact MonoidHom.mem_ker.2 hP1
  have hidx := H.index_dvd_two K' le_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers F))
  have hnorm : K'.Normal := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hidx with h1 | h2
    · rw [Subgroup.index_eq_one.1 h1]
      infer_instance
    · exact Subgroup.normal_of_index_eq_two h2
  have hall : ∀ g, φ g = 1 := by
    intro g
    have hg := hK'le (K'.pow_index_mem g)
    rw [MonoidHom.mem_ker, map_pow] at hg
    rcases (Nat.dvd_prime Nat.prime_two).1 hidx with h1 | h2
    · rw [h1, pow_one] at hg
      exact hg
    · rw [h2] at hg
      have h3 : φ g ^ 3 = 1 := hz3 _
      calc φ g = φ g ^ 3 * (φ g ^ 2)⁻¹ := by group
        _ = 1 := by rw [hg, h3]; simp
  apply MulEquiv.ext
  intro x
  have h1 : x⁻¹ * a x = 1 := congrArg Subtype.val (hall x)
  calc a x = x * (x⁻¹ * a x) := by group
    _ = x := by rw [h1, mul_one]

theorem PXP : P * X * P⁻¹ = w⁻¹ * X := by
  have h : w⁻¹ * X * P = P * X := by
    calc w⁻¹ * X * P = w⁻¹ * (X * P) := by group
      _ = w⁻¹ * (w * (P * X)) := by rw [H.XP]
      _ = P * X := by group
  calc P * X * P⁻¹ = (w⁻¹ * X * P) * P⁻¹ := by rw [h]
    _ = w⁻¹ * X := by group

theorem XPX : X * P * X⁻¹ = w * P := by
  rw [H.XP]
  group

theorem conj_pow_X (n : ℕ) : P ^ n * X * (P ^ n)⁻¹ = (w⁻¹) ^ n * X := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : Commute ((w⁻¹) ^ n) P := ((Commute.inv_left (show Commute w P from
      H.w_central P)).pow_left n)
    calc P ^ (n + 1) * X * (P ^ (n + 1))⁻¹ = P * (P ^ n * X * (P ^ n)⁻¹) * P⁻¹ := by
          rw [pow_succ']; group
      _ = P * ((w⁻¹) ^ n * X) * P⁻¹ := by rw [ih]
      _ = (w⁻¹) ^ n * (P * X * P⁻¹) := by
          rw [← mul_assoc, ← mul_assoc, ← hc.eq]; group
      _ = (w⁻¹) ^ (n + 1) * X := by rw [H.PXP, pow_succ]; group

theorem conj_pow_P (n : ℕ) : X ^ n * P * (X ^ n)⁻¹ = w ^ n * P := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : Commute (w ^ n) X := (show Commute w X from H.w_central X).pow_left n
    calc X ^ (n + 1) * P * (X ^ (n + 1))⁻¹ = X * (X ^ n * P * (X ^ n)⁻¹) * X⁻¹ := by
          rw [pow_succ']; group
      _ = X * (w ^ n * P) * X⁻¹ := by rw [ih]
      _ = w ^ n * (X * P * X⁻¹) := by
          rw [← mul_assoc, ← mul_assoc, ← hc.eq]; group
      _ = w ^ (n + 1) * P := by rw [H.XPX, pow_succ]; group

theorem inner_of_fixes (τ : MulAut M)
    (hτ : ∀ q ∈ heisR X P, τ q * q⁻¹ ∈ Subgroup.center M) : τ ∈ innerAut M := by
  have hu := hτ X (X_mem_heisR X P)
  have hv := hτ P (P_mem_heisR X P)
  obtain ⟨i, hi⟩ : ∃ i : ℕ, w ^ i = τ X * X⁻¹ :=
    Submonoid.mem_powers_iff _ _ |>.1 (mem_powers_iff_mem_zpowers.2 (H.center_le _ hu))
  obtain ⟨j, hj⟩ : ∃ j : ℕ, w ^ j = τ P * P⁻¹ :=
    Submonoid.mem_powers_iff _ _ |>.1 (mem_powers_iff_mem_zpowers.2 (H.center_le _ hv))
  have hw2 : (w⁻¹) ^ 2 = w := by
    calc (w⁻¹) ^ 2 = w⁻¹ * w⁻¹ * w ^ 3 := by rw [H.w_pow, mul_one, pow_two]
      _ = w := by group
  set r : M := P ^ (2 * i) * X ^ j with hr
  have hrX : r * X * r⁻¹ = τ X := by
    have h1 : r * X * r⁻¹ = P ^ (2 * i) * X * (P ^ (2 * i))⁻¹ := by
      have hc : Commute (X ^ j) X := (Commute.refl X).pow_left j
      calc r * X * r⁻¹ = P ^ (2 * i) * (X ^ j * X * (X ^ j)⁻¹) * (P ^ (2 * i))⁻¹ := by
            rw [hr]; group
        _ = P ^ (2 * i) * X * (P ^ (2 * i))⁻¹ := by
            rw [hc.eq]; group
    rw [h1, H.conj_pow_X, pow_mul, hw2, hi]
    group
  have hrP : r * P * r⁻¹ = τ P := by
    have hc : Commute (P ^ (2 * i)) P := (Commute.refl P).pow_left _
    have hcw : Commute (w ^ j) (P ^ (2 * i)) := ((show Commute w (P ^ (2 * i)) from
      H.w_central _).pow_left j)
    calc r * P * r⁻¹ = P ^ (2 * i) * (X ^ j * P * (X ^ j)⁻¹) * (P ^ (2 * i))⁻¹ := by
          rw [hr]; group
      _ = P ^ (2 * i) * (w ^ j * P) * (P ^ (2 * i))⁻¹ := by rw [H.conj_pow_P]
      _ = w ^ j * (P ^ (2 * i) * P * (P ^ (2 * i))⁻¹) := by
          rw [← mul_assoc, ← mul_assoc, ← hcw.eq]; group
      _ = w ^ j * P := by rw [hc.eq]; group
      _ = τ P := by rw [hj]; group
  set σ : MulAut M := (MulAut.conj r)⁻¹ * τ with hσ
  have hσX : σ X = X := by
    rw [hσ, MulAut.mul_apply, MulAut.conj_inv_apply, ← hrX]
    group
  have hσP : σ P = P := by
    rw [hσ, MulAut.mul_apply, MulAut.conj_inv_apply, ← hrP]
    group
  have hσR : ∀ g ∈ heisR X P, σ g = g := by
    intro g hg
    have := MonoidHom.eqOn_closure (f := (σ : M →* M)) (g := MonoidHom.id M)
      (s := ({X, P} : Set M)) (by
        intro x hx
        rcases hx with h | h
        · rw [h]; exact hσX
        · rw [Set.mem_singleton_iff.1 h]; exact hσP) hg
    exact this
  have hRn := H.normal_R
  have hcent : ∀ m : M, m⁻¹ * σ m ∈ Subgroup.center M := by
    intro m
    refine H.cent _ ?_ ?_
    · have hmX : m * X * m⁻¹ ∈ heisR X P := hRn.conj_mem X (X_mem_heisR X P) m
      have e : σ m * X * (σ m)⁻¹ = m * X * m⁻¹ := by
        calc σ m * X * (σ m)⁻¹ = σ (m * X * m⁻¹) := by rw [map_mul, map_mul, map_inv, hσX]
          _ = m * X * m⁻¹ := hσR _ hmX
      have e2 : σ m * X = m * X * m⁻¹ * σ m := mul_inv_eq_iff_eq_mul.1 e
      calc m⁻¹ * σ m * X = m⁻¹ * (σ m * X) := by group
        _ = m⁻¹ * (m * X * m⁻¹ * σ m) := by rw [e2]
        _ = X * (m⁻¹ * σ m) := by group
    · have hmP : m * P * m⁻¹ ∈ heisR X P := hRn.conj_mem P (P_mem_heisR X P) m
      have e : σ m * P * (σ m)⁻¹ = m * P * m⁻¹ := by
        calc σ m * P * (σ m)⁻¹ = σ (m * P * m⁻¹) := by rw [map_mul, map_mul, map_inv, hσP]
          _ = m * P * m⁻¹ := hσR _ hmP
      have e2 : σ m * P = m * P * m⁻¹ * σ m := mul_inv_eq_iff_eq_mul.1 e
      calc m⁻¹ * σ m * P = m⁻¹ * (σ m * P) := by group
        _ = m⁻¹ * (m * P * m⁻¹ * σ m) := by rw [e2]
        _ = P * (m⁻¹ * σ m) := by group
  have hσ1 : σ = 1 := H.eq_one_of_central σ hcent
  have : MulAut.conj r = τ := inv_mul_eq_one.1 hσ1
  exact ⟨r, this⟩

end HeisData

theorem sylowCentreInn_of_heis {X P w F : M} (H : HeisData M X P w F) : SylowCentreInn M :=
  sylowCentreInn_of_data ⊤ le_top (heisR X P) H.isPGroup_R (fun _ _ _ => trivial)
    (fun d _ hd => H.inner_of_fixes d hd)

end CFSG.HardMathSupport.Solomon.Coordinator

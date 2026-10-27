module

public import CFSG.LieType.Steinberg.CentralExt.SpTorus
public import CFSG.LieType.Steinberg.CentralExt.HalfSpaceLift
public import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.ChainPairing

public section

open CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic CFSG.LieType.Steinberg
  CFSG.Assembly.LowTwoRank CFSG.LieType.RootSystem CFSG.LieType.Steinberg.CentralExt.SpTorus
open CFSG.LieType.Universal.Symplectic.SpExtras
open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.SpClosed

attribute [local instance] TorusLift.centerCommGroup

variable {n : ℕ} {F : Type} [Field F]

theorem x_add {γ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC n) ∅) (s t : F) :
    Sp.x n F γ (s + t) = Sp.x n F γ s * Sp.x n F γ t :=
  (Sp.isParametrization γ hγ).2.1 s t

section Lift

variable {E : Type*} [Group E] {π : E →* StatedSp n F}

variable (π) in
@[expose] def IsRootLift (γ : Fin n → ℤ) (Y : F → E) : Prop :=
  (∀ s t, Y (s + t) = Y s * Y t) ∧ (∀ s, π (Y s) = Sp.x n F γ s) ∧
    ∀ (t : Fin n → Fˣ) (e : E), π e = tor F t → ∀ s,
      e * Y s * e⁻¹ = Y ((chi (toStd n γ) t : F) * s)

variable (hcen : π.ker ≤ Subgroup.center E) (hπ : Function.Surjective π)

include hcen in
theorem commPairing_eq_zero [Finite F] (hF4 : Nat.card F ≠ 4) (hF9 : Nat.card F ≠ 9)
    {γ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC n) ∅) :
    TorusLift.commPairing hcen hπ (x_add (F := F) hγ) = 0 := by
  obtain ⟨p, _, _⟩ := TorusLift.exists_prime_charP (k := F)
  refine Pairing.pairing_eq_zero_of_sq p hF4 hF9
    (TorusLift.commPairing_self hcen hπ (x_add hγ)) fun U hU s t => ?_
  obtain ⟨t', ht'⟩ := exists_tor_sq hγ (Units.mk0 U hU)
  refine TorusLift.commPairing_smul hcen hπ (x_add hγ) (g := tor F t') (fun c => ?_) s t
  rw [tor_conj_x hγ, ht', Units.val_pow_eq_pow_val, Units.val_mk0]

include hcen hπ in
theorem exists_isRootLift_of_pairing {γ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC n) ∅)
    (h0 : TorusLift.commPairing hcen hπ (x_add (F := F) hγ) = 0) {t : Fin n → Fˣ}
    (ht : chi (toStd n γ) t ≠ 1) : ∃ Y : F → E, IsRootLift π γ Y := by
  have ha : (chi (toStd n γ) t : F) ≠ 1 := fun h => ht (Units.val_eq_one.1 h)
  exact ⟨TorusLift.canonLift hπ (x := Sp.x n F γ) (tor F t) (chi (toStd n γ) t),
    TorusLift.canonLift_add hcen hπ (x_add hγ) h0 (tor_conj_x hγ t) ha,
    TorusLift.map_canonLift hπ (x_add hγ) (tor_conj_x hγ t) ha,
    fun t' e he s => TorusLift.conj_canonLift hcen hπ (tor_mul_comm t t') (tor_conj_x hγ t') he s⟩

include hcen hπ in
theorem exists_isRootLift [Finite F] (hF4 : Nat.card F ≠ 4) (hF9 : Nat.card F ≠ 9)
    {γ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC n) ∅) {t : Fin n → Fˣ}
    (ht : chi (toStd n γ) t ≠ 1) : ∃ Y : F → E, IsRootLift π γ Y :=
  exists_isRootLift_of_pairing hcen hπ hγ (commPairing_eq_zero hcen hπ hF4 hF9 hγ) ht

theorem notMem_roots_of_three_le {v : Fin n → ℤ} {i : Fin n} (h : 3 ≤ |toStd n v i|) :
    v ∉ roots (isFiniteType_cartanC n) ∅ := fun hv => by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hv
  have := abs_stdVec_le r i
  rw [hr] at this
  linarith

theorem toStd_comb_apply (α β : Fin n → ℤ) (p : ℕ × ℕ) (i : Fin n) :
    toStd n (p.1 • α + p.2 • β) i = p.1 * toStd n α i + p.2 * toStd n β i := by
  rw [Sp.toStd_comb, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul, nsmul_eq_mul]

theorem exists_root_sum {i j : Fin n} (hij : i ≠ j) {s : ℤ} (hs : s = 1 ∨ s = -1) :
    ∃ α ∈ roots (isFiniteType_cartanC n) ∅, toStd n α = s • (Pi.single i 1 + Pi.single j 1) := by
  rcases hs with rfl | rfl <;> rcases lt_or_gt_of_ne hij with h | h
  · obtain ⟨α, hα, he⟩ := Sp.exists_root_of_stdVec (n := n) (.positiveSum i j h)
    exact ⟨α, hα, by rw [he, stdVec, one_smul]⟩
  · obtain ⟨α, hα, he⟩ := Sp.exists_root_of_stdVec (n := n) (.positiveSum j i h)
    exact ⟨α, hα, by rw [he, stdVec, one_smul, add_comm]⟩
  · obtain ⟨α, hα, he⟩ := Sp.exists_root_of_stdVec (n := n) (.negativeSum i j h)
    exact ⟨α, hα, by rw [he, stdVec, neg_one_smul]⟩
  · obtain ⟨α, hα, he⟩ := Sp.exists_root_of_stdVec (n := n) (.negativeSum j i h)
    exact ⟨α, hα, by rw [he, stdVec, neg_one_smul, add_comm]⟩

theorem exists_root_diff {i j : Fin n} (hij : i ≠ j) {s : ℤ} (hs : s = 1 ∨ s = -1) :
    ∃ β ∈ roots (isFiniteType_cartanC n) ∅, toStd n β = s • (Pi.single i 1 - Pi.single j 1) := by
  rcases hs with rfl | rfl
  · obtain ⟨β, hβ, he⟩ := Sp.exists_root_of_stdVec (n := n) (.difference i j hij)
    exact ⟨β, hβ, by rw [he, stdVec, one_smul]⟩
  · obtain ⟨β, hβ, he⟩ := Sp.exists_root_of_stdVec (n := n) (.difference j i hij.symm)
    exact ⟨β, hβ, by rw [he, stdVec, neg_one_smul, neg_sub]⟩

include hcen in
theorem commPairing_eq_zero_long (hn : 2 ≤ n) (h2 : (2 : F) ≠ 0) {γ : Fin n → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanC n) ∅) {i : Fin n} {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hγi : toStd n γ = s • (2 • Pi.single i 1)) :
    TorusLift.commPairing hcen hπ (x_add (F := F) hγ) = 0 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  obtain ⟨j, hji⟩ := exists_ne i
  have hij : i ≠ j := hji.symm
  obtain ⟨α, hα, hαe⟩ := exists_root_sum hij hs
  obtain ⟨β, hβ, hβe⟩ := exists_root_diff hij hs
  have hγαβ : γ = α + β := toStd_inj (by
    rw [toStd_add', hαe, hβe, hγi]
    funext m
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring)
  subst hγαβ
  have hAi : toStd n α i = s := by
    rw [hαe, Pi.smul_apply, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, add_zero,
      smul_eq_mul, mul_one]
  have hBi : toStd n β i = s := by
    rw [hβe, Pi.smul_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, sub_zero,
      smul_eq_mul, mul_one]
  have hGi : toStd n (α + β) i = 2 * s := by
    rw [toStd_add', Pi.add_apply, hAi, hBi]
    ring
  have hne : ∀ v : Fin n → ℤ, toStd n v i ≠ 0 → v ≠ 0 := fun v hv h => hv (by
    rw [h]
    simp [toStd])
  have hαβ : α + β ≠ 0 := hne _ (by rw [hGi]; rcases hs with rfl | rfl <;> norm_num)
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (rootDatum n F).isFiniteType
    (Dv := (rootDatum n F).divisible) rfl
  have hC := Sp.commutatorFormula (n := n) (F := F) O
  have hp11 : (1, 1) ∈ expPairs (Sp.Φ n F) α β :=
    (Sp.mem_expPairs_iff hα hβ hαβ (1, 1)).2 ⟨by simp, by rw [one_smul, one_smul]; exact hγ⟩
  refine ChainPairing.commPairing_eq_zero_of_chain hcen hπ hC (x_add hγ) hα hβ hγ hαβ
    (ChainPairing.list_eq_singleton (O.nodup α β) fun p => ?_) ?_ (hne _ ?_) (hne _ ?_)
    (ChainPairing.list_eq_nil fun p hp => ?_) (ChainPairing.list_eq_nil fun p hp => ?_)
  · refine ((O.mem_iff α hα β hβ hαβ p).trans (Sp.mem_expPairs_iff hα hβ hαβ p)).trans ?_
    constructor
    · rintro ⟨hp, hr⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · rfl
      · exact absurd hr (notMem_roots_of_three_le (i := i) (by
          rw [toStd_comb_apply, hAi, hBi]
          rcases hs with rfl | rfl <;> norm_num))
      · exact absurd hr (notMem_roots_of_three_le (i := i) (by
          rw [toStd_comb_apply, hAi, hBi]
          rcases hs with rfl | rfl <;> norm_num))
    · rintro rfl
      exact (Sp.mem_expPairs_iff hα hβ hαβ (1, 1)).1 hp11
  · rcases Sp.commC_natAbs (F := F) hα hβ hp11 with h | h <;>
      rcases Int.natAbs_eq_iff.1 h with h' | h' <;> rw [h'] <;> push_cast
    · exact one_ne_zero
    · exact neg_ne_zero.2 one_ne_zero
    · exact h2
    · exact neg_ne_zero.2 h2
  · rw [toStd_add', Pi.add_apply, hGi, hAi]
    rcases hs with rfl | rfl <;> norm_num
  · rw [toStd_add', Pi.add_apply, hGi, hBi]
    rcases hs with rfl | rfl <;> norm_num
  · have hγα : α + β + α ≠ 0 := hne _ (by
      rw [toStd_add', Pi.add_apply, hGi, hAi]
      rcases hs with rfl | rfl <;> norm_num)
    obtain ⟨hp', hr⟩ := ((O.mem_iff _ hγ α hα hγα p).trans (Sp.mem_expPairs_iff hγ hα hγα p)).1 hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp'
    rcases hp' with rfl | rfl | rfl <;>
      exact notMem_roots_of_three_le (i := i) (by
        rw [toStd_comb_apply, hGi, hAi]
        rcases hs with rfl | rfl <;> norm_num) hr
  · have hγβ : α + β + β ≠ 0 := hne _ (by
      rw [toStd_add', Pi.add_apply, hGi, hBi]
      rcases hs with rfl | rfl <;> norm_num)
    obtain ⟨hp', hr⟩ := ((O.mem_iff _ hγ β hβ hγβ p).trans (Sp.mem_expPairs_iff hγ hβ hγβ p)).1 hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp'
    rcases hp' with rfl | rfl | rfl <;>
      exact notMem_roots_of_three_le (i := i) (by
        rw [toStd_comb_apply, hGi, hBi]
        rcases hs with rfl | rfl <;> norm_num) hr

theorem exists_tor_eq_of_apply {γ : Fin n → ℤ} {i : Fin n} {e : ℤ} (he : toStd n γ i = e)
    (he1 : e * e = 1) (u : Fˣ) : ∃ t : Fin n → Fˣ, chi (toStd n γ) t = u :=
  ⟨Function.update 1 i (u ^ e), by rw [chi_update, he, ← zpow_mul, he1, zpow_one]⟩

theorem long_or_short {γ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC n) ∅) :
    (∃ (i : Fin n) (s : ℤ), (s = 1 ∨ s = -1) ∧ toStd n γ = s • (2 • Pi.single i 1)) ∨
      ∃ i : Fin n, toStd n γ i = 1 ∨ toStd n γ i = -1 := by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hγ
  cases r with
  | positiveLong i => exact Or.inl ⟨i, 1, Or.inl rfl, by rw [← hr, stdVec, one_smul]⟩
  | negativeLong i => exact Or.inl ⟨i, -1, Or.inr rfl, by rw [← hr, stdVec, neg_one_smul]⟩
  | difference i j hij => exact Or.inr ⟨i, Or.inl (by rw [← hr, stdVec]; simp [hij])⟩
  | positiveSum i j hij => exact Or.inr ⟨i, Or.inl (by rw [← hr, stdVec]; simp [hij.ne])⟩
  | negativeSum i j hij => exact Or.inr ⟨i, Or.inr (by rw [← hr, stdVec]; simp [hij.ne])⟩

include hcen in
theorem commPairing_eq_zero_short [Finite F] (hF4 : Nat.card F ≠ 4) {γ : Fin n → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanC n) ∅) {i : Fin n}
    (hi : toStd n γ i = 1 ∨ toStd n γ i = -1) :
    TorusLift.commPairing hcen hπ (x_add (F := F) hγ) = 0 := by
  obtain ⟨p, _, _⟩ := TorusLift.exists_prime_charP (k := F)
  refine Pairing.pairing_eq_zero_of_units p hF4 (TorusLift.commPairing_self hcen hπ (x_add hγ))
    fun u hu s t => ?_
  have he1 : toStd n γ i * toStd n γ i = 1 := by rcases hi with h | h <;> rw [h] <;> norm_num
  obtain ⟨t', ht'⟩ := exists_tor_eq_of_apply rfl he1 (Units.mk0 u hu)
  refine TorusLift.commPairing_smul hcen hπ (x_add hγ) (g := tor F t') (fun c => ?_) s t
  rw [tor_conj_x hγ, ht', Units.val_mk0]

include hcen in
theorem commPairing_eq_zero' [Finite F] (hn : 2 ≤ n) (hF : 5 ≤ Nat.card F) {γ : Fin n → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanC n) ∅) :
    TorusLift.commPairing hcen hπ (x_add (F := F) hγ) = 0 := by
  rcases long_or_short hγ with ⟨i, s, hs, hγi⟩ | ⟨i, hi⟩
  · by_cases h2 : (2 : F) = 0
    · refine commPairing_eq_zero hcen hπ (by omega) (fun h9 => ?_) hγ
      have := (SpinTorus.two_eq_zero_iff_even_card).1 h2
      rw [h9] at this
      exact absurd this (by decide)
    · exact commPairing_eq_zero_long hcen hπ hn h2 hγ hs hγi
  · exact commPairing_eq_zero_short hcen hπ (by omega) hγ hi

variable (π) in
open _root_.Classical in
@[expose] noncomputable def X (γ : Fin n → ℤ) : F → E :=
  if h : ∃ Y : F → E, IsRootLift π γ Y then h.choose else fun _ => 1

theorem X_isRootLift {γ : Fin n → ℤ} (h : ∃ Y : F → E, IsRootLift π γ Y) :
    IsRootLift π γ (X π γ) := by
  classical
  rw [X, dite_eq_left h]
  exact h.choose_spec

end Lift

theorem sp_exists_section_of_central [Finite F] (hn : 2 ≤ n) (hF : 5 ≤ Nat.card F)
    {E : Type*} [Group E] {π : E →* StatedSp n F}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : StatedSp n F →* E, ∀ g, π (σ g) = g := by
  obtain ⟨w, hw2, -⟩ := SLClosed.exists_unit_sq_cube_ne_one hF
  have hw : w ^ 2 ≠ 1 := fun h => hw2 (by rw [← Units.val_pow_eq_pow_val, h, Units.val_one])
  have hspec : ∀ γ ∈ roots (isFiniteType_cartanC n) ∅, IsRootLift π γ (X π γ) := fun γ hγ => by
    obtain ⟨t, ht⟩ := exists_tor_ne_one hγ hw
    exact X_isRootLift (exists_isRootLift_of_pairing hcen hπ hγ
      (commPairing_eq_zero' hcen hπ hn hF hγ) ht)
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (rootDatum n F).isFiniteType
    (Dv := (rootDatum n F).divisible) rfl
  refine HalfSpaceLift.exists_section_of_lift hcen rfl
    (Sp.chevalleyExtras hn O Sp.commC (Sp.commutatorFormula O)) (Sp.presentationB hn)
    (X := X π) (tor := fun t : Fin n → Fˣ => TorusLift.lift hπ (tor F t))
    (χ := fun t γ => (chi (toStd n γ) t : F)) (fun γ hγ => (hspec γ hγ).1)
    (fun γ hγ => (hspec γ hγ).2.1)
    (fun t γ hγ c => (hspec γ hγ).2.2 t _ (TorusLift.map_lift hπ _) c)
    fun γ hγ δ hδ hli => ?_
  obtain ⟨t, h1, h2⟩ := exists_tor_sep hγ hδ hli hw
  exact ⟨t, by rw [h1, Units.val_one], fun h => h2 (Units.val_eq_one.1 h)⟩

end CFSG.LieType.Steinberg.CentralExt.SpClosed

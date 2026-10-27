module

public import CFSG.Assembly.Defs

public section

namespace CFSG.QuasithinUnique.L246A7

open scoped commutatorElement

section TwoGroups

theorem commutative_of_card_le_four {Γ : Type*} [Group Γ] [Finite Γ] (hΓ : IsPGroup 2 Γ)
    (h4 : Nat.card Γ ≤ 4) : ∀ a b : Γ, a * b = b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hΓ.exists_card_eq
  have hn2 : n ≤ 2 := by
    by_contra h
    push Not at h
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
    omega
  interval_cases n
  ·
    have h1 : Nat.card Γ = 1 := by simpa using hn
    have : Subsingleton Γ := (Nat.card_eq_one_iff_unique.1 h1).1
    intro a b
    exact Subsingleton.elim _ _
  · have h2 : Nat.card Γ = 2 := by simpa using hn
    have : IsCyclic Γ := isCyclic_of_prime_card (p := 2) h2
    have hc : IsMulCommutative Γ := IsCyclic.isMulCommutative
    intro a b
    exact IsMulCommutative.is_comm.comm a b
  · have hc : IsMulCommutative Γ :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by simpa using hn)
    intro a b
    exact IsMulCommutative.is_comm.comm a b

theorem commutator_commutator_eq_bot_of_card_le_eight {Γ : Type*} [Group Γ] [Finite Γ]
    (hΓ : IsPGroup 2 Γ) (h8 : Nat.card Γ ≤ 8) :
    ⁅⁅(⊤ : Subgroup Γ), (⊤ : Subgroup Γ)⁆, (⊤ : Subgroup Γ)⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases h4 : Nat.card Γ ≤ 4
  · have hc := commutative_of_card_le_four hΓ h4
    have h1 : ⁅(⊤ : Subgroup Γ), (⊤ : Subgroup Γ)⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro a _ b _
      simp [commutatorElement_def, hc a b]
    rw [h1, Subgroup.commutator_bot_left]
  · push Not at h4
    obtain ⟨n, hn⟩ := hΓ.exists_card_eq
    have hn3 : n = 3 := by
      have h5 : 2 ^ 2 < 2 ^ n := by omega
      have h6 : n ≤ 3 := by
        by_contra h
        push Not at h
        have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
        omega
      have h7 : 2 < n := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h5
      omega
    subst hn3
    have : Nontrivial Γ := by
      rw [← Finite.one_lt_card_iff_nontrivial]
      omega
    have := hΓ.center_nontrivial
    set Z := Subgroup.center Γ with hZ
    have hZcard : 2 ≤ Nat.card Z := by
      have : 1 < Nat.card Z := Finite.one_lt_card_iff_nontrivial.2 inferInstance
      omega
    have hquot : Nat.card (Γ ⧸ Z) ≤ 4 := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
      have h2 : Nat.card (Γ ⧸ Z) * 2 ≤ Nat.card (Γ ⧸ Z) * Nat.card Z :=
        Nat.mul_le_mul_left _ hZcard
      omega
    have hcq := commutative_of_card_le_four (hΓ.to_quotient Z) hquot
    have h1 : ⁅(⊤ : Subgroup Γ), (⊤ : Subgroup Γ)⁆ ≤ Z := by
      rw [Subgroup.commutator_le]
      intro a _ b _
      have h := hcq (QuotientGroup.mk a) (QuotientGroup.mk b)
      have : ((⁅a, b⁆ : Γ) : Γ ⧸ Z) = 1 := by
        simp only [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        rw [h]
        group
      exact (QuotientGroup.eq_one_iff _).1 this
    rw [eq_bot_iff]
    refine (Subgroup.commutator_mono h1 le_rfl).trans ?_
    rw [Subgroup.commutator_le]
    intro z hz b _
    have h := Subgroup.mem_center_iff.1 hz b
    rw [commutatorElement_def, show z * b = b * z from h.symm]
    simp

end TwoGroups

section A4Action

variable {G : Type*} [Group G]

@[expose] def psi (y v : G) (n : ℕ) : G := y ^ n * v * (y ^ n)⁻¹

theorem psi_add (y v : G) (n m : ℕ) : psi y v (n + m) = psi y (psi y v m) n := by
  unfold psi
  rw [pow_add, mul_inv_rev]
  group

theorem psi_one (y v : G) : psi y v 1 = y * v * y⁻¹ := by simp [psi]

theorem psi_zero (y v : G) : psi y v 0 = v := by simp [psi]

theorem psi_mod {y : G} (hy3 : y ^ 3 = 1) (v : G) (n : ℕ) : psi y v n = psi y v (n % 3) := by
  have : y ^ n = y ^ (n % 3) := by
    conv_lhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hy3, one_pow, mul_one]
  simp [psi, this]

theorem psi_injective (y : G) (n : ℕ) : Function.Injective (psi y · n) := by
  intro a b h
  have h' : y ^ n * a * (y ^ n)⁻¹ = y ^ n * b * (y ^ n)⁻¹ := h
  simpa using h'

structure A4Act (T V : Subgroup G) (y : G) : Prop where
  hT : IsPGroup 2 T
  hy3 : y ^ 3 = 1
  hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a
  hV4 : Nat.card V ≤ 4
  hyV : ∀ v ∈ V, y * v * y⁻¹ ∈ V
  hfpf : ∀ v ∈ V, y * v * y⁻¹ = v → v = 1
  hTV : ∀ t ∈ T, ∀ v ∈ V, t * v * t⁻¹ ∈ V
  hTy : ∀ t ∈ T, ∃ v ∈ V, t * y * t⁻¹ = v * y ∨ t * y * t⁻¹ = v * y⁻¹

namespace A4Act

variable {T V : Subgroup G} {y : G}

@[expose] def Y (_ : A4Act T V y) : Subgroup G := V ⊔ Subgroup.zpowers y

theorem psi_mem (h : A4Act T V y) {v : G} (hv : v ∈ V) (n : ℕ) : psi y v n ∈ V := by
  induction n with
  | zero => simpa [psi_zero] using hv
  | succ n ih =>
    rw [add_comm, psi_add, psi_one]
    exact h.hyV _ (by simpa [psi_zero] using ih)

theorem psi_ne (h : A4Act T V y) {v : G} (hv : v ∈ V) (h1 : v ≠ 1) :
    psi y v 1 ≠ v ∧ psi y v 2 ≠ v := by
  have hy1 : psi y v 1 ≠ v := fun h2 => h1 (h.hfpf v hv (by simpa [psi_one] using h2))
  refine ⟨hy1, fun h2 => hy1 ?_⟩
  have h3 : psi y v 3 = v := by
    rw [psi_mod h.hy3, show (3 : ℕ) % 3 = 0 by norm_num, psi_zero]
  have e : psi y v 3 = psi y (psi y v 2) 1 := by
    rw [show (3 : ℕ) = 1 + 2 by norm_num, psi_add]
  rw [h3, h2] at e
  exact e.symm

theorem V_le_Y (h : A4Act T V y) : V ≤ h.Y := le_sup_left

theorem y_mem_Y (h : A4Act T V y) : y ∈ h.Y := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)

theorem conj_mem_Y (h : A4Act T V y) {t : G} (htT : t ∈ T) {g : G} (hg : g ∈ h.Y) :
    t * g * t⁻¹ ∈ h.Y := by
  have hle : h.Y ≤ h.Y.comap (MulAut.conj t).toMonoidHom := by
    refine sup_le (fun v hv => ?_) (Subgroup.zpowers_le.2 ?_)
    · exact h.V_le_Y (h.hTV t htT v hv)
    · obtain ⟨u, hu, hu'⟩ := h.hTy t htT
      show t * y * t⁻¹ ∈ h.Y
      rcases hu' with e | e
      · rw [e]
        exact h.Y.mul_mem (h.V_le_Y hu) h.y_mem_Y
      · rw [e]
        exact h.Y.mul_mem (h.V_le_Y hu) (h.Y.inv_mem h.y_mem_Y)
  exact hle hg

theorem mem_centralizer_Y (h : A4Act T V y) {t : G} :
    t ∈ Subgroup.centralizer (h.Y : Set G) ↔ (∀ x ∈ V, x * t = t * x) ∧ y * t = t * y := by
  constructor
  · intro ht
    exact ⟨fun x hx => Subgroup.mem_centralizer_iff.1 ht x (h.V_le_Y hx),
      Subgroup.mem_centralizer_iff.1 ht y h.y_mem_Y⟩
  · rintro ⟨hV, hy⟩
    have hle : h.Y ≤ Subgroup.centralizer ({t} : Set G) := by
      refine sup_le (fun x hx => ?_) (Subgroup.zpowers_le.2 ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro s hs
        rw [Set.mem_singleton_iff.1 hs]
        exact (hV x hx).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro s hs
        rw [Set.mem_singleton_iff.1 hs]
        exact hy.symm
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have := Subgroup.mem_centralizer_iff.1 (hle hg) t (Set.mem_singleton t)
    exact this.symm

@[expose] def T2 (h : A4Act T V y) : Subgroup G where
  carrier := {t | t ∈ T ∧ ∃ u ∈ V, t * y * t⁻¹ = u * y}
  one_mem' := ⟨T.one_mem, 1, V.one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨haT, ua, hua, ha⟩ ⟨hbT, ub, hub, hb⟩
    refine ⟨T.mul_mem haT hbT, (a * ub * a⁻¹) * ua, V.mul_mem (h.hTV a haT ub hub) hua, ?_⟩
    calc a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by group
      _ = a * (ub * y) * a⁻¹ := by rw [hb]
      _ = (a * ub * a⁻¹) * (a * y * a⁻¹) := by group
      _ = (a * ub * a⁻¹) * (ua * y) := by rw [ha]
      _ = (a * ub * a⁻¹) * ua * y := by group
  inv_mem' := by
    rintro a ⟨haT, ua, hua, ha⟩
    refine ⟨T.inv_mem haT, (a⁻¹ * ua * a)⁻¹, V.inv_mem (by
      simpa using h.hTV a⁻¹ (T.inv_mem haT) ua hua), ?_⟩
    have e : y = (a⁻¹ * ua * a) * (a⁻¹ * y * a) := by
      calc y = a⁻¹ * (a * y * a⁻¹) * a := by group
        _ = a⁻¹ * (ua * y) * a := by rw [ha]
        _ = (a⁻¹ * ua * a) * (a⁻¹ * y * a) := by group
    calc a⁻¹ * y * a⁻¹⁻¹ = a⁻¹ * y * a := by rw [inv_inv]
      _ = (a⁻¹ * ua * a)⁻¹ * ((a⁻¹ * ua * a) * (a⁻¹ * y * a)) := by group
      _ = (a⁻¹ * ua * a)⁻¹ * y := by rw [← e]

theorem T2_le (h : A4Act T V y) : h.T2 ≤ T := fun _ ht => ht.1

theorem exists_inv_of_notMem (h : A4Act T V y) {s : G} (hsT : s ∈ T) (hs : s ∉ h.T2) :
    ∃ u ∈ V, s * y * s⁻¹ = u * y⁻¹ := by
  obtain ⟨u, hu, e | e⟩ := h.hTy s hsT
  · exact absurd ⟨hsT, u, hu, e⟩ hs
  · exact ⟨u, hu, e⟩

theorem mul_mem_T2 (h : A4Act T V y) {s t : G} (hsT : s ∈ T) (htT : t ∈ T) (hs : s ∉ h.T2)
    (ht : t ∉ h.T2) : s⁻¹ * t ∈ h.T2 := by
  obtain ⟨u, hu, e1⟩ := h.exists_inv_of_notMem htT ht
  have hs' : s⁻¹ ∉ h.T2 := fun h' => hs (by simpa using h.T2.inv_mem h')
  obtain ⟨u', hu', e2⟩ := h.exists_inv_of_notMem (T.inv_mem hsT) hs'
  refine ⟨T.mul_mem (T.inv_mem hsT) htT, (s⁻¹ * u * s) * (y * u'⁻¹ * y⁻¹),
    V.mul_mem (by simpa using h.hTV s⁻¹ (T.inv_mem hsT) u hu)
      (h.hyV _ (V.inv_mem hu')), ?_⟩
  rw [inv_inv] at e2
  calc s⁻¹ * t * y * (s⁻¹ * t)⁻¹ = s⁻¹ * (t * y * t⁻¹) * s := by group
    _ = s⁻¹ * (u * y⁻¹) * s := by rw [e1]
    _ = (s⁻¹ * u * s) * (s⁻¹ * y * s)⁻¹ := by group
    _ = (s⁻¹ * u * s) * (u' * y⁻¹)⁻¹ := by rw [e2]
    _ = (s⁻¹ * u * s) * (y * u'⁻¹ * y⁻¹) * y := by group

theorem relIndex_T2_le (h : A4Act T V y) : h.T2.relIndex T ≤ 2 := by
  by_cases hT : T ≤ h.T2
  · rw [(Subgroup.relIndex_eq_one).2 hT]
    norm_num
  · obtain ⟨s, hsT, hs⟩ := IsConcreteLE.not_le_iff_exists.1 hT
    have : h.T2.relIndex T = 2 := by
      rw [Subgroup.relIndex_eq_two_iff]
      refine ⟨s, hsT, fun b hb => ?_⟩
      by_cases hbT2 : b ∈ h.T2
      · right
        refine ⟨hbT2, fun hbs => hs ?_⟩
        have := h.T2.mul_mem (h.T2.inv_mem hbT2) hbs
        simpa using this
      · left
        refine ⟨?_, hbT2⟩
        have := h.mul_mem_T2 (T.inv_mem hb) hsT (fun h' => hbT2 (by simpa using h.T2.inv_mem h')) hs
        simpa using this
    omega

variable [Finite G]

theorem eq_orbit (h : A4Act T V y) {v₀ : G} (hv₀ : v₀ ∈ V) (h1 : v₀ ≠ 1) :
    ∀ w ∈ V, w = 1 ∨ w = v₀ ∨ w = psi y v₀ 1 ∨ w = psi y v₀ 2 := by
  classical
  intro w hw
  by_contra hcon
  push Not at hcon
  obtain ⟨hw1, hw2, hw3, hw4⟩ := hcon
  have haV : psi y v₀ 1 ∈ V := h.psi_mem hv₀ 1
  have hbV : psi y v₀ 2 ∈ V := h.psi_mem hv₀ 2
  obtain ⟨d4, d5⟩ := h.psi_ne hv₀ h1
  have d2 : (1 : G) ≠ psi y v₀ 1 := by
    intro h2
    apply h1
    apply psi_injective y 1
    simp only [psi_one] at h2 ⊢
    rw [← h2]
    simp
  have d3 : (1 : G) ≠ psi y v₀ 2 := by
    intro h2
    apply h1
    apply psi_injective y 2
    show psi y v₀ 2 = psi y 1 2
    rw [← h2]
    simp [psi]
  have d6 : psi y v₀ 1 ≠ psi y v₀ 2 := by
    intro h2
    apply d4
    have e : psi y v₀ 2 = psi y (psi y v₀ 1) 1 := by
      rw [show (2 : ℕ) = 1 + 1 by norm_num, psi_add]
    rw [e] at h2
    exact (psi_injective y 1 h2).symm
  have hF : ({1, v₀, psi y v₀ 1, psi y v₀ 2, w} : Finset G).card = 5 := by
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨h1.symm, d2, d3, hw1.symm⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨d4.symm, d5.symm, hw2.symm⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨d6, hw3.symm⟩),
      Finset.card_pair hw4.symm]
  have hsub : (({1, v₀, psi y v₀ 1, psi y v₀ 2, w} : Finset G) : Set G) ⊆ (V : Set G) := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact V.one_mem
    · exact hv₀
    · exact haV
    · exact hbV
    · exact hw
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, hF] at hle
  have h5 : (V : Set G).ncard = Nat.card V := (Nat.card_coe_set_eq (V : Set G)).symm
  have := h.hV4
  omega

theorem centralizes (h : A4Act T V y) {t : G} (htT : t ∈ T) {u : G} (hu : u ∈ V)
    (htu : t * y * t⁻¹ = u * y) : ∀ x ∈ V, t * x * t⁻¹ = x := by
  classical
  have hcomm1 : ∀ x ∈ V, t * (y * x * y⁻¹) * t⁻¹ = y * (t * x * t⁻¹) * y⁻¹ := by
    intro x hx
    have hθx : t * x * t⁻¹ ∈ V := h.hTV t htT x hx
    have hz : y * (t * x * t⁻¹) * y⁻¹ ∈ V := h.hyV _ hθx
    have e1 : t * (y * x * y⁻¹) * t⁻¹ = (t * y * t⁻¹) * (t * x * t⁻¹) * (t * y * t⁻¹)⁻¹ := by
      group
    rw [e1, htu]
    have e2 : u * y * (t * x * t⁻¹) * (u * y)⁻¹ = u * (y * (t * x * t⁻¹) * y⁻¹) * u⁻¹ := by group
    rw [e2, h.hVab u hu _ hz, mul_assoc, mul_inv_cancel, mul_one]
  have hcommn : ∀ n : ℕ, ∀ x ∈ V, t * psi y x n * t⁻¹ = psi y (t * x * t⁻¹) n := by
    intro n
    induction n with
    | zero => intro x hx; simp [psi_zero]
    | succ n ih =>
      intro x hx
      rw [add_comm, psi_add, psi_one, psi_add, psi_one]
      rw [hcomm1 _ (h.psi_mem hx n), ih x hx]
  by_cases hV : ∀ x ∈ V, x = 1
  · intro x hx
    rw [hV x hx]
    simp
  push Not at hV
  obtain ⟨v₀, hv₀, h1⟩ := hV
  have hθv₀ : t * v₀ * t⁻¹ ∈ V := h.hTV t htT v₀ hv₀
  have hθ1 : t * v₀ * t⁻¹ ≠ 1 := by
    intro h2
    apply h1
    have : t⁻¹ * (t * v₀ * t⁻¹) * t = v₀ := by group
    rw [← this, h2]
    group
  obtain ⟨k, hk3, hk⟩ : ∃ k : ℕ, k < 3 ∧ t * v₀ * t⁻¹ = psi y v₀ k := by
    rcases h.eq_orbit hv₀ h1 _ hθv₀ with h2 | h2 | h2 | h2
    · exact absurd h2 hθ1
    · exact ⟨0, by norm_num, by rw [psi_zero]; exact h2⟩
    · exact ⟨1, by norm_num, h2⟩
    · exact ⟨2, by norm_num, h2⟩
  have hk0 : k = 0 := by
    by_contra hk0
    have hiter : ∀ j : ℕ, t ^ j * v₀ * (t ^ j)⁻¹ = psi y v₀ (k * j) := by
      intro j
      induction j with
      | zero => simp [psi_zero]
      | succ j ih =>
        have e : t ^ (j + 1) * v₀ * (t ^ (j + 1))⁻¹ = t * (t ^ j * v₀ * (t ^ j)⁻¹) * t⁻¹ := by
          rw [pow_succ', mul_inv_rev]
          group
        rw [e, ih, hcommn _ v₀ hv₀, hk, show k * (j + 1) = k * j + k by ring, psi_add]
    obtain ⟨m, hm⟩ := h.hT ⟨t, htT⟩
    have hm' : t ^ 2 ^ m = 1 := congrArg Subtype.val hm
    have h2 := hiter (2 ^ m)
    rw [hm'] at h2
    simp only [one_mul, inv_one, mul_one] at h2
    have hr : (k * 2 ^ m) % 3 ≠ 0 := by
      intro h0
      have h3 : 3 ∣ k * 2 ^ m := Nat.dvd_of_mod_eq_zero h0
      rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h4 | h4
      · omega
      · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h4
        omega
    rw [psi_mod h.hy3] at h2
    obtain ⟨d1, d2⟩ := h.psi_ne hv₀ h1
    have hr3 : (k * 2 ^ m) % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have hcase : (k * 2 ^ m) % 3 = 1 ∨ (k * 2 ^ m) % 3 = 2 := by omega
    rcases hcase with hc | hc
    · rw [hc] at h2
      exact d1 h2.symm
    · rw [hc] at h2
      exact d2 h2.symm
  subst hk0
  rw [psi_zero] at hk
  intro x hx
  rcases h.eq_orbit hv₀ h1 x hx with h2 | h2 | h2 | h2
  · rw [h2]; simp
  · rw [h2]; exact hk
  · rw [h2, hcommn 1 v₀ hv₀, hk]
  · rw [h2, hcommn 2 v₀ hv₀, hk]

theorem T2_centralizes (h : A4Act T V y) {t : G} (ht : t ∈ h.T2) :
    ∀ x ∈ V, t * x * t⁻¹ = x := by
  obtain ⟨htT, u, hu, e⟩ := ht
  exact h.centralizes htT hu e

@[expose] def D (h : A4Act T V y) : Subgroup G := T ⊓ Subgroup.centralizer (h.Y : Set G)

omit [Finite G] in
theorem D_le_T (h : A4Act T V y) : h.D ≤ T := inf_le_left

omit [Finite G] in
theorem D_le_T2 (h : A4Act T V y) : h.D ≤ h.T2 := by
  rintro t ⟨htT, htc⟩
  refine ⟨htT, 1, V.one_mem, ?_⟩
  have hty : y * t = t * y := ((h.mem_centralizer_Y).1 htc).2
  rw [one_mul]
  calc t * y * t⁻¹ = y * t * t⁻¹ := by rw [← hty]
    _ = y := by group

@[expose] def fT2 (h : A4Act T V y) : ↥h.T2 →* ↥V :=
  MonoidHom.mk' (fun t => ⟨(t : G) * y * (t : G)⁻¹ * y⁻¹, by
      obtain ⟨u, hu, e⟩ := t.2.2
      rw [e]
      simpa using hu⟩) (by
    intro a b
    apply Subtype.ext
    obtain ⟨ua, hua, ea⟩ := a.2.2
    obtain ⟨ub, hub, eb⟩ := b.2.2
    have hcb : (a : G) * ub * (a : G)⁻¹ = ub := h.centralizes a.2.1 hua ea ub hub
    show ((a * b : ↥h.T2) : G) * y * ((a * b : ↥h.T2) : G)⁻¹ * y⁻¹ =
      ((a : G) * y * (a : G)⁻¹ * y⁻¹) * ((b : G) * y * (b : G)⁻¹ * y⁻¹)
    have e1 : ((a * b : ↥h.T2) : G) * y * ((a * b : ↥h.T2) : G)⁻¹ * y⁻¹ = ub * ua := by
      calc ((a * b : ↥h.T2) : G) * y * ((a * b : ↥h.T2) : G)⁻¹ * y⁻¹
          = (a : G) * ((b : G) * y * (b : G)⁻¹) * (a : G)⁻¹ * y⁻¹ := by
            simp only [Subgroup.coe_mul]
            group
        _ = (a : G) * (ub * y) * (a : G)⁻¹ * y⁻¹ := by rw [eb]
        _ = ((a : G) * ub * (a : G)⁻¹) * ((a : G) * y * (a : G)⁻¹) * y⁻¹ := by group
        _ = ub * (ua * y) * y⁻¹ := by rw [hcb, ea]
        _ = ub * ua := by group
    have e2 : ((a : G) * y * (a : G)⁻¹ * y⁻¹) * ((b : G) * y * (b : G)⁻¹ * y⁻¹) = ua * ub := by
      rw [ea, eb]
      group
    rw [e1, e2]
    exact h.hVab ub hub ua hua)

theorem fT2_apply (h : A4Act T V y) (t : ↥h.T2) :
    ((h.fT2 t : ↥V) : G) = (t : G) * y * (t : G)⁻¹ * y⁻¹ := rfl

theorem fT2_ker (h : A4Act T V y) : h.fT2.ker = h.D.subgroupOf h.T2 := by
  ext t
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro ht
    have h1 : (t : G) * y * (t : G)⁻¹ * y⁻¹ = 1 := by
      have := congrArg Subtype.val ht
      simpa [fT2_apply] using this
    have hty : y * (t : G) = (t : G) * y := by
      have h2 : (t : G) * y * (t : G)⁻¹ = y := by
        calc (t : G) * y * (t : G)⁻¹ = ((t : G) * y * (t : G)⁻¹ * y⁻¹) * y := by group
          _ = y := by rw [h1, one_mul]
      calc y * (t : G) = ((t : G) * y * (t : G)⁻¹) * (t : G) := by rw [h2]
        _ = (t : G) * y := by group
    refine ⟨t.2.1, (h.mem_centralizer_Y).2 ⟨fun x hx => ?_, hty⟩⟩
    have := h.T2_centralizes t.2 x hx
    calc x * (t : G) = ((t : G) * x * (t : G)⁻¹) * (t : G) := by rw [this]
      _ = (t : G) * x := by group
  · rintro ⟨htT, htc⟩
    apply Subtype.ext
    have hty : y * (t : G) = (t : G) * y := ((h.mem_centralizer_Y).1 htc).2
    show (t : G) * y * (t : G)⁻¹ * y⁻¹ = 1
    calc (t : G) * y * (t : G)⁻¹ * y⁻¹ = y * (t : G) * (t : G)⁻¹ * y⁻¹ := by rw [← hty]
      _ = 1 := by group

theorem relIndex_D_T2_le (h : A4Act T V y) : h.D.relIndex h.T2 ≤ 4 := by
  rw [Subgroup.relIndex, ← h.fT2_ker, Subgroup.index_ker]
  have h1 : Nat.card h.fT2.range ≤ Nat.card V :=
    Nat.card_le_card_of_injective (Subtype.val : h.fT2.range → V) Subtype.val_injective
  exact h1.trans h.hV4

theorem relIndex_D_le (h : A4Act T V y) : h.D.relIndex T ≤ 8 := by
  rw [← Subgroup.relIndex_mul_relIndex h.D h.T2 T h.D_le_T2 h.T2_le]
  exact (Nat.mul_le_mul h.relIndex_D_T2_le h.relIndex_T2_le).trans (by norm_num)

omit [Finite G] in
theorem D_normal (h : A4Act T V y) : (h.D.subgroupOf T).Normal := by
  rw [Subgroup.normal_subgroupOf_iff h.D_le_T]
  intro d k hd hk
  refine ⟨T.mul_mem (T.mul_mem hk hd.1) (T.inv_mem hk), ?_⟩
  show k * d * k⁻¹ ∈ Subgroup.centralizer (h.Y : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have hg' : k⁻¹ * g * k ∈ h.Y := by simpa using h.conj_mem_Y (T.inv_mem hk) hg
  have hcomm := Subgroup.mem_centralizer_iff.1 hd.2 _ hg'
  calc g * (k * d * k⁻¹) = k * ((k⁻¹ * g * k) * d) * k⁻¹ := by group
    _ = k * (d * (k⁻¹ * g * k)) * k⁻¹ := by rw [hcomm]
    _ = (k * d * k⁻¹) * g := by group

theorem class_two (h : A4Act T V y) : ⁅⁅T, T⁆, T⁆ ≤ Subgroup.centralizer (h.Y : Set G) := by
  have hn := h.D_normal
  set N := h.D.subgroupOf T with hN
  have hΓ2 : IsPGroup 2 (↥T ⧸ N) := h.hT.to_quotient N
  have hΓ8 : Nat.card (↥T ⧸ N) ≤ 8 := by
    rw [← Subgroup.index_eq_card]
    exact h.relIndex_D_le
  have hcc := commutator_commutator_eq_bot_of_card_le_eight hΓ2 hΓ8
  have hC : ⁅⁅(⊤ : Subgroup ↥T), (⊤ : Subgroup ↥T)⁆, (⊤ : Subgroup ↥T)⁆ ≤ N := by
    have hmap : Subgroup.map (QuotientGroup.mk' N)
        ⁅⁅(⊤ : Subgroup ↥T), (⊤ : Subgroup ↥T)⁆, (⊤ : Subgroup ↥T)⁆ = ⊥ := by
      rw [Subgroup.map_commutator, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)]
      exact hcc
    have := (Subgroup.map_eq_bot_iff _).1 hmap
    rwa [QuotientGroup.ker_mk'] at this
  have hTop : (⊤ : Subgroup ↥T).map T.subtype = T := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have heq : ⁅⁅T, T⁆, T⁆ = Subgroup.map T.subtype
      ⁅⁅(⊤ : Subgroup ↥T), (⊤ : Subgroup ↥T)⁆, (⊤ : Subgroup ↥T)⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator, hTop]
  rw [heq]
  refine (Subgroup.map_mono hC).trans ?_
  rw [hN, Subgroup.map_subgroupOf_eq_of_le h.D_le_T]
  exact inf_le_right

end A4Act

end A4Action

end CFSG.QuasithinUnique.L246A7

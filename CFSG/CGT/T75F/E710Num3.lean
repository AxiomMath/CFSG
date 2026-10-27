module

public import CFSG.CGT.T75F.E710Num2
public import CFSG.CGT.T75F.E710Fib

public section

namespace CFSG.CGT.T75F

theorem arith710 (q r φ : ℕ) (hq : 4 ≤ q) (hr : 1 ≤ r) (hφ1 : 1 ≤ φ) (hφ2 : φ ≤ q ^ 2)
    (heq : (q ^ 2 * r - 1) * φ = (q + 1) * (q ^ 2 - 1)) : r = 1 ∧ φ = q + 1 := by
  have hq2 : 16 ≤ q ^ 2 := by nlinarith
  have hqr : 1 ≤ q ^ 2 * r := by nlinarith
  have heqZ : ((q : ℤ) ^ 2 * r - 1) * φ = (q + 1) * ((q : ℤ) ^ 2 - 1) := by
    have h1 := congrArg (fun n : ℕ => (n : ℤ)) heq
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h1
    rw [Nat.cast_sub hqr, Nat.cast_sub (by omega : 1 ≤ q ^ 2)] at h1
    push_cast at h1
    linarith
  set k : ℤ := (r : ℤ) * φ with hk
  have hkey : (q : ℤ) ^ 2 * (k - (q + 1)) = φ - (q + 1) := by
    rw [hk]
    nlinarith
  have hq2Z : (16 : ℤ) ≤ (q : ℤ) ^ 2 := by exact_mod_cast hq2
  have hφ1Z : (1 : ℤ) ≤ φ := by exact_mod_cast hφ1
  have hφ2Z : (φ : ℤ) ≤ (q : ℤ) ^ 2 := by exact_mod_cast hφ2
  have hqZ : (4 : ℤ) ≤ q := by exact_mod_cast hq
  have hk0 : k - (q + 1) = 0 := by
    rcases lt_trichotomy (k - (q + 1)) 0 with ht | ht | ht
    · exfalso
      nlinarith
    · exact ht
    · exfalso
      nlinarith
  have hφ : (φ : ℤ) = q + 1 := by
    rw [hk0, mul_zero] at hkey
    linarith
  have hφN : φ = q + 1 := by exact_mod_cast hφ
  refine ⟨?_, hφN⟩
  have hkq : (r : ℤ) * φ = q + 1 := by linarith
  rw [hφ] at hkq
  have hpos : (0 : ℤ) < (q : ℤ) + 1 := by linarith
  have : (r : ℤ) = 1 := by
    have := mul_right_cancel₀ hpos.ne' (by linarith : (r : ℤ) * (q + 1) = 1 * (q + 1))
    exact this
  exact_mod_cast this

variable {X : Type} [Group X] [Finite X] {D : Set X} {M L : Subgroup X} {q : ℕ}

@[expose] def fib (D : Set X) (M : Subgroup X) (ω : X ⧸ Subgroup.center X) : Set X :=
  {β | β ∈ D ∧ β ∈ M ∧ (QuotientGroup.mk β : X ⧸ Subgroup.center X) = ω}

namespace Endgame710

variable (h : Endgame710 D M L q)

include h in
theorem psi_inj_L {l l' : X} (hl : l ∈ L) (hl' : l' ∈ L)
    (heq : (QuotientGroup.mk l : X ⧸ Subgroup.center X) = QuotientGroup.mk l') : l = l' := by
  have hz : l⁻¹ * l' ∈ Subgroup.center X := QuotientGroup.eq.1 heq
  by_contra hne
  have hne1 : l⁻¹ * l' ≠ 1 := fun h1 => hne (inv_mul_eq_one.1 h1)
  exact h.not_mem_center (h.L_D _ (L.mul_mem (L.inv_mem hl) hl') hne1) hz

include h in
theorem L_inf_center {l : X} (hl : l ∈ L) (hz : l ∈ Subgroup.center X) : l = 1 := by
  by_contra hne
  exact h.not_mem_center (h.L_D l hl hne) hz

include h in
theorem card_Z_mul : Nat.card (M ⊓ Subgroup.center X : Subgroup X) *
    Nat.card (Mhat M) = q ^ 4 := by
  let f : ↥M →* X ⧸ Subgroup.center X := (QuotientGroup.mk' (Subgroup.center X)).comp M.subtype
  have hrange : f.range = Mhat M := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hker : Nat.card f.ker = Nat.card (M ⊓ Subgroup.center X : Subgroup X) := by
    refine Nat.card_congr ?_
    exact
      { toFun := fun x => ⟨(x : X), x.1.2, (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 x.2)⟩
        invFun := fun z => ⟨⟨(z : X), z.2.1⟩,
          MonoidHom.mem_ker.2 ((QuotientGroup.eq_one_iff _).2 z.2.2)⟩
        left_inv := fun x => rfl
        right_inv := fun z => rfl }
  have := Subgroup.card_ker_mul_card_range f
  rw [hker, hrange, h.M_card] at this
  exact this

omit [Finite X] h in
theorem psi_mem_Mhat {β : X} (hβ : β ∈ M) : (QuotientGroup.mk β : X ⧸ Subgroup.center X) ∈ Mhat M :=
  Subgroup.mem_map.2 ⟨β, hβ, rfl⟩

include h in
theorem q_sq_le_card_Mhat : q ^ 2 ≤ Nat.card (Mhat M) := by
  have hinj : Function.Injective (fun l : L => (⟨(QuotientGroup.mk (l : X) : X ⧸ Subgroup.center X),
      psi_mem_Mhat (h.L_le l.2)⟩ : Mhat M)) := by
    intro a b hab
    apply Subtype.ext
    exact h.psi_inj_L a.2 b.2 (congrArg Subtype.val hab)
  have := Nat.card_le_card_of_injective _ hinj
  rwa [h.L_card] at this

variable {q' : ℕ} {δ : X ⧸ Subgroup.center X} (hT : Torus710 M q' δ)

omit [Finite X] in
theorem _root_.CFSG.CGT.T75F.Torus710.ncard_sharp (hT : Torus710 M q' δ) :
    (((Mhat M : Subgroup (X ⧸ Subgroup.center X)) : Set (X ⧸ Subgroup.center X)) \
      ({1} : Set (X ⧸ Subgroup.center X))).ncard = q' - 1 := by
  rw [Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem _)]
  have : ((Mhat M : Subgroup (X ⧸ Subgroup.center X)) :
      Set (X ⧸ Subgroup.center X)).ncard = q' := by
    rw [← Nat.card_coe_set_eq]
    exact hT.card
  rw [this]

include h hT in
theorem conj_mem_delta {a : X} (ha : (QuotientGroup.mk a : X ⧸ Subgroup.center X) = δ) (i : ℕ)
    {β : X} (hβ : β ∈ D) (hβM : β ∈ M) : a ^ i * β * (a ^ i)⁻¹ ∈ D ∧ a ^ i * β * (a ^ i)⁻¹ ∈ M := by
  refine ⟨h.conj_mem β hβ _, ?_⟩
  have h1 := hT.normalizes i _ (psi_mem_Mhat hβM)
  obtain ⟨m, hm, hmeq⟩ := Subgroup.mem_map.1 h1
  have h2 : (QuotientGroup.mk m : X ⧸ Subgroup.center X) =
      QuotientGroup.mk (a ^ i * β * (a ^ i)⁻¹) := by
    change (QuotientGroup.mk' (Subgroup.center X)) m = _
    rw [hmeq]
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow, ha]
  have hz : m⁻¹ * (a ^ i * β * (a ^ i)⁻¹) ∈ Subgroup.center X := QuotientGroup.eq.1 h2
  exact h.mem_M_of_mul_center (h.conj_mem β hβ _) hm hz (by group)

include h hT in
theorem fib_ncard_le {a : X} (ha : (QuotientGroup.mk a : X ⧸ Subgroup.center X) = δ)
    {ω₁ ω₂ : X ⧸ Subgroup.center X} (hω₁ : ω₁ ∈ Mhat M) (hω₁1 : ω₁ ≠ 1) (hω₂ : ω₂ ∈ Mhat M)
    (hω₂1 : ω₂ ≠ 1) : (fib D M ω₁).ncard ≤ (fib D M ω₂).ncard := by
  obtain ⟨i, hi⟩ := hT.trans ω₁ hω₁ hω₁1 ω₂ hω₂ hω₂1
  refine Set.ncard_le_ncard_of_injOn (fun β => a ^ i * β * (a ^ i)⁻¹) ?_ ?_ (Set.toFinite _)
  · rintro β ⟨hβD, hβM, hβω⟩
    obtain ⟨h1, h2⟩ := h.conj_mem_delta hT ha i hβD hβM
    refine ⟨h1, h2, ?_⟩
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow, ha,
      hβω]
    exact hi
  · intro x _ y _ hxy
    have : a ^ i * x * (a ^ i)⁻¹ = a ^ i * y * (a ^ i)⁻¹ := hxy
    simpa using this

include h hT in
theorem fib_ncard_eq {a : X} (ha : (QuotientGroup.mk a : X ⧸ Subgroup.center X) = δ)
    {ω₁ ω₂ : X ⧸ Subgroup.center X} (hω₁ : ω₁ ∈ Mhat M) (hω₁1 : ω₁ ≠ 1) (hω₂ : ω₂ ∈ Mhat M)
    (hω₂1 : ω₂ ≠ 1) : (fib D M ω₁).ncard = (fib D M ω₂).ncard :=
  le_antisymm (h.fib_ncard_le hT ha hω₁ hω₁1 hω₂ hω₂1) (h.fib_ncard_le hT ha hω₂ hω₂1 hω₁ hω₁1)

include h hT in
theorem main_count {a : X} (ha : (QuotientGroup.mk a : X ⧸ Subgroup.center X) = δ) :
    q' = q ^ 2 ∧ (∀ ω ∈ Mhat M, ω ≠ 1 → (fib D M ω).ncard = q + 1) ∧
      Nat.card (M ⊓ Subgroup.center X : Subgroup X) = q ^ 2 := by
  have hq4 := h.q_ge
  have hnt : 1 < Nat.card L := by rw [h.L_card]; nlinarith
  have : Nontrivial L := Finite.one_lt_card_iff_nontrivial.1 hnt
  obtain ⟨⟨u₀, hu₀⟩, hne⟩ := exists_ne (1 : L)
  have hu₀1 : u₀ ≠ 1 := fun h' => hne (Subtype.ext h')
  have hu₀D : u₀ ∈ D := h.L_D u₀ hu₀ hu₀1
  have hu₀M : u₀ ∈ M := h.L_le hu₀
  set ω₀ : X ⧸ Subgroup.center X := QuotientGroup.mk u₀ with hω₀
  have hω₀M : ω₀ ∈ Mhat M := psi_mem_Mhat hu₀M
  have hω₀1 : ω₀ ≠ 1 := h.mk_ne_one hu₀D
  set φ := (fib D M ω₀).ncard with hφ
  have hu₀fib : u₀ ∈ fib D M ω₀ := ⟨hu₀D, hu₀M, rfl⟩
  have hφ1 : 1 ≤ φ := by
    rw [hφ]
    exact Nat.one_le_iff_ne_zero.2 ((Set.ncard_pos (Set.toFinite _)).2 ⟨u₀, hu₀fib⟩).ne'
  have hΩs := hT.ncard_sharp
  have hsum := ncard_eq_mul_of_fibres (D ∩ (M : Set X))
    ((Mhat M : Set (X ⧸ Subgroup.center X)) \ ({1} : Set (X ⧸ Subgroup.center X)))
    (fun β => (QuotientGroup.mk β : X ⧸ Subgroup.center X))
    (fun β hβ => ⟨psi_mem_Mhat hβ.2, h.mk_ne_one hβ.1⟩) φ (by
      intro ω hω
      have hfibω : {β | β ∈ D ∩ (M : Set X) ∧ (QuotientGroup.mk β : X ⧸ Subgroup.center X) = ω} =
          fib D M ω := by
        ext β
        simp [fib, and_assoc]
      rw [hfibω, hφ]
      exact h.fib_ncard_eq hT ha hω.1 hω.2 hω₀M hω₀1)
  have hDelta : (D ∩ (M : Set X)).ncard = (q + 1) * (q ^ 2 - 1) := by
    rw [← Nat.card_coe_set_eq]
    exact h.card_Delta
  rw [hDelta, hΩs] at hsum
  have heq : (q' - 1) * φ = (q + 1) * (q ^ 2 - 1) := hsum.symm
  have hZcard := h.card_Z_mul
  rw [hT.card] at hZcard
  have hφZ : φ ≤ Nat.card (M ⊓ Subgroup.center X : Subgroup X) := by
    have hle : (fib D M ω₀).ncard ≤ ((M ⊓ Subgroup.center X : Subgroup X) : Set X).ncard := by
      refine Set.ncard_le_ncard_of_injOn (fun β => u₀⁻¹ * β) ?_ ?_ (Set.toFinite _)
      · rintro β ⟨hβD, hβM, hβω⟩
        refine ⟨M.mul_mem (M.inv_mem hu₀M) hβM, ?_⟩
        exact QuotientGroup.eq.1 (by rw [← hω₀, hβω])
      · intro x _ y _ hxy
        exact mul_left_cancel hxy
    rw [← Nat.card_coe_set_eq] at hle
    exact hle
  have hq'pow : q ^ 2 ∣ q' := by
    obtain ⟨k, hk, rfl⟩ := h.q_pow
    have hdvd : q' ∣ (2 ^ k) ^ 4 := ⟨_, by rw [← hZcard]; ring⟩
    rw [← pow_mul] at hdvd
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hle := h.q_sq_le_card_Mhat
    rw [hT.card, hj, ← pow_mul] at hle
    have : k * 2 ≤ j := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hle
    rw [hj, ← pow_mul]
    exact pow_dvd_pow 2 this
  obtain ⟨r, hr⟩ := hq'pow
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · exfalso
      rw [h0, mul_zero] at hr
      have := hT.four_le
      omega
    · exact h0
  have hφq : φ ≤ q ^ 2 := by
    have hz : Nat.card (M ⊓ Subgroup.center X : Subgroup X) * r = q ^ 2 := by
      have : Nat.card (M ⊓ Subgroup.center X : Subgroup X) * (q ^ 2 * r) = q ^ 2 * q ^ 2 := by
        rw [← hr, hZcard]; ring
      have hpos : 0 < q ^ 2 := by positivity
      refine Nat.eq_of_mul_eq_mul_left hpos ?_
      linarith
    calc φ ≤ Nat.card (M ⊓ Subgroup.center X : Subgroup X) := hφZ
      _ ≤ Nat.card (M ⊓ Subgroup.center X : Subgroup X) * r := Nat.le_mul_of_pos_right _ hr1
      _ = q ^ 2 := hz
  rw [hr] at heq
  obtain ⟨hr1', hφ'⟩ := arith710 q r φ hq4 hr1 hφ1 hφq heq
  have hq'eq : q' = q ^ 2 := by rw [hr, hr1', mul_one]
  refine ⟨hq'eq, ?_, ?_⟩
  · intro ω hω hω1
    rw [h.fib_ncard_eq hT ha hω hω1 hω₀M hω₀1, ← hφ]
    exact hφ'
  · have hpos : 0 < q ^ 2 := by positivity
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [hq'eq] at hZcard
    rw [hZcard]
    ring

end Endgame710

end CFSG.CGT.T75F

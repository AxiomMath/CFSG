module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompKac
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalRoots
public import CFSG.LieType.AlgebraicGroups.ToralRootCover

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.AlgebraicGroups (rootCharHom)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

namespace KacData

variable {τ : Tag} (K : KacData τ)

@[expose] def extRoot : Option (Fin τ.rank) → Fin τ.rank → ℤ
  | none => -K.θ
  | some j => Pi.single j 1

@[expose] def IsZ (p : ℕ) (μ : Fin τ.rank → ℤ) : Option (Fin τ.rank) → Prop
  | none => K.θ ⬝ᵥ μ = p
  | some j => μ j = 0

@[expose] def Adj (x y : Option (Fin τ.rank)) : Prop :=
  x ≠ y ∧ iform (K.extRoot x) (K.extRoot y) ≠ 0

@[expose] def ZRel (p : ℕ) (μ : Fin τ.rank → ℤ) (x y : Option (Fin τ.rank)) : Prop :=
  K.IsZ p μ x ∧ K.IsZ p μ y ∧ K.Adj x y

@[expose] def comp (p : ℕ) (μ : Fin τ.rank → ℤ) (x : Option (Fin τ.rank)) :
    Set (Option (Fin τ.rank)) :=
  {y | K.IsZ p μ y ∧ Relation.EqvGen (K.ZRel p μ) x y}

@[expose] def combo (n : Option (Fin τ.rank) → ℕ) : Fin τ.rank → ℤ :=
  ∑ x, (n x : ℤ) • K.extRoot x

@[expose] def rootsOf (C : Set (Option (Fin τ.rank))) : Set (Fin τ.rank → ℤ) :=
  {γ | IsRoot τ γ ∧ ∃ n : Option (Fin τ.rank) → ℕ, (∀ x, n x ≠ 0 → x ∈ C) ∧
    (γ = K.combo n ∨ γ = -K.combo n)}

structure Facts : Prop where
  θ_pos : ∀ j, 0 < K.θ j
  le_θ : ∀ γ, IsRoot τ γ → (∀ j, 0 ≤ γ j) → ∀ j, γ j ≤ K.θ j
  split : ∀ (S₁ S₂ : Set (Option (Fin τ.rank))),
    (∀ x ∈ S₁, ∀ y ∈ S₂, x ≠ y ∧ ¬ K.Adj x y) →
    ∀ n₁ n₂ : Option (Fin τ.rank) → ℕ, (∀ x, n₁ x ≠ 0 → x ∈ S₁) →
      (∀ x, n₂ x ≠ 0 → x ∈ S₂) → IsRoot τ (K.combo n₁ + K.combo n₂) →
        K.combo n₁ = 0 ∨ K.combo n₂ = 0

theorem isRoot_extRoot (x : Option (Fin τ.rank)) : IsRoot τ (K.extRoot x) := by
  cases x with
  | none => exact IsRoot.neg K.isRoot_θ
  | some j => exact IsRoot.basis j

theorem extRoot_dvd {p : ℕ} {μ : Fin τ.rank → ℤ} {x : Option (Fin τ.rank)}
    (hx : K.IsZ p μ x) : (p : ℤ) ∣ K.extRoot x ⬝ᵥ μ := by
  cases x with
  | none =>
    change K.θ ⬝ᵥ μ = p at hx
    change (p : ℤ) ∣ (-K.θ) ⬝ᵥ μ
    rw [neg_dotProduct, hx]
    exact dvd_neg.2 dvd_rfl
  | some j =>
    change μ j = 0 at hx
    change (p : ℤ) ∣ (Pi.single j 1 : Fin τ.rank → ℤ) ⬝ᵥ μ
    rw [single_dotProduct, hx, mul_zero]
    exact dvd_zero _

theorem combo_dot (n : Option (Fin τ.rank) → ℕ) (μ : Fin τ.rank → ℤ) :
    K.combo n ⬝ᵥ μ = ∑ x, (n x : ℤ) * (K.extRoot x ⬝ᵥ μ) := by
  simp only [combo, sum_dotProduct, smul_dotProduct, smul_eq_mul]

theorem iform_combo_left (n : Option (Fin τ.rank) → ℕ) (v : Fin τ.rank → ℤ) :
    iform (K.combo n) v = ∑ x, (n x : ℤ) * iform (K.extRoot x) v := by
  simp only [← dotProduct_mulVec_eq_iform, combo, sum_dotProduct, smul_dotProduct, smul_eq_mul]

theorem combo_dvd {p : ℕ} {μ : Fin τ.rank → ℤ} {n : Option (Fin τ.rank) → ℕ}
    (hn : ∀ x, n x ≠ 0 → K.IsZ p μ x) : (p : ℤ) ∣ K.combo n ⬝ᵥ μ := by
  rw [combo_dot]
  refine Finset.dvd_sum fun x _ => ?_
  by_cases h : n x = 0
  · rw [h, Nat.cast_zero, zero_mul]
    exact dvd_zero _
  · exact Dvd.dvd.mul_left (K.extRoot_dvd (hn x h)) _

theorem combo_of_nonneg {γ : Fin τ.rank → ℤ} (hγ : ∀ j, 0 ≤ γ j) :
    K.combo (fun x => Option.elim x 0 fun j => (γ j).toNat) = γ := by
  rw [combo, Fintype.sum_option]
  simp only [Option.elim_none, Nat.cast_zero, zero_smul, zero_add, Option.elim_some, extRoot]
  conv_rhs => rw [pi_eq_sum_univ γ]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Int.toNat_of_nonneg (hγ j)]
  funext k
  simp [Pi.single_apply, eq_comm]

theorem exists_combo_of_dvd (hK : K.Facts) {p : ℕ} (hp : 0 < p) {μ : Fin τ.rank → ℤ}
    (hμ : K.IsNormal p μ) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hk : (p : ℤ) ∣ γ ⬝ᵥ μ) :
    ∃ n : Option (Fin τ.rank) → ℕ, (∀ x, n x ≠ 0 → K.IsZ p μ x) ∧
      (γ = K.combo n ∨ γ = -K.combo n) := by
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  have pos : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → (∀ j, 0 ≤ δ j) → (p : ℤ) ∣ δ ⬝ᵥ μ →
      ∃ n : Option (Fin τ.rank) → ℕ, (∀ x, n x ≠ 0 → K.IsZ p μ x) ∧
        (δ = K.combo n ∨ δ = -K.combo n) := by
    intro δ hδ hδ0 hdv
    have hle := hK.le_θ δ hδ hδ0
    have h0 : 0 ≤ δ ⬝ᵥ μ := Finset.sum_nonneg fun j _ => mul_nonneg (hδ0 j) (hμ.1 j)
    have h1 : δ ⬝ᵥ μ ≤ K.θ ⬝ᵥ μ :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hle j) (hμ.1 j)
    have h2 := hμ.2
    obtain ⟨m, hm⟩ := hdv
    have hm01 : m = 0 ∨ m = 1 := by
      have : 0 ≤ (p : ℤ) * m := hm ▸ h0
      have : (p : ℤ) * m ≤ p := hm ▸ h1.trans h2
      have hm0 : 0 ≤ m := nonneg_of_mul_nonneg_right (by linarith) hpz
      have hm1 : m ≤ 1 := by nlinarith
      omega
    rcases hm01 with rfl | rfl
    ·
      refine ⟨fun x => Option.elim x 0 fun j => (δ j).toNat, fun x hx => ?_,
        Or.inl (K.combo_of_nonneg hδ0).symm⟩
      cases x with
      | none => exact absurd rfl hx
      | some j =>
        change μ j = 0
        have hj : (δ j).toNat ≠ 0 := hx
        have hδj : 0 < δ j := by omega
        have hterm : δ j * μ j = 0 := by
          have hsum : ∑ i, δ i * μ i = 0 := by rw [mul_zero] at hm; exact hm
          exact (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (hδ0 i) (hμ.1 i)).1
            hsum j (Finset.mem_univ j)
        rcases mul_eq_zero.1 hterm with h | h
        · omega
        · exact h
    ·
      rw [mul_one] at hm
      have hθμ : K.θ ⬝ᵥ μ = p := by linarith
      set ε : Fin τ.rank → ℤ := K.θ - δ with hε
      have hε0 : ∀ j, 0 ≤ ε j := fun j => by simp only [hε, Pi.sub_apply]; linarith [hle j]
      have hεμ : ε ⬝ᵥ μ = 0 := by rw [hε, sub_dotProduct, hθμ, hm, sub_self]
      refine ⟨fun x => Option.elim x 1 fun j => (ε j).toNat, fun x hx => ?_, Or.inr ?_⟩
      · cases x with
        | none => exact hθμ
        | some j =>
          change μ j = 0
          have hj : (ε j).toNat ≠ 0 := hx
          have hεj : 0 < ε j := by omega
          have hterm : ε j * μ j = 0 :=
            (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (hε0 i) (hμ.1 i)).1
              hεμ j (Finset.mem_univ j)
          rcases mul_eq_zero.1 hterm with h | h
          · omega
          · exact h
      · have hc : K.combo (fun x => Option.elim x 1 fun j => (ε j).toNat) = -K.θ + ε := by
          rw [combo, Fintype.sum_option]
          simp only [Option.elim_none, Nat.cast_one, one_smul, Option.elim_some]
          congr 1
          have := K.combo_of_nonneg hε0
          rw [combo, Fintype.sum_option] at this
          simpa [Option.elim_none, Option.elim_some, extRoot] using this
        rw [hc, hε]
        abel
  rcases CFSG.LieType.RootSystem.nonneg_or_nonpos (isFiniteType_cartan τ) ∅
      (isRoot_iff_mem_roots.1 hγ) with h | h
  · exact pos γ hγ (fun j => h j) hk
  · obtain ⟨n, hn, hγn⟩ := pos (-γ) (IsRoot.neg hγ) (fun j => by
      have := h j
      simp only [Pi.zero_apply] at this
      simp only [Pi.neg_apply]
      linarith)
      (by rw [neg_dotProduct]; exact dvd_neg.2 hk)
    refine ⟨n, hn, ?_⟩
    rcases hγn with e | e
    · right
      rw [← e, neg_neg]
    · left
      rw [← neg_neg γ, e, neg_neg]

theorem iform_combo_eq_zero {S₁ S₂ : Set (Option (Fin τ.rank))}
    (hS : ∀ x ∈ S₁, ∀ y ∈ S₂, x ≠ y ∧ ¬ K.Adj x y) {n₁ n₂ : Option (Fin τ.rank) → ℕ}
    (hn₁ : ∀ x, n₁ x ≠ 0 → x ∈ S₁) (hn₂ : ∀ x, n₂ x ≠ 0 → x ∈ S₂) :
    iform (K.combo n₁) (K.combo n₂) = 0 := by
  rw [iform_combo_left]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases h1 : n₁ x = 0
  · rw [h1, Nat.cast_zero, zero_mul]
  rw [iform_comm, iform_combo_left]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun y _ => ?_)
  by_cases h2 : n₂ y = 0
  · rw [h2, Nat.cast_zero, zero_mul]
  obtain ⟨hne, hadj⟩ := hS x (hn₁ x h1) y (hn₂ y h2)
  have : iform (K.extRoot y) (K.extRoot x) = 0 := by
    by_contra h0
    exact hadj ⟨hne, by rwa [iform_comm]⟩
  rw [this, mul_zero]

theorem exists_iform_ne_zero {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    {n : Option (Fin τ.rank) → ℕ} (hγn : γ = K.combo n ∨ γ = -K.combo n) :
    ∃ x, n x ≠ 0 ∧ iform γ (K.extRoot x) ≠ 0 := by
  by_contra hne
  push Not at hne
  have hpos := iform_self_pos_of_isRoot hγ
  have h0 : iform γ (K.combo n) = 0 := by
    rw [iform_comm, iform_combo_left]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases h : n x = 0
    · rw [h, Nat.cast_zero, zero_mul]
    · rw [iform_comm, hne x h, mul_zero]
  rcases hγn with e | e
  · rw [← e] at h0
    omega
  · have : iform γ γ = -iform γ (K.combo n) := by
      nth_rewrite 2 [e]
      rw [show -K.combo n = (-1 : ℤ) • K.combo n by rw [neg_one_smul], iform_smul_right]
      ring
    omega

theorem isZ_iff_of_eqvGen {p : ℕ} {μ : Fin τ.rank → ℤ} {x y : Option (Fin τ.rank)}
    (hxy : Relation.EqvGen (K.ZRel p μ) x y) : K.IsZ p μ x ↔ K.IsZ p μ y := by
  induction hxy with
  | rel a b hab => exact ⟨fun _ => hab.2.1, fun _ => hab.1⟩
  | refl a => exact Iff.rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

theorem mem_comp_self {p : ℕ} {μ : Fin τ.rank → ℤ} {x : Option (Fin τ.rank)}
    (hx : K.IsZ p μ x) : x ∈ K.comp p μ x :=
  ⟨hx, Relation.EqvGen.refl x⟩

theorem comp_separated {p : ℕ} {μ : Fin τ.rank → ℤ} {x y : Option (Fin τ.rank)}
    (hy : K.IsZ p μ y) (hyx : y ∉ K.comp p μ x) :
    ∀ a ∈ K.comp p μ x, ∀ b ∈ K.comp p μ y, a ≠ b ∧ ¬ K.Adj a b := by
  rintro a ⟨ha, hxa⟩ b ⟨hb, hyb⟩
  refine ⟨fun hab => hyx ⟨hy, ?_⟩, fun hadj => hyx ⟨hy, ?_⟩⟩
  · subst hab
    exact hxa.trans _ _ _ hyb.symm
  · exact (hxa.trans _ _ _ (Relation.EqvGen.rel _ _ ⟨ha, hb, hadj⟩)).trans _ _ _ hyb.symm

theorem comp_eq_of_mem {p : ℕ} {μ : Fin τ.rank → ℤ} {x y : Option (Fin τ.rank)}
    (hyx : y ∈ K.comp p μ x) : K.comp p μ y = K.comp p μ x := by
  ext z
  constructor
  · rintro ⟨hz, hyz⟩
    exact ⟨hz, hyx.2.trans _ _ _ hyz⟩
  · rintro ⟨hz, hxz⟩
    exact ⟨hz, hyx.2.symm.trans _ _ _ hxz⟩

theorem combo_split (n : Option (Fin τ.rank) → ℕ) (S : Set (Option (Fin τ.rank)))
    [DecidablePred (· ∈ S)] :
    K.combo n = K.combo (fun x => if x ∈ S then n x else 0) +
      K.combo (fun x => if x ∈ S then 0 else n x) := by
  simp only [combo, ← Finset.sum_add_distrib, ← add_smul]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

theorem mem_rootsOf_comp (hK : K.Facts) {p : ℕ} {μ : Fin τ.rank → ℤ}
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) {n : Option (Fin τ.rank) → ℕ}
    (hn : ∀ x, n x ≠ 0 → K.IsZ p μ x) (hγn : γ = K.combo n ∨ γ = -K.combo n)
    {y : Option (Fin τ.rank)} (hny : n y ≠ 0) (hiy : iform γ (K.extRoot y) ≠ 0) :
    γ ∈ K.rootsOf (K.comp p μ y) := by
  classical
  have hy : K.IsZ p μ y := hn y hny
  set S₁ := K.comp p μ y with hS₁
  set n₁ : Option (Fin τ.rank) → ℕ := fun x => if x ∈ S₁ then n x else 0 with hn₁
  set n₂ : Option (Fin τ.rank) → ℕ := fun x => if x ∈ S₁ then 0 else n x with hn₂
  have hsplit := K.combo_split n S₁
  have hsupp₁ : ∀ x, n₁ x ≠ 0 → x ∈ S₁ := fun x hx => by
    by_contra h
    exact hx (ite_eq_right_iff.2 fun h' => absurd h' h)
  set S₂ : Set (Option (Fin τ.rank)) := {z | K.IsZ p μ z ∧ z ∉ S₁} with hS₂
  have hsupp₂ : ∀ x, n₂ x ≠ 0 → x ∈ S₂ := fun x hx => by
    by_cases h : x ∈ S₁
    · exact absurd (by simp only [hn₂, h, ite_true]) hx
    · refine ⟨hn x ?_, h⟩
      intro h0
      exact hx (by simp only [hn₂, h, h0, ite_false])
  have hsep : ∀ a ∈ S₁, ∀ b ∈ S₂, a ≠ b ∧ ¬ K.Adj a b := by
    rintro a ha b ⟨hb, hbS⟩
    have h := K.comp_separated hb hbS a ha b (K.mem_comp_self hb)
    exact h
  have hroot : IsRoot τ (K.combo n₁ + K.combo n₂) := by
    rw [← hsplit]
    rcases hγn with e | e
    · rwa [← e]
    · rw [← neg_neg (K.combo n), ← e]
      exact IsRoot.neg hγ
  rcases hK.split S₁ S₂ hsep n₁ n₂ hsupp₁ hsupp₂ hroot with h0 | h0
  ·
    exfalso
    apply hiy
    have hy' : iform (K.combo n₂) (K.extRoot y) = 0 := by
      have hS := K.iform_combo_eq_zero (S₁ := S₂) (S₂ := S₁)
        (fun a ha b hb => by
          obtain ⟨h1, h2⟩ := hsep b hb a ha
          exact ⟨h1.symm, fun h => h2 ⟨h1, by rw [iform_comm]; exact h.2⟩⟩)
        hsupp₂ (n₂ := fun x => if x = y then 1 else 0) (fun x hx => by
          by_cases h : x = y
          · rw [h]; exact K.mem_comp_self hy
          · exact absurd (by simp only [h, ite_false]) hx)
      have hc : K.combo (fun x => if x = y then 1 else 0) = K.extRoot y := by
        rw [combo, Finset.sum_eq_single y (fun b _ hb => by simp [hb]) (by simp)]
        simp
      rwa [hc] at hS
    rcases hγn with e | e
    · rw [e, hsplit, h0, zero_add, hy']
    · rw [e, hsplit, h0, zero_add, show -K.combo n₂ = (-1 : ℤ) • K.combo n₂ by
        rw [neg_one_smul], iform_smul_left, hy', mul_zero]
  · refine ⟨hγ, n₁, hsupp₁, ?_⟩
    rcases hγn with e | e
    · left
      rw [e, hsplit, h0, add_zero]
    · right
      rw [e, hsplit, h0, add_zero]

section Classes

variable {M : Type*} [CommGroup M]

theorem extRoot_mem_kernelRoots {p : ℕ} {μ : Fin τ.rank → ℤ}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hχ : ∀ γ, IsRoot τ γ → (χ (Multiplicative.ofAdd γ) = 1 ↔ (p : ℤ) ∣ γ ⬝ᵥ μ))
    {x : Option (Fin τ.rank)} (hx : K.IsZ p μ x) : K.extRoot x ∈ kernelRoots χ :=
  ⟨K.isRoot_extRoot x, (hχ _ (K.isRoot_extRoot x)).2 (K.extRoot_dvd hx)⟩

theorem mk_extRoot_eq {p : ℕ} {μ : Fin τ.rank → ℤ} {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hχ : ∀ γ, IsRoot τ γ → (χ (Multiplicative.ofAdd γ) = 1 ↔ (p : ℤ) ∣ γ ⬝ᵥ μ))
    {x y : Option (Fin τ.rank)} (hx : K.IsZ p μ x) (hxy : Relation.EqvGen (K.ZRel p μ) x y) :
    (⟦⟨K.extRoot x, K.extRoot_mem_kernelRoots hχ hx⟩⟧ : KernelComponent χ) =
      ⟦⟨K.extRoot y, K.extRoot_mem_kernelRoots hχ ((K.isZ_iff_of_eqvGen hxy).1 hx)⟩⟧ := by
  revert hx
  induction hxy with
  | rel a b hab => exact fun _ => mk_eq_of_iform_ne_zero hab.2.2.2
  | refl a => exact fun _ => rfl
  | symm a b hab ih =>
    intro hb
    have ha : K.IsZ p μ a := (K.isZ_iff_of_eqvGen hab).2 hb
    exact (ih ha).symm
  | trans a b c hab _ ih1 ih2 =>
    intro ha
    have hb : K.IsZ p μ b := (K.isZ_iff_of_eqvGen hab).1 ha
    exact (ih1 ha).trans (ih2 hb)

theorem componentRoots_eq_rootsOf (hK : K.Facts) {p : ℕ} (hp : 0 < p) {μ : Fin τ.rank → ℤ}
    (hμ : K.IsNormal p μ) {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hχ : ∀ γ, IsRoot τ γ → (χ (Multiplicative.ofAdd γ) = 1 ↔ (p : ℤ) ∣ γ ⬝ᵥ μ))
    (i : KernelComponent χ) :
    ∃ x, K.IsZ p μ x ∧ componentRoots χ i = K.rootsOf (K.comp p μ x) := by
  obtain ⟨⟨β₀, hβ₀⟩, rfl⟩ := Quotient.exists_rep i
  have hdvd : ∀ {γ}, γ ∈ kernelRoots χ → (p : ℤ) ∣ γ ⬝ᵥ μ := fun hγ => (hχ _ hγ.1).1 hγ.2
  obtain ⟨n₀, hn₀, hβn₀⟩ := K.exists_combo_of_dvd hK hp hμ hβ₀.1 (hdvd hβ₀)
  obtain ⟨x₀, hx₀n, hx₀i⟩ := K.exists_iform_ne_zero hβ₀.1 hβn₀
  have hx₀ : K.IsZ p μ x₀ := hn₀ x₀ hx₀n
  refine ⟨x₀, hx₀, ?_⟩
  have hmem : ∀ γ ∈ K.rootsOf (K.comp p μ x₀), ∃ hγ : γ ∈ kernelRoots χ,
      (⟦⟨γ, hγ⟩⟧ : KernelComponent χ) =
        ⟦⟨K.extRoot x₀, K.extRoot_mem_kernelRoots hχ hx₀⟩⟧ := by
    rintro γ ⟨hγ, m, hm, hγm⟩
    have hmZ : ∀ x, m x ≠ 0 → K.IsZ p μ x := fun x hx => (hm x hx).1
    have hγk : γ ∈ kernelRoots χ := ⟨hγ, (hχ γ hγ).2 (by
      rcases hγm with e | e
      · rw [e]; exact K.combo_dvd hmZ
      · rw [e, neg_dotProduct]; exact dvd_neg.2 (K.combo_dvd hmZ))⟩
    obtain ⟨y, hmy, hiy⟩ := K.exists_iform_ne_zero hγ hγm
    refine ⟨hγk, ?_⟩
    have h1 : (⟦⟨γ, hγk⟩⟧ : KernelComponent χ) =
        ⟦⟨K.extRoot y, K.extRoot_mem_kernelRoots hχ (hmZ y hmy)⟩⟧ :=
      mk_eq_of_iform_ne_zero hiy
    rw [h1]
    exact (K.mk_extRoot_eq hχ hx₀ (hm y hmy).2).symm
  have hβ₀C : β₀ ∈ K.rootsOf (K.comp p μ x₀) :=
    K.mem_rootsOf_comp hK hβ₀.1 hn₀ hβn₀ hx₀n hx₀i
  have hβ₀cls : (⟦⟨β₀, hβ₀⟩⟧ : KernelComponent χ) =
      ⟦⟨K.extRoot x₀, K.extRoot_mem_kernelRoots hχ hx₀⟩⟧ := by
    obtain ⟨h, e⟩ := hmem β₀ hβ₀C
    exact e
  have hstep : ∀ δ δ' : kernelRoots χ, iform (δ : Fin τ.rank → ℤ) δ' ≠ 0 →
      (δ : Fin τ.rank → ℤ) ∈ K.rootsOf (K.comp p μ x₀) →
        (δ' : Fin τ.rank → ℤ) ∈ K.rootsOf (K.comp p μ x₀) := by
    intro δ δ' hi hδC
    obtain ⟨-, m, hm, hδm⟩ := hδC
    obtain ⟨n', hn', hδn'⟩ := K.exists_combo_of_dvd hK hp hμ δ'.2.1 (hdvd δ'.2)
    obtain ⟨y, hny, hiy⟩ := K.exists_iform_ne_zero δ'.2.1 hδn'
    have hδ'y := K.mem_rootsOf_comp hK δ'.2.1 hn' hδn' hny hiy
    by_cases hyx : y ∈ K.comp p μ x₀
    · rwa [K.comp_eq_of_mem hyx] at hδ'y
    · exfalso
      obtain ⟨-, m', hm', hδ'm'⟩ := hδ'y
      have h0 := K.iform_combo_eq_zero (K.comp_separated (hn' y hny) hyx) hm hm'
      apply hi
      have hneg : ∀ v : Fin τ.rank → ℤ, -v = (-1 : ℤ) • v := fun v => by rw [neg_one_smul]
      rcases hδm with e | e <;> rcases hδ'm' with e' | e' <;> rw [e, e'] <;>
        simp only [hneg, iform_smul_left, iform_smul_right, h0, mul_zero]
  have hcls : ∀ δ δ' : kernelRoots χ, Relation.EqvGen (fun α β : kernelRoots χ =>
      (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0) δ δ' →
      ((δ : Fin τ.rank → ℤ) ∈ K.rootsOf (K.comp p μ x₀) ↔
        (δ' : Fin τ.rank → ℤ) ∈ K.rootsOf (K.comp p μ x₀)) := by
    intro δ δ' h
    induction h with
    | rel a b hab =>
      rw [dotProduct_mulVec_eq_iform] at hab
      exact ⟨hstep a b hab, hstep b a (by rwa [iform_comm])⟩
    | refl a => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
  ext γ
  constructor
  · rintro ⟨hγ, hγi⟩
    exact (hcls ⟨γ, hγ⟩ ⟨β₀, hβ₀⟩ (Quotient.exact hγi)).2 hβ₀C
  · intro hγC
    obtain ⟨hγk, e⟩ := hmem γ hγC
    exact ⟨hγk, e.trans hβ₀cls.symm⟩

theorem componentRoots_smul_of_isCharConj {χ χ' : Multiplicative (Fin τ.rank → ℤ) →* M}
    {t : WeylGroup τ} (h : IsCharConj χ χ' t) (i : KernelComponent χ) :
    ∃ i' : KernelComponent χ', componentRoots χ i = (fun α => t⁻¹ • α) '' componentRoots χ' i' := by
  obtain ⟨⟨β, hβ⟩, rfl⟩ := Quotient.exists_rep i
  have htβ : t • β ∈ kernelRoots χ' := (kernelRoots_iff_of_isCharConj h).2 (by
    rwa [inv_smul_smul])
  refine ⟨⟦⟨t • β, htβ⟩⟧, ?_⟩
  ext α
  constructor
  · rintro ⟨hα, hαi⟩
    have htα : t • α ∈ kernelRoots χ' := (kernelRoots_iff_of_isCharConj h).2 (by
      rwa [inv_smul_smul])
    refine ⟨t • α, ⟨htα, ?_⟩, inv_smul_smul t α⟩
    rw [mk_eq_mk_iff_of_isCharConj h htα htβ]
    simp only [inv_smul_smul]
    exact hαi
  · rintro ⟨γ, ⟨hγ, hγi⟩, rfl⟩
    have hk := (kernelRoots_iff_of_isCharConj h).1 hγ
    refine ⟨hk, ?_⟩
    have := (mk_eq_mk_iff_of_isCharConj h hγ htβ).1 hγi
    simpa only [inv_smul_smul] using this

end Classes

section Normal

theorem exists_smul_rootsOf (hK : K.Facts) {L : Type} [Field L] {N : ℕ} (hN : 0 < N) {ζ : Lˣ}
    (hζ : IsPrimitiveRoot (ζ : L) N) (a : Fin τ.rank → Lˣ) (ha : ∀ i, a i ^ N = 1) :
    ∃ (v : WeylGroup τ) (μ : Fin τ.rank → ℤ), K.IsNormal N μ ∧
      ∀ i : KernelComponent (rootCharHom a), ∃ x, K.IsZ N μ x ∧
        componentRoots (rootCharHom a) i = (fun α => v • α) '' K.rootsOf (K.comp N μ x) := by
  obtain ⟨w, μ, hμ, hw⟩ := K.exists_weyl_normal hN hζ a ha
  set a' : Fin τ.rank → Lˣ := fun i => ζ ^ μ i with ha'
  have hζu : IsPrimitiveRoot ζ N := IsPrimitiveRoot.coe_units_iff.1 hζ
  have hconj : IsCharConj (rootCharHom a) (rootCharHom a') w := by
    intro v
    change rootChar a' v = rootChar a (w⁻¹ • v)
    rw [hw, smul_inv_smul, ha', rootChar_eq_zpow]
  have hχ : ∀ γ, IsRoot τ γ →
      ((rootCharHom a') (Multiplicative.ofAdd γ) = 1 ↔ (N : ℤ) ∣ γ ⬝ᵥ μ) := by
    intro γ _
    change rootChar a' γ = 1 ↔ _
    rw [ha', rootChar_eq_zpow]
    exact hζu.zpow_eq_one_iff_dvd _
  refine ⟨w⁻¹, μ, hμ, fun i => ?_⟩
  obtain ⟨i', hi'⟩ := componentRoots_smul_of_isCharConj hconj i
  obtain ⟨x, hx, hxi⟩ := K.componentRoots_eq_rootsOf hK hN hμ hχ i'
  exact ⟨x, hx, by rw [hi', hxi]⟩

end Normal

theorem combo_apply_of_none {n : Option (Fin τ.rank) → ℕ} (h0 : n none = 0) (j : Fin τ.rank) :
    K.combo n j = n (some j) := by
  rw [combo, Fintype.sum_option, h0]
  simp only [Nat.cast_zero, zero_smul, zero_add, Finset.sum_apply, Pi.smul_apply, extRoot,
    smul_eq_mul, Pi.single_apply]
  rw [Finset.sum_eq_single j (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

theorem rootsOf_eq_parabolicRoots {C : Set (Option (Fin τ.rank))} (hC : none ∉ C) :
    K.rootsOf C = parabolicRoots τ {j | some j ∈ C} := by
  ext γ
  constructor
  · rintro ⟨hγ, n, hn, hγn⟩
    have h0 : n none = 0 := by
      by_contra h
      exact hC (hn none h)
    refine ⟨hγ, fun j hj => ?_⟩
    have hnj : n (some j) = 0 := by
      by_contra h
      exact hj (hn (some j) h)
    rcases hγn with e | e
    · rw [e, K.combo_apply_of_none h0, hnj, Nat.cast_zero]
    · rw [e, Pi.neg_apply, K.combo_apply_of_none h0, hnj, Nat.cast_zero, neg_zero]
  · rintro ⟨hγ, hJ⟩
    refine ⟨hγ, ?_⟩
    have key : ∀ δ : Fin τ.rank → ℤ, (∀ j, 0 ≤ δ j) → (∀ j, some j ∉ C → δ j = 0) →
        ∃ n : Option (Fin τ.rank) → ℕ, (∀ x, n x ≠ 0 → x ∈ C) ∧ δ = K.combo n := by
      intro δ hδ hδJ
      refine ⟨fun x => Option.elim x 0 fun j => (δ j).toNat, fun x hx => ?_,
        (K.combo_of_nonneg hδ).symm⟩
      cases x with
      | none => exact absurd rfl hx
      | some j =>
        by_contra hj
        exact hx (by simp [hδJ j hj])
    rcases CFSG.LieType.RootSystem.nonneg_or_nonpos (isFiniteType_cartan τ) ∅
        (isRoot_iff_mem_roots.1 hγ) with h | h
    · obtain ⟨n, hn, e⟩ := key γ (fun j => h j) fun j hj => hJ j hj
      exact ⟨n, hn, Or.inl e⟩
    · obtain ⟨n, hn, e⟩ := key (-γ) (fun j => by
          have := h j
          simp only [Pi.zero_apply] at this
          simp only [Pi.neg_apply]
          linarith) fun j hj => by simp [hJ j hj]
      exact ⟨n, hn, Or.inr (by rw [← e, neg_neg])⟩

omit K in
theorem even_iform_self (x : Fin τ.rank → ℤ) : Even (iform x x) := by
  classical
  have key : ∀ s : Finset (Fin τ.rank),
      Even (iform (∑ k ∈ s, x k • (Pi.single k 1 : Fin τ.rank → ℤ))
        (∑ k ∈ s, x k • (Pi.single k 1 : Fin τ.rank → ℤ))) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact ⟨0, by simp [iform]⟩
    | insert k s hk ih =>
      rw [Finset.sum_insert hk]
      set y := ∑ k ∈ s, x k • (Pi.single k 1 : Fin τ.rank → ℤ)
      rw [iform_add_left, iform_add_right, iform_add_right, iform_smul_left, iform_smul_right,
        iform_smul_left, iform_smul_right, iform_single_single, iform_comm y]
      obtain ⟨m, hm⟩ := ih
      exact ⟨m + x k * iform (Pi.single k 1) y + x k * x k * τ.symmetrizer k k, by
        rw [hm]; ring⟩
  have hx : x = ∑ k, x k • (Pi.single k 1 : Fin τ.rank → ℤ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hx]
  exact key Finset.univ

omit K in
theorem eq_zero_of_iform_self {x : Fin τ.rank → ℤ} (h : iform x x = 0) : x = 0 := by
  by_contra hx
  have := iform_self_pos hx
  omega

omit K in
theorem eq_zero_or_eq_zero_of_simplyLaced (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {c₁ c₂ : Fin τ.rank → ℤ} (h0 : iform c₁ c₂ = 0) (hr : IsRoot τ (c₁ + c₂)) :
    c₁ = 0 ∨ c₂ = 0 := by
  have h2 := CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ hr
  rw [iform_add_left, iform_add_right, iform_add_right, h0, iform_comm c₂ c₁, h0] at h2
  obtain ⟨m₁, hm₁⟩ := even_iform_self c₁
  obtain ⟨m₂, hm₂⟩ := even_iform_self c₂
  have hn₁ : 0 ≤ iform c₁ c₁ := by
    by_cases h : c₁ = 0
    · rw [h]; simp [iform]
    · exact (iform_self_pos h).le
  have hn₂ : 0 ≤ iform c₂ c₂ := by
    by_cases h : c₂ = 0
    · rw [h]; simp [iform]
    · exact (iform_self_pos h).le
  rcases (by omega : iform c₁ c₁ = 0 ∨ iform c₂ c₂ = 0) with h | h
  · exact Or.inl (eq_zero_of_iform_self h)
  · exact Or.inr (eq_zero_of_iform_self h)

theorem split_of_simplyLaced (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (S₁ S₂ : Set (Option (Fin τ.rank))) (hS : ∀ x ∈ S₁, ∀ y ∈ S₂, x ≠ y ∧ ¬ K.Adj x y)
    (n₁ n₂ : Option (Fin τ.rank) → ℕ) (hn₁ : ∀ x, n₁ x ≠ 0 → x ∈ S₁)
    (hn₂ : ∀ x, n₂ x ≠ 0 → x ∈ S₂) (hr : IsRoot τ (K.combo n₁ + K.combo n₂)) :
    K.combo n₁ = 0 ∨ K.combo n₂ = 0 :=
  eq_zero_or_eq_zero_of_simplyLaced hτ (K.iform_combo_eq_zero hS hn₁ hn₂) hr

theorem le_θ_of_list (θ' : Fin τ.rank → ℤ) (hθ : K.θ = θ')
    (hlist : ∀ l ∈ τ.artifactRoots, ∀ j : Fin τ.rank,
      (∀ k : Fin τ.rank, 0 ≤ l.getD k 0) → l.getD j 0 ≤ θ' j) :
    ∀ γ, IsRoot τ γ → (∀ j, 0 ≤ γ j) → ∀ j, γ j ≤ K.θ j := by
  intro γ hγ hγ0 j
  have hget : ∀ k : Fin τ.rank, (List.ofFn γ).getD k 0 = γ k := fun k => by
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp
  have h := hlist (List.ofFn γ) (isRoot_iff_mem_artifactRoots.1 hγ) j
    (fun k => by rw [hget]; exact hγ0 k)
  rwa [hget, ← hθ] at h

theorem combo_apply (n : Option (Fin τ.rank) → ℕ) (j : Fin τ.rank) :
    K.combo n j = -(n none : ℤ) * K.θ j + n (some j) := by
  rw [combo, Fintype.sum_option]
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, extRoot, Pi.neg_apply,
    Pi.single_apply]
  rw [Finset.sum_eq_single j (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp only [ite_true, mul_one]
  ring

theorem four_dvd_iform_combo {n : Option (Fin τ.rank) → ℕ} (S : Finset (Option (Fin τ.rank)))
    (hn : ∀ x, n x ≠ 0 → x ∈ S) (h1 : ∀ x ∈ S, 4 ∣ iform (K.extRoot x) (K.extRoot x))
    (h2 : ∀ x ∈ S, ∀ y ∈ S, 2 ∣ iform (K.extRoot x) (K.extRoot y)) :
    4 ∣ iform (K.combo n) (K.combo n) := by
  classical
  have hc : K.combo n = ∑ x ∈ S, (n x : ℤ) • K.extRoot x := by
    rw [combo]
    refine (Finset.sum_subset (Finset.subset_univ S) fun x _ hx => ?_).symm
    have : n x = 0 := by
      by_contra h
      exact hx (hn x h)
    rw [this, Nat.cast_zero, zero_smul]
  rw [hc]
  have key : ∀ s ⊆ S, 4 ∣ iform (∑ x ∈ s, (n x : ℤ) • K.extRoot x)
      (∑ x ∈ s, (n x : ℤ) • K.extRoot x) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp [iform]
    | insert y s hy ih =>
      intro hsub
      have hyS : y ∈ S := hsub (Finset.mem_insert_self y s)
      have hsS : s ⊆ S := fun z hz => hsub (Finset.mem_insert_of_mem hz)
      rw [Finset.sum_insert hy]
      set u := ∑ x ∈ s, (n x : ℤ) • K.extRoot x
      have hu : 2 ∣ iform (K.extRoot y) u := by
        have hsum : iform (K.extRoot y) u =
            ∑ x ∈ s, (n x : ℤ) * iform (K.extRoot y) (K.extRoot x) := by
          rw [iform_finset_sum_right]
          exact Finset.sum_congr rfl fun x _ => iform_smul_right _ _ _
        rw [hsum]
        exact Finset.dvd_sum fun z hz => Dvd.dvd.mul_left (h2 y hyS z (hsS hz)) _
      rw [iform_add_left, iform_add_right, iform_add_right, iform_smul_left, iform_smul_right,
        iform_smul_left, iform_smul_right, iform_comm u (K.extRoot y)]
      obtain ⟨a, ha⟩ := hu
      obtain ⟨b, hb⟩ := h1 y hyS
      obtain ⟨c, hc⟩ := ih hsS
      rw [ha, hb, hc]
      exact ⟨c + (n y : ℤ) * a + (n y : ℤ) * (n y : ℤ) * b, by ring⟩
  exact key S le_rfl

end KacData

section TagFacts


open KacData

theorem facts_E8 : kacE8.Facts where
  θ_pos := show ∀ j : Fin 8, (0 : ℤ) < ![2, 3, 4, 6, 5, 4, 3, 2] j by decide
  le_θ := kacE8.le_θ_of_list ![2, 3, 4, 6, 5, 4, 3, 2] rfl
    (show ∀ l ∈ Tag.E8.artifactRoots, ∀ j : Fin 8, (∀ k : Fin 8, 0 ≤ l.getD k 0) →
      l.getD j 0 ≤ (![2, 3, 4, 6, 5, 4, 3, 2] : Fin 8 → ℤ) j by decide +kernel)
  split := kacE8.split_of_simplyLaced (by decide)

theorem facts_E7 : kacE7.Facts where
  θ_pos := show ∀ j : Fin 7, (0 : ℤ) < ![2, 2, 3, 4, 3, 2, 1] j by decide
  le_θ := kacE7.le_θ_of_list ![2, 2, 3, 4, 3, 2, 1] rfl
    (show ∀ l ∈ Tag.E7.artifactRoots, ∀ j : Fin 7, (∀ k : Fin 7, 0 ≤ l.getD k 0) →
      l.getD j 0 ≤ (![2, 2, 3, 4, 3, 2, 1] : Fin 7 → ℤ) j by decide +kernel)
  split := kacE7.split_of_simplyLaced (by decide)

theorem facts_E6 : kacE6.Facts where
  θ_pos := show ∀ j : Fin 6, (0 : ℤ) < ![1, 2, 2, 3, 2, 1] j by decide
  le_θ := kacE6.le_θ_of_list ![1, 2, 2, 3, 2, 1] rfl
    (show ∀ l ∈ Tag.E6.artifactRoots, ∀ j : Fin 6, (∀ k : Fin 6, 0 ≤ l.getD k 0) →
      l.getD j 0 ≤ (![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ) j by decide +kernel)
  split := kacE6.split_of_simplyLaced (by decide)

theorem facts_D4 : kacD4.Facts where
  θ_pos := show ∀ j : Fin 4, (0 : ℤ) < ![1, 1, 2, 1] j by decide
  le_θ := kacD4.le_θ_of_list ![1, 1, 2, 1] rfl
    (show ∀ l ∈ Tag.D4.artifactRoots, ∀ j : Fin 4, (∀ k : Fin 4, 0 ≤ l.getD k 0) →
      l.getD j 0 ≤ (![1, 1, 2, 1] : Fin 4 → ℤ) j by decide +kernel)
  split := kacD4.split_of_simplyLaced (by decide)

theorem iform_self_le_four_F4 {β : Fin Tag.F4.rank → ℤ} (hβ : IsRoot Tag.F4 β) :
    iform β β ≤ 4 := by
  obtain ⟨w, j, rfl⟩ := isRoot_iff_exists_smul_single.1 hβ
  rw [iform_smul, iform_single_single]
  have h : ∀ j : Fin 4, Tag.F4.symmetrizer j j ≤ 2 := by decide +kernel
  linarith [h j]

theorem f4_long_iform : ∀ u ∈ ([-(![2, 3, 4, 2]), Pi.single ⟨0, by decide⟩ 1,
      Pi.single ⟨1, by decide⟩ 1] : List (Fin Tag.F4.rank → ℤ)),
    ∀ v ∈ ([-(![2, 3, 4, 2]), Pi.single ⟨0, by decide⟩ 1, Pi.single ⟨1, by decide⟩ 1] :
      List (Fin Tag.F4.rank → ℤ)), 2 ∣ iform u v ∧ (u = v → 4 ∣ iform u v) := by
  decide +kernel

theorem f4_short_iform :
    iform (Pi.single (⟨2, by decide⟩ : Fin Tag.F4.rank) 1 : Fin Tag.F4.rank → ℤ)
      (Pi.single ⟨3, by decide⟩ 1) ≠ 0 ∧
    iform (Pi.single (⟨3, by decide⟩ : Fin Tag.F4.rank) 1 : Fin Tag.F4.rank → ℤ)
      (Pi.single ⟨2, by decide⟩ 1) ≠ 0 := by
  decide +kernel

theorem split_F4 (S₁ S₂ : Set (Option (Fin Tag.F4.rank)))
    (hS : ∀ x ∈ S₁, ∀ y ∈ S₂, x ≠ y ∧ ¬ kacF4.Adj x y)
    (n₁ n₂ : Option (Fin Tag.F4.rank) → ℕ) (hn₁ : ∀ x, n₁ x ≠ 0 → x ∈ S₁)
    (hn₂ : ∀ x, n₂ x ≠ 0 → x ∈ S₂) (hr : IsRoot Tag.F4 (kacF4.combo n₁ + kacF4.combo n₂)) :
    kacF4.combo n₁ = 0 ∨ kacF4.combo n₂ = 0 := by
  classical
  set c₁ := kacF4.combo n₁
  set c₂ := kacF4.combo n₂
  have h0 : iform c₁ c₂ = 0 := kacF4.iform_combo_eq_zero hS hn₁ hn₂
  by_contra hne
  push Not at hne
  obtain ⟨hc₁, hc₂⟩ := hne
  have hβ := iform_self_le_four_F4 hr
  rw [iform_add_left, iform_add_right, iform_add_right, h0, iform_comm c₂ c₁, h0] at hβ
  have hp₁ := iform_self_pos hc₁
  have hp₂ := iform_self_pos hc₂
  obtain ⟨m₁, hm₁⟩ := even_iform_self c₁
  obtain ⟨m₂, hm₂⟩ := even_iform_self c₂
  have e₁ : iform c₁ c₁ = 2 := by omega
  have e₂ : iform c₂ c₂ = 2 := by omega
  set s2 : Option (Fin Tag.F4.rank) := some ⟨2, by decide⟩
  set s3 : Option (Fin Tag.F4.rank) := some ⟨3, by decide⟩
  set long : Finset (Option (Fin Tag.F4.rank)) :=
    {none, some ⟨0, by decide⟩, some ⟨1, by decide⟩}
  have hext : ∀ x ∈ long, kacF4.extRoot x ∈ ([-(![2, 3, 4, 2]), Pi.single ⟨0, by decide⟩ 1,
      Pi.single ⟨1, by decide⟩ 1] : List (Fin Tag.F4.rank → ℤ)) := by
    intro x hx
    simp only [long, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hlong1 : ∀ x ∈ long, 4 ∣ iform (kacF4.extRoot x) (kacF4.extRoot x) := fun x hx =>
    (f4_long_iform _ (hext x hx) _ (hext x hx)).2 rfl
  have hlong2 : ∀ x ∈ long, ∀ y ∈ long, 2 ∣ iform (kacF4.extRoot x) (kacF4.extRoot y) :=
    fun x hx y hy => (f4_long_iform _ (hext x hx) _ (hext y hy)).1
  have hshort : ∀ n : Option (Fin Tag.F4.rank) → ℕ,
      iform (kacF4.combo n) (kacF4.combo n) = 2 → n s2 ≠ 0 ∨ n s3 ≠ 0 := by
    intro n hn
    by_contra hz
    push Not at hz
    have hsupp : ∀ x, n x ≠ 0 → x ∈ long := by
      intro x hx
      rcases x with _ | ⟨k, hk⟩
      · simp [long]
      · have hk4 : k < 4 := hk
        interval_cases k
        · simp [long]
        · simp [long]
        · exact absurd hz.1 hx
        · exact absurd hz.2 hx
    have := kacF4.four_dvd_iform_combo long hsupp hlong1 hlong2
    rw [hn] at this
    omega
  have hadj : kacF4.Adj s2 s3 := ⟨by decide, f4_short_iform.1⟩
  have hadj' : kacF4.Adj s3 s2 := ⟨by decide, f4_short_iform.2⟩
  rcases hshort n₁ e₁ with h1 | h1 <;> rcases hshort n₂ e₂ with h2 | h2
  · exact (hS _ (hn₁ _ h1) _ (hn₂ _ h2)).1 rfl
  · exact (hS _ (hn₁ _ h1) _ (hn₂ _ h2)).2 hadj
  · exact (hS _ (hn₁ _ h1) _ (hn₂ _ h2)).2 hadj'
  · exact (hS _ (hn₁ _ h1) _ (hn₂ _ h2)).1 rfl

theorem facts_F4 : kacF4.Facts where
  θ_pos := show ∀ j : Fin 4, (0 : ℤ) < ![2, 3, 4, 2] j by decide
  le_θ := kacF4.le_θ_of_list ![2, 3, 4, 2] rfl
    (show ∀ l ∈ Tag.F4.artifactRoots, ∀ j : Fin 4, (∀ k : Fin 4, 0 ≤ l.getD k 0) →
      l.getD j 0 ≤ (![2, 3, 4, 2] : Fin 4 → ℤ) j by decide +kernel)
  split := split_F4

end TagFacts

end CFSG.HardMathSupport.Timmesfeld.CrossChar

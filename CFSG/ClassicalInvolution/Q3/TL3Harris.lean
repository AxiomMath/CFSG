module

public import CFSG.ClassicalInvolution.Q3.Q3T6AutInn
public import CFSG.ClassicalInvolution.Q3.Q3PlanSplit

public section

namespace CFSG.ClassicalInvolution.Q3.Harris3

open CFSG.Open CFSG.ClassicalInvolution.Balance
open scoped MatrixGroups

private theorem sl2Three_center_sq : ∀ g : SL(2, ZMod 3), (∀ h : SL(2, ZMod 3), g * h = h * g) →
    g * g = 1 := by
  decide +kernel

private theorem sl2Three_factorization_two : (Nat.card SL(2, ZMod 3)).factorization 2 = 3 := by
  rw [Q3T6.Aut.sl2Three_natCard]
  have h : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
  rw [h, Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem sl2Three_mulAut_inner_of_pow_three {β : MulAut SL(2, ZMod 3)} (hβ : β ^ 3 = 1) :
    ∃ g : SL(2, ZMod 3), MulAut.conj g = β := by
  have h2 : (β ^ 2) ^ 2 ∈ Q3T6.inn3 := Subgroup.sq_mem_of_index_two Q3T6.inn3_index _
  have hβ4 : (β ^ 2) ^ 2 = β := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hβ, one_mul]
  rw [hβ4] at h2
  exact h2

variable {C : Type*} [Group C]

@[expose] def conjAutOf (H : Subgroup C) {d : C} (hd : d ∈ Subgroup.normalizer (H : Set C)) :
    MulAut H where
  toFun h := ⟨d * h * d⁻¹, (Subgroup.mem_normalizer_iff.mp hd h).mp h.2⟩
  invFun h := ⟨d⁻¹ * h * d, by
    have := (Subgroup.mem_normalizer_iff.mp hd (d⁻¹ * h * d)).mpr
    simpa [mul_assoc] using this (by simp [mul_assoc])⟩
  left_inv h := Subtype.ext (by simp [mul_assoc])
  right_inv h := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem conjAutOf_apply (H : Subgroup C) {d : C} (hd : d ∈ Subgroup.normalizer (H : Set C))
    (h : H) : ((conjAutOf H hd h : H) : C) = d * h * d⁻¹ :=
  rfl

theorem centralizes_of_normalizes_sl2 [Finite C] {H P : Subgroup C} (e : H ≃* SL(2, ZMod 3))
    (hPH : P ≤ H) (hP8 : Nat.card P = 8) {d : C} (hd : d ∈ Subgroup.normalizer (H : Set C))
    (hdP : ∀ p ∈ P, d * p = p * d) {h : C} (hh : h ∈ H) : d * h = h * d := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ : MulAut H := conjAutOf H hd with hσ
  set α : MulAut SL(2, ZMod 3) := (e.symm.trans σ).trans e with hα
  set P' : Subgroup SL(2, ZMod 3) := (P.subgroupOf H).map e.toMonoidHom with hP'
  have hcard : Nat.card P' = 2 ^ (Nat.card SL(2, ZMod 3)).factorization 2 := by
    rw [sl2Three_factorization_two, hP', Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv, hP8]
    norm_num
  have hfix : ∀ x ∈ Sylow.ofCard P' hcard, α x = x := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := hx
    have hpP : ((p : H) : C) ∈ P := hp
    have hσp : σ p = p := Subtype.ext (by
      rw [hσ, conjAutOf_apply, hdP _ hpP, mul_assoc, mul_inv_cancel, mul_one])
    simp [hα, hσp]
  have hα1 := Q3T6.sl2Three_mulAut_eq_one_of_fixes_sylow (Sylow.ofCard P' hcard) α hfix
  have h1 : α (e ⟨h, hh⟩) = e ⟨h, hh⟩ := by rw [hα1]; rfl
  have h2 : σ ⟨h, hh⟩ = ⟨h, hh⟩ := by
    apply e.injective
    simpa [hα] using h1
  have h3 : d * h * d⁻¹ = h := congrArg Subtype.val h2
  calc d * h = d * h * d⁻¹ * d := by group
    _ = h * d := by rw [h3]

theorem mem_of_pow_three_of_normal_sl2 {M H : Subgroup C} (e : H ≃* SL(2, ZMod 3))
    (hHM : H ≤ M) (hHn : ∀ m ∈ M, ∀ h ∈ H, m * h * m⁻¹ ∈ H)
    (hO : ∀ N : Subgroup C, N ≤ M → (∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N) →
      (∀ n ∈ N, n ^ 3 = 1) → N = ⊥)
    {x : C} (hxM : x ∈ M) (hx3 : x ^ 3 = 1)
    (hxD : ∀ c ∈ M, (∀ h ∈ H, c * h = h * c) → x * c = c * x) : x ∈ H := by
  have hxN : x ∈ Subgroup.normalizer (H : Set C) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hHn x hxM h hh, fun hh => ?_⟩
    have := hHn x⁻¹ (M.inv_mem hxM) _ hh
    simpa [mul_assoc] using this
  set σ : MulAut H := conjAutOf H hxN with hσ
  set β : MulAut SL(2, ZMod 3) := (e.symm.trans σ).trans e with hβ
  have hσ3 : σ ^ 3 = 1 := by
    ext h
    have : (σ ^ 3) h = ⟨x ^ 3 * h * (x ^ 3)⁻¹, by rw [hx3]; simp⟩ := by
      apply Subtype.ext
      simp only [hσ, pow_succ, pow_zero, one_mul, MulAut.mul_apply, conjAutOf_apply]
      group
    rw [this]
    simp [hx3]
  have hβ3 : β ^ 3 = 1 := by
    have hβpow : ∀ n : ℕ, β ^ n = (e.symm.trans (σ ^ n)).trans e := by
      intro n
      induction n with
      | zero => ext g; simp
      | succ k ih =>
        rw [pow_succ, ih, pow_succ]
        ext g
        simp [hβ]
    rw [hβpow, hσ3]
    ext g
    simp
  obtain ⟨g, hg⟩ := sl2Three_mulAut_inner_of_pow_three hβ3
  set y : C := ((e.symm g : H) : C) with hy
  have hyH : y ∈ H := (e.symm g).2
  have hconj : ∀ h ∈ H, x * h * x⁻¹ = y * h * y⁻¹ := by
    intro h hh
    have h1 : β (e ⟨h, hh⟩) = g * e ⟨h, hh⟩ * g⁻¹ := by rw [← hg]; rfl
    have h2 : σ ⟨h, hh⟩ = e.symm g * ⟨h, hh⟩ * (e.symm g)⁻¹ := by
      apply e.injective
      have : e (σ ⟨h, hh⟩) = β (e ⟨h, hh⟩) := by simp [hβ]
      rw [this, h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    have := congrArg Subtype.val h2
    simpa [hσ, conjAutOf_apply, hy] using this
  set c : C := y⁻¹ * x with hc
  have hcM : c ∈ M := M.mul_mem (M.inv_mem (hHM hyH)) hxM
  have hcH : ∀ h ∈ H, c * h = h * c := by
    intro h hh
    have := hconj h hh
    calc c * h = y⁻¹ * (x * h * x⁻¹) * x := by rw [hc]; group
      _ = y⁻¹ * (y * h * y⁻¹) * x := by rw [this]
      _ = h * c := by rw [hc]; group
  have hcZ : ∀ c' ∈ M, (∀ h ∈ H, c' * h = h * c') → c * c' = c' * c := by
    intro c' hc'M hc'H
    have h1 := hxD c' hc'M hc'H
    have h2 := hc'H y⁻¹ (H.inv_mem hyH)
    calc c * c' = y⁻¹ * (x * c') := by rw [hc]; group
      _ = y⁻¹ * (c' * x) := by rw [h1]
      _ = (y⁻¹ * c') * x := by group
      _ = (c' * y⁻¹) * x := by rw [← h2]
      _ = c' * c := by rw [hc]; group
  have hcy : c * y = y * c := hcH y hyH
  have hxyc : x = y * c := by rw [hc]; group
  have hc3 : c ^ 3 = (y ^ 3)⁻¹ := by
    have h1 : x ^ 3 = y ^ 3 * c ^ 3 := by rw [hxyc]; exact (Commute.mul_pow hcy.symm 3)
    rw [hx3] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm
  have hc3H : c ^ 3 ∈ H := by rw [hc3]; exact H.inv_mem (H.pow_mem hyH 3)
  have hc6 : c ^ 6 = 1 := by
    have hcen : ∀ k : SL(2, ZMod 3), e ⟨c ^ 3, hc3H⟩ * k = k * e ⟨c ^ 3, hc3H⟩ := by
      intro k
      have h1 : c ^ 3 * ((e.symm k : H) : C) = ((e.symm k : H) : C) * c ^ 3 :=
        Commute.pow_left (hcH _ (e.symm k).2) 3
      have h2 : (⟨c ^ 3, hc3H⟩ : H) * e.symm k = e.symm k * ⟨c ^ 3, hc3H⟩ := Subtype.ext h1
      have h3 := congrArg e h2
      simpa using h3
    have h4 := sl2Three_center_sq _ hcen
    have h5 : (⟨c ^ 3, hc3H⟩ : H) * ⟨c ^ 3, hc3H⟩ = 1 := by
      apply e.injective
      rw [map_mul, h4, map_one]
    have h6 : c ^ 3 * c ^ 3 = 1 := congrArg Subtype.val h5
    rw [show (6 : ℕ) = 3 + 3 by norm_num, pow_add, h6]
  set N : Subgroup C :=
    { carrier := {n | n ∈ M ∧ (∀ h ∈ H, n * h = h * n) ∧
        (∀ c' ∈ M, (∀ h ∈ H, c' * h = h * c') → n * c' = c' * n) ∧ n ^ 3 = 1}
      mul_mem' := by
        rintro a b ⟨haM, haH, haZ, ha3⟩ ⟨hbM, hbH, hbZ, hb3⟩
        refine ⟨M.mul_mem haM hbM, fun h hh => ?_, fun c' hc'M hc'H => ?_, ?_⟩
        · rw [mul_assoc, hbH h hh, ← mul_assoc, haH h hh, mul_assoc]
        · rw [mul_assoc, hbZ c' hc'M hc'H, ← mul_assoc, haZ c' hc'M hc'H, mul_assoc]
        · have hab : Commute a b := haZ b hbM hbH
          rw [hab.mul_pow, ha3, hb3, one_mul]
      one_mem' := ⟨M.one_mem, fun h _ => by simp, fun c' _ _ => by simp, by simp⟩
      inv_mem' := by
        rintro a ⟨haM, haH, haZ, ha3⟩
        refine ⟨M.inv_mem haM, fun h hh => ?_, fun c' hc'M hc'H => ?_, ?_⟩
        · have := haH h hh
          calc a⁻¹ * h = a⁻¹ * (h * a) * a⁻¹ := by group
            _ = a⁻¹ * (a * h) * a⁻¹ := by rw [this]
            _ = h * a⁻¹ := by group
        · have := haZ c' hc'M hc'H
          calc a⁻¹ * c' = a⁻¹ * (c' * a) * a⁻¹ := by group
            _ = a⁻¹ * (a * c') * a⁻¹ := by rw [this]
            _ = c' * a⁻¹ := by group
        · rw [inv_pow, ha3, inv_one] } with hN
  have hNM : N ≤ M := fun n hn => hn.1
  have hNn : ∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N := by
    rintro m hm n ⟨hnM, hnH, hnZ, hn3⟩
    refine ⟨M.mul_mem (M.mul_mem hm hnM) (M.inv_mem hm), fun h hh => ?_,
      fun c' hc'M hc'H => ?_, ?_⟩
    · have hh' : m⁻¹ * h * m ∈ H := by
        have := hHn m⁻¹ (M.inv_mem hm) h hh
        simpa using this
      have := hnH _ hh'
      calc m * n * m⁻¹ * h = m * (n * (m⁻¹ * h * m)) * m⁻¹ := by group
        _ = m * ((m⁻¹ * h * m) * n) * m⁻¹ := by rw [this]
        _ = h * (m * n * m⁻¹) := by group
    · have hc'' : m⁻¹ * c' * m ∈ M :=
        M.mul_mem (M.mul_mem (M.inv_mem hm) hc'M) hm
      have hc''H : ∀ h ∈ H, m⁻¹ * c' * m * h = h * (m⁻¹ * c' * m) := by
        intro h hh
        have hh' : m * h * m⁻¹ ∈ H := hHn m hm h hh
        have := hc'H _ hh'
        calc m⁻¹ * c' * m * h = m⁻¹ * (c' * (m * h * m⁻¹)) * m := by group
          _ = m⁻¹ * ((m * h * m⁻¹) * c') * m := by rw [this]
          _ = h * (m⁻¹ * c' * m) := by group
      have := hnZ _ hc'' hc''H
      calc m * n * m⁻¹ * c' = m * (n * (m⁻¹ * c' * m)) * m⁻¹ := by group
        _ = m * ((m⁻¹ * c' * m) * n) * m⁻¹ := by rw [this]
        _ = c' * (m * n * m⁻¹) := by group
    · rw [conj_pow, hn3]; group
  have hN3 : ∀ n ∈ N, n ^ 3 = 1 := fun n hn => hn.2.2.2
  have hNbot := hO N hNM hNn hN3
  have hc4N : c ^ 4 ∈ N := by
    refine ⟨M.pow_mem hcM 4, fun h hh => (Commute.pow_left (hcH h hh) 4),
      fun c' hc'M hc'H => (Commute.pow_left (hcZ c' hc'M hc'H) 4), ?_⟩
    rw [← pow_mul, show 4 * 3 = 6 + 6 by norm_num, pow_add, hc6, one_mul]
  rw [hNbot, Subgroup.mem_bot] at hc4N
  have hc2 : c ^ 2 = 1 := by
    have : c ^ 6 = c ^ 4 * c ^ 2 := by rw [← pow_add]
    rw [hc6, hc4N, one_mul] at this
    exact this.symm
  have hcH' : c ∈ H := by
    have : c = c ^ 3 := by rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add, hc2, one_mul, pow_one]
    rw [this]
    exact hc3H
  rw [hxyc]
  exact H.mul_mem hyH hcH'

theorem mem_normalizer_of_forall_conj_mem {M H : Subgroup C}
    (hHn : ∀ m ∈ M, ∀ h ∈ H, m * h * m⁻¹ ∈ H) {m : C} (hm : m ∈ M) :
    m ∈ Subgroup.normalizer (H : Set C) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hHn m hm h hh, fun hh => ?_⟩
  have := hHn m⁻¹ (M.inv_mem hm) _ hh
  simpa [mul_assoc] using this

theorem eq_of_normal_sl2 [Finite C] {M H₁ H₂ P : Subgroup C} (e₁ : H₁ ≃* SL(2, ZMod 3))
    (e₂ : H₂ ≃* SL(2, ZMod 3)) (hH₁M : H₁ ≤ M) (hH₂M : H₂ ≤ M)
    (hH₁n : ∀ m ∈ M, ∀ h ∈ H₁, m * h * m⁻¹ ∈ H₁) (hH₂n : ∀ m ∈ M, ∀ h ∈ H₂, m * h * m⁻¹ ∈ H₂)
    (hP₁ : P ≤ H₁) (hP₂ : P ≤ H₂) (hP8 : Nat.card P = 8)
    (hO : ∀ N : Subgroup C, N ≤ M → (∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N) →
      (∀ n ∈ N, n ^ 3 = 1) → N = ⊥) : H₁ = H₂ := by
  have key : ∀ a ∈ H₂, a ^ 3 = 1 → a ∈ H₁ := by
    intro a ha ha3
    refine mem_of_pow_three_of_normal_sl2 e₁ hH₁M hH₁n hO (hH₂M ha) ha3 ?_
    intro c hcM hcH
    have hcP : ∀ p ∈ P, c * p = p * c := fun p hp => hcH p (hP₁ hp)
    exact (centralizes_of_normalizes_sl2 e₂ hP₂ hP8
      (mem_normalizer_of_forall_conj_mem hH₂n hcM) hcP ha).symm
  have hle : H₂ ≤ H₁ := by
    intro x hx
    obtain ⟨a, b, c, ha, hb, hc, hg⟩ := sl2Three_exists_cubes (e₂ ⟨x, hx⟩)
    have hx' : (⟨x, hx⟩ : H₂) = e₂.symm a * e₂.symm b * e₂.symm c := by
      apply e₂.injective
      simpa using hg
    have hxv : x = ((e₂.symm a : H₂) : C) * (e₂.symm b : H₂) * (e₂.symm c : H₂) :=
      congrArg Subtype.val hx'
    have hcube : ∀ w : SL(2, ZMod 3), w ^ 3 = 1 → ((e₂.symm w : H₂) : C) ∈ H₁ := by
      intro w hw
      refine key _ (e₂.symm w).2 ?_
      have : (e₂.symm w) ^ 3 = 1 := by rw [← map_pow, hw, map_one]
      exact congrArg Subtype.val this
    rw [hxv]
    exact H₁.mul_mem (H₁.mul_mem (hcube a ha) (hcube b hb)) (hcube c hc)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Nat.card_congr e₁.toEquiv, Nat.card_congr e₂.toEquiv]

theorem odd_card_of_pow_three_eq_one [Finite C] {N : Subgroup C} (h : ∀ n ∈ N, n ^ 3 = 1) :
    Odd (Nat.card N) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 N := fun n => ⟨1, Subtype.ext (by simpa using h n n.2)⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  rw [hk]
  exact Odd.pow (by decide)

theorem normalizes_of_isSubnormal_sl2_aux [Finite C] {K P : Subgroup C} (hP8 : Nat.card P = 8)
    (hPK : ∀ g ∈ K, ∀ p ∈ P, g * p * g⁻¹ ∈ P) (hK : oddCoreIn K = ⊥) {X : Subgroup C}
    (hX : IsSubnormal X K) :
    ∀ H : Subgroup C, H ≤ X → (∀ x ∈ X, ∀ h ∈ H, x * h * x⁻¹ ∈ H) →
      Nonempty (H ≃* SL(2, ZMod 3)) → P ≤ H → ∀ g ∈ K, ∀ h ∈ H, g * h * g⁻¹ ∈ H := by
  induction hX with
  | refl => exact fun H _ hHn _ _ => hHn
  | @step X M K hXM hXn hMK ih =>
    intro H hHX hHn hH hPH
    obtain ⟨e⟩ := hH
    have hMK' : M ≤ K := isSubnormal_le hMK
    have hXK : IsSubnormal X K := IsSubnormal.step hXM hXn hMK
    have hXn' : ∀ m ∈ M, ∀ x ∈ X, m * x * m⁻¹ ∈ X := by
      intro m hm x hx
      have h1 := (Subgroup.normal_subgroupOf_iff_le_normalizer hXM).mp hXn hm
      exact (Subgroup.mem_normalizer_iff.mp h1 x).mp hx
    have hO : ∀ N : Subgroup C, N ≤ X → (∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) →
        (∀ n ∈ N, n ^ 3 = 1) → N = ⊥ := by
      intro N hNX hNn hN3
      have hNsub : IsSubnormal N K := by
        refine isSubnormal_trans (isSubnormal_of_normal_subgroupOf hNX ?_) hXK
        rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNX]
        exact fun x hx => mem_normalizer_of_forall_conj_mem hNn hx
      have := le_oddCoreIn_of_isSubnormal hNsub (odd_card_of_pow_three_eq_one hN3)
      rw [hK] at this
      exact le_bot_iff.mp this
    have hHM : ∀ m ∈ M, ∀ h ∈ H, m * h * m⁻¹ ∈ H := by
      intro m hm h hh
      set H' : Subgroup C := H.map (MulAut.conj m).toMonoidHom with hH'
      have hmem : ∀ k, k ∈ H' ↔ m⁻¹ * k * m ∈ H := by
        intro k
        constructor
        · rintro ⟨k', hk', rfl⟩
          simpa [MulAut.conj_apply, mul_assoc] using hk'
        · intro hk
          exact ⟨m⁻¹ * k * m, hk, by simp [MulAut.conj_apply, mul_assoc]⟩
      have e' : H' ≃* SL(2, ZMod 3) :=
        ((H.equivMapOfInjective (MulAut.conj m).toMonoidHom (MulAut.conj m).injective).symm).trans e
      have hH'X : H' ≤ X := by
        intro k hk
        have h1 := hHX ((hmem k).mp hk)
        have h2 := hXn' m hm _ h1
        simpa [mul_assoc] using h2
      have hH'n : ∀ x ∈ X, ∀ k ∈ H', x * k * x⁻¹ ∈ H' := by
        intro x hx k hk
        rw [hmem]
        have hx' : m⁻¹ * x * m ∈ X := by
          have := hXn' m⁻¹ (M.inv_mem hm) x hx
          simpa using this
        have := hHn _ hx' _ ((hmem k).mp hk)
        simpa [mul_assoc] using this
      have hPH' : P ≤ H' := by
        intro p hp
        rw [hmem]
        have := hPK m⁻¹ (hMK' (M.inv_mem hm)) p hp
        exact hPH (by simpa using this)
      have heq := eq_of_normal_sl2 e e' hHX hH'X hHn hH'n hPH hPH' hP8 hO
      have : m * h * m⁻¹ ∈ H' := (hmem _).mpr (by simpa [mul_assoc] using hh)
      rwa [← heq] at this
    exact ih hPK hK H (hHX.trans hXM) hHM ⟨e⟩ hPH

theorem normalizes_of_isSubnormal_sl2 [Finite C] {K H P : Subgroup C} (hHK : IsSubnormal H K)
    (e : H ≃* SL(2, ZMod 3)) (hPH : P ≤ H) (hP8 : Nat.card P = 8)
    (hPK : ∀ g ∈ K, ∀ p ∈ P, g * p * g⁻¹ ∈ P) (hK : oddCoreIn K = ⊥) :
    ∀ g ∈ K, ∀ h ∈ H, g * h * g⁻¹ ∈ H :=
  normalizes_of_isSubnormal_sl2_aux hP8 hPK hK hHK H le_rfl
    (fun _x hx _h hh => H.mul_mem (H.mul_mem hx hh) (H.inv_mem hx)) ⟨e⟩ hPH

theorem centralizes_of_isSubnormal_sl2 [Finite C] {K H P : Subgroup C} (hHK : IsSubnormal H K)
    (e : H ≃* SL(2, ZMod 3)) (hPH : P ≤ H) (hP8 : Nat.card P = 8)
    (hPK : ∀ g ∈ K, ∀ p ∈ P, g * p * g⁻¹ ∈ P) (hK : oddCoreIn K = ⊥) {d : C} (hdK : d ∈ K)
    (hdP : ∀ p ∈ P, d * p = p * d) {h : C} (hh : h ∈ H) : d * h = h * d :=
  centralizes_of_normalizes_sl2 e hPH hP8
    (mem_normalizer_of_forall_conj_mem (normalizes_of_isSubnormal_sl2 hHK e hPH hP8 hPK hK) hdK)
    hdP hh

theorem eq_of_isSubnormal_sl2 [Finite C] {K H₁ H₂ P : Subgroup C} (h₁ : IsSubnormal H₁ K)
    (h₂ : IsSubnormal H₂ K) (e₁ : H₁ ≃* SL(2, ZMod 3)) (e₂ : H₂ ≃* SL(2, ZMod 3))
    (hP₁ : P ≤ H₁) (hP₂ : P ≤ H₂) (hP8 : Nat.card P = 8)
    (hPK : ∀ g ∈ K, ∀ p ∈ P, g * p * g⁻¹ ∈ P) (hK : oddCoreIn K = ⊥) : H₁ = H₂ := by
  refine eq_of_normal_sl2 e₁ e₂ (isSubnormal_le h₁) (isSubnormal_le h₂)
    (normalizes_of_isSubnormal_sl2 h₁ e₁ hP₁ hP8 hPK hK)
    (normalizes_of_isSubnormal_sl2 h₂ e₂ hP₂ hP8 hPK hK) hP₁ hP₂ hP8 ?_
  intro N hNK hNn hN3
  have hNsub : IsSubnormal N K := by
    refine isSubnormal_of_normal_subgroupOf hNK ?_
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNK]
    exact fun x hx => mem_normalizer_of_forall_conj_mem hNn hx
  have := le_oddCoreIn_of_isSubnormal hNsub (odd_card_of_pow_three_eq_one hN3)
  rw [hK] at this
  exact le_bot_iff.mp this

end CFSG.ClassicalInvolution.Q3.Harris3

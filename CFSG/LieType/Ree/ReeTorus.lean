module

public import CFSG.LieType.Ree.ReeHolds
public import CFSG.LieType.Chevalley.TorusCentralizer

public section

namespace CFSG.LieType.Ree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

namespace ReeTag

variable (t : ReeTag)

@[expose] def cartanPair (j : Fin t.tag.rank) (β : Fin t.tag.rank → ℤ) : ℤ :=
  ∑ k, t.tag.cartan j k * β k

@[expose] def GoodChar (j : Fin t.tag.rank) (β : Fin t.tag.rank → ℤ) : Prop :=
  |t.cartanPair j β| ≤ t.prime ∧ |t.cartanPair (t.perm j) β| ≤ t.prime ∧
    ((t.cartanPair (t.perm j) β = 0 ∧ t.cartanPair j β ≠ 0) ∨
      (t.cartanPair (t.perm j) β ≠ 0 ∧ |t.cartanPair j β| < t.prime))

instance (j : Fin t.tag.rank) (β : Fin t.tag.rank → ℤ) : Decidable (t.GoodChar j β) := by
  unfold GoodChar
  infer_instance

theorem charCheck : ∀ m < t.tag.rootCertificate.roots.length,
    0 < height (t.tag.rootCertificate.root m) →
      ∃ j ∈ t.longSet, t.GoodChar j (t.tag.rootCertificate.root m) := by
  cases t <;> decide +kernel

theorem perm_long (j : Fin t.tag.rank) (hj : j ∈ t.longSet) :
    t.perm j ∉ t.longSet ∧ t.perm (t.perm j) = j := by
  revert j
  cases t <;> decide

theorem not_dvd_of_goodChar {p θ A B : ℤ} (hp : 2 ≤ p) (hθ : p ≤ θ) (hA : |A| ≤ p)
    (hB : |B| ≤ p) (h : (B = 0 ∧ A ≠ 0) ∨ (B ≠ 0 ∧ |A| < p)) :
    ¬ (p * θ ^ 2 - 1) ∣ (A + θ * B) := by
  intro hd
  have hθ0 : (0 : ℤ) < θ := by linarith
  have hE : A + θ * B ≠ 0 := by
    rcases h with ⟨rfl, hA0⟩ | ⟨hB0, hAp⟩
    · simpa using hA0
    · intro h0
      have h1 : |θ * B| = |A| := by rw [show θ * B = -A by linarith, abs_neg]
      rw [abs_mul, abs_of_pos hθ0] at h1
      have hB1 : 1 ≤ |B| := Int.one_le_abs hB0
      nlinarith
  have hlt : |A + θ * B| < p * θ ^ 2 - 1 := by
    have h1 : |A + θ * B| ≤ |A| + θ * |B| := by
      calc |A + θ * B| ≤ |A| + |θ * B| := abs_add_le _ _
        _ = |A| + θ * |B| := by rw [abs_mul, abs_of_pos hθ0]
    have h2 : θ * |B| ≤ θ * p := mul_le_mul_of_nonneg_left hB hθ0.le
    nlinarith
  exact hE (Int.eq_zero_of_abs_lt_dvd hd hlt)

variable {K : Type} [Field K] (a : ℕ)

@[expose] noncomputable def reeTorus (j : Fin t.tag.rank) (u : Kˣ) : adjointGroup t.tag K :=
  torusElement t.tag K j u * torusElement t.tag K (t.perm j) (u ^ (t.prime ^ a))

theorem reeTorus_conj (j : Fin t.tag.rank) (u : Kˣ) (β : Root t.tag) (c : K) :
    t.reeTorus a j u * (rootOperatorFamily t.tag).eltElement β c * (t.reeTorus a j u)⁻¹ =
      (rootOperatorFamily t.tag).eltElement β
        (((u ^ (t.cartanPair j β.1 + ((t.prime ^ a : ℕ) : ℤ) * t.cartanPair (t.perm j) β.1) :
          Kˣ) : K) * c) := by
  have e : ∀ x y z : adjointGroup t.tag K, x * y * z * (x * y)⁻¹ = x * (y * z * y⁻¹) * x⁻¹ :=
    fun x y z => by group
  rw [reeTorus, e, RootOperatorFamily.torusElement_mul_eltElement_mul_inv,
    RootOperatorFamily.torusElement_mul_eltElement_mul_inv]
  congr 1
  rw [← mul_assoc, ← Units.val_mul]
  congr 2
  rw [zpow_add, zpow_mul, zpow_natCast]
  rfl

variable [Finite K]

theorem reeTorus_mem_H (j : Fin t.tag.rank) (u : Kˣ) :
    t.reeTorus a j u ∈ (nativeData t.tag K).H :=
  mul_mem (torusElement_mem_H _ j u) (torusElement_mem_H _ _ _)

variable [CharP K t.prime]

theorem reeTorus_mem_reeFixed (hK : Nat.card K = t.prime ^ (2 * a + 1)) {j : Fin t.tag.rank}
    (hj : j ∈ t.longSet) (u : Kˣ) : t.reeTorus a j u ∈ reeFixed t K a := by
  obtain ⟨hρj, hρρ⟩ := t.perm_long j hj
  have hu : u ^ (t.prime ^ (2 * a + 1)) = u := by
    rw [← hK]
    have h1 : u ^ (Nat.card K - 1) = 1 := by
      rw [← Nat.card_units]
      exact pow_card_eq_one'
    calc u ^ Nat.card K = u ^ (Nat.card K - 1 + 1) := by rw [Nat.sub_add_cancel Nat.card_pos]
      _ = u := by rw [pow_succ, h1, one_mul]
  rw [mem_reeFixed, reeTorus, map_mul, reeAut_torusElement, reeAut_torusElement, hρρ]
  simp only [relationExponent, hj, hρj, ↓reduceIte]
  rw [← pow_mul, ← pow_add, show a + (a + 1) = 2 * a + 1 by ring, hu]
  exact (torusElement_commute _ _ _ _).eq

omit [CharP K t.prime] in
theorem exists_orderOf_eq_card_sub_one : ∃ u : Kˣ, orderOf u = Nat.card K - 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  exact ⟨g, by rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units]⟩

omit [Finite K] [CharP K t.prime] in
theorem exists_reeTorus_char_ne_one (ha : 1 ≤ a) (hK : Nat.card K = t.prime ^ (2 * a + 1))
    {u : Kˣ} (hu : orderOf u = Nat.card K - 1) (β : Root t.tag) (hβ : 0 < height β.1) :
    ∃ j ∈ t.longSet, ((u ^ (t.cartanPair j β.1 +
      ((t.prime ^ a : ℕ) : ℤ) * t.cartanPair (t.perm j) β.1) : Kˣ) : K) ≠ 1 := by
  have hm := t.charCheck (rootPos β) (rootPos_lt β) (by rw [root_rootPos]; exact hβ)
  rw [root_rootPos] at hm
  obtain ⟨j, hj, hA, hB, hcase⟩ := hm
  refine ⟨j, hj, fun h1 => ?_⟩
  rw [Units.val_eq_one, ← orderOf_dvd_iff_zpow_eq_one, hu, hK] at h1
  have hp2 : (2 : ℤ) ≤ t.prime := by cases t <;> decide
  have hθ : (t.prime : ℤ) ≤ ((t.prime ^ a : ℕ) : ℤ) :=
    Nat.cast_le.mpr (Nat.le_self_pow (by omega) t.prime)
  refine not_dvd_of_goodChar hp2 hθ hA hB hcase ?_
  have h1p : 1 ≤ t.prime ^ (2 * a + 1) := Nat.one_le_pow _ _ (by omega)
  have e : ((t.prime ^ (2 * a + 1) - 1 : ℕ) : ℤ) =
      (t.prime : ℤ) * ((t.prime ^ a : ℕ) : ℤ) ^ 2 - 1 := by
    rw [Nat.cast_sub h1p]
    push_cast
    ring
  rwa [e] at h1

@[expose] def longWord : (t : ReeTag) → List (Fin t.tag.rank)
  | .G2 => ([0, 1, 0, 1, 0, 1] : List (Fin 2))
  | .F4 => (List.replicate 4 ([0, 3, 1, 2, 1, 2] : List (Fin 4))).flatten

theorem isReduced_longWord : (coxeterSystem t.tag).IsReduced t.longWord :=
  isReduced_of_reducedCheck (by cases t <;> decide +kernel)

theorem negCheck_longWord : negCheck t.tag t.longWord = true := by
  cases t <;> decide +kernel

omit [CharP K t.prime] in
theorem eq_one_of_mem_U_of_forall_reeTorus (ha : 1 ≤ a) (hK : Nat.card K = t.prime ^ (2 * a + 1))
    {u₀ : Kˣ} (hu₀ : orderOf u₀ = Nat.card K - 1) {x : adjointGroup t.tag K}
    (hx : x ∈ (nativeData t.tag K).U)
    (hc : ∀ j ∈ t.longSet, t.reeTorus a j u₀ * x * (t.reeTorus a j u₀)⁻¹ = x) : x = 1 :=
  eq_one_of_mem_U_of_forall_commute (A := {h | ∃ j ∈ t.longSet, h = t.reeTorus a j u₀})
    (by rintro _ ⟨j, -, rfl⟩; exact t.reeTorus_mem_H a j u₀)
    (fun β hβ y hy hyc => by
      obtain ⟨j, hj, hne⟩ := t.exists_reeTorus_char_ne_one a ha hK hu₀ β hβ
      exact eq_one_of_conj_eltElement hne (t.reeTorus_conj a j u₀ β) hy (hyc _ ⟨j, hj, rfl⟩))
    t.isReduced_longWord t.negCheck_longWord hx (by rintro _ ⟨j, hj, rfl⟩; exact hc j hj)

end ReeTag

end CFSG.LieType.Ree

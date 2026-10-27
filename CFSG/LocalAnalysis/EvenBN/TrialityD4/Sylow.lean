module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.Data
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.LocalRing.Basic

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup
open scoped commutatorElement Pointwise

section Generic

variable {G : Type*} [Group G]

theorem commutatorElement_mul_left_eq (g n k : G) :
    ⁅g * n, k⁆ = g * ⁅n, k⁆ * g⁻¹ * ⁅g, k⁆ := by
  simp only [commutatorElement_def]
  group

theorem conj_eq_commutatorElement_mul (g n : G) : g * n * g⁻¹ = ⁅g, n⁆ * n := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_mem_of_commute {x y : G} (h : Commute x y) (N : Subgroup G) :
    ⁅x, y⁆ ∈ N := by
  rw [commutatorElement_eq_one_iff_commute.2 h]
  exact one_mem N

theorem commutatorElement_mem_comm {x y : G} {N : Subgroup G} : ⁅x, y⁆ ∈ N ↔ ⁅y, x⁆ ∈ N := by
  rw [← commutatorElement_inv, inv_mem_iff]

theorem commutatorElement_mul_mem_iff {N : Subgroup G} {g n k : G}
    (hg : g ∈ normalizer (N : Set G)) (hn : ⁅n, k⁆ ∈ N) : ⁅g * n, k⁆ ∈ N ↔ ⁅g, k⁆ ∈ N := by
  rw [commutatorElement_mul_left_eq, mul_mem_cancel_left ((mem_normalizer_iff.1 hg _).1 hn)]

theorem conj_mem_sup {H K L : Subgroup G} {g : G} (hH : ∀ n ∈ H, g * n * g⁻¹ ∈ L)
    (hK : ∀ n ∈ K, g * n * g⁻¹ ∈ L) : ∀ n ∈ H ⊔ K, g * n * g⁻¹ ∈ L := by
  have h : H ⊔ K ≤ L.comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun n hn => by simpa using hH n hn) (fun n hn => by simpa using hK n hn)
  intro n hn
  simpa using h hn

theorem mem_normalizer_sup [Finite G] {H₁ H₂ : Subgroup G} {g : G}
    (h₁ : g ∈ normalizer (H₁ : Set G)) (h₂ : g ∈ normalizer (H₂ : Set G)) :
    g ∈ normalizer ((H₁ ⊔ H₂ : Subgroup G) : Set G) :=
  mem_normalizer_fintype (conj_mem_sup
    (fun n hn => (le_sup_left : H₁ ≤ H₁ ⊔ H₂) ((mem_normalizer_iff.1 h₁ n).1 hn))
    (fun n hn => (le_sup_right : H₂ ≤ H₁ ⊔ H₂) ((mem_normalizer_iff.1 h₂ n).1 hn)))

theorem le_normalizer_of_commutator_le {H K N : Subgroup G} (hNK : N ≤ K) (h : ⁅H, K⁆ ≤ N) :
    H ≤ normalizer (K : Set G) := by
  have key : ∀ g ∈ H, ∀ k ∈ K, g * k * g⁻¹ ∈ K := fun g hg k hk => by
    rw [conj_eq_commutatorElement_mul]
    exact mul_mem (hNK (h (commutator_mem_commutator hg hk))) hk
  intro g hg
  rw [mem_normalizer_iff]
  intro k
  refine ⟨key g hg k, fun hk => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hk
  simpa [mul_assoc] using this

theorem commutator_sup_left_le {N H₁ H₂ K : Subgroup G} (hn₁ : H₁ ≤ normalizer (N : Set G))
    (hn₂ : H₂ ≤ normalizer (N : Set G)) (h₁ : ⁅H₁, K⁆ ≤ N) (h₂ : ⁅H₂, K⁆ ≤ N) :
    ⁅H₁ ⊔ H₂, K⁆ ≤ N := by
  let C : Subgroup G :=
    { carrier := {x | x ∈ normalizer (N : Set G) ∧ ∀ y ∈ K, ⁅x, y⁆ ∈ N}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun y hy => by
        rw [commutatorElement_mul_left_eq]
        exact mul_mem ((mem_normalizer_iff.1 ha.1 _).1 (hb.2 y hy)) (ha.2 y hy)⟩
      one_mem' := ⟨one_mem _, fun y _ => by
        rw [commutatorElement_one_left]
        exact one_mem N⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun y hy => by
        have e : ⁅a⁻¹, y⁆ = a⁻¹ * ⁅a, y⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (mem_normalizer_iff.1 (inv_mem ha.1) _).1 (inv_mem (ha.2 y hy))⟩ }
  have hC : H₁ ⊔ H₂ ≤ C := sup_le
    (fun x hx => ⟨hn₁ hx, fun y hy => h₁ (commutator_mem_commutator hx hy)⟩)
    (fun x hx => ⟨hn₂ hx, fun y hy => h₂ (commutator_mem_commutator hx hy)⟩)
  rw [commutator_le]
  exact fun x hx y hy => (hC hx).2 y hy

theorem commutator_sup_right_le {N H K₁ K₂ : Subgroup G} (hn₁ : K₁ ≤ normalizer (N : Set G))
    (hn₂ : K₂ ≤ normalizer (N : Set G)) (h₁ : ⁅H, K₁⁆ ≤ N) (h₂ : ⁅H, K₂⁆ ≤ N) :
    ⁅H, K₁ ⊔ K₂⁆ ≤ N := by
  rw [commutator_comm] at h₁ h₂ ⊢
  exact commutator_sup_left_le hn₁ hn₂ h₁ h₂

theorem conj_mem_commutator {H : Subgroup G} {g : G} (hg : g ∈ normalizer (H : Set G)) {x : G}
    (hx : x ∈ ⁅H, H⁆) : g * x * g⁻¹ ∈ ⁅H, H⁆ := by
  have h : ⁅H, H⁆ ≤ ⁅H, H⁆.comap (MulAut.conj g).toMonoidHom := by
    rw [commutator_le]
    intro a ha b hb
    rw [mem_comap, MulEquiv.coe_toMonoidHom, map_commutatorElement, MulAut.conj_apply,
      MulAut.conj_apply]
    exact commutator_mem_commutator ((mem_normalizer_iff.1 hg a).1 ha)
      ((mem_normalizer_iff.1 hg b).1 hb)
  simpa using h hx

theorem conj_mem_inf_centralizer {H : Subgroup G} {g : G} (hg : g ∈ normalizer (H : Set G))
    {x : G} (hx : x ∈ H ⊓ centralizer (H : Set G)) :
    g * x * g⁻¹ ∈ H ⊓ centralizer (H : Set G) := by
  refine mem_inf.2 ⟨(mem_normalizer_iff.1 hg x).1 hx.1, ?_⟩
  rw [mem_centralizer_iff]
  intro h hh
  have hh' : g⁻¹ * h * g ∈ H := (mem_normalizer_iff''.1 hg h).1 hh
  have hc := (mem_centralizer_iff.1 hx.2) _ hh'
  calc h * (g * x * g⁻¹) = g * ((g⁻¹ * h * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * h * g)) * g⁻¹ := by rw [hc]
    _ = g * x * g⁻¹ * h := by group

theorem le_normalizer_bot_subgroup (H : Subgroup G) :
    H ≤ normalizer ((⊥ : Subgroup G) : Set G) :=
  fun _ _ => mem_normalizer_iff.2 fun n => by simp

theorem le_or_le_of_forall_mem_or_mem {E A B : Subgroup G} (h : ∀ x ∈ E, x ∈ A ∨ x ∈ B) :
    E ≤ A ∨ E ≤ B := by
  by_contra hne
  push Not at hne
  obtain ⟨⟨x, hxE, hxA⟩, ⟨y, hyE, hyB⟩⟩ := And.intro (Set.not_subset.1 hne.1)
    (Set.not_subset.1 hne.2)
  have hxB : x ∈ B := (h x hxE).resolve_left hxA
  have hyA : y ∈ A := (h y hyE).resolve_right hyB
  rcases h (x * y) (mul_mem hxE hyE) with hxy | hxy
  · exact hxA (by simpa using mul_mem hxy (inv_mem hyA))
  · exact hyB (by simpa using mul_mem (inv_mem hxB) hxy)

end Generic

section RangeSubgroup

variable {X : Type*} [Group X] {A B : Type*} [AddGroup A] [AddGroup B] {x : A → X} {y : B → X}

theorem commutator_rangeSubgroup_le (hx : ∀ a b, x (a + b) = x a * x b)
    (hy : ∀ a b, y (a + b) = y a * y b) {N : Subgroup X} (h : ∀ a b, ⁅x a, y b⁆ ∈ N) :
    ⁅rangeSubgroup hx, rangeSubgroup hy⁆ ≤ N := by
  rw [commutator_le]
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  exact h a b

theorem mem_rangeSubgroup_sup_iff (hx : ∀ a b, x (a + b) = x a * x b) {H : Subgroup X}
    (hH : rangeSubgroup hx ≤ normalizer (H : Set X)) {g : X} :
    g ∈ rangeSubgroup hx ⊔ H ↔ ∃ a, ∃ n ∈ H, x a * n = g := by
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hH, Set.mem_mul]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, n, hn, rfl⟩
    exact ⟨a, n, hn, rfl⟩
  · rintro ⟨a, n, hn, rfl⟩
    exact ⟨_, ⟨a, rfl⟩, n, hn, rfl⟩

theorem commute_of_add {A : Type*} [AddCommGroup A] {x : A → X}
    (hx : ∀ a b, x (a + b) = x a * x b) (a b : A) : Commute (x a) (x b) := by
  rw [Commute, SemiconjBy, ← hx, ← hx, add_comm]

end RangeSubgroup

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem exists_σ_ne : ∃ b : d.Γ, d.σ b ≠ b := by
  by_contra h
  push Not at h
  have hle := Nat.card_le_card_of_surjective (fun c : d.Γ₀ => (c : d.Γ))
    (fun b => ⟨⟨b, h b⟩, rfl⟩)
  rw [d.card_Γ, d.card_Γ₀] at hle
  have hq := d.two_le_q
  have : q ^ 3 = q * q * q := by ring
  nlinarith

theorem σ_σ_apply (c : d.Γ) : d.σ (d.σ c) = c ^ (q ^ 2) := by
  rw [d.σ_apply, d.σ_apply, ← pow_mul, sq]

theorem exists_tr_ne_zero : ∃ c : d.Γ, d.tr c ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have := Fintype.ofFinite d.Γ
  have hq := d.two_le_q
  have hq1 : q ≠ 1 := by omega
  have hq21 : q ^ 2 ≠ 1 := by
    have : 4 ≤ q ^ 2 := by nlinarith
    omega
  set P : Polynomial d.Γ := Polynomial.X + Polynomial.X ^ q + Polynomial.X ^ (q ^ 2) with hP
  have hdeg : P.natDegree < Fintype.card d.Γ := by
    rw [← Nat.card_eq_fintype_card, d.card_Γ]
    have h1 : P.natDegree ≤ q ^ 2 := by
      refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
        · rw [Polynomial.natDegree_X]
          have : 4 ≤ q ^ 2 := by nlinarith
          omega
        · rw [Polynomial.natDegree_X_pow]
          nlinarith
      · rw [Polynomial.natDegree_X_pow]
    have h2 : q ^ 2 < q ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega
  have hzero : P = 0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
    (f := id) Function.injective_id (fun c => by
      have hc := congrArg Subtype.val (h c)
      rw [coe_fixedTrace, d.σ_σ_apply, d.σ_apply] at hc
      simpa [hP] using hc) hdeg
  have hcoeff := congrArg (fun p : Polynomial d.Γ => p.coeff 1) hzero
  simp [hP, Polynomial.coeff_X_pow, Ne.symm hq1, Ne.symm hq21] at hcoeff

theorem tr_smul (l : d.Γ₀) (c : d.Γ) : (d.tr ((l : d.Γ) * c) : d.Γ) = l * d.tr c := by
  rw [coe_fixedTrace, coe_fixedTrace, map_mul, map_mul, apply_coe_fixedSubfield,
    apply_coe_fixedSubfield]
  ring

theorem exists_tr_eq (c : d.Γ₀) : ∃ b : d.Γ, d.tr b = c := by
  obtain ⟨b₀, hb₀⟩ := d.exists_tr_ne_zero
  refine ⟨((c * (d.tr b₀)⁻¹ : d.Γ₀) : d.Γ) * b₀, Subtype.ext ?_⟩
  rw [d.tr_smul, Subfield.coe_mul, Subfield.coe_inv, mul_assoc,
    inv_mul_cancel₀ (fun h0 => hb₀ (Subtype.ext h0)), mul_one]

theorem eq_zero_of_forall_tr_mul {a : d.Γ} (h : ∀ b, d.tr (a * b) = 0) : a = 0 := by
  by_contra ha
  obtain ⟨b₀, hb₀⟩ := d.exists_tr_ne_zero
  apply hb₀
  rw [← h (a⁻¹ * b₀), ← mul_assoc, mul_inv_cancel₀ ha, one_mul]

theorem eq_zero_of_forall_twist {a : d.Γ}
    (h : ∀ b, d.σ b * d.σ (d.σ a) + d.σ (d.σ b) * d.σ a = 0) : a = 0 := by
  have h1 := h 1
  simp only [map_one, one_mul] at h1
  rw [CharTwo.add_eq_zero] at h1
  have hσa : d.σ a = a := d.σ.injective h1
  obtain ⟨b₀, hb₀⟩ := d.exists_σ_ne
  have h2 := h b₀
  rw [hσa, hσa, ← add_mul] at h2
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd (d.σ.injective (CharTwo.add_eq_zero.1 h3).symm) hb₀
  · exact h3

theorem x₁_inv (a : d.Γ) : (d.x₁ a)⁻¹ = d.x₁ a := inv_eq_of_mul_eq_one_right (d.x₁_mul_self a)

theorem x₂_inv (a : d.Γ₀) : (d.x₂ a)⁻¹ = d.x₂ a := inv_eq_of_mul_eq_one_right (d.x₂_mul_self a)

theorem x₃_inv (a : d.Γ) : (d.x₃ a)⁻¹ = d.x₃ a := inv_eq_of_mul_eq_one_right (d.x₃_mul_self a)

theorem x₄_inv (a : d.Γ) : (d.x₄ a)⁻¹ = d.x₄ a := inv_eq_of_mul_eq_one_right (d.x₄_mul_self a)

theorem x₅_inv (a : d.Γ₀) : (d.x₅ a)⁻¹ = d.x₅ a := inv_eq_of_mul_eq_one_right (d.x₅_mul_self a)

theorem x₆_inv (a : d.Γ₀) : (d.x₆ a)⁻¹ = d.x₆ a := inv_eq_of_mul_eq_one_right (d.x₆_mul_self a)

theorem x₁_mem_U₁ (a : d.Γ) : d.x₁ a ∈ d.U₁ := ⟨a, rfl⟩

theorem x₂_mem_U₂ (a : d.Γ₀) : d.x₂ a ∈ d.U₂ := ⟨a, rfl⟩

theorem x₃_mem_U₃ (a : d.Γ) : d.x₃ a ∈ d.U₃ := ⟨a, rfl⟩

theorem x₄_mem_U₄ (a : d.Γ) : d.x₄ a ∈ d.U₄ := ⟨a, rfl⟩

theorem x₅_mem_U₅ (a : d.Γ₀) : d.x₅ a ∈ d.U₅ := ⟨a, rfl⟩

theorem x₆_mem_V (a : d.Γ₀) : d.x₆ a ∈ d.V := ⟨a, rfl⟩

theorem V_le_Y : d.V ≤ d.Y := le_sup_right

theorem U₅_le_Y : d.U₅ ≤ d.Y := le_sup_left

theorem Y_le_W : d.Y ≤ d.W := le_sup_right

theorem U₄_le_W : d.U₄ ≤ d.W := le_sup_left

theorem W_le_F : d.W ≤ d.F := le_sup_right

theorem U₃_le_F : d.U₃ ≤ d.F := le_sup_left

theorem F_le_D : d.F ≤ d.D := le_sup_right

theorem U₂_le_D : d.U₂ ≤ d.D := le_sup_left

theorem F_le_M : d.F ≤ d.M := le_sup_right

theorem U₁_le_M : d.U₁ ≤ d.M := le_sup_left

theorem S_eq_sup : d.S = d.U₁ ⊔ d.D := by
  rw [S, sixClosure, closure_union, closure_union, closure_union, closure_union, closure_union]
  change closure (d.U₁ : Set X) ⊔ closure (d.U₂ : Set X) ⊔ closure (d.U₃ : Set X) ⊔
    closure (d.U₄ : Set X) ⊔ closure (d.U₅ : Set X) ⊔ closure (d.U₆ : Set X) = _
  simp only [closure_eq, D, F, W, Y, V, sup_assoc]

theorem D_le_S : d.D ≤ d.S := d.S_eq_sup ▸ le_sup_right

theorem U₁_le_S : d.U₁ ≤ d.S := d.S_eq_sup ▸ le_sup_left

theorem F_le_S : d.F ≤ d.S := d.F_le_D.trans d.D_le_S

theorem M_le_S : d.M ≤ d.S := sup_le d.U₁_le_S d.F_le_S

theorem W_le_S : d.W ≤ d.S := d.W_le_F.trans d.F_le_S

theorem Y_le_S : d.Y ≤ d.S := d.Y_le_W.trans d.W_le_S

theorem V_le_S : d.V ≤ d.S := d.V_le_Y.trans d.Y_le_S

theorem U₂_le_S : d.U₂ ≤ d.S := d.U₂_le_D.trans d.D_le_S

theorem U₃_le_S : d.U₃ ≤ d.S := d.U₃_le_F.trans d.F_le_S

theorem U₄_le_S : d.U₄ ≤ d.S := d.U₄_le_W.trans d.W_le_S

theorem U₅_le_S : d.U₅ ≤ d.S := d.U₅_le_Y.trans d.Y_le_S

theorem x₅_mem_Y (a : d.Γ₀) : d.x₅ a ∈ d.Y := d.U₅_le_Y (d.x₅_mem_U₅ a)

theorem x₆_mem_Y (a : d.Γ₀) : d.x₆ a ∈ d.Y := d.V_le_Y (d.x₆_mem_V a)

theorem x₄_mem_W (a : d.Γ) : d.x₄ a ∈ d.W := d.U₄_le_W (d.x₄_mem_U₄ a)

theorem x₅_mem_W (a : d.Γ₀) : d.x₅ a ∈ d.W := d.Y_le_W (d.x₅_mem_Y a)

theorem x₆_mem_W (a : d.Γ₀) : d.x₆ a ∈ d.W := d.Y_le_W (d.x₆_mem_Y a)

theorem x₃_mem_F (a : d.Γ) : d.x₃ a ∈ d.F := d.U₃_le_F (d.x₃_mem_U₃ a)

theorem x₄_mem_F (a : d.Γ) : d.x₄ a ∈ d.F := d.W_le_F (d.x₄_mem_W a)

theorem x₅_mem_F (a : d.Γ₀) : d.x₅ a ∈ d.F := d.W_le_F (d.x₅_mem_W a)

theorem x₆_mem_F (a : d.Γ₀) : d.x₆ a ∈ d.F := d.W_le_F (d.x₆_mem_W a)

theorem x₂_mem_D (a : d.Γ₀) : d.x₂ a ∈ d.D := d.U₂_le_D (d.x₂_mem_U₂ a)

theorem x₁_mem_M (a : d.Γ) : d.x₁ a ∈ d.M := d.U₁_le_M (d.x₁_mem_U₁ a)

theorem comm₁₂_mem_F (a : d.Γ) (b : d.Γ₀) : ⁅d.x₁ a, d.x₂ b⁆ ∈ d.F := by
  rw [d.comm₁₂]
  exact mul_mem (mul_mem (d.x₃_mem_F _) (d.x₄_mem_F _)) (d.x₅_mem_F _)

theorem comm₁₃_mem_W (a b : d.Γ) : ⁅d.x₁ a, d.x₃ b⁆ ∈ d.W := by
  rw [d.comm₁₃]
  exact mul_mem (mul_mem (d.x₄_mem_W _) (d.x₅_mem_W _)) (d.x₆_mem_W _)

theorem comm₁₄_mem_U₅ (a b : d.Γ) : ⁅d.x₁ a, d.x₄ b⁆ ∈ d.U₅ := by
  rw [d.comm₁₄]
  exact d.x₅_mem_U₅ _

theorem comm₂₅_mem_V (a b : d.Γ₀) : ⁅d.x₂ a, d.x₅ b⁆ ∈ d.V := by
  rw [d.comm₂₅]
  exact d.x₆_mem_V _

theorem comm₃₄_mem_V (a b : d.Γ) : ⁅d.x₃ a, d.x₄ b⁆ ∈ d.V := by
  rw [d.comm₃₄]
  exact d.x₆_mem_V _

theorem commutator_rangeSubgroup_le_of_commute {A B : Type*} [AddGroup A] [AddGroup B]
    {x : A → X} {y : B → X} (hx : ∀ a b, x (a + b) = x a * x b)
    (hy : ∀ a b, y (a + b) = y a * y b) (h : ∀ a b, Commute (x a) (y b)) (N : Subgroup X) :
    ⁅rangeSubgroup hx, rangeSubgroup hy⁆ ≤ N :=
  commutator_rangeSubgroup_le hx hy fun a b => commutatorElement_mem_of_commute (h a b) N

theorem S_le_centralizer_V : d.S ≤ centralizer (d.V : Set X) := by
  rw [S, sixClosure, closure_le]
  rintro g (((((⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨a, rfl⟩) | ⟨a, rfl⟩) | ⟨a, rfl⟩) | ⟨a, rfl⟩) <;>
    rw [SetLike.mem_coe, mem_centralizer_iff] <;> rintro _ ⟨b, rfl⟩
  exacts [(d.commute₁₆ a b).symm, (d.commute₂₆ a b).symm, (d.commute₃₆ a b).symm,
    (d.commute₄₆ a b).symm, (d.commute₅₆ a b).symm, commute_of_add d.x₆_add b a]

theorem commutator_S_V : ⁅d.S, d.V⁆ = ⊥ :=
  commutator_eq_bot_iff_le_centralizer.2 d.S_le_centralizer_V

theorem S_le_normalizer_V : d.S ≤ normalizer (d.V : Set X) :=
  le_normalizer_of_commutator_le bot_le d.commutator_S_V.le

theorem commutator_S_le {N K : Subgroup X} (hN : d.S ≤ normalizer (N : Set X))
    (h₁ : ⁅d.U₁, K⁆ ≤ N) (h₂ : ⁅d.U₂, K⁆ ≤ N) (h₃ : ⁅d.U₃, K⁆ ≤ N) (h₄ : ⁅d.U₄, K⁆ ≤ N)
    (h₅ : ⁅d.U₅, K⁆ ≤ N) (h₆ : ⁅d.V, K⁆ ≤ N) : ⁅d.S, K⁆ ≤ N := by
  rw [d.S_eq_sup]
  refine commutator_sup_left_le (d.U₁_le_S.trans hN) (d.D_le_S.trans hN) h₁ ?_
  refine commutator_sup_left_le (d.U₂_le_S.trans hN) (d.F_le_S.trans hN) h₂ ?_
  refine commutator_sup_left_le (d.U₃_le_S.trans hN) (d.W_le_S.trans hN) h₃ ?_
  refine commutator_sup_left_le (d.U₄_le_S.trans hN) (d.Y_le_S.trans hN) h₄ ?_
  exact commutator_sup_left_le (d.U₅_le_S.trans hN) (d.V_le_S.trans hN) h₅ h₆

theorem commutator_D_le {N K : Subgroup X} (hN : d.S ≤ normalizer (N : Set X))
    (h₂ : ⁅d.U₂, K⁆ ≤ N) (h₃ : ⁅d.U₃, K⁆ ≤ N) (h₄ : ⁅d.U₄, K⁆ ≤ N) (h₅ : ⁅d.U₅, K⁆ ≤ N)
    (h₆ : ⁅d.V, K⁆ ≤ N) : ⁅d.D, K⁆ ≤ N := by
  refine commutator_sup_left_le (d.U₂_le_S.trans hN) (d.F_le_S.trans hN) h₂ ?_
  refine commutator_sup_left_le (d.U₃_le_S.trans hN) (d.W_le_S.trans hN) h₃ ?_
  refine commutator_sup_left_le (d.U₄_le_S.trans hN) (d.Y_le_S.trans hN) h₄ ?_
  exact commutator_sup_left_le (d.U₅_le_S.trans hN) (d.V_le_S.trans hN) h₅ h₆

theorem commutator_M_le {N K : Subgroup X} (hN : d.S ≤ normalizer (N : Set X))
    (h₁ : ⁅d.U₁, K⁆ ≤ N) (h₃ : ⁅d.U₃, K⁆ ≤ N) (h₄ : ⁅d.U₄, K⁆ ≤ N) (h₅ : ⁅d.U₅, K⁆ ≤ N)
    (h₆ : ⁅d.V, K⁆ ≤ N) : ⁅d.M, K⁆ ≤ N := by
  refine commutator_sup_left_le (d.U₁_le_S.trans hN) (d.F_le_S.trans hN) h₁ ?_
  refine commutator_sup_left_le (d.U₃_le_S.trans hN) (d.W_le_S.trans hN) h₃ ?_
  refine commutator_sup_left_le (d.U₄_le_S.trans hN) (d.Y_le_S.trans hN) h₄ ?_
  exact commutator_sup_left_le (d.U₅_le_S.trans hN) (d.V_le_S.trans hN) h₅ h₆

theorem commutator_S_U₅ : ⁅d.S, d.U₅⁆ ≤ d.V :=
  d.commutator_S_le d.S_le_normalizer_V
    (commutator_rangeSubgroup_le_of_commute d.x₁_add d.x₅_add d.commute₁₅ _)
    (commutator_rangeSubgroup_le d.x₂_add d.x₅_add d.comm₂₅_mem_V)
    (commutator_rangeSubgroup_le_of_commute d.x₃_add d.x₅_add d.commute₃₅ _)
    (commutator_rangeSubgroup_le_of_commute d.x₄_add d.x₅_add d.commute₄₅ _)
    (commutator_rangeSubgroup_le_of_commute d.x₅_add d.x₅_add (commute_of_add d.x₅_add) _)
    (commutator_rangeSubgroup_le_of_commute d.x₆_add d.x₅_add
      (fun a b => (d.commute₅₆ b a).symm) _)

theorem commutator_S_Y : ⁅d.S, d.Y⁆ ≤ d.V :=
  commutator_sup_right_le (d.U₅_le_S.trans d.S_le_normalizer_V)
    (d.V_le_S.trans d.S_le_normalizer_V) d.commutator_S_U₅ (d.commutator_S_V.le.trans bot_le)

theorem S_le_normalizer_Y : d.S ≤ normalizer (d.Y : Set X) :=
  le_normalizer_of_commutator_le d.V_le_Y d.commutator_S_Y

theorem commutator_S_U₄ : ⁅d.S, d.U₄⁆ ≤ d.Y :=
  d.commutator_S_le d.S_le_normalizer_Y
    (commutator_rangeSubgroup_le d.x₁_add d.x₄_add fun a b => d.U₅_le_Y (d.comm₁₄_mem_U₅ a b))
    (commutator_rangeSubgroup_le_of_commute d.x₂_add d.x₄_add d.commute₂₄ _)
    (commutator_rangeSubgroup_le d.x₃_add d.x₄_add fun a b => d.V_le_Y (d.comm₃₄_mem_V a b))
    (commutator_rangeSubgroup_le_of_commute d.x₄_add d.x₄_add (commute_of_add d.x₄_add) _)
    (commutator_rangeSubgroup_le_of_commute d.x₅_add d.x₄_add
      (fun a b => (d.commute₄₅ b a).symm) _)
    (commutator_rangeSubgroup_le_of_commute d.x₆_add d.x₄_add
      (fun a b => (d.commute₄₆ b a).symm) _)

theorem commutator_S_W : ⁅d.S, d.W⁆ ≤ d.Y :=
  commutator_sup_right_le (d.U₄_le_S.trans d.S_le_normalizer_Y)
    (d.Y_le_S.trans d.S_le_normalizer_Y) d.commutator_S_U₄ (d.commutator_S_Y.trans d.V_le_Y)

theorem S_le_normalizer_W : d.S ≤ normalizer (d.W : Set X) :=
  le_normalizer_of_commutator_le d.Y_le_W d.commutator_S_W

theorem commutator_S_U₃ : ⁅d.S, d.U₃⁆ ≤ d.W :=
  d.commutator_S_le d.S_le_normalizer_W
    (commutator_rangeSubgroup_le d.x₁_add d.x₃_add d.comm₁₃_mem_W)
    (commutator_rangeSubgroup_le_of_commute d.x₂_add d.x₃_add d.commute₂₃ _)
    (commutator_rangeSubgroup_le_of_commute d.x₃_add d.x₃_add (commute_of_add d.x₃_add) _)
    (commutator_rangeSubgroup_le d.x₄_add d.x₃_add fun a b =>
      d.Y_le_W (d.V_le_Y (commutatorElement_mem_comm.1 (d.comm₃₄_mem_V b a))))
    (commutator_rangeSubgroup_le_of_commute d.x₅_add d.x₃_add
      (fun a b => (d.commute₃₅ b a).symm) _)
    (commutator_rangeSubgroup_le_of_commute d.x₆_add d.x₃_add
      (fun a b => (d.commute₃₆ b a).symm) _)

theorem commutator_S_F : ⁅d.S, d.F⁆ ≤ d.W :=
  commutator_sup_right_le (d.U₃_le_S.trans d.S_le_normalizer_W)
    (d.W_le_S.trans d.S_le_normalizer_W) d.commutator_S_U₃ (d.commutator_S_W.trans d.Y_le_W)

theorem S_le_normalizer_F : d.S ≤ normalizer (d.F : Set X) :=
  le_normalizer_of_commutator_le d.W_le_F d.commutator_S_F

theorem commutator_S_U₂ : ⁅d.S, d.U₂⁆ ≤ d.F :=
  d.commutator_S_le d.S_le_normalizer_F
    (commutator_rangeSubgroup_le d.x₁_add d.x₂_add d.comm₁₂_mem_F)
    (commutator_rangeSubgroup_le_of_commute d.x₂_add d.x₂_add (commute_of_add d.x₂_add) _)
    (commutator_rangeSubgroup_le_of_commute d.x₃_add d.x₂_add
      (fun a b => (d.commute₂₃ b a).symm) _)
    (commutator_rangeSubgroup_le_of_commute d.x₄_add d.x₂_add
      (fun a b => (d.commute₂₄ b a).symm) _)
    (commutator_rangeSubgroup_le d.x₅_add d.x₂_add fun a b =>
      d.W_le_F (d.Y_le_W (d.V_le_Y (commutatorElement_mem_comm.1 (d.comm₂₅_mem_V b a)))))
    (commutator_rangeSubgroup_le_of_commute d.x₆_add d.x₂_add
      (fun a b => (d.commute₂₆ b a).symm) _)

theorem commutator_S_U₁ : ⁅d.S, d.U₁⁆ ≤ d.F :=
  d.commutator_S_le d.S_le_normalizer_F
    (commutator_rangeSubgroup_le_of_commute d.x₁_add d.x₁_add (commute_of_add d.x₁_add) _)
    (commutator_rangeSubgroup_le d.x₂_add d.x₁_add fun a b =>
      commutatorElement_mem_comm.1 (d.comm₁₂_mem_F b a))
    (commutator_rangeSubgroup_le d.x₃_add d.x₁_add fun a b =>
      d.W_le_F (commutatorElement_mem_comm.1 (d.comm₁₃_mem_W b a)))
    (commutator_rangeSubgroup_le d.x₄_add d.x₁_add fun a b =>
      d.W_le_F (d.Y_le_W (d.U₅_le_Y (commutatorElement_mem_comm.1 (d.comm₁₄_mem_U₅ b a)))))
    (commutator_rangeSubgroup_le_of_commute d.x₅_add d.x₁_add
      (fun a b => (d.commute₁₅ b a).symm) _)
    (commutator_rangeSubgroup_le_of_commute d.x₆_add d.x₁_add
      (fun a b => (d.commute₁₆ b a).symm) _)

theorem commutator_S_D : ⁅d.S, d.D⁆ ≤ d.F :=
  commutator_sup_right_le (d.U₂_le_S.trans d.S_le_normalizer_F)
    (d.F_le_S.trans d.S_le_normalizer_F) d.commutator_S_U₂ (d.commutator_S_F.trans d.W_le_F)

theorem commutator_S_M : ⁅d.S, d.M⁆ ≤ d.F :=
  commutator_sup_right_le (d.U₁_le_S.trans d.S_le_normalizer_F)
    (d.F_le_S.trans d.S_le_normalizer_F) d.commutator_S_U₁ (d.commutator_S_F.trans d.W_le_F)

theorem commutator_S_S : ⁅d.S, d.S⁆ ≤ d.F := by
  have h : ⁅d.S, d.U₁ ⊔ d.D⁆ ≤ d.F := commutator_sup_right_le
    (d.U₁_le_S.trans d.S_le_normalizer_F) (d.D_le_S.trans d.S_le_normalizer_F)
    d.commutator_S_U₁ d.commutator_S_D
  rwa [← d.S_eq_sup] at h

theorem S_le_normalizer_D : d.S ≤ normalizer (d.D : Set X) :=
  le_normalizer_of_commutator_le d.F_le_D d.commutator_S_D

theorem S_le_normalizer_M : d.S ≤ normalizer (d.M : Set X) :=
  le_normalizer_of_commutator_le d.F_le_M d.commutator_S_M

theorem commutator_D_D : ⁅d.D, d.D⁆ ≤ d.V := by
  have hN := d.S_le_normalizer_V
  have h₂ : ⁅d.D, d.U₂⁆ ≤ d.V := d.commutator_D_le hN
    (commutator_rangeSubgroup_le_of_commute d.x₂_add d.x₂_add (commute_of_add d.x₂_add) _)
    (commutator_rangeSubgroup_le_of_commute d.x₃_add d.x₂_add
      (fun a b => (d.commute₂₃ b a).symm) _)
    (commutator_rangeSubgroup_le_of_commute d.x₄_add d.x₂_add
      (fun a b => (d.commute₂₄ b a).symm) _)
    (commutator_rangeSubgroup_le d.x₅_add d.x₂_add fun a b =>
      commutatorElement_mem_comm.1 (d.comm₂₅_mem_V b a))
    (commutator_rangeSubgroup_le_of_commute d.x₆_add d.x₂_add
      (fun a b => (d.commute₂₆ b a).symm) _)
  have h₃ : ⁅d.D, d.U₃⁆ ≤ d.V := d.commutator_D_le hN
    (commutator_rangeSubgroup_le_of_commute d.x₂_add d.x₃_add d.commute₂₃ _)
    (commutator_rangeSubgroup_le_of_commute d.x₃_add d.x₃_add (commute_of_add d.x₃_add) _)
    (commutator_rangeSubgroup_le d.x₄_add d.x₃_add fun a b =>
      commutatorElement_mem_comm.1 (d.comm₃₄_mem_V b a))
    (commutator_rangeSubgroup_le_of_commute d.x₅_add d.x₃_add
      (fun a b => (d.commute₃₅ b a).symm) _)
    (commutator_rangeSubgroup_le_of_commute d.x₆_add d.x₃_add
      (fun a b => (d.commute₃₆ b a).symm) _)
  have h₄ : ⁅d.D, d.U₄⁆ ≤ d.V := d.commutator_D_le hN
    (commutator_rangeSubgroup_le_of_commute d.x₂_add d.x₄_add d.commute₂₄ _)
    (commutator_rangeSubgroup_le d.x₃_add d.x₄_add d.comm₃₄_mem_V)
    (commutator_rangeSubgroup_le_of_commute d.x₄_add d.x₄_add (commute_of_add d.x₄_add) _)
    (commutator_rangeSubgroup_le_of_commute d.x₅_add d.x₄_add
      (fun a b => (d.commute₄₅ b a).symm) _)
    (commutator_rangeSubgroup_le_of_commute d.x₆_add d.x₄_add
      (fun a b => (d.commute₄₆ b a).symm) _)
  have h₅ : ⁅d.D, d.U₅⁆ ≤ d.V := (commutator_mono_left d.D_le_S).trans d.commutator_S_U₅
  have h₆ : ⁅d.D, d.V⁆ ≤ d.V :=
    (commutator_mono_left d.D_le_S).trans d.commutator_S_V.le |>.trans bot_le
  refine commutator_sup_right_le (d.U₂_le_S.trans hN) (d.F_le_S.trans hN) h₂ ?_
  refine commutator_sup_right_le (d.U₃_le_S.trans hN) (d.W_le_S.trans hN) h₃ ?_
  refine commutator_sup_right_le (d.U₄_le_S.trans hN) (d.Y_le_S.trans hN) h₄ ?_
  exact commutator_sup_right_le (d.U₅_le_S.trans hN) (d.V_le_S.trans hN) h₅ h₆

theorem commutator_F_F : ⁅d.F, d.F⁆ ≤ d.V :=
  (commutator_mono d.F_le_D d.F_le_D).trans d.commutator_D_D

theorem commutator_M_M : ⁅d.M, d.M⁆ ≤ d.W := by
  have h₁ : ⁅d.M, d.U₁⁆ ≤ d.W := d.commutator_M_le d.S_le_normalizer_W
    (commutator_rangeSubgroup_le_of_commute d.x₁_add d.x₁_add (commute_of_add d.x₁_add) _)
    (commutator_rangeSubgroup_le d.x₃_add d.x₁_add fun a b =>
      commutatorElement_mem_comm.1 (d.comm₁₃_mem_W b a))
    (commutator_rangeSubgroup_le d.x₄_add d.x₁_add fun a b =>
      d.Y_le_W (d.U₅_le_Y (commutatorElement_mem_comm.1 (d.comm₁₄_mem_U₅ b a))))
    (commutator_rangeSubgroup_le_of_commute d.x₅_add d.x₁_add
      (fun a b => (d.commute₁₅ b a).symm) _)
    (commutator_rangeSubgroup_le_of_commute d.x₆_add d.x₁_add
      (fun a b => (d.commute₁₆ b a).symm) _)
  exact commutator_sup_right_le (d.U₁_le_S.trans d.S_le_normalizer_W)
    (d.F_le_S.trans d.S_le_normalizer_W) h₁
    ((commutator_mono_left d.M_le_S).trans d.commutator_S_F)

theorem commutator_M_Y : ⁅d.M, d.Y⁆ = ⊥ := by
  refine le_bot_iff.1 (commutator_sup_right_le (le_normalizer_bot_subgroup _)
    (le_normalizer_bot_subgroup _)
    ?_ ((commutator_mono_left d.M_le_S).trans d.commutator_S_V.le))
  exact d.commutator_M_le (le_normalizer_bot_subgroup _)
    (commutator_rangeSubgroup_le_of_commute d.x₁_add d.x₅_add d.commute₁₅ _)
    (commutator_rangeSubgroup_le_of_commute d.x₃_add d.x₅_add d.commute₃₅ _)
    (commutator_rangeSubgroup_le_of_commute d.x₄_add d.x₅_add d.commute₄₅ _)
    (commutator_rangeSubgroup_le_of_commute d.x₅_add d.x₅_add (commute_of_add d.x₅_add) _)
    (commutator_rangeSubgroup_le_of_commute d.x₆_add d.x₅_add
      (fun a b => (d.commute₅₆ b a).symm) _)

theorem commutator_W_U₄ : ⁅d.W, d.U₄⁆ = ⊥ := by
  refine le_bot_iff.1 (commutator_sup_left_le (le_normalizer_bot_subgroup _)
    (le_normalizer_bot_subgroup _)
    (commutator_rangeSubgroup_le_of_commute d.x₄_add d.x₄_add (commute_of_add d.x₄_add) _) ?_)
  exact commutator_sup_left_le (le_normalizer_bot_subgroup _) (le_normalizer_bot_subgroup _)
    (commutator_rangeSubgroup_le_of_commute d.x₅_add d.x₄_add
      (fun a b => (d.commute₄₅ b a).symm) _)
    (commutator_rangeSubgroup_le_of_commute d.x₆_add d.x₄_add
      (fun a b => (d.commute₄₆ b a).symm) _)

abbrev nf : d.Γ × d.Γ₀ × d.Γ × d.Γ × d.Γ₀ × d.Γ₀ → X := sixProd d.x₁ d.x₂ d.x₃ d.x₄ d.x₅ d.x₆

theorem nf_injective : Function.Injective d.nf := fun a b h =>
  d.normal_form.injOn (Set.mem_univ a) (Set.mem_univ b) h

theorem nf_apply (a₁ : d.Γ) (a₂ : d.Γ₀) (a₃ a₄ : d.Γ) (a₅ a₆ : d.Γ₀) :
    d.nf (a₁, a₂, a₃, a₄, a₅, a₆) =
      d.x₁ a₁ * d.x₂ a₂ * d.x₃ a₃ * d.x₄ a₄ * d.x₅ a₅ * d.x₆ a₆ := rfl

theorem mem_Y_iff {g : X} : g ∈ d.Y ↔ ∃ a, ∃ n ∈ d.V, d.x₅ a * n = g :=
  mem_rangeSubgroup_sup_iff d.x₅_add (d.U₅_le_S.trans d.S_le_normalizer_V)

theorem mem_W_iff {g : X} : g ∈ d.W ↔ ∃ a, ∃ n ∈ d.Y, d.x₄ a * n = g :=
  mem_rangeSubgroup_sup_iff d.x₄_add (d.U₄_le_S.trans d.S_le_normalizer_Y)

theorem mem_F_iff {g : X} : g ∈ d.F ↔ ∃ a, ∃ n ∈ d.W, d.x₃ a * n = g :=
  mem_rangeSubgroup_sup_iff d.x₃_add (d.U₃_le_S.trans d.S_le_normalizer_W)

theorem mem_D_iff {g : X} : g ∈ d.D ↔ ∃ a, ∃ n ∈ d.F, d.x₂ a * n = g :=
  mem_rangeSubgroup_sup_iff d.x₂_add (d.U₂_le_S.trans d.S_le_normalizer_F)

theorem mem_M_iff {g : X} : g ∈ d.M ↔ ∃ a, ∃ n ∈ d.F, d.x₁ a * n = g :=
  mem_rangeSubgroup_sup_iff d.x₁_add (d.U₁_le_S.trans d.S_le_normalizer_F)

theorem mem_S_iff {g : X} : g ∈ d.S ↔ ∃ a, ∃ n ∈ d.D, d.x₁ a * n = g := by
  rw [d.S_eq_sup]
  exact mem_rangeSubgroup_sup_iff d.x₁_add (d.U₁_le_S.trans d.S_le_normalizer_D)

theorem mem_Y_coords {g : X} (hg : g ∈ d.Y) : ∃ a₅ a₆, d.nf (0, 0, 0, 0, a₅, a₆) = g := by
  obtain ⟨a₅, _, ⟨a₆, rfl⟩, rfl⟩ := d.mem_Y_iff.1 hg
  exact ⟨a₅, a₆, by simp only [nf_apply, x₁_zero, x₂_zero, x₃_zero, x₄_zero, one_mul]⟩

theorem mem_W_coords {g : X} (hg : g ∈ d.W) :
    ∃ a₄ a₅ a₆, d.nf (0, 0, 0, a₄, a₅, a₆) = g := by
  obtain ⟨a₄, n, hn, rfl⟩ := d.mem_W_iff.1 hg
  obtain ⟨a₅, a₆, rfl⟩ := d.mem_Y_coords hn
  exact ⟨a₄, a₅, a₆, by simp only [nf_apply, x₁_zero, x₂_zero, x₃_zero, x₄_zero, one_mul,
    mul_assoc]⟩

theorem mem_F_coords {g : X} (hg : g ∈ d.F) :
    ∃ a₃ a₄ a₅ a₆, d.nf (0, 0, a₃, a₄, a₅, a₆) = g := by
  obtain ⟨a₃, n, hn, rfl⟩ := d.mem_F_iff.1 hg
  obtain ⟨a₄, a₅, a₆, rfl⟩ := d.mem_W_coords hn
  exact ⟨a₃, a₄, a₅, a₆, by simp only [nf_apply, x₁_zero, x₂_zero, x₃_zero, one_mul,
    mul_assoc]⟩

theorem mem_D_coords {g : X} (hg : g ∈ d.D) :
    ∃ a₂ a₃ a₄ a₅ a₆, d.nf (0, a₂, a₃, a₄, a₅, a₆) = g := by
  obtain ⟨a₂, n, hn, rfl⟩ := d.mem_D_iff.1 hg
  obtain ⟨a₃, a₄, a₅, a₆, rfl⟩ := d.mem_F_coords hn
  exact ⟨a₂, a₃, a₄, a₅, a₆, by simp only [nf_apply, x₁_zero, x₂_zero, one_mul, mul_assoc]⟩

theorem mem_M_coords {g : X} (hg : g ∈ d.M) :
    ∃ a₁ a₃ a₄ a₅ a₆, d.nf (a₁, 0, a₃, a₄, a₅, a₆) = g := by
  obtain ⟨a₁, n, hn, rfl⟩ := d.mem_M_iff.1 hg
  obtain ⟨a₃, a₄, a₅, a₆, rfl⟩ := d.mem_F_coords hn
  exact ⟨a₁, a₃, a₄, a₅, a₆, by simp only [nf_apply, x₁_zero, x₂_zero, one_mul, mul_one,
    mul_assoc]⟩

theorem nf_x₁ (a : d.Γ) : d.nf (a, 0, 0, 0, 0, 0) = d.x₁ a := by
  simp only [nf_apply, x₂_zero, x₃_zero, x₄_zero, x₅_zero, x₆_zero, mul_one]

theorem nf_x₂ (a : d.Γ₀) : d.nf (0, a, 0, 0, 0, 0) = d.x₂ a := by
  simp only [nf_apply, x₁_zero, x₃_zero, x₄_zero, x₅_zero, x₆_zero, mul_one, one_mul]

theorem nf_x₃ (a : d.Γ) : d.nf (0, 0, a, 0, 0, 0) = d.x₃ a := by
  simp only [nf_apply, x₁_zero, x₂_zero, x₄_zero, x₅_zero, x₆_zero, mul_one, one_mul]

theorem nf_x₄ (a : d.Γ) : d.nf (0, 0, 0, a, 0, 0) = d.x₄ a := by
  simp only [nf_apply, x₁_zero, x₂_zero, x₃_zero, x₅_zero, x₆_zero, mul_one, one_mul]

theorem nf_x₅ (a : d.Γ₀) : d.nf (0, 0, 0, 0, a, 0) = d.x₅ a := by
  simp only [nf_apply, x₁_zero, x₂_zero, x₃_zero, x₄_zero, x₆_zero, mul_one, one_mul]

theorem x₆_eq_one_iff {a : d.Γ₀} : d.x₆ a = 1 ↔ a = 0 :=
  ⟨fun h => d.x₆_injective (h.trans d.x₆_zero.symm), fun h => h ▸ d.x₆_zero⟩

theorem x₅_mem_V_iff {a : d.Γ₀} : d.x₅ a ∈ d.V ↔ a = 0 := by
  refine ⟨fun ⟨b, hb⟩ => ?_, fun h => h ▸ d.x₅_zero ▸ one_mem _⟩
  have h := d.nf_injective ((show d.nf (0, 0, 0, 0, 0, b) = d.x₆ b by
    simp only [nf_apply, x₁_zero, x₂_zero, x₃_zero, x₄_zero, x₅_zero, one_mul]).trans
    (hb.trans (d.nf_x₅ a).symm))
  exact (congrArg (fun c => c.2.2.2.2.1) h).symm

theorem x₄_mem_Y_iff {a : d.Γ} : d.x₄ a ∈ d.Y ↔ a = 0 := by
  refine ⟨fun hg => ?_, fun h => h ▸ d.x₄_zero ▸ one_mem _⟩
  obtain ⟨a₅, a₆, h⟩ := d.mem_Y_coords hg
  exact (congrArg (fun c => c.2.2.2.1) (d.nf_injective (h.trans (d.nf_x₄ a).symm))).symm

theorem x₂_mem_Y_iff {a : d.Γ₀} : d.x₂ a ∈ d.Y ↔ a = 0 := by
  refine ⟨fun hg => ?_, fun h => h ▸ d.x₂_zero ▸ one_mem _⟩
  obtain ⟨a₅, a₆, h⟩ := d.mem_Y_coords hg
  exact (congrArg (fun c => c.2.1) (d.nf_injective (h.trans (d.nf_x₂ a).symm))).symm

theorem x₃_mem_W_iff {a : d.Γ} : d.x₃ a ∈ d.W ↔ a = 0 := by
  refine ⟨fun hg => ?_, fun h => h ▸ d.x₃_zero ▸ one_mem _⟩
  obtain ⟨a₄, a₅, a₆, h⟩ := d.mem_W_coords hg
  exact (congrArg (fun c => c.2.2.1) (d.nf_injective (h.trans (d.nf_x₃ a).symm))).symm

theorem x₂_mem_F_iff {a : d.Γ₀} : d.x₂ a ∈ d.F ↔ a = 0 := by
  refine ⟨fun hg => ?_, fun h => h ▸ d.x₂_zero ▸ one_mem _⟩
  obtain ⟨a₃, a₄, a₅, a₆, h⟩ := d.mem_F_coords hg
  exact (congrArg (fun c => c.2.1) (d.nf_injective (h.trans (d.nf_x₂ a).symm))).symm

theorem x₁_mem_D_iff {a : d.Γ} : d.x₁ a ∈ d.D ↔ a = 0 := by
  refine ⟨fun hg => ?_, fun h => h ▸ d.x₁_zero ▸ one_mem _⟩
  obtain ⟨a₂, a₃, a₄, a₅, a₆, h⟩ := d.mem_D_coords hg
  exact (congrArg (fun c => c.1) (d.nf_injective (h.trans (d.nf_x₁ a).symm))).symm

theorem x₂_mem_M_iff {a : d.Γ₀} : d.x₂ a ∈ d.M ↔ a = 0 := by
  refine ⟨fun hg => ?_, fun h => h ▸ d.x₂_zero ▸ one_mem _⟩
  obtain ⟨a₁, a₃, a₄, a₅, a₆, h⟩ := d.mem_M_coords hg
  exact (congrArg (fun c => c.2.1) (d.nf_injective (h.trans (d.nf_x₂ a).symm))).symm

theorem card_eq_of_nf {α : Type*} {T : Subgroup X}
    (e : α → d.Γ × d.Γ₀ × d.Γ × d.Γ × d.Γ₀ × d.Γ₀) (he : Function.Injective e)
    (hmem : ∀ c, d.nf (e c) ∈ T) (hsurj : ∀ g ∈ T, ∃ c, d.nf (e c) = g) :
    Nat.card T = Nat.card α := by
  have hrange : Set.range (d.nf ∘ e) = (T : Set X) := by
    ext g
    exact ⟨by rintro ⟨c, rfl⟩; exact hmem c, fun hg => hsurj g hg⟩
  rw [← SetLike.coe_sort_coe, ← hrange, Nat.card_range_of_injective (d.nf_injective.comp he)]

theorem card_U₁ : Nat.card d.U₁ = q ^ 3 :=
  (Nat.card_range_of_injective d.x₁_injective).trans d.card_Γ

theorem card_U₂ : Nat.card d.U₂ = q :=
  (Nat.card_range_of_injective d.x₂_injective).trans d.card_Γ₀

theorem card_U₆ : Nat.card d.U₆ = q :=
  (Nat.card_range_of_injective d.x₆_injective).trans d.card_Γ₀

theorem card_V : Nat.card d.V = q := d.card_U₆

theorem card_Y : Nat.card d.Y = q ^ 2 := by
  rw [d.card_eq_of_nf (fun c : d.Γ₀ × d.Γ₀ => (0, 0, 0, 0, c.1, c.2))
    (Function.LeftInverse.injective (g := fun a => (a.2.2.2.2.1, a.2.2.2.2.2)) fun _ => rfl)
    (fun c => by
      rw [nf_apply, d.x₁_zero, d.x₂_zero, d.x₃_zero, d.x₄_zero]
      exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (one_mem _) (one_mem _)) (one_mem _))
        (one_mem _)) (d.x₅_mem_Y _)) (d.x₆_mem_Y _))
    (fun g hg => by
      obtain ⟨a₅, a₆, h⟩ := d.mem_Y_coords hg
      exact ⟨(a₅, a₆), h⟩), Nat.card_prod, d.card_Γ₀, sq]

theorem card_W : Nat.card d.W = q ^ 5 := by
  rw [d.card_eq_of_nf (fun c : d.Γ × d.Γ₀ × d.Γ₀ => (0, 0, 0, c.1, c.2.1, c.2.2))
    (Function.LeftInverse.injective (g := fun a => (a.2.2.2.1, a.2.2.2.2.1, a.2.2.2.2.2))
      fun _ => rfl)
    (fun c => by
      rw [nf_apply, d.x₁_zero, d.x₂_zero, d.x₃_zero]
      exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (one_mem _) (one_mem _)) (one_mem _))
        (d.x₄_mem_W _)) (d.x₅_mem_W _)) (d.x₆_mem_W _))
    (fun g hg => by
      obtain ⟨a₄, a₅, a₆, h⟩ := d.mem_W_coords hg
      exact ⟨(a₄, a₅, a₆), h⟩), Nat.card_prod, Nat.card_prod, d.card_Γ, d.card_Γ₀]
  ring

theorem card_F : Nat.card d.F = q ^ 8 := by
  rw [d.card_eq_of_nf (fun c : d.Γ × d.Γ × d.Γ₀ × d.Γ₀ => (0, 0, c.1, c.2.1, c.2.2.1, c.2.2.2))
    (Function.LeftInverse.injective
      (g := fun a => (a.2.2.1, a.2.2.2.1, a.2.2.2.2.1, a.2.2.2.2.2)) fun _ => rfl)
    (fun c => by
      rw [nf_apply, d.x₁_zero, d.x₂_zero]
      exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (one_mem _) (one_mem _))
        (d.x₃_mem_F _)) (d.x₄_mem_F _)) (d.x₅_mem_F _)) (d.x₆_mem_F _))
    (fun g hg => by
      obtain ⟨a₃, a₄, a₅, a₆, h⟩ := d.mem_F_coords hg
      exact ⟨(a₃, a₄, a₅, a₆), h⟩), Nat.card_prod, Nat.card_prod, Nat.card_prod, d.card_Γ,
    d.card_Γ₀]
  ring

theorem card_D : Nat.card d.D = q ^ 9 := by
  rw [d.card_eq_of_nf (fun c : d.Γ₀ × d.Γ × d.Γ × d.Γ₀ × d.Γ₀ => (0, c))
    (Prod.mk_right_injective 0)
    (fun c => by
      rw [show ((0 : d.Γ), c) = (0, c.1, c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2) from rfl,
        nf_apply, d.x₁_zero]
      exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (one_mem _) (d.x₂_mem_D _))
        (d.F_le_D (d.x₃_mem_F _))) (d.F_le_D (d.x₄_mem_F _))) (d.F_le_D (d.x₅_mem_F _)))
        (d.F_le_D (d.x₆_mem_F _)))
    (fun g hg => by
      obtain ⟨a₂, a₃, a₄, a₅, a₆, h⟩ := d.mem_D_coords hg
      exact ⟨(a₂, a₃, a₄, a₅, a₆), h⟩), Nat.card_prod, Nat.card_prod, Nat.card_prod,
    Nat.card_prod, d.card_Γ, d.card_Γ₀]
  ring

theorem card_M : Nat.card d.M = q ^ 11 := by
  rw [d.card_eq_of_nf (fun c : d.Γ × d.Γ × d.Γ × d.Γ₀ × d.Γ₀ => (c.1, 0, c.2))
    (Function.LeftInverse.injective (g := fun a => (a.1, a.2.2)) fun _ => rfl)
    (fun c => by
      rw [show (c.1, (0 : d.Γ₀), c.2) = (c.1, 0, c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2) from rfl,
        nf_apply, d.x₂_zero]
      exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (d.x₁_mem_M _) (one_mem _))
        (d.F_le_M (d.x₃_mem_F _))) (d.F_le_M (d.x₄_mem_F _))) (d.F_le_M (d.x₅_mem_F _)))
        (d.F_le_M (d.x₆_mem_F _)))
    (fun g hg => by
      obtain ⟨a₁, a₃, a₄, a₅, a₆, h⟩ := d.mem_M_coords hg
      exact ⟨(a₁, a₃, a₄, a₅, a₆), h⟩), Nat.card_prod, Nat.card_prod, Nat.card_prod,
    Nat.card_prod, d.card_Γ, d.card_Γ₀]
  ring

theorem yamada_3_1 : (∃ P : Sylow 2 X, (P : Subgroup X) = d.S) ∧ Nat.card d.S = q ^ 12 ∧
    (d.S : Set X) = (d.U₁ : Set X) * (d.U₂ : Set X) * (d.U₃ : Set X) * (d.U₄ : Set X) *
      (d.U₅ : Set X) * (d.U₆ : Set X) ∧
    ∀ g ∈ d.S, ∃! a, d.nf a = g := by
  refine ⟨d.exists_sylow_eq_S, d.card_S, ?_, fun g hg => ?_⟩
  · ext g
    rw [SetLike.mem_coe, d.mem_S]
    constructor
    · rintro ⟨⟨a₁, a₂, a₃, a₄, a₅, a₆⟩, rfl⟩
      exact Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul
        (Set.mul_mem_mul ⟨a₁, rfl⟩ ⟨a₂, rfl⟩) ⟨a₃, rfl⟩) ⟨a₄, rfl⟩) ⟨a₅, rfl⟩) ⟨a₆, rfl⟩
    · rintro ⟨_, ⟨_, ⟨_, ⟨_, ⟨_, ⟨a₁, rfl⟩, _, ⟨a₂, rfl⟩, rfl⟩, _, ⟨a₃, rfl⟩, rfl⟩, _,
        ⟨a₄, rfl⟩, rfl⟩, _, ⟨a₅, rfl⟩, rfl⟩, _, ⟨a₆, rfl⟩, rfl⟩
      exact ⟨(a₁, a₂, a₃, a₄, a₅, a₆), rfl⟩
  · obtain ⟨a, ha⟩ := d.mem_S.1 hg
    exact ⟨a, ha, fun b hb => d.nf_injective (hb.trans ha.symm)⟩

theorem torus_mem_normalizer_U₁ (h : d.Γ₀ˣ × d.Γˣ) : d.torus h ∈ normalizer (d.U₁ : Set X) :=
  have := d.finite
  mem_normalizer_fintype fun _ ⟨a, ha⟩ => ⟨_, (d.torus_x₁ h a).symm.trans (by rw [ha])⟩

theorem torus_mem_normalizer_U₂ (h : d.Γ₀ˣ × d.Γˣ) : d.torus h ∈ normalizer (d.U₂ : Set X) :=
  have := d.finite
  mem_normalizer_fintype fun _ ⟨a, ha⟩ => ⟨_, (d.torus_x₂ h a).symm.trans (by rw [ha])⟩

theorem torus_mem_normalizer_U₃ (h : d.Γ₀ˣ × d.Γˣ) : d.torus h ∈ normalizer (d.U₃ : Set X) :=
  have := d.finite
  mem_normalizer_fintype fun _ ⟨a, ha⟩ => ⟨_, (d.torus_x₃ h a).symm.trans (by rw [ha])⟩

theorem torus_mem_normalizer_U₄ (h : d.Γ₀ˣ × d.Γˣ) : d.torus h ∈ normalizer (d.U₄ : Set X) :=
  have := d.finite
  mem_normalizer_fintype fun _ ⟨a, ha⟩ => ⟨_, (d.torus_x₄ h a).symm.trans (by rw [ha])⟩

theorem torus_mem_normalizer_U₅ (h : d.Γ₀ˣ × d.Γˣ) : d.torus h ∈ normalizer (d.U₅ : Set X) :=
  have := d.finite
  mem_normalizer_fintype fun _ ⟨a, ha⟩ => ⟨_, (d.torus_x₅ h a).symm.trans (by rw [ha])⟩

theorem torus_mem_normalizer_U₆ (h : d.Γ₀ˣ × d.Γˣ) : d.torus h ∈ normalizer (d.U₆ : Set X) :=
  have := d.finite
  mem_normalizer_fintype fun _ ⟨a, ha⟩ => ⟨_, (d.torus_x₆ h a).symm.trans (by rw [ha])⟩

theorem J_le_normalizer_V : d.J ≤ normalizer (d.V : Set X) := by
  rintro _ ⟨h, rfl⟩
  exact d.torus_mem_normalizer_U₆ h

theorem J_le_normalizer_Y : d.J ≤ normalizer (d.Y : Set X) := by
  have := d.finite
  rintro _ ⟨h, rfl⟩
  exact mem_normalizer_sup (d.torus_mem_normalizer_U₅ h) (d.torus_mem_normalizer_U₆ h)

theorem J_le_normalizer_W : d.J ≤ normalizer (d.W : Set X) := by
  have := d.finite
  rintro _ ⟨h, rfl⟩
  exact mem_normalizer_sup (d.torus_mem_normalizer_U₄ h) (d.J_le_normalizer_Y ⟨h, rfl⟩)

theorem J_le_normalizer_F : d.J ≤ normalizer (d.F : Set X) := by
  have := d.finite
  rintro _ ⟨h, rfl⟩
  exact mem_normalizer_sup (d.torus_mem_normalizer_U₃ h) (d.J_le_normalizer_W ⟨h, rfl⟩)

theorem J_le_normalizer_D : d.J ≤ normalizer (d.D : Set X) := by
  have := d.finite
  rintro _ ⟨h, rfl⟩
  exact mem_normalizer_sup (d.torus_mem_normalizer_U₂ h) (d.J_le_normalizer_F ⟨h, rfl⟩)

theorem J_le_normalizer_M : d.J ≤ normalizer (d.M : Set X) := by
  have := d.finite
  rintro _ ⟨h, rfl⟩
  exact mem_normalizer_sup (d.torus_mem_normalizer_U₁ h) (d.J_le_normalizer_F ⟨h, rfl⟩)

theorem card_J : Nat.card d.J = (q - 1) * (q ^ 3 - 1) := by
  rw [J, Nat.card_congr (MonoidHom.ofInjective d.torus_injective).symm.toEquiv, Nat.card_prod,
    Nat.card_units, Nat.card_units, d.card_Γ₀, d.card_Γ]

theorem S_inf_J : d.S ⊓ d.J = ⊥ := by
  obtain ⟨f, -, hq⟩ := d.two_pow
  refine disjoint_iff.1 (disjoint_of_coprime_natCard ?_)
  have he := d.even_q
  have h1 : Odd (q - 1) := odd_sub_one_of_even he (by have := d.two_le_q; omega)
  have h3 : Odd (q ^ 3 - 1) :=
    odd_sub_one_of_even (he.pow_of_ne_zero (by norm_num)) (Nat.one_le_pow _ _ (by
      have := d.two_le_q; omega))
  rw [d.card_S, d.card_J, hq, ← pow_mul]
  exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 (hq ▸ h1.mul h3))

end TrialityD4Data

end CFSG.LocalAnalysis.EvenBN.TrialityD4

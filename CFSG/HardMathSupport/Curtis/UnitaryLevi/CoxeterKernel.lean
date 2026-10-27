module

public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.GroupTheory.SchurZassenhaus

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CoxeterSystem

section Alternating

variable {B : Type*} {Γ : Type*} [Group Γ]

theorem prod_alternatingWord_even (g : B → Γ) (i j : B) (p : ℕ) :
    ((alternatingWord i j (2 * p)).map g).prod = (g i * g j) ^ p := by
  induction p with
  | zero => simp [alternatingWord]
  | succ p ih =>
    have h : alternatingWord i j (2 * (p + 1)) = alternatingWord i j (2 * p) ++ [i, j] := by
      rw [show 2 * (p + 1) = (2 * p + 1) + 1 by ring, alternatingWord_succ,
        alternatingWord_succ, List.concat_eq_append, List.concat_eq_append, List.append_assoc]
      rfl
    rw [h, List.map_append, List.prod_append, ih, pow_succ]
    simp

theorem prod_alternatingWord_odd (g : B → Γ) (i j : B) (p : ℕ) :
    ((alternatingWord i j (2 * p + 1)).map g).prod = (g j * g i) ^ p * g j := by
  rw [alternatingWord_succ, List.concat_eq_append, List.map_append, List.prod_append]
  have : alternatingWord j i (2 * p) = alternatingWord j i (2 * p) := rfl
  rw [prod_alternatingWord_even]
  simp

theorem pow_eq_one_of_alternating (g : B → Γ) (i j : B) (m : ℕ)
    (hi : g i * g i = 1) (hj : g j * g j = 1)
    (h : ((alternatingWord i j m).map g).prod = ((alternatingWord j i m).map g).prod) :
    (g i * g j) ^ m = 1 := by
  have hba : g j * g i = (g i * g j)⁻¹ := by
    rw [mul_inv_rev]
    exact congrArg₂ _ (eq_inv_of_mul_eq_one_left hj) (eq_inv_of_mul_eq_one_left hi)
  rcases Nat.even_or_odd' m with ⟨p, rfl | rfl⟩
  · rw [prod_alternatingWord_even, prod_alternatingWord_even, hba, inv_pow] at h
    rw [two_mul, pow_add]
    exact mul_eq_one_iff_eq_inv.2 h
  · rw [prod_alternatingWord_odd, prod_alternatingWord_odd, hba] at h
    set x := g i * g j with hx
    have h2 : (x⁻¹) ^ p * x⁻¹ = x ^ p := by
      calc (x⁻¹) ^ p * x⁻¹ = (x⁻¹) ^ p * (g j * g i) := by rw [hba]
        _ = ((x⁻¹) ^ p * g j) * g i := by rw [mul_assoc]
        _ = (x ^ p * g i) * g i := by rw [h]
        _ = x ^ p := by rw [mul_assoc, hi, mul_one]
    have h3 : x ^ p * x ^ (p + 1) = 1 := by
      rw [← h2, ← pow_succ, inv_pow, inv_mul_cancel]
    rw [show 2 * p + 1 = p + (p + 1) by ring, pow_add]
    exact h3

end Alternating


section Kernel

variable {B : Type*} [DecidableEq B] {M : CoxeterMatrix B} {W : Type*} [Group W]

theorem ker_le_of_coxeter (cs : CoxeterSystem M W) {G : Type*} [Group G] (f : B → G)
    (Z : Subgroup G) [Z.Normal] (hsq : ∀ i, f i ^ 2 ∈ Z)
    (hbr : ∀ i j, ((alternatingWord i j (M i j)).map f).prod *
      (((alternatingWord j i (M i j)).map f).prod)⁻¹ ∈ Z)
    (hgen : Subgroup.closure (Set.range f) = ⊤) (π : G →* W)
    (hπ : ∀ i, π (f i) = cs.simple i) (hZ : Z ≤ π.ker) : π.ker ≤ Z := by
  let mk : G →* G ⧸ Z := QuotientGroup.mk' Z
  let g : B → G ⧸ Z := fun i => mk (f i)
  have hinv : ∀ i, g i * g i = 1 := fun i => by
    have := (QuotientGroup.eq_one_iff (N := Z) (f i ^ 2)).2 (hsq i)
    simpa [g, mk, sq] using this
  have hprod : ∀ (l : List B), (l.map g).prod = mk ((l.map f).prod) := fun l => by
    rw [map_list_prod, List.map_map]
    rfl
  have hlift : M.IsLiftable g := fun i j => by
    by_cases hij : i = j
    · subst hij
      rw [CoxeterMatrix.diagonal, pow_one]
      exact hinv i
    · refine pow_eq_one_of_alternating g i j (M i j) (hinv i) (hinv j) ?_
      rw [hprod, hprod]
      have := hbr i j
      rw [← QuotientGroup.eq_one_iff (N := Z)] at this
      change mk _ = 1 at this
      rw [map_mul, map_inv, mul_inv_eq_one] at this
      exact this
  let φ : W →* G ⧸ Z := cs.lift ⟨g, hlift⟩
  let πbar : G ⧸ Z →* W := QuotientGroup.lift Z π (fun x hx => hZ hx)
  have hcomp : πbar.comp φ = MonoidHom.id W := by
    refine cs.ext_simple fun i => ?_
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, φ, CoxeterSystem.lift_apply_simple, g,
      πbar, mk]
    exact hπ i
  have hsurj : ∀ x : G, ∃ w : W, φ w = mk x := fun x => by
    have hx : x ∈ Subgroup.closure (Set.range f) := hgen ▸ Subgroup.mem_top x
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact ⟨cs.simple i, by simp [φ, g]⟩
    | one => exact ⟨1, by simp⟩
    | mul a b _ _ ha hb =>
      obtain ⟨w₁, h₁⟩ := ha
      obtain ⟨w₂, h₂⟩ := hb
      exact ⟨w₁ * w₂, by rw [map_mul, h₁, h₂, map_mul]⟩
    | inv a _ ha =>
      obtain ⟨w, h⟩ := ha
      exact ⟨w⁻¹, by rw [map_inv, h, map_inv]⟩
  intro x hx
  obtain ⟨w, hw⟩ := hsurj x
  have hw1 : w = 1 := by
    have h1 : πbar (mk x) = π x := rfl
    have h2 : πbar (φ w) = w := by
      have := congrArg (fun F => F w) hcomp
      simpa using this
    rw [hw, h1] at h2
    exact (h2.symm.trans (by simpa using hx))
  rw [hw1, map_one] at hw
  exact (QuotientGroup.eq_one_iff (N := Z) x).1 hw.symm

end Kernel


section Lift

theorem exists_lift_of_ker_two {G W : Type*} [Group G] [Finite G] [Group W] (ψ : G →* W)
    (A Z : Subgroup G) (hZA : Z ≤ A) (hZ : ∀ z ∈ Z, z ^ 2 = 1)
    (hker : ∀ x ∈ A, ψ x = 1 → x ∈ Z) (hZk : Z ≤ ψ.ker)
    (hZn : ∀ g ∈ A, ∀ z ∈ Z, g * z * g⁻¹ ∈ Z)
    (Q : Subgroup W) (hQ : IsPGroup 3 Q) (hsurj : ∀ q ∈ Q, ∃ a ∈ A, ψ a = q) :
    ∃ C : Subgroup G, C ≤ A ∧ (∀ x ∈ C, ∀ y ∈ C, ψ x = ψ y → x = y) ∧
      (∀ q ∈ Q, ∃ c ∈ C, ψ c = q) ∧ ∀ c ∈ C, ψ c ∈ Q := by
  classical
  let B : Subgroup G := A ⊓ Q.comap ψ
  let θ : ↥B →* W := ψ.comp B.subtype
  let Z' : Subgroup ↥B := Z.subgroupOf B
  have hZB : Z ≤ B := fun z hz => Subgroup.mem_inf.2 ⟨hZA hz, by
    show ψ z ∈ Q
    rw [MonoidHom.mem_ker.1 (hZk hz)]
    exact one_mem _⟩
  haveI : Z'.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hZn g g.2.1 n hn⟩
  have hkerθ : θ.ker = Z' := by
    ext b
    simp only [MonoidHom.mem_ker, Z', Subgroup.mem_subgroupOf]
    exact ⟨fun h => hker b b.2.1 h, fun h => MonoidHom.mem_ker.1 (hZk h)⟩
  have hrange : θ.range = Q := by
    ext q
    constructor
    · rintro ⟨b, rfl⟩
      exact b.2.2
    · intro hq
      obtain ⟨a, haA, hψ⟩ := hsurj q hq
      exact ⟨⟨a, haA, by simpa [hψ] using hq⟩, hψ⟩
  have hfQ : Finite Q := by
    rw [← hrange]
    exact Finite.of_surjective θ.rangeRestrict θ.rangeRestrict_surjective
  haveI := hfQ
  have hZ2 : IsPGroup 2 Z' := fun z => ⟨1, by
    have := hZ z (Subgroup.mem_subgroupOf.1 z.2)
    ext
    simpa [pow_one] using this⟩
  have hcard : Nat.Coprime (Nat.card Z') Z'.index := by
    obtain ⟨a, ha⟩ := hZ2.exists_card_eq
    have hq : Nat.card Q = 3 ^ (hQ.exists_card_eq.choose) := hQ.exists_card_eq.choose_spec
    have hidx : Z'.index = Nat.card Q := by
      rw [← hrange, ← hkerθ, Subgroup.index_ker]
    rw [ha, hidx, hq]
    exact Nat.Coprime.pow _ _ (by norm_num)
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcard
  refine ⟨H.map B.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨h, -, rfl⟩
    exact h.2.1
  · rintro _ ⟨h₁, hh₁, rfl⟩ _ ⟨h₂, hh₂, rfl⟩ hψ
    have h1 : h₁ * h₂⁻¹ ∈ Z' := by
      rw [← hkerθ, MonoidHom.mem_ker, map_mul, map_inv]
      exact mul_inv_eq_one.2 hψ
    have h2 : h₁ * h₂⁻¹ ∈ H := mul_mem hh₁ (inv_mem hh₂)
    have h3 : h₁ * h₂⁻¹ = 1 := by
      have := hH.disjoint
      rw [Subgroup.disjoint_def] at this
      exact this h1 h2
    exact congrArg Subtype.val (mul_inv_eq_one.1 h3)
  · intro q hq
    obtain ⟨b, hb⟩ : q ∈ θ.range := hrange ▸ hq
    obtain ⟨⟨⟨n, hn⟩, ⟨h, hh⟩⟩, hnh⟩ :=
      (Subgroup.isComplement_iff_bijective Z' H |>.1 (Subgroup.isComplement'_def.1 hH)).2 b
    have hψn : θ n = 1 := by
      rw [← MonoidHom.mem_ker, hkerθ]
      exact hn
    refine ⟨(h : G), ⟨h, hh, rfl⟩, ?_⟩
    rw [← hb, ← hnh, map_mul, hψn, one_mul]
    rfl
  · rintro _ ⟨h, -, rfl⟩
    exact h.2.2

end Lift

end CFSG.HardMathSupport.Curtis.UnitaryLevi

end

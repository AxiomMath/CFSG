module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup

variable {Y : Type} [Group Y]

theorem subgroupOf_le_iff' {X : Type} [Group X] {C A A' : Subgroup X} (hA : A ≤ C)
    (hA' : A' ≤ C) : A.subgroupOf C ≤ A'.subgroupOf C ↔ A ≤ A' := by
  constructor
  · intro h
    have := Subgroup.map_mono (f := C.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hA, Subgroup.map_subgroupOf_eq_of_le hA'] at this
  · intro h x hx
    exact h hx

theorem le_normalizer_of_conj_mem {M Q : Subgroup Y}
    (h : ∀ x ∈ M, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) : M ≤ normalizer (Q : Set Y) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro q
  refine ⟨fun hq => h x hx q hq, fun hq => ?_⟩
  have := h x⁻¹ (M.inv_mem hx) _ hq
  simpa [mul_assoc] using this

theorem fix_of_fix_radical {r : ℕ} [Fact r.Prime] (b : MulAut Y) (hb : ¬ r ∣ orderOf b)
    {P W : Subgroup Y} (hP : ∀ x ∈ P, b x ∈ P)
    (hWn : ∀ x ∈ P, ∀ w ∈ W, x * w * x⁻¹ ∈ W) (hWp : IsPGroup r ↥W)
    (hWfix : ∀ w ∈ W, b w = w) (hC : ∀ x ∈ P, (∀ w ∈ W, x * w = w * x) → x ∈ W) :
    ∀ x ∈ P, b x = x := by
  intro x hx
  set u : Y := x⁻¹ * b x with hu
  have huP : u ∈ P := P.mul_mem (P.inv_mem hx) (hP x hx)
  have huC : ∀ w ∈ W, u * w = w * u := by
    intro w hw
    have h1 : b (x * w * x⁻¹) = x * w * x⁻¹ := hWfix _ (hWn x hx w hw)
    rw [map_mul, map_mul, map_inv, hWfix w hw] at h1
    calc u * w = x⁻¹ * (b x * w * (b x)⁻¹) * b x := by simp only [hu]; group
      _ = x⁻¹ * (x * w * x⁻¹) * b x := by rw [h1]
      _ = w * u := by simp only [hu]; group
  have huW : u ∈ W := hC u huP huC
  have hbu : b u = u := hWfix u huW
  have hbx : b x = x * u := by simp only [hu]; group
  have hpow : ∀ k : ℕ, (b ^ k) x = x * u ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hbu, hbx, mul_assoc, ← pow_succ']
  have hm : u ^ orderOf b = 1 := by
    have h := hpow (orderOf b)
    rw [pow_orderOf_eq_one, MulAut.one_apply] at h
    have : x * u ^ orderOf b = x * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel this
  obtain ⟨j, hj⟩ := hWp ⟨u, huW⟩
  have hj' : u ^ r ^ j = 1 := congrArg Subtype.val hj
  have hcop : Nat.Coprime (orderOf b) (r ^ j) :=
    ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hb).symm.pow_right j
  have hu1 : u = 1 := by
    have h1 : orderOf u ∣ orderOf b := orderOf_dvd_of_pow_eq_one hm
    have h2 : orderOf u ∣ r ^ j := orderOf_dvd_of_pow_eq_one hj'
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  rw [hbx, hu1, mul_one]

theorem isCoatom_map_mulAut (b : MulAut Y) {M : Subgroup Y} (hM : IsCoatom M) :
    IsCoatom (M.map b.toMonoidHom) := by
  refine ⟨fun h => hM.1 ?_, fun A hA => ?_⟩
  · rw [eq_top_iff]
    intro y _
    have : b y ∈ M.map b.toMonoidHom := h ▸ Subgroup.mem_top _
    obtain ⟨z, hz, hzy⟩ := this
    exact b.injective hzy ▸ hz
  · have h1 : M < A.comap b.toMonoidHom := by
      refine lt_of_le_of_ne (fun x hx => hA.le ⟨x, hx, rfl⟩) ?_
      intro heq
      apply hA.ne
      rw [heq, Subgroup.map_comap_eq_self_of_surjective b.surjective]
    have h2 := hM.2 _ h1
    rw [eq_top_iff]
    intro y _
    obtain ⟨z, rfl⟩ := b.surjective y
    have : z ∈ A.comap b.toMonoidHom := h2 ▸ Subgroup.mem_top _
    exact this

theorem isCoatom_comap_mulAut (b : MulAut Y) {M : Subgroup Y} (hM : IsCoatom M) :
    IsCoatom (M.comap b.toMonoidHom) := by
  have h : M.comap b.toMonoidHom = M.map b⁻¹.toMonoidHom := by
    ext x
    constructor
    · intro hx
      exact ⟨b x, hx, b.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      show b (b⁻¹ y) ∈ M
      have h2 : b (b⁻¹ y) = y := b.apply_symm_apply y
      rw [h2]
      exact hy
  rw [h]
  exact isCoatom_map_mulAut _ hM

theorem aut_eq_one_of_two_maximals {r : ℕ} [Fact r.Prime] (b : MulAut Y) (hb : ¬ r ∣ orderOf b)
    {B M₁ M₂ Q₁ Q₂ : Subgroup Y} (hM₁ : IsCoatom M₁) (hM₂ : IsCoatom M₂) (hne : M₁ ≠ M₂)
    (hB₁ : B ≤ M₁) (hB₂ : B ≤ M₂)
    (hcl : ∀ A : Subgroup Y, IsCoatom A → B ≤ A → A = M₁ ∨ A = M₂)
    (hQ₁ : Q₁ ≠ ⊥) (hQ₁p : IsPGroup r ↥Q₁)
    (hQ₁n : ∀ x ∈ M₁, ∀ q ∈ Q₁, x * q * x⁻¹ ∈ Q₁)
    (hQ₁c : ∀ x ∈ M₁, (∀ q ∈ Q₁, x * q = q * x) → x ∈ Q₁)
    (hQ₂p : IsPGroup r ↥Q₂) (hQ₂B : Q₂ ≤ B)
    (hQ₂n : ∀ x ∈ M₂, ∀ q ∈ Q₂, x * q * x⁻¹ ∈ Q₂)
    (hQ₂c : ∀ x ∈ M₂, (∀ q ∈ Q₂, x * q = q * x) → x ∈ Q₂)
    (hnormal : ∀ R : Subgroup Y, R.Normal → IsPGroup r ↥R → R = ⊥)
    (hfix : ∀ q ∈ Q₁, b q = q) : b = 1 := by
  have hfix' : ∀ q ∈ Q₁, b⁻¹ q = q := by
    intro q hq
    have h : b⁻¹ (b q) = q := b.symm_apply_apply q
    rwa [hfix q hq] at h
  have hNQ : normalizer (Q₁ : Set Y) = M₁ := by
    have hle : M₁ ≤ normalizer (Q₁ : Set Y) := by
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro h
      refine ⟨fun hh => hQ₁n x hx h hh, fun hh => ?_⟩
      have := hQ₁n x⁻¹ (M₁.inv_mem hx) _ hh
      simpa [mul_assoc] using this
    rcases hM₁.le_iff.1 hle with h | h
    · exfalso
      apply hQ₁
      refine hnormal Q₁ ⟨fun n hn g => ?_⟩ hQ₁p
      have : g ∈ normalizer (Q₁ : Set Y) := h ▸ Subgroup.mem_top g
      exact (Subgroup.mem_normalizer_iff.1 this n).1 hn
    · exact h
  have hbM₁ : ∀ x ∈ M₁, b x ∈ M₁ := by
    intro x hx
    rw [← hNQ, Subgroup.mem_normalizer_iff]
    intro h
    have key : b x * h * (b x)⁻¹ = b (x * b⁻¹ h * x⁻¹) := by simp [map_mul]
    constructor
    · intro hh
      have h1 := hQ₁n x hx h hh
      rw [key, hfix' h hh, hfix _ h1]
      exact h1
    · intro hh
      rw [key] at hh
      have h1 : x * b⁻¹ h * x⁻¹ ∈ Q₁ := by
        have h2 : b⁻¹ (b (x * b⁻¹ h * x⁻¹)) = x * b⁻¹ h * x⁻¹ := b.symm_apply_apply _
        rw [hfix' _ hh] at h2
        rw [← h2]
        exact hh
      have h3 : b⁻¹ h ∈ Q₁ := by
        have := hQ₁n x⁻¹ (M₁.inv_mem hx) _ h1
        simpa [mul_assoc] using this
      have h4 : b (b⁻¹ h) = h := b.apply_symm_apply h
      rw [hfix _ h3] at h4
      rw [← h4]
      exact h3
  have hM₁fix : ∀ x ∈ M₁, b x = x :=
    fix_of_fix_radical b hb hbM₁ hQ₁n hQ₁p hfix hQ₁c
  have hbM₂ : M₂.map b.toMonoidHom = M₂ := by
    have hBfix : ∀ x ∈ B, b x = x := fun x hx => hM₁fix x (hB₁ hx)
    have hBle : B ≤ M₂.map b.toMonoidHom := fun x hx => ⟨x, hB₂ hx, hBfix x hx⟩
    rcases hcl _ (isCoatom_map_mulAut b hM₂) hBle with h | h
    · exfalso
      apply hne
      have h1 : M₁.map b.toMonoidHom = M₁ := by
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          show b z ∈ M₁
          rw [hM₁fix z hz]
          exact hz
        · intro hy
          exact ⟨y, hy, hM₁fix y hy⟩
      rw [← h1] at h
      exact (Subgroup.map_injective b.injective h).symm
    · exact h
  have hbM₂' : ∀ x ∈ M₂, b x ∈ M₂ := fun x hx => hbM₂ ▸ ⟨x, hx, rfl⟩
  have hM₂fix : ∀ x ∈ M₂, b x = x :=
    fix_of_fix_radical b hb hbM₂' hQ₂n hQ₂p (fun q hq => hM₁fix q (hB₁ (hQ₂B hq))) hQ₂c
  have hsup : M₁ ⊔ M₂ = ⊤ := by
    rcases hM₁.le_iff.1 (le_sup_left : M₁ ≤ M₁ ⊔ M₂) with h | h
    · exact h
    · exfalso
      have h2 : M₂ ≤ M₁ := h ▸ le_sup_right
      rcases hM₂.le_iff.1 h2 with h3 | h3
      · exact hM₁.1 h3
      · exact hne h3
  have hle : M₁ ⊔ M₂ ≤ MonoidHom.eqLocus b.toMonoidHom (MonoidHom.id Y) :=
    sup_le (fun x hx => hM₁fix x hx) (fun x hx => hM₂fix x hx)
  rw [hsup] at hle
  ext y
  exact hle (Subgroup.mem_top y)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

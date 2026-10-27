module

public import CFSG.LinearAlgebra.CoprimeActions.CoprimePGroupFixedCoset
public import CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialOddQuotientAutFaithfulness

public section



namespace CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift


open CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialOddQuotientAutFaithfulness


variable {E : Type*} [Group E]


@[expose] noncomputable def quotientMap (α : MulAut E) (N : Subgroup E) [N.Normal]
    (hN : ∀ n ∈ N, α n ∈ N) : E ⧸ N →* E ⧸ N :=
  QuotientGroup.map N N α.toMonoidHom (fun n hn => hN n hn)


theorem quotientMap_mk (α : MulAut E) (N : Subgroup E) [N.Normal]
    (hN : ∀ n ∈ N, α n ∈ N) (x : E) :
    quotientMap α N hN (x : E ⧸ N) = ((α x : E) : E ⧸ N) := rfl


theorem fixed_lift [Finite E] {r : ℕ} [Fact r.Prime] (α : MulAut E) (hα : α ^ r = 1)
    (N : Subgroup E) (hNn : N.Normal) (hN : ∀ n ∈ N, α n ∈ N)
    (hr : ¬ r ∣ Nat.card N) (x : E) (hx : α x * x⁻¹ ∈ N) :
    ∃ y : E, y * x⁻¹ ∈ N ∧ α y = y := by
  set B : Subgroup (MulAut E) := Subgroup.zpowers α with hB
  have hord : orderOf α ∣ r := orderOf_dvd_of_pow_eq_one hα
  have hBp : IsPGroup r B := by
    rcases (Nat.dvd_prime Fact.out).mp hord with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [hB, Nat.card_zpowers, h]; simp)
    · exact IsPGroup.of_card (n := 1) (by rw [hB, Nat.card_zpowers, h]; simp)
  have hpow : ∀ n : ℕ, ∀ m ∈ N, (α ^ n) m ∈ N := by
    intro n
    induction n with
    | zero => intro m hm; simpa using hm
    | succ k ih =>
      intro m hm
      rw [pow_succ]
      exact ih _ (hN m hm)
  have hmem : ∀ b : B, ∃ n : ℕ, α ^ n = (b : MulAut E) := by
    intro b
    exact (mem_powers_iff_mem_zpowers).mpr b.2
  have hxB : ∀ n : ℕ, (α ^ n) x * x⁻¹ ∈ N := by
    intro n
    induction n with
    | zero => simp [N.one_mem]
    | succ k ih =>
      rw [pow_succ']
      have h : (α * α ^ k) x * x⁻¹ = α ((α ^ k) x * x⁻¹) * (α x * x⁻¹) := by
        simp [mul_assoc]
      rw [h]
      exact N.mul_mem (hN _ ih) hx
  obtain ⟨y, hy1, hy2⟩ := CFSG.LinearAlgebra.CoprimeActions.CoprimePGroupFixedCoset.exists_fixed (p := r) hBp
    B.subtype N hNn (fun b m hm => by
      obtain ⟨n, hn⟩ := hmem b
      have : (B.subtype b) = α ^ n := hn.symm
      rw [this]; exact hpow n m hm) hr x (fun b => by
      obtain ⟨n, hn⟩ := hmem b
      have : (B.subtype b) = α ^ n := hn.symm
      rw [this]; exact hxB n)
  exact ⟨y, hy1, hy2 ⟨α, Subgroup.mem_zpowers α⟩⟩


theorem fixed_quotient_iff [Finite E] {r : ℕ} [Fact r.Prime] (α : MulAut E) (hα : α ^ r = 1)
    (N : Subgroup E) [hNn : N.Normal] (hN : ∀ n ∈ N, α n ∈ N)
    (hr : ¬ r ∣ Nat.card N) (z : E ⧸ N) :
    quotientMap α N hN z = z ↔ ∃ y : E, (y : E ⧸ N) = z ∧ α y = y := by
  constructor
  · intro h
    induction z using QuotientGroup.induction_on with
    | H x =>
      rw [quotientMap_mk, QuotientGroup.eq_iff_div_mem] at h
      have hx : α x * x⁻¹ ∈ N := by simpa [div_eq_mul_inv] using h
      obtain ⟨y, hy, hy'⟩ := fixed_lift α hα N hNn hN hr x hx
      refine ⟨y, ?_, hy'⟩
      rw [QuotientGroup.eq_iff_div_mem]
      simpa [div_eq_mul_inv] using hy
  · rintro ⟨y, rfl, hy⟩
    rw [quotientMap_mk, hy]


theorem center_quotient_fixed_iff [Finite E] {r : ℕ} [Fact r.Prime] (α : MulAut E)
    (hα : α ^ r = 1) (hr : ¬ r ∣ Nat.card (Subgroup.center E))
    (hfix : ∀ y : E, α y = y ↔ y ∈ Subgroup.center E) (z : E ⧸ Subgroup.center E) :
    quotientHom E α z = z ↔ z = 1 := by
  induction z using QuotientGroup.induction_on with
  | H x =>
    have hN : ∀ n ∈ Subgroup.center E, α n ∈ Subgroup.center E := fun n hn => by
      rw [(hfix n).mpr hn]; exact hn
    have h := fixed_quotient_iff α hα (Subgroup.center E) hN hr (x : E ⧸ Subgroup.center E)
    have e : quotientHom E α (x : E ⧸ Subgroup.center E) = quotientMap α _ hN (x : E ⧸ Subgroup.center E) := rfl
    rw [e, h]
    constructor
    · rintro ⟨y, hy, hy'⟩
      rw [← hy, QuotientGroup.eq_one_iff]
      exact (hfix y).mp hy'
    · intro h1
      rw [QuotientGroup.eq_one_iff] at h1
      exact ⟨x, rfl, (hfix x).mpr h1⟩


end CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift

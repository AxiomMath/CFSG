module

public import CFSG.LieType.SeitzGeneration.OrthThree
public import CFSG.LieType.SeitzGeneration.RegimesOuterNarrow

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open

section Independent

variable {G : Type*} [Group G] {p : ℕ}

theorem exists_elemAbelian_sq_of_independent (hp : p.Prime) {e₁ e₂ : G} (h12 : Commute e₁ e₂)
    (h₁ : e₁ ^ p = 1) (h₂ : e₂ ^ p = 1)
    (hi : ∀ i j : ℤ, e₁ ^ i * e₂ ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j) :
    ∃ F : Subgroup G, IsElemAbelian p F ∧ Nat.card F = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hne1 : e₁ ≠ 1 := fun h => by
    have := (hi 1 0 (by rw [h]; simp)).1
    exact hp.one_lt.ne' (Nat.dvd_one.mp (by exact_mod_cast this))
  have hne2 : e₂ ≠ 1 := fun h => by
    have := (hi 0 1 (by rw [h]; simp)).2
    exact hp.one_lt.ne' (Nat.dvd_one.mp (by exact_mod_cast this))
  have ho₁ : orderOf e₁ = p := orderOf_eq_prime h₁ hne1
  have ho₂ : orderOf e₂ = p := orderOf_eq_prime h₂ hne2
  have hc12 : ∀ (a : ↥(Subgroup.zpowers e₁)) (b : ↥(Subgroup.zpowers e₂)),
      Commute ((Subgroup.zpowers e₁).subtype a) ((Subgroup.zpowers e₂).subtype b) := by
    intro a b
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp b.2
    change Commute (a : G) (b : G)
    rw [← hk, ← hl]
    exact h12.zpow_zpow k l
  let f₂ : ↥(Subgroup.zpowers e₁) × ↥(Subgroup.zpowers e₂) →* G :=
    MonoidHom.noncommCoprod (Subgroup.zpowers e₁).subtype (Subgroup.zpowers e₂).subtype hc12
  have hf : Function.Injective f₂ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, b⟩ hab
    have hab' : (a : G) * b = 1 := hab
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp b.2
    rw [← hk, ← hl] at hab'
    obtain ⟨hpk, hpl⟩ := hi k l hab'
    have ha : a = 1 := by
      apply Subtype.ext
      rw [← hk]
      obtain ⟨n, rfl⟩ := hpk
      rw [zpow_mul, zpow_natCast, h₁, one_zpow]
      rfl
    have hb : b = 1 := by
      apply Subtype.ext
      rw [← hl]
      obtain ⟨n, rfl⟩ := hpl
      rw [zpow_mul, zpow_natCast, h₂, one_zpow]
      rfl
    rw [ha, hb]
    rfl
  have hcard : Nat.card (↥(Subgroup.zpowers e₁) × ↥(Subgroup.zpowers e₂)) = p ^ 2 := by
    rw [Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, ho₁, ho₂]
    ring
  refine ⟨f₂.range, ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩,
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans hcard⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    change (a : G) * b = b * a
    rw [← hx, ← hz, ← map_mul, ← map_mul]
    congr 1
    exact Prod.ext (mul_comm' x.1 z.1) (mul_comm' x.2 z.2)
  · obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    rw [← map_pow]
    have hpow : ∀ (e : G) (he : e ^ p = 1) (a : ↥(Subgroup.zpowers e)), a ^ p = 1 := by
      intro e he a
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
      apply Subtype.ext
      change (a : G) ^ p = 1
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he, one_zpow]
    have : x ^ p = 1 := Prod.ext (hpow e₁ h₁ x.1) (hpow e₂ h₂ x.2)
    rw [this, map_one]

theorem false_of_two_independent (hp : p.Prime) (hr : RankLE1 p G) {e₁ e₂ : G}
    (h12 : Commute e₁ e₂) (h₁ : e₁ ^ p = 1) (h₂ : e₂ ^ p = 1)
    (hi : ∀ i j : ℤ, e₁ ^ i * e₂ ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j) : False := by
  obtain ⟨F, hF, hcard⟩ := exists_elemAbelian_sq_of_independent hp h12 h₁ h₂ hi
  have := hr F hF
  rw [hcard] at this
  have h2 : p ^ 2 = p * p := by ring
  have := hp.one_lt
  nlinarith

end Independent

section Scope

variable {P : Type*} [Group P] {p : ℕ}

theorem finite_mulAut [Finite P] : Finite (MulAut P) :=
  Finite.of_injective (fun α : MulAut P => (α : P → P)) fun _ _ h => MulEquiv.ext (congrFun h)

theorem mulAut_mul_conj_mul_inv (φ : MulAut P) (x : P) :
    φ * MulAut.conj x * φ⁻¹ = MulAut.conj (φ x) := by
  ext y
  simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply]

theorem mem_range_conj_of_pow_mem {f : MulAut P} (hp : p.Prime) (hf : f ^ p = 1) {l : ℤ}
    (hl : ¬ (p : ℤ) ∣ l) (h : f ^ l ∈ (MulAut.conj : P →* MulAut P).range) :
    f ∈ (MulAut.conj : P →* MulAut P).range := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨a, b, hab⟩ : IsCoprime (p : ℤ) l :=
    (Irreducible.coprime_iff_not_dvd hpp.irreducible).mpr hl
  have hfp : f ^ (p : ℤ) = 1 := by rw [zpow_natCast, hf]
  have h1 : f = (f ^ l) ^ b := by
    calc f = f ^ (a * (p : ℤ) + b * l) := by rw [hab, zpow_one]
      _ = (f ^ (p : ℤ)) ^ a * (f ^ l) ^ b := by
          rw [zpow_add, mul_comm a, mul_comm b, _root_.zpow_mul, _root_.zpow_mul]
      _ = (f ^ l) ^ b := by rw [hfp, one_zpow, one_mul]
  rw [h1]
  exact zpow_mem h b

theorem NarrowScope.false_of_fixed_pair [Finite P] (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : P →* MulAut P)) {E : Subgroup (MulAut P)}
    (hs : NarrowScope p E) {f : MulAut P} (hfE : f ∈ E) (hf : f ^ p = 1)
    (hfout : ∀ x, f ≠ MulAut.conj x) {α β : P} (hcomm : Commute α β) (hα : α ^ p = 1)
    (hβ : β ^ p = 1) (hind : ∀ i j : ℤ, α ^ i * β ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j)
    (hfα : f α = α) (hfβ : f β = β) : False := by
  rcases hs.2 with h1 | h2
  · exact false_of_two_independent hp h1 hcomm hα hβ hind
  · have := finite_mulAut (P := P)
    set X : Subgroup (MulAut P) := (MulAut.conj : P →* MulAut P).range ⊔ E with hX
    have hαX : MulAut.conj α ∈ X := Subgroup.mem_sup_left ⟨α, rfl⟩
    have hβX : MulAut.conj β ∈ X := Subgroup.mem_sup_left ⟨β, rfl⟩
    have hfX : f ∈ X := Subgroup.mem_sup_right hfE
    let e₁ : X := ⟨MulAut.conj α, hαX⟩
    let e₂ : X := ⟨MulAut.conj β, hβX⟩
    let e₃ : X := ⟨f, hfX⟩
    have hcf : ∀ x : P, f x = x → Commute (MulAut.conj x) f := fun x hx => by
      have := mulAut_mul_conj_mul_inv f x
      rw [hx] at this
      exact ((mul_inv_eq_iff_eq_mul.mp this).symm : MulAut.conj x * f = f * MulAut.conj x)
    refine false_of_three_independent (e₁ := e₁) (e₂ := e₂) (e₃ := e₃) hp h2 ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact Subtype.ext (by
        change MulAut.conj α * MulAut.conj β = MulAut.conj β * MulAut.conj α
        rw [← map_mul, ← map_mul, hcomm.eq])
    · exact Subtype.ext (hcf α hfα).eq
    · exact Subtype.ext (hcf β hfβ).eq
    · exact Subtype.ext (by
        change MulAut.conj α ^ p = 1
        rw [← map_pow, hα, map_one])
    · exact Subtype.ext (by
        change MulAut.conj β ^ p = 1
        rw [← map_pow, hβ, map_one])
    · exact Subtype.ext hf
    · intro i j l hijl
      have h3 : MulAut.conj α ^ i * MulAut.conj β ^ j * f ^ l = 1 := by
        have := congrArg Subtype.val hijl
        simpa [e₁, e₂, e₃] using this
      have hfl : f ^ l = (MulAut.conj (α ^ i * β ^ j))⁻¹ := by
        rw [map_mul, map_zpow, map_zpow]
        exact eq_inv_of_mul_eq_one_right h3
      have hpl : (p : ℤ) ∣ l := by
        by_contra hl
        refine hfout _ (mem_range_conj_of_pow_mem hp hf hl ?_).choose_spec.symm
        rw [hfl]
        exact inv_mem ⟨_, rfl⟩
      have hfl1 : f ^ l = 1 := by
        obtain ⟨m, rfl⟩ := hpl
        rw [_root_.zpow_mul, zpow_natCast, hf, one_zpow]
      rw [hfl1, mul_one, ← map_zpow, ← map_zpow, ← map_mul] at h3
      have := hind i j (hinj (by rw [h3, map_one]))
      exact ⟨this.1, this.2, hpl⟩

end Scope

end CFSG.LieType.SeitzGeneration

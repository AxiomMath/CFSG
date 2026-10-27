module

public import CFSG.ClassicalInvolution.Q3.TL4ModelFacts28
public import CFSG.ClassicalInvolution.Q3.AE.Models
public import CFSG.ClassicalInvolution.Q3.AE.Twins

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

namespace Mdl117

variable {n : ℕ}

@[expose] noncomputable def permQ (n : ℕ) : AEQ n →* Equiv.Perm (Fin n) :=
  QuotientGroup.lift (piSub n) (permHom n) fun a ha => by
    rcases ha with rfl | rfl
    · rfl
    · rfl

theorem permQ_mkQ (a : Wr n) : permQ n (mkQ n a) = a.perm := rfl

theorem kList_perm_eq : ∀ a ∈ kList, ∀ b ∈ kList, a.perm = b.perm → b = a ∨ b = a * zQ := by
  decide +kernel

theorem eq_or_eq_mul_zOf_of_perm_eq (ι : Fin 4 ↪ Fin n) {a b : Wr n} (ha : a ∈ memK ι)
    (hb : b ∈ memK ι) (h : a.perm = b.perm) : b = a ∨ b = a * zOf ι := by
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  have hp : a'.perm = b'.perm := Equiv.ext fun i => by
    have := congrArg (fun σ : Equiv.Perm (Fin n) => σ (ι i)) h
    simp only [embed_perm, embedPerm_apply] at this
    exact ι.injective this
  rcases kList_perm_eq a' ha' b' hb' hp with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (map_mul _ _ _)

theorem eq_or_eq_mul_zBar (α : Finset (Fin n)) (h : α.card = 4) {x y : AEQ n}
    (hx : x ∈ memBar α h true) (hy : y ∈ memBar α h true) (hp : permQ n x = permQ n y) :
    y = x ∨ y = x * zBar α h := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  rw [permQ_mkQ, permQ_mkQ] at hp
  rcases eq_or_eq_mul_zOf_of_perm_eq (emb α h) ha hb hp with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (map_mul _ _ _)

theorem exists_memBar_false_perm (α : Finset (Fin n)) (h : α.card = 4) {x : AEQ n}
    (hx : x ∈ memBar α h true) : ∃ y ∈ memBar α h false, permQ n y = permQ n x := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, hab⟩ := (memK_mul_vec (emb α h)).1 a ha
  refine ⟨mkQ n b, ⟨b, hb, rfl⟩, ?_⟩
  rw [permQ_mkQ, permQ_mkQ]
  rw [mul_perm, inv_perm] at hab
  exact (inv_mul_eq_one.mp hab).symm

end Mdl117

open Mdl117

theorem model117Pair_proved : Model117Pair := by
  intro n hn5 _ α h x hx3 hxK _ hxK' k hk
  have hperm : ∀ y ∈ memBar α h true, permQ n (x * y * x⁻¹) = permQ n y := by
    intro y hy
    obtain ⟨y', hy', hyy'⟩ := exists_memBar_false_perm α h hy
    have hc : permQ n x * permQ n y' = permQ n y' * permQ n x := by
      rw [← map_mul, ← map_mul, hxK' y' hy']
    rw [map_mul, map_mul, map_inv, ← hyy', hc, mul_inv_cancel_right]
  have hsq : ∀ y ∈ memBar α h true, x * y * x⁻¹ = y ∨ x * y * x⁻¹ = y * zBar α h := fun y hy =>
    eq_or_eq_mul_zBar α h hy ((Subgroup.mem_normalizer_iff.mp hxK y).mp hy) (hperm y hy).symm
  have hz : x * zBar α h * x⁻¹ = zBar α h := by
    rcases hsq _ (zBar_mem_memBar α h true) with h1 | h1
    · exact h1
    · rw [zBar_mul_self] at h1
      exact absurd (by calc zBar α h = x⁻¹ * (x * zBar α h * x⁻¹) * x := by group
          _ = 1 := by rw [h1]; group) (zBar_ne_one hn5 α h)
  have hxz : Commute x (zBar α h) := by
    show x * zBar α h = zBar α h * x
    calc x * zBar α h = x * zBar α h * x⁻¹ * x := by group
      _ = zBar α h * x := by rw [hz]
  rcases hsq k hk with h1 | h1
  · calc x * k = x * k * x⁻¹ * x := by group
      _ = k * x := by rw [h1]
  · exfalso
    have hxk : x * k = k * zBar α h * x := by
      calc x * k = x * k * x⁻¹ * x := by group
        _ = k * zBar α h * x := by rw [h1]
    have hc : Commute (x ^ 2) k := by
      show x ^ 2 * k = k * x ^ 2
      calc x ^ 2 * k = x * (x * k) := by rw [sq, mul_assoc]
        _ = x * (k * zBar α h * x) := by rw [hxk]
        _ = (x * k) * zBar α h * x := by group
        _ = (k * zBar α h * x) * zBar α h * x := by rw [hxk]
        _ = k * zBar α h * (x * zBar α h) * x := by group
        _ = k * zBar α h * (zBar α h * x) * x := by rw [hxz.eq]
        _ = k * (zBar α h * zBar α h) * (x * x) := by group
        _ = k * x ^ 2 := by rw [zBar_mul_self, mul_one, sq]
    obtain ⟨m, hm⟩ := hx3 ⟨x, Subgroup.mem_zpowers x⟩
    have hm' : x ^ 3 ^ m = 1 := by simpa using congrArg Subtype.val hm
    obtain ⟨j, hj⟩ : Odd (3 ^ m) := Odd.pow (by decide)
    have hcj : Commute ((x ^ 2) ^ j) k := hc.pow_left j
    have hzj : Commute ((x ^ 2) ^ j) (zBar α h) := (hxz.pow_left 2).pow_left j
    have key : x ^ 3 ^ m * k = k * zBar α h * x ^ 3 ^ m := by
      rw [hj, pow_succ, pow_mul]
      calc (x ^ 2) ^ j * x * k = (x ^ 2) ^ j * (k * zBar α h * x) := by rw [mul_assoc, hxk]
        _ = ((x ^ 2) ^ j * k) * zBar α h * x := by group
        _ = k * ((x ^ 2) ^ j * zBar α h) * x := by rw [hcj.eq]; group
        _ = k * zBar α h * ((x ^ 2) ^ j * x) := by rw [hzj.eq]; group
    rw [hm', one_mul, mul_one] at key
    exact zBar_ne_one hn5 α h (by
      calc zBar α h = k⁻¹ * (k * zBar α h) := by group
        _ = 1 := by rw [← key]; group)

end CFSG.ClassicalInvolution.Q3.TL4

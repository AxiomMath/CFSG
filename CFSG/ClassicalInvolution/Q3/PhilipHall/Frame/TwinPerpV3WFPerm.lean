module

public import CFSG.ClassicalInvolution.Generic.Frame

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF

open CFSG.ClassicalInvolution.Generic Equiv

private theorem perm4_pow12 : ∀ u : Perm (Fin 4), u ^ 12 = 1 := by decide +kernel

private theorem perm4_fix : ∀ u : Perm (Fin 4), u ≠ 1 → u ^ 3 = 1 →
    ∃ p, u p = p ∧ ∀ q, u q = q → q = p := by
  decide +kernel

private theorem perm4_two : ∀ u v : Perm (Fin 4), u ≠ 1 → u ^ 3 = 1 → v ^ 3 = 1 →
    (∃ i, u i = i ∧ v i ≠ i) →
    ((u * v) ^ 2 = 1 ∧ u * v ≠ 1) ∨ ((u * v⁻¹) ^ 2 = 1 ∧ u * v⁻¹ ≠ 1) := by
  decide +kernel

private theorem perm4_odd : ∀ u : Perm (Fin 4), (∃ k : Fin 12, u = (u * u) ^ (k : ℕ)) →
    u = 1 ∨ u ^ 3 = 1 := by
  decide +kernel

private theorem perm4_cube {u : Perm (Fin 4)} {m : ℕ} (hm : Odd m) (hu : u ^ m = 1) : u ^ 3 = 1 := by
  obtain ⟨j, rfl⟩ := hm
  have h2 : u = (u * u) ^ (j + 1) := by
    calc u = u ^ (2 * j + 1) * u := by rw [hu, one_mul]
      _ = u ^ (2 * (j + 1)) := by rw [← pow_succ]; ring_nf
      _ = (u * u) ^ (j + 1) := by rw [pow_mul, sq]
  have h24 : (u * u) ^ 12 = 1 := by
    calc (u * u) ^ 12 = u ^ (2 * 12) := by rw [← sq, ← pow_mul]
      _ = (u ^ 12) ^ 2 := pow_mul' u 2 12
      _ = 1 := by rw [perm4_pow12 u, one_pow]
  have h3 : u = (u * u) ^ (((j + 1) % 12 : ℕ)) := by
    calc u = (u * u) ^ (j + 1) := h2
      _ = (u * u) ^ (12 * ((j + 1) / 12) + (j + 1) % 12) := by rw [Nat.div_add_mod]
      _ = ((u * u) ^ 12) ^ ((j + 1) / 12) * (u * u) ^ ((j + 1) % 12) := by rw [pow_add, pow_mul]
      _ = (u * u) ^ ((j + 1) % 12) := by rw [h24, one_pow, one_mul]
  rcases perm4_odd u ⟨⟨(j + 1) % 12, Nat.mod_lt _ (by norm_num)⟩, h3⟩ with h | h
  · rw [h]; exact one_pow 3
  · exact h

private theorem eq_one_of_sq_odd {X : Type*} [Group X] {x : X} {m : ℕ} (hm : Odd m) (h2 : x ^ 2 = 1)
    (hx : x ^ m = 1) : x = 1 := by
  obtain ⟨j, rfl⟩ := hm
  rw [pow_succ, pow_mul, h2, one_pow, one_mul] at hx
  exact hx

theorem normalizes_of_odd_normal {Y : Type*} [Group Y] (M : Fin 4 → Subgroup Y)
    (hinj : Function.Injective M) (C : Subgroup Y)
    (hperm : ∀ c ∈ C, ∀ i, ∃ j, conjSub c (M i) = M j)
    (htrans : ∀ i j, ∃ c ∈ C, conjSub c (M i) = M j) (N P : Subgroup Y) (hNC : N ≤ C)
    (hNn : (N.subgroupOf C).Normal) (hPN : P ≤ N) (hPn : ∀ p ∈ P, ∀ i, conjSub p (M i) = M i)
    (hodd : ∀ g ∈ N, ∃ m : ℕ, Odd m ∧ g ^ m ∈ P) : ∀ g ∈ N, ∀ i, conjSub g (M i) = M i := by
  classical
  choose! π hπ using fun (c : ↥C) (i : Fin 4) => hperm c c.2 i
  have hπ1 : ∀ i, π 1 i = i := by
    intro i
    apply hinj
    rw [← hπ 1 i]
    simp
  have hπmul : ∀ (c d : ↥C) i, π (c * d) i = π c (π d i) := by
    intro c d i
    apply hinj
    rw [← hπ (c * d) i, Subgroup.coe_mul, conjSub_mul, hπ d i, hπ c]
  letI : MulAction ↥C (Fin 4) := { smul := π, one_smul := hπ1, mul_smul := hπmul }
  let σ : ↥C →* Perm (Fin 4) := MulAction.toPermHom ↥C (Fin 4)
  have hσ : ∀ (c : ↥C) i, σ c i = π c i := fun c i => rfl
  have hPker : ∀ p (hp : p ∈ P), σ ⟨p, hNC (hPN hp)⟩ = 1 := by
    intro p hp
    refine Equiv.ext fun i => ?_
    show π ⟨p, hNC (hPN hp)⟩ i = i
    apply hinj
    rw [← hπ ⟨p, hNC (hPN hp)⟩ i]
    exact hPn p hp i
  have hodd' : ∀ g (hg : g ∈ N), ∃ m : ℕ, Odd m ∧ (σ ⟨g, hNC hg⟩) ^ m = 1 := by
    intro g hg
    obtain ⟨m, hm, hgm⟩ := hodd g hg
    refine ⟨m, hm, ?_⟩
    rw [← map_pow]
    have e : (⟨g, hNC hg⟩ : ↥C) ^ m = ⟨g ^ m, hNC (hPN hgm)⟩ := Subtype.ext (by simp)
    rw [e]
    exact hPker _ hgm
  intro g hg i
  by_contra hne
  have hgC : g ∈ C := hNC hg
  have hui : σ ⟨g, hgC⟩ i ≠ i := by
    intro h
    apply hne
    rw [hσ] at h
    rw [hπ ⟨g, hgC⟩ i, h]
  obtain ⟨m, hm, hum⟩ := hodd' g hg
  have hu3 : σ ⟨g, hgC⟩ ^ 3 = 1 := perm4_cube hm hum
  have hu1 : σ ⟨g, hgC⟩ ≠ 1 := fun h => hui (by rw [h]; rfl)
  obtain ⟨p, hp, hpuniq⟩ := perm4_fix _ hu1 hu3
  obtain ⟨q, hq⟩ : ∃ q : Fin 4, q ≠ p := by
    by_cases h : p = 0
    · exact ⟨1, by rw [h]; decide⟩
    · exact ⟨0, fun h' => h h'.symm⟩
  obtain ⟨c, hcC, hc⟩ := htrans p q
  let c' : ↥C := ⟨c, hcC⟩
  have hcp : σ c' p = q := by
    rw [hσ]
    apply hinj
    rw [← hπ c' p]
    exact hc
  have hg₂N : c * g * c⁻¹ ∈ N := by
    have := hNn.conj_mem ⟨g, hgC⟩ (Subgroup.mem_subgroupOf.mpr hg) c'
    exact Subgroup.mem_subgroupOf.mp this
  set u := σ ⟨g, hgC⟩ with hu
  have hv : σ ⟨c * g * c⁻¹, hNC hg₂N⟩ = σ c' * u * (σ c')⁻¹ := by
    rw [hu, ← map_inv, ← map_mul, ← map_mul]
    rfl
  set v := σ ⟨c * g * c⁻¹, hNC hg₂N⟩ with hvdef
  have hv3 : v ^ 3 = 1 := by
    rw [hv, conj_pow, hu3, mul_one, mul_inv_cancel]
  have hvp : v ≠ 1 := fun h => hu1 (by
    have : σ c' * u * (σ c')⁻¹ = 1 := by rw [← hv]; exact h
    simpa using this)
  have hvx : ∀ x, v x = σ c' (u ((σ c').symm x)) := fun x => by rw [hv]; rfl
  have hs1 : ∀ x, (σ c').symm (σ c' x) = x := fun x => Equiv.symm_apply_apply _ _
  have hs2 : ∀ x, σ c' ((σ c').symm x) = x := fun x => Equiv.apply_symm_apply _ _
  have hvfix : v q = q := by
    rw [hvx, ← hcp, hs1, hp]
  have hvp' : v p ≠ p := by
    intro h
    have h2 : u ((σ c').symm p) = (σ c').symm p := by
      have h0 : σ c' (u ((σ c').symm p)) = p := by rw [← hvx]; exact h
      have h3 := congrArg (fun x => (σ c').symm x) h0
      simpa [hs1] using h3
    have h4 := hpuniq _ h2
    apply hq
    calc q = σ c' p := hcp.symm
      _ = σ c' ((σ c').symm p) := by rw [h4]
      _ = p := hs2 p
  have key := perm4_two u v hu1 hu3 hv3 ⟨p, hp, hvp'⟩
  have hg₂C : c * g * c⁻¹ ∈ C := hNC hg₂N
  rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩
  ·
    have hN1 : g * (c * g * c⁻¹) ∈ N := N.mul_mem hg hg₂N
    obtain ⟨m', hm', hum'⟩ := hodd' _ hN1
    have e : σ ⟨g * (c * g * c⁻¹), hNC hN1⟩ = u * v := by
      rw [hu, hvdef, ← map_mul]; rfl
    rw [e] at hum'
    exact h2 (eq_one_of_sq_odd hm' h1 hum')
  · have hN1 : g * (c * g * c⁻¹)⁻¹ ∈ N := N.mul_mem hg (N.inv_mem hg₂N)
    obtain ⟨m', hm', hum'⟩ := hodd' _ hN1
    have e : σ ⟨g * (c * g * c⁻¹)⁻¹, hNC hN1⟩ = u * v⁻¹ := by
      rw [hu, hvdef, ← map_inv, ← map_mul]; rfl
    rw [e] at hum'
    exact h2 (eq_one_of_sq_odd hm' h1 hum')

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF

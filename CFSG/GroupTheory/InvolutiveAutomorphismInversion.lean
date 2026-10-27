module

public import CFSG.GroupTheory.PrimeCommutatorSupport
public import CFSG.GroupTheory.OddInversion

public section

namespace CFSG.OddInversion

variable {H : Type*} [Group H] [Finite H]

theorem exists_fixed_mul_inverted (hH : Odd (Nat.card H)) (α : MulAut H) (hα : α * α = 1)
    (h : H) : ∃ c j : H, α c = c ∧ α j = j⁻¹ ∧ h = c * j := by
  classical
  have hαα : ∀ x, α (α x) = x := fun x => by
    have := congrArg (fun β : MulAut H => β x) hα
    simpa using this
  let C : Subgroup H :=
    { carrier := {x | α x = x}
      mul_mem' := fun {a b} ha hb => by simp only [Set.mem_ofPred_eq] at *; rw [map_mul, ha, hb]
      one_mem' := map_one α
      inv_mem' := fun {a} ha => by simp only [Set.mem_ofPred_eq] at *; rw [map_inv, ha] }
  have hC : ∀ x : H, x ∈ C ↔ α • x = x := fun x => Iff.rfl
  let I : Set H := {x | α x = x⁻¹}
  set Tw := (fun a : H => a * (α • a)⁻¹) '' ((⊤ : Subgroup H) : Set H) with hTw
  have hTwI : Tw ⊆ I := by
    rintro _ ⟨a, -, rfl⟩
    change α (a * (α a)⁻¹) = (a * (α a)⁻¹)⁻¹
    rw [map_mul, map_inv, hαα, mul_inv_rev, inv_inv]
  have hcardTw : Nat.card Tw = C.index := by
    rw [hTw, CFSG.SolvableHall.card_image_mul_smul_inv α ⊤ C hC, Subgroup.relIndex_top_right]
  have hodd : Odd (Nat.card (⊤ : Subgroup H)) := by rw [Subgroup.card_top]; exact hH
  have hinj : Set.InjOn (fun x : H × H => x.1 * x.2) ((C : Set H) ×ˢ I) := by
    rintro ⟨c₁, j₁⟩ ⟨hc₁, hj₁⟩ ⟨c₂, j₂⟩ ⟨hc₂, hj₂⟩ hcj
    simp only at hcj
    have hkey : ∀ c j : H, α c = c → α j = j⁻¹ → (c * j)⁻¹ * α (c * j) = j⁻¹ ^ 2 := by
      intro c j hc hj
      rw [map_mul, hc, hj, sq]
      group
    have h1 := hkey c₁ j₁ hc₁ hj₁
    rw [hcj, hkey c₂ j₂ hc₂ hj₂] at h1
    have hj : j₂⁻¹ = j₁⁻¹ := sq_injOn hodd (Subgroup.mem_top _) (Subgroup.mem_top _) h1
    rw [inv_inj] at hj
    subst hj
    rw [mul_right_cancel hcj]
  have hsurj : Set.univ ⊆ (fun x : H × H => x.1 * x.2) '' ((C : Set H) ×ˢ I) := by
    have himage : (fun x : H × H => x.1 * x.2) '' ((C : Set H) ×ˢ I) = Set.univ := by
      apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _) _ (Set.toFinite _)
      rw [hinj.ncard_image, Set.ncard_prod, Set.ncard_univ]
      have hI : C.index ≤ I.ncard := by
        rw [← hcardTw, Nat.card_coe_set_eq]
        exact Set.ncard_le_ncard hTwI (Set.toFinite I)
      have hCcard : (C : Set H).ncard = Nat.card C := by
        rw [← Nat.card_coe_set_eq]
        rfl
      rw [hCcard, ← C.card_mul_index]
      exact Nat.mul_le_mul_left _ hI
    rw [himage]
  obtain ⟨⟨c, j⟩, ⟨hc, hj⟩, hcj⟩ := hsurj (Set.mem_univ h)
  exact ⟨c, j, hc, hj, hcj.symm⟩

theorem inversion_set_conjugacy_and_normality (hH : Odd (Nat.card H)) (α : MulAut H)
    (hα : α * α = 1) :
    (∀ x y : H, α y = y⁻¹ → ∀ ε : ℤ, (ε = 1 ∨ ε = -1) → α x = x ^ ε →
      α (y⁻¹ * x * y) = (y⁻¹ * x * y) ^ ε → x * y = y * x) ∧
    ((∃ K : Subgroup H, (K : Set H) = {h | α h = h⁻¹}) ↔
      ∀ g x : H, α x = x⁻¹ → α (g * x * g⁻¹) = (g * x * g⁻¹)⁻¹) ∧
    ((∀ g x : H, α x = x⁻¹ → α (g * x * g⁻¹) = (g * x * g⁻¹)⁻¹) →
      ∃ K : Subgroup H, (K : Set H) = {h | α h = h⁻¹} ∧ K.Normal ∧ IsMulCommutative K) := by
  classical
  have hodd : Odd (Nat.card (⊤ : Subgroup H)) := by rw [Subgroup.card_top]; exact hH
  have hcomm : ∀ x y : H, α y = y⁻¹ → ∀ ε : ℤ, (ε = 1 ∨ ε = -1) → α x = x ^ ε →
      α (y⁻¹ * x * y) = (y⁻¹ * x * y) ^ ε → x * y = y * x := by
    intro x y hy ε hε hx hxy
    have h1 : y * x ^ ε * y⁻¹ = y⁻¹ * x ^ ε * y := by
      have h2 : α (y⁻¹ * x * y) = y * x ^ ε * y⁻¹ := by
        rw [map_mul, map_mul, map_inv, hy, hx, inv_inv]
      rw [← h2, hxy]
      have := conj_zpow (i := ε) (a := y⁻¹) (b := x)
      rw [inv_inv] at this
      exact this
    have h3 : Commute (x ^ ε) (y ^ 2) := by
      change x ^ ε * y ^ 2 = y ^ 2 * x ^ ε
      calc x ^ ε * y ^ 2 = y * (y⁻¹ * x ^ ε * y) * y := by rw [sq]; group
        _ = y * (y * x ^ ε * y⁻¹) * y := by rw [h1]
        _ = y ^ 2 * x ^ ε := by rw [sq]; group
    have h4 : Commute x (y ^ 2) := by
      rcases hε with rfl | rfl
      · simpa using h3
      · simpa using h3.inv_left
    have h5 : (y ^ ((Nat.card (⊤ : Subgroup H) + 1) / 2)) ^ 2 = y :=
      pow_two_mul_eq_self hodd (Subgroup.mem_top y)
    have h6 : Commute x ((y ^ 2) ^ ((Nat.card (⊤ : Subgroup H) + 1) / 2)) := h4.pow_right _
    rw [← pow_mul, mul_comm, pow_mul, h5] at h6
    exact h6
  have hsub : (∀ g x : H, α x = x⁻¹ → α (g * x * g⁻¹) = (g * x * g⁻¹)⁻¹) →
      ∃ K : Subgroup H, (K : Set H) = {h | α h = h⁻¹} ∧ K.Normal ∧ IsMulCommutative K := by
    intro hinv
    have hpair : ∀ x y : H, α x = x⁻¹ → α y = y⁻¹ → x * y = y * x := by
      intro x y hx hy
      refine hcomm x y hy (-1) (Or.inr rfl) (by rw [hx, zpow_neg_one]) ?_
      have := hinv y⁻¹ x hx
      rw [inv_inv] at this
      rw [this, zpow_neg_one]
    let K : Subgroup H :=
      { carrier := {h | α h = h⁻¹}
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_ofPred_eq] at *
          rw [map_mul, ha, hb, mul_inv_rev, hpair a⁻¹ b⁻¹ (by rw [map_inv, ha])
            (by rw [map_inv, hb])]
        one_mem' := by simp
        inv_mem' := fun {a} ha => by simp only [Set.mem_ofPred_eq] at *; rw [map_inv, ha] }
    refine ⟨K, rfl, ⟨fun x hx g => hinv g x hx⟩, ⟨⟨fun a b => Subtype.ext (hpair a b a.2 b.2)⟩⟩⟩
  refine ⟨hcomm, ⟨?_, fun h => (hsub h).imp fun K hK => hK.1⟩, hsub⟩
  rintro ⟨K, hK⟩ g x hx
  have hxK : x ∈ K := by rw [← SetLike.mem_coe, hK]; exact hx
  obtain ⟨c, j, hc, hj, rfl⟩ := exists_fixed_mul_inverted hH α hα g
  have hjK : j ∈ K := by rw [← SetLike.mem_coe, hK]; exact hj
  have hy : j * x * j⁻¹ ∈ K := K.mul_mem (K.mul_mem hjK hxK) (K.inv_mem hjK)
  have hy' : α (j * x * j⁻¹) = (j * x * j⁻¹)⁻¹ := by
    have := hy
    rw [← SetLike.mem_coe, hK] at this
    exact this
  have : c * j * x * (c * j)⁻¹ = c * (j * x * j⁻¹) * c⁻¹ := by group
  rw [this, map_mul, map_mul, map_inv, hc, hy']
  group

end CFSG.OddInversion

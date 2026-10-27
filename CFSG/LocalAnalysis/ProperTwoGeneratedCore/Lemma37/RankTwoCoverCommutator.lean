module

public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open scoped commutatorElement

variable {P X : Type*} [Group P] [Group X]

theorem commutatorElement_mem_of_abelian (T : Subgroup P) (s : P)
    (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hsT : ∀ t ∈ T, s * t * s⁻¹ ∈ T)
    (hcover : ∀ g : P, g ∈ T ∨ g * s⁻¹ ∈ T) {K : Subgroup P}
    (hK : ∀ t ∈ T, t⁻¹ * (s * t * s⁻¹) ∈ K) (a b : P) : ⁅a, b⁆ ∈ K := by
  have hmixed : ∀ t ∈ T, ∀ t' ∈ T, ⁅t, t' * s⁆ ∈ K := by
    intro t ht t' ht'
    have hc : s * t⁻¹ * s⁻¹ ∈ T := hsT _ (T.inv_mem ht)
    have h1 := hT t' ht' _ hc
    have h2 := hT t ht _ hc
    have heq : ⁅t, t' * s⁆ = (t⁻¹ * (s * t * s⁻¹))⁻¹ := by
      calc ⁅t, t' * s⁆ = t * (t' * (s * t⁻¹ * s⁻¹)) * t'⁻¹ := by
              rw [commutatorElement_def]; group
        _ = t * (s * t⁻¹ * s⁻¹) := by rw [h1]; group
        _ = (s * t⁻¹ * s⁻¹) * t := h2
        _ = (t⁻¹ * (s * t * s⁻¹))⁻¹ := by group
    rw [heq]
    exact K.inv_mem (hK t ht)
  rcases hcover a with ha | ha <;> rcases hcover b with hb | hb
  · rw [commutatorElement_def, hT a ha b hb, mul_inv_cancel_right, mul_inv_cancel]
    exact K.one_mem
  · have := hmixed a ha _ hb
    rwa [inv_mul_cancel_right] at this
  · have := hmixed b hb _ ha
    rw [inv_mul_cancel_right] at this
    rw [← commutatorElement_inv]
    exact K.inv_mem this
  · set t := a * s⁻¹
    set t' := b * s⁻¹
    set x := t' * t⁻¹ with hx
    have hxT : x ∈ T := T.mul_mem hb (T.inv_mem ha)
    have hyT : s * x * s⁻¹ ∈ T := hsT x hxT
    have h1 := hT t ha _ hyT
    have h2 := hT x⁻¹ (T.inv_mem hxT) _ hyT
    have hat : a = t * s := by simp [t]
    have hbt : b = t' * s := by simp [t']
    have heq : ⁅a, b⁆ = x⁻¹ * (s * x * s⁻¹) := by
      calc ⁅a, b⁆ = t * (s * x * s⁻¹) * t'⁻¹ := by
              rw [commutatorElement_def, hat, hbt, hx]; group
        _ = (s * x * s⁻¹) * x⁻¹ := by rw [h1, hx]; group
        _ = x⁻¹ * (s * x * s⁻¹) := h2.symm
    rw [heq]
    exact hK x hxT

theorem commute_of_mem_zpowers (ψ : P →* X) (hcen : ∀ c, ψ c = 1 → ∀ g, g * c = c * g)
    {r a b : P} (ha : ψ a ∈ Subgroup.zpowers (ψ r)) (hb : ψ b ∈ Subgroup.zpowers (ψ r)) :
    a * b = b * a := by
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hc : ψ (r ^ (-i) * a) = 1 := by rw [map_mul, map_zpow, ← hi, zpow_neg, inv_mul_cancel]
  have hc' : ψ (r ^ (-j) * b) = 1 := by rw [map_mul, map_zpow, ← hj, zpow_neg, inv_mul_cancel]
  have ha' : a = r ^ i * (r ^ (-i) * a) := by group
  have hb' : b = r ^ j * (r ^ (-j) * b) := by group
  set c := r ^ (-i) * a
  set c' := r ^ (-j) * b
  have key : Commute (r ^ i * c) (r ^ j * c') :=
    ((Commute.zpow_zpow_self r i j).mul_right (hcen c' hc' (r ^ i))).mul_left
      (hcen c hc _).symm
  rw [← ha', ← hb'] at key
  exact key.eq

theorem inv_mul_conj_mem_zpowers (ψ : P →* X) (hcen : ∀ c, ψ c = 1 → ∀ g, g * c = c * g)
    {r s t : P} (ht : ψ t ∈ Subgroup.zpowers (ψ r))
    (hrs : ψ (s * r * s⁻¹) ∈ Subgroup.zpowers (ψ r)) :
    t⁻¹ * (s * t * s⁻¹) ∈ Subgroup.zpowers (r⁻¹ * (s * r * s⁻¹)) := by
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ht
  have hc : ψ (r ^ (-i) * t) = 1 := by rw [map_mul, map_zpow, ← hi, zpow_neg, inv_mul_cancel]
  set c := r ^ (-i) * t
  have ht' : t = r ^ i * c := by simp [c]
  have hsc : s * c * s⁻¹ = c := by rw [hcen c hc s, mul_inv_cancel_right]
  have hconj : s * t * s⁻¹ = (s * r * s⁻¹) ^ i * c := by
    calc s * t * s⁻¹ = (s * r ^ i * s⁻¹) * (s * c * s⁻¹) := by rw [ht']; group
      _ = (s * r * s⁻¹) ^ i * c := by rw [conj_zpow, hsc]
  have hcomm : Commute r⁻¹ (s * r * s⁻¹) :=
    commute_of_mem_zpowers ψ hcen (r := r)
      (by rw [map_inv]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)) hrs
  have hcinv : ∀ g, g * c⁻¹ = c⁻¹ * g := fun g => hcen c⁻¹ (by rw [map_inv, hc, inv_one]) g
  refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
  symm
  calc t⁻¹ * (s * t * s⁻¹) = c⁻¹ * ((r ^ i)⁻¹ * (s * r * s⁻¹) ^ i) * c := by
          rw [hconj, ht']; group
    _ = ((r ^ i)⁻¹ * (s * r * s⁻¹) ^ i) * c⁻¹ * c := by rw [← hcinv]
    _ = (r ^ i)⁻¹ * (s * r * s⁻¹) ^ i := by group
    _ = (r⁻¹ * (s * r * s⁻¹)) ^ i := by rw [hcomm.mul_zpow, inv_zpow]

theorem mem_or_mul_inv_mem_of_index_two {H : Subgroup P} (hH : H.index = 2) {s : P} (hs : s ∉ H)
    (g : P) : g ∈ H ∨ g * s⁻¹ ∈ H := by
  by_cases hg : g ∈ H
  · exact Or.inl hg
  · right
    rw [Subgroup.mul_mem_iff_of_index_two hH]
    exact iff_of_false hg (fun h => hs (by simpa using H.inv_mem h))

theorem commutator_le_zpowers_of_index_two (ψ : P →* X) (hψ : Function.Surjective ψ)
    (hcen : ∀ c, ψ c = 1 → ∀ g, g * c = c * g) {r s : P}
    (hidx : (Subgroup.zpowers (ψ r)).index = 2) (hs : ψ s ∉ Subgroup.zpowers (ψ r)) :
    commutator P ≤ Subgroup.zpowers (r⁻¹ * (s * r * s⁻¹)) := by
  set T := (Subgroup.zpowers (ψ r)).comap ψ
  have hnorm : (Subgroup.zpowers (ψ r)).Normal := Subgroup.normal_of_index_eq_two hidx
  have hTidx : T.index = 2 := by rw [Subgroup.index_comap_of_surjective _ hψ, hidx]
  have hsT : ∀ t ∈ T, s * t * s⁻¹ ∈ T := fun t ht => by
    change ψ (s * t * s⁻¹) ∈ Subgroup.zpowers (ψ r)
    rw [map_mul, map_mul, map_inv]
    exact hnorm.conj_mem _ ht _
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  exact commutatorElement_mem_of_abelian T s
    (fun a ha b hb => commute_of_mem_zpowers ψ hcen ha hb) hsT
    (mem_or_mul_inv_mem_of_index_two hTidx hs)
    (fun t ht => inv_mul_conj_mem_zpowers ψ hcen ht (hsT r (Subgroup.mem_zpowers _))) a b

theorem mem_zpowers_zpow_of_odd [Finite P] (hP : IsPGroup 2 P) (g : P) {k : ℤ} (hk : Odd k) :
    g ∈ Subgroup.zpowers (g ^ k) := by
  obtain ⟨e, he⟩ := (IsPGroup.iff_orderOf.mp hP) g
  rw [mem_zpowers_zpow_iff, he]
  have hodd : Odd k.natAbs := Int.natAbs_odd.mpr hk
  change Nat.gcd k.natAbs (((2 ^ e : ℕ) : ℤ)).natAbs = 1
  rw [Int.natAbs_natCast]
  exact Nat.Coprime.pow_right e (hodd.coprime_two_right)

end CFSG.ProperTwoGeneratedCore.Lemma37

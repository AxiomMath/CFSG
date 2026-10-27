module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC2Inv

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open QuaternionGroup

namespace PartC

variable {G : Type} [Group G] {T Q P₁ : Subgroup G} {e u y : G} {N : ℕ}
  (φ : (P₁ ⊔ Subgroup.zpowers y : Subgroup G) ≃* QuaternionGroup N)

theorem inv_conj_eq_conj (hc : PartC T Q P₁ e u) {x : G} (hxx : x * x = e) (z : G) :
    x⁻¹ * z * x = x * z * x⁻¹ := by
  have hxi : x⁻¹ = x * e := hc.inv_eq_mul_centralElt hxx
  calc x⁻¹ * z * x = x⁻¹ * z * x⁻¹⁻¹ := by rw [inv_inv]
    _ = (x * e) * z * (x * e)⁻¹ := by rw [hxi]
    _ = x * (e * z * e⁻¹) * x⁻¹ := by group
    _ = x * z * x⁻¹ := by rw [← hc.commute_centralElt z, mul_inv_cancel_right]

theorem mul_eq_of_mod (hc : PartC T Q P₁ e u) {v a b : G} (hvu : v * u = u * v)
    (ha : a = v ∨ a = v * e) (hb : b = u ∨ b = u * e) :
    a * b = u * v ∨ a * b = u * v * e := by
  have he := hc.commute_centralElt
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb]
  · exact Or.inl hvu
  · exact Or.inr (by rw [← mul_assoc, hvu])
  · right
    rw [mul_assoc, ← he u, ← mul_assoc, hvu]
  · left
    calc v * e * (u * e) = v * (e * u) * e := by group
      _ = v * (u * e) * e := by rw [← he u]
      _ = v * u * (e * e) := by group
      _ = u * v := by rw [hc.centralElt_mul_self, mul_one, hvu]

theorem exists_conj_eq_mul_v (hc : PartC T Q P₁ e u) {v : G} (hvQ : v ∈ Q) (hvv : v * v = e)
    (hTv : T ≤ Subgroup.normalizer (Subgroup.zpowers v : Set G)) {x : G} (hxT : x ∈ T)
    (hx : x ∉ Q ⊔ P₁) (hxx : x * x = e) :
    ∃ m ∈ Q, m⁻¹ * x * m = x * v ∨ m⁻¹ * x * m = x * v * e := by
  obtain ⟨m, hm, hm1, hm2⟩ := hc.outer x hxT hx
  have hxP : x * x ∈ P₁ := by
    rw [hxx]
    exact hc.mem_right
  obtain ⟨vx, -, -, -, hfix⟩ := hc.exists_inv_conj hxT hx hxP
  have hxv : x * v * x⁻¹ = v * e := hc.conj_eq_mul_centralElt hxT hx hxx
    (Subgroup.mem_sup_left hvQ) hvv
    ((Subgroup.mem_normalizer_iff.mp (hTv hxT) v).mp (Subgroup.mem_zpowers v))
  have hv1 : v ≠ 1 := fun h => hc.centralElt_ne_one (by rw [← hvv, h, mul_one])
  have hve : v ≠ e := fun h => hc.centralElt_ne_one (by rw [← hvv, h, hc.centralElt_mul_self])
  have hv' : v = vx ∨ v = vx * e := by
    rcases hfix v hvQ (Or.inr hxv) with h | h | h | h
    · exact absurd h hv1
    · exact absurd h hve
    · exact Or.inl h
    · exact Or.inr h
  have hm1' : m ≠ 1 := fun h => hm1 (by rw [h, mul_one, mul_inv_cancel])
  have hme : m ≠ e := fun h => hm1 (by rw [h, hc.conj_centralElt])
  have hmm := hc.mul_self_of_ne hm hm1' hme
  have hk : m * (x * m * x⁻¹) = v ∨ m * (x * m * x⁻¹) = v * e := by
    rcases hc.mul_conj_mem hxT hxP hfix hm with h | h | h | h
    · exfalso
      apply hm2
      rw [← hc.inv_eq_mul_centralElt hmm]
      exact eq_inv_of_mul_eq_one_right h
    · exfalso
      apply hm1
      calc x * m * x⁻¹ = m⁻¹ * (m * (x * m * x⁻¹)) := by group
        _ = m := by rw [h, hc.inv_eq_mul_centralElt hmm, hc.mul_centralElt_mul_centralElt]
    · rcases hv' with h' | h'
      · left
        rw [h, h']
      · right
        rw [h, h', hc.mul_centralElt_mul_centralElt]
    · rcases hv' with h' | h'
      · right
        rw [h, h']
      · left
        rw [h, h']
  have he := hc.commute_centralElt
  have hvx : v * x = x * v * e := by
    calc v * x = x * (x⁻¹ * v * x) := by group
      _ = x * (x * v * x⁻¹) := by rw [hc.inv_conj_eq_conj hxx]
      _ = x * v * e := by rw [hxv, mul_assoc]
  refine ⟨m, hm, ?_⟩
  have hkey : m⁻¹ * x * m = (m * m)⁻¹ * (m * (x * m * x⁻¹)) * x := by group
  rw [hkey, hmm, hc.centralElt_inv]
  rcases hk with h | h <;> rw [h]
  · left
    rw [mul_assoc, hvx, ← he, hc.mul_centralElt_mul_centralElt]
  · right
    calc e * (v * e) * x = e * v * (e * x) := by group
      _ = e * (v * x) * e := by rw [← he x]; group
      _ = e * (x * v * e) * e := by rw [hvx]
      _ = x * v * e * e * e := by rw [← he (x * v * e)]
      _ = x * v * e := by rw [hc.mul_centralElt_mul_centralElt]

include φ in
theorem exists_conj_eq_mul_u [Finite G] [NeZero N] (hc : PartC T Q P₁ e u) (hyT : y ∈ T)
    (hy : y ∉ Q ⊔ P₁) (hyy : y * y ∈ P₁) (hP₁ : ¬ IsCyclic P₁) (hN : 8 ∣ N)
    (hnorm : T ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G)) {x : G} (hxT : x ∈ T)
    (hx : x ∉ Q ⊔ P₁) (hxx : x * x = e) :
    ∃ s ∈ T, s * x * s⁻¹ = x * u ∨ s * x * s⁻¹ = x * u * e := by
  obtain ⟨q, hq, w, hw, rfl, hwc⟩ :=
    hc.exists_mul_eq_of_mul_self φ hyT hy hyy hP₁ hN hxT hx hxx
  have hN3 : 3 ≤ N := by
    obtain ⟨M, hM⟩ := hN
    have := NeZero.ne N
    omega
  obtain ⟨M, hM⟩ := hN
  have hcN : quatGen φ ^ (8 * M) = e := by
    rw [← hM]
    exact hc.quatGen_pow φ hyT hy hyy
  have hr : quatGen φ ^ (2 * M) ∈ P₁ :=
    (hc.quatGen_pow_mem_iff φ hyT hy hyy hP₁ _).mpr (even_two_mul M)
  have hcT : quatGen φ ∈ T := hc.sup_zpowers_le hyT (quatGen_mem φ)
  refine ⟨quatGen φ ^ (2 * M), T.pow_mem hcT _, ?_⟩
  set c := quatGen φ with hcdef
  have hsemi : SemiconjBy w c c⁻¹ := by
    change w * c = c⁻¹ * w
    calc w * c = w * c * w⁻¹ * w := by group
      _ = c⁻¹ * w := by rw [hwc]
  have hcw : c ^ (2 * M) * w = w * (c ^ (2 * M))⁻¹ := by
    have h : w * c ^ (2 * M) = c⁻¹ ^ (2 * M) * w := (hsemi.pow_right (2 * M)).eq
    calc c ^ (2 * M) * w = c ^ (2 * M) * (w * c ^ (2 * M)) * (c ^ (2 * M))⁻¹ := by group
      _ = c ^ (2 * M) * (c⁻¹ ^ (2 * M) * w) * (c ^ (2 * M))⁻¹ := by rw [h]
      _ = w * (c ^ (2 * M))⁻¹ := by rw [inv_pow]; group
  have hqc := hc.commute q hq _ hr
  have hconj : c ^ (2 * M) * (q * w) * (c ^ (2 * M))⁻¹ = q * w * (c ^ (4 * M))⁻¹ := by
    calc c ^ (2 * M) * (q * w) * (c ^ (2 * M))⁻¹ = c ^ (2 * M) * q * w * (c ^ (2 * M))⁻¹ := by
          group
      _ = q * (c ^ (2 * M) * w) * (c ^ (2 * M))⁻¹ := by rw [← hqc]; group
      _ = q * (w * (c ^ (2 * M))⁻¹) * (c ^ (2 * M))⁻¹ := by rw [hcw]
      _ = q * w * (c ^ (2 * M) * c ^ (2 * M))⁻¹ := by group
      _ = q * w * (c ^ (4 * M))⁻¹ := by rw [← pow_add, show 2 * M + 2 * M = 4 * M by ring]
  rw [hconj]
  have hsq : c ^ (4 * M) * c ^ (4 * M) = e := by
    rw [← pow_add, show 4 * M + 4 * M = 8 * M by ring, hcN]
  have he := hc.commute_centralElt
  rcases hc.eq_of_mem_zpowers_quatGen φ hyT hy hyy hN3 hnorm
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _) hsq with h | h <;> rw [h]
  · right
    rw [hc.inv_eq_mul_centralElt hc.sq, ← mul_assoc]
  · left
    rw [mul_inv_rev, hc.centralElt_inv, hc.inv_eq_mul_centralElt hc.sq, ← he (u * e),
      hc.mul_centralElt_mul_centralElt]

include φ in
theorem exists_conj_eq_mul_mul [Finite G] [NeZero N] (hc : PartC T Q P₁ e u) (hyT : y ∈ T)
    (hy : y ∉ Q ⊔ P₁) (hyy : y * y ∈ P₁) (hP₁ : ¬ IsCyclic P₁) (hN : 8 ∣ N)
    (hnorm : T ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G)) {v : G} (hvQ : v ∈ Q)
    (hvv : v * v = e) (hTv : T ≤ Subgroup.normalizer (Subgroup.zpowers v : Set G)) {x : G}
    (hxT : x ∈ T) (hx : x ∉ Q ⊔ P₁) (hxx : x * x = e) :
    ∃ s ∈ T, s * x * s⁻¹ = x * u * v ∨ s * x * s⁻¹ = x * u * v * e := by
  obtain ⟨m, hm, hmx⟩ := hc.exists_conj_eq_mul_v hvQ hvv hTv hxT hx hxx
  obtain ⟨s, hsT, hsx⟩ := hc.exists_conj_eq_mul_u φ hyT hy hyy hP₁ hN hnorm hxT hx hxx
  refine ⟨m⁻¹ * s, T.mul_mem (T.inv_mem (hc.left_le hm)) hsT, ?_⟩
  have he := hc.commute_centralElt
  have hmu : m⁻¹ * u * m = u := by
    rw [mul_assoc, ← hc.commute m hm u hc.self_mem, inv_mul_cancel_left]
  have hz : x⁻¹ * (s * x * s⁻¹) = u ∨ x⁻¹ * (s * x * s⁻¹) = u * e := by
    rcases hsx with h | h <;> rw [h]
    · left
      group
    · right
      group
  have hz' : x⁻¹ * (m⁻¹ * x * m) = v ∨ x⁻¹ * (m⁻¹ * x * m) = v * e := by
    rcases hmx with h | h <;> rw [h]
    · left
      group
    · right
      group
  have hzm : m⁻¹ * (x⁻¹ * (s * x * s⁻¹)) * m = x⁻¹ * (s * x * s⁻¹) := by
    rcases hz with h | h <;> rw [h]
    · exact hmu
    · calc m⁻¹ * (u * e) * m = m⁻¹ * u * (e * m) := by group
        _ = m⁻¹ * u * (m * e) := by rw [← he m]
        _ = m⁻¹ * u * m * e := by group
        _ = u * e := by rw [hmu]
  have key : m⁻¹ * s * x * (m⁻¹ * s)⁻¹ =
      x * ((x⁻¹ * (m⁻¹ * x * m)) * (m⁻¹ * (x⁻¹ * (s * x * s⁻¹)) * m)) := by group
  rw [key, hzm]
  rcases hc.mul_eq_of_mod (hc.commute v hvQ u hc.self_mem) hz' hz with h | h <;> rw [h]
  · left
    simp only [mul_assoc]
  · right
    simp only [mul_assoc]

end PartC

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

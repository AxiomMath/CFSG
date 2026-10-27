module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Q8
public import Certificates.Data.E4QuatCheck

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4C

open CFSG.ClassicalInvolution.Generic CFSG.Sporadic.Schreier CFSG.ClassicalInvolution.Asc77

variable {n : ℕ}

theorem identCheck_spec {r : Equiv.Perm (Fin n)} {reps C W L0 L1 : List (Equiv.Perm (Fin n))}
    (hc : identCheck r reps C W L0 L1 = true) {ρ : Equiv.Perm (Fin n)} (hρ : ρ ∈ reps)
    (hρr : ρ * ρ = r) {j : Equiv.Perm (Fin n)} (hj : j ∈ C) (hjr : j * j = r)
    (hjρ : j * ρ * j⁻¹ = ρ⁻¹) :
    sameSet (q8Elems r ρ j) L0 = true ∨ sameSet (q8Elems r ρ j) L1 = true ∨
      ∃ c ∈ W, violates (q8Elems r ρ j) ρ j c = true := by
  simp only [identCheck, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at hc
  rcases hc ρ hρ with h | h
  · exact absurd hρr h
  · have h1 := h j hj
    rw [tab_eq] at h1
    simp only [identStep, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
      decide_eq_false_iff_not, List.any_eq_true] at h1
    rcases h1 with (h1 | h1) | (h1 | h1) | h1
    · exact absurd hjr h1
    · exact absurd hjρ h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)

theorem sameSet_spec {A B : List (Equiv.Perm (Fin n))} (h : sameSet A B = true) (x : _) :
    x ∈ A ↔ x ∈ B := by
  simp only [sameSet, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1 x, h.2 x⟩

theorem violates_spec {T : List (Equiv.Perm (Fin n))} {i j c : Equiv.Perm (Fin n)}
    (h : violates T i j c = true) :
    (∃ x ∈ T, c * x * c⁻¹ ∉ T) ∧
      ∃ x ∈ [i, j], ∃ y ∈ [c * i * c⁻¹, c * j * c⁻¹], x * y ≠ y * x := by
  simp only [violates, Bool.and_eq_true, List.any_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  exact h

theorem q8_fact : ∀ u : QuaternionGroup 2, u * u ≠ 1 → ∃ v : QuaternionGroup 2,
    v * v = u * u ∧ v * u * v⁻¹ = u⁻¹ ∧
      ∀ x : QuaternionGroup 2, x ∈ [1, u * u, u, u * (u * u), v, v * (u * u), u * v,
        u * v * (u * u)] := by
  decide

theorem exists_q8_gen {K : Subgroup (Equiv.Perm (Fin n))} (e : ↥K ≃* QuaternionGroup 2)
    {ρ : Equiv.Perm (Fin n)} (hρ : ρ ∈ K) (hρ2 : ρ * ρ ≠ 1) :
    ∃ j ∈ K, j * j = ρ * ρ ∧ j * ρ * j⁻¹ = ρ⁻¹ ∧ ∀ x, x ∈ K ↔ x ∈ q8Elems (ρ * ρ) ρ j := by
  let f : QuaternionGroup 2 →* Equiv.Perm (Fin n) := K.subtype.comp e.symm.toMonoidHom
  have hf : ∀ x (hx : x ∈ K), f (e ⟨x, hx⟩) = x := fun x hx => by
    simp [f]
  set u := e ⟨ρ, hρ⟩ with hu
  have hfu : f u = ρ := hf ρ hρ
  have hu2 : u * u ≠ 1 := by
    intro h
    apply hρ2
    rw [← hfu, ← map_mul, h, map_one]
  obtain ⟨v, hv1, hv2, hv3⟩ := q8_fact u hu2
  have hlist : q8Elems (ρ * ρ) ρ (f v) = ([1, u * u, u, u * (u * u), v, v * (u * u), u * v,
      u * v * (u * u)] : List (QuaternionGroup 2)).map f := by
    simp only [q8Elems, List.map_cons, List.map_nil, map_mul, map_one, hfu]
  refine ⟨f v, (e.symm v).2, ?_, ?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · rw [← hfu, ← map_mul, ← map_mul, hv1]
  · rw [← hfu, ← map_inv f v, ← map_mul, ← map_mul, hv2, map_inv]
  · rw [hlist, ← hf x hx]
    exact List.mem_map_of_mem (hv3 _)
  · rw [hlist] at hx
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx
    exact (e.symm a).2

theorem eq_of_identCheck {H K : Subgroup (Equiv.Perm (Fin n))} {r : Equiv.Perm (Fin n)}
    (hd : Vtx.AmbientQuatDatum H K r) {reps C W L0 L1 : List (Equiv.Perm (Fin n))}
    (hc : identCheck r reps C W L0 L1 = true) (hC : ∀ j ∈ H, j * r = r * j → j ∈ C)
    (hW : ∀ c ∈ W, c ∈ H ∧ c * r = r * c) {ρ : Equiv.Perm (Fin n)} (hρ : ρ ∈ reps)
    (hρK : ρ ∈ K) (hρr : ρ * ρ = r) :
    (∀ x, x ∈ K ↔ x ∈ L0) ∨ (∀ x, x ∈ K ↔ x ∈ L1) := by
  obtain ⟨e⟩ := hd.q8
  have hρ2 : ρ * ρ ≠ 1 := hρr ▸ hd.inv.ne_one
  obtain ⟨j, hjK, hjj, hjρ, hKT⟩ := exists_q8_gen e hρK hρ2
  rw [hρr] at hjj hKT
  have hjr : j * r = r * j := by
    have hmem : j * r * j⁻¹ ∈ K := K.mul_mem (K.mul_mem hjK hd.inv.mem) (K.inv_mem hjK)
    have hsq : j * r * j⁻¹ * (j * r * j⁻¹) = 1 := by
      calc j * r * j⁻¹ * (j * r * j⁻¹) = j * (r * r) * j⁻¹ := by group
        _ = 1 := by rw [hd.inv.sq]; group
    rcases hd.inv.unique _ hmem hsq with h1 | h1
    · exfalso
      apply hd.inv.ne_one
      calc r = j⁻¹ * (j * r * j⁻¹) * j := by group
        _ = 1 := by rw [h1]; group
    · calc j * r = (j * r * j⁻¹) * j := by group
        _ = r * j := by rw [h1]
  rcases identCheck_spec hc hρ hρr (hC j (hd.le hjK) hjr) hjj hjρ with h | h | ⟨c, hcW, hv⟩
  · exact Or.inl fun x => (hKT x).trans (sameSet_spec h x)
  · exact Or.inr fun x => (hKT x).trans (sameSet_spec h x)
  · exfalso
    obtain ⟨hcH, hcr⟩ := hW c hcW
    obtain ⟨⟨x, hxT, hxc⟩, a, ha, b, hb, hab⟩ := violates_spec hv
    rcases hd.twins c hcH hcr with h1 | h1
    · apply hxc
      rw [← hKT, ← h1]
      exact conj_mem_conjSub ((hKT x).mpr hxT)
    · have haK : a ∈ K := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · exact hρK
        · exact hjK
      have hbK : b ∈ conjSub c K := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · exact conj_mem_conjSub hρK
        · exact conj_mem_conjSub hjK
      exact hab (h1 a haK b hbK)

end CFSG.ClassicalInvolution.Q3.TL4.E4C

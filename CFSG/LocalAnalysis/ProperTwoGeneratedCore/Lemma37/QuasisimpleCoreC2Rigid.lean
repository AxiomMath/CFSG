module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC2Conj

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open QuaternionGroup

namespace PartC

variable {G : Type} [Group G] {T Q P₁ : Subgroup G} {e u y : G} {N : ℕ}
  (φ : (P₁ ⊔ Subgroup.zpowers y : Subgroup G) ≃* QuaternionGroup N)

theorem conj_swap (hc : PartC T Q P₁ e u) {x s : G} (h : x * s * x⁻¹ = s * e) :
    s * x * s⁻¹ = x * e := by
  have he := hc.commute_centralElt
  calc s * x * s⁻¹ = s * (x * s * x⁻¹)⁻¹ * x := by group
    _ = s * (s * e)⁻¹ * x := by rw [h]
    _ = s * e * s⁻¹ * x := by rw [mul_inv_rev, hc.centralElt_inv]; group
    _ = x * e := by rw [he s, mul_inv_cancel_right, he x]

theorem conj_self_of_conj_mod (hc : PartC T Q P₁ e u) {s z : G} (hz : z = u ∨ z = u * e)
    (h : s * z * s⁻¹ = z * e) : s * u * s⁻¹ = u * e := by
  rcases hz with rfl | rfl
  · exact h
  · rw [hc.conj_mul_centralElt] at h
    exact mul_right_cancel h

theorem mul_mem_zpowers_of_mod (hc : PartC T Q P₁ e u) {v z r : G} (hvv : v * v = e)
    (hz : z = u ∨ z = u * e) (hr : r = u * v ∨ r = u * v * e) :
    z * r ∈ Subgroup.zpowers v := by
  have he := hc.commute_centralElt
  have hve : v * e ∈ Subgroup.zpowers v := mul_centralElt_mem_zpowers hvv
  have hv : v ∈ Subgroup.zpowers v := Subgroup.mem_zpowers v
  have huu := hc.sq
  have h3 : u * e * (u * v) = v := by
    calc u * e * (u * v) = u * (e * u) * v := by group
      _ = u * (u * e) * v := by rw [← he u]
      _ = (u * u) * (e * v) := by group
      _ = v := by rw [huu, ← mul_assoc, hc.centralElt_mul_self, one_mul]
  rcases hz with hz | hz <;> rcases hr with hr | hr <;> rw [hz, hr]
  · rw [← mul_assoc, huu, ← he]
    exact hve
  · rw [show u * (u * v * e) = u * u * v * e by group, huu, ← he,
      hc.mul_centralElt_mul_centralElt]
    exact hv
  · rw [h3]
    exact hv
  · rw [show u * e * (u * v * e) = u * e * (u * v) * e by group, h3]
    exact hve

theorem mul_comm_of_conj_eq (hc : PartC T Q P₁ e u) {a b s : G} (ha : a * s * a⁻¹ = s * e)
    (hb : b * s * b⁻¹ = s * e) : a * b * s = s * (a * b) := by
  have h1 : a * b * s * (a * b)⁻¹ = s := by
    calc a * b * s * (a * b)⁻¹ = a * (b * s * b⁻¹) * a⁻¹ := by group
      _ = a * (s * e) * a⁻¹ := by rw [hb]
      _ = a * s * a⁻¹ * e := hc.conj_mul_centralElt a s
      _ = s := by rw [ha, hc.mul_centralElt_mul_centralElt]
  calc a * b * s = a * b * s * (a * b)⁻¹ * (a * b) := by group
    _ = s * (a * b) := by rw [h1]

include φ in
theorem mul_eq_of_conj_eq [Finite G] [NeZero N] (hc : PartC T Q P₁ e u) (hyT : y ∈ T)
    (hy : y ∉ Q ⊔ P₁) (hyy : y * y ∈ P₁) (hN : 3 ≤ N)
    (hnorm : T ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G)) {v : G} (hvQ : v ∈ Q)
    (hvv : v * v = e) (hTv : T ≤ Subgroup.normalizer (Subgroup.zpowers v : Set G)) {a b : G}
    (haT : a ∈ T) (hbT : b ∈ T) (haa : a * a = e) (hbb : b * b = e) (hau : a * u * a⁻¹ = u * e)
    (hbu : b * u * b⁻¹ = u * e) (habab : a * b * (a * b) = 1) (hab1 : a * b ≠ 1)
    (habe : a * b ≠ e) : a * b = u * v ∨ a * b = u * v * e := by
  have hcase : ∀ t ∈ T, t * t = e → t * u * t⁻¹ = u * e → t ∈ P₁ ∨ t ∉ Q ⊔ P₁ :=
    fun t _ htt htu => by
      by_cases ht : t ∈ Q ⊔ P₁
      · exact Or.inl (hc.mem_right_of_conj_eq ht htt htu)
      · exact Or.inr ht
  have hinvol : orderOf (a * b) = 2 := orderOf_eq_prime (by rw [pow_two]; exact habab) hab1
  have habT : a * b ∈ T := T.mul_mem haT hbT
  rcases hcase a haT haa hau with ha | ha <;> rcases hcase b hbT hbb hbu with hb | hb
  · exact absurd (hc.unique _ (P₁.mul_mem ha hb) hinvol) habe
  · exfalso
    apply hb
    have h := hc.involution_mem _ habT hinvol
    simpa using (Q ⊔ P₁).mul_mem ((Q ⊔ P₁).inv_mem (Subgroup.mem_sup_right ha)) h
  · exfalso
    apply ha
    have h := hc.involution_mem _ habT hinvol
    simpa using (Q ⊔ P₁).mul_mem h ((Q ⊔ P₁).inv_mem (Subgroup.mem_sup_right hb))
  · have habQ : a * b ∈ Q ⊔ P₁ := by
      have h := hc.inv_mul_mem a⁻¹ (T.inv_mem haT) b hbT
        (fun h => ha (by simpa using (Q ⊔ P₁).inv_mem h)) hb
      rwa [inv_inv] at h
    have hvn : ∀ t ∈ T, t * v * t⁻¹ ∈ Subgroup.zpowers v := fun t ht =>
      (Subgroup.mem_normalizer_iff.mp (hTv ht) v).mp (Subgroup.mem_zpowers v)
    have hav := hc.conj_eq_mul_centralElt haT ha haa (Subgroup.mem_sup_left hvQ) hvv (hvn a haT)
    have hbv := hc.conj_eq_mul_centralElt hbT hb hbb (Subgroup.mem_sup_left hvQ) hvv (hvn b hbT)
    exact hc.eq_mul_of_commute φ hyT hy hyy hN hnorm hvQ hvv habQ habab hab1 habe
      (hc.mul_comm_of_conj_eq hau hbu) (hc.mul_comm_of_conj_eq hav hbv)

include φ in
theorem conj_ne_self [Finite G] [NeZero N] (hc : PartC T Q P₁ e u) (hyT : y ∈ T)
    (hy : y ∉ Q ⊔ P₁) (hyy : y * y ∈ P₁) (hP₁ : ¬ IsCyclic P₁) (hN : 8 ∣ N) (S : Sylow 2 G)
    (hST : (S : Subgroup G) = T) (hnorm : T ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G))
    {v : G} (hvQ : v ∈ Q) (hvv : v * v = e)
    (hTv : T ≤ Subgroup.normalizer (Subgroup.zpowers v : Set G))
    (hfus : ∀ g : G, g * u * g⁻¹ ∉ Subgroup.zpowers v) {x : G} (hxT : x ∈ T)
    (hx : x ∉ Q ⊔ P₁) (hxx : x * x = e) (g : G) : g * x * g⁻¹ ≠ u := by
  intro hgx
  have hN3 : 3 ≤ N := by
    obtain ⟨M, hM⟩ := hN
    have := NeZero.ne N
    omega
  have hxu : x * u * x⁻¹ = u * e := hc.conj_eq_mul_centralElt hxT hx hxx
    (Subgroup.mem_sup_right hc.self_mem) hc.sq
    ((Subgroup.mem_normalizer_iff.mp (hnorm hxT) u).mp (Subgroup.mem_zpowers u))
  have hxv : x * v * x⁻¹ = v * e := hc.conj_eq_mul_centralElt hxT hx hxx
    (Subgroup.mem_sup_left hvQ) hvv
    ((Subgroup.mem_normalizer_iff.mp (hTv hxT) v).mp (Subgroup.mem_zpowers v))
  have hvu : v * u = u * v := hc.commute v hvQ u hc.self_mem
  set D := T ⊓ Subgroup.normalizer (Subgroup.zpowers x : Set G) with hD
  have huD : u ∈ D := ⟨hc.right_le hc.self_mem, mem_normalizer_zpowers_of_conj_mem
    (by rw [hc.conj_swap hxu]; exact mul_centralElt_mem_zpowers hxx)⟩
  have hvD : v ∈ D := ⟨hc.left_le hvQ, mem_normalizer_zpowers_of_conj_mem
    (by rw [hc.conj_swap hxv]; exact mul_centralElt_mem_zpowers hxx)⟩
  have hD'X : D.map (MulAut.conj g).toMonoidHom ≤
      Subgroup.normalizer (Subgroup.zpowers u : Set G) := by
    rintro _ ⟨d, ⟨-, hdN⟩, rfl⟩
    refine mem_normalizer_zpowers_of_conj_mem ?_
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
      ((Subgroup.mem_normalizer_iff.mp hdN x).mp (Subgroup.mem_zpowers x))
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hgx, conj_zpow, hk]
    group
  have hD'p : IsPGroup 2 (D.map (MulAut.conj g).toMonoidHom) :=
    (hc.isPGroup.to_le inf_le_left).map _
  obtain ⟨k, hkX, hk⟩ := exists_conj_mem_sylow_of_le S (hST ▸ hnorm) hD'X hD'p
  set σ := MulAut.conj (k * g) with hσ
  have hσT : ∀ d ∈ D, σ d ∈ T := fun d hd => by
    have h1 := hk (g * d * g⁻¹) ⟨d, hd, rfl⟩
    rw [hσ, MulAut.conj_apply, show k * g * d * (k * g)⁻¹ = k * (g * d * g⁻¹) * k⁻¹ by group,
      ← hST]
    exact h1
  have hσe : σ e = e := by rw [hσ, MulAut.conj_apply, hc.conj_centralElt]
  have hx₀ : σ x = u ∨ σ x = u * e := by
    rw [hσ, MulAut.conj_apply, show k * g * x * (k * g)⁻¹ = k * (g * x * g⁻¹) * k⁻¹ by group,
      hgx]
    exact hc.conj_eq_of_mem_zpowers hc.sq
      ((Subgroup.mem_normalizer_iff.mp hkX u).mp (Subgroup.mem_zpowers u))
  have hconj_mod : ∀ s : G, s * x * s⁻¹ = x * e → σ s * u * (σ s)⁻¹ = u * e := fun s h => by
    refine hc.conj_self_of_conj_mod hx₀ ?_
    rw [← map_inv, ← map_mul, ← map_mul, h, map_mul, hσe]
  have hab : σ u * σ v * (σ u * σ v) = 1 := by
    rw [← map_mul, ← map_mul, show u * v * (u * v) = u * u * (v * v) by
      rw [show u * v * (u * v) = u * (v * u) * v by group, hvu]; group, hc.sq, hvv,
      hc.centralElt_mul_self, map_one]
  have hab1 : σ u * σ v ≠ 1 := by
    rw [← map_mul, Ne, map_eq_one_iff _ σ.injective]
    intro h
    have hvP : v ∈ P₁ := by
      rw [eq_inv_of_mul_eq_one_right h]
      exact P₁.inv_mem hc.self_mem
    rcases hc.mem_inf v hvQ hvP with h' | h' <;> rw [h'] at hvv
    · exact hc.centralElt_ne_one (by rw [← hvv, mul_one])
    · exact hc.centralElt_ne_one (by rw [← hvv, hc.centralElt_mul_self])
  have habe : σ u * σ v ≠ e := by
    rw [← map_mul, ← hσe, Ne, σ.injective.eq_iff]
    intro h
    have hvP : v ∈ P₁ := by
      rw [show v = u⁻¹ * (u * v) by group, h]
      exact P₁.mul_mem (P₁.inv_mem hc.self_mem) hc.mem_right
    rcases hc.mem_inf v hvQ hvP with h' | h' <;> rw [h'] at hvv
    · exact hc.centralElt_ne_one (by rw [← hvv, mul_one])
    · exact hc.centralElt_ne_one (by rw [← hvv, hc.centralElt_mul_self])
  have hr := hc.mul_eq_of_conj_eq φ hyT hy hyy hN3 hnorm hvQ hvv hTv (hσT u huD) (hσT v hvD)
    (by rw [← map_mul, hc.sq, hσe]) (by rw [← map_mul, hvv, hσe])
    (hconj_mod u (hc.conj_swap hxu)) (hconj_mod v (hc.conj_swap hxv)) hab hab1 habe
  have hkey : σ (x * u * v) ∈ Subgroup.zpowers v := by
    rw [map_mul, map_mul, mul_assoc]
    exact hc.mul_mem_zpowers_of_mod hvv hx₀ hr
  obtain ⟨s, -, hs⟩ := hc.exists_conj_eq_mul_mul φ hyT hy hyy hP₁ hN hnorm hvQ hvv hTv hxT hx hxx
  have he' : e ∈ Subgroup.zpowers v := by
    rw [← hvv]
    exact Subgroup.mul_mem _ (Subgroup.mem_zpowers v) (Subgroup.mem_zpowers v)
  have hsx : σ s * σ x * (σ s)⁻¹ ∈ Subgroup.zpowers v := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rcases hs with h | h <;> rw [h]
    · exact hkey
    · rw [map_mul, hσe]
      exact Subgroup.mul_mem _ hkey he'
  rcases hx₀ with h | h <;> rw [h] at hsx
  · exact hfus _ hsx
  · rw [hc.conj_mul_centralElt] at hsx
    refine hfus (σ s) ?_
    simpa [hc.mul_centralElt_mul_centralElt] using Subgroup.mul_mem _ hsx he'

end PartC

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

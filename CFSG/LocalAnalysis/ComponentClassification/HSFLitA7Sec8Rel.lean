module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8CPair
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8Elem

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8

open Sec7

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

omit [Finite X] in
theorem mem_normalizer_of_conj_gens' [Finite X] {a b g : X}
    (ha : g * a * g⁻¹ ∈ zpowers a ⊔ zpowers b) (hb : g * b * g⁻¹ ∈ zpowers a ⊔ zpowers b) :
    g ∈ normalizer ((zpowers a ⊔ zpowers b : Subgroup X) : Set X) := by
  have hle : (zpowers a ⊔ zpowers b : Subgroup X).map (MulAut.conj g).toMonoidHom ≤
      zpowers a ⊔ zpowers b := by
    rw [map_le_iff_le_comap]
    exact sup_le (zpowers_le.mpr ha) (zpowers_le.mpr hb)
  refine mem_normalizer_of_map_eq (Subgroup.eq_of_le_of_card_ge hle ?_)
  rw [card_map_of_injective (MulAut.conj g).injective]

namespace VSide

variable (V : VSide S F T₁)

theorem elemAbelianTwo_ki : ElemAbelianTwo (zpowers V.ki) :=
  ⟨fun _ ha _ hb => commute_of_mem_B (zpowers_le.mpr V.hki.mem ha) (zpowers_le.mpr V.hki.mem hb),
    fun _ ha => S.sq_of_mem_B (zpowers_le.mpr V.hki.mem ha)⟩

theorem t_not_mem_ki : S.t ∉ zpowers V.ki := fun h =>
  V.t_not_mem_zk (mem_sup_right h)

theorem card_kt : Nat.card (zpowers V.ki ⊔ zpowers S.t : Subgroup X) = 4 := by
  rw [card_sup_of_not_mem V.elemAbelianTwo_ki S.t_sq V.t_not_mem_ki
    (fun a ha => commute_of_mem_B t_mem_B (zpowers_le.mpr V.hki.mem ha)), Nat.card_zpowers,
    orderOf_eq_prime V.hki.sq V.hki.ne_one]

theorem w₁_mem_Q0 : V.D.w₁ ∈ S.Q0 V.yi V.ki V.D.w₁ V.D.w₂ :=
  mem_sup_left (mem_sup_right (mem_zpowers _))

theorem w₂_mem_Q0' : V.D.w₂ ∈ S.Q0 V.yi V.ki V.D.w₁ V.D.w₂ := mem_sup_right (mem_zpowers _)

theorem eq_of_mem_ki {c : X} (hc : c ∈ zpowers V.ki) : c = 1 ∨ c = V.ki :=
  eq_one_or_eq_of_mem_zpowers V.hki.sq hc

theorem mem_C {c : X} (hc : c ∈ V.D.Q₁ ⊓ centralizer (V.D.D₁₁ : Set X)) :
    c ∈ (zpowers V.ki ⊔ zpowers S.t : Subgroup X) ∨
      c * V.vN⁻¹ ∈ (zpowers V.ki ⊔ zpowers S.t : Subgroup X) := by
  have hN : V.vN ∈ normalizer ((zpowers V.ki ⊔ zpowers S.t : Subgroup X) : Set X) :=
    mem_normalizer_of_conj_gens' (by rw [V.vN_conj_ki]; exact mem_sup_left (mem_zpowers _))
      (by rw [V.vN_conj_t]
          exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left (mem_zpowers _)))
  have hv2 : V.vN ^ 2 ∈ (zpowers V.ki ⊔ zpowers S.t : Subgroup X) := by
    rw [V.vN_sq]; exact one_mem _
  have hle : closure ({S.t, V.ki, V.D.v} : Set X) ≤
      (zpowers V.ki ⊔ zpowers S.t : Subgroup X) ⊔ zpowers V.vN := by
    rw [closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact mem_sup_left (mem_sup_right (mem_zpowers _))
    · exact mem_sup_left (mem_sup_left (mem_zpowers _))
    · rcases V.vN_eq with h | h
      · rw [← h]; exact mem_sup_right (mem_zpowers _)
      · have : V.D.v = V.vN * S.t⁻¹ := by rw [h]; group
        rw [this]
        exact mul_mem (mem_sup_right (mem_zpowers _))
          (mem_sup_left (mem_sup_right (inv_mem (mem_zpowers _))))
  have hc' := hle (V.D.C_eq ▸ hc)
  exact mem_or_of_mem_sup_zpowers hN hv2 hc'

theorem exists_evE : ∃ φ : (Fin 4 → Multiplicative (ZMod 2)) →* X,
    φ (e4 0) = S.t ∧ φ (e4 1) = S.z ∧ φ (e4 2) = V.yi ∧ φ (e4 3) = V.ki := by
  have hE := V.hyi.elemAbelianTwo_E
  have ht := t_mem_E (S := S) V.yi
  have hz := z_mem_E (S := S) V.yi
  have hy := mem_E_self (S := S) V.yi
  have hk := B_le_E V.yi V.hki.mem
  exact exists_evHom4 (hE.comm _ ht _ hz) (hE.comm _ ht _ hy) (hE.comm _ ht _ hk)
    (hE.comm _ hz _ hy) (hE.comm _ hz _ hk) (hE.comm _ hy _ hk) t_mul_t z_mul_z V.yi_mul_yi V.ki_sq

theorem w₂_mem_S₁ : V.D.w₂ ∈ V.D.S₁ := by
  rw [V.D.S₁_eq]; exact mem_sup_left (mem_sup_right (mem_zpowers _))

theorem u_mem_S₁ : V.D.u ∈ V.D.S₁ := by
  rw [V.D.S₁_eq]; exact mem_sup_right (mem_zpowers _)

theorem mem_normalizer_E0 {n : X} (hn : n ∈ normalizer (S.E V.yi : Set X)) :
    n ∈ normalizer (S.E0 V.yi V.ki : Set X) := by
  rw [mem_normalizer_iff]
  intro e
  refine ⟨fun he => V.conj_mem_E0 hn he, fun he => ?_⟩
  have := V.conj_mem_E0 (inv_mem hn) he
  rwa [show n⁻¹ * (n * e * n⁻¹) * n⁻¹⁻¹ = e by group] at this

theorem comm_mem {a b : X} (ha : a ∈ V.D.S₁) (hb : b ∈ V.D.S₁) :
    a * b * a⁻¹ * b⁻¹ ∈ S.E0 V.yi V.ki ⊔ zpowers V.D.w₁ :=
  V.D.S₁_commutator_mem a ha b hb

theorem mem_E0w {c : X} (hc : c ∈ S.E0 V.yi V.ki ⊔ zpowers V.D.w₁) :
    c ∈ S.E0 V.yi V.ki ∨ c * V.D.w₁⁻¹ ∈ S.E0 V.yi V.ki :=
  mem_or_of_mem_sup_zpowers (V.mem_normalizer_E0 (V.D.S₁_le V.w₁_mem_S₁))
    (by rw [V.w₁_sq]; exact one_mem _) hc

theorem mem_E0_cases {e : X} (he : e ∈ S.E0 V.yi V.ki) :
    e ∈ (zpowers S.z ⊔ zpowers V.ki : Subgroup X) ∨
      e * V.yi ∈ (zpowers S.z ⊔ zpowers V.ki : Subgroup X) := by
  rw [E0_eq] at he
  exact mem_or_of_mem_sup (elemAbelianTwo_zk V.hki) V.hyi.sq
    (fun _ hb => V.hyi.comm_B (zk_le_B V.hki hb)) he

theorem u_conj_B {b : X} (hb : b ∈ S.B) : V.D.u * b * V.D.u⁻¹ = b := by
  rw [← S.central_of_mem_B hb V.u_mem_T, mul_inv_cancel_right]

theorem u_conj_yi : V.D.u * V.yi * V.D.u⁻¹ = S.z * V.yi := by
  rw [V.u_eq]
  have h := refl_x_conj V.hyi
  calc S.t * (F.xF * V.yi) * V.yi * (S.t * (F.xF * V.yi))⁻¹ =
      S.t * (F.xF * (V.yi * V.yi * V.yi⁻¹) * F.xF⁻¹) * S.t⁻¹ := by group
    _ = S.t * (S.z * V.yi) * S.t⁻¹ := by rw [mul_inv_cancel_right, h]
    _ = S.z * V.yi := by
        rw [t_comm_T (mul_mem z_mem_T V.hyi.mem_T), mul_inv_cancel_right]

theorem kappa_conj_t : (V.D.w₂ * V.D.w₁ * V.D.w₂⁻¹ * V.D.w₁⁻¹) * S.t *
    (V.D.w₂ * V.D.w₁ * V.D.w₂⁻¹ * V.D.w₁⁻¹)⁻¹ = S.t := by
  obtain ⟨φ, e0, e1, e2, e3⟩ := V.exists_evE
  have a1 := inv_conj_of_inv V.w₁_inv V.w₁_conj_t
  have hw₂z := inv_conj_of_inv V.w₂_inv V.w₂_conj_z
  have hw₂t := inv_conj_of_inv V.w₂_inv V.w₂_conj_t
  have hw₂k := inv_conj_of_inv V.w₂_inv V.w₂_conj_ki
  have a2 : V.D.w₂⁻¹ * (S.t * S.z * V.ki) * V.D.w₂ = S.t * V.yi * S.z * V.ki := by
    rw [show V.D.w₂⁻¹ * (S.t * S.z * V.ki) * V.D.w₂ = (V.D.w₂⁻¹ * S.t * V.D.w₂) *
      (V.D.w₂⁻¹ * S.z * V.D.w₂) * (V.D.w₂⁻¹ * V.ki * V.D.w₂) by group, hw₂t, hw₂z, hw₂k]
    elem_eq φ e0 e1 e2 e3
  have a3 : V.D.w₁ * (S.t * V.yi * S.z * V.ki) * V.D.w₁⁻¹ = S.t * V.yi * V.ki := by
    rw [show V.D.w₁ * (S.t * V.yi * S.z * V.ki) * V.D.w₁⁻¹ = (V.D.w₁ * S.t * V.D.w₁⁻¹) *
      (V.D.w₁ * V.yi * V.D.w₁⁻¹) * (V.D.w₁ * S.z * V.D.w₁⁻¹) * (V.D.w₁ * V.ki * V.D.w₁⁻¹) by
        group, V.w₁_conj_t, V.w₁_conj_yi, V.w₁_conj_z, V.w₁_conj_ki]
    elem_eq φ e0 e1 e2 e3
  have a4 : V.D.w₂ * (S.t * V.yi * V.ki) * V.D.w₂⁻¹ = S.t := by
    rw [show V.D.w₂ * (S.t * V.yi * V.ki) * V.D.w₂⁻¹ = (V.D.w₂ * S.t * V.D.w₂⁻¹) *
      (V.D.w₂ * V.yi * V.D.w₂⁻¹) * (V.D.w₂ * V.ki * V.D.w₂⁻¹) by group, V.w₂_conj_t,
      V.w₂_conj_yi, V.w₂_conj_ki]
    elem_eq φ e0 e1 e2 e3
  calc (V.D.w₂ * V.D.w₁ * V.D.w₂⁻¹ * V.D.w₁⁻¹) * S.t *
      (V.D.w₂ * V.D.w₁ * V.D.w₂⁻¹ * V.D.w₁⁻¹)⁻¹ =
      V.D.w₂ * (V.D.w₁ * (V.D.w₂⁻¹ * (V.D.w₁⁻¹ * S.t * V.D.w₁) * V.D.w₂) * V.D.w₁⁻¹) *
        V.D.w₂⁻¹ := by group
    _ = S.t := by rw [a1, a2, a3, a4]

theorem kappa_mem_E0 : V.D.w₂ * V.D.w₁ * V.D.w₂⁻¹ * V.D.w₁⁻¹ ∈ S.E0 V.yi V.ki := by
  rcases V.mem_E0w (V.comm_mem V.w₂_mem_S₁ V.w₁_mem_S₁) with h | h
  · exact h
  · exfalso
    set κ := V.D.w₂ * V.D.w₁ * V.D.w₂⁻¹ * V.D.w₁⁻¹ with hκ
    set e := κ * V.D.w₁⁻¹ with he
    have hκe : κ = e * V.D.w₁ := by rw [he]; group
    have heE : e ∈ S.E V.yi := E0_le_E V.hki V.yi h
    have h1 := V.kappa_conj_t
    rw [← hκ, hκe] at h1
    have hE := V.hyi.elemAbelianTwo_E
    have hzk : S.t * S.z * V.ki ∈ S.E V.yi :=
      mul_mem (mul_mem (t_mem_E _) (z_mem_E _)) (B_le_E _ V.hki.mem)
    rw [show e * V.D.w₁ * S.t * (e * V.D.w₁)⁻¹ = e * (V.D.w₁ * S.t * V.D.w₁⁻¹) * e⁻¹ by group,
      V.w₁_conj_t, hE.comm _ heE _ hzk, mul_inv_cancel_right, mul_assoc] at h1
    exact V.hki.ne_one (by
      have : S.z * V.ki = 1 := mul_eq_left.mp h1
      exact absurd this (fun h' => S.z_ne_one (by
        have hk : V.ki = S.z := by
          calc V.ki = S.z * (S.z * V.ki) := by rw [← mul_assoc, z_mul_z, one_mul]
            _ = S.z := by rw [h', mul_one]
        exact absurd (hk ▸ mem_sup_left (mem_zpowers _) : V.ki ∈ zpowers S.z ⊔ zpowers S.t)
          V.hki.not_mem)))

theorem kappa_eq : V.D.w₂ * V.D.w₁ * V.D.w₂⁻¹ * V.D.w₁⁻¹ = 1 ∨
    V.D.w₂ * V.D.w₁ * V.D.w₂⁻¹ * V.D.w₁⁻¹ = V.ki := by
  set κ := V.D.w₂ * V.D.w₁ * V.D.w₂⁻¹ * V.D.w₁⁻¹ with hκ
  have hκw : V.D.w₂ * V.D.w₁ * V.D.w₂⁻¹ = κ * V.D.w₁ := by rw [hκ]; group
  have hw₁ := V.w₁_sq
  have hw₂ := V.w₂_sq
  rw [pow_two] at hw₁ hw₂
  have hb : κ * (V.D.w₁ * κ * V.D.w₁⁻¹) = 1 := by
    have : (κ * V.D.w₁) * (κ * V.D.w₁) = 1 := by
      rw [← hκw, show V.D.w₂ * V.D.w₁ * V.D.w₂⁻¹ * (V.D.w₂ * V.D.w₁ * V.D.w₂⁻¹) =
        V.D.w₂ * (V.D.w₁ * V.D.w₁) * V.D.w₂⁻¹ by group, hw₁, mul_one, mul_inv_cancel]
    calc κ * (V.D.w₁ * κ * V.D.w₁⁻¹) = (κ * V.D.w₁) * (κ * V.D.w₁) * V.D.w₁⁻¹ * V.D.w₁⁻¹ := by
          group
      _ = 1 := by rw [this, one_mul, ← mul_inv_rev, hw₁, inv_one]
  have ha : (V.D.w₂ * κ * V.D.w₂⁻¹) * κ = 1 := by
    have h1 : V.D.w₂ * (V.D.w₂ * V.D.w₁ * V.D.w₂⁻¹) * V.D.w₂⁻¹ = V.D.w₁ := by
      rw [show V.D.w₂ * (V.D.w₂ * V.D.w₁ * V.D.w₂⁻¹) * V.D.w₂⁻¹ =
        (V.D.w₂ * V.D.w₂) * V.D.w₁ * (V.D.w₂ * V.D.w₂)⁻¹ by group, hw₂, one_mul, inv_one,
        mul_one]
    have h2 : V.D.w₂ * (κ * V.D.w₁) * V.D.w₂⁻¹ = V.D.w₁ := by rw [← hκw]; exact h1
    have h3 : (V.D.w₂ * κ * V.D.w₂⁻¹) * (κ * V.D.w₁) = V.D.w₁ := by
      calc (V.D.w₂ * κ * V.D.w₂⁻¹) * (κ * V.D.w₁) =
          (V.D.w₂ * κ * V.D.w₂⁻¹) * (V.D.w₂ * V.D.w₁ * V.D.w₂⁻¹) := by rw [hκw]
        _ = V.D.w₂ * (κ * V.D.w₁) * V.D.w₂⁻¹ := by group
        _ = V.D.w₁ := h2
    calc (V.D.w₂ * κ * V.D.w₂⁻¹) * κ = (V.D.w₂ * κ * V.D.w₂⁻¹) * (κ * V.D.w₁) * V.D.w₁⁻¹ := by
          group
      _ = 1 := by rw [h3, mul_inv_cancel]
  have hmem := V.kappa_mem_E0
  rw [← hκ] at hmem
  rcases V.mem_E0_cases hmem with h | h
  · rcases V.eq_of_mem_zk h with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exfalso
      rw [h1, V.w₂_conj_z] at ha
      exact V.hki.ne_one (by
        rw [mul_assoc, V.ki_comm z_mem_T, ← mul_assoc, z_mul_z, one_mul] at ha
        exact ha)
    · exact Or.inr h1
    · exfalso
      rw [h1, show V.D.w₂ * (S.z * V.ki) * V.D.w₂⁻¹ = (V.D.w₂ * S.z * V.D.w₂⁻¹) *
        (V.D.w₂ * V.ki * V.D.w₂⁻¹) by group, V.w₂_conj_z, V.w₂_conj_ki, mul_assoc S.z,
        V.ki_sq, mul_one, ← mul_assoc, z_mul_z, one_mul] at ha
      exact V.hki.ne_one ha
  · exfalso
    set c := κ * V.yi with hc
    have hκc : κ = c * V.yi := by rw [hc, mul_assoc, V.yi_mul_yi, mul_one]
    have hcw : V.D.w₁ * c * V.D.w₁⁻¹ = c := V.conj_zk_of_fix V.w₁_conj_z V.w₁_conj_ki h
    rw [hκc, show V.D.w₁ * (c * V.yi) * V.D.w₁⁻¹ = (V.D.w₁ * c * V.D.w₁⁻¹) *
      (V.D.w₁ * V.yi * V.D.w₁⁻¹) by group, hcw, V.w₁_conj_yi] at hb
    have hcB := zk_le_B V.hki h
    have hcy : c * V.yi = V.yi * c := (V.hyi.comm_B hcB).symm
    have hcc : c * c = 1 := by rw [← pow_two, S.sq_of_mem_B hcB]
    rw [show c * V.yi * (c * (V.yi * V.ki)) = (c * V.yi) * c * V.yi * V.ki by group, hcy,
      mul_assoc V.yi, hcc, mul_one, V.yi_mul_yi, one_mul] at hb
    exact V.hki.ne_one hb

theorem yi_w₁ : V.yi * V.D.w₁ = V.D.w₁ * (V.yi * V.ki) := by
  have h := inv_conj_of_inv V.w₁_inv V.w₁_conj_yi
  calc V.yi * V.D.w₁ = V.D.w₁ * (V.D.w₁⁻¹ * V.yi * V.D.w₁) := by group
    _ = V.D.w₁ * (V.yi * V.ki) := by rw [h]

theorem zk_w₁ {c : X} (hc : c ∈ (zpowers S.z ⊔ zpowers V.ki : Subgroup X)) :
    c * V.D.w₁ = V.D.w₁ * c := by
  have h := inv_conj_of_inv V.w₁_inv (V.conj_zk_of_fix V.w₁_conj_z V.w₁_conj_ki hc)
  calc c * V.D.w₁ = V.D.w₁ * (V.D.w₁⁻¹ * c * V.D.w₁) := by group
    _ = V.D.w₁ * c := by rw [h]

theorem u_yi : V.D.u * V.yi = S.z * V.yi * V.D.u := by
  rw [← V.u_conj_yi]; group

theorem B_u {b : X} (hb : b ∈ S.B) : b * V.D.u = V.D.u * b :=
  S.central_of_mem_B hb V.u_mem_T

end VSide

namespace CPair

variable (P : CPair S F T₁)

theorem w₂_conj_vN : P.V.D.w₂ * P.V.vN * P.V.D.w₂⁻¹ = P.V.vN * (P.V.yi * P.V.ki) := by
  set K := (zpowers P.V.ki ⊔ zpowers S.t : Subgroup X) with hK
  have hC₁ : ¬ P.V.D.C₁ ≤ K := by
    intro hle
    have heq : P.V.D.C₁ = K :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [P.V.D.card_C₁, P.V.card_kt])
    have ht : S.t ∈ P.V.D.C₁ := heq ▸ mem_sup_right (mem_zpowers _)
    have h1 := P.V.D.C₁_comm S.t ht P.V.D.w₁ P.V.w₁_mem_Q0
    apply P.V.D.w₁_comm_t
    rw [← h1]; group
  obtain ⟨c, hc, hcK⟩ := IsConcreteLE.not_le_iff_exists.mp hC₁
  have hcC := P.V.D.C₁_le hc
  have hcw₁ := P.V.D.C₁_comm c hc P.V.D.w₁ P.V.w₁_mem_Q0
  have hcw₂ := P.V.D.C₁_comm c hc P.V.D.w₂ P.V.w₂_mem_Q0'
  rcases P.V.mem_C hcC with h | h
  · exact absurd h hcK
  set d := c * P.V.vN⁻¹ with hd
  have hc' : c = d * P.V.vN := by rw [hd]; group
  rw [hc'] at hcw₁ hcw₂
  rcases mem_or_of_mem_sup P.V.elemAbelianTwo_ki S.t_sq
    (fun a ha => commute_of_mem_B t_mem_B (zpowers_le.mpr P.V.hki.mem ha)) h with h' | h'
  ·
    exfalso
    have hdw : P.V.D.w₁ * d * P.V.D.w₁⁻¹ = d := by
      rcases P.V.eq_of_mem_ki h' with h1 | h1 <;> rw [h1]
      · group
      · exact P.V.w₁_conj_ki
    have hvw : P.V.D.w₁ * P.V.vN * P.V.D.w₁⁻¹ * P.V.vN⁻¹ = 1 := by
      calc P.V.D.w₁ * P.V.vN * P.V.D.w₁⁻¹ * P.V.vN⁻¹ =
          (P.V.D.w₁ * d * P.V.D.w₁⁻¹)⁻¹ * (P.V.D.w₁ * (d * P.V.vN)) * P.V.D.w₁⁻¹ * P.V.vN⁻¹ := by
            group
        _ = 1 := by rw [hdw, ← hcw₁]; group
    rw [P.w₁_comm_vN] at hvw
    exact P.V.hki.not_mem (by
      have : P.V.ki = S.z := by
        calc P.V.ki = S.z * (S.z * P.V.ki) := by rw [← mul_assoc, z_mul_z, one_mul]
          _ = S.z := by rw [hvw, mul_one]
      rw [this]; exact mem_sup_left (mem_zpowers _))
  ·
    set d' := d * S.t with hd'
    have hdd : d = d' * S.t := by rw [hd', mul_assoc, t_mul_t, mul_one]
    have hdw : P.V.D.w₂ * d' * P.V.D.w₂⁻¹ = d' := by
      rcases P.V.eq_of_mem_ki h' with h1 | h1 <;> rw [h1]
      · group
      · exact P.V.w₂_conj_ki
    have hd'E : d' ∈ S.E P.V.yi := B_le_E _ (zpowers_le.mpr P.V.hki.mem h')
    rw [hdd] at hcw₂
    have h2 : P.V.D.w₂ * (d' * S.t * P.V.vN) * P.V.D.w₂⁻¹ = d' * S.t * P.V.vN := by
      rw [← hcw₂]; group
    rw [show P.V.D.w₂ * (d' * S.t * P.V.vN) * P.V.D.w₂⁻¹ = (P.V.D.w₂ * d' * P.V.D.w₂⁻¹) *
      (P.V.D.w₂ * S.t * P.V.D.w₂⁻¹) * (P.V.D.w₂ * P.V.vN * P.V.D.w₂⁻¹) by group, hdw,
      P.V.w₂_conj_t] at h2
    have hE := P.V.hyi.elemAbelianTwo_E
    have hyk : P.V.yi * P.V.ki = P.V.ki * P.V.yi := (P.V.ki_comm P.yi_mem_T).symm
    calc P.V.D.w₂ * P.V.vN * P.V.D.w₂⁻¹ = (d' * (S.t * P.V.yi * P.V.ki))⁻¹ *
        (d' * (S.t * P.V.yi * P.V.ki) * (P.V.D.w₂ * P.V.vN * P.V.D.w₂⁻¹)) := by group
      _ = (d' * (S.t * P.V.yi * P.V.ki))⁻¹ * (d' * S.t * P.V.vN) := by rw [h2]
      _ = (P.V.yi * P.V.ki)⁻¹ * P.V.vN := by group
      _ = P.V.vN * (P.V.yi * P.V.ki) := by
          rw [mul_inv_rev, P.V.ki_inv, P.V.yi_inv, ← hyk]
          have h3 : P.V.vN * (P.V.yi * P.V.ki) * P.V.vN⁻¹ = P.V.yi * P.V.ki := by
            rw [show P.V.vN * (P.V.yi * P.V.ki) * P.V.vN⁻¹ = (P.V.vN * P.V.yi * P.V.vN⁻¹) *
              (P.V.vN * P.V.ki * P.V.vN⁻¹) by group, P.V.vN_conj_yi, P.V.vN_conj_ki]
          calc P.V.yi * P.V.ki * P.V.vN = (P.V.vN * (P.V.yi * P.V.ki) * P.V.vN⁻¹) * P.V.vN := by
                rw [h3]
            _ = P.V.vN * (P.V.yi * P.V.ki) := by group

theorem u_w₁ : P.V.D.u * P.V.D.w₁ = P.V.D.w₁ * (S.z * P.V.ki) * P.V.D.u := by
  rw [← P.u_conj_w₁]; group

theorem wu_not_mem_E0 : P.V.D.w₂ * P.V.D.u * P.V.D.w₂⁻¹ * P.V.D.u⁻¹ ∉ S.E0 P.V.yi P.V.ki := by
  intro h
  set c := P.V.D.w₂ * P.V.D.u * P.V.D.w₂⁻¹ * P.V.D.u⁻¹ with hc
  have hwu : P.V.D.w₂ * P.V.D.u * P.V.D.w₂⁻¹ = c * P.V.D.u := by rw [hc]; group
  have hcE : c ∈ S.E P.V.yi := E0_le_E P.V.hki P.V.yi h
  have hE := P.V.hyi.elemAbelianTwo_E
  have h1 : (P.V.D.w₂ * P.V.D.u * P.V.D.w₂⁻¹) * (P.V.D.w₂ * S.t * P.V.D.w₂⁻¹) *
      (P.V.D.w₂ * P.V.D.u * P.V.D.w₂⁻¹)⁻¹ = P.V.D.w₂ * S.t * P.V.D.w₂⁻¹ := by
    rw [show (P.V.D.w₂ * P.V.D.u * P.V.D.w₂⁻¹) * (P.V.D.w₂ * S.t * P.V.D.w₂⁻¹) *
      (P.V.D.w₂ * P.V.D.u * P.V.D.w₂⁻¹)⁻¹ = P.V.D.w₂ * (P.V.D.u * S.t * P.V.D.u⁻¹) *
        P.V.D.w₂⁻¹ by group, P.V.u_conj_B t_mem_B]
  rw [hwu, P.V.w₂_conj_t] at h1
  have hmem : S.t * (S.z * P.V.yi) * P.V.ki ∈ S.E P.V.yi :=
    mul_mem (mul_mem (t_mem_E _) (mul_mem (z_mem_E _) (mem_E_self _))) (B_le_E _ P.V.hki.mem)
  have h2 : c * P.V.D.u * (S.t * P.V.yi * P.V.ki) * (c * P.V.D.u)⁻¹ =
      S.t * (S.z * P.V.yi) * P.V.ki := by
    rw [show c * P.V.D.u * (S.t * P.V.yi * P.V.ki) * (c * P.V.D.u)⁻¹ =
      c * ((P.V.D.u * S.t * P.V.D.u⁻¹) * (P.V.D.u * P.V.yi * P.V.D.u⁻¹) *
        (P.V.D.u * P.V.ki * P.V.D.u⁻¹)) * c⁻¹ by group, P.V.u_conj_B t_mem_B, P.V.u_conj_yi,
      P.V.u_conj_B P.V.hki.mem, hE.comm _ hcE _ hmem, mul_inv_cancel_right]
  have h3 := h2.symm.trans h1
  obtain ⟨φ, e0, e1, e2, e3⟩ := P.V.exists_evE
  have key : S.z = (S.t * (S.z * P.V.yi) * P.V.ki) * (S.t * P.V.yi * P.V.ki) := by
    elem_eq φ e0 e1 e2 e3
  have key2 : (S.t * P.V.yi * P.V.ki) * (S.t * P.V.yi * P.V.ki) = 1 := by
    elem_eq φ e0 e1 e2 e3
  rw [h3, key2] at key
  exact S.z_ne_one key

theorem exists_e : ∃ c ∈ (zpowers S.z ⊔ zpowers P.V.ki : Subgroup X),
    P.V.D.w₂ * P.V.D.u * P.V.D.w₂⁻¹ = c * P.V.yi * P.V.D.w₁ * P.V.D.u := by
  have hmem := P.V.comm_mem P.V.w₂_mem_S₁ P.V.u_mem_S₁
  rcases P.V.mem_E0w hmem with h | h
  · exact absurd h P.wu_not_mem_E0
  set e := P.V.D.w₂ * P.V.D.u * P.V.D.w₂⁻¹ * P.V.D.u⁻¹ * P.V.D.w₁⁻¹ with he
  have hwu : P.V.D.w₂ * P.V.D.u * P.V.D.w₂⁻¹ = e * P.V.D.w₁ * P.V.D.u := by rw [he]; group
  have hw₁ := P.V.w₁_sq
  have hw₂ := P.V.w₂_sq
  rw [pow_two] at hw₁ hw₂
  have hsq : (e * P.V.D.w₁ * P.V.D.u) * (e * P.V.D.w₁ * P.V.D.u) = 1 := by
    rw [← hwu, show P.V.D.w₂ * P.V.D.u * P.V.D.w₂⁻¹ * (P.V.D.w₂ * P.V.D.u * P.V.D.w₂⁻¹) =
      P.V.D.w₂ * (P.V.D.u * P.V.D.u) * P.V.D.w₂⁻¹ by group, P.V.u_mul_u, mul_one,
      mul_inv_cancel]
  have hform : (e * P.V.D.w₁ * P.V.D.u) * (e * P.V.D.w₁ * P.V.D.u) =
      e * (P.V.D.w₁ * (P.V.D.u * e * P.V.D.u⁻¹) * P.V.D.w₁⁻¹) * (S.z * P.V.ki) := by
    calc (e * P.V.D.w₁ * P.V.D.u) * (e * P.V.D.w₁ * P.V.D.u) =
        e * (P.V.D.w₁ * (P.V.D.u * e * P.V.D.u⁻¹) * P.V.D.w₁⁻¹) *
          (P.V.D.w₁ * (P.V.D.u * P.V.D.w₁ * P.V.D.u⁻¹)) * (P.V.D.u * P.V.D.u) := by group
      _ = _ := by
          rw [P.u_conj_w₁, P.V.u_mul_u, mul_one, ← mul_assoc P.V.D.w₁ P.V.D.w₁, hw₁, one_mul]
  rcases P.V.mem_E0_cases h with h' | h'
  · exfalso
    have hB := zk_le_B P.V.hki h'
    rw [hform, P.V.u_conj_B hB, P.V.conj_zk_of_fix P.V.w₁_conj_z P.V.w₁_conj_ki h',
      ← pow_two, S.sq_of_mem_B hB, one_mul] at hsq
    exact P.V.hki.not_mem (by
      have : P.V.ki = S.z := by
        calc P.V.ki = S.z * (S.z * P.V.ki) := by rw [← mul_assoc, z_mul_z, one_mul]
          _ = S.z := by rw [hsq, mul_one]
      rw [this]; exact mem_sup_left (mem_zpowers _))
  · refine ⟨e * P.V.yi, h', ?_⟩
    rw [hwu, mul_assoc e P.V.yi P.V.yi, P.V.yi_mul_yi, mul_one]

theorem w₂_conj_zk_eq {c : X} (hc : c = 1 ∨ c = S.z ∨ c = P.V.ki ∨ c = S.z * P.V.ki) :
    P.V.D.w₂ * c * P.V.D.w₂⁻¹ = 1 ∧ c = 1 ∨ P.V.D.w₂ * c * P.V.D.w₂⁻¹ = S.z * P.V.ki ∧ c = S.z ∨
      P.V.D.w₂ * c * P.V.D.w₂⁻¹ = P.V.ki ∧ c = P.V.ki ∨
        P.V.D.w₂ * c * P.V.D.w₂⁻¹ = S.z ∧ c = S.z * P.V.ki := by
  rcases hc with rfl | rfl | rfl | rfl
  · left; exact ⟨by group, rfl⟩
  · right; left; exact ⟨P.V.w₂_conj_z, rfl⟩
  · right; right; left; exact ⟨P.V.w₂_conj_ki, rfl⟩
  · right; right; right
    refine ⟨?_, rfl⟩
    rw [show P.V.D.w₂ * (S.z * P.V.ki) * P.V.D.w₂⁻¹ = (P.V.D.w₂ * S.z * P.V.D.w₂⁻¹) *
      (P.V.D.w₂ * P.V.ki * P.V.D.w₂⁻¹) by group, P.V.w₂_conj_z, P.V.w₂_conj_ki, mul_assoc,
      P.V.ki_sq, mul_one]

theorem exists_w₂' : ∃ w : X, (w = P.V.D.w₂ ∨ w = P.V.yi * P.V.D.w₂) ∧
    (∃ c ∈ zpowers P.V.ki, w * P.V.D.u * w⁻¹ = c * P.V.yi * P.V.D.w₁ * P.V.D.u) ∧
      w * P.V.D.w₁ * w⁻¹ = P.V.ki * P.V.D.w₁ := by
  obtain ⟨c, hc, hwu⟩ := P.exists_e
  have hκw : P.V.D.w₂ * P.V.D.w₁ * P.V.D.w₂⁻¹ = (P.V.D.w₂ * P.V.D.w₁ * P.V.D.w₂⁻¹ *
      P.V.D.w₁⁻¹) * P.V.D.w₁ := by group
  have hw₂ := P.V.w₂_sq
  rw [pow_two] at hw₂
  have hcB := zk_le_B P.V.hki hc
  have hcw₁ := P.V.conj_zk_of_fix P.V.w₁_conj_z P.V.w₁_conj_ki hc
  have hrel : (P.V.D.w₂ * c * P.V.D.w₂⁻¹) * P.V.yi *
      (P.V.D.w₂ * P.V.D.w₁ * P.V.D.w₂⁻¹ * P.V.D.w₁⁻¹) * (c * (P.V.yi * P.V.ki)) = 1 := by
    have h1 : P.V.D.w₂ * (P.V.D.w₂ * P.V.D.u * P.V.D.w₂⁻¹) * P.V.D.w₂⁻¹ = P.V.D.u := by
      rw [show P.V.D.w₂ * (P.V.D.w₂ * P.V.D.u * P.V.D.w₂⁻¹) * P.V.D.w₂⁻¹ =
        (P.V.D.w₂ * P.V.D.w₂) * P.V.D.u * (P.V.D.w₂ * P.V.D.w₂)⁻¹ by group, hw₂, one_mul,
        inv_one, mul_one]
    rw [hwu, show P.V.D.w₂ * (c * P.V.yi * P.V.D.w₁ * P.V.D.u) * P.V.D.w₂⁻¹ =
      (P.V.D.w₂ * c * P.V.D.w₂⁻¹) * (P.V.D.w₂ * P.V.yi * P.V.D.w₂⁻¹) *
        (P.V.D.w₂ * P.V.D.w₁ * P.V.D.w₂⁻¹) * (P.V.D.w₂ * P.V.D.u * P.V.D.w₂⁻¹) by group,
      P.V.w₂_conj_yi, hκw, hwu] at h1
    have h2 : P.V.D.w₁ * (c * P.V.yi) * P.V.D.w₁ = c * (P.V.yi * P.V.ki) := by
      have h3 : P.V.D.w₁ * (c * P.V.yi) * P.V.D.w₁⁻¹ = c * (P.V.yi * P.V.ki) := by
        rw [show P.V.D.w₁ * (c * P.V.yi) * P.V.D.w₁⁻¹ = (P.V.D.w₁ * c * P.V.D.w₁⁻¹) *
          (P.V.D.w₁ * P.V.yi * P.V.D.w₁⁻¹) by group, hcw₁, P.V.w₁_conj_yi]
      rwa [P.V.w₁_inv] at h3
    calc (P.V.D.w₂ * c * P.V.D.w₂⁻¹) * P.V.yi *
        (P.V.D.w₂ * P.V.D.w₁ * P.V.D.w₂⁻¹ * P.V.D.w₁⁻¹) * (c * (P.V.yi * P.V.ki)) =
        (P.V.D.w₂ * c * P.V.D.w₂⁻¹) * P.V.yi *
          (P.V.D.w₂ * P.V.D.w₁ * P.V.D.w₂⁻¹ * P.V.D.w₁⁻¹) * (P.V.D.w₁ * (c * P.V.yi) *
            P.V.D.w₁) := by rw [h2]
      _ = ((P.V.D.w₂ * c * P.V.D.w₂⁻¹) * P.V.yi *
          ((P.V.D.w₂ * P.V.D.w₁ * P.V.D.w₂⁻¹ * P.V.D.w₁⁻¹) * P.V.D.w₁) *
            (c * P.V.yi * P.V.D.w₁ * P.V.D.u)) * P.V.D.u⁻¹ := by group
      _ = 1 := by rw [h1, mul_inv_cancel]
  obtain ⟨φ, e0, e1, e2, e3⟩ := P.V.exists_evE
  have hy : ∀ c' : X, c' * P.V.yi = P.V.yi * c' → P.V.yi * (c' * P.V.yi * P.V.D.w₁ * P.V.D.u) *
      P.V.yi⁻¹ = P.V.yi * c' * P.V.yi * S.z * (P.V.yi * P.V.ki) * P.V.D.w₁ * P.V.D.u := by
    intro c' _
    have hzw := P.V.zk_w₁ P.V.z_mem_zk
    calc P.V.yi * (c' * P.V.yi * P.V.D.w₁ * P.V.D.u) * P.V.yi⁻¹ =
        P.V.yi * c' * P.V.yi * P.V.D.w₁ * (P.V.D.u * P.V.yi) := by rw [P.V.yi_inv]; group
      _ = P.V.yi * c' * P.V.yi * (P.V.D.w₁ * S.z) * (P.V.yi * P.V.D.u) := by
          rw [P.V.u_yi]; group
      _ = P.V.yi * c' * P.V.yi * S.z * (P.V.D.w₁ * P.V.yi * P.V.D.w₁⁻¹) * P.V.D.w₁ * P.V.D.u := by
          rw [← hzw]; group
      _ = _ := by rw [P.V.w₁_conj_yi]
  have hyw : P.V.yi * P.V.D.w₁ * P.V.yi⁻¹ = P.V.ki * P.V.D.w₁ := by
    rw [P.V.yi_w₁, P.V.yi_inv, ← mul_assoc, mul_assoc P.V.D.w₁ P.V.yi, ← P.V.ki_comm P.yi_mem_T,
      mul_assoc P.V.D.w₁, mul_assoc P.V.ki, P.V.yi_mul_yi, mul_one, P.V.zk_w₁ P.V.ki_mem_zk]
  rcases P.V.kappa_eq with hκ | hκ <;> rw [hκ] at hrel hκw <;>
    rcases P.w₂_conj_zk_eq (P.V.eq_of_mem_zk hc) with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ |
      ⟨h1, rfl⟩ <;> rw [h1] at hrel
  · exfalso
    have h2 : (1 : X) * P.V.yi * 1 * (1 * (P.V.yi * P.V.ki)) = P.V.ki := by elem_eq φ e0 e1 e2 e3
    rw [h2] at hrel
    exact P.V.hki.ne_one hrel
  ·
    refine ⟨P.V.yi * P.V.D.w₂, Or.inr rfl, ⟨P.V.ki, mem_zpowers _, ?_⟩, ?_⟩
    · rw [show P.V.yi * P.V.D.w₂ * P.V.D.u * (P.V.yi * P.V.D.w₂)⁻¹ =
        P.V.yi * (P.V.D.w₂ * P.V.D.u * P.V.D.w₂⁻¹) * P.V.yi⁻¹ by group, hwu,
        hy S.z (S.central_of_mem_B z_mem_B P.yi_mem_T)]
      have h2 : P.V.yi * S.z * P.V.yi * S.z * (P.V.yi * P.V.ki) = P.V.ki * P.V.yi := by
        elem_eq φ e0 e1 e2 e3
      rw [h2]
    · rw [show P.V.yi * P.V.D.w₂ * P.V.D.w₁ * (P.V.yi * P.V.D.w₂)⁻¹ =
        P.V.yi * (P.V.D.w₂ * P.V.D.w₁ * P.V.D.w₂⁻¹) * P.V.yi⁻¹ by group, hκw, one_mul, hyw]
  · exfalso
    have h2 : P.V.ki * P.V.yi * 1 * (P.V.ki * (P.V.yi * P.V.ki)) = P.V.ki := by
      elem_eq φ e0 e1 e2 e3
    rw [h2] at hrel
    exact P.V.hki.ne_one hrel
  ·
    refine ⟨P.V.yi * P.V.D.w₂, Or.inr rfl, ⟨1, one_mem _, ?_⟩, ?_⟩
    · rw [show P.V.yi * P.V.D.w₂ * P.V.D.u * (P.V.yi * P.V.D.w₂)⁻¹ =
        P.V.yi * (P.V.D.w₂ * P.V.D.u * P.V.D.w₂⁻¹) * P.V.yi⁻¹ by group, hwu,
        hy (S.z * P.V.ki) (S.central_of_mem_B (mul_mem z_mem_B P.V.hki.mem) P.yi_mem_T)]
      have h2 : P.V.yi * (S.z * P.V.ki) * P.V.yi * S.z * (P.V.yi * P.V.ki) = 1 * P.V.yi := by
        elem_eq φ e0 e1 e2 e3
      rw [h2]
    · rw [show P.V.yi * P.V.D.w₂ * P.V.D.w₁ * (P.V.yi * P.V.D.w₂)⁻¹ =
        P.V.yi * (P.V.D.w₂ * P.V.D.w₁ * P.V.D.w₂⁻¹) * P.V.yi⁻¹ by group, hκw, one_mul, hyw]
  · exact ⟨P.V.D.w₂, Or.inl rfl, ⟨1, one_mem _, hwu⟩, hκw⟩
  · exfalso
    have h2 : S.z * P.V.ki * P.V.yi * P.V.ki * (S.z * (P.V.yi * P.V.ki)) = P.V.ki := by
      elem_eq φ e0 e1 e2 e3
    rw [h2] at hrel
    exact P.V.hki.ne_one hrel
  · exact ⟨P.V.D.w₂, Or.inl rfl, ⟨P.V.ki, mem_zpowers _, hwu⟩, hκw⟩
  · exfalso
    have h2 : S.z * P.V.yi * P.V.ki * (S.z * P.V.ki * (P.V.yi * P.V.ki)) = P.V.ki := by
      elem_eq φ e0 e1 e2 e3
    rw [h2] at hrel
    exact P.V.hki.ne_one hrel

noncomputable def w₂N : X := Classical.choose P.exists_w₂'

theorem w₂N_eq : P.w₂N = P.V.D.w₂ ∨ P.w₂N = P.V.yi * P.V.D.w₂ :=
  (Classical.choose_spec P.exists_w₂').1

theorem exists_c : ∃ c ∈ zpowers P.V.ki,
    P.w₂N * P.V.D.u * P.w₂N⁻¹ = c * P.V.yi * P.V.D.w₁ * P.V.D.u :=
  (Classical.choose_spec P.exists_w₂').2.1

theorem w₂N_conj_w₁ : P.w₂N * P.V.D.w₁ * P.w₂N⁻¹ = P.V.ki * P.V.D.w₁ :=
  (Classical.choose_spec P.exists_w₂').2.2

noncomputable def cN : X := Classical.choose P.exists_c

theorem cN_mem : P.cN ∈ zpowers P.V.ki := (Classical.choose_spec P.exists_c).1

theorem w₂N_conj_u' : P.w₂N * P.V.D.u * P.w₂N⁻¹ = P.cN * P.V.yi * P.V.D.w₁ * P.V.D.u :=
  (Classical.choose_spec P.exists_c).2

@[expose] noncomputable def w₁N : X := P.V.D.w₁ * P.cN

theorem w₁N_eq : P.w₁N = P.V.D.w₁ * P.cN := rfl

theorem cN_eq : P.cN = 1 ∨ P.cN = P.V.ki := P.V.eq_of_mem_ki P.cN_mem

theorem cN_mem_zk : P.cN ∈ (zpowers S.z ⊔ zpowers P.V.ki : Subgroup X) :=
  mem_sup_right P.cN_mem

theorem cN_mem_B : P.cN ∈ S.B := zk_le_B P.V.hki P.cN_mem_zk

theorem cN_mem_E : P.cN ∈ S.E P.V.yi := B_le_E _ P.cN_mem_B

theorem cN_comm_w₁ : P.cN * P.V.D.w₁ = P.V.D.w₁ * P.cN := P.V.zk_w₁ P.cN_mem_zk

theorem w₁N_conj_E {e : X} (he : e ∈ S.E P.V.yi) :
    P.w₁N * e * P.w₁N⁻¹ = P.V.D.w₁ * e * P.V.D.w₁⁻¹ := by
  rw [P.w₁N_eq, show P.V.D.w₁ * P.cN * e * (P.V.D.w₁ * P.cN)⁻¹ =
    P.V.D.w₁ * (P.cN * e * P.cN⁻¹) * P.V.D.w₁⁻¹ by group,
    P.V.hyi.elemAbelianTwo_E.comm _ P.cN_mem_E _ he, mul_inv_cancel_right]

theorem w₁N_sq : P.w₁N * P.w₁N = 1 := by
  have hw := P.V.w₁_sq
  rw [pow_two] at hw
  rw [P.w₁N_eq, show P.V.D.w₁ * P.cN * (P.V.D.w₁ * P.cN) = P.cN * P.V.D.w₁ * P.V.D.w₁ * P.cN by
    rw [P.cN_comm_w₁]; group, mul_assoc P.cN, hw, mul_one, ← pow_two,
    S.sq_of_mem_B P.cN_mem_B]

theorem w₁N_conj_z : P.w₁N * S.z * P.w₁N⁻¹ = S.z := by
  rw [P.w₁N_conj_E (z_mem_E _), P.V.w₁_conj_z]

theorem w₁N_conj_yi : P.w₁N * P.V.yi * P.w₁N⁻¹ = P.V.yi * P.V.ki := by
  rw [P.w₁N_conj_E (mem_E_self _), P.V.w₁_conj_yi]

theorem w₁N_conj_t : P.w₁N * S.t * P.w₁N⁻¹ = S.z * (S.t * P.V.ki) := by
  rw [P.w₁N_conj_E (t_mem_E _), P.V.w₁_conj_t, ← S.central_of_mem_B z_mem_B S.data.t_mem_T,
    mul_assoc]

theorem w₁N_conj_ki : P.w₁N * P.V.ki * P.w₁N⁻¹ = P.V.ki := by
  rw [P.w₁N_conj_E (B_le_E _ P.V.hki.mem), P.V.w₁_conj_ki]

theorem w₁N_conj_vN : P.w₁N * P.V.vN * P.w₁N⁻¹ = P.V.vN * (S.z * P.V.ki) := by
  have hc : P.cN * P.V.vN * P.cN⁻¹ = P.V.vN := by
    have h := P.V.vN_conj_of_zk P.cN_mem_zk
    have h' : P.V.vN * P.cN = P.cN * P.V.vN := by
      calc P.V.vN * P.cN = (P.V.vN * P.cN * P.V.vN⁻¹) * P.V.vN := by group
        _ = P.cN * P.V.vN := by rw [h]
    rw [← h', mul_inv_cancel_right]
  rw [P.w₁N_eq, show P.V.D.w₁ * P.cN * P.V.vN * (P.V.D.w₁ * P.cN)⁻¹ =
    P.V.D.w₁ * (P.cN * P.V.vN * P.cN⁻¹) * P.V.D.w₁⁻¹ by group, hc, P.w₁_conj_vN]

theorem u_conj_w₁N : P.V.D.u * P.w₁N * P.V.D.u⁻¹ = P.w₁N * (S.z * P.V.ki) := by
  rw [P.w₁N_eq, show P.V.D.u * (P.V.D.w₁ * P.cN) * P.V.D.u⁻¹ = (P.V.D.u * P.V.D.w₁ * P.V.D.u⁻¹) *
    (P.V.D.u * P.cN * P.V.D.u⁻¹) by group, P.u_conj_w₁, P.V.u_conj_B P.cN_mem_B, mul_assoc,
    P.zk_comm (S.B_le_T P.cN_mem_B), ← mul_assoc]

theorem w₂N_conj_E {e : X} (he' : P.V.D.w₂ * e * P.V.D.w₂⁻¹ ∈ S.E P.V.yi) :
    P.w₂N * e * P.w₂N⁻¹ = P.V.D.w₂ * e * P.V.D.w₂⁻¹ := by
  rcases P.w₂N_eq with h | h <;> rw [h]
  rw [show P.V.yi * P.V.D.w₂ * e * (P.V.yi * P.V.D.w₂)⁻¹ =
    P.V.yi * (P.V.D.w₂ * e * P.V.D.w₂⁻¹) * P.V.yi⁻¹ by group,
    P.V.hyi.elemAbelianTwo_E.comm _ (mem_E_self _) _ he', mul_inv_cancel_right]

theorem w₂N_sq : P.w₂N * P.w₂N = 1 := by
  have hw := P.V.w₂_sq
  rw [pow_two] at hw
  rcases P.w₂N_eq with h | h <;> rw [h]
  · exact hw
  · rw [show P.V.yi * P.V.D.w₂ * (P.V.yi * P.V.D.w₂) =
      P.V.yi * (P.V.D.w₂ * P.V.yi * P.V.D.w₂⁻¹) * (P.V.D.w₂ * P.V.D.w₂) by group, hw, mul_one,
      P.V.w₂_conj_yi, P.V.yi_mul_yi]

theorem w₂N_conj_z : P.w₂N * S.z * P.w₂N⁻¹ = S.z * P.V.ki := by
  have h : P.V.D.w₂ * S.z * P.V.D.w₂⁻¹ ∈ S.E P.V.yi := by
    rw [P.V.w₂_conj_z]; exact mul_mem (z_mem_E _) (B_le_E _ P.V.hki.mem)
  rw [P.w₂N_conj_E h, P.V.w₂_conj_z]

theorem w₂N_conj_yi : P.w₂N * P.V.yi * P.w₂N⁻¹ = P.V.yi := by
  have h : P.V.D.w₂ * P.V.yi * P.V.D.w₂⁻¹ ∈ S.E P.V.yi := by
    rw [P.V.w₂_conj_yi]; exact mem_E_self _
  rw [P.w₂N_conj_E h, P.V.w₂_conj_yi]

theorem w₂N_conj_t : P.w₂N * S.t * P.w₂N⁻¹ = P.V.yi * (S.t * P.V.ki) := by
  have hE := P.V.hyi.elemAbelianTwo_E
  have h : P.V.D.w₂ * S.t * P.V.D.w₂⁻¹ ∈ S.E P.V.yi := by
    rw [P.V.w₂_conj_t]
    exact mul_mem (mul_mem (t_mem_E _) (mem_E_self _)) (B_le_E _ P.V.hki.mem)
  rw [P.w₂N_conj_E h, P.V.w₂_conj_t, hE.comm _ (t_mem_E _) _ (mem_E_self _), mul_assoc]

theorem w₂N_conj_ki : P.w₂N * P.V.ki * P.w₂N⁻¹ = P.V.ki := by
  have h : P.V.D.w₂ * P.V.ki * P.V.D.w₂⁻¹ ∈ S.E P.V.yi := by
    rw [P.V.w₂_conj_ki]; exact B_le_E _ P.V.hki.mem
  rw [P.w₂N_conj_E h, P.V.w₂_conj_ki]

theorem w₂N_conj_vN : P.w₂N * P.V.vN * P.w₂N⁻¹ = P.V.vN * (P.V.yi * P.V.ki) := by
  rcases P.w₂N_eq with h | h <;> rw [h]
  · exact P.w₂_conj_vN
  · have hyv : P.V.yi * P.V.vN = P.V.vN * P.V.yi := by
      calc P.V.yi * P.V.vN = (P.V.vN * P.V.yi * P.V.vN⁻¹) * P.V.vN := by rw [P.V.vN_conj_yi]
        _ = P.V.vN * P.V.yi := by group
    have hyk : P.V.yi * (P.V.yi * P.V.ki) * P.V.yi⁻¹ = P.V.yi * P.V.ki := by
      rw [P.V.hyi.elemAbelianTwo_E.comm _ (mem_E_self _) _ (mul_mem (mem_E_self _)
        (B_le_E _ P.V.hki.mem)), mul_inv_cancel_right]
    calc P.V.yi * P.V.D.w₂ * P.V.vN * (P.V.yi * P.V.D.w₂)⁻¹ =
        P.V.yi * (P.V.D.w₂ * P.V.vN * P.V.D.w₂⁻¹) * P.V.yi⁻¹ := by group
      _ = (P.V.yi * P.V.vN) * (P.V.yi * P.V.ki) * P.V.yi⁻¹ := by rw [P.w₂_conj_vN]; group
      _ = P.V.vN * (P.V.yi * (P.V.yi * P.V.ki) * P.V.yi⁻¹) := by rw [hyv]; group
      _ = P.V.vN * (P.V.yi * P.V.ki) := by rw [hyk]

theorem w₂N_conj_w₁N : P.w₂N * P.w₁N * P.w₂N⁻¹ = P.w₁N * P.V.ki := by
  have hc : P.w₂N * P.cN * P.w₂N⁻¹ = P.cN := by
    rcases P.cN_eq with h | h <;> rw [h]
    · group
    · exact P.w₂N_conj_ki
  rw [P.w₁N_eq]
  calc P.w₂N * (P.V.D.w₁ * P.cN) * P.w₂N⁻¹ = (P.w₂N * P.V.D.w₁ * P.w₂N⁻¹) *
      (P.w₂N * P.cN * P.w₂N⁻¹) := by group
    _ = (P.V.ki * P.V.D.w₁) * P.cN := by rw [P.w₂N_conj_w₁, hc]
    _ = P.V.D.w₁ * (P.V.ki * P.cN) := by rw [P.V.zk_w₁ P.V.ki_mem_zk]; group
    _ = P.V.D.w₁ * P.cN * P.V.ki := by rw [P.V.ki_comm (S.B_le_T P.cN_mem_B)]; group

theorem w₂N_conj_u : P.w₂N * P.V.D.u * P.w₂N⁻¹ = P.V.D.u * (P.w₁N * P.V.yi) := by
  rw [P.w₂N_conj_u', P.w₁N_eq]
  obtain ⟨φ, e0, e1, e2, e3⟩ := P.V.exists_evE
  have hB : P.cN * P.V.D.u = P.V.D.u * P.cN := P.V.B_u P.cN_mem_B
  calc P.cN * P.V.yi * P.V.D.w₁ * P.V.D.u = P.cN * (P.V.yi * P.V.D.w₁) * P.V.D.u := by group
    _ = P.cN * (P.V.D.w₁ * (P.V.yi * P.V.ki)) * P.V.D.u := by rw [P.V.yi_w₁]
    _ = (P.cN * P.V.D.w₁) * (P.V.yi * P.V.ki) * P.V.D.u := by group
    _ = P.V.D.w₁ * (P.cN * (P.V.yi * P.V.ki)) * P.V.D.u := by rw [P.cN_comm_w₁]; group
    _ = P.V.D.w₁ * (S.z * P.V.ki * P.cN * (S.z * P.V.yi)) * P.V.D.u := by
        congr 2
        rcases P.cN_eq with h | h <;> rw [h] <;> elem_eq φ e0 e1 e2 e3
    _ = P.V.D.w₁ * (S.z * P.V.ki) * P.cN * (S.z * P.V.yi * P.V.D.u) := by group
    _ = P.V.D.w₁ * (S.z * P.V.ki) * (P.cN * P.V.D.u) * P.V.yi := by rw [← P.V.u_yi]; group
    _ = (P.V.D.w₁ * (S.z * P.V.ki) * P.V.D.u) * P.cN * P.V.yi := by rw [hB]; group
    _ = P.V.D.u * (P.V.D.w₁ * P.cN * P.V.yi) := by rw [← P.u_w₁]; group

end CPair

end Sec8

end CFSG.ComponentClassification.HSFLit

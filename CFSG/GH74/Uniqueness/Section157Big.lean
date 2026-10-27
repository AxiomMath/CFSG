module

public import CFSG.GH74.Uniqueness.Section157R0
public import CFSG.GH74.Uniqueness.Section15Aux2

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X]

namespace Sec157

omit [Finite X] in
theorem conj_mem_sup {A B : Subgroup X} {d : X} (hA : ∀ x ∈ A, d * x * d⁻¹ ∈ A)
    (hB : ∀ x ∈ B, d * x * d⁻¹ ∈ B) {x : X} (hx : x ∈ A ⊔ B) : d * x * d⁻¹ ∈ A ⊔ B := by
  have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj d).toMonoidHom := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mem_sup_left (hA a ha)
    · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mem_sup_right (hB b hb)
  have := hle hx
  rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

end Sec157

namespace Conf156

variable {M : Subgroup X} {n : ℕ} {L D K J Mo V R₁ : Subgroup X} {u : X}

omit [Finite X] in
theorem not_sq_of_mem_V (C : Conf156 M n L D K J Mo V R₁ u) {w : X} (hw : w ∈ V) :
    w * w ≠ u := by
  intro hwu
  have hc : w * u = u * w := by
    rw [← hwu]
    group
  rcases C.NV w hw (C.cent_le_N hc) with h | h
  · apply C.u_ne
    rw [← hwu]
    exact C.F.Mo_sq w h
  · apply C.u_ne
    have h1 : w * u * (w * u) = u := by
      calc w * u * (w * u) = w * (u * w) * u := by group
        _ = w * (w * u) * u := by rw [hc]
        _ = (w * w) * (u * u) := by group
        _ = u := by rw [C.u_sq, hwu, mul_one]
    rw [← h1]
    exact C.F.Mo_sq _ h

omit [Finite X] in
theorem not_sq_conj (C : Conf156 M n L D K J Mo V R₁ u) {v g : X} (hv : v ∈ V) (hg : g ∈ M) :
    v * v ≠ g * u * g⁻¹ := by
  intro h
  have hw : g⁻¹ * v * g ∈ V := by
    have := C.F.V_normal g⁻¹ (M.inv_mem hg) v hv
    rwa [inv_inv] at this
  refine C.not_sq_of_mem_V hw ?_
  calc g⁻¹ * v * g * (g⁻¹ * v * g) = g⁻¹ * (v * v) * g := by group
    _ = u := by rw [h]; group

theorem false_of_ne (C : Conf156 M n L D K J Mo V R₁ u) {R₀ : Subgroup X}
    (hR : R0Data M K Mo R₁ R₀ n u) (hne : R₁ ≠ V) : False := by
  have F := C.F
  obtain ⟨hcardV, hMVD, hfreeV⟩ := C.big hne
  obtain ⟨k₁, hk₁, hk₁1⟩ := C.exists_ne_one_K
  have hR₀V : R₀ ≤ V := hR.le_R₁.trans C.R₁_le
  have huV : u ∈ V := C.R₁_le C.u_mem_R₁
  have hindex : (R₁.subgroupOf V).index = 2 ^ n := by
    have h := Sec157.card_mul_index_subgroupOf C.R₁_le
    rw [C.card_R₁, hcardV] at h
    have e : 2 ^ (3 * n + 1) = 2 ^ (2 * n + 1) * 2 ^ n := by
      rw [← pow_add]
      congr 1
      omega
    rw [e] at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  have hAP : ∀ a ∈ K, ∀ x ∈ V, a * x * a⁻¹ ∈ V := fun a ha x hx =>
    F.V_normal a (F.K_le_M ha) x hx
  have hAN : ∀ a ∈ K, ∀ x ∈ R₁, a * x * a⁻¹ ∈ R₁ := fun a ha x hx =>
    C.R₁_normal a (F.K_le_M ha) x hx
  have htrans := trans_of_free_of_card C.R₁_le hAP hAN hfreeV (by rw [hindex, F.card_K])
  have hsqR₁ : ∀ v ∈ V, v * v ∈ R₁ :=
    sq_mem_of_transitive F.V_pgroup C.R₁_le
      (fun g hg x hx => C.R₁_normal g (F.V_le hg) x hx) hAP hAN htrans
  have hsqR₀ : ∀ v ∈ V, v * v ∈ R₀ := by
    intro v hv
    by_contra hnot
    have h1 : v * v ∈ R₁ := hsqR₁ v hv
    have h2 : v * v * (v * v) = 1 := hR.invol _ h1 hnot
    have h3 : v * v ∉ Mo := fun h => hnot (hR.Mo_le h)
    obtain ⟨g, hg, hgu⟩ := C.inv_R₁ _ h1 h3 h2
    exact C.not_sq_conj hv hg hgu.symm
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b * a⁻¹ * b⁻¹ ∈ R₀ :=
    Sec157.comm_mem_of_sq_mem (fun g hg x hx => hR.normal g (F.V_le hg) x hx) hsqR₀
  obtain ⟨M₁, hM₁R, hM₁V, hM₁u, hM₁cases, -, hM₁K⟩ := Sec157.exists_invariant_index_two (M := M)
    (N := R₀) (P := V) (A := K) (u := u) hR.normal F.V_normal hR₀V F.V_le F.K_le_M F.odd_card_K
    hcomm huV hR.u_not_mem (by rw [C.u_sq]; exact R₀.one_mem)
    (fun a ha => C.D_comm_u (F.K_le_D ha))
    (fun x hx hfix => by
      have h1 := hfix k₁ hk₁
      exact hR.cases x (hfreeV k₁ hk₁ hk₁1 x hx (hR.le_R₁ h1)))
  have hM₁n : ∀ g ∈ M, ∀ x ∈ M₁, g * x * g⁻¹ ∈ M₁ := by
    intro g hg x hx
    obtain ⟨v, hv, d, hd, rfl⟩ := hMVD g hg
    have hxd : d * x * d⁻¹ ∈ M₁ :=
      hM₁K d (F.D_le hd) (fun a ha => F.D_conj_K hd ha) x hx
    have hxV : d * x * d⁻¹ ∈ V := hM₁V hxd
    have h1 : v * (d * x * d⁻¹) * v⁻¹ = (v * (d * x * d⁻¹) * v⁻¹ * (d * x * d⁻¹)⁻¹) *
        (d * x * d⁻¹) := by group
    have e : v * d * x * (v * d)⁻¹ = v * (d * x * d⁻¹) * v⁻¹ := by group
    rw [e, h1]
    exact M₁.mul_mem (hM₁R (hcomm v hv _ hxV)) hxd
  have hinf : M₁ ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases C.VD x (mem_inf.mp hx).2 (hM₁V (mem_inf.mp hx).1) with h | h
    · exact mem_bot.mpr h
    · exact absurd (h ▸ (mem_inf.mp hx).1) hM₁u
  have huD : u ∈ D := F.J_le_D C.u_mem_J
  have huM : u ∈ M := F.D_le huD
  have hsup : ∀ g ∈ M, ∃ a ∈ M₁, ∃ d ∈ D, g = a * d := by
    intro g hg
    obtain ⟨v, hv, d, hd, rfl⟩ := hMVD g hg
    rcases hM₁cases v hv with h | h
    · exact ⟨v, h, d, hd, rfl⟩
    · refine ⟨u * (u * v) * u⁻¹, hM₁n u huM _ h, u * d, D.mul_mem huD hd, ?_⟩
      have e : u * (u * v) * u⁻¹ * (u * d) = (u * u) * v * d := by group
      rw [e, C.u_sq, one_mul]
  have hKD : K ≤ D := F.K_le_D
  have hKJ : K ⊓ J = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact mem_bot.mpr (F.eq_one_of_mem_K_J (mem_inf.mp hx).1 (mem_inf.mp hx).2)
  have hcardKJ : Nat.card ↥(K ⊔ J) = 2 * Nat.card K := by
    rw [card_sup_of_normal (fun d hd x hx => F.D_conj_K (F.J_le_D hd) hx) hKJ, C.card_J, mul_comm]
  have hDcomm : ∀ a ∈ D, ∀ b ∈ D, a * b * a⁻¹ * b⁻¹ ∈ K :=
    comm_mem_of_cyclic_quotient (sup_le hKD F.J_le_D) le_sup_left
      (fun d hd x hx => Sec157.conj_mem_sup (fun y hy => F.D_conj_K hd hy)
        (fun y hy => F.D_conj_J hd hy) hx)
      (fun d hd x hx => F.D_conj_K hd hx) hcardKJ F.out_cyclic
  have huK : u ∉ K := fun h => C.u_ne (F.eq_one_of_mem_K_J h C.u_mem_J)
  have hO2D := not_mem_closure_odd_of_comm hKD hDcomm huD C.u_sq huK
  have hO2M := not_mem_closure_odd_of_complement F.D_le (hM₁V.trans F.V_le) hM₁n hsup hinf huD
    hO2D
  exact hO2M (by rw [F.oddGen]; exact huM)

end Conf156

end CFSG.GH74.Uniqueness

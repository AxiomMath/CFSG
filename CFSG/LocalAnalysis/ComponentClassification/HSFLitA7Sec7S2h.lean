module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7S2g

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec7

variable {X : Type} [Group X] [Finite X]

namespace Setup

variable {S : A7Base X} (C : Setup S)

theorem conj_E0_of_gens {s : X} (hz : s * S.z * s⁻¹ = S.z) (hy : s * C.F.yF * s⁻¹ = C.F.yF)
    (hk : s * C.F.kF * s⁻¹ = C.F.kF) : ∀ e ∈ C.E₀, s * e * s⁻¹ = e := by
  have hc : ∀ {a : X}, s * a * s⁻¹ = a → a * s = s * a := fun {a} h => by
    calc a * s = (s * a * s⁻¹) * s := by rw [h]
      _ = s * a := by group
  have hle : C.E₀ ≤ centralizer ({s} : Set X) := by
    show closure {S.z, C.F.yF, C.F.kF} ≤ _
    rw [closure_le]
    intro e he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    rcases he with rfl | rfl | rfl
    · exact hc hz
    · exact hc hy
    · exact hc hk
  intro e he
  rw [← mem_centralizer_singleton_iff.mp (hle he), mul_inv_cancel_right]

abbrev Q₂₀ : Subgroup X := C.S₂ ⊓ centralizer (C.Fv : Set X)

theorem mem_Q₂₀_of {s : X} (hs : s ∈ C.S₂) (hy : s * C.F.yF * s⁻¹ = C.F.yF)
    (hv : s * C.v' * s⁻¹ = C.v') : s ∈ C.Q₂₀ := by
  have hF := C.conj_Fv_of (by
    calc s * C.v' = s * C.v' * s⁻¹ * s := by group
      _ = C.v' * s := by rw [hv]) (C.conj_E0_of_gens (C.S₂_z hs) hy (C.S₂_k hs))
  refine ⟨hs, mem_centralizer_iff.mpr fun f hf => ?_⟩
  calc f * s = (s * f * s⁻¹) * s := by rw [hF f hf]
    _ = s * f := by group

theorem Q₂₀_F {s : X} (hs : s ∈ C.Q₂₀) {f : X} (hf : f ∈ C.Fv) : s * f * s⁻¹ = f := by
  rw [← mem_centralizer_iff.mp hs.2 f hf, mul_inv_cancel_right]

theorem conj_Q₂₀ {s : X} (hs : s ∈ C.S₂) {x : X} (hx : x ∈ C.Q₂₀) : s * x * s⁻¹ ∈ C.Q₂₀ := by
  refine Subgroup.mem_inf.mpr ⟨C.S₂.mul_mem (C.S₂.mul_mem hs hx.1) (C.S₂.inv_mem hs),
    mem_centralizer_iff.mpr fun f hf => ?_⟩
  have hf' : s⁻¹ * f * s⁻¹⁻¹ ∈ C.Fv := by
    rw [← act_Fv C (inv_mem (C.S₂_le hs))]; exact ⟨f, hf, rfl⟩
  rw [inv_inv] at hf'
  have h1 := C.Q₂₀_F hx hf'
  calc f * (s * x * s⁻¹) = s * ((s⁻¹ * f * s) * x) * s⁻¹ := by group
    _ = s * (x * (s⁻¹ * f * s)) * s⁻¹ := by
        rw [show (s⁻¹ * f * s) * x = x * (s⁻¹ * f * s) by
          calc (s⁻¹ * f * s) * x = (x * (s⁻¹ * f * s) * x⁻¹) * x := by rw [h1]
            _ = x * (s⁻¹ * f * s) := by group]
    _ = s * x * s⁻¹ * f := by group

theorem S₂_le_normalizer_Q₂₀ : C.S₂ ≤ normalizer (C.Q₂₀ : Set X) := fun s hs =>
  mem_normalizer_of_map_le (by rintro _ ⟨x, hx, rfl⟩; exact C.conj_Q₂₀ hs hx)

theorem t_mem_S₂ : S.t ∈ C.S₂ := C.Q₁_le_S₂ C.t_mem_Q₁

theorem t_not_mem_Q₂₀ : S.t ∉ C.Q₂₀ := fun h => C.ne_one_k (by
  have h1 := C.Q₂₀_F h (mem_sup_right (mem_zpowers C.v'))
  rw [C.t_v'] at h1
  simpa using h1)

theorem t_y : S.t * C.F.yF * S.t⁻¹ = C.F.yF := conj_eq_of_comm (C.t_comm_E0 C.y_mem_E0)

theorem card_S₂_eq : Nat.card C.S₂ = 4 * Nat.card C.Q₂₀ := by
  have hQt : C.Q₂₀ ⊔ zpowers S.t ≤ C.S₂ := sup_le inf_le_left (zpowers_le.mpr C.t_mem_S₂)
  have ht2 : S.t ^ 2 ∈ C.Q₂₀ := by rw [S.t_sq]; exact one_mem _
  have hcard1 := card_sup_zpowers_eq (C.S₂_le_normalizer_Q₂₀ C.t_mem_S₂) ht2 C.t_not_mem_Q₂₀
  have hfixy : ∀ x ∈ C.Q₂₀ ⊔ zpowers S.t, x * C.F.yF * x⁻¹ = C.F.yF := by
    intro x hx
    rcases mem_or_of_mem_sup_zpowers (C.S₂_le_normalizer_Q₂₀ C.t_mem_S₂) ht2 hx with h | h
    · exact C.Q₂₀_F h (mem_sup_left C.y_mem_E0)
    · rw [show x = x * S.t⁻¹ * S.t by group, show x * S.t⁻¹ * S.t * C.F.yF * (x * S.t⁻¹ * S.t)⁻¹ =
        (x * S.t⁻¹) * (S.t * C.F.yF * S.t⁻¹) * (x * S.t⁻¹)⁻¹ by group, C.t_y,
        C.Q₂₀_F h (mem_sup_left C.y_mem_E0)]
  have hu2 : C.D₁.u ^ 2 ∈ C.Q₂₀ ⊔ zpowers S.t := by
    rw [pow_two, C.u_mul_u]; exact one_mem _
  have huN : C.D₁.u ∈ normalizer ((C.Q₂₀ ⊔ zpowers S.t : Subgroup X) : Set X) := by
    refine mem_normalizer_of_map_le ?_
    rw [map_le_iff_le_comap]
    refine sup_le (fun x hx => mem_sup_left (C.conj_Q₂₀ C.u_mem_S₂ hx)) (zpowers_le.mpr ?_)
    rw [mem_comap]
    show C.D₁.u * S.t * C.D₁.u⁻¹ ∈ C.Q₂₀ ⊔ zpowers S.t
    rw [conj_eq_of_comm (C.u_comm_B t_mem_B)]
    exact mem_sup_right (mem_zpowers _)
  have huQ : C.D₁.u ∉ C.Q₂₀ ⊔ zpowers S.t := fun h => by
    have h1 := hfixy _ h
    rw [C.u_y] at h1
    exact S.z_ne_one (by simpa using h1)
  have hcard2 := card_sup_zpowers_eq huN hu2 huQ
  have hle : C.S₂ ≤ C.Q₂₀ ⊔ zpowers S.t ⊔ zpowers C.D₁.u := by
    intro s hs
    obtain ⟨s', hs', hy', hsu⟩ : ∃ s' ∈ C.S₂, s' * C.F.yF * s'⁻¹ = C.F.yF ∧
        (s = s' ∨ s = s' * C.D₁.u) := by
      rcases C.S₂_y hs with h | h
      · exact ⟨s, hs, h, Or.inl rfl⟩
      · refine ⟨s * C.D₁.u⁻¹, mul_mem hs (inv_mem C.u_mem_S₂), ?_, Or.inr (by group)⟩
        have e : C.D₁.u⁻¹ * C.F.yF * C.D₁.u⁻¹⁻¹ = S.z * C.F.yF := by rw [C.u_inv]; exact C.u_y
        rw [show s * C.D₁.u⁻¹ * C.F.yF * (s * C.D₁.u⁻¹)⁻¹ =
          s * (C.D₁.u⁻¹ * C.F.yF * C.D₁.u⁻¹⁻¹) * s⁻¹ by group, e, conj_mul_eq,
          C.S₂_z hs, h, ← mul_assoc, zz S, one_mul]
    obtain ⟨s'', hs'', hsv⟩ : ∃ s'' ∈ C.Q₂₀, s' = s'' ∨ s' = s'' * S.t := by
      rcases C.S₂_v' hs' with h | h
      · exact ⟨s', C.mem_Q₂₀_of hs' hy' h, Or.inl rfl⟩
      · refine ⟨s' * S.t⁻¹, C.mem_Q₂₀_of (mul_mem hs' (inv_mem C.t_mem_S₂)) ?_ ?_,
          Or.inr (by group)⟩
        · rw [show s' * S.t⁻¹ * C.F.yF * (s' * S.t⁻¹)⁻¹ = s' * (S.t⁻¹ * C.F.yF * S.t) * s'⁻¹ by
            group, t_inv S, show S.t * C.F.yF * S.t = S.t * C.F.yF * S.t⁻¹ by rw [t_inv S],
            C.t_y, hy']
        · rw [show s' * S.t⁻¹ * C.v' * (s' * S.t⁻¹)⁻¹ = s' * (S.t⁻¹ * C.v' * S.t) * s'⁻¹ by group,
            t_inv S, show S.t * C.v' * S.t = S.t * C.v' * S.t⁻¹ by rw [t_inv S], C.t_v',
            conj_mul_eq, C.S₂_k hs', h, ← mul_assoc, C.kk, one_mul]
    have hs''Q : s'' ∈ C.Q₂₀ ⊔ zpowers S.t ⊔ zpowers C.D₁.u := mem_sup_left (mem_sup_left hs'')
    have ht : S.t ∈ C.Q₂₀ ⊔ zpowers S.t ⊔ zpowers C.D₁.u :=
      mem_sup_left (mem_sup_right (mem_zpowers _))
    have hu : C.D₁.u ∈ C.Q₂₀ ⊔ zpowers S.t ⊔ zpowers C.D₁.u := mem_sup_right (mem_zpowers _)
    rcases hsu with rfl | rfl <;> rcases hsv with rfl | rfl
    · exact hs''Q
    · exact mul_mem hs''Q ht
    · exact mul_mem hs''Q hu
    · exact mul_mem (mul_mem hs''Q ht) hu
  have heq : C.S₂ = C.Q₂₀ ⊔ zpowers S.t ⊔ zpowers C.D₁.u :=
    le_antisymm hle (sup_le hQt (zpowers_le.mpr C.u_mem_S₂))
  rw [heq, hcard2, hcard1]
  ring

theorem card_S₁ : Nat.card C.D₁.S₁ = 256 := by
  rw [C.S₁_eq_sup, card_sup_zpowers_eq C.u_normalizes
    (by rw [pow_two, C.u_mul_u]; exact one_mem _) (u_not_mem_Q₁ C.isRefl_y C.D₁), C.card_Q₁]

theorem card_Q₂₀ : Nat.card C.Q₂₀ = 256 := by
  have h := C.card_S₂_eq
  rw [C.card_S₂, C.card_S₁] at h
  omega

theorem Fv_sq {f : X} (hf : f ∈ C.Fv) : f ^ 2 = 1 := by
  have hel := C.isRefl_y.elemAbelianTwo_E0 C.isK_k
  rcases mem_or_of_mem_sup_zpowers (C.normalizes_E0_of_mem_Q₁ C.v'_mem_Q₁) C.v'_sq_mem_E0 hf with
    h | h
  · exact hel.sq_eq_one f h
  · obtain ⟨e, he, rfl⟩ : ∃ e ∈ C.E₀, f = e * C.v' := ⟨_, h, by group⟩
    rw [pow_two, show e * C.v' * (e * C.v') = e * (C.v' * e) * C.v' by group,
      C.comm_v'_E0 he, show e * (e * C.v') * C.v' = (e * e) * (C.v' * C.v') by group,
      ← pow_two e, hel.sq_eq_one e he, C.v'v', one_mul]

theorem card_Fv : Nat.card C.Fv = 16 := by
  rw [card_sup_zpowers_eq (C.normalizes_E0_of_mem_Q₁ C.v'_mem_Q₁) C.v'_sq_mem_E0
    C.v'_not_mem_E0, C.isRefl_y.card_E0 C.isK_k]

theorem isPGroup_Q₂₀ : IsPGroup 2 C.Q₂₀ := C.isPGroup_S₂.to_le inf_le_left

theorem sq_of_conjTo {j : X} (hj : ConjTo S.t j) : j ^ 2 = 1 := by
  obtain ⟨c, rfl⟩ := hj
  exact conj_sq_one S.t_sq

theorem not_conjTo_of_mem_Q₂₀ {j : X} (hj : j ∈ C.Q₂₀) : ¬ ConjTo S.t j := by
  intro hc
  by_cases hjF : j ∈ C.Fv
  · refine not_conjTo_of_card C.isPGroup_Q₂₀ (fun x hx => ?_) (by rw [C.card_Q₂₀]; norm_num) hc
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.mp hx.2 j hjF).symm
  · have hj2 := sq_of_conjTo hc
    have hjN : j ∈ normalizer (C.Fv : Set X) := mem_normalizer_of_map_le (by
      rintro _ ⟨f, hf, rfl⟩
      show j * f * j⁻¹ ∈ C.Fv
      rw [C.Q₂₀_F hj hf]; exact hf)
    have hj2F : j ^ 2 ∈ C.Fv := by rw [hj2]; exact one_mem _
    set A := C.Fv ⊔ zpowers j with hA
    have hcomm : ∀ f ∈ C.Fv, f * j = j * f := fun f hf => mem_centralizer_iff.mp hj.2 f hf
    have hcases : ∀ a ∈ A, a ∈ C.Fv ∨ a * j⁻¹ ∈ C.Fv := fun a ha =>
      mem_or_of_mem_sup_zpowers hjN hj2F ha
    have hel : ElemAbelianTwo A := by
      refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
      · rcases hcases a ha with h1 | h1 <;> rcases hcases b hb with h2 | h2
        · exact C.Fv_comm h1 h2
        · obtain ⟨g, hg, rfl⟩ : ∃ g ∈ C.Fv, b = g * j := ⟨_, h2, by group⟩
          calc a * (g * j) = (a * g) * j := by group
            _ = (g * a) * j := by rw [C.Fv_comm h1 hg]
            _ = g * (a * j) := by group
            _ = g * (j * a) := by rw [hcomm a h1]
            _ = g * j * a := by group
        · obtain ⟨f, hf, rfl⟩ : ∃ f ∈ C.Fv, a = f * j := ⟨_, h1, by group⟩
          calc f * j * b = f * (j * b) := by group
            _ = f * (b * j) := by rw [hcomm b h2]
            _ = (f * b) * j := by group
            _ = (b * f) * j := by rw [C.Fv_comm hf h2]
            _ = b * (f * j) := by group
        · obtain ⟨f, hf, rfl⟩ : ∃ f ∈ C.Fv, a = f * j := ⟨_, h1, by group⟩
          obtain ⟨g, hg, rfl⟩ : ∃ g ∈ C.Fv, b = g * j := ⟨_, h2, by group⟩
          calc f * j * (g * j) = f * (j * g) * j := by group
            _ = f * (g * j) * j := by rw [hcomm g hg]
            _ = (f * g) * j * j := by group
            _ = (g * f) * j * j := by rw [C.Fv_comm hf hg]
            _ = g * (f * j) * j := by group
            _ = g * (j * f) * j := by rw [hcomm f hf]
            _ = g * j * (f * j) := by group
      · rcases hcases a ha with h1 | h1
        · exact C.Fv_sq h1
        · obtain ⟨f, hf, rfl⟩ : ∃ f ∈ C.Fv, a = f * j := ⟨_, h1, by group⟩
          calc (f * j) ^ 2 = f * (j * f) * j := by rw [pow_two]; group
            _ = f * (f * j) * j := by rw [hcomm f hf]
            _ = f ^ 2 * j ^ 2 := by rw [pow_two, pow_two]; group
            _ = 1 := by rw [C.Fv_sq hf, hj2, one_mul]
    have hAj : A ≤ centralizer ({j} : Set X) := by
      intro a ha
      rw [mem_centralizer_singleton_iff]
      exact hel.comm a ha j (mem_sup_right (mem_zpowers j))
    have hcardA : Nat.card A = 32 := by
      rw [hA, card_sup_zpowers_eq hjN hj2F hjF, C.card_Fv]
    exact not_conjTo_of_elem hel hAj (by rw [hcardA]) hc

theorem inv_cases_q {q a : X} (hqN : q ∈ normalizer (C.D₁.Q₁ : Set X)) (hqF : ∀ f ∈ C.Fv,
    q * f * q⁻¹ = f) (hq2 : q ^ 2 ∈ C.E₀) {g : X} (hg : g ∈ C.D₁.Q₁)
    (hc : C.Cong (q * g * q⁻¹) (C.v' * g)) (ha : a ∈ C.D₁.Q₁) (hj : (q * a) ^ 2 = 1) :
    a * C.v' = C.v' * a := by
  have hqE : ∀ e ∈ C.E₀, q * e * q⁻¹ = e := fun e he => hqF e (mem_sup_left he)
  have hcong : C.Cong (q * a * q⁻¹) a := by
    refine C.cong_def.mpr ?_
    have e1 : q * a * q⁻¹ * a⁻¹ = (q ^ 2)⁻¹ * (a ^ 2)⁻¹ := by
      have h1 : q * a * q⁻¹ = a⁻¹ * (q ^ 2)⁻¹ := by
        have : q * a * q * a = 1 := by rw [← hj, pow_two]; group
        calc q * a * q⁻¹ = (q * a * q * a) * a⁻¹ * (q ^ 2)⁻¹ := by rw [pow_two]; group
          _ = a⁻¹ * (q ^ 2)⁻¹ := by rw [this, one_mul]
      rw [h1]
      calc a⁻¹ * (q ^ 2)⁻¹ * a⁻¹ = (q ^ 2)⁻¹ * a⁻¹ * a⁻¹ := by
            rw [← C.comm_E0_Q₁ (inv_mem hq2) (inv_mem ha)]
        _ = (q ^ 2)⁻¹ * (a ^ 2)⁻¹ := by rw [pow_two a]; group
    rw [e1]
    exact mul_mem (inv_mem hq2) (inv_mem (C.sq_mem_E0 ha))
  exact C.comm_of_cong hqN hqE ha hcong hg C.v'_mem_Q₁ hc

theorem inv_cases_Q₂ {j : X} (hj : j ∈ C.S₂) (hy : j * C.F.yF * j⁻¹ = C.F.yF)
    (hj2 : j ^ 2 = 1) : j ∈ C.D₁.Q₁ ∨ j ∈ C.Q₂₀ := by
  obtain ⟨-, -, -, -, -, hq₁F, hq₁2⟩ := C.q₁_spec
  obtain ⟨-, b0, b2, b1, b3, hq₂F, hq₂2⟩ := C.q₂_spec
  obtain ⟨-, a0, a1, a2, a3, -, -⟩ := C.q₁_spec
  have caseq₂ : ∀ a ∈ C.D₁.Q₁, (C.q₂ * a) ^ 2 = 1 → C.q₂ * a ∈ C.Q₂₀ := fun a ha h => by
    have hav := C.inv_cases_q C.q₂_N hq₂F hq₂2 C.w₁'_mem_Q₁ C.q₂_cong.2.1 ha h
    have haF := C.conj_Fv_of_Q₁ ha hav
    refine ⟨mul_mem C.q₂_mem (C.Q₁_le_S₂ ha), mem_centralizer_iff.mpr fun f hf => ?_⟩
    have h1 : C.q₂ * a * f * (C.q₂ * a)⁻¹ = f := by
      rw [show C.q₂ * a * f * (C.q₂ * a)⁻¹ = C.q₂ * (a * f * a⁻¹) * C.q₂⁻¹ by group, haF f hf,
        hq₂F f hf]
    calc f * (C.q₂ * a) = (C.q₂ * a * f * (C.q₂ * a)⁻¹) * (C.q₂ * a) := by rw [h1]
      _ = C.q₂ * a * f := by group
  obtain ⟨w, hw, h | h⟩ := C.mem_S₂_cases hj
  · obtain ⟨a, ha, rfl⟩ : ∃ a ∈ C.D₁.Q₁, j = w * a := ⟨_, h, by group⟩
    rcases hw with rfl | rfl | rfl | rfl
    · left; rw [one_mul]; exact ha
    · right
      have hav := C.inv_cases_q C.q₁_N hq₁F hq₁2 C.w₂_mem_Q₁ C.q₁_cong.2.2 ha hj2
      have haF := C.conj_Fv_of_Q₁ ha hav
      refine ⟨hj, mem_centralizer_iff.mpr fun f hf => ?_⟩
      have h1 : C.q₁ * a * f * (C.q₁ * a)⁻¹ = f := by
        rw [show C.q₁ * a * f * (C.q₁ * a)⁻¹ = C.q₁ * (a * f * a⁻¹) * C.q₁⁻¹ by group, haF f hf,
          hq₁F f hf]
      calc f * (C.q₁ * a) = (C.q₁ * a * f * (C.q₁ * a)⁻¹) * (C.q₁ * a) := by rw [h1]
        _ = C.q₁ * a * f := by group
    · right; exact caseq₂ a ha hj2
    · right
      have hu := C.u_mem_S₂
      have hp : C.q₂⁻¹ * (C.D₁.u * (C.q₁ * C.q₂) * C.D₁.u⁻¹) ∈ C.D₁.Q₁ := by
        refine C.mem_Q₁_of_fix (mul_mem (inv_mem C.q₂_mem) (mul_mem (mul_mem hu
          (mul_mem C.q₁_mem C.q₂_mem)) (inv_mem hu))) ?_ ?_
        · rw [act_mul, act_mul, act_mul, act_mul, C.u_inv, C.u_E₁, b0, a2, C.u_G₃',
            act_inv_eq b0]
        · rw [act_mul, act_mul, act_mul, act_mul, C.u_inv, C.u_G₂', b3, a1, C.u_E₁,
            act_inv_eq b2]
      set p := C.q₂⁻¹ * (C.D₁.u * (C.q₁ * C.q₂) * C.D₁.u⁻¹)
      have e1 : C.D₁.u * (C.q₁ * C.q₂ * a) * C.D₁.u⁻¹ =
          C.q₂ * (p * (C.D₁.u * a * C.D₁.u⁻¹)) := by simp only [p]; group
      have hua := C.conj_mem_Q₁ C.u_normalizes ha
      have hin := caseq₂ _ (mul_mem hp hua) (by
        rw [← e1, show (C.D₁.u * (C.q₁ * C.q₂ * a) * C.D₁.u⁻¹) ^ 2 =
          C.D₁.u * (C.q₁ * C.q₂ * a) ^ 2 * C.D₁.u⁻¹ by rw [pow_two, pow_two]; group, hj2]
        group)
      rw [← e1] at hin
      have := C.conj_Q₂₀ (inv_mem hu) hin
      rwa [show C.D₁.u⁻¹ * (C.D₁.u * (C.q₁ * C.q₂ * a) * C.D₁.u⁻¹) * C.D₁.u⁻¹⁻¹ =
        C.q₁ * C.q₂ * a by group] at this
  · exfalso
    obtain ⟨a, ha, rfl⟩ : ∃ a ∈ C.D₁.Q₁, j = w * a * C.D₁.u := ⟨_, h, by group⟩
    rw [show w * a * C.D₁.u * C.F.yF * (w * a * C.D₁.u)⁻¹ =
      w * (a * (C.D₁.u * C.F.yF * C.D₁.u⁻¹) * a⁻¹) * w⁻¹ by group, C.u_y,
      C.conj_eq_of_mem_Q₁ ha (mul_mem C.z_mem_E0 C.y_mem_E0),
      C.W_F hw (mem_sup_left (mul_mem C.z_mem_E0 C.y_mem_E0))] at hy
    exact S.z_ne_one (by simpa using hy)

theorem Q₁_le_of_conjTo {H : Subgroup X} (hH : ∀ c ∈ C.D₁.Q₁, ConjTo S.t c → c ∈ H) :
    C.D₁.Q₁ ≤ H := by
  have ht : S.t ∈ H := hH _ C.t_mem_Q₁ ⟨1, by group⟩
  have hE : C.E₀ ≤ H := fun e he => by
    have h1 := hH _ (mul_mem C.t_mem_Q₁ (C.E0_le_Q₁ he))
      (conjTo_t_mul_any C.D₁ C.isRefl_y C.isK_k he)
    rw [show e = S.t⁻¹ * (S.t * e) by group]
    exact mul_mem (inv_mem ht) h1
  have hr : ∀ {A : Subgroup X} {r : X}, C.Conj₁ A → A = C.E₀ ⊔ zpowers r → r ∈ C.D₁.Q₁ →
      r ^ 2 ∈ C.E₀ → r ∈ H := fun {A r} hA hAr hrQ hr2 => by
    obtain ⟨n, hn, hnA⟩ := C.conj₁_def.mp hA
    have hc := C.cong_E₁ hn hrQ hr2 (by rw [← hAr]; exact hnA)
    have h1 := hH _ (C.conj_mem_Q₁ hn C.t_mem_Q₁) ⟨n, rfl⟩
    rw [show r = (n * S.t * n⁻¹ * r⁻¹)⁻¹ * (n * S.t * n⁻¹) by group]
    exact mul_mem (inv_mem (hE (C.cong_def.mp hc))) h1
  have h1 := hr C.conj₁_all.1 rfl C.r₁_mem C.r₁_sq_mem
  have h2 := hr C.conj₁_all.2.1 rfl C.r₂_mem C.r₂_sq_mem
  have h3 := hr C.conj₁_all.2.2 rfl C.r₃_mem C.r₃_sq_mem
  have hv1 : C.v' * C.w₁' ∈ H := by
    rw [show C.v' * C.w₁' = S.t⁻¹ * (S.t * C.v' * C.w₁') by group]
    exact mul_mem (inv_mem ht) h1
  have hv2 : C.v' * C.D₁.w₂ ∈ H := by
    rw [show C.v' * C.D₁.w₂ = S.t⁻¹ * (S.t * C.v' * C.D₁.w₂) by group]
    exact mul_mem (inv_mem ht) h2
  have hw₂ : C.D₁.w₂ ∈ H := by
    rw [show C.D₁.w₂ = (S.t * C.v' * C.w₁')⁻¹ * (S.t * C.v' * C.w₁' * C.D₁.w₂) by group]
    exact mul_mem (inv_mem h1) h3
  have hv : C.v' ∈ H := by
    rw [show C.v' = C.v' * C.D₁.w₂ * C.D₁.w₂⁻¹ by group]
    exact mul_mem hv2 (inv_mem hw₂)
  have hw₁ : C.w₁' ∈ H := by
    rw [show C.w₁' = C.v'⁻¹ * (C.v' * C.w₁') by group]
    exact mul_mem (inv_mem hv) hv1
  rw [C.Q₁_eq]
  refine sup_le (sup_le (sup_le ?_ (zpowers_le.mpr hv)) (zpowers_le.mpr hw₁))
    (zpowers_le.mpr hw₂)
  rw [C.E₁_eq]
  exact sup_le hE (zpowers_le.mpr ht)

end Setup

end Sec7

end CFSG.ComponentClassification.HSFLit

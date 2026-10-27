module

public import CFSG.CGT.Stroth77.Arch76Lemma2Finite
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.CGT.Stroth77.Arch76

namespace Config

variable {X : Type*} [Group X] (C : Config X) [hN : C.A.Normal]

theorem mul_ev (g : X) (v : Co) : g * C.ev v = C.ev (C.act g⁻¹ v) * g := by
  rw [ev_act, inv_inv]; group

theorem uv_inv : C.uv⁻¹ = C.uv := inv_eq_of_mul_eq_one_right (by rw [← pow_two, C.huv2])
theorem t_inv : C.t⁻¹ = C.t := inv_eq_of_mul_eq_one_right (by rw [← pow_two, C.ht2])
theorem u_inv : C.u⁻¹ = C.u := inv_eq_of_mul_eq_one_right (by rw [← pow_two, C.hu2])

theorem uv_mul_ev (v : Co) : C.uv * C.ev v = C.ev (fuv v) * C.uv := by rw [mul_ev, act_uv_inv]
theorem t_mul_ev (v : Co) : C.t * C.ev v = C.ev (ft v) * C.t := by rw [mul_ev, act_t_inv]
theorem u_mul_ev (v : Co) : C.u * C.ev v = C.ev (fu v) * C.u := by rw [mul_ev, act_u_inv]

theorem ev_mul_ev_mul (a b : Co) (g h : X) :
    C.ev a * g * (C.ev b * h) = C.ev (a + C.act g⁻¹ b) * (g * h) := by
  calc C.ev a * g * (C.ev b * h) = C.ev a * (g * C.ev b) * h := by group
    _ = C.ev a * C.ev (C.act g⁻¹ b) * (g * h) := by rw [mul_ev]; group
    _ = _ := by rw [ev_add]

theorem conj_ev_mul (k : X) (a : Co) (g : X) :
    k⁻¹ * (C.ev a * g) * k = C.ev (C.act k a) * (k⁻¹ * g * k) := by
  rw [ev_act]; group

theorem ev_conj_ev_mul (c a : Co) (g : X) :
    (C.ev c)⁻¹ * (C.ev a * g) * C.ev c = C.ev (-c + a + C.act g⁻¹ c) * g := by
  calc (C.ev c)⁻¹ * (C.ev a * g) * C.ev c = C.ev (-c) * C.ev a * (g * C.ev c) := by
        rw [ev_neg]; group
    _ = _ := by rw [C.mul_ev g c, ← mul_assoc, ← ev_add, ← ev_add]

theorem conj_mul_ev_of {s g : X} {va : Co} (h : s⁻¹ * g * s = C.ev va * g) (c : Co) :
    (s * C.ev c)⁻¹ * g * (s * C.ev c) = C.ev (-c + va + C.act g⁻¹ c) * g := by
  rw [← C.ev_conj_ev_mul c va g, ← h]; group

theorem ev_cancel {a b : Co} {g : X} (h : C.ev a * g = C.ev b * g) : a = b :=
  C.ev_injective (mul_right_cancel h)

theorem ev_mem_K (v : Co) : C.ev v ∈ C.K := C.A_le_K (C.ev_mem v)

theorem kap_ev (v : Co) : C.kap (C.ev v) = 0 := C.kap_of_mem_A (C.ev_mem v)

theorem kap_one : C.kap 1 = 0 := C.kap_of_mem_A (one_mem _)

theorem kap_add_self {k : X} (hk : k ∈ C.K) : C.kap k + C.kap k = 0 := by
  obtain ⟨h1, h2⟩ := C.kap_two_nsmul hk
  rw [two_nsmul] at h1 h2
  exact Prod.ext h1 h2

theorem kap_inv {k : X} (hk : k ∈ C.K) : C.kap k⁻¹ = C.kap k := by
  have h := C.kap_mul (inv_mem hk) hk
  rw [inv_mul_cancel, kap_one] at h
  have h2 := C.kap_add_self hk
  calc C.kap k⁻¹ = C.kap k⁻¹ + (C.kap k + C.kap k) := by rw [h2, add_zero]
    _ = (C.kap k⁻¹ + C.kap k) + C.kap k := by abel
    _ = C.kap k := by rw [← h, zero_add]

variable (hCA : Subgroup.centralizer (C.A : Set X) = C.A)
include hCA

theorem exists_ev_of_kap_eq {k k' : X} (hk : k ∈ C.K) (hk' : k' ∈ C.K)
    (h : C.kap k' = C.kap k) : ∃ v : Co, k' = k * C.ev v := by
  have hm : k⁻¹ * k' ∈ C.A := by
    rw [← C.kap_eq_zero_iff hCA (mul_mem (inv_mem hk) hk'), C.kap_mul (inv_mem hk) hk',
      C.kap_inv hk, h, C.kap_add_self hk]
  obtain ⟨v, hv⟩ := C.exists_ev hm
  exact ⟨v, by rw [hv]; group⟩

theorem exists_sq {k : X} (hk : k ∈ C.K) : ∃ v : Co, k * k = C.ev v := by
  obtain ⟨v, hv⟩ := C.exists_ev_of_kap_eq hCA (one_mem _) (mul_mem hk hk)
    (by rw [C.kap_mul hk hk, C.kap_add_self hk, kap_one])
  exact ⟨v, by rw [hv, one_mul]⟩

theorem exists_transl {k g : X} (hk : k ∈ C.K) (hg : g⁻¹ = g)
    (hfix : C.kap (g⁻¹ * k * g) = C.kap k) : ∃ v : Co, k⁻¹ * g * k = C.ev v * g := by
  obtain ⟨v, hv⟩ := C.exists_ev_of_kap_eq hCA hk (C.conj_mem_K hk g) hfix
  refine ⟨v, ?_⟩
  calc k⁻¹ * g * k = k⁻¹ * g⁻¹ * k := by rw [hg]
    _ = k⁻¹ * (g⁻¹ * k * g) * g⁻¹ := by group
    _ = C.ev v * g := by rw [hv, hg]; group

omit hCA in
theorem transl_t_of_comm {s : X} (hρ : C.ρ⁻¹ * s * C.ρ = s) {va : Co}
    (hva : s⁻¹ * C.uv * s = C.ev va * C.uv) : s⁻¹ * C.t * s = C.ev (fρ va) * C.t := by
  calc s⁻¹ * C.t * s = s⁻¹ * (C.ρ⁻¹ * C.uv * C.ρ) * s := by rw [C.hρuv]
    _ = C.ρ⁻¹ * (s⁻¹ * C.uv * s) * C.ρ := by
        conv_lhs => rw [← hρ]
        group
    _ = C.ev (fρ va) * C.t := by rw [hva, conj_ev_mul, act_ρ, C.hρuv]

theorem mem_A_of_act_eq {g : X} (h : ∀ v, C.act g v = v) : g ∈ C.A := by
  rw [← hCA, Subgroup.mem_centralizer_iff]
  intro a ha
  obtain ⟨v, rfl⟩ := C.exists_ev ha
  have h1 := C.ev_act g v
  rw [h] at h1
  calc C.ev v * g = g * (g⁻¹ * C.ev v * g) := by group
    _ = g * C.ev v := by rw [← h1]

theorem ρ_cube (hρodd : Odd (orderOf C.ρ)) : C.ρ ^ 3 = 1 := by
  have hcen : C.ρ ^ 3 ∈ C.A := C.mem_A_of_act_eq hCA fun v => by
    rw [pow_three', act_mul, act_mul, act_ρ, act_ρ, act_ρ,
      fρ_fρ_fρ]
  obtain ⟨v, hv⟩ := C.exists_ev hcen
  have h4 : (C.ρ ^ 3) ^ 4 = 1 := by rw [← hv, ← ev_nsmul, four_nsmul_eq, ev_zero]
  have hd : orderOf (C.ρ ^ 3) ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  obtain ⟨k, hk⟩ := hρodd.of_dvd_nat (orderOf_pow_dvd 3)
  have hle := Nat.le_of_dvd (by norm_num) hd
  have hk' : k = 0 ∨ k = 1 := by omega
  rcases hk' with rfl | rfl
  · exact orderOf_eq_one_iff.mp (by simpa using hk)
  · rw [hk] at hd; norm_num at hd

theorem exists_comm_ρ (hρ3 : C.ρ ^ 3 = 1) {k : X} (hk : k ∈ C.K)
    (hfix : Lρ (C.kap k) = C.kap k) :
    ∃ k' ∈ C.K, C.kap k' = C.kap k ∧ C.ρ⁻¹ * k' * C.ρ = k' := by
  obtain ⟨vr, hvr⟩ := C.exists_ev_of_kap_eq hCA hk (C.conj_mem_K hk C.ρ)
    (by rw [C.kap_conj_ρ hk, hfix])
  have hstep : ∀ c : Co, C.ρ⁻¹ * (k * C.ev c) * C.ρ = k * C.ev (vr + fρ c) := fun c => by
    calc C.ρ⁻¹ * (k * C.ev c) * C.ρ = (C.ρ⁻¹ * k * C.ρ) * (C.ρ⁻¹ * C.ev c * C.ρ) := by group
      _ = k * C.ev (vr + fρ c) := by rw [hvr, conj_ρ_ev, ev_add, mul_assoc]
  have h3 : C.ρ⁻¹ * (C.ρ⁻¹ * (C.ρ⁻¹ * k * C.ρ) * C.ρ) * C.ρ = k := by
    calc _ = (C.ρ ^ 3)⁻¹ * k * C.ρ ^ 3 := by rw [pow_three']; group
      _ = k := by rw [hρ3]; group
  rw [hvr, hstep, hstep] at h3
  have h0 : vr + fρ (vr + fρ vr) = 0 :=
    (C.ev_eq_one_iff _).mp (mul_left_cancel (h3.trans (mul_one k).symm))
  rw [fρ_add, ← add_assoc] at h0
  obtain ⟨c, hc⟩ := exists_fix_of_norm vr h0
  refine ⟨k * C.ev c, mul_mem hk (C.ev_mem_K c), ?_, ?_⟩
  · rw [C.kap_mul hk (C.ev_mem_K c), kap_ev, add_zero]
  · rw [hstep, ← hc]

theorem pow_eight_of_mem_K {k : X} (hk : k ∈ C.K) : k ^ 8 = 1 := by
  obtain ⟨v, hv⟩ := C.exists_sq hCA hk
  calc k ^ 8 = (k * k) ^ 4 := by rw [← pow_two, ← pow_mul]
    _ = 1 := by rw [hv, ← ev_nsmul, four_nsmul_eq, ev_zero]

theorem K_isPGroup : IsPGroup 2 C.K := fun g =>
  ⟨3, Subtype.ext (by simpa using C.pow_eight_of_mem_K hCA g.2)⟩

omit hCA in
theorem K_normal : C.K.Normal := ⟨fun k hk g => by simpa using C.conj_mem_K hk g⁻¹⟩

theorem K_le (P : Sylow 2 X) : C.K ≤ P := by
  haveI := C.K_normal
  exact (C.K_isPGroup hCA).le_sylow_of_normal P

omit hCA

@[expose] noncomputable def mat (g : X) : Mat := (C.act g (1, 0, 0), C.act g X0, C.act g Y0)

theorem act_eq_matAct (g : X) (v : Co) : C.act g v = matAct (C.mat g) v := by
  conv_lhs => rw [← lin_basis' v]
  rw [act_lin]; rfl

theorem mat_mul (g h : X) : C.mat (g * h) = matMul (C.mat g) (C.mat h) := by
  show (C.act (g * h) (1, 0, 0), C.act (g * h) X0, C.act (g * h) Y0) =
    (matAct (C.mat h) (C.act g (1, 0, 0)), matAct (C.mat h) (C.act g X0),
      matAct (C.mat h) (C.act g Y0))
  rw [act_mul, act_mul, act_mul, C.act_eq_matAct h, C.act_eq_matAct h (C.act g X0),
    C.act_eq_matAct h (C.act g Y0)]

theorem mat_mem_d8 {d : X} (hd : d ∈ Subgroup.closure {C.uv, C.t, C.u}) : C.mat d ∈ d8 := by
  have huv : C.mat C.uv ∈ d8 := by
    show (C.act C.uv (1, 0, 0), C.act C.uv X0, C.act C.uv Y0) ∈ d8
    rw [act_uv, act_uv, act_uv]; exact uv_mem_d8
  have ht : C.mat C.t ∈ d8 := by
    show (C.act C.t (1, 0, 0), C.act C.t X0, C.act C.t Y0) ∈ d8
    rw [act_t, act_t, act_t]; exact t_mem_d8
  have hu : C.mat C.u ∈ d8 := by
    show (C.act C.u (1, 0, 0), C.act C.u X0, C.act C.u Y0) ∈ d8
    rw [act_u, act_u, act_u]; exact u_mem_d8
  induction hd using Subgroup.closure_induction'' with
  | mem g hg =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    exacts [huv, ht, hu]
  | inv_mem g hg =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · rwa [uv_inv]
    · rwa [t_inv]
    · rwa [u_inv]
  | one =>
    show (C.act 1 (1, 0, 0), C.act 1 X0, C.act 1 Y0) ∈ d8
    rw [act_one, act_one, act_one]; exact one_mem_d8
  | mul g h _ _ ihg ihh => rw [mat_mul]; exact matMul_mem_d8 _ ihg _ ihh

include hCA

theorem mem_A_of_mem_T {τ : X} (hτ : τ ∈ C.A ⊔ Subgroup.closure {C.uv, C.t, C.u})
    (hK : τ ∈ C.K) : τ ∈ C.A := by
  have hτ' : τ ∈ ((C.A ⊔ Subgroup.closure {C.uv, C.t, C.u} : Subgroup X) : Set X) := hτ
  rw [Subgroup.normal_mul, Set.mem_mul] at hτ'
  obtain ⟨a, ha, d, hd, rfl⟩ := hτ'
  have hdK : d ∈ C.K := by
    have h := mul_mem (inv_mem (C.A_le_K ha)) hK
    rwa [inv_mul_cancel_left] at h
  have hfix := C.mem_K_iff.mp hdK
  have e := eq_one_of_mem_d8 _ (C.mat_mem_d8 hd) (hfix _ (by decide))
    (by show 2 • C.act d X0 = _; rw [← act_nsmul, hfix _ (by decide)]; rfl)
    (by show 2 • C.act d Y0 = _; rw [← act_nsmul, hfix _ (by decide)]; rfl)
  have hdA : d ∈ C.A := C.mem_A_of_act_eq hCA fun v => by
    rw [act_eq_matAct, e]; exact lin_basis v
  exact mul_mem ha hdA

omit hCA

theorem ev_two_nsmul_mem_E (v : Co) :
    C.ev (2 • v) ∈ Subgroup.closure {C.x ^ 2, C.y ^ 2, C.uv, C.t} := by
  have h1 : C.ev (0, 2, 0) = C.x ^ 2 := by simp [ev, show (2 : ZMod 4).val = 2 from rfl]
  have h2 : C.ev (0, 0, 2) = C.y ^ 2 := by simp [ev, show (2 : ZMod 4).val = 2 from rfl]
  rw [two_nsmul_eq, ev_add, ev_nsmul, ev_nsmul, h1, h2]
  exact mul_mem (pow_mem (Subgroup.subset_closure (by simp)) _)
    (pow_mem (Subgroup.subset_closure (by simp)) _)

theorem mem_normalizer_E {k : X} (hk : k ∈ C.K) {a b : Co}
    (ha : k⁻¹ * C.uv * k = C.ev (2 • a) * C.uv) (hb : k⁻¹ * C.t * k = C.ev (2 • b) * C.t) :
    k ∈ Subgroup.normalizer (Subgroup.closure {C.x ^ 2, C.y ^ 2, C.uv, C.t} : Set X) := by
  set E := Subgroup.closure {C.x ^ 2, C.y ^ 2, C.uv, C.t} with hE
  have hfix := C.mem_K_iff.mp hk
  have hcomm : ∀ v : Co, 2 • v = 0 → k * C.ev v = C.ev v * k := fun v hv => by
    have h1 := C.ev_act k v
    rw [hfix v hv] at h1
    calc k * C.ev v = k * (k⁻¹ * C.ev v * k) := by rw [← h1]
      _ = C.ev v * k := by group
  have hx2 : C.x ^ 2 = C.ev (0, 2, 0) := by simp [ev, show (2 : ZMod 4).val = 2 from rfl]
  have hy2 : C.y ^ 2 = C.ev (0, 0, 2) := by simp [ev, show (2 : ZMod 4).val = 2 from rfl]
  have huvE : C.uv ∈ E := Subgroup.subset_closure (by simp)
  have htE : C.t ∈ E := Subgroup.subset_closure (by simp)
  have hx2E : C.x ^ 2 ∈ E := Subgroup.subset_closure (by simp)
  have hy2E : C.y ^ 2 ∈ E := Subgroup.subset_closure (by simp)
  have hconjA : ∀ v : Co, 2 • v = 0 → k⁻¹ * C.ev v * k = C.ev v := fun v hv => by
    rw [mul_assoc, ← hcomm v hv]; group
  have hconjA' : ∀ v : Co, 2 • v = 0 → k * C.ev v * k⁻¹ = C.ev v := fun v hv => by
    rw [hcomm v hv]; group
  have hinvuv : k * C.uv * k⁻¹ = (C.ev (2 • a))⁻¹ * C.uv := by
    have h := congrArg (fun z => k * z * k⁻¹) ha
    rw [show k * (k⁻¹ * C.uv * k) * k⁻¹ = C.uv by group,
      show k * (C.ev (2 • a) * C.uv) * k⁻¹ = (k * C.ev (2 • a) * k⁻¹) * (k * C.uv * k⁻¹) by group,
      hconjA' _ (two_two_nsmul a)] at h
    rw [eq_inv_mul_iff_mul_eq]; exact h.symm
  have hinvt : k * C.t * k⁻¹ = (C.ev (2 • b))⁻¹ * C.t := by
    have h := congrArg (fun z => k * z * k⁻¹) hb
    rw [show k * (k⁻¹ * C.t * k) * k⁻¹ = C.t by group,
      show k * (C.ev (2 • b) * C.t) * k⁻¹ = (k * C.ev (2 • b) * k⁻¹) * (k * C.t * k⁻¹) by group,
      hconjA' _ (two_two_nsmul b)] at h
    rw [eq_inv_mul_iff_mul_eq]; exact h.symm
  have fwd : ∀ e ∈ E, k⁻¹ * e * k ∈ E := by
    intro e he
    induction he using Subgroup.closure_induction with
    | mem g hg =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · rw [hx2, hconjA _ (by decide), ← hx2]; exact hx2E
      · rw [hy2, hconjA _ (by decide), ← hy2]; exact hy2E
      · rw [ha]; exact mul_mem (C.ev_two_nsmul_mem_E a) huvE
      · rw [hb]; exact mul_mem (C.ev_two_nsmul_mem_E b) htE
    | one => simp
    | mul g₁ g₂ _ _ ihg ihh =>
      have h := mul_mem ihg ihh
      rwa [show k⁻¹ * g₁ * k * (k⁻¹ * g₂ * k) = k⁻¹ * (g₁ * g₂) * k by group] at h
    | inv g _ ih =>
      have h := inv_mem ih
      rwa [show (k⁻¹ * g * k)⁻¹ = k⁻¹ * g⁻¹ * k by group] at h
  have bwd : ∀ e ∈ E, k * e * k⁻¹ ∈ E := by
    intro e he
    induction he using Subgroup.closure_induction with
    | mem g hg =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · rw [hx2, hconjA' _ (by decide), ← hx2]; exact hx2E
      · rw [hy2, hconjA' _ (by decide), ← hy2]; exact hy2E
      · rw [hinvuv]; exact mul_mem (inv_mem (C.ev_two_nsmul_mem_E a)) huvE
      · rw [hinvt]; exact mul_mem (inv_mem (C.ev_two_nsmul_mem_E b)) htE
    | one => simp
    | mul g₁ g₂ _ _ ihg ihh =>
      have h := mul_mem ihg ihh
      rwa [show k * g₁ * k⁻¹ * (k * g₂ * k⁻¹) = k * (g₁ * g₂) * k⁻¹ by group] at h
    | inv g _ ih =>
      have h := inv_mem ih
      rwa [show (k * g * k⁻¹)⁻¹ = k * g⁻¹ * k⁻¹ by group] at h
  rw [Subgroup.mem_normalizer_iff'']
  intro h
  refine ⟨fwd h, fun h' => ?_⟩
  have h2 := bwd _ h'
  rwa [show k * (k⁻¹ * h * k) * k⁻¹ = h by group] at h2

include hCA in
theorem kap_eq_zero_of_normalizes (P : Sylow 2 X)
    (hE : ∀ g ∈ (P : Subgroup X),
      g ∈ Subgroup.normalizer (Subgroup.closure {C.x ^ 2, C.y ^ 2, C.uv, C.t} : Set X) →
        g ∈ C.A ⊔ Subgroup.closure {C.uv, C.t, C.u})
    {k : X} (hk : k ∈ C.K) {a b : Co}
    (ha : k⁻¹ * C.uv * k = C.ev (2 • a) * C.uv) (hb : k⁻¹ * C.t * k = C.ev (2 • b) * C.t) :
    C.kap k = 0 :=
  C.kap_of_mem_A (C.mem_A_of_mem_T hCA (hE k (C.K_le hCA P hk) (C.mem_normalizer_E hk ha hb)) hk)

theorem act_injective (g : X) : Function.Injective (C.act g) := fun v v' h => by
  have e : ∀ w, C.act g⁻¹ (C.act g w) = w := fun w => by
    rw [← act_mul, mul_inv_cancel, act_one]
  rw [← e v, h, e v']

theorem act_pow_eq {g : X} {v : Co} (h : C.act g v = v) (n : ℕ) : C.act (g ^ n) v = v := by
  induction n with
  | zero => rw [pow_zero, act_one]
  | succ n ih => rw [pow_succ, act_mul, ih, h]

theorem act_cube (g : X) (v : Co) : C.act (g ^ 3) v = C.act g (C.act g (C.act g v)) := by
  rw [pow_three', act_mul, act_mul]

theorem act_fix_of_cube {g : X} (hg : ∃ n : ℕ, g ^ 2 ^ n = 1) {v : Co}
    (h : C.act (g ^ 3) v = v) : C.act g v = v := by
  obtain ⟨n, hn⟩ := hg
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hn)
  have hcop : Nat.Coprime 3 (orderOf g) := by
    rw [hj]; exact Nat.Coprime.pow_right _ (by norm_num)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]; exact C.act_pow_eq h m

theorem not_three_cycle {g : X} (hg : ∃ n : ℕ, g ^ 2 ^ n = 1)
    (h : (C.act g (0, 2, 0) = (0, 0, 2) ∧ C.act g (0, 0, 2) = (0, 2, 2)) ∨
      (C.act g (0, 2, 0) = (0, 2, 2) ∧ C.act g (0, 0, 2) = (0, 2, 0))) : False := by
  have e3 : ((0, 2, 2) : Co) = (0, 2, 0) + (0, 0, 2) := by decide
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h3 : C.act g (0, 2, 2) = (0, 2, 0) := by rw [e3, act_add, h1, h2]; decide
    have := C.act_fix_of_cube hg (v := (0, 2, 0)) (by rw [act_cube, h1, h2, h3])
    rw [h1] at this; exact absurd this (by decide)
  · have h3 : C.act g (0, 2, 2) = (0, 0, 2) := by rw [e3, act_add, h1, h2]; decide
    have := C.act_fix_of_cube hg (v := (0, 2, 0)) (by rw [act_cube, h1, h3, h2])
    rw [h1] at this; exact absurd this (by decide)

theorem mem_K_of_fix {k : X} (h1 : C.act k (1, 0, 0) = (1, 0, 0))
    (h2 : C.act k (0, 2, 0) = (0, 2, 0)) (h3 : C.act k (0, 0, 2) = (0, 0, 2)) : k ∈ C.K := by
  rw [mem_K_iff]
  intro v hv
  rw [om_decomp v hv, act_add, act_add, act_nsmul, act_nsmul, act_nsmul, h1, h2, h3]

theorem uv_mem_T : C.uv ∈ C.A ⊔ Subgroup.closure {C.uv, C.t, C.u} :=
  Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
theorem t_mem_T : C.t ∈ C.A ⊔ Subgroup.closure {C.uv, C.t, C.u} :=
  Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
theorem u_mem_T : C.u ∈ C.A ⊔ Subgroup.closure {C.uv, C.t, C.u} :=
  Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))

theorem exists_mul_mem_K_of_fix {g : X} (h1 : C.act g (0, 2, 0) = (0, 2, 0))
    (h2 : C.act g (0, 0, 2) = (0, 0, 2)) :
    ∃ τ ∈ C.A ⊔ Subgroup.closure {C.uv, C.t, C.u}, g * τ ∈ C.K := by
  have h3 : C.act g (0, 2, 2) = (0, 2, 2) := by
    rw [show ((0, 2, 2) : Co) = (0, 2, 0) + (0, 0, 2) by decide, act_add, h1, h2]
  have hinj := C.act_injective g
  have hz := w_cases (C.act g (1, 0, 0))
    (by rw [← act_nsmul, show (2 • ((1, 0, 0) : Co)) = 0 by decide, act_zero])
    (fun h => absurd (hinj (h.trans (C.act_zero g).symm)) (by decide))
    (fun h => absurd (hinj (h.trans h1.symm)) (by decide))
    (fun h => absurd (hinj (h.trans h2.symm)) (by decide))
    (fun h => absurd (hinj (h.trans h3.symm)) (by decide))
  rcases hz with hz | hz | hz | hz
  · refine ⟨1, one_mem _, ?_⟩
    rw [mul_one]; exact C.mem_K_of_fix hz h1 h2
  · refine ⟨C.t, C.t_mem_T, C.mem_K_of_fix ?_ ?_ ?_⟩ <;>
      rw [act_mul, act_t] <;> simp only [hz, h1, h2] <;> decide
  · refine ⟨C.uv * C.t, mul_mem C.uv_mem_T C.t_mem_T, C.mem_K_of_fix ?_ ?_ ?_⟩ <;>
      rw [act_mul, act_mul, act_uv, act_t] <;> simp only [hz, h1, h2] <;> decide
  · refine ⟨C.uv, C.uv_mem_T, C.mem_K_of_fix ?_ ?_ ?_⟩ <;>
      rw [act_mul, act_uv] <;> simp only [hz, h1, h2] <;> decide

theorem exists_mul_mem_K {g : X} (hg : ∃ n : ℕ, g ^ 2 ^ n = 1)
    (hgu : ∃ n : ℕ, (g * C.u) ^ 2 ^ n = 1) :
    ∃ τ ∈ C.A ⊔ Subgroup.closure {C.uv, C.t, C.u}, g * τ ∈ C.K := by
  have hinj := C.act_injective g
  have e1 : C.act g (0, 2, 0) = 2 • C.act g X0 := by rw [← act_nsmul]; rfl
  have e2 : C.act g (0, 0, 2) = 2 • C.act g Y0 := by rw [← act_nsmul]; rfl
  have hu1 : ∀ v, C.act (g * C.u) v = fu (C.act g v) := fun v => by rw [act_mul, act_u]
  have hcases := sq_cases (C.act g X0) (C.act g Y0)
    (fun h => absurd (hinj ((e1.trans h).trans (C.act_zero g).symm)) (by decide))
    (fun h => absurd (hinj ((e2.trans h).trans (C.act_zero g).symm)) (by decide))
    (fun h => absurd (hinj ((e1.trans h).trans e2.symm)) (by decide))
  rw [← e1, ← e2] at hcases
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact C.exists_mul_mem_K_of_fix h1 h2
  · obtain ⟨τ, hτ, hgτ⟩ := C.exists_mul_mem_K_of_fix (g := g * C.u)
      (by rw [hu1, h1]; decide) (by rw [hu1, h2]; decide)
    exact ⟨C.u * τ, mul_mem C.u_mem_T hτ, by rwa [← mul_assoc]⟩
  · exact (C.not_three_cycle hg (Or.inl ⟨h1, h2⟩)).elim
  · exact (C.not_three_cycle hg (Or.inr ⟨h1, h2⟩)).elim
  · exact (C.not_three_cycle hgu (Or.inl ⟨by rw [hu1, h1]; decide, by rw [hu1, h2]; decide⟩)).elim
  · exact (C.not_three_cycle hgu (Or.inr ⟨by rw [hu1, h1]; decide, by rw [hu1, h2]; decide⟩)).elim

include hCA in
theorem sylow_eq (P : Sylow 2 X) (hTP : C.A ⊔ Subgroup.closure {C.uv, C.t, C.u} ≤ P) :
    (P : Subgroup X) = (C.A ⊔ Subgroup.closure {C.uv, C.t, C.u}) ⊔ C.K := by
  refine le_antisymm (fun g hg => ?_) (sup_le hTP (C.K_le hCA P))
  have h2 : ∀ h ∈ (P : Subgroup X), ∃ n : ℕ, h ^ 2 ^ n = 1 := fun h hh => by
    obtain ⟨n, hn⟩ := P.isPGroup' ⟨h, hh⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  obtain ⟨τ, hτ, hgτ⟩ := C.exists_mul_mem_K (h2 g hg) (h2 _ (mul_mem hg (hTP C.u_mem_T)))
  rw [show g = g * τ * τ⁻¹ by group]
  exact mul_mem (Subgroup.mem_sup_right hgτ) (Subgroup.mem_sup_left (inv_mem hτ))

end Config

end CFSG.CGT.Stroth77.Arch76

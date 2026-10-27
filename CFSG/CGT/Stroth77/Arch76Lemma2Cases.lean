module

public import CFSG.CGT.Stroth77.Arch76Lemma2Sylow

public section

namespace CFSG.CGT.Stroth77.Arch76

namespace Config

variable {X : Type*} [Group X] (C : Config X) [hN : C.A.Normal]

theorem ev_011 : C.ev (0, 1, 1) = C.x * C.y := by
  simp [ev, show (1 : ZMod 4).val = 1 from rfl]

theorem ev_003 : C.ev (0, 0, 3) = C.y⁻¹ := by
  rw [y_inv_eq]; simp [ev, show (3 : ZMod 4).val = 3 from rfl]

theorem ev_031 : C.ev (0, 3, 1) = C.x⁻¹ * C.y := by
  rw [x_inv_eq]; simp [ev, show (3 : ZMod 4).val = 3 from rfl, show (1 : ZMod 4).val = 1 from rfl]

theorem ev_032 : C.ev (0, 3, 2) = C.x⁻¹ * C.y ^ 2 := by
  rw [x_inv_eq]; simp [ev, show (3 : ZMod 4).val = 3 from rfl, show (2 : ZMod 4).val = 2 from rfl]

theorem ρ_t_inv : C.ρ * C.t * C.ρ⁻¹ = C.uv := by rw [← C.hρuv]; group

theorem ρ_conj_uvt : C.ρ⁻¹ * (C.uv * C.t) * C.ρ = C.uv := by
  rw [conj_mul_eq, C.hρuv, C.hρt, ← mul_assoc, ← C.huvt, mul_assoc, ← pow_two, C.ht2, mul_one]

theorem ρ_uv_inv : C.ρ * C.uv * C.ρ⁻¹ = C.uv * C.t := by
  calc C.ρ * C.uv * C.ρ⁻¹ = C.ρ * (C.ρ⁻¹ * (C.uv * C.t) * C.ρ) * C.ρ⁻¹ := by rw [ρ_conj_uvt]
    _ = C.uv * C.t := by group

theorem ρ_conj_ev_mul (a : Co) (g : X) :
    C.ρ⁻¹ * (C.ev a * g) * C.ρ = C.ev (fρ a) * (C.ρ⁻¹ * g * C.ρ) := by
  rw [conj_ev_mul, act_ρ]

omit hN in
theorem conj_conj_ρ (z g : X) : (C.ρ⁻¹ * z * C.ρ)⁻¹ * g * (C.ρ⁻¹ * z * C.ρ) =
    C.ρ⁻¹ * (z⁻¹ * (C.ρ * g * C.ρ⁻¹) * z) * C.ρ := by group

omit hN in
theorem conj_comm_ρ {s : X} (hρ : C.ρ⁻¹ * s * C.ρ = s) (g : X) :
    s⁻¹ * (C.ρ⁻¹ * g * C.ρ) * s = C.ρ⁻¹ * (s⁻¹ * g * s) * C.ρ := by
  conv_lhs => rw [← hρ]
  group

theorem transl_comm {s : X} {va vd : Co} (hva : s⁻¹ * C.uv * s = C.ev va * C.uv)
    (hvd : s⁻¹ * C.t * s = C.ev vd * C.t) : va + fuv vd = vd + ft va := by
  have h1 : s⁻¹ * (C.uv * C.t) * s = C.ev (va + fuv vd) * (C.uv * C.t) := by
    rw [conj_mul_eq, hva, hvd, ev_mul_ev_mul, act_uv_inv]
  have h2 : s⁻¹ * (C.t * C.uv) * s = C.ev (vd + ft va) * (C.t * C.uv) := by
    rw [conj_mul_eq, hvd, hva, ev_mul_ev_mul, act_t_inv]
  rw [C.huvt] at h1
  exact C.ev_cancel (h1.symm.trans h2)

theorem transl_sq {s g : X} {va vq : Co} (hva : s⁻¹ * g * s = C.ev va * g)
    (hq : s * s = C.ev vq) : C.act s va + va = -vq + C.act g⁻¹ vq := by
  have h1 : (s * s)⁻¹ * g * (s * s) = C.ev (C.act s va + va) * g := by
    rw [show (s * s)⁻¹ * g * (s * s) = s⁻¹ * (s⁻¹ * g * s) * s by group, hva, conj_ev_mul, hva,
      ← mul_assoc, ← ev_add]
  have h2 : (s * s)⁻¹ * g * (s * s) = C.ev (-vq + C.act g⁻¹ vq) * g := by
    have h := C.ev_conj_ev_mul vq 0 g
    rw [ev_zero, one_mul, add_zero] at h
    rw [hq, h]
  exact C.ev_cancel (h1.symm.trans h2)

theorem act_sq {s : X} {vq : Co} (hq : s * s = C.ev vq) : C.act s vq = vq := by
  apply C.act_eq_of
  rw [← hq]; group

theorem ρ_comm_sq {s : X} (hρ : C.ρ⁻¹ * s * C.ρ = s) {vq : Co} (hq : s * s = C.ev vq) :
    fρ vq = vq := by
  apply C.ev_injective
  rw [← conj_ρ_ev, ← hq]
  calc C.ρ⁻¹ * (s * s) * C.ρ = (C.ρ⁻¹ * s * C.ρ) * (C.ρ⁻¹ * s * C.ρ) := by group
    _ = s * s := by rw [hρ]

theorem exists_kap_add {r r' : Co × Co} (h : ∃ k ∈ C.K, C.kap k = r)
    (h' : ∃ k ∈ C.K, C.kap k = r') : ∃ k ∈ C.K, C.kap k = r + r' := by
  obtain ⟨k, hk, rfl⟩ := h
  obtain ⟨k', hk', rfl⟩ := h'
  exact ⟨k * k', mul_mem hk hk', C.kap_mul hk hk'⟩

theorem exists_kap_Luv {r : Co × Co} (h : ∃ k ∈ C.K, C.kap k = r) :
    ∃ k ∈ C.K, C.kap k = Luv r := by
  obtain ⟨k, hk, rfl⟩ := h
  exact ⟨_, C.conj_mem_K hk C.uv, C.kap_conj_uv hk⟩

theorem exists_kap_Lρ {r : Co × Co} (h : ∃ k ∈ C.K, C.kap k = r) :
    ∃ k ∈ C.K, C.kap k = Lρ r := by
  obtain ⟨k, hk, rfl⟩ := h
  exact ⟨_, C.conj_mem_K hk C.ρ, C.kap_conj_ρ hk⟩

theorem exists_kap_nρ {r : Co × Co} (h : ∃ k ∈ C.K, C.kap k = r) :
    ∃ k ∈ C.K, C.kap k = nρ r :=
  C.exists_kap_add (C.exists_kap_Lρ h) (C.exists_kap_Lρ (C.exists_kap_Lρ h))

theorem exists_gam1 {k : X} (hk : k ∈ C.K) (hρ : Lρ (C.kap k) ≠ C.kap k) :
    ∃ s ∈ C.K, C.kap s = gam1 := by
  have h0 : ∃ k' ∈ C.K, C.kap k' = C.kap k := ⟨k, hk, rfl⟩
  have h1 := C.exists_kap_add h0 (C.exists_kap_Luv h0)
  obtain ⟨h2a, h2b⟩ := C.kap_two_nsmul hk
  rcases gam1_mem_words _ h2a h2b hρ with h | h | h | h | h | h <;> rw [h]
  · exact C.exists_kap_nρ h0
  · exact C.exists_kap_Lρ (C.exists_kap_nρ h0)
  · exact C.exists_kap_Lρ (C.exists_kap_Lρ (C.exists_kap_nρ h0))
  · exact C.exists_kap_nρ h1
  · exact C.exists_kap_Lρ (C.exists_kap_nρ h1)
  · exact C.exists_kap_Lρ (C.exists_kap_Lρ (C.exists_kap_nρ h1))

theorem exists_bet {k : X} (hk : k ∈ C.K) (hρ : Lρ (C.kap k) = C.kap k) (h0 : C.kap k ≠ 0)
    (ha : C.kap k ≠ al0) : ∃ r ∈ C.K, C.kap r = bet := by
  obtain ⟨h2a, h2b⟩ := C.kap_two_nsmul hk
  rcases bet_mem_words _ h2a h2b hρ h0 ha with h | h
  · exact ⟨k, hk, h⟩
  · exact ⟨_, C.conj_mem_K hk C.u, by rw [C.kap_conj_u hk, h]⟩

variable (hCA : Subgroup.centralizer (C.A : Set X) = C.A) (hρ3 : C.ρ ^ 3 = 1) (P : Sylow 2 X)
  (hE : ∀ g ∈ (P : Subgroup X),
    g ∈ Subgroup.normalizer (Subgroup.closure {C.x ^ 2, C.y ^ 2, C.uv, C.t} : Set X) →
      g ∈ C.A ⊔ Subgroup.closure {C.uv, C.t, C.u})
include hCA hE

theorem compIII_false {s : X} (hs : s ∈ C.K) (hκ : C.kap s = gam1) : False := by
  obtain ⟨va, hva⟩ := C.exists_transl hCA hs C.uv_inv (by rw [C.kap_conj_uv hs, hκ, Luv_gam1])
  obtain ⟨vd, hvd⟩ := C.exists_transl hCA hs C.t_inv (by rw [C.kap_conj_t hs, hκ, Lt_gam1])
  obtain ⟨vq, hq⟩ := C.exists_sq hCA hs
  have hc := C.transl_comm hva hvd
  have he1 := C.transl_sq hva hq
  have he2 := C.transl_sq hvd hq
  have hqq := C.act_sq hq
  obtain ⟨e, he_def⟩ : ∃ e, e = C.ρ⁻¹ * s * C.ρ := ⟨_, rfl⟩
  have he : e ∈ C.K := he_def ▸ C.conj_mem_K hs C.ρ
  have hκe : C.kap e = gam2 := by rw [he_def, C.kap_conj_ρ hs, hκ, Lρ_gam1]
  have hm : C.ρ⁻¹ * e * C.ρ ∈ C.K := C.conj_mem_K he C.ρ
  have hκm : C.kap (C.ρ⁻¹ * e * C.ρ) = C.kap (s * e) := by
    rw [C.kap_conj_ρ he, hκe, Lρ_gam2, C.kap_mul hs he, hκ, hκe, gam1_add_gam2]
  obtain ⟨vn, hvn⟩ := C.exists_ev_of_kap_eq hCA (mul_mem hs he) hm hκm
  have hsuvt : s⁻¹ * (C.uv * C.t) * s = C.ev (va + fuv vd) * (C.uv * C.t) := by
    rw [conj_mul_eq, hva, hvd, ev_mul_ev_mul, act_uv_inv]
  have heuv : e⁻¹ * C.uv * e = C.ev (fρ (va + fuv vd)) * C.uv := by
    rw [he_def, conj_conj_ρ, ρ_uv_inv, hsuvt, ρ_conj_ev_mul, ρ_conj_uvt]
  have het : e⁻¹ * C.t * e = C.ev (fρ va) * C.t := by
    rw [he_def, conj_conj_ρ, ρ_t_inv, hva, ρ_conj_ev_mul, C.hρuv]
  have hm1 : (C.ρ⁻¹ * e * C.ρ)⁻¹ * C.t * (C.ρ⁻¹ * e * C.ρ) =
      C.ev (fρ (fρ (va + fuv vd))) * C.t := by
    rw [conj_conj_ρ, ρ_t_inv, heuv, ρ_conj_ev_mul, C.hρuv]
  have hm2 : (C.ρ⁻¹ * e * C.ρ)⁻¹ * C.t * (C.ρ⁻¹ * e * C.ρ) =
      C.ev (-vn + (C.act e vd + fρ va) + ft vn) * C.t := by
    rw [hvn, show (s * e * C.ev vn)⁻¹ * C.t * (s * e * C.ev vn) =
        (C.ev vn)⁻¹ * (e⁻¹ * (s⁻¹ * C.t * s) * e) * C.ev vn by group, hvd,
      C.conj_ev_mul e vd C.t, het, ← mul_assoc (C.ev (C.act e vd)), ← ev_add, ev_conj_ev_mul,
      act_t_inv]
  have hj := C.ev_cancel (hm1.symm.trans hm2)
  have hs' : ∀ v, C.act s v = kmap gam1 v := fun v => by rw [C.act_of_mem_K hs, hκ]
  have he' : ∀ v, C.act e v = kmap gam2 v := fun v => by rw [C.act_of_mem_K he, hκe]
  rw [hs', act_uv_inv] at he1
  rw [hs', act_t_inv] at he2
  rw [hs'] at hqq
  rw [he'] at hj
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := compIII_finite va vd hc vq he1 he2 hqq vn hj.symm
  subst ha hb
  have h0 := C.kap_eq_zero_of_normalizes hCA P hE hs hva hvd
  rw [hκ] at h0
  exact gam1_ne_zero h0

include hρ3 in
theorem compII_false {r0 : X} (hr0 : r0 ∈ C.K) (hκ0 : C.kap r0 = bet) : False := by
  obtain ⟨r, hr, hκ, hρr⟩ := C.exists_comm_ρ hCA hρ3 hr0 (by rw [hκ0, Lρ_bet])
  rw [hκ0] at hκ
  obtain ⟨va, hva⟩ := C.exists_transl hCA hr C.uv_inv (by rw [C.kap_conj_uv hr, hκ, Luv_bet])
  have hvd := C.transl_t_of_comm hρr hva
  have hrt : fρ (fρ va) = va + fuv (fρ va) := by
    have h1 : r⁻¹ * (C.ρ⁻¹ * C.t * C.ρ) * r = C.ev (fρ (fρ va)) * (C.uv * C.t) := by
      rw [C.conj_comm_ρ hρr, hvd, ρ_conj_ev_mul, C.hρt]
    rw [C.hρt, conj_mul_eq, hva, hvd, ev_mul_ev_mul, act_uv_inv] at h1
    exact (C.ev_cancel h1).symm
  obtain ⟨s, hs_def⟩ : ∃ s, s = C.u⁻¹ * r * C.u * r⁻¹ := ⟨_, rfl⟩
  have hs : s ∈ C.K := hs_def ▸ mul_mem (C.conj_mem_K hr C.u) (inv_mem hr)
  have hκs : C.kap s = al0 := by
    rw [hs_def, C.kap_mul (C.conj_mem_K hr C.u) (inv_mem hr), C.kap_conj_u hr, C.kap_inv hr, hκ,
      Lu_bet_add]
  have hρs : C.ρ⁻¹ * s * C.ρ = s := by
    have e1 : C.u * C.ρ⁻¹ * C.u⁻¹ = C.ρ := by
      calc C.u * C.ρ⁻¹ * C.u⁻¹ = C.u⁻¹ * C.ρ⁻¹ * C.u := by rw [C.u_inv]
        _ = (C.u⁻¹ * C.ρ * C.u)⁻¹ := by group
        _ = C.ρ := by rw [C.hρu, inv_inv]
    have e3 : C.u * C.ρ * C.u⁻¹ = C.ρ⁻¹ := by
      calc C.u * C.ρ * C.u⁻¹ = C.u⁻¹ * C.ρ * C.u := by rw [C.u_inv]
        _ = C.ρ⁻¹ := C.hρu
    have e2 : C.ρ * r * C.ρ⁻¹ = r := by
      calc C.ρ * r * C.ρ⁻¹ = C.ρ * (C.ρ⁻¹ * r * C.ρ) * C.ρ⁻¹ := by rw [hρr]
        _ = r := by group
    calc C.ρ⁻¹ * s * C.ρ
        = C.u⁻¹ * ((C.u * C.ρ⁻¹ * C.u⁻¹) * r * (C.u * C.ρ * C.u⁻¹)) * C.u *
            (C.ρ⁻¹ * r * C.ρ)⁻¹ := by rw [hs_def]; group
      _ = C.u⁻¹ * (C.ρ * r * C.ρ⁻¹) * C.u * r⁻¹ := by rw [e1, e3, hρr]
      _ = s := by rw [e2, hs_def]
  have huvu1 : C.u * C.uv * C.u⁻¹ = C.uv := by rw [← C.huvu]; group
  have huvu2 : C.u⁻¹ * C.uv * C.u = C.uv := by rw [mul_assoc, C.huvu]; group
  have hruv : r * C.uv * r⁻¹ = C.ev (-C.act r⁻¹ va) * C.uv := by
    have h1 : r⁻¹⁻¹ * (C.ev va * C.uv) * r⁻¹ = C.uv := by rw [← hva]; group
    rw [conj_ev_mul, inv_inv] at h1
    rw [ev_neg, eq_inv_mul_iff_mul_eq]; exact h1
  have hvs : s⁻¹ * C.uv * s = C.ev (C.act r⁻¹ (fu va) + -C.act r⁻¹ va) * C.uv := by
    calc s⁻¹ * C.uv * s = r * (C.u⁻¹ * (r⁻¹ * (C.u * C.uv * C.u⁻¹) * r) * C.u) * r⁻¹ := by
          rw [hs_def]; group
      _ = r * (C.u⁻¹ * (C.ev va * C.uv) * C.u) * r⁻¹ := by rw [huvu1, hva]
      _ = r * (C.ev (fu va) * C.uv) * r⁻¹ := by rw [C.conj_ev_mul C.u va C.uv, act_u, huvu2]
      _ = r⁻¹⁻¹ * (C.ev (fu va) * C.uv) * r⁻¹ := by rw [inv_inv]
      _ = C.ev (C.act r⁻¹ (fu va)) * (r * C.uv * r⁻¹) := by rw [conj_ev_mul, inv_inv]
      _ = _ := by rw [hruv, ← mul_assoc, ← ev_add]
  have hvst := C.transl_t_of_comm hρs hvs
  have hr' : ∀ v, C.act r⁻¹ v = kmap bet v := fun v => by
    rw [C.act_of_mem_K (inv_mem hr), C.kap_inv hr, hκ]
  simp only [hr'] at hvs hvst
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := compII_finite va hrt
  rw [← ha] at hvs
  rw [← hb] at hvst
  have h0 := C.kap_eq_zero_of_normalizes hCA P hE hs hvs hvst
  rw [hκs] at h0
  exact al0_ne_zero h0

include hρ3 in
theorem compI {s0 : X} (hs0 : s0 ∈ C.K) (hκ0 : C.kap s0 = al0) :
    ∃ s ∈ C.K, C.kap s = al0 ∧ s ^ 2 = 1 ∧ s⁻¹ * C.w * s = C.w ∧ s⁻¹ * C.x * s = C.x⁻¹ ∧
      s⁻¹ * C.y * s = C.y⁻¹ ∧
      ((s⁻¹ * C.uv * s = C.x * C.y * C.uv ∧ s⁻¹ * C.t * s = C.x⁻¹ * C.t ∧
          s⁻¹ * C.u * s = C.u) ∨
        (s⁻¹ * C.uv * s = C.x⁻¹ * C.y * C.uv ∧ s⁻¹ * C.t * s = C.x⁻¹ * C.y ^ 2 * C.t ∧
          s⁻¹ * C.u * s = C.w * C.u)) := by
  obtain ⟨s, hs, hκ, hρs⟩ := C.exists_comm_ρ hCA hρ3 hs0 (by rw [hκ0, Lρ_al0])
  rw [hκ0] at hκ
  obtain ⟨va, hva⟩ := C.exists_transl hCA hs C.uv_inv (by rw [C.kap_conj_uv hs, hκ, Luv_al0])
  have hvd := C.transl_t_of_comm hρs hva
  obtain ⟨vb, hvb⟩ := C.exists_transl hCA hs C.u_inv (by rw [C.kap_conj_u hs, hκ, Lu_al0])
  obtain ⟨vq, hq⟩ := C.exists_sq hCA hs
  have hs' : ∀ v, C.act s v = kmap al0 v := fun v => by rw [C.act_of_mem_K hs, hκ]
  have h5 := C.transl_sq hva hq
  rw [hs', act_uv_inv] at h5
  have hqr := C.ρ_comm_sq hρs hq
  have h7a : vb + fu vb = 0 := by
    have h1 : (C.ev vb * C.u) * (C.ev vb * C.u) = 1 := by
      rw [← hvb, show s⁻¹ * C.u * s * (s⁻¹ * C.u * s) = s⁻¹ * (C.u * C.u) * s by group,
        ← pow_two, C.hu2]
      group
    rw [ev_mul_ev_mul, act_u_inv, ← pow_two, C.hu2, mul_one] at h1
    exact (C.ev_eq_one_iff _).mp h1
  have h7c : fu (-vb + fρ va + ft vb) = va + fuv (fρ va) := by
    have h1 : s⁻¹ * (C.u⁻¹ * C.t * C.u) * s =
        C.ev (fu (-vb + fρ va + ft vb)) * (C.uv * C.t) := by
      calc s⁻¹ * (C.u⁻¹ * C.t * C.u) * s =
            (s⁻¹ * C.u * s)⁻¹ * (s⁻¹ * C.t * s) * (s⁻¹ * C.u * s) := by group
        _ = (C.ev vb * C.u)⁻¹ * (C.ev (fρ va) * C.t) * (C.ev vb * C.u) := by rw [hvb, hvd]
        _ = C.u⁻¹ * ((C.ev vb)⁻¹ * (C.ev (fρ va) * C.t) * C.ev vb) * C.u := by group
        _ = C.u⁻¹ * (C.ev (-vb + fρ va + ft vb) * C.t) * C.u := by
          rw [ev_conj_ev_mul, act_t_inv]
        _ = C.ev (fu (-vb + fρ va + ft vb)) * (C.u⁻¹ * C.t * C.u) := by rw [conj_ev_mul, act_u]
        _ = _ := by rw [C.htu]
    rw [C.htu, conj_mul_eq, hva, hvd, ev_mul_ev_mul, act_uv_inv] at h1
    exact (C.ev_cancel h1).symm
  rcases compI_finite va vq h5 hqr vb h7a h7c with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ | ⟨c, hcq, hc⟩
  · exfalso
    rw [← ha] at hva
    rw [← hb] at hvd
    have h0 := C.kap_eq_zero_of_normalizes hCA P hE hs hva hvd
    rw [hκ] at h0
    exact al0_ne_zero h0
  have hconjA : ∀ v, (s * C.ev c)⁻¹ * C.ev v * (s * C.ev c) = C.ev (kmap al0 v) := fun v => by
    rw [← ev_act, act_mul, C.act_of_mem_A (C.ev_mem c), hs']
  have huv' := C.conj_mul_ev_of hva c
  have ht' := C.conj_mul_ev_of hvd c
  have hu' := C.conj_mul_ev_of hvb c
  rw [act_uv_inv] at huv'
  rw [act_t_inv] at ht'
  rw [act_u_inv] at hu'
  refine ⟨s * C.ev c, mul_mem hs (C.ev_mem_K c), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [C.kap_mul hs (C.ev_mem_K c), kap_ev, add_zero, hκ]
  · rw [pow_two, show s * C.ev c * (s * C.ev c) = (s * s) * (s⁻¹ * C.ev c * s) * C.ev c by group,
      hq, ← ev_act, hs', ← ev_add, ← ev_add, hcq, ev_zero]
  · rw [← C.ev_w, hconjA]; exact congrArg C.ev (by decide)
  · rw [← C.ev_x, hconjA, ← ev_neg]; exact congrArg C.ev (by decide)
  · rw [← C.ev_y, hconjA, ← ev_neg]; exact congrArg C.ev (by decide)
  · rcases hc with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · left
      refine ⟨?_, ?_, ?_⟩
      · rw [huv', h1, ev_011]
      · rw [ht', h2, ev_030]
      · rw [hu', h3, ev_zero, one_mul]
    · right
      refine ⟨?_, ?_, ?_⟩
      · rw [huv', h1, ev_031]
      · rw [ht', h2, ev_032]
      · rw [hu', h3, ev_w]

end Config

end CFSG.CGT.Stroth77.Arch76

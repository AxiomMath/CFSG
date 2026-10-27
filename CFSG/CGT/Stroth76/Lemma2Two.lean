module

public import CFSG.CGT.Stroth76.Lemma2Four
public import CFSG.CGT.Stroth76.Lemma1Data
public import CFSG.CGT.Stroth77.Arch76Lemma2Cases
public import CFSG.CGT.Stroth76.TFacts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.Stroth76

open CFSG.CGT.Stroth77.Arch76

theorem co_two_nsmul_ne_w : ∀ v : Co, 2 • v ≠ (1, 0, 0) := by decide +kernel

theorem dact_fix_om : ∀ d : Dc, dact d (1, 0, 0) = (1, 0, 0) → dact d (0, 2, 0) = (0, 2, 0) →
    dact d (0, 0, 2) = (0, 0, 2) → d = 0 := by
  decide +kernel

theorem co_w_add_fuv_ne_zero : ∀ v δ : Co, δ.1 = 0 → (1, 0, 0) + (v + (δ + fuv v)) ≠ 0 := by
  decide +kernel

theorem transl_uv_cases3 : ∀ va : Co, fρ (fρ va) = va + fuv (fρ va) →
    ((∃ a : Co, 2 • a = va) ∧ ∃ b : Co, 2 • b = fρ va) ∨
      ((∃ a : Co, 2 • a = va + (0, 3, 3)) ∧ ∃ b : Co, 2 • b = fρ va + (0, 1, 0)) := by
  decide +kernel

theorem transl_uv_cases4 : ∀ va : Co, fρ (fρ va) = va + fuv (fρ va) →
    ((∃ a : Co, 2 • a = va) ∧ ∃ b : Co, 2 • b = fρ va) ∨
      ((∃ a : Co, 2 • a = va + (0, 1, 3)) ∧ ∃ b : Co, 2 • b = fρ va + (0, 1, 2)) := by
  decide +kernel

section Elements

variable {X : Type*} [Group X] (K : Config X)

theorem ev_x_mul_y_inv : K.ev (0, 1, 3) = K.x * K.y⁻¹ := by
  rw [K.y_inv_eq]
  simp [Config.ev, show (1 : ZMod 4).val = 1 from rfl, show (3 : ZMod 4).val = 3 from rfl]

theorem conj_tElt_ev_dact (p : Tc) (e : Co) :
    (tElt K p)⁻¹ * K.ev e * tElt K p = K.ev (dact p.2 e) := by
  obtain ⟨v, d⟩ := p
  calc (tElt K (v, d))⁻¹ * K.ev e * tElt K (v, d)
      = (dElt K d)⁻¹ * ((K.ev v)⁻¹ * K.ev e * K.ev v) * dElt K d := by simp only [tElt]; group
    _ = K.ev (dact d e) := by
      rw [mul_assoc (K.ev v)⁻¹, K.comm (K.ev_mem e) (K.ev_mem v), inv_mul_cancel_left,
        conj_dElt_ev]

theorem mem_closure_cxy_cases {c : X} (hcom : ∀ v, c * K.ev v = K.ev v * c) (hc2 : c ^ 2 = K.w)
    {n : X} (hn : n ∈ Subgroup.closure {c, K.x, K.y}) :
    (∃ v, n = K.ev v) ∨ ∃ v, n = c * K.ev v := by
  have hcc : c * c = K.ev (1, 0, 0) := by rw [K.ev_w, ← hc2, pow_two]
  have hcinv : c⁻¹ = c * K.ev (1, 0, 0) := by
    rw [← hcc]
    refine inv_eq_of_mul_eq_one_left ?_
    rw [show c * (c * c) * c = (c * c) * (c * c) by simp only [mul_assoc], hcc, ← K.ev_add,
      show ((1, 0, 0) : Co) + (1, 0, 0) = 0 from by decide, K.ev_zero]
  induction hn using Subgroup.closure_induction with
  | mem g hg =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact Or.inr ⟨0, by rw [K.ev_zero, mul_one]⟩
    · exact Or.inl ⟨(0, 1, 0), K.ev_x.symm⟩
    · exact Or.inl ⟨(0, 0, 1), K.ev_y.symm⟩
  | one => exact Or.inl ⟨0, K.ev_zero.symm⟩
  | mul g h _ _ ihg ihh =>
    rcases ihg with ⟨v, rfl⟩ | ⟨v, rfl⟩ <;> rcases ihh with ⟨v', rfl⟩ | ⟨v', rfl⟩
    · exact Or.inl ⟨v + v', (K.ev_add v v').symm⟩
    · refine Or.inr ⟨v + v', ?_⟩
      calc K.ev v * (c * K.ev v') = (K.ev v * c) * K.ev v' := (mul_assoc _ _ _).symm
        _ = (c * K.ev v) * K.ev v' := by rw [hcom]
        _ = c * K.ev (v + v') := by rw [mul_assoc, K.ev_add]
    · exact Or.inr ⟨v + v', by rw [K.ev_add, mul_assoc]⟩
    · refine Or.inl ⟨(1, 0, 0) + (v + v'), ?_⟩
      calc c * K.ev v * (c * K.ev v') = c * (K.ev v * c) * K.ev v' := by group
        _ = c * (c * K.ev v) * K.ev v' := by rw [hcom]
        _ = c * c * (K.ev v * K.ev v') := by group
        _ = K.ev ((1, 0, 0) + (v + v')) := by rw [hcc, K.ev_add, K.ev_add]
  | inv g _ ih =>
    rcases ih with ⟨v, rfl⟩ | ⟨v, rfl⟩
    · exact Or.inl ⟨-v, (K.ev_neg v).symm⟩
    · refine Or.inr ⟨-v + (1, 0, 0), ?_⟩
      calc (c * K.ev v)⁻¹ = K.ev (-v) * c⁻¹ := by rw [mul_inv_rev, K.ev_neg]
        _ = (K.ev (-v) * c) * K.ev (1, 0, 0) := by rw [hcinv, mul_assoc]
        _ = (c * K.ev (-v)) * K.ev (1, 0, 0) := by rw [hcom]
        _ = c * K.ev (-v + (1, 0, 0)) := by rw [mul_assoc, K.ev_add]

variable [K.A.Normal]

theorem act_tElt_eq_dact (p : Tc) (e : Co) : K.act (tElt K p) e = dact p.2 e :=
  K.act_eq_of (conj_tElt_ev_dact K p e).symm

theorem snd_eq_zero_of_tElt_mem_K {p : Tc} (h : tElt K p ∈ K.K) : p.2 = 0 := by
  have hfix := K.mem_K_iff.mp h
  exact dact_fix_om p.2 ((act_tElt_eq_dact K p _).symm.trans (hfix _ (by decide)))
    ((act_tElt_eq_dact K p _).symm.trans (hfix _ (by decide)))
    ((act_tElt_eq_dact K p _).symm.trans (hfix _ (by decide)))

theorem centralizer_A_le_K : Subgroup.centralizer (K.A : Set X) ≤ K.K := by
  apply Subgroup.centralizer_le
  rintro _ ⟨v, -, rfl⟩
  exact K.ev_mem v

theorem mem_A_of_mem_Tsub_of_mem_K {τ : X} (hτ : τ ∈ Tsub K) (hK : τ ∈ K.K) : τ ∈ K.A := by
  obtain ⟨p, rfl⟩ := exists_tElt K hτ
  rw [tElt_mem_A_iff]
  exact snd_eq_zero_of_tElt_mem_K K hK

theorem dElt_mem_K_eq_zero {d : Dc} (h : dElt K d ∈ K.K) : d = 0 := by
  have h' : tElt K (0, d) ∈ K.K := by rwa [show tElt K (0, d) = dElt K d by simp [tElt]]
  exact snd_eq_zero_of_tElt_mem_K K h'

theorem mem_centralizer_A_of_act_eq {g : X} (h : ∀ v, K.act g v = v) :
    g ∈ Subgroup.centralizer (K.A : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  obtain ⟨v, rfl⟩ := K.exists_ev ha
  have h1 := K.ev_act g v
  rw [h] at h1
  calc K.ev v * g = g * (g⁻¹ * K.ev v * g) := by group
    _ = g * K.ev v := by rw [← h1]

theorem mul_self_mem_centralizer_of_mem_K {k : X} (hk : k ∈ K.K) :
    k * k ∈ Subgroup.centralizer (K.A : Set X) := by
  have h0 : K.kap (k * k) = 0 := by rw [K.kap_mul hk hk, K.kap_add_self hk]
  exact mem_centralizer_A_of_act_eq K fun v => by
    rw [K.act_of_mem_K (mul_mem hk hk), h0]; simp [kmap, dl]

end Elements

variable {X : Type*} [Group X] [Finite X] (K : Config X) [K.A.Normal]

theorem arch76Lemma2_index_two_core (hρodd : Odd (orderOf K.ρ)) {C : Subgroup X}
    (hCA : Subgroup.centralizer (K.A : Set X) = C) (hC : Nat.card C ∣ 2 ^ 7) (hne : C ≠ K.A)
    (P : Sylow 2 X) (hTP : K.A ⊔ Subgroup.closure {K.uv, K.t, K.u} ≤ P)
    (hP : Nat.card P ∣ 2 ^ 10)
    (hE : ∀ g ∈ (P : Subgroup X), g ∈ Subgroup.normalizer
      ((Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} : Subgroup X) : Set X) →
        g ∈ K.A ⊔ Subgroup.closure {K.uv, K.t, K.u})
    {c : X} (hCc : C = Subgroup.closure {c, K.x, K.y}) (hc2 : c ^ 2 = K.w) {δ₁ δ₂ : Co}
    (huvc : K.uv⁻¹ * c * K.uv = c * K.ev δ₁) (htc : K.t⁻¹ * c * K.t = c * K.ev δ₂)
    (hρc : K.ρ⁻¹ * c * K.ρ = c) (hδ : δ₁.1 = 0)
    (hfin : ∀ va : Co, fρ (fρ va) = va + fuv (fρ va) →
      ((∃ a : Co, 2 • a = va) ∧ ∃ b : Co, 2 • b = fρ va) ∨
        ((∃ a : Co, 2 • a = va + δ₁) ∧ ∃ b : Co, 2 • b = fρ va + δ₂)) :
    (P : Subgroup X) = C ⊔ Subgroup.closure {K.uv, K.t, K.u} := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hCn : C.Normal := by rw [← hCA]; infer_instance
  have hCP : C ≤ P := (IsPGroup.of_card_dvd_pow hC).le_sylow_of_normal P
  have hmemC : ∀ {g : X}, g ∈ C ↔ ∀ v, g * K.ev v = K.ev v * g := by
    intro g
    rw [← hCA, Subgroup.mem_centralizer_iff]
    refine ⟨fun h v => (h _ (K.ev_mem v)).symm, fun h a ha => ?_⟩
    obtain ⟨v, rfl⟩ := K.exists_ev ha
    exact (h v).symm
  have hAC : K.A ≤ C := fun a ha => hmemC.mpr fun v => K.comm ha (K.ev_mem v)
  have hcC : c ∈ C := by rw [hCc]; exact Subgroup.subset_closure (by simp)
  have hcom : ∀ v, c * K.ev v = K.ev v * c := hmemC.mp hcC
  have hcA : c ∉ K.A := fun h => by
    obtain ⟨v, hv⟩ := K.exists_ev h
    exact co_two_nsmul_ne_w v (K.ev_injective (by rw [K.ev_nsmul, hv, hc2, K.ev_w]))
  have hCcases : ∀ n ∈ C, (∃ v, n = K.ev v) ∨ ∃ v, n = c * K.ev v := fun n hn =>
    mem_closure_cxy_cases K hcom hc2 (hCc ▸ hn)
  have hcc : ∀ v v', c * K.ev v * (c * K.ev v') = K.ev ((1, 0, 0) + (v + v')) := fun v v' => by
    calc c * K.ev v * (c * K.ev v') = c * (K.ev v * c) * K.ev v' := by group
      _ = c * (c * K.ev v) * K.ev v' := by rw [hcom]
      _ = c * c * (K.ev v * K.ev v') := by group
      _ = K.ev ((1, 0, 0) + (v + v')) := by rw [K.ev_add, K.ev_add, K.ev_w, ← hc2, pow_two]
  have hρcA : ∀ v, K.ρ⁻¹ * (c * K.ev v) * K.ρ = c * K.ev (fρ v) := fun v => by
    rw [Config.conj_mul_eq, hρc, K.conj_ρ_ev]
  have hC64 : 64 ≤ Nat.card C := by
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hAC
    rw [K.hAcard] at hm
    have hm1 : m ≠ 1 := by
      rintro rfl
      exact hne (Subgroup.eq_of_le_of_card_ge hAC (by rw [hm, K.hAcard])).symm
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact (Nat.card_pos (α := C)).ne' (by rw [hm])
    omega
  have hCK : C ≤ K.K := hCA ▸ centralizer_A_le_K K
  haveI : K.K.Normal := K.K_normal
  have hK2 : IsPGroup 2 K.K := by
    rintro ⟨k, hk⟩
    have hkk : k * k ∈ C := hCA ▸ mul_self_mem_centralizer_of_mem_K K hk
    have h7 : (k * k) ^ 2 ^ 7 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp ((Subgroup.orderOf_dvd_natCard C hkk).trans hC)
    refine ⟨8, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, show 2 ^ 8 = 2 * 2 ^ 7 by norm_num, pow_mul, pow_two,
      h7]
  have hKP : K.K ≤ P := hK2.le_sylow_of_normal P
  have hDP : Subgroup.closure {K.uv, K.t, K.u} ≤ P := le_sup_right.trans hTP
  have hK128 : Nat.card K.K ≤ 2 ^ 7 := by
    have h8 := (card_sup_dElt_ge K (B := K.K) fun d hd => dElt_mem_K_eq_zero K hd).trans
      (Subgroup.card_le_of_le (sup_le hKP hDP))
    have hPle : Nat.card P ≤ 2 ^ 10 := Nat.le_of_dvd (by norm_num) hP
    omega
  have hPTK : (P : Subgroup X) ≤ (K.A ⊔ Subgroup.closure {K.uv, K.t, K.u}) ⊔ K.K := by
    intro g hg
    have h2 : ∀ h ∈ (P : Subgroup X), ∃ n : ℕ, h ^ 2 ^ n = 1 := fun h hh => by
      obtain ⟨n, hn⟩ := P.isPGroup' ⟨h, hh⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    obtain ⟨τ, hτ, hgτ⟩ := K.exists_mul_mem_K (h2 g hg) (h2 _ (mul_mem hg (hTP K.u_mem_T)))
    rw [show g = g * τ * τ⁻¹ by group]
    exact mul_mem (Subgroup.mem_sup_right hgτ) (Subgroup.mem_sup_left (inv_mem hτ))
  by_cases hKC : K.K ≤ C
  · refine le_antisymm (hPTK.trans (sup_le (sup_le (hAC.trans le_sup_left) le_sup_right)
      (hKC.trans le_sup_left))) (sup_le hCP hDP)
  exfalso
  obtain ⟨k₀, hk₀, hk₀C⟩ := SetLike.not_le_iff_exists.mp hKC
  have hidx : (C.subgroupOf K.K).index = 2 := by
    have h1 := (C.subgroupOf K.K).card_mul_index
    rw [show Nat.card (C.subgroupOf K.K) = Nat.card C from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCK).toEquiv] at h1
    have h3 : (C.subgroupOf K.K).index ≠ 1 := fun h =>
      hKC (Subgroup.subgroupOf_eq_top.mp (Subgroup.index_eq_one.mp h))
    have h0 : (C.subgroupOf K.K).index ≠ 0 := fun h => by
      rw [h, mul_zero] at h1
      exact (Nat.card_pos (α := K.K)).ne' h1.symm
    by_contra h4
    have h5 : 3 ≤ (C.subgroupOf K.K).index := by omega
    have := Nat.mul_le_mul hC64 h5
    omega
  have hcoset : ∀ k ∈ K.K, k ∉ C → k₀⁻¹ * k ∈ C := by
    intro k hk hkC
    have h := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨k₀, hk₀⟩ : K.K)⁻¹)
      (b := ⟨k, hk⟩)).mpr (by
        simp only [Subgroup.mem_subgroupOf, InvMemClass.coe_inv, inv_mem_iff]
        exact iff_of_false hk₀C hkC)
    simpa [Subgroup.mem_subgroupOf] using h
  have hρ3 : K.ρ * K.ρ * K.ρ = 1 := rho_cube_eq_one K hρodd (n := 7) (by rw [hCA]; exact hC)
  have hρk : K.ρ⁻¹ * k₀ * K.ρ ∈ K.K := K.conj_mem_K hk₀ K.ρ
  have hρkC : K.ρ⁻¹ * k₀ * K.ρ ∉ C := fun h => hk₀C (by
    have := hCn.conj_mem _ h K.ρ
    rwa [show K.ρ * (K.ρ⁻¹ * k₀ * K.ρ) * K.ρ⁻¹ = k₀ by group] at this)
  obtain ⟨n, hnC, hn⟩ : ∃ n ∈ C, K.ρ⁻¹ * k₀ * K.ρ = k₀ * n :=
    ⟨_, hcoset _ hρk hρkC, by group⟩
  have hstep : ∀ m, K.ρ⁻¹ * (k₀ * m) * K.ρ = k₀ * (n * (K.ρ⁻¹ * m * K.ρ)) := fun m => by
    calc K.ρ⁻¹ * (k₀ * m) * K.ρ = (K.ρ⁻¹ * k₀ * K.ρ) * (K.ρ⁻¹ * m * K.ρ) := by group
      _ = _ := by rw [hn, mul_assoc]
  have hnorm : n * (K.ρ⁻¹ * (n * (K.ρ⁻¹ * n * K.ρ)) * K.ρ) = 1 := by
    have h1 : K.ρ⁻¹ * (K.ρ⁻¹ * (K.ρ⁻¹ * k₀ * K.ρ) * K.ρ) * K.ρ = k₀ := by
      calc _ = (K.ρ * K.ρ * K.ρ)⁻¹ * k₀ * (K.ρ * K.ρ * K.ρ) := by group
        _ = k₀ := by rw [hρ3]; group
    rw [hn, hstep, hstep] at h1
    exact mul_left_cancel (h1.trans (mul_one k₀).symm)
  obtain ⟨s, hsK, hsC, hρs⟩ : ∃ s ∈ K.K, s ∉ C ∧ K.ρ⁻¹ * s * K.ρ = s := by
    rcases hCcases n hnC with ⟨vr, rfl⟩ | ⟨vr, rfl⟩
    · have h0 : vr + fρ vr + fρ (fρ vr) = 0 := by
        rw [K.conj_ρ_ev, ← K.ev_add, K.conj_ρ_ev, ← K.ev_add, K.ev_eq_one_iff, fρ_add,
          ← add_assoc] at hnorm
        exact hnorm
      obtain ⟨c', hc'⟩ := exists_fix_of_norm vr h0
      refine ⟨k₀ * K.ev c', mul_mem hk₀ (K.A_le_K (K.ev_mem c')), fun h => hk₀C ?_, ?_⟩
      · have := C.mul_mem h (C.inv_mem (hAC (K.ev_mem c')))
        rwa [mul_inv_cancel_right] at this
      · rw [hstep, K.conj_ρ_ev, ← K.ev_add, ← hc']
    · exfalso
      apply hcA
      rw [hρcA, hcc, K.conj_ρ_ev, mul_assoc, ← K.ev_add] at hnorm
      rw [eq_inv_of_mul_eq_one_left hnorm]
      exact K.A.inv_mem (K.ev_mem _)
  have huvK : K.uv⁻¹ * s * K.uv ∈ K.K := K.conj_mem_K hsK K.uv
  have huvC : K.uv⁻¹ * s * K.uv ∉ C := fun h => hsC (by
    have := hCn.conj_mem _ h K.uv
    rwa [show K.uv * (K.uv⁻¹ * s * K.uv) * K.uv⁻¹ = s by group] at this)
  have hn1 : s⁻¹ * K.uv * s * K.uv⁻¹ ∈ C := by
    have h1 := C.mul_mem (C.inv_mem (hcoset _ hsK hsC)) (hcoset _ huvK huvC)
    have h2 := hCn.conj_mem _ (C.inv_mem h1) K.uv
    rwa [show K.uv * ((k₀⁻¹ * s)⁻¹ * (k₀⁻¹ * (K.uv⁻¹ * s * K.uv)))⁻¹ * K.uv⁻¹ =
      s⁻¹ * K.uv * s * K.uv⁻¹ by group] at h2
  rcases hCcases _ hn1 with ⟨va, hva0⟩ | ⟨v, hv⟩
  swap
  ·
    have h1 : (s⁻¹ * K.uv * s * K.uv⁻¹) * K.uv * ((s⁻¹ * K.uv * s * K.uv⁻¹) * K.uv) = 1 := by
      calc _ = s⁻¹ * (K.uv * K.uv) * s := by group
        _ = 1 := by rw [uv_mul_self K]; group
    rw [hv] at h1
    have h2 : K.uv * (c * K.ev v) * K.uv = c * K.ev (δ₁ + fuv v) := by
      calc K.uv * (c * K.ev v) * K.uv = K.uv⁻¹ * (c * K.ev v) * K.uv := by rw [uv_inv K]
        _ = (K.uv⁻¹ * c * K.uv) * (K.uv⁻¹ * K.ev v * K.uv) := by group
        _ = c * K.ev (δ₁ + fuv v) := by rw [huvc, K.conj_uv_ev, mul_assoc, K.ev_add]
    rw [show c * K.ev v * K.uv * (c * K.ev v * K.uv) =
      c * K.ev v * (K.uv * (c * K.ev v) * K.uv) by group, h2, hcc, K.ev_eq_one_iff] at h1
    exact co_w_add_fuv_ne_zero v δ₁ hδ h1
  have hva : s⁻¹ * K.uv * s = K.ev va * K.uv := by rw [← hva0]; group
  have hvd := K.transl_t_of_comm hρs hva
  have hrt : fρ (fρ va) = va + fuv (fρ va) := by
    have h1 : s⁻¹ * (K.ρ⁻¹ * K.t * K.ρ) * s = K.ev (fρ (fρ va)) * (K.uv * K.t) := by
      rw [K.conj_comm_ρ hρs, hvd, K.ρ_conj_ev_mul, K.hρt]
    rw [K.hρt, Config.conj_mul_eq, hva, hvd, K.ev_mul_ev_mul, K.act_uv_inv] at h1
    exact (K.ev_cancel h1).symm
  rcases hfin va hrt with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ | ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  · have hN := K.mem_normalizer_E hsK (a := a) (b := b) (by rw [hva, ha]) (by rw [hvd, hb])
    exact hsC (hAC (mem_A_of_mem_Tsub_of_mem_K K (hE s (hKP hsK) hN) hsK))
  · have hscK : s * c ∈ K.K := mul_mem hsK (hCK hcC)
    have hcv : ∀ v, c⁻¹ * K.ev v * c = K.ev v := fun v => by
      rw [mul_assoc, ← hcom, inv_mul_cancel_left]
    have hcuv : c⁻¹ * K.uv * c = K.ev δ₁ * K.uv := by
      calc c⁻¹ * K.uv * c = c⁻¹ * (K.uv⁻¹ * c * K.uv) * K.uv⁻¹ := by
            conv_lhs => rw [← uv_inv K]
            group
        _ = K.ev δ₁ * K.uv := by rw [huvc, uv_inv K]; group
    have hct : c⁻¹ * K.t * c = K.ev δ₂ * K.t := by
      calc c⁻¹ * K.t * c = c⁻¹ * (K.t⁻¹ * c * K.t) * K.t⁻¹ := by
            conv_lhs => rw [← t_inv K]
            group
        _ = K.ev δ₂ * K.t := by rw [htc, t_inv K]; group
    have h1 : (s * c)⁻¹ * K.uv * (s * c) = K.ev (2 • a) * K.uv := by
      calc (s * c)⁻¹ * K.uv * (s * c) = (c⁻¹ * K.ev va * c) * (c⁻¹ * K.uv * c) := by
            rw [show (s * c)⁻¹ * K.uv * (s * c) = c⁻¹ * (s⁻¹ * K.uv * s) * c by group, hva]
            group
        _ = K.ev (2 • a) * K.uv := by rw [hcv, hcuv, ← mul_assoc, ← K.ev_add, ha]
    have h2 : (s * c)⁻¹ * K.t * (s * c) = K.ev (2 • b) * K.t := by
      calc (s * c)⁻¹ * K.t * (s * c) = (c⁻¹ * K.ev (fρ va) * c) * (c⁻¹ * K.t * c) := by
            rw [show (s * c)⁻¹ * K.t * (s * c) = c⁻¹ * (s⁻¹ * K.t * s) * c by group, hvd]
            group
        _ = K.ev (2 • b) * K.t := by rw [hcv, hct, ← mul_assoc, ← K.ev_add, hb]
    have hA := mem_A_of_mem_Tsub_of_mem_K K (hE _ (hKP hscK) (K.mem_normalizer_E hscK h1 h2)) hscK
    exact hsC (by
      have := C.mul_mem (hAC hA) (C.inv_mem hcC)
      rwa [mul_inv_cancel_right] at this)

theorem arch76Lemma2_index_two (hρodd : Odd (orderOf K.ρ)) {C : Subgroup X}
    (hCA : Subgroup.centralizer (K.A : Set X) = C) (hC : Nat.card C ∣ 2 ^ 7) (hne : C ≠ K.A)
    (P : Sylow 2 X) (hTP : K.A ⊔ Subgroup.closure {K.uv, K.t, K.u} ≤ P)
    (hP : Nat.card P ∣ 2 ^ 10)
    (hE : ∀ g ∈ (P : Subgroup X), g ∈ Subgroup.normalizer
      ((Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} : Subgroup X) : Set X) →
        g ∈ K.A ⊔ Subgroup.closure {K.uv, K.t, K.u})
    {c : X} (hCc : C = Subgroup.closure {c, K.x, K.y}) (hc2 : c ^ 2 = K.w)
    (hcase : (K.uv⁻¹ * c * K.uv = c * K.x⁻¹ * K.y⁻¹ ∧ K.t⁻¹ * c * K.t = c * K.x ∧
        K.u⁻¹ * c * K.u = c ∧ K.ρ⁻¹ * c * K.ρ = c) ∨
      (K.uv⁻¹ * c * K.uv = c * K.x * K.y⁻¹ ∧ K.t⁻¹ * c * K.t = c * K.x * K.y ^ 2 ∧
        K.u⁻¹ * c * K.u = c⁻¹ ∧ K.ρ⁻¹ * c * K.ρ = c)) :
    (P : Subgroup X) = C ⊔ Subgroup.closure {K.uv, K.t, K.u} := by
  rcases hcase with ⟨huv, ht, -, hρ⟩ | ⟨huv, ht, -, hρ⟩
  · exact arch76Lemma2_index_two_core K hρodd hCA hC hne P hTP hP hE hCc hc2
      (δ₁ := (0, 3, 3)) (δ₂ := (0, 1, 0)) (by rw [huv, K.ev_033, mul_assoc])
      (by rw [ht, K.ev_x]) hρ rfl transl_uv_cases3
  · exact arch76Lemma2_index_two_core K hρodd hCA hC hne P hTP hP hE hCc hc2
      (δ₁ := (0, 1, 3)) (δ₂ := (0, 1, 2)) (by rw [huv, ev_x_mul_y_inv, mul_assoc])
      (by rw [ht, K.ev_012, mul_assoc]) hρ rfl transl_uv_cases4

end CFSG.CGT.Stroth76

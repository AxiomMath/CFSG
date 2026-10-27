module

public import CFSG.GH74.GLS.C3.Layer1.Th2A7ExcAlphaSetup
public import CFSG.GH74.GLS.C3.Layer1.Th2A7ExcAlphaChain

public section

namespace CFSG.GH74.GLS.Th2.AlphaStep

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer1.Bk CFSG.GH74.GLS.C3.Layer1.Back
  CFSG.GH74.GLS.C3.Layer1.U1a Equiv Equiv.Perm CFSG.LieType.SteinbergBR.SmallAlt
  CFSG.GH74.GLS.Th2.P43f

variable {G : Type} [Group G] {x z a : G} {K T : Subgroup G} {psi : G → Perm (Fin 7)}

theorem AlphaSetup.psi_ne_z (A : AlphaSetup x K T a z psi)
    (hα : T ⊓ CxK x K ≤ (T ⊓ K).map (MulAut.conj a).toMonoidHom)
    {v : G} (hv : v ∈ (T ⊓ K).map (MulAut.conj a).toMonoidHom) : psi v ≠ a7P 1 := by
  intro h
  have hvT : v ∈ T := A.Pa_le hv
  have hvC := A.T_le_C hvT
  have hzC := A.T_le_C A.z_mem.1
  have h11 : a7P 1 * a7P 1 = 1 := by decide
  have h1 : psi (v * z) = 1 := by
    rw [A.psiD.mul v hvC z hzC, h, A.psi_z, h11]
  have hvz : v * z ∈ CxK x K := (A.psi_ker _ ((centralizer ({x} : Set G)).mul_mem hvC hzC)).1 h1
  have hvzQ : v * z ∈ T ⊓ CxK x K := ⟨T.mul_mem hvT A.z_mem.1, hvz⟩
  have hvzP := hα hvzQ
  have hzPa : z ∈ (T ⊓ K).map (MulAut.conj a).toMonoidHom := by
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hv) hvzP
    simpa using this
  have hz1 : z ∈ (T ⊓ K) ⊓ (T ⊓ K).map (MulAut.conj a).toMonoidHom := ⟨A.z_mem, hzPa⟩
  rw [A.disj, Subgroup.mem_bot] at hz1
  exact A.z_ne hz1

theorem AlphaSetup.psi_refl (A : AlphaSetup x K T a z psi)
    (hα : T ⊓ CxK x K ≤ (T ⊓ K).map (MulAut.conj a).toMonoidHom)
    {u : G} (hu : u ∈ (T ⊓ K).map (MulAut.conj a).toMonoidHom) (huu : u * u = 1) (hu1 : u ≠ 1)
    (hux : u ≠ x) : psi u = swap 5 6 ∨ psi u = a7P 1 * swap 5 6 := by
  have huT : u ∈ T := A.Pa_le hu
  have huC := A.T_le_C huT
  have hcomm : ∀ k : Fin 8, psi u * a7P k = a7P k * psi u := by
    intro k
    obtain ⟨w, hw, hwk⟩ := A.psi_P_surj k
    have hwC := A.T_le_C hw.1
    rw [← hwk, ← A.psiD.mul u huC w hwC, ← A.psiD.mul w hwC u huC, A.comm w hw u hu]
  rcases cent_a7P (psi u) hcomm with h | h | h | h
  · exfalso
    have hmem : u ∈ CxK x K := (A.psi_ker u huC).1 h
    rcases A.Q_invol u ⟨huT, hmem⟩ huu with h1 | h1
    · exact hu1 h1
    · exact hux h1
  · exact absurd h (A.psi_ne_z hα hu)
  · exact Or.inl h
  · exact Or.inr h

theorem AlphaSetup.psi_refl_eq (A : AlphaSetup x K T a z psi)
    (hα : T ⊓ CxK x K ≤ (T ⊓ K).map (MulAut.conj a).toMonoidHom)
    {u u' : G} (hu : u ∈ (T ⊓ K).map (MulAut.conj a).toMonoidHom) (huu : u * u = 1) (hu1 : u ≠ 1)
    (hux : u ≠ x) (hu' : u' ∈ (T ⊓ K).map (MulAut.conj a).toMonoidHom) (huu' : u' * u' = 1)
    (hu1' : u' ≠ 1) (hux' : u' ≠ x) : psi u = psi u' := by
  have huC := A.T_le_C (A.Pa_le hu)
  have hu'C := A.T_le_C (A.Pa_le hu')
  have hvPa : u * u'⁻¹ ∈ (T ⊓ K).map (MulAut.conj a).toMonoidHom :=
    Subgroup.mul_mem _ hu (Subgroup.inv_mem _ hu')
  have hpv : psi (u * u'⁻¹) = psi u * (psi u')⁻¹ := by
    rw [A.psiD.mul u huC u'⁻¹ ((centralizer ({x} : Set G)).inv_mem hu'C), A.psiD.inv hu'C]
  rcases A.psi_refl hα hu huu hu1 hux with h | h <;>
    rcases A.psi_refl hα hu' huu' hu1' hux' with h' | h'
  · rw [h, h']
  · exfalso
    apply A.psi_ne_z hα hvPa
    rw [hpv, h, h']
    decide
  · exfalso
    apply A.psi_ne_z hα hvPa
    rw [hpv, h, h']
    decide
  · rw [h, h']

theorem AlphaSetup.conj_inv_mem (A : AlphaSetup x K T a z psi) {s : G} (hs : s ∈ T ⊓ K) :
    a⁻¹ * s * a ∈ (T ⊓ K).map (MulAut.conj a).toMonoidHom := by
  have haa : a * a ∈ (T ⊓ K) ⊔ (T ⊓ K).map (MulAut.conj a).toMonoidHom := by
    rw [← A.T_eq]; exact A.haa
  obtain ⟨u₁, hu₁, u₂, hu₂, hdec⟩ := mem_sup_of_commute A.comm haa
  have hf₁ : a * s * a⁻¹ ∈ (T ⊓ K).map (MulAut.conj a).toMonoidHom :=
    Subgroup.mem_map.2 ⟨s, hs, by simp [MulAut.conj_apply]⟩
  have hc : u₁ * (a * s * a⁻¹) = (a * s * a⁻¹) * u₁ := A.comm u₁ hu₁ _ hf₁
  have h1 : a⁻¹ * s * a = u₂⁻¹ * (a * s * a⁻¹) * u₂ := by
    calc a⁻¹ * s * a = (a * a)⁻¹ * (a * s * a⁻¹) * (a * a) := by group
      _ = (u₁ * u₂)⁻¹ * (a * s * a⁻¹) * (u₁ * u₂) := by rw [hdec]
      _ = u₂⁻¹ * (u₁⁻¹ * (a * s * a⁻¹) * u₁) * u₂ := by group
      _ = u₂⁻¹ * (a * s * a⁻¹) * u₂ := by
        have : u₁⁻¹ * (a * s * a⁻¹) * u₁ = a * s * a⁻¹ := by
          calc u₁⁻¹ * (a * s * a⁻¹) * u₁ = u₁⁻¹ * ((a * s * a⁻¹) * u₁) := by group
            _ = u₁⁻¹ * (u₁ * (a * s * a⁻¹)) := by rw [hc]
            _ = a * s * a⁻¹ := by group
        rw [this]
  rw [h1]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hu₂) hf₁) hu₂

theorem AlphaSetup.exists_invol (A : AlphaSetup x K T a z psi) {i : Fin 8}
    (hi : i = 2 ∨ i = 3 ∨ i = 6 ∨ i = 7) :
    ∃ p ∈ T ⊓ K, psi p = a7P i ∧ p * p = 1 ∧ p ≠ z ∧ p ≠ 1 := by
  obtain ⟨p, hp, hpi⟩ := A.psi_P_surj i
  have hsq : a7P i * a7P i = 1 := by rcases hi with rfl | rfl | rfl | rfl <;> decide
  have hne1 : a7P i ≠ a7P 1 := by rcases hi with rfl | rfl | rfl | rfl <;> decide
  have hne0 : a7P i ≠ 1 := by rcases hi with rfl | rfl | rfl | rfl <;> decide
  refine ⟨p, hp, hpi, A.P_inv p hp (by rw [hpi]; exact hsq), ?_, ?_⟩
  · intro h
    apply hne1
    rw [← hpi, h, A.psi_z]
  · intro h
    apply hne0
    rw [← hpi, h, A.psiD.one]

theorem AlphaSetup.alpha_conj_x_v (A : AlphaSetup x K T a z psi) {τ₀ : Perm (Fin 7)}
    (hτ₀ : ∀ u ∈ (T ⊓ K).map (MulAut.conj a).toMonoidHom, u * u = 1 → u ≠ 1 → u ≠ x →
      psi u = τ₀)
    (hτsq : τ₀ * τ₀ = 1) (hτc : ∀ k : Fin 8, τ₀ * a7P k = a7P k * τ₀) {i j : Fin 8}
    (hi : i = 2 ∨ i = 3 ∨ i = 6 ∨ i = 7) (hj : j = 2 ∨ j = 3 ∨ j = 6 ∨ j = 7)
    (hc1 : (a7P j * τ₀).support.card = τ₀.support.card)
    (hc2 : (a7P 1 * τ₀).support.card = (a7P i * τ₀).support.card) :
    ∃ g : G, g * x * g⁻¹ = z * x := by
  obtain ⟨p₁, hp₁P, hp₁i, hp₁p₁, hp₁z, hp₁1⟩ := A.exists_invol hi
  obtain ⟨s, hsP, hsj, hss, hsz, hs1⟩ := A.exists_invol hj
  have hfPa : a * p₁ * a⁻¹ ∈ (T ⊓ K).map (MulAut.conj a).toMonoidHom :=
    Subgroup.mem_map.2 ⟨p₁, hp₁P, by simp [MulAut.conj_apply]⟩
  have hf'Pa : a⁻¹ * s * a ∈ (T ⊓ K).map (MulAut.conj a).toMonoidHom := A.conj_inv_mem hsP
  have hff : (a * p₁ * a⁻¹) * (a * p₁ * a⁻¹) = 1 := by
    calc (a * p₁ * a⁻¹) * (a * p₁ * a⁻¹) = a * (p₁ * p₁) * a⁻¹ := by group
      _ = 1 := by rw [hp₁p₁]; group
  have hf'f' : (a⁻¹ * s * a) * (a⁻¹ * s * a) = 1 := by
    calc (a⁻¹ * s * a) * (a⁻¹ * s * a) = a⁻¹ * (s * s) * a := by group
      _ = 1 := by rw [hss]; group
  have hf1 : a * p₁ * a⁻¹ ≠ 1 := by
    intro h
    apply hp₁1
    calc p₁ = a⁻¹ * (a * p₁ * a⁻¹) * a := by group
      _ = 1 := by rw [h]; group
  have hf'1 : a⁻¹ * s * a ≠ 1 := by
    intro h
    apply hs1
    calc s = a * (a⁻¹ * s * a) * a⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hfx : a * p₁ * a⁻¹ ≠ x := by
    intro h
    apply hp₁z
    calc p₁ = a⁻¹ * (a * p₁ * a⁻¹) * a := by group
      _ = a⁻¹ * x * a := by rw [h]
      _ = z := by rw [← A.hxz]; group
  have hf'x : a⁻¹ * s * a ≠ x := by
    intro h
    apply hsz
    calc s = a * (a⁻¹ * s * a) * a⁻¹ := by group
      _ = a * x * a⁻¹ := by rw [h]
      _ = z := A.hxa
  have hCx : x ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 rfl
  refine ChainData.exists_conj_x_v (C := centralizer ({x} : Set G)) (K := K) (psi := psi)
    (x := x) (z := z) (a := a) (p₁ := p₁) (s := s) (f := a * p₁ * a⁻¹) (f' := a⁻¹ * s * a)
    (i := i) (j := j) (τ₀ := τ₀) ?_
  exact
    { psiD := A.psiD
      hxC := hCx
      hxx := A.x_sq
      hxK := fun k hk => mem_centralizer_singleton_iff.1 (A.psiD.K_le hk)
      hz := A.z_mem.2
      hzz := A.z_sq
      hzx := mem_centralizer_singleton_iff.1 (A.T_le_C A.z_mem.1)
      hxz := A.hxz
      hp₁ := hp₁P.2
      hp₁p₁ := hp₁p₁
      hs := hsP.2
      hss := hss
      hzp₁ := A.z_central p₁ hp₁P.1
      hzs := A.z_central s hsP.1
      hfa := by group
      hfa' := by group
      hf := A.T_le_C (A.Pa_le hfPa)
      hf' := A.T_le_C (A.Pa_le hf'Pa)
      hsf := A.comm s hsP _ hfPa
      hp₁f' := A.comm p₁ hp₁P _ hf'Pa
      hzf' := A.comm z A.z_mem _ hf'Pa
      psi_z := A.psi_z
      psi_x := A.psi_x
      psi_p₁ := hp₁i
      psi_s := hsj
      psi_f := hτ₀ _ hfPa hff hf1 hfx
      psi_f' := hτ₀ _ hf'Pa hf'f' hf'1 hf'x
      hi := hi
      hj := hj
      τ₀_sq := hτsq
      τ₀_comm := hτc
      card1 := hc1
      card2 := hc2 }

theorem AlphaSetup.exists_conj_x_v (A : AlphaSetup x K T a z psi)
    (hα : T ⊓ CxK x K ≤ (T ⊓ K).map (MulAut.conj a).toMonoidHom) :
    ∃ g : G, g * x * g⁻¹ = z * x := by
  obtain ⟨p, hp, hpi, hpp, hpz, hp1⟩ := A.exists_invol (i := 2) (Or.inl rfl)
  have hfPa : a * p * a⁻¹ ∈ (T ⊓ K).map (MulAut.conj a).toMonoidHom :=
    Subgroup.mem_map.2 ⟨p, hp, by simp [MulAut.conj_apply]⟩
  have hff : (a * p * a⁻¹) * (a * p * a⁻¹) = 1 := by
    calc (a * p * a⁻¹) * (a * p * a⁻¹) = a * (p * p) * a⁻¹ := by group
      _ = 1 := by rw [hpp]; group
  have hf1 : a * p * a⁻¹ ≠ 1 := by
    intro h
    apply hp1
    calc p = a⁻¹ * (a * p * a⁻¹) * a := by group
      _ = 1 := by rw [h]; group
  have hfx : a * p * a⁻¹ ≠ x := by
    intro h
    apply hpz
    calc p = a⁻¹ * (a * p * a⁻¹) * a := by group
      _ = a⁻¹ * x * a := by rw [h]
      _ = z := by rw [← A.hxz]; group
  have huniq : ∀ u ∈ (T ⊓ K).map (MulAut.conj a).toMonoidHom, u * u = 1 → u ≠ 1 → u ≠ x →
      psi u = psi (a * p * a⁻¹) := fun u hu huu hu1 hux =>
    A.psi_refl_eq hα hu huu hu1 hux hfPa hff hf1 hfx
  have hτ₀sq : ∀ τ₀ : Perm (Fin 7), (τ₀ = swap 5 6 ∨ τ₀ = a7P 1 * swap 5 6) → τ₀ * τ₀ = 1 := by
    rintro τ₀ (rfl | rfl) <;> decide
  have hτ₀c : ∀ τ₀ : Perm (Fin 7), (τ₀ = swap 5 6 ∨ τ₀ = a7P 1 * swap 5 6) →
      ∀ k : Fin 8, τ₀ * a7P k = a7P k * τ₀ := by
    rintro τ₀ (rfl | rfl) <;> decide
  rcases A.psi_refl hα hfPa hff hf1 hfx with h | h
  · exact A.alpha_conj_x_v (τ₀ := psi (a * p * a⁻¹)) huniq (hτ₀sq _ (Or.inl h))
      (hτ₀c _ (Or.inl h)) (i := 2) (j := 6) (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl)))
      (by rw [h]; decide) (by rw [h]; decide)
  · exact A.alpha_conj_x_v (τ₀ := psi (a * p * a⁻¹)) huniq (hτ₀sq _ (Or.inr h))
      (hτ₀c _ (Or.inr h)) (i := 6) (j := 2) (Or.inr (Or.inr (Or.inl rfl))) (Or.inl rfl)
      (by rw [h]; decide) (by rw [h]; decide)

theorem false_of_conj_x_v [Finite G] {x v : G} {T S : Subgroup G}
    (hTC : IsSylowOf 2 T (centralizer ({x} : Set G))) (hS : IsSylowOf 2 S ⊤) (hTS : T < S)
    {g : G} (hg : g * x * g⁻¹ = v) (hSv : S ≤ centralizer ({v} : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH : S.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer ({x} : Set G) := by
    intro y hy
    obtain ⟨s, hsS, rfl⟩ := Subgroup.mem_map.1 hy
    have h := mem_centralizer_singleton_iff.1 (hSv hsS)
    rw [← hg] at h
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g⁻¹ * s * g⁻¹⁻¹ * x = g⁻¹ * (s * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * s) * g := by rw [h]
      _ = x * (g⁻¹ * s * g⁻¹⁻¹) := by group
  have hcardH : Nat.card (S.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card S :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hdvd : Nat.card S ∣ Nat.card (centralizer ({x} : Set G)) := by
    rw [← hcardH]
    exact Subgroup.card_dvd_of_le hH
  have hSc := hS.card_eq
  have hTc := hTC.card_eq
  have hle : Nat.card S ≤ Nat.card T := by
    rw [hSc, hTc]
    apply Nat.pow_le_pow_right (by norm_num)
    have h2 : 2 ^ (Nat.card (⊤ : Subgroup G)).factorization 2 ∣
        Nat.card (centralizer ({x} : Set G)) := by
      rw [← hSc]; exact hdvd
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 h2
  exact hTS.ne (Subgroup.eq_of_le_of_card_ge hTS.le hle)

end CFSG.GH74.GLS.Th2.AlphaStep

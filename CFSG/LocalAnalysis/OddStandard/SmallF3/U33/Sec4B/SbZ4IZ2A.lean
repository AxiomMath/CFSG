module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IZ0B

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

@[expose] def z4iF (K : Subgroup H) (t τ : H) : Subgroup H := K ⊔ closure {t, τ}

@[expose] def z4iK1 (K : Subgroup H) (τ : H) : Subgroup H := K ⊔ zpowers τ

namespace ZEData

variable {Q Y V V' B K : Subgroup H} {ρ t τ l : H}

private lemma z4i_pow_add_fin {G : Type*} [Group G] (x : G) (hx : x * x = 1)
    (a a' : Fin 2) : x ^ (a : ℕ) * x ^ (a' : ℕ) = x ^ ((a + a' : Fin 2) : ℕ) := by
  rw [← pow_add, pow_eq_pow_mod (n := 2) ((a : ℕ) + (a' : ℕ))
      (by simpa [pow_two] using hx), ← Fin.val_add]

private lemma z4i_mul_pair_comm {G : Type*} [Group G] {a₁ a₂ b₁ b₂ : G}
    (h : Commute a₂ b₁) : a₁ * a₂ * (b₁ * b₂) = (a₁ * b₁) * (a₂ * b₂) := by
  calc a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
    _ = a₁ * (b₁ * a₂) * b₂ := by rw [h.eq]
    _ = (a₁ * b₁) * (a₂ * b₂) := by group

private lemma mem_closure_pair_iff (h : ZEData Q Y V V' B K ρ t τ l) {x : H} :
    x ∈ closure ({t, τ} : Set H) ↔ ∃ a b : Fin 2, x = t ^ (a : ℕ) * τ ^ (b : ℕ) := by
  let W : Subgroup H :=
    { carrier := {x | ∃ a b : Fin 2, x = t ^ (a : ℕ) * τ ^ (b : ℕ)}
      one_mem' := ⟨0, 0, by simp⟩
      mul_mem' := by
        rintro x y ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
        exact ⟨a + a', b + b', by
          rw [z4i_mul_pair_comm ((show Commute τ t from h.t_tau.symm).pow_pow b a'),
            z4i_pow_add_fin t h.t_sq a a', z4i_pow_add_fin τ h.tau_sq b b']⟩
      inv_mem' := by
        rintro x ⟨a, b, rfl⟩
        exact ⟨a, b, by
          rw [mul_inv_rev, ← inv_pow, ← inv_pow,
            inv_eq_of_mul_eq_one_right h.t_sq, inv_eq_of_mul_eq_one_right h.tau_sq]
          exact ((show Commute τ t from h.t_tau.symm).pow_pow b a).eq⟩ }
  constructor
  · intro hx
    refine (Subgroup.closure_le (k := ({t, τ} : Set H)) W).mpr ?_ hx
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  · rintro ⟨a, b, rfl⟩
    have ht : t ∈ closure ({t, τ} : Set H) := Subgroup.subset_closure (by simp)
    have hτ : τ ∈ closure ({t, τ} : Set H) := Subgroup.subset_closure (by simp)
    exact (closure ({t, τ} : Set H)).mul_mem
      ((closure ({t, τ} : Set H)).pow_mem ht a) ((closure ({t, τ} : Set H)).pow_mem hτ b)

private lemma mem_zpowers_tau_iff (h : ZEData Q Y V V' B K ρ t τ l) {x : H} :
    x ∈ zpowers τ ↔ ∃ b : Fin 2, x = τ ^ (b : ℕ) := by
  let W : Subgroup H :=
    { carrier := {x | ∃ b : Fin 2, x = τ ^ (b : ℕ)}
      one_mem' := ⟨0, by simp⟩
      mul_mem' := by
        rintro x y ⟨b, rfl⟩ ⟨b', rfl⟩
        exact ⟨b + b', by rw [z4i_pow_add_fin τ h.tau_sq b b']⟩
      inv_mem' := by
        rintro x ⟨b, rfl⟩
        exact ⟨b, by rw [← inv_pow, inv_eq_of_mul_eq_one_right h.tau_sq]⟩ }
  constructor
  · intro hx
    rw [Subgroup.zpowers_eq_closure] at hx
    refine (Subgroup.closure_le (k := ({τ} : Set H)) W).mpr ?_ hx
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact ⟨1, by simp⟩
  · rintro ⟨b, rfl⟩
    exact (zpowers τ).pow_mem (Subgroup.mem_zpowers τ) b

private lemma mem_normalizer_of_sq (h : ZEData Q Y V V' B K ρ t τ l) {g : H}
    (hg2 : g * g = 1) (hnorm : ∀ k ∈ K, g * k * g⁻¹ ∈ K) :
    g ∈ Subgroup.normalizer (K : Set H) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro k
  constructor
  · exact hnorm k
  · intro hk
    have hconj : g * (g * k * g⁻¹) * g⁻¹ = k := by
      calc g * (g * k * g⁻¹) * g⁻¹ = (g * g) * k * (g * g)⁻¹ := by group
        _ = k := by rw [hg2]; simp
    have hk' : g * (g * k * g⁻¹) * g⁻¹ ∈ K := hnorm (g * k * g⁻¹) hk
    rwa [hconj] at hk'

private lemma t_mem_normalizer (h : ZEData Q Y V V' B K ρ t τ l) :
    t ∈ Subgroup.normalizer (K : Set H) :=
  mem_normalizer_of_sq h h.t_sq h.t_norm_K

private lemma tau_mem_normalizer (h : ZEData Q Y V V' B K ρ t τ l) :
    τ ∈ Subgroup.normalizer (K : Set H) :=
  mem_normalizer_of_sq h h.tau_sq h.tau_norm_K

private lemma T2_norm_K (h : ZEData Q Y V V' B K ρ t τ l) :
    ∀ s ∈ closure ({t, τ} : Set H), ∀ k ∈ K, s * k * s⁻¹ ∈ K := by
  have hle : closure ({t, τ} : Set H) ≤ Subgroup.normalizer (K : Set H) :=
    (Subgroup.closure_le (k := ({t, τ} : Set H)) (Subgroup.normalizer (K : Set H))).mpr
      (by
        intro g hg
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        rcases hg with rfl | rfl
        · exact t_mem_normalizer h
        · exact tau_mem_normalizer h)
  intro s hs k hk
  exact ((Subgroup.mem_set_normalizer_iff (S := (K : Set H))).mp (hle hs) k).mp hk

private lemma zpowers_tau_norm_K (h : ZEData Q Y V V' B K ρ t τ l) :
    ∀ s ∈ zpowers τ, ∀ k ∈ K, s * k * s⁻¹ ∈ K := by
  have hle : zpowers τ ≤ Subgroup.normalizer (K : Set H) :=
    Subgroup.zpowers_le.mpr (tau_mem_normalizer h)
  intro s hs k hk
  exact ((Subgroup.mem_set_normalizer_iff (S := (K : Set H))).mp (hle hs) k).mp hk

theorem tau_cent_Y (h : ZEData Q Y V V' B K ρ t τ l) : ∀ y ∈ Y, τ * y = y * τ := by
  intro y hy
  have h1 : τ * y * τ⁻¹ = y⁻¹ := h.tau_inv y (h.Y_le_Q hy)
  have h2 : y⁻¹ = y := inv_eq_of_mul_eq_one_right (h.Y_sq y hy)
  rw [h2] at h1
  calc τ * y = (τ * y * τ⁻¹) * τ := by group
    _ = y * τ := by rw [h1]

theorem l_not_cent_V (h : ZEData Q Y V V' B K ρ t τ l) : ∃ v ∈ V, l * v ≠ v * l := by
  by_contra hcon
  have hcon' : ∀ v ∈ V, l * v = v * l := by
    intro v hv
    by_contra hvne
    exact hcon ⟨v, hv, hvne⟩
  haveI : Nontrivial V := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro hbot
    have hcardV : Nat.card V = 4 := h.card_V
    rw [hbot, Subgroup.card_bot] at hcardV
    norm_num at hcardV
  obtain ⟨v, hv, hv1⟩ := Subgroup.exists_ne_one_of_nontrivial V
  have hwV : ρ * v * ρ⁻¹ ∈ V := h.rho_norm_V v hv
  have hwcent : l * (ρ * v * ρ⁻¹) * l⁻¹ = ρ * v * ρ⁻¹ := by
    rw [hcon' (ρ * v * ρ⁻¹) hwV]
    group
  have hlv : l * v * l⁻¹ = v := by rw [hcon' v hv]; group
  have hlρ' : l * ρ⁻¹ * l⁻¹ = ρ := by
    calc l * ρ⁻¹ * l⁻¹ = (l * ρ * l⁻¹)⁻¹ := by group
      _ = ρ := by rw [h.l_rho, inv_inv]
  have hexpand : l * (ρ * v * ρ⁻¹) * l⁻¹ = ρ⁻¹ * v * ρ := by
    calc l * (ρ * v * ρ⁻¹) * l⁻¹
        = (l * ρ * l⁻¹) * (l * v * l⁻¹) * (l * ρ⁻¹ * l⁻¹) := by group
      _ = ρ⁻¹ * v * ρ := by rw [h.l_rho, hlv, hlρ']
  have heq : ρ * v * ρ⁻¹ = ρ⁻¹ * v * ρ := by rw [← hexpand, hwcent]
  have hρ3 : ρ * ρ * ρ = 1 := by rw [← pow_three', h.rho_pow_three]
  have h2 : ρ * ρ * v = v * ρ * ρ := by
    calc ρ * ρ * v = ρ * (ρ * v * ρ⁻¹) * ρ := by group
      _ = ρ * (ρ⁻¹ * v * ρ) * ρ := by rw [heq]
      _ = v * ρ * ρ := by group
  have h4 : ρ * ρ * v * ρ = v := by
    calc ρ * ρ * v * ρ = (v * ρ * ρ) * ρ := by rw [h2]
      _ = v := by rw [show v * ρ * ρ * ρ = v * (ρ * ρ * ρ) by group, hρ3, mul_one]
  have hcomm : ρ * v = v * ρ := by
    calc ρ * v = ρ * (ρ * ρ * v * ρ) := by rw [h4]
      _ = v * ρ := by
        rw [show ρ * (ρ * ρ * v * ρ) = ρ * ρ * ρ * v * ρ by group, hρ3, one_mul]
  exact hv1 (h.rho_fpf_Q v (h.toZIKData.V_le_Q hv) (by rw [hcomm]; group))

theorem t_not_cent_Y (h : ZEData Q Y V V' B K ρ t τ l) : ∃ y ∈ Y, t * y ≠ y * t := by
  by_contra hcon
  have hcon' : ∀ y ∈ Y, t * y = y * t := by
    intro y hy
    by_contra hyne
    exact hcon ⟨y, hy, hyne⟩
  have hYV : Y ≤ V := fun y hy => h.Y_cent_t y hy (hcon' y hy)
  have hcard := Subgroup.card_le_of_le hYV
  rw [h.card_Y, h.card_V] at hcard
  omega

theorem mem_F_iff (h : ZEData Q Y V V' B K ρ t τ l) {x : H} :
    x ∈ z4iF K t τ ↔ ∃ k ∈ K, ∃ a b : Fin 2, x = k * t ^ (a : ℕ) * τ ^ (b : ℕ) := by
  have hnorm := T2_norm_K h
  rw [z4iF, mem_sup_iff_of_normalizes (H := K) (K := closure ({t, τ} : Set H)) hnorm]
  constructor
  · rintro ⟨k, hk, s, hs, rfl⟩
    obtain ⟨a, b, rfl⟩ := (mem_closure_pair_iff h).mp hs
    exact ⟨k, hk, a, b, by rw [mul_assoc]⟩
  · rintro ⟨k, hk, a, b, rfl⟩
    exact ⟨k, hk, t ^ (a : ℕ) * τ ^ (b : ℕ), (mem_closure_pair_iff h).mpr ⟨a, b, rfl⟩,
      by rw [mul_assoc]⟩

theorem mem_K1_iff (h : ZEData Q Y V V' B K ρ t τ l) {x : H} :
    x ∈ z4iK1 K τ ↔ ∃ k ∈ K, ∃ b : Fin 2, x = k * τ ^ (b : ℕ) := by
  have hnorm := zpowers_tau_norm_K h
  rw [z4iK1, mem_sup_iff_of_normalizes (H := K) (K := zpowers τ) hnorm]
  constructor
  · rintro ⟨k, hk, s, hs, rfl⟩
    obtain ⟨b, rfl⟩ := (mem_zpowers_tau_iff h).mp hs
    exact ⟨k, hk, b, rfl⟩
  · rintro ⟨k, hk, b, rfl⟩
    exact ⟨k, hk, τ ^ (b : ℕ), (mem_zpowers_tau_iff h).mpr ⟨b, rfl⟩, rfl⟩

theorem F_le_Vc (h : ZEData Q Y V V' B K ρ t τ l) : z4iF K t τ ≤ z4iVc K t τ l := by
  show K ⊔ closure ({t, τ} : Set H) ≤ K ⊔ z4iT3 t τ l
  refine sup_le_sup_left ?_ K
  show closure ({t, τ} : Set H) ≤ closure ({t, τ, l} : Set H)
  refine Subgroup.closure_mono ?_
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
  rcases hg with rfl | rfl <;> simp

theorem K1_le_F (h : ZEData Q Y V V' B K ρ t τ l) : z4iK1 K τ ≤ z4iF K t τ := by
  show K ⊔ zpowers τ ≤ K ⊔ closure ({t, τ} : Set H)
  exact sup_le_sup_left (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))) K

private lemma F_le_cent_V (h : ZEData Q Y V V' B K ρ t τ l) :
    z4iF K t τ ≤ centralizer (V : Set H) := by
  intro x hx
  obtain ⟨k, hk, a, b, rfl⟩ := (mem_F_iff h).mp hx
  have hk' : k ∈ centralizer (V : Set H) :=
    Subgroup.mem_centralizer_iff.mpr
      (fun v hv => (h.K_cent_Y k hk v (h.toZIKData.V_le_Y hv)).symm)
  have ht' : t ∈ centralizer (V : Set H) :=
    Subgroup.mem_centralizer_iff.mpr (fun v hv => (h.V_cent_t v hv).symm)
  have hτ' : τ ∈ centralizer (V : Set H) :=
    Subgroup.mem_centralizer_iff.mpr
          (fun v hv => (tau_cent_Y h v (h.toZIKData.V_le_Y hv)).symm)
  exact (centralizer (V : Set H)).mul_mem
    ((centralizer (V : Set H)).mul_mem hk' ((centralizer (V : Set H)).pow_mem ht' a))
    ((centralizer (V : Set H)).pow_mem hτ' b)

private lemma K1_le_cent_Y (h : ZEData Q Y V V' B K ρ t τ l) :
    z4iK1 K τ ≤ centralizer (Y : Set H) := by
  intro x hx
  obtain ⟨k, hk, b, rfl⟩ := (mem_K1_iff h).mp hx
  have hk' : k ∈ centralizer (Y : Set H) :=
    Subgroup.mem_centralizer_iff.mpr (fun y hy => (h.K_cent_Y k hk y hy).symm)
  have hτ' : τ ∈ centralizer (Y : Set H) :=
    Subgroup.mem_centralizer_iff.mpr (fun y hy => (tau_cent_Y h y hy).symm)
  exact (centralizer (Y : Set H)).mul_mem hk' ((centralizer (Y : Set H)).pow_mem hτ' b)

private lemma lc_cent_of_ttau_lc_cent (h : ZEData Q Y V V' B K ρ t τ l) {a b c : Fin 2}
    (hword : t ^ (a : ℕ) * τ ^ (b : ℕ) * l ^ (c : ℕ) ∈ centralizer (V : Set H)) :
    l ^ (c : ℕ) ∈ centralizer (V : Set H) := by
  have hz : t ^ (a : ℕ) * τ ^ (b : ℕ) ∈ centralizer (V : Set H) :=
    (centralizer (V : Set H)).mul_mem
      ((centralizer (V : Set H)).pow_mem
        (Subgroup.mem_centralizer_iff.mpr (fun v hv => (h.V_cent_t v hv).symm)) a)
      ((centralizer (V : Set H)).pow_mem
        (Subgroup.mem_centralizer_iff.mpr
          (fun v hv => (tau_cent_Y h v (h.toZIKData.V_le_Y hv)).symm)) b)
  have hzw : t ^ (a : ℕ) * τ ^ (b : ℕ) * l ^ (c : ℕ) ∈ centralizer (V : Set H) := hword
  have hmem := (centralizer (V : Set H)).mul_mem ((centralizer (V : Set H)).inv_mem hz) hzw
  simpa [mul_assoc] using hmem

theorem Vc_inf_cent_V (h : ZEData Q Y V V' B K ρ t τ l) :
    z4iVc K t τ l ⊓ centralizer (V : Set H) = z4iF K t τ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxVc, hxcent⟩ := hx
    obtain ⟨k, hk, s, hs, rfl⟩ := (mem_Vc_iff h).mp hxVc
    obtain ⟨a, b, c, rfl⟩ := (mem_T3_iff h).mp hs
    have hk_cent : k ∈ centralizer (V : Set H) :=
      Subgroup.mem_centralizer_iff.mpr
      (fun v hv => (h.K_cent_Y k hk v (h.toZIKData.V_le_Y hv)).symm)
    have hw_cent : t ^ (a : ℕ) * τ ^ (b : ℕ) * l ^ (c : ℕ) ∈ centralizer (V : Set H) := by
      have := (centralizer (V : Set H)).mul_mem
        ((centralizer (V : Set H)).inv_mem hk_cent) hxcent
      simpa using this
    have hlc_cent := lc_cent_of_ttau_lc_cent h hw_cent
    fin_cases c
    · rw [mem_F_iff h]
      exact ⟨k, hk, a, b, by simp [mul_assoc]⟩
    · exfalso
      obtain ⟨v, hv, hvne⟩ := l_not_cent_V h
      have hvl : v * l = l * v := by
        simpa using Subgroup.mem_centralizer_iff.mp hlc_cent v hv
      exact hvne hvl.symm
  · intro x hx
    exact ⟨F_le_Vc h hx, F_le_cent_V h hx⟩

theorem F_inf_cent_Y (h : ZEData Q Y V V' B K ρ t τ l) :
    z4iF K t τ ⊓ centralizer (Y : Set H) = z4iK1 K τ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxF, hxcent⟩ := hx
    obtain ⟨k, hk, a, b, rfl⟩ := (mem_F_iff h).mp hxF
    have hk_cent : k ∈ centralizer (Y : Set H) :=
      Subgroup.mem_centralizer_iff.mpr (fun y hy => (h.K_cent_Y k hk y hy).symm)
    have hτb_cent : τ ^ (b : ℕ) ∈ centralizer (Y : Set H) :=
      (centralizer (Y : Set H)).pow_mem
        (Subgroup.mem_centralizer_iff.mpr (fun y hy => (tau_cent_Y h y hy).symm)) b
    have hkta : k * t ^ (a : ℕ) ∈ centralizer (Y : Set H) := by
      have := (centralizer (Y : Set H)).mul_mem hxcent
        ((centralizer (Y : Set H)).inv_mem hτb_cent)
      simpa [mul_assoc] using this
    have hta_cent : t ^ (a : ℕ) ∈ centralizer (Y : Set H) := by
      have := (centralizer (Y : Set H)).mul_mem ((centralizer (Y : Set H)).inv_mem hk_cent) hkta
      simpa using this
    fin_cases a
    · rw [mem_K1_iff h]
      exact ⟨k, hk, b, by simp [mul_assoc]⟩
    · exfalso
      obtain ⟨y, hy, hyne⟩ := t_not_cent_Y h
      have hyt : y * t = t * y := by
        simpa using Subgroup.mem_centralizer_iff.mp hta_cent y hy
      exact hyne hyt.symm
  · intro x hx
    exact ⟨K1_le_F h hx, K1_le_cent_Y h hx⟩

end ZEData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B

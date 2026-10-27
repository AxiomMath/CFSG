module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ExitCent
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base7Sec
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ModuleSec
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.NineCore

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin Equiv Equiv.Perm

variable {V : Type} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)} {n : ℕ}
  {ψ : ↥H →* Perm (Fin n)}

theorem sixteen_le_card (hV : ∀ v : V, v ^ 2 = 1) (hn : 8 ≤ n) (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin n) ≤ ψ.range)
    (h3 : ∀ x : ↥H, (ψ x).IsThreeCycle → fixV (Subgroup.zpowers (x : MulAut V)) = ⊥) :
    16 ≤ Nat.card V := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let ι : Fin 8 ↪ Fin n := Fin.castLEEmb hn
  let ρ : alternatingGroup (Fin 8) →* ↥H := (altPreInv hψ hA).comp (altLift ι)
  have hρ : ∀ σ, ψ (ρ σ) = viaEmbedding (σ : Perm (Fin 8)) ι := fun σ =>
    (apply_altPreInv hψ hA _).trans (coe_altLift ι σ)
  let ρ' : alternatingGroup (Fin 8) →* MulAut V := H.subtype.comp ρ
  let c₁ : alternatingGroup (Fin 8) := ⟨swap 0 1 * swap 0 2, by rw [mem_alternatingGroup]; decide⟩
  let c₂ : alternatingGroup (Fin 8) := ⟨swap 3 4 * swap 3 5, by rw [mem_alternatingGroup]; decide⟩
  let d : alternatingGroup (Fin 8) := ⟨swap 4 5 * swap 6 7, by rw [mem_alternatingGroup]; decide⟩
  have e₁ : c₁ ^ 3 = 1 := by decide
  have e₂ : c₂ ^ 3 = 1 := by decide
  have r₁₂ : c₁ * c₂ = c₂ * c₁ := by decide
  have s₁ : d * c₁ * d⁻¹ = c₁ := by decide
  have s₂ : d * c₂ * d⁻¹ = c₂⁻¹ := by decide
  have hf : ∀ {a b c : Fin 8}, a ≠ b → a ≠ c → b ≠ c →
      ∀ hm : swap a b * swap a c ∈ alternatingGroup (Fin 8),
        fixV (Subgroup.zpowers (ρ' ⟨_, hm⟩)) = ⊥ := by
    intro a b c hab hac hbc hm
    exact h3 (ρ ⟨_, hm⟩) (by rw [hρ]; exact isThreeCycle_viaEmbedding ι hab hac hbc)
  have f₁ : fixV (Subgroup.zpowers (ρ' c₁)) = ⊥ := hf (by decide) (by decide) (by decide) _
  have f₂ : fixV (Subgroup.zpowers (ρ' c₂)) = ⊥ := hf (by decide) (by decide) (by decide) _
  have hx₁ : ρ' c₁ ≠ 1 := by
    intro h
    have h1 : ρ c₁ = 1 := Subtype.ext h
    have h2 := hρ c₁
    rw [h1, map_one] at h2
    have h3c := isThreeCycle_viaEmbedding ι (a := (0 : Fin 8)) (b := 1) (c := 2) (by decide)
      (by decide) (by decide)
    exact h3c.ne_one h2.symm
  have h₁ : ρ' c₁ ^ 3 = 1 := by rw [← map_pow, e₁, map_one]
  have h₂ : ρ' c₂ ^ 3 = 1 := by rw [← map_pow, e₂, map_one]
  have c₁₂ : ρ' c₁ * ρ' c₂ = ρ' c₂ * ρ' c₁ := by rw [← map_mul, ← map_mul, r₁₂]
  have g₁ : ρ' d * ρ' c₁ * (ρ' d)⁻¹ = ρ' c₁ := by rw [← map_inv, ← map_mul, ← map_mul, s₁]
  have g₂ : ρ' d * ρ' c₂ * (ρ' d)⁻¹ = (ρ' c₂)⁻¹ := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, s₂]
  have hV1 : 1 < Nat.card V := by
    by_contra hle
    have : Subsingleton V := (Finite.card_le_one_iff_subsingleton).1 (by omega)
    exact hx₁ (MulEquiv.ext fun v => Subsingleton.elim _ _)
  have hx₂1 : ρ' c₂ ≠ 1 := ne_one_of_fixV_eq_bot hV1 f₂
  have hy₂ : ρ' c₂ ∉ Subgroup.zpowers (ρ' c₁) := notMem_zpowers_of_conj h₂ hx₂1 g₁ g₂
  have hcard := card_eq_card_fixV_mul_card_fixV hV h₁ h₂ c₁₂ hx₁ hy₂ f₂
  have hconj : ρ' d * (ρ' c₁ * ρ' c₂) * (ρ' d)⁻¹ = ρ' c₁ * ρ' c₂ ^ 2 := by
    have hinv : (ρ' c₂)⁻¹ = ρ' c₂ ^ 2 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', h₂]
    calc ρ' d * (ρ' c₁ * ρ' c₂) * (ρ' d)⁻¹ =
          (ρ' d * ρ' c₁ * (ρ' d)⁻¹) * (ρ' d * ρ' c₂ * (ρ' d)⁻¹) := by group
      _ = ρ' c₁ * ρ' c₂ ^ 2 := by rw [g₁, g₂, hinv]
  rw [f₁, Subgroup.card_bot, one_mul, ← hconj, card_fixV_zpowers_conj] at hcard
  set c := Nat.card (fixV (Subgroup.zpowers (ρ' c₁ * ρ' c₂)))
  have hP3 : IsPGroup 3 (Subgroup.zpowers (ρ' c₁)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime h₁ hx₁, pow_one])
  have hst : Subgroup.zpowers (ρ' c₁) ≤ stabSub (fixV (Subgroup.zpowers (ρ' c₁ * ρ' c₂))) := by
    refine B1.le_stabSub_of_invariant fun k hk w hw => ?_
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    rw [mem_fixV_zpowers_iff] at hw ⊢
    have hcomm : Commute (ρ' c₁ ^ j) (ρ' c₁ * ρ' c₂) :=
      ((Commute.refl (ρ' c₁)).mul_right c₁₂).zpow_left j
    have h1 : (ρ' c₁ ^ j) ((ρ' c₁ * ρ' c₂) w) = (ρ' c₁ * ρ' c₂) ((ρ' c₁ ^ j) w) :=
      congrArg (fun φ : MulAut V => φ w) hcomm.eq
    rw [hw] at h1
    exact h1.symm
  have hmod := card_modEq_card_inf_fixV hP3 hst
  rw [f₁, inf_bot_eq, Subgroup.card_bot] at hmod
  have hdvd : c ∣ 2 ^ rk V := by
    rw [← card_eq_two_pow_rk hV]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hev : Even i := Proving.two_pow_mod_three_even i (by rw [← hi]; exact hmod)
  obtain ⟨k, rfl⟩ := hev
  have hk : 1 ≤ k := by
    by_contra hk0
    rw [show k = 0 by omega] at hi
    rw [hcard, hi] at hV1
    norm_num at hV1
  rw [hcard, hi]
  calc 16 = 2 ^ (1 + 1) * 2 ^ (1 + 1) := by norm_num
    _ ≤ 2 ^ (k + k) * 2 ^ (k + k) :=
        Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega))
          (Nat.pow_le_pow_right (by norm_num) (by omega))

omit [Finite V] in
theorem le_stabSub_top' (K : Subgroup (MulAut V)) : K ≤ stabSub (⊤ : Subgroup V) :=
  fun _ _ _ => by simp only [Subgroup.mem_top]

theorem exists_quot (hV : ∀ v : V, v ^ 2 = 1) (h5 : 5 ≤ n) (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin n) ≤ ψ.range)
    (hC : ∀ y : ↥H, (ψ y).IsThreeCycle →
      fixV (Subgroup.zpowers (y : MulAut V)) = fixV (altPre ψ)) :
    ∃ (W : Type) (_ : CommGroup W) (_ : Finite W) (G : Subgroup (MulAut W))
      (φ : ↥G →* Perm (Fin n)) (e : ↥H →* ↥G),
      (∀ w : W, w ^ 2 = 1) ∧ Function.Injective φ ∧ alternatingGroup (Fin n) ≤ φ.range ∧
      (∀ x : ↥G, (φ x).IsThreeCycle → fixV (Subgroup.zpowers (x : MulAut W)) = ⊥) ∧
      Function.Surjective e ∧ (∀ h, φ (e h) = ψ h) ∧
      (∀ h : ↥H, (fixV (Subgroup.zpowers (e h : MulAut W))).index ≤
        (fixV (Subgroup.zpowers (h : MulAut V))).index) ∧
      ∀ B : Subgroup (MulAut V), IsFFStarOffender H B →
        ∃ B' : Subgroup (MulAut W), B' ≤ G ∧ B' ≠ ⊥ ∧ IsElemAbelian2 B' ∧
          Nat.card W ≤ Nat.card B' * Nat.card (fixV B') ∧
          ∀ b : ↥G, (b : MulAut W) ∈ B' ↔ ∃ a : ↥H, (a : MulAut V) ∈ B ∧ e a = b := by
  set C₀ := fixV (altPre ψ) with hC₀
  have hH₀ : H ≤ stabSub C₀ := le_stabSub_fixV le_normalizer_altPre
  have hH₁ : H ≤ stabSub (⊤ : Subgroup V) := le_stabSub_top' H
  have hpow3 : ∀ y : ↥H, (ψ y).IsThreeCycle → (y : MulAut V) ^ 3 = 1 := fun y hy => by
    have h1 : y ^ 3 = 1 := hψ (by rw [map_pow, map_one, ← hy.orderOf, pow_orderOf_eq_one])
    rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
  have hL : ¬ IsCentralSec (altPre ψ) C₀ ⊤ := by
    intro hcen
    have hab : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
    have hac : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
    have hbc : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
    have hσ := isThreeCycle_swap_mul_swap_same hab hac hbc
    obtain ⟨y, hy⟩ := hA hσ.mem_alternatingGroup
    have hy3 : (ψ y).IsThreeCycle := hy ▸ hσ
    have hyL : (y : MulAut V) ∈ altPre ψ := coe_mem_altPre_iff.2 hy3.mem_alternatingGroup
    have htop : fixV (Subgroup.zpowers (y : MulAut V)) = ⊤ := by
      rw [eq_top_iff]
      intro v _
      rw [hC y hy3]
      exact mem_of_mul_inv_mem hV (hpow3 y hy3) (hC y hy3) (hcen _ hyL v (Subgroup.mem_top v))
    have h1 : y = 1 := Subtype.ext (eq_one_of_fixV_eq_top htop)
    exact hy3.ne_one (by rw [h1, map_one])
  have hσinj : Function.Injective (secHom hH₀ hH₁) :=
    secHom_injective hH₀ hH₁ (inf_centSec_eq_bot h5 hψ hA hH₀ hH₁ hL)
  have hrange : (secHom hH₀ hH₁).range = autSec H ⊤ C₀ := range_secHom hH₀ hH₁
  let e : ↥H →* ↥(autSec H ⊤ C₀) :=
    (secHom hH₀ hH₁).codRestrict (autSec H ⊤ C₀) fun h => hrange ▸ ⟨h, rfl⟩
  have he : ∀ h, ((e h : ↥(autSec H ⊤ C₀)) : MulAut (Sec ⊤ C₀)) = secHom hH₀ hH₁ h :=
    fun _ => rfl
  have heinj : Function.Injective e := fun a b hab => hσinj (congrArg Subtype.val hab)
  have hesurj : Function.Surjective e := by
    rintro ⟨g, hg⟩
    rw [← hrange] at hg
    obtain ⟨h, rfl⟩ := hg
    exact ⟨h, rfl⟩
  let eq : ↥H ≃* ↥(autSec H ⊤ C₀) := MulEquiv.ofBijective e ⟨heinj, hesurj⟩
  let φ : ↥(autSec H ⊤ C₀) →* Perm (Fin n) := ψ.comp eq.symm.toMonoidHom
  have hφe : ∀ h, φ (e h) = ψ h := fun h => by
    change ψ (eq.symm (eq h)) = ψ h
    rw [MulEquiv.symm_apply_apply]
  refine ⟨Sec ⊤ C₀, inferInstance, inferInstance, autSec H ⊤ C₀, φ, e, ?_, ?_, ?_, ?_, hesurj,
    hφe, ?_, ?_⟩
  ·
    intro w
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective w
    rw [← QuotientGroup.mk_pow]
    have h1 : v ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hV _)
    rw [h1, QuotientGroup.mk_one]
  · exact hψ.comp eq.symm.injective
  · intro τ hτ
    obtain ⟨h, rfl⟩ := hA hτ
    exact ⟨e h, hφe h⟩
  ·
    intro x hx3
    obtain ⟨h, rfl⟩ := hesurj x
    rw [hφe] at hx3
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective w
    rw [mem_fixV_zpowers_iff, he, secHom_mk, mk_eq_mk_sec_iff] at hw
    rw [Subgroup.mem_bot, mk_eq_one_sec_iff]
    exact mem_of_mul_inv_mem hV (hpow3 h hx3) (hC h hx3) hw
  ·
    intro h
    have hle : fixV (autSec (Subgroup.zpowers (h : MulAut V)) ⊤ C₀) ≤
        fixV (Subgroup.zpowers ((e h : ↥(autSec H ⊤ C₀)) : MulAut (Sec ⊤ C₀))) := by
      apply fixV_zpowers_le
      rw [he, ← map_secHom hH₀ hH₁ (Subgroup.zpowers_le.2 h.2)]
      exact ⟨h, Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers _), rfl⟩
    have h1 := index_fixV_autSec_mul_relIndex_le (A := Subgroup.zpowers (h : MulAut V))
      (W := ⊤) (U := C₀) le_top (le_stabSub_top' _)
    have h2 : 0 < (fixV (Subgroup.zpowers (h : MulAut V))).relIndex C₀ :=
      relIndex_pos_of_finite _ _
    rw [Subgroup.relIndex_top_right] at h1
    calc (fixV (Subgroup.zpowers ((e h : ↥(autSec H ⊤ C₀)) : MulAut (Sec ⊤ C₀)))).index
        ≤ (fixV (autSec (Subgroup.zpowers (h : MulAut V)) ⊤ C₀)).index :=
          Subgroup.index_antitone hle
      _ ≤ (fixV (autSec (Subgroup.zpowers (h : MulAut V)) ⊤ C₀)).index *
            (fixV (Subgroup.zpowers (h : MulAut V))).relIndex C₀ := Nat.le_mul_of_pos_right _ h2
      _ ≤ (fixV (Subgroup.zpowers (h : MulAut V))).index := h1
  ·
    intro B hB
    have hBH := hB.1
    refine ⟨autSec B ⊤ C₀, autSec_mono hBH _ _, autSec_ne_bot h5 hψ hA hH₀ hH₁ hL hBH hB.2.1,
      ?_, ?_, ?_⟩
    · rw [← map_secHom hH₀ hH₁ hBH]
      refine ⟨?_, ?_⟩
      · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        rw [← map_mul, ← map_mul]
        exact congrArg _ (Subtype.ext (hB.2.2.1.1 _ (Subgroup.mem_subgroupOf.1 ha) _
          (Subgroup.mem_subgroupOf.1 hb)))
      · rintro _ ⟨a, ha, rfl⟩
        rw [← map_pow]
        have h1 : a ^ 2 = 1 := Subtype.ext (by
          rw [Subgroup.coe_pow]
          exact hB.2.2.1.2 _ (Subgroup.mem_subgroupOf.1 ha))
        rw [h1, map_one]
    · have h1 := index_fixV_autSec_le hB (W := ⊤) (U := C₀) le_top (le_stabSub_top' _)
      have h2 := card_autSec_eq_card h5 hψ hA hH₀ hH₁ hL hBH
      rw [← (fixV (autSec B ⊤ C₀)).index_mul_card, h2]
      exact Nat.mul_le_mul_right _ h1
    · intro b
      rw [← map_secHom hH₀ hH₁ hBH]
      constructor
      · rintro ⟨a, ha, hab⟩
        exact ⟨a, Subgroup.mem_subgroupOf.1 ha, Subtype.ext hab⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a, Subgroup.mem_subgroupOf.2 ha, rfl⟩

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

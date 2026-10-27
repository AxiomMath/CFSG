module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.Core

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Swap

open Module CFSG.EvenSporadicStandard.HNRecog.Fpf

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

private lemma a₀_pow_five : (a₀ : A5) ^ 5 = 1 := by
  have := pow_orderOf_eq_one a₀
  rwa [orderOf_a₀] at this

private lemma pow_mul_pow_comm (a : A5) (m n : ℕ) : a ^ m * a ^ n = a ^ n * a ^ m := by
  rw [← pow_add, ← pow_add, Nat.add_comm]

private lemma n₀_conj_a₀_pow (m : ℕ) : n₀ * a₀ ^ m * n₀⁻¹ = (a₀ ^ m)⁻¹ := by
  rw [← conj_pow, n₀_mul_a₀_mul_inv, inv_pow]

private lemma a₀_inv_pow (m : ℕ) (hm : m ≤ 5) : (a₀ ^ m)⁻¹ = a₀ ^ (5 - m) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_add, Nat.add_sub_of_le hm, a₀_pow_five]

private lemma σ_conj (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (g h : A5 × A5) :
    σ g * σ h * (σ g)⁻¹ = σ (g * h * g⁻¹) := by
  rw [← map_mul, ← map_inv, ← map_mul]

private lemma σ_mul_comm_apply (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (g h : A5 × A5)
    (hgh : g * h = h * g) (v : V) : σ g (σ h v) = σ h (σ g v) := by
  have h1 : σ g * σ h = σ h * σ g := by rw [← map_mul, ← map_mul, hgh]
  rw [← LinearEquiv.mul_apply, h1, LinearEquiv.mul_apply]

private lemma σ_fixed_conj (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) {g h : A5 × A5} {v : V}
    (hv : σ h v = v) : σ (g * h * g⁻¹) (σ g v) = σ g v := by
  rw [← σ_conj]
  simp only [LinearEquiv.mul_apply]
  rw [show (σ g)⁻¹ ((σ g) v) = v from LinearEquiv.symm_apply_apply (σ g) v, hv]

private lemma fixed_of_inv_fixed {z : V ≃ₗ[ZMod 2] V} {w : V} (h : z⁻¹ w = w) : z w = w := by
  have h2 : z (z⁻¹ w) = z w := congrArg z h
  rw [show z (z⁻¹ w) = w from LinearEquiv.apply_symm_apply z w] at h2
  exact h2.symm

private lemma σ_pow_mul (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (m : ℕ) :
    σ (a₀ ^ m, a₀) = σ (a₀, 1) ^ m * σ (1, a₀) := by
  have hge : (((a₀, (1 : A5)) : A5 × A5) ^ m) * (1, a₀) = (a₀ ^ m, a₀) := by
    ext <;> simp [Prod.pow_fst, Prod.pow_snd]
  calc σ (a₀ ^ m, a₀) = σ ((((a₀, (1 : A5)) : A5 × A5) ^ m) * (1, a₀)) := by rw [hge]
    _ = σ (((a₀, (1 : A5)) : A5 × A5) ^ m) * σ (1, a₀) := map_mul σ _ _
    _ = σ (a₀, 1) ^ m * σ (1, a₀) := by rw [map_pow]

private lemma σ_alpha_pow_five (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) :
    (σ (a₀, 1)) ^ 5 = 1 := by
  have h1 : (((a₀, (1 : A5)) : A5 × A5) ^ 5) = 1 := by
    ext <;> simp [Prod.pow_fst, Prod.pow_snd, a₀_pow_five]
  calc (σ (a₀, 1)) ^ 5 = σ (((a₀, (1 : A5)) : A5 × A5) ^ 5) := (map_pow σ _ _).symm
    _ = σ 1 := by rw [h1]
    _ = 1 := map_one σ

structure StdHyp (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) : Prop where
  inj : Function.Injective σ
  finrank_eq : finrank (ZMod 2) V = 8
  irr : ∀ U : Submodule (ZMod 2) V, (∀ g : A5 × A5, ∀ u ∈ U, σ g u ∈ U) → U = ⊥ ∨ U = ⊤

theorem StdHyp.fixedFree_left {σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)} (hS : StdHyp σ) {y : A5}
    (hy : orderOf y = 5) : ∀ u : V, σ (y, 1) u = u → u = 0 := by
  obtain ⟨hα, hβ⟩ := fixedFree_of_irreducible σ hS.inj hS.finrank_eq hS.irr
  exact (fixedFree_of_orderOf_eq_five σ hα hβ hy).1

theorem StdHyp.fixedFree_left_pow {σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)} (hS : StdHyp σ) {n : ℕ}
    (hn : ¬ 5 ∣ n) : ∀ u : V, σ (a₀ ^ n, 1) u = u → u = 0 := by
  have h5 : orderOf (a₀ ^ n) = 5 := by
    have hc : (orderOf a₀).Coprime n := by
      rw [orderOf_a₀]
      exact (Nat.prime_five.coprime_iff_not_dvd).mpr hn
    rw [hc.orderOf_pow, orderOf_a₀]
  exact StdHyp.fixedFree_left hS h5

structure EigenData (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (c : ℕ) (Fp Fm : Submodule (ZMod 2) V) :
    Prop where
  one_le : 1 ≤ c
  le_four : c ≤ 4
  isCompl : IsCompl Fp Fm
  finrank_plus : finrank (ZMod 2) Fp = 4
  finrank_minus : finrank (ZMod 2) Fm = 4
  mem_plus : ∀ v : V, v ∈ Fp ↔ σ (a₀ ^ (5 - c), a₀) v = v
  mem_minus : ∀ v : V, v ∈ Fm ↔ σ (a₀ ^ c, a₀) v = v

theorem exists_eigenData (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (hS : StdHyp σ) :
    ∃ (c : ℕ) (Fp Fm : Submodule (ZMod 2) V), EigenData σ c Fp Fm := by
  obtain ⟨hα0, hβ0⟩ := fixedFree_of_irreducible σ hS.inj hS.finrank_eq hS.irr
  obtain ⟨v, hv_ne, k, hk1, hk4, hvk⟩ := exists_fixed_vector σ hS.finrank_eq hα0 hβ0
  let φ : A5 × A5 →* Module.End (ZMod 2) V :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 2) (M := V)).comp σ
  have hφ : ∀ (g : A5 × A5) (w : V), φ g w = σ g w := fun g w => rfl
  set c : ℕ := 5 - k with hc_def
  have hc1 : 1 ≤ c := by omega
  have hc4 : c ≤ 4 := by omega
  have hkc : 5 - c = k := by omega
  let α : Module.End (ZMod 2) V := φ (a₀, 1)
  let β : Module.End (ZMod 2) V := φ (1, a₀)
  let zpE : V ≃ₗ[ZMod 2] V := σ (a₀ ^ (5 - c), a₀)
  let zmE : V ≃ₗ[ZMod 2] V := σ (a₀ ^ c, a₀)
  let zp : Module.End (ZMod 2) V := zpE
  let zm : Module.End (ZMod 2) V := zmE
  let Fp : Submodule (ZMod 2) V := LinearMap.ker (zp - 1)
  let Fm : Submodule (ZMod 2) V := LinearMap.ker (zm - 1)
  have memFp : ∀ w : V, w ∈ Fp ↔ zp w = w := by
    intro w
    show w ∈ LinearMap.ker (zp - 1) ↔ zp w = w
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Module.End.one_apply]
  have memFm : ∀ w : V, w ∈ Fm ↔ zm w = w := by
    intro w
    show w ∈ LinearMap.ker (zm - 1) ↔ zm w = w
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Module.End.one_apply]
  have hvFp : v ∈ Fp := by
    rw [memFp]
    show σ (a₀ ^ (5 - c), a₀) v = v
    rw [hkc]
    exact hvk
  have hα5 : α ^ 5 = 1 := by
    have h1 : (((a₀, (1 : A5)) : A5 × A5) ^ 5) = 1 := by
      ext <;> simp [Prod.pow_fst, Prod.pow_snd, a₀_pow_five]
    calc α ^ 5 = φ (a₀, 1) ^ 5 := rfl
      _ = φ (((a₀, (1 : A5)) : A5 × A5) ^ 5) := (map_pow φ _ _).symm
      _ = φ 1 := by rw [h1]
      _ = 1 := map_one φ
  have hαzp : α * zp = zp * α := by
    have hge : (((a₀, (1 : A5)) : A5 × A5) * (a₀ ^ (5 - c), a₀))
        = (a₀ ^ (5 - c), a₀) * (a₀, (1 : A5)) := by
      apply Prod.ext
      · show a₀ * a₀ ^ (5 - c) = a₀ ^ (5 - c) * a₀
        simpa using pow_mul_pow_comm a₀ 1 (5 - c)
      · show (1 : A5) * a₀ = a₀ * 1
        simp
    calc α * zp = φ (((a₀, (1 : A5)) : A5 × A5) * (a₀ ^ (5 - c), a₀)) :=
          (map_mul φ _ _).symm
      _ = φ ((a₀ ^ (5 - c), a₀) * (a₀, (1 : A5))) := by rw [hge]
      _ = zp * α := map_mul φ _ _
  have hUα : ∀ w ∈ Fp, α w ∈ Fp := by
    intro w hw
    rw [memFp] at hw ⊢
    calc zp (α w) = α (zp w) := by
          have h := congrArg (fun f : Module.End (ZMod 2) V => f w) hαzp
          simpa [Module.End.mul_apply] using h.symm
      _ = α w := by rw [hw]
  have hfixα : ∀ w ∈ Fp, α w = w → w = 0 := by
    intro w _ hw
    exact hα0 w (by simpa [α, hφ] using hw)
  have h4dvd : 4 ∣ finrank (ZMod 2) Fp :=
    four_dvd_finrank_of_fixedFree α hα5 Fp hUα hfixα
  have hFp_le : finrank (ZMod 2) Fp ≤ 8 := by
    have := Submodule.finrank_le Fp
    rwa [hS.finrank_eq] at this
  have hFp_ne : Fp ≠ ⊥ := by
    intro hbot
    exact hv_ne (by simpa [hbot] using hvFp)
  have hfin : finrank (ZMod 2) Fp = 4 := by
    obtain ⟨m, hm⟩ := h4dvd
    have hmle : m ≤ 2 := by omega
    have hne0 : m ≠ 0 := by
      intro h0
      have hz : finrank (ZMod 2) Fp = 0 := by rw [hm, h0, mul_zero]
      exact hFp_ne (Submodule.finrank_eq_zero.mp hz)
    have hne2 : m ≠ 2 := by
      intro h2
      have h8 : finrank (ZMod 2) Fp = 8 := by rw [hm, h2]
      have htop : Fp = ⊤ :=
        Submodule.eq_top_of_finrank_eq (by rw [h8, hS.finrank_eq])
      have hzp1 : zp = 1 := by
        ext w
        have hw : w ∈ Fp := by rw [htop]; trivial
        rw [memFp] at hw
        simpa using hw
      have hσ1 : σ (a₀ ^ (5 - c), a₀) = 1 := by
        ext w
        have h := congrArg (fun f : Module.End (ZMod 2) V => f w) hzp1
        simpa [zp, zpE, hφ] using h
      have hpair : ((a₀ ^ (5 - c), a₀) : A5 × A5) = 1 := by
        apply hS.inj
        rw [hσ1, map_one]
      have ha0eq1 : a₀ = 1 := by
        have h := congrArg Prod.snd hpair
        simpa using h
      have h5 : orderOf a₀ = 5 := orderOf_a₀
      rw [ha0eq1, orderOf_one] at h5
      exact absurd h5 (by norm_num)
    omega
  have hn₀2 : n₀ * n₀ = 1 := by decide +kernel
  have hn₀_inv : n₀⁻¹ = n₀ := inv_eq_of_mul_eq_one_right hn₀2
  have hpair_inv : ((n₀, (1 : A5)) : A5 × A5)⁻¹ = (n₀, 1) := by
    apply Prod.ext
    · show n₀⁻¹ = n₀
      exact hn₀_inv
    · show (1 : A5)⁻¹ = 1
      simp
  have hσν_inv : (σ (n₀, 1))⁻¹ = σ (n₀, 1) := by
    rw [← map_inv, hpair_inv]
  have hge1 : (((n₀, (1 : A5)) : A5 × A5) * (a₀ ^ (5 - c), a₀)) * (n₀, (1 : A5))⁻¹
      = (a₀ ^ c, a₀) := by
    apply Prod.ext
    · show n₀ * a₀ ^ (5 - c) * n₀⁻¹ = a₀ ^ c
      rw [n₀_conj_a₀_pow, a₀_inv_pow (5 - c) (by omega), Nat.sub_sub_self (by omega)]
    · show (1 : A5) * a₀ * 1⁻¹ = a₀
      simp
  have hge1' : (((n₀, (1 : A5)) : A5 × A5) * (a₀ ^ c, a₀)) * (n₀, (1 : A5))⁻¹
      = (a₀ ^ (5 - c), a₀) := by
    apply Prod.ext
    · show n₀ * a₀ ^ c * n₀⁻¹ = a₀ ^ (5 - c)
      rw [n₀_conj_a₀_pow, a₀_inv_pow c (by omega)]
    · show (1 : A5) * a₀ * 1⁻¹ = a₀
      simp
  have hmap_le : Submodule.map (σ (n₀, 1) : V →ₗ[ZMod 2] V) Fp ≤ Fm := by
    rintro w ⟨u, hu, rfl⟩
    rw [memFm]
    have hu' : σ (a₀ ^ (5 - c), a₀) u = u := (memFp u).mp hu
    have h1 := σ_fixed_conj σ (g := (n₀, 1)) (h := (a₀ ^ (5 - c), a₀)) hu'
    have h2 : σ (a₀ ^ c, a₀) (σ (n₀, 1) u) = σ (n₀, 1) u := by
      rwa [hge1] at h1
    simpa [zm, zmE, hφ] using h2
  have hmap_ge : Fm ≤ Submodule.map (σ (n₀, 1) : V →ₗ[ZMod 2] V) Fp := by
    intro w hw
    rw [Submodule.mem_map]
    refine ⟨(σ (n₀, 1))⁻¹ w, ?_, ?_⟩
    · rw [memFp]
      have hw' : σ (a₀ ^ c, a₀) w = w := (memFm w).mp hw
      have h1 := σ_fixed_conj σ (g := (n₀, 1)) (h := (a₀ ^ c, a₀)) hw'
      have h2 : σ (a₀ ^ (5 - c), a₀) (σ (n₀, 1) w) = σ (n₀, 1) w := by
        rwa [hge1'] at h1
      rw [hσν_inv]
      simpa [zp, zpE, hφ] using h2
    · exact LinearEquiv.apply_symm_apply (σ (n₀, 1)) w
  have hmap : Submodule.map (σ (n₀, 1) : V →ₗ[ZMod 2] V) Fp = Fm :=
    le_antisymm hmap_le hmap_ge
  have hfin_m : finrank (ZMod 2) Fm = 4 := by
    rw [← hmap, LinearEquiv.finrank_map_eq (σ (n₀, 1)) Fp, hfin]
  have hcinv : (a₀ ^ c)⁻¹ = a₀ ^ (5 - c) := a₀_inv_pow c (by omega)
  have hzpzm : zpE * zmE⁻¹ = σ (a₀ ^ (2 * (5 - c)), 1) := by
    have hge : ((a₀ ^ (5 - c), a₀) : A5 × A5) * (a₀ ^ c, a₀)⁻¹
        = (a₀ ^ (2 * (5 - c)), 1) := by
      apply Prod.ext
      · show a₀ ^ (5 - c) * (a₀ ^ c)⁻¹ = a₀ ^ (2 * (5 - c))
        rw [hcinv, ← pow_add, two_mul]
      · show a₀ * a₀⁻¹ = (1 : A5)
        rw [mul_inv_cancel]
    show σ (a₀ ^ (5 - c), a₀) * (σ (a₀ ^ c, a₀))⁻¹ = σ (a₀ ^ (2 * (5 - c)), 1)
    rw [← map_inv, ← map_mul, hge]
  have hndvd : ¬ 5 ∣ 2 * (5 - c) := by
    have hc : 5 - c = 1 ∨ 5 - c = 2 ∨ 5 - c = 3 ∨ 5 - c = 4 := by omega
    rcases hc with h | h | h | h <;> rw [h] <;> decide
  have hinf : Fp ⊓ Fm = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    rw [Submodule.mem_inf] at hw
    obtain ⟨hwp, hwm⟩ := hw
    rw [memFp] at hwp
    rw [memFm] at hwm
    have hzminv : zmE⁻¹ w = w := by
      have hwm' : zmE w = w := hwm
      have h := congrArg (fun x => zmE⁻¹ x) hwm'
      rw [show zmE⁻¹ (zmE w) = w from LinearEquiv.symm_apply_apply zmE w] at h
      exact h.symm
    have hfix : σ (a₀ ^ (2 * (5 - c)), 1) w = w := by
      rw [← hzpzm]
      show (zpE * zmE⁻¹) w = w
      rw [LinearEquiv.mul_apply, hzminv]
      exact hwp
    exact StdHyp.fixedFree_left_pow hS hndvd w (by simpa using hfix)
  have hsup_dim : finrank (ZMod 2) (Fp ⊔ Fm : Submodule (ZMod 2) V) = 8 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq Fp Fm
    rw [hinf, finrank_bot, add_zero, hfin, hfin_m] at h
    omega
  have htop : Fp ⊔ Fm = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [hsup_dim, hS.finrank_eq])
  refine ⟨c, Fp, Fm, ?_⟩
  refine ⟨hc1, hc4, ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr htop⟩, hfin, hfin_m, ?_, ?_⟩
  · intro w
    rw [memFp]
    rfl
  · intro w
    rw [memFm]
    rfl

variable {σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)} {c : ℕ} {Fp Fm : Submodule (ZMod 2) V}

theorem EigenData.alpha_mem (hE : EigenData σ c Fp Fm) :
    (∀ v ∈ Fp, σ (a₀, 1) v ∈ Fp) ∧ (∀ v ∈ Fm, σ (a₀, 1) v ∈ Fm) := by
  constructor
  · intro v hv
    rw [hE.mem_plus]
    have hcomm : (((a₀ ^ (5 - c), a₀) : A5 × A5) * (a₀, (1 : A5)))
        = (a₀, (1 : A5)) * (a₀ ^ (5 - c), a₀) := by
      apply Prod.ext
      · show a₀ ^ (5 - c) * a₀ = a₀ * a₀ ^ (5 - c)
        simpa using pow_mul_pow_comm a₀ (5 - c) 1
      · show a₀ * 1 = 1 * a₀
        simp
    calc σ (a₀ ^ (5 - c), a₀) (σ (a₀, 1) v)
        = σ (a₀, 1) (σ (a₀ ^ (5 - c), a₀) v) :=
          σ_mul_comm_apply σ (a₀ ^ (5 - c), a₀) (a₀, 1) hcomm v
      _ = σ (a₀, 1) v := by rw [(hE.mem_plus v).mp hv]
  · intro v hv
    rw [hE.mem_minus]
    have hcomm : (((a₀ ^ c, a₀) : A5 × A5) * (a₀, (1 : A5)))
        = (a₀, (1 : A5)) * (a₀ ^ c, a₀) := by
      apply Prod.ext
      · show a₀ ^ c * a₀ = a₀ * a₀ ^ c
        simpa using pow_mul_pow_comm a₀ c 1
      · show a₀ * 1 = 1 * a₀
        simp
    calc σ (a₀ ^ c, a₀) (σ (a₀, 1) v)
        = σ (a₀, 1) (σ (a₀ ^ c, a₀) v) :=
          σ_mul_comm_apply σ (a₀ ^ c, a₀) (a₀, 1) hcomm v
      _ = σ (a₀, 1) v := by rw [(hE.mem_minus v).mp hv]

theorem EigenData.beta_eq (hE : EigenData σ c Fp Fm) :
    (∀ v ∈ Fp, σ (1, a₀) v = (σ (a₀, 1) ^ c) v) ∧
      (∀ v ∈ Fm, σ (1, a₀) v = (σ (a₀, 1) ^ (5 - c)) v) := by
  have hc4 : c ≤ 4 := hE.le_four
  have hα5 : (σ (a₀, 1)) ^ 5 = 1 := σ_alpha_pow_five σ
  have hαc_inv : (σ (a₀, 1) ^ c)⁻¹ = σ (a₀, 1) ^ (5 - c) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add, show c + (5 - c) = 5 by omega, hα5]
  have hα5c_inv : (σ (a₀, 1) ^ (5 - c))⁻¹ = σ (a₀, 1) ^ c := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add, show 5 - c + c = 5 by omega, hα5]
  constructor
  · intro v hv
    have h1 : (σ (a₀, 1) ^ (5 - c) * σ (1, a₀)) v = v := by
      rw [← σ_pow_mul σ (5 - c)]
      exact (hE.mem_plus v).mp hv
    rw [LinearEquiv.mul_apply] at h1
    have h2 : σ (1, a₀) v = (σ (a₀, 1) ^ (5 - c))⁻¹ v := by
      have h := congrArg (fun x => (σ (a₀, 1) ^ (5 - c))⁻¹ x) h1
      rw [show (σ (a₀, 1) ^ (5 - c))⁻¹ ((σ (a₀, 1) ^ (5 - c)) (σ (1, a₀) v)) =
            σ (1, a₀) v from
          LinearEquiv.symm_apply_apply (σ (a₀, 1) ^ (5 - c)) (σ (1, a₀) v)] at h
      exact h
    rwa [hα5c_inv] at h2
  · intro v hv
    have h1 : (σ (a₀, 1) ^ c * σ (1, a₀)) v = v := by
      rw [← σ_pow_mul σ c]
      exact (hE.mem_minus v).mp hv
    rw [LinearEquiv.mul_apply] at h1
    have h2 : σ (1, a₀) v = (σ (a₀, 1) ^ c)⁻¹ v := by
      have h := congrArg (fun x => (σ (a₀, 1) ^ c)⁻¹ x) h1
      rw [show (σ (a₀, 1) ^ c)⁻¹ ((σ (a₀, 1) ^ c) (σ (1, a₀) v)) = σ (1, a₀) v from
          LinearEquiv.symm_apply_apply (σ (a₀, 1) ^ c) (σ (1, a₀) v)] at h
      exact h
    rwa [hαc_inv] at h2

theorem EigenData.nu₁_mem (hE : EigenData σ c Fp Fm) :
    (∀ v ∈ Fp, σ (n₀, 1) v ∈ Fm) ∧ (∀ v ∈ Fm, σ (n₀, 1) v ∈ Fp) := by
  have hc4 : c ≤ 4 := hE.le_four
  have hge1 : (((n₀, (1 : A5)) : A5 × A5) * (a₀ ^ (5 - c), a₀)) * (n₀, (1 : A5))⁻¹
      = (a₀ ^ c, a₀) := by
    apply Prod.ext
    · show n₀ * a₀ ^ (5 - c) * n₀⁻¹ = a₀ ^ c
      rw [n₀_conj_a₀_pow, a₀_inv_pow (5 - c) (by omega), Nat.sub_sub_self (by omega)]
    · show (1 : A5) * a₀ * 1⁻¹ = a₀
      simp
  have hge2 : (((n₀, (1 : A5)) : A5 × A5) * (a₀ ^ c, a₀)) * (n₀, (1 : A5))⁻¹
      = (a₀ ^ (5 - c), a₀) := by
    apply Prod.ext
    · show n₀ * a₀ ^ c * n₀⁻¹ = a₀ ^ (5 - c)
      rw [n₀_conj_a₀_pow, a₀_inv_pow c (by omega)]
    · show (1 : A5) * a₀ * 1⁻¹ = a₀
      simp
  constructor
  · intro v hv
    rw [hE.mem_minus]
    have hv' : σ (a₀ ^ (5 - c), a₀) v = v := (hE.mem_plus v).mp hv
    have h1 := σ_fixed_conj σ (g := (n₀, 1)) (h := (a₀ ^ (5 - c), a₀)) hv'
    rwa [hge1] at h1
  · intro v hv
    rw [hE.mem_plus]
    have hv' : σ (a₀ ^ c, a₀) v = v := (hE.mem_minus v).mp hv
    have h1 := σ_fixed_conj σ (g := (n₀, 1)) (h := (a₀ ^ c, a₀)) hv'
    rwa [hge2] at h1

theorem EigenData.nu₂_mem (hE : EigenData σ c Fp Fm) :
    (∀ v ∈ Fp, σ (1, n₀) v ∈ Fm) ∧ (∀ v ∈ Fm, σ (1, n₀) v ∈ Fp) := by
  have hc4 : c ≤ 4 := hE.le_four
  have hge1 : (((1, n₀) : A5 × A5) * (a₀ ^ (5 - c), a₀)) * (1, n₀)⁻¹
      = (a₀ ^ (5 - c), a₀⁻¹) := by
    apply Prod.ext
    · show (1 : A5) * a₀ ^ (5 - c) * 1⁻¹ = a₀ ^ (5 - c)
      simp
    · show n₀ * a₀ * n₀⁻¹ = a₀⁻¹
      rw [n₀_mul_a₀_mul_inv]
  have hge2 : (((1, n₀) : A5 × A5) * (a₀ ^ c, a₀)) * (1, n₀)⁻¹
      = (a₀ ^ c, a₀⁻¹) := by
    apply Prod.ext
    · show (1 : A5) * a₀ ^ c * 1⁻¹ = a₀ ^ c
      simp
    · show n₀ * a₀ * n₀⁻¹ = a₀⁻¹
      rw [n₀_mul_a₀_mul_inv]
  have hg1 : ((a₀ ^ (5 - c), a₀⁻¹) : A5 × A5) = (a₀ ^ c, a₀)⁻¹ := by
    apply Prod.ext
    · show a₀ ^ (5 - c) = (a₀ ^ c)⁻¹
      rw [a₀_inv_pow c (by omega)]
    · show a₀⁻¹ = a₀⁻¹
      rfl
  have hg2 : ((a₀ ^ c, a₀⁻¹) : A5 × A5) = (a₀ ^ (5 - c), a₀)⁻¹ := by
    apply Prod.ext
    · show a₀ ^ c = (a₀ ^ (5 - c))⁻¹
      rw [a₀_inv_pow (5 - c) (by omega), Nat.sub_sub_self (by omega)]
    · show a₀⁻¹ = a₀⁻¹
      rfl
  have hinv1 : σ (a₀ ^ (5 - c), a₀⁻¹) = (σ (a₀ ^ c, a₀))⁻¹ := by
    rw [hg1, map_inv]
  have hinv2 : σ (a₀ ^ c, a₀⁻¹) = (σ (a₀ ^ (5 - c), a₀))⁻¹ := by
    rw [hg2, map_inv]
  constructor
  · intro v hv
    rw [hE.mem_minus]
    have hv' : σ (a₀ ^ (5 - c), a₀) v = v := (hE.mem_plus v).mp hv
    have h1 := σ_fixed_conj σ (g := (1, n₀)) (h := (a₀ ^ (5 - c), a₀)) hv'
    have h2 : σ (a₀ ^ (5 - c), a₀⁻¹) (σ (1, n₀) v) = σ (1, n₀) v := by
      rwa [hge1] at h1
    have h3 : (σ (a₀ ^ c, a₀))⁻¹ (σ (1, n₀) v) = σ (1, n₀) v := by
      rwa [hinv1] at h2
    exact fixed_of_inv_fixed h3
  · intro v hv
    rw [hE.mem_plus]
    have hv' : σ (a₀ ^ c, a₀) v = v := (hE.mem_minus v).mp hv
    have h1 := σ_fixed_conj σ (g := (1, n₀)) (h := (a₀ ^ c, a₀)) hv'
    have h2 : σ (a₀ ^ c, a₀⁻¹) (σ (1, n₀) v) = σ (1, n₀) v := by
      rwa [hge2] at h1
    have h3 : (σ (a₀ ^ (5 - c), a₀))⁻¹ (σ (1, n₀) v) = σ (1, n₀) v := by
      rwa [hinv2] at h2
    exact fixed_of_inv_fixed h3

end CFSG.EvenSporadicStandard.HNRecog.Swap

module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67CoreTools

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Generic

variable {Y : Type} [Group Y]

theorem false_of_inner_abelian_core {r : ℕ} {V Z : Subgroup (MulAut Y)}
    (hcen : Subgroup.center Y = ⊥) (h2 : N2Cfg Y r V Z) (h3 : N3Full Y V Z)
    {z : Y} (hz1 : z ≠ 1) (hzV : (MulAut.conj z : MulAut Y) ∈ V) {e : MulAut Y} (heV : e ∈ V)
    (hab : ∀ N₀ : Subgroup Y, N₀ ≤ fixSub (MulAut.conj z) →
      (∀ f ∈ fixSub (MulAut.conj z), ∀ x ∈ N₀, f * x * f⁻¹ ∈ N₀) →
      (∀ x ∈ N₀, ∀ y ∈ N₀, x * y = y * x) → (∀ c ∈ N₀, e c = c) → N₀ ≤ Subgroup.zpowers z)
    (hker : ∀ ζ : MulAut Y, Odd (orderOf ζ) → Nat.Coprime (orderOf ζ) r →
      ζ * MulAut.conj z = MulAut.conj z * ζ → ζ * e = e * ζ →
        (∀ c ∈ fixSub (MulAut.conj z), ζ c = c) → ζ = 1) :
    False := by
  obtain ⟨-, -, hVe, -, hZab, hZodd, hZcop, hZbot, hcomm⟩ := h2
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) :=
    mulAut_conj_injective_of_center_bot hcen
  have hι1 : (MulAut.conj z : MulAut Y) ≠ 1 := fun h => hz1 (hinj (by rw [map_one]; exact h))
  have hzr : z ^ r = 1 := by
    apply hinj
    rw [map_pow, map_one]
    exact elemPow_eq_one_of_isElementaryAbelian _ hzV
  set F : Subgroup Y := fixSub (MulAut.conj z) with hF
  set N₀ : Subgroup Y := (Z.comap (MulAut.conj : Y →* MulAut Y)) ⊓ F with hN₀
  have hN₀mem : ∀ c : Y, c ∈ N₀ ↔ MulAut.conj c ∈ Z ∧ c ∈ F := fun c => Iff.rfl
  have hN₀F : N₀ ≤ F := inf_le_right
  have hN₀norm : ∀ f ∈ F, ∀ x ∈ N₀, f * x * f⁻¹ ∈ N₀ := by
    intro f hf x hx
    obtain ⟨hxZ, hxF⟩ := (hN₀mem x).1 hx
    have hgN := h3 _ hzV hι1 f hf
    have h1 := (Subgroup.mem_normalizer_iff.1 hgN _).1 hxZ
    refine (hN₀mem _).2 ⟨?_, F.mul_mem (F.mul_mem hf hxF) (F.inv_mem hf)⟩
    simpa [map_mul, map_inv] using h1
  have hN₀ab : ∀ x ∈ N₀, ∀ y ∈ N₀, x * y = y * x := by
    intro x hx y hy
    apply hinj
    simp only [map_mul]
    exact hZab _ ((hN₀mem x).1 hx).1 _ ((hN₀mem y).1 hy).1
  have hN₀e : ∀ c ∈ N₀, e c = c := by
    intro c hc
    have h1 := hcomm e heV _ ((hN₀mem c).1 hc).1
    apply hinj
    rw [← mulAut_conj_conj e c, h1]
    group
  have hN₀z : N₀ ≤ Subgroup.zpowers z := hab N₀ hN₀F hN₀norm hN₀ab hN₀e
  have hN₀bot : N₀ = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    rw [Subgroup.mem_bot]
    have hcz : c ∈ Subgroup.zpowers z := hN₀z hc
    have hcr : c ^ r = 1 := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hcz
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzr, one_zpow]
    have hdz : orderOf c ∣ Nat.card ↥Z := by
      have h1 : orderOf (MulAut.conj c : MulAut Y) ∣ Nat.card ↥Z := by
        have := orderOf_dvd_natCard (⟨_, ((hN₀mem c).1 hc).1⟩ : ↥Z)
        rwa [← Subgroup.orderOf_coe] at this
      have h2 : orderOf (MulAut.conj c : MulAut Y) = orderOf c :=
        orderOf_injective (MulAut.conj : Y →* MulAut Y) hinj c
      rwa [h2] at h1
    have hdr : orderOf c ∣ r := orderOf_dvd_of_pow_eq_one hcr
    have : orderOf c = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdz hZcop)
      hdr
    exact orderOf_eq_one_iff.1 this
  have hfix : ∀ ζ ∈ Z, ∀ c ∈ F, ζ c = c := by
    intro ζ hζ c hc
    have hζF : ζ c ∈ F := by
      rw [hF, mem_fixSub] at hc ⊢
      have := hcomm _ hzV ζ hζ
      have h1 := congrArg (fun t : MulAut Y => t c) this
      simp only [MulAut.mul_apply] at h1
      rw [h1, hc]
    have hnorm := h3 _ hzV hι1 c hc
    have h1 := (Subgroup.mem_normalizer_iff.1 hnorm ζ).1 hζ
    have h4 : MulAut.conj c * ζ * (MulAut.conj c)⁻¹ * ζ⁻¹ ∈ Z :=
      Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hζ)
    have h5 : MulAut.conj c * ζ * (MulAut.conj c)⁻¹ * ζ⁻¹ = MulAut.conj (c * ζ c⁻¹) := by
      have : ζ * (MulAut.conj c)⁻¹ * ζ⁻¹ = MulAut.conj (ζ c⁻¹) := by
        have := mulAut_conj_conj ζ c⁻¹
        simpa [map_inv] using this
      calc MulAut.conj c * ζ * (MulAut.conj c)⁻¹ * ζ⁻¹
          = MulAut.conj c * (ζ * (MulAut.conj c)⁻¹ * ζ⁻¹) := by group
        _ = MulAut.conj (c * ζ c⁻¹) := by rw [this, map_mul]
    rw [h5] at h4
    have hmemF : c * ζ c⁻¹ ∈ F := by
      rw [map_inv]
      exact F.mul_mem hc (F.inv_mem hζF)
    have hx : c * ζ c⁻¹ ∈ N₀ := (hN₀mem _).2 ⟨h4, hmemF⟩
    rw [hN₀bot, Subgroup.mem_bot] at hx
    have h7 : ζ c⁻¹ = c⁻¹ := by
      have := congrArg (fun t => c⁻¹ * t) hx
      simpa using this
    have := congrArg (fun t => t⁻¹) h7
    simpa using this
  obtain ⟨ζ, hζ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZbot
  have hdvd : orderOf (ζ : MulAut Y) ∣ Nat.card ↥Z := by
    have := orderOf_dvd_natCard ζ
    rwa [← Subgroup.orderOf_coe] at this
  have hodd : Odd (orderOf (ζ : MulAut Y)) := Odd.of_dvd_nat hZodd hdvd
  have hcop : Nat.Coprime (orderOf (ζ : MulAut Y)) r := Nat.Coprime.coprime_dvd_left hdvd hZcop
  have hζι : (ζ : MulAut Y) * MulAut.conj z = MulAut.conj z * (ζ : MulAut Y) :=
    (hcomm _ hzV ζ ζ.2).symm
  have hζe : (ζ : MulAut Y) * e = e * (ζ : MulAut Y) := (hcomm e heV ζ ζ.2).symm
  have := hker ζ hodd hcop hζι hζe (fun c hc => hfix ζ ζ.2 c hc)
  exact hζ1 (Subtype.ext this)

end Generic

end CFSG.GH74.GLS.Stage2.Bender.Thm1

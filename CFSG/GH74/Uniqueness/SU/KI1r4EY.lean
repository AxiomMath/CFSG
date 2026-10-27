module

public import CFSG.GH74.Uniqueness.SU.KI1r4TG2b
public import CFSG.GH74.Uniqueness.SU.KI1r4EWalter2

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4

open Subgroup CFSG CFSG.GH74.Uniqueness.SU CFSG.GH74.Uniqueness.SU.K.R3
open CFSG.GH74.Uniqueness.SU.K.R3.Pow CFSG.GH74.Uniqueness.SU.K.R4.L82
open CFSG.OrderReductions.FrattiniAutomorphisms
open scoped commutatorElement

theorem invariant_abelian_or_top {M : Type} [Group M] [Finite M] (hM : IsPGroup 2 M)
    {σ τ : MulAut M} (h : DihAct σ τ 1) (h64 : Nat.card M = 64)
    (hZ4 : Nat.card (center M) = 4) (hfr : frattini M = center M)
    (W : Subgroup M) (hZW : center M ≤ W) (hσW : ∀ w ∈ W, σ w ∈ W) :
    (∀ a ∈ W, ∀ b ∈ W, a * b = b * a) ∨ W = ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcomm, hsq⟩ := quot_comm_sq hM
  have hΦcard : Nat.card (frattini M) = 4 := by rw [hfr]; exact hZ4
  have hΦW : frattini M ≤ W := hfr ▸ hZW
  have hVcard : Nat.card (M ⧸ frattini M) = 16 := by
    have h1 := (frattini M).card_mul_index
    have h2 : Nat.card (M ⧸ frattini M) = (frattini M).index := rfl
    rw [hΦcard, h64] at h1
    rw [h2]
    omega
  have hb3 : bar σ ^ 3 = 1 := by
    have h3 : σ ^ 3 = 1 := by simpa using h.pow
    rw [← map_pow, h3, map_one]
  have hWbinv : ∀ u ∈ W.map (QuotientGroup.mk' (frattini M)), bar σ u ∈
      W.map (QuotientGroup.mk' (frattini M)) := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨σ w, hσW w hw, (bar_mk σ w).symm⟩
  have hmod := card_invariant_mod_three (bar σ) hb3 (bar_fix hM h) _ hWbinv
  have hWcard := card_eq_mul_card_map_mk (frattini M) W hΦW
  rw [hΦcard] at hWcard
  have hdvd : Nat.card (W.map (QuotientGroup.mk' (frattini M))) ∣ 16 :=
    hVcard ▸ Subgroup.card_subgroup_dvd_card _
  have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
  rw [h16] at hdvd
  obtain ⟨i, hi, hWbi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [hWbi] at hmod hWcard
  interval_cases i
  ·
    left
    have hW4 : Nat.card W = 4 := by simpa using hWcard
    have hWΦ : frattini M = W := Subgroup.eq_of_le_of_card_ge hΦW (by rw [hW4, hΦcard])
    intro a ha b hb
    have haZ : a ∈ center M := hfr ▸ hWΦ ▸ ha
    exact (Subgroup.mem_center_iff.mp haZ b).symm
  · exfalso
    norm_num [Nat.ModEq] at hmod
  ·
    left
    have hW16 : Nat.card W = 16 := by simpa using hWcard
    have hWb4 : Nat.card (W.map (QuotientGroup.mk' (frattini M))) = 4 := by simpa using hWbi
    obtain ⟨c, hcW, hcΦ⟩ : ∃ c ∈ W, c ∉ frattini M := by
      by_contra hno
      push Not at hno
      have hle : W ≤ frattini M := fun c hc => hno c hc
      have := Subgroup.card_le_of_le hle
      rw [hΦcard] at this
      omega
    set u : M ⧸ frattini M := (c : M ⧸ frattini M) with hu
    have hu1 : u ≠ 1 := fun h1 => hcΦ ((QuotientGroup.eq_one_iff c).mp h1)
    have hv : bar σ u = ((σ c : M) : M ⧸ frattini M) := bar_mk σ c
    have hvu : bar σ u ≠ u := fun h1 => hu1 (bar_fix hM h u h1)
    have hv1 : bar σ u ≠ 1 := fun h1 => hu1 ((bar σ).injective (by rw [map_one]; exact h1))
    set ℓ : Subgroup (M ⧸ frattini M) := zpowers u ⊔ zpowers (bar σ u) with hℓ
    have huWb : u ∈ W.map (QuotientGroup.mk' (frattini M)) := ⟨c, hcW, rfl⟩
    have hvWb : bar σ u ∈ W.map (QuotientGroup.mk' (frattini M)) := hWbinv u huWb
    have hℓWb : ℓ ≤ W.map (QuotientGroup.mk' (frattini M)) :=
      sup_le (zpowers_le.mpr huWb) (zpowers_le.mpr hvWb)
    have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq u) hu1
    have hzu : Nat.card (zpowers u) = 2 := by rw [Nat.card_zpowers, hu2]
    have hℓcard : 4 ≤ Nat.card ℓ := by
      obtain ⟨k, hk⟩ : ∃ k, Nat.card ℓ = Nat.card (zpowers u) * k :=
        Subgroup.card_dvd_of_le (le_sup_left : zpowers u ≤ ℓ)
      rw [hzu] at hk
      have hk0 : k ≠ 0 := by
        rintro rfl
        exact (Nat.card_pos (α := ℓ)).ne' (by rw [hk])
      have hk1 : k ≠ 1 := by
        rintro rfl
        have hzℓ : zpowers u = ℓ :=
          Subgroup.eq_of_le_of_card_ge le_sup_left (le_of_eq (by rw [hk, hzu]))
        have hvmem : bar σ u ∈ zpowers u := hzℓ ▸ Subgroup.mem_sup_right (mem_zpowers _)
        rcases LemmaYAux.eq_one_or_eq_of_mem_zpowers (hsq u) hvmem with h1 | h1
        · exact hv1 h1
        · exact hvu h1
      omega
    have hℓeq : ℓ = W.map (QuotientGroup.mk' (frattini M)) :=
      Subgroup.eq_of_le_of_card_ge hℓWb (by rw [hWb4]; exact hℓcard)
    have hcσc : c * σ c = σ c * c := (commute_sigma h c).eq
    set N : Subgroup M := zpowers c ⊔ zpowers (σ c) with hN
    have hcc : ∀ a ∈ zpowers c, ∀ b ∈ zpowers (σ c), a * b = b * a := by
      rintro a ⟨m, rfl⟩ b ⟨n, rfl⟩
      exact ((Commute.zpow_zpow (show Commute c (σ c) from hcσc) m n)).eq
    have hNab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
      intro a ha b hb
      obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := SU1.mem_sup_of_commute hcc ha
      obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := SU1.mem_sup_of_commute hcc hb
      have e1 : a₁ * b₁ = b₁ * a₁ := by
        obtain ⟨m, rfl⟩ := ha₁; obtain ⟨n, rfl⟩ := hb₁
        exact ((Commute.zpow_zpow_self c m n)).eq
      have e2 : a₂ * b₂ = b₂ * a₂ := by
        obtain ⟨m, rfl⟩ := ha₂; obtain ⟨n, rfl⟩ := hb₂
        exact ((Commute.zpow_zpow_self (σ c) m n)).eq
      have e3 := hcc _ ha₁ _ hb₂
      have e4 := hcc _ hb₁ _ ha₂
      calc a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
        _ = a₁ * (b₁ * a₂) * b₂ := by rw [(hcc b₁ hb₁ a₂ ha₂).symm]
        _ = (a₁ * b₁) * (a₂ * b₂) := by group
        _ = (b₁ * a₁) * (b₂ * a₂) := by rw [e1, e2]
        _ = b₁ * (a₁ * b₂) * a₂ := by group
        _ = b₁ * (b₂ * a₁) * a₂ := by rw [e3]
        _ = b₁ * b₂ * (a₁ * a₂) := by group
    have hWN : ∀ w ∈ W, ∃ n ∈ N, ∃ z ∈ frattini M, w = n * z := by
      intro w hw
      have hwℓ : (QuotientGroup.mk' (frattini M)) w ∈ ℓ := by
        rw [hℓeq]; exact ⟨w, hw, rfl⟩
      obtain ⟨p, hp, q, hq, hpq⟩ := SU1.mem_sup_of_commute (fun a _ b _ => hcomm a b) hwℓ
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
      refine ⟨c ^ i * σ c ^ j, Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_sup_left
        (mem_zpowers c)) i) (Subgroup.zpow_mem _ (Subgroup.mem_sup_right (mem_zpowers (σ c))) j),
        (c ^ i * σ c ^ j)⁻¹ * w, ?_, by group⟩
      have hπ : (QuotientGroup.mk' (frattini M)) (c ^ i * σ c ^ j) = u ^ i * (bar σ u) ^ j := by
        rw [map_mul, map_zpow, map_zpow, hv]
        rfl
      have h1 : (QuotientGroup.mk' (frattini M)) ((c ^ i * σ c ^ j)⁻¹ * w) = 1 := by
        rw [map_mul, map_inv, hπ, hpq]
        simp
      exact (QuotientGroup.eq_one_iff _).mp h1
    intro a ha b hb
    obtain ⟨n₁, hn₁, z₁, hz₁, rfl⟩ := hWN a ha
    obtain ⟨n₂, hn₂, z₂, hz₂, rfl⟩ := hWN b hb
    have hz₁c : ∀ g : M, g * z₁ = z₁ * g := fun g =>
      Subgroup.mem_center_iff.mp (hfr ▸ hz₁) g
    have hz₂c : ∀ g : M, g * z₂ = z₂ * g := fun g =>
      Subgroup.mem_center_iff.mp (hfr ▸ hz₂) g
    calc n₁ * z₁ * (n₂ * z₂) = n₁ * (z₁ * n₂) * z₂ := by group
      _ = n₁ * (n₂ * z₁) * z₂ := by rw [(hz₁c n₂).symm]
      _ = (n₁ * n₂) * (z₁ * z₂) := by group
      _ = (n₂ * n₁) * (z₂ * z₁) := by
        rw [hNab n₁ hn₁ n₂ hn₂, show z₁ * z₂ = z₂ * z₁ from hz₂c z₁]
      _ = n₂ * (n₁ * z₂) * z₁ := by group
      _ = n₂ * (z₂ * n₁) * z₁ := by rw [(hz₂c n₁).symm]
      _ = n₂ * z₂ * (n₁ * z₁) := by group
  · exfalso
    norm_num [Nat.ModEq] at hmod
  · right
    have hW64 : Nat.card W = 64 := by simpa using hWcard
    exact Subgroup.eq_top_of_card_eq W (by rw [hW64, h64])

variable {H : Type} [Group H] [Finite H]

theorem RData.dihAct {T : Sylow 2 H} {x : H} {A R : Subgroup H} {y : H} (hR : RData T x A R y) :
    ∃ σ τ : MulAut ↥R, DihAct σ τ 1 ∧ ∀ r : ↥R, ((σ r : ↥R) : H) = y * r * y⁻¹ := by
  have hyN := Pow.mem_normalizer_of_forall_mem R hR.y_norm
  have hxN := Pow.mem_normalizer_of_forall_mem R hR.x_norm
  set σ : MulAut ↥R := R.normalizerMonoidHom ⟨y, hyN⟩ with hσ
  set τ : MulAut ↥R := R.normalizerMonoidHom ⟨x, hxN⟩ with hτ
  have hσapp : ∀ r : ↥R, ((σ r : ↥R) : H) = y * r * y⁻¹ := fun r => rfl
  refine ⟨σ, τ, ?_, hσapp⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : σ ^ 3 = 1 := by
      refine MulEquiv.ext fun r => ?_
      have h0 : ((σ ^ 3) r : ↥R) = σ (σ (σ r)) := by
        simp [pow_succ, MulAut.mul_apply]
      rw [h0]
      show σ (σ (σ r)) = r
      apply Subtype.ext
      rw [hσapp, hσapp, hσapp]
      have h3 := hR.y_cube r r.2
      have hy3 : y ^ 3 = y * y * y := by rw [pow_succ, pow_two]
      rw [hy3] at h3
      calc y * (y * (y * (r : H) * y⁻¹) * y⁻¹) * y⁻¹
          = y * y * y * r * (y * y * y)⁻¹ := by group
        _ = r := h3
    simpa using h1
  · have : (⟨x, hxN⟩ : normalizer (R : Set H)) ^ 2 = 1 :=
      Subtype.ext (by simpa [pow_two] using hR.x_sq)
    change R.normalizerMonoidHom ⟨x, hxN⟩ ^ 2 = 1
    rw [← map_pow, this, map_one]
  · have : (⟨x, hxN⟩ : normalizer (R : Set H)) * ⟨y, hyN⟩ *
        (⟨x, hxN⟩ : normalizer (R : Set H))⁻¹ = (⟨y, hyN⟩ : normalizer (R : Set H))⁻¹ :=
      Subtype.ext (by simpa using hR.xy)
    have h2 := congrArg R.normalizerMonoidHom this
    simpa only [map_mul, map_inv] using h2
  · intro r hr
    exact Subtype.ext (hR.y_free r r.2 (by rw [← hσapp r, hr]))

theorem RData.invariant_abelian_or_eq {T : Sylow 2 H} {x : H} {A R : Subgroup H} {y : H}
    (hR : RData T x A R y) (h64 : Nat.card R = 64) (hZ4 : Nat.card (center ↥R) = 4)
    (hfr : frattini ↥R = center ↥R) {W : Subgroup H} (hWR : W ≤ R)
    (hZW : ∀ z ∈ center ↥R, (z : H) ∈ W) (hWy : ∀ w ∈ W, y * w * y⁻¹ ∈ W) :
    (∀ a ∈ W, ∀ b ∈ W, a * b = b * a) ∨ W = R := by
  obtain ⟨σ, τ, hDih, hσ⟩ := hR.dihAct
  rcases invariant_abelian_or_top hR.R_two hDih h64 hZ4 hfr (W.subgroupOf R)
    (fun z hz => Subgroup.mem_subgroupOf.mpr (hZW z hz))
    (fun w hw => Subgroup.mem_subgroupOf.mpr (by
      rw [hσ]; exact hWy w (Subgroup.mem_subgroupOf.mp hw))) with hab | htop
  · left
    intro a ha b hb
    have := hab ⟨a, hWR ha⟩ (Subgroup.mem_subgroupOf.mpr ha) ⟨b, hWR hb⟩
      (Subgroup.mem_subgroupOf.mpr hb)
    exact congrArg Subtype.val this
  · right
    refine le_antisymm hWR fun r hr => ?_
    have : (⟨r, hr⟩ : ↥R) ∈ W.subgroupOf R := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this

end CFSG.GH74.Uniqueness.SU.K.R4

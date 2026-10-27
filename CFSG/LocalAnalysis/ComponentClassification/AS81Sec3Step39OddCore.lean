module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step39Core

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

namespace CFSG.ComponentClassification.AS81

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.Open
open CFSG.ABGLocalTools Sec3

namespace Sec38Hyp

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}
  (H : Sec38Hyp G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀)
include H

theorem range_le_omega_of_odd
    (hΩ : omegaGroup H.xsub.q H.xsub.q_nondegenerate ≤ H.ρG.range)
    (hinner : ∀ w : G, w * x = x * w →
      ∃ b ∈ sec3B A₁ x, b⁻¹ * w ∈ centralizer (sec3B A₁ x : Set G))
    (hCBz : ∀ k ∈ sec3B A₁ x ⊓ centralizer ({z} : Set G), ∃ b₀ ∈ B₀, ∃ i : ℤ, k = b₀ * x ^ i)
    (hOB : AS76b.oddCoreIn (centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) ≤
      centralizer (sec3B A₁ x : Set G))
    (hBn : ∀ h : G, (∀ b ∈ sec3B A₁ x, h * b * h⁻¹ ∈ centralizer ({x} : Set G)) →
      h * z * h⁻¹ = z → h ∈ normalizer (sec3B A₁ x : Set G)) :
    H.ρG.range ≤ omegaGroup H.xsub.q H.xsub.q_nondegenerate := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  obtain ⟨_, ⟨n₁, rfl⟩, hn₁⟩ := Set.not_subset.mp hcon
  have : Nontrivial (H.xsub.clSub Q) :=
    Module.nontrivial_of_finrank_pos (R := ZMod 2) (by rw [H.finrank_W']; norm_num)
  obtain ⟨v', hv'⟩ := exists_map_ne_zero H.W'_nondegenerate
  have hvW' : (v' : H.xsub.Qt) ∈ H.xsub.clSub Q := v'.2
  have hv : H.xsub.q (v' : H.xsub.Qt) ≠ 0 := hv'
  let _ : Invertible (H.xsub.q (v' : H.xsub.Qt)) := invertibleOfNonzero hv
  set r := TauCeti.QuadraticMap.reflection H.xsub.q (v' : H.xsub.Qt) with hrdef
  have hrO : r ∈ TauCeti.QuadraticMap.orthogonalGroup H.xsub.q :=
    TauCeti.QuadraticMap.reflection_mem_orthogonalGroup _ _
  have hr1 : finrank (ZMod 2) (commSpace r) = 1 :=
    finrank_commSpace_reflection H.xsub.q_nondegenerate _
  have hrW₀ : ∀ w ∈ H.xsub.clSub Q₀, r w = w := fun w hw =>
    TauCeti.QuadraticMap.reflection_apply_of_polar_eq_zero _ _
      (by rw [polar_comm]; exact H.polar_W₀_W' hw hvW')
  have hrW' : ∀ w ∈ H.xsub.clSub Q, r w ∈ H.xsub.clSub Q := by
    intro w hw
    rw [TauCeti.QuadraticMap.reflection_apply]
    exact sub_mem hw (Submodule.smul_mem _ _ hvW')
  have hrr : ∀ w : H.xsub.Qt, r (r w) = w := fun w => by
    have h := congrArg (fun e : H.xsub.Qt ≃ₗ[ZMod 2] H.xsub.Qt => e w)
      (TauCeti.QuadraticMap.reflection_mul_self H.xsub.q (v' : H.xsub.Qt))
    simpa using h
  have hrN : r ∈ H.ρG.range := by
    let a : TauCeti.QuadraticMap.orthogonalGroup H.xsub.q := H.xsub.ρ n₁
    let b : TauCeti.QuadraticMap.orthogonalGroup H.xsub.q := ⟨r, hrO⟩
    have hda : dicksonHom H.xsub.q H.xsub.q_nondegenerate a ≠ 1 := by
      intro h
      apply hn₁
      have hk : a ∈ (dicksonHom H.xsub.q H.xsub.q_nondegenerate).ker := h
      rw [dicksonHom_ker, mem_subgroupOf] at hk
      exact hk
    have hdb : dicksonHom H.xsub.q H.xsub.q_nondegenerate b ≠ 1 := by
      intro h
      have hk : b ∈ (dicksonHom H.xsub.q H.xsub.q_nondegenerate).ker := h
      rw [dicksonHom_ker, mem_subgroupOf, mem_omegaGroup, hr1] at hk
      exact Nat.not_even_one hk.2
    have hab : a⁻¹ * b ∈ (dicksonHom H.xsub.q H.xsub.q_nondegenerate).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, eq_of_ne_one_multiplicative hda hdb,
        inv_mul_cancel]
    rw [dicksonHom_ker, mem_subgroupOf] at hab
    obtain ⟨m, hm⟩ := hΩ hab
    refine ⟨n₁ * m, ?_⟩
    rw [map_mul, hm]
    show (a : H.xsub.Qt ≃ₗ[ZMod 2] H.xsub.Qt) * ((a⁻¹ * b : TauCeti.QuadraticMap.orthogonalGroup
      H.xsub.q) : H.xsub.Qt ≃ₗ[ZMod 2] H.xsub.Qt) = r
    rw [← Subgroup.coe_mul, mul_inv_cancel_left]
  obtain ⟨g₀, hg₀⟩ := hrN
  have hW₀x : ∀ w ∈ H.xsub.clSub Q₀, H.ρG ⟨x, H.x_mem_N⟩ w ∈ H.xsub.clSub Q₀ := by
    intro w hw
    rw [← H.map_ρG_W₀ (n := ⟨x, H.x_mem_N⟩) H.q0.x_Q₀]
    exact Submodule.mem_map_of_mem hw
  have hcommr : H.ρG g₀ * H.ρG ⟨x, H.x_mem_N⟩ = H.ρG ⟨x, H.x_mem_N⟩ * H.ρG g₀ := by
    rw [hg₀]
    refine LinearEquiv.ext fun u => ?_
    have hu : u ∈ H.xsub.clSub Q₀ ⊔ H.xsub.clSub Q := H.W₀_sup_W' ▸ Submodule.mem_top
    obtain ⟨u₀, hu₀, u₁, hu₁, rfl⟩ := Submodule.mem_sup.mp hu
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, map_add, map_add, map_add, map_add,
      hrW₀ _ (hW₀x u₀ hu₀), hrW₀ u₀ hu₀, H.ρx_W' hu₁, H.ρx_W' (hrW' u₁ hu₁)]
  set R₃ := AS76b.oddCoreIn (centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) with hR₃def
  have hxZ : x ∈ centerIn (sec3B A₁ x) := by
    rw [H.q0.dData.suz.B_center]
    exact mem_zpowers x
  have hxB : x ∈ sec3B A₁ x := (mem_inf.mp hxZ).1
  have hR₃C : R₃ ≤ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G) := AS76b.oddCoreIn_le _
  have hR₃x : ∀ s ∈ R₃, s * x = x * s := fun s hs =>
    (mem_centralizer_iff.mp (hOB hs) x hxB).symm
  have hNR : ∀ n ∈ H.xsub.N, n ∈ normalizer (R₃ : Set G) := fun n hn =>
    AS76b.normalizer_le_normalizer_oddCoreIn _ (mem_normalizer_centralizer hn)
  have hQ₁2 : IsPGroup 2 ↥(Q₀ ⊔ Q) := IsPGroup.of_card (n := 9) H.card
  have hR₃Q₁ : R₃ ⊓ (Q₀ ⊔ Q) = ⊥ := AS76b.oddCoreIn_inf_eq_bot hQ₁2
  have hR₃N : R₃ ≤ H.xsub.N := hR₃C.trans (centralizer_le_normalizer _)
  have hy : x⁻¹ * ((g₀ : G) * x * (g₀ : G)⁻¹) ∈ (Q₀ ⊔ Q) ⊔ R₃ := by
    have h1 : H.xsub.ρ ((⟨x, H.x_mem_N⟩ : H.xsub.N)⁻¹ * (g₀ * ⟨x, H.x_mem_N⟩ * g₀⁻¹)) = 1 := by
      rw [← H.ρG_eq_one_iff, map_mul, map_inv, map_mul, map_mul, map_inv, hcommr,
        mul_inv_cancel_right, inv_mul_cancel]
    obtain ⟨c, hc, hcn⟩ := (H.xsub.ρ_eq_one_iff _).mp h1
    have hcQ : c ∈ Q₀ ⊔ Q := hc
    have hcn' : c⁻¹ * (x⁻¹ * ((g₀ : G) * x * (g₀ : G)⁻¹)) ∈
        centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G) := hcn
    have h2 := H.le_sup_oddCoreIn_of_le_centralizer (le_refl _) hcn'
    rw [show x⁻¹ * ((g₀ : G) * x * (g₀ : G)⁻¹) =
      c * (c⁻¹ * (x⁻¹ * ((g₀ : G) * x * (g₀ : G)⁻¹))) by group]
    exact mul_mem (mem_sup_left hcQ) h2
  have hy' : x⁻¹ * ((g₀ : G) * x * (g₀ : G)⁻¹) ∈ (((Q₀ ⊔ Q) ⊔ R₃ : Subgroup G) : Set G) := hy
  rw [coe_mul_of_left_le_normalizer_right (Q₀ ⊔ Q) R₃ (fun a ha => hNR a (H.xsub.le_N ha)),
    Set.mem_mul] at hy'
  obtain ⟨q, hq, s, hs, hqs⟩ := hy'
  set u := x * q with hudef
  have hyu : (g₀ : G) * x * (g₀ : G)⁻¹ = u * s := by
    rw [hudef, mul_assoc x q s, hqs]
    group
  have hsu : s * u = u * s := by
    have h1 : s * x = x * s := hR₃x s hs
    have h2 : s * q = q * s := (mem_centralizer_iff.mp (hR₃C hs) q hq).symm
    calc s * u = s * x * q := by rw [hudef, mul_assoc]
      _ = x * (s * q) := by rw [h1, mul_assoc]
      _ = x * (q * s) := by rw [h2]
      _ = u * s := by rw [hudef, mul_assoc]
  have hxQ₁ : ∀ a ∈ Q₀ ⊔ Q, x * a * x⁻¹ ∈ Q₀ ⊔ Q := fun a ha =>
    (mem_normalizer_iff.mp H.x_mem_N a).mp ha
  have hu3Q : u ^ 3 ∈ Q₀ ⊔ Q := by
    have e : u ^ 3 = (x * q * x⁻¹) * (x * (x * q * x⁻¹) * x⁻¹) * x ^ 3 * q := by
      rw [hudef, pow_three', pow_three']
      group
    rw [e, H.x_pow_three, mul_one]
    exact mul_mem (mul_mem (hxQ₁ q hq) (hxQ₁ _ (hxQ₁ q hq))) hq
  have hy3 : ((g₀ : G) * x * (g₀ : G)⁻¹) ^ 3 = 1 := by
    rw [conj_pow, H.x_pow_three, mul_one, mul_inv_cancel]
  have hu3R : u ^ 3 ∈ R₃ := by
    have h1 : u ^ 3 * s ^ 3 = 1 := by
      rw [← (Commute.mul_pow (show Commute u s from hsu.symm) 3), ← hyu, hy3]
    rw [eq_inv_of_mul_eq_one_left h1]
    exact inv_mem (pow_mem hs 3)
  have hu3 : u ^ 3 = 1 := by
    have h : u ^ 3 ∈ R₃ ⊓ (Q₀ ⊔ Q) := ⟨hu3R, hu3Q⟩
    rw [hR₃Q₁, mem_bot] at h
    exact h
  have hu1 : u ≠ 1 := by
    intro h
    have hxq : x = q⁻¹ := eq_inv_of_mul_eq_one_left h
    have hx1 : H.xsub.ρ ⟨x, H.x_mem_N⟩ = 1 :=
      H.xsub.ρ_eq_one_of_mem (show x ∈ Q₀ ⊔ Q by rw [hxq]; exact inv_mem hq)
    have h3 := H.orderOf_ρx
    rw [(H.ρG_eq_one_iff _).mpr hx1, orderOf_one] at h3
    omega
  have hu3' : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  set L : Subgroup G := (Q₀ ⊔ Q) ⊔ zpowers x with hLdef
  have hx3 : orderOf x = 3 := H.q0.dData.suz.setting.order_x
  have hcardX : Nat.card (zpowers x) = 3 := by rw [Nat.card_zpowers, hx3]
  have hcardL : Nat.card L = 2 ^ 9 * 3 := by
    have h := card_sup_mul_card_inf (H := Q₀ ⊔ Q) (R := zpowers x)
      (zpowers_le.mpr H.x_mem_N)
    have hinf : (Q₀ ⊔ Q) ⊓ zpowers x = ⊥ :=
      disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard (by rw [H.card, hcardX]; norm_num))
    rw [hinf, card_bot, mul_one, H.card, hcardX] at h
    exact h
  have hsyl : ∀ {w : G}, w ∈ L → orderOf w = 3 → IsSylowOf 3 (zpowers w) L := by
    intro w hw hw3
    have hcardW : Nat.card (zpowers w) = 3 := by rw [Nat.card_zpowers, hw3]
    refine isSylowOf_iff.mpr ⟨zpowers_le.mpr hw, IsPGroup.of_card (n := 1)
      (by rw [hcardW, pow_one]), ?_⟩
    have h := Subgroup.relIndex_mul_card (zpowers w) L
    rw [inf_of_le_left (zpowers_le.mpr hw), hcardW, hcardL] at h
    have h2 : (zpowers w).relIndex L = 2 ^ 9 := by omega
    rw [h2]
    norm_num
  have hxL : x ∈ L := mem_sup_right (mem_zpowers x)
  have huL : u ∈ L := mul_mem hxL (mem_sup_left hq)
  obtain ⟨l, hlL, hl⟩ := IsSylowOf.exists_mem_conj (hsyl hxL hx3) (hsyl huL hu3')
  have hl1 := (hl u).mp (mem_zpowers _)
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hl1
  let Lρ : Subgroup G :=
    { carrier := {m | ∃ hm : m ∈ H.xsub.N, H.ρG ⟨m, hm⟩ * H.ρG ⟨x, H.x_mem_N⟩ =
        H.ρG ⟨x, H.x_mem_N⟩ * H.ρG ⟨m, hm⟩ ∧ ∀ w ∈ H.xsub.clSub Q, H.ρG ⟨m, hm⟩ w = w}
      mul_mem' := by
        rintro a c ⟨ha, ha1, ha2⟩ ⟨hc, hc1, hc2⟩
        refine ⟨mul_mem ha hc, ?_, fun w hw => ?_⟩
        · rw [show (⟨a * c, mul_mem ha hc⟩ : H.xsub.N) = ⟨a, ha⟩ * ⟨c, hc⟩ from rfl, map_mul,
            mul_assoc, hc1, ← mul_assoc, ha1, mul_assoc]
        · rw [show (⟨a * c, mul_mem ha hc⟩ : H.xsub.N) = ⟨a, ha⟩ * ⟨c, hc⟩ from rfl, map_mul,
            LinearEquiv.mul_apply, hc2 w hw, ha2 w hw]
      one_mem' := ⟨one_mem _, by
        rw [show (⟨1, one_mem _⟩ : H.xsub.N) = 1 from rfl, map_one, one_mul, mul_one],
        fun w _ => by rw [show (⟨1, one_mem _⟩ : H.xsub.N) = 1 from rfl, map_one]; rfl⟩
      inv_mem' := by
        rintro a ⟨ha, ha1, ha2⟩
        refine ⟨inv_mem ha, ?_, fun w hw => ?_⟩
        · rw [show (⟨a⁻¹, inv_mem ha⟩ : H.xsub.N) = (⟨a, ha⟩)⁻¹ from rfl, map_inv]
          exact (Commute.inv_left (show Commute (H.ρG ⟨a, ha⟩) (H.ρG ⟨x, H.x_mem_N⟩) from ha1)).eq
        · rw [show (⟨a⁻¹, inv_mem ha⟩ : H.xsub.N) = (⟨a, ha⟩)⁻¹ from rfl, map_inv]
          have h := ha2 w hw
          calc (H.ρG ⟨a, ha⟩)⁻¹ w = (H.ρG ⟨a, ha⟩)⁻¹ (H.ρG ⟨a, ha⟩ w) := by rw [h]
            _ = w := by rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl }
  have hLLρ : L ≤ Lρ := by
    refine sup_le (fun a ha => ⟨H.xsub.le_N ha, ?_, fun w _ => ?_⟩) ?_
    · rw [(H.ρG_eq_one_iff _).mpr (H.xsub.ρ_eq_one_of_mem (g := ⟨a, H.xsub.le_N ha⟩) ha),
        one_mul, mul_one]
    · rw [(H.ρG_eq_one_iff _).mpr (H.xsub.ρ_eq_one_of_mem (g := ⟨a, H.xsub.le_N ha⟩) ha)]
      rfl
    · rw [zpowers_le]
      exact ⟨H.x_mem_N, rfl, fun w hw => H.ρx_W' hw⟩
  obtain ⟨hlN, hl1ρ, hl2ρ⟩ := hLLρ hlL
  set gN : H.xsub.N := (⟨l, hlN⟩ : H.xsub.N)⁻¹ * g₀ with hgN
  have hs'R : l⁻¹ * s * l ∈ R₃ := by
    have h1 := (mem_normalizer_iff.mp (hNR _ (inv_mem hlN)) s).mp hs
    rwa [inv_inv] at h1
  have hs'N : l⁻¹ * s * l ∈ H.xsub.N := hR₃N hs'R
  have hgx : (gN : G) * x * (gN : G)⁻¹ = x ^ k * (l⁻¹ * s * l) := by
    rw [hk]
    show l⁻¹ * (g₀ : G) * x * (l⁻¹ * (g₀ : G))⁻¹ = l⁻¹ * u * l * (l⁻¹ * s * l)
    rw [show l⁻¹ * (g₀ : G) * x * (l⁻¹ * (g₀ : G))⁻¹ =
      l⁻¹ * ((g₀ : G) * x * (g₀ : G)⁻¹) * l by group, hyu]
    group
  have hρgx : H.ρG gN * H.ρG ⟨x, H.x_mem_N⟩ * (H.ρG gN)⁻¹ = H.ρG ⟨x, H.x_mem_N⟩ := by
    rw [hgN, map_mul, map_inv]
    calc (H.ρG ⟨l, hlN⟩)⁻¹ * H.ρG g₀ * H.ρG ⟨x, H.x_mem_N⟩ *
          ((H.ρG ⟨l, hlN⟩)⁻¹ * H.ρG g₀)⁻¹ =
        (H.ρG ⟨l, hlN⟩)⁻¹ * (H.ρG g₀ * H.ρG ⟨x, H.x_mem_N⟩) * (H.ρG g₀)⁻¹ *
          H.ρG ⟨l, hlN⟩ := by group
      _ = (H.ρG ⟨l, hlN⟩)⁻¹ * H.ρG ⟨x, H.x_mem_N⟩ * H.ρG ⟨l, hlN⟩ := by
          rw [hcommr]; group
      _ = H.ρG ⟨x, H.x_mem_N⟩ := by
          rw [mul_assoc, ← hl1ρ, ← mul_assoc, inv_mul_cancel, one_mul]
  have hρs' : H.ρG ⟨l⁻¹ * s * l, hs'N⟩ = 1 :=
    (H.ρG_eq_one_iff _).mpr (H.xsub.ρ_eq_one_of_mem_centralizer (hR₃C hs'R))
  have hxk : x ^ k = x := by
    have hρk : H.ρG ⟨x, H.x_mem_N⟩ ^ k = H.ρG ⟨x, H.x_mem_N⟩ := by
      have h1 : (gN * ⟨x, H.x_mem_N⟩ * gN⁻¹ : H.xsub.N) =
          ⟨x, H.x_mem_N⟩ ^ k * ⟨l⁻¹ * s * l, hs'N⟩ := by
        apply Subtype.ext
        show (gN : G) * x * (gN : G)⁻¹ =
          ((⟨x, H.x_mem_N⟩ ^ k : H.xsub.N) : G) * (l⁻¹ * s * l)
        rw [SubgroupClass.coe_zpow]
        exact hgx
      have h2 : H.ρG (gN * ⟨x, H.x_mem_N⟩ * gN⁻¹) = H.ρG ⟨x, H.x_mem_N⟩ := by
        rw [map_mul, map_mul, map_inv, hρgx]
      have h3 : H.ρG (⟨x, H.x_mem_N⟩ ^ k * ⟨l⁻¹ * s * l, hs'N⟩) = H.ρG ⟨x, H.x_mem_N⟩ ^ k := by
        rw [map_mul, map_zpow, hρs', mul_one]
      rw [← h3, ← h1, h2]
    have hk1 : (k : ℤ) % 3 = 1 := by
      have h1 : H.ρG ⟨x, H.x_mem_N⟩ ^ (k - 1) = 1 := by
        rw [zpow_sub_one, hρk, mul_inv_cancel]
      have h2 := orderOf_dvd_iff_zpow_eq_one.mpr h1
      rw [H.orderOf_ρx] at h2
      omega
    rw [← zpow_mod_orderOf, hx3]
    rw [show ((3 : ℕ) : ℤ) = 3 by rfl, hk1, zpow_one]
  have hgx' : (gN : G) * x * (gN : G)⁻¹ = x * (l⁻¹ * s * l) := by rw [hgx, hxk]
  have hgB : ∀ b ∈ sec3B A₁ x, (gN : G) * b * (gN : G)⁻¹ ∈ centralizer ({x} : Set G) := by
    intro b hb
    set w := (gN : G)⁻¹ * (l⁻¹ * s * l) * gN with hwdef
    have hwR : w ∈ R₃ := by
      have h1 := (mem_normalizer_iff.mp (hNR _ (inv_mem gN.2)) _).mp hs'R
      rwa [inv_inv] at h1
    have hbw : b * w = w * b := mem_centralizer_iff.mp (hOB hwR) b hb
    have hbw' : b * w⁻¹ = w⁻¹ * b := by
      calc b * w⁻¹ = w⁻¹ * (w * b) * w⁻¹ := by group
        _ = w⁻¹ * (b * w) * w⁻¹ := by rw [← hbw]
        _ = w⁻¹ * b := by group
    have hbx : b * x = x * b := mem_centralizer_iff.mp (mem_inf.mp hxZ).2 b hb
    have hxeq : x = (gN : G) * (x * w⁻¹) * (gN : G)⁻¹ := by
      have e1 : (gN : G) * (x * w⁻¹) * (gN : G)⁻¹ =
          ((gN : G) * x * (gN : G)⁻¹) * ((gN : G) * w * (gN : G)⁻¹)⁻¹ := by group
      have e2 : (gN : G) * w * (gN : G)⁻¹ = l⁻¹ * s * l := by rw [hwdef]; group
      rw [e1, e2, hgx']
      group
    have hbxw : b * x * w⁻¹ = x * w⁻¹ * b := by rw [hbx, mul_assoc, hbw', ← mul_assoc]
    rw [mem_centralizer_singleton_iff]
    calc (gN : G) * b * (gN : G)⁻¹ * x =
        (gN : G) * b * (gN : G)⁻¹ * ((gN : G) * (x * w⁻¹) * (gN : G)⁻¹) := by rw [← hxeq]
      _ = (gN : G) * (b * x * w⁻¹) * (gN : G)⁻¹ := by group
      _ = (gN : G) * (x * w⁻¹ * b) * (gN : G)⁻¹ := by rw [hbxw]
      _ = (gN : G) * (x * w⁻¹) * (gN : G)⁻¹ * ((gN : G) * b * (gN : G)⁻¹) := by group
      _ = x * ((gN : G) * b * (gN : G)⁻¹) := by rw [← hxeq]
  have hgz : (gN : G) * z * (gN : G)⁻¹ = z := by
    have h1 := (mem_normalizer_iff.mp (Sec3.mem_normalizer_centerIn (H := Q₀ ⊔ Q) gN.2) z).mp
      (by rw [H.center_sup]; exact mem_zpowers z)
    rw [H.center_sup] at h1
    rcases H.xsub.mem_zpowers_z_iff.mp h1 with h | h
    · exfalso
      apply H.z_ne_one
      calc z = (gN : G)⁻¹ * ((gN : G) * z * (gN : G)⁻¹) * gN := by group
        _ = 1 := by rw [h]; group
    · exact h
  have hx2 : (gN : G) * x * (gN : G)⁻¹ ∈ zpowers x := by
    have h1 := (mem_normalizer_iff.mp (Sec3.mem_normalizer_centerIn (hBn gN hgB hgz)) x).mp hxZ
    rwa [H.q0.dData.suz.B_center] at h1
  rw [hgx'] at hx2
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hx2
  have hs'1 : l⁻¹ * s * l = 1 := by
    have e : l⁻¹ * s * l = x ^ (j - 1) := by
      rw [show j - 1 = -1 + j by ring, zpow_add, zpow_neg_one, hj]
      group
    have h0 : (⟨l⁻¹ * s * l, hs'N⟩ : H.xsub.N) = ⟨x, H.x_mem_N⟩ ^ (j - 1) :=
      Subtype.ext (by rw [SubgroupClass.coe_zpow]; exact e)
    have h1 : H.ρG ⟨x, H.x_mem_N⟩ ^ (j - 1) = 1 := by rw [← map_zpow, ← h0, hρs']
    have h2 := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rw [H.orderOf_ρx] at h2
    rw [e]
    exact orderOf_dvd_iff_zpow_eq_one.mp (by rw [hx3]; exact h2)
  have hgxc : (gN : G) * x = x * (gN : G) := by
    calc (gN : G) * x = (gN : G) * x * (gN : G)⁻¹ * gN := by group
      _ = x * gN := by rw [hgx', hs'1, mul_one]
  have hgW' : ∀ w ∈ H.xsub.clSub Q, H.ρG gN w = r w := by
    intro w hw
    rw [hgN, map_mul, map_inv, LinearEquiv.mul_apply, hg₀]
    have h := hl2ρ (r w) (hrW' w hw)
    calc (H.ρG ⟨l, hlN⟩)⁻¹ (r w) = (H.ρG ⟨l, hlN⟩)⁻¹ (H.ρG ⟨l, hlN⟩ (r w)) := by rw [h]
      _ = r w := by rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
  have hgQ : (gN : G) ∈ normalizer (Q : Set G) := by
    refine H.xsub.mem_normalizer_of_map_ρ_clSub H.Q_le H.z_mem_Q gN ?_
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      change H.ρG gN w ∈ _
      rw [hgW' w hw]
      exact hrW' w hw
    · intro w hw
      refine ⟨r w, hrW' w hw, ?_⟩
      change H.ρG gN (r w) = w
      rw [hgW' _ (hrW' w hw), hrr]
  obtain ⟨b, hbB, hbc⟩ := hinner gN hgxc
  have hcQ : b⁻¹ * (gN : G) ∈ centralizer (Q : Set G) :=
    Subgroup.centralizer_le (H.q0.dData.suz.Q_le.trans H.q0.dData.suz.T_le) hbc
  have hbQ : b ∈ normalizer (Q : Set G) := by
    rw [show b = (gN : G) * (b⁻¹ * gN)⁻¹ by group]
    exact mul_mem hgQ (inv_mem (centralizer_le_normalizer _ hcQ))
  have hbz : b ∈ centralizer ({z} : Set G) := by
    have h1 := Sec3.mem_normalizer_centerIn hbQ
    rw [H.q0.dData.suz.Q_center] at h1
    have h2 := (mem_normalizer_iff.mp h1 z).mp (mem_zpowers z)
    rcases H.xsub.mem_zpowers_z_iff.mp h2 with h | h
    · exfalso
      apply H.z_ne_one
      calc z = b⁻¹ * (b * z * b⁻¹) * b := by group
        _ = 1 := by rw [h]; group
    · have h' : b * z * b⁻¹ = z := h
      refine mem_centralizer_singleton_iff.mpr ?_
      calc b * z = b * z * b⁻¹ * b := by group
        _ = z * b := by rw [h']
  obtain ⟨b₀, hb₀, i, hbi⟩ := hCBz b (mem_inf.mpr ⟨hbB, hbz⟩)
  have hgb₀ : ∀ w ∈ H.xsub.clSub Q, H.ρG gN w = H.ρG ⟨b₀, H.B₀_le_N hb₀⟩ w := by
    intro w hw
    obtain ⟨a, haQ, ha, rfl⟩ := H.xsub.mem_clSub_iff.mp hw
    rw [H.ρG_cl _ ha, H.ρG_cl _ ha]
    congr 1
    have h1 : (b⁻¹ * (gN : G)) * a = a * (b⁻¹ * gN) :=
      (mem_centralizer_iff.mp hcQ a haQ).symm
    have h2 : x ^ i * a = a * x ^ i :=
      (mem_centralizer_iff.mp (zpow_mem H.x_mem_centralizer_Q i) a haQ).symm
    show (gN : G) * a * (gN : G)⁻¹ = b₀ * a * b₀⁻¹
    calc (gN : G) * a * (gN : G)⁻¹ =
        b * ((b⁻¹ * gN) * a) * (b⁻¹ * gN)⁻¹ * b⁻¹ := by group
      _ = b * (a * (b⁻¹ * gN)) * (b⁻¹ * gN)⁻¹ * b⁻¹ := by rw [h1]
      _ = b * a * b⁻¹ := by group
      _ = b₀ * (x ^ i * a) * x ^ (-i) * b₀⁻¹ := by rw [hbi]; group
      _ = b₀ * (a * x ^ i) * x ^ (-i) * b₀⁻¹ := by rw [h2]
      _ = b₀ * a * b₀⁻¹ := by group
  have hmap : (H.xsub.clSub Q).map ((H.ρG gN : H.xsub.Qt →ₗ[ZMod 2] H.xsub.Qt) - 1) =
      (H.xsub.clSub Q).map ((H.ρG ⟨b₀, H.B₀_le_N hb₀⟩ : H.xsub.Qt →ₗ[ZMod 2] H.xsub.Qt) - 1) := by
    ext u
    simp only [Submodule.mem_map, LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, by rw [hgb₀ w hw]⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, by rw [hgb₀ w hw]⟩
  have hmapr : (H.xsub.clSub Q).map ((H.ρG gN : H.xsub.Qt →ₗ[ZMod 2] H.xsub.Qt) - 1) =
      (H.xsub.clSub Q).map ((r : H.xsub.Qt →ₗ[ZMod 2] H.xsub.Qt) - 1) := by
    ext u
    simp only [Submodule.mem_map, LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, by rw [hgW' w hw]⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, by rw [hgW' w hw]⟩
  have hodd : finrank (ZMod 2) ((H.xsub.clSub Q).map ((r : H.xsub.Qt →ₗ[ZMod 2] H.xsub.Qt) - 1))
      = 1 := by
    have hW₀r : (H.xsub.clSub Q₀).map (r : H.xsub.Qt →ₗ[ZMod 2] H.xsub.Qt) = H.xsub.clSub Q₀ := by
      ext u
      constructor
      · rintro ⟨w, hw, rfl⟩
        change r w ∈ _
        rw [hrW₀ w hw]
        exact hw
      · intro hu
        exact ⟨u, hu, hrW₀ u hu⟩
    have hW'r : (H.xsub.clSub Q).map (r : H.xsub.Qt →ₗ[ZMod 2] H.xsub.Qt) = H.xsub.clSub Q := by
      apply le_antisymm
      · rintro _ ⟨w, hw, rfl⟩
        exact hrW' w hw
      · intro w hw
        exact ⟨r w, hrW' w hw, hrr w⟩
    have h := finrank_commSpace_split H.W₀_sup_W' H.W₀_inf_W' hW₀r hW'r
    have h0 : (H.xsub.clSub Q₀).map ((r : H.xsub.Qt →ₗ[ZMod 2] H.xsub.Qt) - 1) = ⊥ := by
      refine eq_bot_iff.mpr ?_
      rintro _ ⟨w, hw, rfl⟩
      rw [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply, hrW₀ w hw, sub_self]
      exact Submodule.zero_mem _
    rw [h0, finrank_bot, zero_add, hr1] at h
    exact h.symm
  have heven := (mem_omegaGroup.mp (H.resB₀_mem_omega ⟨b₀, hb₀⟩)).2
  rw [show H.resB₀ ⟨b₀, hb₀⟩ = resLE (H.xsub.clSub Q) (g := H.ρG ⟨b₀, H.B₀_le_N hb₀⟩)
      (H.map_ρG_W' (H.B₀_quot.2 hb₀)) from rfl, finrank_commSpace_resLE, ← hmap, hmapr,
    hodd] at heven
  exact Nat.not_even_one heven

end Sec38Hyp

end CFSG.ComponentClassification.AS81

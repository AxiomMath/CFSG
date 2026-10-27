module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step38F

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

theorem le_sup_oddCoreIn_of_le_centralizer {C₁ : Subgroup G}
    (hC₁ : C₁ ≤ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) :
    C₁ ≤ (Q₀ ⊔ Q) ⊔ AS76b.oddCoreIn C₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 ↥C₁ := default
  have hPz : (P : Subgroup ↥C₁).map C₁.subtype ≤ zpowers z :=
    H.le_zpowers_of_le_centralizer (P.isPGroup'.map _) ((map_subtype_le _).trans hC₁)
  have hPc : ∀ p ∈ (P : Subgroup ↥C₁), ∀ c : ↥C₁, c * p = p * c := by
    intro p hp c
    have hpz : (p : G) ∈ zpowers z := hPz ⟨p, hp, rfl⟩
    have hzc : z * (c : G) = (c : G) * z :=
      mem_centralizer_iff.mp (hC₁ c.2) z (H.Q_le H.z_mem_Q)
    apply Subtype.ext
    rcases H.xsub.mem_zpowers_z_iff.mp hpz with h | h
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, h, mul_one, one_mul]
    · have h' : (p : G) = z := h
      rw [Subgroup.coe_mul, Subgroup.coe_mul, h']
      exact hzc.symm
  have hP : normalizer ((P : Subgroup ↥C₁) : Set ↥C₁) ≤
      centralizer ((P : Subgroup ↥C₁) : Set ↥C₁) :=
    fun c _ => mem_centralizer_iff.mpr fun p hp => (hPc p hp c).symm
  have hcomp := MonoidHom.ker_transferSylow_isComplement' P hP
  have hodd : Odd (Nat.card (MonoidHom.transferSylow P hP).ker) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (MonoidHom.not_dvd_card_ker_transferSylow P hP))
  have hKO : (MonoidHom.transferSylow P hP).ker ≤ CFSG.Assembly.oddCore ↥C₁ :=
    le_sSup ⟨inferInstance, hodd⟩
  intro c hc
  have hctop : (⟨c, hc⟩ : ↥C₁) ∈ (MonoidHom.transferSylow P hP).ker ⊔ (P : Subgroup ↥C₁) := by
    rw [hcomp.sup_eq_top]
    exact mem_top _
  have hmap := Subgroup.mem_map_of_mem C₁.subtype hctop
  rw [Subgroup.map_sup] at hmap
  exact (sup_le ((map_mono hKO).trans le_sup_right)
    (hPz.trans ((zpowers_le.mpr (H.Q_le H.z_mem_Q)).trans le_sup_left))) hmap

theorem centralizer_le_zpowers
    (hO : AS76b.oddCoreIn (normalizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) = ⊥) :
    centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G) ≤ zpowers z := by
  set C := centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G) with hCdef
  have hCN : C ≤ H.xsub.N := centralizer_le_normalizer _
  have hNC : H.xsub.N ≤ normalizer (C : Set G) := by
    intro n hn
    have key : ∀ m ∈ H.xsub.N, ∀ c ∈ C, m * c * m⁻¹ ∈ C := by
      intro m hm c hc
      refine mem_centralizer_iff.mpr fun a ha => ?_
      have ha' : m⁻¹ * a * m ∈ Q₀ ⊔ Q := by
        have h := (mem_normalizer_iff.mp (inv_mem hm) a).mp ha
        rwa [inv_inv] at h
      have h1 := mem_centralizer_iff.mp hc _ ha'
      calc a * (m * c * m⁻¹) = m * ((m⁻¹ * a * m) * c) * m⁻¹ := by group
        _ = m * (c * (m⁻¹ * a * m)) * m⁻¹ := by rw [h1]
        _ = m * c * m⁻¹ * a := by group
    exact G2.mem_normalizer_of_conj (key n hn) fun c hc => by
      simpa using key n⁻¹ (inv_mem hn) c hc
  have hOC : AS76b.oddCoreIn C = ⊥ := by
    have hON := (hNC.trans (AS76b.normalizer_le_normalizer_oddCoreIn C))
    have hOCN : AS76b.oddCoreIn C ≤ H.xsub.N := (AS76b.oddCoreIn_le C).trans hCN
    have hnorm : ((AS76b.oddCoreIn C).subgroupOf H.xsub.N).Normal :=
      ⟨fun a ha w => mem_subgroupOf.mpr ((mem_normalizer_iff.mp (hON w.2) a).mp
        (mem_subgroupOf.mp ha))⟩
    have hodd : Odd (Nat.card ((AS76b.oddCoreIn C).subgroupOf H.xsub.N)) := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hOCN).toEquiv]
      exact AS76b.odd_card_oddCoreIn C
    have hle : (AS76b.oddCoreIn C).subgroupOf H.xsub.N ≤ CFSG.Assembly.oddCore ↥H.xsub.N :=
      le_sSup ⟨hnorm, hodd⟩
    rw [eq_bot_iff]
    intro c hc
    have h1 : (⟨c, hOCN hc⟩ : ↥H.xsub.N) ∈ CFSG.Assembly.oddCore ↥H.xsub.N :=
      hle (mem_subgroupOf.mpr hc)
    have h2 : c ∈ AS76b.oddCoreIn (normalizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) :=
      ⟨_, h1, rfl⟩
    rw [hO] at h2
    exact h2
  have h1 := H.le_sup_oddCoreIn_of_le_centralizer (le_refl C)
  rw [hOC, sup_bot_eq] at h1
  intro c hc
  rw [← H.center_sup]
  exact ⟨h1 hc, hc⟩

theorem mem_Q₁_of_ρ_eq_one (hC : centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G) ≤ zpowers z)
    {n : H.xsub.N} (h : H.xsub.ρ n = 1) : (n : G) ∈ Q₀ ⊔ Q := by
  obtain ⟨c, hc, hcn⟩ := (H.xsub.ρ_eq_one_iff n).mp h
  have hcQ : c ∈ Q₀ ⊔ Q := hc
  have h1 : c⁻¹ * (n : G) ∈ Q₀ ⊔ Q := (zpowers_le.mpr (H.Q_le H.z_mem_Q)) (hC hcn)
  rw [show (n : G) = c * (c⁻¹ * n) by group]
  exact mul_mem hcQ h1

omit H in
theorem eq_of_ne_one_multiplicative {a b : Multiplicative (ZMod 2)} (ha : a ≠ 1) (hb : b ≠ 1) :
    a = b := by
  induction a using Multiplicative.rec with
  | ofAdd a =>
    induction b using Multiplicative.rec with
    | ofAdd b =>
      rcases zmod_two_eq_zero_or_one a with rfl | rfl
      · exact absurd rfl ha
      rcases zmod_two_eq_zero_or_one b with rfl | rfl
      · exact absurd rfl hb
      rfl

theorem range_le_omega (hC : centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G) ≤ zpowers z)
    (hΩ : omegaGroup H.xsub.q H.xsub.q_nondegenerate ≤ H.ρG.range)
    (hinner : ∀ w : G, w * x = x * w →
      ∃ b ∈ sec3B A₁ x, b⁻¹ * w ∈ centralizer (sec3B A₁ x : Set G))
    (hCBz : ∀ k ∈ sec3B A₁ x ⊓ centralizer ({z} : Set G), ∃ b₀ ∈ B₀, ∃ i : ℤ, k = b₀ * x ^ i) :
    H.ρG.range ≤ omegaGroup H.xsub.q H.xsub.q_nondegenerate := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
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
  have hy : x⁻¹ * ((g₀ : G) * x * (g₀ : G)⁻¹) ∈ Q₀ ⊔ Q := by
    have h1 : H.xsub.ρ ((⟨x, H.x_mem_N⟩ : H.xsub.N)⁻¹ * (g₀ * ⟨x, H.x_mem_N⟩ * g₀⁻¹)) = 1 := by
      rw [← H.ρG_eq_one_iff, map_mul, map_inv, map_mul, map_mul, map_inv, hcommr,
        mul_inv_cancel_right, inv_mul_cancel]
    exact H.mem_Q₁_of_ρ_eq_one hC h1
  set L : Subgroup G := (Q₀ ⊔ Q) ⊔ zpowers x with hLdef
  have hLN : L ≤ H.xsub.N := sup_le le_normalizer (zpowers_le.mpr H.x_mem_N)
  have hx3 : orderOf x = 3 := H.q0.dData.suz.setting.order_x
  have hcardX : Nat.card (zpowers x) = 3 := by rw [Nat.card_zpowers, hx3]
  have hcardL : Nat.card L = 2 ^ 9 * 3 := by
    have h := card_sup_mul_card_inf (H := Q₀ ⊔ Q) (R := zpowers x)
      (zpowers_le.mpr H.x_mem_N)
    have hinf : (Q₀ ⊔ Q) ⊓ zpowers x = ⊥ :=
      disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard (by rw [H.card, hcardX]; norm_num))
    rw [hinf, card_bot, mul_one, H.card, hcardX] at h
    exact h
  have hsyl : ∀ {u : G}, u ∈ L → orderOf u = 3 → IsSylowOf 3 (zpowers u) L := by
    intro u hu hu3
    have hcardU : Nat.card (zpowers u) = 3 := by rw [Nat.card_zpowers, hu3]
    refine isSylowOf_iff.mpr ⟨zpowers_le.mpr hu, IsPGroup.of_card (n := 1)
      (by rw [hcardU, pow_one]), ?_⟩
    have h := Subgroup.relIndex_mul_card (zpowers u) L
    rw [inf_of_le_left (zpowers_le.mpr hu), hcardU, hcardL] at h
    have h2 : (zpowers u).relIndex L = 2 ^ 9 := by omega
    rw [h2]
    norm_num
  have hxL : x ∈ L := mem_sup_right (mem_zpowers x)
  have hyL : (g₀ : G) * x * (g₀ : G)⁻¹ ∈ L := by
    rw [show (g₀ : G) * x * (g₀ : G)⁻¹ = x * (x⁻¹ * ((g₀ : G) * x * (g₀ : G)⁻¹)) by group]
    exact mul_mem hxL (mem_sup_left hy)
  have hy3 : orderOf ((g₀ : G) * x * (g₀ : G)⁻¹) = 3 := by
    rw [← hx3]
    exact MulEquiv.orderOf_eq (MulAut.conj (g₀ : G)) x
  obtain ⟨l, hlL, hl⟩ := IsSylowOf.exists_mem_conj (hsyl hxL hx3) (hsyl hyL hy3)
  have hl1 := (hl ((g₀ : G) * x * (g₀ : G)⁻¹)).mp (mem_zpowers _)
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
  have hgx : (gN : G) * x * (gN : G)⁻¹ = x ^ k := by
    rw [hk]
    show l⁻¹ * (g₀ : G) * x * (l⁻¹ * (g₀ : G))⁻¹ = l⁻¹ * ((g₀ : G) * x * (g₀ : G)⁻¹) * l
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
  have hgxc : (gN : G) * x = x * (gN : G) := by
    have hρk : H.ρG ⟨x, H.x_mem_N⟩ ^ k = H.ρG ⟨x, H.x_mem_N⟩ := by
      have h1 : (gN * ⟨x, H.x_mem_N⟩ * gN⁻¹ : H.xsub.N) = ⟨x, H.x_mem_N⟩ ^ k :=
        Subtype.ext (by rw [SubgroupClass.coe_zpow]; exact hgx)
      rw [← map_zpow, ← h1, map_mul, map_mul, map_inv, hρgx]
    have hk1 : (k : ℤ) % 3 = 1 := by
      have h1 : H.ρG ⟨x, H.x_mem_N⟩ ^ (k - 1) = 1 := by
        rw [zpow_sub_one, hρk, mul_inv_cancel]
      have h2 := orderOf_dvd_iff_zpow_eq_one.mpr h1
      rw [H.orderOf_ρx] at h2
      omega
    have hxk : x ^ k = x := by
      rw [← zpow_mod_orderOf, hx3]
      rw [show ((3 : ℕ) : ℤ) = 3 by rfl, hk1, zpow_one]
    calc (gN : G) * x = (gN : G) * x * (gN : G)⁻¹ * gN := by group
      _ = x * gN := by rw [hgx, hxk]
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

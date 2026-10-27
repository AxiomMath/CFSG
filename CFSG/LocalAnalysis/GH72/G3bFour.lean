module

public import CFSG.LocalAnalysis.GH72.L2Local
public import CFSG.LocalAnalysis.GH72.DDLocal
public import CFSG.Timmesfeld.Bridge.SchurNarrowCore

public section

namespace CFSG.GH72

open Subgroup
open CFSG.CGT.Foote81L6

namespace Sec3Setting

variable {G : Type*} [Group G] [Finite G]

variable (𝔖 : Sec3Setting G)

theorem exists_central_involution_S₂ (𝔖 : Sec3Setting G) :
    ∃ z ∈ 𝔖.S₂, orderOf z = 2 ∧
      𝔖.S₂ ⊓ Subgroup.centralizer (𝔖.S₂ : Set G) = Subgroup.zpowers z :=
  IsDihNonab.exists_inf_centralizer_self_eq 𝔖.decomp.dih₂

theorem commute_left_zpowers (𝔖 : Sec3Setting G) {z : G} (hzS₂ : z ∈ 𝔖.S₂) :
    ∀ u ∈ 𝔖.S₁, ∀ v ∈ Subgroup.zpowers z, u * v = v * u := by
  intro u hu v hv
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hv
  rw [← hk]
  exact (Commute.zpow_right (Subgroup.mem_centralizer_iff.mp (𝔖.decomp.commute hzS₂) u hu) k).eq

theorem center_S_eq (𝔖 : Sec3Setting G) (h₁ : IsKleinFour 𝔖.S₁) {z : G} (hzS₂ : z ∈ 𝔖.S₂)
    (hZ₂ : 𝔖.S₂ ⊓ Subgroup.centralizer (𝔖.S₂ : Set G) = Subgroup.zpowers z) :
    (𝔖.S : Subgroup G) ⊓ Subgroup.centralizer (𝔖.S : Set G) =
      𝔖.S₁ ⊔ Subgroup.zpowers z := by
  haveI : IsMulCommutative ↥𝔖.S₁ := h₁.isMulCommutative
  have hS₁ : 𝔖.S₁ ⊓ Subgroup.centralizer (𝔖.S₁ : Set G) = 𝔖.S₁ :=
    inf_of_le_left (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance)
  calc (𝔖.S : Subgroup G) ⊓ Subgroup.centralizer (𝔖.S : Set G)
      = (𝔖.S₁ ⊓ Subgroup.centralizer (𝔖.S₁ : Set G)) ⊔
          (𝔖.S₂ ⊓ Subgroup.centralizer (𝔖.S₂ : Set G)) := 𝔖.decomp.inf_centralizer_self
    _ = 𝔖.S₁ ⊔ Subgroup.zpowers z := by rw [hS₁, hZ₂]

theorem central_of_mem_center_S₂ (𝔖 : Sec3Setting G) {z : G} (hzS₂ : z ∈ 𝔖.S₂)
    (hZ₂ : 𝔖.S₂ ⊓ Subgroup.centralizer (𝔖.S₂ : Set G) = Subgroup.zpowers z) :
    z ∈ Subgroup.centralizer (𝔖.S : Set G) := by
  have hzC : z ∈ Subgroup.centralizer (𝔖.S₂ : Set G) := by
    have hz : z ∈ 𝔖.S₂ ⊓ Subgroup.centralizer (𝔖.S₂ : Set G) := by
      rw [hZ₂]
      exact Subgroup.mem_zpowers z
    exact (mem_inf.mp hz).2
  have hzC₁ : z ∈ Subgroup.centralizer (𝔖.S₁ : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun x hx =>
      Subgroup.mem_centralizer_iff.mp (𝔖.decomp.commute hzS₂) x hx
  refine Subgroup.mem_centralizer_iff.mpr fun s hs => ?_
  have hs' : s ∈ (𝔖.S : Subgroup G) := hs
  obtain ⟨x, hx, y, hy, rfl⟩ := 𝔖.decomp.mem_iff.mp hs'
  have hxy : x * y = y * x := 𝔖.decomp.comm hx hy
  have hxz : x * z = z * x := Subgroup.mem_centralizer_iff.mp hzC₁ x hx
  have hyz : y * z = z * y := Subgroup.mem_centralizer_iff.mp hzC y hy
  calc x * y * z = x * (y * z) := by group
    _ = x * (z * y) := by rw [hyz]
    _ = z * (x * y) := by rw [← mul_assoc, hxz, mul_assoc]

theorem center_S_sq_eq_one (𝔖 : Sec3Setting G) (h₁ : IsKleinFour 𝔖.S₁) {z : G}
    (hzS₂ : z ∈ 𝔖.S₂) (hzord : orderOf z = 2)
    (hZ₂ : 𝔖.S₂ ⊓ Subgroup.centralizer (𝔖.S₂ : Set G) = Subgroup.zpowers z) :
    ∀ x ∈ ((𝔖.S : Subgroup G) ⊓ Subgroup.centralizer (𝔖.S : Set G)),
      x * x = 1 := by
  intro x hx
  change x ∈ (𝔖.S : Subgroup G) ⊓ Subgroup.centralizer (𝔖.S : Set G) at hx
  rw [center_S_eq 𝔖 h₁ hzS₂ hZ₂] at hx
  have hcomm : ∀ u ∈ 𝔖.S₁, ∀ v ∈ Subgroup.zpowers z, u * v = v * u :=
    commute_left_zpowers 𝔖 hzS₂
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm hcomm)).mp hx
  have ha2 : a * a = 1 := by
    have := sq_eq_one_of_mem_kleinFour h₁ ha
    rwa [sq] at this
  have hb2 : b * b = 1 := by
    have hdvd : orderOf b ∣ 2 := by
      simpa [hzord] using orderOf_dvd_of_mem_zpowers hb
    rw [← pow_two]
    exact (orderOf_dvd_iff_pow_eq_one (x := b) (n := 2)).mp hdvd
  have hab : a * b = b * a := hcomm a ha b hb
  calc (a * b) * (a * b) = a * (b * (a * b)) := by rw [mul_assoc]
    _ = a * ((b * a) * b) := by rw [mul_assoc]
    _ = a * ((a * b) * b) := by rw [← hab]
    _ = (a * a) * (b * b) := by rw [mul_assoc, mul_assoc]
    _ = 1 := by rw [ha2, hb2, one_mul]

theorem center_S_card (𝔖 : Sec3Setting G) (h₁ : IsKleinFour 𝔖.S₁) {z : G}
    (hzS₂ : z ∈ 𝔖.S₂) (hzord : orderOf z = 2)
    (hZ₂ : 𝔖.S₂ ⊓ Subgroup.centralizer (𝔖.S₂ : Set G) = Subgroup.zpowers z) :
    Nat.card ↥((𝔖.S : Subgroup G) ⊓
      Subgroup.centralizer (𝔖.S : Set G)) = 8 := by
  have hV : ((𝔖.S : Subgroup G) ⊓
      Subgroup.centralizer (𝔖.S : Set G)) = 𝔖.S₁ ⊔ Subgroup.zpowers z :=
    center_S_eq (z := z) 𝔖 h₁ hzS₂ hZ₂
  rw [hV]
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzord
    exact absurd hzord (by norm_num)
  have hdisj : Disjoint (𝔖.S₁ : Subgroup G) (Subgroup.zpowers z) := by
    rw [disjoint_iff_inf_le, le_bot_iff, eq_bot_iff]
    intro x hx
    obtain ⟨hxS₁, hxz⟩ := mem_inf.mp hx
    rcases (CFSG.Timmesfeld.Bridge.mem_zpowers_iff_of_orderOf_eq_two hzord).mp hxz with h | h
    · exact h
    · exfalso
      have hzS₁ : z ∈ 𝔖.S₁ := h ▸ hxS₁
      have hmem : z ∈ 𝔖.S₁ ⊓ 𝔖.S₂ := mem_inf.mpr ⟨hzS₁, hzS₂⟩
      rw [𝔖.decomp.inf_eq] at hmem
      exact hz1 (mem_bot.mp hmem)
  have hzC₁ : z ∈ Subgroup.centralizer (𝔖.S₁ : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun u hu =>
      Subgroup.mem_centralizer_iff.mp (𝔖.decomp.commute hzS₂) u hu
  have hnorm : Subgroup.zpowers z ≤ Subgroup.normalizer (𝔖.S₁ : Set G) :=
    (Subgroup.zpowers_le.mpr hzC₁).trans (Subgroup.centralizer_le_normalizer _)
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj,
    h₁.card_four, Nat.card_zpowers, hzord]

theorem commutator_S_eq (𝔖 : Sec3Setting G) (h₁ : IsKleinFour 𝔖.S₁) :
    ⁅(𝔖.S : Subgroup G), (𝔖.S : Subgroup G)⁆ = ⁅𝔖.S₂, 𝔖.S₂⁆ := by
  haveI : IsMulCommutative ↥𝔖.S₁ := h₁.isMulCommutative
  calc ⁅(𝔖.S : Subgroup G), (𝔖.S : Subgroup G)⁆
      = ⁅𝔖.S₁ ⊔ 𝔖.S₂, 𝔖.S₁ ⊔ 𝔖.S₂⁆ := by rw [𝔖.decomp.sup_eq]
    _ = ⁅𝔖.S₁, 𝔖.S₁⁆ ⊔ ⁅𝔖.S₂, 𝔖.S₂⁆ :=
        commutator_sup_eq_of_commute (fun a ha b hb => 𝔖.decomp.comm ha hb)
    _ = ⁅𝔖.S₂, 𝔖.S₂⁆ := by
        rw [Subgroup.commutator_self_eq_bot_iff.mpr inferInstance, bot_sup_eq]

theorem z_mem_commutator (𝔖 : Sec3Setting G) (h₁ : IsKleinFour 𝔖.S₁) {z : G}
    (hzS₂ : z ∈ 𝔖.S₂) (hz1 : z ≠ 1)
    (hZ₂ : 𝔖.S₂ ⊓ Subgroup.centralizer (𝔖.S₂ : Set G) = Subgroup.zpowers z) :
    z ∈ ⁅(𝔖.S : Subgroup G), (𝔖.S : Subgroup G)⁆ := by
  rw [commutator_S_eq 𝔖 h₁]
  refine 𝔖.decomp.dih₂.mem_commutator_of_central hzS₂ hz1 fun g hg => ?_
  have hzC : z ∈ Subgroup.centralizer (𝔖.S₂ : Set G) := by
    have hz : z ∈ 𝔖.S₂ ⊓ Subgroup.centralizer (𝔖.S₂ : Set G) := by
      rw [hZ₂]
      exact Subgroup.mem_zpowers z
    exact (mem_inf.mp hz).2
  exact Subgroup.mem_centralizer_iff.mp hzC g hg

theorem eq_one_or_eq_z_of_mem_commutator (𝔖 : Sec3Setting G) (h₁ : IsKleinFour 𝔖.S₁) {z : G}
    (hzS₂ : z ∈ 𝔖.S₂) (hzord : orderOf z = 2)
    (hZ₂ : 𝔖.S₂ ⊓ Subgroup.centralizer (𝔖.S₂ : Set G) = Subgroup.zpowers z) {w : G}
    (hw : w ∈ ⁅(𝔖.S : Subgroup G), (𝔖.S : Subgroup G)⁆) (hw2 : w * w = 1) :
    w = 1 ∨ w = z := by
  rw [commutator_S_eq 𝔖 h₁] at hw
  have hwD : w ∈ 𝔖.S₂ := Subgroup.commutator_le_self 𝔖.S₂ hw
  have hwC : w ∈ Subgroup.centralizer (𝔖.S₂ : Set G) :=
    Subgroup.mem_centralizer_iff.mpr
      (𝔖.decomp.dih₂.mem_centralizer_of_mem_commutator hw hw2)
  have hwz : w ∈ Subgroup.zpowers z := by
    rw [← hZ₂]
    exact mem_inf.mpr ⟨hwD, hwC⟩
  exact (CFSG.Timmesfeld.Bridge.mem_zpowers_iff_of_orderOf_eq_two hzord).mp hwz

theorem normalizer_fixes_z (𝔖 : Sec3Setting G) (h₁ : IsKleinFour 𝔖.S₁) {z u : G}
    (hzS₂ : z ∈ 𝔖.S₂) (hzord : orderOf z = 2) (hz1 : z ≠ 1)
    (hZ₂ : 𝔖.S₂ ⊓ Subgroup.centralizer (𝔖.S₂ : Set G) = Subgroup.zpowers z)
    (huN : u ∈ Subgroup.normalizer ((𝔖.S : Subgroup G) : Set G)) :
    u * z * u⁻¹ = z := by
  have hz2 : z * z = 1 := by
    rw [← pow_two, ← hzord]
    exact pow_orderOf_eq_one z
  have hzcomm : z ∈ ⁅(𝔖.S : Subgroup G), (𝔖.S : Subgroup G)⁆ :=
    z_mem_commutator 𝔖 h₁ hzS₂ hz1 hZ₂
  have hmapS : (𝔖.S : Subgroup G).map (MulAut.conj u).toMonoidHom = 𝔖.S :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp huN
  have hmap : (⁅(𝔖.S : Subgroup G), (𝔖.S : Subgroup G)⁆).map
      (MulAut.conj u).toMonoidHom = ⁅(𝔖.S : Subgroup G), (𝔖.S : Subgroup G)⁆ := by
    rw [Subgroup.map_commutator, hmapS]
  have hmem : u * z * u⁻¹ ∈ ⁅(𝔖.S : Subgroup G), (𝔖.S : Subgroup G)⁆ := by
    have h := Subgroup.mem_map_of_mem (MulAut.conj u).toMonoidHom hzcomm
    rwa [hmap] at h
  have hmem2 : (u * z * u⁻¹) * (u * z * u⁻¹) = 1 := by
    calc (u * z * u⁻¹) * (u * z * u⁻¹) = u * (z * z) * u⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  rcases eq_one_or_eq_z_of_mem_commutator 𝔖 h₁ hzS₂ hzord hZ₂ hmem hmem2 with h | h
  · exfalso
    apply hz1
    have := congrArg (fun w => u⁻¹ * w * u) h
    simpa [mul_assoc] using this
  · exact h

theorem center_S_inf_S₂ (𝔖 : Sec3Setting G) (h₁ : IsKleinFour 𝔖.S₁) {z : G}
    (hzS₂ : z ∈ 𝔖.S₂)
    (hZ₂ : 𝔖.S₂ ⊓ Subgroup.centralizer (𝔖.S₂ : Set G) = Subgroup.zpowers z) :
    ((𝔖.S : Subgroup G) ⊓ Subgroup.centralizer (𝔖.S : Set G)) ⊓ 𝔖.S₂ =
      Subgroup.zpowers z := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨⟨hxS, hxC⟩, hxS₂⟩ := mem_inf.mp hx
    have hxS₂C : x ∈ 𝔖.S₂ ⊓ Subgroup.centralizer (𝔖.S₂ : Set G) := by
      refine mem_inf.mpr ⟨hxS₂, ?_⟩
      exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_iff.mp hxC y (𝔖.decomp.le_right hy)
    rwa [hZ₂] at hxS₂C
  · rw [Subgroup.zpowers_le]
    exact mem_inf.mpr ⟨mem_inf.mpr ⟨𝔖.decomp.le_right hzS₂,
      central_of_mem_center_S₂ 𝔖 hzS₂ hZ₂⟩, hzS₂⟩

@[expose] def Lemma34OddInput (𝔖 : Sec3Setting G) : Prop :=
  ∃ (z u : G) (W : Subgroup G),
    z ∈ 𝔖.S₂ ∧ orderOf z = 2 ∧
    𝔖.S₂ ⊓ Subgroup.centralizer (𝔖.S₂ : Set G) = Subgroup.zpowers z ∧
    u ∈ Subgroup.normalizer (𝔖.S : Set G) ∧ Odd (orderOf u) ∧
    u ∉ Subgroup.centralizer (𝔖.S : Set G) ∧
    W ≤ (𝔖.S : Subgroup G) ⊓ Subgroup.centralizer (𝔖.S : Set G) ∧
    Nat.card W = 4 ∧ z ∉ W ∧
    u ∈ Subgroup.normalizer (W : Set G) ∧
    u ∉ Subgroup.centralizer (W : Set G) ∧
    W ⊓ Subgroup.zpowers z = ⊥ ∧
    W ⊔ Subgroup.zpowers z = (𝔖.S : Subgroup G) ⊓
      Subgroup.centralizer (𝔖.S : Set G)

theorem lemma_3_4_of_oddInput (𝔖 : Sec3Setting G) (h₁ : IsKleinFour 𝔖.S₁)
    (h₂ : ∀ x ∈ 𝔖.S₂, ∀ y ∈ 𝔖.S₂, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (hIn : Lemma34OddInput 𝔖) :
    ∃ S₁' : Subgroup G, DDDecomp (𝔖.S : Subgroup G) S₁' 𝔖.S₂ ∧
      ∃ n : ℕ, ∃ u ∈ Subgroup.normalizer ((𝔖.S : Subgroup G) : Set G),
        orderOf u = 3 ^ n ∧
        u ∈ Subgroup.normalizer (S₁' : Set G) ∧
        u ∉ Subgroup.centralizer (S₁' : Set G) := by
  classical
  obtain ⟨z, u, W, hzS₂, hzord, hZ₂, huN, huodd, huC, hWle, hWcard, hzW,
    huNW, huCW, hWdisj, hWsup⟩ := hIn
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzord
    exact absurd hzord (by norm_num)
  let V : Subgroup G := (𝔖.S : Subgroup G) ⊓ Subgroup.centralizer (𝔖.S : Set G)
  have hVeq : V = 𝔖.S₁ ⊔ Subgroup.zpowers z := center_S_eq 𝔖 h₁ hzS₂ hZ₂
  have hVsq : ∀ x ∈ V, x * x = 1 := center_S_sq_eq_one 𝔖 h₁ hzS₂ hzord hZ₂
  have hVinfS₂ : V ⊓ 𝔖.S₂ = Subgroup.zpowers z :=
    center_S_inf_S₂ 𝔖 h₁ hzS₂ hZ₂
  have hVS₂ : V ⊔ 𝔖.S₂ = (𝔖.S : Subgroup G) := by
    calc V ⊔ 𝔖.S₂ = (𝔖.S₁ ⊔ Subgroup.zpowers z) ⊔ 𝔖.S₂ := by rw [hVeq]
      _ = 𝔖.S₁ ⊔ (Subgroup.zpowers z ⊔ 𝔖.S₂) := by rw [sup_assoc]
      _ = 𝔖.S₁ ⊔ 𝔖.S₂ := by rw [sup_eq_right.mpr (Subgroup.zpowers_le.mpr hzS₂)]
      _ = (𝔖.S : Subgroup G) := 𝔖.decomp.sup_eq
  have hsup : W ⊔ 𝔖.S₂ = (𝔖.S : Subgroup G) := by
    calc W ⊔ 𝔖.S₂ = W ⊔ (Subgroup.zpowers z ⊔ 𝔖.S₂) := by
          rw [sup_eq_right.mpr (Subgroup.zpowers_le.mpr hzS₂)]
      _ = (W ⊔ Subgroup.zpowers z) ⊔ 𝔖.S₂ := by rw [sup_assoc]
      _ = V ⊔ 𝔖.S₂ := by rw [hWsup]
      _ = (𝔖.S : Subgroup G) := hVS₂
  have hinf : W ⊓ 𝔖.S₂ = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have hxW : x ∈ W := (mem_inf.mp hx).1
    have hxS₂ : x ∈ 𝔖.S₂ := (mem_inf.mp hx).2
    have hxV : x ∈ V := hWle hxW
    have hxz : x ∈ Subgroup.zpowers z := by
      have h : x ∈ V ⊓ 𝔖.S₂ := mem_inf.mpr ⟨hxV, hxS₂⟩
      rwa [hVinfS₂] at h
    have h : x ∈ W ⊓ Subgroup.zpowers z := mem_inf.mpr ⟨hxW, hxz⟩
    rwa [hWdisj, mem_bot] at h
  have hcomm : 𝔖.S₂ ≤ Subgroup.centralizer (W : Set G) := by
    have hWcS : W ≤ Subgroup.centralizer (𝔖.S : Set G) := hWle.trans inf_le_right
    have hSCW : (𝔖.S : Subgroup G) ≤ Subgroup.centralizer (W : Set G) :=
      Subgroup.le_centralizer_iff.mpr hWcS
    exact fun x hx => hSCW (𝔖.decomp.le_right hx)
  haveI hKW : IsKleinFour ↥W := by
    haveI hWnt : Nontrivial ↥W := by
      rw [← Finite.one_lt_card_iff_nontrivial, hWcard]
      norm_num
    refine ⟨hWcard, ?_⟩
    rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
    intro g hg1
    refine orderOf_eq_prime ?_ hg1
    rw [pow_two]
    apply Subtype.ext
    simpa using hVsq (g : G) (hWle g.2)
  have hdih₁ : IsDih W := by
    refine ⟨1, le_rfl, ?_⟩
    rw [pow_one]
    exact IsKleinFour.nonempty_mulEquiv
  have hdd : DDDecomp (𝔖.S : Subgroup G) W 𝔖.S₂ :=
    ⟨hsup, hinf, hcomm, hdih₁, 𝔖.decomp.dih₂⟩
  have hu2C : u ^ 2 ∉ Subgroup.centralizer (W : Set G) := by
    intro h2
    let σ : MulAut ↥W := Subgroup.normalizerMonoidHom (H := W) ⟨u, huNW⟩
    have hσ2 : σ ^ 2 = 1 := by
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      rw [pow_two, MulAut.mul_apply]
      have hσ_apply : ∀ y : ↥W, ((σ y : ↥W) : G) = u * (y : G) * u⁻¹ := fun _ => rfl
      rw [hσ_apply, hσ_apply]
      have h := Subgroup.mem_centralizer_iff.mp h2 (x : G) x.2
      have h2' : (x : G) * (u * u) = (u * u) * (x : G) := by simpa [pow_two] using h
      calc u * (u * (x : G) * u⁻¹) * u⁻¹ = u * u * (x : G) * (u⁻¹ * u⁻¹) := by group
        _ = (u * u) * (x : G) * ((u * u)⁻¹) := by rw [mul_inv_rev]
        _ = (x : G) := by
            rw [← h2']
            group
    have hσodd : Odd (orderOf σ) := by
      have hdvd : orderOf σ ∣ orderOf u := by
        change orderOf ((Subgroup.normalizerMonoidHom (H := W)) ⟨u, huNW⟩) ∣ orderOf u
        rw [← Subgroup.orderOf_mk u huNW]
        exact orderOf_map_dvd _ _
      exact huodd.of_dvd_nat hdvd
    have hσ1 : orderOf σ = 1 := by
      have hdvd2 : orderOf σ ∣ 2 :=
        (orderOf_dvd_iff_pow_eq_one (x := σ) (n := 2)).mpr hσ2
      exact Nat.eq_one_of_dvd_coprimes hσodd.coprime_two_right dvd_rfl hdvd2
    have hσeq : σ = 1 := orderOf_eq_one_iff.mp hσ1
    apply huCW
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hconj : u * x * u⁻¹ = x := by
      have h := congrArg (fun τ : MulAut ↥W => ((τ ⟨x, hx⟩ : ↥W) : G)) hσeq
      simpa [σ] using h
    have hxu : u * x = x * u := by
      calc u * x = (u * x * u⁻¹) * u := by group
        _ = x * u := by rw [hconj]
    exact hxu.symm
  obtain ⟨m, ⟨n, hmn⟩, hfix⟩ :=
    exists_pow_three_element_of_sq_not_mem_centralizer hKW huNW hu2C
  have hvN : u ^ m ∈ Subgroup.normalizer ((𝔖.S : Subgroup G) : Set G) := by
    simpa using Subgroup.pow_mem _ huN m
  have hvNW : u ^ m ∈ Subgroup.normalizer (W : Set G) := Subgroup.pow_mem _ huNW m
  have hvC : u ^ m ∉ Subgroup.centralizer (W : Set G) := by
    intro hC
    haveI hWnt : Nontrivial ↥W := by
      rw [← Finite.one_lt_card_iff_nontrivial, hWcard]
      norm_num
    obtain ⟨a, ha⟩ := exists_ne (1 : ↥W)
    have h := Subgroup.mem_centralizer_iff.mp hC (a : G) a.2
    apply hfix (a : G) a.2 (fun h1 => ha (Subtype.ext h1))
    calc u ^ m * (a : G) * (u ^ m)⁻¹ = (a : G) * u ^ m * (u ^ m)⁻¹ := by rw [h]
      _ = (a : G) := by group
  refine ⟨W, hdd, n, u ^ m, hvN, hmn, hvNW, hvC⟩

end Sec3Setting

end CFSG.GH72


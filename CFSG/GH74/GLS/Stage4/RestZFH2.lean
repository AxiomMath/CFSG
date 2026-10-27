module

public import CFSG.GH74.GLS.Stage4.RestZFDef
public import CFSG.GH74.GLS.Stage4.RestX2Q4
public import CFSG.GH74.GLS.Stage4.T2GoodRed
public import CFSG.GH74.GLS.Stage4.T9Final

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank DodecA CFSG.GH74.GLS.Stage4.Rest.T6
open scoped Pointwise commutatorElement

theorem good_keyH (h3 : Ch6T2P51) (h4 : Ch6T2P52) (h5 : Ch6T2P53)
    (h5' : Ch6T2SLe) {n : ℕ} (G : Type) [Group G] [Finite G] (hr : pRank 2 G = 3) (Gs : Type) [Group Gs]
    (z : G) (K K' : Subgroup G) (F₁' F₂' : Type) [Field F₁'] [Field F₂'] (t : G)
    (hS : Ch6Setup G Gs (3 ^ n) (3 ^ n) z K K' F₁' F₂') (hR : Ch6Rem z K K' F₁' F₂' t)
    (hOut : Ch6P71Out n z K K') : ∃ D : Ch6Notation G, Ch6Pre D ∧ ¬ D.AllX2 ∧ D.HIdx := by
  have hNum : Ch6NumD 3 (3 ^ n) (3 ^ n) :=
    ⟨Nat.prime_three, by norm_num, ⟨n, rfl⟩, ⟨n, rfl⟩, Or.inl rfl⟩
  obtain ⟨N₁, u, hz, hK₁, hK₂, hq₁, hq₂, hLoc, hCoord⟩ :=
    h3 G Gs (3 ^ n) (3 ^ n) z K K' F₁' F₂' t hS hR rfl
  obtain ⟨F, hF5⟩ :=
    h4 G Gs (3 ^ n) (3 ^ n) z K K' F₁' F₂' t hS hR N₁ u hz hK₁ hK₂ hq₁ hq₂ hLoc hCoord
  obtain ⟨a, hau, hWeyl⟩ :=
    h5 G hr Gs (3 ^ n) (3 ^ n) z K K' F₁' F₂' t hS hR (⟨N₁, F⟩ : T2N2 G) u hz hK₁ hK₂ hq₁ hq₂
      hLoc hCoord hF5
  let N₃ : T2N3 G := ⟨⟨N₁, F⟩, a⟩
  have hSec : Ch6Sec5 N₃ u := ⟨hLoc, hF5, hWeyl, hau⟩
  have hSle : N₃.S ≤ ⨆ g ∈ N₃.Nsub, conjBy g (N₃.K₁ ⊔ N₃.K₂) :=
    h5' G hr Gs (3 ^ n) (3 ^ n) z K K' F₁' F₂' t hS hR N₃ u hz hK₁ hK₂ hq₁ hq₂ hLoc hCoord hF5 hWeyl
  have hctx : T6.T6Ctx N₃ u 3 :=
    T6.t6Ctx_of hS hR (N := N₃) (u := u) (p := 3) hz hK₁ hK₂ hq₁ hq₂ hNum hCoord hSec
  obtain ⟨hcard, P₀, hP₀F, hP₀p, hSyl⟩ := hOut N₃ u hz hK₁ hK₂ hq₁ hq₂ hCoord hSec
  obtain ⟨hS6, hPre⟩ := good_data hctx hSle hcard hP₀F hP₀p hSyl
  by_cases hAll : (⟨N₃, 3, P₀, T6.R₂ N₃ 3 ⊔ N₃.X₁⟩ : T2N4 G).toCh6.AllX2
  swap
  · have hH : (⟨N₃, 3, P₀, T6.R₂ N₃ 3 ⊔ N₃.X₁⟩ : T2N4 G).toCh6.HIdx := hLoc.H_idx
    exact ⟨_, hPre, hAll, hH⟩
  obtain ⟨α, γ, hαγ, hSh⟩ := hAll
  have hh : AllX2Hyp (⟨N₃, 3, P₀, T6.R₂ N₃ 3 ⊔ N₃.X₁⟩ : T2N4 G).toCh6 := AllX2Hyp.of_good hPre hS6
  obtain ⟨E₁, E₂, hE₁, hE₂, hd, hd', hc₁, hc₂⟩ := allX2_pairs hh hαγ hSh
  have hu : (⟨N₃, 3, P₀, T6.R₂ N₃ 3 ⊔ N₃.X₁⟩ : T2N4 G).toCh6.u = u := hau
  rw [hu] at hd hd'
  have hq : N₃.q₁ = N₃.q₂ := by
    show N₁.q₁ = N₁.q₂
    rw [hq₁, hq₂]
  have hSec' : Ch6Sec5 N₃.swap u := hSec.swap hq
  have hctx' : T6.T6Ctx N₃.swap u 3 :=
    T6.t6Ctx_of (hS.swap rfl) hR.swap (N := N₃.swap) (u := u) (p := 3) hz hK₂ hK₁ hq₂ hq₁ hNum
      (Ch6Coord.swap (N := N₃) hCoord) hSec'
  obtain ⟨hcard', P₀', hP₀F', hP₀p', hSyl'⟩ :=
    allX2_P71Out hctx hctx' hP₀F hP₀p rfl hS6.R₂_card hS6.Sylow_PP₀ hd hd' hc₁ hc₂
  have hSle' : N₃.swap.S ≤ ⨆ g ∈ N₃.swap.Nsub, conjBy g (N₃.swap.K₁ ⊔ N₃.swap.K₂) := by
    rw [T2N3.swap_Nsub hLoc hWeyl]
    show N₃.S ≤ ⨆ g ∈ N₃.Nsub, conjBy g (N₃.K₂ ⊔ N₃.K₁)
    rw [sup_comm N₃.K₂ N₃.K₁]
    exact hSle
  obtain ⟨hS6', hPre'⟩ := good_data hctx' hSle' hcard' hP₀F' hP₀p' hSyl'
  have hH' : (⟨N₃.swap, 3, P₀', T6.R₂ N₃.swap 3 ⊔ N₃.swap.X₁⟩ : T2N4 G).toCh6.HIdx :=
    hSec'.loc.H_idx
  refine ⟨_, hPre', ?_, hH'⟩
  rintro ⟨α', γ', hαγ', hSh'⟩
  have hh' : AllX2Hyp (⟨N₃.swap, 3, P₀', T6.R₂ N₃.swap 3 ⊔ N₃.swap.X₁⟩ : T2N4 G).toCh6 :=
    AllX2Hyp.of_good hPre' hS6'
  obtain ⟨-, hPβ', -, -⟩ := Ch6Notation.shape_le hSh'
  rw [Ch6Notation.B_false] at hPβ'
  have hX₂' := hh'.rootGrp_X₂
  have hY : conjBy N₃.a N₃.X₁ ≤ T6.R₂ N₃.swap 3 := by
    intro x hx
    have h1 : N₃.z * x * N₃.z⁻¹ = x⁻¹ := (z_inv_conjBy_a hh' hX₂'.zc hX₂'.ui).1 x hx
    exact hh'.inv_R₂ x (hPβ' hx) h1
  have hY' : conjBy N₃.a N₃.X₁' ≤ T6.R₂ N₃.swap 3 := T6.R_le_R₂' hctx' hd.p₂ hd.C₂ hd.z₂
  have hK₁eq : N₃.K₁ = N₃.X₁ ⊔ N₃.X₁' := hh.basics.K₁_eq
  have hK₁R : conjBy N₃.a N₃.K₁ ≤ T6.R₂ N₃.swap 3 := by
    rw [hK₁eq, conjBy_sup']
    exact sup_le hY hY'
  have hzK : N₃.a⁻¹ * N₃.z * N₃.a ∈ conjBy N₃.a N₃.K₁ := by
    rw [mem_conjBy_iff]
    have e : N₃.a * (N₃.a⁻¹ * N₃.z * N₃.a) * N₃.a⁻¹ = N₃.z := by group
    rw [e]
    exact hh.basics.z_mem_K₁
  have hz1 : N₃.z ≠ 1 := hh.basics.z_ne_one
  have hzz : N₃.z * N₃.z = 1 := hh.basics.z_mul_z
  refine not_mem_pGroup_of_sq Nat.prime_three (by norm_num) (T6.R₂_pGroup N₃.swap Nat.prime_three)
    (hK₁R hzK) ?_ ?_
  · intro h1
    apply hz1
    have : N₃.z = N₃.a * (N₃.a⁻¹ * N₃.z * N₃.a) * N₃.a⁻¹ := by group
    rw [this, h1]
    group
  · have e : N₃.a⁻¹ * N₃.z * N₃.a * (N₃.a⁻¹ * N₃.z * N₃.a) = N₃.a⁻¹ * (N₃.z * N₃.z) * N₃.a := by group
    rw [e, hzz]
    group

theorem ch6T2GoodAuxH (hRemL : Ch6T2Rem) (h3 : Ch6T2P51)
    (h4 : Ch6T2P52) (h5 : Ch6T2P53) (h5' : Ch6T2SLe) (hP : Ch6T2Prop71) {n : ℕ} (hn : 2 ≤ n)
    (G : Type) [Group G] [Finite G] (hStd : Std G) (hr : pRank 2 G = 3) (Gs : Type) [Group Gs]
    (hAt : IsTwoCentralG2TypeG2At G Gs (3 ^ n) (3 ^ n)) (hBad : ¬ Ch6Bad3 G) :
    ∃ D : Ch6Notation G, Ch6Pre D ∧ ¬ D.AllX2 ∧ D.HIdx := by
  obtain ⟨z, K₁, K₂, F₁, F₂, iF₁, iF₂, hSet⟩ := ch6_setup hr hAt
  obtain ⟨t, hRem⟩ := hRemL G hStd hr Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂ hSet
  rcases hP G hStd hr Gs n hn hAt hBad z K₁ K₂ F₁ F₂ t hSet hRem with hO | hO
  · exact good_keyH h3 h4 h5 h5' G hr Gs z K₁ K₂ F₁ F₂ t hSet hRem hO
  · exact good_keyH h3 h4 h5 h5' G hr Gs z K₂ K₁ F₂ F₁ t (hSet.swap rfl) hRem.swap hO

@[expose] def Ch6T2Good9XH : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs], IsTwoCentralG2TypeG2At G Gs 9 9 → ¬ Ch6Bad3 G →
      ∃ D : Ch6Notation G, Ch6Pre D ∧ ¬ D.AllX2 ∧ D.HIdx

@[expose] def Ch6T2GoodGt9XH : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (n : ℕ), 3 ≤ n → IsTwoCentralG2TypeG2At G Gs (3 ^ n) (3 ^ n) →
      ¬ Ch6Bad3 G → ∃ D : Ch6Notation G, Ch6Pre D ∧ ¬ D.AllX2 ∧ D.HIdx

theorem ch6T2Good9XH_of_leaf (hRemL : Ch6T2Rem) (h3 : Ch6T2P51)
    (h4 : Ch6T2P52) (h5 : Ch6T2P53) (h5' : Ch6T2SLe) (hP : Ch6T2Prop71) : Ch6T2Good9XH := by
  intro G _ _ hStd hr Gs _ hAt hBad
  have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
  rw [h9] at hAt
  exact ch6T2GoodAuxH hRemL h3 h4 h5 h5' hP (n := 2) le_rfl G hStd hr Gs hAt hBad

theorem ch6T2GoodGt9XH_of_leaf (hRemL : Ch6T2Rem) (h3 : Ch6T2P51)
    (h4 : Ch6T2P52) (h5 : Ch6T2P53) (h5' : Ch6T2SLe) (hP : Ch6T2Prop71) : Ch6T2GoodGt9XH := by
  intro G _ _ hStd hr Gs _ n hn hAt hBad
  exact ch6T2GoodAuxH hRemL h3 h4 h5 h5' hP (by omega) G hStd hr Gs hAt hBad

end CFSG.GH74.GLS.Stage4.Rest

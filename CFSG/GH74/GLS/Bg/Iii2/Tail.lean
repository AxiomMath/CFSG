module

public import CFSG.GH74.GLS.Bg.Iii2.TailPin
public import CFSG.GH74.GLS.Bg.Iii2.TailIso
public import CFSG.GH74.GLS.Bg.Iii2.TailKlein
public import CFSG.GH74.GLS.Bg.Iii2.FusionStmt

public section

namespace CFSG.GH74.GLS.Bg.Iii2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.ABGLocalTools
  CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec6

private theorem orderOf_eq_of_isConj' {G : Type} [Group G] {x y : G} (h : IsConj x y) :
    orderOf x = orderOf y := by
  obtain ⟨c, hc⟩ := h
  exact SemiconjBy.orderOf_eq _ hc

theorem tailP_of (hquat : II4_4_quat) (h44 : II4_44) (hCM : CM) (hF : FusionKlein) : TailP := by
  intro G _ _ hG hgen h3 x T E
  by_contra hcon
  push Not at hcon
  have hxo : orderOf x = 2 := E.ord
  have hTx : T ≤ centralizer ({x} : Set G) := E.le_cent
  have hT : IsSylowOf 2 T (centralizer ({x} : Set G)) := E.sylow.of_le hTx le_top
  have hsq : ∀ w : G, orderOf w = 2 → w * w = 1 := fun w hw => by
    have := pow_orderOf_eq_one w
    rwa [hw, sq] at this
  have hne1 : ∀ w : G, orderOf w = 2 → w ≠ 1 := fun w hw h => by
    rw [h, orderOf_one] at hw
    omega
  have hY : ∀ y ∈ T, IsConj x y → y ∈ zStar (rigidProduct x) := fun y hy hc => hcon y (hTx hy) hc
  by_cases hiso : ∀ y ∈ T, IsConj x y → y = x
  · exact false_of_isolated hG E hiso
  push Not at hiso
  obtain ⟨y, hyT, hcy, hyx⟩ := hiso
  have hyo : orderOf y = 2 := (orderOf_eq_of_isConj' hcy).symm.trans hxo
  have hxZ : x ∈ zStar (rigidProduct x) := hY x E.mem (IsConj.refl x)
  have hyZ : y ∈ zStar (rigidProduct x) := hY y hyT hcy
  have hx1 : x ≠ 1 := hne1 x hxo
  have hy1 : y ≠ 1 := hne1 y hyo
  obtain ⟨K₀, hK₀⟩ := E.nonempty
  by_cases hsingle : ∀ K', IsRigidRankOneComp x K' → K' = K₀
  ·
    obtain ⟨z, -, hZ⟩ := zStar_single hquat hG hK₀ hT hsingle
    rcases hZ x ⟨E.mem, hxZ⟩ with h | h
    · exact hx1 h
    rcases hZ y ⟨hyT, hyZ⟩ with h' | h'
    · exact hy1 h'
    exact hyx (h'.trans h.symm)
  · push Not at hsingle
    obtain ⟨K₂, hK₂, hne⟩ := hsingle
    have hall : ∀ K, IsRigidRankOneComp x K → K = K₀ ∨ K = K₂ := by
      intro K hK
      by_contra hcon'
      push Not at hcon'
      have hfin : {K : Subgroup G | IsRigidRankOneComp x K}.Finite := Set.toFinite _
      have hlt : 2 < Set.ncard {K : Subgroup G | IsRigidRankOneComp x K} :=
        (Set.two_lt_ncard_iff hfin).2
          ⟨K₀, K₂, K, hK₀, hK₂, hK, hne.symm, hcon'.1.symm, hcon'.2.symm⟩
      exact absurd (rr_ncard_le_two hquat hG hgen hxo) (not_le.2 hlt)
    obtain ⟨z₁, z₂, q₁, q₂, hZ⟩ := zStar_two hquat hG hgen hK₀ hK₂ hne.symm hT
    have hz12 : z₁ ≠ z₂ := by
      intro h12
      have hone : z₁ * z₂ = 1 := by rw [← h12]; exact q₁.sq
      have key : ∀ w, w ∈ T ⊓ zStar (rigidProduct x) → w ≠ 1 → w = z₁ := by
        intro w hw hw1
        rcases hZ w hw with h | h | h | h
        · exact absurd h hw1
        · exact h
        · rw [h, h12]
        · exact absurd (h.trans hone) hw1
      exact hyx ((key y ⟨hyT, hyZ⟩ hy1).trans (key x ⟨E.mem, hxZ⟩ hx1).symm)
    have C : KleinCfg x T K₀ K₂ z₁ z₂ := ⟨hxo, hT, hK₀, hK₂, hne.symm, hall, q₁, q₂, hz12⟩
    have hmem3 : ∀ w, w ∈ T ⊓ zStar (rigidProduct x) → w ≠ 1 → (w = z₁ ∨ w = z₂ ∨ w = z₁ * z₂) := by
      intro w hw hw1
      rcases hZ w hw with h | h | h | h
      · exact absurd h hw1
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    have hx3 := hmem3 x ⟨E.mem, hxZ⟩ hx1
    have hy3 := hmem3 y ⟨hyT, hyZ⟩ hy1
    have hswap := klein_swap q₁.sq q₂.sq C.z_comm hx3 hy3 hyx.symm
    have hxc : ∀ t ∈ T, t * x = x * t := fun t ht =>
      Subgroup.mem_centralizer_singleton_iff.1 (hTx ht)
    have hcomm : x * y = y * x := (hxc y hyT).symm
    have hweak : ∀ g : G, g * x * g⁻¹ ∈ T →
        g * x * g⁻¹ = x ∨ g * x * g⁻¹ = y ∨ g * x * g⁻¹ = x * y := by
      intro g hg
      have hcw : IsConj x (g * x * g⁻¹) := isConj_iff.2 ⟨g, rfl⟩
      have hwo : orderOf (g * x * g⁻¹) = 2 := (orderOf_eq_of_isConj' hcw).symm.trans hxo
      exact hswap _ (hmem3 _ ⟨hg, hY _ hg hcw⟩ (hne1 _ hwo))
    have hconj_xy : IsConj x (x * y) :=
      hF G T E.sylow x y (hsq x hxo) (hsq y hyo) hx1 hy1 hyx.symm hcomm E.mem hyT hxc hcy hweak
    have hz₁c : IsConj x z₁ := by
      rcases hswap z₁ (Or.inl rfl) with h | h | h
      · exact h ▸ IsConj.refl x
      · exact h ▸ hcy
      · exact h ▸ hconj_xy
    have hz₃c : IsConj x (z₁ * z₂) := by
      rcases hswap (z₁ * z₂) (Or.inr (Or.inr rfl)) with h | h | h
      · exact h ▸ IsConj.refl x
      · exact h ▸ hcy
      · exact h ▸ hconj_xy
    exact C.false_of_conj hCM hquat h44 hG h3 hTx hz₁c hz₃c

end CFSG.GH74.GLS.Bg.Iii2

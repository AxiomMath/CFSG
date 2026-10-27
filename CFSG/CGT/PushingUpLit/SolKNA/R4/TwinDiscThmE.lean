module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinReduce
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWBridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open scoped commutatorElement

section Defs

variable {G : Type} [Group G]

@[expose] def CentralizersSylowPairsW (Ω : Set (Subgroup G)) (K W H : Subgroup G) : Prop :=
  ∀ L ∈ twinSet Ω K, ∀ J ∈ KPerp Ω L, ∀ R₁ R₂ : Subgroup G, R₁ ∈ RSet Ω → R₁ ≤ L →
    R₂ ∈ RSet Ω → R₂ ≤ J → (Commutes R₁ R₂ ∨ R₂ = R₁) → ∀ a ∈ R₁ ⊔ R₂, a ∈ W → a ≠ 1 →
      a * a = 1 → Subgroup.centralizer ({a} : Set G) ≤ H

structure EHypSylW (Ω : Set (Subgroup G)) (K W H : Subgroup G) : Prop where
  trans : ∀ J ∈ dstarComp Ω K, ∃ h ∈ H, conjSub h K = J
  cent : CentralizersSylowPairsW Ω K W H

structure StdCentW (Ω : Set (Subgroup G)) (K W H : Subgroup G) (z : G) : Prop where
  z_le : Subgroup.centralizer ({z} : Set G) ≤ H
  nonTwin : ∀ L ∈ twinSet Ω K, ∀ J ∈ omegaNbr Ω L, ∀ z' : G, IsUniqueInvolution J z' → z' ≠ z →
    z' ∈ W → Subgroup.centralizer ({z'} : Set G) ≤ H ∧ Subgroup.centralizer ({z * z'} : Set G) ≤ H
  twin : ∀ L ∈ twinSet Ω K, ∀ L' ∈ twinSet Ω K, L' ≠ L → ∀ R₁ R₂ : Subgroup G,
    IsSylow2In R₁ L → IsSylow2In R₂ L' → Commutes R₁ R₂ → ∀ x ∈ R₁, ∀ y ∈ R₂, orderOf x = 4 →
      orderOf y = 4 → x * y ∈ W → Subgroup.centralizer ({x * y} : Set G) ≤ H

end Defs


@[expose] def TwinThmER (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TwinCoreHypR r n Y R S t → ∀ K H W : Subgroup Y, K ∈ CoreAssembly.conjClass (tightCore R) →
      TwinThmEW.PrintedWT (CoreAssembly.conjClass (tightCore R)) K W →
      EHypSylW (CoreAssembly.conjClass (tightCore R)) K W H → H = ⊤

section Std

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem wSet_comm (hΩ : HypOmegaGen Ω) {W : Subgroup G} (hW : W ∈ WSet Ω) :
    ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
  obtain ⟨η, hη, rfl⟩ := hW
  exact TC.etaSpan_comm hΩ hη

theorem centralizersSylowPairsW_of_stdCentW (hΩ : HypOmegaGen Ω)
    {K W H : Subgroup G} {z : G} (hz : IsUniqueInvolution K z) (hzW : z ∈ W)
    (h : StdCentW Ω K W H z) : CentralizersSylowPairsW Ω K W H := by
  intro L hL J hJ R₁ R₂ hR₁ hR₁L hR₂ hR₂J hcomm a ha haW ha1 ha2
  have hLΩ : L ∈ Ω := hL.1
  have hzL : IsUniqueInvolution L z := isUniqueInvolution_of_mem_twinSet hz hL
  have hR₁syl : IsSylow2In R₁ L := Q3.Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hLΩ hR₁ hR₁L
  rcases Set.mem_insert_iff.mp hJ with hJL | hJnbr
  · have haL : a ∈ L := (sup_le hR₁L (hR₂J.trans hJL.le)) ha
    rcases hzL.unique a haL ha2 with h1 | h1
    · exact absurd h1 ha1
    · rw [h1]
      exact h.z_le
  · have hJΩ : J ∈ Ω := hJnbr.1
    have hJL : J ≠ L := hJnbr.2.1
    obtain ⟨z', hz'⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJΩ
    have hR₂syl : IsSylow2In R₂ J := Q3.Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hR₂ hR₂J
    have hne : R₂ ≠ R₁ := by
      intro heq
      have h1 := Sec6Gen.card_le_two_of_le_inf hΩ hLΩ hJΩ hJL.symm hR₁syl.2.1 hR₁L
        (by rw [← heq]; exact hR₂J)
      have h2 := Sec6Gen.eight_le_of_mem_RSet hΩ hR₁
      omega
    have hc : Commutes R₁ R₂ := hcomm.resolve_right hne
    obtain ⟨x, hx, y, hy, rfl⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hc ha
    have hcxy : x * y = y * x := hc x hx y hy
    have hsq : (x * x) * (y * y) = 1 := by
      calc (x * x) * (y * y) = x * (x * y) * y := by group
        _ = x * (y * x) * y := by rw [hcxy]
        _ = (x * y) * (x * y) := by group
        _ = 1 := ha2
    have hcard : Nat.card ↥(R₁ ⊓ R₂) ≤ 2 :=
      Sec6Gen.card_le_two_of_le_inf hΩ hLΩ hJΩ hJL.symm (hR₁syl.2.1.to_le inf_le_left)
        (inf_le_left.trans hR₁L) (inf_le_right.trans hR₂J)
    have hA : ∀ e ∈ R₁ ⊓ R₂, e * e = 1 := by
      intro e he
      have hd : orderOf e ∣ Nat.card ↥(R₁ ⊓ R₂) := Subgroup.orderOf_dvd_natCard _ he
      have hpos : 0 < Nat.card ↥(R₁ ⊓ R₂) := Nat.card_pos
      have h2 : orderOf e ∣ 2 := by
        interval_cases hc2 : Nat.card ↥(R₁ ⊓ R₂)
        · exact hd.trans (one_dvd 2)
        · exact hd
      have := orderOf_dvd_iff_pow_eq_one.mp h2
      rwa [pow_two] at this
    have hxxA : x * x ∈ R₁ ⊓ R₂ := by
      refine ⟨R₁.mul_mem hx hx, ?_⟩
      have : x * x = (y * y)⁻¹ := eq_inv_of_mul_eq_one_left hsq
      rw [this]
      exact R₂.inv_mem (R₂.mul_mem hy hy)
    have hxx2 : (x * x) * (x * x) = 1 := hA _ hxxA
    have hxL : x ∈ L := hR₁L hx
    have hyJ : y ∈ J := hR₂J hy
    by_cases hzz : z' = z
    · have hzJ : IsUniqueInvolution J z := hzz ▸ hz'
      have hJtw : J ∈ twinSet Ω K := ⟨hJΩ, z, hz, hzJ⟩
      rcases hzL.unique (x * x) (L.mul_mem hxL hxL) hxx2 with hx2 | hx2
      · have hy2 : y * y = 1 := by rwa [hx2, one_mul] at hsq
        have hxz : x = 1 ∨ x = z := hzL.unique x hxL hx2
        have hyz : y = 1 ∨ y = z := hzJ.unique y hyJ hy2
        have hcase : x * y = z := by
          rcases hxz with h1 | h1 <;> rcases hyz with h2 | h2
          · exact absurd (by rw [h1, h2, one_mul]) ha1
          · rw [h1, h2, one_mul]
          · rw [h1, h2, mul_one]
          · exact absurd (by rw [h1, h2]; exact hz.sq) ha1
        rw [hcase]
        exact h.z_le
      · have hy2 : y * y = z := by
          have h1 : y * y = z⁻¹ := eq_inv_of_mul_eq_one_right (by rwa [hx2] at hsq)
          rw [h1]
          exact inv_eq_of_mul_eq_one_right hz.sq
        have hx4 : orderOf x = 4 := T7A.orderOf_eq_four_of_sq hz hx2
        have hy4 : orderOf y = 4 := T7A.orderOf_eq_four_of_sq hz hy2
        exact h.twin L hL J hJtw hJL R₁ R₂ hR₁syl hR₂syl hc x hx y hy hx4 hy4 haW
    · have hx2 : x * x = 1 := by
        by_contra hne1
        have h1 : x * x = z := (hzL.unique _ (L.mul_mem hxL hxL) hxx2).resolve_left hne1
        have hxxJ : x * x ∈ J := hR₂J (Subgroup.mem_inf.mp hxxA).2
        have h2 : x * x = z' := (hz'.unique _ hxxJ hxx2).resolve_left hne1
        exact hzz (h2.symm.trans h1)
      have hy2 : y * y = 1 := by rwa [hx2, one_mul] at hsq
      have hxz : x = 1 ∨ x = z := hzL.unique x hxL hx2
      have hyz : y = 1 ∨ y = z' := hz'.unique y hyJ hy2
      rcases hxz with h1 | h1 <;> rcases hyz with h2 | h2
      · exact absurd (by rw [h1, h2, one_mul]) ha1
      · rw [h1, h2, one_mul] at haW ⊢
        exact (h.nonTwin L hL J hJnbr z' hz' hzz haW).1
      · rw [h1, h2, mul_one]
        exact h.z_le
      · rw [h1, h2] at haW ⊢
        have hz'W : z' ∈ W := by
          have := W.mul_mem hzW haW
          rwa [← mul_assoc, hz.sq, one_mul] at this
        exact (h.nonTwin L hL J hJnbr z' hz' hzz hz'W).2

end Std

end CFSG.CGT.PushingUpLit.SolKNA.R4

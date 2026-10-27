module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22RestAut
public import CFSG.ClassicalInvolution.Q3.TL4ModelFacts

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Generic
open CFSG.CGT.PushingUpLit.SolKNA.R4.Perp22Rest

theorem concl163_of_quotAut {Q : Type} [Group Q] [Finite Q] {R : Subgroup Q} {S : Sylow 2 R} {z : Q}
    (hd : TightDatum R S z) (hgen : TightSelfGen R) (hO : TightOddFree Q)
    (hzc : z ∉ Subgroup.center Q)
    (hdich : ∀ φ : Q ≃* Q, (∀ x, φ (φ x) = x) →
      (∀ s ∈ (S : Subgroup R).map R.subtype, φ s = s) →
      (∀ y, Perp22Rest.quotCenterAut φ y = y) ∨
        (∀ y, Perp22Rest.quotCenterAut φ y = QuotientGroup.mk z * y * (QuotientGroup.mk z)⁻¹)) :
    CFSG.ClassicalInvolution.Q3.TL4.Concl163 R z := by
  have hU : IsUniqueInvolution (tightCore R) z := hd.isUniqueInvolution_core
  have hO' : CFSG.Open.classicalInvolutionOddCore Q = ⊥ := hO
  have hgen' : (⨆ g : Q, CFSG.ClassicalInvolution.Generic.conjSub g (tightCore R)) = ⊤ := hgen
  have hinf : ∀ w : Q, w ∈ tightCore R → w ∈ Subgroup.center Q → w = 1 := by
    intro w hwK hwC
    have hodd : Odd (orderOf w) := by
      rcases Nat.even_or_odd (orderOf w) with ⟨m, hm⟩ | ho
      · exfalso
        have hmpos : 0 < m := by
          have := orderOf_pos w
          omega
        have hv2 : w ^ m * w ^ m = 1 := by
          rw [← pow_add, ← hm, pow_orderOf_eq_one]
        have hv1 : w ^ m ≠ 1 := by
          intro h1
          have h2 := Nat.le_of_dvd hmpos (orderOf_dvd_of_pow_eq_one h1)
          omega
        have hvz : w ^ m = z := (hU.unique (w ^ m) (Subgroup.pow_mem _ hwK m) hv2).resolve_left hv1
        exact hzc (by rw [← hvz]; exact Subgroup.pow_mem _ hwC m)
      · exact ho
    have hN : (Subgroup.zpowers w).Normal := by
      refine ⟨fun x hx g => ?_⟩
      have hxC : x ∈ Subgroup.center Q := Subgroup.zpowers_le.mpr hwC hx
      have e : g * x * g⁻¹ = x := by
        rw [Subgroup.mem_center_iff.mp hxC g]
        group
      rw [e]
      exact hx
    have hcard : Odd (Nat.card (Subgroup.zpowers w)) := by
      rw [Nat.card_zpowers]
      exact hodd
    have hle : Subgroup.zpowers w ≤ CFSG.Open.classicalInvolutionOddCore Q :=
      le_sSup (show Subgroup.zpowers w ∈ {N : Subgroup Q | N.Normal ∧ Odd (Nat.card N)} from
        ⟨hN, hcard⟩)
    rw [hO'] at hle
    exact Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers w))
  have htop : ∀ C : Q → Prop, C 1 → (∀ x y : Q, C x → C y → C (x * y)) →
      (∀ g k : Q, k ∈ tightCore R → C (g * k * g⁻¹)) → ∀ x : Q, C x := by
    intro C h1 hmul hconj x
    have hx : x ∈ (⨆ g : Q, CFSG.ClassicalInvolution.Generic.conjSub g (tightCore R)) := by
      rw [hgen']
      exact Subgroup.mem_top x
    refine Subgroup.iSup_induction (fun g : Q => CFSG.ClassicalInvolution.Generic.conjSub g
      (tightCore R)) (C := C) hx (fun g y hy => ?_) h1 hmul
    have h3 := hconj g (g⁻¹ * y * g) (CFSG.ClassicalInvolution.Generic.mem_conjSub_iff.mp hy)
    rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at h3
  intro β hβ hfix
  have hinv : ∀ x, β (β x) = x := fun x => by
    have h := congrArg (fun γ : MulAut Q => γ x) hβ
    simpa [MulAut.mul_apply, MulAut.one_apply] using h
  have hSyl : ∀ s ∈ (S : Subgroup R).map R.subtype, β s = s :=
    fun s hs => hfix s (hd.sylow_core.1 hs)
  rcases hdich β hinv hSyl with hA | hB
  ·
    left
    have hcen : ∀ g : Q, ∃ c ∈ Subgroup.center Q, β g = g * c := by
      intro g
      have h1 := hA (QuotientGroup.mk g)
      rw [quotCenterAut_mk] at h1
      exact ⟨g⁻¹ * β g, QuotientGroup.eq.mp h1.symm, by group⟩
    have hfixA : ∀ g k : Q, k ∈ tightCore R → β (g * k * g⁻¹) = g * k * g⁻¹ := by
      intro g k hk
      obtain ⟨c, hc, hβc⟩ := hcen g
      have hck : c * k = k * c := (Subgroup.mem_center_iff.mp hc k).symm
      rw [map_mul, map_mul, map_inv, hfix k hk, hβc, mul_inv_rev]
      calc g * c * k * (c⁻¹ * g⁻¹) = g * (c * k) * c⁻¹ * g⁻¹ := by group
        _ = g * (k * c) * c⁻¹ * g⁻¹ := by rw [hck]
        _ = g * k * g⁻¹ := by group
    have h1A : β 1 = 1 := map_one β
    have hmulA : ∀ x y : Q, β x = x → β y = y → β (x * y) = x * y := by
      intro x y hx hy
      rw [map_mul, hx, hy]
    have hall : ∀ x : Q, β x = x := htop (fun x => β x = x) h1A hmulA hfixA
    exact MulEquiv.ext fun x => hall x
  ·
    right
    have hcen : ∀ g : Q, ∃ c ∈ Subgroup.center Q, β g = z * g * z⁻¹ * c := by
      intro g
      have h1 := hB (QuotientGroup.mk g)
      rw [quotCenterAut_mk] at h1
      have h2 : (QuotientGroup.mk (z * g * z⁻¹) : Q ⧸ Subgroup.center Q) =
          QuotientGroup.mk z * QuotientGroup.mk g * (QuotientGroup.mk z)⁻¹ := by
        simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [← h2] at h1
      exact ⟨(z * g * z⁻¹)⁻¹ * β g, QuotientGroup.eq.mp h1.symm, by group⟩
    have hcomm : ∀ k ∈ tightCore R, z * k * z⁻¹ = k := by
      intro k hk
      obtain ⟨c, hc, hβc⟩ := hcen k
      rw [hfix k hk] at hβc
      have hc' : c = (z * k * z⁻¹)⁻¹ * k := by
        calc c = (z * k * z⁻¹)⁻¹ * (z * k * z⁻¹ * c) := by group
          _ = (z * k * z⁻¹)⁻¹ * k := by rw [← hβc]
      have hcK : c ∈ tightCore R := by
        rw [hc']
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _
          (Subgroup.mul_mem _ hU.mem hk) (Subgroup.inv_mem _ hU.mem))) hk
      rw [hinf c hcK hc, mul_one] at hβc
      exact hβc.symm
    have hzk : ∀ k ∈ tightCore R, z⁻¹ * k * z = k := by
      intro k hk
      calc z⁻¹ * k * z = z⁻¹ * (z * k * z⁻¹) * z := by rw [hcomm k hk]
        _ = k := by group
    have hconj : ∀ g k : Q, k ∈ tightCore R →
        β (g * k * g⁻¹) = z * (g * k * g⁻¹) * z⁻¹ := by
      intro g k hk
      obtain ⟨c, hc, hβc⟩ := hcen g
      have hck : c * k = k * c := (Subgroup.mem_center_iff.mp hc k).symm
      rw [map_mul, map_mul, map_inv, hfix k hk, hβc, mul_inv_rev]
      calc z * g * z⁻¹ * c * k * (c⁻¹ * (z * g * z⁻¹)⁻¹)
          = z * g * z⁻¹ * (c * k) * (c⁻¹ * (z * g * z⁻¹)⁻¹) := by group
        _ = z * g * z⁻¹ * (k * c) * (c⁻¹ * (z * g * z⁻¹)⁻¹) := by rw [hck]
        _ = z * g * z⁻¹ * k * (z * g * z⁻¹)⁻¹ := by group
        _ = z * g * (z⁻¹ * k * z) * g⁻¹ * z⁻¹ := by group
        _ = z * g * k * g⁻¹ * z⁻¹ := by rw [hzk k hk]
        _ = z * (g * k * g⁻¹) * z⁻¹ := by group
    have hmulB : ∀ x y : Q, β x = z * x * z⁻¹ → β y = z * y * z⁻¹ →
        β (x * y) = z * (x * y) * z⁻¹ := by
      intro x y hx hy
      rw [map_mul, hx, hy]
      group
    have h1B : β 1 = z * 1 * z⁻¹ := by simp
    have hall : ∀ x : Q, β x = z * x * z⁻¹ :=
      htop (fun x => β x = z * x * z⁻¹) h1B hmulB hconj
    exact MulEquiv.ext fun x => hall x

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

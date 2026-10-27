module

public import CFSG.ClassicalInvolution.Asc77.AscT8RAl
public import CFSG.ClassicalInvolution.Asc77.AscT8RZ

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.AscP1Nine3

namespace T8R

section Cert

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

@[expose] def OuterFusion (K J : Subgroup G) (S : Sylow 2 G) (R T : Subgroup G) (z t : G) :
    Prop :=
  ∀ g : G, g⁻¹ * (z * t) * g ∈ (S : Subgroup G) →
    conjSub (g⁻¹ * (z * t) * g) R = R → conjSub (g⁻¹ * (z * t) * g) T = T →
    (¬ ∃ x ∈ K, orderOf x = 4 ∧
      x * (g⁻¹ * (z * t) * g) = (g⁻¹ * (z * t) * g) * x) →
    (¬ ∃ x ∈ J, orderOf x = 4 ∧
      x * (g⁻¹ * (z * t) * g) = (g⁻¹ * (z * t) * g) * x) →
    g⁻¹ * (z * t) * g = z * t


theorem zt_mem_sylow (hs : Std8 p f Ω K J S R T W z t) : z * t ∈ (S : Subgroup G) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hRsyl : IsSylow2In R K := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hs.stand.mem hRΩ hRK
  have hTsyl : IsSylow2In T J := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hs.hJ.1 hTΩ hTJ
  have h8R := hΩ.eight_le_of_mem_RSet hp hRΩ
  have h8T := hΩ.eight_le_of_mem_RSet hp hTΩ
  have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hRK hRsyl.2.1 (by omega)
  have htT : t ∈ T := T3.mem_of_isPGroup hs.ht hTJ hTsyl.2.1 (by omega)
  exact S.mul_mem (hRS hzR) (hTS htT)

theorem eq_of_centralizes (hs : Std8 p f Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) (hV : ExtraTrans Ω K J S z t)
    {g x : G} (hb : g⁻¹ * (z * t) * g ∈ (S : Subgroup G)) (hxK : x ∈ K) (hx4 : orderOf x = 4)
    (hxc : x * (g⁻¹ * (z * t) * g) = (g⁻¹ * (z * t) * g) * x) :
    g⁻¹ * (z * t) * g = z * t := by
  have hn : x * (g⁻¹ * (z * t) * (g⁻¹)⁻¹) = (g⁻¹ * (z * t) * (g⁻¹)⁻¹) * x := by
    rw [inv_inv]
    exact hxc
  have h1 := conj_zt_mul_inv_mem_of_orderFour hs hX hV (n := g⁻¹) hxK hx4 hn
  rw [inv_inv] at h1
  exact eq_of_mul_inv_mem_odd S.isPGroup' hb (zt_mem_sylow hs) (oddCoreOf_odd_natCard _) h1

theorem eq_of_centralizes_J (hs : Std8 p f Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) (hV' : ExtraTrans Ω J K S t z)
    {g x : G} (hb : g⁻¹ * (z * t) * g ∈ (S : Subgroup G)) (hxJ : x ∈ J) (hx4 : orderOf x = 4)
    (hxc : x * (g⁻¹ * (z * t) * g) = (g⁻¹ * (z * t) * g) * x) :
    g⁻¹ * (z * t) * g = z * t := by
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hzt : z * t = t * z := T8.mul_comm_of_mem_omegaNbr hp hΩ hs.hz hs.hJ hs.ht
  have hs' := Std8.symm' hs
  have hX' := eq_sup_oddCoreOf_swap hs hX
  rw [hzt] at hb hxc ⊢
  exact eq_of_centralizes hs' hX' hV' hb hxJ hx4 hxc

theorem exists_not_comm [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t) :
    ∃ x y : G, x * y ≠ y * x := by
  have hKs := CFSG.StronglyEmbedded.UniqueCoset.not_isSolvable_of_mem hs.stand.hyp
    hs.stand.mem hs.hz
  by_contra hcon
  push Not at hcon
  have : Group.IsSolvable G := IsSimpleGroup.comm_iff_isSolvable.mp hcon
  exact hKs inferInstance

theorem false_of_hX [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) (hV : ExtraTrans Ω K J S z t)
    (hV' : ExtraTrans Ω J K S t z) (hO : OuterFusion K J S R T z t) : False := by
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have haa : z * t * (z * t) = 1 := T8.mul_self_zt hp hΩ hs.hz hs.hJ hs.ht
  have hza : orderOf (z * t) = 2 := by
    refine orderOf_eq_prime (by rw [pow_two]; exact haa) ?_
    intro h
    have hzt : z ≠ t := by
      intro h'
      exact hs.hJ.2.1 (hs.noTwins J ⟨hs.hJ.1, z, hs.hz, h' ▸ hs.ht⟩)
    exact hzt ((eq_inv_of_mul_eq_one_left h).trans (inv_eq_of_mul_eq_one_right hs.ht.sq))
  have haS := zt_mem_sylow hs
  obtain ⟨g, hgS, hgne⟩ := exists_conj_mem_sylow_ne (exists_not_comm hs) S haS
    (fun s hs' => by
      have := conj_zt_of_mem_sylow hs hX hs'
      calc s * (z * t) = (s * (z * t) * s⁻¹) * s := by group
        _ = (z * t) * s := by rw [this]) hza
  apply hgne
  rcases fix_or_swap hs hX hgS with ⟨hR, hT⟩ | ⟨hR, -⟩
  · by_cases hK : ∃ x ∈ K, orderOf x = 4 ∧
        x * (g⁻¹ * (z * t) * g) = (g⁻¹ * (z * t) * g) * x
    · obtain ⟨x, hxK, hx4, hxc⟩ := hK
      exact eq_of_centralizes hs hX hV hgS hxK hx4 hxc
    by_cases hJ : ∃ x ∈ J, orderOf x = 4 ∧
        x * (g⁻¹ * (z * t) * g) = (g⁻¹ * (z * t) * g) * x
    · obtain ⟨x, hxJ, hx4, hxc⟩ := hJ
      exact eq_of_centralizes_J hs hX hV' hgS hxJ hx4 hxc
    exact hO g hgS hR hT hK hJ
  · exact eq_of_swap hs hX hV hgS hR

end Cert

end T8R

end CFSG.ClassicalInvolution.Asc77

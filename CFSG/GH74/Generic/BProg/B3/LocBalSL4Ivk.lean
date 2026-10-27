module

public import CFSG.GH74.Generic.BProg.B3.LocBalSL4Abs
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011CFX
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk413HProved

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2
  CFSG.GH74.GLS.Stage2.Final.Thm6.L2011 CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.CFT
  CFSG.Assembly.Dichotomy Subgroup

namespace LocBalSL4Ivk


theorem exists_inner_of_odd_core
    {X : Type} [Group X] [Finite X] (hZ : ∀ k : X, (∀ g : X, g * k = k * g) → k = 1)
    {q : ℕ} (hq : Odd q) (hq3 : 3 < q) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (h8 : ¬ ((q : ℤ) ≡ ε [ZMOD 8])) (hL : IsLnEps 4 X ε q) {β : X}
    (hβ : IsCentralInvolution β) {H : Subgroup (MulAut X)}
    (hH : (MulAut.conj : X →* MulAut X).range ≤ H) {c : ↥H}
    (hc : c ∈ involutionOddCore (LocBalSL4Abs.phi hH β)) (hc1 : c ≠ 1) :
    ∃ γ ∈ pPrimeCoreOf 2 (centralizer ({β} : Set X)),
      ((c : ↥H) : MulAut X) = MulAut.conj γ := by
  have hX : ∀ k : X, MulAut.conj k ∈ H := fun k => hH ⟨k, rfl⟩
  set K' : Subgroup ↥H := innRange H hX with hK'
  have hK'n : K'.Normal := innRange_normal H hX
  let eK : X ≃* ↥K' := MonoidHom.ofInjective (innIn_injective H hX hZ)
  have hfix : IsG2Sp4L4U4_fixed X q := by
    rcases hε with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl ⟨h8, hL⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h8, hL⟩))
  have hfix' : IsG2Sp4L4U4_fixed ↥K' q := isG2Sp4L4U4_of_equiv eK hfix
  have hcen : centralizer (K' : Set ↥H) = ⊥ := centralizer_innRange_eq_bot H hX hZ
  obtain ⟨S, hzS, hz2, hSc⟩ := exists_sylow_cent H hX hZ hβ
  have hphi : LocBalSL4Abs.phi hH = innIn H hX := MonoidHom.ext fun _ => rfl
  have hc' : c ∈ (pPrimeCore 2 ↥(centralizer ({innIn H hX β} : Set ↥H))).map
      (centralizer ({innIn H hX β} : Set ↥H)).subtype := by
    rw [hphi] at hc
    unfold involutionOddCore at hc
    rwa [oddCore_eq_pPrimeCore] at hc
  have hne : (pPrimeCore 2 ↥(centralizer ({innIn H hX β} : Set ↥H))).map
      (centralizer ({innIn H hX β} : Set ↥H)).subtype ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hc'
    exact hc1 hc'
  obtain ⟨-, -, hpc, -, -⟩ := ivk_4_13_H_proved ↥H K' q hK'n hq hq3 hfix' hcen (innIn H hX β)
    (innIn_mem_innRange H hX β) ⟨S, hzS, hz2, hSc⟩ hne
  have hc'' : c ∈ (pPrimeCore 2 ↥(centralizer ({innIn H hX β} : Set ↥H) ⊓ K')).map
      (centralizer ({innIn H hX β} : Set ↥H) ⊓ K').subtype := by
    rw [hpc]
    exact hc'
  obtain ⟨a, ha, hac⟩ := Subgroup.mem_map.mp hc''
  have hiso := CFSG.pPrimeCore_map_iso 2 (centEquiv H hX hZ β)
  rw [← hiso] at ha
  obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
  refine ⟨(a₀ : X), ⟨a₀, ha₀, rfl⟩, ?_⟩
  have hca : c = innIn H hX (a₀ : X) := by
    rw [← hac]
    rfl
  rw [hca]
  rfl

end LocBalSL4Ivk

end CFSG.GH74.Generic.BProg.B3

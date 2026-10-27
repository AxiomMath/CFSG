module

public import CFSG.HardMathSupport.Curtis.Coordinator.SPLCellOrbit
public import CFSG.HardMathSupport.Curtis.Coordinator.SPLCellMult

public section

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary

namespace CFSG.HardMathSupport.Curtis.Coordinator.SPLCell

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {V : Type} [AddCommGroup V] [Module K V] [Module.Finite K V]
  {G : Type} [CommGroup G] [Fintype G]

theorem exists_big_primary_factor {f p r k : ℕ} (hK : Nat.card K = 2 ^ f) (hp : p.Prime)
    (hp2 : p ≠ 2) (hr : r.Prime) (hr5 : 5 ≤ r) (hrp : ¬ r ∣ p - 1)
    (hGp : ∀ g : G, g ^ p = 1) (hGK : ((Fintype.card G : ℕ) : K) ≠ 0)
    (ρ : G →* (V ≃ₗ[K] V)) (hρinj : Function.Injective ρ)
    (z : Module.End K V) (hz : ∀ g, Commute z ((ρ g : V ≃ₗ[K] V) : Module.End K V))
    (hzp : z ^ p = 1) (γ : MulAut G) (hγ : γ ^ r ^ k = 1) (g₀ : G) (hg₀ : γ g₀ ≠ g₀)
    (σ : K ≃+* K) (hσpow : σ ^ r ^ k = 1) (fM : V →ₛₗ[(σ : K →+* K)] V)
    (hfbij : Function.Bijective fM) (hfρ : ∀ (e : G) (v : V), fM (ρ e v) = ρ (γ e) (fM v))
    (hfz : ∀ v, fM (z v) = z (fM v)) :
    ∃ h : K[X], h ∈ primaryFactors z ∧ Irreducible h ∧ 5 ≤ primaryMultiplicity z h := by
  classical
  have hpK : (p : K) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff K 2] at h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h0).symm
  have hσ : ∀ h : K[X], h.Monic → Irreducible h → h ∣ X ^ p - 1 →
      h.map (σ : K →+* K) = h := fun h hm hi hd =>
    map_eq_of_irreducible_dvd hp hp2 hr hrp hK σ hσpow hm hi hd
  obtain ⟨h, hirr, hmon, hdvd, Mi, hMne, hMh, hMz, hMind⟩ :=
    exists_five_pieces hp hr hr5 hrp hpK hGp hGK ρ hρinj z hz hzp γ k hγ g₀ hg₀ σ fM hfbij hfρ hfz hσ
  obtain ⟨v, hvM, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hMne 0)
  have hdvdmin : h ∣ minpoly K z := dvd_minpoly_of_aeval_eq_zero z hirr hv0 (hMh 0 v hvM)
  exact ⟨h, mem_primaryFactors.2 ⟨hirr, hmon, hdvdmin⟩, hirr,
    five_le_primaryMultiplicity z hirr Mi hMne hMh hMz hMind⟩

end CFSG.HardMathSupport.Curtis.Coordinator.SPLCell

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3Nine10
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3ProdAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3A6Aut
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResCSA6

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.EvenSporadicStandard.M24Std

theorem ordFacts_alt6 : OrdFacts (alternatingGroup (Fin 6)) where
  simple N hN := DRes.alt6_hsimple N hN
  central _ h := DRes.alt6_central h
  nontrivial := by
    have : Nontrivial (alternatingGroup (Fin 6)) :=
      Finite.one_lt_card_iff_nontrivial.1 (by rw [DRes.card_alt6]; norm_num)
    exact exists_ne 1
  pow_eight := mulAut_alt6_pow_eight
  eq_pow := mulAut_alt6_eq_pow

@[expose] def conjProd {A K : Type*} [Group A] [Group K] (N : Subgroup K) [N.Normal]
    (e : N ≃* A × A) : K →* MulAut (A × A) :=
  (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal

theorem conjProd_injective {A K : Type*} [Group A] [Group K] (N : Subgroup K) [N.Normal]
    (e : N ≃* A × A) (hN : centralizer (N : Set K) = ⊥) : Function.Injective (conjProd N e) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : (MulAut.conjNormal g : MulAut N) = 1 := by
    apply (MulAut.congr e).injective
    rw [map_one]
    exact hg
  have hmem : g ∈ centralizer (N : Set K) := by
    rw [mem_centralizer_iff]
    intro n hn
    have h2 := congrArg (fun γ : MulAut N => (γ ⟨n, hn⟩ : K)) h1
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
    exact (mul_inv_eq_iff_eq_mul.1 h2).symm
  rw [hN] at hmem
  exact mem_bot.1 hmem

theorem not_d8InCentralizer16_of_prod {K : Type} [Group K]
    {N : Subgroup K} (hNn : N.Normal)
    (e : N ≃* alternatingGroup (Fin 6) × alternatingGroup (Fin 6))
    (hN : centralizer (N : Set K) = ⊥) : ¬ D8InCentralizer16 K := by
  rintro ⟨s, D, hs, hD, ⟨d⟩⟩
  have := hNn
  set ρ := conjProd N e with hρdef
  have hρ : Function.Injective ρ := conjProd_injective N e hN
  have hα : orderOf (ρ s) = 16 := by rw [orderOf_injective ρ hρ s]; exact hs
  have hcomm : ∀ z ∈ D, ρ z * ρ s = ρ s * ρ z := fun z hz => by
    rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 (hD hz)]
  set x : D := d.symm (DihedralGroup.r 1) with hx
  set y : D := d.symm (DihedralGroup.sr 0) with hy
  have h1 := ordFacts_alt6.comm_of_orderOf_sixteen hα (hcomm x x.2) (hcomm y y.2)
  rw [← map_mul, ← map_mul] at h1
  have h2 : (x : K) * y = y * x := hρ h1
  have h3 : x * y = y * x := Subtype.ext h2
  have h4 := congrArg d h3
  rw [map_mul, map_mul, hx, hy, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h4
  exact absurd h4 (by decide)

end CFSG.EvenSporadicStandard.Fin76b

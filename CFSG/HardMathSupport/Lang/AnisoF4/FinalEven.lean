module

public import CFSG.HardMathSupport.Lang.AnisoF4.Final
public import CFSG.HardMathSupport.Lang.AnisoF4.B4ConjEven
public import CFSG.HardMathSupport.Lang.AnisoF4.B4PlanesEven
public import CFSG.HardMathSupport.Lang.AnisoE6.TwFinal4

public noncomputable section

namespace CFSG.HardMathSupport.Lang.AnisoF4

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.CurtisTits CFSG.ComponentClassification.CatLeafProof CFSG.LieType.SeitzGeneration
open scoped MatrixGroups

set_option linter.unusedSectionVars false


theorem f4FourEvenClosure : F4FourEvenClosure := by
  intro K _ _ h2 hK4 p hpF hp5 hpq E₀ hE₀p hE₀c
  classical
  have : Fintype K := Fintype.ofFinite K
  have hc : ringChar K = 2 := by
    have hd : ringChar K ∣ 2 := ringChar.dvd (by exact_mod_cast h2)
    obtain ⟨n, hℓ, -⟩ := FiniteField.card K (ringChar K)
    exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 hd
  have : CharP K 2 := ringChar.of_eq hc
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  obtain ⟨Ψ, hker, hrange, -, -⟩ := exists_psi_B4_F4_frame_even hK hK4
  obtain ⟨e, heA, heo, hec⟩ := exists_e1_F4_four (K := K) (p := p) (by omega) hpq
  have heX : e ∈ ⨆ k, b4Chain K k :=
    (sup_le (sup_le (le_iSup (b4Chain K) 0) (le_iSup (b4Chain K) 1)) (le_iSup (b4Chain K) 2)) heA
  obtain ⟨g, hgX, hge⟩ := exists_conj_plane_b4_even hK4 hp5 hpq heX heo E₀ hE₀p hE₀c
  have hE₁p : ∀ x ∈ E₀.map (MulAut.conj g).toMonoidHom, x ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE₀p x hx, map_one]
  have hE₁c : Nat.card (E₀.map (MulAut.conj g).toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hE₀c]
  have he1 : e ≠ 1 := by
    intro h
    rw [h, orderOf_one] at heo
    omega
  apply closure_centralizers_eq_top_of_map_conj g E₀
  apply eq_top_of_b4Chain_le_of_delta_le
  · exact iSup_b4Chain_le_closure_centralizers_of_sp hpF.out hp5 hpq Ψ hker hrange _ hgX hE₁p hE₁c
  · intro y hy
    exact Subgroup.subset_closure ⟨e, hge, he1, (hec y hy).symm⟩


theorem seitzExcAnisotropicF4Class_four : SeitzExcAnisotropicF4Class 4 :=
  seitzExcAnisotropicF4Class_four_of_even f4FourEvenClosure


theorem seitzExcAnisotropicTwistedE6Class_four : SeitzExcAnisotropicTwistedE6Class 4 :=
  CFSG.HardMathSupport.Lang.AnisoE6.seitzExcAnisotropicTwistedE6Class_four_of_f4
    seitzExcAnisotropicF4Class_four

end CFSG.HardMathSupport.Lang.AnisoF4

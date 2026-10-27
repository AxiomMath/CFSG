module

public import CFSG.ClassicalInvolution.Q3.TL4C264OmX
public import CFSG.ClassicalInvolution.Q3.TL4C263Ab
public import CFSG.ClassicalInvolution.Q3.TL4C264OmS

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.Blueprint

section Cit3


variable {n : ℕ}

theorem tightC264Omega_of (h4 : Thm4RBelow 3 n) (hLC : TightLambdaCommR 3 n)
    (hRk : Model264Rank3) (h1521 : Model1521Twin3) (h263 : TightC263E4 n) :
    TightC264Omega n := by
  intro hP Y _ _ Rd Sd z J S R T W t hs hΛp hE hcj hO2 hω
  have h := TightLargeHypR.typeRFam hs.large
  have hzY := mem_layerY_of_isUniqueInvolution h hs.xMem_K hs.hz
  have htY := mem_layerY_of_isUniqueInvolution h hs.xMem_J hs.ht
  obtain ⟨t₁, ht1C, ⟨g, hgX, hgt⟩, ⟨J₁, hJ₁, -, hJ₁t⟩, hσ⟩ :=
    hs.exists_twinSigmaOut3 h4 hLC hΛp hE hcj hO2 hzY htY
  obtain ⟨N, hNn, hNeq, hpsl, hL3, hout⟩ :=
    hs.exists_psl43_of_models hRk h1521 h4 hE hcj hω hσ (hs.secCyc_mul_eq_zpowers hzY htY)
  refine ⟨⟨N, hNn, hNeq, hpsl⟩, ?_⟩
  have ht1sq : t₁ * t₁ = 1 := by
    rw [← hgt]
    calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [hs.ht.sq]; group
  have h263' : LieModel (XQuot (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)) .PSL 3 3 1 ∨
      ∀ P : Subgroup (XQuot (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)),
        IsPGroup 3 ↥P → ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    rcases h263 hP Y Rd Sd z J S R T W t hs hΛp hE with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (abelian3_of_m11_or_l2 h2)
  obtain ⟨hc, hxt, hcomm, hLie⟩ := exists_c264Two_ii h hs.xMem_K hs.hz ht1C ht1sq hgX hgt hJ₁
    hJ₁t hout N hL3 (exists_nonabelian_three_of_lieModel_psl33 hL3) h263'
  exact ⟨hc, hxt, hcomm, Or.inl hLie⟩

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4

module

public import CFSG.GH74.GLS.C3.Layer1.EvenSelFin

public section

namespace CFSG.GH74.GLS.C3.Layer1.EndZ

open Subgroup CFSG CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem normal_of_pRank_CxK_le_one {x : G} {K : Subgroup G}
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) (h2K : 2 ≤ pRank 2 ↥K)
    (h1 : pRank 2 ↥(CxK x K) ≤ 1) :
    ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K := by
  intro c hc k hk
  by_contra hkc
  have hK' : IsPCompIn 2 (centralizer ({x} : Set G)) (K.map (MulAut.conj c).toMonoidHom) := by
    have := Stage1.Thm2.Recip.isPCompIn_map_conj hK c
    rwa [Thm1.map_conj_eq_self_of_mem hc] at this
  have hne : K.map (MulAut.conj c).toMonoidHom ≠ K := by
    intro h
    apply hkc
    have hmem : c * k * c⁻¹ ∈ K.map (MulAut.conj c).toMonoidHom :=
      ⟨k, hk, by simp [MulAut.conj_apply]⟩
    rwa [h] at hmem
  have hle : K.map (MulAut.conj c).toMonoidHom ≤ CxK x K :=
    le_inf hK'.1 (Stage1.Thm2.Recip.le_cSec_of_ne hK' hK hne)
  have h3 : pRank 2 ↥(K.map (MulAut.conj c).toMonoidHom) = pRank 2 ↥K := Th2.pRank_cj c K
  have h4 : pRank 2 ↥(K.map (MulAut.conj c).toMonoidHom) ≤ pRank 2 ↥(CxK x K) :=
    Back.pRank_mono' hle
  omega

theorem endB_of_central
    (hG : C3Hyp G) {x : G} {K : Subgroup G} (hx : IsStar2 x) (hc : IsCentralInvolution x)
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (hL29 : HasL2Model (kBar K) (fun q => q = 9)) (h1 : pRank 2 ↥(CxK x K) = 1) : False := by
  have hodd : HasL2Model (kBar K) Odd :=
    Back.hasL2Model_mono (fun q hq => by subst hq; decide) hL29
  have hnorm := normal_of_pRank_CxK_le_one hK (Thm1.two_le_pRank_of_shape (Or.inl hodd)) h1.le
  obtain ⟨p, f, hp, hf, hq, hL⟩ := hL29
  have h9 : p ^ f = 9 := hq
  have hG4 : pRank 2 ↥(centralizer ({x} : Set G)) = 4 := by
    rw [hx.2, hG.pRank_eq_four]
  have h2 : 2 ≤ pRank 2 ↥(CxK x K) :=
    EvenSelP.rankQ_of_good hG hK hnorm hG4 hp hf (Or.inl (by rw [h9])) hL (Or.inl hc)
  omega

end CFSG.GH74.GLS.C3.Layer1.EndZ

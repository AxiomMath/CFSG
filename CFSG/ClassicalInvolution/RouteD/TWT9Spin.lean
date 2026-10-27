module

public import CFSG.ClassicalInvolution.RouteD.GapsFrPair
public import CFSG.ClassicalInvolution.RouteD.TypeDModel
public import CFSG.ClassicalInvolution.RouteD.TypeDAdapt
public import CFSG.ClassicalInvolution.RouteD.GapsFrNodes
public import CFSG.ClassicalInvolution.RouteD.GapsFrIso
public import CFSG.ClassicalInvolution.RouteD.TWT8Spin
public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusChain
public import CFSG.ClassicalInvolution.RouteD.TWT8V
public import CFSG.ClassicalInvolution.RouteD.TWEB6Bridge
public import CFSG.ClassicalInvolution.RouteD.TwinYR2SpinFrame
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.TWT9

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.WeakCT CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.RouteD.TWE.B6
open CFSG.ClassicalInvolution.Generic (Commutes fundamentalSubgroups)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

set_option linter.unusedSectionVars false

section Generic

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem no_scalar_between_frames (h2 : (2 : K) ≠ 0) (hdim : 8 < Module.finrank K V)
    (fr₀ fr₂ : OFrame Q) (hperp : ∀ x ∈ fr₀.span, ∀ y ∈ fr₂.span, polar Q x y = 0)
    {b : V ≃ₗ[K] V} (hb : b ∈ fr₂.La.range)
    (hsc : (fr₀.La (-1))⁻¹ * b ∈ scalars K V) : False := by
  classical
  rw [mem_scalars] at hsc
  obtain ⟨c, hc⟩ := hsc
  obtain ⟨B, rfl⟩ := hb
  have hbv : ∀ v, fr₂.La B v = c • fr₀.La (-1) v := fun v => by
    calc fr₂.La B v = (fr₀.La (-1) * ((fr₀.La (-1))⁻¹ * fr₂.La B)) v := by
          rw [mul_inv_cancel_left]
      _ = fr₀.La (-1) (c • v) := by rw [LinearEquiv.mul_apply, hc v]
      _ = c • fr₀.La (-1) v := map_smul _ _ _
  have hne : fr₀.perp ⊓ fr₂.perp ≠ ⊥ := by
    intro h
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq fr₀.perp fr₂.perp
    have h3 := CFSG.ClassicalInvolution.ModelFacts.finrank_perp_add_four fr₀
    have h4 := CFSG.ClassicalInvolution.ModelFacts.finrank_perp_add_four fr₂
    have h5 := Submodule.finrank_le (fr₀.perp ⊔ fr₂.perp)
    rw [h, finrank_bot] at h1
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hBv : fr₂.La B v = v :=
    Frame.La_apply_of_coords_eq_zero fr₂ B ((Frame.mem_perp_iff fr₂).mp (Submodule.mem_inf.mp hv).2)
  have hLv : fr₀.La (-1) v = v :=
    TWT8.La_neg_one_apply_of_mem_perp h2 fr₀ (Submodule.mem_inf.mp hv).1
  have hc1 : c = 1 := by
    have h1 := hbv v
    rw [hBv, hLv] at h1
    have h3 : (c - 1) • v = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hv0)
  have he : fr₀.P.e ∈ fr₀.span := by
    rw [frame_span_eq fr₀]
    exact Submodule.mem_sup_left (e_mem_hypPlane fr₀.P)
  have he₂ : fr₀.P.e ∈ fr₂.perp := (Frame.mem_perp_iff_forall_incl fr₂).mpr fun Y =>
    hperp _ he _ ⟨Y, rfl⟩
  have hBe : fr₂.La B fr₀.P.e = fr₀.P.e :=
    Frame.La_apply_of_coords_eq_zero fr₂ B ((Frame.mem_perp_iff fr₂).mp he₂)
  have hLe : fr₀.La (-1) fr₀.P.e = -fr₀.P.e := TWT8.La_neg_one_apply_of_mem_span h2 fr₀ he
  have h1 := hbv fr₀.P.e
  rw [hBe, hLe, hc1, one_smul] at h1
  have h3 : (2 : K) • fr₀.P.e = 0 := by
    calc (2 : K) • fr₀.P.e = fr₀.P.e + fr₀.P.e := two_smul K _
      _ = fr₀.P.e + -fr₀.P.e := by rw [← h1]
      _ = 0 := add_neg_cancel _
  exact fr₀.P.e_ne_zero ((smul_eq_zero.mp h3).resolve_left h2)

end Generic

section Models

variable {p f : ℕ} [Fact p.Prime]

theorem exists_chain_spin_plus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {R₀ R₁ : Subgroup (spinGroup (quadPlus 5 (GaloisField p f)))}
    (h₀ : R₀ ∈ fundamentalSubgroups .POmegaPlus (plusDatum 5 (GaloisField p f) (by norm_num)))
    (h₁ : R₁ ∈ fundamentalSubgroups .POmegaPlus (plusDatum 5 (GaloisField p f) (by norm_num)))
    (hadj : ModelAdj (Subgroup.center _) R₀ R₁)
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField p f) W R₀ R₁) :
    ∃ T₁ ∈ fundamentalSubgroups .POmegaPlus (plusDatum 5 (GaloisField p f) (by norm_num)),
      ∃ T₂ ∈ fundamentalSubgroups .POmegaPlus (plusDatum 5 (GaloisField p f) (by norm_num)),
        Commutes T₁ R₀ ∧ (∃ W, LinearBlockStandardPair (GaloisField p f) W R₁ T₁) ∧
        Commutes T₂ R₀ ∧ Commutes T₂ R₁ ∧
        ∃ W, LinearBlockStandardPair (GaloisField p f) W T₁ T₂ := by
  classical
  have hm3 : 3 ≤ 5 := by norm_num
  have cq := centralQuot_plus (m := 5) hp2 (by norm_num) (by norm_num) hq
  have hq4 : 4 ≤ p ^ f := by omega
  obtain ⟨x₀, hx0, hx1⟩ := exists_spin_pair hp2 hq (m := 5) (by norm_num) h₀ h₁ hadj hlin
  let ι : spinGroup (quadPlus 5 (GaloisField p f)) ≃* spinGroup (quadPlus 5 (GaloisField p f)) :=
    MulAut.conj x₀
  have hrk : ∀ (k : ℕ) (hk : k + 1 < 5),
      rankOne (plusDatum 5 (GaloisField p f) hm3).rootGroup (⟨k, by omega⟩ : Fin 5) =
        rootSL2 (plusFrame 5 (GaloisField p f) hm3) k (k + 1) (by omega) hk (by omega) true
          false := fun k hk => rankOne_plusDatum_of_lt hm3 (k := ⟨k, by omega⟩) hk
  have hR₀ : R₀ = (rankOne (plusDatum 5 (GaloisField p f) hm3).rootGroup
      (⟨0, by norm_num⟩ : Fin 5)).map ι.toMonoidHom := by
    rw [hrk 0 (by norm_num)]
    exact hx0
  have hR₁ : R₁ = (rankOne (plusDatum 5 (GaloisField p f) hm3).rootGroup
      (⟨1, by norm_num⟩ : Fin 5)).map ι.toMonoidHom := by
    rw [hrk 1 (by norm_num)]
    exact hx1
  have c20 := commutes_rankOne_plusDatum (K := GaloisField p f) (hn3 := hm3)
    (i := (⟨2, by norm_num⟩ : Fin 5)) (j := (⟨0, by norm_num⟩ : Fin 5)) (by decide)
  have c30 := commutes_rankOne_plusDatum (K := GaloisField p f) (hn3 := hm3)
    (i := (⟨3, by norm_num⟩ : Fin 5)) (j := (⟨0, by norm_num⟩ : Fin 5)) (by decide)
  have c31 := commutes_rankOne_plusDatum (K := GaloisField p f) (hn3 := hm3)
    (i := (⟨3, by norm_num⟩ : Fin 5)) (j := (⟨1, by norm_num⟩ : Fin 5)) (by decide)
  have s12 := standardPair_plusDatum_edge (F := GaloisField p f) hm3
    (i := (⟨1, by norm_num⟩ : Fin 5)) (j := (⟨2, by norm_num⟩ : Fin 5))
    (Or.inl ⟨rfl, by norm_num⟩)
  have s23 := standardPair_plusDatum_edge (F := GaloisField p f) hm3
    (i := (⟨2, by norm_num⟩ : Fin 5)) (j := (⟨3, by norm_num⟩ : Fin 5))
    (Or.inl ⟨rfl, by norm_num⟩)
  refine ⟨(rankOne (plusDatum 5 (GaloisField p f) hm3).rootGroup (⟨2, by norm_num⟩ : Fin 5)).map
    ι.toMonoidHom, ?_, (rankOne (plusDatum 5 (GaloisField p f) hm3).rootGroup
      (⟨3, by norm_num⟩ : Fin 5)).map ι.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrk 2 (by norm_num)]
    exact rootSL2_conj_mem_gen hq4 cq _ _ _ _ true false x₀
  · rw [hrk 3 (by norm_num)]
    exact rootSL2_conj_mem_gen hq4 cq _ _ _ _ true false x₀
  · rw [hR₀]
    exact (commutes_map_equiv ι).mpr c20
  · obtain ⟨W, hW⟩ := s12
    rw [hR₁]
    exact ⟨_, linearBlockStandardPair_map_equiv ι hW⟩
  · rw [hR₀]
    exact (commutes_map_equiv ι).mpr c30
  · rw [hR₁]
    exact (commutes_map_equiv ι).mpr c31
  · obtain ⟨W, hW⟩ := s23
    exact ⟨_, linearBlockStandardPair_map_equiv ι hW⟩

end Models

end CFSG.ClassicalInvolution.RouteD.TWT9

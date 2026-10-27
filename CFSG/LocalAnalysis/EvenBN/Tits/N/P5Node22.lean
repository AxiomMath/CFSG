module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Steps
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Five
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5S22Set
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5S24
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5S23
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5S25

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits
open CFSG.Goldschmidt
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem step22_of_top (hTop : TopStatement) : Step22 := by
  intro G _ _ d z₀ h49 hd hz h14 h17s h17 h19 h20 h21 S hS
  obtain ⟨hmaxK, -, hTI, hWt, hSylW, -, -, -⟩ := h20
  obtain ⟨hUab, hUcard, -⟩ := h17s
  obtain ⟨-, -, -, hCcent, -, -⟩ := h17
  obtain ⟨-, -, -, -, hWg, hWquot, hWab, hWcard⟩ := h19
  obtain ⟨-, hP, hE1, hE2⟩ := h21
  obtain ⟨hP1, hP2, -⟩ := hP S hS
  have hE2S := hE2 S hS
  have hW256 : Nat.card (Ws d) = 256 := by rw [hWcard]; norm_num
  have hxKs := star_x5_mem_Ks h49 hd
  have htKs := star_t_mem_Ks h49 hd
  have hSIs : fusionIsSylowIn 2 (img d S) (Is d) := by
    have h := fusionIsSylowIn_imgIn d.s56V hS.1 (preIn_le_normalizer d.s56V (Is d))
    have e : imgIn d.s56V (Ig d) = Is d := imgIn_preIn_of_le d.s56V inf_le_right
    rwa [e] at h
  have hWHs : Ws d ≤ Hs d := hWg ▸ imgIn_le_range d.s56V (Wg d z₀)
  have hWIs : Ws d ≤ Is d := le_inf Subgroup.le_normalizer hWHs
  have hSN : img d S ≤ normalizer ((Ws d : Subgroup (MulAut ↥d.s56V)) : Set _) :=
    hSIs.1.trans inf_le_left
  have hWS : Ws d ≤ img d S :=
    le_of_fusionIsSylowIn_of_normalizes hSIs hWab.isPGroup hWIs hSN
  have hCS : img d S ⊓ centralizer ((Ws d : Subgroup (MulAut ↥d.s56V)) : Set _) = Ws d := by
    refine le_antisymm ?_ (le_inf hWS (le_centralizer_of_isElemAbelian hWab))
    have hC : img d S ⊓ centralizer ((Ws d : Subgroup (MulAut ↥d.s56V)) : Set _) ≤
        centralizer ((Ws d : Subgroup (MulAut ↥d.s56V)) : Set _) ⊓ Hs d :=
      le_inf inf_le_right ((inf_le_left.trans (hSIs.1.trans inf_le_right)))
    have hCp : IsPGroup 2 ↥(img d S ⊓ centralizer ((Ws d : Subgroup (MulAut ↥d.s56V)) : Set _)) :=
      hSIs.2.1.to_le inf_le_left
    exact (hSylW.2.2 _ hC hCp (le_inf hWS (le_centralizer_of_isElemAbelian hWab))).symm ▸ le_rfl
  obtain ⟨c1, c2, c3, c4, c5⟩ := six23 hWab hW256 hWS hSN hCS hP1 hP2 hE2S
  have hH : fusionIsSylowIn 2 S (Hg d) :=
    fusionIsSylowIn_normalizer_of_maxElemAbelian2 d.s56V hWab hS.1 c1
  have hSylHs : fusionIsSylowIn 2 (img d S) (Hs d) :=
    fusionIsSylowIn_imgIn d.s56V hH le_rfl
  refine ⟨⟨c1, fun h _ => c2 h, c3, c4⟩, hH, ?_⟩
  have hx1 : star d d.x₅ ≠ 1 := star_x5_ne_one_of_card h49 hd hUcard
  have hxN : star d d.x₅ ∈ normalizer ((Ws d : Subgroup (MulAut ↥d.s56V)) : Set _) :=
    mem_normalizer_of_maxElemAbelian2 hmaxK hxKs
  have htN : star d d.t ∈ normalizer ((Ws d : Subgroup (MulAut ↥d.s56V)) : Set _) :=
    mem_normalizer_of_maxElemAbelian2 hmaxK htKs
  have hfpf : ∀ a ∈ Ws d, star d d.x₅ * a * (star d d.x₅)⁻¹ = a → a = 1 :=
    fpf_of_commutator (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Ks d)) (star_x5_pow_five h49 hd)
      hx1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Ks d) hxKs) (Ws_eq h49 hd) hWab
  have hCt : ∀ a ∈ Ws d, star d d.t * a * (star d d.t)⁻¹ = a ↔ a ∈ Us d := by
    intro a ha
    rw [← hWt]
    constructor
    · intro h
      refine ⟨ha, mem_centralizer_singleton_iff.2 ?_⟩
      calc a * star d d.t = (star d d.t * a * (star d d.t)⁻¹) * star d d.t := by rw [h]
        _ = star d d.t * a := by group
    · rintro ⟨-, h⟩
      have h' : a * star d d.t = star d d.t * a := mem_centralizer_singleton_iff.1 h
      calc star d d.t * a * (star d d.t)⁻¹ = (a * star d d.t) * (star d d.t)⁻¹ := by rw [h']
        _ = a := by group
  obtain ⟨-, -, -, hSC⟩ := h14
  obtain ⟨h, hhH, hh⟩ := hSC
  have htT : d.t ∈ sylT d := t_mem_sylT hd
  have hvT : d.pv 2 ∈ sylT d := pv2_mem_sylT hd
  have htvI : d.t * d.pv 2 ∈ Ig d := mul_mem (hTI htT) (hTI hvT)
  have htvN : d.t * d.pv 2 ∈ Hg d := mul_mem (t_mem_Hg h49 hd) (pv2_mem_Hg h49 hd)
  have hsIs : star d (d.t * d.pv 2) ∈ Is d := ((mem_preIn_iff d.s56V (Is d)).1 htvI).2
  have hsHs : star d (d.t * d.pv 2) ∈ Hs d := actFun_mem_imgIn htvN htvN
  have hsW : star d (d.t * d.pv 2) ∈
      normalizer ((Ws d : Subgroup (MulAut ↥d.s56V)) : Set _) := hsIs.1
  have hconj : star d (h * d.t * h⁻¹) = star d h * star d d.t * (star d h)⁻¹ :=
    actFun_conj d.s56V hhH (t_mem_Hg h49 hd)
  have hs : ∃ g ∈ Hs d, star d (d.t * d.pv 2) = g * star d d.t * g⁻¹ :=
    ⟨star d h, actFun_mem_imgIn hhH hhH, by rw [← hh, hconj]⟩
  have hv : (star d d.t * star d (d.t * d.pv 2)) * star d d.x₅ *
      (star d d.t * star d (d.t * d.pv 2))⁻¹ = (star d d.x₅)⁻¹ := by
    have e : star d d.t * star d (d.t * d.pv 2) = star d (d.pv 2) := by
      show actFun d.s56V d.t * actFun d.s56V (d.t * d.pv 2) = actFun d.s56V (d.pv 2)
      rw [← actFun_mul d.s56V (t_mem_Hg h49 hd) htvN, ← mul_assoc, hd.t_mul_self, one_mul]
    rw [e]
    exact star_pv2_inv_x5 h49 hd
  have hsolv := isSolvable_centralizer_star_t h49 hd hCcent
  exact six25 hTop hSylHs hWHs hWab hW256 hWS (fun g _ => c2 g) c5 c3 c4
    (actFun_mem_imgIn (x5_mem_Hg h49 hd) (x5_mem_Hg h49 hd))
    (actFun_mem_imgIn (t_mem_Hg h49 hd) (t_mem_Hg h49 hd)) hsHs
    (star_x5_pow_five h49 hd) hx1 (star_t_mul_self h49 hd)
    (actFun_comm_of_comm d.s56V hd.s56_x5_comm_t.symm) hxN htN hfpf hWquot.1 hUcard hCt hs hsW hv
    hsolv hE1

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5

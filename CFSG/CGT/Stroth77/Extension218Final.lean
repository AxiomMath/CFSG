module

public import CFSG.CGT.Stroth77.Extension218Cocycle
public import CFSG.CGT.Stroth77.Extension218Images
public import CFSG.CGT.Stroth77.Extension218Assembly
public import CFSG.CGT.Stroth77.Extension218Square

public section

namespace CFSG.CGT.Stroth77

open Matrix Ext218

variable {S : Type*} [Group S] [Finite S] {B C : Subgroup S} {s : ℕ} {hs : 1 ≤ s}

theorem hasStrothType_t121_of_normal_form_t221 (D : StrothTypeData B (StrothTypeIndex.t221 s hs))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) (hL : D.L ≤ Subgroup.normalizer C)
    {d : S} (hdC : d ∈ C) (hdB : d ∉ B) (hd2 : d * d = (D.c : S)) {bU bR bT bV : B}
    (hbU : conjBy (hL D.u_mem_L) (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC bU)
    (hU : D.ec bU = baseU221 s + bv221 s 0 0 0)
    (hbR : conjBy (hL D.ρ_mem_L) (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC bR)
    (hR : D.ec bR = 0)
    (hbT : conjBy (hL D.t_mem_L) (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC bT)
    (hT : D.ec bT = baseT221 s (Type120.GV (s + 4)) + bv221 s 0 0 0)
    (hbV : conjBy (hL D.uv_mem_L) (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC bV)
    (hV : D.ec bV = baseUV221 s (Type120.GV (s + 4)) + bv221 s 0 0 0) :
    HasStrothType C (StrothTypeIndex.t121 (s + 3) (by omega)) := by
  have h' : Type121.Data (s + 3) (Type120.iV (s + 4)) (Type120.FV (s + 4)) (Type120.GV (s + 4))
      (2 ^ (s + 3)) (2 ^ (s + 3 - 1)) := Type121.data (s + 3) (by omega)
  let E : CubicBasisEquiv218 D hBC d hdC (Type121.k (s + 3)) :=
    cubicBasisEquiv218 D hBC hC hrel hdC hdB hd2 (Type121.k (s + 3))
      (by rw [m_t221]; rfl) (by rw [n_t221]; rfl) (by rw [n_t221]; rfl)
  rw [bv221_zero, add_zero, baseU221] at hU
  rw [bv221_zero, add_zero, baseT221] at hT
  rw [bv221_zero, add_zero, baseUV221] at hV
  replace hR := hR.trans zero_eq_gens_t221
  refine hasStrothType_of_images218 D hBC hL hdC (StrothTypeIndex.t121 (s + 3) (by omega)) E
    ?_ ?_ ?_ ?_
  ·
    intro j
    fin_cases j
    · change E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (⟨d, hdC⟩ : C))) =
          (Type121.action h').φuv (gen (Type121.k (s + 3)) 0)
      rw [E_conj_d218 D hBC hdC hd2 E (hL D.uv_mem_L) hbV hV,
        phiUV_gen0_t121_t221 h']
      module
    · change E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type121.action h').φuv (gen (Type121.k (s + 3)) 1)
      rw [E_conj_inclusion218 D hBC hdC hd2 E (hL D.uv_mem_L) D.uv_mem D.a
        (by rw [ec_conj_uv_t221 D, ec_a_t221 D]; exact phiUV_gen1_t221 (Type221.data s)),
        phiUV_gen1_t121_t221 h']
    · change E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type121.action h').φuv (gen (Type121.k (s + 3)) 2)
      rw [E_conj_inclusion218 D hBC hdC hd2 E (hL D.uv_mem_L) D.uv_mem D.b
        (by rw [ec_conj_uv_t221 D, ec_b_t221 D]; exact phiUV_gen2_t221 (Type221.data s)),
        phiUV_gen2_t121_t221 h']
  ·
    intro j
    fin_cases j
    · change E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (⟨d, hdC⟩ : C))) =
          (Type121.action h').φt (gen (Type121.k (s + 3)) 0)
      rw [E_conj_d218 D hBC hdC hd2 E (hL D.t_mem_L) hbT hT,
        phiT_gen0_t121_t221 h']
      module
    · change E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type121.action h').φt (gen (Type121.k (s + 3)) 1)
      rw [E_conj_inclusion218 D hBC hdC hd2 E (hL D.t_mem_L) D.t_mem D.a
        (by rw [ec_conj_t_t221 D, ec_a_t221 D]; exact phiT_gen1_t221 (Type221.data s)),
        phiT_gen1_t121_t221 h']
    · change E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type121.action h').φt (gen (Type121.k (s + 3)) 2)
      rw [E_conj_inclusion218 D hBC hdC hd2 E (hL D.t_mem_L) D.t_mem D.b
        (by rw [ec_conj_t_t221 D, ec_b_t221 D]; exact phiT_gen2_t221 (Type221.data s)),
        phiT_gen2_t121_t221 h']
  ·
    intro j
    fin_cases j
    · change E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (⟨d, hdC⟩ : C))) =
          (Type121.action h').φu (gen (Type121.k (s + 3)) 0)
      rw [E_conj_d218 D hBC hdC hd2 E (hL D.u_mem_L) hbU hU,
        phiU_gen0_t121_t221 h']
      module
    · change E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type121.action h').φu (gen (Type121.k (s + 3)) 1)
      rw [E_conj_inclusion218 D hBC hdC hd2 E (hL D.u_mem_L) D.u_mem D.a
        (by rw [ec_conj_u_t221 D, ec_a_t221 D]; exact phiU_gen1_t221 (Type221.data s)),
        phiU_gen1_t121_t221 h']
    · change E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type121.action h').φu (gen (Type121.k (s + 3)) 2)
      rw [E_conj_inclusion218 D hBC hdC hd2 E (hL D.u_mem_L) D.u_mem D.b
        (by rw [ec_conj_u_t221 D, ec_b_t221 D]; exact phiU_gen2_t221 (Type221.data s)),
        phiU_gen2_t121_t221 h']
  ·
    intro j
    fin_cases j
    · change E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (⟨d, hdC⟩ : C))) =
          (Type121.action h').φρ (gen (Type121.k (s + 3)) 0)
      rw [E_conj_d218 D hBC hdC hd2 E (hL D.ρ_mem_L) hbR hR,
        phiR_gen0_t121_t221 h']
      module
    · change E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type121.action h').φρ (gen (Type121.k (s + 3)) 1)
      rw [E_conj_inclusion218 D hBC hdC hd2 E (hL D.ρ_mem_L) D.ρ_mem D.a
        (by rw [ec_conj_ρ_t221 D, ec_a_t221 D]; exact phiR_gen1_t221 (Type221.data s)),
        phiR_gen1_t121_t221 h']
    · change E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type121.action h').φρ (gen (Type121.k (s + 3)) 2)
      rw [E_conj_inclusion218 D hBC hdC hd2 E (hL D.ρ_mem_L) D.ρ_mem D.b
        (by rw [ec_conj_ρ_t221 D, ec_b_t221 D]; exact phiR_gen2_t221 (Type221.data s)),
        phiR_gen2_t121_t221 h']

theorem hasStrothType_t131_of_normal_form_t221 (D : StrothTypeData B (StrothTypeIndex.t221 s hs))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) (hL : D.L ≤ Subgroup.normalizer C)
    {d : S} (hdC : d ∈ C) (hdB : d ∉ B) (hd2 : d * d = (D.c : S)) {bU bR bT bV : B}
    (hbU : conjBy (hL D.u_mem_L) (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC bU)
    (hU : D.ec bU = baseU221 s + bv221 s 1 0 0)
    (hbR : conjBy (hL D.ρ_mem_L) (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC bR)
    (hR : D.ec bR = 0)
    (hbT : conjBy (hL D.t_mem_L) (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC bT)
    (hT : D.ec bT = baseT221 s (Type120.GV (s + 4)) + bv221 s 0 0 1)
    (hbV : conjBy (hL D.uv_mem_L) (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC bV)
    (hV : D.ec bV = baseUV221 s (Type120.GV (s + 4)) + bv221 s 0 1 0) :
    HasStrothType C (StrothTypeIndex.t131 (s + 3) (by omega)) := by
  have h' : Type131.Data (s + 3) (Type120.iV (s + 4)) (Type120.FV (s + 4)) (Type120.GV (s + 4))
      (2 ^ (s + 3)) (2 ^ (s + 3 - 1)) (2 ^ (s + 3 - 2)) := Type131.data (s + 3) (by omega)
  let E : CubicBasisEquiv218 D hBC d hdC (Type131.k (s + 3)) :=
    cubicBasisEquiv218 D hBC hC hrel hdC hdB hd2 (Type131.k (s + 3))
      (by rw [m_t221]; rfl) (by rw [n_t221]; rfl) (by rw [n_t221]; rfl)
  replace hU := hU.trans baseU_one_t221
  replace hT := hT.trans baseT_one_t221
  replace hV := hV.trans baseUV_one_t221
  replace hR := hR.trans zero_eq_gens_t221
  refine hasStrothType_of_images218 D hBC hL hdC (StrothTypeIndex.t131 (s + 3) (by omega)) E
    ?_ ?_ ?_ ?_
  ·
    intro j
    fin_cases j
    · change E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (⟨d, hdC⟩ : C))) =
          (Type131.action h').φuv (gen (Type131.k (s + 3)) 0)
      rw [E_conj_d218 D hBC hdC hd2 E (hL D.uv_mem_L) hbV hV,
        phiUV_gen0_t131_t221 h']
      module
    · change E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type131.action h').φuv (gen (Type131.k (s + 3)) 1)
      rw [E_conj_inclusion218 D hBC hdC hd2 E (hL D.uv_mem_L) D.uv_mem D.a
        (by rw [ec_conj_uv_t221 D, ec_a_t221 D]; exact phiUV_gen1_t221 (Type221.data s)),
        phiUV_gen1_t131_t221 h']
    · change E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type131.action h').φuv (gen (Type131.k (s + 3)) 2)
      rw [E_conj_inclusion218 D hBC hdC hd2 E (hL D.uv_mem_L) D.uv_mem D.b
        (by rw [ec_conj_uv_t221 D, ec_b_t221 D]; exact phiUV_gen2_t221 (Type221.data s)),
        phiUV_gen2_t131_t221 h']
  ·
    intro j
    fin_cases j
    · change E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (⟨d, hdC⟩ : C))) =
          (Type131.action h').φt (gen (Type131.k (s + 3)) 0)
      rw [E_conj_d218 D hBC hdC hd2 E (hL D.t_mem_L) hbT hT,
        phiT_gen0_t131_t221 h']
      module
    · change E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type131.action h').φt (gen (Type131.k (s + 3)) 1)
      rw [E_conj_inclusion218 D hBC hdC hd2 E (hL D.t_mem_L) D.t_mem D.a
        (by rw [ec_conj_t_t221 D, ec_a_t221 D]; exact phiT_gen1_t221 (Type221.data s)),
        phiT_gen1_t131_t221 h']
    · change E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type131.action h').φt (gen (Type131.k (s + 3)) 2)
      rw [E_conj_inclusion218 D hBC hdC hd2 E (hL D.t_mem_L) D.t_mem D.b
        (by rw [ec_conj_t_t221 D, ec_b_t221 D]; exact phiT_gen2_t221 (Type221.data s)),
        phiT_gen2_t131_t221 h']
  ·
    intro j
    fin_cases j
    · change E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (⟨d, hdC⟩ : C))) =
          (Type131.action h').φu (gen (Type131.k (s + 3)) 0)
      rw [E_conj_d218 D hBC hdC hd2 E (hL D.u_mem_L) hbU hU,
        phiU_gen0_t131_t221 h']
      module
    · change E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type131.action h').φu (gen (Type131.k (s + 3)) 1)
      rw [E_conj_inclusion218 D hBC hdC hd2 E (hL D.u_mem_L) D.u_mem D.a
        (by rw [ec_conj_u_t221 D, ec_a_t221 D]; exact phiU_gen1_t221 (Type221.data s)),
        phiU_gen1_t131_t221 h']
    · change E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type131.action h').φu (gen (Type131.k (s + 3)) 2)
      rw [E_conj_inclusion218 D hBC hdC hd2 E (hL D.u_mem_L) D.u_mem D.b
        (by rw [ec_conj_u_t221 D, ec_b_t221 D]; exact phiU_gen2_t221 (Type221.data s)),
        phiU_gen2_t131_t221 h']
  ·
    intro j
    fin_cases j
    · change E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (⟨d, hdC⟩ : C))) =
          (Type131.action h').φρ (gen (Type131.k (s + 3)) 0)
      rw [E_conj_d218 D hBC hdC hd2 E (hL D.ρ_mem_L) hbR hR,
        phiR_gen0_t131_t221 h']
      module
    · change E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type131.action h').φρ (gen (Type131.k (s + 3)) 1)
      rw [E_conj_inclusion218 D hBC hdC hd2 E (hL D.ρ_mem_L) D.ρ_mem D.a
        (by rw [ec_conj_ρ_t221 D, ec_a_t221 D]; exact phiR_gen1_t221 (Type221.data s)),
        phiR_gen1_t131_t221 h']
    · change E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type131.action h').φρ (gen (Type131.k (s + 3)) 2)
      rw [E_conj_inclusion218 D hBC hdC hd2 E (hL D.ρ_mem_L) D.ρ_mem D.b
        (by rw [ec_conj_ρ_t221 D, ec_b_t221 D]; exact phiR_gen2_t221 (Type221.data s)),
        phiR_gen2_t131_t221 h']

theorem hasStrothTypeOver_t121_of_normal_form_t221
    (D : StrothTypeData B (StrothTypeIndex.t221 s hs))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) (hL : D.L ≤ Subgroup.normalizer C)
    {d : S} (hdC : d ∈ C) (hdB : d ∉ B) (hd2 : d * d = (D.c : S)) {bU bR bT bV : B}
    (hbU : conjBy (hL D.u_mem_L) (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC bU)
    (hU : D.ec bU = baseU221 s + bv221 s 0 0 0)
    (hbR : conjBy (hL D.ρ_mem_L) (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC bR)
    (hR : D.ec bR = 0)
    (hbT : conjBy (hL D.t_mem_L) (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC bT)
    (hT : D.ec bT = baseT221 s (Type120.GV (s + 4)) + bv221 s 0 0 0)
    (hbV : conjBy (hL D.uv_mem_L) (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC bV)
    (hV : D.ec bV = baseUV221 s (Type120.GV (s + 4)) + bv221 s 0 0 0) :
    HasStrothTypeOver D C (StrothTypeIndex.t121 (s + 3) (by omega)) := by
  have h' : Type121.Data (s + 3) (Type120.iV (s + 4)) (Type120.FV (s + 4)) (Type120.GV (s + 4))
      (2 ^ (s + 3)) (2 ^ (s + 3 - 1)) := Type121.data (s + 3) (by omega)
  let E : CubicBasisEquiv218 D hBC d hdC (Type121.k (s + 3)) :=
    cubicBasisEquiv218 D hBC hC hrel hdC hdB hd2 (Type121.k (s + 3))
      (by rw [m_t221]; rfl) (by rw [n_t221]; rfl) (by rw [n_t221]; rfl)
  rw [bv221_zero, add_zero, baseU221] at hU
  rw [bv221_zero, add_zero, baseT221] at hT
  rw [bv221_zero, add_zero, baseUV221] at hV
  replace hR := hR.trans zero_eq_gens_t221
  refine hasStrothTypeOver_of_images218 D hBC hL hdC (StrothTypeIndex.t121 (s + 3) (by omega)) E
    ?_ ?_ ?_ ?_
  ·
    intro j
    fin_cases j
    · change E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (⟨d, hdC⟩ : C))) =
          (Type121.action h').φuv (gen (Type121.k (s + 3)) 0)
      rw [E_conj_d218 D hBC hdC hd2 E (hL D.uv_mem_L) hbV hV,
        phiUV_gen0_t121_t221 h']
      module
    · change E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type121.action h').φuv (gen (Type121.k (s + 3)) 1)
      rw [E_conj_inclusion218 D hBC hdC hd2 E (hL D.uv_mem_L) D.uv_mem D.a
        (by rw [ec_conj_uv_t221 D, ec_a_t221 D]; exact phiUV_gen1_t221 (Type221.data s)),
        phiUV_gen1_t121_t221 h']
    · change E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type121.action h').φuv (gen (Type121.k (s + 3)) 2)
      rw [E_conj_inclusion218 D hBC hdC hd2 E (hL D.uv_mem_L) D.uv_mem D.b
        (by rw [ec_conj_uv_t221 D, ec_b_t221 D]; exact phiUV_gen2_t221 (Type221.data s)),
        phiUV_gen2_t121_t221 h']
  ·
    intro j
    fin_cases j
    · change E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (⟨d, hdC⟩ : C))) =
          (Type121.action h').φt (gen (Type121.k (s + 3)) 0)
      rw [E_conj_d218 D hBC hdC hd2 E (hL D.t_mem_L) hbT hT,
        phiT_gen0_t121_t221 h']
      module
    · change E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type121.action h').φt (gen (Type121.k (s + 3)) 1)
      rw [E_conj_inclusion218 D hBC hdC hd2 E (hL D.t_mem_L) D.t_mem D.a
        (by rw [ec_conj_t_t221 D, ec_a_t221 D]; exact phiT_gen1_t221 (Type221.data s)),
        phiT_gen1_t121_t221 h']
    · change E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type121.action h').φt (gen (Type121.k (s + 3)) 2)
      rw [E_conj_inclusion218 D hBC hdC hd2 E (hL D.t_mem_L) D.t_mem D.b
        (by rw [ec_conj_t_t221 D, ec_b_t221 D]; exact phiT_gen2_t221 (Type221.data s)),
        phiT_gen2_t121_t221 h']
  ·
    intro j
    fin_cases j
    · change E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (⟨d, hdC⟩ : C))) =
          (Type121.action h').φu (gen (Type121.k (s + 3)) 0)
      rw [E_conj_d218 D hBC hdC hd2 E (hL D.u_mem_L) hbU hU,
        phiU_gen0_t121_t221 h']
      module
    · change E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type121.action h').φu (gen (Type121.k (s + 3)) 1)
      rw [E_conj_inclusion218 D hBC hdC hd2 E (hL D.u_mem_L) D.u_mem D.a
        (by rw [ec_conj_u_t221 D, ec_a_t221 D]; exact phiU_gen1_t221 (Type221.data s)),
        phiU_gen1_t121_t221 h']
    · change E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type121.action h').φu (gen (Type121.k (s + 3)) 2)
      rw [E_conj_inclusion218 D hBC hdC hd2 E (hL D.u_mem_L) D.u_mem D.b
        (by rw [ec_conj_u_t221 D, ec_b_t221 D]; exact phiU_gen2_t221 (Type221.data s)),
        phiU_gen2_t121_t221 h']
  ·
    intro j
    fin_cases j
    · change E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (⟨d, hdC⟩ : C))) =
          (Type121.action h').φρ (gen (Type121.k (s + 3)) 0)
      rw [E_conj_d218 D hBC hdC hd2 E (hL D.ρ_mem_L) hbR hR,
        phiR_gen0_t121_t221 h']
      module
    · change E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type121.action h').φρ (gen (Type121.k (s + 3)) 1)
      rw [E_conj_inclusion218 D hBC hdC hd2 E (hL D.ρ_mem_L) D.ρ_mem D.a
        (by rw [ec_conj_ρ_t221 D, ec_a_t221 D]; exact phiR_gen1_t221 (Type221.data s)),
        phiR_gen1_t121_t221 h']
    · change E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type121.action h').φρ (gen (Type121.k (s + 3)) 2)
      rw [E_conj_inclusion218 D hBC hdC hd2 E (hL D.ρ_mem_L) D.ρ_mem D.b
        (by rw [ec_conj_ρ_t221 D, ec_b_t221 D]; exact phiR_gen2_t221 (Type221.data s)),
        phiR_gen2_t121_t221 h']

theorem hasStrothTypeOver_t131_of_normal_form_t221
    (D : StrothTypeData B (StrothTypeIndex.t221 s hs))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) (hL : D.L ≤ Subgroup.normalizer C)
    {d : S} (hdC : d ∈ C) (hdB : d ∉ B) (hd2 : d * d = (D.c : S)) {bU bR bT bV : B}
    (hbU : conjBy (hL D.u_mem_L) (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC bU)
    (hU : D.ec bU = baseU221 s + bv221 s 1 0 0)
    (hbR : conjBy (hL D.ρ_mem_L) (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC bR)
    (hR : D.ec bR = 0)
    (hbT : conjBy (hL D.t_mem_L) (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC bT)
    (hT : D.ec bT = baseT221 s (Type120.GV (s + 4)) + bv221 s 0 0 1)
    (hbV : conjBy (hL D.uv_mem_L) (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC bV)
    (hV : D.ec bV = baseUV221 s (Type120.GV (s + 4)) + bv221 s 0 1 0) :
    HasStrothTypeOver D C (StrothTypeIndex.t131 (s + 3) (by omega)) := by
  have h' : Type131.Data (s + 3) (Type120.iV (s + 4)) (Type120.FV (s + 4)) (Type120.GV (s + 4))
      (2 ^ (s + 3)) (2 ^ (s + 3 - 1)) (2 ^ (s + 3 - 2)) := Type131.data (s + 3) (by omega)
  let E : CubicBasisEquiv218 D hBC d hdC (Type131.k (s + 3)) :=
    cubicBasisEquiv218 D hBC hC hrel hdC hdB hd2 (Type131.k (s + 3))
      (by rw [m_t221]; rfl) (by rw [n_t221]; rfl) (by rw [n_t221]; rfl)
  replace hU := hU.trans baseU_one_t221
  replace hT := hT.trans baseT_one_t221
  replace hV := hV.trans baseUV_one_t221
  replace hR := hR.trans zero_eq_gens_t221
  refine hasStrothTypeOver_of_images218 D hBC hL hdC (StrothTypeIndex.t131 (s + 3) (by omega)) E
    ?_ ?_ ?_ ?_
  ·
    intro j
    fin_cases j
    · change E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (⟨d, hdC⟩ : C))) =
          (Type131.action h').φuv (gen (Type131.k (s + 3)) 0)
      rw [E_conj_d218 D hBC hdC hd2 E (hL D.uv_mem_L) hbV hV,
        phiUV_gen0_t131_t221 h']
      module
    · change E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type131.action h').φuv (gen (Type131.k (s + 3)) 1)
      rw [E_conj_inclusion218 D hBC hdC hd2 E (hL D.uv_mem_L) D.uv_mem D.a
        (by rw [ec_conj_uv_t221 D, ec_a_t221 D]; exact phiUV_gen1_t221 (Type221.data s)),
        phiUV_gen1_t131_t221 h']
    · change E.e (Additive.ofMul (conjBy (hL D.uv_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type131.action h').φuv (gen (Type131.k (s + 3)) 2)
      rw [E_conj_inclusion218 D hBC hdC hd2 E (hL D.uv_mem_L) D.uv_mem D.b
        (by rw [ec_conj_uv_t221 D, ec_b_t221 D]; exact phiUV_gen2_t221 (Type221.data s)),
        phiUV_gen2_t131_t221 h']
  ·
    intro j
    fin_cases j
    · change E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (⟨d, hdC⟩ : C))) =
          (Type131.action h').φt (gen (Type131.k (s + 3)) 0)
      rw [E_conj_d218 D hBC hdC hd2 E (hL D.t_mem_L) hbT hT,
        phiT_gen0_t131_t221 h']
      module
    · change E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type131.action h').φt (gen (Type131.k (s + 3)) 1)
      rw [E_conj_inclusion218 D hBC hdC hd2 E (hL D.t_mem_L) D.t_mem D.a
        (by rw [ec_conj_t_t221 D, ec_a_t221 D]; exact phiT_gen1_t221 (Type221.data s)),
        phiT_gen1_t131_t221 h']
    · change E.e (Additive.ofMul (conjBy (hL D.t_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type131.action h').φt (gen (Type131.k (s + 3)) 2)
      rw [E_conj_inclusion218 D hBC hdC hd2 E (hL D.t_mem_L) D.t_mem D.b
        (by rw [ec_conj_t_t221 D, ec_b_t221 D]; exact phiT_gen2_t221 (Type221.data s)),
        phiT_gen2_t131_t221 h']
  ·
    intro j
    fin_cases j
    · change E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (⟨d, hdC⟩ : C))) =
          (Type131.action h').φu (gen (Type131.k (s + 3)) 0)
      rw [E_conj_d218 D hBC hdC hd2 E (hL D.u_mem_L) hbU hU,
        phiU_gen0_t131_t221 h']
      module
    · change E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type131.action h').φu (gen (Type131.k (s + 3)) 1)
      rw [E_conj_inclusion218 D hBC hdC hd2 E (hL D.u_mem_L) D.u_mem D.a
        (by rw [ec_conj_u_t221 D, ec_a_t221 D]; exact phiU_gen1_t221 (Type221.data s)),
        phiU_gen1_t131_t221 h']
    · change E.e (Additive.ofMul (conjBy (hL D.u_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type131.action h').φu (gen (Type131.k (s + 3)) 2)
      rw [E_conj_inclusion218 D hBC hdC hd2 E (hL D.u_mem_L) D.u_mem D.b
        (by rw [ec_conj_u_t221 D, ec_b_t221 D]; exact phiU_gen2_t221 (Type221.data s)),
        phiU_gen2_t131_t221 h']
  ·
    intro j
    fin_cases j
    · change E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (⟨d, hdC⟩ : C))) =
          (Type131.action h').φρ (gen (Type131.k (s + 3)) 0)
      rw [E_conj_d218 D hBC hdC hd2 E (hL D.ρ_mem_L) hbR hR,
        phiR_gen0_t131_t221 h']
      module
    · change E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (⟨D.a, hBC D.a.2⟩ : C))) =
          (Type131.action h').φρ (gen (Type131.k (s + 3)) 1)
      rw [E_conj_inclusion218 D hBC hdC hd2 E (hL D.ρ_mem_L) D.ρ_mem D.a
        (by rw [ec_conj_ρ_t221 D, ec_a_t221 D]; exact phiR_gen1_t221 (Type221.data s)),
        phiR_gen1_t131_t221 h']
    · change E.e (Additive.ofMul (conjBy (hL D.ρ_mem_L) (⟨D.b, hBC D.b.2⟩ : C))) =
          (Type131.action h').φρ (gen (Type131.k (s + 3)) 2)
      rw [E_conj_inclusion218 D hBC hdC hd2 E (hL D.ρ_mem_L) D.ρ_mem D.b
        (by rw [ec_conj_ρ_t221 D, ec_b_t221 D]; exact phiR_gen2_t221 (Type221.data s)),
        phiR_gen2_t131_t221 h']

end CFSG.CGT.Stroth77

module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6E26C
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6E26D

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y6e_B_mod_F (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    (∀ x ∈ c.s.fr.B, x ^ 2 ∈ c.s.fr.F) ∧
      (∀ x ∈ c.s.fr.B, ∀ y ∈ c.s.fr.B, ⁅x, y⁆ ∈ c.s.fr.F) := by
  obtain ⟨hn, hmax⟩ := hH.hLF.fact14.2.2.2.2.1.1
  have hn' : (c.s.fr.F.subgroupOf c.s.fr.S).Normal := hn
  haveI := hn'
  have hmax' : maxElemAbelian (⊤ : Subgroup (↥c.s.fr.S ⧸ c.s.fr.F.subgroupOf c.s.fr.S)) =
      {(c.s.fr.A.subgroupOf c.s.fr.S).map (QuotientGroup.mk' (c.s.fr.F.subgroupOf c.s.fr.S)),
        (c.s.fr.B.subgroupOf c.s.fr.S).map
          (QuotientGroup.mk' (c.s.fr.F.subgroupOf c.s.fr.S))} := hmax
  have hmem : (c.s.fr.B.subgroupOf c.s.fr.S).map
      (QuotientGroup.mk' (c.s.fr.F.subgroupOf c.s.fr.S)) ∈
        maxElemAbelian (⊤ : Subgroup (↥c.s.fr.S ⧸ c.s.fr.F.subgroupOf c.s.fr.S)) := by
    rw [hmax']
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  exact y6e_of_isElemAbelian_map (s3_B_le_S c.s) hmem.2.1

theorem y6e_psi (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ∃ ψ : ↥(M3 c.s) →* ↥c.s.fr.F, Function.Surjective ψ ∧
      (∀ m : ↥(M3 c.s), ψ m = 1 ↔ (m : G) ∈ c.s.fr.F) ∧
      ∀ n ∈ normIn c.s.H c.s.fr.F, ∀ m m' : ↥(M3 c.s), (m' : G) = n * m * n⁻¹ →
        ((ψ m' : ↥c.s.fr.F) : G) = n * (ψ m : G) * n⁻¹ := by
  obtain ⟨hn, φ, hφ⟩ := y54_secProp c hH
  haveI := hn
  refine ⟨φ.toMonoidHom.comp (QuotientGroup.mk' (c.s.fr.F.subgroupOf (M3 c.s))),
    φ.surjective.comp (QuotientGroup.mk'_surjective _), fun m => ?_,
    fun n hn' m m' h => hφ n hn' m m' h⟩
  show φ (QuotientGroup.mk' (c.s.fr.F.subgroupOf (M3 c.s)) m) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf]

theorem y6e_exists_W (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hF : c.Facts5) :
    ∃ W : Subgroup G, W ≤ M3 c.s ∧ c.s.fr.F ≤ W ∧ 4 * Nat.card ↥c.s.fr.F ≤ Nat.card ↥W ∧
      (∀ x ∈ W, x ^ 2 ∈ c.s.fr.F) ∧ (∀ x ∈ W, ∀ y ∈ W, ⁅x, y⁆ ∈ c.s.fr.F) ∧
      (∀ x ∈ c.s.fr.B, ∀ y ∈ W, ⁅x, y⁆ ∈ c.s.fr.F) := by
  obtain ⟨ψ, hsurj, hker, hequi⟩ := y6e_psi c hH
  haveI := y6e_M3_comm c hF
  have hFM : c.s.fr.F ≤ M3 c.s := le_sup_right
  have hVF : cen c.s.fr.B ≤ c.s.fr.F := y54_V_le_F hH
  let K : Subgroup ↥c.s.fr.F := (cen c.s.fr.B).subgroupOf c.s.fr.F
  let W0 : Subgroup ↥(M3 c.s) := K.comap ψ
  have hWM : W0.map (M3 c.s).subtype ≤ M3 c.s := Subgroup.map_subtype_le W0
  have hFW : c.s.fr.F ≤ W0.map (M3 c.s).subtype := by
    intro x hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hFM hx⟩, ?_, rfl⟩
    show ψ ⟨x, hFM hx⟩ ∈ K
    rw [(hker ⟨x, hFM hx⟩).2 hx]
    exact K.one_mem
  have hmemW : ∀ x : G, x ∈ W0.map (M3 c.s).subtype →
      ∃ m : ↥(M3 c.s), ψ m ∈ K ∧ (m : G) = x := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨m, hm, rfl⟩
  refine ⟨W0.map (M3 c.s).subtype, hWM, hFW, ?_, ?_, ?_, ?_⟩
  · have hker' : ψ.ker = c.s.fr.F.subgroupOf (M3 c.s) := by
      ext m
      rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    have hcard := y6e_card_map_mul_card_ker hWM hFW ψ hker'
    have h1 : (W0.map (M3 c.s).subtype).subgroupOf (M3 c.s) = W0 := by
      rw [← Subgroup.comap_subtype]
      exact W0.comap_map_eq_self_of_injective Subtype.coe_injective
    have h2 : W0.map ψ = K := Subgroup.map_comap_eq_self_of_surjective hsurj K
    rw [h1, h2] at hcard
    have h3 : Nat.card ↥K = 4 := by
      rw [← y54_V_card hH]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVF).toEquiv
    rw [h3] at hcard
    omega
  · intro x hx
    obtain ⟨m, -, rfl⟩ := hmemW x hx
    have h1 : ψ (m ^ 2) = 1 := by
      rw [map_pow]
      apply Subtype.ext
      simpa using y54_F_sq hH _ (ψ m).2
    exact (hker _).1 h1
  · intro x hx y hy
    obtain ⟨m, -, rfl⟩ := hmemW x hx
    obtain ⟨m', -, rfl⟩ := hmemW y hy
    rw [(commutatorElement_eq_one_iff_mul_comm).2
      (Subgroup.mul_comm_of_mem_isMulCommutative _ m.2 m'.2)]
    exact c.s.fr.F.one_mem
  · intro b hb y hy
    obtain ⟨m, hmK, rfl⟩ := hmemW y hy
    have hbS : b ∈ c.s.fr.S := s3_B_le_S c.s hb
    have hbN : b ∈ normIn L c.s.fr.F := y54_S_le_N hH hbS
    have hbH : b ∈ normIn c.s.H c.s.fr.F :=
      Subgroup.mem_inf.mpr ⟨s3_L_le_H c.s hH.hS (Subgroup.mem_inf.mp hbN).1,
        (Subgroup.mem_inf.mp hbN).2⟩
    have hbM : b * (m : G) * b⁻¹ ∈ M3 c.s :=
      y54_N_norm_M3 c hH b (y54_NL_le_N hH hbN) m m.2
    have hcen : ((ψ m : ↥c.s.fr.F) : G) ∈ cen c.s.fr.B := Subgroup.mem_subgroupOf.mp hmK
    have hcomm : b * ((ψ m : ↥c.s.fr.F) : G) * b⁻¹ = ((ψ m : ↥c.s.fr.F) : G) := by
      have h := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hcen).2) b hb
      rw [h, mul_assoc, mul_inv_cancel, mul_one]
    have heq : ψ ⟨b * (m : G) * b⁻¹, hbM⟩ = ψ m := by
      apply Subtype.ext
      rw [hequi b hbH m ⟨b * (m : G) * b⁻¹, hbM⟩ rfl, hcomm]
    have h1 : ψ (⟨b * (m : G) * b⁻¹, hbM⟩ * m⁻¹) = 1 := by
      rw [map_mul, map_inv, heq, mul_inv_cancel]
    have h2 := (hker _).1 h1
    simpa [commutatorElement_def] using h2

theorem y6e_false_of_hsec (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hF : c.Facts5)
    (hQ : HRG23 (↥L ⧸ Subgroup.center ↥L))
    (hsec : SecProp (⊤ : Subgroup ↥(S3 c.s)) (c.s.fr.F.subgroupOf (S3 c.s))
      (fun Y _ _ _ => Sec2.IsG23Type Y)) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨W, hWM, hFW, hcW, hWsq, hWc, hBWc⟩ := y6e_exists_W c hH hF
  obtain ⟨hBsq, hBc⟩ := y6e_B_mod_F c hH
  have hZ : Subgroup.center ↥L = ⊥ := by
    have h := f3_zL_eq_bot hH
    unfold zL at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).1 h
  let S' : Sylow 2 (↥L ⧸ Subgroup.center ↥L) := Classical.arbitrary _
  have h3 : CFSG.pRank 2 ↥S' = 3 :=
    y6e_pRank_sylow_quotient c.s.sylow_S hZ hH.hLF.fact14.2.2.2.2.2.2.1 S'
  refine y6e_false_of_G23Type_sub (S := S3 c.s) (N := c.s.fr.F) (B := c.s.fr.B) (W := W)
    ((s3_B_le_S c.s).trans le_sup_left) (hWM.trans le_sup_right) (y54_F_le_B hH) hFW ?_
    hBsq hBc hWsq hWc hBWc ?_ hcW hQ S' h3 hsec
  · intro x hx
    have hxS : x ∈ c.s.fr.S := s3_B_le_S c.s hx.1
    have hxM : x ∈ M3 c.s := hWM hx.2
    rw [← y6e_S_inf_M3 c hH]
    exact ⟨hxS, hxM⟩
  · rw [y54_card_B hH, (y54_F_isE3 hH).2]
    norm_num

end CFSG.OddStandard.HigherRank.YamadaG23

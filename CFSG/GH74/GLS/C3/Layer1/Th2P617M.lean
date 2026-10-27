module

public import CFSG.GH74.GLS.C3.Layer1.Th2P617H
public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Equiv Equiv.Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.Th2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x y : G} {K T S : Subgroup G}

theorem false_of_E (hG : C3Hyp G)
    (hs : Th2Std x y K T S) (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    {B : Subgroup G} (hB : IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B) {b : G} {J : Subgroup G}
    (hobs : Obstr52 B b J) {E : Subgroup G} (hES : IsS (T ⊓ CxK x K) E) (hEB : E ≤ B)
    (hP8 : Nat.card ↥(T ⊓ K) = 8) (hxb : b ≠ x) (hbE : b ∈ E) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eK⟩ := h7
  have hcen := centerlessBar_of_A7 ⟨eK⟩
  have hcd := hs.commDisj hcen
  have hr4 : pRank 2 G = 4 := hG.pRank_eq_four
  have hG4 : pRank 2 G ≤ 4 := hr4.le
  have hKn := hs.K_normal_A7 hG ⟨eK⟩
  have hE4 : IsE 4 ⊤ B := isE_of_isSn le_top hB le_rfl
  have hBel : CFSG.IsElementaryAbelian 2 ↥B := hE4.2.1
  have hBR : B ≤ (T ⊓ K) ⊔ (T ⊓ CxK x K) := hB.1.1
  have hBT : B ≤ T := hBR.trans (sup_le inf_le_left inf_le_left)
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  have hEQ : E ≤ T ⊓ CxK x K := hES.1
  have hbo : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hBsq b hobs.mem) hobs.ne_one
  have hxo := hs.orderOf_x
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hxo; omega
  have hxQ : x ∈ T ⊓ CxK x K := ⟨hs.x_mem_T, hs.x_mem_CxK⟩
  have hxE : x ∈ E := hs.x_mem_of_isS (X := T ⊓ CxK x K) inf_le_left hxQ hES
  have hxB : x ∈ B := hEB hxE
  have hbC : b ∈ CxK x K := (hEQ hbE).2
  have hterm : IsTwoTerminal x K := hs.v2ss.isV2Triple.2.1
  have hR3 : 3 ≤ pRank 2 ↥(centralizer ({b} : Set G)) :=
    TwoThin.rankThreeCentralizers G hG.kproper.1 hG.kproper.2.1 (by rw [hr4]; norm_num) b hbo
  obtain ⟨Kb, hlt⟩ := TwoThin.exists_pumpup_of_involution hxo hbo hs.comp hbC.1 hbC.2 hterm.1 hR3
  have hKbc : IsPCompIn 2 (centralizer ({b} : Set G)) Kb := hlt.2.1.2.2
  have htr := hterm.2.1 b Kb hlt
  obtain ⟨Λ, hΛ⟩ := C3.Layer1.Iv251.exists_trivData hlt htr
  have hJKb : J ≠ Kb := by
    intro hJ
    have hxC : x ∈ CxK b J := hJ ▸ hΛ.x_mem
    rcases hobs.B_inf_ker hG4 hBel hE4.2.2 hxB hxC.2 with h1 | h1
    · exact hx1 h1
    · exact hxb h1.symm
  have hKbJ : Kb ≤ centralizerSection J (pPrimeCoreOf 2 J) :=
    Stage1.Thm2.Recip.le_cSec_of_ne hKbc hobs.comp (fun h => hJKb h.symm)
  have hPKb : T ⊓ K ≤ Kb := by
    intro p hp
    have hpb : p * b = b * p := hcd.comm p hp b (hEQ hbE)
    obtain ⟨k, hk⟩ : ∃ k : ℕ, p ^ (2 ^ k) = 1 := by
      obtain ⟨k, hk⟩ := hs.T_pGroup ⟨p, hp.1⟩
      exact ⟨k, congrArg Subtype.val hk⟩
    exact hΛ.le (hΛ.lam.twoElt p ⟨hp.2, mem_centralizer_singleton_iff.2 hpb⟩ ⟨k, hk⟩)
  set V : Subgroup G := T ⊓ centralizer ({b} : Set G) with hV
  have hBV : B ≤ V := fun β hβ => ⟨hBT hβ, hobs.B_le_centralizer hBel hβ⟩
  have hV2 : IsPGroup 2 ↥V := hs.T_pGroup.to_inf_left
  have hPV : T ⊓ K ≤ V := fun p hp =>
    ⟨hp.1, mem_centralizer_singleton_iff.2 (hcd.comm p hp b (hEQ hbE))⟩
  have hNn : V ≤ normalizer ((T ⊓ K : Subgroup G) : Set G) := fun v hv =>
    hs.mem_normalizer_P hKn hv.1
  have hP1 : T ⊓ K ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hP8
    omega
  have hbP := hobs.b_mem_of_normal_ker hG4 hBel hE4.2.2 (X := V) hV2 hBV (N := T ⊓ K) hPV hNn
    (fun p hp => ⟨(hPV hp).2, hKbJ (hPKb hp)⟩) hP1
  exact hobs.ne_one (hcd.eq_one_of_mem hbP (hEQ hbE))

end CFSG.GH74.GLS.Th2.Obs

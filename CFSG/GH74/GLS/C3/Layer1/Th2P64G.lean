module

public import CFSG.GH74.GLS.C3.Layer1.Th2P64C
public import CFSG.GH74.GLS.C3.Layer1.Th2P64F
public import CFSG.GH74.GLS.C3.Layer1.Th2P617B
public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR2
public import CFSG.GH74.GLS.C3.Layer1.Th2Cor6R4B

public section

namespace CFSG.GH74.GLS

open Equiv Equiv.Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.Obs
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x y : G} {K T S : Subgroup G}

theorem Th2Std.hasL2Model_odd (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem) (hG : C3Hyp G)
    (hs : Th2Std x y K T S) (hKA : ¬ Nonempty (kBar K ≃* alternatingGroup (Fin 7))) :
    HasL2Model (kBar K) Odd := by
  have hKU : InU2 (kBar K) := h102 G hG x y K hs.v2ss.isV2StarTriple.1.1.1.1.1
  rcases hKU.2 with hL | hA | ⟨hl34, hel, hcard⟩
  · exact hL
  · exact absurd hA hKA
  · exact absurd ⟨hl34, hel, hcard⟩ (hL34 G hG.gen4 x K hs.orderOf_x hs.comp)

end CFSG.GH74.GLS

namespace CFSG.GH74.GLS.Th2.Obs

open Equiv Equiv.Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x y : G} {K T S : Subgroup G}

theorem Obstr52.ne_x_of_shape (hG : C3Hyp G) (hs : Th2Std x y K T S) (hcen : CenterlessBar K)
    (hP : RankTwoShape (T ⊓ K)) {B : Subgroup G} {b : G} {J : Subgroup G}
    (hB : IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B) (hobs : Th2.Obs.Obstr52 B b J) (hJK : J ≠ K) :
    b ≠ x := by
  classical
  intro hbx
  rw [hbx] at hobs
  have hE : IsE 4 ⊤ B := isE_of_isSn le_top hB le_rfl
  have hBel := hE.2.1
  have hG4 : pRank 2 G ≤ 4 := hG.pRank_eq_four.le
  have hPQ := hs.commDisj hcen
  obtain ⟨U, hU, E₁, hE₁S, hE₁2, hBdef⟩ := (isS_sup_iff hPQ hP B).1 hB
  have hEqQ : E₁ ≤ T ⊓ CxK x K := hE₁S.1
  have hBN : ∀ g ∈ B, g ∈ normalizer (J : Set G) := hobs.normalizes hG4 hBel
  have hE₁N : E₁ ≤ normalizer (J : Set G) := fun q hq => hBN q (hBdef ▸ Subgroup.mem_sup_right hq)
  have hKJ : K ≤ centralizerSection J (pPrimeCoreOf 2 J) :=
    Stage1.Thm2.Recip.le_cSec_of_ne hs.comp hobs.comp hJK.symm
  have hE₁card : Nat.card ↥E₁ ≤ 4 := by
    have h1 := C3.Layer1.Back.card_eq_two_pow_pRank hE₁S.2.1
    have h2 : pRank 2 ↥E₁ ≤ 2 := by
      have hrk := hPQ.pRank_sup hU.2.1 hE₁S.2.1 hU.1 hEqQ
      have hUr : pRank 2 ↥U = 2 := pRank_of_isFourSub hU
      have hle : pRank 2 ↥(U ⊔ E₁) ≤ pRank 2 G := pRank_le_top' _
      omega
    rw [h1]
    calc 2 ^ pRank 2 ↥E₁ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h2
      _ = 4 := by norm_num
  refine hobs.false_of_image_le hG4 hBel (A := E₁) hE₁card hE₁N ?_
  intro g hg
  have hg' : g ∈ U ⊔ E₁ := hBdef ▸ hg
  obtain ⟨u, hu, q, hq, hgq⟩ := exists_mul_of_mem_sup_of_commute
    (fun u hu q hq => hPQ.comm u (hU.1 hu) q (hEqQ hq)) hg'
  have huK : u ∈ K := (hU.1 hu).2
  have hus : u ∈ centralizerSection J (pPrimeCoreOf 2 J) := hKJ huK
  have huN : u ∈ normalizer (J : Set G) := hus.1
  have hqN : q ∈ normalizer (J : Set G) := hE₁N hq
  refine ⟨q, hq, ?_⟩
  have h1 : barAct J ⟨u, huN⟩ = 1 := (barAct_eq_one_iff _).2 hus
  have : (⟨g, hBN g hg⟩ : ↥(normalizer (J : Set G))) = ⟨u, huN⟩ * ⟨q, hqN⟩ :=
    Subtype.ext hgq
  rw [this, map_mul, h1, one_mul]

end CFSG.GH74.GLS.Th2.Obs

namespace CFSG.GH74.GLS

open Equiv Equiv.Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.Obs
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x y : G} {K T S : Subgroup G}

@[expose] def B_prop64_lemma66 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S : Subgroup G),
    Th2Std x y K T S → HasL2Model (kBar K) Odd →
      ∀ B : Subgroup G, IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B →
        ∀ (b : G) (J : Subgroup G), Th2.Obs.Obstr52 B b J →
          Nonempty (kBar J ≃* alternatingGroup (Fin 7)) → twoPartCard (CxK b J) = 2 →
            (∀ q ∈ CxK x K, orderOf q = 2 → ∀ g : G, g * q * g⁻¹ ≠ b) →
              ∀ V : Subgroup G, IsSylowOf 2 V (centralizer ({x, b} : Set G)) → B ≤ V →
                ∀ u ∈ V, ∀ v ∈ V, ⁅u, v⁆ ∈ CxK x K

theorem b_prop64_rank4_ne5_of_lemma66
    (h102 : B_ivk_10_2) (h14 : B_prop14) (h103 : B_ivk_10_3) (hL34 : B_gen4_noL34_elem)
    (hA7C2 : B_A7_notC2) (hR : B_a7_rigid_step) (hT1 : B_thm1_A7_any) (h66 : B_prop64_lemma66) :
    B_prop64_rank4_ne5 := by
  classical
  intro G _ _ hG x y K T S hs _ B hB b J hobs hA
  by_contra hKA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL2 : HasL2Model (kBar K) Odd := hs.hasL2Model_odd h102 hL34 hG hKA
  have hcen : CenterlessBar K := centerlessBar_of_hasL2Model (fun q hq => hq) hL2
  have hE : IsE 4 ⊤ B := isE_of_isSn le_top hB le_rfl
  have hBel := hE.2.1
  have hN2 := cor62b_of h102 h14 h103 hL34 hA7C2 hR hT1 hG hs.v2ss.isV2StarTriple hKA hBel hobs hA
  have hP : RankTwoShape (T ⊓ K) :=
    rankTwoShape_sylow_L2 hs.sylow_P (TwoThin.isQuasisimple_hat hs.comp) (fun q hq => hq) hL2
  have hP2 : 2 ≤ pRank 2 ↥(T ⊓ K) := by
    have := pRank_eq_two_of_rankTwoShape hP
    omega
  have hKn := hs.K_normal (by rw [hG.pRank_eq_four]) hcen hP2
  have hBR : B ≤ (T ⊓ K) ⊔ (T ⊓ CxK x K) := hB.1.1
  have hBT : B ≤ T := hBR.trans (sup_le inf_le_left inf_le_left)
  have hBx : B ≤ centralizer ({x} : Set G) := hBT.trans hs.T_le_C
  have hJK : J ≠ K := fun h' => hKA (h' ▸ hA)
  have hxb : x ≠ b := (hobs.ne_x_of_shape hG hs hcen hP hB hJK).symm
  have hxo := hs.orderOf_x
  have hterm : IsTwoTerminal x K := hs.v2ss.isV2Triple.2.1
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  have hb2 : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hBsq b hobs.mem) hobs.ne_one
  have h65b : ∀ q ∈ CxK x K, orderOf q = 2 → ∀ g : G, g * q * g⁻¹ ≠ b :=
    not_conj_invol_CxK hG hxo hs.comp hterm hL2 hobs.comp hA hN2
  have hbC : b ∉ CxK x K := fun hbC => h65b b hbC hb2 1 (by simp)
  have hPQ := hs.commDisj hcen
  obtain ⟨U, hU, E₁, hE₁S, hE₁2, hBdef⟩ := (isS_sup_iff hPQ hP B).1 hB
  have hEqQ : E₁ ≤ T ⊓ CxK x K := hE₁S.1
  obtain ⟨u, hu, q, hq, hbuq⟩ := exists_mul_of_mem_sup_of_commute
    (fun u hu q hq => hPQ.comm u (hU.1 hu) q (hEqQ hq)) (hBdef ▸ hobs.mem : b ∈ U ⊔ E₁)
  have hbdec : ∃ a ∈ K, ∃ e ∈ CxK x K, a ∈ B ∧ e ∈ B ∧ a * e = b :=
    ⟨u, (hU.1 hu).2, q, (hEqQ hq).2, hBdef ▸ Subgroup.mem_sup_left hu,
      hBdef ▸ Subgroup.mem_sup_right hq, hbuq.symm⟩
  exact prop64_false_of_lemma66 hG hxo hs.K_le_C hKn hcen hL2 hBel hobs hA hN2 hBx hxb hbC hbdec
    (fun V hV hBV u hu' v hv => h66 G hG x y K T S hs hL2 B hB b J hobs hA hN2 h65b V hV hBV u hu' v hv)

end CFSG.GH74.GLS

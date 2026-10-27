module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5DE
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem5DD

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615C

theorem borelL_le_normalizer_oTwoUpper_ch615_F4 (h432 : Stmt4_3_2_F4) (c : Cx615C G T M L V H n)
    (hCM : cXU615 T L H ≤ M)
    (hN : borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G)) :
    borelL T L ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
  have h := c.hyp
  set K := oTwoUpper H with hKdef
  set C := cXU615 T L H with hCdef
  set Q := pCoreOf 2 (L ⊔ T) with hQdef
  set R := (T ⊓ L) ⊔ Q with hRdef
  set S := baum R with hSdef
  have hTH : T ≤ H := c.hH.1.1
  have hQT : Q ≤ T := F7.isSylowTwoOf_pCoreOf_le (h.toHyp5_0_1.isSylowTwoOf le_sup_right)
  have hRT : R ≤ T := sup_le inf_le_left hQT
  have hST : S ≤ T := inf_le_left.trans hRT
  have hS2 : IsPGroup 2 S := h.sylow.1.to_le hST
  have hJR : thompsonJ T ≤ R := c.thompsonJ_le_ch615
  have hJS : thompsonJ T ≤ S := by
    rw [← B6.thompsonJ_eq_of_le hJR hRT]
    exact thompsonJ_le_baum_ch615 R
  have hKH : K ≤ H := oTwoUpper_le H
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_oTwoUpper H
  have hSK : S ≤ Subgroup.normalizer (K : Set G) := (hST.trans hTH).trans hHK
  have hCS : C ≤ Subgroup.normalizer (S : Set G) := c.le_normalizer_baum_ch615_F4 h432 hCM
  have hKC : K ≤ Subgroup.normalizer (C : Set G) :=
    (hKH.trans le_sup_right).trans le_normalizer_cXU615

  have hcl : conjClosure S (K ⊔ C) = K ⊔ S := by
    apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨g, hg, s, hs, rfl⟩
      have hg' : g ∈ ((K ⊔ C : Subgroup G) : Set G) := hg
      rw [Subgroup.coe_mul_of_left_le_normalizer_right K C hKC] at hg'
      obtain ⟨k, hk, x, hx, rfl⟩ := hg'
      have hxs : x * s * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp (hCS hx) s).mp hs
      have e1 : k * x * s * (k * x)⁻¹ = k * (x * s * x⁻¹) * k⁻¹ := by group
      rw [e1]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hk)
        (Subgroup.mem_sup_right hxs)) (Subgroup.mem_sup_left (K.inv_mem hk))
    · refine sup_le ?_ (le_conjClosure S (K ⊔ C))
      calc K = ⁅K, thompsonJ T⁆ := c.JK.symm
        _ ≤ ⁅K, S⁆ := Subgroup.commutator_mono le_rfl hJS
        _ ≤ conjClosure S (K ⊔ C) := by
          rw [Subgroup.commutator_le]
          intro k hk s hs
          rw [commutatorElement_def]
          exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨k, Subgroup.mem_sup_left hk, s, hs,
            rfl⟩) (le_conjClosure S (K ⊔ C) (S.inv_mem hs))

  have hO : oTwoUpper (K ⊔ S) = K := by
    apply le_antisymm
    · exact (Subgroup.closure_le _).mpr fun x hx =>
        mem_of_odd_of_mem_sup_ch615 hS2 hSK hx.1 hx.2
    · exact (Subgroup.closure_le _).mpr fun x hx =>
        mem_oTwoUpper_of_odd (Subgroup.mem_sup_left (Subgroup.subset_closure hx)) hx.2
  intro b hb
  have hbS : b ∈ Subgroup.normalizer (S : Set G) := borelL_le_normalizer_baumQ_ch615 hb
  have h1 := mem_normalizer_conjClosure_ch615 hbS (hN hb)
  rw [hcl] at h1
  rw [← hO]
  exact normalizer_le_normalizer_oTwoUpper _ h1

end Cx615C

end CFSG.Quasithin.H13

module

public import CFSG.GH74.GLS.C3.Layer1.BkP85SpGlue
public import CFSG.GH74.GLS.C3.Layer1.BkP85SpFus
public import CFSG.GH74.Generic.S45.LEvSporOuter
public import CFSG.GH74.GLS.C3.Layer1.BkP85SpLift
public import CFSG.GH74.GLS.C3.Layer1.BkP85SpSeven

public section

namespace CFSG.GH74.GLS.Th2.P85.Sp

open Subgroup CFSG CFSG.ABGLocalTools Blueprint CFSG.GH74.GLS CFSG.GH74.GLS.Th2
  CFSG.GH74.GLS.Th2.P85 CFSG.GH74.GLS.Th2.P85.Alt CFSG.GH74.GLS.TwoThin

theorem card_centralizer_conj' {G : Type} [Group G] (x g : G) :
    Nat.card ↥(centralizer ({g * x * g⁻¹} : Set G)) = Nat.card ↥(centralizer ({x} : Set G)) := by
  have h := Stage1.Thm2.Recip.map_centralizer_singleton_conj x g
  rw [← h, Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem p85_index_two_false
    {G : Type} [Group G] [Finite G]
    {M K Q : Subgroup G} {J : Subgroup (Mb M)} {x : G}
    (hG : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a)
    (hxM : x ∈ M) (hx2 : orderOf x = 2)
    (hQel : CFSG.IsElementaryAbelian 2 ↥Q)
    (hCx : centralizer ({x} : Set G) ≤ M)
    (hgam : gammaK 2 Q 1 ≤ M)
    (cfg : SporAutCfg (⊤ : Subgroup (Mb M)) J (imgM M K) (imgM M Q)
      (barMk ↥M ⟨x, hxM⟩)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx2M : orderOf (⟨x, hxM⟩ : ↥M) = 2 := (Subgroup.orderOf_mk x hxM).trans hx2
  have hxb2 : orderOf (barMk ↥M ⟨x, hxM⟩) = 2 := orderOf_barMk hx2M
  obtain ⟨u₀, -, hu₀L, hu₀2, hu₀x⟩ :=
    CFSG.GH74.GLS.b_spor_outer_invol_proved (Mb M) ⊤ J (imgM M K)
      (imgM M Q) (barMk ↥M ⟨x, hxM⟩) cfg
  obtain ⟨u, hu2, hux, hub⟩ := exists_involution_lift hx2M hu₀2 hu₀x
  have huL : (u : G) ∉ preimgM M J := by
    intro h
    obtain ⟨hum, hh⟩ := mem_preimgM_iff.1 h
    exact hu₀L (hub ▸ hh)
  have hidx : (preimgM M J).relIndex M = 2 :=
    relIndex_preimgM_eq_two M (by simpa [Subgroup.card_top] using cfg.index_two)
  have hnorm := preimgM_normal (M := M) (Lb := J)
    (fun n h hh => cfg.socle.normal n (Subgroup.mem_top n) h hh)
  obtain ⟨g, hgM, hgn⟩ := EvenSporTransfer.exists_not_fused_of_index_two
    (no_normal_index_two hG hnab) hnorm hidx hxM hx2 u.2 huL
    ((Subgroup.orderOf_coe u).trans hu2) (congrArg Subtype.val hux) hCx
  set w : G := g⁻¹ * x * g with hwdef
  have hw2 : orderOf w = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) x
    simpa [MulAut.conj_apply, hwdef] using this.trans hx2
  have hw2M : orderOf (⟨w, hgM⟩ : ↥M) = 2 := (Subgroup.orderOf_mk w hgM).trans hw2
  have hwb2 : orderOf (barMk ↥M ⟨w, hgM⟩) = 2 := orderOf_barMk hw2M
  have hg : g * w * g⁻¹ = x := by rw [hwdef]; group
  have hcardw : Nat.card ↥(centralizer ({w} : Set G)) = Nat.card ↥(centralizer ({x} : Set G)) :=
    card_centralizer_conj x g
  have hdom := two_adic_dom hxM hgM hx2 hw2 hCx hcardw
  have hynot : ∀ n ∈ (⊤ : Subgroup (Mb M)),
      n * barMk ↥M ⟨x, hxM⟩ * n⁻¹ ≠ barMk ↥M ⟨w, hgM⟩ := by
    intro n _ h
    have hconj : IsConj (barMk ↥M ⟨w, hgM⟩) (barMk ↥M ⟨x, hxM⟩) :=
      isConj_iff.2 ⟨n⁻¹, by rw [← h]; group⟩
    obtain ⟨m, hm⟩ := exists_conj_of_barMk_conj hw2M hx2M hconj
    exact hgn _ (M.inv_mem m.2) (by rw [inv_inv]; exact (congrArg Subtype.val hm).symm)
  rcases CFSG.GH74.GLS.Th2.P85.Sp.spor_fusion_dom cfg (Subgroup.mem_top _) hwb2 hynot hdom with
    ⟨-, h240, h480, n, -, hnQ⟩ | ⟨-, h672, h480, h7⟩
  ·
    obtain ⟨q, hqQ, hqb⟩ := mem_imgM_iff.1 hnQ
    have hqb2 : orderOf (barMk ↥M q) = 2 := by
      rw [hqb]
      have := MulEquiv.orderOf_eq (MulAut.conj n) (barMk ↥M ⟨w, hgM⟩)
      simpa [MulAut.conj_apply] using this.trans hwb2
    have hq1 : q ≠ 1 := by
      intro h
      rw [h, map_one, orderOf_one] at hqb2
      omega
    have hqsq : q ^ 2 = 1 := by
      have := (C3.Layer1.Back.forall_of_isElementaryAbelian hQel).2 (q : G) hqQ
      exact Subtype.ext (by simpa [pow_two] using this)
    have hq2M : orderOf q = 2 := orderOf_eq_prime hqsq hq1
    have hq2G : orderOf (q : G) = 2 := (Subgroup.orderOf_coe q).trans hq2M
    have hconj : IsConj (barMk ↥M q) (barMk ↥M ⟨w, hgM⟩) :=
      isConj_iff.2 ⟨n⁻¹, by rw [hqb]; group⟩
    obtain ⟨m, hm⟩ := exists_conj_of_barMk_conj hq2M hw2M hconj
    have hCq : centralizer ({(q : G)} : Set G) ≤ M :=
      (C3.Layer1.U1a.centralizer_le_gammaK (Q := Q) hqQ hq2G).trans hgam
    have hqeq : (q : G) = (m : G) * w * (m : G)⁻¹ := (congrArg Subtype.val hm).symm
    have hcq1 : Nat.card ↥(centralizer ({(q : G)} : Set G)) =
        Nat.card ↥(centralizer ({x} : Set G)) := by
      rw [hqeq, card_centralizer_conj', hcardw]
    have hcq2 := card_centralizer_of_le q.2 hCq
    obtain ⟨rq, hrq, hcq⟩ := card_centralizer_barMk (M := M) hq2M
    obtain ⟨rx, hrx, hcx⟩ := card_centralizer_barMk (M := M) hx2M
    have hcqb : Nat.card ↥(centralizer ({barMk ↥M q} : Set (Mb M))) = 240 := by
      have := CFSG.GH74.Generic.S45.card_cent_conj (N := (⊤ : Subgroup (Mb M)))
        (Subgroup.mem_top n) (barMk ↥M ⟨w, hgM⟩)
      rw [← hqb, inf_top_eq, inf_top_eq] at this
      rw [this]
      rw [inf_top_eq] at h240
      exact h240
    have hcxb : Nat.card ↥(centralizer ({barMk ↥M ⟨x, hxM⟩} : Set (Mb M))) = 480 := by
      rw [inf_top_eq] at h480
      exact h480
    have hcx2 := card_centralizer_of_le hxM hCx
    have hall : rq * 240 = rx * 480 := by
      calc rq * 240 = Nat.card ↥(centralizer ({q} : Set ↥M)) := by rw [hcq, hcqb]
        _ = Nat.card ↥(centralizer ({(q : G)} : Set G)) := hcq2.symm
        _ = Nat.card ↥(centralizer ({x} : Set G)) := hcq1
        _ = Nat.card ↥(centralizer ({(⟨x, hxM⟩ : ↥M)} : Set ↥M)) := hcx2
        _ = rx * 480 := by rw [hcx, hcxb]
    have h5 : 2 ^ 5 ∣ rq * 240 := by
      rw [hall]
      exact ⟨rx * 15, by ring⟩
    have hcop : Nat.Coprime (2 ^ 5) rq := Nat.Coprime.pow_left 5 (Nat.coprime_two_left.2 hrq)
    have := hcop.dvd_of_dvd_mul_left h5
    norm_num at this
  ·
    have hY : Nat.card ↥(centralizer ({barMk ↥M ⟨x, hxM⟩} : Set (Mb M))) = 480 := by
      rw [inf_top_eq] at h480
      exact h480
    have h672' : Nat.card ↥(centralizer ({barMk ↥M ⟨w, hgM⟩} : Set (Mb M))) = 672 := by
      rw [inf_top_eq] at h672
      exact h672
    have hZ7 : 7 ∣ Nat.card ↥(centralizer ({barMk ↥M ⟨w, hgM⟩} : Set (Mb M))) := by
      rw [h672']
      norm_num
    obtain ⟨R, hRle, hRnorm, hRodd, hR7⟩ := exists_odd_normal_seven hxM hgM hw2 hCx hg hY hZ7
    refine false_of_seven (X := Mb M) (N := ⊤) (H := J) le_top
      (by simpa [Subgroup.card_top] using cfg.index_two) h672 h7
      (fun r hr => ⟨hRle hr, Subgroup.mem_top r⟩) (fun z hz r hr => hRnorm z hz.1 r hr) hRodd hR7

end CFSG.GH74.GLS.Th2.P85.Sp

module

public import CFSG.GH74.GLS.LU.Local.FiveStdRepX1b

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU.Local

open scoped Pointwise

namespace CFSG.GH74.GLS.LU.Local.Five

open CFSG.GH74.GLS.LU.Local.FiveStd CFSG.GH74.GLS.LU.Local.Five.FiveStdRep

namespace FiveStdX1

variable {G : Type} [Group G] [Finite G] {st : FiveStdSetting G} {tE uE a b g : E} {H' : Subgroup G}
  (c : GoodCtx st tE uE a b g H')

namespace GoodCtx

include c

theorem clause_normXB :
    normalizer ((XB (st.ι tE) (zpowers (st.ι g)) : Subgroup G) : Set G) ⊓ Cz st.z =
      XB (st.ι tE) (zpowers (st.ι g)) ⊔ st.K₁ ⊔ H' := by
  rw [c.XB_eq]
  obtain ⟨-, hV1, -⟩ := baseCheck_spec c.base
  have h5 := (goodX1_spec c.hgood).2.2.2.2.1
  have hS2 := c.g2_coe
  have hV2 : V (powers (conjE tE g) 5) := st.model.V_powers c.g2v 5
  have hVH : V (ppE a b 4 4) := st.model.V_ppE c.ha c.hb 4 4
  have hV21 : V (mulLL (powers (conjE tE g) 5) K1l) := st.model.V_mulLL hV2 hV1
  have hVprod : V (prod3 (powers (conjE tE g) 5) K1l (ppE a b 4 4)) := st.model.V_mulLL hV21 hVH
  have hVfil : V (Cs.filter fun c' => normG c' [conjE tE g] (powers (conjE tE g) 5)) := V_filter _ FiveStdSetting.V_Cs
  have hEq := (st.model.eqL_iff hVfil hVprod).1 h5
  have hfil : S st.ι (Cs.filter fun c' => normG c' [conjE tE g] (powers (conjE tE g) 5)) =
      ((normalizer ((zpowers (st.ι (conjE tE g)) : Subgroup G) : Set G) ⊓ Cz st.z : Subgroup G) : Set G) := by
    apply FiveStdX1.coe_filter_Cs st
    intro x hx
    exact normG_iff_normalizer st.model ((mem_Cs_iff x).1 hx) (V_cons c.g2v V_nil) hV2 hS2 (by simp)
      (Subgroup.zpowers_le.2 (zpowers_le_closure_list [conjE tE g] (by simp)))
  rw [hfil] at hEq
  apply sup3_of_coe_eq
  rw [hEq, prod3, st.model.S_mulLL hV21 hVH, st.model.S_mulLL hV2 hV1, ← hS2, ← st.hK₁, ← c.hH']

theorem clause_cenXB :
    centralizer ((XB (st.ι tE) (zpowers (st.ι g)) : Subgroup G) : Set G) ⊓ Cz st.z =
      XB (st.ι tE) (zpowers (st.ι g)) ⊔ st.K₁ := by
  rw [c.XB_eq]
  obtain ⟨-, hV1, -⟩ := baseCheck_spec c.base
  have h6 := (goodX1_spec c.hgood).2.2.2.2.2.1
  have hS2 := c.g2_coe
  have hV2 : V (powers (conjE tE g) 5) := st.model.V_powers c.g2v 5
  have hVprod : V (prod2 (powers (conjE tE g) 5) K1l) := st.model.V_mulLL hV2 hV1
  have hVfil : V (Cs.filter fun c' => cenG c' [conjE tE g]) := V_filter _ FiveStdSetting.V_Cs
  have hEq := (st.model.eqL_iff hVfil hVprod).1 h6
  have hfil : S st.ι (Cs.filter fun c' => cenG c' [conjE tE g]) =
      ((centralizer ((zpowers (st.ι (conjE tE g)) : Subgroup G) : Set G) ⊓ Cz st.z : Subgroup G) : Set G) := by
    apply FiveStdX1.coe_filter_Cs st
    intro x hx
    exact cenG_iff_centralizer st.model ((mem_Cs_iff x).1 hx) (V_cons c.g2v V_nil) (by simp)
      (Subgroup.zpowers_le.2 (zpowers_le_closure_list [conjE tE g] (by simp)))
  rw [hfil] at hEq
  apply sup2_of_coe_eq
  rw [hEq, prod2, st.model.S_mulLL hV2 hV1, ← hS2, ← st.hK₁]

theorem clause_normXX :
    normalizer ((XX (st.ι tE) (zpowers (st.ι g)) : Subgroup G) : Set G) ⊓ Cz st.z =
      XX (st.ι tE) (zpowers (st.ι g)) ⊔ H' ⊔ zpowers (st.ι tE) := by
  rw [c.XX_eq]
  obtain ⟨-, hV1, -⟩ := baseCheck_spec c.base
  have h7 := (goodX1_spec c.hgood).2.2.2.2.2.2.1
  have hXc := c.XX_coe
  have hVXX : V (ppE g (conjE tE g) 5 5) := st.model.V_ppE c.gv c.g2v 5 5
  have hVH : V (ppE a b 4 4) := st.model.V_ppE c.ha c.hb 4 4
  have hV4 : V [oneE, tE] := V_cons st.model.valid_one (V_cons c.ht V_nil)
  have hVXH : V (mulLL (ppE g (conjE tE g) 5 5) (ppE a b 4 4)) := st.model.V_mulLL hVXX hVH
  have hVprod : V (prod3 (ppE g (conjE tE g) 5 5) (ppE a b 4 4) [oneE, tE]) := st.model.V_mulLL hVXH hV4
  have hVfil : V (Cs.filter fun c' => normG c' [g, conjE tE g] (ppE g (conjE tE g) 5 5)) := V_filter _ FiveStdSetting.V_Cs
  have hEq := (st.model.eqL_iff hVfil hVprod).1 h7
  have hgens : ∀ x ∈ [g, conjE tE g], st.ι x ∈ zpowers (st.ι g) ⊔ zpowers (st.ι (conjE tE g)) := by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · rw [List.mem_singleton.1 hx]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hK : zpowers (st.ι g) ⊔ zpowers (st.ι (conjE tE g)) ≤ closure (st.ι '' {x | x ∈ [g, conjE tE g]}) :=
    sup_le (Subgroup.zpowers_le.2 (zpowers_le_closure_list [g, conjE tE g] (by simp)))
      (Subgroup.zpowers_le.2 (zpowers_le_closure_list [g, conjE tE g] (by simp)))
  have hfil : S st.ι (Cs.filter fun c' => normG c' [g, conjE tE g] (ppE g (conjE tE g) 5 5)) =
      ((normalizer ((zpowers (st.ι g) ⊔ zpowers (st.ι (conjE tE g)) : Subgroup G) : Set G) ⊓ Cz st.z :
        Subgroup G) : Set G) := by
    apply FiveStdX1.coe_filter_Cs st
    intro x hx
    exact normG_iff_normalizer st.model ((mem_Cs_iff x).1 hx) (V_cons c.gv (V_cons c.g2v V_nil)) hVXX hXc hgens hK
  rw [hfil] at hEq
  have hEq' : ((normalizer ((zpowers (st.ι g) ⊔ zpowers (st.ι (conjE tE g)) : Subgroup G) : Set G) ⊓ Cz st.z :
      Subgroup G) : Set G) =
      ((zpowers (st.ι g) ⊔ zpowers (st.ι (conjE tE g)) : Subgroup G) : Set G) * (H' : Set G) *
        S st.ι [oneE, tE] := by
    rw [hEq, prod3, st.model.S_mulLL hVXH hV4, st.model.S_mulLL hVXX hVH, ← hXc, ← c.hH']
  have htD : st.ι tE ∈ S st.ι [oneE, tE] := mem_S.2 ⟨tE, by simp, rfl⟩
  have htN : zpowers (st.ι tE) ≤
      normalizer ((zpowers (st.ι g) ⊔ zpowers (st.ι (conjE tE g)) : Subgroup G) : Set G) ⊓ Cz st.z := by
    rw [Subgroup.zpowers_le]
    have : st.ι tE ∈ ((normalizer ((zpowers (st.ι g) ⊔ zpowers (st.ι (conjE tE g)) : Subgroup G) : Set G) ⊓
        Cz st.z : Subgroup G) : Set G) := by
      rw [hEq']
      have := Set.mul_mem_mul (Set.mul_mem_mul (Subgroup.one_mem (zpowers (st.ι g) ⊔ zpowers (st.ι (conjE tE g))))
        H'.one_mem) htD
      simpa using this
    exact this
  refine sup3_of_coe_eq_D hEq' ?_ ?_ htN
  · exact mem_S.2 ⟨oneE, by simp, st.model.map_one⟩
  · intro y hy
    obtain ⟨e, he, rfl⟩ := mem_S.1 hy
    rcases List.mem_cons.1 he with rfl | he
    · rw [st.model.map_one]
      exact Subgroup.one_mem _
    · rw [List.mem_singleton.1 he]
      exact Subgroup.mem_zpowers _

theorem clause_inv_sub :
    ∀ A : Subgroup G, A ≤ XX (st.ι tE) (zpowers (st.ι g)) → Nat.card ↥A = 5 → (∀ h ∈ H', cjL h A = A) →
      A = zpowers (st.ι g) ∨ A = XB (st.ι tE) (zpowers (st.ι g)) := by
  intro A hAXX hA5 hAinv
  rw [c.XX_eq] at hAXX
  rw [c.XB_eq]
  have h8 := (goodX1_spec c.hgood).2.2.2.2.2.2.2.1
  have hVXX : V (ppE g (conjE tE g) 5 5) := st.model.V_ppE c.gv c.g2v 5 5
  have hnt : Nontrivial ↥A := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨⟨a0, ha0A⟩, ha0ne⟩ := exists_ne (1 : ↥A)
  have ha0ne' : a0 ≠ 1 := fun h => ha0ne (Subtype.ext h)
  have ha0S : a0 ∈ S st.ι (ppE g (conjE tE g) 5 5) := by
    rw [← c.XX_coe]
    exact hAXX ha0A
  obtain ⟨h, hhX, rfl⟩ := mem_S.1 ha0S
  have hhv : validE h = true := hVXX h hhX
  have hhne : h ≠ oneE := fun e => ha0ne' (by rw [e, st.model.map_one])
  have hord : orderOf (st.ι h) = 5 := by
    have hdvd : orderOf (st.ι h) ∣ 5 := hA5 ▸ Subgroup.orderOf_dvd_natCard A ha0A
    rcases (Nat.dvd_prime (by norm_num)).1 hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.1 h1) ha0ne'
    · exact h1
  have h5 : st.ι h ^ 5 = 1 := by
    have := pow_orderOf_eq_one (st.ι h)
    rwa [hord] at this
  have hAeq : zpowers (st.ι h) = A :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 ha0A) (by rw [hA5, Nat.card_zpowers, hord])
  have hZS : S st.ι (powers h 5) = (A : Set G) := by
    rw [← coe_zpowers_eq_S st.model hhv h5, hAeq]
  rcases h8 h hhX with h1 | h1 | h1 | h1
  · exact absurd h1 hhne
  · exfalso
    have hn : normAll [a, b] [h] (powers h 5) = true := by
      rw [st.model.normAll_iff (V_cons c.ha (V_cons c.hb V_nil)) (V_cons hhv V_nil) (st.model.V_powers hhv 5)]
      intro h' hh' x hx
      have hh'H : st.ι h' ∈ H' := by
        rcases List.mem_cons.1 hh' with rfl | hh'
        · exact c.aH
        · rw [List.mem_singleton.1 hh']
          exact c.bH
      rw [List.mem_singleton.1 hx, hZS, SetLike.mem_coe]
      have h2 := repCj_mem_self (g := st.ι h') ha0A
      rwa [hAinv _ hh'H] at h2
    rw [hn] at h1
    exact absurd h1 (by simp)
  · left
    have := (st.model.eqL_iff (st.model.V_powers hhv 5) (st.model.V_powers c.gv 5)).1 h1
    rw [hZS, ← c.g_coe] at this
    exact SetLike.coe_injective this
  · right
    have := (st.model.eqL_iff (st.model.V_powers hhv 5) (st.model.V_powers c.g2v 5)).1 h1
    rw [hZS, ← c.g2_coe] at this
    exact SetLike.coe_injective this

omit [Finite G] in
theorem clause_card : Nat.card ↥(XZ (st.ι tE) (zpowers (st.ι g))) = 5 := by
  have h9 := (goodX1_spec c.hgood).2.2.2.2.2.2.2.2
  have hnd := (goodX1_spec c.hgood).2.2.2.1
  have hVXX : V (ppE g (conjE tE g) 5 5) := st.model.V_ppE c.gv c.g2v 5 5
  show Nat.card ↥(XX (st.ι tE) (zpowers (st.ι g)) ⊓ centralizer ({st.ι tE} : Set G)) = 5
  rw [c.XX_eq]
  have hfil : S st.ι ((ppE g (conjE tE g) 5 5).filter fun x => commE x tE) =
      (((zpowers (st.ι g) ⊔ zpowers (st.ι (conjE tE g))) ⊓ centralizer ({st.ι tE} : Set G) : Subgroup G) :
        Set G) := by
    rw [S_filter (Q := fun y => y ∈ centralizer ({st.ι tE} : Set G))
      (fun x hx => by rw [st.model.commE_iff (hVXX x hx) c.ht, Subgroup.mem_centralizer_singleton_iff])]
    ext y
    rw [Set.mem_ofPred_eq, SetLike.mem_coe, Subgroup.mem_inf, ← c.XX_coe, SetLike.mem_coe]
  rw [FiveStdBase.natCard_eq_of_coe _ hfil.symm, FiveStdBase.natCard_S st.model (V_filter _ hVXX) (hnd.filter _), h9]

end GoodCtx

end FiveStdX1

end CFSG.GH74.GLS.LU.Local.Five

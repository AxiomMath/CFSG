module

public import CFSG.GH74.GLS.C3.Prop121.Card7Abs2
public import CFSG.GH74.GLS.C3.Layer2.FinModel
public import CFSG.GH74.GLS.C3.Layer3.Basic
public import CFSG.GH74.GLS.C3.Prop121.Interfaces
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

universe u

theorem card_option_eq {α : Type u} [Finite α] : Nat.card (Option α) = Nat.card α + 1 := by
  have : Nat.card PUnit.{u + 1} = 1 := Nat.card_unique
  rw [Nat.card_congr (Equiv.optionEquivSumPUnit α), Nat.card_sum, this]

theorem nm7_conj (k f : F7) : nm7 ((k * f * k⁻¹ : F7) : Amb 7) = nm7 (f : Amb 7) := by
  unfold nm7
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv,
    Prod.snd_inv]
  rw [numMoved_conj, numMoved_conj]

theorem ccard_self_eq {M : Type*} [Group M] (f : M) :
    ccard M f f = Nat.card ↥(centralizer ({f} : Set M)) := by
  unfold ccard
  refine Nat.card_congr (Equiv.subtypeEquivRight (fun c => ?_))
  rw [mem_centralizer_singleton_iff]
  tauto

section Abstract

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem lab_ge (hF : FFacts) (x : G) (hx : orderOf x = 2)
    (ι : ↥(centralizer ({x} : Set G)) ≃* F7) (pf : PatternFacts G 7)
    (z : ↥(centralizer ({x} : Set G))) (hz2 : orderOf (z : G) = 2) (hzx : IsConj x (z : G))
    (hz1 : ((ι z : F7) : Amb 7).2 = 1)
    (c : ↥(centralizer ({x} : Set G))) (hc2 : orderOf c = 2) (h4 : nm7 ((ι c : F7) : Amb 7) = 4) :
    IsConj (c : G) x := by
  have hcG : orderOf (c : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hc2
  have hinv : IsInv (ι c) := by
    rw [isInv_iff_orderOf, MulEquiv.orderOf_eq]; exact hc2
  have hcardx : Nat.card ↥(centralizer ({x} : Set G)) = 4 * Nat.factorial 7 := by
    rw [Nat.card_congr ι.toEquiv, card_Fgrp]
  rcases hF.nm4_forced (ι c) hinv h4 with h21 | hnd
  ·
    have hinvz : IsInv (ι z) := by
      rw [isInv_iff_orderOf, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]; exact hz2
    obtain ⟨k, hk⟩ := hF.conj_inv40 (ι c) (ι z) hinv hinvz h21 hz1
    have hk' : ι.symm k * c * (ι.symm k)⁻¹ = z := by
      apply ι.injective
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact hk
    have hcz : IsConj (c : G) (z : G) := by
      rw [isConj_iff]
      exact ⟨(ι.symm k : G), by
        have := congrArg Subtype.val hk'
        simpa using this⟩
    exact hcz.trans hzx.symm
  ·
    have hdvd : Nat.card (centralizer ({ι c} : Set F7)) ∣ Nat.card ↥(centralizer ({(c : G)} : Set G)) := by
      rw [← ccard_self_eq, ← cc3_eq_ccard (a := x) (u := (c : G)) (v := (c : G)) ι c.2 c.2,
        ← Ctx.card_inf_centralizer]
      exact Subgroup.card_dvd_of_le inf_le_right
    have h20160 : Nat.card ↥(centralizer ({(c : G)} : Set G)) = 4 * Nat.factorial 7 := by
      rcases pf.1 (c : G) hcG with h | h
      · exact h
      · exfalso
        rw [h] at hdvd
        exact hnd (by simpa [Nat.factorial] using hdvd)
    exact pf.2 (c : G) x hcG hx h20160 hcardx

theorem lab_abstract (hF : FFacts) (x : G) (hx : orderOf x = 2)
    (ι : ↥(centralizer ({x} : Set G)) ≃* F7) (pf : PatternFacts G 7)
    (z : ↥(centralizer ({x} : Set G))) (hz2 : orderOf (z : G) = 2) (hzx : IsConj x (z : G))
    (hz1 : ((ι z : F7) : Amb 7).2 = 1)
    (S T : Subgroup G) (hTS : T ≤ S) (QT : Sylow 2 ↥(centralizer ({x} : Set G)))
    (hQT : (QT : Subgroup ↥(centralizer ({x} : Set G))).map
      (centralizer ({x} : Set G)).subtype = T)
    (hcount : Nat.card {u : ↥S // orderOf (u : G) = 2 ∧ IsConj x (u : G)} = 14) :
    ∀ c : ↥(centralizer ({x} : Set G)), orderOf c = 2 →
      (IsConj (c : G) x ↔ nm7 ((ι c : F7) : Amb 7) = 4) := by
  intro c hc2
  refine ⟨fun hcx => ?_, lab_ge hF x hx ι pf z hz2 hzx hz1 c hc2⟩
  by_contra h4
  have hinv : IsInv (ι c) := by rw [isInv_iff_orderOf, MulEquiv.orderOf_eq]; exact hc2
  have h8 : nm7 ((ι c : F7) : Amb 7) = 8 := by
    rcases hF.inv_nm _ hinv with h | h
    · exact absurd h h4
    · exact h
  obtain ⟨d, hd⟩ := CFSG.GH74.GLS.Layer3.exists_conj_mem_sylow_two QT hc2
  set c' : ↥(centralizer ({x} : Set G)) := d * c * d⁻¹ with hc'
  have hc'2 : orderOf c' = 2 := by
    rw [hc', show d * c * d⁻¹ = MulAut.conj d c from rfl, MulEquiv.orderOf_eq]; exact hc2
  have hc'G : orderOf (c' : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hc'2
  have hc'x : IsConj (c' : G) x := by
    have : IsConj (c : G) (c' : G) := isConj_iff.2 ⟨(d : G), by simp [hc']⟩
    exact this.symm.trans hcx
  have hnm' : nm7 ((ι c' : F7) : Amb 7) = 8 := by
    rw [hc', map_mul, map_mul, map_inv, nm7_conj]; exact h8
  have hmemT : ∀ q : ↥(centralizer ({x} : Set G)), q ∈ QT → (q : G) ∈ S := fun q hq =>
    hTS (hQT ▸ ⟨q, hq, rfl⟩)
  set P : Subgroup F7 := (QT : Subgroup ↥(centralizer ({x} : Set G))).map ι.toMonoidHom with hP
  have hQTcard : Nat.card QT = 64 := by
    have h1 := Sylow.card_eq_multiplicity QT
    have h2 : Nat.card ↥(centralizer ({x} : Set G)) = 20160 := by
      rw [Nat.card_congr ι.toEquiv, card_Fgrp]; norm_num [Nat.factorial]
    rw [h2] at h1
    have h3 : (20160 : ℕ).factorization 2 = 6 := by decide +kernel
    rw [h3] at h1
    exact h1.trans (by norm_num)
  have hPcard : Nat.card P = 64 := by
    rw [hP, Subgroup.card_map_of_injective ι.injective]; exact hQTcard
  have h14 := hF.sylow_count P hPcard
  have hPmem : ∀ f : P, ι.symm (f : F7) ∈ QT := by
    rintro ⟨_, q, hq, rfl⟩
    simpa using hq
  have hSome : ∀ f : {f : P // XF (f : F7)},
      ((ι.symm (f.1 : F7) : ↥(centralizer ({x} : Set G))) : G) ∈ S :=
    fun f => hmemT _ (hPmem f.1)
  have hSomeOrd : ∀ f : {f : P // XF (f : F7)},
      orderOf ((ι.symm (f.1 : F7) : ↥(centralizer ({x} : Set G))) : G) = 2 := by
    intro f
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact isInv_iff_orderOf.1 f.2.1
  have hSomeConj : ∀ f : {f : P // XF (f : F7)},
      IsConj x ((ι.symm (f.1 : F7) : ↥(centralizer ({x} : Set G))) : G) := by
    intro f
    have hord : orderOf (ι.symm (f.1 : F7) : ↥(centralizer ({x} : Set G))) = 2 := by
      rw [← Subgroup.orderOf_coe]; exact hSomeOrd f
    have := lab_ge hF x hx ι pf z hz2 hzx hz1 (ι.symm (f.1 : F7)) hord (by
      rw [MulEquiv.apply_symm_apply]; exact f.2.2)
    exact this.symm
  let φ : Option {f : P // XF (f : F7)} → {u : ↥S // orderOf (u : G) = 2 ∧ IsConj x (u : G)} :=
    fun o => match o with
      | none => ⟨⟨(c' : G), hmemT c' hd⟩, hc'G, hc'x.symm⟩
      | some f => ⟨⟨((ι.symm (f.1 : F7) : ↥(centralizer ({x} : Set G))) : G), hSome f⟩,
          hSomeOrd f, hSomeConj f⟩
  have hinj : Function.Injective φ := by
    rintro (_ | f) (_ | f') h
    · rfl
    · exfalso
      have h1 : (c' : G) = ((ι.symm (f'.1 : F7) : ↥(centralizer ({x} : Set G))) : G) :=
        congrArg (fun u => ((u.1 : ↥S) : G)) h
      have h2 : c' = ι.symm (f'.1 : F7) := Subtype.ext h1
      have h3 : ι c' = (f'.1 : F7) := by rw [h2, MulEquiv.apply_symm_apply]
      have := f'.2.2
      rw [← h3] at this
      omega
    · exfalso
      have h1 : ((ι.symm (f.1 : F7) : ↥(centralizer ({x} : Set G))) : G) = (c' : G) :=
        congrArg (fun u => ((u.1 : ↥S) : G)) h
      have h2 : ι.symm (f.1 : F7) = c' := Subtype.ext h1
      have h3 : ι c' = (f.1 : F7) := by rw [← h2, MulEquiv.apply_symm_apply]
      have := f.2.2
      rw [← h3] at this
      omega
    · have h1 : ((ι.symm (f.1 : F7) : ↥(centralizer ({x} : Set G))) : G) =
          ((ι.symm (f'.1 : F7) : ↥(centralizer ({x} : Set G))) : G) :=
        congrArg (fun u => ((u.1 : ↥S) : G)) h
      have h2 : ι.symm (f.1 : F7) = ι.symm (f'.1 : F7) := Subtype.ext h1
      have h3 : (f.1 : F7) = (f'.1 : F7) := ι.symm.injective h2
      rw [Subtype.ext (Subtype.ext h3)]
  have hle := Nat.card_le_card_of_injective φ hinj
  rw [hcount, card_option_eq, h14] at hle
  omega

end Abstract

end CFSG.GH74.GLS.C3.Prop121.Card7

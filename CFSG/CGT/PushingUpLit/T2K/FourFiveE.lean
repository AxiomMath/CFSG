module

public import CFSG.CGT.PushingUpLit.T2K.FourFiveD
public import CFSG.CGT.PushingUpLit.T2K.CoverQuot

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L M T A : Subgroup G} {n : ℕ}

namespace Hyp45

variable (H : Hyp45 L M T A n)
include H

theorem sq_eq_one_of_mem_oTwoIn (hZ : blockZ L = ⊥) {o : G} (ho : o ∈ oTwoIn L) : o ^ 2 = 1 := by
  have hV : o ^ 2 ∈ blockU L := H.block.sq_mem_blockU_of_mem_oTwoIn ho
  have hoC : o ∈ Subgroup.centralizer (blockU L : Set G) := by
    rw [← H.block.inf_centralizer_blockU] at ho
    exact ho.2
  have hC : o ^ 2 ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hw : ⁅o⁻¹, l⁆ ∈ blockU L := Subgroup.commutator_mem_commutator (inv_mem ho) hl
    set w := ⁅o⁻¹, l⁆ with hwdef
    have e : l * o * l⁻¹ = o * w := by
      rw [hwdef]
      simp only [commutatorElement_def]
      group
    have hcom : Commute o w := (Subgroup.mem_centralizer_iff.1 hoC w hw).symm
    have hw2 : w ^ 2 = 1 := H.block.sq_eq_one_of_mem_blockU hw
    have key : l * o ^ 2 * l⁻¹ = o ^ 2 := by
      calc l * o ^ 2 * l⁻¹ = (l * o * l⁻¹) ^ 2 := (conj_pow).symm
        _ = (o * w) ^ 2 := by rw [e]
        _ = o ^ 2 * w ^ 2 := hcom.mul_pow 2
        _ = o ^ 2 := by rw [hw2, mul_one]
    have := key
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have hZ' : o ^ 2 ∈ blockZ L := ⟨hV, hC⟩
  rw [hZ] at hZ'
  exact Subgroup.mem_bot.1 hZ'

theorem oTwoIn_le_bGrp (hZ : blockZ L = ⊥)
    (hS : IsElemAbelian 2 (T ⊓ Subgroup.centralizer (L : Set G))) : oTwoIn L ≤ bGrp L A := by
  intro o ho
  refine mem_of_isMaxElemAbelian H.isMaxElemAbelian_B
    (NatBlock.oTwoIn_le_sylow H.le H.normal H.sylow ho) (H.sq_eq_one_of_mem_oTwoIn hZ ho) ?_
  intro b hb
  rw [H.bGrp_eq_sup_S hS] at hb
  have hcomm : ∀ x ∈ T ⊓ Subgroup.centralizer (L : Set G), ∀ y ∈ blockU L, x * y = y * x :=
    fun x hx y hy => commute_S_V hx.2 hy
  obtain ⟨s, hs, v, hv, rfl⟩ := exists_mul_of_mem_sup' hcomm hb
  have hoC : o ∈ Subgroup.centralizer (blockU L : Set G) := by
    rw [← H.block.inf_centralizer_blockU] at ho
    exact ho.2
  have hos : o * s = s * o := Subgroup.mem_centralizer_iff.1 hs.2 o (oTwoIn_le L ho)
  have hov : v * o = o * v := Subgroup.mem_centralizer_iff.1 hoC v hv
  calc s * v * o = s * (v * o) := mul_assoc _ _ _
    _ = s * (o * v) := by rw [hov]
    _ = (s * o) * v := (mul_assoc _ _ _).symm
    _ = (o * s) * v := by rw [hos]
    _ = o * (s * v) := mul_assoc _ _ _

theorem conj_mem_bGrp (hS : IsElemAbelian 2 (T ⊓ Subgroup.centralizer (L : Set G))) {p b : G}
    (hp : p ∈ T ⊓ Subgroup.centralizer (blockU L : Set G)) (hb : b ∈ bGrp L A) :
    p⁻¹ * b * p ∈ bGrp L A := by
  rw [H.bGrp_eq_sup_S hS] at hb ⊢
  have hcomm : ∀ x ∈ T ⊓ Subgroup.centralizer (L : Set G), ∀ y ∈ blockU L, x * y = y * x :=
    fun x hx y hy => commute_S_V hx.2 hy
  obtain ⟨s, hs, v, hv, rfl⟩ := exists_mul_of_mem_sup' hcomm hb
  have hpv : p⁻¹ * v * p = v := by
    have := Subgroup.mem_centralizer_iff.1 hp.2 v hv
    rw [mul_assoc, this, inv_mul_cancel_left]
  have hps : p⁻¹ * s * p ∈ T ⊓ Subgroup.centralizer (L : Set G) := by
    refine ⟨T.mul_mem (T.mul_mem (T.inv_mem hp.1) hs.1) hp.1, ?_⟩
    have := conj_mem_centralizer_of_normalizer (x := p⁻¹) (H.normal (H.sylow.le (T.inv_mem hp.1)))
      hs.2
    simpa using this
  have e : p⁻¹ * (s * v) * p = (p⁻¹ * s * p) * (p⁻¹ * v * p) := by group
  rw [e, hpv]
  exact Subgroup.mul_mem_sup hps hv

theorem tOf_mul_aux {r r' r'' t t' t'' : G} (hr' : r' ∈ L) (hr : r ∈ L) (hr'' : r'' ∈ L)
    (ht : t ∈ M ⊓ Subgroup.centralizer (blockU L : Set G))
    (ht' : t' ∈ M ⊓ Subgroup.centralizer (blockU L : Set G))
    (ht'' : t'' ∈ M ⊓ Subgroup.centralizer (blockU L : Set G))
    (h : r * t * (r' * t') = r'' * t'') :
    ∃ o ∈ oTwoIn L, ∃ w ∈ blockU L, t'' = o * (t * t') * w := by
  have hw : ⁅t⁻¹, r'⁻¹⁆ ∈ blockU L :=
    H.block.comm_centralizer_mem_blockU H.normal ⟨M.inv_mem ht.1, Subgroup.inv_mem _ ht.2⟩ r'⁻¹
      (L.inv_mem hr')
  set w := ⁅t⁻¹, r'⁻¹⁆ with hwdef
  have hwt' : w * t' = t' * w := Subgroup.mem_centralizer_iff.1 ht'.2 w hw
  have e1 : t'' = (r''⁻¹ * r * r') * (t * t') * w := by
    have h1 : t'' = r''⁻¹ * (r * t * (r' * t')) := by rw [h]; group
    have h2 : t * r' = r' * t * w := by
      rw [hwdef]
      simp only [commutatorElement_def]
      group
    calc t'' = r''⁻¹ * (r * (t * r') * t') := by rw [h1]; group
      _ = r''⁻¹ * (r * (r' * t * w) * t') := by rw [h2]
      _ = r''⁻¹ * r * r' * t * (w * t') := by group
      _ = r''⁻¹ * r * r' * t * (t' * w) := by rw [hwt']
      _ = (r''⁻¹ * r * r') * (t * t') * w := by group
  refine ⟨r''⁻¹ * r * r', ?_, w, hw, e1⟩
  rw [← H.block.inf_centralizer_blockU]
  refine ⟨L.mul_mem (L.mul_mem (L.inv_mem hr'') hr) hr', ?_⟩
  have hoeq : r''⁻¹ * r * r' = t'' * w⁻¹ * (t * t')⁻¹ := by
    rw [e1]
    group
  rw [hoeq]
  exact (Subgroup.centralizer (blockU L : Set G)).mul_mem
    ((Subgroup.centralizer (blockU L : Set G)).mul_mem ht''.2
      ((Subgroup.centralizer (blockU L : Set G)).inv_mem (H.blockU_le_centralizer hw)))
    ((Subgroup.centralizer (blockU L : Set G)).inv_mem
      ((Subgroup.centralizer (blockU L : Set G)).mul_mem ht.2 ht'.2))

theorem tOf_mul_mem (hZ : blockZ L = ⊥)
    (hS : IsElemAbelian 2 (T ⊓ Subgroup.centralizer (L : Set G))) (a a' : ↥A) :
    ((H.lOf a)⁻¹ * (a : G) * ((H.lOf a')⁻¹ * (a' : G)))⁻¹ *
      ((H.lOf (a * a'))⁻¹ * ((a * a' : ↥A) : G)) ∈ bGrp L A := by
  have hmul : (a : G) * (a' : G) = ((a * a' : ↥A) : G) := rfl
  obtain ⟨o, ho, w, hw, e⟩ := H.tOf_mul_aux (r := H.lOf a) (r' := H.lOf a') (r'' := H.lOf (a * a'))
    (t := (H.lOf a)⁻¹ * (a : G)) (t' := (H.lOf a')⁻¹ * (a' : G))
    (t'' := (H.lOf (a * a'))⁻¹ * ((a * a' : ↥A) : G)) (H.lOf_mem a') (H.lOf_mem a)
    (H.lOf_mem (a * a')) (H.tOf_mem_M a) (H.tOf_mem_M a') (H.tOf_mem_M (a * a'))
    (by rw [← hmul]; group)
  rw [e]
  have hP : (H.lOf a)⁻¹ * (a : G) * ((H.lOf a')⁻¹ * (a' : G)) ∈
      T ⊓ Subgroup.centralizer (blockU L : Set G) :=
    mul_mem (H.tOf_mem a) (H.tOf_mem a')
  have h1 := H.conj_mem_bGrp hS hP (H.oTwoIn_le_bGrp hZ hS ho)
  have h2 : w ∈ bGrp L A := (le_sup_right : blockU L ≤ bGrp L A) hw
  have e2 : ((H.lOf a)⁻¹ * (a : G) * ((H.lOf a')⁻¹ * (a' : G)))⁻¹ *
      (o * ((H.lOf a)⁻¹ * (a : G) * ((H.lOf a')⁻¹ * (a' : G))) * w) =
      (((H.lOf a)⁻¹ * (a : G) * ((H.lOf a')⁻¹ * (a' : G)))⁻¹ * o *
        ((H.lOf a)⁻¹ * (a : G) * ((H.lOf a')⁻¹ * (a' : G)))) * w := by group
  rw [e2]
  exact (bGrp L A).mul_mem h1 h2

theorem relIndex_bGrp_le (hS : IsElemAbelian 2 (T ⊓ Subgroup.centralizer (L : Set G))) :
    (bGrp L A).relIndex (T ⊓ Subgroup.centralizer (blockU L : Set G)) ≤ 2 ^ n := by
  set X : Subgroup G := ((M ⊓ Subgroup.centralizer (L : Set G)) ⊔ blockU L) with hX
  set U : Subgroup G := M ⊓ Subgroup.centralizer (blockU L : Set G) with hU
  set P : Subgroup G := T ⊓ Subgroup.centralizer (blockU L : Set G) with hP
  have hPU : P ≤ U := inf_le_inf_right _ H.sylow.le
  have hXP : X ⊓ P = bGrp L A := by
    apply le_antisymm
    · rintro x ⟨hxX, hxP⟩
      have hcomm : ∀ c ∈ M ⊓ Subgroup.centralizer (L : Set G), ∀ y ∈ blockU L, c * y = y * c :=
        fun c hc y hy => commute_S_V hc.2 hy
      obtain ⟨c, hc, v, hv, rfl⟩ := exists_mul_of_mem_sup' hcomm hxX
      have hcT : c ∈ T := by
        have e : c = (c * v) * v⁻¹ := by group
        rw [e]
        exact T.mul_mem hxP.1 (T.inv_mem (H.V_le_T hv))
      rw [H.bGrp_eq_sup_S hS]
      exact Subgroup.mul_mem_sup ⟨hcT, hc.2⟩ hv
    · refine le_inf ?_ H.B_le_P
      rw [H.bGrp_eq_sup_S hS]
      exact sup_le_sup_right (inf_le_inf_right _ H.sylow.le) _
  have hne : X.relIndex U ≠ 0 := Subgroup.index_ne_zero_of_finite
  calc (bGrp L A).relIndex P = (X ⊓ P).relIndex P := by rw [hXP]
    _ = X.relIndex P := Subgroup.inf_relIndex_right _ _
    _ ≤ X.relIndex U := Subgroup.relIndex_le_of_le_right hPU hne
    _ ≤ 2 ^ n := H.block.relIndex_le H.le H.normal

end Hyp45

end CFSG.CGT.PushingUpLit.T2K

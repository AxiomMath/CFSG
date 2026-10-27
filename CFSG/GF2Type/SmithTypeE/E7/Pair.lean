module

public import CFSG.GF2Type.SmithTypeE.E7.E23aCard
public import CFSG.GF2Type.SmithTypeE.E7.E23Four
public import Certificates.Certificate38802
public import CFSG.GF2Type.SmithTypeE.DMod.RhoTD6

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open Subgroup
open CFSG.SmithD6 (wt tvCols applyCols tvImg)
open CFSG.GF2Type.SmithTypeE.DMod

attribute [local irreducible] CFSG.SmithD6.tvCols CFSG.SmithD6.wt CFSG.SmithD6.applyCols

theorem commute_conj_inv_E7 {G : Type*} [Group G] (g : G) {x y : G} (h : Commute x y) :
    Commute (g⁻¹ * x * g) (g⁻¹ * y * g) := by
  show g⁻¹ * x * g * (g⁻¹ * y * g) = g⁻¹ * y * g * (g⁻¹ * x * g)
  have e1 : g⁻¹ * x * g * (g⁻¹ * y * g) = g⁻¹ * (x * y) * g := by group
  have e2 : g⁻¹ * y * g * (g⁻¹ * x * g) = g⁻¹ * (y * x) * g := by group
  rw [e1, e2, h.eq]

section Checks


theorem ea7F3Check_holds : ∀ p ∈ CFSG.SmithD6.ea7I, ∃ i < 75735,
    applyCols (tvCols 0) (wt i) = wt i ∧ applyCols (tvCols 31899) (wt i) = wt i ∧
    ∃ c < 2 ^ 32, applyCols (tvCols p) c ^^^ c = wt i :=
  Certificates.certificate38802

end Checks


theorem inE_of_vec {k : Fin 365211} {i : ℕ} (hi : i < 75735) {v : V}
    (h : tvEquiv k.val v + v = wtV i) : InE k.val i := by
  refine ⟨code32 v, code32_lt v, ?_⟩
  refine eq_of_decode32_eq (Nat.xor_lt_two_pow (applyCols_lt (size_tvCols k.val)
    (fun c hc => tvCols_lt k.val hc) (code32 v)) (code32_lt v)) (wt_lt hi) ?_
  rw [decode32_xor, ← tvEquiv_decode k.2, decode32_code32, h, wtV]

theorem vec_of_inE {k : Fin 365211} {i : ℕ} (h : InE k.val i) :
    ∃ v : V, tvEquiv k.val v + v = wtV i := by
  obtain ⟨c, -, hc⟩ := h
  refine ⟨decode32 c, ?_⟩
  rw [tvEquiv_decode k.2, ← decode32_xor, hc, wtV]

theorem fix_of_vec {k : Fin 365211} {i : ℕ} (hi : i < 75735)
    (h : tvEquiv k.val (wtV i) = wtV i) : applyCols (tvCols k.val) (wt i) = wt i := by
  refine eq_of_decode32_eq (applyCols_lt (size_tvCols k.val) (fun c hc => tvCols_lt k.val hc)
    (wt i)) (wt_lt hi) ?_
  rw [← tvEquiv_decode k.2]
  exact h

theorem vec_of_fix {k : Fin 365211} {i : ℕ} (h : applyCols (tvCols k.val) (wt i) = wt i) :
    tvEquiv k.val (wtV i) = wtV i := by
  rw [wtV, tvEquiv_decode k.2, h]

theorem rhoMod_tvEquiv (g : TD6) (k : Fin 365211) (v : V) :
    rhoMod g (tvEquiv k.val v) = tvEquiv ((g : Equiv.Perm (Fin 365211)) k).val (rhoMod g v) := by
  have h := congrArg (fun L : V ≃ₗ[ZMod 2] V => L (rhoMod g v)) (rhoMod_conj_tvEquiv g k)
  simpa using h

theorem transport_inE (g : TD6) {k : Fin 365211} {i : Fin 75735} (h : InE k.val i.val) :
    InE ((g : Equiv.Perm (Fin 365211)) k).val (g • i).val := by
  obtain ⟨v, hv⟩ := vec_of_inE h
  refine inE_of_vec (g • i).2 (v := rhoMod g v) ?_
  rw [← rhoMod_tvEquiv, ← map_add, hv, rhoMod_wtV]

theorem transport_fix (g : TD6) {k : Fin 365211} {i : Fin 75735}
    (h : applyCols (tvCols k.val) (wt i.val) = wt i.val) :
    applyCols (tvCols ((g : Equiv.Perm (Fin 365211)) k).val) (wt (g • i).val) = wt (g • i).val := by
  refine fix_of_vec (g • i).2 ?_
  have h2 := congrArg (rhoMod g) (vec_of_fix h)
  rw [rhoMod_tvEquiv, rhoMod_wtV] at h2
  exact h2

theorem commute_tvP_of_conj {g : Equiv.Perm (Fin 365211)} (hg : g ∈ TD6) {a b : Fin 365211}
    (h : Commute (tvP (g a)) (tvP (g b))) : Commute (tvP a) (tvP b) := by
  rw [← mul_tvP_mul_inv hg a, ← mul_tvP_mul_inv hg b] at h
  have h2 := commute_conj_inv_E7 g h
  have e : ∀ x : Equiv.Perm (Fin 365211), g⁻¹ * (g * x * g⁻¹) * g = x := fun x => by group
  rwa [e, e] at h2

theorem f3_std {k : Fin 365211} (h0 : Commute (tvP k) (tvP 0))
    (h1 : Commute (tvP k) (tvP stdOpp)) :
    ∃ i < 75735, InE k.val i ∧ applyCols (tvCols 0) (wt i) = wt i ∧
      applyCols (tvCols stdOpp.val) (wt i) = wt i := by
  have e0 : tvImg k.val 0 = 0 := tvImg_eq_of_commute (a := k) (b := 0) h0.eq
  have e31 : tvImg k.val 31899 = 31899 := by
    have h := tvImg_eq_of_commute (a := k) (b := stdOpp) h1.eq
    rw [stdOpp_val] at h
    exact h
  have hkX : CFSG.SmithD6.ea7InX k.val = true := by
    simp [CFSG.SmithD6.ea7InX, e0, e31]
  have hkI : k.val ∈ CFSG.SmithD6.ea7I := by
    unfold CFSG.SmithD6.ea7I
    exact List.mem_filter.mpr ⟨List.mem_range.mpr k.2, hkX⟩
  obtain ⟨i, hi, hA, hB, c, hc, hC⟩ := ea7F3Check_holds k.val hkI
  have hB' : applyCols (tvCols stdOpp.val) (wt i) = wt i := by
    rw [stdOpp_val]
    exact hB
  exact ⟨i, hi, ⟨_, hc, hC⟩, hA, hB'⟩

theorem hF3_holds : ∀ kt ku k : Fin 365211, orderOf (tvP kt * tvP ku) = 3 →
    Commute (tvP k) (tvP kt) → Commute (tvP k) (tvP ku) →
      ∃ i < 75735, InE k.val i ∧ applyCols (tvCols kt.val) (wt i) = wt i ∧
        applyCols (tvCols ku.val) (wt i) = wt i := by
  intro kt ku k hord h1 h2
  obtain ⟨g, hg, hg0, hg31⟩ := exists_mem_TD6_pair hord
  have hkk : g (g⁻¹ k) = k := by simp
  have hc0 : Commute (tvP (g⁻¹ k)) (tvP 0) :=
    commute_tvP_of_conj hg (by rw [hkk, hg0]; exact h1)
  have hc31 : Commute (tvP (g⁻¹ k)) (tvP stdOpp) :=
    commute_tvP_of_conj hg (by rw [hkk, hg31]; exact h2)
  obtain ⟨i, hi, hE, hf0, hf31⟩ := f3_std hc0 hc31
  let gT : TD6 := ⟨g, hg⟩
  refine ⟨(gT • (⟨i, hi⟩ : Fin 75735)).val, (gT • (⟨i, hi⟩ : Fin 75735)).2, ?_, ?_, ?_⟩
  · have := transport_inE gT (k := g⁻¹ k) (i := ⟨i, hi⟩) hE
    rwa [show (gT : Equiv.Perm (Fin 365211)) (g⁻¹ k) = k from hkk] at this
  · have := transport_fix gT (k := 0) (i := ⟨i, hi⟩) hf0
    rwa [show (gT : Equiv.Perm (Fin 365211)) 0 = kt from hg0] at this
  · have := transport_fix gT (k := stdOpp) (i := ⟨i, hi⟩) hf31
    rwa [show (gT : Equiv.Perm (Fin 365211)) stdOpp = ku from hg31] at this

section M4


theorem commute_tvP_conj {g : Equiv.Perm (Fin 365211)} (hg : g ∈ TD6) {a b : Fin 365211}
    (h : Commute (tvP a) (tvP b)) : Commute (tvP (g a)) (tvP (g b)) := by
  rw [← mul_tvP_mul_inv hg a, ← mul_tvP_mul_inv hg b]
  have h2 := commute_conj_inv_E7 g⁻¹ h
  simpa only [inv_inv] using h2

theorem hM4_holds : ∀ kt ku : Fin 365211, orderOf (tvP kt * tvP ku) = 3 →
    1045094400 ≤ Nat.card ↥(closure (tvP '' {k : Fin 365211 |
      Commute (tvP k) (tvP kt) ∧ Commute (tvP k) (tvP ku)})) := by
  intro kt ku hord
  obtain ⟨g, hg, hg0, hg31⟩ := exists_mem_TD6_pair hord
  refine le_trans card_Lstd_ge ?_
  obtain ⟨c, hc⟩ : ∃ c : Equiv.Perm (Fin 365211) →* Equiv.Perm (Fin 365211),
      c = (MulAut.conj g).toMonoidHom := ⟨_, rfl⟩
  have hinj : Function.Injective c := by rw [hc]; exact (MulAut.conj g).injective
  have hcapp : ∀ x, c x = g * x * g⁻¹ := fun x => by rw [hc]; rfl
  have hle : Lstd.map c ≤ closure (tvP '' {k : Fin 365211 |
      Commute (tvP k) (tvP kt) ∧ Commute (tvP k) (tvP ku)}) := by
    rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨k, ⟨h0, h1⟩, rfl⟩
    show c (tvP k) ∈ closure (tvP '' {k : Fin 365211 |
      Commute (tvP k) (tvP kt) ∧ Commute (tvP k) (tvP ku)})
    rw [hcapp, mul_tvP_mul_inv hg k]
    refine Subgroup.subset_closure ⟨g k, ⟨?_, ?_⟩, rfl⟩
    · have := commute_tvP_conj hg h0
      rwa [hg0] at this
    · have := commute_tvP_conj hg h1
      rwa [hg31] at this
  calc Nat.card ↥Lstd = Nat.card ↥(Lstd.map c) := (Subgroup.card_map_of_injective hinj).symm
    _ ≤ _ := Subgroup.card_le_of_le hle

end M4

end CFSG.GF2Type.SmithTypeE.E7

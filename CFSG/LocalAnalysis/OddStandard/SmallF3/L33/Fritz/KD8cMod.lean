module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cCertInputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8cLift

public section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8c
open CFSG.ComponentClassification.HSFLit.KD8c

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

@[expose] noncomputable def cntX (P : Subgroup X) (h : X) : ℕ :=
  Nat.card {g : P // (g : X) * g = 1 ∨ (g : X) * g = h}

omit [Finite X] in
theorem conj_eq_conj_iff (c a b : X) : c * a * c⁻¹ = c * b * c⁻¹ ↔ a = b := by
  constructor
  · intro h
    have := congrArg (fun x => c⁻¹ * x * c) h
    simpa [mul_assoc] using this
  · rintro rfl
    rfl

omit [Finite X] in
theorem conj_eq_one_iff' (c a : X) : c * a * c⁻¹ = 1 ↔ a = 1 := by
  have h := conj_eq_conj_iff c a 1
  rwa [mul_one, mul_inv_cancel] at h

omit [Finite X] in
theorem cntX_map (P : Subgroup X) (h c : X) :
    cntX (P.map (MulAut.conj c).toMonoidHom) (c * h * c⁻¹) = cntX P h := by
  unfold cntX
  refine (Nat.card_congr (Equiv.subtypeEquiv (P.equivMapOfInjective _
    (MulAut.conj c).injective).toEquiv fun g => ?_)).symm
  show ((g : X) * g = 1 ∨ (g : X) * g = h) ↔
    (c * g * c⁻¹ * (c * g * c⁻¹) = 1 ∨ c * g * c⁻¹ * (c * g * c⁻¹) = c * h * c⁻¹)
  rw [show c * g * c⁻¹ * (c * g * c⁻¹) = c * (g * g) * c⁻¹ by group, conj_eq_conj_iff,
    conj_eq_one_iff']

theorem cntX_eq_of_conjTo (C : A.CaseKD) {h : X} (hconj : ConjTo t h) {P : Subgroup X}
    (hP : IsPGroup 2 P) (hPC : P ≤ centralizer ({h} : Set X)) (hcard : 64 ≤ Nat.card P) :
    cntX P h = cntX A.T t := by
  obtain ⟨c, hc, hcP⟩ := exists_conj_eq_T C hconj hP hPC hcard
  rw [← hcP, ← hc, cntX_map]

namespace VSide

variable (V : VSide S T₁)

theorem conjTo_of_not_mem_E0 (hE : Nat.card (S.E V.yi) = 16) {e : X} (he : e ∈ S.E V.yi)
    (he0 : e ∉ S.E0 V.yi V.ki) : ConjTo t e := by
  classical
  set As : Set X := {e | e ∈ S.E V.yi ∧ ConjTo t e} with hAs
  set Bs : Set X := (S.E V.yi : Set X) \ (S.E0 V.yi V.ki : Set X) with hBs
  have hAB : As ⊆ Bs := fun e he => ⟨he.1, fun h0 => V.not_conjTo_of_mem_E0 h0 he.2⟩
  have hA : As.ncard = 8 := by
    rw [← V.D.card_conj, ← Nat.card_coe_set_eq]
    exact Nat.card_congr
      { toFun := fun e => ⟨⟨e.1, e.2.1⟩, e.2.2⟩
        invFun := fun e => ⟨e.1.1, e.1.2, e.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hB : Bs.ncard = 8 := by
    have h0 : Nat.card (S.E0 V.yi V.ki) = 8 := V.F.card_E0
    rw [hBs, Set.ncard_sdiff (fun x hx => V.E0_le_E hx), ← Nat.card_coe_set_eq,
      ← Nat.card_coe_set_eq]
    simp only [SetLike.coe_sort_coe]
    rw [hE, h0]
  have hEq := Set.eq_of_subset_of_ncard_le hAB (by rw [hA, hB]) (Set.toFinite _)
  have hmem : e ∈ Bs := ⟨he, he0⟩
  rw [← hEq] at hmem
  exact hmem.2

end VSide

namespace Conf

namespace T2

namespace Lift

variable {K : Conf S T₁} {T : K.T2} (W : T.Lift)

theorem ψ_mem (x : Ext W.D') : W.ψ x ∈ T.P := W.range_ψ ▸ ⟨x, rfl⟩

theorem exists_ψ {g : X} (hg : g ∈ T.P) : ∃ x, W.ψ x = g := by
  rw [← W.range_ψ] at hg
  exact hg

theorem PC_eq (x : Ext W.D') :
    T.P ⊓ centralizer ({W.ψ x} : Set X) = (centralizer ({x} : Set (Ext W.D'))).map W.ψ := by
  ext g
  simp only [mem_inf, mem_centralizer_singleton_iff, mem_map]
  constructor
  · rintro ⟨hg, hc⟩
    obtain ⟨y, rfl⟩ := W.exists_ψ hg
    exact ⟨y, W.ψ_injective (by rw [map_mul, map_mul]; exact hc), rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨W.ψ_mem y, by rw [← map_mul, hy, map_mul]⟩

theorem card_PC (x : Ext W.D') :
    Nat.card (T.P ⊓ centralizer ({W.ψ x} : Set X) : Subgroup X) = ccE x := by
  classical
  rw [W.PC_eq, card_map_of_injective W.ψ_injective,
    show Nat.card (centralizer ({x} : Set (Ext W.D'))) =
      Nat.card {g : Ext W.D' // g * x = x * g} from
      Nat.card_congr (Equiv.subtypeEquivRight fun _ => mem_centralizer_singleton_iff),
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

theorem cnt_PC (x : Ext W.D') :
    cntX (T.P ⊓ centralizer ({W.ψ x} : Set X)) (W.ψ x) = cntE x := by
  classical
  have hb : Function.Bijective (fun y : {g : Ext W.D' // g * x = x * g ∧
      (g * g = 1 ∨ g * g = x)} =>
      (⟨⟨W.ψ y.1, W.ψ_mem _, mem_centralizer_singleton_iff.mpr
        (by rw [← map_mul, y.2.1, map_mul])⟩, by
          rcases y.2.2 with h | h
          · left; rw [← map_mul, h, map_one]
          · right; rw [← map_mul, h]⟩ :
      {g : (T.P ⊓ centralizer ({W.ψ x} : Set X) : Subgroup X) //
        (g : X) * g = 1 ∨ (g : X) * g = W.ψ x})) := by
    refine ⟨fun a b h => Subtype.ext (W.ψ_injective ?_), fun g => ?_⟩
    · have := congrArg (fun g => (g.1 : X)) h
      simpa using this
    · obtain ⟨⟨g, hgP, hgc⟩, hsq⟩ := g
      obtain ⟨y, rfl⟩ := W.exists_ψ hgP
      have hyc : y * x = x * y :=
        W.ψ_injective (by rw [map_mul, map_mul]; exact mem_centralizer_singleton_iff.mp hgc)
      have hysq : y * y = 1 ∨ y * y = x := by
        rcases hsq with h | h
        · left; exact W.ψ_injective (by rw [map_mul, map_one]; exact h)
        · right; exact W.ψ_injective (by rw [map_mul]; exact h)
      exact ⟨⟨y, hyc, hysq⟩, rfl⟩
  rw [cntX, ← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

include W in
theorem nt_card {x : Ext W.D'} (h : 64 < ccE x) : ¬ ConjTo t (W.ψ x) := by
  refine not_conjTo_of_card_gt C (P := T.P ⊓ centralizer ({W.ψ x} : Set X))
    (T.isPGroup.to_le inf_le_left) inf_le_right ?_
  rw [W.card_PC]
  exact h

theorem nt_conj (c x : Ext W.D') (h : ¬ ConjTo t (W.ψ (c * x * c⁻¹))) : ¬ ConjTo t (W.ψ x) := by
  rwa [map_mul, map_mul, map_inv, conjTo_conj_iff] at h

theorem ψ_e0 {x : Ext W.D'} (hx : x.e = false) : W.ψ x = K.ι x.a := by
  rw [W.ψ_apply, hx]
  simp

theorem nt_F {x : Ext W.D'} (hx : x.e = false) (hF : inE 6 x.a = true ∨ inE 7 x.a = true) :
    ¬ ConjTo t (W.ψ x) := by
  rw [W.ψ_e0 hx]
  rcases hF with h | h
  · exact fun hc => K.not_hasT_6 ⟨_, K.ι_mem_Ex h, hc⟩
  · exact fun hc => K.not_hasT_7 ⟨_, K.ι_mem_Ex h, hc⟩

abbrev uh : Ext W.D' := Ext.incl W.D' MC.u

theorem conjTo_u : ConjTo t (W.ψ W.uh) := by
  rw [W.ψ_incl, K.ι_u]
  let V₂ := side₂ S K.h4 K.D₁ K.D₂ K.hq₁ K.hq₂
  have hxy : S.x * S.y ∈ S.E0 V₂.yi V₂.ki := V₂.F.yF_mem_E0
  refine V₂.conjTo_of_not_mem_E0 (KD46.card_E₂ S)
    (mul_mem (KD46.mem_E_t S _) (V₂.E0_le_E hxy)) fun h => V₂.F.t_not_mem_E0 ?_
  have := mul_mem h (inv_mem hxy)
  rwa [mul_inv_cancel_right] at this

include W in
theorem nt_cnt {x : Ext W.D'} (h64 : 64 ≤ ccE x) (hu64 : 64 ≤ ccE W.uh)
    (hne : cntE x ≠ cntE W.uh) : ¬ ConjTo t (W.ψ x) := by
  intro hx
  apply hne
  rw [← W.cnt_PC, ← W.cnt_PC]
  rw [cntX_eq_of_conjTo C hx (T.isPGroup.to_le inf_le_left) inf_le_right
      (by rw [W.card_PC]; exact h64),
    cntX_eq_of_conjTo C W.conjTo_u (T.isPGroup.to_le inf_le_left) inf_le_right
      (by rw [W.card_PC]; exact hu64)]

end Lift

end T2

end Conf

end KD8c

end CFSG.OddStandard.SmallF3.L33.KD

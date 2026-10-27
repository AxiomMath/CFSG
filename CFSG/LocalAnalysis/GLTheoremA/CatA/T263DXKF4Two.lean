module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXWFam
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXHardExc
public import CFSG.RankThree.PartOne.KF.ClsExcF4Two

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.T263
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def t263GExcHard2F (p : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .F4 q | .G2 q => q.card = 2 ∧ ¬ p ∣ q.card ^ 2 - 1
    | _ => False

@[expose] def t263GExcHard2E (p : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .E7 q | .E8 q => q.card = 2 ∧ ¬ p ∣ q.card ^ 2 - 1
    | _ => False

theorem t263SelWP_excHard2_of (hF : T263SelWP t263GExcHard2F) (hE : T263SelWP t263GExcHard2E) :
    T263SelWP t263GExcHard2 := by
  refine T263SelWP.of_cover ?_ hF hE
  intro p i hi
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d <;> simp only [t263GExcHard2, t263GExcHard2F, t263GExcHard2E, onLie] at hi ⊢ <;>
      first | exact hi.elim | exact Or.inl hi | exact Or.inr hi
  | cyclic r hr => exact hi.elim
  | alternating n hn => exact hi.elim
  | sporadic s => exact hi.elim

theorem t263SelWP_excHard2F :
    T263SelWP t263GExcHard2F := by
  refine DXW.t263SelWP_of_innerRank (fun p hp hp2 Ω _ _ S hSn hSq hSp hcat b hbp hInn => ?_)
    (fun p hp hp2 X _ hcat E U hE hU2 hU hEU => ?_)
  · refine inducesInnerMod_excInner hp hp2 hSn hSq hSp (S10.catalogIs_imp ?_ hcat) hbp hInn
    intro i hi
    cases i with
    | lie d =>
      obtain ⟨d, hv⟩ := d
      cases d <;> simp only [t263GExcHard2F, t263GExcInner, onLie] at hi ⊢ <;>
        first | exact hi.elim | exact (K144I.p_eq_two_of_card_eq_two hi.1).1
    | cyclic r hr => exact hi.elim
    | alternating n hn => exact hi.elim
    | sporadic s => exact hi.elim
  · classical
    obtain ⟨i, hi, ⟨e⟩⟩ := hcat
    cases i with
    | lie d =>
      obtain ⟨d, hv⟩ := d
      cases d
      case F4 q =>
        obtain ⟨hq2, hpq⟩ : q.card = 2 ∧ ¬ p ∣ q.card ^ 2 - 1 := hi
        have hp3 : p ≠ 3 := fun h => hpq (by rw [hq2, h]; norm_num)
        have hp5 : 5 ≤ p := by
          have := hp.two_le
          rcases (by omega : p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p) with h | h | h | h
          · exact absurd h hp2
          · exact absurd h hp3
          · exact absurd (h ▸ hp) (by decide)
          · exact h
        obtain ⟨K, _, _, hK, -, ⟨φ⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv
        haveI := finite_modGL (τ := .F4) (K := K)
        let ψ : X ≃* ↥(adjointGroup .F4 K) := e.trans φ
        haveI : Finite X := Finite.of_equiv _ ψ.symm.toEquiv
        haveI : Fact p.Prime := ⟨hp⟩
        by_contra hgt
        push Not at hgt
        have hEp : IsPGroup p ↥E := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 x x.2)⟩
        obtain ⟨k, hk⟩ := hEp.exists_card_eq
        have hk2 : 2 ≤ k := by
          by_contra h
          push Not at h
          interval_cases k
          · rw [hk, pow_zero] at hgt; exact absurd hgt (by have := hp.one_lt; omega)
          · rw [hk, pow_one] at hgt; exact lt_irrefl _ hgt
        obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E) p
          (show p ^ 2 ∣ Nat.card ↥E by rw [hk]; exact pow_dvd_pow p hk2)
        set E' : Subgroup X := H.map E.subtype with hE'
        have hE'c : Nat.card E' = p ^ 2 := by
          rw [hE', Subgroup.card_map_of_injective E.subtype_injective, hH]
        have hE'U : E' ≤ Subgroup.normalizer (U : Set X) :=
          (Subgroup.map_subtype_le H).trans hEU
        refine CFSG.RankThree.PartOne.KFU.no_plane_F4_two (hK.trans hq2) hp hp5
          (U := U.map ψ.toMonoidHom) (E := E'.map ψ.toMonoidHom) ?_ (hU2.map ψ.toMonoidHom) ?_ ?_
        · intro hbot
          exact hU ((Subgroup.map_eq_bot_iff_of_injective U ψ.injective).1 hbot)
        · rw [← Subgroup.map_equiv_normalizer_eq]
          exact Subgroup.map_mono hE'U
        · rw [Subgroup.card_map_of_injective ψ.injective, hE'c]
      case G2 q =>
        obtain ⟨hq2, -⟩ : q.card = 2 ∧ ¬ p ∣ q.card ^ 2 - 1 := hi
        have h3 := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
        rw [TauCeti.LieTypeIndex.inStandardRange_iff] at h3
        omega
      all_goals exact False.elim hi
    | cyclic r hr => exact False.elim hi
    | alternating n hn => exact False.elim hi
    | sporadic s => exact False.elim hi

end CFSG.LocalAnalysis.GLTheoremA.T263.DX

end

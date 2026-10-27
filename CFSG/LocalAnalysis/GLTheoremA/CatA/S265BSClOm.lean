module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BTy
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BSClAsm
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BSClInn
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BSClOmPair
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CBridge
import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma49i
import CFSG.HardMathSupport.Dickson.Bal207.OrthInnerField

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.RankThree.Classical2 (orthDerived)
open scoped commutatorElement

theorem statedClassicalModel_of_tyOm10m {G : Type} [Group G] (h : catalogIs G tyOm10m) :
    StatedClassicalModel G .POmegaMinus 5 2 1 := by
  obtain ⟨q, hv, hq, ⟨e₀⟩⟩ : ∃ (q : TauCeti.PrimePower)
      (hv : (TauCeti.LieTypeIndex.twistedD 5 q).Valid), q.card = 2 ∧
        Nonempty (G ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedD 5 q, hv⟩) := by
    obtain ⟨d, hv, hP, ⟨e⟩⟩ := CatB.exists_lieIndex h
    cases d with
    | twistedD r q =>
      rcases r with _ | _ | _ | _ | _ | _ | r
      all_goals first | exact hP.elim | exact ⟨q, hv, hP, ⟨e⟩⟩
    | _ => exact hP.elim
  have hq' : q.p ^ q.exponent = 2 := by rw [← TauCeti.PrimePower.card_def]; exact hq
  have hp2 : q.p = 2 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1
    (hq' ▸ dvd_pow_self q.p (Nat.pos_iff_ne_zero.mp q.exponent_pos))
  have he1 : q.exponent = 1 := by
    rw [hp2] at hq'
    exact Nat.pow_right_injective le_rfl (hq'.trans (pow_one 2).symm)
  have hS := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even 5 q hv hp2 e₀
  rw [hp2, he1] at hS
  exact hS

private theorem isOmMA_of_tyOm10m {G : Type} [Group G] (h : catalogIs G tyOm10m) :
    catalogIs G (isOmMA 5 (2 ^ 1)) := by
  obtain ⟨i, hi, he⟩ := h
  refine ⟨i, ?_, he⟩
  cases i with
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | twistedD r q =>
      rcases r with _ | _ | _ | _ | _ | _ | r
      all_goals first | exact hi.elim | exact Or.inl ⟨rfl, by rw [pow_one]; exact hi⟩
    | _ => exact hi.elim
  | _ => exact hi.elim

theorem qsBRes_om10m {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω}
    {D K : Subgroup Ω} (hN : QSNL 3 S B T x D K) (hS : catalogIs (PSimple 3 S) tyOm10m)
    (hK : catalogIs (PSimple 3 K) S9.isU5two ∨ catalogIs (PSimple 3 K) S9.isU6two)
    (hB : Nat.card B = 3 ^ 5)
    (hc : ¬ (⁅T, B⁆ : Subgroup Ω) ≤ Subgroup.centralizer (S : Set Ω)) : QSConcl 3 S B D K := by
  have h := hN.cfg
  have hSN : ∀ g : Ω, g ∈ Subgroup.normalizer (S : Set Ω) := fun g =>
    (Subgroup.normalizer_eq_top_iff.2 h.normal) ▸ Subgroup.mem_top g
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Ω →* MulAut (PSimple 3 S),
      ∀ (w : Ω) (hw : w ∈ Subgroup.normalizer (S : Set Ω)), Φ w = chevAut 3 S ⟨w, hw⟩ :=
    ⟨(chevAut 3 S).comp (MonoidHom.mk' (fun g => (⟨g, hSN g⟩ :
      Subgroup.normalizer (S : Set Ω))) fun _ _ => rfl), fun _ _ => rfl⟩
  obtain ⟨W, ρ₀, hWn, hWmem, hρ₀, hρ₀1⟩ :=
    exists_innerSection Φ (center_pSimple_eq_bot Nat.prime_three h.comp)
  have hS' := statedClassicalModel_of_tyOm10m hS
  have hinn : ∀ (g : Ω) (p : ℕ), p.Prime → p ≠ 2 → g ^ p = 1 → g ∈ W := fun g p hp hp2 hg =>
    (hWmem g).2 (by
      by_contra hne
      push Not at hne
      exact hp.ne_one (Nat.dvd_one.1 (CFSG.HardMathSupport.Dickson.Bal207.OrthFix.orth_outer_dvd
        (Or.inr rfl) le_rfl hS' hp hp2 (β := Φ g) (by rw [← map_pow, hg, map_one]) hne)))
  have hBW : B ≤ W := fun b hb => hinn b 3 Nat.prime_three (by norm_num) (h.elem.2 b hb)
  haveI := hWn
  obtain ⟨F, _, _, _, V, _, _, _, Q, hF, hQ, hdim, -, hmod⟩ :=
    S172C.exists_omegaMinus_model (n := 5) (k := 1) (by norm_num) le_rfl
  obtain ⟨ψ⟩ := hmod (PSimple 3 S) (isOmMA_of_tyOm10m hS)
  haveI : Finite ↥(orthDerived Q) := Finite.of_equiv _ ψ.toEquiv
  refine qsConcl_of_section h hK hB hc (eS := ψ.toMonoidHom) ψ.injective (W := W)
    (ψ.toMonoidHom.comp ρ₀) (fun w hw z => ?_)
    (fun w hw => (ψ.map_eq_one_iff).trans ((hρ₀1 w).trans (by rw [hΦ w hw]))) hBW
    ((Subgroup.commutator_mono le_top hBW).trans (Subgroup.commutator_le_right ⊤ W))
    (fun y _ hy => hinn y 11 (by norm_num) (by norm_num)
      (by rw [← hy]; exact pow_orderOf_eq_one y))
    fun A T₁ d y hA h81 hdA hd1 hy hy1 hdy hT hT1 hAT => ?_
  · have h1 : chevAut 3 S ⟨w, hw⟩ z = ρ₀ w * z * (ρ₀ w)⁻¹ :=
      (congrArg (fun γ : MulAut (PSimple 3 S) => γ z) ((hρ₀ w).trans (hΦ w hw))).symm
    rw [h1]
    simp
  · obtain ⟨e, heA, hec, hlay⟩ := exists_layer_pair_orthDerived (by simpa using hF)
      (by simpa using hdim) hQ hA h81 hdA hd1 hy hy1 hdy hT hT1 hAT
    exact ⟨e, heA, hec, glaPLayer_comap_ne_bot_of_equiv ψ hlay⟩

theorem qsBResOm10m_holds : QSBResOm10m :=
  fun _ _ _ _ _ _ _ _ _ hN hS hK hB hc => qsBRes_om10m hN hS hK hB hc

end CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

end

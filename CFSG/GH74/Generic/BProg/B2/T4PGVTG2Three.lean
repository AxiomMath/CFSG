module

public import CFSG.GH74.Generic.BProg.B2.PuG2OddAux
public import CFSG.GH74.Generic.BProg.B2.T4PGVTBasic

public section

namespace CFSG.GH74.Generic.BProg.B2.T4.PGV

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley (fixSubfield odd_pinned_Chevalley_p_components)

open CFSG.LieType.Ree (ReeTag)

open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 (fixSub mem_fixSub)

open CFSG.GH74.GLS.IVK.Proofs2
open scoped commutatorElement


theorem q3Out_g2three {f : ℕ} (hf : 1 ≤ f) : Q3EmptyOut (fun X _ => LieModel X .G2 0 3 f) := by
  intro N _ _ H t K hs htH hH
  have := hs.normal
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := Ivk47ab.exists_equiv_of_lieModel hH
  obtain ⟨α, hα2, hαout, hαfix⟩ :=
    PumpupOutOrders.exists_outer_aut hs.inv hs.faithful htH e
  set X : Subgroup ↥H := fixSub (MulAut.conjNormal t : MulAut ↥H) with hX
  have hXα : X.map e.toMonoidHom = fixSub α := by
    ext y
    rw [Subgroup.mem_map, mem_fixSub, hαfix y]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using (PumpupOutOrders.mem_fixSub_conjNormal (H := H) (t := t) (y := x)).1 hx
    · intro h
      exact ⟨e.symm y, (PumpupOutOrders.mem_fixSub_conjNormal (H := H) (t := t)).2 h,
        e.apply_symm_apply y⟩
  let Ψ : ↥X ≃* ↥(fixSub α) :=
    (X.equivMapOfInjective e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr hXα)
  have : CharP F ReeTag.G2.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      hf hcard
  have hα2' : α ^ 2 = 1 := (sq α).trans hα2
  rcases CFSG.LieType.AlgebraicGroups.G2_three_involution_inner_quadratic_or_exceptional hf hcard
      hα2' with ⟨g, a, hαg⟩ | ⟨e', he', hKe, δ, hδ, g, a, hαg⟩ | ⟨b, g, hfb, hαb⟩
  · exact hαout (ivk93res_inner_of_diag hαg)
  ·
    obtain ⟨Φ⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm2.P911.g2_quadratic_fixed_equiv Nat.prime_three
      he' hKe δ hδ hαg hα2'
    have hk : Nat.card (fixSubfield δ) = 3 ^ e' :=
      PuG2OddAux.card_fixSubfield_quad Nat.prime_three he' hKe δ hδ
    have hkodd : ringChar (fixSubfield δ) ≠ 2 :=
      CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow Nat.prime_three (by norm_num) hk
    obtain ⟨hsk, -⟩ := odd_pinned_Chevalley_p_components ReeTag.G2.tag (fixSubfield δ) hkodd
    have hsimple : IsSimpleGroup ↥X := (MulEquiv.isSimpleGroup_congr (Ψ.trans Φ)).2 hsk
    have h3k : 3 ≤ 3 ^ e' := Nat.le_self_pow (by omega) 3
    have hmodel : LieModel (adjointGroup ReeTag.G2.tag (fixSubfield δ)) .G2 0 3 e' :=
      Ivk47ab.lieModel_G2g Nat.prime_three he' h3k hk
    have hcK := hs.card_eq_of_fixSub_simple hsimple
    rw [hs.card_K, Nat.card_congr (Ψ.trans Φ).toEquiv,
      CFSG.GH74.card_of_lieModel_G2 (by norm_num) hmodel] at hcK
    exact (lt_ordG2 h3k).ne hcK
  ·
    have hK' : Nat.card F = 3 ^ (2 * b + 1) := hfb ▸ hcard
    have hα' : (MulAut.conj g * ReeTag.G2.finiteReeAut F b) ^ 2 = 1 := hαb ▸ hα2'
    obtain ⟨Ψ'⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm2.P911.g2_ree_fixed_equiv hK' hα'
    have hfix := congrArg fixSub hαb
    obtain ⟨Φ0⟩ := PumpupOutOrders.exists_fixEquiv (H := H) (t := t)
    have hcC : Nat.card ↥(H ⊓ centralizer ({t} : Set N)) =
        Nat.card ↥(ReeTag.G2.reeGamma F b) :=
      Nat.card_congr (Φ0.trans (Ψ.trans ((MulEquiv.subgroupCongr hfix).trans Ψ'))).toEquiv
    rw [CFSG.ComponentClassification.LiteratureLocal.G2_card_reeGamma b hK'] at hcC
    apply PumpupOutOrders.not_sixteen_dvd_ordRee b
    have h16 := hs.sixteen_dvd.trans hs.card_dvd_cent
    rw [hcC] at h16
    exact h16

end CFSG.GH74.Generic.BProg.B2.T4.PGV

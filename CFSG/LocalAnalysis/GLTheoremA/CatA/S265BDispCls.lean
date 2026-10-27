module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoClBase
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeLinFive
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeSpDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeSpWitness
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BBridge
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeOmMinusHolds

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ClassicalGroups.Orthogonal (formOfRingEquiv formOfRingEquiv_apply
  nondegenerate_formOfRingEquiv)

private theorem wit_of_equiv {G H : Type} [Group G] [Group H] (f : G ≃* H) {E : Subgroup G}
    (hE : IsElemAbelian 3 E) (h5 : 3 ^ 5 ≤ Nat.card E) (hTL : T171S.TwoLocal E) :
    ∃ E : Subgroup H, IsElemAbelian 3 E ∧ 3 ^ 5 ≤ Nat.card E ∧ T171S.TwoLocal E :=
  ⟨E.map f.toMonoidHom, hE.map f.toMonoidHom,
    h5.trans_eq (Subgroup.card_map_of_injective (f := f.toMonoidHom) f.injective).symm,
    hTL.map f.toMonoidHom f.injective⟩

theorem exists_twoLocal_five_A {n : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A n q).Valid) (hq : q.card = 2) (hn : 9 ≤ n) :
    ∃ E : Subgroup (TauCeti.CFSGIndex.lie ⟨.A n q, hv⟩).Group,
      IsElemAbelian 3 E ∧ 3 ^ 5 ≤ Nat.card E ∧ T171S.TwoLocal E := by
  obtain ⟨hp2, hexp⟩ := I1431C2.cl_primePower_card_two hq
  have hcl := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv
    (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.A n q, hv⟩).Group)
  rw [hp2, hexp] at hcl
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hcl
  obtain ⟨U, hU2, hU1, E, hEU, hE, h5⟩ := T171S.localPow5_sl_fin (m := n + 1) (Nat.succ_le_succ hn)
  exact wit_of_equiv (e.trans (CFSG.QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two
    (n + 1) K (by simpa using hK))).symm hE h5.ge ⟨U, hU2, hU1, hEU⟩

theorem exists_twoLocal_five_B {n : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.B n q).Valid) (hq : q.card = 2) (hn : 6 ≤ n) :
    ∃ E : Subgroup (TauCeti.CFSGIndex.lie ⟨.B n q, hv⟩).Group,
      IsElemAbelian 3 E ∧ 3 ^ 5 ≤ Nat.card E ∧ T171S.TwoLocal E := by
  obtain ⟨f⟩ := T171S.nonempty_mulEquiv_lie_statedSp n q hv hq (le_trans (by norm_num) hn)
  obtain ⟨E, hE, h5, hTL⟩ := T171S.exists_twoLocal_elementaryAbelian n 5 hn
  exact wit_of_equiv f.symm hE h5.ge hTL

theorem exists_twoLocal_five_D {n : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.D n q).Valid) (hq : q.card = 2) (hn : 6 ≤ n) :
    ∃ E : Subgroup (TauCeti.CFSGIndex.lie ⟨.D n q, hv⟩).Group,
      IsElemAbelian 3 E ∧ 3 ^ 5 ≤ Nat.card E ∧ T171S.TwoLocal E := by
  obtain ⟨V, _, _, _, Q, hQ, hdim, hplus, hθ⟩ :=
    S172B.exists_omegaPlusTwo_model (n := n) (le_trans (by norm_num) hn)
  have hcat : catalogIs (TauCeti.CFSGIndex.lie ⟨.D n q, hv⟩).Group (isOmPA n 2) :=
    ⟨TauCeti.CFSGIndex.lie ⟨.D n q, hv⟩, Or.inl ⟨rfl, hq⟩, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨f⟩ := hθ _ hcat
  rcases hn.eq_or_lt with rfl | h7
  · obtain ⟨E, hE, h5, hTL⟩ := T171S.exists_twoLocal_three_pow_five_six hQ hdim hplus
    exact wit_of_equiv f.symm hE h5.ge hTL
  · obtain ⟨E, hE, h5, hTL⟩ := T171S.exists_twoLocal_three_pow_five_plus hQ hdim h7 hplus
    exact wit_of_equiv f.symm hE h5.ge hTL

private theorem wit_minus {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {Q : QuadraticForm F V} (hF : Nat.card F = 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ} (hdim : Module.finrank F V = 2 * n)
    (hn : 6 ≤ n) (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    ∃ E : Subgroup ↥(orthDerived Q), IsElemAbelian 3 E ∧ 3 ^ 5 ≤ Nat.card E ∧ T171S.TwoLocal E := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Finite V := Module.finite_of_finite F
  let e : ZMod 2 ≃+* F :=
    ZMod.ringEquivOfPrime F Nat.prime_two (by rwa [← Nat.card_eq_fintype_card])
  letI : Module (ZMod 2) V := Module.compHom V (e : ZMod 2 →+* F)
  have hsmul : ∀ (c : ZMod 2) (v : V), c • v = e c • v := fun _ _ => rfl
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hFc : Nat.card F = Nat.card (ZMod 2) := by rw [hF, Nat.card_zmod]
  have hdim' : Module.finrank (ZMod 2) V = 2 * n := by
    have h1 : Nat.card V = Nat.card F ^ Module.finrank F V := Module.natCard_eq_pow_finrank
    have h2 : Nat.card V = Nat.card (ZMod 2) ^ Module.finrank (ZMod 2) V :=
      Module.natCard_eq_pow_finrank
    rw [hdim, hFc] at h1
    exact Nat.pow_right_injective (by rw [Nat.card_zmod]) (h2.symm.trans h1)
  have hminus' : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (formOfRingEquiv e hsmul Q) := by
    rintro ⟨W, hWdim, hW0⟩
    apply hminus
    let W' : Submodule F V :=
      { carrier := W
        add_mem' := W.add_mem
        zero_mem' := W.zero_mem
        smul_mem' := fun c v hv => by
          have h := W.smul_mem (e.symm c) hv
          rwa [hsmul, RingEquiv.apply_symm_apply] at h }
    haveI : Finite ↥W' := Subtype.finite
    haveI : Finite ↥W := Subtype.finite
    haveI : Module.Finite F ↥W' := Module.Finite.of_finite
    haveI : Module.Finite (ZMod 2) ↥W := Module.Finite.of_finite
    have hdimW : Module.finrank F W' = Module.finrank (ZMod 2) W := by
      have h1 : Nat.card ↥W' = Nat.card F ^ Module.finrank F W' := Module.natCard_eq_pow_finrank
      have h2 : Nat.card ↥W = Nat.card (ZMod 2) ^ Module.finrank (ZMod 2) W :=
        Module.natCard_eq_pow_finrank
      have hc : Nat.card ↥W' = Nat.card ↥W :=
        Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
      rw [hc, hFc] at h1
      exact Nat.pow_right_injective (by rw [Nat.card_zmod]) (h1.symm.trans h2)
    refine ⟨W', ?_, fun x hx => ?_⟩
    · rw [hdimW, hWdim, hdim', hdim]
    · have hx0 : formOfRingEquiv e hsmul Q x = 0 := hW0 x hx
      rw [formOfRingEquiv_apply] at hx0
      exact (map_eq_zero_iff e.symm e.symm.injective).1 hx0
  obtain ⟨E, hE, h5, hTL⟩ := T171S.exists_twoLocal_three_pow_five_minus
    (nondegenerate_formOfRingEquiv hQ) hdim' hn hminus'
  obtain ⟨iso⟩ := T171S.nonempty_orthDerived_equiv_of_ringEquiv e hsmul Q
  exact wit_of_equiv iso hE h5.ge hTL

theorem exists_twoLocal_five_twistedD {n : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedD n q).Valid) (hq : q.card = 2) (hn : 6 ≤ n) :
    ∃ E : Subgroup (TauCeti.CFSGIndex.lie ⟨.twistedD n q, hv⟩).Group,
      IsElemAbelian 3 E ∧ 3 ^ 5 ≤ Nat.card E ∧ T171S.TwoLocal E := by
  obtain ⟨F, _, _, _, V, _, _, _, Q, hF, hQ, hdim, hminus, hθ⟩ :=
    S172C.exists_omegaMinus_model (n := n) (k := 1) (le_trans (by norm_num) hn) le_rfl
  have hcat : catalogIs (TauCeti.CFSGIndex.lie ⟨.twistedD n q, hv⟩).Group (isOmMA n 2) :=
    ⟨TauCeti.CFSGIndex.lie ⟨.twistedD n q, hv⟩, Or.inl ⟨rfl, hq⟩, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨f⟩ := hθ _ hcat
  obtain ⟨E, hE, h5, hTL⟩ := wit_minus (hF.trans (pow_one 2)) hQ hdim hn hminus
  exact wit_of_equiv f.symm hE h5 hTL

end CFSG.LocalAnalysis.GLTheoremA.S265

end

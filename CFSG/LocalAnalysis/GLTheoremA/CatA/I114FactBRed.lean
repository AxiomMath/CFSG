module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I114FactBDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T5
import CFSG.LocalAnalysis.GLTheoremA.CatB.SL3TorArith
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I114Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I114

open CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremA CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator

theorem exists_field_of_isSLThreeExc {K : Type} [Group K] [Finite K] (hK : IsSLThreeExc K)
    (hcat : catalogIs (K ⧸ Subgroup.center K) S9.isL3char2) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (f : ℕ), CharP F 2 ∧ 1 ≤ f ∧
      Nat.card F = 2 ^ f ∧ ¬ 3 ∣ f ∧ (Nat.card F % 9 = 4 ∨ Nat.card F % 9 = 7) ∧
      Nonempty (K ≃* Matrix.SpecialLinearGroup (Fin 3) F) := by
  classical
  obtain ⟨F, hF, hFfin, hmod, ⟨e⟩⟩ := hK
  let _ := hF
  let _ := hFfin
  obtain ⟨m, hm2, hmeven, hLie⟩ := I91T.lieModel_of_catalogIs_isL3char2 hcat
  have hclass : (StatedLieTag.PSL) ∈ CFSG.Blueprint.classicalTags := by decide
  obtain ⟨-, F₀, hF₀, hF₀fin, hF₀card, ⟨e₀⟩⟩ := hLie.statedClassicalModel hclass
  have h3F : 3 ∣ Nat.card F - 1 := by omega
  have hZK : Nat.card (Subgroup.center K) = 3 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact CFSG.Open.StatedCenterThree.card_center_statedSL_three h3F
  have hK₁ : Nat.card K = Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) := by
    rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_three]
  have hK₂ : Nat.card K = 3 * Nat.card (K ⧸ Subgroup.center K) := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K)
    rw [this, hZK]
    ring
  have hK₃ : Nat.card (K ⧸ Subgroup.center K) = Nat.card (StatedProj (StatedSL 3 F₀)) :=
    Nat.card_congr e₀.toEquiv
  have hF₀mod : Nat.card F₀ % 3 = 1 := by
    rw [hF₀card]
    obtain ⟨j, hj⟩ := hmeven
    rw [hj, ← two_mul, pow_mul]
    norm_num [Nat.pow_mod]
  have hgcd : Nat.gcd 3 (Nat.card F₀ - 1) = 3 := Nat.gcd_eq_left (by omega)
  have hPSL : 3 * Nat.card (StatedProj (StatedSL 3 F₀)) =
      Nat.card F₀ ^ 3 * ((Nat.card F₀ ^ 2 - 1) * (Nat.card F₀ ^ 3 - 1)) := by
    have h := CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd.card_statedProj_statedSL_three_mul
      (F := F₀)
    rw [hgcd] at h
    rw [Nat.mul_comm, h, mul_assoc]
  have hK₄ : Nat.card K =
      Nat.card F₀ ^ 3 * ((Nat.card F₀ ^ 2 - 1) * (Nat.card F₀ ^ 3 - 1)) := by
    rw [hK₂, hK₃, ← hPSL, Nat.mul_comm]
  have hcardeq : Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) =
      Nat.card F₀ ^ 3 * ((Nat.card F₀ ^ 2 - 1) * (Nat.card F₀ ^ 3 - 1)) :=
    hK₁.symm.trans hK₄
  have hFeq : Nat.card F = Nat.card F₀ := by
    have h2F : 2 ≤ Nat.card F := Finite.one_lt_card
    have h2F₀ : 2 ≤ Nat.card F₀ := Finite.one_lt_card
    refine CFSG.LocalAnalysis.GLTheoremA.CatB.SL3Tor.sl_card_inj h2F h2F₀ ?_
    simpa [mul_assoc] using hcardeq
  have hcardpow : Nat.card F = 2 ^ m := hFeq.trans hF₀card
  have hchar : CharP F 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hcardpow
  have h3m : ¬ 3 ∣ m := by
    refine CFSG.HardMathSupport.Solomon.Coordinator.not_three_dvd_of_mod_nine
      (p := 2) (f := m) hcardpow ?_
    rcases hmod with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
  refine ⟨F, hF, hFfin, m, hchar, by omega, hcardpow, h3m, hmod, ?_⟩
  exact ⟨e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm⟩

private theorem transport_hypotheses {K G : Type} [Group K] [Finite K] [Group G] [Finite G]
    (e : K ≃* G) {H : Subgroup (MulAut K)} {S : Subgroup K}
    (hHab : IsElemAbelian 3 H) (hHcard : Nat.card H = 9) (hSne : S ≠ ⊥)
    (hS2 : IsPGroup 2 S) (hSnorm : ∀ h ∈ H, S.map h.toMonoidHom = S) :
    IsElemAbelian 3 (H.map (MulAut.congr e).toMonoidHom) ∧
      Nat.card (H.map (MulAut.congr e).toMonoidHom) = 9 ∧
      (S.map e.toMonoidHom) ≠ ⊥ ∧ IsPGroup 2 (S.map e.toMonoidHom) ∧
      (∀ h' ∈ H.map (MulAut.congr e).toMonoidHom,
        (S.map e.toMonoidHom).map h'.toMonoidHom = S.map e.toMonoidHom) := by
  let c : MulAut K ≃* MulAut G := MulAut.congr e
  let H' : Subgroup (MulAut G) := H.map c.toMonoidHom
  let S' : Subgroup G := S.map e.toMonoidHom
  have hHab' : IsElemAbelian 3 H' := hHab.map c.toMonoidHom
  have hHcard' : Nat.card H' = 9 := by
    rw [Subgroup.card_map_of_injective c.injective, hHcard]
  have hSne' : S' ≠ ⊥ := by
    intro hbot
    have hmap : S.map e.toMonoidHom = ⊥ := by simpa [S'] using hbot
    exact hSne ((Subgroup.map_eq_bot_iff_of_injective (H := S) (f := e.toMonoidHom)
      e.injective).mp hmap)
  have hS2' : IsPGroup 2 S' := hS2.map e.toMonoidHom
  have hSnorm' : ∀ h' ∈ H', S'.map h'.toMonoidHom = S' := by
    intro h' hh'
    have hh'' : h' ∈ H.map c.toMonoidHom := by simpa [H'] using hh'
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hh''
    calc S'.map (c a).toMonoidHom
        = S.map ((c a).toMonoidHom.comp e.toMonoidHom) := by
          rw [show S' = S.map e.toMonoidHom from rfl, Subgroup.map_map]
      _ = S.map (e.toMonoidHom.comp a.toMonoidHom) := by
          congr 1
          ext s
          simp [c, MulAut.congr_apply]
      _ = (S.map a.toMonoidHom).map e.toMonoidHom := by rw [Subgroup.map_map]
      _ = S' := by rw [hSnorm a ha]
  exact ⟨hHab', hHcard', hSne', hS2', hSnorm'⟩

private theorem transport_U_y {K G : Type} [Group K] [Finite K] [Group G] [Finite G]
    (e : K ≃* G) {H : Subgroup (MulAut K)} {H' : Subgroup (MulAut G)}
    (hH' : H' = H.map (MulAut.congr e).toMonoidHom)
    {U' : Subgroup G} {y' : G} (hU'ne : U' ≠ ⊥) (hU'2 : IsPGroup 2 U')
    (hU'inv : ∀ h ∈ H', U'.map h.toMonoidHom = U')
    (hy'nc : ∃ z : G, z * y' ≠ y' * z) (hy'ord : orderOf y' = 3)
    (hy'norm : y' ∈ Subgroup.normalizer (U' : Set G))
    (hy'fix : ∀ h ∈ H', h y' = y') :
    ∃ U : Subgroup K, U ≠ ⊥ ∧ IsPGroup 2 U ∧
      (∀ h ∈ H, U.map h.toMonoidHom = U) ∧
      ∃ y : K, (∃ z : K, z * y ≠ y * z) ∧ orderOf y = 3 ∧
        y ∈ Subgroup.normalizer (U : Set K) ∧ (∀ h ∈ H, h y = y) := by
  let U : Subgroup K := U'.comap e.toMonoidHom
  let y : K := e.symm y'
  have hcomap : U = U'.map e.symm.toMonoidHom := Subgroup.comap_equiv_eq_map_symm' e U'
  have hUne : U ≠ ⊥ := by
    rw [hcomap]
    exact fun h => hU'ne ((Subgroup.map_eq_bot_iff_of_injective (H := U')
      (f := e.symm.toMonoidHom) e.symm.injective).mp h)
  have hU2 : IsPGroup 2 U := hU'2.comap_of_injective e.toMonoidHom e.injective
  have hUinv : ∀ h ∈ H, U.map h.toMonoidHom = U := by
    intro h hh
    calc U.map h.toMonoidHom
        = U'.map (h.toMonoidHom.comp e.symm.toMonoidHom) := by
            rw [hcomap, Subgroup.map_map]
      _ = U'.map (e.symm.toMonoidHom.comp (MulAut.congr e h).toMonoidHom) := by
            congr 1
            ext g
            simp [MulAut.congr_apply]
      _ = (U'.map (MulAut.congr e h).toMonoidHom).map e.symm.toMonoidHom := by
            rw [Subgroup.map_map]
      _ = U := by
            rw [hU'inv (MulAut.congr e h) (by
              rw [hH']; exact Subgroup.mem_map_of_mem _ hh)]
            exact hcomap.symm
  have hy_nc : ∃ z : K, z * y ≠ y * z := by
    obtain ⟨z', hz'⟩ := hy'nc
    refine ⟨e.symm z', ?_⟩
    intro hzy
    exact hz' (by simpa [y, map_mul] using congrArg e hzy)
  have hy_ord : orderOf y = 3 := by
    have := e.symm.orderOf_eq y'
    simpa [y, hy'ord] using this
  have hy_norm : y ∈ Subgroup.normalizer (U : Set K) := by
    have hmap := Subgroup.map_equiv_normalizer_eq (U' : Subgroup G) e.symm
    have hmem : e.symm y' ∈ (Subgroup.normalizer (U' : Set G)).map e.symm.toMonoidHom :=
      Subgroup.mem_map_of_mem _ hy'norm
    rw [hmap, show U'.map e.symm.toMonoidHom = U from hcomap.symm] at hmem
    exact hmem
  have hy_fix : ∀ h ∈ H, h y = y := by
    intro h hh
    apply e.injective
    have hh' : MulAut.congr e h ∈ H' := by
      rw [hH']; exact Subgroup.mem_map_of_mem _ hh
    have := hy'fix (MulAut.congr e h) hh'
    simpa [y, MulAut.congr_apply] using this
  exact ⟨U, hUne, hU2, hUinv, y, hy_nc, hy_ord, hy_norm, hy_fix⟩

private theorem transport_alpha {K G : Type} [Group K] [Finite K] [Group G] [Finite G]
    (e : K ≃* G) {H : Subgroup (MulAut K)} {H' : Subgroup (MulAut G)}
    (hH' : H' = H.map (MulAut.congr e).toMonoidHom)
    {α' : MulAut G} (hα'H' : α' ∈ H') (hα'ord : orderOf α' = 3)
    (hα'out : ¬ ∃ k : G, ∀ z : G, α' z = k * z * k⁻¹) :
    ∃ α ∈ H, orderOf α = 3 ∧ ¬ ∃ k : K, ∀ z : K, α z = k * z * k⁻¹ := by
  let α : MulAut K := (MulAut.congr e).symm α'
  have hαH : α ∈ H := by
    have hα'' : MulAut.congr e α ∈ H' := by
      rw [show MulAut.congr e α = α' from (MulAut.congr e).apply_symm_apply α']
      exact hα'H'
    have hα''' : MulAut.congr e α ∈ H.map (MulAut.congr e).toMonoidHom := by
      simpa [hH'] using hα''
    obtain ⟨a, ha, hca⟩ := Subgroup.mem_map.1 hα'''
    have haeq : a = α := (MulAut.congr e).injective hca
    simpa [haeq] using ha
  have hα_ord : orderOf α = 3 := by
    have := (MulAut.congr e).symm.orderOf_eq α'
    simpa [α, hα'ord] using this
  have hα_out : ¬ ∃ k : K, ∀ z : K, α z = k * z * k⁻¹ := by
    rintro ⟨k, hk⟩
    apply hα'out
    refine ⟨e k, fun z => ?_⟩
    have hαconj : α = MulAut.conj k := by ext z; exact hk z
    have h : MulAut.congr e α = MulAut.conj (e k) := by
      rw [hαconj, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj]
    have hα'eq : α' = MulAut.conj (e k) := by
      rw [← (MulAut.congr e).apply_symm_apply α', h]
    rw [hα'eq, MulAut.conj_apply]
  exact ⟨α, hαH, hα_ord, hα_out⟩

theorem i114FactB_of_coreSL (h : I114CoreSL) : I114FactB := by
  intro K _ _ hK hcat H S hHab hHcard hSne hS2 hSnorm
  obtain ⟨F, hF, hFfin, f, hchar, hf, hcard, h3f, hmod, ⟨e⟩⟩ :=
    exists_field_of_isSLThreeExc hK hcat
  let _ := hF
  let _ := hFfin
  haveI := hchar
  let G := Matrix.SpecialLinearGroup (Fin 3) F
  let c : MulAut K ≃* MulAut G := MulAut.congr e
  let H' : Subgroup (MulAut G) := H.map c.toMonoidHom
  let S' : Subgroup G := S.map e.toMonoidHom
  obtain ⟨hHab', hHcard', hSne', hS2', hSnorm'⟩ :=
    transport_hypotheses e hHab hHcard hSne hS2 hSnorm
  obtain ⟨U', hU'ne, hU'2, hU'inv, y', hy'nc, hy'ord, hy'norm, hy'fix, α', hα'H',
    hα'ord, hα'out⟩ :=
    h F f hf hcard h3f hmod H' S' hHab' hHcard' hSne' hS2' hSnorm'
  obtain ⟨U, hUne, hU2, hUinv, y, hy_nc, hy_ord, hy_norm, hy_fix⟩ :=
    transport_U_y e (by rfl : H' = H.map c.toMonoidHom) hU'ne hU'2 hU'inv
      hy'nc hy'ord hy'norm hy'fix
  obtain ⟨α, hαH, hα_ord, hα_out⟩ :=
    transport_alpha e (by rfl : H' = H.map c.toMonoidHom) hα'H' hα'ord hα'out
  exact ⟨U, hUne, hU2, hUinv, y, hy_nc, hy_ord, hy_norm, hy_fix, α, hαH, hα_ord, hα_out⟩

end CFSG.LocalAnalysis.GLTheoremA.I114

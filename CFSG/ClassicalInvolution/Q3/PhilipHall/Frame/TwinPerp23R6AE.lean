module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23FusExit
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23FusMain
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23FusPair
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23FusW

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.AE

open Wr

variable {n : ℕ}

theorem yQ_moves_kQ : ∀ a ∈ kList, a * a ≠ 1 → yQ * a * yQ⁻¹ ≠ a ∧ yQ * a * yQ⁻¹ ≠ a⁻¹ := by
  decide +kernel

theorem yQ_moves_kQStar :
    ∀ a ∈ kStarList, a * a ≠ 1 → yQ * a * yQ⁻¹ ≠ a ∧ yQ * a * yQ⁻¹ ≠ a⁻¹ := by
  decide +kernel

theorem yOf_moves_memAt (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    ∀ a ∈ memAt α h b, a * a ≠ 1 →
      yOf (emb α h) * a * (yOf (emb α h))⁻¹ ≠ a ∧ yOf (emb α h) * a * (yOf (emb α h))⁻¹ ≠ a⁻¹ := by
  intro a ha ha2
  have key : ∀ a₀ : Wr 4, (a₀ * a₀ ≠ 1 → yQ * a₀ * yQ⁻¹ ≠ a₀ ∧ yQ * a₀ * yQ⁻¹ ≠ a₀⁻¹) →
      a = embed (emb α h) a₀ →
      yOf (emb α h) * a * (yOf (emb α h))⁻¹ ≠ a ∧
        yOf (emb α h) * a * (yOf (emb α h))⁻¹ ≠ a⁻¹ := by
    intro a₀ hmv rfl
    have ha₀ : a₀ * a₀ ≠ 1 := fun h1 => ha2 (by rw [← map_mul, h1, map_one])
    obtain ⟨h1, h2⟩ := hmv ha₀
    unfold yOf
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    exact ⟨fun h' => h1 (embed_injective _ h'), fun h' => h2 (embed_injective _ h')⟩
  cases b
  · obtain ⟨a₀, ha₀, rfl⟩ := ha
    exact key a₀ (yQ_moves_kQStar a₀ ha₀) rfl
  · obtain ⟨a₀, ha₀, rfl⟩ := ha
    exact key a₀ (yQ_moves_kQ a₀ ha₀) rfl

theorem yBar_moves_memBar (hn : 5 ≤ n) (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    ∀ x ∈ memBar α h b, x * x ≠ 1 →
      yBar α h * x * (yBar α h)⁻¹ ≠ x ∧ yBar α h * x * (yBar α h)⁻¹ ≠ x⁻¹ := by
  rintro _ ⟨a, ha, rfl⟩ hx2
  have ha2 : a * a ≠ 1 := fun h1 => hx2 (by rw [← map_mul, h1, map_one])
  have hs := supportedOn_of_mem_memAt ha
  have hy := yOf_supportedOn (emb α h)
  obtain ⟨h1, h2⟩ := yOf_moves_memAt α h b a ha ha2
  have hconj : yBar α h * mkQ n a * (yBar α h)⁻¹ =
      mkQ n (yOf (emb α h) * a * (yOf (emb α h))⁻¹) := by
    rw [yBar, map_mul, map_mul, map_inv]
  rw [hconj]
  refine ⟨fun h' => h1 (mkQ_inj_of_supportedOn hn ((hy.mul hs).mul hy.inv) hs h'), fun h' => ?_⟩
  rw [← map_inv] at h'
  exact h2 (mkQ_inj_of_supportedOn hn ((hy.mul hs).mul hy.inv) hs.inv h')

end CFSG.ClassicalInvolution.Q3.AE

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Fus

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section Sec

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)} {m : ℕ}

theorem ae_fusion_section (hm : 5 ≤ m) (hS : TwinDisc.Q8Section X Φ) (I : TC.Thin.AEIdent Φ m)
    {J : Subgroup X} (hJ : J ∈ Φ) :
    ∃ x : X, Odd (orderOf x) ∧ x ∈ Subgroup.normalizer (J : Set X) ∧
      ∀ j ∈ J, j ^ 2 ≠ 1 → x * j * x⁻¹ ≠ j ∧ x * j * x⁻¹ ≠ j⁻¹ := by
  classical
  obtain ⟨α, h, b, hlab⟩ := I.label J hJ
  have hyr : AE.yBar α h ∈ I.φ.range := by rw [I.range_eq]; exact AE.yBar_mem α h
  obtain ⟨y, hy, a, hya⟩ := I.exists_lift_pow_three hyr (AE.yBar_pow_three α h)
  have h8 : Nat.card J = 8 := TwinDisc.AE5.members_card8 hm hS I J hJ
  refine ⟨(y : X), ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat (Odd.pow (by decide : Odd 3)) (orderOf_dvd_of_pow_eq_one hya)
  ·
    have hmapσ : (AE.memBar α h b).map (MulAut.conj (I.φ y)).toMonoidHom = AE.memBar α h b := by
      have hle : (AE.memBar α h b).map (MulAut.conj (I.φ y)).toMonoidHom ≤ AE.memBar α h b := by
        rintro _ ⟨x, hx, rfl⟩
        rw [hy]
        exact AE.yBar_conj_mem_memBar α h b x hx
      refine Subgroup.eq_of_le_of_card_ge hle (le_of_eq ?_)
      exact (Subgroup.card_map_of_injective (MulAut.conj (I.φ y)).injective).symm
    have hJc : conjSub (y : X) J ∈ Φ := hS.hyp.conjInvariant (y : X) J hJ
    have heq : conjSub (y : X) J = J := by
      refine TwinDisc.AE5.same_of_image_n hm hS I hJc hJ ?_
      rw [TwinDisc.AE5.label_conj I hJ y, hlab, hmapσ]
    exact mem_normalizer_iff_conjSub_eq.mpr heq
  · intro j hj hj2
    set j' : ↥(TC.Thin.pSpan Φ) := ⟨j, TC.Thin.le_pSpan hJ hj⟩ with hj'
    have hjm : I.φ j' ∈ AE.memBar α h b := hlab ▸ I.mem_map hJ hj
    have hφj2 : I.φ j' * I.φ j' ≠ 1 := by
      intro h1
      apply hj2
      have hjj : j * j ∈ J := J.mul_mem hj hj
      have : I.φ ⟨j * j, TC.Thin.le_pSpan hJ hjj⟩ = I.φ ⟨1, TC.Thin.le_pSpan hJ J.one_mem⟩ := by
        rw [show (⟨j * j, TC.Thin.le_pSpan hJ hjj⟩ : ↥(TC.Thin.pSpan Φ)) = j' * j' from rfl,
          show (⟨1, TC.Thin.le_pSpan hJ J.one_mem⟩ : ↥(TC.Thin.pSpan Φ)) = 1 from rfl,
          map_mul, map_one, h1]
      rw [pow_two]
      exact I.injOn (by omega) hJ h8 hlab hjj J.one_mem this
    obtain ⟨h1, h2⟩ := AE.yBar_moves_memBar hm α h b _ hjm hφj2
    rw [← hy] at h1 h2
    constructor
    · intro he
      apply h1
      have : y * j' * y⁻¹ = j' := Subtype.ext (by simpa [hj'] using he)
      rw [← map_inv, ← map_mul, ← map_mul, this]
    · intro he
      apply h2
      have : y * j' * y⁻¹ = j'⁻¹ := Subtype.ext (by simpa [hj'] using he)
      rw [← map_inv, ← map_mul, ← map_mul, this, map_inv]

end Sec

section At

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem ae_fusion_at (h : PerpHypS n Y R S t) {c : Y} {J J' Q Q' : Subgroup Y} {w : Y}
    (hT : LayerTwins Y R c J J' Q Q' w) {m : ℕ} (hm : 5 ≤ m)
    (I : TC.Thin.AEIdent (TwinDisc.secFam (Om R) c) m) :
    ∃ x : Y, x ∈ Subgroup.centralizer ({c} : Set Y) ∧ Odd (orderOf x) ∧
      (∀ q ∈ Q, x * q * x⁻¹ ∈ Q) ∧
      ∀ q ∈ Q, q ^ 2 ≠ 1 → x * q * x⁻¹ ≠ q ∧ x * q * x⁻¹ ≠ q⁻¹ := by
  classical
  have hC := CoreData.of_S h.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hc2' : IsPGroup 2 (Subgroup.zpowers c) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hT.hc2
  have hS := p23_q8Section h hT.hc2
  have h2all := TwinDisc.AE5.members_twoN hm hS I
  obtain ⟨xb, hxbodd, hxbN, hxbmove⟩ :=
    ae_fusion_section hm hS I (TwinDisc.secImg_mem_secFam hT.hJ)
  set C := Subgroup.centralizer ({c} : Set Y) with hCdef
  set H := TwinDisc.coreHull (Om R) c with hHdef
  set N := classicalInvolutionOddCore ↥H with hNdef
  set π := QuotientGroup.mk' N with hπ
  set A : Subgroup ↥H := (Q.subgroupOf C).subgroupOf H with hAdef
  have hAmap : A.map π = TwinDisc.secImg (Om R) c J :=
    map_syl_eq_secImg hc2' hT.hJ hT.hQ hT.hQc (h2all _ (TwinDisc.secImg_mem_secFam hT.hJ))
  have hNodd : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card ↥H
  have hA2 : IsPGroup 2 ↥A :=
    (hT.hQ.2.1.comap_of_injective C.subtype C.subtype_injective).comap_of_injective
      H.subtype H.subtype_injective
  have hAQ : ∀ a ∈ A, (((a : ↥H) : ↥C) : Y) ∈ Q := fun a ha =>
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp ha)
  have hxA : xb ∈ Subgroup.normalizer ((A.map π : Subgroup (↥H ⧸ N)) : Set (↥H ⧸ N)) := by
    rw [hAmap]; exact hxbN
  obtain ⟨x₂, hx₂odd, hx₂π, hx₂A, -⟩ :=
    lift_odd_normalizing N hNodd hA2 (IsPGroup.of_bot (p := 2) (G := ↥H))
      (fun a _ b hb => by rw [Subgroup.mem_bot.mp hb, mul_one, one_mul]) hxbodd hxA
      (fun b hb => by rw [Subgroup.mem_bot.mp hb, map_one, mul_one, one_mul])
  have hTs : IsSylow2In Q (TwinADescent.coreAt c J) :=
    (TwinADescent.isSylow2In_coreAt_iff hc2' hT.hJ.2).mpr ⟨hT.hQ, hT.hQc⟩
  have hqA : ∀ q ∈ Q, ∃ a ∈ A, (((a : ↥H) : ↥C) : Y) = q := by
    intro q hq
    have hqC : q ∈ C := hT.hQc hq
    have hqH : (⟨q, hqC⟩ : ↥C) ∈ H :=
      le_coreHull hT.hJ (Subgroup.mem_subgroupOf.mpr (hTs.1 hq))
    exact ⟨⟨⟨q, hqC⟩, hqH⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hq), rfl⟩
  have hAN : A ⊓ N = ⊥ :=
    AscQuot.inf_eq_bot_of_isPGroup_of_odd N hA2 le_rfl
      (hNodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
  refine ⟨(((x₂ : ↥H) : ↥C) : Y), ((x₂ : ↥H) : ↥C).2, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hx₂odd
  · intro q hq
    obtain ⟨a, ha, rfl⟩ := hqA q hq
    exact hAQ _ (hx₂A a ha)
  · intro q hq hq2
    obtain ⟨a, ha, rfl⟩ := hqA q hq
    have hja : π a ∈ TwinDisc.secImg (Om R) c J := hAmap ▸ ⟨a, ha, rfl⟩
    have hj2 : (π a) ^ 2 ≠ 1 := by
      intro h
      apply hq2
      have hπa2 : π (a ^ 2) = 1 := by rw [map_pow]; exact h
      have h1 : a ^ 2 ∈ A ⊓ N := ⟨A.pow_mem ha 2, (QuotientGroup.eq_one_iff _).mp hπa2⟩
      rw [hAN, Subgroup.mem_bot] at h1
      have h2 := congrArg (fun z : ↥H => (((z : ↥H) : ↥C) : Y)) h1
      simpa [pow_two] using h2
    obtain ⟨hm1, hm2⟩ := hxbmove _ hja hj2
    constructor
    · intro h
      apply hm1
      have h1 : x₂ * a * x₂⁻¹ = a := Subtype.ext (Subtype.ext h)
      rw [← hx₂π, ← map_inv, ← map_mul, ← map_mul, h1]
    · intro h
      apply hm2
      have h1 : x₂ * a * x₂⁻¹ = a⁻¹ := Subtype.ext (Subtype.ext h)
      rw [← hx₂π, ← map_inv, ← map_mul, ← map_mul, h1, map_inv]

end At

section E6AE

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem comm_of_normalizes_of_unique {J Q : Subgroup Y} {w x : Y} (hw : IsUniqueInvolution J w)
    (hQJ : Q ≤ J) (hwQ : w ∈ Q) (hxQ : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) : x * w = w * x := by
  have hm : x * w * x⁻¹ ∈ J := hQJ (hxQ w hwQ)
  have hsq : x * w * x⁻¹ * (x * w * x⁻¹) = 1 := by
    calc x * w * x⁻¹ * (x * w * x⁻¹) = x * (w * w) * x⁻¹ := by group
      _ = 1 := by rw [hw.sq, mul_one, mul_inv_cancel]
  rcases hw.unique _ hm hsq with h1 | h1
  · exact absurd (by simpa using h1 : w = 1) hw.ne_one
  · calc x * w = x * w * x⁻¹ * x := by group
      _ = w * x := by rw [h1]

theorem wshape_e_false_of_ae_u (hc : P23Cfg n Y R S t K' W u e g)
    (I : TC.Thin.AEIdent (TwinDisc.secFam (Om R) u) 5)
    (h2 : ∀ L ∈ TwinDisc.secFam (Om R) e, IsPGroup 2 ↥L)
    (hV : ∃ V : Subgroup (SecQ R e), WSet (TwinDisc.secFam (Om R) e) = {V}) : False := by
  obtain ⟨Q, Q', hTu, hTe⟩ := layerTwins_both hc
  obtain ⟨x, hxu, -, hxQ, hmove⟩ := ae_fusion_at hc.std.perp hTu (le_refl 5) I
  have hΩ : HypOmegaGen (Om R) := (CoreData.of_S hc.std.perp.core).hyp
  have hwQ : u * e ∈ Q := involution_mem_sylow hΩ hTu.hJ.1 hTu.hw hTu.hQ
  have hxw := comm_of_normalizes_of_unique hTu.hw hTu.hQ.1 hwQ hxQ
  have hxe := mem_cent_e_of_cent_u hc hxu hxw
  exact wshape_false hc.std.perp hTe h2 hV hxe hxQ hmove

theorem noExit_e_false_of_ae_u (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (I : TC.Thin.AEIdent (TwinDisc.secFam (Om R) u) 5) (hno : SecNoExit R e) : False := by
  obtain ⟨Q, Q', hTu, hTe⟩ := layerTwins_both hc
  obtain ⟨x, hxe, hxodd, hxQ, hxQ', ⟨q, hq, hxq⟩, -⟩ := lie_fusion_at hcit hP hc.std.perp hTe hno
  have hΩ : HypOmegaGen (Om R) := (CoreData.of_S hc.std.perp.core).hyp
  have hwQ' : u * e ∈ Q' := involution_mem_sylow hΩ hTe.hJ'.1 hTe.hw' hTe.hQ'
  have hxu := mem_cent_u_of_cent_e hc hxe (hxQ' _ hwQ')
  exact hxq (nside_ae hc.std.perp hTu (Or.inl rfl) I hxu hxodd hxQ hxQ' q hq)

end E6AE

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Fus

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

@[expose] def P23E6AE' (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → SecAE R u 5 → SecAE R e 6

theorem p23E6AE'_proved {n : ℕ} (hT : TwinThmE.T4Supply)
    (hmodel : TwinDisc.ExitE4.E4ModelDStar) (hD4 : TwinCentRes.ModelFactD42) (hMu : P23E4Mu n) :
    P23E6AE' n := by
  intro hcit hP Y _ _ R S t K' W u e g hc h5
  obtain ⟨I⟩ := h5
  by_cases hno : SecNoExit R e
  · exact (Fus.noExit_e_false_of_ae_u hcit hP hc I hno).elim
  rcases Fus.p23E4ExitCases_of_mu hT hmodel hD4 hMu hcit hP Y R S t K' W u e g hc hno with
    hpair | ⟨hV, h2⟩ | h5e | h6
  · exact (Fus.pair_impossible hc hpair).elim
  · exact (Fus.wshape_e_false_of_ae_u hc I h2 hV).elim
  · exact (TwinPerp23.W.p23_false_of_ae5 hc h5e).elim
  · exact h6

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

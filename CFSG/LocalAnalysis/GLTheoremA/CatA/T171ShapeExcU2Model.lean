module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcU2Main
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110d
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
import CFSG.Assembly.LargeEvenGLABridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom onCenterQuotient
  onCenterQuotient_apply_mk centerQuotientHom_injective)


theorem mem_centralizer_of_action_trivial {G : Type} [Group G] [Finite G] {L : Subgroup G} {d : G}
    (hperf : commutator ↥L = ⊤) (hdN : d ∈ Subgroup.normalizer (L : Set G))
    (hZ : ∀ l l' : ↥L, (l' : G) = d⁻¹ * (l : G) * d →
      (QuotientGroup.mk l : ↥L ⧸ Subgroup.center ↥L) = QuotientGroup.mk l') :
    d ∈ Subgroup.centralizer (L : Set G) := by
  let φd : MulAut ↥L := CFSG.StandardType.ggGamma L (le_refl (Subgroup.normalizer (L : Set G)))
    ⟨d⁻¹, Subgroup.inv_mem _ hdN⟩
  have hφd : ∀ x : ↥L, (φd x : G) = d⁻¹ * (x : G) * d := by
    intro x
    simpa using CFSG.StandardType.ggGamma_coe L (le_refl (Subgroup.normalizer (L : Set G)))
      ⟨d⁻¹, Subgroup.inv_mem _ hdN⟩ x
  have hcen : centerQuotientHom ↥L φd = 1 := by
    ext q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    show onCenterQuotient φd (QuotientGroup.mk' (Subgroup.center ↥L) l) =
      QuotientGroup.mk' (Subgroup.center ↥L) l
    rw [onCenterQuotient_apply_mk]
    exact (hZ l (φd l) (hφd l)).symm
  haveI : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hperf
  have hconj1 : φd = 1 := centerQuotientHom_injective ↥L (by rw [hcen, map_one])
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h := congrArg (fun f : MulAut ↥L => ((f ⟨y, hy⟩ : ↥L) : G)) hconj1
  simp only [MulAut.one_apply] at h
  rw [hφd] at h
  calc y * d = d * (d⁻¹ * y * d) := by group
    _ = d * y := by rw [h]


theorem conj_mem_subgroupStabAut {G : Type} [Group G] [Finite G] {p : ℕ}
    {L J A : Subgroup G} {d b : G} (hS : Setup p L J A d b)
    (hbN : b ∈ Subgroup.normalizer (L : Set G))
    {R : Type} [Group R] [Finite R] (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) {w : R}
    (hwind : LargeEvenInduces θ (conjRel b) (MulAut.conj w)) :
    MulAut.conj w ∈ CFSG.GroupActions.subgroupStabAut
      ((J.subgroupOf L).map (piCenterQuot θ)) := by
  let cw : MulAut R := MulAut.conj w
  let φb : MulAut ↥L := CFSG.StandardType.ggGamma L (le_refl (Subgroup.normalizer (L : Set G)))
    ⟨b⁻¹, Subgroup.inv_mem _ hbN⟩
  have hφb : ∀ x : ↥L, (φb x : G) = b⁻¹ * (x : G) * b := by
    intro x
    simpa using CFSG.StandardType.ggGamma_coe L (le_refl (Subgroup.normalizer (L : Set G)))
      ⟨b⁻¹, Subgroup.inv_mem _ hbN⟩ x
  change ((J.subgroupOf L).map (piCenterQuot θ)).map cw.toMonoidHom =
    (J.subgroupOf L).map (piCenterQuot θ)
  have hev : ∀ l : ↥L, cw (piCenterQuot θ l) = piCenterQuot θ (φb l) := by
    intro l
    have h := hwind l (φb l) (hφb l)
    simpa [cw, MulAut.conj_apply] using h
  have hJinv : (J.subgroupOf L).map φb.toMonoidHom ≤ J.subgroupOf L := by
    rintro _ ⟨y, hy, rfl⟩
    have hb' : b⁻¹ ∈ Subgroup.normalizer (J : Set G) := Subgroup.inv_mem _ hS.b_norm
    have h := (Subgroup.mem_normalizer_iff.mp hb' (y : G)).mp hy
    rw [Subgroup.mem_subgroupOf]
    simpa [hφb] using h
  have hle : ((J.subgroupOf L).map (piCenterQuot θ)).map cw.toMonoidHom ≤
      (J.subgroupOf L).map (piCenterQuot θ) := by
    rintro _ ⟨-, ⟨y, hy, rfl⟩, rfl⟩
    change cw (piCenterQuot θ y) ∈ (J.subgroupOf L).map (piCenterQuot θ)
    rw [hev]
    exact Subgroup.mem_map_of_mem _ (hJinv (Subgroup.mem_map_of_mem _ hy))
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (f := cw.toMonoidHom) cw.injective]

theorem mul_comm_of_largeEvenInduces {G : Type} [Group G] [Finite G] {p : ℕ}
    {L J A : Subgroup G} {d b : G} (hS : Setup p L J A d b)
    {R : Type} [Group R] [Finite R] (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) {x w : R}
    (hdN : d ∈ Subgroup.normalizer (L : Set G)) (hbN : b ∈ Subgroup.normalizer (L : Set G))
    (hZ : Subgroup.center R = ⊥)
    (hxind : LargeEvenInduces θ (conjRel d) (MulAut.conj x))
    (hwind : LargeEvenInduces θ (conjRel b) (MulAut.conj w)) :
    x * w = w * x := by
  have hdb : d * b = b * d :=
    CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_commute hS.elem hS.d_mem hS.b_mem
  have h1 := largeEvenInduces_mul hdN hbN hdb hxind hwind
  have h2 := largeEvenInduces_mul hbN hdN hdb.symm hwind hxind
  rw [← hdb] at h2
  have huniq : MulAut.conj x * MulAut.conj w = MulAut.conj w * MulAut.conj x :=
    largeEvenInduces_unique h1 h2 (conjRel_total (Subgroup.mul_mem _ hdN hbN))
  refine CFSG.mulAutConj_injective_of_center_eq_bot hZ ?_
  rw [map_mul, map_mul]
  exact huniq


theorem indAut_of_adjointModel {G : Type} [Group G] [Finite G] {p : ℕ}
    {L J A : Subgroup G} {d b : G} (hA : ExcAdjCompInnAut) (hS : Setup p L J A d b)
    (hshape : ¬ I171.I171LieShapeAt p L) (hin : InducesInnerMod p L b)
    (hcat : catalogIs (PSimple p L) (onLie fun i => KD264Lie.isExcUntwistedIdx i ∧
      i.characteristic = 2)) :
    MI.indAut p J b hS.b_norm ∈ innAutDerived (PSimple p J) ∨
      Nat.card (PSimple p J) = 360 := by
  have hJleL : J ≤ L := hS.comp.1.1.trans inf_le_left
  have hpJ : p ∣ Nat.card ↥J :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110d.prime_dvd_card_of_glaPComponent
      hS.prime hS.pcomp
  have hpL : p ∣ Nat.card ↥L := hpJ.trans (Subgroup.card_dvd_of_le hJleL)
  have hdN : d ∈ Subgroup.normalizer (L : Set G) :=
    S171.normalizer_of_innerDiagMarking hS.idiag hS.d_mem
  have hbN : b ∈ Subgroup.normalizer (L : Set G) :=
    S171.normalizer_of_innerDiagMarking hS.idiag hS.b_mem
  have hLself : GLAPComponent p L L := glaPComponent_self_of_dvd_card hS.prime hS.qs hpL
  haveI hperfL : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hS.qs.1
  have hdin : InducesInnerMod p L d := inducesInnerMod_of_mem_not_shape hS hshape hS.d_mem
  obtain ⟨eP, heP⟩ := exists_pSimpleEquivCenterQuot_mk hS.prime hS.qs hpL
  obtain ⟨r, hr⟩ : ∃ r : PSimple p L, MulAut.conj r = MI.indAut p L d hdN :=
    (MI.indAut_mem_inner_iff hS.prime hLself hdN).2 hdin
  obtain ⟨r', hr'⟩ : ∃ r' : PSimple p L, MulAut.conj r' = MI.indAut p L b hbN :=
    (MI.indAut_mem_inner_iff hS.prime hLself hbN).2 hin
  have key : ∀ (τ : CFSG.Blueprint.Chevalley.Tag) (K : Type) [Field K] [Finite K]
      [CharP K 2],
      (τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) →
      (τ = .G2 → 4 ≤ Nat.card K) → (τ = .E6 → p = 3 → ¬ 3 ∣ Nat.card K - 1) →
      Nonempty (PSimple p L ≃* ↥(CFSG.Blueprint.Chevalley.adjointGroup τ K)) →
      MI.indAut p J b hS.b_norm ∈ innAutDerived (PSimple p J) ∨
        Nat.card (PSimple p J) = 360 := by
    intro τ K _ _ _ hτ hG2 hE6 ⟨eAd⟩
    by_cases h360 : Nat.card (PSimple p J) = 360
    · exact Or.inr h360
    · refine Or.inl ?_
      let θ : ↥L ⧸ Subgroup.center ↥L ≃*
          ↥(CFSG.Blueprint.Chevalley.adjointGroup τ K) := eP.trans eAd
      have hθmk : ∀ l : ↥L, θ (QuotientGroup.mk l) =
          eAd (QuotientGroup.mk (QuotientGroup.mk l)) := by
        intro l
        show eAd (eP (QuotientGroup.mk l)) = _
        rw [heP l]
      set x : ↥(CFSG.Blueprint.Chevalley.adjointGroup τ K) := eAd r with hxdef
      set w : ↥(CFSG.Blueprint.Chevalley.adjointGroup τ K) := eAd r' with hwdef
      have hxind : LargeEvenInduces θ (conjRel d) (MulAut.conj x) := by
        intro l l' hll
        have hrel : indRel p L d (QuotientGroup.mk l) (QuotientGroup.mk l') :=
          ⟨l, l', rfl, rfl, hll⟩
        have h1 : MI.indAut p L d hdN (QuotientGroup.mk (QuotientGroup.mk l)) =
            QuotientGroup.mk (QuotientGroup.mk l') := MI.indAut_apply_mk hdN hrel
        have h3 : r * (QuotientGroup.mk (QuotientGroup.mk l) : PSimple p L) * r⁻¹ =
            QuotientGroup.mk (QuotientGroup.mk l') := by
          rw [← MulAut.conj_apply, hr]
          exact h1
        rw [hθmk l, hθmk l', MulAut.conj_apply]
        change eAd r * eAd (QuotientGroup.mk (QuotientGroup.mk l)) * (eAd r)⁻¹ =
          eAd (QuotientGroup.mk (QuotientGroup.mk l'))
        rw [← map_inv, ← map_mul, ← map_mul, h3]
      have hwind : LargeEvenInduces θ (conjRel b) (MulAut.conj w) := by
        intro l l' hll
        have hrel : indRel p L b (QuotientGroup.mk l) (QuotientGroup.mk l') :=
          ⟨l, l', rfl, rfl, hll⟩
        have h1 : MI.indAut p L b hbN (QuotientGroup.mk (QuotientGroup.mk l)) =
            QuotientGroup.mk (QuotientGroup.mk l') := MI.indAut_apply_mk hbN hrel
        have h3 : r' * (QuotientGroup.mk (QuotientGroup.mk l) : PSimple p L) * r'⁻¹ =
            QuotientGroup.mk (QuotientGroup.mk l') := by
          rw [← MulAut.conj_apply, hr']
          exact h1
        rw [hθmk l, hθmk l', MulAut.conj_apply]
        change eAd r' * eAd (QuotientGroup.mk (QuotientGroup.mk l)) * (eAd r')⁻¹ =
          eAd (QuotientGroup.mk (QuotientGroup.mk l'))
        rw [← map_inv, ← map_mul, ← map_mul, h3]
      have hxp : x ^ p = 1 :=
        pow_eq_one_of_conj_pow_eq_one' (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot)
          (largeEvenInduces_pow_eq_one hdN hxind (hS.elem.2 d hS.d_mem))
      have hwp : w ^ p = 1 :=
        pow_eq_one_of_conj_pow_eq_one' (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot)
          (largeEvenInduces_pow_eq_one hbN hwind (hS.elem.2 b hS.b_mem))
      have hxw : x * w = w * x :=
        mul_comm_of_largeEvenInduces hS θ hdN hbN
          (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot) hxind hwind
      have hx1 : x ≠ 1 := by
        intro hx1
        have htriv : LargeEvenInduces θ (conjRel d) (1 : MulAut _) := by
          simpa [hx1] using hxind
        have hZ : ∀ l l' : ↥L, (l' : G) = d⁻¹ * (l : G) * d →
            (QuotientGroup.mk l : ↥L ⧸ Subgroup.center ↥L) = QuotientGroup.mk l' := by
          intro l l' hll
          have h := htriv l l' hll
          exact θ.injective (by simpa using h)
        have hmem := mem_centralizer_of_action_trivial hS.qs.1 hdN hZ
        have hbot : d ∈ A ⊓ Subgroup.centralizer (L : Set G) := ⟨hS.d_mem, hmem⟩
        rw [hS.faithful] at hbot
        exact hS.d_ne (Subgroup.mem_bot.1 hbot)
      have hJc : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer ({d} : Set G)) :=
        (CFSG.Assembly.isComponentOf_iff_open).2 hS.comp.1
      have hcomp := componentDescent_holds G L hS.qs
        ↥(CFSG.Blueprint.Chevalley.adjointGroup τ K) θ d hdN (MulAut.conj x) hxind J hJc
        ((CFSG.Assembly.LargeEven.largeEvenLayer_eq_glaLayer _).trans hS.comp.2)
      have hwstab : MulAut.conj w ∈ CFSG.GroupActions.subgroupStabAut
          ((J.subgroupOf L).map (piCenterQuot θ)) :=
        conj_mem_subgroupStabAut hS hbN θ hwind
      obtain ⟨e, he⟩ := exists_indAut_eq_centerQuotient hS θ w hwind hwstab
      have hKc360 : Nat.card
          (↥((J.subgroupOf L).map (piCenterQuot θ)) ⧸
            Subgroup.center ↥((J.subgroupOf L).map (piCenterQuot θ))) ≠ 360 := by
        intro hc
        exact h360 ((Nat.card_congr e.toEquiv).trans hc)
      have hcKc := hA hτ K p hS.prime hS.odd hG2 hE6 x w hx1 hxp hwp hxw
        ((J.subgroupOf L).map (piCenterQuot θ)) hcomp.1 hKc360 hwstab
      exact (CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr e).1
        (he ▸ hcKc)
  obtain ⟨i₀, hi₀, ⟨eCat⟩⟩ := hcat
  cases i₀ with
  | cyclic _ _ => exact absurd hi₀ (by simp [onLie])
  | alternating _ _ => exact absurd hi₀ (by simp [onLie])
  | sporadic _ => exact absurd hi₀ (by simp [onLie])
  | lie dd =>
    obtain ⟨idx, hv⟩ := dd
    obtain ⟨hPexc, hPchar⟩ := hi₀
    cases idx with
    | G2 q =>
      have hq2 : q.p = 2 := by
        rw [← TauCeti.LieTypeIndex.characteristic_G2]; exact hPchar
      obtain ⟨K, hKf, hKfin, hKcard, hKchar, ⟨eAd⟩⟩ :=
        CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
      letI := hKf
      letI := hKfin
      haveI : CharP K 2 := by rw [← hq2]; exact hKchar
      have h4 : 4 ≤ Nat.card K := by
        rw [hKcard, TauCeti.PrimePower.card_def, hq2]
        have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
          ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
        have hq3 : 3 ≤ 2 ^ q.exponent := by
          have h := hr
          simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at h
          rw [TauCeti.PrimePower.card_def, hq2] at h
          exact h
        have h2 : 2 ≤ q.exponent := by
          by_contra h
          have h1 : q.exponent ≤ 1 := by omega
          have hle : 2 ^ q.exponent ≤ 2 := by
            simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) h1
          omega
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) h2
      exact key .G2 K (Or.inl rfl) (fun _ => h4) (fun h _ => absurd h (by decide))
        ⟨eCat.trans eAd⟩
    | F4 q =>
      have hq2 : q.p = 2 := by
        rw [← TauCeti.LieTypeIndex.characteristic_F4]; exact hPchar
      obtain ⟨K, hKf, hKfin, hKcard, hKchar, ⟨eAd⟩⟩ :=
        CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv
      letI := hKf
      letI := hKfin
      haveI : CharP K 2 := by rw [← hq2]; exact hKchar
      exact key .F4 K (Or.inr (Or.inl rfl)) (fun h => absurd h (by decide))
        (fun h _ => absurd h (by decide)) ⟨eCat.trans eAd⟩
    | E6 q =>
      have hq2 : q.p = 2 := by
        rw [← TauCeti.LieTypeIndex.characteristic_E6]; exact hPchar
      obtain ⟨K, hKf, hKfin, hKcard, hKchar, ⟨eAd⟩⟩ :=
        CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
      letI := hKf
      letI := hKfin
      haveI : CharP K 2 := by rw [← hq2]; exact hKchar
      exact key .E6 K (Or.inr (Or.inr (Or.inl rfl))) (fun h => absurd h (by decide))
        (fun _ hp3 h3 => by
          rw [hKcard] at h3
          exact hshape ⟨.lie ⟨.E6 q, hv⟩, ⟨hp3, hq2, h3⟩, ⟨eCat⟩⟩)
        ⟨eCat.trans eAd⟩
    | E7 q =>
      have hq2 : q.p = 2 := by
        rw [← TauCeti.LieTypeIndex.characteristic_E7]; exact hPchar
      obtain ⟨K, hKf, hKfin, hKcard, hKchar, ⟨eAd⟩⟩ :=
        CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv
      letI := hKf
      letI := hKfin
      haveI : CharP K 2 := by rw [← hq2]; exact hKchar
      exact key .E7 K (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        (fun h => absurd h (by decide)) (fun h _ => absurd h (by decide)) ⟨eCat.trans eAd⟩
    | E8 q =>
      have hq2 : q.p = 2 := by
        rw [← TauCeti.LieTypeIndex.characteristic_E8]; exact hPchar
      obtain ⟨K, hKf, hKfin, hKcard, hKchar, ⟨eAd⟩⟩ :=
        CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv
      letI := hKf
      letI := hKfin
      haveI : CharP K 2 := by rw [← hq2]; exact hKchar
      exact key .E8 K (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
        (fun h => absurd h (by decide)) (fun h _ => absurd h (by decide)) ⟨eCat.trans eAd⟩
    | _ => exact hPexc.elim

theorem innerCompNonShape_excUntwisted_charTwo_of (hA : ExcAdjCompInnAut) (hH : ExcSmallExit) :
    InnerCompNonShape fun i => KD264Lie.isExcUntwistedIdx i ∧ i.characteristic = 2 := by
  intro G _ _ p L J A d b hS hcat hshape hin
  exact exit_of_indAut hH hS hcat hshape hin (indAut_of_adjointModel hA hS hshape hin hcat)

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end

module

public import CFSG.LocalAnalysis.GLTheoremA.S4S.Prop415Hat
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RankOneAutomorphisms
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Prop415Base

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem mem_glaPPrimeCore_of_mem {p : ℕ} {L : Subgroup G} {y : G} (hy : y ∈ L)
    (h : y ∈ GLAPPrimeCoreOf p L) : (⟨y, hy⟩ : ↥L) ∈ GLAPPrimeCore p ↥L := by
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 h
  have hzeq : z = ⟨y, hy⟩ := Subtype.ext hzy
  rw [← hzeq]
  exact hz

private theorem centMod_mk_mem_center {p : ℕ} {L : Subgroup G} {a : G} (ha : a ∈ L)
    (hc : a ∈ centModSubgroup p L) :
    (QuotientGroup.mk (⟨a, ha⟩ : L) : PQuot p L) ∈ Subgroup.center (PQuot p L) := by
  have hN : a ∈ Subgroup.normalizer (GLAPPrimeCoreOf p L : Set G) :=
    normalizer_le_normalizer_glaPPrimeCoreOf p L (mem_centModSubgroup.1 hc).1
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk_surjective g
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  have e : (l * a)⁻¹ * (a * l) = a⁻¹ * ⁅l⁻¹, a⁆ * a := by
    simp only [commutatorElement_def]
    group
  have hcomm : ⁅l⁻¹, a⁆ ∈ GLAPPrimeCoreOf p L := (mem_centModSubgroup.1 hc).2 l⁻¹ (L.inv_mem hl)
  have hconj := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hN) _).1 hcomm
  rw [inv_inv] at hconj
  have hmem : (l * a)⁻¹ * (a * l) ∈ GLAPPrimeCoreOf p L := by
    rw [e]
    exact hconj
  exact mem_glaPPrimeCore_of_mem _ hmem

theorem exists_Bstar {B : Subgroup G} {x : G} {L : Subgroup G} (hBel : IsElemAbelian 3 B)
    (hxB : x ∈ B) (hL : GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) L)
    (hBL : B ≤ Subgroup.normalizer (L : Set G)) (hM12 : catalogIs (PSimple 3 L) isM12)
    (h1016 : I1016At G) (h71 : I71M12At G) :
    ∃ Bs D U : Subgroup G, IsElemAbelian 3 Bs ∧ x ∈ Bs ∧
      Bs ≤ Subgroup.normalizer (L : Set G) ∧ Nat.card B ≤ Nat.card Bs ∧ D ≤ Bs ∧ D ≤ L ∧
      IsElemAbelian 3 D ∧ Nat.card D = 9 ∧ Subgroup.center (PQuot 3 L) = ⊥ ∧ U ≤ L ∧
      IsPGroup 2 U ∧ Bs ≤ Subgroup.normalizer (U : Set G) ∧ ¬ U ≤ GLAPPrimeCoreOf 3 L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨A, hAdef⟩ : ∃ A : Subgroup G, A = B ⊓ centModSubgroup 3 L := ⟨_, rfl⟩
  have hmemA : ∀ a, a ∈ A ↔ a ∈ B ∧ a ∈ centModSubgroup 3 L := fun a => by
    rw [hAdef, Subgroup.mem_inf]
  have hAel : IsElemAbelian 3 A := isElemAbelian_mono hBel (fun a ha => ((hmemA a).1 ha).1)
  have hAN : A ≤ Subgroup.normalizer (L : Set G) := fun a ha => hBL ((hmemA a).1 ha).1
  have hAC : ∀ a ∈ A, CentMod 3 L a := fun a ha => centMod_iff.2 ((hmemA a).1 ha).2
  obtain ⟨hZ, D, hDC, hDel, hDc, U, hUL, hU2, hAD, hUO⟩ :=
    h1016 (Subgroup.centralizer ({x} : Set G)) L A hL hM12 hAel hAN hAC
  have hDL : D ≤ L := hDC.trans inf_le_left
  have hDCA : D ≤ Subgroup.centralizer (A : Set G) := hDC.trans inf_le_right
  have hADN : D ≤ Subgroup.normalizer (A : Set G) :=
    hDCA.trans (Subgroup.centralizer_le_normalizer _)
  have hADc : A ≤ Subgroup.centralizer (D : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun d hd =>
      ((Subgroup.mem_centralizer_iff.1 (hDCA hd)) a ha).symm
  have hAD' : IsElemAbelian 3 (A ⊔ D) := isElemAbelian_sup_of_commute hAel hDel hADc
  have hxA : x ∈ A := by
    refine (hmemA x).2 ⟨hxB, ?_⟩
    have hxC : x ∈ Subgroup.centralizer (L : Set G) :=
      Subgroup.mem_centralizer_iff.2 fun l hl => Subgroup.mem_centralizer_singleton_iff.1 (hL.1 hl)
    exact centMod_iff.1 (centMod_of_mem_centralizer hxC)
  have hAD0 : A ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    rintro a ⟨haA, haD⟩
    have haL : a ∈ L := hDL haD
    have h1 : (QuotientGroup.mk (⟨a, haL⟩ : L) : PQuot 3 L) = 1 := by
      have hc := centMod_mk_mem_center haL ((hmemA a).1 haA).2
      rw [hZ] at hc
      exact (Subgroup.mem_bot).1 hc
    have hcore : (⟨a, haL⟩ : ↥L) ∈ GLAPPrimeCore 3 ↥L := (QuotientGroup.eq_one_iff _).1 h1
    have hO : a ∈ GLAPPrimeCoreOf 3 L := Subgroup.mem_map.2 ⟨⟨a, haL⟩, hcore, rfl⟩
    have hord : orderOf a ∣ 3 := orderOf_dvd_of_pow_eq_one (hDel.2 a haD)
    have hdvd : orderOf a ∣ Nat.card ↥(GLAPPrimeCoreOf 3 L) := by
      rw [← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.2 hO)
    have hcop : Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCoreOf 3 L)) :=
      CFSG.HardMathSupport.Timmesfeld.Proving.coprime_card_GLAPPrimeCoreOf Nat.prime_three L
    have hg : orderOf a ∣ Nat.gcd 3 (Nat.card ↥(GLAPPrimeCoreOf 3 L)) := Nat.dvd_gcd hord hdvd
    rw [hcop.gcd_eq_one] at hg
    rw [Subgroup.mem_bot]
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hg)
  have hcard : Nat.card (A ⊔ D : Subgroup G) * Nat.card (A ⊓ D : Subgroup G) =
      Nat.card A * Nat.card D :=
    card_sup_mul_card_inf_of_le_normalizer hADN
  rw [hAD0, Subgroup.card_bot, mul_one, hDc] at hcard
  have h71' : Nat.card B ≤ 9 * Nat.card A := by
    have := h71 (Subgroup.centralizer ({x} : Set G)) L B hL hM12 hBel hBL
    rw [hAdef]
    exact this
  have hBA : Nat.card B ≤ Nat.card (A ⊔ D : Subgroup G) := by
    rw [hcard, mul_comm]
    exact h71'
  have hBsN : A ⊔ D ≤ Subgroup.normalizer (L : Set G) :=
    sup_le hAN (hDL.trans Subgroup.le_normalizer)
  exact ⟨A ⊔ D, D, U, hAD', Subgroup.mem_sup_left hxA, hBsN, hBA, le_sup_right, hDL, hDel, hDc,
    hZ, hUL, hU2, hAD, hUO⟩

private theorem pCore_ne_top_of_quasisimple {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.Open.IsQuasisimple Q) : CFSG.pCore p Q ≠ ⊤ := by
  intro h
  haveI : Nontrivial Q := isQuasisimple_nontrivial hQ
  haveI : Group.IsPerfect Q := Group.isPerfect_def.2 hQ.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p Q := fun g => by
    have hg : g ∈ CFSG.pCore p Q := h ▸ Subgroup.mem_top g
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := p) (G := Q)) ⟨g, hg⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  exact Group.IsPerfect.not_isNilpotent Q (IsPGroup.isNilpotent hpg)

private theorem mem_oPPrimeP_413 {p : ℕ} {X : Subgroup G} {y : G} :
    y ∈ oPPrimeP p X ↔ ∃ h : y ∈ X,
      QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨y, h⟩ ∈ CFSG.pCore p (↥X ⧸ GLAPPrimeCore p ↥X) := by
  unfold oPPrimeP
  simp [Subgroup.mem_map]

private theorem eq_one_of_mem_glaPPrimeCoreOf {p : ℕ} (hp : p.Prime) {L : Subgroup G} {a : G}
    (hO : a ∈ GLAPPrimeCoreOf p L) (hap : a ^ p = 1) : a = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf a ∣ p := orderOf_dvd_of_pow_eq_one hap
  have hdvd : orderOf a ∣ Nat.card ↥(GLAPPrimeCoreOf p L) := by
    rw [← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.2 hO)
  have hcop : Nat.Coprime p (Nat.card ↥(GLAPPrimeCoreOf p L)) :=
    CFSG.HardMathSupport.Timmesfeld.Proving.coprime_card_GLAPPrimeCoreOf hp L
  have hg : orderOf a ∣ Nat.gcd p (Nat.card ↥(GLAPPrimeCoreOf p L)) := Nat.dvd_gcd hord hdvd
  rw [hcop.gcd_eq_one] at hg
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hg)

private theorem eq_one_of_mem_oPPrimeP {p : ℕ} (hp : p.Prime) {L : Subgroup G}
    (hQ : CFSG.Open.IsQuasisimple (PQuot p L)) (hZ : Subgroup.center (PQuot p L) = ⊥) {d : G}
    (hd : d ∈ oPPrimeP p L) (hdp : d ^ p = 1) : d = 1 := by
  obtain ⟨h, hmem⟩ := mem_oPPrimeP_413.1 hd
  have hcent : QuotientGroup.mk' (GLAPPrimeCore p ↥L) ⟨d, h⟩ ∈ Subgroup.center (PQuot p L) :=
    le_center_of_normal_of_isQuasisimple hQ (inferInstance : (CFSG.pCore p (PQuot p L)).Normal)
      (pCore_ne_top_of_quasisimple hp hQ) hmem
  rw [hZ] at hcent
  have hcore : (⟨d, h⟩ : ↥L) ∈ GLAPPrimeCore p ↥L := (QuotientGroup.eq_one_iff _).1 (Subgroup.mem_bot.1 hcent)
  exact eq_one_of_mem_glaPPrimeCoreOf hp (Subgroup.mem_map.2 ⟨⟨d, h⟩, hcore, rfl⟩) hdp

private def conjSubgroupEquiv {R : Subgroup G} {d : G} (hd : d ∈ Subgroup.normalizer (R : Set G)) :
    R ≃* R where
  toFun r := ⟨d * r * d⁻¹, (Subgroup.mem_normalizer_iff.1 hd r).1 r.2⟩
  invFun r := ⟨d⁻¹ * r * d, by
    simpa using (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hd) r).1 r.2⟩
  left_inv r := Subtype.ext (by simp [mul_assoc])
  right_inv r := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

private def tauAut {R : Subgroup G} (e : R ≃* QuaternionGroup 2) {d : G}
    (hd : d ∈ Subgroup.normalizer (R : Set G)) : MulAut (QuaternionGroup 2) :=
  e.symm.trans ((conjSubgroupEquiv hd).trans e)

private def actD {R D : Subgroup G} (e : R ≃* QuaternionGroup 2)
    (hDN : D ≤ Subgroup.normalizer (R : Set G)) : ↥D →* MulAut (QuaternionGroup 2) where
  toFun d := tauAut e (hDN d.2)
  map_one' := by
    ext q
    simp [tauAut, conjSubgroupEquiv]
  map_mul' a b := by
    ext q
    simp [tauAut, conjSubgroupEquiv, mul_assoc]

theorem faithful_D_on_R {X L D R Bs : Subgroup G} (hL : GLAPComponent 3 X L)
    (hcat : catalogIs (PSimple 3 L) isM12)
    (hZ : Subgroup.center (PQuot 3 L) = ⊥) (hDL : D ≤ L) (hDel : IsElemAbelian 3 D)
    (hDc : Nat.card D = 9) (hDBs : D ≤ Bs) (hBsR : Bs ≤ Subgroup.normalizer (R : Set G))
    (hR2 : IsPGroup 2 R) (hCR : L ⊓ Subgroup.centralizer (R : Set G) ≤ oPPrimeP 3 L) :
    (⁅R, Bs⁆ : Subgroup G) ≠ ⊥ ∧ IsEmpty (R ≃* QuaternionGroup 2) := by
  have hQ : CFSG.Open.IsQuasisimple (PQuot 3 L) :=
    isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hL
  have hCD : D ⊓ Subgroup.centralizer (R : Set G) = ⊥ := by
    rw [eq_bot_iff]
    rintro d ⟨hdD, hdC⟩
    rw [Subgroup.mem_bot]
    have hdO : d ∈ oPPrimeP 3 L := hCR ⟨hDL hdD, hdC⟩
    exact eq_one_of_mem_oPPrimeP Nat.prime_three hQ hZ hdO (hDel.2 d hdD)
  have hDN : D ≤ Subgroup.normalizer (R : Set G) := hDBs.trans hBsR
  refine ⟨?_, ⟨fun e => ?_⟩⟩
  ·
    intro hbot
    have hBC : Bs ≤ Subgroup.centralizer (R : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 (by rw [Subgroup.commutator_comm]; exact hbot)
    have hDC : D ≤ D ⊓ Subgroup.centralizer (R : Set G) := le_inf le_rfl (hDBs.trans hBC)
    rw [hCD] at hDC
    have h0 : D = ⊥ := le_bot_iff.1 hDC
    rw [h0, Subgroup.card_bot] at hDc
    exact absurd hDc (by norm_num)
  ·
    have hinj : Function.Injective (actD e hDN) := by
      rw [injective_iff_map_eq_one]
      intro d hd
      have hdC : (d : G) ∈ Subgroup.centralizer (R : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro r hr
        have h1 := congrArg (fun φ : MulAut (QuaternionGroup 2) => φ (e ⟨r, hr⟩)) hd
        simp [actD, tauAut, conjSubgroupEquiv] at h1
        exact (mul_inv_eq_iff_eq_mul.1 h1).symm
      have hdD : (d : G) ∈ D ⊓ Subgroup.centralizer (R : Set G) := ⟨d.2, hdC⟩
      rw [hCD, Subgroup.mem_bot] at hdD
      exact Subtype.ext hdD
    have hcore : IsPGroup 2 (QuaternionGroup 2) := by
      have := CFSG.ProperTwoGeneratedCore.quaternion_power_two_isPGroup 1
      simpa using this
    have hinj2 := CFSG.LargeEvenClassification.Helpers.frattiniAutAction_odd_injective
      Nat.prime_two Nat.prime_three (by norm_num) hcore (isPGroup_of_isElemAbelian hDel)
      (actD e hDN) hinj
    have htp : Function.Injective
        (MulAut.toPerm (M := QuaternionGroup 2 ⧸ frattini (QuaternionGroup 2))) :=
      fun f g h => MulEquiv.ext fun x => congrArg (fun σ : Equiv.Perm _ => σ x) h
    have hΦ : Function.Injective
        ((MulAut.toPerm (M := QuaternionGroup 2 ⧸ frattini (QuaternionGroup 2))).comp
          ((CFSG.LargeEvenClassification.Helpers.frattiniAutAction (QuaternionGroup 2)).comp
            (actD e hDN))) := htp.comp hinj2
    have hdvd := Subgroup.card_dvd_of_injective _ hΦ
    rw [Nat.card_perm, hDc] at hdvd
    have hcard : Nat.card (QuaternionGroup 2 ⧸ frattini (QuaternionGroup 2)) ≤ 4 := by
      have := CFSG.ProperTwoGeneratedCore.quaternion_frattini_quotient_card_le_four 1
      simpa using this
    generalize Nat.card (QuaternionGroup 2 ⧸ frattini (QuaternionGroup 2)) = n at hdvd hcard
    interval_cases n <;> norm_num [Nat.factorial] at hdvd

theorem m12_adjust {m : ℕ} (hctx : ThmACtx G m) {p : ℕ} (hp : p ∈ Mu G m)
    (h1810 : I1810UsedAt G p) (h1016 : I1016At G) (h71 : I71M12At G) {B : Subgroup G} {x : G}
    {L : Subgroup G} (hD3 : D3Data G p B x L) (hM12 : catalogIs (PSimple p L) isM12) :
    ∃ Bs : Subgroup G, D3Data G p Bs x L ∧ ∃ U : Subgroup G, U ≤ L ∧ IsPGroup 2 U ∧
      Bs ≤ Subgroup.normalizer (U : Set G) ∧ ¬ U ≤ GLAPPrimeCoreOf p L := by
  have hp3 := hD3.p_eq
  subst hp3
  have hpp : Nat.Prime 3 := hp.1.1
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨hB, hess, hL⟩ := hD3.isS0.1
  have hxB : x ∈ B := hess.1
  have hx1 : x ≠ 1 := hess.2.1
  have hBel : IsElemAbelian 3 B := hB.1
  have hBL := hD3.bnormL
  obtain ⟨Bs, D, U, hBsel, hxBs, hBsL, hcard, hDBs, hDL, hDel, hDc, hZ, hUL, hU2, hBsU, hUO⟩ :=
    exists_Bstar hBel hxB hL hBL hM12 h1016 h71
  have hYK : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x} : Set G)) :=
    hctx.1.kProper.isKGroup _ (centralizer_ne_top_of_ne_one hctx.1.simple hctx.1.nonabelian hx1)
  obtain ⟨X, R, hXL, hLX, hXO', hXOx, hBsX, hcopX, hRX, hR2, hRidx, hBsR, hR1, hCR⟩ :=
    exists_R_data hpp hp2 h1810 hBsel hxBs hYK hL hBsL hD3.evenX
  obtain ⟨hRne, hQ8⟩ := faithful_D_on_R hL hM12 hZ hDL hDel hDc hDBs hBsR hR2 hCR
  have hBsB : GLAIsBmax 3 Bs := by
    refine ⟨hBsel, ?_, R, hR1, hR2, hBsR⟩
    have h1 := card_le_pow_glaTwoLocalRank hpp hBsel hR1 hR2 hBsR
    have h2 : Nat.card B ≤ Nat.card Bs := hcard
    rw [hB.2.1] at h2
    exact le_antisymm h1 h2
  have hess' : IsEssential 3 Bs x := by
    refine ⟨hxBs, hx1, R, ?_, hR2, hBsR, hRne, fun _ => hQ8⟩
    intro r hr
    exact hL.1 (hXL (hRX hr))
  exact ⟨Bs, D3Data.of_core hpp hp2 rfl hBsB hess' hL hBsL hD3.lev hD3.hd hD3.evenX, U, hUL,
    hU2, hBsU, hUO⟩

theorem prop415_pre {m : ℕ} (hctx : ThmACtx G m) {p : ℕ} (hp : p ∈ Mu G m)
    (h1810 : I1810UsedAt G p) (h145 : I145UsedAt G p) (h1426 : I1426At G p) {B : Subgroup G}
    {x : G} {L : Subgroup G} (hD3 : D3Data G p B x L)
    (hM12 : catalogIs (PSimple p L) isM12 → ∃ U : Subgroup G, U ≤ L ∧ IsPGroup 2 U ∧
      B ≤ Subgroup.normalizer (U : Set G) ∧ ¬ U ≤ GLAPPrimeCoreOf p L) :
    ∃ D S Ss : Subgroup G, Prop415Pre B x D S Ss := by
  have hp3 := hD3.p_eq
  subst hp3
  have hpp : Nat.Prime 3 := hp.1.1
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hΔ : GLADeltaZero G 3 := hp.2.2
  obtain ⟨hB, hess, hL⟩ := hD3.isS0.1
  have hxB : x ∈ B := hess.1
  have hx1 : x ≠ 1 := hess.2.1
  have hBel : IsElemAbelian 3 B := hB.1
  have hBL := hD3.bnormL
  have hSC : IsSC 3 B := hD3.sc
  set Cx : Subgroup G := Subgroup.centralizer ({x} : Set G) with hCx
  have hBCx : B ≤ Cx := isElemAbelian_le_centralizer hBel hxB
  have hYK : CFSG.Open.IsKGroup ↥Cx :=
    hctx.1.kProper.isKGroup Cx (centralizer_ne_top_of_ne_one hctx.1.simple hctx.1.nonabelian hx1)
  obtain ⟨X, R, hXL, hLX, hXO', hXOx, hBX, hcopX, hRX, hR2, hRidx, hBR, hR1, hCR⟩ :=
    exists_R_data hpp hp2 h1810 hBel hxB hYK hL hBL hD3.evenX
  have hall : ∀ E : Subgroup G, E ≤ B → IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      GLAPLayer 3 (L ⊓ Subgroup.centralizer (E : Set G)) = ⊥ := by
    intro E hEB hEel hEc
    by_contra hne
    exact hD3.noG ⟨E, hEB, hEel, hEc, by rwa [closureIn_eq_self hBL]⟩
  have h4 : 3 ^ 4 ≤ Nat.card B := by
    have hm4 : 4 ≤ GLATwoLocalRank 3 G := by
      rw [hp.2.1]
      exact hctx.1.four_le
    rw [hB.2.1]
    exact Nat.pow_le_pow_right hpp.pos hm4
  obtain ⟨hB81, A, J₁, T₁, hAB, hAel, hAc, hJ₁eq, hJ₁comp, hcat, hCM, hT₁J, hT₁2, hBT₁, hBT₁',
      hT₁el, hT₁c, hO₁⟩ :=
    h1426 rfl B x L hBel hxB hx1 hL hBL hD3.lev h4 hD3.maxRank hall hM12
  have hOnL : B ≤ Subgroup.normalizer (GLAPPrimeCoreOf 3 L : Set G) :=
    hBL.trans (normalizer_le_normalizer_glaPPrimeCoreOf 3 L)
  obtain ⟨Rs, hRRs, hRsO, hRs2, hRsidx, hBRs⟩ := exists_invariant_sylow_ge hpp hp2
    (isPGroup_of_isElemAbelian hBel) hOnL
    (CFSG.HardMathSupport.Timmesfeld.Proving.coprime_card_GLAPPrimeCoreOf hpp L)
    (hRX.trans hXO') hR2 hBR
  have hBCA : B ≤ Subgroup.centralizer (A : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact isElemAbelian_commute hBel (hAB ha) hg
  have hJ₁ne : J₁ ≠ ⊥ := glaPComponent_ne_bot' hJ₁comp
  have hZ : GLAPLayer 3 (L ⊓ Subgroup.centralizer (A : Set G)) ≠ ⊥ := by
    rw [← hJ₁eq]
    exact hJ₁ne
  have hLlay : GLAPLayer 3 L = L := by
    have h := (layer_closureIn hpp hL (hBCx.trans Subgroup.le_normalizer)).2.2.2
    rwa [closureIn_eq_self hBL] at h
  obtain ⟨J, hJL, hJR, hJA, hBJ, hJ1, hJlay, hJle, hJcov⟩ :=
    exists_J_data hpp hp2 hLlay hBL hBel hAB (Subgroup.map_subtype_le _)
      (le_normalizer_glaPPrimeCoreOf 3 L) le_rfl hRs2 hRsO hRsidx hBRs hZ
  have hJJ₁ : J ≤ J₁ := by
    rw [hJ₁eq]
    exact hJle
  have hJ₁L : J₁ ≤ L := hJ₁comp.1.trans inf_le_left
  have hBJ₁ : B ≤ Subgroup.normalizer (J₁ : Set G) := by
    rw [hJ₁eq]
    exact fun b hb => mem_normalizer_glaPLayer
      (le_normalizer_inf hBL (hBCA.trans Subgroup.le_normalizer) hb)
  have hJcov' : J₁ ≤ J ⊔ GLAPPrimeCoreOf 3 L := by
    rw [hJ₁eq]
    exact hJcov
  obtain ⟨T, hTJ, hT2, hBT, hRsT, hRsTn, hTcard, hAT, hBTnc, hTO⟩ :=
    exists_T_data hBel hAB hBL hRsO hRs2 hRsidx hBRs hJL hJR hJA hBJ hJlay hJJ₁ hJ₁L hBJ₁ hJcov'
      hO₁ hT₁J hT₁2 hBT₁ hBT₁' ⟨hT₁el, hT₁c⟩
  have hxA : x ∈ A := by
    refine (hCM x hxB).1 ⟨hBJ₁ hxB, ?_⟩
    have hJ₁C : J₁ ≤ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact hJ₁L.trans hL.1
    rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).2 hJ₁C]
    exact bot_le
  have hCA2 : IsPGroup 2 (Rs ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) :=
    hRs2.to_le inf_le_left
  have hBCn : B ≤ Subgroup.normalizer ((Rs ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf hBRs (hBCA.trans Subgroup.le_normalizer)
  have hJCn : J ≤ Subgroup.normalizer ((Rs ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf hJR (hJA.trans Subgroup.le_normalizer)
  have hACx : Subgroup.centralizer (A : Set G) ≤ Cx := Subgroup.centralizer_le (by
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact hxA)
  have hJΛ : J ≤ GLAPLayer 3 (Subgroup.centralizer (A : Set G)) := by
    have h1 := layer_inf_centralizer_le (p := 3) hpp (E := A) hL (bot_le.trans Subgroup.le_normalizer
      : (⊥ : Subgroup G) ≤ Subgroup.normalizer (Cx : Set G))
    rw [closureIn_eq_self (bot_le.trans Subgroup.le_normalizer : (⊥ : Subgroup G) ≤
      Subgroup.normalizer (L : Set G)), inf_eq_right.2 hACx] at h1
    have h2 : J₁ ≤ GLAPLayer 3 (Subgroup.centralizer (A : Set G)) := by
      rw [hJ₁eq]
      exact h1
    exact hJJ₁.trans h2
  have hCO : Rs ⊓ Subgroup.centralizer (A : Set G) ≤
      GLAPPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := by
    intro g hg
    have h1 : g ∈ GLAPPrimeCoreOf 3 Cx :=
      CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCoreOf_le_of_isSubnormal hpp hL.2.1 (hRsO hg.1)
    exact inf_glaPPrimeCoreOf_le hpp hACx (Subgroup.mem_inf.2 ⟨hg.2, h1⟩)
  have hCΔ : (⁅Rs ⊓ Subgroup.centralizer (A : Set G), J⁆ : Subgroup G) ≤ GLADelta 3 A := by
    refine le_iInf fun a => le_iInf fun haA => le_iInf fun ha1 => ?_
    have hAa : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({a} : Set G) :=
      Subgroup.centralizer_le (by
        intro g hg
        rw [Set.mem_singleton_iff] at hg
        rw [hg]
        exact haA)
    have hYa : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({a} : Set G)) :=
      hctx.1.kProper.isKGroup _ (centralizer_ne_top_of_ne_one hctx.1.simple hctx.1.nonabelian ha1)
    have hAle : A ≤ Subgroup.centralizer ({a} : Set G) := by
      intro g hg
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact isElemAbelian_commute hBel (hAB hg) (hAB haA)
    have h := h145 hpp hp2 (Subgroup.centralizer ({a} : Set G)) A hYa hAle
      (isPGroup_of_isElemAbelian hAel)
    rw [inf_eq_right.2 hAa] at h
    calc (⁅Rs ⊓ Subgroup.centralizer (A : Set G), J⁆ : Subgroup G)
        = ⁅J, Rs ⊓ Subgroup.centralizer (A : Set G)⁆ := Subgroup.commutator_comm _ _
      _ ≤ ⁅GLAPLayer 3 (Subgroup.centralizer (A : Set G)),
            GLAPPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))⁆ :=
          Subgroup.commutator_mono hJΛ hCO
      _ ≤ _ := h
  have hAc' : Nat.card A = 3 ^ 2 := by rw [hAc]; norm_num
  have hJC : (⁅Rs ⊓ Subgroup.centralizer (A : Set G), J⁆ : Subgroup G) = ⊥ :=
    layer_commutator_eq_bot hpp hp2 hΔ hB hSC hAB hAel hAc' hBJ hJlay hCA2 hBCn hJCn hCΔ
  have hAR : A ≤ Subgroup.normalizer (Rs : Set G) := hAB.trans hBRs
  obtain ⟨hNn, hBN⟩ := normal_hatN hRsT hRsTn hTJ hJR hJA hJC hBT hBRs hAB hBel
  have hCL : L ⊓ Subgroup.centralizer (Rs : Set G) ≤ oPPrimeP 3 L :=
    fun g hg => hCR ⟨hg.1, Subgroup.centralizer_le hRRs hg.2⟩
  have hhat : HatSetup B A T Rs (hatN Rs A) := by
    refine ⟨hBel, hB81, hAB, hAel, hAc, hT2, ?_, hRsT, hNn, hRsTn, hBT, hBRs, hBN, ?_,
      faithful_mod hJL hJlay hJR hJA hJC hAR hRs2 hRsT hT2 hTJ hNn hCL hTO hAel, hTcard, hAT, hBTnc,
      fpf_mod hRs2 hAel hAR⟩
    · exact hatN_le Rs A
    · exact ⟨(commutator_le_frat2 Rs).trans (frat2_le_hatN Rs A), fun r hr =>
        frat2_le_hatN Rs A (sq_mem_frat2 hr)⟩
  obtain ⟨D, S, hDB, hDel, hDc, hST, hBS, hBSS, hSSR, hne, hidx⟩ := abstract_hat hhat
  refine ⟨D, S, S ⊓ Rs, ?_⟩
  exact ⟨hDB, hDel, hDc, hT2.to_le (hST.trans inf_le_left), hBS, hBSS, hST.trans inf_le_right,
    inf_le_left, le_normalizer_inf hBS hBRs,
    inf_le_right.trans (hRsO.trans
      (CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCoreOf_le_of_isSubnormal hpp hL.2.1)),
    hidx, le_inf (commutator_self_le S) hSSR, hne⟩

end CFSG.LocalAnalysis.GLTheoremA

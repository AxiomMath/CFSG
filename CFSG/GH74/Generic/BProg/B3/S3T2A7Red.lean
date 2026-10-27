module

public import CFSG.GH74.Generic.BProg.B3.S3T2A7Defs
public import CFSG.GH74.Generic.BProg.B3.ObsPump
public import CFSG.GH74.Generic.BProg.B3.S3BootDefs

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3T2A7

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1 CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification
open scoped commutatorElement

@[expose] def A7Bridge (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (x : G) (K A B M : Subgroup G) (a : G) (D J : Subgroup G), Boot15B G x K A B M →
    a ∈ A → Obs32 A a D J → IsA7A11Quot (kBar J) →
      Nonempty ((↥J ⧸ pPrimeCore 2 ↥J) ≃* alternatingGroup (Fin 7))

theorem isA7A11Quot_of_equiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    (h : IsA7A11Quot X') : IsA7A11Quot X := by
  let φ : X ⧸ center X ≃* X' ⧸ center X' :=
    QuotientGroup.congr (center X) (center X') e (Subgroup.map_center_eq e)
  rcases h with h | h
  · obtain ⟨ψ⟩ := h
    exact Or.inl ⟨φ.trans ψ⟩
  · obtain ⟨ψ⟩ := h
    exact Or.inr ⟨φ.trans ψ⟩

variable {G : Type} [Group G] [Finite G]

theorem sectional_barQ (h4 : SectionalTwoRankLE G 4) (C : Subgroup G) :
    SectionalTwoRankLE (barQ ↥C) 4 :=
  SectionalTwoRankLE.quotient _ (SectionalTwoRankLE.subgroup _ h4)

omit [Finite G] in
theorem secGH_barQ (hK : KGH G) {C : Subgroup G} (hC : C ≠ ⊤) : SecGH (barQ ↥C) := by
  intro H N _ hs hn
  let π : ↥C →* barQ ↥C := barMk ↥C
  let Hpre : Subgroup ↥C := H.comap π
  let H' : Subgroup G := Hpre.map C.subtype
  have hH'C : H' ≤ C := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  have hH' : H' ≠ ⊤ := fun h => hC (top_le_iff.1 (h ▸ hH'C))
  let e₁ : ↥Hpre ≃* ↥H' := Hpre.equivMapOfInjective C.subtype C.subtype_injective
  let q : ↥Hpre →* ↥H := (π.comp Hpre.subtype).codRestrict H fun k => k.2
  have hq : Function.Surjective q := by
    intro k
    obtain ⟨c, hc⟩ := barMk_surjective (k : barQ ↥C)
    exact ⟨⟨c, show π c ∈ H by rw [hc]; exact k.2⟩, Subtype.ext hc⟩
  let f : ↥H' →* ↥H ⧸ N := ((QuotientGroup.mk' N).comp q).comp e₁.symm.toMonoidHom
  have hf : Function.Surjective f :=
    ((QuotientGroup.mk'_surjective _).comp hq).comp e₁.symm.surjective
  exact Generic.ghList_of_surjection hK hH' f hf hs hn

omit [Finite G] in
theorem centralizer_ne_top (hG : IsSimpleGroup G) (hnab : ∃ u v : G, u * v ≠ v * u) {a : G}
    (ha : a ≠ 1) : centralizer ({a} : Set G) ≠ ⊤ := by
  intro htop
  have hZ : a ∈ center G := Subgroup.mem_center_iff.mpr fun g =>
    mem_centralizer_singleton_iff.mp (htop ▸ Subgroup.mem_top g)
  rcases hG.eq_bot_or_eq_top_of_normal (center G) with h | h
  · exact ha (Subgroup.mem_bot.mp (h ▸ hZ))
  · obtain ⟨u, v, huv⟩ := hnab
    exact huv (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top v) u)

omit [Finite G] in
theorem isElementaryAbelian_of_forall {X : Type*} [Group X] {U : Subgroup X}
    (hab : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) (hsq : ∀ u ∈ U, u * u = 1) :
    CFSG.IsElementaryAbelian 2 ↥U := by
  have : IsMulCommutative ↥U := ⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, sq]
  exact hsq a a.2

omit [Finite G] in
theorem bar_isElementaryAbelian {a : G} {B : Subgroup G} (hBel : CFSG.IsElementaryAbelian 2 ↥B) :
    CFSG.IsElementaryAbelian 2 ↥(PumpCalc.bar a B) := by
  obtain ⟨hc, hsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  refine isElementaryAbelian_of_forall ?_ ?_
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc _ (Subgroup.mem_subgroupOf.mp hu) _ (Subgroup.mem_subgroupOf.mp hv))
  · rintro _ ⟨u, hu, rfl⟩
    rw [← map_mul]
    have : u * u = 1 := Subtype.ext (hsq _ (Subgroup.mem_subgroupOf.mp hu))
    rw [this, map_one]

theorem pRank_bar {a : G} {B : Subgroup G} (hBel : CFSG.IsElementaryAbelian 2 ↥B)
    (hBC : B ≤ centralizer ({a} : Set G)) {k : ℕ} (hk : pRank 2 ↥B = k) :
    pRank 2 ↥(PumpCalc.bar a B) = k := by
  obtain ⟨-, hsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  have := bar_isElementaryAbelian (a := a) hBel
  refine CFSG.pRank_eq_of_card_eq_pow one_lt_two ?_
  rw [Th2.Bal.card_map_piBar hsq hBC, C3.Layer1.Back.card_eq_two_pow_pRank hBel, hk]

theorem bar_self_ne_one {a : G} (ha2 : orderOf a = 2) (haC : a ∈ centralizer ({a} : Set G)) :
    barMk ↥(centralizer ({a} : Set G)) ⟨a, haC⟩ ≠ 1 := by
  intro h1
  have h2 : (⟨a, haC⟩ : ↥(centralizer ({a} : Set G))) * ⟨a, haC⟩ = 1 := by
    apply Subtype.ext
    have h := pow_orderOf_eq_one a
    rw [ha2, sq] at h
    exact h
  have ha1 : a ≠ 1 := fun h => by simp [h] at ha2
  exact ha1 (congrArg Subtype.val
    (Th2.Bal.eq_one_of_sq_of_mem_pPrimeCore h2 (Th2.Bal.piBar_eq_one_iff.mp h1)))

omit [Finite G] in
theorem bar_self_mem_center {a : G} (haC : a ∈ centralizer ({a} : Set G)) :
    barMk ↥(centralizer ({a} : Set G)) ⟨a, haC⟩ ∈ center (barQ ↥(centralizer ({a} : Set G))) := by
  refine Subgroup.mem_center_iff.mpr fun g => ?_
  obtain ⟨y, rfl⟩ := barMk_surjective g
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_singleton_iff.mp y.2)

theorem gammaK_bar_le {a : G} {B M : Subgroup G} (hBel : CFSG.IsElementaryAbelian 2 ↥B)
    (hγ : gammaK 2 B 3 ≤ M) :
    gammaK 2 (PumpCalc.bar a B) 3 ≤ PumpCalc.bar a M := by
  classical
  set C : Subgroup G := centralizer ({a} : Set G) with hC
  obtain ⟨-, hsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  refine iSup_le fun Q => iSup_le fun hQB => iSup_le fun hQr => ?_
  set E' : Subgroup ↥C := B.subgroupOf C ⊓ Q.comap (barMk ↥C) with hE'
  have hmapE : E'.map (barMk ↥C) = Q := by
    apply le_antisymm
    · rintro _ ⟨e, he, rfl⟩
      exact he.2
    · intro q hq
      obtain ⟨b, hb, rfl⟩ := hQB hq
      exact ⟨b, ⟨hb, hq⟩, rfl⟩
  have hE'2 : IsPGroup 2 ↥E' := fun g => ⟨1, by
    rw [pow_one, sq]
    exact Subtype.ext (Subtype.ext (hsq _ (Subgroup.mem_subgroupOf.mp g.2.1)))⟩
  have himg := OddKernelNormalizers.image (barMk ↥C) barMk_surjective odd_card_ker_barMk E' hE'2
  rw [hmapE] at himg
  rw [← himg]
  refine Subgroup.map_mono fun c hc => Subgroup.mem_subgroupOf.mpr (hγ ?_)
  set E : Subgroup G := E'.map C.subtype with hE
  have hEB : E ≤ B := by
    rintro _ ⟨e, he, rfl⟩
    exact Subgroup.mem_subgroupOf.mp he.1
  have hEel : CFSG.IsElementaryAbelian 2 ↥E := Th2Sig6.isElementaryAbelian_of_le hBel hEB
  have hQel : CFSG.IsElementaryAbelian 2 ↥Q :=
    Th2Sig6.isElementaryAbelian_of_le (bar_isElementaryAbelian hBel) hQB
  have hinj : Function.Injective ((barMk ↥C).comp E'.subtype) := fun x y hxy =>
    Subtype.ext (Th2.Bal.piBar_injOn hsq x.2.1 y.2.1 hxy)
  have hr : ((barMk ↥C).comp E'.subtype).range = E'.map (barMk ↥C) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcQ : Nat.card ↥Q = Nat.card ↥E' := by
    rw [← hmapE, ← hr, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  have hcE : Nat.card ↥E = Nat.card ↥E' :=
    (Nat.card_congr (E'.equivMapOfInjective C.subtype C.subtype_injective).toEquiv).symm
  have hrk : pRank 2 ↥E = pRank 2 ↥Q := by
    have h1 := C3.Layer1.Back.card_eq_two_pow_pRank hEel
    have h2 := C3.Layer1.Back.card_eq_two_pow_pRank hQel
    rw [hcE] at h1
    rw [hcQ] at h2
    exact Nat.pow_right_injective le_rfl (h1.symm.trans h2)
  have hNE : normalizer (E : Set G) ≤ gammaK 2 B 3 :=
    le_iSup₂_of_le E hEB (le_iSup_of_le (by rw [hrk]; exact hQr) le_rfl)
  exact hNE (Subgroup.le_normalizer_map C.subtype ⟨c, hc, rfl⟩)

omit [Finite G] in
theorem le_pPrimeCoreOf_of_odd {X : Type*} [Group X] {A Z : Subgroup X} (hAZ : A ≤ Z)
    (hnorm : Z ≤ normalizer (A : Set X)) (hodd : Odd (Nat.card ↥A)) : A ≤ pPrimeCoreOf 2 Z := by
  have hnormal : (A.subgroupOf Z).Normal := by
    refine ⟨fun u hu h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hu ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hnorm h.2) u).mp hu
  have hcop : Nat.Coprime 2 (Nat.card (A.subgroupOf Z)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAZ).toEquiv]
    exact Nat.coprime_two_left.2 hodd
  have hle : A.subgroupOf Z ≤ pPrimeCore 2 ↥Z := le_sSup ⟨hnormal, hcop⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hAZ]
  exact Subgroup.map_mono hle

theorem bar_mem_pPrimeCoreOf {a w : G} {M : Subgroup G} (hwM : w ∈ pPrimeCoreOf 2 M)
    (hwC : w ∈ centralizer ({a} : Set G)) :
    barMk ↥(centralizer ({a} : Set G)) ⟨w, hwC⟩ ∈ pPrimeCoreOf 2 (PumpCalc.bar a M) := by
  set C : Subgroup G := centralizer ({a} : Set G) with hC
  set W : Subgroup ↥C := (pPrimeCoreOf 2 M).subgroupOf C with hW
  have hodd : Odd (Nat.card ↥(W.map (barMk ↥C))) := by
    have h1 : Odd (Nat.card ↥(pPrimeCoreOf 2 M)) := by
      rw [pPrimeCoreOf, Subgroup.card_map_of_injective M.subtype_injective]
      exact odd_card_pPrimeCore _
    have h2 : Nat.card ↥W = Nat.card ↥(W.map C.subtype) :=
      (Subgroup.card_map_of_injective C.subtype_injective).symm
    have h3 : W.map C.subtype ≤ pPrimeCoreOf 2 M := by
      rintro _ ⟨u, hu, rfl⟩
      exact Subgroup.mem_subgroupOf.mp hu
    have h4 : Odd (Nat.card ↥W) := h2 ▸ h1.of_dvd_nat (Subgroup.card_dvd_of_le h3)
    exact h4.of_dvd_nat (Subgroup.card_map_dvd _ _)
  refine le_pPrimeCoreOf_of_odd ?_ ?_ hodd ⟨⟨w, hwC⟩, Subgroup.mem_subgroupOf.mpr hwM, rfl⟩
  · exact Subgroup.map_mono fun u hu => Subgroup.mem_subgroupOf.mpr
      (Th2Sig6.pPrimeCoreOf_le (Subgroup.mem_subgroupOf.mp hu))
  · rintro _ ⟨m, hm, rfl⟩
    refine Subgroup.le_normalizer_map _ ⟨m, ?_, rfl⟩
    have hmN : (m : G) ∈ normalizer ((pPrimeCoreOf 2 M : Subgroup G) : Set G) :=
      mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer (Subgroup.mem_subgroupOf.mp hm))
    rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp hmN (y : G)

omit [Finite G] in
theorem exists_X_not_cSec {A D J : Subgroup G} {a : G} (hAel : CFSG.IsElementaryAbelian 2 ↥A)
    (h : Obs32 A a D J) :
    ∃ n ∈ AG D ⊓ centralizer ({a} : Set G), n ∉ centralizerSection J (pPrimeCoreOf 2 J) := by
  rcases h.unbal with ⟨-, hnle⟩ | ⟨-, c, hc, b, hbA, hcb⟩
  · exact IsConcreteLE.not_le_iff_exists.mp hnle
  · refine ⟨⁅c, b⁆, ?_, hcb⟩
    have hbC : b ∈ centralizer ({a} : Set G) :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp h.y_cent b hbA)
    have hbN : b ∈ normalizer ((AG D ⊓ centralizer ({a} : Set G) : Subgroup G) : Set G) :=
      mem_normalizer_inf (Th2Sig10.le_normalizer_AG hAel h.D_le.1 hbA)
        (Subgroup.le_normalizer hbC)
    have h1 : b * c⁻¹ * b⁻¹ ∈ AG D ⊓ centralizer ({a} : Set G) :=
      (Subgroup.mem_normalizer_iff.mp hbN c⁻¹).mp (inv_mem hc)
    have h2 : ⁅c, b⁆ = c * (b * c⁻¹ * b⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h2]
    exact mul_mem hc h1

theorem setting125_bar {x : G} {K A B M : Subgroup G} {a : G} (h : Boot15B G x K A B M)
    (haA : a ∈ A) (ha2 : orderOf a = 2) {J : Subgroup G}
    (hJ : IsPCompIn 2 (centralizer ({a} : Set G)) J) :
    Setting125 (barQ ↥(centralizer ({a} : Set G))) (PumpCalc.bar a J) (PumpCalc.bar a B)
      (PumpCalc.bar a M)
      (barMk ↥(centralizer ({a} : Set G)) ⟨a, mem_centralizer_singleton_iff.mpr rfl⟩) := by
  have hBel : CFSG.IsElementaryAbelian 2 ↥B := h.B_E4.2.1
  obtain ⟨hBc, -⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  have haB : a ∈ B := h.AB haA
  have hBC : B ≤ centralizer ({a} : Set G) := fun b hb =>
    mem_centralizer_singleton_iff.mpr (hBc b hb a haB)
  have ha1 : a ≠ 1 := fun h1 => by simp [h1] at ha2
  exact
    { core := CFSG.GH74.GLS.pPrimeCore_quotient_eq_bot _
      sec4 := sectional_barQ h.hyp.gen4 _
      secGH := secGH_barQ h.hyp.kgh (centralizer_ne_top h.hyp.simple h.hyp.nonab ha1)
      comp := PumpCalc.isComponent_bar hJ
      B_el := bar_isElementaryAbelian hBel
      B_rank := pRank_bar hBel hBC h.B_rank
      z_mem := ⟨⟨a, mem_centralizer_singleton_iff.mpr rfl⟩, Subgroup.mem_subgroupOf.mpr haB, rfl⟩
      z_ne := bar_self_ne_one ha2 _
      z_cent := bar_self_mem_center _
      gamma := gammaK_bar_le hBel ((prop41_52 h.B_E4 h.bal52.1 h.bal52.2).2.1.trans h.M_norm) }

theorem sig125_bar {a w : G} {M J : Subgroup G} (hJ : IsPCompIn 2 (centralizer ({a} : Set G)) J)
    (hwM : w ∈ pPrimeCoreOf 2 M) (hwC : w ∈ centralizer ({a} : Set G))
    (hwN : w ∈ normalizer (J : Set G)) (hwS : w ∉ centralizerSection J (pPrimeCoreOf 2 J)) :
    Sig125 (PumpCalc.bar a J) (PumpCalc.bar a M) :=
  ⟨_, bar_mem_pPrimeCoreOf hwM hwC, ObsPump.bar_mem_normalizer hJ.1 hwC hwN, fun hc =>
    hwS (ObsPump.mem_cSec_of_bar_comm hJ hwC fun l hl =>
      ((Subgroup.mem_centralizer_iff.mp hc) l hl).symm)⟩

theorem cut125_bar {x : G} {K A B M : Subgroup G} {a : G} {D J : Subgroup G}
    (h : Boot15B G x K A B M) (hobs : Obs32 A a D J) :
    Cut125 (PumpCalc.bar a J) (PumpCalc.bar a B) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centralizer ({a} : Set G) with hC
  obtain ⟨hDA, hDel, hDrk⟩ := hobs.D_le
  obtain ⟨-, hDsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hDel
  have hAC : ∀ y ∈ A, y ∈ C := fun y hy =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hobs.y_cent y hy)
  have hJC : J ≤ C := hobs.comp.1
  obtain ⟨n, hnX, hnS⟩ := exists_X_not_cSec (isE3_of_isSource2 h.src).2.1 hobs
  obtain ⟨d, hdD, hd1⟩ := Th2Sig6.exists_ne_one_of_card (k := pRank 2 ↥D) hDrk
    (C3.Layer1.Back.card_eq_two_pow_pRank hDel)
  have hdC : d ∈ C := hAC d (hDA hdD)
  have hnC : n ∈ C := (Subgroup.mem_inf.mp hnX).2
  have hdel : ((AG D).subgroupOf C).map (barMk ↥C) ≤
      deltaCore ((D.subgroupOf C).map (barMk ↥C)) :=
    Th2.Bal.map_le_deltaCore (a := a) hDsq fun d hd hd1 => iInf₂_le d ⟨hd, hd1⟩
  have hπd1 : barMk ↥C ⟨d, hdC⟩ ≠ 1 := fun h1 => by
    have h2 : (⟨d, hdC⟩ : ↥C) * ⟨d, hdC⟩ = 1 := Subtype.ext (hDsq d hdD)
    exact hd1 (congrArg Subtype.val
      (Th2.Bal.eq_one_of_sq_of_mem_pPrimeCore h2 (Th2.Bal.piBar_eq_one_iff.mp h1)))
  refine ⟨barMk ↥C ⟨d, hdC⟩, ⟨⟨d, hdC⟩, Subgroup.mem_subgroupOf.mpr (h.AB (hDA hdD)), rfl⟩,
    ObsPump.bar_mem_normalizer hJC hdC (hobs.D_norm hdD), ?_, barMk ↥C ⟨n, hnC⟩, ?_,
    ObsPump.bar_mem_normalizer hJC hnC (hobs.AG_inf_le_normalizer hnX), ?_⟩
  · intro hc
    exact hobs.D_faith d hdD hd1 (ObsPump.mem_cSec_of_bar_comm hobs.comp hdC
      fun l hl => ((Subgroup.mem_centralizer_iff.mp hc) l hl).symm)
  · exact deltaCore_le_involutionOddCore (D := (D.subgroupOf C).map (barMk ↥C))
      ⟨⟨d, hdC⟩, Subgroup.mem_subgroupOf.mpr hdD, rfl⟩ hπd1
      (hdel ⟨⟨n, hnC⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp hnX).1, rfl⟩)
  · intro hc
    exact hnS (ObsPump.mem_cSec_of_bar_comm hobs.comp hnC
      fun l hl => ((Subgroup.mem_centralizer_iff.mp hc) l hl).symm)

theorem a7id_of_lem125 (h125 : Lem125p2) (hbr : A7Bridge G) :
    ∀ (x : G) (K A B M : Subgroup G) (a : G) (D J : Subgroup G), Boot15B G x K A B M →
      a ∈ A → Obs32 A a D J →
      (∃ w ∈ pPrimeCoreOf 2 M, w ∈ centralizer ({a} : Set G) ∧ w ∈ normalizer (J : Set G) ∧
        w ∉ centralizerSection J (pPrimeCoreOf 2 J)) →
      Nonempty ((↥J ⧸ pPrimeCore 2 ↥J) ≃* alternatingGroup (Fin 7)) := by
  intro x K A B M a D J h haA hobs ⟨w, hwM, hwC, hwN, hwS⟩
  refine hbr x K A B M a D J h haA hobs ?_
  obtain ⟨e⟩ := PumpCalc.kBar_equiv_bar hobs.comp
  exact isA7A11Quot_of_equiv e (h125 _ _ _ _ _ (setting125_bar h haA hobs.y_ord hobs.comp)
    (sig125_bar hobs.comp hwM hwC hwN hwS) (cut125_bar h hobs))

theorem isILo_of_obs {x : G} {K A B M : Subgroup G} {a : G} {D J : Subgroup G}
    (h : Boot15B G x K A B M) (hobs : Obs32 A a D J) : IsILo 2 a J := by
  obtain ⟨-, hel, hcard, -⟩ := h.src
  have hAC : A ≤ centralizer ({a} : Set G) := fun y hy =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hobs.y_cent y hy)
  have h8 : Nat.card ↥A = 2 ^ pRank 2 ↥A := C3.Layer1.Back.card_eq_two_pow_pRank hel
  have hr : pRank 2 ↥A = 3 := by
    have : (2 : ℕ) ^ pRank 2 ↥A = 2 ^ 3 := by rw [← h8, hcard]; norm_num
    exact Nat.pow_right_injective le_rfl this
  have hmono := C3.Layer1.Back.pRank_mono' hAC
  have h3 : oBound 2 = 3 := by simp [oBound]
  exact ⟨hobs.y_ord, by omega, hobs.comp⟩

theorem a7Bridge_proved : A7Bridge G := by
  intro x K A B M a D J h _ hobs hq
  obtain ⟨h11, h7⟩ := h.a15A7 a J (isILo_of_obs h hobs)
  rcases hq with hq | hq
  · obtain ⟨e⟩ := hq
    have hZ : center (kBar J) = ⊥ := h7 ⟨e⟩
    exact ⟨QuotientGroup.quotientBot.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hZ).symm.trans e)⟩
  · obtain ⟨e⟩ := hq
    exact (h11.false e).elim

theorem a7id_of_lem125p2 (h125 : Lem125p2) :
    ∀ (x : G) (K A B M : Subgroup G) (a : G) (D J : Subgroup G), Boot15B G x K A B M →
      a ∈ A → Obs32 A a D J →
      (∃ w ∈ pPrimeCoreOf 2 M, w ∈ centralizer ({a} : Set G) ∧ w ∈ normalizer (J : Set G) ∧
        w ∉ centralizerSection J (pPrimeCoreOf 2 J)) →
      Nonempty ((↥J ⧸ pPrimeCore 2 ↥J) ≃* alternatingGroup (Fin 7)) :=
  a7id_of_lem125 h125 a7Bridge_proved

end S3T2A7

end CFSG.GH74.Generic.BProg.B3

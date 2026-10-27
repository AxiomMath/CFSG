module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15OraclesCyc
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.OraclesAt
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Ctx
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftBasic
public import CFSG.RankThree.PartTwo.Sec13.Item135CritProof
import CFSG.GroupTheory.SteinbergBKOddMetacyclicTorsion

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.LocalAnalysis.AGL81TheoremCD.Section15
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

namespace CycHatProof

open CFSG.RankThree.PartTwo.Sec13.CritProof (exists_isThompsonCritical_omega omegaOneIn)

theorem conj_mem_map_subtype_of_char {Y : Type*} [Group Y] {S : Subgroup Y} {K : Subgroup S}
    (hK : K.Characteristic) {g : Y} (hg : g ∈ Subgroup.normalizer (S : Set Y)) {w : Y}
    (hw : w ∈ K.map S.subtype) : g * w * g⁻¹ ∈ K.map S.subtype := by
  obtain ⟨k, hk, rfl⟩ := hw
  let φ : MulAut S := Subgroup.normalizerMonoidHom S ⟨g, hg⟩
  have hφ : φ k ∈ K := (Subgroup.characteristic_iff_le_comap.mp hK) φ hk
  exact ⟨φ k, hφ, rfl⟩

theorem normalizer_le_normalizer_map_subtype_of_char {Y : Type*} [Group Y] {S : Subgroup Y}
    {K : Subgroup S} (hK : K.Characteristic) :
    Subgroup.normalizer (S : Set Y) ≤ Subgroup.normalizer (K.map S.subtype : Set Y) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_map_subtype_of_char hK hg hh, fun hh => ?_⟩
  have := conj_mem_map_subtype_of_char hK ((Subgroup.normalizer (S : Set Y)).inv_mem hg) hh
  have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  rwa [e] at this

theorem not_isCyclic_of_exp_of_lt_card {D : Type*} [Group D] {p : ℕ} (hp : p.Prime)
    (hD : ∀ x : D, x ^ p = 1) (hcard : p < Nat.card D) : ¬ IsCyclic D := by
  intro hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := D)
  have h1 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (hD g)
  have h2 := Nat.le_of_dvd hp.pos h1
  omega

theorem isCyclic_of_omega_le_cyclic {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hP : IsPGroup p P) {C D : Subgroup P} (hCD : ∀ x ∈ C, x ^ p = 1 → x ∈ D)
    (hD : IsCyclic D) (hDexp : ∀ x ∈ D, x ^ p = 1) : IsCyclic C := by
  by_contra hCnc
  haveI : Fact (IsPGroup p C) := ⟨hP.to_subgroup C⟩
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a hp2 hCnc
  have hSexp : ∀ x : C, x ∈ S → x ^ p = 1 := fun x hx =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian x hx
  have hSle : S.map C.subtype ≤ D := by
    rintro _ ⟨x, hx, rfl⟩
    refine hCD x x.2 ?_
    have := congrArg Subtype.val (hSexp x hx)
    simpa using this
  have hcycS : IsCyclic (S.map C.subtype) := Subgroup.isCyclic_of_le hSle
  have hcycS' : IsCyclic S :=
    ((S.equivMapOfInjective C.subtype C.subtype_injective).isCyclic).mpr hcycS
  have hexpS : ∀ x : S, x ^ p = 1 := fun x => Subtype.ext (hSexp x.1 x.2)
  have hlt : p < Nat.card S := by
    rw [hScard]
    have := hp.out.one_lt
    nlinarith
  exact not_isCyclic_of_exp_of_lt_card (D := ↥S) hp.out hexpS hlt hcycS'

theorem isCyclic_quotient_of_self_centralizing {P : Type*} [Group P] [Finite P] {p : ℕ}
    [hp : Fact p.Prime] (hp2 : p ≠ 2) (hP : IsPGroup p P) (C : Subgroup P) [C.Normal]
    (hC : IsCyclic C) (hcen : Subgroup.centralizer (C : Set P) ≤ C) : IsCyclic (P ⧸ C) := by
  let φ : P →* MulAut C := MulAut.conjNormal
  have hker : φ.ker ≤ C := by
    intro x hx
    apply hcen
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have h1 := congrArg (fun f : MulAut C => ((f ⟨c, hc⟩ : C) : P)) (MonoidHom.mem_ker.1 hx)
    change x * c * x⁻¹ = c at h1
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  have hAut : IsCyclic (MulAut C) := by
    refine (IsCyclic.mulAutMulEquiv C).isCyclic.mpr ?_
    obtain ⟨k, hk⟩ := (hP.to_subgroup C).exists_card_eq
    rw [hk]
    exact ZMod.isCyclic_units_of_prime_pow p hp.out hp2 k
  haveI : IsCyclic φ.range := inferInstance
  haveI : IsCyclic (P ⧸ φ.ker) :=
    isCyclic_of_surjective (QuotientGroup.quotientKerEquivRange φ).symm.toMonoidHom
      (QuotientGroup.quotientKerEquivRange φ).symm.surjective
  refine isCyclic_of_surjective (QuotientGroup.map φ.ker C (MonoidHom.id P) hker) fun y => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨QuotientGroup.mk x, rfl⟩

theorem exists_char_noncyclic_exp {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hP : IsPGroup p P) (hnc : ¬ IsCyclic P) :
    ∃ D : Subgroup P, D.Characteristic ∧ ¬ IsCyclic D ∧ (∀ x ∈ D, x ^ p = 1) ∧
      ⁅⁅D, D⁆, D⁆ = ⊥ := by
  obtain ⟨C, hC, -, -, hset, hchar, -, hcomm, hexp, -, -⟩ := exists_isThompsonCritical_omega hp2 hP
  by_cases hD : IsCyclic (omegaOneIn p C)
  ·
    have hCcyc : IsCyclic C := by
      refine isCyclic_of_omega_le_cyclic hp2 hP (D := omegaOneIn p C)
        (fun x hxC hx => ?_) hD (fun x hx => hexp x hx)
      have : x ∈ ((omegaOneIn p C : Subgroup P) : Set P) := by
        rw [hset]
        exact ⟨hxC, hx⟩
      exact this
    haveI : C.Normal := by
      haveI := hC.1
      infer_instance
    have hcen : Subgroup.centralizer (C : Set P) ≤ C := by
      rw [hC.2.2.2]
      exact inf_le_left
    have hPC := isCyclic_quotient_of_self_centralizing hp2 hP C hCcyc hcen
    obtain ⟨-, -, hT, -⟩ := CFSG.GroupTheory.SteinbergBK.odd_metacyclic_torsion_counts
      (hp.out.odd_of_ne_two hp2) hP C hCcyc hPC
    obtain ⟨T, hTset, hTchar, hTel, hTcard, -⟩ := hT hnc
    have hTexp : ∀ x ∈ T, x ^ p = 1 := fun x hx => by
      have : x ∈ (T : Set P) := hx
      rw [hTset] at this
      exact this
    refine ⟨T, hTchar, ?_, hTexp, ?_⟩
    · refine not_isCyclic_of_exp_of_lt_card (D := ↥T) hp.out (fun x => Subtype.ext (hTexp x x.2)) ?_
      rw [hTcard]
      have := hp.out.one_lt
      nlinarith
    · have hcomm : ⁅T, T⁆ = ⊥ := Subgroup.commutator_self_eq_bot_iff.mpr hTel.toIsMulCommutative
      rw [hcomm, Subgroup.commutator_bot_left]
  · refine ⟨_, hchar, hD, hexp, ?_⟩
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact (Subgroup.commutator_mono le_rfl le_top).trans (hcomm.trans inf_le_right)

theorem pRank_eq_of_sup_normal_eq_top {X : Type} [Group X] [Finite X] {N H : Subgroup X}
    [N.Normal] (hsup : H ⊔ N = ⊤) {q : ℕ} [hq : Fact q.Prime] (hqN : ¬ q ∣ Nat.card N) :
    CFSG.Open.pRank q H = CFSG.Open.pRank q (⊤ : Subgroup X) := by
  let φ : ↥H →* X ⧸ N := (QuotientGroup.mk' N).comp H.subtype
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hx : x ∈ H ⊔ N := by
      rw [hsup]
      exact Subgroup.mem_top x
    obtain ⟨h, hh, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    refine ⟨⟨h, hh⟩, ?_⟩
    show QuotientGroup.mk' N h = QuotientGroup.mk' N (h * n)
    have h1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).2 hn
    rw [map_mul, h1, mul_one]
  have hmemN : ∀ x : φ.ker, (x : H).1 ∈ N := fun x => by
    have h1 := MonoidHom.mem_ker.1 x.2
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hkerdvd : Nat.card φ.ker ∣ Nat.card N := by
    refine Subgroup.card_dvd_of_injective
      (((H.subtype).comp φ.ker.subtype).codRestrict N hmemN) ?_
    intro a b hab
    have := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext this)
  have hkerq : ¬ q ∣ Nat.card φ.ker := fun h => hqN (h.trans hkerdvd)
  let e : (↥H ⧸ φ.ker) ≃* (X ⧸ N) := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  calc CFSG.Open.pRank q H = CFSG.Open.pRank q (⊤ : Subgroup ↥H) :=
        CFSG.SectionRank.pRank_eq_pRank_top_subgroup H
    _ = CFSG.Open.pRank q (⊤ : Subgroup (↥H ⧸ φ.ker)) :=
        (CFSG.SectionRank.pRank_quotient_eq φ.ker hkerq).symm
    _ = CFSG.Open.pRank q (⊤ : Subgroup (X ⧸ N)) :=
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv hq.out.one_lt e
    _ = CFSG.Open.pRank q (⊤ : Subgroup X) := CFSG.SectionRank.pRank_quotient_eq N hqN

theorem pRank_normalizer_sylow_eq {X : Type} [Group X] [Finite X] {N : Subgroup X} [N.Normal]
    {r : ℕ} [Fact r.Prime] (P : Sylow r N) {q : ℕ} [Fact q.Prime] (hqN : ¬ q ∣ Nat.card N) :
    CFSG.Open.pRank q (Subgroup.normalizer ((P.map N.subtype : Subgroup X) : Set X)) =
      CFSG.Open.pRank q (⊤ : Subgroup X) :=
  pRank_eq_of_sup_normal_eq_top (Sylow.normalizer_sup_eq_top P) hqN

theorem exists_sylow_preimage {X : Type} [Group X] [Finite X] {Q : Subgroup X} [Q.Normal]
    (hQ : IsPGroup 2 Q) {r : ℕ} [Fact r.Prime] {R : Subgroup (X ⧸ Q)} [R.Normal]
    (hR : IsPGroup r R) :
    ∃ (N : Subgroup X) (_ : N.Normal) (P : Sylow r N),
      (∀ x : X, x ∈ N ↔ (QuotientGroup.mk x : X ⧸ Q) ∈ R) ∧
      (P.map N.subtype : Subgroup X).map (QuotientGroup.mk' Q) = R ∧
      ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ r → ¬ q ∣ Nat.card N := by
  let N : Subgroup X := R.comap (QuotientGroup.mk' Q)
  haveI hNn : N.Normal := Subgroup.Normal.comap inferInstance _
  let fN : ↥N →* ↥R := ((QuotientGroup.mk' Q).comp N.subtype).codRestrict R (fun x => x.2)
  have hfN : Function.Surjective fN := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective Q (y : X ⧸ Q)
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    show QuotientGroup.mk' Q x ∈ R
    rw [hx]
    exact y.2
  obtain ⟨P⟩ : Nonempty (Sylow r ↥N) := inferInstance
  have htop : (P.map fN : Subgroup ↥R) = ⊤ :=
    ((P.mapSurjective hfN).is_maximal' (hR.to_subgroup ⊤) le_top).symm
  refine ⟨N, hNn, P, fun x => Iff.rfl, ?_, ?_⟩
  · have e : (QuotientGroup.mk' Q).comp N.subtype = R.subtype.comp fN := MonoidHom.ext fun x => rfl
    calc (P.map N.subtype : Subgroup X).map (QuotientGroup.mk' Q)
        = (P : Subgroup ↥N).map ((QuotientGroup.mk' Q).comp N.subtype) := Subgroup.map_map _ _ _
      _ = (P : Subgroup ↥N).map (R.subtype.comp fN) := by rw [e]
      _ = ((P : Subgroup ↥N).map fN).map R.subtype := (Subgroup.map_map _ _ _).symm
      _ = R := by rw [htop, Subgroup.map_top, Subgroup.range_subtype]
  · intro q hq hq2 hqr hdvd
    obtain ⟨a, ha⟩ := hQ.exists_card_eq
    obtain ⟨b, hb⟩ := hR.exists_card_eq
    have hcard : Nat.card N = Nat.card Q * Nat.card R :=
      QuotientGroup.card_preimage_mk Q (R : Set (X ⧸ Q))
    rw [hcard, ha, hb] at hdvd
    rcases (Nat.Prime.dvd_mul hq).1 hdvd with h | h
    · exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h))
    · exact hqr ((Nat.prime_dvd_prime_iff_eq hq (Fact.out : r.Prime)).1 (hq.dvd_of_dvd_pow h))

theorem pCoreOf_normal {Y : Type*} [Group Y] (K : Subgroup Y) [K.Normal] (r : ℕ) :
    (pCoreOf r K).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hg : g ∈ Subgroup.normalizer (K : Set Y) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top g
  exact conj_mem_map_subtype_of_char (S := K) (K := CFSG.pCore r ↥K) inferInstance hg hn

theorem two_le_pRank_of_not_isCyclic {X : Type} [Group X] [Finite X] {r : ℕ} [hr : Fact r.Prime]
    (hr2 : r ≠ 2) {P : Subgroup X} (hP : IsPGroup r P) (hnc : ¬ IsCyclic P) :
    2 ≤ CFSG.Open.pRank r P := by
  haveI : Fact (IsPGroup r P) := ⟨hP⟩
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a hr2 hnc
  have hE : CFSG.Open.IsElemAbelian r S :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian r S).mp hSel
  have h2 := CFSG.SectionRank.le_pRank hr.out.one_lt (le_top : S ≤ ⊤) hE hScard
  rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at h2

theorem map_props {A B : Type*} [Group A] [Group B] (f : A →* B) (hf : Function.Injective f)
    {p : ℕ} {D : Subgroup A} (hnc : ¬ IsCyclic D) (hexp : ∀ x ∈ D, x ^ p = 1)
    (hcl : ⁅⁅D, D⁆, D⁆ = ⊥) :
    ¬ IsCyclic (D.map f) ∧ (∀ x ∈ D.map f, x ^ p = 1) ∧
      ⁅⁅D.map f, D.map f⁆, D.map f⁆ = ⊥ := by
  refine ⟨fun h => hnc (((D.equivMapOfInjective f hf).isCyclic).mpr h), ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexp x hx, map_one]
  · rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, hcl, Subgroup.map_bot]

theorem normalizer_le_normalizer_omegaOneCenterOf {G : Type*} [Group G] (T : Subgroup G) :
    Subgroup.normalizer (T : Set G) ≤
      Subgroup.normalizer ((CFSG.Quasithin.omegaOneCenterOf T : Subgroup G) : Set G) := by
  have h := normalizer_le_normalizer_map_subtype_of_char (S := T)
    (CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf T)
  have hle : CFSG.Quasithin.omegaOneCenterOf T ≤ T :=
    CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le T
  rwa [Subgroup.map_subgroupOf_eq_of_le hle] at h

theorem coe_mem_centralizer_omegaOneCenterOf {G : Type} [Group G] {M T : Subgroup G} (hTM : T ≤ M)
    {x : ↥M} (hx : x ∈ CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.gnC (T.subgroupOf M)) :
    (x : G) ∈ Subgroup.centralizer ((CFSG.Quasithin.omegaOneCenterOf T : Subgroup G) : Set G) := by
  rw [← map_omegaOneCenterOf_subgroupOf hTM, Subgroup.mem_centralizer_iff]
  rintro _ ⟨z, hz, rfl⟩
  have hzV : z ∈ CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.gnV (T.subgroupOf M) :=
    Subgroup.le_normalClosure hz
  exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hx z hzV)

end CycHatProof

open CycHatProof in
theorem cycHat_of_O1219Sigma_gen {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (hO1219 : O1219SigmaAt G M) (hO1211 : O1211At G M)
    (ctx : S15CtxGen G M T T₁ T₂) : CycHat G M T := by
  intro r hr hr3
  by_contra hnc
  haveI : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by omega
  have hr5 : 5 ≤ r := by
    have h4 : r ≠ 4 := by
      rintro rfl
      exact absurd hr (by norm_num)
    omega
  have hTM : T ≤ M := ctx.sylow.le
  have hQC : CFSG.pCore 2 ↥M ≤ gnC (T.subgroupOf M) := pCore_le_gnC ctx.gn
  haveI : (cHatImage G M T).Normal :=
    Subgroup.Normal.map (gnC_normal _) (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  haveI : (pCoreOf r (cHatImage G M T)).Normal := pCoreOf_normal _ r
  have hRp : IsPGroup r ↥(pCoreOf r (cHatImage G M T)) :=
    (CFSG.pCore_isPGroup).map (cHatImage G M T).subtype
  obtain ⟨N, hNn, P, hNmem, hPmap, hNcard⟩ := exists_sylow_preimage CFSG.pCore_isPGroup hRp
  set PX : Subgroup ↥M := (P.map N.subtype : Subgroup ↥M) with hPXdef
  have hNC : N ≤ gnC (T.subgroupOf M) := by
    intro x hx
    have hxR := (hNmem x).1 hx
    obtain ⟨c, hc, hcx⟩ := (Subgroup.map_subtype_le _) hxR
    have h1 : c⁻¹ * x ∈ gnC (T.subgroupOf M) := hQC (QuotientGroup.eq.1 hcx)
    have h2 := (gnC (T.subgroupOf M)).mul_mem hc h1
    simpa using h2
  have hPX : IsPGroup r ↥PX := P.isPGroup'.map N.subtype
  have hPXC : PX ≤ gnC (T.subgroupOf M) := (Subgroup.map_subtype_le _).trans hNC
  have hPXnc : ¬ IsCyclic ↥PX := by
    intro hcyc
    apply hnc
    rw [← hPmap]
    exact isCyclic_of_surjective ((QuotientGroup.mk' _).subgroupMap _)
      (MonoidHom.subgroupMap_surjective _ _)
  have hrσ : r ∉ sigmaM G M := by
    intro hmem
    have h1 := ctx.rank_C r hmem
    have h2 := two_le_pRank_of_not_isCyclic hr2 hPX hPXnc
    have h3 := CFSG.SectionRank.pRank_mono hr.one_lt hPXC
    omega
  obtain ⟨Dpl, hDchar, hDnc, hDexp, hDcl⟩ := exists_char_noncyclic_exp hr2 hPX hPXnc
  obtain ⟨hDXnc, hDXexp, hDXcl⟩ := map_props PX.subtype PX.subtype_injective hDnc hDexp hDcl
  set DX : Subgroup ↥M := Dpl.map PX.subtype with hDXdef
  obtain ⟨hDGnc, hDGexp, hDGcl⟩ := map_props M.subtype M.subtype_injective hDXnc hDXexp hDXcl
  set DG : Subgroup G := DX.map M.subtype with hDGdef
  obtain ⟨q, hq⟩ := ctx.p_mem
  have hqp : q.Prime := sigmaA_prime q hq.1
  have hq2 : q ≠ 2 := sigmaA_odd q hq.1
  have hqr : q ≠ r := fun h => hrσ (h ▸ hq)
  haveI : Fact q.Prime := ⟨hqp⟩
  have hfr : CFSG.Open.pRank q (Subgroup.normalizer (PX : Set ↥M)) =
      CFSG.Open.pRank q (⊤ : Subgroup ↥M) :=
    pRank_normalizer_sylow_eq P (hNcard q hqp hq2 hqr)
  have hnorm : Subgroup.normalizer (PX : Set ↥M) ≤ Subgroup.normalizer (DX : Set ↥M) :=
    normalizer_le_normalizer_map_subtype_of_char hDchar
  have hrank : CFSG.Open.pRank q (M ⊓ Subgroup.normalizer (DG : Set G)) = CFSG.Open.pRank q M := by
    apply le_antisymm (CFSG.SectionRank.pRank_mono hqp.one_lt inf_le_left)
    calc CFSG.Open.pRank q M = CFSG.Open.pRank q (⊤ : Subgroup ↥M) :=
          CFSG.SectionRank.pRank_eq_pRank_top_subgroup M
      _ = CFSG.Open.pRank q (Subgroup.normalizer (PX : Set ↥M)) := hfr.symm
      _ ≤ CFSG.Open.pRank q (Subgroup.normalizer (DX : Set ↥M)) :=
          CFSG.SectionRank.pRank_mono hqp.one_lt hnorm
      _ ≤ CFSG.Open.pRank q ((Subgroup.normalizer (DX : Set ↥M)).map M.subtype) :=
          CFSG.SectionRank.pRank_le_map hqp.one_lt M.subtype M.subtype_injective _
      _ ≤ CFSG.Open.pRank q (M ⊓ Subgroup.normalizer (DG : Set G)) :=
          CFSG.SectionRank.pRank_mono hqp.one_lt
            (le_inf (Subgroup.map_subtype_le _) (Subgroup.le_normalizer_map M.subtype))
  obtain ⟨E, hEDG, hEel, hEcard, hΓ⟩ := hO1219 q r hq hr hr2 hrσ DG
    (Subgroup.map_subtype_le _) hDGnc hDGexp hDGcl hrank
  have hEM : E ≤ M := hEDG.trans (Subgroup.map_subtype_le _)
  have hTp : IsPGroup 2 T := ctx.sylow.isPGroup
  have hT0 : T ≠ ⊥ := ne_bot_of_isSylowOf_two ctx.maxLocal.1 ctx.sylow
  have hZ0 : CFSG.Quasithin.omegaOneCenterOf T ≠ ⊥ :=
    CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hTp hT0
  have hZ2 : IsPGroup 2 (CFSG.Quasithin.omegaOneCenterOf T : Subgroup G) :=
    hTp.to_le (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le T)
  have hloc : IsTwoLocal (Subgroup.normalizer
      ((CFSG.Quasithin.omegaOneCenterOf T : Subgroup G) : Set G)) := ⟨_, hZ0, hZ2, rfl⟩
  have hEZ : E ≤
      Subgroup.normalizer ((CFSG.Quasithin.omegaOneCenterOf T : Subgroup G) : Set G) := by
    intro e he
    obtain ⟨x, hxDX, rfl⟩ := Subgroup.mem_map.1 (hEDG he)
    obtain ⟨y, hyD, rfl⟩ := Subgroup.mem_map.1 hxDX
    have hxC : (PX.subtype y : ↥M) ∈ gnC (T.subgroupOf M) := hPXC y.2
    exact Subgroup.centralizer_le_normalizer _ (coe_mem_centralizer_omegaOneCenterOf hTM hxC)
  have hHM := hO1211 r hr hr5 hrσ E hEM hEel hEcard hΓ _ hloc hEZ
  exact ctx.notLe ((normalizer_le_normalizer_omegaOneCenterOf T).trans hHM)

theorem cycHat_of_O1219Sigma (hO1219 : O1219Sigma) (hO1211 : O1211) {G : Type} [Group G] [Finite G]
    {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M} (ctx : S15Ctx2 G M T T₁ T₂) : CycHat G M T :=
  cycHat_of_O1219Sigma_gen (O1219SigmaAt.of_ctx2 hO1219 ctx) (O1211At.of_ctx2 hO1211 ctx)
    (S15CtxGen.of_ctx2 ctx)

end CFSG.LocalAnalysis.RankThreeUC.S15

module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims136b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltFacts5
public import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Shape
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611
public import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDownComp
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamSpor
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1415

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup
  glaPComponent_map_fixSubgroup)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom onCenterQuotient_apply_mk)

section Fix

variable {K : Type} [Group K]

theorem autFixSub_eq (x : MulAut K) : Prop126.autFixSub x = fixSubgroup x :=
  Subgroup.ext fun _ => Iff.rfl

theorem lemma1314_fixSub_eq (x : MulAut K) : Lemma1314.fixSub x = fixSubgroup x :=
  Subgroup.ext fun _ => Iff.rfl

theorem fixSub_eq (x : MulAut K) : MovingAround.fixSub x = fixSubgroup x :=
  Subgroup.ext fun _ => Iff.rfl

theorem fixSubgroup_conj (s : K) :
    fixSubgroup (MulAut.conj s) = Subgroup.centralizer ({s} : Set K) := by
  ext g
  rw [mem_fixSubgroup, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff,
    mul_inv_eq_iff_eq_mul]
  exact eq_comm

end Fix

section Transfer

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem center_transfer (hp : p.Prime) (x : MulAut K) {J : Subgroup K}
    (hJ : GLAPComponent p (fixSubgroup x) J) :
    GLAPComponent p (fixSubgroup (centerQuotientHom K x))
        (J.map (QuotientGroup.mk' (Subgroup.center K))) ∧
      Nonempty (PSimple p J ≃* PSimple p (J.map (QuotientGroup.mk' (Subgroup.center K)))) := by
  have hπs : Function.Surjective (QuotientGroup.mk' (Subgroup.center K)) :=
    QuotientGroup.mk'_surjective _
  have hker : (QuotientGroup.mk' (Subgroup.center K)).ker ≤ Subgroup.center K :=
    (QuotientGroup.ker_mk' _).le
  have hαβ : ∀ k, QuotientGroup.mk' (Subgroup.center K) (x k) =
      centerQuotientHom K x (QuotientGroup.mk' (Subgroup.center K) k) :=
    fun k => (onCenterQuotient_apply_mk x k).symm
  have hJ' := glaPComponent_map_fixSubgroup _ hker x _ hαβ hπs hp hJ
  exact ⟨hJ', CFSG.LocalAnalysis.GLTheoremA.nonempty_pSimple_equiv_map hp _ hJ hJ'⟩

theorem centerQuotientHom_pow_eq_one {x : MulAut K} (hx : x ^ p = 1) :
    centerQuotientHom K x ^ p = 1 := by
  rw [← map_pow, hx, map_one]

theorem centerQuotientHom_ne_one (hperf : commutator K = ⊤) {x : MulAut K} (hx : x ≠ 1) :
    centerQuotientHom K x ≠ 1 := by
  haveI : Group.IsPerfect K := Group.isPerfect_def.mpr hperf
  intro h
  apply hx
  apply CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective K
  rw [h, map_one]

theorem comp_transport {T Q : Type} [Group T] [Group Q] [Finite T] (hp : p.Prime) (e : T ≃* Q) {s : T}
    {I : Subgroup T} (hI : GLAPComponent p (Subgroup.centralizer ({s} : Set T)) I) :
    GLAPComponent p (Subgroup.centralizer ({e s} : Set Q)) (I.map e.toMonoidHom) ∧
      Nonempty (PSimple p I ≃* PSimple p (I.map e.toMonoidHom)) := by
  have h := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv hp e hI
  rw [CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_mulEquiv] at h
  exact ⟨h, ⟨CFSG.HardMathSupport.Dickson.I271.pSimpleEquiv p (e.subgroupMap I)⟩⟩

end Transfer

section AltCat

theorem alt_chev_degree (hnl : Prop1116Design.InputAltNotLie) {r m : ℕ} (hm : 5 ≤ m) {S : Type}
    [Group S] (e : S ≃* alternatingGroup (Fin m)) (hch : IsChevSimple r S) : m = 5 ∨ m = 6 ∨ m = 8 := by
  rcases hch with ⟨i, hi, ⟨g⟩⟩ | ⟨i, hi, ⟨g⟩⟩
  · rcases i with ⟨q, hq⟩ | ⟨n, hn⟩ | idx | s
    · exact hi.elim
    · exact hi.elim
    · exact ((hnl m idx hm).false (e.symm.trans g)).elim
    · exact hi.elim
  · rcases i with ⟨q, hq⟩ | ⟨n, hn⟩ | idx | s
    · exact hi.elim
    · have hmn : m = n := Prop1116Design.alt_iso_degree hm hn (e.symm.trans g)
      subst hmn
      rcases hi with ⟨h5, -⟩ | ⟨h6, -⟩ | ⟨h8, -⟩
      · exact Or.inl h5
      · exact Or.inr (Or.inl h6)
      · exact Or.inr (Or.inr h8)
    · exact ((hnl m idx hm).false (e.symm.trans g)).elim
    · exact hi.elim

end AltCat

section AltFamily

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem alt_family (hp : p.Prime) (hp2 : p ≠ 2) (hq : CFSG.Open.IsQuasisimple K) (hO : GLAPPrimeCore p K = ⊥)
    {n : ℕ} (hn : 5 ≤ n) (f : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) {x : MulAut K}
    (hx : orderOf x = p) {J₁ : Subgroup K} (hJ₁ : GLAPComponent p (fixSubgroup x) J₁) {m : ℕ}
    (hm : 5 ≤ m) (hJt : Nonempty (PSimple p J₁ ≃* alternatingGroup (Fin m))) :
    ∃ k : ℕ, 1 ≤ k ∧ n = m + k * p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hxp : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    exact hp.one_lt.ne' hx.symm
  have hA : ∀ a ∈ Subgroup.zpowers x, a ^ p = 1 := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
  obtain ⟨τ, hτinj, hτ⟩ := AltFacts5.exists_tau hpodd hn hq.1 f hA
  set x' : ↥(Subgroup.zpowers x) := ⟨x, Subgroup.mem_zpowers x⟩ with hx'
  set t : Equiv.Perm (Fin n) := τ x' with ht
  have htp : t ^ p = 1 := by
    rw [ht, ← map_pow, show x' ^ p = 1 from Subtype.ext (by simpa using hxp), map_one]
  have ht1 : t ≠ 1 := by
    intro h1
    have : x' = 1 := hτinj (by rw [← ht, h1, map_one])
    exact hx1 (congrArg Subtype.val this)
  have hZ : IsPGroup p ↥(Subgroup.center K) := AltFacts2.isPGroup_center_of_core_eq_bot hp hO
  have hJ₁' : GLAPComponent p (MovingAround.fixSub x) J₁ := by rwa [fixSub_eq]
  obtain ⟨h5, ⟨eA⟩⟩ := AltFacts5.component_alt hp hp2 (AltFacts5.isAltRep_of_equiv f) hZ
    (α := x) (τ := t) (fun y => hτ x' y) htp hJ₁'
  obtain ⟨eJ⟩ := hJt
  have hmF : m = t.supportᶜ.card :=
    Prop1116Design.alt_iso_degree hm h5 (eJ.symm.trans eA)
  have hmod : t.supportᶜ.card ≡ n [MOD p] := by
    have := Equiv.Perm.card_compl_support_modEq (p := p) (n := 1) (σ := t) (by rw [pow_one]; exact htp)
    rwa [Fintype.card_fin] at this
  have hsupp : t.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, Equiv.Perm.support_eq_empty_iff]
    exact ht1
  have hcard : t.supportᶜ.card + t.support.card = n := by
    have := Finset.card_compl t.support
    rw [Fintype.card_fin] at this
    have hle : t.support.card ≤ n := by
      simpa using Finset.card_le_univ t.support
    omega
  have hpos : 0 < t.support.card := Finset.card_pos.2 hsupp
  rw [← hmF] at hmod hcard
  have hlt : m < n := by omega
  obtain ⟨k, hk⟩ : p ∣ n - m := (Nat.modEq_iff_dvd' hlt.le).1 hmod
  refine ⟨k, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, mul_zero] at hk
      omega
    · exact h0
  · rw [mul_comm k p]
    omega

end AltFamily

section LieFamily

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem lie_family_degree (hnl : Prop1116Design.InputAltNotLie) (hp : p.Prime)
    (hq : CFSG.Open.IsQuasisimple K) (idx : TauCeti.ValidLieTypeIndex)
    (hD : CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ p idx.1.characteristic)
    (f : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie idx).Group) {x : MulAut K} (hx : x ^ p = 1)
    {J₁ : Subgroup K} (hJ₁ : GLAPComponent p (fixSubgroup x) J₁) {m : ℕ} (hm : 5 ≤ m)
    (hJt : Nonempty (PSimple p J₁ ≃* alternatingGroup (Fin m))) : m = 5 ∨ m = 6 ∨ m = 8 := by
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2
  have hnab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hq
  obtain ⟨hJ', ⟨eJ⟩⟩ := center_transfer hp x hJ₁
  have hchev : IsChevSimple idx.1.characteristic (K ⧸ Subgroup.center K) :=
    Or.inl ⟨TauCeti.CFSGIndex.lie idx, rfl, ⟨f⟩⟩
  have hI := hD (K ⧸ Subgroup.center K) inferInstance hnab hchev (centerQuotientHom K x)
    (centerQuotientHom_pow_eq_one hx) _ hJ'
  obtain ⟨eA⟩ := hJt
  exact alt_chev_degree hnl hm (eJ.symm.trans eA)
    (CFSG.LocalAnalysis.GLTheoremA.chev_isChevSimple_of_mulEquiv
      (MulEquiv.refl _) hI)

end LieFamily

@[expose] def SporNoAltDown (p m : ℕ) (name : TauCeti.SporadicName) : Prop :=
  ∀ (T : Type) [Group T] [Finite T], Nonempty (T ≃* (TauCeti.CFSGIndex.sporadic name).Group) →
    ∀ s : T, orderOf s = p → ∀ I : Subgroup T,
      GLAPComponent p (Subgroup.centralizer ({s} : Set T)) I →
        IsEmpty (PSimple p I ≃* alternatingGroup (Fin m))

section SporFamily

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem spor_family (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hp : p.Prime) (hp2 : p ≠ 2) (hq : CFSG.Open.IsQuasisimple K) (name : TauCeti.SporadicName)
    (f : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic name).Group) {x : MulAut K}
    (hx : orderOf x = p) {J₁ : Subgroup K} (hJ₁ : GLAPComponent p (fixSubgroup x) J₁) {m : ℕ}
    (hJt : Nonempty (PSimple p J₁ ≃* alternatingGroup (Fin m))) : ¬ SporNoAltDown p m name := by
  intro hS
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2
  have hnab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hq
  have hcen : Subgroup.center (K ⧸ Subgroup.center K) = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hnab
  have hout := hOut (K ⧸ Subgroup.center K) inferInstance hnab name ⟨f⟩
  have hxp : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    exact hp.one_lt.ne' hx.symm
  obtain ⟨hJ', ⟨eJ⟩⟩ := center_transfer hp x hJ₁
  obtain ⟨s, hs, hsp⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_conj_of_pow hp hp2 hcen hout
    (centerQuotientHom K x) (centerQuotientHom_pow_eq_one hxp)
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [map_one] at hs
    exact centerQuotientHom_ne_one hq.1 hx1 hs.symm
  have hso : orderOf s = p := orderOf_eq_prime hsp hs1
  rw [← hs, fixSubgroup_conj] at hJ'
  obtain ⟨eA⟩ := hJt
  exact (hS _ ⟨f⟩ s hso _ hJ').false (eJ.symm.trans eA)

end SporFamily

section SporTools

@[expose] def CentNoAlt (p m : ℕ) (Q : Type) [Group Q] : Prop :=
  ∀ s : Q, orderOf s = p → ∀ I : Subgroup Q,
    GLAPComponent p (Subgroup.centralizer ({s} : Set Q)) I →
      IsEmpty (PSimple p I ≃* alternatingGroup (Fin m))

theorem CentNoAlt.of_equiv {p m : ℕ} (hp : p.Prime) {Q T : Type} [Group Q] [Group T] [Finite T]
    (e : T ≃* Q) (h : CentNoAlt p m Q) : CentNoAlt p m T := by
  intro s hs I hI
  have hs' : orderOf (e s) = p := by rw [MulEquiv.orderOf_eq, hs]
  obtain ⟨hI', ⟨f⟩⟩ := comp_transport hp e hI
  refine ⟨fun g => (h (e s) hs' _ hI').false (f.symm.trans g)⟩

theorem sporNoAltDown_of_model {p m : ℕ} (hp : p.Prime) {name : TauCeti.SporadicName} {Q : Type}
    [Group Q] (e : Q ≃* (TauCeti.CFSGIndex.sporadic name).Group) (h : CentNoAlt p m Q) :
    SporNoAltDown p m name := by
  intro T _ _ ⟨f⟩ s hs I hI
  exact (h.of_equiv hp (f.trans e.symm)) s hs I hI

theorem mul_card_alt_dvd {T : Type} [Group T] [Finite T] {p m : ℕ} (hp : p.Prime) {s : T}
    (hs : orderOf s = p) {I : Subgroup T}
    (hI : GLAPComponent p (Subgroup.centralizer ({s} : Set T)) I)
    (e : PSimple p I ≃* alternatingGroup (Fin m)) :
    p * Nat.card (alternatingGroup (Fin m)) ∣
      Nat.card (Subgroup.centralizer ({s} : Set T)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set C : Subgroup T := Subgroup.centralizer ({s} : Set T) with hC
  have hQ : Nat.card (PQuot p I) =
      Nat.card (Subgroup.center (PQuot p I)) * Nat.card (alternatingGroup (Fin m)) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (PQuot p I)),
      Nat.card_congr e.toEquiv, mul_comm]
  have hQI : Nat.card (PQuot p I) ∣ Nat.card I := Subgroup.card_quotient_dvd_card _
  have hIC : Nat.card I ∣ Nat.card C := Subgroup.card_dvd_of_le hI.1
  have hAI : Nat.card (alternatingGroup (Fin m)) ∣ Nat.card I :=
    (Dvd.intro_left _ hQ.symm).trans hQI
  by_cases hZ : Subgroup.center (PQuot p I) = ⊥
  ·
    have hsI : s ∉ I := by
      intro hsI
      have hcen : (⟨s, hsI⟩ : ↥I) ∈ Subgroup.center ↥I := by
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        exact Subgroup.mem_centralizer_singleton_iff.1 (hI.1 g.2)
      have himg : (QuotientGroup.mk (⟨s, hsI⟩ : ↥I) : PQuot p I) ∈ Subgroup.center (PQuot p I) :=
        Subgroup.map_center_le_center (QuotientGroup.mk'_surjective _) ⟨_, hcen, rfl⟩
      rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at himg
      have hdvd : orderOf (⟨s, hsI⟩ : ↥I) ∣ Nat.card (GLAPPrimeCore p ↥I) :=
        Subgroup.orderOf_dvd_natCard _ himg
      rw [Subgroup.orderOf_mk, hs] at hdvd
      have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥I)) := CFSG.pPrimeCore_coprime_card
      exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hdvd)
    have hsC : s ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
    have hcomm : ∀ (a : ↥I) (b : ↥(Subgroup.zpowers s)),
        Commute (I.subtype a) ((Subgroup.zpowers s).subtype b) := by
      intro a b
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 b.2
      have ha : Commute (a : T) s := (Subgroup.mem_centralizer_singleton_iff.1 (hI.1 a.2))
      show Commute (a : T) (b : T)
      rw [← hk]
      exact ha.zpow_right k
    set φ : ↥I × ↥(Subgroup.zpowers s) →* T :=
      MonoidHom.noncommCoprod I.subtype (Subgroup.zpowers s).subtype hcomm with hφ
    have hinj : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      rintro ⟨a, b⟩ hab
      have hab' : (a : T) * (b : T) = 1 := hab
      have hab2 : (a : T) = (b : T)⁻¹ := eq_inv_of_mul_eq_one_left hab'
      have hbI : ((b : T)⁻¹) ∈ I := hab2 ▸ a.2
      have hb1 : (b : T) = 1 := by
        by_contra hb1
        have hbI' : (b : T) ∈ I := by simpa using I.inv_mem hbI
        have hne : I ⊓ Subgroup.zpowers s ≠ ⊥ := by
          intro hbot
          have : (b : T) ∈ I ⊓ Subgroup.zpowers s := ⟨hbI', b.2⟩
          rw [hbot, Subgroup.mem_bot] at this
          exact hb1 this
        have hprime : (Nat.card ↥(Subgroup.zpowers s)).Prime := by
          rw [Nat.card_zpowers, hs]; exact hp
        have hsub : (I ⊓ Subgroup.zpowers s).subgroupOf (Subgroup.zpowers s) = ⊤ := by
          haveI : Fact (Nat.card ↥(Subgroup.zpowers s)).Prime := ⟨hprime⟩
          rcases Subgroup.eq_bot_or_eq_top_of_prime_card
            ((I ⊓ Subgroup.zpowers s).subgroupOf (Subgroup.zpowers s)) with h | h
          · exact absurd ((Subgroup.subgroupOf_eq_bot.1 h).eq_bot_of_le inf_le_right) hne
          · exact h
        have hle : Subgroup.zpowers s ≤ I ⊓ Subgroup.zpowers s :=
          Subgroup.subgroupOf_eq_top.1 hsub
        exact hsI (hle (Subgroup.mem_zpowers s)).1
      have ha1 : (a : T) = 1 := by rw [hab2, hb1, inv_one]
      exact Prod.ext (Subtype.ext ha1) (Subtype.ext hb1)
    have hrange : φ.range ≤ C := by
      rintro _ ⟨⟨a, b⟩, rfl⟩
      show (a : T) * (b : T) ∈ C
      refine C.mul_mem (hI.1 a.2) ?_
      exact (Subgroup.zpowers_le.2 hsC) b.2
    have hcard : Nat.card φ.range = Nat.card I * p := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, Nat.card_zpowers,
        hs]
    have h1 : Nat.card I * p ∣ Nat.card C := hcard ▸ Subgroup.card_dvd_of_le hrange
    rw [mul_comm p]
    exact (Nat.mul_dvd_mul_right hAI p).trans h1
  ·
    have hZp : IsPGroup p ↥(Subgroup.center (PQuot p I)) :=
      AltFacts2.isPGroup_center_of_core_eq_bot hp (glaPPrimeCore_quotient_eq_bot hp)
    have hpZ : p ∣ Nat.card ↥(Subgroup.center (PQuot p I)) := by
      rcases hZp.card_eq_or_dvd with h1 | h1
      · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hZ
      · exact h1
    calc p * Nat.card (alternatingGroup (Fin m))
        ∣ Nat.card (Subgroup.center (PQuot p I)) * Nat.card (alternatingGroup (Fin m)) :=
          Nat.mul_dvd_mul_right hpZ _
      _ = Nat.card (PQuot p I) := hQ.symm
      _ ∣ Nat.card C := hQI.trans hIC

theorem centNoAlt_of_card {p m : ℕ} (hp : p.Prime) {Q : Type} [Group Q] [Finite Q]
    (h : ∀ s : Q, orderOf s = p →
      ¬ p * Nat.card (alternatingGroup (Fin m)) ∣ Nat.card (Subgroup.centralizer ({s} : Set Q))) :
    CentNoAlt p m Q :=
  fun s hs _ hI => ⟨fun e => h s hs (mul_card_alt_dvd hp hs hI e)⟩

theorem card_alt (m : ℕ) (hm : 2 ≤ m) : Nat.card (alternatingGroup (Fin m)) = m.factorial / 2 := by
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 hm
  rw [nat_card_alternatingGroup, Nat.card_fin]

theorem sporNoAltDown_of_not_dvd
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable) {p m : ℕ} (hp : p.Prime)
    (hm : 2 ≤ m) {name : TauCeti.SporadicName}
    (h : ¬ p * (m.factorial / 2) ∣ CFSG.HardMathSupport.Solomon.Coordinator.sporOrd name) :
    SporNoAltDown p m name := by
  intro T _ _ ⟨f⟩ s hs I hI
  refine ⟨fun e => h ?_⟩
  have h1 := mul_card_alt_dvd hp hs hI e
  rw [card_alt m hm] at h1
  have h2 : Nat.card (Subgroup.centralizer ({s} : Set T)) ∣ Nat.card T :=
    Subgroup.card_subgroup_dvd_card _
  rw [Nat.card_congr f.toEquiv, hOrd name] at h2
  exact h1.trans h2

end SporTools

section Rank

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem center_eq_bot_of_alt {X : Type*} [Group X] {m : ℕ} (hm : 4 ≤ m)
    (e : X ≃* alternatingGroup (Fin m)) : Subgroup.center X = ⊥ := by
  have h2 : Subgroup.center (alternatingGroup (Fin m)) = ⊥ :=
    alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hm)
  rw [eq_bot_iff]
  intro z hz
  have : e z ∈ Subgroup.center (alternatingGroup (Fin m)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz) g']
  rw [h2, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact (MulEquiv.map_eq_one_iff e).1 this

theorem eq_one_of_central_of_alt (hp : p.Prime) {J : Subgroup K} {m : ℕ} (hm : 4 ≤ m)
    (e : CFSG.HardMathSupport.Solomon.LocalBalance.barOf p J ≃* alternatingGroup (Fin m)) {c : K}
    (hcJ : c ∈ J) (hcp : c ^ p = 1) (hc : ∀ j ∈ J, c * j = j * c) : c = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set c' : ↥J := ⟨c, hcJ⟩ with hc'
  have hcen : c' ∈ Subgroup.center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2).symm
  have hq : (QuotientGroup.mk c' : CFSG.HardMathSupport.Solomon.LocalBalance.barOf p J) ∈
      Subgroup.center (CFSG.HardMathSupport.Solomon.LocalBalance.barOf p J) :=
    Subgroup.map_center_le_center (QuotientGroup.mk'_surjective _) ⟨_, hcen, rfl⟩
  rw [center_eq_bot_of_alt hm e, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hq
  have h1 : orderOf c' ∣ Nat.card (GLAPPrimeCore p ↥J) := Subgroup.orderOf_dvd_natCard _ hq
  have h2 : orderOf c' ∣ p := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hcp))
  have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥J)) := CFSG.pPrimeCore_coprime_card
  have h3 : orderOf c' = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hcop) h1
  have h4 : c' = 1 := orderOf_eq_one_iff.1 h3
  exact congrArg Subtype.val h4

theorem le_pRank_aut_of_alt (hp : p.Prime) (hp2 : p ≠ 2) {x : MulAut K} (hx : orderOf x = p)
    {J₁ : Subgroup K} (hJ₁ : GLAPComponent p (fixSubgroup x) J₁) {m : ℕ} (hm : 5 ≤ m)
    (e : CFSG.HardMathSupport.Solomon.LocalBalance.barOf p J₁ ≃* alternatingGroup (Fin m)) :
    m / p + 1 ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut K)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hrJ : CFSG.Open.pRank p (⊤ : Subgroup ↥J₁) = m / p := by
    have hN : ¬ p ∣ Nat.card (GLAPPrimeCore p ↥J₁) := fun h =>
      hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd CFSG.pPrimeCore_coprime_card h)
    have h1 := CFSG.SectionRank.pRank_quotient_eq (GLAPPrimeCore p ↥J₁) hN
    have h2 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e
    have h3 := (CFSG.Quasithin.H13.A7.section_rank_alternating_odd_prime_rank).1 m p hp hp2
    rw [← h1]
    exact h2.trans h3
  obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup ↥J₁)
  rw [hrJ] at hEc
  set ι : ↥E →* K := J₁.subtype.comp E.subtype with hι
  have hιinj : Function.Injective ι := J₁.subtype_injective.comp E.subtype_injective
  have hιJ : ∀ a : ↥E, ι a ∈ J₁ := fun a => (a : ↥J₁).2
  have hfix : ∀ a : ↥E, x (ι a) = ι a := fun a => hJ₁.1 (hιJ a)
  set f : ↥E →* MulAut K := MulAut.conj.comp ι with hf
  have hcomm1 : ∀ a : ↥E, Commute (f a) x := by
    intro a
    ext k
    show ι a * x k * (ι a)⁻¹ = x (ι a * k * (ι a)⁻¹)
    rw [map_mul, map_mul, map_inv, hfix a]
  have hcomm : ∀ (a : ↥E) (b : ↥(Subgroup.zpowers x)),
      Commute (f a) ((Subgroup.zpowers x).subtype b) := by
    intro a b
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 b.2
    show Commute (f a) (b : MulAut K)
    rw [← hk]
    exact (hcomm1 a).zpow_right k
  set ψ : ↥E × ↥(Subgroup.zpowers x) →* MulAut K :=
    MonoidHom.noncommCoprod f (Subgroup.zpowers x).subtype hcomm with hψ
  have hEp : ∀ a : ↥E, a ^ p = 1 := fun a => Subtype.ext (hE.2 _ a.2)
  have hkey : ∀ a : ↥E, (∀ j ∈ J₁, ι a * j = j * ι a) → a = 1 := by
    intro a ha
    have hap : ι a ^ p = 1 := by rw [← map_pow, hEp a, map_one]
    exact hιinj ((eq_one_of_central_of_alt hp (by omega) e (hιJ a) hap ha).trans (map_one ι).symm)
  have hxp : ∀ y ∈ Subgroup.zpowers x, y ^ p = 1 := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hx, pow_orderOf_eq_one,
      one_zpow]
  have hx1 : x ≠ 1 := fun h => by
    rw [h, orderOf_one] at hx
    exact hp.one_lt.ne' hx.symm
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    have hab' : f a * (b : MulAut K) = 1 := hab
    have hfa : f a = (b : MulAut K)⁻¹ := eq_inv_of_mul_eq_one_left hab'
    have hfaz : f a ∈ Subgroup.zpowers x := hfa ▸ (Subgroup.zpowers x).inv_mem b.2
    have hfa1 : f a = 1 := by
      by_contra hne
      have hord : orderOf (f a) = p := orderOf_eq_prime (hxp _ hfaz) hne
      have hle : Subgroup.zpowers (f a) ≤ Subgroup.zpowers x := Subgroup.zpowers_le.2 hfaz
      have heq : Subgroup.zpowers (f a) = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hord, hx])
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (heq ▸ Subgroup.mem_zpowers x :
        x ∈ Subgroup.zpowers (f a))
      have hk' : f (a ^ k) = x := by rw [map_zpow]; exact hk
      have hak : a ^ k = 1 := by
        refine hkey _ fun j hj => ?_
        have h1 : x j = j := hJ₁.1 hj
        rw [← hk'] at h1
        have h2 : ι (a ^ k) * j * (ι (a ^ k))⁻¹ = j := h1
        calc ι (a ^ k) * j = ι (a ^ k) * j * (ι (a ^ k))⁻¹ * ι (a ^ k) := by group
          _ = j * ι (a ^ k) := by rw [h2]
      rw [hak, map_one] at hk'
      exact hx1 hk'.symm
    have ha1 : a = 1 := by
      refine hkey a fun j _ => ?_
      have h1 : f a j = j := by rw [hfa1]; rfl
      have h2 : ι a * j * (ι a)⁻¹ = j := h1
      calc ι a * j = ι a * j * (ι a)⁻¹ * ι a := by group
        _ = j * ι a := by rw [h2]
    have hb1 : (b : MulAut K) = 1 := by rw [← inv_inv (b : MulAut K), ← hfa, hfa1, inv_one]
    exact Prod.ext ha1 (Subtype.ext hb1)
  have hcommE : ∀ a b : ↥E, a * b = b * a := fun a b => hE.1.is_comm.comm a b
  have hcommU : ∀ u v : ↥E × ↥(Subgroup.zpowers x), u * v = v * u := by
    rintro ⟨a, b⟩ ⟨a', b'⟩
    refine Prod.ext (hcommE a a') ?_
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 b.2
    obtain ⟨k', hk'⟩ := Subgroup.mem_zpowers_iff.1 b'.2
    apply Subtype.ext
    show (b : MulAut K) * b' = b' * b
    rw [← hk, ← hk', ← zpow_add, ← zpow_add, add_comm]
  have hEA : CFSG.Open.IsElemAbelian p ψ.range := by
    refine ⟨⟨⟨fun y z => ?_⟩⟩, ?_⟩
    · obtain ⟨u, hu⟩ := y.2
      obtain ⟨v, hv⟩ := z.2
      apply Subtype.ext
      show (y : MulAut K) * z = z * y
      rw [← hu, ← hv, ← map_mul, ← map_mul, hcommU u v]
    · rintro _ ⟨⟨a, b⟩, rfl⟩
      rw [← map_pow]
      have : (a, b) ^ p = 1 := Prod.ext (hEp a) (Subtype.ext (hxp _ b.2))
      rw [this, map_one]
  have hcard : Nat.card ψ.range = p ^ (m / p + 1) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, Nat.card_zpowers, hx,
      hEc, pow_succ]
  exact CFSG.SectionRank.le_pRank hp.one_lt le_top hEA hcard

end Rank

section Classify

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem pumpup_alt_classify (hnl : Prop1116Design.InputAltNotLie)
    (hD : ∀ r, CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ p r)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) (hp : p.Prime)
    (hp2 : p ≠ 2) {m : ℕ} (hm7 : 7 ≤ m) (hm8 : m ≠ 8) (hq : CFSG.Open.IsQuasisimple K)
    (hcat : IsCatalogGroup (K ⧸ Subgroup.center K)) (hO : GLAPPrimeCore p K = ⊥) {x : MulAut K}
    (hx : orderOf x = p) {J₁ : Subgroup K} (hJ₁ : GLAPComponent p (fixSubgroup x) J₁)
    (hJt : Nonempty (PSimple p J₁ ≃* alternatingGroup (Fin m))) :
    (∃ k : ℕ, 1 ≤ k ∧ IsAltType (m + k * p) (K ⧸ Subgroup.center K)) ∨
      ∃ name : TauCeti.SporadicName, IsSporType name (K ⧸ Subgroup.center K) ∧
        ¬ SporNoAltDown p m name := by
  have hnab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hq
  have hxp : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  obtain ⟨i, ⟨f⟩⟩ := hcat
  cases i with
  | cyclic q hq' =>
    exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    apply f.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating n hn =>
    obtain ⟨k, hk, hnk⟩ := alt_family hp hp2 hq hO hn f hx hJ₁ (by omega) hJt
    subst hnk
    exact Or.inl ⟨k, hk, ⟨f⟩⟩
  | lie idx =>
    exfalso
    rcases lie_family_degree hnl hp hq idx (hD _) f hxp hJ₁ (by omega) hJt with h | h | h <;> omega
  | sporadic name =>
    exact Or.inr ⟨name, ⟨f⟩, spor_family hOut hp hp2 hq name f hx hJ₁ hJt⟩

end Classify

section SevenThree

theorem nonempty_center_quot_of_alt {X : Type*} [Group X] {m : ℕ} (hm : 4 ≤ m)
    (e : X ≃* alternatingGroup (Fin m)) : Nonempty ((X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin m)) := by
  have hZ : Subgroup.center X = ⊥ := by
    have h2 : Subgroup.center (alternatingGroup (Fin m)) = ⊥ :=
      alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hm)
    rw [eq_bot_iff]
    intro z hz
    have : e z ∈ Subgroup.center (alternatingGroup (Fin m)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz) g']
    rw [h2, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact (MulEquiv.map_eq_one_iff e).1 this
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩

@[expose] def HeNoAltSevenDown : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → GLAPPrimeCore 3 K = ⊥ →
    IsSporType .He (K ⧸ Subgroup.center K) → ∀ x : MulAut K, orderOf x = 3 →
      ∀ J₁ : Subgroup K, GLAPComponent 3 (fixSubgroup x) J₁ →
        ¬ IsAltType 7 (CFSG.HardMathSupport.Solomon.LocalBalance.barOf 3 J₁)

theorem input14_15_3_of_spor (hnl : Prop1116Design.InputAltNotLie)
    (hD : ∀ r, CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 3 r)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hS : ∀ name : TauCeti.SporadicName, name ≠ .He →
      CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic name).Group → SporNoAltDown 3 7 name) :
    Prop126.Input14_15_3 := by
  intro K _ _ hq hKG hO x hx J₁ hJ₁ hty
  rw [autFixSub_eq] at hJ₁
  have hJt : Nonempty (PSimple 3 J₁ ≃* alternatingGroup (Fin 7)) := by
    rcases hty with h | h
    · obtain ⟨e⟩ : Nonempty (CFSG.HardMathSupport.Solomon.LocalBalance.barOf 3 J₁ ≃*
        alternatingGroup (Fin 7)) := h
      exact nonempty_center_quot_of_alt (by norm_num) e
    · exact h.2.2
  obtain ⟨-, hcat⟩ := CFSG.HardMathSupport.Solomon.Coordinator.I1420.catalog_of_quasisimple hq hKG
  rcases pumpup_alt_classify hnl hD hOut Nat.prime_three (by norm_num) (by norm_num) (by norm_num)
    hq hcat hO hx hJ₁ hJt with ⟨k, hk, hA⟩ | ⟨name, hname, hns⟩
  · exact Or.inr ⟨k, hk, by rwa [mul_comm 3 k]⟩
  · by_cases hHe : name = .He
    · subst hHe
      exact Or.inl hname
    · obtain ⟨g⟩ := hname
      exact (hns (hS name hHe ((hKG.quotient _).of_surjective g.toMonoidHom g.surjective))).elim

theorem input14_15A7_of_spor (hnl : Prop1116Design.InputAltNotLie)
    (hD : ∀ r, CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 3 r)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hS : ∀ name : TauCeti.SporadicName, name ≠ .He →
      CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic name).Group → SporNoAltDown 3 7 name)
    (hHe : HeNoAltSevenDown) : Claims136b.Input14_15A7 := by
  intro K _ _ hq hKG hO x hx J₁ hJ₁ hty
  rw [autFixSub_eq] at hJ₁
  obtain ⟨e⟩ : Nonempty (CFSG.HardMathSupport.Solomon.LocalBalance.barOf 3 J₁ ≃*
    alternatingGroup (Fin 7)) := hty
  have hJt : Nonempty (PSimple 3 J₁ ≃* alternatingGroup (Fin 7)) :=
    nonempty_center_quot_of_alt (by norm_num) e
  obtain ⟨-, hcat⟩ := CFSG.HardMathSupport.Solomon.Coordinator.I1420.catalog_of_quasisimple hq hKG
  rcases pumpup_alt_classify hnl hD hOut Nat.prime_three (by norm_num) (by norm_num) (by norm_num)
    hq hcat hO hx hJ₁ hJt with ⟨k, hk, hA⟩ | ⟨name, hname, hns⟩
  · exact ⟨k, hk, by rwa [mul_comm 3 k]⟩
  · by_cases hHe : name = .He
    · subst hHe
      exact (hHe K hq hO hname x hx J₁ hJ₁ ⟨e⟩).elim
    · obtain ⟨g⟩ := hname
      exact (hns (hS name hHe ((hKG.quotient _).of_surjective g.toMonoidHom g.surjective))).elim

end SevenThree

section Input1314

variable {K : Type} [Group K] [Finite K]

theorem alt_of_center_odd (hq : CFSG.Open.IsQuasisimple K) {n : ℕ} (hn : 8 ≤ n)
    (f : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n))
    (hodd : Odd (Nat.card (Subgroup.center K))) : Nonempty (K ≃* alternatingGroup (Fin n)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  haveI : Group.IsPerfect K := Group.isPerfect_def.mpr hq.1
  set η : K →* alternatingGroup (Fin (m + 2)) :=
    f.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)) with hη
  have hηs : Function.Surjective η := f.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : η.ker = Subgroup.center K := by
    ext k
    rw [MonoidHom.mem_ker]
    show f (QuotientGroup.mk' (Subgroup.center K) k) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have h1 := CFSG.Alternating.Multipliers.card_ker_eq_one_of_odd (by omega) η hηs hker.le
    (by rw [hker]; exact hodd)
  have hinj : Function.Injective η := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact Subgroup.eq_bot_of_card_eq _ h1
  exact ⟨MulEquiv.ofBijective η ⟨hinj, hηs⟩⟩

theorem odd_card_center {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hO : GLAPPrimeCore p K = ⊥) :
    Odd (Nat.card (Subgroup.center K)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := (AltFacts2.isPGroup_center_of_core_eq_bot hp hO).exists_card_eq
  rw [ha]
  exact (hp.odd_of_ne_two hp2).pow

end Input1314

section I1415

theorem i1415At_of_spor (hnl : Prop1116Design.InputAltNotLie)
    (hD : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ r, CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ p r)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hS : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ m : ℕ, 9 < m → p ≤ m → ∀ name : TauCeti.SporadicName,
      CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic name).Group → SporNoAltDown p m name)
    (G : Type) [Group G] [Finite G] (p : ℕ) : CFSG.LocalAnalysis.GLTheoremA.I1415At G p := by
  intro hp hp2 X K J y m hX hK hyN hyp hcent hJ hm hJt
  haveI : Fact p.Prime := ⟨hp⟩
  have hpm : p ≤ m := by
    by_contra hlt
    push Not at hlt
    obtain ⟨eA⟩ := hJt
    apply CFSG.LocalAnalysis.GLTheoremA.AltDown.not_coprime_card_of_glaPComponent hp hJ
    have h1 : Nat.card ↥J = Nat.card (PQuot p J) * Nat.card (GLAPPrimeCore p ↥J) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    rw [h1, Nat.card_congr eA.toEquiv, card_alt m (by omega)]
    refine Nat.Coprime.mul_right ?_ CFSG.pPrimeCore_coprime_card
    refine (Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd (Nat.dvd_factorial (by norm_num)
      (by omega))) ?_)
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => by
      have := (Nat.Prime.dvd_factorial hp).1 h
      omega
  have hy : IsPGroup p (Subgroup.zpowers y) :=
    CFSG.LocalAnalysis.GLTheoremA.isPGroup_zpowers_of_pow_eq_one hyp
  obtain ⟨Q, _, _, K', y', ⟨eK⟩, hnorm, hpow, hcm, hcomp⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.exists_pQuot_transfer hp hy hyN
  obtain ⟨J', hJ', ⟨eJ⟩⟩ := hcomp J hJ
  have hqP : CFSG.Open.IsQuasisimple (PQuot p K) :=
    CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hK
  have hq' : CFSG.Open.IsQuasisimple ↥K' :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eK.symm hqP
  have hKG : CFSG.Open.IsKGroup (PQuot p K) := (hX.of_le hK.1).quotient _
  have hKG' : CFSG.Open.IsKGroup ↥K' := hKG.of_injective eK.toMonoidHom eK.injective
  have hcat : IsCatalogGroup (↥K' ⧸ Subgroup.center ↥K') :=
    CFSG.LocalAnalysis.GLTheoremA.I2611.isCatalogGroup_center_quotient' hKG' hq'
  have hO' : GLAPPrimeCore p ↥K' = ⊥ := by
    have h1 := CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCore_map_iso p eK.symm
    rw [glaPPrimeCore_quotient_eq_bot hp, Subgroup.map_bot] at h1
    exact h1.symm
  set β : MulAut ↥K' := K'.normalizerMonoidHom ⟨y', hnorm⟩ with hβ
  have hβapp : ∀ k : ↥K', ((β k : ↥K') : Q) = y' * (k : Q) * y'⁻¹ := fun k => rfl
  have hβp : β ^ p = 1 := by
    have h3 : (⟨y', hnorm⟩ : ↥(Subgroup.normalizer (K' : Set Q))) ^ p = 1 :=
      Subtype.ext (hpow p hyp)
    rw [hβ, ← map_pow, h3, map_one]
  have hfix : fixSubgroup β = (K' ⊓ Subgroup.centralizer ({y'} : Set Q)).subgroupOf K' := by
    ext k
    rw [mem_fixSubgroup, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hk
      have h1 : ((β k : ↥K') : Q) = (k : Q) := congrArg Subtype.val hk
      rw [hβapp] at h1
      exact ⟨k.2, (mul_inv_eq_iff_eq_mul.1 h1).symm⟩
    · rintro ⟨-, hk⟩
      apply Subtype.ext
      rw [hβapp]
      exact mul_inv_eq_iff_eq_mul.2 hk.symm
  have hβ1 : β ≠ 1 := by
    intro h1
    apply hcent
    apply hcm
    intro k hk
    have h2 : ((β ⟨k, hk⟩ : ↥K') : Q) = k := by rw [h1]; rfl
    rw [hβapp] at h2
    exact Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 h2).symm
  have hβo : orderOf β = p := orderOf_eq_prime hβp hβ1
  have hJ₁ : GLAPComponent p (fixSubgroup β) (J'.subgroupOf K') := by
    rw [hfix]
    exact CFSG.LocalAnalysis.GLTheoremA.glaPComponent_subgroupOf hp inf_le_left hJ'
  obtain ⟨f₁⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.nonempty_pQuot_equiv_subgroupOf p (hJ'.1.trans inf_le_left)
  obtain ⟨eA⟩ := hJt
  have hJt' : Nonempty (PSimple p (J'.subgroupOf K') ≃* alternatingGroup (Fin m)) :=
    nonempty_center_quot_of_alt (by omega) ((f₁.trans eJ.symm).trans eA)
  rcases pumpup_alt_classify hnl (hD p hp hp2) hOut hp hp2 (by omega) (by omega) hq' hcat hO' hβo
    hJ₁ hJt' with ⟨k, hk, ⟨f⟩⟩ | ⟨name, ⟨g⟩, hns⟩
  · obtain ⟨f'⟩ := alt_of_center_odd hq' (by omega) f (odd_card_center hp hp2 hO')
    exact ⟨k, hk, ⟨eK.symm.trans f'⟩⟩
  · exact (hns (hS p hp hp2 m hm hpm name
      ((hKG'.quotient _).of_surjective g.toMonoidHom g.surjective))).elim

end I1415

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1415

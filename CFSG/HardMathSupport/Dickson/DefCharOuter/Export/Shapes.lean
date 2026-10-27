module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.KData
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerCriterion

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Dickson.I271 (isChevSimple_of_mulEquiv isLTwoTwentySeven_of_mulEquiv
  isHatSix_of_mulEquiv pQuotEquiv pSimpleEquiv fixSubgroup_congr coprime_ker_mulEquiv)

structure SimpleNormalData (p : ℕ) {S : Type} [Group S] (β : MulAut S) (M : Subgroup S) :
    Prop where
  le : M ≤ fixSubgroup β
  normal : (M.subgroupOf (fixSubgroup β)).Normal
  simple : IsSimpleGroup ↥M
  nonabelian : ∃ a b : ↥M, a * b ≠ b * a
  solvable_quotient : Group.IsSolvable (↥(fixSubgroup β) ⧸ M.subgroupOf (fixSubgroup β))
  centralizer_trivial : ∀ x ∈ fixSubgroup β, (∀ m ∈ M, x * m = m * x) → x = 1
  chev : IsChevSimple p ↥M
  dvd : p ∣ Nat.card ↥M

section Simple

variable {p : ℕ} {S : Type} [Group S] [Finite S] {β : MulAut S} {M : Subgroup S}

theorem SimpleNormalData.eq_of_glaPComponent (h : SimpleNormalData p β M) {I : Subgroup S}
    (hI : GLAPComponent p (fixSubgroup β) I) : I = M := by
  haveI := h.normal
  have hIC : I ≤ fixSubgroup β := hI.1
  have hperf : ⁅I, I⁆ = I := glaPComponent_perfect hI
  have hIM : I ≤ M :=
    LieSemisimple.perfect_le_of_solvable_quotient h.le h.solvable_quotient hIC hperf
  have hsn : IsSubnormal I M := isSubnormal_of_le_of_le hI.2.1 hIM h.le
  rcases IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hsn h.simple with h0 | h0
  · exact absurd h0 (glaPComponent_ne_bot' hI)
  · exact h0

theorem SimpleNormalData.primeCore_eq_bot (hp : p.Prime) (h : SimpleNormalData p β M) :
    GLAPPrimeCore p ↥M = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := h.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore p ↥M) with h0 | h0
  · exact h0
  · exfalso
    have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥M)) := CFSG.pPrimeCore_coprime_card
    rw [h0, Subgroup.card_top] at hcop
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl p) h.dvd)

noncomputable def SimpleNormalData.pQuotEquivSelf (hp : p.Prime) (h : SimpleNormalData p β M) :
    PQuot p M ≃* ↥M :=
  (QuotientGroup.quotientMulEquivOfEq (h.primeCore_eq_bot hp)).trans QuotientGroup.quotientBot

theorem SimpleNormalData.center_pQuot_eq_bot (hp : p.Prime) (h : SimpleNormalData p β M) :
    Subgroup.center (PQuot p M) = ⊥ := by
  let e := h.pQuotEquivSelf hp
  haveI := h.simple
  haveI : IsSimpleGroup (PQuot p M) := e.isSimpleGroup
  refine b3Lie_center_eq_bot ?_
  obtain ⟨a, b, hab⟩ := h.nonabelian
  exact ⟨e.symm a, e.symm b, fun h' => hab (by
    have := congrArg e h'
    simpa using this)⟩

noncomputable def SimpleNormalData.pSimpleEquivSelf (hp : p.Prime) (h : SimpleNormalData p β M) :
    PSimple p M ≃* ↥M :=
  (QuotientGroup.quotientMulEquivOfEq (h.center_pQuot_eq_bot hp)).trans
    (QuotientGroup.quotientBot.trans (h.pQuotEquivSelf hp))

theorem SimpleNormalData.core_eq_bot (hp : p.Prime) (h : SimpleNormalData p β M) :
    GLAPPrimeCoreOf p (fixSubgroup β) = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := h.simple
  set C := fixSubgroup β with hC
  have hWC : ∀ w ∈ GLAPPrimeCoreOf p C, w ∈ C := fun w hw => Subgroup.map_subtype_le _ hw
  have hcon : ∀ t ∈ C, ∀ w ∈ GLAPPrimeCoreOf p C, t * w * t⁻¹ ∈ GLAPPrimeCoreOf p C :=
    fun t ht w hw => CFSG.HardMathSupport.Dickson.I271.conj_mem_glaPPrimeCoreOf p C ht hw
  have hndvd := not_dvd_card_glaPPrimeCoreOf hp C
  have hinf : GLAPPrimeCoreOf p C ⊓ M = ⊥ := by
    have hnorm : ((GLAPPrimeCoreOf p C ⊓ M).subgroupOf M).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have hgC : (g : S) ∈ C := h.le g.2
      refine ⟨?_, ?_⟩
      · exact hcon _ hgC _ hn.1
      · exact M.mul_mem (M.mul_mem g.2 hn.2) (M.inv_mem g.2)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((GLAPPrimeCoreOf p C ⊓ M).subgroupOf M)
      with h0 | h0
    · rw [eq_bot_iff]
      intro x hx
      have h1 : (⟨x, hx.2⟩ : ↥M) ∈ (GLAPPrimeCoreOf p C ⊓ M).subgroupOf M := hx
      rw [h0, Subgroup.mem_bot] at h1
      simpa using congrArg Subtype.val h1
    · exfalso
      have hMW : M ≤ GLAPPrimeCoreOf p C := by
        intro x hx
        have h1 : (⟨x, hx⟩ : ↥M) ∈ (GLAPPrimeCoreOf p C ⊓ M).subgroupOf M := by
          rw [h0]
          exact Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.1 h1).1
      exact hndvd (h.dvd.trans (Subgroup.card_dvd_of_le hMW))
  refine eq_bot_iff.2 fun w hw => ?_
  rw [Subgroup.mem_bot]
  have hwC := hWC w hw
  refine h.centralizer_trivial w hwC fun m hm => ?_
  have hmC : m ∈ C := h.le hm
  have hc1 : w * m * w⁻¹ * m⁻¹ ∈ GLAPPrimeCoreOf p C := by
    have h1 := (GLAPPrimeCoreOf p C).mul_mem hw
      (hcon m hmC w⁻¹ ((GLAPPrimeCoreOf p C).inv_mem hw))
    have e : w * m * w⁻¹ * m⁻¹ = w * (m * w⁻¹ * m⁻¹) := by group
    rw [e]
    exact h1
  have hc2 : w * m * w⁻¹ * m⁻¹ ∈ M := by
    have hnm := h.normal.conj_mem (⟨m, hmC⟩ : ↥C) (Subgroup.mem_subgroupOf.2 hm) ⟨w, hwC⟩
    have h3 : w * m * w⁻¹ ∈ M := Subgroup.mem_subgroupOf.1 hnm
    exact M.mul_mem h3 (M.inv_mem hm)
  have hc : w * m * w⁻¹ * m⁻¹ = 1 := by
    have h1 : w * m * w⁻¹ * m⁻¹ ∈ GLAPPrimeCoreOf p C ⊓ M := ⟨hc1, hc2⟩
    rwa [hinf, Subgroup.mem_bot] at h1
  calc w * m = (w * m * w⁻¹ * m⁻¹) * (m * w) := by group
    _ = m * w := by rw [hc, one_mul]

theorem SimpleNormalData.ofSimple (hs : IsSimpleGroup ↥(fixSubgroup β))
    (hnc : ∃ a b : ↥(fixSubgroup β), a * b ≠ b * a) (hchev : IsChevSimple p ↥(fixSubgroup β))
    (hdvd : p ∣ Nat.card ↥(fixSubgroup β)) : SimpleNormalData p β (fixSubgroup β) := by
  have hnorm : ((fixSubgroup β).subgroupOf (fixSubgroup β)).Normal := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  haveI := hnorm
  have hZ : Subgroup.center ↥(fixSubgroup β) = ⊥ := b3Lie_center_eq_bot hnc
  refine
    { le := le_rfl
      normal := hnorm
      simple := hs
      nonabelian := hnc
      solvable_quotient := ?_
      centralizer_trivial := fun x hx hxc => ?_
      chev := hchev
      dvd := hdvd }
  · haveI : Subsingleton (↥(fixSubgroup β) ⧸ (fixSubgroup β).subgroupOf (fixSubgroup β)) := by
      refine ⟨fun a b => ?_⟩
      induction a using QuotientGroup.induction_on with | H a => ?_
      induction b using QuotientGroup.induction_on with | H b => ?_
      exact QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2
        ((fixSubgroup β).mul_mem ((fixSubgroup β).inv_mem a.2) b.2))
    exact Group.isSolvable_of_comm fun a b => Subsingleton.elim _ _
  · have h1 : (⟨x, hx⟩ : ↥(fixSubgroup β)) ∈ Subgroup.center ↥(fixSubgroup β) :=
      Subgroup.mem_center_iff.2 fun y => (Subtype.ext (hxc y y.2)).symm
    rw [hZ, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1

end Simple

section OfSimple

variable {p : ℕ} {S : Type} [Group S] [Finite S] {β : MulAut S} {M : Subgroup S}

theorem OuterCentData.ofSimpleNormal (hp : p.Prime) (h : SimpleNormalData p β M)
    (cent : ¬ (p = 3 ∧ IsLTwoTwentySeven S) → ∀ w : MulAut S, Nat.Coprime p (orderOf w) →
      w * β = β * w → (∀ x ∈ fixSubgroup β, w x = x) → w ∈ innerAut S)
    (l227 : p = 3 → IsLTwoTwentySeven ↥M → ∀ β' : MulAut S, β' ^ 3 = 1 → β' * β = β * β' →
      M.map β'.toMonoidHom = M → ∃ i ∈ M, ∀ x ∈ M, β' x = i * x * i⁻¹) :
    OuterCentData p β where
  unique I J hI hJ := (h.eq_of_glaPComponent hI).trans (h.eq_of_glaPComponent hJ).symm
  chev I hI := by
    rw [h.eq_of_glaPComponent hI]
    exact isChevSimple_of_mulEquiv (h.pSimpleEquivSelf hp).symm h.chev
  core _ := h.core_eq_bot hp
  cent := cent
  noHatSix hp3 I hI := by
    subst hp3
    rw [h.eq_of_glaPComponent hI]
    intro hH
    have h1 := hH.2.1
    rw [h.center_pQuot_eq_bot hp, Subgroup.card_bot] at h1
    exact absurd h1 (by norm_num)
  l227 hp3 I hI hL β' hβ3 hβ hmap := by
    subst hp3
    obtain rfl := h.eq_of_glaPComponent hI
    obtain ⟨i, hi, hx⟩ := l227 rfl (isLTwoTwentySeven_of_mulEquiv (h.pSimpleEquivSelf hp) hL) β'
      hβ3 hβ hmap
    exact ⟨i, hi, fun x hxM => by rw [hx x hxM, mul_inv_cancel]; exact one_mem _⟩

end OfSimple

section NoComponent

theorem OuterCentData.ofNoComponent {p : ℕ} {S : Type} [Group S] {β : MulAut S}
    (hno : ∀ I : Subgroup S, ¬ GLAPComponent p (fixSubgroup β) I)
    (core : ¬ (p = 3 ∧ IsLTwoTwentySeven S) → GLAPPrimeCoreOf p (fixSubgroup β) = ⊥)
    (cent : ¬ (p = 3 ∧ IsLTwoTwentySeven S) → ∀ w : MulAut S, Nat.Coprime p (orderOf w) →
      w * β = β * w → (∀ x ∈ fixSubgroup β, w x = x) → w ∈ innerAut S) :
    OuterCentData p β where
  unique I _ hI _ := (hno I hI).elim
  chev I hI := (hno I hI).elim
  core := core
  cent := cent
  noHatSix hp3 I hI := by
    subst hp3
    exact (hno I hI).elim
  l227 hp3 I hI := by
    subst hp3
    exact (hno I hI).elim

theorem noComponent_of_solvable {p : ℕ} {S : Type} [Group S] [Finite S] {β : MulAut S}
    (hC : Group.IsSolvable ↥(fixSubgroup β)) :
    ∀ I : Subgroup S, ¬ GLAPComponent p (fixSubgroup β) I :=
  fun _ hI => not_glaPComponent_of_solvable hC hI

theorem false_of_perfect_le_solvable {G : Type} [Group G] {I X : Subgroup G}
    (hX : Group.IsSolvable ↥X) (hIX : I ≤ X) (hperf : ⁅I, I⁆ = I) (hne : I ≠ ⊥) : False := by
  haveI : Group.IsPerfect ↥I := Subgroup.isPerfect_iff.mpr hperf
  haveI : Group.IsSolvable ↥I :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hIX)
      (Subgroup.inclusion_injective hIX)
  haveI : Nontrivial ↥I := (Subgroup.nontrivial_iff_ne_bot I).2 hne
  exact Group.IsPerfect.not_isSolvable (G := ↥I) inferInstance

theorem noComponent_of_pConstrained {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {X P : Subgroup G} (hcore : GLAPPrimeCoreOf p X = ⊥) (hPX : P ≤ X)
    (hPn : (P.subgroupOf X).Normal) (hPp : IsPGroup p ↥P)
    (hc : ∀ x ∈ X, (∀ y ∈ P, x * y = y * x) → x ∈ P) :
    ∀ I : Subgroup G, ¬ GLAPComponent p X I := by
  intro I hI
  haveI : Fact p.Prime := ⟨hp⟩
  have hIX : I ≤ X := hI.1
  have hOI : GLAPPrimeCore p ↥I = ⊥ := by
    have h1 : GLAPPrimeCoreOf p I ≤ GLAPPrimeCoreOf p X :=
      glaPPrimeCoreOf_le_of_isSubnormal hp hI.2.1
    rw [hcore, le_bot_iff] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ I.subtype_injective).1 h1
  have hq : CFSG.Open.IsQuasisimple ↥I :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hOI).trans QuotientGroup.quotientBot)
      (CFSG.HardMathSupport.Solomon.UniquenessMaximal.isQuasisimple_quotient_of_glaPComponent hp hI)
  have hcomp : CFSG.Open.IsComponentOf I X := ⟨hIX, hI.2.1, hq⟩
  have hPsn : CFSG.Open.IsSubnormal P X :=
    CFSG.Open.IsSubnormal.step hPX hPn (CFSG.Open.IsSubnormal.refl X)
  have hIP : I ≤ P := by
    rcases b3Lie_comp_le_or_comm hcomp hPX hPsn with h | h
    · exact h
    · intro x hx
      refine hc x (hIX hx) fun y hy => ?_
      exact ((Subgroup.mem_centralizer_iff.1
        (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h hx)) y hy).symm
  haveI : Group.IsNilpotent ↥P := hPp.isNilpotent
  exact false_of_perfect_le_solvable inferInstance hIP (glaPComponent_perfect hI)
    (glaPComponent_ne_bot' hI)

end NoComponent

section Congr

theorem OuterCentData.of_congr {p : ℕ} (hp : p.Prime) {S T : Type} [Group S] [Group T] [Finite S]
    (e : S ≃* T) {β : MulAut S} (h : OuterCentData p (MulAut.congr e β)) :
    OuterCentData p β := by
  have hfix := fixSubgroup_congr e β
  have hmap : ∀ {I : Subgroup S}, GLAPComponent p (fixSubgroup β) I →
      GLAPComponent p (fixSubgroup (MulAut.congr e β)) (I.map e.toMonoidHom) := fun hI => by
    rw [hfix]
    exact glaPComponent_map hp e.toMonoidHom (coprime_ker_mulEquiv e _) hI
  have hL27 : IsLTwoTwentySeven S ↔ IsLTwoTwentySeven T :=
    ⟨isLTwoTwentySeven_of_mulEquiv e, isLTwoTwentySeven_of_mulEquiv e.symm⟩
  refine
    { unique := fun I J hI hJ => ?_
      chev := fun I hI => ?_
      core := fun hexc => ?_
      cent := fun hexc w hw hwβ hfixw => ?_
      noHatSix := fun hp3 I hI => ?_
      l227 := fun hp3 I hI hL β' hβ3 hβ'β hmapI => ?_ }
  · exact Subgroup.map_injective e.injective (h.unique _ _ (hmap hI) (hmap hJ))
  · exact isChevSimple_of_mulEquiv (pSimpleEquiv p (e.subgroupMap I)).symm (h.chev _ (hmap hI))
  · have h1 := h.core fun ⟨h3, h27⟩ => hexc ⟨h3, hL27.2 h27⟩
    rw [hfix, ← map_glaPPrimeCoreOf_of_injective p e.toMonoidHom e.injective] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h1
  · have hw' : Nat.Coprime p (orderOf (MulAut.congr e w)) := by
      rw [MulEquiv.orderOf_eq]
      exact hw
    have hcomm : MulAut.congr e w * MulAut.congr e β = MulAut.congr e β * MulAut.congr e w := by
      rw [← map_mul, ← map_mul, hwβ]
    have hfixw' : ∀ y ∈ fixSubgroup (MulAut.congr e β), MulAut.congr e w y = y := by
      intro y hy
      rw [hfix] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      have h1 := hfixw x hx
      simp [MulAut.congr_apply, h1]
    obtain ⟨t, ht⟩ := h.cent (fun ⟨h3, h27⟩ => hexc ⟨h3, hL27.2 h27⟩) _ hw' hcomm hfixw'
    refine ⟨e.symm t, ?_⟩
    apply (MulAut.congr e).injective
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
    exact ht
  · subst hp3
    intro hH
    exact h.noHatSix rfl _ (hmap hI) (isHatSix_of_mulEquiv (pQuotEquiv 3 (e.subgroupMap I)) hH)
  · subst hp3
    have hL' : IsLTwoTwentySeven (PSimple 3 (I.map e.toMonoidHom)) :=
      isLTwoTwentySeven_of_mulEquiv (pSimpleEquiv 3 (e.subgroupMap I)) hL
    have hβ3' : MulAut.congr e β' ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
    have hββ' : MulAut.congr e β' * MulAut.congr e β = MulAut.congr e β * MulAut.congr e β' := by
      rw [← map_mul, ← map_mul, hβ'β]
    have hmap' : (I.map e.toMonoidHom).map (MulAut.congr e β').toMonoidHom =
        I.map e.toMonoidHom := by
      rw [Subgroup.map_map]
      have hcomp : (MulAut.congr e β').toMonoidHom.comp e.toMonoidHom =
          e.toMonoidHom.comp β'.toMonoidHom := by
        ext x
        simp [MulAut.congr_apply]
      rw [hcomp, ← Subgroup.map_map, hmapI]
    obtain ⟨i', hi', hx'⟩ := h.l227 rfl _ (hmap hI) hL' _ hβ3' hββ' hmap'
    obtain ⟨i, hi, rfl⟩ := hi'
    refine ⟨i, hi, fun x hx => ?_⟩
    have h1 := hx' (e x) ⟨x, hx, rfl⟩
    rw [← map_glaPPrimeCoreOf_of_injective 3 e.toMonoidHom e.injective] at h1
    obtain ⟨z, hz, hze⟩ := h1
    have h2 : z = β' x * (i * x * i⁻¹)⁻¹ := by
      apply e.injective
      simpa [MulAut.congr_apply] using hze
    rwa [h2] at hz

end Congr

section Conj

theorem OuterCentData.of_conj {p : ℕ} (hp : p.Prime) {S : Type} [Group S] [Finite S]
    (ε β : MulAut S) (h : OuterCentData p (ε * β * ε⁻¹)) : OuterCentData p β := by
  refine OuterCentData.of_congr hp (ε : S ≃* S) (β := β) ?_
  have : MulAut.congr (ε : S ≃* S) β = ε * β * ε⁻¹ := by
    ext x
    rfl
  rw [this]
  exact h

end Conj

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export

module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Aux.Cube
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltCent
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltSn
public import CFSG.ClassicalInvolution.PerfectCase.Basic
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Aux.Defs

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.RankThree.PartTwo.KFacts CFSG.ComponentClassification.OuterAutomorphisms

theorem exists_perm_conj_of_pow_three {n : ℕ} (hn : 5 ≤ n)
    {β : MulAut (alternatingGroup (Fin n))} (h3 : β ^ 3 = 1) :
    ∃ σ : Equiv.Perm (Fin n), σ ^ 3 = 1 ∧ MulAut.conjNormal σ = β := by
  have hinj := CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n (by omega)
  by_cases h6 : n = 6
  · subst h6
    obtain ⟨τ, hτ⟩ := CFSG.HardMathSupport.Dickson.Sec6.I923.inner_of_pow_three
      CFSG.HardMathSupport.Dickson.Sec6.I923.not_three_dvd_card_outer_alt_six h3
    have hτσ : MulAut.conjNormal (τ : Equiv.Perm (Fin 6)) = β := by
      rw [← hτ]
      ext x
      simp [MulAut.conjNormal_apply, MulAut.conj_apply]
    refine ⟨(τ : Equiv.Perm (Fin 6)), hinj ?_, hτσ⟩
    rw [map_pow, hτσ, h3, map_one]
  · obtain ⟨σ, hσ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn
      h6).2 β
    refine ⟨σ, hinj ?_, hσ⟩
    rw [map_pow, hσ, h3, map_one]

theorem isInnerAut_of_alt {T : Type*} [Group T] {β' : Type} [Fintype β'] [DecidableEq β']
    (hβ : 5 ≤ Nat.card β') (e : T ≃* alternatingGroup β') {ρ : MulAut T} (h3 : ρ ^ 3 = 1) :
    IsInnerAut ρ := by
  set m := Fintype.card β' with hm
  have hm5 : 5 ≤ m := by rw [hm, ← Nat.card_eq_fintype_card]; exact hβ
  let E : T ≃* alternatingGroup (Fin m) := e.trans (Fintype.equivFin β').altCongrHom
  refine (isInnerAut_congr E ρ).1 ?_
  have hβ3 : (MulAut.congr E ρ) ^ 3 = 1 := by rw [← map_pow, h3, map_one]
  obtain ⟨σ, hσ3, hσ⟩ := exists_perm_conj_of_pow_three hm5 hβ3
  have hsign : σ.sign = 1 := by
    have h := congrArg Equiv.Perm.sign hσ3
    rw [map_pow, map_one] at h
    rcases Int.units_eq_one_or σ.sign with h1 | h1
    · exact h1
    · exact absurd h (by rw [h1]; decide)
  have hσA : σ ∈ alternatingGroup (Fin m) := Equiv.Perm.mem_alternatingGroup.2 hsign
  refine ⟨⟨σ, hσA⟩, ?_⟩
  rw [← hσ]
  ext x
  simp [MulAut.conjNormal_apply, MulAut.conj_apply]

theorem alt_layer_of_centralizer {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hn : 5 ≤ n)
    (e : (Y ⧸ Subgroup.center Y) ≃* alternatingGroup (Fin n)) {ξ : MulAut Y} (hξ : ξ ^ 3 = 1)
    {J : Subgroup Y} (hJ : GLAPComponent 3 (fixSub ξ) J) :
    ∃ (β' : Type) (_ : Fintype β') (_ : DecidableEq β'), 5 ≤ Nat.card β' ∧
      Nonempty ((barOf 3 J ⧸ Subgroup.center (barOf 3 J)) ≃* alternatingGroup β') := by
  have hKq : CFSG.Open.IsQuasisimple (barOf 3 J) := isQuasisimple_quotient_of_glaPComponent hJ
  have hLs : IsSimpleGroup (barOf 3 J ⧸ Subgroup.center (barOf 3 J)) := hKq.2
  have hLns : ¬ Group.IsSolvable (barOf 3 J ⧸ Subgroup.center (barOf 3 J)) := fun hs =>
    CFSG.ClassicalInvolution.not_isSolvable_of_open_isQuasisimple hKq
      (Group.isSolvable_of_subgroup_quotient (Subgroup.center (barOf 3 J)))
  let φ : Y →* Equiv.Perm (Fin n) :=
    (alternatingGroup (Fin n)).subtype.comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y)))
  have hφapp : ∀ y, φ y = ((e (QuotientGroup.mk y) : alternatingGroup (Fin n)) :
      Equiv.Perm (Fin n)) := fun y => rfl
  have hker : φ.ker ≤ Subgroup.center Y := by
    intro x hx
    rw [MonoidHom.mem_ker, hφapp] at hx
    have h1 : e (QuotientGroup.mk x) = 1 := Subtype.ext hx
    rw [map_eq_one_iff _ e.injective] at h1
    exact (QuotientGroup.eq_one_iff x).1 h1
  have hrange : φ.range = alternatingGroup (Fin n) := by
    ext p
    constructor
    · rintro ⟨y, rfl⟩
      exact (e (QuotientGroup.mk y)).2
    · intro hp
      obtain ⟨a, ha⟩ := e.surjective ⟨p, hp⟩
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective a
      exact ⟨y, by rw [hφapp, ha]⟩
  let g : ↥J →* barOf 3 J ⧸ Subgroup.center (barOf 3 J) :=
    (QuotientGroup.mk' (Subgroup.center (barOf 3 J))).comp
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J))
  have hg : Function.Surjective g :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hgk : ∀ j : ↥J, φ j = 1 → g j = 1 := by
    intro j hj
    have hjc := Subgroup.mem_center_iff.1 (hker (MonoidHom.mem_ker.2 hj))
    refine (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_center_iff.2 fun k => ?_)
    obtain ⟨j', rfl⟩ := QuotientGroup.mk_surjective k
    show QuotientGroup.mk j' * QuotientGroup.mk j = QuotientGroup.mk j * QuotientGroup.mk j'
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg _ (Subtype.ext (hjc j'))
  have hkerle : (φ.subgroupMap J).ker ≤ g.ker := by
    intro x hx
    rw [Subgroup.ker_subgroupMap, Subgroup.mem_subgroupOf] at hx
    exact MonoidHom.mem_ker.2 (hgk x (MonoidHom.mem_ker.1 hx))
  let f : ↥(J.map φ) →* barOf 3 J ⧸ Subgroup.center (barOf 3 J) :=
    MonoidHom.liftOfSurjective (φ.subgroupMap J) (φ.subgroupMap_surjective J) ⟨g, hkerle⟩
  have hf : Function.Surjective f := by
    intro l
    obtain ⟨x, rfl⟩ := hg l
    exact ⟨φ.subgroupMap J x, MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨g, hkerle⟩ x⟩
  let ᾱ : MulAut (Y ⧸ Subgroup.center Y) := centerDescend Y ξ
  have hᾱ : ∀ y : Y, ᾱ (QuotientGroup.mk y) = QuotientGroup.mk (ξ y) := fun y => rfl
  have hᾱ3 : ᾱ ^ 3 = 1 := by
    rw [← map_pow, hξ, map_one]
  let β : MulAut (alternatingGroup (Fin n)) := MulAut.congr e ᾱ
  have hβe : ∀ z, β (e z) = e (ᾱ z) := fun z => by simp [β]
  have hβ3 : β ^ 3 = 1 := by rw [← map_pow, hᾱ3, map_one]
  obtain ⟨σ, hσ3, hσ⟩ := exists_perm_conj_of_pow_three hn hβ3
  have hφ : ∀ y, φ (ξ y) = σ * φ y * σ⁻¹ := by
    intro y
    rw [hφapp, hφapp, ← hᾱ, ← hβe, ← hσ, MulAut.conjNormal_apply]
  obtain ⟨hle, hsn⟩ := isSubnormal_map_centralizer φ hrange hker ξ σ hφ hJ.2.1
  have hq : IsSubnormalQuotient (Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin n))))
      (barOf 3 J ⧸ Subgroup.center (barOf 3 J)) :=
    ⟨(J.map φ).subgroupOf (Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin n)))), hsn,
      f.comp (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom,
      hf.comp (MulEquiv.surjective _)⟩
  obtain ⟨β', _, _, h5, ⟨e'⟩⟩ := IsSubnormalQuotient.alt_of_centralizer hσ3 hLns hq
  exact ⟨β', inferInstance, inferInstance, h5, ⟨e'⟩⟩

theorem exists_mem_not_zpowers {G : Type*} [Group G] {Â : Subgroup G} {ξ : G} (hξ3 : ξ ^ 3 = 1)
    (hcard : Nat.card Â = 9) : ∃ η ∈ Â, η ∉ Subgroup.zpowers ξ := by
  by_contra hno
  push Not at hno
  have hfin : Finite (Subgroup.zpowers ξ) := by
    have : Nat.card (Subgroup.zpowers ξ) ≠ 0 := by
      rw [Nat.card_zpowers]
      exact (orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, hξ3⟩)).ne'
    exact Nat.finite_of_card_ne_zero this
  have hle : Â ≤ Subgroup.zpowers ξ := fun η hη => hno η hη
  have h1 : Nat.card Â ≤ Nat.card (Subgroup.zpowers ξ) := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers] at h1
  have h2 : orderOf ξ ∣ 3 := orderOf_dvd_of_pow_eq_one hξ3
  have h3 : orderOf ξ ≤ 3 := Nat.le_of_dvd (by norm_num) h2
  omega

theorem inducedBarHom_pow_three {Y : Type*} [Group Y] (J : Subgroup Y) {η : MulAut Y}
    (h : η ∈ stabAut J) (h3 : η ^ 3 = 1) : inducedBarHom J ⟨η, h⟩ ^ 3 = 1 := by
  rw [← map_pow]
  have : (⟨η, h⟩ : ↥(stabAut J)) ^ 3 = 1 := Subtype.ext (by simpa using h3)
  rw [this, map_one]

theorem false_of_alt (hU : L2OrderUnique) (hF : L2FieldFixed) {V : InndiagVocab} {Y : Type}
    [Group Y] [Finite Y] {Â : Subgroup (MulAut Y)} {ξ : MulAut Y} {J : Subgroup Y} {q : ℕ}
    (c : Y1431Cfg V Y Â ξ J q) {n : ℕ} (hn : 5 ≤ n)
    (e : (Y ⧸ Subgroup.center Y) ≃* alternatingGroup (Fin n)) : False := by
  have hξ3 : ξ ^ 3 = 1 := c.elemAbelian.2 ξ c.mem
  obtain ⟨η, hηA, hηξ⟩ := exists_mem_not_zpowers hξ3 c.card
  have hη3 : η ^ 3 = 1 := c.elemAbelian.2 η hηA
  obtain ⟨⟨h, hfld⟩, hnt⟩ := c.field η hηA hηξ
  have hα1 : inducedBarHom J ⟨η, h⟩ ≠ 1 := fun h1 => hnt ⟨h, h1⟩
  have hα3 := inducedBarHom_pow_three J h hη3
  have hQ : CFSG.Open.IsQuasisimple (barOf 3 J) := isQuasisimple_quotient_of_glaPComponent c.comp
  obtain ⟨β', _, _, h5, ⟨e'⟩⟩ := alt_layer_of_centralizer hn e hξ3 c.comp
  have hinn : IsInnerAut (centerDescend (barOf 3 J) (inducedBarHom J ⟨η, h⟩)) := by
    refine isInnerAut_of_alt h5 e' ?_
    rw [← map_pow, hα3, map_one]
  exact not_isInnerAut_descend_of_fieldAut hU hF hQ hα3 hα1 hfld c.typeL2 c.not_dvd c.ne_eight hinn

theorem cfg_cube (hU : L2OrderUnique) (hF : L2FieldFixed) {V : InndiagVocab} {Y : Type}
    [Group Y] [Finite Y] {Â : Subgroup (MulAut Y)} {ξ : MulAut Y} {J : Subgroup Y} {q : ℕ}
    (c : Y1431Cfg V Y Â ξ J q) : ∃ q0 : ℕ, 4 ≤ q0 ∧ q = q0 ^ 3 := by
  have hξ3 : ξ ^ 3 = 1 := c.elemAbelian.2 ξ c.mem
  obtain ⟨η, hηA, hηξ⟩ := exists_mem_not_zpowers hξ3 c.card
  have hη3 : η ^ 3 = 1 := c.elemAbelian.2 η hηA
  obtain ⟨⟨h, hfld⟩, hnt⟩ := c.field η hηA hηξ
  have hα1 : inducedBarHom J ⟨η, h⟩ ≠ 1 := fun h1 => hnt ⟨h, h1⟩
  have hα3 := inducedBarHom_pow_three J h hη3
  have hQ : CFSG.Open.IsQuasisimple (barOf 3 J) := isQuasisimple_quotient_of_glaPComponent c.comp
  exact cube_of_fieldAut hU hF hQ hα3 hα1 hfld c.typeL2 c.not_dvd c.ne_eight

end CFSG.HardMathSupport.Dickson.Sec6.I1431

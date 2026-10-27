module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Aux.Defs
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop42CaseThreeProof

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs
  CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

section BarMap

variable {Y P : Type} [Group Y] [Finite Y] [Group P] [Finite P]

@[expose] noncomputable def barMap (π : Y →* P) (J : Subgroup Y) : barOf 3 J →* barOf 3 (J.map π) :=
  QuotientGroup.lift _
    ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥(J.map π))).comp (π.subgroupMap J))
    (fun x hx => by
      rw [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff _).2
        (map_gLAPPrimeCore_le' 3 (π.subgroupMap J) (π.subgroupMap_surjective J) ⟨x, hx, rfl⟩))

theorem barMap_mk (π : Y →* P) (J : Subgroup Y) (j : ↥J) :
    barMap π J (QuotientGroup.mk j) = QuotientGroup.mk (π.subgroupMap J j) :=
  rfl

theorem barMap_surjective (π : Y →* P) (J : Subgroup Y) : Function.Surjective (barMap π J) := by
  intro y
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥(J.map π)) y
  obtain ⟨j, rfl⟩ := π.subgroupMap_surjective J a
  exact ⟨QuotientGroup.mk j, rfl⟩

theorem barMap_ker_le_center (π : Y →* P) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center Y) (α : MulAut Y) (ψ : MulAut P)
    (hαψ : ∀ y, π (α y) = ψ (π y)) {J : Subgroup Y}
    (hJ : GLAPComponent 3 (fixSubgroup α) J) : (barMap π J).ker ≤ Subgroup.center (barOf 3 J) := by
  have hA := glaPComponent_map_fixSubgroup π hker α ψ hαψ hπ Nat.prime_three hJ
  have hJq : CFSG.Open.IsQuasisimple (barOf 3 J) :=
    isQuasisimple_barOf_of_glaPComponent Nat.prime_three hJ
  have hAq : CFSG.Open.IsQuasisimple (barOf 3 (J.map π)) :=
    isQuasisimple_barOf_of_glaPComponent Nat.prime_three hA
  have hJq' : CFSG.IsQuasisimple (barOf 3 J) :=
    ⟨Group.isPerfect_def.2 hJq.1, hJq.2, I923.exists_not_comm_of_quasisimple hJq⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hJq' (barMap π J).normal_ker with h | h
  · exfalso
    have hall : ∀ y : barOf 3 (J.map π), y = 1 := by
      intro y
      obtain ⟨x, rfl⟩ := barMap_surjective π J y
      have : x ∈ (barMap π J).ker := by rw [h]; exact Subgroup.mem_top x
      exact this
    have hsub : Subsingleton (barOf 3 (J.map π)) := ⟨fun a b => (hall a).trans (hall b).symm⟩
    have hs2 : Subsingleton (barOf 3 (J.map π) ⧸ Subgroup.center (barOf 3 (J.map π))) :=
      (QuotientGroup.mk'_surjective (Subgroup.center (barOf 3 (J.map π)))).subsingleton
    exact (not_nontrivial_iff_subsingleton.2 hs2) hAq.2.toNontrivial
  · exact h

end BarMap

section Field

variable {Q Q' : Type} [Group Q] [Group Q']

@[expose] noncomputable def centerQuotEquiv (hQ : Group.IsPerfect Q) (f : Q →* Q')
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center Q) :
    (Q ⧸ Subgroup.center Q) ≃* (Q' ⧸ Subgroup.center Q') :=
  (QuotientGroup.quotientMulEquivOfEq (show Subgroup.center Q =
      ((QuotientGroup.mk' (Subgroup.center Q')).comp f).ker by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact (CFSG.LocalCores.comap_center_eq_of_perfect hQ f hf hker).symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp hf))

theorem isFieldAutPSLn_map (hQ : Group.IsPerfect Q) (f : Q →* Q') (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center Q) {α : MulAut Q} {α' : MulAut Q'}
    (hαα' : ∀ x, f (α x) = α' (f x)) {n : ℕ} (h : IsFieldAutPSLn n α) :
    IsFieldAutPSLn n α' := by
  obtain ⟨F, hFf, hFfin, θ, σ, φ, γ, hφ, hθ⟩ := h
  refine ⟨F, hFf, hFfin, (centerQuotEquiv hQ f hf hker).symm.trans θ, σ, φ, γ, hφ, fun y' => ?_⟩
  obtain ⟨y, rfl⟩ := hf y'
  rw [← hαα' y]
  have h1 : ((centerQuotEquiv hQ f hf hker).symm.trans θ) (QuotientGroup.mk (f (α y))) =
      θ (QuotientGroup.mk (α y)) := by
    show θ ((centerQuotEquiv hQ f hf hker).symm (QuotientGroup.mk (f (α y)))) = _
    congr 1
    rw [MulEquiv.symm_apply_eq]
    rfl
  have h2 : ((centerQuotEquiv hQ f hf hker).symm.trans θ) (QuotientGroup.mk (f y)) =
      θ (QuotientGroup.mk y) := by
    show θ ((centerQuotEquiv hQ f hf hker).symm (QuotientGroup.mk (f y))) = _
    congr 1
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [h1, h2]
  exact hθ y

theorem eq_one_of_map_eq {Q Q' : Type} [Group Q] [Group Q'] (hQ : CFSG.Open.IsQuasisimple Q)
    (f : Q →* Q') (hker : f.ker ≤ Subgroup.center Q) {α : MulAut Q} (h : ∀ x, f (α x) = f x) :
    α = 1 := by
  apply eq_one_of_centerDescend_eq_one hQ
  ext x
  induction x using QuotientGroup.induction_on with
  | H x =>
    rw [centerDescend_mk]
    show (QuotientGroup.mk (α x) : Q ⧸ Subgroup.center Q) = QuotientGroup.mk x
    rw [QuotientGroup.eq]
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]

end Field

section Descend

variable {Y P : Type} [Group Y] [Finite Y] [Group P] [Finite P]

@[expose] noncomputable def descendHom (e : (Y ⧸ Subgroup.center Y) ≃* P) : MulAut Y →* MulAut P :=
  (MulAut.congr e).toMonoidHom.comp (centerDescend Y)

theorem descendHom_apply (e : (Y ⧸ Subgroup.center Y) ≃* P) (α : MulAut Y) (y : Y) :
    descendHom e α (e (QuotientGroup.mk y)) = e (QuotientGroup.mk (α y)) :=
  (descend_compat e α y).symm

@[expose] noncomputable def descendProj (e : (Y ⧸ Subgroup.center Y) ≃* P) : Y →* P :=
  (e : (Y ⧸ Subgroup.center Y) →* P).comp (QuotientGroup.mk' (Subgroup.center Y))

theorem descendProj_apply (e : (Y ⧸ Subgroup.center Y) ≃* P) (y : Y) :
    descendProj e y = e (QuotientGroup.mk y) :=
  rfl

theorem descendProj_surjective (e : (Y ⧸ Subgroup.center Y) ≃* P) :
    Function.Surjective (descendProj e) := fun p => by
  obtain ⟨q, rfl⟩ := e.surjective p
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
  exact ⟨y, rfl⟩

theorem descendProj_ker_le (e : (Y ⧸ Subgroup.center Y) ≃* P) :
    (descendProj e).ker ≤ Subgroup.center Y := by
  intro y hy
  have h1 : (QuotientGroup.mk y : Y ⧸ Subgroup.center Y) = 1 :=
    e.injective (by simpa [descendProj_apply] using hy)
  exact (QuotientGroup.eq_one_iff y).1 h1

theorem descendHom_compat (e : (Y ⧸ Subgroup.center Y) ≃* P) (α : MulAut Y) (y : Y) :
    descendProj e (α y) = descendHom e α (descendProj e y) := by
  rw [descendProj_apply, descendProj_apply]
  exact (descendHom_apply e α y).symm

theorem descendHom_injective (e : (Y ⧸ Subgroup.center Y) ≃* P) (hY : CFSG.Open.IsQuasisimple Y) :
    Function.Injective (descendHom e) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  apply eq_one_of_centerDescend_eq_one hY
  apply (MulAut.congr e).injective
  rw [map_one]
  exact ha

theorem descendHom_mem_stabAut (e : (Y ⧸ Subgroup.center Y) ≃* P) {J : Subgroup Y}
    {γ : MulAut Y} (hγ : γ ∈ stabAut J) : descendHom e γ ∈ stabAut (J.map (descendProj e)) := by
  set π := descendProj e with hπ
  set ψ := descendHom e γ with hψ
  have hJγ : J.map γ.toMonoidHom = J := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact (hγ j).2 hj
    · intro hy
      exact ⟨γ.symm y, (hγ (γ.symm y)).1 (by simpa using hy), by simp⟩
  have hcomp : (ψ : P →* P).comp π = π.comp γ.toMonoidHom := by
    ext y
    exact (descendHom_compat e γ y).symm
  have hmap : (J.map π).map ψ.toMonoidHom = J.map π := by
    rw [Subgroup.map_map, show ψ.toMonoidHom.comp π = π.comp γ.toMonoidHom from hcomp,
      ← Subgroup.map_map, hJγ]
  intro p
  constructor
  · intro hp
    rw [← hmap] at hp
    exact (Subgroup.mem_map_iff_mem (f := ψ.toMonoidHom) ψ.injective).1 hp
  · intro hp
    have : ψ p ∈ (J.map π).map ψ.toMonoidHom := Subgroup.mem_map_of_mem _ hp
    rwa [hmap] at this

theorem barMap_inducedBarHom (e : (Y ⧸ Subgroup.center Y) ≃* P) {J : Subgroup Y}
    {γ : MulAut Y} (hγ : γ ∈ stabAut J) (x : barOf 3 J) :
    barMap (descendProj e) J (inducedBarHom J ⟨γ, hγ⟩ x) =
      inducedBarHom (J.map (descendProj e)) ⟨descendHom e γ, descendHom_mem_stabAut e hγ⟩
        (barMap (descendProj e) J x) := by
  induction x using QuotientGroup.induction_on with
  | H j =>
    rw [inducedBarHom_mk, barMap_mk, barMap_mk, inducedBarHom_mk]
    congr 1
    apply Subtype.ext
    exact descendHom_compat e γ (j : Y)

structure S1431Cfg (P : Type) [Group P] (A : Subgroup (MulAut P)) (ψ : MulAut P) (J : Subgroup P)
    (q : ℕ) : Prop where
  elemAbelian : IsElemAbelian 3 A
  card : Nat.card A = 9
  mem : ψ ∈ A
  ne_one : ψ ≠ 1
  comp : GLAPComponent 3 (Lemma510Ns.fixSub ψ) J
  typeL2 : IsTypeL2 q (barOf 3 J)
  not_dvd : ¬ 3 ∣ q
  ne_eight : q ≠ 8
  field : ∀ η ∈ A, η ∉ Subgroup.zpowers ψ → FieldBar 2 J η ∧ ¬ TrivBar J η

theorem Y1431Cfg.descend {V : InndiagVocab} {Â : Subgroup (MulAut Y)} {ξ : MulAut Y}
    {J : Subgroup Y} {q : ℕ} (c : Y1431Cfg V Y Â ξ J q) (e : (Y ⧸ Subgroup.center Y) ≃* P) :
    S1431Cfg P (Â.map (descendHom e)) (descendHom e ξ) (J.map (descendProj e)) q := by
  set π := descendProj e with hπ
  have hinj := descendHom_injective e c.quasisimple
  have hπs := descendProj_surjective e
  have hπk := descendProj_ker_le e
  have hJq : CFSG.Open.IsQuasisimple (barOf 3 J) :=
    isQuasisimple_barOf_of_glaPComponent Nat.prime_three c.comp
  have hperf : Group.IsPerfect (barOf 3 J) := Group.isPerfect_def.2 hJq.1
  have hker := barMap_ker_le_center π hπs hπk ξ (descendHom e ξ) (descendHom_compat e ξ) c.comp
  refine ⟨?_, ?_, ⟨ξ, c.mem, rfl⟩, ?_, ?_, ?_, c.not_dvd, c.ne_eight, ?_⟩
  ·
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · obtain ⟨a', ha', ha'e⟩ := Subgroup.mem_map.1 a.2
      obtain ⟨b', hb', hb'e⟩ := Subgroup.mem_map.1 b.2
      apply Subtype.ext
      show (a : MulAut P) * b = b * a
      rw [← ha'e, ← hb'e, ← map_mul, ← map_mul]
      congr 1
      have := c.elemAbelian.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩
      exact congrArg Subtype.val this
    · obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 ha
      rw [← map_pow, c.elemAbelian.2 a' ha', map_one]
  · rw [Subgroup.card_map_of_injective hinj, c.card]
  · intro h
    exact c.ne_one (hinj (by rw [map_one]; exact h))
  · exact glaPComponent_map_fixSubgroup π hπk ξ (descendHom e ξ) (descendHom_compat e ξ) hπs
      Nat.prime_three c.comp
  ·
    obtain ⟨F, hF, hFin, hcard, ⟨g⟩⟩ := c.typeL2
    exact ⟨F, hF, hFin, hcard, ⟨(centerQuotEquiv hperf (barMap π J) (barMap_surjective π J)
      hker).symm.trans g⟩⟩
  ·
    intro η hη hηψ
    obtain ⟨η', hη', rfl⟩ := Subgroup.mem_map.1 hη
    have hη'ξ : η' ∉ Subgroup.zpowers ξ := by
      intro hmem
      apply hηψ
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hmem
      exact ⟨k, by rw [map_zpow]⟩
    obtain ⟨⟨h, hfld⟩, hntriv⟩ := c.field η' hη' hη'ξ
    refine ⟨⟨descendHom_mem_stabAut e h, ?_⟩, ?_⟩
    · exact isFieldAutPSLn_map hperf (barMap π J) (barMap_surjective π J) hker
        (barMap_inducedBarHom e h) hfld
    · rintro ⟨h', hone⟩
      apply hntriv
      refine ⟨h, ?_⟩
      apply eq_one_of_map_eq hJq (barMap π J) hker
      intro x
      rw [barMap_inducedBarHom e h x]
      have : inducedBarHom (J.map π) ⟨descendHom e η', descendHom_mem_stabAut e h⟩ = 1 := hone
      rw [this]
      rfl

end Descend

end CFSG.HardMathSupport.Dickson.Sec6.I1431

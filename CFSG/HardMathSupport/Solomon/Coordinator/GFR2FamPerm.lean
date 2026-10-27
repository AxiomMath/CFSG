module

public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamAltCore
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB Equiv Equiv.Perm B3FamAlt
open scoped commutatorElement

section Perm

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

@[expose] def cycSub (σ : Perm Ω) : Subgroup (Perm Ω) :=
  Subgroup.closure (σ.cycleFactorsFinset : Set (Perm Ω))

theorem cycSub_le_centAlt {σ : Perm Ω} (hσ : σ ^ 3 = 1) : cycSub σ ≤ centAlt σ :=
  (Subgroup.closure_le _).2 fun c hc => mem_centAlt.2
    ⟨(self_mem_cycle_factors_commute hc).eq,
      (cycle_pow_eq_one Nat.prime_three (by norm_num) hσ hc).2⟩

theorem cycSub_comm {σ : Perm Ω} {a b : Perm Ω} (ha : a ∈ cycSub σ) (hb : b ∈ cycSub σ) :
    a * b = b * a := by
  set S : Set (Perm Ω) := (σ.cycleFactorsFinset : Set (Perm Ω)) with hS
  have hs : ∀ c ∈ S, ∀ d ∈ S, c * d = d * c := by
    intro c hc d hd
    by_cases h : c = d
    · rw [h]
    · exact (cycleFactorsFinset_mem_commute σ hc hd h).eq
  have h1 : S ⊆ Subgroup.centralizer S := fun c hc d hd => (hs d hd c hc)
  have h2 : cycSub σ ≤ Subgroup.centralizer S :=
    (Subgroup.closure_le_centralizer_centralizer S).trans (Subgroup.centralizer_le h1)
  have h3 : S ⊆ Subgroup.centralizer ({a} : Set (Perm Ω)) := by
    intro c hc
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 (h2 ha) c hc)
  have h4 : cycSub σ ≤ Subgroup.centralizer ({a} : Set (Perm Ω)) :=
    (Subgroup.closure_le _).2 h3
  exact (Subgroup.mem_centralizer_singleton_iff.1 (h4 hb)).symm

theorem conj_mem_cycSub {σ g : Perm Ω} (hg : g * σ = σ * g) {h : Perm Ω} (hh : h ∈ cycSub σ) :
    g * h * g⁻¹ ∈ cycSub σ := by
  have : cycSub σ ≤ (cycSub σ).comap (MulAut.conj g).toMonoidHom := by
    refine (Subgroup.closure_le _).2 fun c hc => ?_
    exact Subgroup.subset_closure (conj_mem_cycleFactors hg hc)
  exact this hh

theorem cycSub_normal {σ : Perm Ω} (hσ : σ ^ 3 = 1) :
    ((cycSub σ).subgroupOf (centAlt σ)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (cycSub_le_centAlt hσ)]
  intro g hg
  have hgσ : g * σ = σ * g := (mem_centAlt.1 hg).1
  have hg' : g⁻¹ * σ = σ * g⁻¹ := by
    have := congrArg (fun t => g⁻¹ * t * g⁻¹) hgσ
    simpa [mul_assoc] using this.symm
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_cycSub hgσ hh, fun hh => ?_⟩
  have := conj_mem_cycSub hg' hh
  simpa [mul_assoc] using this

theorem isQuasisimple_nontrivial {X : Type*} [Group X] (hq : CFSG.Open.IsQuasisimple X) :
    Nontrivial X := by
  obtain ⟨-, hs⟩ := hq
  exact (QuotientGroup.mk'_surjective (Subgroup.center X)).nontrivial

theorem comm_cycSub_of_component {σ : Perm Ω} (hσ : σ ^ 3 = 1) {J : Subgroup (Perm Ω)}
    (hJC : J ≤ centAlt σ) (hsn : IsSubnormal J (centAlt σ))
    (hq : CFSG.Open.IsQuasisimple ↥J) : ∀ j ∈ J, ∀ v ∈ cycSub σ, j * v = v * j := by
  set C := centAlt σ with hC
  set V := cycSub σ with hV
  have hVC : V ≤ C := cycSub_le_centAlt hσ
  have hcomp : IsComponentOf (J.subgroupOf C) ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · have h1 := isSubnormal_comap' C.subtype hsn
      rw [show C.comap C.subtype = ⊤ from Subgroup.subgroupOf_self C] at h1
      exact h1
    · exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hJC).symm hq
  have hVs : IsSubnormal (V.subgroupOf C) ⊤ := isSubnormal_of_normal (cycSub_normal hσ)
  haveI : Group.IsSolvable ↥(V.subgroupOf C) := Group.isSolvable_of_comm fun a b =>
    Subtype.ext (Subtype.ext (cycSub_comm a.2 b.2))
  have hbot := CFSG.ComponentClassification.LocalComponents.commutes_with_solvable_subnormal
    (J.subgroupOf C) (V.subgroupOf C) hcomp hVs
  intro j hj v hv
  have hmem := Subgroup.commutator_mem_commutator
    (show (⟨j, hJC hj⟩ : ↥C) ∈ J.subgroupOf C from hj)
    (show (⟨v, hVC hv⟩ : ↥C) ∈ V.subgroupOf C from hv)
  rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact congrArg Subtype.val hmem

theorem exists_zpow_of_comm_cycles {σ w : Perm Ω} (hw : w * σ = σ * w)
    (hcyc : ∀ c ∈ σ.cycleFactorsFinset, w * c = c * w) {a : Ω} (ha : σ a ≠ a) :
    ∃ i : ℤ, w a = (σ ^ i) a := by
  have hc : σ.cycleOf a ∈ σ.cycleFactorsFinset := by
    rw [cycleOf_mem_cycleFactorsFinset_iff, Perm.mem_support]; exact ha
  have h1 := hcyc _ hc
  have hconj : w * σ.cycleOf a * w⁻¹ = σ.cycleOf a := by
    rw [h1]; group
  have haS : a ∈ (σ.cycleOf a).support := by
    rw [Perm.mem_support, cycleOf_apply_self]; exact ha
  have hwa : w a ∈ (w * σ.cycleOf a * w⁻¹).support := by
    rw [support_conj]
    exact Finset.mem_map.2 ⟨a, haS, rfl⟩
  rw [hconj, mem_support_cycleOf_iff] at hwa
  obtain ⟨i, hi⟩ := hwa.1
  exact ⟨i, hi.symm⟩

theorem comm_apply_zpow {σ w : Perm Ω} (hw : w * σ = σ * w) (i : ℤ) (x : Ω) :
    w ((σ ^ i) x) = (σ ^ i) (w x) :=
  congrArg (fun f : Perm Ω => f x) ((Commute.zpow_right (show Commute w σ from hw) i).eq)

theorem comm_on_support {σ w₁ w₂ : Perm Ω} (h₁ : w₁ * σ = σ * w₁) (h₂ : w₂ * σ = σ * w₂)
    (c₁ : ∀ c ∈ σ.cycleFactorsFinset, w₁ * c = c * w₁)
    (c₂ : ∀ c ∈ σ.cycleFactorsFinset, w₂ * c = c * w₂) {a : Ω} (ha : σ a ≠ a) :
    w₁ (w₂ a) = w₂ (w₁ a) := by
  obtain ⟨i₁, hi₁⟩ := exists_zpow_of_comm_cycles h₁ c₁ ha
  obtain ⟨i₂, hi₂⟩ := exists_zpow_of_comm_cycles h₂ c₂ ha
  rw [hi₂, comm_apply_zpow h₁, hi₁, comm_apply_zpow h₂, hi₂]
  rw [← Perm.mul_apply, ← Perm.mul_apply, ← zpow_add, ← zpow_add, add_comm]

@[expose] def fixSupp (σ : Perm Ω) : Subgroup (Perm Ω) where
  carrier := {g | ∀ x, σ x ≠ x → g x = x}
  mul_mem' := fun {a b} ha hb x hx => by
    rw [Perm.mul_apply, hb x hx, ha x hx]
  one_mem' := fun x _ => rfl
  inv_mem' := fun {a} ha x hx => by
    have := ha x hx
    rw [Perm.inv_eq_iff_eq]
    exact this.symm

theorem apply_ne_of_comm {σ w : Perm Ω} (hw : w * σ = σ * w) {x : Ω} (hx : σ x ≠ x) :
    σ (w x) ≠ w x := by
  intro h
  have : σ (w x) = w (σ x) := (congrArg (fun f : Perm Ω => f x) hw.symm)
  rw [this] at h
  exact hx (w.injective h)

theorem le_fixSupp_of_component {σ : Perm Ω} (hσ : σ ^ 3 = 1) {J : Subgroup (Perm Ω)}
    (hJC : J ≤ centAlt σ) (hsn : IsSubnormal J (centAlt σ))
    (hq : CFSG.Open.IsQuasisimple ↥J) : J ≤ fixSupp σ := by
  have hcomm := comm_cycSub_of_component hσ hJC hsn hq
  have hcyc : ∀ j ∈ J, ∀ c ∈ σ.cycleFactorsFinset, j * c = c * j := fun j hj c hc =>
    hcomm j hj c (Subgroup.subset_closure hc)
  have hσc : ∀ j ∈ J, j * σ = σ * j := fun j hj => (mem_centAlt.1 (hJC hj)).1
  have hcommut : ∀ a ∈ J, ∀ b ∈ J, ⁅a, b⁆ ∈ fixSupp σ := by
    intro a ha b hb x hx
    rw [commutatorElement_def]
    have hinv : ∀ w : Perm Ω, w * σ = σ * w → w⁻¹ * σ = σ * w⁻¹ := fun w hw => by
      have := congrArg (fun t => w⁻¹ * t * w⁻¹) hw
      simpa [mul_assoc] using this.symm
    have hb' : σ (b⁻¹ x) ≠ b⁻¹ x := apply_ne_of_comm (hinv b (hσc b hb)) hx
    have hab' : σ (a⁻¹ (b⁻¹ x)) ≠ a⁻¹ (b⁻¹ x) := apply_ne_of_comm (hinv a (hσc a ha)) hb'
    have h1 := comm_on_support (hσc a ha) (hσc b hb) (hcyc a ha) (hcyc b hb) hab'
    simp only [Perm.mul_apply]
    rw [h1]
    simp
  have hperf : ⁅J, J⁆ = J := by
    have h := hq.1
    rw [commutator] at h
    have h2 := congrArg (Subgroup.map J.subtype) h
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype] at h2
    rw [h2]
  rw [← hperf]
  exact Subgroup.commutator_le.2 hcommut

@[expose] def mAlt (σ : Perm Ω) : Subgroup (Perm Ω) := centAlt σ ⊓ fixSupp σ

theorem mAlt_le (σ : Perm Ω) : mAlt σ ≤ centAlt σ := inf_le_left

variable (σ : Perm Ω)

noncomputable def mAltEquiv : ↥(mAlt σ) ≃* alternatingGroup (Function.fixedPoints σ) := by
  have hofs : ∀ g : ↥(mAlt σ), ofSubtype (rho σ ⟨g, (g.2).1⟩) = (g : Perm Ω) := fun g =>
    ofSubtype_rho g.2.1 g.2.2
  let ρ : ↥(mAlt σ) →* alternatingGroup (Function.fixedPoints σ) :=
    ((rho σ).comp (Subgroup.inclusion (mAlt_le σ))).codRestrict _ (fun g => by
      rw [mem_alternatingGroup]
      have h1 := sign_ofSubtype (rho σ ⟨g, (g.2).1⟩)
      rw [hofs g] at h1
      show sign (rho σ ⟨(g : Perm Ω), g.2.1⟩) = 1
      rw [← h1]
      exact (mem_centAlt.1 g.2.1).2)
  refine MulEquiv.ofBijective ρ ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro g hg
    have h1 : rho σ ⟨g, (g.2).1⟩ = 1 := congrArg Subtype.val hg
    apply Subtype.ext
    rw [← hofs g, h1]
    simp
  · rintro ⟨τ, hτ⟩
    have hτX : ofSubtype τ ∈ centAlt σ := mem_centAlt.2
      ⟨(disjoint_ofSubtype_of_memFixedPoints_self τ).commute.eq, by
        rw [sign_ofSubtype]; exact mem_alternatingGroup.1 hτ⟩
    have hτM : ofSubtype τ ∈ mAlt σ := ⟨hτX, fun x hx => by
      exact ofSubtype_apply_of_not_mem τ (fun h => hx h)⟩
    refine ⟨⟨ofSubtype τ, hτM⟩, ?_⟩
    apply Subtype.ext
    ext ⟨x, hx⟩
    show ((rho σ ⟨ofSubtype τ, hτX⟩ : Perm (Function.fixedPoints σ)) ⟨x, hx⟩ : Ω) = _
    rw [rho_apply]
    exact ofSubtype_apply_of_mem τ hx

theorem alt_component_struct {σ : Perm Ω} (hσ : σ ^ 3 = 1) {J : Subgroup (Perm Ω)}
    (hJC : J ≤ centAlt σ) (hsn : IsSubnormal J (centAlt σ))
    (hq : CFSG.Open.IsQuasisimple ↥J) :
    5 ≤ Nat.card (Function.fixedPoints σ) ∧ Nonempty (↥J ≃* alternatingGroup (Function.fixedPoints σ)) := by
  have hJM : J ≤ mAlt σ := le_inf hJC (le_fixSupp_of_component hσ hJC hsn hq)
  have hsnM : IsSubnormal J (mAlt σ) := isSubnormal_of_le_of_le hsn hJM (mAlt_le σ)
  have hsnJ : IsSubnormal (J.subgroupOf (mAlt σ)) ⊤ := by
    have h1 := isSubnormal_comap' (mAlt σ).subtype hsnM
    rw [show (mAlt σ).comap (mAlt σ).subtype = ⊤ from Subgroup.subgroupOf_self _] at h1
    exact h1
  haveI := isQuasisimple_nontrivial hq
  have hJe : ↥J ≃* ↥(J.subgroupOf (mAlt σ)) := (Subgroup.subgroupOfEquivOfLe hJM).symm
  by_cases h5 : 5 ≤ Nat.card (Function.fixedPoints σ)
  · refine ⟨h5, ?_⟩
    haveI : IsSimpleGroup (alternatingGroup (Function.fixedPoints σ)) :=
      alternatingGroup.isSimpleGroup h5
    haveI : IsSimpleGroup ↥(mAlt σ) := (mAltEquiv σ).isSimpleGroup
    rcases i112f_eq_bot_or_top_of_isSubnormal hsnJ with hbot | htop
    · exfalso
      have : Subsingleton ↥(J.subgroupOf (mAlt σ)) := by rw [hbot]; infer_instance
      have := hJe.injective.subsingleton
      exact not_subsingleton ↥J ‹_›
    · exact ⟨hJe.trans ((MulEquiv.subgroupCongr htop).trans
        (Subgroup.topEquiv.trans (mAltEquiv σ)))⟩
  · exfalso
    have h4 : Nat.card (Function.fixedPoints σ) ≤ 4 := by omega
    haveI := alternatingGroup.isSolvable h4
    haveI : Group.IsSolvable ↥(mAlt σ) := Group.isSolvable_of_isSolvable_injective
      (mAltEquiv σ).injective
    haveI : Group.IsSolvable ↥J := Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective hJM)
    have hperf : Group.IsPerfect ↥J := ⟨hq.1⟩
    exact Group.IsPerfect.not_isSolvable ↥J inferInstance

end Perm

end CFSG.HardMathSupport.Solomon.Coordinator

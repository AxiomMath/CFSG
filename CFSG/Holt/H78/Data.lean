module

public import CFSG.Holt.H78.Sections
public import CFSG.Holt.H78.AltModel
public import CFSG.Holt.H78.SEModelAction

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General
open scoped Pointwise commutatorElement

section Factor

theorem isPerfect_of_isPretransitive {X : Type*} [Group X] [IsSimpleGroup X] {Δ : Type*}
    [MulAction X Δ] [FaithfulSMul X Δ] [IsPretransitive X Δ] {x : X} (hx : x ≠ 1) {δ : Δ}
    (hxδ : x • δ = δ) : Group.IsPerfect X := by
  refine ⟨(IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X)).resolve_left fun h => ?_⟩
  have hc := (commutator_eq_bot_iff X).mp h
  refine hx (eq_of_smul_eq_smul (α := Δ) fun δ' => ?_)
  obtain ⟨g, rfl⟩ := exists_smul_eq X δ δ'
  rw [one_smul, smul_smul, hc.is_comm.comm x g, mul_smul, hxδ]

variable {Δ : Type*} [Fintype Δ] [DecidableEq Δ] {M : Subgroup (Equiv.Perm Δ)}

theorem IsHoltFactor.five_le_card (hM : IsHoltFactor M) : 5 ≤ Fintype.card Δ := by
  rcases hM with ⟨-, h7⟩ | ⟨q, e, h⟩
  · omega
  · obtain ⟨hq, -, he, -⟩ := h.params
    rw [← Nat.card_eq_fintype_card, h.card_eq]
    have := Nat.le_self_pow (n := e) (by omega) q
    omega

theorem IsHoltFactor.isPretransitive (hM : IsHoltFactor M) : IsPretransitive M Δ := by
  rcases hM with ⟨rfl, h7⟩ | ⟨q, e, h⟩
  · exact alternatingGroup.isPretransitive_of_three_le_card (α := Δ)
      (by rw [Nat.card_eq_fintype_card]; omega)
  · have := h.isPretransitive
    refine ⟨fun a b => ?_⟩
    obtain ⟨n, hn⟩ := exists_smul_eq (⊤ : Subgroup M) a b
    exact ⟨n, hn⟩

theorem IsHoltFactor.isSimpleGroup (hM : IsHoltFactor M) : IsSimpleGroup M := by
  rcases hM with ⟨rfl, h7⟩ | ⟨q, e, h⟩
  · exact alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card]; omega)
  · obtain ⟨n, e', -, hB⟩ := IsBenderNormal.benderType h
    have := hB.isSimple
    exact (Subgroup.topEquiv (G := M)).symm.isSimpleGroup

theorem IsHoltFactor.isPerfect (hM : IsHoltFactor M) : Group.IsPerfect M := by
  have := hM.isSimpleGroup
  have := hM.isPretransitive
  rcases hM with ⟨rfl, h7⟩ | ⟨q, e, h⟩
  · obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp (by omega : 2 < Fintype.card Δ)
    obtain ⟨g, hg, hga, hgb⟩ :=
      exists_mem_alternatingGroup_fix_apply_eq (by omega) hab.symm hac.symm
    refine isPerfect_of_isPretransitive (x := ⟨g, hg⟩) (δ := a) (fun h1 => hbc ?_) hga
    rw [← hgb, show g = 1 from congrArg Subtype.val h1, Equiv.Perm.one_apply]
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨S⟩ : Nonempty (Sylow 2 M) := inferInstance
    obtain ⟨hq, -, he, -⟩ := h.params
    have hS : 1 < Nat.card (S : Subgroup M) := by
      rw [h.card_sylow S]
      exact Nat.one_lt_pow (by omega) (by omega)
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      ((Subgroup.one_lt_card_iff_ne_bot _).mp hS)
    obtain ⟨δ, hδ⟩ := fixSet_nonempty_of_odd h.odd_card S.isPGroup'
    exact isPerfect_of_isPretransitive (x := (x : M)) (fun h1 => hx1 (Subtype.ext h1))
      (hδ x x.2)

end Factor

namespace HoltData

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω] (D : HoltData G Ω)

abbrev M (i : D.ι) : Subgroup (Equiv.Perm (D.Ψc i)) := factorImage G Ω (D.L i) (D.ρ i)

abbrev tHull : jHull G Ω := ⟨D.t, mem_jHull_of_mem_longInv D.t_mem⟩

abbrev socPre : Subgroup G := jOddCore G Ω ⊔ ⨆ i, D.L i

variable {D}

theorem rho_eq_one_of_mem_jOddCore {h : jHull G Ω} (hh : (h : G) ∈ jOddCore G Ω) (i : D.ι) :
    D.ρ i h = 1 := by
  have hh' : h ∈ (jOddCore G Ω).subgroupOf (jHull G Ω) := hh
  rw [← D.inf_ker i] at hh'
  exact hh'.2

theorem rho_eq_one_of_mem_L {i j : D.ι} (hij : i ≠ j) {h : jHull G Ω} (hh : (h : G) ∈ D.L i) :
    D.ρ j h = 1 :=
  D.le_ker i j hij hh

theorem mem_jOddCore_of_mem_L {i : D.ι} {h : jHull G Ω} (hh : (h : G) ∈ D.L i)
    (h1 : D.ρ i h = 1) : (h : G) ∈ jOddCore G Ω := by
  have hh' : h ∈ (D.L i).subgroupOf (jHull G Ω) ⊓ (D.ρ i).ker := ⟨hh, h1⟩
  rw [D.inf_ker i] at hh'
  exact hh'

theorem mem_M {i : D.ι} {x : Equiv.Perm (D.Ψc i)} :
    x ∈ D.M i ↔ ∃ h : jHull G Ω, (h : G) ∈ D.L i ∧ D.ρ i h = x :=
  mem_factorImage

theorem rho_mem_M {i : D.ι} {h : jHull G Ω} (hh : (h : G) ∈ D.L i) : D.ρ i h ∈ D.M i :=
  mem_M.mpr ⟨h, hh, rfl⟩

omit [MulAction G Ω] in
private theorem mem_of_le_map_subtype {K : Subgroup G} {C : Subgroup K} {A : Subgroup G}
    (hA : A ≤ C.map K.subtype) {h : K} (hh : (h : G) ∈ A) : h ∈ C := by
  obtain ⟨c, hc, hch⟩ := hA hh
  rwa [← Subtype.ext hch]

variable (D) in
theorem eq_top_of_forall_mem {C : Subgroup (jHull G Ω)}
    (hO : ∀ h : jHull G Ω, (h : G) ∈ jOddCore G Ω → h ∈ C)
    (hL : ∀ (i : D.ι) (h : jHull G Ω), (h : G) ∈ D.L i → h ∈ C) (ht : D.tHull ∈ C) : C = ⊤ := by
  have hle : jHull G Ω ≤ C.map (jHull G Ω).subtype :=
    D.sup_eq.ge.trans (sup_le (sup_le (fun g hg => ⟨⟨g, jOddCore_le_jHull hg⟩, hO _ hg, rfl⟩)
      (iSup_le fun i g hg => ⟨⟨g, D.L_le i hg⟩, hL i _ hg, rfl⟩))
      (Subgroup.zpowers_le.mpr ⟨D.tHull, ht, rfl⟩))
  exact eq_top_iff.mpr fun h _ => mem_of_le_map_subtype hle h.2

variable (D) in
theorem mem_of_mem_socPre {C : Subgroup (jHull G Ω)}
    (hO : ∀ h : jHull G Ω, (h : G) ∈ jOddCore G Ω → h ∈ C)
    (hL : ∀ (i : D.ι) (h : jHull G Ω), (h : G) ∈ D.L i → h ∈ C) {h : jHull G Ω}
    (hh : (h : G) ∈ D.socPre) : h ∈ C := by
  have hle : D.socPre ≤ C.map (jHull G Ω).subtype :=
    sup_le (fun g hg => ⟨⟨g, jOddCore_le_jHull hg⟩, hO _ hg, rfl⟩)
      (iSup_le fun i g hg => ⟨⟨g, D.L_le i hg⟩, hL i _ hg, rfl⟩)
  exact mem_of_le_map_subtype hle hh

theorem rho_mem_M_of_mem_socPre {h : jHull G Ω} (hh : (h : G) ∈ D.socPre) (i : D.ι) :
    D.ρ i h ∈ D.M i := by
  refine D.mem_of_mem_socPre (C := (D.M i).comap (D.ρ i))
    (fun h' hh' => ?_) (fun j h' hh' => ?_) hh
  · rw [Subgroup.mem_comap, rho_eq_one_of_mem_jOddCore hh' i]
    exact (D.M i).one_mem
  · rw [Subgroup.mem_comap]
    by_cases hji : j = i
    · subst hji
      exact rho_mem_M hh'
    · rw [rho_eq_one_of_mem_L hji hh']
      exact (D.M i).one_mem

theorem range_rho (i : D.ι) :
    (D.ρ i).range = D.M i ⊔ Subgroup.zpowers (D.ρ i D.tHull) := by
  refine le_antisymm ?_ (sup_le (Subgroup.map_le_range _ _)
    (Subgroup.zpowers_le.mpr ⟨D.tHull, rfl⟩))
  rintro _ ⟨h, rfl⟩
  have hC := D.eq_top_of_forall_mem
    (C := (D.M i ⊔ Subgroup.zpowers (D.ρ i D.tHull)).comap (D.ρ i))
    (fun h' hh' => ?_) (fun j h' hh' => ?_) ?_
  · exact (Subgroup.eq_top_iff' _).mp hC h
  · rw [Subgroup.mem_comap, rho_eq_one_of_mem_jOddCore hh' i]
    exact Subgroup.one_mem _
  · rw [Subgroup.mem_comap]
    by_cases hji : j = i
    · subst hji
      exact Subgroup.mem_sup_left (rho_mem_M hh')
    · rw [rho_eq_one_of_mem_L hji hh']
      exact Subgroup.one_mem _
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem range_rho_of_not_isOuterFactor {i : D.ι} (hi : ¬ IsOuterFactor (D.M i)) :
    (D.ρ i).range = D.M i := by
  rw [range_rho, sup_eq_left, Subgroup.zpowers_le]
  exact D.inner i hi

variable (D) in
theorem exists_coord_eq_update (ω₀ : Ω) (i : D.ι) (b : D.Ψc i) :
    ∃ ω : Ω, D.coord ω = Function.update (D.coord ω₀) i b :=
  D.coord_surjective _

variable (D) in
theorem exists_coord_apply_eq (i : D.ι) (b : D.Ψc i) : ∃ ω : Ω, D.coord ω i = b := by
  obtain ⟨ω₀, -⟩ := D.t_mem.2
  obtain ⟨ω, hω⟩ := D.exists_coord_eq_update ω₀ i b
  exact ⟨ω, by rw [hω, Function.update_self]⟩

theorem rho_eq_one_iff {i : D.ι} {h : jHull G Ω} :
    D.ρ i h = 1 ↔ ∀ ω : Ω, D.coord ((h : G) • ω) i = D.coord ω i := by
  refine ⟨fun h1 ω => by rw [D.coord_smul, h1, Equiv.Perm.one_apply], fun hc => ?_⟩
  ext b
  obtain ⟨ω, hω⟩ := D.exists_coord_apply_eq i b
  rw [← hω, ← D.coord_smul, hc, Equiv.Perm.one_apply]

theorem mem_jOrbitKernel_iff_rho {h : jHull G Ω} :
    (h : G) ∈ jOrbitKernel G Ω ↔ ∀ i, D.ρ i h = 1 := by
  rw [mem_jOrbitKernel_iff]
  refine ⟨fun hk i => rho_eq_one_iff.mpr fun ω => ?_, fun h1 => ⟨h.2, fun ω => ?_⟩⟩
  · exact congrFun ((D.coord_eq_iff ω _).mpr (hk.2 ω)).symm i
  · exact (D.coord_eq_iff ω _).mp (funext fun i => (rho_eq_one_iff.mp (h1 i) ω).symm)

variable (D) in
@[expose] noncomputable def equivPsi : orbitRel.Quotient (jOddCore G Ω) Ω ≃ ∀ i, D.Ψc i :=
  Equiv.ofBijective
    (Quotient.lift D.coord fun a b hab =>
      ((D.coord_eq_iff b a).mpr (orbitRel_apply.mp hab)).symm)
    ⟨fun x y => Quotient.inductionOn₂ x y fun a b hab =>
        Quotient.sound (orbitRel_apply.mpr (mem_orbit_symm.mp ((D.coord_eq_iff a b).mp hab))),
      fun f => (D.coord_surjective f).elim fun ω hω => ⟨Quotient.mk'' ω, hω⟩⟩

@[simp] theorem equivPsi_mk (ω : Ω) : D.equivPsi (Quotient.mk'' ω) = D.coord ω := rfl

variable (D) in
theorem five_le_card (i : D.ι) : 5 ≤ Fintype.card (D.Ψc i) :=
  (D.factor i).five_le_card

variable (D) in
theorem isSimpleGroup_M (i : D.ι) : IsSimpleGroup (D.M i) :=
  (D.factor i).isSimpleGroup

variable (D) in
theorem isPerfect_M (i : D.ι) : Group.IsPerfect (D.M i) :=
  (D.factor i).isPerfect

variable (D) in
theorem not_isMulCommutative_M (i : D.ι) : ¬ IsMulCommutative (D.M i) := by
  have := D.isSimpleGroup_M i
  have := D.isPerfect_M i
  exact Group.IsPerfect.not_isMulCommutative _

variable (D) in
theorem isEmpty_ι_iff : IsEmpty D.ι ↔ IsPretransitive (jOddCore G Ω) Ω := by
  refine ⟨fun hι => ⟨fun a b => ?_⟩, fun hO => ⟨fun i => ?_⟩⟩
  · exact mem_orbit_iff.mp ((D.coord_eq_iff a b).mp (funext fun i => (IsEmpty.false i).elim))
  · obtain ⟨ω₀, -⟩ := D.t_mem.2
    obtain ⟨b, b', hbb'⟩ :=
      (Fintype.one_lt_card_iff (α := D.Ψc i)).mp (by have := D.five_le_card i; omega)
    obtain ⟨ω, hω⟩ := D.exists_coord_eq_update ω₀ i b
    obtain ⟨ω', hω'⟩ := D.exists_coord_eq_update ω₀ i b'
    have h := congrFun ((D.coord_eq_iff ω ω').mpr
      (mem_orbit_iff.mpr (exists_smul_eq (jOddCore G Ω) ω ω'))) i
    rw [hω, hω', Function.update_self, Function.update_self] at h
    exact hbb' h

variable (D)

theorem jOddCore_le_socPre : jOddCore G Ω ≤ D.socPre := le_sup_left

theorem L_le_socPre (i : D.ι) : D.L i ≤ D.socPre := le_sup_of_le_right (le_iSup D.L i)

theorem socPre_le_jHull : D.socPre ≤ jHull G Ω := sup_le jOddCore_le_jHull (iSup_le D.L_le)

theorem socPre_sup_zpowers : D.socPre ⊔ Subgroup.zpowers D.t = jHull G Ω := D.sup_eq

theorem conj_mem_socPre {g : G} (hg : g ∈ jHull G Ω) {x : G} (hx : x ∈ D.socPre) :
    g * x * g⁻¹ ∈ D.socPre := by
  have hle : D.socPre ≤ D.socPre.comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun o ho => D.jOddCore_le_socPre (jOddCore_normal.conj_mem o ho g))
      (iSup_le fun i l hl => D.L_le_socPre i
        ((Subgroup.mem_normalizer_iff.mp (D.le_normalizer i hg) l).mp hl))
  exact hle hx

theorem le_normalizer_socPre : jHull G Ω ≤ Subgroup.normalizer (D.socPre : Set G) := by
  intro g hg
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨D.conj_mem_socPre hg, fun hx => ?_⟩
  have h := D.conj_mem_socPre (inv_mem hg) hx
  simpa only [inv_inv, mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] using h

theorem normal_socPre_subgroupOf : (D.socPre.subgroupOf (jHull G Ω)).Normal :=
  ⟨fun _ hn g => D.conj_mem_socPre g.2 hn⟩

theorem relIndex_socPre_jHull_dvd_two : D.socPre.relIndex (jHull G Ω) ∣ 2 := by
  have := D.normal_socPre_subgroupOf
  have hsup : D.socPre.subgroupOf (jHull G Ω) ⊔ Subgroup.zpowers D.tHull = ⊤ := by
    apply Subgroup.map_injective (jHull G Ω).subtype_injective
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left D.socPre_le_jHull, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact D.sup_eq
  rw [Subgroup.relIndex, ← Subgroup.relIndex_top_right, ← hsup, Subgroup.relIndex_sup_left,
    ← Subgroup.inf_relIndex_right]
  have h2 : Nat.card (Subgroup.zpowers D.tHull) = 2 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, D.t_mem.1]
  exact h2 ▸ Subgroup.relIndex_dvd_card _ _

theorem relIndex_socPre_jHull_le_two : D.socPre.relIndex (jHull G Ω) ≤ 2 :=
  Nat.le_of_dvd two_pos D.relIndex_socPre_jHull_dvd_two

theorem rho_eq_one_of_mem_sup_finsetSup (s : Finset D.ι) {h : jHull G Ω}
    (hh : (h : G) ∈ jOddCore G Ω ⊔ s.sup D.L) :
    (∀ j ∉ s, D.ρ j h = 1) ∧ ((∀ i ∈ s, D.ρ i h = 1) → (h : G) ∈ jOddCore G Ω) := by
  induction s using Finset.induction_on generalizing h with
  | empty =>
    rw [Finset.sup_empty, sup_bot_eq] at hh
    exact ⟨fun j _ => rho_eq_one_of_mem_jOddCore hh j, fun _ => hh⟩
  | insert a s ha ih =>
    have heq : jOddCore G Ω ⊔ (insert a s).sup D.L = jOddCore G Ω ⊔ s.sup D.L ⊔ D.L a := by
      rw [Finset.sup_insert]
      ac_rfl
    have hP : jOddCore G Ω ⊔ s.sup D.L ≤ jHull G Ω :=
      sup_le jOddCore_le_jHull (Finset.sup_le fun i _ => D.L_le i)
    have hh' : (h : G) ∈ ((jOddCore G Ω ⊔ s.sup D.L ⊔ D.L a : Subgroup G) : Set G) := heq ▸ hh
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hP.trans (D.le_normalizer a))] at hh'
    obtain ⟨p, hp, l, hl, hpl⟩ := Set.mem_mul.mp hh'
    obtain ⟨ih1, ih2⟩ := ih (h := ⟨p, hP hp⟩) hp
    obtain rfl : h = ⟨p, hP hp⟩ * ⟨l, D.L_le a hl⟩ := Subtype.ext hpl.symm
    refine ⟨fun j hj => ?_, fun hs => ?_⟩
    · rw [Finset.mem_insert, not_or] at hj
      rw [map_mul, ih1 j hj.2, rho_eq_one_of_mem_L (Ne.symm hj.1) (h := ⟨l, D.L_le a hl⟩) hl,
        mul_one]
    · have hla : D.ρ a ⟨l, D.L_le a hl⟩ = 1 := by
        have h1 := hs a (Finset.mem_insert_self a s)
        rwa [map_mul, ih1 a ha, one_mul] at h1
      have hlO : l ∈ jOddCore G Ω := mem_jOddCore_of_mem_L (h := ⟨l, D.L_le a hl⟩) hl hla
      have hpO : p ∈ jOddCore G Ω := ih2 fun i hi => by
        have h1 := hs i (Finset.mem_insert_of_mem hi)
        rwa [map_mul, rho_eq_one_of_mem_jOddCore (h := ⟨l, D.L_le a hl⟩) hlO i, mul_one] at h1
      exact (jOddCore G Ω).mul_mem hpO hlO

theorem socPre_inf_jOrbitKernel : D.socPre ⊓ jOrbitKernel G Ω = jOddCore G Ω := by
  refine le_antisymm (fun g hg => ?_) (le_inf D.jOddCore_le_socPre jOddCore_le_jOrbitKernel)
  have hgH : g ∈ jHull G Ω := jOrbitKernel_le_jHull hg.2
  have h1 := (mem_jOrbitKernel_iff_rho (D := D) (h := ⟨g, hgH⟩)).mp hg.2
  have hg' : g ∈ jOddCore G Ω ⊔ Finset.univ.sup D.L := by
    rw [Finset.sup_univ_eq_iSup]
    exact hg.1
  exact (D.rho_eq_one_of_mem_sup_finsetSup Finset.univ (h := ⟨g, hgH⟩) hg').2 fun i _ => h1 i

include D in
theorem relIndex_jOddCore_jOrbitKernel_le_two :
    (jOddCore G Ω).relIndex (jOrbitKernel G Ω) ≤ 2 := by
  have hdvd := D.relIndex_socPre_jHull_dvd_two
  have hne : D.socPre.relIndex (jHull G Ω) ≠ 0 := fun h0 => by
    rw [h0] at hdvd
    norm_num at hdvd
  calc (jOddCore G Ω).relIndex (jOrbitKernel G Ω)
      = (D.socPre ⊓ jOrbitKernel G Ω).relIndex (jOrbitKernel G Ω) := by
        rw [D.socPre_inf_jOrbitKernel]
    _ = D.socPre.relIndex (jOrbitKernel G Ω) := Subgroup.inf_relIndex_right _ _
    _ ≤ D.socPre.relIndex (jHull G Ω) := Subgroup.relIndex_le_of_le_right jOrbitKernel_le_jHull hne
    _ ≤ 2 := Nat.le_of_dvd two_pos hdvd

variable {D}

theorem commutator_L_le {i j : D.ι} (hij : i ≠ j) : ⁅D.L i, D.L j⁆ ≤ jOddCore G Ω := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hxH := D.L_le i hx
  have hyH := D.L_le j hy
  have hc : ⁅x, y⁆ ∈ D.L i := by
    rw [show ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) by group]
    exact (D.L i).mul_mem hx ((Subgroup.mem_normalizer_iff.mp (D.le_normalizer i hyH) _).mp
      ((D.L i).inv_mem hx))
  refine mem_jOddCore_of_mem_L (h := ⁅(⟨x, hxH⟩ : jHull G Ω), ⟨y, hyH⟩⁆) hc ?_
  rw [map_commutatorElement, rho_eq_one_of_mem_L hij.symm (h := ⟨y, hyH⟩) hy,
    commutatorElement_one_right]

end HoltData

section LongInv

variable {G : Type*} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω]

theorem odd_card_orbit_jOddCore (ω : Ω) : Odd (Nat.card (orbit (jOddCore G Ω) ω)) := by
  rw [Nat.card_coe_set_eq, ← index_stabilizer]
  exact Odd.of_dvd_nat odd_card_jOddCore (Subgroup.index_dvd_card _)

theorem smul_orbit_jOddCore_eq_iff {u : G} {α : Ω} (hu : u ∈ longInvAt G Ω α) (ω : Ω) :
    u • orbit (jOddCore G Ω) ω = orbit (jOddCore G Ω) ω ↔ ω ∈ orbit (jOddCore G Ω) α := by
  refine ⟨fun h => mem_orbit_symm.mp ?_, fun h => ?_⟩
  · have : Finite (orbit (jOddCore G Ω) ω) := (Set.finite_range _).to_subtype
    exact mem_of_mem_longInvAt_of_mem_stabilizer hu (odd_card_orbit_jOddCore ω) h
  · rw [orbit_eq_iff.mpr h, smul_orbit_eq_orbit_smul, hu.2]

namespace HoltData

variable (D : HoltData G Ω)

theorem coord_smul_eq_iff {u : G} {α : Ω} (hu : u ∈ longInvAt G Ω α) (ω : Ω) :
    D.coord (u • ω) = D.coord ω ↔ D.coord ω = D.coord α :=
  calc D.coord (u • ω) = D.coord ω ↔ u • ω ∈ orbit (jOddCore G Ω) ω := by
        rw [eq_comm]
        exact D.coord_eq_iff ω (u • ω)
    _ ↔ u • orbit (jOddCore G Ω) ω = orbit (jOddCore G Ω) ω := by
        rw [smul_orbit_eq_orbit_smul, orbit_eq_iff]
    _ ↔ ω ∈ orbit (jOddCore G Ω) α := smul_orbit_jOddCore_eq_iff hu ω
    _ ↔ D.coord ω = D.coord α := by
        rw [eq_comm]
        exact (D.coord_eq_iff α ω).symm

theorem rho_apply_eq_iff {u : G} {α : Ω} (hu : u ∈ longInvAt G Ω α) (i : D.ι) (b : D.Ψc i) :
    D.ρ i ⟨u, mem_jHull_of_mem_longInv hu.1⟩ b = b ↔ b = D.coord α i := by
  set uH : jHull G Ω := ⟨u, mem_jHull_of_mem_longInv hu.1⟩
  have hsmul : ∀ (ω : Ω) (j : D.ι), D.coord (u • ω) j = D.ρ j uH (D.coord ω j) :=
    fun ω j => D.coord_smul uH ω j
  refine ⟨fun hb => ?_, fun hb => ?_⟩
  · obtain ⟨ω, hω⟩ := D.exists_coord_eq_update α i b
    have hfix : D.coord (u • ω) = D.coord ω := by
      funext j
      rw [hsmul]
      rcases eq_or_ne j i with rfl | hj
      · rw [hω, Function.update_self, hb]
      · rw [hω, Function.update_of_ne hj, ← hsmul, hu.2]
    have h := congrFun ((D.coord_smul_eq_iff hu ω).mp hfix) i
    rwa [hω, Function.update_self] at h
  · rw [hb, ← hsmul, hu.2]

theorem rho_mem_longInvAt {u : G} {α : Ω} (hu : u ∈ longInvAt G Ω α) (i : D.ι) :
    D.ρ i ⟨u, mem_jHull_of_mem_longInv hu.1⟩ ∈
      longInvAt (Equiv.Perm (D.Ψc i)) (D.Ψc i) (D.coord α i) := by
  have : Nontrivial (D.Ψc i) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by have := D.five_le_card i; omega)
  refine mem_longInvAt_of_mul_self ?_ (fun b => ?_) (exists_ne _)
  · rw [← map_mul, show (⟨u, mem_jHull_of_mem_longInv hu.1⟩ : jHull G Ω) *
      ⟨u, mem_jHull_of_mem_longInv hu.1⟩ = 1 from
      Subtype.ext (mul_self_eq_one_of_mem_longInv hu.1), map_one]
  · rw [Equiv.Perm.smul_def]
    exact D.rho_apply_eq_iff hu i b

theorem rho_mem_longInv {u : G} (hu : u ∈ longInv G Ω) (i : D.ι) :
    D.ρ i ⟨u, mem_jHull_of_mem_longInv hu⟩ ∈ longInv (Equiv.Perm (D.Ψc i)) (D.Ψc i) := by
  obtain ⟨α, hα⟩ := exists_mem_longInvAt hu
  exact (D.rho_mem_longInvAt hα i).1

theorem odd_card_Ψc (i : D.ι) : Odd (Fintype.card (D.Ψc i)) :=
  odd_card_of_mem_longInv_perm (D.rho_mem_longInv D.t_mem i)

theorem rho_mem_M_iff {u : G} (hu : u ∈ longInv G Ω) (i : D.ι) :
    D.ρ i ⟨u, mem_jHull_of_mem_longInv hu⟩ ∈ D.M i ↔ ¬ IsOuterFactor (D.M i) := by
  refine ⟨fun hM hout => ?_, fun hn => ?_⟩
  · rw [hout.1] at hM
    exact (mem_alternatingGroup_iff_not_isOuterFactor (D.rho_mem_longInv hu i)).mp hM
      ⟨rfl, hout.2⟩
  · rw [← range_rho_of_not_isOuterFactor hn]
    exact ⟨_, rfl⟩

theorem t_mem_socPre_iff [FaithfulSMul G Ω] :
    D.t ∈ D.socPre ↔ jOddCore G Ω = ⊥ ∧ ∀ i, ¬ IsOuterFactor (D.M i) := by
  refine ⟨fun ht => ?_, fun ⟨hO, hn⟩ => ?_⟩
  · have hn : ∀ i, ¬ IsOuterFactor (D.M i) := fun i =>
      (D.rho_mem_M_iff D.t_mem i).mp (rho_mem_M_of_mem_socPre (h := D.tHull) ht i)
    refine ⟨by_contra fun hO => ?_, hn⟩
    have h2 := (D.ker_inner hn).2 hO
    have hsoc : D.socPre = jHull G Ω :=
      le_antisymm D.socPre_le_jHull
        (D.sup_eq.ge.trans (sup_le le_rfl (Subgroup.zpowers_le.mpr ht)))
    have hK := D.socPre_inf_jOrbitKernel
    rw [hsoc, inf_of_le_right jOrbitKernel_le_jHull] at hK
    rw [hK, Subgroup.relIndex_self] at h2
    exact absurd h2 (by norm_num)
  · have h := (D.ker_inner hn).1
    rw [jOrbitKernel_eq_bot hO, sup_bot_eq] at h
    exact h

end HoltData

end LongInv

end CFSG.Holt.H78

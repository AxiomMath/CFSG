module

public import CFSG.CharacterTheory.Semidihedral.PerfectLayerNormalization

public section

namespace CFSG.Semidihedral.FullRootSylowCentralizers

noncomputable section

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.LinearGroups
open CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.SemilinearOddExtensions
open CFSG.GorensteinWalter CFSG.Open
open scoped Pointwise

universe u v

variable {F : Type u} [Field F]

theorem full_translation_centralizer_representative (c : Equiv.Perm (Omega F))
    (hc : c ∈ Subgroup.centralizer (coordinateU F : Set (Equiv.Perm (Omega F)))) :
    ∃! b : F, c = translation F b := by
  have hcomm (b : F) (x : Omega F) : translation F b (c x) = c (translation F b x) :=
    congrArg (fun a : Equiv.Perm (Omega F) => a x)
      (Subgroup.mem_centralizer_iff.mp hc _ (translation_mem_coordinateU b))
  have hinf : c none = none := by
    cases h : c none with
    | none => rfl
    | some a =>
      have ht := hcomm 1 none
      simp only [h, translation_some, translation_none] at ht
      have h10 : (1 : F) = 0 :=
        add_left_cancel ((Option.some.inj ht).trans (add_zero a).symm)
      exact (one_ne_zero h10).elim
  obtain ⟨b, hb⟩ : ∃ b : F, c (some 0) = some b := by
    cases h : c (some 0) with
    | none =>
      have hbad := c.injective (h.trans hinf.symm)
      exact (Option.some_ne_none 0 hbad).elim
    | some b => exact ⟨b, rfl⟩
  have hcb : c = translation F b := by
    apply Equiv.ext
    intro x
    cases x with
    | none => exact hinf
    | some a =>
      have ht := hcomm a (some 0)
      simpa only [hb, translation_some, zero_add, add_zero, add_comm] using ht.symm
  refine ⟨b, hcb, ?_⟩
  intro a ha
  have h := congrArg (fun g : Equiv.Perm (Omega F) => g (some 0))
    (ha.symm.trans hcb)
  simpa only [translation_some, zero_add, Option.some_inj] using h

theorem full_translation_centralizer_eq :
    Subgroup.centralizer (coordinateU F : Set (Equiv.Perm (Omega F))) = coordinateU F := by
  apply le_antisymm
  · intro c hc
    obtain ⟨b, rfl, -⟩ := full_translation_centralizer_representative c hc
    exact translation_mem_coordinateU b
  · intro c hc
    rw [coordinateU_eq_range] at hc
    obtain ⟨b, rfl⟩ := hc
    apply Subgroup.mem_centralizer_iff.mpr
    intro d hd
    rw [coordinateU_eq_range] at hd
    obtain ⟨a, rfl⟩ := hd
    rw [← map_mul, ← map_mul, mul_comm]

theorem mem_full_translation_centralizer_iff (c : Equiv.Perm (Omega F)) :
    c ∈ Subgroup.centralizer (coordinateU F : Set (Equiv.Perm (Omega F))) ↔
      ∃ b : F, c = translation F b := by
  constructor
  · intro hc
    obtain ⟨b, hb, -⟩ := full_translation_centralizer_representative c hc
    exact ⟨b, hb⟩
  · rintro ⟨b, rfl⟩
    rw [full_translation_centralizer_eq]
    exact translation_mem_coordinateU b

@[expose] def fullTranslationCentralizerEquiv (F : Type u) [Field F] :
    Multiplicative F ≃*
      Subgroup.centralizer (coordinateU F : Set (Equiv.Perm (Omega F))) :=
  (coordinateUEquiv F).trans (MulEquiv.subgroupCongr full_translation_centralizer_eq.symm)

theorem fullTranslationCentralizerEquiv_apply (b : F) :
    (fullTranslationCentralizerEquiv F (Multiplicative.ofAdd b) :
      Equiv.Perm (Omega F)) = translation F b :=
  coordinateUEquiv_apply b

theorem coordinate_sylow_translation_image [Finite F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (Q : Sylow p (coordinateG F)) :
    ∃ g : coordinateG F, (Q : Subgroup (coordinateG F)).map (coordinateG F).subtype =
      (coordinateU F).map (MulAut.conj (g : Equiv.Perm (Omega F))).toMonoidHom := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (coordinateG F) (coordinateUSylow F p) Q
  refine ⟨g, ?_⟩
  rw [← hg]
  have hc : ((g • coordinateUSylow F p : Sylow p (coordinateG F)) :
      Subgroup (coordinateG F)) =
      ((coordinateU F).subgroupOf (coordinateG F)).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul, coe_coordinateUSylow]
    rfl
  rw [hc, Subgroup.map_map]
  have hs : (coordinateG F).subtype.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (g : Equiv.Perm (Omega F))).toMonoidHom.comp
        (coordinateG F).subtype := by
    ext x
    rfl
  rw [hs, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le coordinateU_le_coordinateG]

theorem full_coordinate_sylow_centralizer [Finite F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (Q : Sylow p (coordinateG F)) :
    Subgroup.centralizer
      ((Q : Subgroup (coordinateG F)).map (coordinateG F).subtype :
        Set (Equiv.Perm (Omega F))) =
      (Q : Subgroup (coordinateG F)).map (coordinateG F).subtype := by
  obtain ⟨g, hg⟩ := coordinate_sylow_translation_image p Q
  rw [hg, ← PerfectLayerNormalization.isomorphism_maps_actual_centralizer,
    full_translation_centralizer_eq]

theorem original_odd_quotient_involution {G : Type u} [Group G] [Finite G]
    (i : G) (hi : orderOf i = 2) :
    Odd (Nat.card (N i)) ∧ orderOf (nu i (tInC i)) = 2 ∧
      nu i (tInC i) ∈ Subgroup.center (H i) ∧
      (barKappa i).ker = Subgroup.zpowers (nu i (tInC i)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card (N i)) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (G := C i) (p := 2))
  have hiC : orderOf (tInC i) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hi
  have hne : nu i (tInC i) ≠ 1 := by
    intro h
    have hm := (QuotientGroup.eq_one_iff (N := N i) (tInC i)).mp h
    have hd : 2 ∣ Nat.card (N i) := hiC ▸ (N i).orderOf_dvd_natCard hm
    exact hodd.not_two_dvd_nat hd
  refine ⟨hodd, orderOf_eq_prime ?_ hne, ?_, barKappa_kernel i⟩
  · calc
      (nu i (tInC i)) ^ 2 = nu i ((tInC i) ^ 2) := (map_pow (nu i) _ _).symm
      _ = nu i ((tInC i) ^ orderOf (tInC i)) :=
        congrArg (fun m => nu i ((tInC i) ^ m)) hiC.symm
      _ = 1 := by rw [pow_orderOf_eq_one, map_one]
  · exact Subgroup.map_center_le_center (QuotientGroup.mk'_surjective _)
      (Subgroup.mem_map_of_mem _ (tInC_central i))

abbrev originalT0 {G : Type u} [Group G] (i : G) : Subgroup (H i) :=
  (CFSG.generalizedFitting (Gamma i)).comap (barKappa i)

abbrev originalSylowImage {G : Type u} [Group G] (i : G) (p : ℕ)
    (P : Sylow p (originalT0 i)) : Subgroup (H i) :=
  (P : Subgroup (originalT0 i)).map (originalT0 i).subtype

@[expose] def originalLayerProjection {G : Type u} [Group G] (i : G) :
    originalT0 i →* CFSG.generalizedFitting (Gamma i) :=
  (barKappa i).subgroupComap (CFSG.generalizedFitting (Gamma i))

theorem originalLayerProjection_surjective {G : Type u} [Group G] (i : G) :
    Function.Surjective (originalLayerProjection i) :=
  (barKappa i).subgroupComap_surjective _ (barKappa_surjective i)

theorem original_sylow_image_disjoint {G : Type u} [Group G] [Finite G]
    (i : G) (hi : orderOf i = 2) (p : ℕ) (hpodd : Odd p)
    (P : Sylow p (originalT0 i)) :
    Disjoint (originalSylowImage i p P) (Subgroup.zpowers (nu i (tInC i))) := by
  obtain ⟨-, hz, -, -⟩ := original_odd_quotient_involution i hi
  have hP : IsPGroup p (originalSylowImage i p P) :=
    P.isPGroup'.map (originalT0 i).subtype
  have hZ : IsPGroup 2 (Subgroup.zpowers (nu i (tInC i))) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  exact IsPGroup.disjoint_of_coprime hP hZ hpodd.coprime_two_right

theorem original_sylow_projection_injective {G : Type u} [Group G] [Finite G]
    (i : G) (hi : orderOf i = 2) (p : ℕ) (hpodd : Odd p)
    (P : Sylow p (originalT0 i)) :
    Function.Injective ((barKappa i).comp (originalSylowImage i p P).subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  apply Subtype.ext
  apply Subgroup.disjoint_def.mp (original_sylow_image_disjoint i hi p hpodd P) x.property
  rw [← barKappa_kernel i]
  exact hx

theorem original_sylow_projection_image {G : Type u} [Group G] [Finite G]
    (i : G) (p : ℕ) [Fact p.Prime] (P : Sylow p (originalT0 i)) :
    ∃ Q : Sylow p (CFSG.generalizedFitting (Gamma i)),
      (Q : Subgroup (CFSG.generalizedFitting (Gamma i))).map
        (CFSG.generalizedFitting (Gamma i)).subtype =
      (originalSylowImage i p P).map (barKappa i) := by
  let Q := P.mapSurjective (originalLayerProjection_surjective i)
  refine ⟨Q, ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map]
  change (P : Subgroup (originalT0 i)).map
    ((CFSG.generalizedFitting (Gamma i)).subtype.comp (originalLayerProjection i)) = _
  rw [originalSylowImage, Subgroup.map_map]
  rfl

theorem original_local_faithful_same_field_action
    {G : Type u} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (i : G) (hi : orderOf i = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma i))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma i), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma i) : Set (Gamma i)) = ⊥)
    (hnc : ∀ Q : Sylow 2 (CFSG.generalizedFitting (Gamma i)), ¬ IsCyclic Q)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma i) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F))) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (A : Subgroup (F ≃+* F))
      (rho : Gamma i →* coordinateE F),
      Nat.card F = p ^ f ∧ 5 ≤ Nat.card F ∧ Function.Injective rho ∧
      (CFSG.generalizedFitting (Gamma i)).map rho = specialLayer F ∧
      rho.range = OddFieldLift.Gamma F A ∧
      (∀ x : C i, barKappa i (nu i x) = kappa i x) := by
  obtain ⟨G', hgroup, hfinite, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{u, 0} G
  let : Group G' := hgroup
  let : Fintype G' := hfinite
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S0' : Sylow 2 G' := S0.mapSurjective (f := e.toMonoidHom) e.surjective
  let f0' : SemidihedralGroup n ≃* S0' :=
    f0.trans ((S0 : Subgroup G).equivMapOfInjective e.toMonoidHom e.injective)
  let d := PerfectLayerNormalization.originalGeneralizedFittingEquiv e i
  let a := PerfectLayerNormalization.originalReducedQuotientEquiv e i
  let : IsSimpleGroup (CFSG.generalizedFitting (Gamma (e i))) := d.symm.isSimpleGroup
  have hcentral' : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma (e i)) : Set (Gamma (e i))) = ⊥ := by
    have h := congrArg (Subgroup.map a.toMonoidHom) hcentral
    rw [PerfectLayerNormalization.isomorphism_maps_actual_centralizer,
      PerfectLayerNormalization.isomorphism_maps_actual_generalizedFitting,
      Subgroup.map_bot] at h
    exact h
  obtain ⟨F, hfield, hfiniteF, A, rho', data⟩ := actual_simple_layer_matrix_data
    n hn S0' f0' (PerfectLayerNormalization.isomorphism_transports_no_index_two e hG)
    (e i) ((e.orderOf_eq i).trans hi)
    (PerfectLayerNormalization.isomorphism_transports_nonabelian d hnonab) hcentral'
    (PerfectLayerNormalization.isomorphism_transports_noncyclic_sylows d 2 hnc)
    p f hp hpodd hf (PerfectLayerNormalization.original_psl_two_model_transport d p f hmodel)
  let : Field F := hfield
  let : Finite F := hfiniteF
  let rho := rho'.comp a.toMonoidHom
  refine ⟨F, hfield, hfiniteF, A, rho, data.field_card, data.field_card ▸ hq,
    data.faithful.comp a.injective, ?_, ?_, barKappa_nu i⟩
  · change (CFSG.generalizedFitting (Gamma i)).map (rho'.comp a.toMonoidHom) = _
    rw [← Subgroup.map_map,
      PerfectLayerNormalization.isomorphism_maps_actual_generalizedFitting]
    exact data.layer_image
  · change (rho'.comp a.toMonoidHom).range = _
    have ha : a.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr a.surjective
    rw [MonoidHom.range_comp, ha,
      ← MonoidHom.range_eq_map]
    exact data.full_image

theorem original_sylow_translation_action
    {G : Type u} [Group G] [Finite G] (i : G) (p : ℕ) [Fact p.Prime]
    (F : Type v) [Field F] [Finite F] [CharP F p]
    (rho : Gamma i →* coordinateE F) (hinj : Function.Injective rho)
    (hL : (CFSG.generalizedFitting (Gamma i)).map rho = specialLayer F)
    (P : Sylow p (originalT0 i)) :
    ∃ Q : Sylow p (coordinateG F),
      (Q : Subgroup (coordinateG F)).map (coordinateG F).subtype =
        (originalSylowImage i p P).map
          (((coordinateE F).subtype.comp rho).comp (barKappa i)) ∧
      ∃ g : coordinateG F,
        (originalSylowImage i p P).map
          (((coordinateE F).subtype.comp rho).comp (barKappa i)) =
        (coordinateU F).map (MulAut.conj (g : Equiv.Perm (Omega F))).toMonoidHom := by
  let eta := (coordinateE F).subtype.comp rho
  have heta : Function.Injective eta := (coordinateE F).subtype_injective.comp hinj
  have hLG : (CFSG.generalizedFitting (Gamma i)).map eta = coordinateG F := by
    rw [← Subgroup.map_map, hL]
    exact ambientImage_specialLayer F
  let e : CFSG.generalizedFitting (Gamma i) ≃* coordinateG F :=
    ((CFSG.generalizedFitting (Gamma i)).equivMapOfInjective eta heta).trans
      (MulEquiv.subgroupCongr hLG)
  obtain ⟨Q0, hQ0⟩ := original_sylow_projection_image i p P
  have hsurj : Function.Surjective e.toMonoidHom := by
    intro y
    obtain ⟨x, hx⟩ := e.surjective y
    exact ⟨x, hx⟩
  let Q := Q0.mapSurjective (f := e.toMonoidHom) hsurj
  have hQ : (Q : Subgroup (coordinateG F)).map (coordinateG F).subtype =
      (originalSylowImage i p P).map (eta.comp (barKappa i)) := by
    change (Q0.mapSurjective (f := e.toMonoidHom) hsurj :
      Subgroup (coordinateG F)).map (coordinateG F).subtype = _
    rw [Sylow.coe_mapSurjective, Subgroup.map_map]
    have he : (coordinateG F).subtype.comp e.toMonoidHom =
        eta.comp (CFSG.generalizedFitting (Gamma i)).subtype := by
      ext x
      rfl
    rw [he, ← Subgroup.map_map, hQ0, Subgroup.map_map]
  obtain ⟨g, hg⟩ := coordinate_sylow_translation_image p Q
  exact ⟨Q, hQ, g, hQ.symm.trans hg⟩

theorem faithful_original_sylow_centralizer
    {G : Type u} [Group G] [Finite G] (i : G) (hi : orderOf i = 2)
    (p : ℕ) [Fact p.Prime] (hpodd : Odd p)
    (F : Type v) [Field F] [Finite F] [CharP F p]
    (rho : Gamma i →* coordinateE F) (hinj : Function.Injective rho)
    (hL : (CFSG.generalizedFitting (Gamma i)).map rho = specialLayer F)
    (P : Sylow p (originalT0 i)) :
    IsMulCommutative (originalSylowImage i p P) ∧
      Subgroup.centralizer (originalSylowImage i p P : Set (H i)) =
        originalSylowImage i p P ⊔ Subgroup.zpowers (nu i (tInC i)) := by
  let PD := originalSylowImage i p P
  let eta := (coordinateE F).subtype.comp rho
  let psi := eta.comp (barKappa i)
  obtain ⟨Q, hQ, -⟩ := original_sylow_translation_action i p F rho hinj hL P
  have hQcent : Subgroup.centralizer (PD.map psi : Set (Equiv.Perm (Omega F))) =
      PD.map psi := by
    rw [← hQ]
    exact full_coordinate_sylow_centralizer p Q
  have hcommImage : IsMulCommutative (PD.map psi) := by
    apply IsMulCommutative.of_setLike_mul_comm
    intro x hx y hy
    have hycent : y ∈ Subgroup.centralizer
        (PD.map psi : Set (Equiv.Perm (Omega F))) := hQcent.symm ▸ hy
    exact Subgroup.mem_centralizer_iff.mp hycent x hx
  let : IsMulCommutative (PD.map psi) := hcommImage
  have hpsi : Function.Injective (psi.comp PD.subtype) :=
    ((coordinateE F).subtype_injective.comp hinj).comp
      (original_sylow_projection_injective i hi p hpodd P)
  have hPD : IsMulCommutative PD := by
    apply IsMulCommutative.of_setLike_mul_comm
    intro x hx y hy
    have hxy : psi (x * y) = psi (y * x) := by
      rw [map_mul, map_mul]
      have hyImage : psi y ∈ PD.map psi := Subgroup.mem_map_of_mem psi hy
      have hycent : psi y ∈ Subgroup.centralizer
          (PD.map psi : Set (Equiv.Perm (Omega F))) := hQcent.symm ▸ hyImage
      exact Subgroup.mem_centralizer_iff.mp hycent (psi x)
        (Subgroup.mem_map_of_mem psi hx)
    exact congrArg Subtype.val (hpsi
      (show psi.comp PD.subtype (⟨x * y, PD.mul_mem hx hy⟩ : PD) =
        psi.comp PD.subtype (⟨y * x, PD.mul_mem hy hx⟩ : PD) from hxy))
  let : IsMulCommutative PD := hPD
  have hz : nu i (tInC i) ∈ Subgroup.center (H i) :=
    (original_odd_quotient_involution i hi).2.2.1
  have hker : psi.ker = Subgroup.zpowers (nu i (tInC i)) := by
    rw [MonoidHom.ker_comp_of_injective (barKappa i) eta
      ((coordinateE F).subtype_injective.comp hinj), barKappa_kernel]
  refine ⟨hPD, le_antisymm ?_ ?_⟩
  · intro x hx
    have hxImage : psi x ∈ Subgroup.centralizer
        (PD.map psi : Set (Equiv.Perm (Omega F))) := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      simpa only [map_mul] using congrArg psi (hx z hz)
    have hm : psi x ∈ PD.map psi := hQcent ▸ hxImage
    have hc : x ∈ (PD.map psi).comap psi := hm
    rw [Subgroup.comap_map_eq, hker] at hc
    exact hc
  · apply sup_le
    · exact Subgroup.le_centralizer PD
    · exact (Subgroup.zpowers_le.mpr hz).trans (Subgroup.center_le_centralizer _)

@[expose] def internalProductEquiv {D : Type u} [Group D] (P Z : Subgroup D)
    (hcomm : ∀ (x : P) (y : Z), Commute (x : D) (y : D)) (hdisj : Disjoint P Z) :
    P × Z ≃* (P ⊔ Z : Subgroup D) := by
  have hcomm' : ∀ (x : P) (y : Z), Commute (P.subtype x) (Z.subtype y) :=
    fun x y => hcomm x y
  let phi := P.subtype.noncommCoprod Z.subtype hcomm'
  have hphi : Function.Injective phi :=
    (MonoidHom.noncommCoprod_injective _ _ _).mpr
      ⟨P.subtype_injective, Z.subtype_injective, by
        simpa only [Subgroup.range_subtype] using hdisj⟩
  have hrange : phi.range = P ⊔ Z := by
    calc
      phi.range = P.subtype.range ⊔ Z.subtype.range :=
        MonoidHom.noncommCoprod_range P.subtype Z.subtype hcomm'
      _ = P ⊔ Z := by rw [Subgroup.range_subtype, Subgroup.range_subtype]
  exact (MonoidHom.ofInjective hphi).trans (MulEquiv.subgroupCongr hrange)

theorem internalProductEquiv_apply {D : Type u} [Group D] (P Z : Subgroup D)
    (hcomm : ∀ (x : P) (y : Z), Commute (x : D) (y : D)) (hdisj : Disjoint P Z)
    (x : P) (y : Z) :
    (internalProductEquiv P Z hcomm hdisj (x, y) : D) = (x : D) * (y : D) := rfl

theorem original_sylow_image_equiv_field
    {G : Type u} [Group G] [Finite G] (i : G) (hi : orderOf i = 2)
    (p : ℕ) [Fact p.Prime] (hpodd : Odd p)
    (F : Type v) [Field F] [Finite F] [CharP F p]
    (rho : Gamma i →* coordinateE F) (hinj : Function.Injective rho)
    (hL : (CFSG.generalizedFitting (Gamma i)).map rho = specialLayer F)
    (P : Sylow p (originalT0 i)) :
    Nonempty (originalSylowImage i p P ≃* Multiplicative F) := by
  let PD := originalSylowImage i p P
  let psi := ((coordinateE F).subtype.comp rho).comp (barKappa i)
  have hpsi : Function.Injective (psi.comp PD.subtype) :=
    ((coordinateE F).subtype_injective.comp hinj).comp
      (original_sylow_projection_injective i hi p hpodd P)
  have hrange : (psi.comp PD.subtype).range = PD.map psi := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  obtain ⟨-, -, g, hg⟩ := original_sylow_translation_action i p F rho hinj hL P
  let conj := MulAut.conj (g : Equiv.Perm (Omega F))
  exact ⟨((MonoidHom.ofInjective hpsi).trans
    (MulEquiv.subgroupCongr (hrange.trans hg))).trans
      ((conj.subgroupMap (coordinateU F)).symm.trans (coordinateUEquiv F).symm)⟩

abbrev OriginalRootSylowCentralizerConclusion {G : Type u} [Group G]
    (i : G) (p f : ℕ) (P : Sylow p (originalT0 i)) : Prop :=
  Odd (Nat.card (N i)) ∧
  orderOf (nu i (tInC i)) = 2 ∧
  nu i (tInC i) ∈ Subgroup.center (H i) ∧
  (barKappa i).ker = Subgroup.zpowers (nu i (tInC i)) ∧
  Function.Injective ((barKappa i).comp (originalSylowImage i p P).subtype) ∧
  (∃ Q : Sylow p (CFSG.generalizedFitting (Gamma i)),
    (Q : Subgroup (CFSG.generalizedFitting (Gamma i))).map
      (CFSG.generalizedFitting (Gamma i)).subtype =
    (originalSylowImage i p P).map (barKappa i)) ∧
  IsMulCommutative (originalSylowImage i p P) ∧
  Disjoint (originalSylowImage i p P) (Subgroup.zpowers (nu i (tInC i))) ∧
  (∀ (x : originalSylowImage i p P) (y : Subgroup.zpowers (nu i (tInC i))),
    Commute (x : H i) (y : H i)) ∧
  Subgroup.centralizer (originalSylowImage i p P : Set (H i)) =
    originalSylowImage i p P ⊔ Subgroup.zpowers (nu i (tInC i)) ∧
  Nat.card (originalSylowImage i p P) = p ^ f ∧
  (∃ e : originalSylowImage i p P × Subgroup.zpowers (nu i (tInC i)) ≃*
      Subgroup.centralizer (originalSylowImage i p P : Set (H i)),
    (∀ (x : originalSylowImage i p P) (y : Subgroup.zpowers (nu i (tInC i))),
      (e (x, y) : H i) = (x : H i) * (y : H i)) ∧
    (∀ c : Subgroup.centralizer (originalSylowImage i p P : Set (H i)),
      ∃! xy : originalSylowImage i p P × Subgroup.zpowers (nu i (tInC i)),
        e xy = c ∧ (xy.1 : H i) * (xy.2 : H i) = (c : H i))) ∧
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F p)
    (A : Subgroup (F ≃+* F)) (rho : Gamma i →* coordinateE F),
    Nat.card F = p ^ f ∧ 5 ≤ Nat.card F ∧ Function.Injective rho ∧
    (CFSG.generalizedFitting (Gamma i)).map rho = specialLayer F ∧
    rho.range = OddFieldLift.Gamma F A ∧
    (∀ x : C i, barKappa i (nu i x) = kappa i x) ∧
    Nonempty (originalSylowImage i p P ≃* Multiplicative F) ∧
    ∃ (Q : Sylow p (coordinateG F)) (g : coordinateG F),
      (Q : Subgroup (coordinateG F)).map (coordinateG F).subtype =
        (originalSylowImage i p P).map
          (((coordinateE F).subtype.comp rho).comp (barKappa i)) ∧
      (originalSylowImage i p P).map
          (((coordinateE F).subtype.comp rho).comp (barKappa i)) =
        (coordinateU F).map (MulAut.conj (g : Equiv.Perm (Omega F))).toMonoidHom

theorem original_full_root_sylow_centralizer
    {G : Type u} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (i : G) (hi : orderOf i = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma i))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma i), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma i) : Set (Gamma i)) = ⊥)
    (hnc : ∀ Q : Sylow 2 (CFSG.generalizedFitting (Gamma i)), ¬ IsCyclic Q)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma i) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    (P : Sylow p (originalT0 i)) : OriginalRootSylowCentralizerConclusion i p f P := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, hfield, hfinite, A, rho, hcard, hqF, hinj, hL, hrange, hmaps⟩ :=
    original_local_faithful_same_field_action n hn S0 f0 hG i hi
      hnonab hcentral hnc p f hp hpodd hf hq hmodel
  let : Field F := hfield
  let : Finite F := hfinite
  let hchar : CharP F p := FixedFieldData.characteristic_of_prime_power_card F hp hcard
  let : CharP F p := hchar
  obtain ⟨hodd, hzorder, hzcenter, hkernel⟩ := original_odd_quotient_involution i hi
  have hinjP := original_sylow_projection_injective i hi p hpodd P
  have hQ := original_sylow_projection_image i p P
  obtain ⟨hab, hcent⟩ := faithful_original_sylow_centralizer i hi p hpodd F rho hinj hL P
  have hdisj := original_sylow_image_disjoint i hi p hpodd P
  have hcomm : ∀ (x : originalSylowImage i p P)
      (y : Subgroup.zpowers (nu i (tInC i))), Commute (x : H i) (y : H i) := by
    intro x y
    exact Subgroup.mem_center_iff.mp (Subgroup.zpowers_le.mpr hzcenter y.property) x
  obtain ⟨efield⟩ := original_sylow_image_equiv_field i hi p hpodd F rho hinj hL P
  have hPcard : Nat.card (originalSylowImage i p P) = p ^ f :=
    (Nat.card_congr efield.toEquiv).trans hcard
  let e : originalSylowImage i p P × Subgroup.zpowers (nu i (tInC i)) ≃*
      Subgroup.centralizer (originalSylowImage i p P : Set (H i)) :=
    (internalProductEquiv _ _ hcomm hdisj).trans (MulEquiv.subgroupCongr hcent.symm)
  have he (x : originalSylowImage i p P) (y : Subgroup.zpowers (nu i (tInC i))) :
      (e (x, y) : H i) = (x : H i) * (y : H i) :=
    internalProductEquiv_apply _ _ hcomm hdisj x y
  refine ⟨hodd, hzorder, hzcenter, hkernel, hinjP, hQ, hab, hdisj, hcomm, hcent, hPcard,
    ⟨e, he, ?_⟩, F, hfield, hfinite, hchar, A, rho, hcard, hqF, hinj, hL, hrange,
      hmaps, ⟨efield⟩, ?_⟩
  · intro c
    refine ⟨e.symm c, ⟨e.apply_symm_apply c, ?_⟩, ?_⟩
    · exact (he (e.symm c).1 (e.symm c).2).symm.trans
        (congrArg Subtype.val (e.apply_symm_apply c))
    · intro xy hxy
      exact e.injective (hxy.1.trans (e.apply_symm_apply c).symm)
  · obtain ⟨Q, hQ, g, hg⟩ := original_sylow_translation_action i p F rho hinj hL P
    exact ⟨Q, g, hQ, hg⟩

theorem original_perfect_full_root_sylow_centralizer
    {G : Type u} [Group G] [Finite G] [Group.IsPerfect G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (i : G) (hi : orderOf i = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma i))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma i), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma i) : Set (Gamma i)) = ⊥)
    (hnc : ∀ Q : Sylow 2 (CFSG.generalizedFitting (Gamma i)), ¬ IsCyclic Q)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma i) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    (P : Sylow p (originalT0 i)) : OriginalRootSylowCentralizerConclusion i p f P :=
  original_full_root_sylow_centralizer n hn S0 f0
    Principal.RotationCongruence.index_ne_two_of_isPerfect i hi
    hnonab hcentral hnc p f hp hpodd hf hq hmodel P

theorem original_simple_full_root_sylow_centralizer
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (i : G) (hi : orderOf i = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma i))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma i), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma i) : Set (Gamma i)) = ⊥)
    (hnc : ∀ Q : Sylow 2 (CFSG.generalizedFitting (Gamma i)), ¬ IsCyclic Q)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma i) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    (P : Sylow p (originalT0 i)) : OriginalRootSylowCentralizerConclusion i p f P :=
  original_full_root_sylow_centralizer n hn S0 f0
    (Principal.index_ne_two_of_isSimpleGroup hGnonab) i hi
    hnonab hcentral hnc p f hp hpodd hf hq hmodel P

end

end CFSG.Semidihedral.FullRootSylowCentralizers

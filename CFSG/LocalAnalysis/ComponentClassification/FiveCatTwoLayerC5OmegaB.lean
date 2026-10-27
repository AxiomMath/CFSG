module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatTwoLayerC5Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentLift

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat.TwoL5.Omega

open CFSG Subgroup CFSG.Open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def AFive (L : Type) [Group L] : Prop :=
  Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 5))

@[expose] def CInv (L : Type) [Group L] : Prop := ∀ z ∈ center L, z * z = 1 → z = 1

theorem AFive.of_mulEquiv {L L' : Type} [Group L] [Group L'] (e : L ≃* L') (h : AFive L) :
    AFive L' :=
  ⟨(QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).symm.trans h.some⟩

theorem mem_center_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) {a : A} :
    e a ∈ center B ↔ a ∈ center A := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h g
    apply e.injective
    rw [map_mul, map_mul]
    exact h (e g)
  · intro h b
    obtain ⟨g, rfl⟩ := e.surjective b
    rw [← map_mul, ← map_mul, h g]

theorem CInv.of_mulEquiv {L L' : Type} [Group L] [Group L'] (e : L ≃* L') (h : CInv L) :
    CInv L' := by
  intro z hz hzz
  have hc : e.symm z ∈ center L := (mem_center_mulEquiv e).1 (by simpa using hz)
  have h1 := h _ hc (by rw [← map_mul, hzz, map_one])
  simpa using congrArg e h1

theorem map_eq_one_of_cInv {Q R : Type} [Group Q] [Group R] (f : Q →* R)
    (hf : Function.Surjective f) (hR : CInv R) {q : Q} (hq : q ∈ center Q) (hqq : q * q = 1) :
    f q = 1 := by
  apply hR
  · rw [Subgroup.mem_center_iff]
    intro r
    obtain ⟨y, rfl⟩ := hf r
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hq y]
  · rw [← map_mul, hqq, map_one]

theorem litLayer_iff {G : Type} [Group G] {L : Subgroup G} :
    LitLayer L ↔ IsComponent L ∧ AFive ↥L ∧ CInv ↥L := by
  constructor
  · rintro ⟨hc, hA, hz⟩
    refine ⟨hc, hA, fun z hzc hzz => ?_⟩
    have := hz z z.2 (fun y hy => by
      have := Subgroup.mem_center_iff.mp hzc ⟨y, hy⟩
      exact congrArg Subtype.val this.symm) (by simpa using congrArg Subtype.val hzz)
    exact Subtype.ext this
  · rintro ⟨hc, hA, hz⟩
    refine ⟨hc, hA, fun z hzL hzc hzz => ?_⟩
    have hmem : (⟨z, hzL⟩ : ↥L) ∈ center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hzc y.1 y.2).symm
    have := hz ⟨z, hzL⟩ hmem (Subtype.ext hzz)
    exact congrArg Subtype.val this

@[expose] def LiftedLit {G : Type} [Group G] (P : G → Prop) (M : Subgroup G) : Prop :=
  IsComponent M ∧ AFive ↥M ∧ ∀ z : ↥M, z ∈ center ↥M → z * z = 1 → P (z : G)

@[expose] def LiftedLitUnique {G : Type} [Group G] (P : G → Prop) : Prop :=
  ∀ M₁ M₂ : Subgroup G, LiftedLit P M₁ → LiftedLit P M₂ → M₁ = M₂

theorem LiftedLitUnique.congr {G : Type} [Group G] {P P' : G → Prop} (hP : ∀ x, P x ↔ P' x)
    (h : LiftedLitUnique P) : LiftedLitUnique P' := by
  have : P = P' := funext fun x => propext (hP x)
  rwa [← this]

theorem LiftedLitUnique.of_injective {G' G : Type} [Group G'] [Group G] (j : G' →* G)
    (hj : Function.Injective j)
    (hcomp : ∀ M' : Subgroup G', IsComponent M' → IsComponent (M'.map j))
    {P : G → Prop} (h : LiftedLitUnique P) : LiftedLitUnique (fun x : G' => P (j x)) := by
  have key : ∀ M' : Subgroup G', LiftedLit (fun x : G' => P (j x)) M' → LiftedLit P (M'.map j) := by
    rintro M' ⟨hc, hA, hz⟩
    let ε : ↥M' ≃* ↥(M'.map j) := M'.equivMapOfInjective j hj
    refine ⟨hcomp M' hc, AFive.of_mulEquiv ε hA, fun z hzc hzz => ?_⟩
    have hw : ε.symm z ∈ center ↥M' := (mem_center_mulEquiv ε.symm).2 hzc
    have hww : ε.symm z * ε.symm z = 1 := by rw [← map_mul, hzz, map_one]
    have h1 := hz _ hw hww
    have h2 : j ((ε.symm z : ↥M') : G') = (z : G) := by
      have h3 := Subgroup.coe_equivMapOfInjective_apply M' j hj (ε.symm z)
      have h4 : (M'.equivMapOfInjective j hj) (ε.symm z) = z := ε.apply_symm_apply z
      rw [h4] at h3
      exact h3.symm
    rwa [← h2]
  intro M₁ M₂ h₁ h₂
  exact Subgroup.map_injective hj (h _ _ (key M₁ h₁) (key M₂ h₂))

theorem LiftedLitUnique.of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H) {P : H → Prop}
    (h : LiftedLitUnique P) : LiftedLitUnique (fun x : G => P (e x)) :=
  LiftedLitUnique.of_injective e.toMonoidHom e.injective
    (fun _ hM => LocalCores.isComponent_map_mulEquiv e hM) h

theorem LiftedLitUnique.of_normal_subtype {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    {P : G → Prop} (h : LiftedLitUnique P) : LiftedLitUnique (fun x : ↥N => P (x : G)) :=
  LiftedLitUnique.of_injective N.subtype N.subtype_injective
    (fun _ hM => CatLeafProof.isComponent_map_subtype_of_normal hM) h

theorem exists_surjective_of_map_eq {P S : Type} [Group P] [Group S] (π : P →* S)
    {Q : Subgroup P} {R : Subgroup S} (h : Q.map π = R) :
    ∃ f : ↥Q →* ↥R, Function.Surjective f ∧ ∀ x : ↥Q, ((f x : ↥R) : S) = π (x : P) := by
  refine ⟨(π.comp Q.subtype).codRestrict R fun x => by rw [← h]; exact ⟨x, x.2, rfl⟩, ?_,
    fun x => rfl⟩
  rintro ⟨r, hr⟩
  rw [← h] at hr
  obtain ⟨x, hx, rfl⟩ := hr
  exact ⟨⟨x, hx⟩, rfl⟩

theorem litUnique_of_central_cover {P S : Type} [Group P] [Group S] [Finite P] {π : P →* S}
    (hπ : Function.Surjective π) (hK : π.ker ≤ center P) {a : MulAut P} {α : MulAut S}
    (ha : ∀ x, a (a x) = x) (hα : ∀ s, α (α s) = s) (hcomm : ∀ x, π (a x) = α (π x))
    (h : LiftedLitUnique (fun x : ↥(fixedSubgroup a) => π (x : P) = 1)) :
    LitUnique ↥(fixedSubgroup α) := by
  have : Finite S := Finite.of_surjective π hπ
  obtain ⟨-, -, -, hlift, -⟩ :=
    LocalAnalysis.ComponentInitial.full_central_kernel_involution_fixed_component_correspondence
      hπ hK ha hα hcomm
  have key : ∀ L : Subgroup ↥(fixedSubgroup α), LitLayer L →
      ∃ M : Subgroup ↥(fixedSubgroup a),
        LiftedLit (fun x : ↥(fixedSubgroup a) => π (x : P) = 1) M ∧
          (M.map (fixedSubgroup a).subtype).map π = L.map (fixedSubgroup α).subtype := by
    intro L hL
    obtain ⟨hLc, hLA, hLz⟩ := litLayer_iff.mp hL
    have hLR : (L.map (fixedSubgroup α).subtype).subgroupOf (fixedSubgroup α) = L :=
      comap_map_eq_self_of_injective (subtype_injective _) L
    have hRC : CFSG.Assembly.IsComponentOf (L.map (fixedSubgroup α).subtype)
        (fixedSubgroup α) :=
      (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
        (map_subtype_le L)).2 (by rw [hLR]; exact hLc)
    obtain ⟨-, hQB, hQmap, -, -, -, ⟨eQ⟩⟩ := hlift _ hRC
    set Q := ⁅(L.map (fixedSubgroup α).subtype).comap π,
      (L.map (fixedSubgroup α).subtype).comap π⁆ with hQ
    let eLR : ↥L ≃* ↥(L.map (fixedSubgroup α).subtype) :=
      L.equivMapOfInjective _ (subtype_injective _)
    have hAR : AFive ↥(L.map (fixedSubgroup α).subtype) := AFive.of_mulEquiv eLR hLA
    have hCR : CInv ↥(L.map (fixedSubgroup α).subtype) := CInv.of_mulEquiv eLR hLz
    have hAQ : AFive ↥Q := ⟨eQ.trans hAR.some⟩
    let eM : ↥(Q.subgroupOf (fixedSubgroup a)) ≃* ↥Q := Subgroup.subgroupOfEquivOfLe hQB.1
    obtain ⟨f, hf, hfπ⟩ := exists_surjective_of_map_eq π hQmap
    refine ⟨Q.subgroupOf (fixedSubgroup a), ⟨?_, AFive.of_mulEquiv eM.symm hAQ, ?_⟩, ?_⟩
    · exact (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hQB.1).1 hQB
    · intro z hzc hzz
      have hq : eM z ∈ center ↥Q := (mem_center_mulEquiv eM).2 hzc
      have hqq : eM z * eM z = 1 := by rw [← map_mul, hzz, map_one]
      have h1 := map_eq_one_of_cInv f hf hCR hq hqq
      have h2 := hfπ (eM z)
      rw [h1] at h2
      exact h2.symm
    · rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hQB.1, hQmap]
  intro L₁ L₂ h₁ h₂
  obtain ⟨M₁, hM₁, himg₁⟩ := key L₁ h₁
  obtain ⟨M₂, hM₂, himg₂⟩ := key L₂ h₂
  have hM : M₁ = M₂ := h M₁ M₂ hM₁ hM₂
  subst hM
  exact Subgroup.map_injective (subtype_injective _) (himg₁.symm.trans himg₂)

open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed in
theorem litUnique_of_normalQuotient {X : Type} [Group X] [Finite X] (N Z : Subgroup X)
    [N.Normal] [Z.Normal] (hcentral : Z ≤ center X) (ψ : MulAut X) (hψ : ∀ x, ψ (ψ x) = x)
    (hN : N.map ψ.toMonoidHom = N) (hZ : Z.map ψ.toMonoidHom = Z)
    (h : LiftedLitUnique (fun z : ↥(fixedSubgroup ψ) => (z : X) ∈ Z)) :
    LitUnique ↥(fixedSubgroup (onNormalCentralQuotient N Z ψ hN hZ)) := by
  set a := restrictAutomorphism N ψ hN with ha_def
  have hπ : Function.Surjective (QuotientGroup.mk' (Z.subgroupOf N)) :=
    QuotientGroup.mk'_surjective _
  have hK : (QuotientGroup.mk' (Z.subgroupOf N)).ker ≤ center ↥N := by
    rw [QuotientGroup.ker_mk']
    exact central_subgroupOf N Z hcentral
  have ha : ∀ x, a (a x) = x := fun x => Subtype.ext (by
    rw [ha_def, restrictAutomorphism_apply, restrictAutomorphism_apply]
    exact hψ x.val)
  have hcomm : ∀ x, QuotientGroup.mk' (Z.subgroupOf N) (a x) =
      onNormalCentralQuotient N Z ψ hN hZ (QuotientGroup.mk' (Z.subgroupOf N) x) :=
    fun x => (onNormalCentralQuotient_mk N Z ψ hN hZ x).symm
  have hα : ∀ s, onNormalCentralQuotient N Z ψ hN hZ
      (onNormalCentralQuotient N Z ψ hN hZ s) = s := by
    intro s
    obtain ⟨x, rfl⟩ := hπ s
    rw [← hcomm, ← hcomm, ha]
  refine litUnique_of_central_cover hπ hK ha hα hcomm ?_
  have : (N.subgroupOf (fixedSubgroup ψ)).Normal := Subgroup.Normal.subgroupOf inferInstance _
  have h1 := LiftedLitUnique.of_normal_subtype (N.subgroupOf (fixedSubgroup ψ)) h
  have h2 := LiftedLitUnique.of_mulEquiv (fixedNormalEquiv N ψ hN) h1
  refine LiftedLitUnique.congr (fun x => ?_) h2
  rw [fixedNormalEquiv_apply]
  rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]

end CFSG.ComponentClassification.SolMax.FiveCat.TwoL5.Omega

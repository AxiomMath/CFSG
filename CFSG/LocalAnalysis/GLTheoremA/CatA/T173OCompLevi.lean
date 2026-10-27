module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.Quasithin.Background.A1aFStar

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open

private theorem mem_centralizer_of_mem_mul_unique {G : Type} [Group G]
    {P Q L : Subgroup G} (hQP : Q ≤ P) (hLP : L ≤ P) (hQn : (Q.subgroupOf P).Normal)
    (huniq : ∀ g ∈ P, ∃! ql : G × G, ql.1 ∈ Q ∧ ql.2 ∈ L ∧ g = ql.1 * ql.2)
    {d k q l : G} (hd : d ∈ L) (hkP : k ∈ P)
    (hkC : k ∈ Subgroup.centralizer ({d} : Set G))
    (hq : q ∈ Q) (hl : l ∈ L) (hkl : k = q * l) :
    q ∈ Subgroup.centralizer ({d} : Set G) ∧ l ∈ Subgroup.centralizer ({d} : Set G) := by
  have hdP : d ∈ P := hLP hd
  have hkd : k * d = d * k := Subgroup.mem_centralizer_singleton_iff.mp hkC
  have hconj : d * k * d⁻¹ = k := by rw [← hkd]; group
  have hQconj : d * q * d⁻¹ ∈ Q :=
    (Subgroup.normal_subgroupOf_iff hQP).mp hQn q d hq hdP
  have hLconj : d * l * d⁻¹ ∈ L := L.mul_mem (L.mul_mem hd hl) (L.inv_mem hd)
  have hpair : (d * q * d⁻¹, d * l * d⁻¹) = (q, l) := by
    have heq : k = (d * q * d⁻¹) * (d * l * d⁻¹) := by
      calc k = d * k * d⁻¹ := hconj.symm
        _ = d * (q * l) * d⁻¹ := by rw [hkl]
        _ = (d * q * d⁻¹) * (d * l * d⁻¹) := by group
    exact (huniq k hkP).unique ⟨hQconj, hLconj, heq⟩ ⟨hq, hl, hkl⟩
  have hqd : d * q * d⁻¹ = q := congrArg Prod.fst hpair
  have hld : d * l * d⁻¹ = l := congrArg Prod.snd hpair
  refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_,
    Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  · calc q * d = (d * q * d⁻¹) * d := by rw [hqd]
      _ = d * q := by group
  · calc l * d = (d * l * d⁻¹) * d := by rw [hld]
      _ = d * l := by group

private theorem commutator_eq_bot_of_isComponentOf_centralizer_inf {G : Type} [Group G]
    [Finite G] {P Q : Subgroup G} (hQP : Q ≤ P) (hQn : (Q.subgroupOf P).Normal)
    (hQs : IsSolvable ↥Q) {d : G} {Kb : Subgroup G}
    (hK : IsComponentOf Kb (Subgroup.centralizer ({d} : Set G) ⊓ P)) :
    ⁅Kb, Q ⊓ Subgroup.centralizer ({d} : Set G)⁆ = ⊥ := by
  classical
  set C : Subgroup G := Subgroup.centralizer ({d} : Set G)
  set CP : Subgroup G := C ⊓ P
  have hKb : Kb ≤ CP := hK.1
  have hQnorm : P ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mp hQn
  have hsol : IsSolvable ↥(Q ⊓ C) := by
    haveI : Group.IsSolvable ↥Q := hQs
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective inf_le_left)
  have hAR : CP ≤ Subgroup.normalizer ((Q ⊓ C : Subgroup G) : Set G) := by
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hQnorm hx.2, Subgroup.le_normalizer hx.1⟩
  have hRA : Q ⊓ C ≤ CP := le_inf inf_le_right (inf_le_left.trans hQP)
  have hRn : ((Q ⊓ C).subgroupOf CP).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRA).mpr hAR
  have hKsub : CFSG.IsComponent (Kb.subgroupOf CP) :=
    (CFSG.isComponent_iff_open (Kb.subgroupOf CP)).mpr
      ((CFSG.Quasithin.isComponentOf_iff_subgroupOf.mp hK).2)
  have hRsolv : IsSolvable ↥((Q ⊓ C).subgroupOf CP) := by
    haveI : Group.IsSolvable ↥(Q ⊓ C) := hsol
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hRA).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hRA).injective
  have hcomm : ⁅Kb.subgroupOf CP, (Q ⊓ C).subgroupOf CP⁆ = ⊥ :=
    (CFSG.LocalCores.component_solvable_centralizer (G := ↥CP) hRsolv
      hRn.isSubnormal).1 (Kb.subgroupOf CP) hKsub
  have hcent : Kb.subgroupOf CP ≤
      Subgroup.centralizer (((Q ⊓ C).subgroupOf CP : Subgroup ↥CP) : Set ↥CP) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr ?_
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hk' : (⟨k, hKb hk⟩ : ↥CP) ∈ Kb.subgroupOf CP := hk
  have hq' : (⟨q, hRA hq⟩ : ↥CP) ∈ (Q ⊓ C).subgroupOf CP := hq
  exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp (hcent hk') _ hq')

private theorem exists_qPart_of_isComponentOf_centralizer_inf {G : Type} [Group G]
    {P Q L : Subgroup G} (hQP : Q ≤ P) (hLP : L ≤ P) (hQn : (Q.subgroupOf P).Normal)
    (huniq : ∀ g ∈ P, ∃! ql : G × G, ql.1 ∈ Q ∧ ql.2 ∈ L ∧ g = ql.1 * ql.2)
    {d : G} (hd : d ∈ L) {Kb : Subgroup G}
    (hK : IsComponentOf Kb (Subgroup.centralizer ({d} : Set G) ⊓ P)) :
    ∃ qf lf : Kb → G,
      (∀ k : Kb, qf k ∈ Q) ∧ (∀ k : Kb, lf k ∈ L) ∧
        (∀ k : Kb, (k : G) = qf k * lf k) ∧
          (∀ k : Kb, qf k ∈ Subgroup.centralizer ({d} : Set G)) := by
  classical
  set C : Subgroup G := Subgroup.centralizer ({d} : Set G)
  have hKbP : Kb ≤ P := hK.1.trans inf_le_right
  let qf : Kb → G := fun k => (Classical.choose (huniq (k : G) (hKbP k.2))).1
  let lf : Kb → G := fun k => (Classical.choose (huniq (k : G) (hKbP k.2))).2
  have hqfm : ∀ k : Kb, qf k ∈ Q := fun k =>
    (Classical.choose_spec (huniq (k : G) (hKbP k.2))).1.1
  have hlfm : ∀ k : Kb, lf k ∈ L := fun k =>
    (Classical.choose_spec (huniq (k : G) (hKbP k.2))).1.2.1
  have hdec : ∀ k : Kb, (k : G) = qf k * lf k := fun k =>
    (Classical.choose_spec (huniq (k : G) (hKbP k.2))).1.2.2
  have hqfC : ∀ k : Kb, qf k ∈ C := fun k =>
    (mem_centralizer_of_mem_mul_unique hQP hLP hQn huniq hd (hKbP k.2) (hK.1 k.2).1
      (hqfm k) (hlfm k) (hdec k)).1
  exact ⟨qf, lf, hqfm, hlfm, hdec, hqfC⟩

private theorem qPart_mul_comm_of_isComponentOf_centralizer_inf {G : Type} [Group G]
    {P Q L : Subgroup G} (hQP : Q ≤ P) (hLP : L ≤ P) (hQn : (Q.subgroupOf P).Normal)
    (huniq : ∀ g ∈ P, ∃! ql : G × G, ql.1 ∈ Q ∧ ql.2 ∈ L ∧ g = ql.1 * ql.2)
    {d : G} {Kb : Subgroup G} (hKbP : Kb ≤ P) {qf lf : Kb → G}
    (hqfm : ∀ k : Kb, qf k ∈ Q) (hlfm : ∀ k : Kb, lf k ∈ L)
    (hdec : ∀ k : Kb, (k : G) = qf k * lf k)
    (hqfC : ∀ k : Kb, qf k ∈ Subgroup.centralizer ({d} : Set G))
    (hcent : Kb ≤ Subgroup.centralizer
      ((Q ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) : Set G))
    (k₁ k₂ : Kb) : qf (k₁ * k₂) = qf k₂ * qf k₁ := by
  have hcq : (k₁ : G) * qf k₂ = qf k₂ * (k₁ : G) :=
    (Subgroup.mem_centralizer_iff.mp (hcent k₁.2) (qf k₂) ⟨hqfm k₂, hqfC k₂⟩).symm
  rw [hdec k₁] at hcq
  have hconjq : lf k₁ * qf k₂ * (lf k₁)⁻¹ = (qf k₁)⁻¹ * qf k₂ * qf k₁ := by
    calc lf k₁ * qf k₂ * (lf k₁)⁻¹
        = (qf k₁)⁻¹ * (qf k₁ * lf k₁ * qf k₂) * (lf k₁)⁻¹ := by group
      _ = (qf k₁)⁻¹ * (qf k₂ * (qf k₁ * lf k₁)) * (lf k₁)⁻¹ := by rw [hcq]
      _ = (qf k₁)⁻¹ * qf k₂ * qf k₁ := by group
  have hQmem : qf k₁ * (lf k₁ * qf k₂ * (lf k₁)⁻¹) ∈ Q :=
    Q.mul_mem (hqfm k₁)
      ((Subgroup.normal_subgroupOf_iff hQP).mp hQn (qf k₂) (lf k₁) (hqfm k₂) (hLP (hlfm k₁)))
  have hpair : (qf (k₁ * k₂), lf (k₁ * k₂)) =
      (qf k₁ * (lf k₁ * qf k₂ * (lf k₁)⁻¹), lf k₁ * lf k₂) := by
    refine (huniq ((k₁ * k₂ : Kb) : G) (hKbP (k₁ * k₂).2)).unique
      ⟨hqfm _, hlfm _, hdec _⟩ ⟨hQmem, ?_, ?_⟩
    · exact L.mul_mem (hlfm k₁) (hlfm k₂)
    · change (k₁ : G) * (k₂ : G) =
        (qf k₁ * (lf k₁ * qf k₂ * (lf k₁)⁻¹)) * (lf k₁ * lf k₂)
      rw [hdec k₁, hdec k₂]
      group
  calc qf (k₁ * k₂) = qf k₁ * (lf k₁ * qf k₂ * (lf k₁)⁻¹) :=
        congrArg Prod.fst hpair
    _ = qf k₁ * ((qf k₁)⁻¹ * qf k₂ * qf k₁) := by rw [hconjq]
    _ = qf k₂ * qf k₁ := by group

theorem le_of_isComponentOf_centralizer_inf {G : Type} [Group G] [Finite G]
    {P Q L : Subgroup G} (hQP : Q ≤ P) (hLP : L ≤ P) (hQn : (Q.subgroupOf P).Normal)
    (huniq : ∀ g ∈ P, ∃! ql : G × G, ql.1 ∈ Q ∧ ql.2 ∈ L ∧ g = ql.1 * ql.2)
    (hQs : IsSolvable ↥Q) {d : G} (hd : d ∈ L) {Kb : Subgroup G}
    (hK : IsComponentOf Kb (Subgroup.centralizer ({d} : Set G) ⊓ P)) : Kb ≤ L := by
  classical
  set C : Subgroup G := Subgroup.centralizer ({d} : Set G)
  have hcent : Kb ≤ Subgroup.centralizer ((Q ⊓ C : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (commutator_eq_bot_of_isComponentOf_centralizer_inf hQP hQn hQs hK)
  obtain ⟨qf, lf, hqfm, hlfm, hdec, hqfC⟩ :=
    exists_qPart_of_isComponentOf_centralizer_inf hQP hLP hQn huniq hd hK
  have hanti : ∀ k₁ k₂ : Kb, qf (k₁ * k₂) = qf k₂ * qf k₁ :=
    qPart_mul_comm_of_isComponentOf_centralizer_inf hQP hLP hQn huniq
      (hK.1.trans inf_le_right) hqfm hlfm hdec hqfC hcent
  let ψ : Kb →* ↥Q :=
    { toFun := fun k => ⟨(qf k)⁻¹, Q.inv_mem (hqfm k)⟩
      map_one' := by
        apply Subtype.ext
        change (qf 1)⁻¹ = 1
        have hq1 : qf 1 = 1 := by
          have h := congrArg (fun x => (qf 1)⁻¹ * x) (by simpa using hanti 1 1)
          simpa [mul_assoc] using h.symm
        rw [hq1, inv_one]
      map_mul' := by
        intro k₁ k₂
        apply Subtype.ext
        change (qf (k₁ * k₂))⁻¹ = (qf k₁)⁻¹ * (qf k₂)⁻¹
        rw [hanti k₁ k₂, mul_inv_rev] }
  haveI : Group.IsPerfect ↥Kb := ⟨hK.2.2.1⟩
  haveI : Group.IsSolvable ↥Q := hQs
  have hψ : ψ = 1 := CFSG.ComponentClassification.SolvableKernelContainment.hom_eq_one ψ
  intro k hk
  have hval : (qf ⟨k, hk⟩)⁻¹ = 1 := by
    have h := congrArg (fun f : Kb →* ↥Q => (f ⟨k, hk⟩ : ↥Q)) hψ
    simpa [ψ] using h
  have hqk : qf ⟨k, hk⟩ = 1 := inv_eq_one.mp hval
  have hmem : (k : G) = lf ⟨k, hk⟩ := by
    have h := hdec ⟨k, hk⟩
    rw [hqk, one_mul] at h
    simpa using h
  exact hmem ▸ hlfm ⟨k, hk⟩

end CFSG.LocalAnalysis.GLTheoremA.T173O

end

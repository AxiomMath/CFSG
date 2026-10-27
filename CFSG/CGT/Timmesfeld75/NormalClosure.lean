module

public import CFSG.CGT.Timmesfeld75.WeaklyClosed

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type*} [Group G]

section Conjugates

theorem mem_smul_sylow_iff_inv_mul_mul_mem {X : Type*} [Group X] {p : ℕ} {S : Sylow p X}
    {x y : X} : y ∈ x • S ↔ x⁻¹ * y * x ∈ S := by
  show y ∈ ((x • S : Sylow p X) : Subgroup X) ↔ _
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [MulAut.smul_def, MulAut.conj_inv_apply]
  exact Iff.rfl

theorem conjSubgroup_le_of_le_of_mem {T K : Subgroup G} (hTK : T ≤ K) {g : G} (hg : g ∈ K) :
    conjSubgroup g T ≤ K := by
  intro y hy
  have h := K.mul_mem (K.mul_mem hg (hTK (mem_conjSubgroup.1 hy))) (K.inv_mem hg)
  simpa [mul_assoc] using h

theorem exists_mem_conj_eq_of_le [Finite G] {T : Subgroup G} (hT : IsWC T) {X : Subgroup G}
    (hTX : T ≤ X) {g : G} (hg : conjSubgroup g T ≤ X) :
    ∃ x ∈ X, conjSubgroup g T = conjSubgroup x T := by
  obtain ⟨S, hS⟩ := ((isPGroup_two_of_isElemAbelian hT.1).comap_subtype (K := X)).exists_le_sylow
  obtain ⟨S', hS'⟩ :=
    ((isPGroup_two_of_isElemAbelian (isElemAbelian_conjSubgroup hT.1 g)).comap_subtype
      (K := X)).exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X S S'
  have hPp : IsPGroup 2 ((S : Subgroup X).map X.subtype) := S.isPGroup'.map X.subtype
  have hTP : T ≤ (S : Subgroup X).map X.subtype := fun t ht => ⟨⟨t, hTX ht⟩, hS ht, rfl⟩
  have hkP : conjSubgroup ((x : G)⁻¹ * g) T ≤ (S : Subgroup X).map X.subtype := by
    intro z hz
    have h1 : (x : G) * z * (x : G)⁻¹ ∈ conjSubgroup g T := by
      rw [mem_conjSubgroup]
      convert mem_conjSubgroup.1 hz using 1
      group
    have hzX : z ∈ X := by
      have := X.mul_mem (X.mul_mem (X.inv_mem x.2) (hg h1)) x.2
      simpa [mul_assoc] using this
    have h2 : (⟨(x : G) * z * (x : G)⁻¹, hg h1⟩ : X) ∈ S' := hS' h1
    rw [← hx, mem_smul_sylow_iff_inv_mul_mul_mem] at h2
    have e : x⁻¹ * (⟨(x : G) * z * (x : G)⁻¹, hg h1⟩ : X) * x = ⟨z, hzX⟩ :=
      Subtype.ext (by simp [mul_assoc])
    rw [e] at h2
    exact ⟨⟨z, hzX⟩, h2, rfl⟩
  have hk := eq_of_conj_le_pGroup hT hPp hTP hkP
  refine ⟨x, x.2, ?_⟩
  calc conjSubgroup g T = conjSubgroup ((x : G) * ((x : G)⁻¹ * g)) T := by
        rw [mul_inv_cancel_left]
    _ = conjSubgroup (x : G) (conjSubgroup ((x : G)⁻¹ * g) T) :=
        (conjSubgroup_conjSubgroup _ _ _).symm
    _ = conjSubgroup (x : G) T := by rw [hk]

theorem conjSubgroup_le_normalClosure (T : Subgroup G) (g : G) :
    conjSubgroup g T ≤ Subgroup.normalClosure (T : Set G) := by
  intro y hy
  have h : g⁻¹ * y * g ∈ Subgroup.normalClosure (T : Set G) :=
    Subgroup.le_normalClosure (mem_conjSubgroup.1 hy)
  simpa [mul_assoc] using Subgroup.normalClosure_normal.conj_mem _ h g

theorem exists_mem_normalClosure_conj_eq [Finite G] {T : Subgroup G} (hT : IsWC T) (g : G) :
    ∃ h ∈ Subgroup.normalClosure (T : Set G), conjSubgroup g T = conjSubgroup h T :=
  exists_mem_conj_eq_of_le hT Subgroup.le_normalClosure (conjSubgroup_le_normalClosure T g)

end Conjugates

section SubgroupOf

theorem conjSubgroup_subgroupOf (K T : Subgroup G) (g : K) :
    conjSubgroup g (T.subgroupOf K) = (conjSubgroup (g : G) T).subgroupOf K := by
  ext y
  rw [mem_conjSubgroup, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, mem_conjSubgroup]
  rfl

theorem normalClosure_subgroupOf_eq_top [Finite G] {T : Subgroup G} (hT : IsWC T) :
    Subgroup.normalClosure
      ((T.subgroupOf (Subgroup.normalClosure (T : Set G)) :
        Subgroup ↥(Subgroup.normalClosure (T : Set G))) :
        Set ↥(Subgroup.normalClosure (T : Set G))) = ⊤ := by
  have hconj := exists_mem_normalClosure_conj_eq hT
  generalize hK : Subgroup.normalClosure (T : Set G) = K at hconj ⊢
  have hTK : T ≤ K := Subgroup.le_normalClosure.trans hK.le
  set M := Subgroup.normalClosure ((T.subgroupOf K : Subgroup K) : Set K) with hM
  have hKM : K ≤ M.map K.subtype := by
    refine hK.ge.trans ((Subgroup.closure_le _).2 ?_)
    intro x hx
    obtain ⟨a, ha, hconjxa⟩ := Group.mem_conjugatesOfSet_iff.1 hx
    obtain ⟨c, rfl⟩ := isConj_iff.1 hconjxa
    obtain ⟨h, hhK, hch⟩ := hconj c
    have hx' : c * a * c⁻¹ ∈ conjSubgroup h T := by
      rw [← hch, mem_conjSubgroup]
      simpa [mul_assoc] using ha
    have ht : h⁻¹ * (c * a * c⁻¹) * h ∈ T := mem_conjSubgroup.1 hx'
    have htM : (⟨h⁻¹ * (c * a * c⁻¹) * h, hTK ht⟩ : K) ∈ M :=
      Subgroup.subset_normalClosure (Subgroup.mem_subgroupOf.2 ht)
    refine ⟨_, Subgroup.normalClosure_normal.conj_mem _ htM ⟨h, hhK⟩, ?_⟩
    simp [mul_assoc]
  rw [eq_top_iff]
  intro y _
  obtain ⟨m, hm, hmy⟩ := hKM y.2
  rwa [show m = y from Subtype.ext hmy] at hm

theorem isWC_subgroupOf {T : Subgroup G} (hT : IsWC T) (K : Subgroup G) (hTK : T ≤ K) :
    IsWC (T.subgroupOf K) := by
  refine ⟨⟨?_, fun x hx => ?_⟩, fun t ht ht1 => ?_⟩
  · have := hT.1.1
    infer_instance
  · exact Subtype.ext (hT.1.2 (x : G) (Subgroup.mem_subgroupOf.1 hx))
  · have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.1 ht
    have ht1' : (t : G) ≠ 1 := fun h => ht1 (Subtype.ext h)
    refine ⟨fun x hx => ?_, fun g hg => ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact Subtype.ext (elemAbelian_mul_comm hT.1 htT (Subgroup.mem_subgroupOf.1 hx))
    ·
      have hTg : conjSubgroup (g : G) T ≤ Subgroup.centralizer ({(t : G)} : Set G) := by
        intro y hy
        have hyK : y ∈ K := conjSubgroup_le_of_le_of_mem hTK g.2 hy
        have hyg : (⟨y, hyK⟩ : K) ∈ conjSubgroup g (T.subgroupOf K) := by
          rw [conjSubgroup_subgroupOf]
          exact Subgroup.mem_subgroupOf.2 hy
        have hc := Subgroup.mem_centralizer_iff.1 (hg hyg) t (Set.mem_singleton t)
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact congrArg Subtype.val hc
      rw [conjSubgroup_subgroupOf, (hT.2 (t : G) htT ht1').2 (g : G) hTg]

theorem isWC_subgroupOf_normalClosure {T : Subgroup G} (hT : IsWC T) :
    IsWC (T.subgroupOf (Subgroup.normalClosure (T : Set G))) :=
  isWC_subgroupOf hT _ Subgroup.le_normalClosure

end SubgroupOf

end CFSG.CGT.Timmesfeld75

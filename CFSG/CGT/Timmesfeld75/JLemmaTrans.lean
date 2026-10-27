module

public import CFSG.CGT.Timmesfeld75.JLemmaQuot

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

section Abstract

variable {R : Type} [Group R] [Finite R]

theorem odd_card_center_quot_pCore :
    Odd (Nat.card (Subgroup.center (R ⧸ CFSG.pCore 2 R))) :=
  odd_card_center normal_pGroup_quot_pCore_eq_bot

theorem le_sup_pCore_of_map_jMap_le {S S' : Subgroup R} (hS : IsElemAbelian 2 S)
    (hS' : IsElemAbelian 2 S') (h : S.map (jMap R) ≤ S'.map (jMap R)) :
    S ≤ S' ⊔ CFSG.pCore 2 R := by
  intro u hu
  obtain ⟨s, hs, hsu⟩ := Subgroup.mem_map.1 (h (Subgroup.mem_map_of_mem _ hu))
  have hw : s⁻¹ * u ∈ (jMap R).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hsu, inv_mul_cancel]
  have hz : QuotientGroup.mk' (CFSG.pCore 2 R) (s⁻¹ * u) ∈
      Subgroup.center (R ⧸ CFSG.pCore 2 R) :=
    (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hw)
  have hss : s * s = 1 := elemAbelian_mul_self hS' hs
  have huu : u * u = 1 := elemAbelian_mul_self hS hu
  have hsu' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hw2 : (s⁻¹ * u) * (s⁻¹ * u) ∈ CFSG.pCore 2 R := by
    set mk := QuotientGroup.mk' (CFSG.pCore 2 R) with hmk
    have hc : mk (s⁻¹ * u) * mk s = mk s * mk (s⁻¹ * u) :=
      (Subgroup.mem_center_iff.1 hz (mk s)).symm
    have e : mk ((s⁻¹ * u) * (s⁻¹ * u)) = 1 := by
      have e1 : (s⁻¹ * u) * (s⁻¹ * u) = (s⁻¹ * u) * (s⁻¹ * u) := rfl
      have e2 : mk ((s⁻¹ * u) * (s⁻¹ * u)) = mk (s⁻¹ * u) * mk (s⁻¹ * u) := map_mul _ _ _
      have e3 : mk u = mk s * mk (s⁻¹ * u) := by
        rw [← map_mul]
        congr 1
        group
      have e4 : mk u * mk u = 1 := by rw [← map_mul, huu, map_one]
      have e5 : mk s * mk s = 1 := by rw [← map_mul, hss, map_one]
      calc mk ((s⁻¹ * u) * (s⁻¹ * u)) = mk (s⁻¹ * u) * mk (s⁻¹ * u) := e2
        _ = (mk s * mk s) * (mk (s⁻¹ * u) * mk (s⁻¹ * u)) := by rw [e5, one_mul]
        _ = mk s * (mk s * mk (s⁻¹ * u)) * mk (s⁻¹ * u) := by group
        _ = mk s * (mk (s⁻¹ * u) * mk s) * mk (s⁻¹ * u) := by rw [← hc]
        _ = (mk s * mk (s⁻¹ * u)) * (mk s * mk (s⁻¹ * u)) := by group
        _ = mk u * mk u := by rw [← e3]
        _ = 1 := e4
    exact (QuotientGroup.eq_one_iff _).1 e
  have hwO : s⁻¹ * u ∈ CFSG.pCore 2 R := by
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 R) (s⁻¹ * u) = 1 := by
      refine eq_one_of_mul_self_of_odd (odd_card_center_quot_pCore (R := R)) hz ?_
      rw [← map_mul]
      exact (QuotientGroup.eq_one_iff _).2 hw2
    exact (QuotientGroup.eq_one_iff _).1 h1
  have : u = s * (s⁻¹ * u) := by group
  rw [this]
  exact Subgroup.mul_mem_sup hs hwO

theorem eq_of_map_jMap_le {T : Subgroup R} (hT : IsWC T) {a b : R}
    (h : (conjSubgroup a T).map (jMap R) ≤ (conjSubgroup b T).map (jMap R)) :
    conjSubgroup a T = conjSubgroup b T := by
  have hle := le_sup_pCore_of_map_jMap_le (isElemAbelian_conjSubgroup hT.1 a)
    (isElemAbelian_conjSubgroup hT.1 b) h
  have hwcb : IsWC (conjSubgroup b T) := hT.conj b
  have hS : IsPGroup 2 ↥(conjSubgroup b T ⊔ CFSG.pCore 2 R) :=
    (isPGroup_two_of_isElemAbelian hwcb.1).to_sup_of_normal_right CFSG.pCore_isPGroup
  have hconj : conjSubgroup (a * b⁻¹) (conjSubgroup b T) ≤ conjSubgroup b T ⊔ CFSG.pCore 2 R := by
    rw [conjSubgroup_conjSubgroup, show a * b⁻¹ * b = a by group]
    exact hle
  have := eq_of_conj_le_pGroup hwcb hS le_sup_left hconj
  rwa [conjSubgroup_conjSubgroup, show a * b⁻¹ * b = a by group] at this

theorem exists_mem_conj_of_jMap {T : Subgroup R} (hT : IsWC T)
    (hconcl : Lemma26Concl (jQuot R) (T.map (jMap R)))
    (hA6 : ¬ Nonempty (jQuot R ⧸ Subgroup.center (jQuot R) ≃* alternatingGroup (Fin 6)))
    {a₁ a₂ b₁ b₂ : R} (hne₁ : conjSubgroup a₁ T ≠ conjSubgroup a₂ T)
    (hne₂ : conjSubgroup b₁ T ≠ conjSubgroup b₂ T) :
    ∃ r : R, conjSubgroup r (conjSubgroup a₁ T) = conjSubgroup b₁ T ∧
      conjSubgroup r (conjSubgroup a₂ T) = conjSubgroup b₂ T := by
  have hmap : ∀ a : R, (conjSubgroup a T).map (jMap R) = conjSubgroup (jMap R a) (T.map (jMap R)) :=
    fun a => map_conjSubgroup (jMap R) a T
  have hne : ∀ {c d : R}, conjSubgroup c T ≠ conjSubgroup d T →
      (conjSubgroup c T).map (jMap R) ≠ (conjSubgroup d T).map (jMap R) :=
    fun h h' => h (eq_of_map_jMap_le hT h'.le)
  obtain ⟨k, hk1, hk2⟩ := hconcl.2 hA6 ((conjSubgroup a₁ T).map (jMap R))
    ((conjSubgroup a₂ T).map (jMap R)) ((conjSubgroup b₁ T).map (jMap R))
    ((conjSubgroup b₂ T).map (jMap R)) ⟨jMap R a₁, hmap a₁⟩ ⟨jMap R a₂, hmap a₂⟩
    ⟨jMap R b₁, hmap b₁⟩ ⟨jMap R b₂, hmap b₂⟩ (hne hne₁) (hne hne₂)
  obtain ⟨r, rfl⟩ := jMap_surjective k
  have key : ∀ {c d : R}, conjSubgroup (jMap R r) ((conjSubgroup c T).map (jMap R)) =
      (conjSubgroup d T).map (jMap R) → conjSubgroup r (conjSubgroup c T) = conjSubgroup d T := by
    intro c d h
    rw [conjSubgroup_conjSubgroup]
    refine eq_of_map_jMap_le hT (le_of_eq ?_)
    rw [← h, hmap c, hmap (r * c), map_mul, conjSubgroup_conjSubgroup]
  exact ⟨r, key hk1, key hk2⟩

end Abstract


section Sub

variable {G : Type} [Group G] [Finite G] {R T : Subgroup G}

theorem exists_mem_conj_of_jMap_sub (hT : IsWC T) (hTR : T ≤ R)
    (hconcl : Lemma26Concl (jQuot ↥R) ((T.subgroupOf R).map (jMap ↥R)))
    (hA6 : ¬ Nonempty (jQuot ↥R ⧸ Subgroup.center (jQuot ↥R) ≃* alternatingGroup (Fin 6)))
    {a₁ a₂ b₁ b₂ : G} (ha₁ : a₁ ∈ R) (ha₂ : a₂ ∈ R) (hb₁ : b₁ ∈ R) (hb₂ : b₂ ∈ R)
    (hne₁ : conjSubgroup a₁ T ≠ conjSubgroup a₂ T) (hne₂ : conjSubgroup b₁ T ≠ conjSubgroup b₂ T) :
    ∃ r ∈ R, conjSubgroup r (conjSubgroup a₁ T) = conjSubgroup b₁ T ∧
      conjSubgroup r (conjSubgroup a₂ T) = conjSubgroup b₂ T := by
  have hconj : ∀ {c : G} (hc : c ∈ R), conjSubgroup (⟨c, hc⟩ : ↥R) (T.subgroupOf R) =
      (conjSubgroup c T).subgroupOf R := fun {c} hc => conjSubgroup_subgroupOf R T ⟨c, hc⟩
  have hle : ∀ {c : G}, c ∈ R → conjSubgroup c T ≤ R := fun hc =>
    conjSubgroup_le_of_le_of_mem hTR hc
  have hne : ∀ {c d : G} (hc : c ∈ R) (hd : d ∈ R), conjSubgroup c T ≠ conjSubgroup d T →
      conjSubgroup (⟨c, hc⟩ : ↥R) (T.subgroupOf R) ≠
        conjSubgroup (⟨d, hd⟩ : ↥R) (T.subgroupOf R) := by
    intro c d hc hd h h'
    rw [hconj hc, hconj hd] at h'
    have := Subgroup.subgroupOf_inj.1 h'
    rw [inf_of_le_left (hle hc), inf_of_le_left (hle hd)] at this
    exact h this
  obtain ⟨r, h1, h2⟩ := exists_mem_conj_of_jMap (isWC_subgroupOf hT R hTR) hconcl hA6
    (hne ha₁ ha₂ hne₁) (hne hb₁ hb₂ hne₂)
  refine ⟨(r : G), r.2, ?_, ?_⟩
  · rw [hconj ha₁, hconj hb₁, conjSubgroup_subgroupOf] at h1
    have := Subgroup.subgroupOf_inj.1 h1
    rwa [inf_of_le_left (conjSubgroup_le_of_le_of_mem (hle ha₁) r.2), inf_of_le_left (hle hb₁)]
      at this
  · rw [hconj ha₂, hconj hb₂, conjSubgroup_subgroupOf] at h2
    have := Subgroup.subgroupOf_inj.1 h2
    rwa [inf_of_le_left (conjSubgroup_le_of_le_of_mem (hle ha₂) r.2), inf_of_le_left (hle hb₂)]
      at this

end Sub

end CFSG.CGT.Timmesfeld75

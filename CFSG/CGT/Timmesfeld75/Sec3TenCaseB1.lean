module

public import CFSG.CGT.Timmesfeld75.Sec3GlobalConj
public import CFSG.CGT.Timmesfeld75.Sec3EightTransv

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type} [Group G] {T T₁ : Subgroup G}

@[expose] def Sec3Dih (T T₁ : Subgroup G) (n : ℕ) : Prop :=
  ∃ _ : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal,
    Nonempty (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁) ≃* DihedralGroup n)

theorem Sec3Dih.conj {A B : Subgroup G} {n : ℕ} (h : Sec3Dih A B n) (c : G) :
    Sec3Dih (conjSubgroup c A) (conjSubgroup c B) n := by
  obtain ⟨hN, ⟨iso⟩⟩ := h
  obtain ⟨hN', ⟨e⟩⟩ := exists_normal_quotientEquiv_conj hN c
    (X' := conjSubgroup c A ⊔ conjSubgroup c B) (M' := cfgM (conjSubgroup c A) (conjSubgroup c B))
    (conjSubgroup_sup_eq_sup c A B).symm (cfgM_conj c A B)
  exact ⟨hN', ⟨e.trans iso⟩⟩

theorem Sec3Dih.conj_of_mem_normalizer {n : ℕ} (h : Sec3Dih T T₁ n) {g : G}
    (hg : g ∈ Subgroup.normalizer (T : Set G)) : Sec3Dih T (conjSubgroup g T₁) n := by
  have := h.conj g
  rwa [mem_normalizer_iff_conjSubgroup_eq.1 hg] at this

theorem Sec3.conj_of_mem_normalizer [Finite G] (hS : Sec3 T T₁) {g : G}
    (hg : g ∈ Subgroup.normalizer (T : Set G)) : Sec3 T (conjSubgroup g T₁) := by
  have := hS.conj_gen g
  rwa [mem_normalizer_iff_conjSubgroup_eq.1 hg] at this

theorem normIn_conj_left_of_mem_normalizer {g : G} (hg : g ∈ Subgroup.normalizer (T : Set G))
    (T₁ : Subgroup G) : normIn T (conjSubgroup g T₁) = conjSubgroup g (normIn T T₁) :=
  normIn_conjSubgroup_of_mem_normalizer hg T₁

theorem normIn_conj_right_of_mem_normalizer {g : G} (hg : g ∈ Subgroup.normalizer (T : Set G))
    (T₁ : Subgroup G) : normIn (conjSubgroup g T₁) T = conjSubgroup g (normIn T₁ T) := by
  have := normIn_conj g T₁ T
  rwa [mem_normalizer_iff_conjSubgroup_eq.1 hg] at this

theorem Sec3.isLElt_conj [Finite G] (hS : Sec3 T T₁) {g : G}
    (hg : g ∈ Subgroup.normalizer (T : Set G)) {x : G} (hx : x ∈ conjSubgroup g (normIn T₁ T))
    (hx1 : x ≠ 1) : IsLElt T (conjSubgroup g T₁) x :=
  (hS.conj_of_mem_normalizer hg).isLElt_of_mem_normIn
    (by rwa [normIn_conj_right_of_mem_normalizer hg]) hx1

end CFSG.CGT.Timmesfeld75

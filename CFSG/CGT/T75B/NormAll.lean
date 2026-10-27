module

public import CFSG.CGT.Timmesfeld75.Sec3Thirteen
public import CFSG.CGT.Timmesfeld75.Sec3Results
public import CFSG.CGT.Timmesfeld75.Sec4CaseIJBasic
public import CFSG.CGT.Timmesfeld75.Sec3TenCaseA
public import CFSG.CGT.Timmesfeld75.Sec4CaseIBasic
public import CFSG.CGT.Timmesfeld75.Sec4CaseIIIFour
public import CFSG.CGT.Timmesfeld75.Sec4CaseIPGroup
public import CFSG.CGT.Timmesfeld75.Sec4CaseIPartition4
public import CFSG.CGT.Timmesfeld75.Sec4Three
public import CFSG.CGT.Timmesfeld75.Sec5FiveEng
public import CFSG.CGT.Timmesfeld75.Step511Card
public import CFSG.CGT.Timmesfeld75.Step57Reduction
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_18_b
public import Certificates.Certificate113

public section

namespace CFSG.CGT.T75B

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped commutatorElement

section Pair

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {T T₁ : Subgroup G}

theorem Sec3.inv_mul_conj_mem_cfgM (hnab : ∃ a b : G, a * b ≠ b * a) (hT : IsWC T)
    (hglob : Sec3Global T) (hiso : Sec3IsoGlobal T) (h16 : Nat.card T ≠ 16) (hS : Sec3 T T₁)
    (hSiso : Sec3Iso T T₁) {b : G} (hbD : b ∈ classD T)
    (hbT : b ∈ Subgroup.normalizer (T : Set G)) (hbS : b ∈ Subgroup.normalizer (T₁ : Set G))
    {x : G} (hx : x ∈ T ⊔ T₁) : x⁻¹ * (b * x * b⁻¹) ∈ cfgM T T₁ := by
  obtain ⟨hN, f, hf, hpair⟩ := hS.exists_isL2Pair hSiso
  have hbb : b * b = 1 := by
    obtain ⟨k, t, ht, -, hbk⟩ := hbD
    rw [hbk]
    calc k⁻¹ * t * k * (k⁻¹ * t * k) = k⁻¹ * (t * t) * k := by group
      _ = 1 := by rw [elemAbelian_mul_self hT.1 ht]; group
  have hbX : b ∈ Subgroup.normalizer ((T ⊔ T₁ : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff_conjSubgroup_eq, conjSubgroup_sup_eq_sup,
      mem_normalizer_iff_conjSubgroup_eq.1 hbT, mem_normalizer_iff_conjSubgroup_eq.1 hbS]
  have hbM : b ∈ Subgroup.normalizer (cfgM T T₁ : Set G) := by
    rw [mem_normalizer_iff_conjSubgroup_eq, ← cfgM_conj, mem_normalizer_iff_conjSubgroup_eq.1 hbT,
      mem_normalizer_iff_conjSubgroup_eq.1 hbS]
  obtain ⟨φ, hφ⟩ := exists_quotient_conj_equiv (X := T ⊔ T₁) (N := cfgM T T₁) hbX hbM
  have hφφ := quotient_conj_equiv_involutive hbX hbb φ hφ
  have hφT := map_quotient_conj_equiv hbX hbT hbb φ hφ
  have hφS := map_quotient_conj_equiv hbX hbS hbb φ hφ
  have hconj : ∃ g : ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁),
      (T₁.subgroupOf (T ⊔ T₁)).map
        (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))) =
      conjSubgroup g ((T.subgroupOf (T ⊔ T₁)).map
        (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))) := by
    obtain ⟨y, hy, hy'⟩ := hS.conj
    refine ⟨QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨y, hy⟩, ?_⟩
    rw [← map_conjSubgroup, conjSubgroup_subgroupOf, ← hy']
  rcases autInvolDichotomy _ _ _ _ hpair hconj hS.map_ne_map φ hφφ hφT hφS with
    hid | ⟨F, iF, finF, charF, e, σ, hσ, -, -, hσe⟩
  · have h1 := hφ ⟨x, hx⟩
    rw [hid] at h1
    exact Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 h1)
  · exfalso
    have hbXc : ∀ y ∈ T ⊔ T₁, b * y * b⁻¹ ∈ T ⊔ T₁ := fun y hy =>
      (Subgroup.mem_normalizer_iff.1 hbX y).1 hy
    have hind : InducesFieldAut (T ⊔ T₁) (cfgM T T₁) b e σ :=
      ⟨hbXc, fun y => by rw [← hφ y]; exact hσe (QuotientGroup.mk y)⟩
    exact h16 (lemma312 G hnab T T₁ hT hglob hiso hS b hbD hN F iF finF charF e σ hσ hind).1

theorem Sec3.comm_mem_cfgM (hnab : ∃ a b : G, a * b ≠ b * a) (hT : IsWC T)
    (hglob : Sec3Global T) (hiso : Sec3IsoGlobal T) (h16 : Nat.card T ≠ 16) (hS : Sec3 T T₁)
    (hSiso : Sec3Iso T T₁) {b : G} (hbD : b ∈ classD T)
    (hbT : b ∈ Subgroup.normalizer (T : Set G)) (hbS : b ∈ Subgroup.normalizer (T₁ : Set G))
    {w : G} (hw : w ∈ T ⊔ T₁) : ⁅b, w⁆ ∈ cfgM T T₁ := by
  have h1 := Sec3.inv_mul_conj_mem_cfgM hnab hT hglob hiso h16 hS hSiso hbD hbT hbS hw
  have h2 := hS.cfg.conj_mem_cfgM hw h1
  have e : ⁅b, w⁆ = w * (w⁻¹ * (b * w * b⁻¹)) * w⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact h2

end Pair

section Hyp

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {T T₁ T₂ : Subgroup G} {a : G}

theorem _root_.CFSG.CGT.Timmesfeld75.Sec4Hyp.actsTriv_of_normalizes
    (h : Sec4Hyp T T₁ a T₂) (hnab : ∃ a b : G, a * b ≠ b * a) (h16 : Nat.card T ≠ 16) {x : G}
    (hxD : x ∈ classD T) (hxT : x ∈ Subgroup.normalizer (T : Set G))
    (hx₁ : x ∈ Subgroup.normalizer (T₁ : Set G)) (hx₂ : x ∈ Subgroup.normalizer (T₂ : Set G)) :
    Sec4ActsTriv T T₁ T₂ x := by
  have hT := h.pair.wc
  have hS₂ : Sec3 T T₂ :=
    sec3_of_conj_conj h.glob ⟨1, (conjSubgroup_one T).symm⟩ h.conj h.ne_left h.normIn_ne_bot
  have hI₂ : Sec3Iso T T₂ :=
    sec3Iso_of_conj_conj h.iso ⟨1, (conjSubgroup_one T).symm⟩ h.conj h.ne_left h.normIn_ne_bot
  have hM₂ : cfgM T T₂ ≤ sec4N T T₁ T₂ := by
    obtain ⟨g, hg, hg'⟩ := h.exists_mem_sec4Y_conj₂
    have hne : conjSubgroup g T ≠ T := hg' ▸ h.ne_left
    have := h.cfgM_conj_le_sec4N (h.sec4Y_le_normalizer hg) hne
    rwa [← hg'] at this
  refine h.actsTriv_of_commutators (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_)
  · exact cfgM_le_sec4N (Sec3.comm_mem_cfgM hnab hT h.glob h.iso h16 h.sec3 h.sec3Iso hxD hxT hx₁
      (Subgroup.mem_sup_left ht))
  · exact cfgM_le_sec4N (Sec3.comm_mem_cfgM hnab hT h.glob h.iso h16 h.sec3 h.sec3Iso hxD hxT hx₁
      (Subgroup.mem_sup_right ht))
  · exact hM₂ (Sec3.comm_mem_cfgM hnab hT h.glob h.iso h16 hS₂ hI₂ hxD hxT hx₂
      (Subgroup.mem_sup_right ht))

end Hyp

end CFSG.CGT.T75B
